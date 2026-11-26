#!/usr/bin/env python3
import json
from pathlib import Path
import tempfile
import unittest

from frontier import compute, load_proof_uses, main, render


def entry(tag, status, statement=(), proof=(), article='art'):
    e = {'tag': tag, 'title': f'Title {tag}', 'article': article, 'proof_status': status}
    if status != 'unformalised':
        e['dependencies'] = {'statement': list(statement), 'proof': list(proof)}
    return e


MANIFEST = {'schema': 'perclib-manifest-v1', 'commit': 'abc123', 'assertions': [
    entry('AAAA', 'proved'),
    entry('BBBB', 'statement-only', statement=['AAAA']),        # ready
    entry('CCCC', 'unformalised'),                               # ready via authored
    entry('DDDD', 'unformalised'),                               # blocked by BBBB only
    entry('EEEE', 'statement-only', statement=['BBBB']),         # blocked by BBBB, CCCC
    entry('FFFF', 'unformalised'),                               # blocked by EEEE
    entry('GGGG', 'unformalised'),                               # cycle with HHHH
    entry('HHHH', 'unformalised'),
    entry('IIII', 'unformalised', article='other'),              # missing prerequisite
    entry('JJJJ', 'unformalised'),                               # no record: unknown
    entry('KKKK', 'proved-modulo', article='other'),             # ready, unproved
]}
AUTHORED = {'BBBB': [], 'CCCC': ['AAAA'], 'DDDD': ['BBBB', 'AAAA'], 'EEEE': ['CCCC'],
            'FFFF': ['EEEE'], 'GGGG': ['HHHH'], 'HHHH': ['GGGG'], 'IIII': ['ZZZZ'],
            'KKKK': [], 'AAAA': ['JJJJ']}


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.result = compute(MANIFEST, AUTHORED)

    def test_classification(self):
        r = self.result
        self.assertEqual({x['tag'] for x in r['ranked']}, {'BBBB', 'CCCC', 'KKKK'})
        self.assertEqual(r['blocked'], ['DDDD', 'EEEE', 'FFFF', 'GGGG', 'HHHH', 'IIII'])
        self.assertEqual(r['unknown'], ['JJJJ'])
        # A proved assertion's authored record is ignored.
        self.assertEqual(r['proved'], ['AAAA'])

    def test_counts_and_order(self):
        rows = {x['tag']: x for x in self.result['ranked']}
        self.assertEqual((rows['BBBB']['unblocks'], rows['BBBB']['dependents']), (1, 3))
        self.assertEqual((rows['CCCC']['unblocks'], rows['CCCC']['dependents']), (0, 2))
        self.assertEqual((rows['KKKK']['unblocks'], rows['KKKK']['dependents']), (0, 0))
        self.assertEqual([x['tag'] for x in self.result['ranked']], ['BBBB', 'CCCC', 'KKKK'])
        self.assertEqual([a for a, _ in self.result['articles']], ['art', 'other'])

    def test_cycle_and_missing(self):
        self.assertEqual(self.result['cycles'], [['GGGG', 'HHHH']])
        self.assertEqual(self.result['missing'], ['ZZZZ'])

    def test_self_loop_is_ignored(self):
        m = {'schema': 'perclib-manifest-v1', 'assertions': [entry('AAAA', 'unformalised')]}
        r = compute(m, {'AAAA': ['AAAA']})
        self.assertEqual([x['tag'] for x in r['ranked']], ['AAAA'])
        self.assertEqual(r['cycles'], [])

    def test_render(self):
        text = render(self.result, 'abc123')
        self.assertIn('`abc123`', text)
        self.assertIn('- `BBBB` Title BBBB (article art; statement-only; unblocks 1, '
                      'dependents 3)', text)
        self.assertLess(text.index('`BBBB`'), text.index('`CCCC`'))
        self.assertIn('## Prerequisite cycles', text)
        self.assertIn('`ZZZZ`', text)
        self.assertNotIn('JJJJ', text.split('## art')[1])

    def test_load_and_main(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            (d / 'records').mkdir()
            rows = [{'order': i, 'tag': t, 'proof_uses': u, 'reason': 'r'}
                    for i, (t, u) in enumerate(sorted(AUTHORED.items()))]
            (d / 'records' / 'art.json').write_text(json.dumps(
                {'schema': 'perclib-article-records-v1', 'proofUses': rows}))
            (d / 'records' / 'ignored.json').write_text(json.dumps({'schema': 'other'}))
            self.assertEqual(load_proof_uses(d / 'records'),
                             {t: sorted(u) for t, u in AUTHORED.items()})
            (d / 'uses.json').write_text(json.dumps(
                {'schema': 'perclib-proof-uses-v1', 'assertions': rows}))
            self.assertEqual(load_proof_uses(d / 'uses.json'), load_proof_uses(d / 'records'))
            (d / 'm.json').write_text(json.dumps(MANIFEST))
            main([str(d / 'm.json'), '--proof-uses', str(d / 'records'),
                  '--output', str(d / 'out.md')])
            self.assertEqual((d / 'out.md').read_text(), render(self.result, 'abc123'))

    def test_duplicate_record_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'uses.json'
            row = {'tag': 'AAAA', 'proof_uses': [], 'reason': 'r'}
            p.write_text(json.dumps({'schema': 'perclib-proof-uses-v1',
                                     'assertions': [row, row]}))
            with self.assertRaises(ValueError):
                load_proof_uses(p)


if __name__ == '__main__':
    unittest.main()
