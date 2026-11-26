import test from 'node:test';
import assert from 'node:assert/strict';
import { renderMath } from '../src/render.mjs';

test('math inequalities are rendered before their angle brackets can be treated as HTML', () => {
  const raw = '<p>For $0<c<C$, take $p<p_c$. Thus Cauchy–Schwarz gives $d>3$.</p><div>$$a<b<c>d$$</div>';
  const escaped = raw.replace(/\$\$([\s\S]*?)\$\$|\$([^$]+?)\$/g, part => part.replaceAll('<', '&lt;').replaceAll('>', '&gt;'));
  const rendered = renderMath(raw);
  assert.equal(rendered, renderMath(escaped));
  assert.equal((rendered.match(/class="katex-mathml"/g) || []).length, 4);
  assert.ok(rendered.includes('Thus Cauchy–Schwarz gives'));
  assert.ok(!rendered.includes('$'));
});

test('attributes and code examples retain literal dollar delimiters', () => {
  const prefix = '<p title="$x<y$ and $y>x$">';
  const code = '<code>$a<b$</code><pre><code>$$p<q$$</code></pre>';
  const rendered = renderMath(prefix + '$x<y$</p>' + code);
  assert.ok(rendered.startsWith(prefix));
  assert.ok(rendered.endsWith(code));
  assert.equal((rendered.match(/class="katex-mathml"/g) || []).length, 1);
});

test('an unmatched dollar in a shortened excerpt does not consume the next element', () => {
  const excerpt = '<p>Truncated $x ...</p><a href="/source/#page">Source</a>';
  const rendered = renderMath(excerpt + '<p>Now $y>0$.</p>');
  assert.ok(rendered.startsWith(excerpt));
  assert.equal((rendered.match(/class="katex-mathml"/g) || []).length, 1);
  assert.ok(rendered.endsWith('</p>'));
});
