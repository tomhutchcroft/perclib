"use strict";
// Article pages: collapsible blocks, links into them, expand/collapse all,
// printing with every block open, and hover previews of linked statements.
(() => {
  const article = document.querySelector("article.article");
  if (!article) return;
  const blocks = () => Array.from(article.querySelectorAll("details"));

  // Open every collapsed block enclosing the element with this id, then show it.
  function reveal(id) {
    const target = id && document.getElementById(id);
    if (!target) return false;
    for (let node = target.parentElement; node; node = node.parentElement)
      if (node.tagName === "DETAILS") node.open = true;
    target.scrollIntoView({ block: "start" });
    return true;
  }
  const fragment = (hash) => {
    const raw = hash.replace(/^#/, "");
    try {
      return decodeURIComponent(raw);
    } catch {
      return raw;
    }
  };
  const revealHash = () => reveal(fragment(location.hash));
  addEventListener("hashchange", revealHash);
  revealHash();

  // A link to a fragment of this page, or to /tag/XXXX/ for an assertion on
  // this page, reveals its target without leaving the page.
  document.addEventListener("click", (event) => {
    if (event.defaultPrevented || event.button || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const link = event.target.closest && event.target.closest("a[href]");
    if (!link) return;
    let url;
    try {
      url = new URL(link.getAttribute("href"), location.href);
    } catch {
      return;
    }
    let id = null;
    const tag = /\/tag\/([0-9A-Z]{4})\/(?:index\.html)?$/.exec(url.pathname);
    if (tag && document.getElementById("tag-" + tag[1])) id = "tag-" + tag[1];
    else if (url.hash && url.pathname === location.pathname && url.search === location.search)
      id = fragment(url.hash);
    if (!id || !document.getElementById(id)) return;
    event.preventDefault();
    if (fragment(location.hash) === id) reveal(id);
    else location.hash = id; // hashchange reveals it and keeps history
  });

  const tools = article.querySelector(".article-tools");
  if (tools) {
    tools.hidden = false;
    for (const button of tools.querySelectorAll("[data-details-action]"))
      button.addEventListener("click", () => {
        const open = button.getAttribute("data-details-action") === "expand";
        for (const block of blocks()) block.open = open;
      });
  }

  // Print everything; restore the reader's choice afterwards.
  let saved = null;
  addEventListener("beforeprint", () => {
    saved = blocks().map((block) => [block, block.open]);
    for (const [block] of saved) block.open = true;
  });
  addEventListener("afterprint", () => {
    if (saved) for (const [block, open] of saved) block.open = open;
    saved = null;
  });

  const dataNode = document.getElementById("link-preview-data");
  if (!dataNode) return;
  let previews;
  try {
    previews = JSON.parse(dataNode.textContent);
  } catch {
    return;
  }
  let box = null;
  const hide = () => {
    if (box) box.remove();
    box = null;
  };
  const show = (link) => {
    const entry = previews[link.getAttribute("data-preview")];
    if (!entry) return;
    hide();
    box = document.createElement("div");
    box.className = "link-preview";
    box.setAttribute("role", "tooltip");
    // Pre-rendered at build time from the article sources (titles, summaries).
    box.innerHTML = `<small>${entry.k}</small><strong>${entry.t}</strong><p>${entry.s}</p>`;
    document.body.append(box);
    const rect = link.getBoundingClientRect();
    const top = rect.bottom + 8;
    box.style.left = Math.max(12, Math.min(rect.left, innerWidth - box.offsetWidth - 12)) + "px";
    box.style.top = (top + box.offsetHeight > innerHeight ? rect.top - box.offsetHeight - 8 : top) + "px";
  };
  const previewLink = (event) => event.target.closest && event.target.closest("a[data-preview]");
  article.addEventListener("mouseover", (event) => {
    const link = previewLink(event);
    if (link) show(link);
  });
  article.addEventListener("mouseout", (event) => {
    if (previewLink(event)) hide();
  });
  article.addEventListener("focusin", (event) => {
    const link = previewLink(event);
    if (link) show(link);
  });
  article.addEventListener("focusout", hide);
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hide();
  });
  addEventListener("scroll", hide, { passive: true });
})();
