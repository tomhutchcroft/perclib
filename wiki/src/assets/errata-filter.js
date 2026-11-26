"use strict";
(() => {
  const form = document.querySelector("#errata-filter");
  if (!form) return;
  const status = document.querySelector("#errata-filter-status");
  const pending = document.querySelector("#errata-pending");
  const keys = ["repair", "significance", "source"];
  const fields = Object.fromEntries(keys.map((key) => [key, form.elements.namedItem(key)]));
  const groups = [...document.querySelectorAll("[data-errata-group]")].map((element) => ({
    element,
    rows: [...element.querySelectorAll("[data-errata-row]")],
  }));
  const rows = groups.flatMap((group) => group.rows);
  const total = rows.filter((row) => row.dataset.repair !== "withdrawn").length;
  const withdrawnTotal = rows.length - total;
  function readLocation() {
    const params = new URLSearchParams(location.search);
    for (const key of keys) {
      const value = params.get(key) ?? "";
      fields[key].value = [...fields[key].options].some((option) => option.value === value) ? value : "";
    }
  }
  function render(updateLocation) {
    const repair = fields.repair.value, scale = fields.significance.value, source = fields.source.value;
    let shown = 0, withdrawn = 0;
    for (const group of groups) {
      let visible = 0;
      for (const row of group.rows) {
        row.hidden = Boolean((source && group.element.dataset.errataGroup !== source) ||
          (repair && row.dataset.repair !== repair) || (scale && row.dataset.scale !== scale));
        if (!row.hidden) {
          visible++;
          if (row.dataset.repair === "withdrawn") withdrawn++;
          else shown++;
        }
      }
      group.element.hidden = visible === 0;
    }
    if (pending) pending.hidden = Boolean(repair || scale || source);
    status.textContent = `Showing ${shown} of ${total} active entries` +
      (withdrawnTotal ? `; ${withdrawn} of ${withdrawnTotal} withdrawn entries` : "") + "." +
      (shown + withdrawn === 0 ? " No entries match these filters. Clear a filter to see more." : "");
    if (updateLocation) {
      const params = new URLSearchParams(location.search);
      for (const key of keys) {
        if (fields[key].value) params.set(key, fields[key].value);
        else params.delete(key);
      }
      const query = params.toString();
      // Filtering also works in downloaded copies where changing the URL is forbidden.
      try { history.replaceState(null, "", location.pathname + (query ? "?" + query : "") + location.hash); }
      catch {}
    }
  }
  form.addEventListener("change", () => render(true));
  form.addEventListener("submit", (event) => { event.preventDefault(); render(true); });
  form.addEventListener("reset", (event) => {
    event.preventDefault();
    for (const key of keys) fields[key].value = "";
    render(true);
  });
  window.addEventListener("popstate", () => { readLocation(); render(false); });
  readLocation();
  render(false);
  form.hidden = false;
})();
