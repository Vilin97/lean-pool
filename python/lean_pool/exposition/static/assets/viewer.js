/* All-declarations viewer for the Lean Pool exposition.
 *
 * Fetches ../data/decls.json (~55K rows, compact arrays) and renders a
 * virtual-scrolled table: one absolutely positioned window of recycled row
 * elements inside a fixed-height spacer. All heavy work happens once at
 * load (lowercased names, per-column sorted index arrays); interactions are
 * a single O(N) pass over typed arrays, well under 50 ms at pool scale.
 */
(function () {
  "use strict";

  const ROW_HEIGHT = 34; // px; must match .vrow height in viewer.css
  const OVERSCAN = 12;   // extra rows rendered above/below the viewport
  const SEARCH_DEBOUNCE_MS = 150;
  const CANONICAL_KINDS = [
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "class", "inductive", "axiom", "opaque",
  ];

  const scroller = document.getElementById("vscroll");
  const spacer = document.getElementById("vspacer");
  const windowEl = document.getElementById("vwindow");
  const emptyEl = document.getElementById("vempty");
  const countEl = document.getElementById("declCount");
  const searchEl = document.getElementById("declSearch");
  const selectEl = document.getElementById("projectSelect");
  const chipsEl = document.getElementById("kindChips");
  const headEl = document.getElementById("vhead");
  const errorEl = document.getElementById("loadError");

  // Column-store over the decls array (filled in init).
  let total = 0;
  let kinds = [];
  let projects = [];
  let names = null;      // string[]
  let lowerNames = null; // string[], precomputed once for search + sort
  let kindOf = null;     // Uint8Array
  let projectOf = null;  // Uint16Array
  let declIdOf = null;   // Uint32Array
  let kindRank = null;   // Uint8Array: kind index -> canonical display rank

  const sortedOrders = new Map(); // column name -> ascending Uint32Array
  let filtered = null;            // Uint32Array scratch; first filteredCount valid
  let filteredCount = 0;

  const state = {
    column: "name",
    descending: false,
    query: "",
    project: -1,       // -1 = all projects
    kindActive: [],    // boolean per kind index
  };

  const rowPool = []; // recycled .vrow elements
  let renderScheduled = false;

  function formatCount(value) {
    return value.toLocaleString("en-US");
  }

  function kindClass(kindName) {
    return CANONICAL_KINDS.includes(kindName) ? `k-${kindName}` : "k-other";
  }

  // ---------- sorting ----------

  function nameCompare(a, b) {
    const la = lowerNames[a];
    const lb = lowerNames[b];
    if (la < lb) return -1;
    if (la > lb) return 1;
    return a - b; // deterministic tie-break
  }

  function orderFor(column) {
    let order = sortedOrders.get(column);
    if (order) return order;
    order = new Uint32Array(total);
    for (let i = 0; i < total; i++) order[i] = i;
    let compare = nameCompare;
    if (column === "kind") {
      compare = (a, b) => kindRank[kindOf[a]] - kindRank[kindOf[b]] || nameCompare(a, b);
    } else if (column === "project") {
      compare = (a, b) => projectOf[a] - projectOf[b] || nameCompare(a, b);
    }
    order.sort(compare);
    sortedOrders.set(column, order);
    return order;
  }

  // ---------- filtering ----------

  function applyFilter() {
    const order = orderFor(state.column);
    const descending = state.descending;
    const query = state.query;
    const hasQuery = query.length > 0;
    const project = state.project;
    const kindActive = state.kindActive;
    const allKindsActive = kindActive.every(Boolean);
    let n = 0;
    for (let j = 0; j < total; j++) {
      // Descending = walk the ascending order backwards (no array reversal).
      const i = order[descending ? total - 1 - j : j];
      if (project !== -1 && projectOf[i] !== project) continue;
      if (!allKindsActive && !kindActive[kindOf[i]]) continue;
      if (hasQuery && lowerNames[i].indexOf(query) === -1) continue;
      filtered[n++] = i;
    }
    filteredCount = n;
  }

  function refresh(resetScroll) {
    applyFilter();
    spacer.style.height = `${filteredCount * ROW_HEIGHT}px`;
    emptyEl.hidden = filteredCount !== 0;
    countEl.textContent =
      `${formatCount(filteredCount)} of ${formatCount(total)} declarations`;
    if (resetScroll) scroller.scrollTop = 0;
    renderWindow();
  }

  // ---------- virtual window ----------

  function makeRow() {
    const row = document.createElement("div");
    row.className = "vrow";
    // A real link gives keyboard focus, Enter activation, and open-in-new-tab.
    const name = document.createElement("a");
    name.className = "vcell-name";
    const kind = document.createElement("span");
    kind.className = "kchip";
    const project = document.createElement("a");
    project.className = "vcell-project";
    row.append(name, kind, project);
    row._name = name;
    row._kind = kind;
    row._project = project;
    return row;
  }

  function ensureRows(count) {
    while (rowPool.length < count) {
      const row = makeRow();
      windowEl.appendChild(row);
      rowPool.push(row);
    }
  }

  function fillRow(row, i) {
    row.dataset.index = i;
    row._name.textContent = names[i];
    const slug = projects[projectOf[i]];
    row._name.href = `../p/${encodeURIComponent(slug)}/index.html#d${declIdOf[i]}`;
    const kindName = kinds[kindOf[i]];
    row._kind.textContent = kindName;
    row._kind.className = `kchip ${kindClass(kindName)}`;
    row._project.textContent = slug;
    row._project.href = `../p/${encodeURIComponent(slug)}/`;
  }

  function renderWindow() {
    let first = Math.floor(scroller.scrollTop / ROW_HEIGHT) - OVERSCAN;
    if (first < 0) first = 0;
    const visible = Math.ceil(scroller.clientHeight / ROW_HEIGHT) + 2 * OVERSCAN;
    const needed = Math.max(0, Math.min(visible, filteredCount - first));
    ensureRows(needed);
    windowEl.style.transform = `translateY(${first * ROW_HEIGHT}px)`;
    for (let r = 0; r < rowPool.length; r++) {
      const row = rowPool[r];
      if (r < needed) {
        fillRow(row, filtered[first + r]);
        row.style.display = "";
      } else {
        row.style.display = "none";
      }
    }
  }

  function scheduleRender() {
    if (renderScheduled) return;
    renderScheduled = true;
    requestAnimationFrame(() => {
      renderScheduled = false;
      renderWindow();
    });
  }

  // ---------- toolbar ----------

  function buildProjectSelect() {
    const fragment = document.createDocumentFragment();
    for (let p = 0; p < projects.length; p++) {
      const option = document.createElement("option");
      option.value = String(p);
      option.textContent = projects[p];
      fragment.appendChild(option);
    }
    selectEl.appendChild(fragment);
  }

  function buildKindChips(kindCounts) {
    const displayOrder = kinds.map((_, k) => k)
      .sort((a, b) => kindRank[a] - kindRank[b] || a - b);
    for (const k of displayOrder) {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.className = `kfilter-chip ${kindClass(kinds[k])}`;
      chip.setAttribute("aria-pressed", "true");
      const label = document.createElement("span");
      label.textContent = kinds[k];
      const count = document.createElement("span");
      count.className = "chip-count";
      count.textContent = formatCount(kindCounts[k]);
      chip.append(label, count);
      chip.addEventListener("click", () => {
        state.kindActive[k] = !state.kindActive[k];
        chip.setAttribute("aria-pressed", String(state.kindActive[k]));
        chip.classList.toggle("chip-off", !state.kindActive[k]);
        refresh(true);
      });
      chipsEl.appendChild(chip);
    }
  }

  function updateSortIndicators() {
    for (const button of headEl.querySelectorAll(".vsort")) {
      if (button.dataset.col === state.column) {
        button.dataset.dir = state.descending ? "desc" : "asc";
        button.setAttribute("aria-sort",
          state.descending ? "descending" : "ascending");
      } else {
        delete button.dataset.dir;
        button.setAttribute("aria-sort", "none");
      }
    }
  }

  function wireEvents() {
    scroller.addEventListener("scroll", scheduleRender);
    window.addEventListener("resize", scheduleRender);

    // Row click -> project page anchored at the declaration. Clicks on the
    // project <a> keep their default navigation (to the project page top).
    windowEl.addEventListener("click", (event) => {
      if (event.target.closest("a")) return;
      const row = event.target.closest(".vrow");
      if (!row) return;
      const i = Number(row.dataset.index);
      const slug = encodeURIComponent(projects[projectOf[i]]);
      window.location.href = `../p/${slug}/index.html#d${declIdOf[i]}`;
    });

    let searchTimer = 0;
    searchEl.addEventListener("input", () => {
      clearTimeout(searchTimer);
      searchTimer = setTimeout(() => {
        state.query = searchEl.value.trim().toLowerCase();
        refresh(true);
      }, SEARCH_DEBOUNCE_MS);
    });

    selectEl.addEventListener("change", () => {
      state.project = Number(selectEl.value);
      refresh(true);
    });

    headEl.addEventListener("click", (event) => {
      const button = event.target.closest(".vsort");
      if (!button) return;
      const column = button.dataset.col;
      if (state.column === column) {
        state.descending = !state.descending;
      } else {
        state.column = column;
        state.descending = false;
      }
      updateSortIndicators();
      refresh(true);
    });
  }

  // ---------- boot ----------

  function init(data) {
    kinds = data.kinds || [];
    projects = data.projects || [];
    const raw = data.decls || [];
    total = raw.length;

    names = new Array(total);
    lowerNames = new Array(total);
    kindOf = new Uint8Array(total);
    projectOf = new Uint16Array(total);
    declIdOf = new Uint32Array(total);
    const kindCounts = new Array(kinds.length).fill(0);
    for (let i = 0; i < total; i++) {
      const row = raw[i];
      names[i] = row[0];
      lowerNames[i] = row[0].toLowerCase();
      kindOf[i] = row[1];
      projectOf[i] = row[2];
      declIdOf[i] = row[3];
      kindCounts[row[1]] += 1;
    }

    kindRank = new Uint8Array(kinds.length);
    for (let k = 0; k < kinds.length; k++) {
      const rank = CANONICAL_KINDS.indexOf(kinds[k]);
      kindRank[k] = rank === -1 ? CANONICAL_KINDS.length : rank;
    }
    state.kindActive = new Array(kinds.length).fill(true);
    filtered = new Uint32Array(total);

    buildProjectSelect();
    buildKindChips(kindCounts);
    wireEvents();
    updateSortIndicators();
    refresh(true);
  }

  fetch("../data/decls.json")
    .then((response) => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then(init)
    .catch((error) => {
      countEl.textContent = "";
      errorEl.hidden = false;
      errorEl.textContent =
        `Failed to load ../data/decls.json (${error.message}). `
        + "If you opened this page from disk, serve it over HTTP instead.";
    });
})();
