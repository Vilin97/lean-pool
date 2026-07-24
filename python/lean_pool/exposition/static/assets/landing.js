/* Landing page for the Lean Pool exposition.
 *
 * Fetches data/index.json (relative to the exposition root) and renders:
 *   - stat tiles (projects / declarations / edges / deepest chain),
 *   - a segmented kind-breakdown bar with a legend,
 *   - a sortable, filterable project table,
 *   - a "generated … · commit …" footer.
 */
(function () {
  "use strict";

  const CANONICAL_KINDS = [
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "class", "inductive", "axiom", "opaque",
  ];

  const COLUMNS = [
    { key: "project", label: "Project", numeric: false },
    { key: "branch", label: "Area", numeric: false },
    { key: "provenance", label: "Provenance", numeric: false },
    { key: "license", label: "License", numeric: false },
    { key: "nodes", label: "Decls", numeric: true },
    { key: "edges", label: "Edges", numeric: true },
    { key: "maxDepth", label: "Max depth", numeric: true },
    { key: "avgDepth", label: "Avg depth", numeric: true },
  ];

  // Default sort: declaration count, largest first.
  const state = { column: "nodes", descending: true, filter: "" };
  let projects = [];

  function element(id) {
    return document.getElementById(id);
  }

  function formatCount(value) {
    return Number(value).toLocaleString("en-US");
  }

  function kindColor(kind) {
    return CANONICAL_KINDS.includes(kind) ? `var(--kind-${kind})` : "var(--muted)";
  }

  // ---------- stat tiles ----------

  function renderTiles(totals) {
    const tiles = [
      ["Projects", totals.projects],
      ["Declarations", totals.decls],
      ["Dependency edges", totals.edges],
      ["Deepest chain", totals.maxDepth],
    ];
    const box = element("statTiles");
    for (const [label, value] of tiles) {
      const tile = document.createElement("div");
      tile.className = "stat-tile";
      const valueEl = document.createElement("div");
      valueEl.className = "stat-value";
      valueEl.textContent = formatCount(value);
      const labelEl = document.createElement("div");
      labelEl.className = "stat-label";
      labelEl.textContent = label;
      tile.append(valueEl, labelEl);
      box.appendChild(tile);
    }
    box.hidden = false;
  }

  // ---------- kind breakdown bar ----------

  function renderKindBreakdown(kinds) {
    const entries = Object.entries(kinds || {})
      .filter(([, count]) => count > 0)
      .sort((a, b) => b[1] - a[1]);
    if (entries.length === 0) return;
    const total = entries.reduce((sum, [, count]) => sum + count, 0);

    const bar = element("kindBar");
    const legend = element("kindLegend");
    for (const [kind, count] of entries) {
      const segment = document.createElement("div");
      segment.className = "kind-seg";
      segment.style.flexGrow = String(count);
      segment.style.background = kindColor(kind);
      const pct = ((100 * count) / total).toFixed(1);
      segment.title = `${kind} — ${formatCount(count)} (${pct}%)`;
      bar.appendChild(segment);

      const item = document.createElement("span");
      item.className = "legend-item";
      const dot = document.createElement("span");
      dot.className = "legend-dot";
      dot.style.background = kindColor(kind);
      const name = document.createElement("span");
      name.textContent = kind;
      const countEl = document.createElement("span");
      countEl.className = "legend-count";
      countEl.textContent = formatCount(count);
      item.append(dot, name, countEl);
      legend.appendChild(item);
    }
    element("kindBreakdown").hidden = false;
  }

  // ---------- project table ----------

  function sortValue(project, key) {
    switch (key) {
      case "project":
        return (project.title || project.slug).toLowerCase();
      case "provenance":
      case "branch":
      case "license":
        return (project[key] || "￿").toLowerCase(); // sort null values last (asc)
      default:
        return project[key];
    }
  }

  function compareProjects(a, b) {
    const va = sortValue(a, state.column);
    const vb = sortValue(b, state.column);
    let cmp = va < vb ? -1 : va > vb ? 1 : 0;
    if (cmp === 0) cmp = a.slug < b.slug ? -1 : a.slug > b.slug ? 1 : 0;
    return state.descending ? -cmp : cmp;
  }

  function renderHead() {
    const row = element("projectHead");
    row.textContent = "";
    for (const column of COLUMNS) {
      const th = document.createElement("th");
      if (column.numeric) th.className = "num";
      th.setAttribute("aria-sort", state.column === column.key
        ? (state.descending ? "descending" : "ascending")
        : "none");
      const button = document.createElement("button");
      button.type = "button";
      button.className = "sort-button";
      button.textContent = column.label;
      if (state.column === column.key) {
        button.dataset.dir = state.descending ? "desc" : "asc";
      }
      button.addEventListener("click", () => {
        if (state.column === column.key) {
          state.descending = !state.descending;
        } else {
          state.column = column.key;
          state.descending = column.numeric; // numeric columns start descending
        }
        renderHead();
        renderBody();
      });
      th.appendChild(button);
      row.appendChild(th);
    }
  }

  function numericCell(text) {
    const td = document.createElement("td");
    td.className = "num";
    td.textContent = text;
    return td;
  }

  function renderRow(project) {
    const tr = document.createElement("tr");

    const projectCell = document.createElement("td");
    projectCell.className = "cell-project";
    const link = document.createElement("a");
    link.href = `p/${encodeURIComponent(project.slug)}/`;
    const title = document.createElement("span");
    title.className = "project-name";
    title.textContent = project.title || project.slug;
    const slug = document.createElement("span");
    slug.className = "project-slug";
    slug.textContent = project.slug;
    link.append(title, slug);
    projectCell.appendChild(link);
    if (project.authors && project.authors.length) {
      const authors = document.createElement("span");
      authors.className = "project-authors";
      authors.textContent = project.authors.join(", ");
      projectCell.appendChild(authors);
    }
    tr.appendChild(projectCell);

    const branchCell = document.createElement("td");
    branchCell.className = "cell-branch";
    branchCell.textContent = project.branch || "—";
    tr.appendChild(branchCell);

    const provenanceCell = document.createElement("td");
    const badge = document.createElement("span");
    badge.className = `prov prov-${project.provenance || "none"}`;
    badge.textContent = project.provenance || "—";
    provenanceCell.appendChild(badge);
    tr.appendChild(provenanceCell);

    const licenseCell = document.createElement("td");
    licenseCell.className = "cell-license";
    licenseCell.textContent = project.license || "—";
    tr.appendChild(licenseCell);

    tr.appendChild(numericCell(formatCount(project.nodes)));
    tr.appendChild(numericCell(formatCount(project.edges)));
    tr.appendChild(numericCell(formatCount(project.maxDepth)));
    tr.appendChild(numericCell(Number(project.avgDepth || 0).toFixed(2)));
    return tr;
  }

  function renderBody() {
    const query = state.filter;
    const rows = projects.filter((p) =>
      !query
      || p.slug.toLowerCase().includes(query)
      || (p.title || "").toLowerCase().includes(query)
      || (p.branch || "").toLowerCase().includes(query)
      || (p.authors || []).some((a) => a.toLowerCase().includes(query)));
    rows.sort(compareProjects);

    const body = element("projectBody");
    body.textContent = "";
    const fragment = document.createDocumentFragment();
    for (const project of rows) fragment.appendChild(renderRow(project));
    body.appendChild(fragment);

    if (rows.length === 0) {
      const tr = document.createElement("tr");
      const td = document.createElement("td");
      td.colSpan = COLUMNS.length;
      td.className = "table-empty";
      td.textContent = "No projects match.";
      tr.appendChild(td);
      body.appendChild(tr);
    }

    element("projectCount").textContent = query
      ? `${rows.length} of ${projects.length} projects`
      : `${projects.length} projects`;
  }

  // ---------- footer ----------

  function renderFooter(data) {
    const footer = element("landingFooter");
    const date = (data.generated || "").slice(0, 10);
    const sha = (data.commit || "").slice(0, 7);
    footer.append(`generated ${date} · commit `);
    const link = document.createElement("a");
    link.className = "mono";
    link.href = `https://github.com/Vilin97/lean-pool/commit/${encodeURIComponent(data.commit || "")}`;
    link.textContent = sha;
    footer.appendChild(link);
  }

  // ---------- boot ----------

  function init(data) {
    projects = (data.projects || []).slice();
    renderTiles(data.totals || {});
    renderKindBreakdown((data.totals || {}).kinds);
    renderHead();
    renderBody();
    renderFooter(data);
    element("projectsSection").hidden = false;

    element("projectFilter").addEventListener("input", (event) => {
      state.filter = event.target.value.trim().toLowerCase();
      renderBody();
    });
  }

  fetch("data/index.json")
    .then((response) => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then(init)
    .catch((error) => {
      const box = element("loadError");
      box.hidden = false;
      box.textContent =
        `Failed to load data/index.json (${error.message}). `
        + "If you opened this page from disk, serve it over HTTP instead.";
    });
})();
