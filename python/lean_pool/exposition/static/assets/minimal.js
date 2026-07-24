/* Minimal Lean file builder for the Lean Pool exposition.
 *
 * Pure logic, no DOM: exposed as window.ExpoMinimal so graph.js (browser)
 * and the validation harness (node) share the exact same code paths.
 *
 * Faithful port of LMLExposition's assembly phases (Extract.lean, Rémy
 * Degenne, after Matthew Ballard's EmitStandalone.lean): per-target
 * filtering (`restrictToTarget`), external-import closure
 * (`externalImports`), `variable`-binder pruning (`pruneVariable` /
 * `binderBoundNames`), scope-tagged emission with empty-scope stripping
 * (`ScopeTag` / `stripEmptyScopes`), blank-line collapsing
 * (`collapseBlankRuns`), and the notation-usage closure at the end of
 * `writeAllExtractions`. The per-command classification (LML's phase 1)
 * happens ahead of time in the extractor; each shard module carries a
 * `commands` table whose positions are UTF-8 BYTE offsets into the raw
 * module source, so `sources` maps module index -> byte array
 * (Uint8Array in the browser, Buffer in node) and every slice is decoded
 * with TextDecoder after byte-slicing.
 *
 * Command-table entries (see SCHEMA.md):
 *   decl    {t:"d", s, e, d:[declIds], ed:[[s,e,repl],…]?, un:[kind…]?}
 *   context {t:"c", s, e, k:"ns"|"end"|"open"|"var"|"sec"|"opt"|"univ"|
 *            "nota", ns?, q?, b:[[s,e,[ident…]],…]?, on:[ns,[ident…]]?,
 *            kn:[kind…]?, nd:[declIds]?}
 * Non-exposed declarations have no entry (holes, like LML's `skip`).
 */
(function (root) {
  "use strict";

  var PROOF_KINDS = { theorem: true, lemma: true };

  function isProofKind(kind) {
    return PROOF_KINDS[kind] === true;
  }

  /* ----- byte slicing ------------------------------------------------------------ */

  var utf8Decoder = new TextDecoder("utf-8");

  /* Decode the byte range [start, end) of a module source. Accepts a
   * Uint8Array (browser) or a node Buffer (a Uint8Array subclass); both
   * support subarray and TextDecoder. */
  function decodeSlice(bytes, start, end) {
    return utf8Decoder.decode(bytes.subarray(start, end));
  }

  /* Port of LML's `applyEdits`: the source bytes [start, end) with each
   * edit [s, e, replacement] applied (a zero-width range is an insertion).
   * Edits are non-overlapping byte ranges computed by the extractor
   * (theorem proofs -> ":= sorry", by-blocks in def values -> "sorry"). */
  function applyEdits(bytes, start, end, edits) {
    if (!edits || edits.length === 0) return decodeSlice(bytes, start, end);
    var sorted = edits.slice().sort(function (a, b) { return a[0] - b[0]; });
    var out = "";
    var cursor = start;
    for (var i = 0; i < sorted.length; i++) {
      out += decodeSlice(bytes, cursor, sorted[i][0]) + sorted[i][2];
      cursor = sorted[i][1];
    }
    return out + decodeSlice(bytes, cursor, end);
  }

  /* ----- shard indexes ----------------------------------------------------------- */

  /* Dependencies to follow for a node: an `alias` keeps its body verbatim,
   * so it follows full deps despite its theorem kind (LML's isAlias rule);
   * theorem/lemma proofs become `sorry`, so only statement deps (`tdeps`)
   * are needed; everything else keeps its body and follows full deps. */
  function declDeps(node) {
    if (node.alias) return node.deps;
    return isProofKind(node.kind) && node.tdeps ? node.tdeps : node.deps;
  }

  /* Index the shard's command tables for the notation-usage closure:
   * declToKinds[declId] -> notation kind names its command's source uses
   * (LML's `declUsedNotations`), and kindEntries[kind] -> the notation
   * context entries defining that kind (matched via `kn`). */
  function notationIndex(shard) {
    var declToKinds = {};
    var kindEntries = {};
    var moduleData = shard.moduleData || [];
    for (var m = 0; m < moduleData.length; m++) {
      var commands = moduleData[m].commands || [];
      for (var c = 0; c < commands.length; c++) {
        var entry = commands[c];
        if (entry.t === "d" && entry.un) {
          for (var i = 0; i < entry.d.length; i++) {
            declToKinds[entry.d[i]] = entry.un;
          }
        } else if (entry.t === "c" && entry.k === "nota" && entry.kn) {
          for (var k = 0; k < entry.kn.length; k++) {
            (kindEntries[entry.kn[k]] = kindEntries[entry.kn[k]] || [])
              .push({ module: m, entry: entry });
          }
        }
      }
    }
    return { declToKinds: declToKinds, kindEntries: kindEntries };
  }

  /* ----- dependency cone (with notation closure) ---------------------------------- */

  /* Walk the dependency closure from `seeds` into `state`; returns the ids
   * newly added by this walk. */
  function walkCone(shard, seeds, state) {
    var decls = shard.decls;
    var added = [];
    var stack = seeds.slice();
    while (stack.length > 0) {
      var id = stack.pop();
      var node = decls[id];
      if (!node || state.seen[id]) continue;
      state.seen[id] = true;
      state.included.push(id);
      added.push(id);
      var deps = declDeps(node) || [];
      for (var i = 0; i < deps.length; i++) stack.push(deps[i]);
    }
    return added;
  }

  /* The target's transitive closure plus the notation-usage closure (port
   * of the frontier loop at the end of LML's `writeAllExtractions`): a kept
   * declaration whose source uses a notation needs that notation's command
   * replayed, and the notation's expansion deps (`nd`) join the cone — whose
   * members may in turn use further notations, so iterate to fixpoint. */
  function coneInfo(shard, targetId) {
    var index = notationIndex(shard);
    var state = { seen: {}, included: [] };
    var neededKinds = {};
    var notationEntries = []; // [{module, entry}] in discovery order
    var frontier = walkCone(shard, [targetId], state);
    while (frontier.length > 0) {
      var next = [];
      for (var f = 0; f < frontier.length; f++) {
        var kinds = index.declToKinds[frontier[f]] || [];
        for (var k = 0; k < kinds.length; k++) {
          if (neededKinds[kinds[k]]) continue;
          neededKinds[kinds[k]] = true;
          var defs = index.kindEntries[kinds[k]] || [];
          for (var d = 0; d < defs.length; d++) {
            notationEntries.push(defs[d]);
            var expansionDeps = defs[d].entry.nd || [];
            next = next.concat(walkCone(shard, expansionDeps, state));
          }
        }
      }
      frontier = next;
    }
    var ids = state.included.slice().sort(function (a, b) { return a - b; });
    // Involved modules: those containing kept declaration commands or
    // needed notation entries (LML's `involved`, which requires a kept
    // declaration — notation commands are declaration entries there).
    var moduleSet = {};
    for (var i = 0; i < ids.length; i++) {
      moduleSet[shard.decls[ids[i]].module] = true;
    }
    for (var n = 0; n < notationEntries.length; n++) {
      moduleSet[notationEntries[n].module] = true;
    }
    return {
      ids: ids,
      seen: state.seen,
      neededKinds: neededKinds,
      moduleSet: moduleSet,
    };
  }

  /* Dependency cone for the minimal file: shard-local ids plus the module
   * indices whose raw sources `build` will need (callers prefetch these).
   * `missingHost` is retained for API compatibility; hosts are gone from
   * the data (generated declarations share their command's entry). */
  function coneIds(shard, targetId) {
    var info = coneInfo(shard, targetId);
    return {
      ids: info.ids,
      modules: Object.keys(info.moduleSet).map(Number),
      missingHost: [],
    };
  }

  /* ----- module ordering and imports ---------------------------------------------- */

  /* Project modules reachable from `moduleSet` through `moduleData.uses`
   * (same-project imports), as a set. */
  function usesClosure(shard, moduleSet) {
    var moduleData = shard.moduleData || [];
    var closed = {};
    var queue = [];
    for (var m in moduleSet) {
      if (moduleSet[m]) { closed[m] = true; queue.push(Number(m)); }
    }
    while (queue.length > 0) {
      var current = queue.pop();
      var uses = (moduleData[current] || {}).uses || [];
      for (var i = 0; i < uses.length; i++) {
        if (!closed[uses[i]]) {
          closed[uses[i]] = true;
          queue.push(uses[i]);
        }
      }
    }
    return closed;
  }

  /* Emission order for the involved modules: dependencies-first along the
   * import DAG. The topological walk runs over the full same-project import
   * closure (so two involved modules connected only through a non-involved
   * intermediary still order correctly — LML gets this for free from
   * `env.header.moduleNames`), then keeps the involved ones. */
  function orderInvolvedModules(shard, involvedSet) {
    var moduleData = shard.moduleData || [];
    var closed = usesClosure(shard, involvedSet);
    var closedList = Object.keys(closed).map(Number).sort(function (a, b) {
      return a - b;
    });
    var placed = {};
    var order = [];
    function place(moduleIndex, depth) {
      if (placed[moduleIndex] || depth > closedList.length) return;
      placed[moduleIndex] = true; // pre-mark: cycles fall back to index order
      var needs = (moduleData[moduleIndex] || {}).uses || [];
      for (var k = 0; k < needs.length; k++) place(needs[k], depth + 1);
      order.push(moduleIndex);
    }
    for (var i = 0; i < closedList.length; i++) place(closedList[i], 0);
    return order.filter(function (m) { return involvedSet[m]; });
  }

  /* Involved-module emission order for a cone (exported helper). */
  function moduleOrder(shard, ids) {
    var index = notationIndex(shard);
    var involved = {};
    var kinds = {};
    var i;
    for (i = 0; i < ids.length; i++) {
      involved[shard.decls[ids[i]].module] = true;
      var used = index.declToKinds[ids[i]] || [];
      for (var k = 0; k < used.length; k++) kinds[used[k]] = true;
    }
    for (var kind in kinds) {
      var defs = index.kindEntries[kind] || [];
      for (var d = 0; d < defs.length; d++) involved[defs[d].module] = true;
    }
    return orderInvolvedModules(shard, involved);
  }

  /* Port of LML's `externalImports`: because project modules are emitted
   * inline rather than imported, an external (Mathlib) dependency may only
   * be reachable *through* a project module, so walk the same-project
   * import graph transitively and union the external imports of every
   * reachable module (`moduleData.imports` holds exactly each module's
   * external frontier). */
  function externalImports(shard, involvedSet) {
    var moduleData = shard.moduleData || [];
    var closed = usesClosure(shard, involvedSet);
    var seen = {};
    var result = [];
    for (var m in closed) {
      var imports = (moduleData[m] || {}).imports || [];
      for (var i = 0; i < imports.length; i++) {
        if (!seen[imports[i]]) {
          seen[imports[i]] = true;
          result.push(imports[i]);
        }
      }
    }
    result.sort();
    return result.length > 0 ? result : ["Mathlib"];
  }

  /* ----- variable pruning (port of pruneVariable / binderBoundNames) -------------- */

  /* The local names a `variable` binder introduces, parsed from its source
   * text (port of LML's `binderBoundNames`): the identifiers before the
   * first `:` (so `(a b : T)` / `{a b : T}` / `[inst : T]` give `a b` /
   * `inst`), or — when there is no `:` and it is not an instance binder —
   * every identifier (so `{a b}` gives `a b`). */
  function binderBoundNames(binderSrc) {
    var s = binderSrc.replace(/^\s+/, "");
    var isInstance = s.charAt(0) === "[";
    var colon = s.indexOf(":");
    var beforeColon = colon === -1 ? (isInstance ? "" : s) : s.slice(0, colon);
    return beforeColon
      .split(/[\s(){}[\],⦃⦄]+/)
      .filter(function (w) { return w.length > 0; });
  }

  /* Port of LML's `pruneVariable`: re-renders a `variable` command,
   * dropping the binders that reference an *excluded* exposed declaration
   * (outside the target's closure, hence not emitted, so referencing it
   * would be an undefined name). An identifier counts as such a reference
   * if some in-scope namespace prefix turns it into an excluded name and it
   * is not a locally bound `variable` name. LML additionally skips
   * identifiers that already denote an external (Mathlib) constant
   * (`env.contains`); that guard needs the Lean environment and is
   * unavailable client-side, so a project declaration sharing its name
   * with the Mathlib constant a binder actually meant can over-drop that
   * binder here. Returns null when no binder survives. */
  function pruneVariable(entry, bytes, activePrefixes, excludedNames, boundVars) {
    var binders = entry.b || [];
    if (binders.length === 0) {
      return decodeSlice(bytes, entry.s, entry.e); // no decomposition: verbatim
    }
    function refsExcluded(ident) {
      if (boundVars[ident]) return false; // locally bound, not a global ref
      for (var p = 0; p < activePrefixes.length; p++) {
        var full = activePrefixes[p] === ""
          ? ident : activePrefixes[p] + "." + ident;
        if (excludedNames[full]) return true;
      }
      return false;
    }
    var keptTexts = [];
    for (var i = 0; i < binders.length; i++) {
      var idents = binders[i][2] || [];
      var drops = false;
      for (var j = 0; j < idents.length; j++) {
        if (refsExcluded(idents[j])) { drops = true; break; }
      }
      if (!drops) keptTexts.push(decodeSlice(bytes, binders[i][0], binders[i][1]));
    }
    if (keptTexts.length === 0) return null;
    return "variable " + keptTexts.join(" ");
  }

  /* ----- open-only trimming (port of restrictToTarget's openOnly logic) ----------- */

  /* Effective text of an `open` context entry: an `open NS (a b c)` is
   * trimmed to the listed identifiers that are the short name of a kept
   * declaration (or dropped entirely — null — when none are); keeping a
   * name unconditionally would otherwise reference a declaration this
   * target dropped, or even `NS` itself. Matching by short name only can
   * under-drop, never wrongly drop (a false positive keeps a harmless
   * extra name). Every other `open` form is kept verbatim. */
  function openEntryText(entry, bytes, keepShortNames) {
    var src = decodeSlice(bytes, entry.s, entry.e);
    if (!entry.on) return src;
    var idents = entry.on[1] || [];
    var kept = idents.filter(function (ident) {
      return keepShortNames[ident] === true;
    });
    if (kept.length === 0) return null;
    if (kept.length === idents.length) return src;
    return "open " + entry.on[0] + " (" + kept.join(" ") + ")";
  }

  /* ----- scope stripping and whitespace (ports of ScopeTag machinery) ------------- */

  /* Chunk tags, port of LML's `ScopeTag`:
   *   openSection   opens a strippable scope (`section`);
   *   openNamespace opens a `namespace X` scope (also strippable when it
   *                 ends up empty — the namespace stubs already declare it);
   *   close         `end` / `end X`;
   *   soft          `variable` / `open` lines: content that does not, on
   *                 its own, justify keeping its scope;
   *   hard          declarations and any other context command. */

  /* Port of LML's `stripEmptyScopes`: drops `section` / `namespace` scopes
   * whose content is only `soft` chunks (which are scoped to the dropped
   * block, hence safe to remove with it). A scope is kept iff it
   * transitively contains a `hard` chunk; matching opens/closes are tracked
   * on a stack so nesting stays balanced. */
  function stripEmptyScopes(items) {
    var stack = []; // {open, lines[], keep}
    var top = [];
    for (var i = 0; i < items.length; i++) {
      var tag = items[i].tag;
      var text = items[i].text;
      if (tag === "openSection" || tag === "openNamespace") {
        stack.push({ open: text, lines: [], keep: false });
      } else if (tag === "close") {
        if (stack.length === 0) {
          top.push(text); // unbalanced (shouldn't happen): emit verbatim
        } else {
          var scope = stack.pop();
          if (scope.keep) {
            var rendered = [scope.open].concat(scope.lines, [text]);
            if (stack.length === 0) {
              top = top.concat(rendered);
            } else {
              var parent = stack[stack.length - 1];
              parent.lines = parent.lines.concat(rendered);
              parent.keep = true;
            }
          }
          // else: drop the scope (open, soft lines, and close) entirely.
        }
      } else if (stack.length === 0) {
        top.push(text);
      } else {
        stack[stack.length - 1].lines.push(text);
        if (tag === "hard") stack[stack.length - 1].keep = true;
      }
    }
    // Flush any unclosed scopes verbatim (shouldn't happen).
    for (var s = 0; s < stack.length; s++) {
      top.push(stack[s].open);
      top = top.concat(stack[s].lines);
    }
    return top.join("");
  }

  /* Port of LML's `collapseBlankRuns`: collapse runs of two or more
   * consecutive blank lines into a single blank line. */
  function collapseBlankRuns(text) {
    var lines = text.split("\n");
    var out = [];
    for (var i = 0; i < lines.length; i++) {
      var blank = /^\s*$/.test(lines[i]);
      if (blank && out.length > 0 && /^\s*$/.test(out[out.length - 1])) continue;
      out.push(lines[i]);
    }
    return out.join("\n");
  }

  /* ----- namespace stubs (port of assembleTarget's nsStubs) ------------------------ */

  /* Every project namespace, taken as the proper dotted prefixes of the
   * exposed declaration names (LML derives them from the declarations'
   * name prefixes the same way). */
  function projectNamespaces(shard) {
    var namespaces = {};
    for (var d = 0; d < shard.decls.length; d++) {
      var parts = shard.decls[d].name.split(".");
      var prefix = "";
      for (var p = 0; p < parts.length - 1; p++) {
        prefix = prefix === "" ? parts[p] : prefix + "." + parts[p];
        namespaces[prefix] = true;
      }
    }
    return namespaces;
  }

  /* ----- assembly (port of assembleTarget) ----------------------------------------- */

  /* Assemble the minimal file.
   *   shard:    the project shard JSON.
   *   sources:  module index -> raw source bytes (Uint8Array or Buffer).
   *   targetId: shard-local declaration id.
   * Returns {pending: [moduleIndex…]} when required sources are missing. */
  function build(shard, sources, targetId) {
    var decls = shard.decls;
    var moduleData = shard.moduleData || [];
    var info = coneInfo(shard, targetId);
    var order = orderInvolvedModules(shard, info.moduleSet);

    var pending = order.filter(function (m) { return sources[m] === undefined; });
    if (pending.length > 0) return { pending: pending };

    // Kept declarations' short (last-component) names, for open-only
    // trimming (LML's keepShortNames in restrictToTarget).
    var keepShortNames = {};
    var i;
    for (i = 0; i < info.ids.length; i++) {
      var parts = decls[info.ids[i]].name.split(".");
      keepShortNames[parts[parts.length - 1]] = true;
    }
    // Exposed declarations *not* emitted in this file: a `variable` binder
    // referencing one would reference an undefined name (LML's
    // excludedNames).
    var excludedNames = {};
    for (var d = 0; d < decls.length; d++) {
      if (!info.seen[d]) excludedNames[decls[d].name] = true;
    }
    // All names bound by `variable` binders across the involved modules:
    // these are local, so an identifier matching one is not a reference to
    // a same-named global declaration (LML's boundVars).
    var boundVars = {};
    for (i = 0; i < order.length; i++) {
      var commandsScan = moduleData[order[i]].commands || [];
      for (var c = 0; c < commandsScan.length; c++) {
        var scanEntry = commandsScan[c];
        if (scanEntry.t !== "c" || scanEntry.k !== "var") continue;
        var binders = scanEntry.b || [];
        for (var b = 0; b < binders.length; b++) {
          var text = decodeSlice(
            sources[order[i]], binders[b][0], binders[b][1]);
          var names = binderBoundNames(text);
          for (var n = 0; n < names.length; n++) boundVars[names[n]] = true;
        }
      }
    }

    // Project namespaces entered (`namespace X`, via its fully qualified
    // `q`) or opened (`open` tokens naming a project namespace) across the
    // involved modules, in first-appearance order: existence stubs are
    // emitted up front since an `open Foo` may precede the `namespace Foo`
    // that (re)creates `Foo` here (LML's nsStubs).
    var knownNamespaces = projectNamespaces(shard);
    var stubSeen = {};
    var stubs = [];
    function addStub(namespaceName) {
      if (!stubSeen[namespaceName]) {
        stubSeen[namespaceName] = true;
        stubs.push(namespaceName);
      }
    }
    for (i = 0; i < order.length; i++) {
      var stubCommands = moduleData[order[i]].commands || [];
      for (var sc = 0; sc < stubCommands.length; sc++) {
        var stubEntry = stubCommands[sc];
        if (stubEntry.t !== "c") continue;
        if (stubEntry.k === "ns" && stubEntry.q) {
          addStub(stubEntry.q);
        } else if (stubEntry.k === "open") {
          var openText = openEntryText(
            stubEntry, sources[order[i]], keepShortNames);
          if (openText === null) continue;
          var openTokens = openText.replace(/\n/g, " ").split(" ");
          for (var ot = 0; ot < openTokens.length; ot++) {
            if (knownNamespaces[openTokens[ot]]) addStub(openTokens[ot]);
          }
        }
      }
    }

    var target = decls[targetId];
    var importList = externalImports(shard, info.moduleSet);

    var out = [];
    out.push("/- Minimal Lean file for `" + target.name + "`.");
    out.push("Extracted from the Lean Pool project `" + shard.project
      + "` (commit " + String(shard.commit || "main").slice(0, 12) + ").");
    out.push("Definitions keep their bodies; theorem proofs are replaced by"
      + " `sorry`.");
    out.push("Auto-generated by the Lean Pool exposition — may need minor"
      + " adjustments. -/");
    out.push("");
    for (i = 0; i < importList.length; i++) out.push("import " + importList[i]);
    out.push("");
    // Replayed notation/macro commands may mention declarations that appear
    // later in the file; defer their right-hand-side resolution to use
    // sites (as in LML), and silence linters on the sorried bodies.
    out.push("set_option quotPrecheck false");
    out.push("set_option linter.all false");
    out.push("");
    if (stubs.length > 0) {
      out.push("-- Namespace stubs (so later `open`s resolve).");
      for (i = 0; i < stubs.length; i++) {
        out.push("namespace " + stubs[i]);
        out.push("end " + stubs[i]);
      }
      out.push("");
    }
    var header = out.join("\n") + "\n";

    // Per-module tagged chunks (port of assembleTarget's items loop).
    // activePrefixes accumulates across modules and is never popped — an
    // over-approximation of scope; pruning only matches exact excluded
    // names against it ("" is LML's Name.anonymous root).
    var items = [];
    var activePrefixes = [""];
    var emittedModules = 0;
    for (i = 0; i < order.length; i++) {
      var moduleIndex = order[i];
      var bytes = sources[moduleIndex];
      var commands = moduleData[moduleIndex].commands || [];
      emittedModules += 1;
      items.push({ tag: "hard",
        text: "\n-- ═══ " + shard.modules[moduleIndex] + " ═══\n" });
      // Wrap each module's replayed content in its own `section` so its
      // `open`s stay local to it (as in the original project) instead of
      // piling up across modules — repeated `open Foo`s can make an
      // unqualified name ambiguous through redundant open-paths.
      items.push({ tag: "openSection", text: "section\n" });
      for (c = 0; c < commands.length; c++) {
        var entry = commands[c];
        if (entry.t === "d") {
          // restrictToTarget: emit iff the command defines a kept
          // declaration (any of its ids — mutual blocks and generated
          // instances share one command).
          var keep = false;
          for (var kd = 0; kd < entry.d.length; kd++) {
            if (info.seen[entry.d[kd]]) { keep = true; break; }
          }
          if (!keep) continue;
          items.push({ tag: "hard",
            text: "\n" + applyEdits(bytes, entry.s, entry.e, entry.ed)
              + "\n\n" });
        } else if (entry.k === "ns") {
          // Track the namespace as spelled (LML pushes nsName?, the
          // possibly-relative spelling, for variable pruning).
          if (entry.ns) activePrefixes.push(entry.ns);
          // `namespace A.B` opens one scope per dotted component; emit
          // extra empty opens so `end A.B` / `end B` + `end A` rebalance.
          var nsComponents = entry.ns ? entry.ns.split(".").length : 1;
          items.push({ tag: "openNamespace",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
          for (var nc = 1; nc < nsComponents; nc++) {
            items.push({ tag: "openNamespace", text: "" });
          }
        } else if (entry.k === "sec") {
          items.push({ tag: "openSection",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
        } else if (entry.k === "end") {
          // `end A.B` closes one scope per dotted component; a bare `end`
          // closes one. Only the last close carries the text.
          var endComponents = entry.ns ? entry.ns.split(".").length : 1;
          for (var ec = 1; ec < endComponents; ec++) {
            items.push({ tag: "close", text: "" });
          }
          items.push({ tag: "close",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
        } else if (entry.k === "open") {
          var effective = openEntryText(entry, bytes, keepShortNames);
          if (effective === null) continue; // open-only with nothing kept
          // Every token after `open`/`scoped` may name a namespace brought
          // into scope; LML pushes all tokens (keywords included) as an
          // over-approximation, which at worst over-drops via exact-name
          // matches that keywords can never produce.
          var tokens = effective.replace(/\n/g, " ").split(" ");
          for (var t = 0; t < tokens.length; t++) {
            if (tokens[t] !== "") activePrefixes.push(tokens[t]);
          }
          items.push({ tag: "soft", text: effective + "\n" });
        } else if (entry.k === "var") {
          var pruned = pruneVariable(
            entry, bytes, activePrefixes, excludedNames, boundVars);
          if (pruned !== null) items.push({ tag: "soft", text: pruned + "\n" });
        } else if (entry.k === "nota") {
          if (entry.kn) {
            // Defines pool notation kinds: replayed iff the cone uses one
            // (in LML these are declaration entries filtered by the
            // notation closure).
            var needed = false;
            for (var nk = 0; nk < entry.kn.length; nk++) {
              if (info.neededKinds[entry.kn[nk]]) { needed = true; break; }
            }
            if (!needed) continue;
            items.push({ tag: "hard",
              text: "\n" + decodeSlice(bytes, entry.s, entry.e) + "\n\n" });
          } else {
            // macro_rules / elab_rules /…: plain context in LML, replayed
            // unconditionally.
            items.push({ tag: "hard",
              text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
          }
        } else {
          // "opt", "univ" (and anything future): hard context, verbatim.
          items.push({ tag: "hard",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
        }
      }
      items.push({ tag: "close", text: "end\n" });
    }

    var textOut = collapseBlankRuns(header + stripEmptyScopes(items));
    return {
      text: textOut.replace(/\s+$/, "") + "\n",
      declarationCount: info.ids.length,
      moduleCount: emittedModules,
      missingHost: [], // hosts are gone from the data; kept for callers
    };
  }

  var api = { build: build, coneIds: coneIds, moduleOrder: moduleOrder };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  if (root) root.ExpoMinimal = api;
})(typeof window !== "undefined" ? window : null);
