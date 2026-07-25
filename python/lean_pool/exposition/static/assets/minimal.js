/* Minimal Lean file builder for the Lean Pool exposition.
 *
 * Pure logic, no DOM: exposed as window.ExpoMinimal so graph.js (browser)
 * and the validation harness (node) share the exact same code paths.
 *
 * Port of LMLExposition's assembly phases (Extract.lean, Rémy Degenne,
 * after Matthew Ballard's EmitStandalone.lean): external-import closure
 * (`externalImports`), scope-tagged emission with empty-scope stripping
 * (`ScopeTag` / `stripEmptyScopes`), blank-line collapsing
 * (`collapseBlankRuns`), namespace stubs (`nsStubs`), open-only trimming
 * (`restrictToTarget`). The per-command classification (LML's phase 1)
 * happens ahead of time in the extractor; each shard module carries a
 * `commands` table whose positions are UTF-8 BYTE offsets into the raw
 * module source, so `sources` maps module index -> byte array
 * (Uint8Array in the browser, Buffer in node) and every slice is decoded
 * with TextDecoder after byte-slicing.
 *
 * Two deliberate departures from LML, driven by whole-pool validation:
 *
 * - `variable` commands are never pruned (LML's `pruneVariable`): dropping
 *   a binder silently changes every later signature. Instead binder
 *   references to exposed declarations outside the cone PULL those
 *   declarations in, and assembly runs again (at most three extra passes).
 * - Notation/syntax machinery replays wholesale: every `nota` entry of an
 *   involved module is emitted, and any same-project import-closure module
 *   that defines syntax is included wholesale (all its declarations join
 *   the cone) — macro_rules/elab implementations only work together with
 *   the syntax they serve, which no per-declaration signal captures.
 *
 * Command-table entries (see SCHEMA.md):
 *   decl    {t:"d", s, e, d:[declIds], ed:[[s,e,repl],…]?, un:[kind…]?,
 *            sd:[declIds]?}
 *   context {t:"c", s, e, k:"ns"|"end"|"open"|"var"|"sec"|"opt"|"univ"|
 *            "nota", ns?, q?, b:[[s,e,[ident…]],…]?, on:[ns,[ident…]]?,
 *            kn:[kind…]?, nd:[declIds]?}
 * Non-exposed declarations have no entry (holes, like LML's `skip`).
 * `sd` lists syntactic references from the command's kept source text
 * (simp lists, reducible-inlined constants) that never surface in the
 * elaborated dependencies; they are followed only when the body is
 * actually emitted.
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

  /* Identifier-ish tokens of a piece of Lean source text. */
  function identTokens(text) {
    return text.match(/[A-Za-z_À-￿][\w.'À-￿]*/g) || [];
  }

  /* ----- shard indexes ----------------------------------------------------------- */

  /* True when a node's body (value/proof) is emitted verbatim: an `alias`
   * keeps its body despite its theorem kind (LML's isAlias rule), and every
   * non-theorem keeps its body; theorem/lemma proofs become `sorry`. */
  function bodyEmitted(node) {
    return node.alias === true || !isProofKind(node.kind);
  }

  /* Dependencies to follow for a node: statement-only deps (`tdeps`) when
   * the proof is sorried, full deps when the body is emitted. */
  function declDeps(node) {
    if (bodyEmitted(node)) return node.deps;
    return node.tdeps || node.deps;
  }

  /* Index the shard's command tables:
   *   declToKinds[declId]     -> notation kind names its command's source
   *                              uses (LML's `declUsedNotations`);
   *   kindEntries[kind]       -> the notation context entries defining that
   *                              kind (matched via `kn`);
   *   declToSyntactic[declId] -> its command's `sd` ids: syntactic
   *                              references from the kept source text (simp
   *                              lists, reducible-inlined constants) that
   *                              elaborated deps miss — followed only for
   *                              nodes whose body is emitted. */
  function commandIndex(shard) {
    var declToKinds = {};
    var kindEntries = {};
    var declToSyntactic = {};
    var moduleData = shard.moduleData || [];
    for (var m = 0; m < moduleData.length; m++) {
      var commands = moduleData[m].commands || [];
      for (var c = 0; c < commands.length; c++) {
        var entry = commands[c];
        if (entry.t === "d") {
          for (var i = 0; i < entry.d.length; i++) {
            if (entry.un) declToKinds[entry.d[i]] = entry.un;
            if (entry.sd) declToSyntactic[entry.d[i]] = entry.sd;
          }
        } else if (entry.t === "c" && entry.k === "nota" && entry.kn) {
          for (var k = 0; k < entry.kn.length; k++) {
            (kindEntries[entry.kn[k]] = kindEntries[entry.kn[k]] || [])
              .push({ module: m, entry: entry });
          }
        }
      }
    }
    return {
      declToKinds: declToKinds,
      kindEntries: kindEntries,
      declToSyntactic: declToSyntactic,
    };
  }

  /* Name-resolution index over the shard's exposed declaration names
   * (the pre-port "strict matcher" semantics):
   *   exact[name]   -> ids with exactly that (display) name;
   *   strict[token] -> ids whose name the token denotes: the full name, or
   *                    a dotted suffix at a component boundary
   *                    (`DeMorgan.verum` ~ `LO.DeMorgan.verum`); bare
   *                    single-component tokens only match single-component
   *                    names, since matching them against last components
   *                    would misfire on Mathlib homonyms. Over-matching
   *                    only grows the cone. */
  function nameIndex(shard) {
    var exact = {};
    var strict = {};
    function record(map, key, id) {
      (map[key] = map[key] || []).push(id);
    }
    for (var d = 0; d < shard.decls.length; d++) {
      var parts = shard.decls[d].name.split(".");
      record(exact, shard.decls[d].name, d);
      for (var p = 0; p < parts.length; p++) {
        if (p === 0 || p < parts.length - 1) {
          record(strict, parts.slice(p).join("."), d);
        }
      }
    }
    return { exact: exact, strict: strict };
  }

  /* Shard ids an identifier token may refer to: strict-matcher hits plus
   * exact hits after qualifying with each active namespace prefix. */
  function resolveToken(token, names, activePrefixes) {
    var ids = (names.strict[token] || []).slice();
    for (var p = 0; p < activePrefixes.length; p++) {
      if (activePrefixes[p] === "") continue;
      var qualified = names.exact[activePrefixes[p] + "." + token];
      if (qualified) ids = ids.concat(qualified);
    }
    return ids;
  }

  /* Reverse instance index: declId -> instances whose dependencies include
   * it. Ordinary cone members carry the instances they use inside their
   * elaborated deps, but a declaration pulled in for a *source-only*
   * reference (a variable binder's type, a notation body) never got
   * elaborated, so the instances its type application needs (e.g.
   * `PartialOrder Hollom` for a binder `{C : Set Hollom}`) must be pulled
   * by association: every project instance mentioning the declaration. */
  function instanceIndex(shard) {
    var instancesOf = {};
    for (var d = 0; d < shard.decls.length; d++) {
      if (shard.decls[d].kind !== "instance") continue;
      var deps = shard.decls[d].deps || [];
      for (var i = 0; i < deps.length; i++) {
        (instancesOf[deps[i]] = instancesOf[deps[i]] || []).push(d);
      }
    }
    return instancesOf;
  }

  /* ----- dependency cone --------------------------------------------------------- */

  /* Walk the dependency closure from `seeds` into `state`; returns the ids
   * newly added by this walk. Nodes whose body is emitted additionally pull
   * their command's syntactic references (`sd`) — sorried theorems do not,
   * since the text that mentioned them is replaced by `sorry`. */
  function walkCone(shard, seeds, state, index) {
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
      var i;
      for (i = 0; i < deps.length; i++) stack.push(deps[i]);
      if (bodyEmitted(node)) {
        var syntactic = index.declToSyntactic[id] || [];
        for (i = 0; i < syntactic.length; i++) stack.push(syntactic[i]);
      }
    }
    return added;
  }

  /* Seeds for a wholesale-included module: every declaration it exposes
   * plus its notations' expansion deps. */
  function wholesaleSeeds(commands) {
    var seeds = [];
    for (var c = 0; c < commands.length; c++) {
      var entry = commands[c];
      if (entry.t === "d") seeds = seeds.concat(entry.d);
      else if (entry.k === "nota" && entry.nd) seeds = seeds.concat(entry.nd);
    }
    return seeds;
  }

  function hasNotationEntry(commands) {
    for (var c = 0; c < commands.length; c++) {
      if (commands[c].t === "c" && commands[c].k === "nota") return true;
    }
    return false;
  }

  /* The target's transitive closure (from the target plus `extraSeeds`,
   * the binder/notation references discovered by earlier assembly passes)
   * plus two source-level closures:
   *
   * 1. Notation usage (port of the frontier loop at the end of LML's
   *    `writeAllExtractions`): a kept declaration whose source uses a
   *    notation (`un`) pulls that notation's module and expansion deps
   *    (`nd`) into the cone, iterated to fixpoint.
   * 2. Wholesale syntax-module inclusion: any module in the involved
   *    modules' same-project import closure that defines syntax machinery
   *    (`nota` entries: notation, syntax, declare_syntax_cat, macro/elab
   *    rules, register_simp_attr, …) but is not yet involved is included
   *    wholesale — all its declarations join the cone. Tactic
   *    implementations and registrations only work together with the
   *    syntax they serve, which no per-declaration signal captures. */
  function coneInfo(shard, targetId, extraSeeds) {
    var index = commandIndex(shard);
    var decls = shard.decls;
    var moduleData = shard.moduleData || [];
    var state = { seen: {}, included: [] };
    var seenKinds = {};
    var notationModules = {};
    var wholesale = {};
    var pendingIds = walkCone(
      shard, [targetId].concat(extraSeeds || []), state, index);
    for (;;) {
      // Notation-usage fixpoint over the newly added declarations.
      while (pendingIds.length > 0) {
        var next = [];
        for (var f = 0; f < pendingIds.length; f++) {
          var kinds = index.declToKinds[pendingIds[f]] || [];
          for (var k = 0; k < kinds.length; k++) {
            if (seenKinds[kinds[k]]) continue;
            seenKinds[kinds[k]] = true;
            var defs = index.kindEntries[kinds[k]] || [];
            for (var d = 0; d < defs.length; d++) {
              notationModules[defs[d].module] = true;
              var expansionDeps = defs[d].entry.nd || [];
              next = next.concat(walkCone(shard, expansionDeps, state, index));
            }
          }
        }
        pendingIds = next;
      }
      // Involved modules so far: kept declaration commands, used-notation
      // modules, and previously wholesale-included modules.
      var moduleSet = {};
      var i;
      for (i = 0; i < state.included.length; i++) {
        moduleSet[decls[state.included[i]].module] = true;
      }
      for (var nm in notationModules) moduleSet[nm] = true;
      for (var wm in wholesale) moduleSet[wm] = true;
      // Wholesale scan over the same-project import closure.
      var closed = usesClosure(shard, moduleSet);
      var seeds = [];
      for (var cm in closed) {
        if (moduleSet[cm]) continue;
        var commands = (moduleData[cm] || {}).commands || [];
        if (!hasNotationEntry(commands)) continue;
        wholesale[cm] = true;
        seeds = seeds.concat(wholesaleSeeds(commands));
      }
      if (seeds.length === 0) {
        return {
          ids: state.included.slice().sort(function (a, b) { return a - b; }),
          seen: state.seen,
          moduleSet: moduleSet,
        };
      }
      pendingIds = walkCone(shard, seeds, state, index);
    }
  }

  /* Dependency cone for the minimal file: shard-local ids plus the module
   * indices whose raw sources `build` will need (callers prefetch these;
   * later assembly passes may still request more via {pending}).
   * `missingHost` is retained for API compatibility; hosts are gone from
   * the data (generated declarations share their command's entry). */
  function coneIds(shard, targetId) {
    var info = coneInfo(shard, targetId, []);
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
   * import DAG, so wholesale syntax modules replay before the modules that
   * use them. The topological walk runs over the full same-project import
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

  /* Involved-module emission order for a cone (exported helper): the ids'
   * modules, the modules defining notations they use, and — matching
   * coneInfo's wholesale rule — syntax-defining modules reachable through
   * same-project imports. */
  function moduleOrder(shard, ids) {
    var index = commandIndex(shard);
    var moduleData = shard.moduleData || [];
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
    for (;;) {
      var closed = usesClosure(shard, involved);
      var grew = false;
      for (var cm in closed) {
        if (involved[cm]) continue;
        if (hasNotationEntry((moduleData[cm] || {}).commands || [])) {
          involved[cm] = true;
          grew = true;
        }
      }
      if (!grew) break;
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

  /* ----- variable binders ---------------------------------------------------------- */

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

  /* ----- open-only trimming (port of restrictToTarget's openOnly logic) ----------- */

  /* Effective text of an `open` context entry: an `open NS (a b c)` is
   * trimmed to the listed identifiers that are the short name of a kept
   * declaration (or dropped entirely — null — when none are); keeping a
   * name unconditionally would otherwise reference a declaration this
   * target dropped. Matching by short name only can under-drop, never
   * wrongly drop. Every other `open` form is kept verbatim. */
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

  /* ----- registration machinery stripping ------------------------------------------ */

  var REGISTRATION_PATTERN =
    /^\s*(register_simp_attr|register_label_attr|declare_aesop_rule_sets)\b\s*(?:\[([^\]]*)\]|([A-Za-z_À-￿][\w'À-￿]*))?/m;

  /* Attribute names registered by import-time-only commands found in the
   * given module sources (`register_simp_attr foo`, `register_label_attr`,
   * `declare_aesop_rule_sets [Bar]`). Such registrations run in
   * initializers, so replaying them in a single file can never make the
   * name usable — the commands are dropped and references to the names
   * stripped instead. Scans whole sources because rule-set declarations
   * often live in modules without any command-table entry. */
  function collectRegisteredNames(order, sources) {
    var names = {};
    var pattern = new RegExp(REGISTRATION_PATTERN.source, "gm");
    for (var i = 0; i < order.length; i++) {
      var text = decodeSlice(sources[order[i]], 0, sources[order[i]].length);
      var match;
      while ((match = pattern.exec(text)) !== null) {
        if (match[3]) names[match[3]] = true;
        if (match[2]) {
          identTokens(match[2]).forEach(function (n) { names[n] = true; });
        }
      }
    }
    return names;
  }

  /* Attribute entries of a bracket group with the registered ones dropped:
   * null when nothing survives, the joined entry list otherwise. */
  function filterAttributeEntries(inner, registeredNames) {
    var entries = inner.split(",");
    var kept = entries.filter(function (entry) {
      var words = identTokens(entry.replace(/^[\s←↓↑\-!]+/, ""));
      var attr = words[0] === "local" || words[0] === "scoped"
        ? words[1] : words[0];
      return !(attr && registeredNames[attr] === true);
    });
    if (kept.length === entries.length) return inner;
    if (kept.length === 0) return null;
    return kept.join(",").trim();
  }

  /* Strip references to import-time registrations from emitted text:
   * `(rule_sets := [...])` groups are removed wholesale (a project rule
   * set can never exist in a single file; a Mathlib built-in one is merely
   * no longer pinned, which still elaborates), `@[...]` entries naming a
   * collected registered attribute are dropped (the whole group disappears
   * when empty), and bare occurrences of registered names inside bracket
   * lists (`simp only [simp_fixing, foo]`) are removed. */
  function stripRegistrations(text, registeredNames) {
    text = text.replace(/[ \t]*\(\s*rule_sets\s*:=\s*\[[^\]]*\]\s*\)/g, "");
    text = text.replace(/@\[([^[\]]*)\][ \t]*\n?/g, function (whole, inner) {
      var kept = filterAttributeEntries(inner, registeredNames);
      if (kept === inner) return whole;
      if (kept === null) return "";
      return "@[" + kept + "] ";
    });
    return text.replace(/\[([^[\]]*)\]/g, function (whole, inner) {
      if (inner.indexOf(",") === -1 && !registeredNames[inner.trim()]) {
        return whole;
      }
      var parts = inner.split(",");
      var kept = parts.filter(function (part) {
        return registeredNames[part.trim()] !== true;
      });
      if (kept.length === parts.length) return whole;
      return "[" + kept.join(",") + "]";
    });
  }

  /* ----- synthetic context recovery -------------------------------------------------
   *
   * The extractor's classifier skips some context-relevant commands
   * entirely (`attribute [...] targets`, `export NS (names)`, parser
   * aliases `syntax name := ...`); dropping them loses local instances
   * (`attribute [local instance] Classical.propDecidable`),
   * `match_pattern` attributes, exported short names, and named syntax
   * parsers. The raw module bytes are available here, so recover them:
   * scan for column-0 lines starting one of those commands, outside every
   * known command range, extending over unbalanced brackets. */

  var SYNTHETIC_LINE =
    /^(?:attribute[ \t]*\[|export[ \t]+[A-Za-z_À-￿]|syntax[ \t]+[A-Za-z_À-￿][\w'À-￿]*[ \t]*:=|initialize_simps_projections[ \t])/;
  var OPEN_IN_LINE = /^(?:scoped[ \t]+|local[ \t]+)?open[ \t].*[ \t]in[ \t]*$/;
  var MACHINERY_LINE =
    /^(?:syntax|notation3?|macro_rules|macro|elab_rules|elab|declare_syntax_cat|binder_predicate|attribute|export)\b/;

  function bracketBalance(text) {
    var depth = 0;
    for (var i = 0; i < text.length; i++) {
      var ch = text.charAt(i);
      if (ch === "(" || ch === "[") depth += 1;
      else if (ch === ")" || ch === "]") depth -= 1;
    }
    return depth;
  }

  function syntheticCommands(bytes, commands) {
    // Split into lines with byte offsets.
    var lines = [];
    var start = 0;
    for (var i = 0; i <= bytes.length; i++) {
      if (i === bytes.length || bytes[i] === 10) {
        lines.push({ s: start, e: i, text: decodeSlice(bytes, start, i) });
        start = i + 1;
      }
    }
    var sorted = commands.slice().sort(function (a, b) { return a.s - b.s; });
    var cmdIdx = 0;
    var synth = [];
    // Consume the command starting at line `at`: its line, unbalanced
    // brackets, and indented continuation lines. Returns the end line idx.
    function commandBlockEnd(at) {
      var depth = bracketBalance(lines[at].text);
      var last = at;
      while (last + 1 < lines.length) {
        var next = lines[last + 1].text;
        if (depth > 0 || /^[ \t]+\S/.test(next)) {
          depth += bracketBalance(next);
          last += 1;
        } else break;
      }
      return last;
    }
    for (var l = 0; l < lines.length; l++) {
      var line = lines[l];
      if (line.text === "") continue;
      while (cmdIdx < sorted.length && sorted[cmdIdx].e <= line.s) cmdIdx++;
      if (cmdIdx < sorted.length && sorted[cmdIdx].s <= line.s
          && line.s < sorted[cmdIdx].e) continue; // inside a known command
      if (SYNTHETIC_LINE.test(line.text)) {
        var last = commandBlockEnd(l);
        synth.push({ t: "c", k: "synth", s: line.s, e: lines[last].e });
        l = last;
      } else if (OPEN_IN_LINE.test(line.text)) {
        // `open X in` wrapping a syntax-machinery command is classified as
        // neither context nor declaration by the extractor — recover the
        // whole block (wrapper, optional doc comment, command).
        var probe = l + 1;
        if (probe < lines.length && /^\/--/.test(lines[probe].text)) {
          while (probe < lines.length && lines[probe].text.indexOf("-/") === -1) {
            probe += 1;
          }
          probe += 1;
        }
        if (probe < lines.length && MACHINERY_LINE.test(lines[probe].text)) {
          var blockEnd = commandBlockEnd(probe);
          synth.push({ t: "c", k: "synth", s: line.s, e: lines[blockEnd].e });
          l = blockEnd;
        }
      }
    }
    return synth;
  }

  /* ----- scope stripping and whitespace (ports of ScopeTag machinery) ------------- */

  /* Chunk tags, port of LML's `ScopeTag`:
   *   openSection   opens a strippable scope (`section`);
   *   openNamespace opens a `namespace X` scope (also strippable when it
   *                 ends up empty — the namespace stubs already declare it);
   *   close         `end` / `end X`;
   *   soft          `variable` / `open` lines: content that does not, on
   *                 its own, justify keeping its scope;
   *   hard          declarations and any other context command.
   * Chunks are {tag, text, refs?}; `refs` are candidate shard ids the
   * chunk's source references (variable binders, notation bodies). */

  /* Port of LML's `stripEmptyScopes`: drops `section` / `namespace` scopes
   * whose content is only `soft` chunks (which are scoped to the dropped
   * block, hence safe to remove with it). A scope is kept iff it
   * transitively contains a `hard` chunk. Returns the rendered text plus
   * the union of `refs` on every chunk that actually rendered — the
   * inclusion pass only chases references that survived stripping. */
  function stripEmptyScopes(items) {
    var stack = []; // {open, chunks[], keep}
    var top = [];
    for (var i = 0; i < items.length; i++) {
      var item = items[i];
      if (item.tag === "openSection" || item.tag === "openNamespace") {
        stack.push({ open: item, chunks: [], keep: false });
      } else if (item.tag === "close") {
        if (stack.length === 0) {
          top.push(item); // unbalanced (shouldn't happen): emit verbatim
        } else {
          var scope = stack.pop();
          if (scope.keep) {
            var rendered = [scope.open].concat(scope.chunks, [item]);
            if (stack.length === 0) {
              top = top.concat(rendered);
            } else {
              var parent = stack[stack.length - 1];
              parent.chunks = parent.chunks.concat(rendered);
              parent.keep = true;
            }
          }
          // else: drop the scope (open, soft chunks, and close) entirely.
        }
      } else if (stack.length === 0) {
        top.push(item);
      } else {
        stack[stack.length - 1].chunks.push(item);
        if (item.tag === "hard") stack[stack.length - 1].keep = true;
      }
    }
    // Flush any unclosed scopes verbatim (shouldn't happen).
    for (var s = 0; s < stack.length; s++) {
      top.push(stack[s].open);
      top = top.concat(stack[s].chunks);
    }
    var text = "";
    var refs = [];
    for (var t = 0; t < top.length; t++) {
      text += top[t].text;
      if (top[t].refs) refs = refs.concat(top[t].refs);
    }
    return { text: text, refs: refs };
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

  /* ----- namespace stubs ------------------------------------------------------------ */

  /* Lean keywords that must be guillemet-quoted when a namespace component
   * collides with them (`namespace «Prop»`). Quoting a name that did not
   * need it is always valid, so the list errs on the large side. */
  var LEAN_KEYWORDS = {
    Prop: 1, Type: 1, Sort: 1, in: 1, at: 1, do: 1, by: 1, fun: 1, let: 1,
    end: 1, open: 1, section: 1, namespace: 1, theorem: 1, def: 1,
    instance: 1, example: 1, variable: 1, universe: 1, axiom: 1,
    structure: 1, class: 1, inductive: 1, abbrev: 1, mutual: 1, match: 1,
    with: 1, deriving: 1, where: 1, extends: 1, if: 1, then: 1, else: 1,
    from: 1, import: 1, export: 1, notation: 1, macro: 1, syntax: 1,
    attribute: 1, include: 1, omit: 1, calc: 1, show: 1, have: 1,
    suffices: 1, set_option: 1,
  };

  function escapeNamespaceComponent(component) {
    if (component.charAt(0) === "«") return component;
    if (LEAN_KEYWORDS[component] === 1
        || !/^[A-Za-z_À-￿][\w'!?À-￿]*$/.test(component)) {
      return "«" + component + "»";
    }
    return component;
  }

  function escapeNamespacePath(path) {
    return path.split(".").map(escapeNamespaceComponent).join(".");
  }

  var OPEN_KEYWORDS = { scoped: true, hiding: true, renaming: true, in: true };

  /* Every project namespace, taken as the proper dotted prefixes of the
   * exposed declaration names (as in LML): needed to recognize lowercase
   * project namespaces (`open fromModuleCatOverMatrix`) that the
   * capitalized/dotted heuristic below misses. */
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

  /* Namespace-looking tokens of an `open` command's text: capitalized or
   * dotted identifiers (or known project namespaces of any case), with
   * parenthesized short-name lists stripped. Stubbing an already-existing
   * namespace (Mathlib's, or a structure's) is a no-op, so over-stubbing
   * is safe — under-stubbing leaves an `open` of a namespace nothing
   * re-creates, which is an error. */
  function namespaceTokens(openText, knownNamespaces) {
    var body = openText.replace(/\n/g, " ").replace(/\([^)]*\)/g, " ")
      .replace(/^\s*(?:scoped\s+|local\s+)?open\b/, "");
    var found = [];
    var tokens = body.split(/\s+/);
    for (var i = 0; i < tokens.length; i++) {
      var token = tokens[i];
      if (!token || OPEN_KEYWORDS[token] === true) continue;
      if (!/^[A-Za-z_À-￿][\w.'À-￿]*$/.test(token)) continue;
      if (!/^[A-ZÀ-￿]/.test(token) && token.indexOf(".") === -1
          && knownNamespaces[token] !== true) continue;
      found.push(token);
    }
    return found;
  }

  /* ----- assembly ------------------------------------------------------------------- */

  /* One assembly pass. Returns {pending} when required sources are
   * missing, else {text, declarationCount, moduleCount, newIds} where
   * `newIds` are exposed declarations referenced by surviving variable
   * binders / notation bodies but absent from the cone — the caller
   * extends the cone with them and reassembles. */
  function assemblePass(shard, sources, targetId, extraSeeds, names) {
    var decls = shard.decls;
    var moduleData = shard.moduleData || [];
    var info = coneInfo(shard, targetId, extraSeeds);
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
    // All names bound by `variable` binders across the involved modules:
    // an identifier matching one is a local, not a reference to a
    // same-named global declaration (LML's boundVars).
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
          var bound = binderBoundNames(text);
          for (var n = 0; n < bound.length; n++) boundVars[bound[n]] = true;
        }
      }
    }
    // Import-time-only registrations across the involved modules.
    var registeredNames = collectRegisteredNames(order, sources);

    var target = decls[targetId];
    var importList = externalImports(shard, info.moduleSet);

    // Candidate reference ids for a list of identifier tokens.
    function referenceIds(tokens, activePrefixes) {
      var refs = [];
      for (var t = 0; t < tokens.length; t++) {
        if (boundVars[tokens[t]]) continue;
        refs = refs.concat(resolveToken(tokens[t], names, activePrefixes));
      }
      return refs;
    }

    // ----- namespace stubs (port of assembleTarget's nsStubs, broadened) -----
    // Entered namespaces (fully qualified `q`) plus every namespace-looking
    // token of kept `open` commands and of `open … in` declaration prefix
    // lines.
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
        if (stubEntry.t === "d") {
          // `open Foo in` prefix lines inside declaration commands.
          var declSlice = decodeSlice(
            sources[order[i]], stubEntry.s, stubEntry.e);
          var prefixLines = declSlice.match(
            /^[ \t]*(?:scoped\s+|local\s+)?open\s[^\n]*\sin[ \t]*$/gm) || [];
          for (var pm = 0; pm < prefixLines.length; pm++) {
            namespaceTokens(prefixLines[pm].replace(/\sin[ \t]*$/, ""),
              knownNamespaces).forEach(addStub);
          }
        } else if (stubEntry.k === "ns" && stubEntry.q) {
          addStub(stubEntry.q);
        } else if (stubEntry.k === "open") {
          var openText = openEntryText(
            stubEntry, sources[order[i]], keepShortNames);
          if (openText !== null) {
            namespaceTokens(openText, knownNamespaces).forEach(addStub);
          }
        }
      }
    }

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
        out.push("namespace " + escapeNamespacePath(stubs[i]));
        out.push("end " + escapeNamespacePath(stubs[i]));
      }
      out.push("");
    }
    var header = out.join("\n") + "\n";

    // Per-module tagged chunks (port of assembleTarget's items loop).
    // activePrefixes accumulates across modules and is never popped — an
    // over-approximation of scope used only for name resolution ("" is
    // LML's Name.anonymous root).
    var items = [];
    var activePrefixes = [""];
    var emittedModules = 0;
    for (i = 0; i < order.length; i++) {
      var moduleIndex = order[i];
      var bytes = sources[moduleIndex];
      var commands = (moduleData[moduleIndex].commands || [])
        .concat(syntheticCommands(bytes, moduleData[moduleIndex].commands || []))
        .sort(function (a, b) { return a.s - b.s; });
      emittedModules += 1;
      items.push({ tag: "hard",
        text: "\n-- ═══ " + shard.modules[moduleIndex] + " ═══\n" });
      // Wrap each module's replayed content in its own `section` so its
      // `open`s stay local to it (as in the original project) instead of
      // piling up across modules — repeated `open Foo`s can make an
      // unqualified name ambiguous through redundant open-paths.
      items.push({ tag: "openSection", text: "section\n" });
      // Typed scope stack for `end` synthesis: one frame per open scope —
      // section frames (with the section name when present), one frame per
      // dotted namespace component. Reset per module.
      var scopeStack = [];
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
          var declBody = stripRegistrations(
            applyEdits(bytes, entry.s, entry.e, entry.ed), registeredNames);
          items.push({ tag: "hard", text: "\n" + declBody + "\n\n" });
        } else if (entry.k === "ns") {
          // Track the namespace for name resolution — as spelled, fully
          // qualified (`q`), and as the current nesting join (so a short
          // name inside `namespace A` + `namespace B` resolves against
          // `A.B.<name>`) — then open one synthesized scope per dotted
          // component so every scope has a self-contained open/close pair
          // no matter which inner scopes stripEmptyScopes later drops.
          if (entry.ns) {
            activePrefixes.push(entry.ns);
            if (entry.q && entry.q !== entry.ns) activePrefixes.push(entry.q);
            var nsComponents = entry.ns.split(".");
            for (var nc = 0; nc < nsComponents.length; nc++) {
              scopeStack.push({ section: false, name: nsComponents[nc] });
              items.push({ tag: "openNamespace",
                text: "namespace "
                  + escapeNamespaceComponent(nsComponents[nc]) + "\n" });
            }
            var nestingJoin = scopeStack
              .filter(function (fr) { return !fr.section && fr.name; })
              .map(function (fr) { return fr.name; })
              .join(".");
            if (nestingJoin !== entry.ns) activePrefixes.push(nestingJoin);
          } else {
            scopeStack.push({ section: false, name: null });
            items.push({ tag: "openNamespace",
              text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
          }
        } else if (entry.k === "sec") {
          var secText = decodeSlice(bytes, entry.s, entry.e);
          // Module-system scaffolding cannot appear in a plain single file:
          // reduce `@[expose] public section` / `public section` to a plain
          // `section` (keeps the scope balanced).
          if (/(?:^|\s)public\s+section/.test(secText)
              || /^\s*@\[expose\]/.test(secText)) {
            secText = "section";
          }
          // A named `section Foo` must close with `end Foo`: remember the
          // name for the synthesized close.
          var secMatch = secText.match(/section\s+([^\s]+)\s*$/);
          scopeStack.push({ section: true, name: secMatch ? secMatch[1] : null });
          items.push({ tag: "openSection", text: secText + "\n" });
        } else if (entry.k === "end") {
          // Never slice `end` text from the source: pop one typed frame per
          // dotted component (a bare `end` pops one) and synthesize each
          // frame's own close line, innermost first — `end A.B` becomes
          // `end B` + `end A`. Per-frame lines keep every open/close pair
          // intact when stripEmptyScopes drops an inner scope but keeps an
          // outer one.
          var popCount = entry.ns ? entry.ns.split(".").length : 1;
          for (var ec = 0; ec < popCount && scopeStack.length > 0; ec++) {
            var frame = scopeStack.pop();
            items.push({ tag: "close",
              text: frame.name
                ? "end " + escapeNamespaceComponent(frame.name) + "\n"
                : "end\n" });
          }
        } else if (entry.k === "open") {
          var effective = openEntryText(entry, bytes, keepShortNames);
          if (effective === null) continue; // open-only with nothing kept
          // Every token may name a namespace brought into scope (an
          // over-approximation, as in LML: only exact-name matches use it).
          var tokens = effective.replace(/\n/g, " ").split(" ");
          for (var t = 0; t < tokens.length; t++) {
            if (tokens[t] !== "") activePrefixes.push(tokens[t]);
          }
          // `open NS hiding a b` / `renaming a -> b` name declarations that
          // must exist: resolve and pull them like binder references.
          items.push({
            tag: "soft",
            text: effective + "\n",
            refs: referenceIds(identTokens(effective), activePrefixes),
          });
        } else if (entry.k === "var") {
          // Never prune binders (dropping one silently changes every later
          // signature); references to out-of-cone declarations are pulled
          // into the cone by the multi-pass caller instead (via refs).
          var varIdents = [];
          var varBinders = entry.b || [];
          for (var vb = 0; vb < varBinders.length; vb++) {
            varIdents = varIdents.concat(varBinders[vb][2] || []);
          }
          items.push({
            tag: "soft",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n",
            refs: referenceIds(varIdents, activePrefixes),
          });
        } else if (entry.k === "nota") {
          var notaText = decodeSlice(bytes, entry.s, entry.e);
          // Import-time-only registrations can never take effect inside a
          // single file: drop them (references are stripped instead).
          if (REGISTRATION_PATTERN.test(notaText)) continue;
          // Extractor quirk: a `declare_syntax_cat` slice can end right
          // after the keyword; recover the category name from `kn`.
          if (/declare_syntax_cat\s*$/.test(notaText)
              && entry.kn && entry.kn.length === 1) {
            notaText += " "
              + entry.kn[0].replace(/\.quot$/, "").split(".").pop();
          }
          notaText = stripRegistrations(notaText, registeredNames);
          // Replay ALL syntax machinery of involved modules: macro_rules /
          // elab_rules only work together with the syntax/categories they
          // extend, and quotPrecheck false defers unused right-hand sides.
          // Identifier tokens feed the inclusion pass so expansions'
          // helpers exist when the notation is actually used.
          items.push({
            tag: "hard",
            text: "\n" + notaText + "\n\n",
            refs: referenceIds(identTokens(notaText), activePrefixes),
          });
        } else if (entry.k === "synth") {
          // Recovered commands the extractor's classifier skipped:
          // `attribute [...] targets`, `export NS (names)`,
          // `syntax name := ...` (see syntheticCommands).
          // Remove `(rule_sets := [...])` groups FIRST so the attribute
          // bracket group has no nested brackets left to confuse parsing.
          var synthText = decodeSlice(bytes, entry.s, entry.e)
            .replace(/[ \t]*\(\s*rule_sets\s*:=\s*\[[^\]]*\]\s*\)/g, "");
          var attrMatch = synthText.match(/^attribute[ \t]*\[([^\]]*)\]([\s\S]*)$/);
          if (attrMatch) {
            var keptEntries = filterAttributeEntries(attrMatch[1], registeredNames);
            if (keptEntries === null) continue; // only registered attrs
            synthText = "attribute [" + keptEntries + "]" + attrMatch[2];
          }
          items.push({
            tag: "hard",
            text: synthText + "\n",
            refs: referenceIds(identTokens(synthText), activePrefixes),
          });
        } else {
          // "opt", "univ" (and anything future): hard context, verbatim.
          items.push({ tag: "hard",
            text: decodeSlice(bytes, entry.s, entry.e) + "\n" });
        }
      }
      // Close any scopes the source left open (defensive: module sources
      // are balanced) so the module wrapper's `end` pairs correctly.
      while (scopeStack.length > 0) {
        var leftover = scopeStack.pop();
        items.push({ tag: "close",
          text: leftover.name ? "end " + leftover.name + "\n" : "end\n" });
      }
      items.push({ tag: "close", text: "end\n" });
    }

    var body = stripEmptyScopes(items);
    var newIds = [];
    var newSeen = {};
    for (i = 0; i < body.refs.length; i++) {
      var ref = body.refs[i];
      if (!info.seen[ref] && !newSeen[ref]) {
        newSeen[ref] = true;
        newIds.push(ref);
      }
    }
    return {
      text: collapseBlankRuns(header + body.text).replace(/\s+$/, "") + "\n",
      declarationCount: info.ids.length,
      moduleCount: emittedModules,
      newIds: newIds,
    };
  }

  /* Assemble the minimal file.
   *   shard:    the project shard JSON.
   *   sources:  module index -> raw source bytes (Uint8Array or Buffer).
   *   targetId: shard-local declaration id.
   * Returns {pending: [moduleIndex…]} when required sources are missing.
   * Runs up to three extra passes: references from surviving variable
   * binders / notation bodies extend the cone, then assembly reruns. */
  function build(shard, sources, targetId) {
    var names = nameIndex(shard);
    var instancesOf = instanceIndex(shard);
    var extraSeeds = [];
    var result = null;
    for (var pass = 0; pass < 8; pass++) {
      result = assemblePass(shard, sources, targetId, extraSeeds, names);
      if (result.pending) return { pending: result.pending };
      if (result.newIds.length === 0) break;
      // Source-only references never got elaborated, so pull the project
      // instances mentioning them along (their types need those to
      // re-elaborate here).
      var expanded = result.newIds.slice();
      for (var n = 0; n < result.newIds.length; n++) {
        expanded = expanded.concat(instancesOf[result.newIds[n]] || []);
      }
      extraSeeds = extraSeeds.concat(expanded);
    }
    return {
      text: result.text,
      declarationCount: result.declarationCount,
      moduleCount: result.moduleCount,
      missingHost: [], // hosts are gone from the data; kept for callers
    };
  }

  var api = { build: build, coneIds: coneIds, moduleOrder: moduleOrder };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  if (root) root.ExpoMinimal = api;
})(typeof window !== "undefined" ? window : null);
