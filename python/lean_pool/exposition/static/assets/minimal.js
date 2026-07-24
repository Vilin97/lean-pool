/* Minimal Lean file builder for the Lean Pool exposition.
 *
 * Pure logic, no DOM: exposed as window.ExpoMinimal so graph.js (browser)
 * and the validation harness (node) share the exact same code paths.
 *
 * Given a project shard, the raw text of the involved modules, and a target
 * declaration id, `build` assembles a standalone .lean file: the union of
 * the involved modules' external imports, then each module replayed in
 * original order — top-level context commands (namespace/section/open/
 * variable/notation/...) kept verbatim, needed definitions copied verbatim,
 * needed theorems cut at their statement boundary with `:= sorry` — the
 * whole module wrapped in a `section` so its `variable`s stay local.
 *
 * The dependency cone follows statement-only deps (`tdeps`) through
 * theorems (their proofs become `sorry`) and full deps through everything
 * else (bodies are kept). Generated declarations (deriving/@[simps]/...)
 * are represented by their host declaration's source.
 */
(function (root) {
  "use strict";

  var PROOF_KINDS = { theorem: true, lemma: true };

  function isProofKind(kind) {
    return PROOF_KINDS[kind] === true;
  }

  /* Walk the dependency closure from `seeds`, accumulating into
   * `state = {seen, included, missingHost}`; generated declarations are
   * replaced by their hosts. */
  function walkCone(shard, seeds, state) {
    var decls = shard.decls;
    var stack = seeds.slice();
    while (stack.length > 0) {
      var id = stack.pop();
      var node = decls[id];
      if (!node) continue;
      if (typeof node.host === "number") {
        id = node.host;
        node = decls[id];
        if (!node) continue;
      } else if (node.statement === "" && node.stmtEnd === undefined) {
        // Generated declaration without a source host: cannot be emitted.
        if (!state.seen["m" + id]) {
          state.seen["m" + id] = true;
          state.missingHost.push(id);
        }
        continue;
      }
      if (state.seen[id]) continue;
      state.seen[id] = true;
      state.included.push(id);
      var deps = declDeps(node);
      for (var i = 0; i < deps.length; i++) stack.push(deps[i]);
    }
  }

  /* Dependency cone for the minimal file. Returns shard-local ids, with
   * generated declarations replaced by their hosts. */
  function coneIds(shard, targetId) {
    var state = { seen: {}, included: [], missingHost: [] };
    walkCone(shard, [targetId], state);
    state.included.sort(function (a, b) { return a - b; });
    return { ids: state.included, missingHost: state.missingHost };
  }

  /* Dependencies to follow for a node. Theorems contribute statement-only
   * deps (their proofs become `sorry`) — EXCEPT mutual-block members
   * (span): the whole block is emitted verbatim, proofs included, so their
   * full dependencies are needed. */
  function declDeps(node) {
    if (node.span) return node.deps;
    return isProofKind(node.kind) && node.tdeps ? node.tdeps : node.deps;
  }

  /* Involved modules in emission order: the cone's modules closed under
   * same-project imports (`moduleData.uses` — pulls in notation-only files
   * whose context commands the cone's statements may rely on), ordered
   * dependencies-first along the import DAG; ties keep module index order. */
  function moduleOrder(shard, ids) {
    var decls = shard.decls;
    var moduleData = shard.moduleData || [];
    var involved = {};
    var queue = [];
    var i;
    for (i = 0; i < ids.length; i++) {
      var moduleIndex = decls[ids[i]].module;
      if (!involved[moduleIndex]) {
        involved[moduleIndex] = true;
        queue.push(moduleIndex);
      }
    }
    while (queue.length > 0) {
      var current = queue.pop();
      var uses = (moduleData[current] || {}).uses || [];
      for (var j = 0; j < uses.length; j++) {
        if (!involved[uses[j]]) {
          involved[uses[j]] = true;
          queue.push(uses[j]);
        }
      }
    }
    var moduleList = Object.keys(involved).map(Number).sort(function (a, b) {
      return a - b;
    });
    var placed = {};
    var order = [];
    function place(moduleIndex, depth) {
      if (placed[moduleIndex] || depth > moduleList.length) return;
      placed[moduleIndex] = true; // pre-mark: cycles fall back to index order
      var needs = ((moduleData[moduleIndex] || {}).uses || [])
        .filter(function (m) { return involved[m]; });
      for (var k = 0; k < needs.length; k++) place(needs[k], depth + 1);
      order.push(moduleIndex);
    }
    for (i = 0; i < moduleList.length; i++) place(moduleList[i], 0);
    return order;
  }

  /* Slice a UTF-16 string prefix of `codepoints` Unicode code points. */
  function codePointPrefix(line, codepoints) {
    var index = 0;
    var count = 0;
    while (index < line.length && count < codepoints) {
      var code = line.codePointAt(index);
      index += code > 0xffff ? 2 : 1;
      count += 1;
    }
    return line.slice(0, index);
  }

  function declText(node, lines) {
    var startLine = node.line;
    var endLine = node.endLine;
    var prefix = "";
    if (node.prefix) {
      // Drop `attribute [custom] X in` prefix lines whose attribute cannot
      // be replayed; keep open/set_option/variable prefixes.
      var prefixLines = node.prefix.split("\n").filter(function (line) {
        var attr = line.match(/^\s*attribute\s*\[([^\]]*)\]/);
        return !(attr && hasUnknownAttribute(attr[1]));
      });
      if (prefixLines.length > 0) prefix = prefixLines.join("\n") + "\n";
    }
    if (node.span) {
      startLine = node.span[0];
      endLine = node.span[1];
      prefix = "";
    } else if (isProofKind(node.kind) && node.stmtEnd) {
      var upto = lines.slice(startLine - 1, node.stmtEnd[0] - 1);
      var boundaryLine = lines[node.stmtEnd[0] - 1] || "";
      upto.push(codePointPrefix(boundaryLine, node.stmtEnd[1]));
      var statement = upto.join("\n").replace(/\s+$/, "");
      return sanitizeAttributes(prefix + statement) + " := sorry";
    }
    return sanitizeAttributes(
      prefix + lines.slice(startLine - 1, endLine).join("\n").replace(/\s+$/, ""));
  }

  /* Identifier-ish tokens of a command text (used for context pruning). */
  function identTokens(text) {
    return text.match(/[A-Za-z_À-￿][\w.'À-￿]*/g) || [];
  }

  /* Attributes whose registrations ship with Lean/Mathlib. An `attribute`
   * context using anything else (a project-registered attribute) cannot be
   * replayed, since the registering command is not a context. */
  var KNOWN_ATTRIBUTES = {
    simp: 1, instance: 1, ext: 1, norm_cast: 1, push_cast: 1, coe: 1,
    reducible: 1, semireducible: 1, irreducible: 1, inline: 1, specialize: 1,
    simps: 1, mono: 1, positivity: 1, gcongr: 1, fun_prop: 1,
    measurability: 1, continuity: 1, aesop: 1, refl: 1, symm: 1, trans: 1,
    congr: 1, to_additive: 1, default_instance: 1, match_pattern: 1,
    class: 1, induction_eliminator: 1, cases_eliminator: 1, elab_as_elim: 1,
    pp_nodot: 1, grind: 1, norm_num: 1, local: 1, scoped: 1, nolint: 1,
    deprecated: 1, simp_nf: 1, higher_order: 1,
  };

  /* Index the project's declaration names for token matching.
   * `strict` — full names plus dotted suffixes at component boundaries
   * (`DeMorgan.verum` ~ `LO.DeMorgan.verum`); bare single-component tokens
   * only match single-component names, since matching them against last
   * components would misfire on Mathlib homonyms. Used for pruning.
   * `loose` — additionally last components (`coprodTree_node` ~
   * `CK.coprodTree_node`). Used for tactic-reference closure, where the
   * bracket list is known to name lemmas. */
  function makeNameMatcher(shard) {
    var strict = {}; // token -> [decl ids]
    var loose = {};
    function record(map, key, id) {
      (map[key] = map[key] || []).push(id);
    }
    for (var d = 0; d < shard.decls.length; d++) {
      var parts = shard.decls[d].name.split(".");
      for (var p = 0; p < parts.length; p++) {
        var suffix = parts.slice(p).join(".");
        if (p === 0 || p < parts.length - 1) record(strict, suffix, d);
        record(loose, suffix, d);
      }
    }
    return { strict: strict, loose: loose };
  }

  /* Decide whether a context command survives into the minimal file.
   * - `variable`/`attribute` commands mentioning project declarations
   *   outside the cone are dropped (safe: a section variable actually used
   *   by an emitted declaration only mentions cone declarations — they
   *   appear in its statement's dependencies).
   * - `attribute` commands using non-builtin attribute names are dropped
   *   (their registration command cannot be replayed).
   * - `export NS (a b …)` is dropped when `NS.a` … resolve outside the
   *   cone. */
  /* Does an `@[...]` entry list contain a non-builtin attribute name? */
  function hasUnknownAttribute(inner) {
    var entries = inner.split(",");
    for (var e = 0; e < entries.length; e++) {
      var words = identTokens(entries[e].replace(/^[\s\-↓↑]+/, ""));
      var attrName = words[0] === "local" || words[0] === "scoped"
        ? words[1] : words[0];
      if (attrName && !KNOWN_ATTRIBUTES[attrName]) return true;
    }
    return false;
  }

  /* Drop non-builtin attributes from emitted declaration text: their
   * registering command cannot be replayed, so `@[simp_isPosition]` would
   * fail with "unknown attribute". */
  function sanitizeAttributes(text) {
    return text.replace(/@\[([^[\]]*)\]\s*/g, function (whole, inner) {
      var kept = inner.split(",").filter(function (entry) {
        return !hasUnknownAttribute(entry);
      });
      if (kept.length === 0) return "";
      if (kept.length === inner.split(",").length) return whole;
      return "@[" + kept.join(",").trim() + "] ";
    });
  }

  function makeContextPruner(matcher, seen) {
    function outOnlyIds(ids) {
      if (!ids) return false;
      for (var k = 0; k < ids.length; k++) {
        if (seen[ids[k]]) return false;
      }
      return true;
    }
    /* nsPrefixes: enclosing namespace joins, innermost last. parentFallback:
     * for reference lists (attribute/export args) a dotted token whose full
     * name is unknown may be a structure/class projection — resolve its
     * parent instead. */
    function mentionsOutOnly(tokens, nsPrefixes, parentFallback) {
      for (var t = 0; t < tokens.length; t++) {
        var token = tokens[t];
        var ids = matcher.strict[token];
        if (!ids && nsPrefixes) {
          for (var p = nsPrefixes.length - 1; p >= 0 && !ids; p--) {
            ids = matcher.strict[nsPrefixes[p] + "." + token];
          }
        }
        if (!ids && parentFallback && token.indexOf(".") >= 0) {
          var parent = token.slice(0, token.lastIndexOf("."));
          ids = matcher.loose[parent];
        }
        if (ids && outOnlyIds(ids)) return true;
      }
      return false;
    }
    return function keepContext(text, nsPrefixes) {
      var exportMatch = text.match(
        /^\s*export\s+([\w.'À-￿]+)\s*\(([^)]*)\)/);
      if (exportMatch) {
        var namespacePath = exportMatch[1];
        var members = identTokens(exportMatch[2]);
        var qualified = members.map(function (member) {
          return namespacePath + "." + member;
        });
        // The namespace itself resolving out-of-cone also prunes (it may
        // not even exist in the file without its declarations).
        qualified.push(namespacePath);
        return !mentionsOutOnly(qualified, nsPrefixes, true);
      }
      var attributeMatch = text.match(
        /^\s*(?:scoped\s+|local\s+)?attribute\s*\[([^\]]*)\]/);
      if (attributeMatch) {
        if (hasUnknownAttribute(attributeMatch[1])) return false;
        return !mentionsOutOnly(identTokens(text), nsPrefixes, true);
      }
      if (/^\s*(?:scoped\s+|local\s+)?variable\b/.test(text)) {
        return !mentionsOutOnly(identTokens(text), nsPrefixes, false);
      }
      return true;
    };
  }

  /* Track `namespace`/`section`/`end` context commands to know the
   * enclosing namespace path at each point of a module replay. */
  function updateNamespaceStack(stack, text) {
    var ns = text.match(/^\s*namespace\s+([\w.'À-￿]+)/);
    if (ns) {
      stack.push(ns[1]);
      return;
    }
    if (/^\s*(?:noncomputable\s+)?section\b/.test(text)) {
      stack.push(null); // section: no namespace component
      return;
    }
    if (/^\s*end\b/.test(text)) stack.pop();
  }

  function namespacePrefixes(stack) {
    var prefixes = [];
    var current = "";
    for (var i = 0; i < stack.length; i++) {
      if (stack[i] === null) continue;
      current = current ? current + "." + stack[i] : stack[i];
      prefixes.push(current);
    }
    return prefixes;
  }

  /* Namespaces mentioned by kept `open` commands; stubbed up front so the
   * opens resolve even when nothing from that namespace is emitted. */
  function openedNamespaces(contextTexts) {
    var found = [];
    var seen = {};
    for (var i = 0; i < contextTexts.length; i++) {
      var text = contextTexts[i];
      if (!/^\s*(?:scoped\s+|local\s+)?open\b/.test(text)) continue;
      var body = text.replace(/^\s*(?:scoped\s+|local\s+)?open\b/, "")
        .replace(/\([^)]*\)/g, " ");
      var tokens = body.split(/\s+/);
      for (var j = 0; j < tokens.length; j++) {
        var token = tokens[j];
        if (!token || token === "scoped" || token === "hiding"
            || token === "renaming" || token === "in") continue;
        // Namespaces open with a capitalized or dotted path; anything else
        // (prose, keywords, operators) must not become a stub.
        if (!/^[A-Z\u00c0-\uffff][\w.'\u00c0-\uffff]*$/.test(token)
            && token.indexOf(".") === -1) continue;
        if (!/^[A-Za-z_\u00c0-\uffff][\w.'\u00c0-\uffff]*$/.test(token)) continue;
        if (!seen[token]) {
          seen[token] = true;
          found.push(token);
        }
      }
    }
    return found;
  }

  /* Lemma references named in tactic bracket lists of an emitted body.
   * `simp only [foo]` applies rfl-lemmas definitionally, leaving no
   * constant in the proof term, so the recorded dependencies miss them;
   * the bracket list is the only trace. */
  function tacticReferences(text) {
    var refs = [];
    var pattern =
      /\b(?:simp_all|simp_rw|simp|rw|rewrite|unfold|dsimp)\s+(?:only\s+)?\[([^\]]*)\]/g;
    var match;
    while ((match = pattern.exec(text)) !== null) {
      var tokens = identTokens(match[1]);
      for (var i = 0; i < tokens.length; i++) refs.push(tokens[i]);
    }
    return refs;
  }

  var TACTIC_MATCH_CAP = 5; // ambiguous tokens (many homonyms) are skipped

  /* Grow the cone with declarations named in emitted bodies' tactic lists.
   * Mutates `state`; returns module indices whose sources are still needed
   * (the caller fetches them and calls build again). */
  function expandTacticReferences(shard, sources, state, matcher, linesFor) {
    var decls = shard.decls;
    var pending = {};
    for (var round = 0; round < 4; round++) {
      var changed = false;
      var idsNow = state.included.slice();
      for (var i = 0; i < idsNow.length; i++) {
        var node = decls[idsNow[i]];
        if (isProofKind(node.kind) && !node.span) continue; // body sorried
        if (sources[node.module] === undefined) {
          pending[node.module] = true;
          continue;
        }
        var refs = tacticReferences(declText(node, linesFor(node.module)));
        for (var r = 0; r < refs.length; r++) {
          var candidates = matcher.loose[refs[r]];
          if (!candidates || candidates.length > TACTIC_MATCH_CAP) continue;
          var anyCone = false;
          var c;
          for (c = 0; c < candidates.length; c++) {
            if (state.seen[candidates[c]]) { anyCone = true; break; }
          }
          if (anyCone) continue;
          for (c = 0; c < candidates.length; c++) {
            walkCone(shard, [candidates[c]], state);
            changed = true;
          }
        }
      }
      if (!changed) break;
    }
    for (var j = 0; j < state.included.length; j++) {
      var moduleIndex = decls[state.included[j]].module;
      if (sources[moduleIndex] === undefined) pending[moduleIndex] = true;
    }
    return Object.keys(pending).map(Number);
  }

  /* Assemble the minimal file.
   * shard: the project shard JSON.
   * sources: object mapping module index -> raw module text.
   * targetId: shard-local declaration id.
   * Returns {pending: [moduleIndex…]} when more sources are required.
   */
  function build(shard, sources, targetId) {
    var decls = shard.decls;
    var linesCache = {};
    function linesFor(moduleIndex) {
      if (!linesCache[moduleIndex]) {
        linesCache[moduleIndex] = (sources[moduleIndex] || "").split("\n");
      }
      return linesCache[moduleIndex];
    }
    var state = { seen: {}, included: [], missingHost: [] };
    walkCone(shard, [targetId], state);
    var matcher = makeNameMatcher(shard);
    var stillNeeded = expandTacticReferences(
      shard, sources, state, matcher, linesFor);
    if (stillNeeded.length > 0) return { pending: stillNeeded };
    var ids = state.included.slice().sort(function (a, b) { return a - b; });
    var cone = { ids: ids, missingHost: state.missingHost };
    var target = decls[targetId];
    var byModule = {};
    var i;
    for (i = 0; i < ids.length; i++) {
      var node = decls[ids[i]];
      (byModule[node.module] = byModule[node.module] || []).push(ids[i]);
    }
    var order = moduleOrder(shard, ids);

    var keepContext = makeContextPruner(matcher, state.seen);
    var imports = {};
    var allContexts = [];
    var keptContextsByModule = {};
    for (i = 0; i < order.length; i++) {
      var moduleData = (shard.moduleData || [])[order[i]] || {};
      (moduleData.imports || []).forEach(function (name) {
        imports[name] = true;
      });
      var nsStack = [];
      var kept = [];
      (moduleData.contexts || []).forEach(function (entry) {
        if (keepContext(entry[1], namespacePrefixes(nsStack))) {
          kept.push(entry);
          allContexts.push(entry[1]);
        }
        updateNamespaceStack(nsStack, entry[1]);
      });
      keptContextsByModule[order[i]] = kept;
    }
    var importList = Object.keys(imports).sort();
    if (importList.length === 0) importList = ["Mathlib"];

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
    out.push("set_option quotPrecheck false");
    out.push("set_option linter.all false");
    out.push("");

    var stubs = openedNamespaces(allContexts);
    if (stubs.length > 0) {
      out.push("-- Namespace stubs so later `open`s resolve.");
      for (i = 0; i < stubs.length; i++) {
        out.push("namespace " + stubs[i]);
        out.push("end " + stubs[i]);
      }
      out.push("");
    }

    for (i = 0; i < order.length; i++) {
      var moduleIndex = order[i];
      var moduleName = shard.modules[moduleIndex];
      var needed = (byModule[moduleIndex] || []).slice();
      var keptContexts = keptContextsByModule[moduleIndex] || [];
      // Context-only modules (no cone declarations) are replayed for their
      // notation/attribute commands; skip them when nothing survives.
      if (needed.length === 0 && keptContexts.length === 0) continue;
      var source = sources[moduleIndex];
      if (needed.length > 0 && source === undefined) continue;
      var lines = source === undefined ? [] : source.split("\n");
      var events = [];
      var k;
      for (k = 0; k < keptContexts.length; k++) {
        events.push({ line: keptContexts[k][0], text: keptContexts[k][1] });
      }
      var emittedSpans = {};
      for (k = 0; k < needed.length; k++) {
        var entry = decls[needed[k]];
        var spanKey = entry.span ? entry.span.join(":") : "d" + needed[k];
        if (emittedSpans[spanKey]) continue;
        emittedSpans[spanKey] = true;
        events.push({
          line: entry.span ? entry.span[0] : entry.line,
          text: declText(entry, lines),
        });
      }
      events.sort(function (a, b) { return a.line - b.line; });
      out.push("-- ═══ " + moduleName + " ═══");
      out.push("section");
      for (k = 0; k < events.length; k++) {
        out.push(events[k].text);
        out.push("");
      }
      out.push("end");
      out.push("");
    }

    return {
      text: out.join("\n"),
      declarationCount: ids.length,
      moduleCount: order.length,
      missingHost: cone.missingHost.map(function (id) {
        return decls[id] ? decls[id].name : String(id);
      }),
    };
  }

  var api = { build: build, coneIds: coneIds, moduleOrder: moduleOrder };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  if (root) root.ExpoMinimal = api;
})(typeof window !== "undefined" ? window : null);
