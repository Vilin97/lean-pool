# Lean Pool — provenance: human vs AI vs mixed

_How many of the pooled formalization projects were produced by a human, by an AI system, or by a mix of both._

## Summary

Across all **123** projects in `LeanPool/projects.yml` (as of 2026-07-19):

| Provenance | Count | Share |
|---|---:|---:|
| Human-made | **65** | 52% |
| AI-made | **38** | 30% |
| Mixed (human + AI) | **20** | 16% |
| **Total** | **123** | 100% |

Confidence breakdown:

| Provenance | high | medium | low |
|---|---:|---:|---:|
| human | 5 | 60 | 0 |
| AI | 30 | 8 | 0 |
| mix | 10 | 9 | 1 |

### The honest caveats

1. **The AI-vs-mix line is a judgment call.** The rubric below draws it at *where the proofs mostly came from*: a human committing the output of a one-shot agent/Aristotle run is **AI**, not mix; **mix** requires substantial human-written formalization alongside the AI's. Sensitivity: 3 *mix* projects are AI-leaning and 2 *AI* projects could be argued into *mix* (tagged in the tables), so shifting the line moves the AI/mix split by up to ~5.

2. **Absence of a signal is not proof of human authorship.** A human can commit AI-generated proofs with no trailer, no disclosure, and no agent-config file. The *human* bucket contains every project for which no credible AI evidence could be found after the checks below — a lower bound on AI, an upper bound on human. (Conversely, several *human* entries have *positive* evidence of human authorship, e.g. `erdos137`'s author develops the mathematics in public dialogue on the erdosproblems.com forum while committing incrementally.)

## Methodology

Two passes, evidence gathered per project (not self-reported).

**Pass 1 — automated sweep (all 123 projects).** For each of the 122 unique upstream repos: full commit history via blobless bare clone, scanned for AI co-authorship trailers (`Co-authored-by: Claude`, Aristotle/Codex/Copilot markers) and AI-agent bot committers (CI bots like `github-actions[bot]`/`dependabot[bot]` excluded); upstream README scanned for disclosure (false positives like the author name "Claude-Alain", "our aim", AI-generated logos filtered manually); agent-config files (`AGENTS.md`, `CLAUDE.md`, `.claude/`); publisher identity.

**Pass 2 — per-project verification (2026-07-19).** Every project that was newly pooled since a prior verified audit (2026-06-12) or where evidence sources disagreed — 52 of 123 — was verified individually: registry block + **vendored code** in `LeanPool/` grepped for AI self-attribution; upstream README and full commit forensics via the GitHub API (including what each suspect commit actually changed); arXiv abstracts/full text and in-repo report PDFs; publisher orgs confirmed against primary sources (AxiomMath/AxiomProver, Math Inc./Gauss, FrenzyMath/Archon, EPFL-LARA — all verified as autonomous AI formalization operations); the **complete history of the Lean Zulip channel "AI authored projects"** (channel 583339; 831 messages, 2026-02-18 → 2026-07-18, harvested via the unauthenticated spectator API); and the erdosproblems.com AI-contributions wiki. Every verdict that changed a label or sat at low confidence was then re-checked by an **independent adversarial pass** instructed to refute it (31 of 52; all verdicts survived).

Instructive cases the second pass caught that a signal scan alone misses:

- **Disclosure living outside the README/commits:** `bannai-bannai-stanton` (LLM-usage section in the author's report PDF inside the repo), `pebbling-hypercube` (disclosure in the arXiv paper), `domain-theory` (paper's "AI-assisted development" section), `unconditional-schauder-basis` (`AGENTS.md` proof-delegation directives + an 831-line proof commit 83 minutes after that file appeared), `erdos367` (erdosproblems.com wiki documents the author's Aristotle/Claude/Codex/GPT toolchain).
- **Vendored code self-attribution:** `polynomial-method-restricted-sums` (upstream is 404, but the vendored files carry `AristotleLemmas` sections and "originally proved by Aristotle" docstrings), `lean-model-checking` ("Code below here mostly written by GPT-5-Codex" headers), `clawristotle` (pipeline credits in the vendored header).
- **A false AI positive:** `zeta_3_irrational` — an earlier automated pass attributed it to AI agent bots; the full commit history shows all 133 commits are by the human authors (Junqi Liu, Jujian Zhang, et al.). Classified **human** with high confidence.
- **One-shot agent output committed by a human is AI, not mix:** `2-coloring-1-round`, `burkholder`, `fineqs`, `kalton-roberts`, `krafftsieve`, `kuramoto`, `cramer-wold`, `semicircle-catalan`, `spectral-positivity`, `osforgff`, `phaseretrieval`, `formal-learning-theory`, and others moved accordingly.

### Rubric

- **AI** — the Lean proofs are *primarily machine-generated*: an autonomous org pipeline (AxiomProver, Gauss, Archon, EPFL autoformalization, one-shot Harmonic Aristotle), an AI-agent bot as primary committer, near-total AI co-authorship, or the project's own README/paper says the formalization was done by AI/LLMs with humans supervising, curating, scaffolding definitions, or committing the output.
- **Mixed** — clear evidence of *both* substantial human-written formalization *and* substantial AI assistance.
- **Human** — no credible AI evidence in commits, README, paper, vendored code, or publisher identity. (A handful of trivial AI-trailer commits, <~5% and non-substantive, stays human and is noted.)

### Limitations

- One upstream repo (`NickAdfor/The-polynomial-method-and-restricted-sums-of-congruence-classes`) is 404; its project is classified from vendored-code self-attribution instead.
- The `cencov-petz` / `compact-spectral` / `rellich-kondrachov` and `erdos367` / `critical-portraits` AI verdicts rest on publisher-identity/methodology inference plus commit forensics (squashed single-timestamp dumps), not an explicit per-repo disclosure — hence medium confidence; a statement from the authors would settle them (see flagged list).
- The registry `authors:` field does **not** capture provenance — most AI-made projects credit only the supervising humans or the org. Use this document, not `authors:`, when provenance matters.

## AI-made — 38 projects

_Primarily machine-generated proofs (humans supervise/curate/commit)._

| Project (slug) | Upstream repo | Conf. | Evidence |
|---|---|---|---|
| `2-coloring-1-round` | suomela/2-coloring-1-round | high | Upstream README (gh api repos/suomela/2-coloring-1-round/readme): "Our proof was largely discovered, developed, and formalized by large language models. We used primarily Codex with GPT-5.2" in a Docker sandbox agent loop — the rubric's own-README-says-AI criterion for the AI bucket. |
| `agree-to-disagree` | AxiomMath/AgreeToDisagree | high | Upstream README (AxiomMath/AgreeToDisagree) says the repo contains "inputs given to and outputs of AxiomProver" and that the AgreeToDisagree folder is the "final hand-cleaned formalisation" of AxiomProver's output — proofs machine-generated, humans curating. |
| `anderson-conjecture` | frenzymath/Anderson-Conjecture | high | FrenzyMath "Archon" autonomous agent |
| `archon-firstproof-results` | frenzymath/Archon-FirstProof-Results | high | FrenzyMath "Archon" agent |
| `biswal` | AxiomMath/Biswal | high | Upstream is AxiomMath/Biswal (Axiom Math, axiommath.ai — autonomous AxiomProver pipeline). Its README describes the repo as pipeline input/output: natural-language task.md "input files" and machine-produced "output files" (problem.lean = translation of statement, solution.lean = formal solution), … |
| `burkholder` | SmaniaD/Burkholder | high | Upstream README ("An Informal Report On How The Formalization Was Done", github.com/SmaniaD/Burkholder): "we barely had to type any Lean code ourselves; instead, we mostly guided the agent" and "it is remarkable that we barely had to write any proof by hand" — Copilot/Codex in agent mode wrote the … |
| `chudnovsky` | ldct/lean-eval-chudnovsky | high | Upstream README (ldct/lean-eval-chudnovsky) Attribution section: "Produced by Claude Opus 4.8 and Fable 5 via multi-agent, file-parallel orchestration with human direction and review at the architecture level." A lean-eval benchmark submission, ~20k lines. |
| `clawristotle` | Vilin97/Clawristotle | high | Vendored header LeanPool/Clawristotle.lean:47-48: "Architecture and review by Vasily Ilin; implementation by Claude Code; informal proof generation by Gemini DeepThink; 111 hard lemmas closed by Aristotle" — the human steered, AI wrote the Lean proofs. |
| `cramer-wold` | Lemmy00/lean-pool | high | epfl-lara/AutoformalizedProjects README lists CramerWoldTheorem as a completed project "produced with the LeanFlow workflow" (EPFL-LARA's LLM prove-loop); author Lemmy00 (Lazar Milikic) is LeanFlow's own developer, and the pool file's core proof (Measure.ext_of_charFunDual + … |
| `dead-ends` | AxiomMath/dead-ends | high | AxiomMath / AxiomProver |
| `domain-theory` | catskillsresearch/domain_theory | high | The project's own paper (arxiv.md "AI-assisted development") attributes the Lean proof work to AI agents: Cursor Composer 2.5 for "routine... medium proof obligations" (Props 1.2-2.5, partial §3) and Claude Opus 4.8 for "the heaviest proof and design work" (Props 2.9-2.11, Thm 2.12, 3.3, 3.8, … |
| `egrs75` _(AI→could-be-mix)_ | lyfar/egrs75-lean | high | Upstream formalization.yaml `automation.methods` declares method "agent" with models claude-fable-5 / claude-opus-4-7 via "Claude Code (agentic sessions)" producing the proofs; README states "produced with substantial AI assistance (Anthropic Claude, agentic sessions)". All 5 commits carry Claude … |
| `erdos1196` | math-inc/Erdos1196 | high | Math Inc. "Gauss" autoformalization agent |
| `erdos403` _(AI→could-be-mix)_ | gotrevor/erdos-403 | high | Upstream README (gotrevor/erdos-403) discloses "This formalization was produced by Trevor Morris with Claude Code (Anthropic)", and all 56/56 commits carry a "Co-Authored-By: Claude ... <noreply@anthropic.com>" trailer (55 Opus 4.8, 1 Fable 5). |
| `fel-conjecture` | AxiomMath/fel-polynomial | high | AxiomMath / AxiomProver |
| `fineqs` | nasqret/fineqs | high | Upstream README (nasqret/fineqs) and every vendored file header state the formalization "was performed with the software Aristotle by Harmonic"; "Aristotle" is listed as a co-author in LeanPool/projects.yml and in the copyright lines of LeanPool/Fineqs.lean and LeanPool/Fineqs/Main.lean. |
| `formal-learning-theory` | Zetetic-Dhruv/formal-learning-theory-kernel | high | Upstream README self-describes the project as "human-guided, AI-driven proof search" whose search "produced 354 machine-checked theorems"; 115/198 commits are Co-Authored-By: Claude Opus 4.6 (1M context), with the rest mostly infra/docs (gh api repos/Zetetic-Dhruv/formal-learning-theory-kernel). |
| `frontiermath-open-hypergraphs` | math-inc/FrontierMathOpen-Hypergraphs | high | Repo lives in the math-inc GitHub org (Math Inc., the Gauss autoformalization pipeline — a rubric-listed autonomous AI org), and its README states the development is based on an informal proof produced by GPT-5.4 Pro (prompters Kevin Barreto and Liam Price); history is a single squash commit by … |
| `grothendieck-vanishing` | Vilin97/Clawristotle | high | Upstream README (Vilin97/Clawristotle) states the projects are "produced by centaur teams of AI agents": "The human steers ... while AI agents handle the implementation: writing the Lean code, searching for proofs, dispatching hard lemmas to ... Aristotle". Agent stack for this project: Claude … |
| `krafftsieve` | ElNando888/KrafftSieve | high | Upstream README (ElNando888/KrafftSieve): "Aristotle 0.7.0 was the workhorse for the formal verification process"; Gemini 3.1 Pro wrote the blueprint and prompts. Every vendored Lean file header says "Portions of this file were generated by Aristotle (https://aristotle.harmonic.fun)". |
| `kuramoto` | velvetmonkey/kuramoto-lean | high | Upstream README Acknowledgements: "Proofs in this library were generated using Aristotle, an AI proof assistant for Lean 4 and Mathlib" — blanket, whole-library; plus 21/47 commits carry Claude co-author trailers and the Frontier module is explicitly Aristotle-generated … |
| `lattice-triangle` | AxiomMath/lattice-triangle | high | AxiomMath / AxiomProver |
| `osforgff` | mrdouglasny/OSforGFF | high | Upstream self-report formalization.yaml (mathlib-initiative v0.3), automation.methods: Claude Opus 4.6 via Claude Code is the "Primary prover ... cycle-by-cycle with compiler-guided repair", GPT-5.2 Codex "Auxiliary proving", Gemini 3 Pro review — the project's own declaration that the proofs were … |
| `partial-regularity` | AxiomMath/partial-regularity | high | AxiomMath / AxiomProver |
| `phaseretrieval` | susannabertolini/PhaseRetrieval | high | Upstream README (susannabertolini/PhaseRetrieval) says the proof modules in Internal/ are "autoformalization output" and ScaffoldingNotes/ and ProofSketch/ are LLM-generated; only the "deliberately small" public entry points were human-curated. Vendored code has "GPT Lemma/Proposition/Section" … |
| `pythagorean-polynomial-parametrization` | epfl-lara/AutoformalizedProjects | high | Upstream README (epfl-lara/AutoformalizedProjects) titles itself "Paper-Level Autoformalizations": "Lean 4 formalization projects produced with the LeanFlow workflow" — an EPFL-LARA autoformalization pipeline; PythagoreanPolynomialParametrization is listed as one of its completed autoformalized … |
| `ramanujan-tau-misses-primes` | AxiomMath/ramanujan-tau-misses-primes | high | AxiomMath / AxiomProver |
| `semicircle-catalan` | Wondermonger-daydreaming/semicircle-catalan | high | The commit introducing the whole formalization (2f106e25 "Add sorry-free Lean formalization (3715 lines, 0 sorries)") is Co-Authored-By: Claude Opus 4.6, and the README acknowledges "OpenGauss-managed proving workflows for project orchestration and proof search" (Gauss/Math Inc. autoprover). |
| `spectral-positivity` | mrdouglasny/spectral-positivity | high | The project's own formalization.yaml self-report declares automation method "agent", models ["claude-opus-4-8"], framework "Claude Code", with "Cycle-by-cycle proving with compiler-guided repair" — i.e. the proofs were produced by an AI agent; 12/14 commits carry Claude Opus Co-Authored-By trailers. |
| `zeta-h123` | AxiomMath/zeta-h123 | high | Upstream README (AxiomMath/zeta-h123) states the repo "contains artifacts generated by AxiomProver", with problem.lean/solution.lean produced by the Axiom Math pipeline; listed humans are repository maintainers/paper authors, not proof authors. |
| `cencov-petz` | abenenson/cencov-petz | medium | Author Adam Benenson is founder of Forethink Labs ("agent orchestration"; gh api users/abenenson), published Jan-2026 essays describing delegating Lean proof development to coding agents via sorry-decomposition, and burst-produced 5 sorry-free graduate-level Lean repos in disparate fields Mar–May … |
| `compact-spectral` | abenenson/compact-spectral | medium | Entire history is a scripted batch export: 5/6 commits share timestamp 2026-05-11T22:01:00Z, and an identical "style: classify supporting declarations as lemmas" commit lands at 2026-05-14T13:17:14Z (same second) in all four of abenenson's Lean repos (gh api repos/abenenson/*/commits). Author bio: … |
| `connes-kreimer` | karlesmarin/connes-kreimer-lean | medium | All 8 upstream commits (karlesmarin/connes-kreimer-lean) carry "Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>", including the initial commit landing the whole formalization; README admits "A large language model was used as a coding assistant". |
| `critical-portraits` | no-way-labs/lean-critical-portraits | medium | Publisher no-way-labs is a one-person LLM-agent lab: sibling repo minimum-state-product documents its sorry-free Lean formalization as produced by Claude-agent/GPT-agent lineages with exploration_log_lean.md (raw.githubusercontent.com/no-way-labs/minimum-state-product README), and … |
| `erdos367` | scottdhughes/erdos367 | medium | erdosproblems.com AI-contributions wiki lists Scott Hughes's parallel Lean project (#942, 13-14 Jun 2026, "Partial result (Lean)") as produced with "Aristotle, Claude Opus 4.8, Codex, GPT-5.5"; erdos367 (created 10 Jun 2026, same author, single-commit dump, README: modules are "the verification … |
| `five-eighths-theorem` | ldct/lean-monorepo | medium | The project's sole authoring commit (a616b7bc, PR Vilin97/lean-pool#177 by ldct) carries "Co-Authored-By: Claude Fable 5"; the file does not exist in the upstream monorepo tree or 433 commit messages, so the 254-line proof arrived fully formed in one Claude Code commit. |
| `kalton-roberts` | boonsuan/KaltonRoberts | medium | Upstream README (boonsuan/KaltonRoberts): "The formalization was carried out with GPT-5.5 Pro and Harmonic Aristotle." — the whole Lean development is credited to two AI systems (Aristotle is a one-shot autoprover); no evidence anywhere of substantial human-written Lean. |
| `rellich-kondrachov` | abenenson/rellich-kondrachov | medium | Author is an agent-orchestration AI-lab founder (not a mathematician) whose own essays (Jan 2026, abenenson.github.io repo) describe delegating Lean proof production to AI agents ("agentic coding is optimization, not authorship"); the ~10.7k-line repo appeared as 7 staged commits all within one … |

## Mixed (human + AI) — 20 projects

_Substantial human **and** AI contribution._

| Project (slug) | Upstream repo | Conf. | Evidence |
|---|---|---|---|
| `bannai-bannai-stanton` | AntoineduFresne/Bannai-Bannai-Stanton_Theorem | high | Author's own report PDF in the upstream repo (Formalisation_..._Report_tex.pdf, section 3 "Workflow and LLM Usage"): "I utilised Gemini Pro 3 ... heavily"; the LLM "almost did all of the work" on the monomial-counting bijection; the AI supplied the rank-bound proof approach. Human designed … |
| `circuit-complexity` | SamuelSchlesinger/circuit-complexity | high | 4 of 26 upstream commits carry "Co-Authored-By: Claude Opus 4.6" trailers (gh api commits, SamuelSchlesinger/circuit-complexity) — all by Vincent Liew, contributing the entire CNF/DNF module (~970 added lines) incl. 2/6 registered main results; the other ~22 commits (Shannon, Schnorr, gate … |
| `computability` | tannerduve/computability | high | aleph-prover-dev[bot] (AI agent) authored commit 51cacaf8 "Proof for RecursiveIn_cond / Automated commit" (+266/-13 to TuringDegree.lean), and tannerduve's commit 80b54cf1 (+127) carries a Co-authored-by: aleph-prover-dev[bot] trailer; those proofs survive verbatim in the vendored … |
| `demazure-product` | npflueger/demazure | high | Upstream README "Generative AI disclosure": portions built with OpenAI Codex and Claude Code; AI-written proofs marked with model comments; "overall design, and all formalized theorem statements, were written by the author." Vendored code has ~140 "Proof written by GPT 5.5/Codex/Claude Opus 4.7" … |
| `forward-euler` | Vilin97/forward_euler | high | projects.yml lists "Aristotle" as co-author; "initial code generated by Aristotle" |
| `lean-model-checking` | kuruczgy/lean-model-checking | high | Upstream README (kuruczgy/lean-model-checking) has an "AI usage" section: "a significant amount of AI written code... I try to write the theorem statements myself, but some proofs are entirely AI written"; vendored files carry explicit AI attributions (GPT-5-Codex, GPT-5.2, Claude 4.5 Opus). |
| `leanmodularforms` _(mix→AI-leaning)_ | CBirkbeck/LeanModularForms | high | The 36k-LOC GeneralizedResidueTheory+ValenceFormula core (both registry main_declarations) was developed on branch feat/mathlib-prs with ~100% "Co-Authored-By: Claude Opus 4.7/4.8" trailers (pages 3/5/7: 100/100 each), while the vendored Modularforms/ support files trace to Birkbeck's human-written … |
| `polynomial-method-restricted-sums` | NickAdfor/The-polynomial-method-and-restricted-sums-of-congruence-classes | high | Vendored code self-discloses AI: docstrings "The main theorem of this file was originally proved by Aristotle (Lean v4.24.0, project request uuid ...)" in CompressedSizesRestrictedSum.lean and DiasDaSilvaHamidoune.lean, plus ~1500/3200 LOC inside explicit "noncomputable section AristotleLemmas" … |
| `rl-theory-in-lean` | ShangtongZhang/rl-theory-in-lean | high | Pool snapshot (vendored 2026-05-10) derives from upstream post-PR-#1 state: LeanPool/RlTheoryInLean/Data/Matrix/Stochastic.lean shares 560 unique lines with the PR-#1 version vs 355 with the pre-PR version; PR #1's author dennj states in the PR thread "100% of the code is AI-generated" … |
| `singular-moduli` | ElodinLaarz/lean-thesis | high | Registered main result prime_split_iff (commit e153d23) is "Co-authored-by: Claude Opus 4.7"; other substantive commits carry Claude/aider trailers, while the majority of Layer-2a feature commits (prime_inert_iff, quotient iso, root counting, etc.) are trailer-free human work by Caleb Geiger. |
| `five-distance-sharp` _(mix→AI-leaning)_ | ElVec1o/five-distance-sharp | medium | Upstream README Acknowledgements (gh api repos/ElVec1o/five-distance-sharp/readme): "Developed by Vico Bonfioli with substantial assistance from Anthropic's Claude (an AI assistant) for proof development, refactoring, and verification" — a disclosed substantial-AI-assistance project with a named … |
| `leancomplexanalysis` | seb488/LeanComplexAnalysis | medium | README: "developed with the assistance of Aristotle" |
| `pebbling-hypercube` _(mix→AI-leaning)_ | pachterlab/P_2026_2 | medium | Paper (arXiv:2606.01685, sole author Lior Pachter) discloses: "The author used GPT-5.5 for assistance with the mathematics and in drafting an initial version of this manuscript"; human "developed the proof strategy, verified the mathematical arguments". Refutes draft's "no AI signal". |
| `ramanujan-nagell` | BarinderBanwait/ramanujan_nagell | medium | B. Banwait; 26% Claude-coauthored |
| `root-system` | Antoine-dSG/root_system | medium | README: "Contributions: Aristotle and ChatGPT 5.5" |
| `shannon-1948-formalization` | SamuelSchlesinger/shannon-1948-formalization | medium | README "## AI Assistance": "developed with substantial assistance from Claude (Anthropic)" |
| `sumsthreesquares` | pitmonticone/SumsThreeSquares | medium | 38% AI-trailer; copilot-swe-agent[bot] + Aristotle; multi human author |
| `unconditional-schauder-basis` | SmaniaD/UnconditionalSchauderBasis | medium | Upstream repo has AGENTS.md with proof-delegation directives to an AI agent ("after the run report which sorries you added"; "Do not add additional assumptions... without asking for permission"), and an 831-line proof commit (b25bab3f) landed 83 min after its creation — while all 57 commits are … |
| `zhang-yeung-inequality` | cboone/zhang-yeung-inequality | medium | README "## AI Statement": "substantial assistance from Opus 4.6+4.7 and GPT 5.4 via claude/opencode"; AGENTS.md+CLAUDE.md+copilot config (commit trailers missed it) |
| `sensitivity` | SamuelSchlesinger/sensitivity-conjecture | low | Repo itself has zero AI markers, but the same author's Lean repo built the same week (shannon-1948-formalization README) discloses "substantial assistance from Claude ... throughout the formalization effort", and sensitivity shows the same pattern: 718-line 8-file scaffold in one commit, all … |

## Human-made — 65 projects

_No credible AI evidence found (see caveat #2)._

| Project (slug) | Upstream repo | Conf. | Evidence |
|---|---|---|---|
| `brauergroup_new` | Whysoserioushah/BrauerGroup | high | All Claude-trailer commits in Whysoserioushah/BrauerGroup are non-substantive: a 16-line mathlib-bump fix (co-authored by pool maintainer V. Ilin), a ".claude gitignore" commit, and a LICENSE add. Zero AI trailers on proof-content commits across all 543 commits; no AI mention in README or vendored … |
| `directed-topology-lean-4` | Dominique-Lawson/Directed-Topology-Lean-4 | high | FP: matched "our AIm" not "our AI" |
| `duality` | madvorak/duality | high | FP: only an AI-generated IMAGE in README; author M. Dvorak (human Lean dev) |
| `sardmoreira` | urkud/SardMoreira | high | core Mathlib dev (urkud); 3% AI-trailer — negligible |
| `zeta_3_irrational` | ahhwuhu/zeta_3_irrational | high | All 133 upstream commits (gh api repos/ahhwuhu/zeta_3_irrational/commits, pages 1-2 = full history) are by human accounts ahhwuhu (Junqi Liu), jjaassoonn (Jujian Zhang), zjj, zhilihong, 97l — zero bot committers and zero AI trailers. The draft's claimed numina-lean-agent[bot]/lean-agent-app[bot] … |
| `a-formalization-of-borel-determinacy-in-lean` | sven-manthe/A-formalization-of-Borel-determinacy-in-Lean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `abc-exceptions` | b-mehta/ABC-Exceptions | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `aharonikorman` | b-mehta/AharoniKorman | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `apportionment` | mdbrnowski/apportionmentlib | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `artin-wedderburn` | JobPetrovcic/ArtinWedderburn | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `brouwer` | math-xmum/Brouwer | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `bruhat-tits` | chrisflav/bruhat-tits | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `circuitlib` | matthunz/circuitlib | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `computablereal` | Timeroot/computableReal | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `demazureoperatorslean` | bolito2/DemazureOperatorsLean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `desargues` | oneofvalts/desargues | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `ec-tate-lean` | KisaraBlue/ec-tate-lean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `erdos-tuza-valtr` | jcpaik/erdos-tuza-valtr | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `erdos137` | scottdhughes/erdos137 | medium | All 19 upstream commits authored by scottdhughes with no AI trailers/bots (gh api repos/scottdhughes/erdos137/commits), and the author personally develops the underlying math in real dialogue with Will Sawin and Thomas Bloom on the erdosproblems.com/137 forum thread (mirror: … |
| `event-structures` | vikraman/event-structures | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `factorizationsystems` | ivankobe/FactorizationSystems | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `flean` | josephmckinsey/flean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `fo-zfc` | ishiut/fo_zfc | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `formalization-of-bounded-arithmetic` | ruplet/formalization-of-bounded-arithmetic | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `frieze-patterns` | Antoine-dSG/frieze_patterns | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `fundamental-inequality` | linzialessandro/FundamentalInequality | medium | All 9 upstream commits authored solely by Alessandro Linzi (linzialessandro), a valuation theorist, with zero AI co-author trailers or agent bots (gh api repos/linzialessandro/FundamentalInequality/commits); README, vendored code, and Zulip show no AI disclosure. |
| `hsd-interior-point-lp` | makoto-yamashita/proof-on-a-homogeneous-self-dual-interior-point-method-for-linear-programming | medium | No AI signal anywhere: upstream repo (makoto-yamashita/proof-on-a-homogeneous-self-dual-...) has 2 commits, both authored by Makoto Yamashita (GitHub bio: "Researcher on Mathematical Optimization (Professor)"), zero AI trailers; README and vendored code contain no AI/LLM mentions; no Zulip … |
| `incompleteness` | FormalizedFormalLogic/Incompleteness | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `isoperimetric` | hojonathanho/isoperimetric | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `istranscendentalpi` | samuelborza/IsTranscendentalPi | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lean-booleanfun` | roos-j/lean-booleanfun | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lean-poly-abc` | seewoo5/lean-poly-abc | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lean-quantumalg` | QudeLeap/Lean-QuantumAlg | medium | No AI signal in any source: upstream README (gh api repos/QudeLeap/Lean-QuantumAlg/readme) has no AI disclosure; all 9 commits are anonymized "sync public release" squashes with no trailers; vendored-code grep hits only the false positive "teleportBe[llM]easure"; publisher QudeLeap is a … |
| `lean4-gl-coalgebras` | mgignoux/lean4-gl-coalgebras | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lean4-itree` | mit-plv/lean4-itree | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lentil` | verse-lab/Lentil | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `lowdimsolvclassification` | LieLean/LowDimSolvClassification | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `main-theorem-of-polytopes` | Jun2M/Main-theorem-of-polytopes | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `misere-games` | t4ccer/misere-games | medium | All 237 upstream commits authored by two humans (t4ccer 183, alfiemd 54) with zero AI trailers/tool mentions (gh api repos/t4ccer/misere-games/commits, pages 1-3); no AI strings in vendored code (git grep over LeanPool/MisereGames on origin/main). |
| `monlib4` | themathqueen/monlib4 | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `monsky` | dhyan-aranha/Monsky | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `mriscx` | JulsDE/MRiscX | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `neukirch` | jjdishere/neukirch | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `order-p-q` | wupr/order-p-q | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `partial-combinatory-algebras` | andrejbauer/partial-combinatory-algebras | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `pcf-theory` | YnirPaz/PCF-Theory | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `pentagonal-number-theorem` | wwylele/PentagonalNumberTheorem | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `pl-accelerated-nesterov-lean` | M1ngXU/PL-Accelerated-Nesterov-Lean | medium | No AI signal in any primary source: zero hits for AI/LLM markers in vendored code (git grep origin/main LeanPool/PLAcceleratedNesterovLean), no disclosure in upstream README (gh api repos/M1ngXU/PL-Accelerated-Nesterov-Lean/readme), no AI trailers/bots (single human commit), no AI-org publisher; … |
| `pointwise-birkhoff` | lua-vr/pointwise-birkhoff | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `polya-enumeration-theorem` | Luka-O/polya-enumeration-theorem | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `polylean` | siddhartha-gadgil/Polylean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `pumping-cfg` | AlexLoitzl/pumping_cfg | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `quasi-borel-spaces` | YellPika/quasi-borel-spaces | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `redhill` | Parcly-Taxel/Redhill | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `riemann-mapping-theorem` | vbeffara/RMT4 | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `rupert` | dwrensha/Rupert.lean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `selberg-sieve4` | amellendijk/selberg-sieve4 | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `semicirclelaw` | FredRaj3/SemicircleLaw | medium | Upstream file history for the one vendored file shows ~25 human commits ("proof inputted", "cleanup", grind experiments) by 4 SURIM students vs one Aristotle commit e22655af (+99/-7 lines, proof of variance_fun_id_semicircleReal, one admit later proven by a human) — AI share ~10% of one file, rest … |
| `settheory` | znssong/SetTheory | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `special-numbers` | provables/special-numbers | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `synthetic-euclid` | ah1112/synthetic_euclid_4 | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `turan3` | ro-gut/turan3 | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `virasoroproject` | kkytola/VirasoroProject | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `whitehead-theorem` | jzxia/WhiteheadTheorem | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |
| `zflean` | VTrelat/ZFLean | medium | no AI signal (no trailers / agent bots / AI-org / AI README disclosure) |

## Flagged for follow-up

The calls most likely to change with new information (medium/low confidence on a non-human label, or an unverifiable source). Asking the author would settle each:

| Project | Label | Why flagged |
|---|---|---|
| `sensitivity` | mix/low | In-repo evidence alone reads human; flip rests on the author's same-week Claude disclosure on `shannon-1948-formalization` plus one-evening development velocity. |
| `cencov-petz`, `compact-spectral`, `rellich-kondrachov` | AI/medium | Author is an agent-orchestration founder whose essays describe delegating Lean proofs to agents; all three histories are squashed single-timestamp dumps; no per-repo disclosure. |
| `erdos367` | AI/medium | erdosproblems.com wiki documents the author's AI toolchain on the parallel #942 project; erdos367 itself is a one-shot "artifacts as produced" dump. (Contrast `erdos137`, same author, verified human.) |
| `critical-portraits` | AI/medium | Publisher no-way-labs is a one-person LLM-agent lab; sibling repo documents an agent pipeline; no in-repo disclosure. |
| `five-eighths-theorem` | AI/medium | Written directly in the pool import PR with a Claude co-author trailer; no upstream development history exists. |
| `pebbling-hypercube` | mix/medium | Paper discloses GPT-5.5 assistance "with the mathematics"; the 12.5k-line Lean formalization landed in a single one-shot commit. |
| `unconditional-schauder-basis` | mix/medium | `AGENTS.md` + commit-timing evidence covers only the tail of development; the May bulk has no per-commit marker. |
| `polynomial-method-restricted-sums` | mix/high | Upstream repo 404; classified from vendored `AristotleLemmas` self-attribution. |

## Reproducibility

The per-project machine-readable classification is [`candidates/provenance.jsonl`](provenance.jsonl) (one object per line, same shape as `decisions.jsonl`). Entries carry a `verified` field when they went through the individual 2026-07-19 verification (with `(adversarial second pass)` where an independent refutation attempt ran). The tables above are generated from that file. Counts are point-in-time: new imports should be classified the same way (vendored grep + upstream README/commits + paper + Zulip), since local metadata alone is insufficient.
