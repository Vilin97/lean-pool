# Lean Pool shortlist

Working list of candidate projects considered for import into `lean-pool`. The
candidates table at [`README.md`](README.md) is the source. This shortlist is
everything in that table judged to fit the criteria below, organised by topic,
with the user's initial picks (down to `b-mehta/AharoniKorman`-level depth)
listed first.

Curated 2026-05-16. Projects already in lean-pool (see
[`LeanPool/projects.yml`](../LeanPool/projects.yml)) are omitted. So is
`math-inc/KakeyaFiniteFields`, which fit mathematically but had PR #33 closed
unmerged pending an explicit upstream license.

A **[June 2026 refresh](#june-2026-refresh--new-candidates)** of projects that
appeared or became active since the early-May sweep is appended at the end of
this file.

## Selection criteria (all four required)

1. **Substantive research- or graduate-level mathematics.** A named theorem, a
   paper formalisation, or a clearly-defined research topic. Not contests,
   courses, exercise sets, programming-language metatheory, verification tools,
   or libraries.
2. **Permissive license, relicensable under Apache-2.0.** The repo must carry
   an explicit permissive license compatible with redistribution under
   Apache-2.0 — Apache-2.0 itself, MIT, BSD-2/3-Clause, 0BSD, ISC, or Zlib.
   No license at all is **not** acceptable: lean-pool ships under Apache-2.0,
   so an explicit permissive grant must already be present in the repo.
   Copyleft and share-alike licenses (GPL / LGPL / AGPL / MPL / CC-BY-SA) are
   out.
3. **Stale.** Last commit ≥ 1 month ago (i.e. on or before 2026-04-16 at this
   curation date). Hard cutoff — anything more recent is presumed actively
   pushed and gets excluded.
4. **Lean toolchain ≤ v4.28.** Hard cutoff — `v4.29.x`, `v4.30.x`, recent
   `nightly-2026-…` all out. Anything `<= v4.28.x` or older `nightly-2023…`
   stays.

Soft preference for ≥ ~1k LOC (fragments below that are not worth importing).

## User's initial picks (filtered)

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [658060/topos](https://github.com/658060/topos) | Topos theory | *none* | v4.15.0 | 1,571 | 2026-02-20 |
| [sven-manthe/A-formalization-of-Borel-determinacy-in-Lean](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) | Borel determinacy | Apache-2.0 | v4.28.0-rc1 | 8,277 | 2026-02-26 |
| [calcu16/lean_complexity](https://github.com/calcu16/lean_complexity) | Complexity analysis | *none* | v4.5.0-rc1 | 5,595 | 2025-02-04 |

**Dropped from user's original list (failed staleness / Lean cutoff):**

- `sinhp/Poly` — updated 2026-04-26 (within the month)
- `math-inc/Erdos1196` — v4.30.0-rc1 (already in pool anyway)
- `aetilley/banach-tarski` — updated 2026-05-01 (within the month)
- `GasStationManager/ArtificialTheorems` — updated 2026-04-30 (within the month)
- `kebekus/ProjectVD` — v4.30.0-rc2 (the user's flagged mistake)

## Additional picks (rows below ProjectVD)

### Number theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [seewoo5/lean-poly-abc](https://github.com/seewoo5/lean-poly-abc) | Mason–Stothers (polynomial ABC) | Apache-2.0 | v4.9.0-rc2 | 1,290 | 2026-03-04 |
| [alainchmt/RingOfIntegersProject](https://github.com/alainchmt/RingOfIntegersProject) | Certifying rings of integers in number fields | Apache-2.0 | v4.14.0-rc2 | 93,799 | 2026-03-20 |
| [BarinderBanwait/ramanujan_nagell](https://github.com/BarinderBanwait/ramanujan_nagell) | Ramanujan–Nagell theorem | Apache-2.0 | v4.26.0-rc2 | 3,571 | 2026-04-08 |
| [KisaraBlue/ec-tate-lean](https://github.com/KisaraBlue/ec-tate-lean) | Elliptic curves, Tate's algorithm | Apache-2.0 | nightly-2023-08-19 | 7,786 | 2024-05-26 |
| [kckennylau/EllipticCurve](https://github.com/kckennylau/EllipticCurve) | Elliptic curve over schemes | Apache-2.0 | v4.25.0-rc2 | 7,309 | 2025-11-04 |
| [mariainesdff/ostrowski2024](https://github.com/mariainesdff/ostrowski2024) | Ostrowski's theorem | *none* | v4.26.0-rc2 | 2,507 | 2025-12-14 |
| [CBirkbeck/LeanModularForms](https://github.com/CBirkbeck/LeanModularForms) | Modular forms | Apache-2.0 | v4.29.0-rc8 | 77,344 | 2026-05-21 |

### Algebra / commutative algebra

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [jonhanke/quadratic_forms_in_lean](https://github.com/jonhanke/quadratic_forms_in_lean) | Quadratic forms | *none* | v4.19.0-rc3 | 2,113 | 2025-09-07 |
| [Whysoserioushah/BrauerGroup_new](https://github.com/Whysoserioushah/BrauerGroup_new) | Brauer groups | Apache-2.0 | v4.26.0-rc2 | 14,855 | 2026-03-20 |
| [mariainesdff/LocalClassFieldTheory](https://github.com/mariainesdff/LocalClassFieldTheory) | Local fields, towards LCFT | *none* | v4.22.0-rc2 | 14,717 | 2026-03-10 |
| [xyzw12345/CohenMacaulay](https://github.com/xyzw12345/CohenMacaulay) | Cohen–Macaulay rings | *none* | v4.19.0-rc2 | 2,083 | 2025-05-01 |
| [AntoineChambert-Loir/Jordan4](https://github.com/AntoineChambert-Loir/Jordan4) | Jordan's theorem on permutation groups | *none* | v4.16.0 | 13,660 | 2025-09-13 |
| [AlexBrodbelt/DicksonsClassificationTheorem](https://github.com/AlexBrodbelt/DicksonsClassificationTheorem) | Dickson's classification theorem | *none* | v4.24.0 | 5,831 | 2026-01-08 |
| [Antoine-dSG/root_system](https://github.com/Antoine-dSG/root_system) | Root systems (type A) | Apache-2.0 | v4.30.0-rc2 | 506 | 2026-05-24 |

### Algebraic geometry

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [Paul-Lez/Stacks-project](https://github.com/Paul-Lez/Stacks-project) | Fibered categories and stacks | *none* | v4.24.0-rc1 | 6,119 | 2025-12-30 |
| [dagurtomas/LeanCondensed](https://github.com/dagurtomas/LeanCondensed) | Condensed mathematics | Apache-2.0 | v4.28.0-rc1 | 1,876 | 2026-03-20 |
| [smorel394/ExteriorPowers](https://github.com/smorel394/ExteriorPowers) | Exterior powers | *none* | v4.7.0-rc2 | 8,922 | 2024-01-12 |
| [smorel394/Grassmannian](https://github.com/smorel394/Grassmannian) | Grassmannian | *none* | v4.2.0-rc1 | 8,133 | 2024-10-08 |
| [smorel394/ProjectiveSpace_lean4](https://github.com/smorel394/ProjectiveSpace_lean4) | Projective space | *none* | v4.2.0-rc1 | 5,767 | 2024-01-16 |

### Combinatorics / graph theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [Antoine-dSG/frieze_patterns](https://github.com/Antoine-dSG/frieze_patterns) | Coxeter's frieze patterns | Apache-2.0 | v4.10.0-rc2 | 1,440 | 2025-03-18 |
| [ro-gut/turan3](https://github.com/ro-gut/turan3) | Turán's theorem (3rd proof, "from THE BOOK") | Apache-2.0 | v4.24.0-rc1 | 2,836 | 2025-09-24 |
| [aroheebhoja/vizing](https://github.com/aroheebhoja/vizing) | Vizing's theorem (Misra–Gries) | *none* | v4.21.0-rc3 | 3,752 | 2026-03-27 |
| [b-mehta/HighlyAbundant](https://github.com/b-mehta/HighlyAbundant) | Highly abundant numbers (MO/501066) | *none* | v4.24.0-rc1 | 12,957 | 2025-12-19 |
| [jcpaik/erdos-tuza-valtr](https://github.com/jcpaik/erdos-tuza-valtr) | Erdős–Tuza–Valtr conjecture | Apache-2.0 | v4.13.0-rc3 | 2,302 | 2024-11-09 |
| [NickAdfor/polynomial-method-restricted-sums](https://github.com/NickAdfor/The-polynomial-method-and-restricted-sums-of-congruence-classes) | Polynomial method, restricted sumsets | Apache-2.0 | v4.27.0-rc1 | 4,149 | 2026-03-13 |
| [dwrensha/Rupert.lean](https://github.com/dwrensha/Rupert.lean) | The Rupert problem for convex polyhedra | Apache-2.0 | v4.28.0 | 1,713 | 2026-04-05 |

### Analysis / probability / PDE

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [YellPika/quasi-borel-spaces](https://github.com/YellPika/quasi-borel-spaces) | Quasi-Borel spaces | MIT | v4.28.0-rc1 | 8,626 | 2026-04-10 |
| [FredRaj3/SemicircleLaw](https://github.com/FredRaj3/SemicircleLaw) | Wigner's semicircle law | MIT | v4.24.0 | 3,174 | 2026-04-11 |
| [cboone/zhang-yeung-inequality](https://github.com/cboone/zhang-yeung-inequality) | Zhang–Yeung non-Shannon inequality | Apache-2.0 | v4.28.0-rc1 | 5,008 | 2026-04-22 |
| [susannabertolini/PhaseRetrieval](https://github.com/susannabertolini/PhaseRetrieval) | Stable phase retrieval (Hermite–Fock) | Apache-2.0 | v4.29.0-rc6 | 60,247 | 2026-05-20 |

### Topology / differential geometry

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [Jun2M/Main-theorem-of-polytopes](https://github.com/Jun2M/Main-theorem-of-polytopes) | Main theorem of polytopes | Apache-2.0 | v4.7.0-rc2 | 2,293 | 2024-05-22 |
| [jzxia/WhiteheadTheorem](https://github.com/jzxia/WhiteheadTheorem) | Whitehead theorem (homotopy groups) | Apache-2.0 | v4.21.0-rc3 | 7,984 | 2026-03-12 |
| [unhyperbolic/hyperbolicGeometryInLean](https://github.com/unhyperbolic/hyperbolicGeometryInLean) | Hyperbolic geometry | *none* | nightly-2023-06-20 | 933 | 2025-11-07 |
| [adri326/rubin-lean4](https://github.com/adri326/rubin-lean4) | Rubin's theorem | *none* | v4.5.0-rc1 | 9,198 | 2024-03-29 |

### Categorical / higher categorical

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [kyoDralliam/model-theory-topos](https://github.com/kyoDralliam/model-theory-topos) | First-order model theory in a topos | *none* | v4.22.0-rc3 | 9,409 | 2026-01-29 |
| [mckoen/quasicategory](https://github.com/mckoen/quasicategory) | Quasi-categories | Apache-2.0 | v4.18.0-rc1 | 11,675 | 2025-10-25 |
| [themathqueen/monlib4](https://github.com/themathqueen/monlib4) | Non-commutative graph theory | Apache-2.0 | v4.21.0-rc3 | 31,853 | 2026-01-06 |

### Logic / set theory / foundations

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [FormalizedFormalLogic/Incompleteness](https://github.com/FormalizedFormalLogic/Incompleteness) | Gödel incompleteness | Apache-2.0 | v4.16.0-rc2 | 2,514 | 2025-09-23 |
| [mgignoux/lean4-gl-coalgebras](https://github.com/mgignoux/lean4-gl-coalgebras) | Craig interpolation for Gödel–Löb logic | Apache-2.0 | v4.28.0 | 9,594 | 2026-04-16 |

### CS-theory (graduate theoretical CS)

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [tannerduve/computability](https://github.com/tannerduve/computability) | Oracle computability, Turing degrees | Apache-2.0 | v4.24.0 | 3,035 | 2026-02-05 |
| [SamuelSchlesinger/circuit-complexity](https://github.com/SamuelSchlesinger/circuit-complexity) | Boolean circuit complexity | Apache-2.0 | v4.29.0-rc4 | 7,756 | 2026-05-29 |

### Quantum / physics

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [guest2180/lean4-quantum](https://github.com/guest2180/lean4-quantum) | Theory of quantum computing | *none* | v4.16.0 | 5,150 | 2025-12-27 |

### Miscellaneous research math

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [vihdzp/ordinal-notation](https://github.com/vihdzp/ordinal-notation) | Ordinal notations | *none* | v4.16.0-rc2 | 6,161 | 2025-07-20 |
| [Timeroot/lean-descartes-signs](https://github.com/Timeroot/lean-descartes-signs) | Descartes' rule of signs | *none* | v4.3.0-rc2 | 1,475 | 2025-09-04 |
| [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4) | Brouwer + Kakutani fixed-point theorems | *none* | v4.21.0-rc3 | 3,257 | 2026-03-04 |
| [LodeVermeulen/Lean4_Bogdanovs_lemma](https://github.com/LodeVermeulen/Lean4_Bogdanovs_lemma) | Bogdanov's lemma | *none* | v4.8.0-rc1 | 1,209 | 2024-07-03 |
| [oneofvalts/desargues](https://github.com/oneofvalts/desargues) | Desargues's theorem | Apache-2.0 | n/a | 1,221 | 2025-07-14 |
| [wwylele/PentagonalNumberTheorem](https://github.com/wwylele/PentagonalNumberTheorem) | Euler's pentagonal number theorem | Apache-2.0 | v4.26.0-rc2 | 2,856 | 2025-12-15 |
| [ADedecker/ProperAction](https://github.com/ADedecker/ProperAction) | Proper actions | *none* | v4.7.0-rc2 | 908 | 2024-05-14 |
| [AntoineChambert-Loir/Sion4](https://github.com/AntoineChambert-Loir/Sion4) | Sion's minimax theorem | *none* | v4.21.0-rc3 | 3,319 | 2025-09-26 |
| [SReichelt/universe-abstractions](https://github.com/SReichelt/universe-abstractions) | Mathematical universes | *none* | nightly-2022-01-14 | 19,432 | 2024-04-08 |
| [thejohncrafter/Catlib4](https://github.com/thejohncrafter/Catlib4) | Category theory + theoretical CS | *none* | nightly-2023-04-20 | 3,045 | 2024-11-25 |
| [ChrisHughes24/axgroth](https://github.com/ChrisHughes24/axgroth) | Ax–Grothendieck (likely) | *none* | v4.23.0-rc2 | 933 | 2026-03-29 |
| [Louis-Le-Grand/Formalisation-of-constructable-numbers](https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers) | Constructible numbers | *none* | v4.11.0-rc2 | 6,146 | 2024-11-13 |
| [penteract/pythagTreeProof](https://github.com/penteract/pythagTreeProof) | Area of the Pythagoras tree | *none* | v4.22.0-rc3 | 7,813 | 2025-07-22 |
| [samvang/StoneDualityInLean](https://github.com/samvang/StoneDualityInLean) | Stone duality | *none* | v4.8.0-rc1 | 1,079 | 2025-11-27 |

## Fit the criteria but unlicensed (criterion 2)

Every row above with **License = *none*** satisfies criteria 1, 3, and 4 but
ships no license file. Under the tightened criterion 2 these cannot be
imported as-is — lean-pool is Apache-2.0 and needs an explicit permissive
grant. Each becomes importable the moment its author adds a permissive
license (Apache-2.0 / MIT / BSD / 0BSD / ISC / Zlib); each is worth a
one-line issue requesting one.

Two further candidates from the AI-infused-formalization survey fit every
other criterion but are likewise unlicensed:

- [SamuelSchlesinger/complexitylib](https://github.com/SamuelSchlesinger/complexitylib) — computational complexity theory (Arora–Barak); v4.28.0, ~13,060 LOC, dormant since 2026-04-17.
- [LarsenClose/fixed-point-formalization](https://github.com/LarsenClose/fixed-point-formalization) — fixed points in monoidal closed categories; v4.28.0, ~8,328 LOC, dormant since 2026-03-05.

Closed import PRs that should not be retried until the blocker changes:

- `math-inc/KakeyaFiniteFields` — PR #33; good Lean Pool fit, but closed
  unmerged because the upstream repository has no explicit license.

## Dropped after import PR review

These candidates had import PRs closed without merge and should stay out of the
active shortlist/queues unless a materially stronger upstream or project scope
appears.

- `amarmaduke/lean-subst` — PR #168; reusable substitution/reduction
  infrastructure without a source-anchored headline theorem.
- `tsurumi-yizhou/SPG` — PR #159; computational spin-point-group routines
  without proved correctness/headline theorem.
- `gdncc/cryptography` — PR #47 and PR #158; SHA-3 implementation lacks a
  formal specification/correctness theorem.
- `tangentstorm/leansieve` — PR #153; elementary sieve verification, below the
  Lean Pool graduate/research project bar.
- `riccardobrasca/FLT3` — PR #150; advertised theorem is imported from Mathlib
  rather than proved by the project.
- `bjoernkjoshanssen/hypothesis` — PR #142; loose undergraduate
  statistics/examples collection without a source-anchored headline theorem.
- `pannous/hyper-lean` — PR #102 and PR #139; only introductory
  probability/measure examples survived, not the hyperreal project.
- `JoeyEremondi/lean-cwf` — PR #98 and PR #104; BSD-3-Clause license and
  substantial omitted upstream content under current criteria.
- `badly-drawn-wizards/noperthedron` — PR #91; auxiliary geometry fragments do
  not prove the advertised convex/no-Rupert headline theorem.
- `pitmonticone/QuadraticIntegers` — PR #87; support instances only; the
  quadratic-integers ring-of-integers theorem is absent.
- `or4nge19/NeuralNetworks` — PR #82; weak/overstated Hopfield convergence
  theorem and low code-quality assessment after scope narrowing.
- `Command-Master/lean-bourgain` — PR #64; support layers only, missing the
  Bourgain extractor/Szemeredi-Trotter theorem layer.
- `mkaratarakis/HopfieldNet` — PR #125; unresolved `sorry`/build backlog and
  duplicate overlap with the NeuralNetworks Hopfield core.
- `fpvandoorn/sard` — PR #95; Sard support API only, no Sard/Sard-Smale theorem.
- `sinhp/LeanFibredCategories` — PR #78; cartesian-morphism/fiber API only, no
  theorem-level endpoint.
- `RemyDegenne/testing-lower-bounds` — PR #62; only measure/kernel support API
  survived, not the lower-bound formalization.
- `misaka10987/archimedes` — PR #51; elementary coordinate-geometry API, no
  graduate/research headline result.

Closed import PRs superseded by later accepted imports:

- `jjdishere/neukirch` — PR #130 closed unmerged; now represented in
  [`LeanPool/projects.yml`](../LeanPool/projects.yml).
- `dhyan-aranha/Monsky` — PR #96 and PR #105 closed unmerged; now represented
  in [`LeanPool/projects.yml`](../LeanPool/projects.yml).
- `siddhartha-gadgil/Polylean` — PR #97 closed unmerged; now represented in
  [`LeanPool/projects.yml`](../LeanPool/projects.yml).
- `ivankobe/FactorizationSystems` — PR #99 closed unmerged; now represented in
  [`LeanPool/projects.yml`](../LeanPool/projects.yml).
- `VTrelat/ZFLean` — PR #100 closed unmerged; now represented in
  [`LeanPool/projects.yml`](../LeanPool/projects.yml).
- `ruplet/formalization-of-bounded-arithmetic` — PR #101 closed unmerged; now
  represented in [`LeanPool/projects.yml`](../LeanPool/projects.yml).

## Dropped by the tightened criteria

For transparency, entries that survived the previous (looser) draft of this
list but failed the staleness / Lean cutoff:

**Updated within the last month** (after 2026-04-16):

- `urkud/DeRhamCohomology` (2026-05-09)
- `mbkybky/QuillenSuslin` (2026-05-06)
- `mbkybky/InfiniteGaloisTheory` (2026-05-04)
- `uw-math-ai/FormalizingGMT` (2026-04-30)
- `weiran-sun/pde` (2026-04-29)
- `mitchell-horner/ErdosStoneSimonovitsKovariSosTuran` (2026-04-29)
- `taeyool/lean-flag-algebras` (2026-05-09)
- `JasonShroyer/sgc-lean` (2026-04-26)
- `mariovagomarzal/HigherCategoryTheory` (2026-04-25)
- `smmercuri/adele-ring_locally-compact` (2026-04-24)
- `Timeroot/CircuitComp` (2026-04-23)
- `cameronfreer/exchangeability` (2026-04-19)

**Lean toolchain ≥ v4.29** (regardless of date):

- `samuelborza/IsTranscendentalPi` (v4.30.0-rc2)
- `Akwardbro/RamificationGroup` (v4.29.0-rc2)
- `AntoineChambert-Loir/DividedPowers4` (v4.30.0-rc1)
- `chrisflav/proetale` (v4.30.0-rc2)
- `WuProver/lean_characteristic_set` (v4.29.0-rc6)
- `mattrobball/BridgelandStability` (v4.29.0)
- `chrisflav/pi1` (v4.30.0-rc2)
- `YijunYuan/HarderNarasimhan` (v4.29.1)
- `elazarg/GameTheory` (v4.29.0)
- `Parcly-Taxel/Redhill` (v4.30.0-rc2)
- `znssong/Frucht` (v4.29.0-rc4)
- `hwatheod/galeShapley` (v4.29.0-rc7)
- `mseri/BET` (v4.30.0-rc2)
- `or4nge19/MCMC` (v4.29.0)
- `mrdouglasny/jacobian-challenge` (v4.30.0-rc1)
- `mrdouglasny/gaussian-field` (v4.29.0)
- `Paul-Lez/PersistentDecomp` (v4.29.0)
- `AlexKontorovich/CoveringSpacesProject` (v4.29.0-rc8)
- `peabrainiac/lean-catdg` (v4.29.0)
- `riccardobrasca/SDG` (v4.30.0-rc2)
- `Mathias-Stout/Many-sorted-model-theory` (v4.30.0-rc2)
- `AlexeyMilovanov/kolmogorov-complexity-lean` (v4.29.0-rc8)
- `girving/aks` (v4.29.0-rc4)
- `SamuelSchlesinger/analysis-of-boolean-functions` (v4.29.0-rc6)
- `YanYablonovskiy/AlgebraicWheelTheory` (v4.29.0-rc6)
- `YijunYuan/SphericalCompleteness` (v4.29.1)

## Other near-misses (criterion 1 or 2)

- **YaelDillies/\*** (`APAP`, `Toric`, `AddCombi`, `ForbiddenMatrix`, `MeanFourier`) — actively pushed to mathlib by Yael.
- **apnelson1/Matroid**, **artie2000/real-closed-field**, **jsm28/AperiodicMonotilesLean**, **acmepjz/Iwasawalib**, **kbuzzard/ClassFieldTheory**, **scholzhannah/CWComplexes**, **oliver-butterley/SpectralThm**, **mbkybky/module_localProperties** — active mathlib-bound work or staging for mathlib upstream.
- **RemyDegenne/kolmogorov_extension4**, **RemyDegenne/clt**, **leanprover-community/SphereEversion**, **leanprover-community/add-combi**, **RemyDegenne/BrownianMotion**, **j-loreaux/LeanOA** — same reasoning (active mathlib pipeline).
- **frenzymath/Anderson-Conjecture**, **mrdouglasny/OSforGFF**, **AxiomMath/{ramanujan-tau-misses-primes,partial-regularity,dead-ends,lattice-triangle}** — already queued or imported (see [`import-queue.md`](import-queue.md) and [`LeanPool/projects.yml`](../LeanPool/projects.yml)).
- **MichaelStollBayreuth/{EulerProducts,Heights,LegendreQF,Weights}**, **leanprover/LeroyCompilerVerificationCourse**, **uw-math-ai/lean-polyhedral-geometry**, **lindy-labs/WadrayVerification**, **lindy-labs/corelib_verification**, **MohanadAhmed/LeanMathSigProc**, **parabamoghv/DashedMonoids**, **T-Brick/{controlflow,numbers}**, **klavins/LeanBook**, **katzenpost/crypt_walker**, **lexzaiello/DCC**, **Bergschaf/Localic-Caratheodory-Extensions** — copyleft (GPL / LGPL / AGPL / CC-BY-SA).
- **gift-framework/core**, **adambornemann-glitch/Logos_Library**, **Project-Navi/cd-formalization**, **AfonsoBitoque/LeanServer**, **Mintpath/p_ne_np**, **physicslib/Physicslib**, **vporton/atgt** — suspected crank, autogenerated, or unverifiable bold claims.
- **mortarsanjaya/IMOSLLean4**, **logical-intelligence/Putnam**, **mo271/FormalBook**, **FordUniver/thebook.lean**, **fpvandoorn/bonnAnalysis**, **kkytola/ExtremeValueProject** (course), **AnirudhG07/LeanHuffmanCoding**, **niklasmohrin/lean-seminar-2023**, **knowsys/Formale-Systeme-in-LEAN**, **kmill/msri2023_graphs**, **gmcninch-prof/VERSEIM-2025**, **DhyeyMavani2003/chip-firing-with-lean** — contests, courses, summer-school output, or textbook exercise sets.

## June 2026 refresh — new candidates

Curated 2026-06-07. New or newly-discovered projects that appeared / became active since the early-May sweep. For these recent additions the original staleness (criterion 3) and Lean ≤ v4.28 (criterion 4) cutoffs are relaxed — they are recent by nature; the actual Lean toolchain and last-commit date are shown so a maintainer can judge porting effort. Criteria 1 (serious research-/graduate-level math, CS, or physics) and 2 (permissive, Apache-2.0-compatible license) still gate inclusion below. Projects clearly staging for mathlib upstream are listed under near-misses, not as fresh picks.

### Number theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [xiangyazi24/invitation-to-qseries-lean](https://github.com/xiangyazi24/invitation-to-qseries-lean) | q-series: partitions, Jacobi triple product, Rogers-Ramanujan, Ramanujan congruences, mock theta (Chan textbook) | Apache-2.0 | v4.27.0 | 258,169 | 2026-06-06 |
| [logical-intelligence/erdos-unit-distance](https://github.com/logical-intelligence/erdos-unit-distance) | Bounds toward the Erdős unit-distance problem via class field towers (conditional on Golod–Shafarevich / Shafarevich relation-rank) | Apache-2.0 | v4.29.1 | 33,087 | 2026-05-28 |
| [axiommath/andrews_dhar_problem](https://github.com/AxiomMath/andrews_dhar_problem) | Andrews-Dhar partition equidistribution and 3-flat/3-regular bijection | MIT | v4.28.0 | 22,475 | 2026-06-03 |
| [mathlib-initiative/sum_product](https://github.com/mathlib-initiative/sum_product) | A sum-product–type bound fails over ℝ, conditional on Martinet totally-real towers (Bloom–Sawin–Schildkraut–Zhelezov); Dedekind-zeta theta–Mellin library | Apache-2.0 | v4.31.0-rc1 | 18,553 | 2026-06-04 |
| [elnando888/poissonviacrt](https://github.com/ElNando888/PoissonViaCRT) | Poisson statistics of CRT subsets via k-level correlation (Granville-Kurlberg) | Apache-2.0 | v4.29.0 | 17,869 | 2026-06-07 |
| [axiommath/partitionpolynomial](https://github.com/AxiomMath/PartitionPolynomial) | Reciprocals of partition polynomials (Ballantine-Beck-Feigon-Maurischat conjectures), arXiv:2605.21718 | MIT | v4.28.0 | 12,556 | 2026-05-22 |
| [wangfrankie/quadraticnumberfields](https://github.com/WangFrankie/QuadraticNumberFields) | Quadratic number fields: rings of integers, discriminants, prime splitting, class number | Apache-2.0 | v4.30.0-rc2 | 8,624 | 2026-06-07 |
| [elvec1o/kravitz-lonely-runner-n3](https://github.com/ElVec1o/kravitz-lonely-runner-n3) | n=3 Lonely Runner / view-obstruction coordinate bound (delta_2(4)<=3/14 input) | Apache-2.0 | v4.30.0 | 6,165 | 2026-06-04 |
| [arij-aziz/selberg_improvement_general](https://github.com/Arij-Aziz/Selberg_improvement_general) | Multi-prime Selberg sieve majorant: L2 identity, Mobius-weight optimality, mass-energy tradeoff | Apache-2.0 | v4.28.0 | 5,666 | 2026-06-07 |
| [elvec1o/five-distance-sharp](https://github.com/ElVec1o/five-distance-sharp) | Sharp five-distance & sup-norm gap theorems for Kronecker sequences on tori (g₂=5, g_∞≤2^d+1, g_∞(3)=9) | Apache-2.0 | v4.30.0 | 5,366 | 2026-06-04 |
| [elodinlaarz/lean-thesis](https://github.com/ElodinLaarz/lean-thesis) | Singular moduli & the ideal class group: quadratic orders, prime ramification via Legendre symbols, sqrt-counting mod prime powers | Apache-2.0 | v4.28.0 | 2,440 | 2026-06-07 |
| [gotrevor/erdos-403](https://github.com/gotrevor/erdos-403) | Erdos #403: sums of distinct factorials that are powers of 2 (finiteness + sharp bound m<=7) | Apache-2.0 | v4.29.1 | 1,076 | 2026-06-07 |

### Algebra / commutative algebra

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [spectra-research/asymptotic-tensor-rank-semicontinuity](https://github.com/spectra-research/asymptotic-tensor-rank-semicontinuity) | Asymptotic tensor rank semicontinuity / characterized by polynomials | Apache-2.0 | v4.27.0 | 59,472 | 2026-06-07 |
| [singerng/steinberg-formalization](https://github.com/singerng/steinberg-formalization) | Steinberg relations suffice to present the graded unipotent B3-large Chevalley group (O'Donnell-Singer) | Apache-2.0 | v4.15.0-rc1 | 11,204 | 2025-09-10 |
| [phylliida/lean-quadratic-extension](https://github.com/Phylliida/lean-quadratic-extension) | Order on a quadratic field extension F(√d), positive cone closed under addition | MIT | v4.25.0 | 264 | 2026-06-05 |

### Algebraic geometry

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [mgyamada/tropicalgeometry](https://github.com/MGYamada/TropicalGeometry) | Exact min-plus tropical algebra: hypersurface membership, initial forms, tropical determinant singularity certificates | Apache-2.0 | v4.30.0 | 12,361 | 2026-06-07 |
| [mgyamada/toricgeometry](https://github.com/MGYamada/ToricGeometry) | 2D toric geometry: dual cones, smooth fans, affine-chart atlas (P^2, P^1xP^1) | Apache-2.0 | v4.30.0 | 5,526 | 2026-06-07 |

### Combinatorics / graph theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [jzuiddam/asymptotic-spectrum-distance](https://github.com/jzuiddam/asymptotic-spectrum-distance) | Asymptotic spectrum distance, graph limits, Shannon capacity of odd cycles (new C15 bound) | Apache-2.0 | v4.30.0 | 93,238 | 2026-06-06 |
| [xiangyazi24/analyticcombinatorics](https://github.com/xiangyazi24/AnalyticCombinatorics) | Flajolet-Sedgewick Analytic Combinatorics: symbolic method, generating functions, saddle-point/partition asymptotics | Apache-2.0 | v4.29.0 | 61,689 | 2026-06-07 |
| [bryangingechen/combinatorialrigidity](https://github.com/bryangingechen/CombinatorialRigidity) | Combinatorial rigidity: Laman's theorem, Lee-Streinu pebble game, Tay body-bar/hinge, molecular conjecture | Apache-2.0 | v4.30.0-rc2 | 34,819 | 2026-06-07 |
| [pachterlab/p_2026_2](https://github.com/pachterlab/P_2026_2) | Optimal pebbling number of the hypercube is Theta((4/3)^n) | Apache-2.0 | v4.30.0-rc2 | 12,071 | 2026-06-06 |
| [npflueger/demazure](https://github.com/npflueger/demazure) | Demazure products and almost-sign-preserving (ASP) permutations | Apache-2.0 | v4.28.0 | 10,481 | 2026-05-28 |
| [math-inc/frontiermathopen-hypergraphs](https://github.com/math-inc/FrontierMathOpen-Hypergraphs) | Lower bounds for the extremal hypergraph Ramsey function H(n) (FrontierMath open problem): 26/25 uniform bound and Lubell asymptotic liminf H(n)/k(n) >= 2 ln 2 | Apache-2.0 | v4.28.0 | 7,510 | 2026-03-13 |
| [karlesmarin/godsil-gutman-lean](https://github.com/karlesmarin/godsil-gutman-lean) | Godsil-Gutman & Heilmann-Lieb matching polynomial + Bass/Ihara-zeta determinant formula in spectral graph theory | Apache-2.0 | v4.30.0-rc2 | 7,453 | 2026-06-07 |
| [axiommath/biswal](https://github.com/AxiomMath/Biswal) | Positivity of coefficients in Chebyshev quotients / Demazure multiplicities / Dyck-path models | MIT | v4.28.0 | 6,062 | 2026-04-30 |
| [smaniad/laminarfamiliesmaximalbinarytrees](https://github.com/SmaniaD/LaminarFamiliesMaximalBinaryTrees) | Rooted binary trees of disjoint Finset pairs / maximal laminar families | Apache-2.0 | v4.30.0-rc2 | 3,843 | 2026-05-16 |
| [wondermonger-daydreaming/semicircle-catalan](https://github.com/Wondermonger-daydreaming/semicircle-catalan) | Genus-zero pairings = noncrossing, counted by Catalan numbers (Wigner semicircle moments) | Apache-2.0 | v4.29.0-rc6 | 3,720 | 2026-05-30 |

### Analysis / probability / PDE

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [smaniad/besovspacesgoodgrid](https://github.com/SmaniaD/BesovSpacesGoodGrid) | Besov spaces via atomic decomposition over good/weak grids (Smania 2022) | Apache-2.0 | v4.30.0-rc2 | 44,740 | 2026-06-07 |
| [raphaelrrcoelho/formal-mathfin](https://github.com/raphaelrrcoelho/formal-mathfin) | Formal mathematical finance: Black-Scholes PDE/Greeks, binomial/CRR convergence, Ito calculus, Girsanov, portfolio theory, risk measures | Apache-2.0 | v4.30.0-rc2 | 33,516 | 2026-06-07 |
| [robby955/formalslt](https://github.com/Robby955/FormalSLT) | Finite-sample statistical learning theory: sharp McDiarmid, Rademacher/VC bounds, PAC-Bayes, Dudley chaining | MIT | v4.30.0-rc2 | 33,510 | 2026-06-04 |
| [smaniad/burkholder](https://github.com/SmaniaD/Burkholder) | Burkholder martingale transform inequality + sharp Lp estimates (Burkholder 1985) | Apache-2.0 | v4.30.0-rc2 | 22,502 | 2026-05-16 |
| [smaniad/unbalancedhaarwavelet](https://github.com/SmaniaD/UnbalancedHaarWavelet) | Unbalanced Haar wavelets: orthogonality, L^p density, martingale/Burkholder, unconditional Schauder bases | Apache-2.0 | v4.30.0-rc2 | 13,598 | 2026-05-23 |
| [abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov) | Rellich-Kondrachov compact Sobolev embedding H1->L2 on compact Riemannian manifolds | Apache-2.0 | v4.29.1 | 10,281 | 2026-05-14 |
| [mrdouglasny/bochner](https://github.com/mrdouglasny/bochner) | Bochner and Minlos theorems, nuclear spaces, white noise on S'(ℝ) | Apache-2.0 | v4.30.0 | 8,528 | 2026-06-05 |
| [fieldnote-echo/ordvec-formalization](https://github.com/Fieldnote-Echo/ordvec-formalization) | Finite Bayes-threshold optimality and hypergeometric calibration for bitmap overlap models | Apache-2.0 | v4.28.0 | 6,037 | 2026-06-04 |
| [frenzymath/qrcp-bounded-coherence-obstruction](https://github.com/frenzymath/qrcp-bounded-coherence-obstruction) | Bounded-coherence obstruction for exact QR column pivoting (QRCP) | Apache-2.0 | v4.30.0-rc2 | 5,679 | 2026-05-31 |
| [abenenson/cencov-petz](https://github.com/abenenson/cencov-petz) | Finite Cencov-Petz uniqueness: continuous monotone metrics on the probability simplex are scalar multiples of Fisher information | Apache-2.0 | v4.29.1 | 3,734 | 2026-05-14 |
| [mrdouglasny/spectral-positivity](https://github.com/mrdouglasny/spectral-positivity) | Perron-Frobenius, Jentzsch's theorem, M-matrix inverse positivity, operator positivity | Apache-2.0 | v4.30.0 | 2,635 | 2026-06-05 |
| [abenenson/compact-spectral](https://github.com/abenenson/compact-spectral) | Spectral theorem for compact self-adjoint operators (Hilbert basis of eigenvectors) | Apache-2.0 | v4.29.1 | 2,496 | 2026-05-14 |
| [abenenson/channel-capacity](https://github.com/abenenson/channel-capacity) | Uniqueness of capacity-achieving priors for Markov kernels (Shannon channel capacity) | Apache-2.0 | v4.29.1 | 2,475 | 2026-05-14 |
| [axiommath/agreetodisagree](https://github.com/AxiomMath/AgreeToDisagree) | Aumann's agreement theorem (common knowledge implies agreement on posteriors) | MIT | v4.28.0 | 1,464 | 2026-05-27 |
| [smaniad/unconditionalschauderbasis](https://github.com/SmaniaD/UnconditionalSchauderBasis) | Schauder bases and unconditional Schauder bases for Banach spaces (finite sign criterion) | Apache-2.0 | v4.30.0-rc2 | 1,416 | 2026-05-23 |
| [mirajcs/isoperimetricinequality](https://github.com/mirajcs/IsoperimetricInequality) | Isoperimetric inequality (Hurwitz/Fourier proof; Parseval, Wirtinger) | MIT | v4.27.0 | 1,365 | 2026-05-17 |
| [velvetmonkey/kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) | Finite-N Kuramoto synchronization: order-parameter bounds, Lyapunov descent, contraction, ODE existence | MIT | v4.31.0-rc1 | 989 | 2026-06-04 |
| [mrdouglasny/gibbs-variational](https://github.com/mrdouglasny/gibbs-variational) | Gibbs/Donsker-Varadhan variational principle + finite-dim Boue-Dupuis bound | Apache-2.0 | v4.30.0 | 489 | 2026-06-05 |

### Logic / set theory / foundations

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [jamesj64/lean-modal-logic](https://github.com/jamesj64/lean-modal-logic) | Soundness and completeness of modal logics K and S5 (canonical model construction) | MIT | v4.7.0-rc2 | 1,740 | 2026-05-01 |
| [abenenson/godel-loeb](https://github.com/abenenson/godel-loeb) | Modal provability logic (K4/GL): Loeb's theorem and modal second incompleteness | Apache-2.0 | v4.29.1 | 1,207 | 2026-05-14 |

### CS-theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [nikhgarg/econcslib](https://github.com/nikhgarg/EconCSLib) | Economics-and-Computation: mechanism design, matching markets, auctions, fair division, online algorithms (Gale-Shapley, Roth, MSVV07 AdWords, LMMS04, GN21 surge pricing) | Apache-2.0 | v4.30.0-rc2 | 650,074 | 2026-06-06 |
| [kim-em/hex](https://github.com/kim-em/hex) | Verified computational algebra: polynomial factoring (Berlekamp-Zassenhaus), LLL, finite fields | Apache-2.0 | v4.30.0-rc2 | 195,999 | 2026-06-05 |
| [khanukov/p-np2](https://github.com/khanukov/p-np2) | Hardness magnification / AC0 lower bounds toward P vs NP (conditional framework) | Apache-2.0 | v4.22.0-rc2 | 164,358 | 2026-06-01 |
| [grievejia/fwpython](https://github.com/grievejia/FwPython) | Gradual type system metatheory: soundness, blame, gradual guarantees for an OO language | MIT | v4.29.1 | 46,020 | 2026-05-12 |
| [input-output-hk/plutuscoreblaster](https://github.com/input-output-hk/PlutusCoreBlaster) | CEK machine + executable formal semantics of Plutus Core (Cardano UPLC) with verified crypto primitives | Apache-2.0 | v4.24.0 | 37,696 | 2026-05-22 |
| [verified-zkevm/polyfun](https://github.com/Verified-zkEVM/PolyFun) | Polynomial functors, interaction trees, and dependent interaction frameworks for protocol/PL semantics | Apache-2.0 | v4.30.0 | 35,027 | 2026-05-31 |
| [z-tech/z-lean](https://github.com/z-tech/z-lean) | Sumcheck protocol + Reed-Solomon codes + BCGM25 mutual-correlated-agreement (zk proof systems) | Apache-2.0 | v4.30.0-rc2 | 26,403 | 2026-05-31 |
| [bacon-labs/tamago](https://github.com/Bacon-labs/tamago) | Formal verification of EVM smart contracts and integer sqrt/cbrt/log correctness | MIT | v4.22.0 | 19,290 | 2026-05-26 |
| [leonardoalt/evm-smith](https://github.com/leonardoalt/evm-smith) | Verified EVM bytecode safety (WETH solvency, balance monotonicity) over formal Yellow-Paper semantics | Apache-2.0 | v4.22.0 | 18,715 | 2026-05-12 |
| [rayiskander2406/qanary-contracts](https://github.com/rayiskander2406/qanary-contracts) | Machine-checked soundness of OpenZeppelin ReentrancyGuard against an executable EVM/Yul semantics in Lean 4 | MIT | v4.30.0-rc1 | 10,161 | 2026-06-02 |
| [incremental-computing/autoinc-lean](https://github.com/incremental-computing/autoinc-lean) | Verified incremental computation: change structures and monadic differential operators | MIT | v4.27.0-rc1 | 6,352 | 2026-03-16 |
| [arademaker/bignum](https://github.com/arademaker/bignum) | Verified ARM crypto-bignum arithmetic (s2n-bignum port): machine semantics + Hoare-logic specs | Apache-2.0 | v4.30.0-rc2 | 4,637 | 2026-04-21 |
| [beneficial-ai-foundation/postquantumextendeddiffiehellman-model](https://github.com/Beneficial-AI-Foundation/PostQuantumeXtendedDiffieHellman-model) | PQXDH/X3DH key-agreement security (DDH reduction, ROM, game-based crypto) | MIT | v4.28.0 | 4,118 | 2026-05-13 |
| [kyrylr/phd-symmetric-cryptography](https://github.com/KyrylR/phd-symmetric-cryptography) | Verified canonical base-m byte-string encoding for finite-ring cryptosystems (encode/decode roundtrip + state-window invariants) | Apache-2.0 | v4.29.0-rc6 | 1,442 | 2026-05-18 |
| [garfieldnate/am_complexity_proof](https://github.com/garfieldnate/am_complexity_proof) | #P-completeness of exact Analogical Modeling scoring (via #⋃℘ / #VERTEX-COVER reductions) | MIT | v4.29.1 | 1,210 | 2026-06-07 |
| [josejj2143/cook-levin-lean](https://github.com/josejj2143/Cook-Levin-Lean) | Constructive Cook-Levin reduction (Turing machines to SAT/CNF) | MIT | n/a | 754 | 2026-06-07 |

### Quantum / physics

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [yezhuoyang/formalrv](https://github.com/yezhuoyang/FormalRV) | Formal verification of Shor's algorithm + fault-tolerant resource estimation (quantum circuits, lattice surgery, QEC) | MIT | v4.29.1 | 125,970 | 2026-06-06 |
| [mrdouglasny/pphi2](https://github.com/mrdouglasny/pphi2) | Construction of phi^4_2 Euclidean QFT (Osterwalder-Schrader axioms, Glimm-Jaffe/Nelson) | Apache-2.0 | v4.30.0 | 80,612 | 2026-06-07 |
| [hayata-yamasaki-group/lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum) | Quantum information theory: Lieb-Ando trace inequality, Lowner-Heinz, Jensen operator inequality, sandwiched Renyi relative entropy, quantum channels | Apache-2.0 | v4.29.0-rc6 | 15,730 | 2026-05-26 |
| [unitaryfoundation/stabrank](https://github.com/unitaryfoundation/stabrank) | Stabilizer-rank bounds for qutrit/qubit magic-state decompositions (Labib-Russo 2026) | Apache-2.0 | v4.29.1 | 1,714 | 2026-06-02 |
| [marozols/clifford-project](https://github.com/marozols/clifford-project) | Structure theorem for the single-qudit Clifford group (SL(2,Z_d) ⋉ Z_d^2), odd prime d | Apache-2.0 | v4.30.0 | 1,150 | 2026-06-05 |

### Miscellaneous research math

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [jingyuanli-hk/-wakker-debreu-koopmans-lean](https://github.com/jingyuanli-hk/-wakker-debreu-koopmans-lean) | Wakker additive representation + Debreu-Koopmans concavity (decision/measurement theory) | Apache-2.0 | v4.28.0-rc1 | 53,631 | 2026-06-07 |

### Fit the criteria but unlicensed (criterion 2)

Substantive and on-topic, but ship no explicit permissive license — not importable as-is. Worth a one-line issue asking the author to add Apache-2.0 / MIT / BSD / ISC / 0BSD / Zlib.

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [jayyhk/erdos-lean](https://github.com/Jayyhk/erdos-lean) | Solutions to erdosproblems.com (number theory, combinatorics, graph theory) | *none* | v4.24.0 | 413,945 | 2026-06-07 |
| [aria1th/torus-hamilton-decomposition-program](https://github.com/aria1th/Torus-Hamilton-Decomposition-Program) | Hamilton decompositions of directed odd-modulus torus Cayley digraphs (all d>=2, odd m>=3) | *none* | v4.30.0-rc2 | 162,281 | 2026-05-10 |
| [xiangyazi24/ssexactmajority](https://github.com/xiangyazi24/SSExactMajority) | Time/space-optimal silent self-stabilizing exact majority in population protocols (Kanaya 2025; Burman ranking) | *none* | v4.30.0 | 111,734 | 2026-06-06 |
| [junwei-lu/lean-asymptotic-statistical-theory](https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory) | Asymptotic statistical theory (van der Vaart 1998): LAN, local asymptotic minimax, Hajek-Le Cam convolution, empirical processes, semiparametric efficiency | *none* | v4.29.1 | 80,903 | 2026-06-06 |
| [d0d1/singer-theorem-lean](https://github.com/d0d1/singer-theorem-lean) | Singer's theorem on cyclic difference sets / Sidon sets (Erdos #30) | GPL-3.0 | v4.29.0 | 62,481 | 2026-05-11 |
| [dominicbreuker/cook-levin-lean](https://github.com/DominicBreuker/cook-levin-lean) | Cook-Levin theorem (SAT is NP-complete), WIP Coq->Lean port | *none* | v4.30.0-rc2 | 45,978 | 2026-06-07 |
| [nielstron/rust_constraining_lean](https://github.com/nielstron/rust_constraining_lean) | Soundness (progress, preservation, borrow safety) of a featherweight Rust (FR) calculus | *none* | v4.31.0-rc1 | 24,485 | 2026-06-07 |
| [logical-intelligence/cayley-adj3](https://github.com/logical-intelligence/cayley-adj3) | Diameter of the adjacent-3-cycle Cayley graph of the alternating group A_n equals floor(n^2/4) | *none* | v4.27.0-rc1 | 18,116 | 2026-05-06 |
| [yuanhez/prim](https://github.com/YuanheZ/Prim) | Erdos #1196/#1217: primitive sets and von Mangoldt chains | *none* | v4.30.0-rc2 | 14,593 | 2026-06-04 |
| [dominique-unruh/plonk-lean](https://github.com/dominique-unruh/plonk-lean) | Formalization of Plonk zkSNARK security + framework for cryptographic proofs in Lean | *none* | v4.30.0 | 13,392 | 2026-06-07 |
| [oe-parks/blossom](https://github.com/oe-parks/Blossom) | Edmonds' blossom algorithm correctness via a verified graph IR (matching theory, Berge, BFS) | *none* | v4.29.1 | 12,826 | 2026-05-10 |
| [verifiedqc/lean-qec](https://github.com/VerifiedQC/Lean-QEC) | Quantum error correction: stabilizer/CSS codes and verified SAT-based code-distance pipeline | *none* | v4.30.0-rc2 | 11,606 | 2026-06-04 |
| [ryangibb/package-calculus](https://github.com/RyanGibb/package-calculus) | Package Calculus: formal model of dependency resolution + NP-completeness (3SAT reduction) | *none* | v4.28.0 | 11,090 | 2026-06-07 |
| [yuanhez/erdosgraham](https://github.com/YuanheZ/ErdosGraham) | Irrationality of rapidly converging series (Erdos-Graham problem #1051) | *none* | v4.28.0 | 8,514 | 2026-06-04 |
| [duckki/graphcoql](https://github.com/duckki/GraphCoQL.lean) | Lean 4 port of GraphCoQL: mechanized GraphQL query semantics, schema conformance, normal forms | *none* | v4.30.0 | 8,511 | 2026-06-07 |
| [sun123zxy/nilpotent-orbit-classical-formalization](https://github.com/sun123zxy/nilpotent-orbit-classical-formalization) | Dominance-order covers for admissible partitions of classical Lie types (nilpotent orbits) | *none* | v4.30.0-rc2 | 8,325 | 2026-05-31 |
| [xiangyazi24/pp-proof](https://github.com/xiangyazi24/pp-proof) | O(n log n) convergence of 3-state approximate majority population protocol (Angluin-Aspnes-Eisenstat) | *none* | v4.27.0 | 7,312 | 2026-04-25 |
| [monoid-gmbh/actus-spec-lean](https://github.com/monoid-gmbh/actus-spec-lean) | Formal spec of ACTUS financial contracts as state machines; relational↔functional agreement + payoff-bound metatheorems | *none* | v4.30.0 | 5,440 | 2026-06-07 |
| [tomdif/eml-lean](https://github.com/tomdif/eml-lean) | All elementary functions from one operator eml(x,y)=exp x−ln y; +modular cocycle/Hecke arc | *none* | v4.29.0 | 4,708 | 2026-05-12 |
| [d0d1/lean-stokes-theorem](https://github.com/d0d1/lean-stokes-theorem) | Stokes' theorem for smooth singular cubes and axis-aligned boxes (differential forms) | GPL-3.0-only | v4.29.1 | 4,081 | 2026-05-07 |
| [yuanhez/erdos1196](https://github.com/YuanheZ/Erdos1196) | Erdos #1196: primitive-set Erdos sum bound f(A) <= 1 + C/log x (Erdos-Sarkozy-Szemeredi) | *none* | v4.30.0-rc2 | 3,989 | 2026-06-04 |
| [tomtreijn/rsk](https://github.com/TomTreijn/RSK) | Robinson-Schensted-Knuth correspondence (Young tableaux, RSK bijection) | *none* | v4.28.0-rc1 | 3,650 | 2026-06-07 |
| [duckki/quantum-computing-lean](https://github.com/duckki/quantum-computing-lean) | Quantum computing: matrices, gates, measurement, no-cloning theorem | *none* | v4.29.1 | 2,908 | 2026-05-31 |
| [formalizedformallogic/veryweaksubintuitionistic](https://github.com/FormalizedFormalLogic/VeryWeakSubintuitionistic) | Completeness of very weak subintuitionistic propositional and modal logics | CC-BY-SA-4.0 | v4.31.0-rc1 | 2,863 | 2026-06-07 |
| [mrdouglasny/reflection-positivity](https://github.com/mrdouglasny/reflection-positivity) | Reflection positivity (Osterwalder-Schrader & Freedman-Lovasz-Schrijver), gapped transfer operators for constructive QFT | *none* | v4.30.0 | 2,556 | 2026-06-05 |
| [jeremiahhockaday/setcoloringgames_lean4](https://github.com/JeremiahHockaday/SetColoringGames_Lean4) | Set coloring / combinatorial games (Primordial QPF games, Hex, game order) | *none* | v4.29.0-rc8 | 2,532 | 2026-06-06 |
| [bll4/ramseyb8b10](https://github.com/BLL4/RamseyB8B10) | Book Ramsey number upper bound R(B_8,B_10) <= 37 via SRG spectral obstruction | *none* | v4.29.1 | 1,799 | 2026-05-18 |
| [oliver-butterley/fec](https://github.com/oliver-butterley/FEC) | Finite-field elliptic curves: twisted Edwards/Montgomery models, Curve25519/Ed25519 group law via Mathlib Weierstrass | *none* | v4.30.0 | 1,720 | 2026-06-07 |
| [jacobparish/cs294-project](https://github.com/jacobparish/cs294-project) | Kleene-Post theorem: existence of incomparable Turing degrees; relativized oracle partial-recursive codes | *none* | v4.28.0 | 1,383 | 2026-05-08 |
| [seewoo5/differentproofs](https://github.com/seewoo5/DifferentProofs) | Multiple proofs of Fermat's little theorem and infinitude of primes | *none* | v4.30.0 | 1,368 | 2026-06-05 |
| [hlxy-420/guthkatzjointtheorem](https://github.com/HLXY-420/GuthKatzJointTheorem) | Joints conjecture / Guth-Katz theorem: O(\|L\|^{3/2}) joints from L lines in R^3 | *none* | v4.28.0 | 1,176 | 2026-05-07 |
| [yhx-12243/sidon3](https://github.com/yhx-12243/Sidon3) | Sidon constant of {0,1,2,3} equals 5/3 | *none* | v4.30.0-rc2 | 926 | 2026-05-11 |
| [formalizedformallogic/seqpl](https://github.com/FormalizedFormalLogic/SeqPL) | Gentzen sequent calculus for provability logic GL (soundness/completeness/cut-elimination) | *none* | v4.30.0-rc2 | 740 | 2026-05-14 |
| [arhaan2/formalizing-online-prediction-from-halving-to-hedge-in-lean](https://github.com/Arhaan2/Formalizing-Online-Prediction-From-Halving-to-Hedge-in-Lean) | Online learning: Halving mistake bound, Hoeffding log-MGF, Weighted Majority & Hedge regret | *none* | v4.28.0 | 721 | 2026-05-08 |
| [nyxfoundation/goldfish-fv](https://github.com/NyxFoundation/goldfish-fv) | Safety/liveness of the Goldfish Ethereum consensus protocol (synchronous sleepy model) | *none* | v4.29.0 | 713 | 2026-05-27 |

### Near-misses — active mathlib-bound work

On-topic and often permissively licensed, but being pushed toward mathlib upstream (or by a mathlib maintainer), so importing into lean-pool would duplicate or conflict with that pipeline.

- [cbirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) — Dirichlet density of prime ideals, toward Chebotarev's density theorem (Apache-2.0, v4.31.0-rc1).
- [grunweg/sobolevslobodeckij](https://github.com/grunweg/SobolevSlobodeckij) — Sobolev-Slobodeckij spaces: weak derivatives, MemSobolev, Sobolev norm/embedding (no license, v4.30.0).
- [mbkybky/strictaffinoid](https://github.com/mbkybky/StrictAffinoid) — Tate algebras, strict affinoid algebras, Weierstrass preparation and Noether normalization (Apache-2.0, v4.31.0-rc1).
- [peralexandersson/realrooted](https://github.com/PerAlexandersson/RealRooted) — Real-rooted polynomials, interlacing, compatibility, Sturm sequences, Veronese/Hurwitz matrices (no license, v4.30.0-rc2).
- [riccardobrasca/kummercriterion](https://github.com/riccardobrasca/KummerCriterion) — Kummer's criterion: regular primes via Bernoulli numerators; FLT for exponents <100 (Apache-2.0, v4.31.0-rc1).
- [scottcarnahan/vertexalg](https://github.com/ScottCarnahan/vertexAlg) — Vertex operator algebras (toward Monster VOA / Monstrous Moonshine) (Apache-2.0, v4.30.0-rc2).
- [whysoserioushah/cupproduct](https://github.com/Whysoserioushah/CupProduct) — Group/Tate cohomology, cup products, Herbrand quotient (class field theory infra) (no license, v4.30.0-rc1).
- [xroblot/skw](https://github.com/xroblot/SKW) — Stickelberger's theorem and Kronecker-Weber via Stickelberger (Gauss sums, cyclotomic fields) (no license, v4.31.0-rc1).
- [xylem-group/lopt-entropy-formal](https://github.com/Xylem-Group/lopt-entropy-formal) — Generalized inverse (quantile fn) of StieltjesFunction + NIST SP 800-90B min-entropy estimators (Apache-2.0, v4.30.0).
- [yssnbkd/mathlib4-computable-analysis](https://github.com/YssnBkd/mathlib4-computable-analysis) — Computable analysis (Pour-El & Richards): computability structures on reals and C[a,b] (Apache-2.0, v4.31.0-rc1).

### Other on-topic includes (tracked, not shortlisted)

Classified `include=true` and recorded in [`decisions.jsonl`](decisions.jsonl) / [`manual.txt`](manual.txt), but held back from the picks above — typically a blueprint with substantial `sorry` in its high-level assembly, an under-250-line fragment, a near-duplicate/rename of an already-tracked project, or otherwise borderline. Listed for completeness.

- [amellendijk/lean-bombieri-vinogradov](https://github.com/amellendijk/lean-bombieri-vinogradov) — Bombieri-Vinogradov theorem (GRH on average) blueprint formalization (Apache-2.0, v4.28.0, 3,384 LOC) — Active blueprint formalizing Bombieri-Vinogradov (analytic number theory). 3384 LOC own code; Delta.lean (877 lines) and
- [cbirkbeck/adic-spaces](https://github.com/CBirkbeck/Adic-Spaces) — Adic spaces (Wedhorn): valuation spectrum, Huber/Tate rings, Tate algebras, perfectoid spaces, tilting (Apache-2.0, v4.29.0-rc6, 126,076 LOC) — Large p-adic geometry formalization (Wedhorn adic spaces, Tate algebras, perfectoid/tilting) by mathlib contributor C. B
- [cgarryza/levystochcalc](https://github.com/cgarryZA/LevyStochCalc) — Lévy-driven stochastic calculus: Itô-Lévy isometry/formula, BSDEJs (Apache-2.0, v4.30.0-rc2, 18,725 LOC) — Serious ~18.7k-line Lévy stochastic-calculus formalization with real measure-theoretic proofs (simple-integral isometry,
- [jlebar/vir](https://github.com/jlebar/vir) — Formally-verified compiler IR (LLVM-like) with dominator analysis and fixed-point termination proofs (Apache-2.0, v4.27.0, 3,690 LOC) — Formally-verified LLVM-like compiler IR: type-safe IDs, instruction validation predicates, dominator analysis, real fixe
- [nktkt/starlib](https://github.com/nktkt/starlib) — Formally verified SNARKs / Interactive Oracle Reductions (IOR theory, coding theory, FRI/WHIR/Binius/Sumcheck) (Apache-2.0, v4.29.0, 63,412 LOC) — Serious 63k-LOC Lean formalization of SNARKs/Interactive Oracle Reductions + coding theory (FRI/WHIR/Binius/Sumcheck): 1
- [solpin-manai/sperner-lean](https://github.com/Solpin-manai/sperner-lean) — Sperner's Lemma (combinatorial topology, standard-simplex triangulation parity) (Apache-2.0, v4.27.0-rc1, 3,591 LOC) — Genuine WIP formalization of Sperner's Lemma (combinatorial topology). Active Mathlibb lib ~1015 LOC, real completed pro
