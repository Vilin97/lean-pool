# Lean Pool shortlist

Working list of candidate projects considered for import into `lean-pool`. The
candidates table at [`README.md`](README.md) is the source. This shortlist is
everything in that table judged to fit the criteria below, organised by topic,
with the user's initial picks (down to `b-mehta/AharoniKorman`-level depth)
listed first.

Curated 2026-05-16. Projects already in lean-pool (see
[`LeanPool/projects.yml`](../LeanPool/projects.yml)) are omitted. So is
`math-inc/KakeyaFiniteFields` (imported via PR #33).

## Selection criteria (all four required)

1. **Substantive research- or graduate-level mathematics.** A named theorem, a
   paper formalisation, or a clearly-defined research topic. Not contests,
   courses, exercise sets, programming-language metatheory, verification tools,
   or libraries.
2. **Permissive license or none.** MIT / Apache-2.0 / BSD / 0BSD / Zlib all OK.
   Absent license is OK when the content is clearly research math (the import
   step can chase the author for a license). Copyleft (GPL / LGPL / AGPL /
   CC-BY-SA) is out.
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
| [Luka-O/polya-enumeration-theorem](https://github.com/Luka-O/polya-enumeration-theorem) | Pólya enumeration theorem | MIT | v4.14.0-rc2 | 1,419 | 2025-09-11 |
| [b-mehta/ABCExceptions](https://github.com/b-mehta/ABC-Exceptions) | Exceptions to the ABC conjecture | Apache-2.0 | v4.21.0-rc3 | 3,353 | 2026-04-03 |
| [658060/topos](https://github.com/658060/topos) | Topos theory |  | v4.15.0 | 1,571 | 2026-02-20 |
| [andrejbauer/partial-combinatory-algebras](https://github.com/andrejbauer/partial-combinatory-algebras) | Partial combinatory algebras | MIT | v4.15.0-rc1 | 1,270 | 2025-06-23 |
| [sven-manthe/A-formalization-of-Borel-determinacy-in-Lean](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) | Borel determinacy | Apache-2.0 | v4.28.0-rc1 | 8,277 | 2026-02-26 |
| [RemyDegenne/testing-lower-bounds](https://github.com/RemyDegenne/testing-lower-bounds) | Information theory & hypothesis testing | Apache-2.0 | v4.13.0-rc3 | 13,201 | 2026-04-15 |
| [b-mehta/AharoniKorman](https://github.com/b-mehta/AharoniKorman) | Disproof of the Aharoni–Korman conjecture | Apache-2.0 | v4.16.0-rc2 | 1,288 | 2025-12-01 |
| [YnirPaz/PCF-Theory](https://github.com/YnirPaz/PCF-Theory) | PCF theory (Shelah) | MIT | v4.18.0-rc1 | 1,193 | 2026-02-24 |
| [calcu16/lean_complexity](https://github.com/calcu16/lean_complexity) | Complexity analysis |  | v4.5.0-rc1 | 5,595 | 2025-02-04 |

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
| [ahhwuhu/Zeta3Irrational](https://github.com/ahhwuhu/zeta_3_irrational) | Apéry: ζ(3) is irrational | Apache-2.0 | v4.18.0 | 4,157 | 2026-03-20 |
| [seewoo5/lean-poly-abc](https://github.com/seewoo5/lean-poly-abc) | Mason–Stothers (polynomial ABC) |  | v4.9.0-rc2 | 1,290 | 2026-03-04 |
| [alainchmt/RingOfIntegersProject](https://github.com/alainchmt/RingOfIntegersProject) | Certifying rings of integers in number fields | Apache-2.0 | v4.14.0-rc2 | 93,799 | 2026-03-20 |
| [Command-Master/lean-bourgain](https://github.com/Command-Master/lean-bourgain) | Bourgain's pseudorandomness | Apache-2.0 | v4.7.0 | 7,322 | 2024-11-05 |
| [FLDutchmann/selberg-sieve4](https://github.com/FLDutchmann/selberg-sieve4) | Selberg sieve | Apache-2.0 | v4.7.0-rc2 | 3,534 | 2026-04-08 |
| [BarinderBanwait/ramanujan_nagell](https://github.com/BarinderBanwait/ramanujan_nagell) | Ramanujan–Nagell theorem |  | v4.26.0-rc2 | 3,571 | 2026-04-08 |
| [jjdishere/neukirch](https://github.com/jjdishere/neukirch) | Neukirch ANT formalisation |  | v4.5.0-rc1 | 4,756 | 2024-12-03 |
| [KisaraBlue/ec-tate-lean](https://github.com/KisaraBlue/ec-tate-lean) | Elliptic curves, Tate's algorithm |  | nightly-2023-08-19 | 7,786 | 2024-05-26 |
| [kckennylau/EllipticCurve](https://github.com/kckennylau/EllipticCurve) | Elliptic curve over schemes | Apache-2.0 | v4.25.0-rc2 | 7,309 | 2025-11-04 |
| [mariainesdff/ostrowski2024](https://github.com/mariainesdff/ostrowski2024) | Ostrowski's theorem |  | v4.26.0-rc2 | 2,507 | 2025-12-14 |
| [pitmonticone/QuadraticIntegers](https://github.com/pitmonticone/QuadraticIntegers) | Ring of integers in quadratic fields | Apache-2.0 | v4.24.0 | 2,126 | 2026-03-09 |

### Algebra / commutative algebra

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [LieLean/LowDimSolvClassification](https://github.com/LieLean/LowDimSolvClassification) | Solvable Lie algebras (dim ≤ 3) | Apache-2.0 | v4.19.0 | 5,595 | 2025-10-09 |
| [jonhanke/quadratic_forms_in_lean](https://github.com/jonhanke/quadratic_forms_in_lean) | Quadratic forms |  | v4.19.0-rc3 | 2,113 | 2025-09-07 |
| [Whysoserioushah/BrauerGroup_new](https://github.com/Whysoserioushah/BrauerGroup_new) | Brauer groups | Apache-2.0 | v4.26.0-rc2 | 14,855 | 2026-03-20 |
| [mariainesdff/LocalClassFieldTheory](https://github.com/mariainesdff/LocalClassFieldTheory) | Local fields, towards LCFT |  | v4.22.0-rc2 | 14,717 | 2026-03-10 |
| [JobPetrovcic/ArtinWedderburn](https://github.com/JobPetrovcic/ArtinWedderburn) | Artin–Wedderburn theorem | MIT | v4.14.0-rc2 | 2,768 | 2025-07-14 |
| [xyzw12345/CohenMacaulay](https://github.com/xyzw12345/CohenMacaulay) | Cohen–Macaulay rings |  | v4.19.0-rc2 | 2,083 | 2025-05-01 |
| [AntoineChambert-Loir/Jordan4](https://github.com/AntoineChambert-Loir/Jordan4) | Jordan's theorem on permutation groups |  | v4.16.0 | 13,660 | 2025-09-13 |
| [bolito2/DemazureOperatorsLean](https://github.com/bolito2/DemazureOperatorsLean) | Demazure operators | Apache-2.0 | v4.14.0-rc3 | 2,927 | 2025-02-20 |
| [wupr/order-p-q](https://github.com/wupr/order-p-q) | Classification of groups of order p·q | Apache-2.0 | v4.15.0 | 924 | 2026-01-19 |
| [AlexBrodbelt/DicksonsClassificationTheorem](https://github.com/AlexBrodbelt/DicksonsClassificationTheorem) | Dickson's classification theorem |  | v4.24.0 | 5,831 | 2026-01-08 |

### Algebraic geometry

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [Paul-Lez/Stacks-project](https://github.com/Paul-Lez/Stacks-project) | Fibered categories and stacks |  | v4.24.0-rc1 | 6,119 | 2025-12-30 |
| [chrisflav/bruhat-tits](https://github.com/chrisflav/bruhat-tits) | Bruhat–Tits tree | Apache-2.0 | v4.19.0 | 8,284 | 2026-02-17 |
| [dagurtomas/LeanCondensed](https://github.com/dagurtomas/LeanCondensed) | Condensed mathematics | Apache-2.0 | v4.28.0-rc1 | 1,876 | 2026-03-20 |
| [smorel394/ExteriorPowers](https://github.com/smorel394/ExteriorPowers) | Exterior powers |  | v4.7.0-rc2 | 8,922 | 2024-01-12 |
| [smorel394/Grassmannian](https://github.com/smorel394/Grassmannian) | Grassmannian |  | v4.2.0-rc1 | 8,133 | 2024-10-08 |
| [smorel394/ProjectiveSpace_lean4](https://github.com/smorel394/ProjectiveSpace_lean4) | Projective space |  | v4.2.0-rc1 | 5,767 | 2024-01-16 |

### Combinatorics / graph theory

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [Antoine-dSG/frieze_patterns](https://github.com/Antoine-dSG/frieze_patterns) | Coxeter's frieze patterns |  | v4.10.0-rc2 | 1,440 | 2025-03-18 |
| [ro-gut/turan3](https://github.com/ro-gut/turan3) | Turán's theorem (3rd proof, "from THE BOOK") |  | v4.24.0-rc1 | 2,836 | 2025-09-24 |
| [aroheebhoja/vizing](https://github.com/aroheebhoja/vizing) | Vizing's theorem (Misra–Gries) |  | v4.21.0-rc3 | 3,752 | 2026-03-27 |
| [b-mehta/HighlyAbundant](https://github.com/b-mehta/HighlyAbundant) | Highly abundant numbers (MO/501066) |  | v4.24.0-rc1 | 12,957 | 2025-12-19 |
| [jcpaik/erdos-tuza-valtr](https://github.com/jcpaik/erdos-tuza-valtr) | Erdős–Tuza–Valtr conjecture |  | v4.13.0-rc3 | 2,302 | 2024-11-09 |
| [NickAdfor/polynomial-method-restricted-sums](https://github.com/NickAdfor/The-polynomial-method-and-restricted-sums-of-congruence-classes) | Polynomial method, restricted sumsets |  | v4.27.0-rc1 | 4,149 | 2026-03-13 |
| [badly-drawn-wizards/noperthedron](https://github.com/badly-drawn-wizards/noperthedron) | Convex polyhedron without Rupert property | Apache-2.0 | v4.25.0-rc2 | 1,105 | 2026-02-15 |

### Analysis / probability / PDE

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [YellPika/quasi-borel-spaces](https://github.com/YellPika/quasi-borel-spaces) | Quasi-Borel spaces | MIT | v4.28.0-rc1 | 8,626 | 2026-04-10 |
| [SamuelSchlesinger/shannon-1948-formalization](https://github.com/SamuelSchlesinger/shannon-1948-formalization) | Shannon's 1948 entropy paper | MIT | v4.28.0 | 1,912 | 2026-04-11 |
| [FredRaj3/SemicircleLaw](https://github.com/FredRaj3/SemicircleLaw) | Wigner's semicircle law | MIT | v4.24.0 | 3,174 | 2026-04-11 |
| [kkytola/VirasoroProject](https://github.com/kkytola/VirasoroProject) | Virasoro algebra, Witt 2-cohomology | Apache-2.0 | v4.27.0-rc1 | 6,026 | 2026-04-05 |
| [urkud/SardMoreira](https://github.com/urkud/SardMoreira) | Moreira's Sard theorem | Apache-2.0 | v4.27.0-rc1 | 4,869 | 2025-12-27 |
| [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff) | Pointwise Birkhoff ergodic theorem | Apache-2.0 | v4.20.0-rc5 | 567 | 2025-06-20 |
| [seb488/LeanComplexAnalysis](https://github.com/seb488/LeanComplexAnalysis) | Classical complex analysis theorems | Apache-2.0 | v4.28.0-rc1 | 4,910 | 2026-03-19 |
| [bjoernkjoshanssen/hypothesis](https://github.com/bjoernkjoshanssen/hypothesis) | Probability and statistics |  | v4.27.0-rc1 | 5,401 | 2026-02-18 |
| [fpvandoorn/sard](https://github.com/fpvandoorn/sard) | General Sard theorem | Apache-2.0 | v4.12.0 | 1,360 | 2024-10-07 |
| [nasqret/fineqs](https://github.com/nasqret/fineqs) | arXiv 1906.11174 (Cauchy–Davenport flavour) | Apache-2.0 | v4.24.0 | 648 | 2026-01-26 |

### Topology / differential geometry

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [dhyan-aranha/Monsky](https://github.com/dhyan-aranha/Monsky) | Monsky's theorem (UvA Lean community) | Apache-2.0 | v4.16.0-rc2 | 8,137 | 2025-10-30 |
| [Dominique-Lawson/Directed-Topology-Lean-4](https://github.com/Dominique-Lawson/Directed-Topology-Lean-4) | Directed topology | MIT | v4.6.0-rc1 | 6,721 | 2026-03-26 |
| [Jun2M/Main-theorem-of-polytopes](https://github.com/Jun2M/Main-theorem-of-polytopes) | Main theorem of polytopes |  | v4.7.0-rc2 | 2,293 | 2024-05-22 |
| [jzxia/WhiteheadTheorem](https://github.com/jzxia/WhiteheadTheorem) | Whitehead theorem (homotopy groups) |  | v4.21.0-rc3 | 7,984 | 2026-03-12 |
| [unhyperbolic/hyperbolicGeometryInLean](https://github.com/unhyperbolic/hyperbolicGeometryInLean) | Hyperbolic geometry |  | nightly-2023-06-20 | 933 | 2025-11-07 |
| [adri326/rubin-lean4](https://github.com/adri326/rubin-lean4) | Rubin's theorem |  | v4.5.0-rc1 | 9,198 | 2024-03-29 |

### Categorical / higher categorical

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [siddhartha-gadgil/Polylean](https://github.com/siddhartha-gadgil/Polylean) | Polylean (category theory) | Apache-2.0 | v4.19.0-rc3 | 5,102 | 2025-06-02 |
| [kyoDralliam/model-theory-topos](https://github.com/kyoDralliam/model-theory-topos) | First-order model theory in a topos |  | v4.22.0-rc3 | 9,409 | 2026-01-29 |
| [sinhp/LeanFibredCategories](https://github.com/sinhp/LeanFibredCategories) | Fibred categories | Apache-2.0 | v4.4.0-rc1 | 3,574 | 2026-04-15 |
| [JoeyEremondi/lean-cwf](https://github.com/JoeyEremondi/lean-cwf) | Categories with Families | BSD-3-Clause | n/a | 5,346 | 2025-02-18 |
| [mckoen/quasicategory](https://github.com/mckoen/quasicategory) | Quasi-categories |  | v4.18.0-rc1 | 11,675 | 2025-10-25 |
| [themathqueen/monlib4](https://github.com/themathqueen/monlib4) | Non-commutative graph theory | Apache-2.0 | v4.21.0-rc3 | 31,853 | 2026-01-06 |
| [ivankobe/FactorizationSystems](https://github.com/ivankobe/FactorizationSystems) | Factorization systems | MIT | v4.14.0-rc2 | 2,501 | 2025-01-21 |

### Logic / set theory / foundations

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [FormalizedFormalLogic/Incompleteness](https://github.com/FormalizedFormalLogic/Incompleteness) | Gödel incompleteness | Apache-2.0 | v4.16.0-rc2 | 2,514 | 2025-09-23 |
| [VTrelat/ZFLean](https://github.com/VTrelat/ZFLean) | ZF set theory framework | Apache-2.0 | v4.27.0 | 9,623 | 2026-04-01 |
| [ishiut/fo_zfc](https://github.com/ishiut/fo_zfc) | First-order ZFC | Apache-2.0 | v4.22.0-rc3 | 2,450 | 2025-08-04 |

### CS-theory (graduate theoretical CS)

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [tannerduve/computability](https://github.com/tannerduve/computability) | Oracle computability, Turing degrees |  | v4.24.0 | 3,035 | 2026-02-05 |
| [suomela/2-coloring-1-round](https://github.com/suomela/2-coloring-1-round) | 2-Coloring cycles in one round | MIT | v4.28.0 | 17,214 | 2026-03-13 |

### ML / statistics research

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [or4nge19/NeuralNetworks](https://github.com/or4nge19/NeuralNetworks) | Neural networks | Apache-2.0 | v4.24.0-rc1 | 31,666 | 2026-02-12 |
| [mkaratarakis/HopfieldNet](https://github.com/mkaratarakis/HopfieldNet) | Hopfield networks | MIT | v4.27.0-rc1 | 149,180 | 2026-02-10 |

### Quantum / physics

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [guest2180/lean4-quantum](https://github.com/guest2180/lean4-quantum) | Theory of quantum computing |  | v4.16.0 | 5,150 | 2025-12-27 |

### Miscellaneous research math

| Repo | Theorem / topic | License | Lean | LOC | Updated |
| --- | --- | --- | --- | ---: | --- |
| [ruplet/formalization-of-bounded-arithmetic](https://github.com/ruplet/formalization-of-bounded-arithmetic) | Bounded arithmetic | MIT | v4.22.0 | 6,612 | 2026-04-10 |
| [madvorak/duality](https://github.com/madvorak/duality) | LP duality and extensions | Apache-2.0 | v4.18.0 | 2,582 | 2026-02-26 |
| [vihdzp/ordinal-notation](https://github.com/vihdzp/ordinal-notation) | Ordinal notations |  | v4.16.0-rc2 | 6,161 | 2025-07-20 |
| [Timeroot/lean-descartes-signs](https://github.com/Timeroot/lean-descartes-signs) | Descartes' rule of signs |  | v4.3.0-rc2 | 1,475 | 2025-09-04 |
| [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4) | Brouwer + Kakutani fixed-point theorems |  | v4.21.0-rc3 | 3,257 | 2026-03-04 |
| [LodeVermeulen/Lean4_Bogdanovs_lemma](https://github.com/LodeVermeulen/Lean4_Bogdanovs_lemma) | Bogdanov's lemma |  | v4.8.0-rc1 | 1,209 | 2024-07-03 |
| [oneofvalts/desargues](https://github.com/oneofvalts/desargues) | Desargues's theorem |  | n/a | 1,221 | 2025-07-14 |
| [wwylele/PentagonalNumberTheorem](https://github.com/wwylele/PentagonalNumberTheorem) | Euler's pentagonal number theorem |  | v4.26.0-rc2 | 2,856 | 2025-12-15 |
| [ADedecker/ProperAction](https://github.com/ADedecker/ProperAction) | Proper actions |  | v4.7.0-rc2 | 908 | 2024-05-14 |
| [AntoineChambert-Loir/Sion4](https://github.com/AntoineChambert-Loir/Sion4) | Sion's minimax theorem |  | v4.21.0-rc3 | 3,319 | 2025-09-26 |
| [SReichelt/universe-abstractions](https://github.com/SReichelt/universe-abstractions) | Mathematical universes |  | nightly-2022-01-14 | 19,432 | 2024-04-08 |
| [pannous/hyper-lean](https://github.com/pannous/hyper-lean) | Hyperreal numbers | Apache-2.0 | v4.27.0 | 9,636 | 2026-03-21 |
| [thejohncrafter/Catlib4](https://github.com/thejohncrafter/Catlib4) | Category theory + theoretical CS |  | nightly-2023-04-20 | 3,045 | 2024-11-25 |
| [ChrisHughes24/axgroth](https://github.com/ChrisHughes24/axgroth) | Ax–Grothendieck (likely) |  | v4.23.0-rc2 | 933 | 2026-03-29 |
| [CBirkbeck/ModularForms_Lean4](https://github.com/CBirkbeck/ModularForms_Lean4) | Modular forms |  | v4.5.0-rc1 | 11,539 | 2024-11-08 |
| [Louis-Le-Grand/Formalisation-of-constructable-numbers](https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers) | Constructible numbers |  | v4.11.0-rc2 | 6,146 | 2024-11-13 |
| [penteract/pythagTreeProof](https://github.com/penteract/pythagTreeProof) | Area of the Pythagoras tree |  | v4.22.0-rc3 | 7,813 | 2025-07-22 |
| [roos-j/lean-booleanfun](https://github.com/roos-j/lean-booleanfun) | Arrow's theorem via Fourier analysis | Apache-2.0 | v4.16.0-rc2 | 1,517 | 2026-03-03 |
| [samvang/StoneDualityInLean](https://github.com/samvang/StoneDualityInLean) | Stone duality |  | v4.8.0-rc1 | 1,079 | 2025-11-27 |

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
