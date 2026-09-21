/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetMain
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyEndpoints
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeStandardRefinement
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyCompletionModel

/-!
# FJP: the literature-facing sheafiness endpoints (WO5)

Corollaries of the fixed-pair headline `finiteJet_isSheafy` ([FJP] Theorem 1.3)
through the generic bridges — **no FJP-specific re-proof of anything**:

* `finiteJet_isSheafyFor` — pair-level sheafiness in the public vocabulary: the
  genuine all-open projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` is a sheaf
  of topological rings (`IsSheafyFor`, via the C5 equivalence).
* `finiteJet_isSheafOfTopologicalRings` — **Wedhorn Remark 8.20's own formulation**:
  for every topological commutative ring `T`, `V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf
  of sets.
* `finiteJet_structurePresheaf_isSheaf` / `finiteJet_structureSheaf` — the bundled
  public structure presheaf satisfies mathlib's categorical sheaf condition; the
  sheaf object. The topology is the projective-limit topology — nothing discrete.
* `finiteJet_standardSheafCondition` — the `A⁺`-free standard sheaf condition
  (Kedlaya Remark 1.6.9's `A⁺`-independent middle term) holds for `𝓐`
  unconditionally, through the single-pair transfer
  `standardSheafCondition_of_isSheafyFor`. Note `𝓐` is **not** noetherian
  ([FJP] Thm 1.3), so this is *not* obtainable from the strongly noetherian route —
  it is the genuine transfer from the proved pair.
* `finiteJet_isSheafyComplete_of_hasStandardRefinements` — sheafiness at **every**
  valid ring of integral elements, conditional on exactly the descent input
  (Kedlaya Lemma 1.6.8's conclusion, `HasStandardRefinements`; see
  `StandardDescent.lean` for the precise blocked dependencies). Stated conditionally
  (the older conditional form, retained as a lower-level result). The UNCONDITIONAL
  all-pairs sheafiness `finiteJet_isSheafyComplete` is now available (below), via the
  Huber form-(a) product refinement — with no strongly-noetherian bypass.

All original FJP headline endpoints are untouched (regression-protected).
-/

noncomputable section

namespace FiniteJet

open ValuationSpectrum

universe u

variable (F : Type u) [Field F]

/-- The canonical valid pair of the pinching algebra: its maximal plus ring,
bundled. -/
def finiteJetPlus : RingOfIntegralElements (JetA F) :=
  ⟨((JetA F)⁺ : Subring (JetA F)), inferInstance⟩

/-- **Pair-level sheafiness of the pinching algebra, public form**: the genuine
all-open projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` is a sheaf of
topological rings. Corollary of `finiteJet_isSheafy` through the C5 equivalence. -/
theorem finiteJet_isSheafyFor : IsSheafyFor (JetA F) (finiteJetPlus F) := by
  classical
  letI := (finiteJetPlus F).toPlusSubring
  haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) :=
    (finiteJetPlus F).2
  haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  show IsLimitSheaf (JetA F)
  exact isLimitSheaf_of_isSheafy

/-- **The pinching algebra's structure presheaf is a sheaf of topological rings in
Wedhorn's own sense** (Remark 8.20): for every topological commutative ring `T`,
`V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf of sets on `Spa (𝓐, 𝓐⁺)`. -/
theorem finiteJet_isSheafOfTopologicalRings :
    IsSheafOfTopologicalRings (JetA F) := by
  classical
  refine (isSheafOfTopologicalRings_iff_isLimitSheaf).mpr ?_
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  exact isLimitSheaf_of_isSheafy

/-- **The public structure presheaf of the pinching algebra is a sheaf of
topological rings in the generic sense** (`TopCat.Presheaf.IsSheafOfTopologicalRings`,
Wedhorn Remark 8.20 for the bundled presheaf) — the P0 wrapper applied to
`finiteJet_isSheafyFor`. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA F)) := by
  classical
  refine (structurePresheaf_isSheafOfTopologicalRings_iff (JetA F)).mpr ?_
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  exact isLimitSheaf_of_isSheafy

/-- **The bundled public structure presheaf of the pinching algebra satisfies the
categorical sheaf condition** ([Stacks 00VR] `Hom`-by-`Hom` form). -/
theorem finiteJet_structurePresheaf_isSheaf :
    (ValuationSpectrum.structurePresheaf (JetA F)).IsSheaf := by
  classical
  refine structurePresheaf_isSheaf (JetA F) ?_
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  exact isLimitSheaf_of_isSheafy

/-- The structure sheaf of the pinching algebra, as a sheaf object valued in the
(coherent) category of complete separated topological commutative rings. -/
def finiteJet_structureSheaf :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop (JetA F)) :=
  ⟨ValuationSpectrum.structurePresheaf (JetA F), finiteJet_structurePresheaf_isSheaf F⟩

/-- **The `A⁺`-free standard sheaf condition holds for the pinching algebra,
unconditionally** — through the genuine single-pair transfer
(`standardSheafCondition_of_isSheafyFor`, Kedlaya Remark 1.6.9's mechanism). Since
`𝓐` is not noetherian, this is *not* an instance of the strongly noetherian
theorems: it is the transfer from the proved pair `(𝓐, 𝓐⁺)`. -/
theorem finiteJet_standardSheafCondition : StandardSheafCondition (JetA F) :=
  standardSheafCondition_of_isSheafyFor (finiteJetPlus F) (finiteJet_isSheafyFor F)

/-- **Sheafiness of the pinching algebra at every valid ring of integral elements**,
conditional on exactly the descent input (Kedlaya Lemma 1.6.8's conclusion) at each
pair — retained as a lower-level result; the UNCONDITIONAL `finiteJet_isSheafyComplete`
(below) supersedes it via the Huber form-(a) product refinement (no noetherian bypass). -/
theorem finiteJet_isSheafyComplete_of_hasStandardRefinements
    (hall : ∀ Bplus : RingOfIntegralElements (JetA F),
      Bplus.HasStandardRefinements (JetA F)) :
    IsSheafyComplete (JetA F) :=
  (isSheafyFor_iff_isSheafyComplete_of_hasStandardRefinements
    (finiteJetPlus F) hall).mp
    (finiteJet_isSheafyFor F)

/-- **Pinching algebra: sheafiness at EVERY valid ring of integral elements**,
unconditionally (PHASE 2E). `𝓐 = JetA F` is complete Tate; A⁺-independence
(`isSheafyFor_iff_isSheafyComplete`, via Huber's form-(a) product refinement) upgrades
the single proved pair `(𝓐, 𝓐⁺)` to all pairs — with **no** noetherian bypass
(`𝓐` is non-noetherian, [FJP] Thm 1.3). -/
theorem finiteJet_isSheafyComplete : IsSheafyComplete (JetA F) :=
  (isSheafyFor_iff_isSheafyComplete (finiteJetPlus F)).mp (finiteJet_isSheafyFor F)

/-- The `∀`-unfolding: the pinching algebra is sheafy at every valid `Bplus`. -/
theorem finiteJet_isSheafyFor_all (Bplus : RingOfIntegralElements (JetA F)) :
    IsSheafyFor (JetA F) Bplus :=
  finiteJet_isSheafyComplete F Bplus

/-- **The public structure presheaf of the pinching algebra is a sheaf of topological
rings at EVERY valid ring of integral elements** (PASS 4): the P0 wrapper applied to the
unconditional all-pairs sheafiness. The presheaf is `structurePresheaf` with its
projective/`limitSections` topology — never the discrete locally-fraction presheaf. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings_all
    (Bplus : RingOfIntegralElements (JetA F)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA F)) :=
  isSheafyFor_structurePresheaf_isSheafOfTopologicalRings Bplus
    (finiteJet_isSheafyFor_all F Bplus)

/-- **The public structure presheaf of the pinching algebra satisfies the categorical
sheaf condition at EVERY valid ring of integral elements** (PASS 4). -/
theorem finiteJet_structurePresheaf_isSheaf_all
    (Bplus : RingOfIntegralElements (JetA F)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (JetA F)).IsSheaf :=
  isSheafyFor_structurePresheaf_isSheaf Bplus (finiteJet_isSheafyFor_all F Bplus)

/-! ### The unconditional literature-facing endpoint (PASS F) -/

/-- **The pinching algebra is sheafy in the ring-level Tate sense**
(Wedhorn Definition 8.26 at Tate scope, the unconditional literature-facing
endpoint): every ring of integral elements of every completion model of
`𝓐 = JetA F` gives a sheafy pair. Formal consequence of the all-pairs
complete-ring sheafiness (`finiteJet_isSheafyComplete`) through the generic
completion-model collapse `isSheafyTateRing_iff_isSheafyComplete` — `𝓐` is
complete Tate, so its completion models are canonically isomorphic to `𝓐`
itself. No noetherian or strongly noetherian hypotheses are available or used
(`𝓐` is deliberately non-noetherian, [FJP] Theorem 1.3). -/
theorem finiteJet_isSheafyTateRing : IsSheafyTateRing (JetA F) :=
  (isSheafyTateRing_iff_isSheafyComplete (A := JetA F)).2
    (finiteJet_isSheafyComplete F)

/-- **The public projective-topology structure presheaf of every completion model
of the pinching algebra, at every valid ring of integral elements, is a sheaf of
topological rings** (PASS F): the explicit-`P`-and-`Bplus` endpoint, concluding
sheafiness of the actual `structurePresheaf` — never a discrete comparison
object. -/
theorem finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings
    (P : PairOfDefinition (JetA F))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA F) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA F) P)⁺ : Subring (CompletionModel (JetA F) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA F) P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (CompletionModel (JetA F) P)) :=
  isSheafyTateRing_structurePresheaf_isSheafOfTopologicalRings
    (finiteJet_isSheafyTateRing F) P Bplus

/-- **The categorical sheaf condition for every completion model of the pinching
algebra** ([Stacks 00VR] form, PASS F). -/
theorem finiteJet_completionModel_structurePresheaf_isSheaf
    (P : PairOfDefinition (JetA F))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA F) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA F) P)⁺ : Subring (CompletionModel (JetA F) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA F) P) :=
      hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (CompletionModel (JetA F) P)).IsSheaf :=
  isSheafyTateRing_structurePresheaf_isSheaf (finiteJet_isSheafyTateRing F) P Bplus

end FiniteJet
