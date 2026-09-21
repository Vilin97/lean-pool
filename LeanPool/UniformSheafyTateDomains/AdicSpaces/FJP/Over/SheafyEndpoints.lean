/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.SheafTransfer
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyEndpoints
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeStandardRefinement
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyCompletionModel

/-!
# FJP over a CDVF base: the literature-facing public endpoints (K9, Phase 9)

The generic-base counterpart of `FJP/FiniteJetSheafyEndpoints.lean`: the finite-jet
pinching algebra `𝓐 = FiniteJet.JetA K` over an arbitrary complete nonarchimedean base
`K` (`[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`, crosswalk D9)
now carries the full public sheafiness API, as corollaries of the headline
`FiniteJetOver.isSheafy_JetA` ([FJP] Theorem 5.3) through the **base-agnostic** generic
bridges — **no FJP-specific re-proof of anything**.

The whole `IsSheafy → …` machinery is base-independent, so this is a re-parameterization of
the Laurent template with `F ⇒ K` and the frozen `finiteJet_isSheafy` replaced by the
CDVF sheafiness discharger. As in the K8 sheaf-transfer split (`isSheafy_JetA` /
`isSheafy_JetA_of_dvr`) each endpoint that consumes sheafiness comes in **two layers**:

* **Layer 1** (`ϖ`-explicit): takes an explicit uniformizer `ϖ : Uniformizer K` and the
  base-ball noetherianity `hK₀ : IsNoetherianRing (unitBall K)`, feeding
  `isSheafy_JetA K ϖ hK₀`.
* **Layer 2** (`_of_dvr`, the public endpoint): over a base whose valuation ring `𝒪[K]`
  is a discrete valuation ring, the uniformizer is chosen by `Uniformizer.ofDVR` and the
  ball-noetherianity by `CDVFBase.isNoetherianRing_unitBall`, feeding
  `isSheafy_JetA_of_dvr K`. This is the form the p-adic instantiation (K11) consumes.

Headline Theorem-1.3 endpoints (uniform / domain / non-noetherian / not-stably-uniform)
are re-exported here in the `FiniteJetOver` namespace; the frozen `FiniteJet.finiteJet_*`
Laurent types in `FiniteJetMain.lean` are untouched.

The structure-presheaf endpoints (`…structurePresheaf_isSheafOfTopologicalRings…`,
`…structurePresheaf_isSheaf…`, both the arbitrary-`A⁺` and completion-model variants) all
conclude sheafiness of the genuine all-open projective-limit
`ValuationSpectrum.structurePresheaf` with its `limitSections` topology — never a discrete
locally-fraction comparison object.
-/

noncomputable section

namespace FiniteJetOver

open FiniteJet
open ValuationSpectrum

open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Theorem 1.3 headline endpoints over a CDVF base ([FJP] Theorem 1.3)

The four ring-level Theorem-1.3 conclusions in the public `FiniteJetOver` vocabulary. The
frozen Laurent forms live in `FiniteJetMain.lean`; these are their generic-base analogues. -/

/-- **[FJP] Theorem 1.3 (uniform), layer 1**: `𝓐` over a CDVF base is uniform; any base
uniformizer witnesses it. -/
theorem finiteJet_isUniform (ϖ : Uniformizer K) :
    TopologicalRing.IsUniform (JetA K) :=
  isUniform_JetA ϖ

/-- **[FJP] Theorem 1.3 (domain)**: `𝓐` is an integral domain (generic base; instance). -/
theorem finiteJet_isDomain : IsDomain (JetA K) :=
  inferInstance

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: `𝓐` is not noetherian (generic base). -/
theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (JetA K) :=
  not_isNoetherianRing_JetA K

/-- **[FJP] Theorem 1.3 (not stably uniform), layer 1**: `𝓐` is not stably uniform; the
Huber structure of `𝓐` is an unconditional instance (`Over/Functoriality.lean`), the
witness uses the chart at `ϖ`. -/
theorem finiteJet_not_stablyUniform (ϖ : Uniformizer K) :
    ¬ TopologicalRing.IsStablyUniform (JetA K) :=
  not_isStablyUniform_JetA K ϖ

/-! ### The canonical valid pair of `𝓐` -/

/-- The canonical valid pair of the pinching algebra over a CDVF base: its maximal plus
ring, bundled. -/
def finiteJetPlus : RingOfIntegralElements (JetA K) :=
  ⟨((JetA K)⁺ : Subring (JetA K)), inferInstance⟩

/-! ### Pair-level sheafiness endpoints, layer 1 (`ϖ`-explicit) -/

/-- **Pair-level sheafiness of the pinching algebra, public form** (layer 1): the genuine
all-open projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` is a sheaf of topological
rings. Corollary of `isSheafy_JetA` through the C5 equivalence. -/
theorem finiteJet_isSheafyFor (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsSheafyFor (JetA K) (finiteJetPlus K) := by
  classical
  letI := (finiteJetPlus K).toPlusSubring
  haveI : IsRingOfIntegralElements ((JetA K)⁺ : Subring (JetA K)) := (finiteJetPlus K).2
  haveI : HasLocLiftPowerBounded (JetA K) := hasLocLiftPowerBounded_faithful
  haveI : IsSheafy (JetA K) := isSheafy_JetA K ϖ hK₀
  show IsLimitSheaf (JetA K)
  exact isLimitSheaf_of_isSheafy

/-- **The pinching algebra's structure presheaf is a sheaf of topological rings in
Wedhorn's own sense** (Remark 8.20; layer 1): for every topological commutative ring `T`,
`V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf of sets on `Spa (𝓐, 𝓐⁺)`. -/
theorem finiteJet_isSheafOfTopologicalRings (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsSheafOfTopologicalRings (JetA K) := by
  classical
  refine (isSheafOfTopologicalRings_iff_isLimitSheaf).mpr ?_
  haveI : IsSheafy (JetA K) := isSheafy_JetA K ϖ hK₀
  exact isLimitSheaf_of_isSheafy

/-- **The public structure presheaf of the pinching algebra is a sheaf of topological
rings in the generic sense** (`TopCat.Presheaf.IsSheafOfTopologicalRings`, Wedhorn Remark
8.20 for the bundled presheaf; layer 1) — the P0 wrapper applied to `finiteJet_isSheafyFor`.
The presheaf is `structurePresheaf` with its projective/`limitSections` topology. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA K)) := by
  classical
  refine (structurePresheaf_isSheafOfTopologicalRings_iff (JetA K)).mpr ?_
  haveI : IsSheafy (JetA K) := isSheafy_JetA K ϖ hK₀
  exact isLimitSheaf_of_isSheafy

/-- **The bundled public structure presheaf of the pinching algebra satisfies the
categorical sheaf condition** ([Stacks 00VR] `Hom`-by-`Hom` form; layer 1). -/
theorem finiteJet_structurePresheaf_isSheaf (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    (ValuationSpectrum.structurePresheaf (JetA K)).IsSheaf := by
  classical
  refine structurePresheaf_isSheaf (JetA K) ?_
  haveI : IsSheafy (JetA K) := isSheafy_JetA K ϖ hK₀
  exact isLimitSheaf_of_isSheafy

/-- The structure sheaf of the pinching algebra, as a sheaf object valued in the
(coherent) category of complete separated topological commutative rings (layer 1). -/
def finiteJet_structureSheaf (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop (JetA K)) :=
  ⟨ValuationSpectrum.structurePresheaf (JetA K),
    finiteJet_structurePresheaf_isSheaf K ϖ hK₀⟩

/-- **The `A⁺`-free standard sheaf condition holds for the pinching algebra** (layer 1) —
through the genuine single-pair transfer (`standardSheafCondition_of_isSheafyFor`, Kedlaya
Remark 1.6.9's mechanism). Since `𝓐` is not noetherian, this is *not* an instance of the
strongly noetherian theorems: it is the transfer from the proved pair `(𝓐, 𝓐⁺)`. -/
theorem finiteJet_standardSheafCondition (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    StandardSheafCondition (JetA K) :=
  standardSheafCondition_of_isSheafyFor (finiteJetPlus K) (finiteJet_isSheafyFor K ϖ hK₀)

/-- **Sheafiness of the pinching algebra at every valid ring of integral elements**,
conditional on exactly the descent input (Kedlaya Lemma 1.6.8's conclusion) at each pair
(layer 1) — retained as a lower-level result; the unconditional `finiteJet_isSheafyComplete`
supersedes it via the Huber form-(a) product refinement (no noetherian bypass). -/
theorem finiteJet_isSheafyComplete_of_hasStandardRefinements (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K))
    (hall : ∀ Bplus : RingOfIntegralElements (JetA K),
      Bplus.HasStandardRefinements (JetA K)) :
    IsSheafyComplete (JetA K) :=
  (isSheafyFor_iff_isSheafyComplete_of_hasStandardRefinements
    (finiteJetPlus K) hall).mp
    (finiteJet_isSheafyFor K ϖ hK₀)

/-- **Pinching algebra: sheafiness at EVERY valid ring of integral elements**,
unconditionally (layer 1). `𝓐 = JetA K` is complete Tate; A⁺-independence
(`isSheafyFor_iff_isSheafyComplete`, via Huber's form-(a) product refinement) upgrades the
single proved pair `(𝓐, 𝓐⁺)` to all pairs — with **no** noetherian bypass (`𝓐` is
non-noetherian, [FJP] Thm 1.3). -/
theorem finiteJet_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsSheafyComplete (JetA K) :=
  (isSheafyFor_iff_isSheafyComplete (finiteJetPlus K)).mp (finiteJet_isSheafyFor K ϖ hK₀)

/-- The `∀`-unfolding: the pinching algebra is sheafy at every valid `Bplus` (layer 1). -/
theorem finiteJet_isSheafyFor_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (Bplus : RingOfIntegralElements (JetA K)) :
    IsSheafyFor (JetA K) Bplus :=
  finiteJet_isSheafyComplete K ϖ hK₀ Bplus

/-- **The pinching algebra is sheafy in the ring-level Tate sense** (Wedhorn Definition
8.26 at Tate scope; layer 1): every ring of integral elements of every completion model of
`𝓐 = JetA K` gives a sheafy pair. Formal consequence of the all-pairs complete-ring
sheafiness through `isSheafyTateRing_iff_isSheafyComplete`. No noetherian or strongly
noetherian hypotheses are available or used. -/
theorem finiteJet_isSheafyTateRing (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsSheafyTateRing (JetA K) :=
  (isSheafyTateRing_iff_isSheafyComplete (A := JetA K)).2
    (finiteJet_isSheafyComplete K ϖ hK₀)

/-- **The public structure presheaf of the pinching algebra is a sheaf of topological rings
at EVERY valid ring of integral elements** (layer 1): the P0 wrapper applied to the
unconditional all-pairs sheafiness. The presheaf is `structurePresheaf` with its
projective/`limitSections` topology — never the discrete locally-fraction presheaf. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (Bplus : RingOfIntegralElements (JetA K)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA K)⁺ : Subring (JetA K)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA K) := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA K)) :=
  isSheafyFor_structurePresheaf_isSheafOfTopologicalRings Bplus
    (finiteJet_isSheafyFor_all K ϖ hK₀ Bplus)

/-- **The public structure presheaf of the pinching algebra satisfies the categorical sheaf
condition at EVERY valid ring of integral elements** (layer 1). -/
theorem finiteJet_structurePresheaf_isSheaf_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (Bplus : RingOfIntegralElements (JetA K)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA K)⁺ : Subring (JetA K)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA K) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (JetA K)).IsSheaf :=
  isSheafyFor_structurePresheaf_isSheaf Bplus (finiteJet_isSheafyFor_all K ϖ hK₀ Bplus)

/-- **The public projective-topology structure presheaf of every completion model of the
pinching algebra, at every valid ring of integral elements, is a sheaf of topological
rings** (layer 1): the explicit-`P`-and-`Bplus` endpoint, concluding sheafiness of the
actual `structurePresheaf` — never a discrete comparison object. -/
theorem finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (P : PairOfDefinition (JetA K))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA K) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA K) P)⁺ : Subring (CompletionModel (JetA K) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA K) P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (CompletionModel (JetA K) P)) :=
  isSheafyTateRing_structurePresheaf_isSheafOfTopologicalRings
    (finiteJet_isSheafyTateRing K ϖ hK₀) P Bplus

/-- **The categorical sheaf condition for every completion model of the pinching algebra**
([Stacks 00VR] form; layer 1). -/
theorem finiteJet_completionModel_structurePresheaf_isSheaf
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (P : PairOfDefinition (JetA K))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA K) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA K) P)⁺ : Subring (CompletionModel (JetA K) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA K) P) :=
      hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (CompletionModel (JetA K) P)).IsSheaf :=
  isSheafyTateRing_structurePresheaf_isSheaf (finiteJet_isSheafyTateRing K ϖ hK₀) P Bplus

/-! ### Layer 2: the public endpoints over a discretely-valued base

For a base whose valuation ring `𝒪[K]` is a discrete valuation ring the uniformizer and
ball-noetherianity are canonical (`Uniformizer.ofDVR`, `CDVFBase.isNoetherianRing_unitBall`),
so the sheafiness inputs vanish from the interface. These are the forms the p-adic
regression (K11) instantiates. -/

/-- **[FJP] Theorem 1.3 (uniform), layer 2**: `𝓐` over a discretely-valued base is
uniform. -/
theorem finiteJet_isUniform_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    TopologicalRing.IsUniform (JetA K) :=
  finiteJet_isUniform K (Uniformizer.ofDVR K)

/-- **[FJP] Theorem 1.1 (`𝓐° = 𝓐₀`), layer 2**. -/
theorem finiteJet_powerBounded_eq_unitBall_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    TopologicalRing.powerBoundedSubring (JetA K) =
      (FiniteJet.unitBall (JetA K) : Set (JetA K)) :=
  powerBoundedSubring_eq_unitBall (Uniformizer.ofDVR K)

/-- **[FJP] Theorem 1.3 (not stably uniform), layer 2**. -/
theorem finiteJet_not_stablyUniform_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    ¬ TopologicalRing.IsStablyUniform (JetA K) :=
  finiteJet_not_stablyUniform K (Uniformizer.ofDVR K)

/-- **Pair-level sheafiness of `𝓐`, public endpoint** (layer 2). -/
theorem finiteJet_isSheafyFor_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    IsSheafyFor (JetA K) (finiteJetPlus K) :=
  finiteJet_isSheafyFor K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- **`𝓐`'s structure presheaf is a sheaf of topological rings (Wedhorn's own sense),
public endpoint** (layer 2). -/
theorem finiteJet_isSheafOfTopologicalRings_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    IsSheafOfTopologicalRings (JetA K) :=
  finiteJet_isSheafOfTopologicalRings K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- **`𝓐`'s bundled structure presheaf is a sheaf of topological rings, public endpoint**
(layer 2) — the genuine projective-limit-topology `structurePresheaf`. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings_of_dvr
    [IsDiscreteValuationRing 𝒪[K]] :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA K)) :=
  finiteJet_structurePresheaf_isSheafOfTopologicalRings K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K)

/-- **`𝓐`'s bundled structure presheaf satisfies the categorical sheaf condition, public
endpoint** (layer 2). -/
theorem finiteJet_structurePresheaf_isSheaf_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    (ValuationSpectrum.structurePresheaf (JetA K)).IsSheaf :=
  finiteJet_structurePresheaf_isSheaf K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- The structure sheaf of `𝓐` over a discretely-valued base (layer 2). -/
def finiteJet_structureSheaf_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop (JetA K)) :=
  finiteJet_structureSheaf K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- **The `A⁺`-free standard sheaf condition for `𝓐`, public endpoint** (layer 2). -/
theorem finiteJet_standardSheafCondition_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    StandardSheafCondition (JetA K) :=
  finiteJet_standardSheafCondition K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- **Conditional all-pairs sheafiness of `𝓐`, public endpoint** (layer 2). -/
theorem finiteJet_isSheafyComplete_of_hasStandardRefinements_of_dvr
    [IsDiscreteValuationRing 𝒪[K]]
    (hall : ∀ Bplus : RingOfIntegralElements (JetA K),
      Bplus.HasStandardRefinements (JetA K)) :
    IsSheafyComplete (JetA K) :=
  finiteJet_isSheafyComplete_of_hasStandardRefinements K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K) hall

/-- **Unconditional all-pairs sheafiness of `𝓐`, public endpoint** (layer 2). -/
theorem finiteJet_isSheafyComplete_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    IsSheafyComplete (JetA K) :=
  finiteJet_isSheafyComplete K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- The `∀`-unfolding at every valid `Bplus`, public endpoint (layer 2). -/
theorem finiteJet_isSheafyFor_all_of_dvr [IsDiscreteValuationRing 𝒪[K]]
    (Bplus : RingOfIntegralElements (JetA K)) :
    IsSheafyFor (JetA K) Bplus :=
  finiteJet_isSheafyFor_all K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K) Bplus

/-- **`𝓐` is sheafy in the ring-level Tate sense, public endpoint** (layer 2). -/
theorem finiteJet_isSheafyTateRing_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    IsSheafyTateRing (JetA K) :=
  finiteJet_isSheafyTateRing K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

/-- **`𝓐`'s structure presheaf is a sheaf of topological rings at EVERY valid ring of
integral elements, public endpoint** (layer 2) — the genuine projective-limit-topology
`structurePresheaf` on all opens, for every `A⁺`. -/
theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings_all_of_dvr
    [IsDiscreteValuationRing 𝒪[K]] (Bplus : RingOfIntegralElements (JetA K)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA K)⁺ : Subring (JetA K)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA K) := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA K)) :=
  finiteJet_structurePresheaf_isSheafOfTopologicalRings_all K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K) Bplus

/-- **`𝓐`'s structure presheaf satisfies the categorical sheaf condition at EVERY valid
ring of integral elements, public endpoint** (layer 2). -/
theorem finiteJet_structurePresheaf_isSheaf_all_of_dvr
    [IsDiscreteValuationRing 𝒪[K]] (Bplus : RingOfIntegralElements (JetA K)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA K)⁺ : Subring (JetA K)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA K) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (JetA K)).IsSheaf :=
  finiteJet_structurePresheaf_isSheaf_all K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K) Bplus

/-- **Every completion model of `𝓐` has a projective-topology structure presheaf that is a
sheaf of topological rings, public endpoint** (layer 2) — the "every completion model
required by the public API" clause, on the genuine `structurePresheaf`. -/
theorem finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings_of_dvr
    [IsDiscreteValuationRing 𝒪[K]] (P : PairOfDefinition (JetA K))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA K) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA K) P)⁺ : Subring (CompletionModel (JetA K) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA K) P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (CompletionModel (JetA K) P)) :=
  finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings K
    (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K) P Bplus

/-- **The categorical sheaf condition for every completion model of `𝓐`, public endpoint**
(layer 2). -/
theorem finiteJet_completionModel_structurePresheaf_isSheaf_of_dvr
    [IsDiscreteValuationRing 𝒪[K]] (P : PairOfDefinition (JetA K))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA K) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA K) P)⁺ : Subring (CompletionModel (JetA K) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA K) P) :=
      hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (CompletionModel (JetA K) P)).IsSheaf :=
  finiteJet_completionModel_structurePresheaf_isSheaf K (Uniformizer.ofDVR K)
    (isNoetherianRing_unitBall K) P Bplus

end FiniteJetOver
