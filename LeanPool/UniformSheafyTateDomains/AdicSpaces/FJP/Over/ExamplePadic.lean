/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.SheafyEndpoints
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The p-adic regression: `𝓐` over `ℚ_[p]` (K11, Phase 3; crosswalk D10)

The **genuinely base-independent** witness of the CDVF campaign (acceptance gate 7). Every
public endpoint of `FJP/Over/SheafyEndpoints.lean` is stated over an *arbitrary* complete
discretely valued nonarchimedean field `K`; here we instantiate the whole layer-2 `_of_dvr`
API at `K := ℚ_[p]`. Because `ℚ_[p]` is **not** a Laurent-series field, these theorems show
the new `FiniteJetOver` development is the real general result and not the old Laurent proof
hidden behind a type class.

## The one nontrivial input: `IsDiscreteValuationRing 𝒪[ℚ_[p]]`

Each layer-2 endpoint carries the sole side condition `[IsDiscreteValuationRing 𝒪[K]]`, so the
whole file rests on registering that instance for `K = ℚ_[p]`. Mathlib knows
`IsDiscreteValuationRing ℤ_[p]` (`PadicInt`), but `𝒪[ℚ_[p]] = Valued.integer ℚ_[p]` (the
valuation ring of the scoped `NormedField.toValued` structure the FJP stack uses) has no direct
DVR instance. The bridge is a subring identification followed by transport:

* `integer_eq_subring` — `𝒪[ℚ_[p]] = PadicInt.subring p` as subrings of `ℚ_[p]`, since both
  carriers are `{x | ‖x‖ ≤ 1}` (`Valued.integer.mem_iff` ↔ `PadicInt.mem_subring_iff`);
* `integerRingEquiv` — the induced `ℤ_[p] ≃+* 𝒪[ℚ_[p]]` (`RingEquiv.subringCongr`, using that
  `ℤ_[p]` is defeq to `↥(PadicInt.subring p)`);
* `instIsDiscreteValuationRing` — `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`
  transports the DVR structure from `ℤ_[p]` (both `IsDomain`s are automatic, being subrings of
  the field `ℚ_[p]`).

We deliberately use the norm-based `Valued.integer.mem_iff` route rather than
`PadicInt.withValIntegersRingEquiv`, whose `Valued` structure comes from `WithVal
(Rat.padicValuation p)` and differs from the `NormedField.toValued` structure of the FJP stack.

## Endpoints

With the instance in scope, the p-adic forms of the Theorem-1.3 headliners
(uniform / domain / non-noetherian / not-stably-uniform) and the sheafiness API
(Tate-ring sheafiness, all-pairs completeness, and — the gate-7 witnesses — the genuine
projective-limit `structurePresheaf` as a sheaf of topological rings and as a categorical
sheaf, at every valid `A⁺` and for every completion model) are one-line specializations.
-/

@[expose] public section

noncomputable section

namespace FiniteJetOver.Padic

open FiniteJet
open ValuationSpectrum
open scoped NormedField Valued

variable (p : ℕ) [Fact p.Prime]

/-! ### The discrete-valuation-ring bridge `ℤ_[p] → 𝒪[ℚ_[p]]` -/

/-- The valuation ring `𝒪[ℚ_[p]]` of the `NormedField.toValued` structure on `ℚ_[p]` is the
subring `PadicInt.subring p` — both are the closed unit ball `{x | ‖x‖ ≤ 1}` of `ℚ_[p]`
(`Valued.integer.mem_iff` and `PadicInt.mem_subring_iff`). -/
theorem integer_eq_subring : (𝒪[ℚ_[p]] : Subring ℚ_[p]) = PadicInt.subring p :=
  Subring.ext fun x =>
    (Valued.integer.mem_iff (x := x)).trans (PadicInt.mem_subring_iff (p := p)).symm

/-- The ring equivalence `ℤ_[p] ≃+* 𝒪[ℚ_[p]]` induced by `integer_eq_subring` (using that
`ℤ_[p]` is definitionally `↥(PadicInt.subring p)`). -/
def integerRingEquiv : ℤ_[p] ≃+* 𝒪[ℚ_[p]] :=
  RingEquiv.subringCongr (integer_eq_subring p).symm

/-- **The valuation ring of `ℚ_[p]` is a discrete valuation ring.** This is the single
nontrivial input of the whole p-adic regression: it transports `IsDiscreteValuationRing ℤ_[p]`
(mathlib) along `integerRingEquiv` via
`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`, discharging the sole side
condition `[IsDiscreteValuationRing 𝒪[K]]` of every layer-2 `_of_dvr` endpoint at `K = ℚ_[p]`. -/
instance instIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[ℚ_[p]] :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (integerRingEquiv p)

/-! ### Theorem 1.3 headliners over `ℚ_[p]` ([FJP] Theorem 1.3, CDVF regression)

The four ring-level conclusions, now witnessed over the non-Laurent base `ℚ_[p]`. -/

/-- **[FJP] Theorem 1.3 (uniform) over `ℚ_[p]`** — the CDVF regression witness. -/
theorem padicFiniteJet_isUniform : TopologicalRing.IsUniform (JetA ℚ_[p]) :=
  finiteJet_isUniform_of_dvr ℚ_[p]

/-- **[FJP] Theorem 1.3 (domain) over `ℚ_[p]`** — the CDVF regression witness. -/
theorem padicFiniteJet_isDomain : IsDomain (JetA ℚ_[p]) :=
  finiteJet_isDomain ℚ_[p]

/-- **[FJP] Theorem 1.3 (non-noetherian) over `ℚ_[p]`** — the CDVF regression witness. -/
theorem padicFiniteJet_not_noetherian : ¬ IsNoetherianRing (JetA ℚ_[p]) :=
  finiteJet_not_noetherian ℚ_[p]

/-- **[FJP] Theorem 1.3 (not stably uniform) over `ℚ_[p]`** — the CDVF regression witness. -/
theorem padicFiniteJet_not_stablyUniform :
    ¬ TopologicalRing.IsStablyUniform (JetA ℚ_[p]) :=
  finiteJet_not_stablyUniform_of_dvr ℚ_[p]

/-! ### Sheafiness of `𝓐` over `ℚ_[p]` ([FJP] Theorem 1.1 endpoints, CDVF regression) -/

/-- **`𝓐` over `ℚ_[p]` is sheafy in the ring-level Tate sense** — the CDVF regression witness. -/
theorem padicFiniteJet_isSheafyTateRing : IsSheafyTateRing (JetA ℚ_[p]) :=
  finiteJet_isSheafyTateRing_of_dvr ℚ_[p]

/-- **`𝓐` over `ℚ_[p]` is sheafy at every valid ring of integral elements** — the CDVF
regression witness. -/
theorem padicFiniteJet_isSheafyFor_all (Bplus : RingOfIntegralElements (JetA ℚ_[p])) :
    IsSheafyFor (JetA ℚ_[p]) Bplus :=
  finiteJet_isSheafyFor_all_of_dvr ℚ_[p] Bplus

/-- **`𝓐` over `ℚ_[p]` is sheafy at every valid `A⁺` (complete-ring form)** — the CDVF
regression witness. -/
theorem padicFiniteJet_isSheafyComplete : IsSheafyComplete (JetA ℚ_[p]) :=
  finiteJet_isSheafyComplete_of_dvr ℚ_[p]

/-- **The genuine projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` over `ℚ_[p]` is a
sheaf of topological rings at every valid `A⁺`** (Wedhorn Remark 8.20) — a gate-7 structure
presheaf witness of the CDVF regression. The presheaf is `structurePresheaf` with its
`limitSections` topology, never a discrete locally-fraction comparison object. -/
theorem padicFiniteJet_structurePresheaf_isSheafOfTopologicalRings_all
    (Bplus : RingOfIntegralElements (JetA ℚ_[p])) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA ℚ_[p])⁺ : Subring (JetA ℚ_[p])) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA ℚ_[p]) := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA ℚ_[p])) :=
  finiteJet_structurePresheaf_isSheafOfTopologicalRings_all_of_dvr ℚ_[p] Bplus

/-- **The genuine projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` over `ℚ_[p]`
satisfies the categorical sheaf condition at every valid `A⁺`** ([Stacks 00VR]) — a gate-7
structure presheaf witness of the CDVF regression. -/
theorem padicFiniteJet_structurePresheaf_isSheaf_all
    (Bplus : RingOfIntegralElements (JetA ℚ_[p])) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA ℚ_[p])⁺ : Subring (JetA ℚ_[p])) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA ℚ_[p]) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (JetA ℚ_[p])).IsSheaf :=
  finiteJet_structurePresheaf_isSheaf_all_of_dvr ℚ_[p] Bplus

/-- **Every completion model of `𝓐` over `ℚ_[p]` has a projective-limit structure presheaf
that is a sheaf of topological rings** (at every valid `A⁺`) — the CDVF regression witness on
the genuine `structurePresheaf`. -/
theorem padicFiniteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings
    (P : PairOfDefinition (JetA ℚ_[p]))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA ℚ_[p]) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA ℚ_[p]) P)⁺ : Subring (CompletionModel (JetA ℚ_[p]) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA ℚ_[p]) P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (CompletionModel (JetA ℚ_[p]) P)) :=
  finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings_of_dvr ℚ_[p] P Bplus

/-- **The categorical sheaf condition for every completion model of `𝓐` over `ℚ_[p]`**
([Stacks 00VR]) — the CDVF regression witness. -/
theorem padicFiniteJet_completionModel_structurePresheaf_isSheaf
    (P : PairOfDefinition (JetA ℚ_[p]))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA ℚ_[p]) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA ℚ_[p]) P)⁺ : Subring (CompletionModel (JetA ℚ_[p]) P)) :=
      Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA ℚ_[p]) P) :=
      hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (CompletionModel (JetA ℚ_[p]) P)).IsSheaf :=
  finiteJet_completionModel_structurePresheaf_isSheaf_of_dvr ℚ_[p] P Bplus

end FiniteJetOver.Padic
