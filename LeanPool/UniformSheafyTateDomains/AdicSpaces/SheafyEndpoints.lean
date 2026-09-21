/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructurePresheafBundled
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardDescent

/-!
# End-to-end public endpoints: sheafiness means the public presheaf is a sheaf

Named wrappers (P0.3) connecting the sheafiness predicates to the **public
projective-topology structure presheaf** (`structurePresheaf`,
`StructurePresheafBundled.lean`), through the generic
`TopCat.Presheaf.IsSheafOfTopologicalRings` (Wedhorn Remark 8.20) and mathlib's
categorical sheaf condition ([Stacks 00VR]):

* `isSheafyFor_structurePresheaf_isSheafOfTopologicalRings` /
  `isSheafyFor_structurePresheaf_isSheaf` — pair level.
* `isSheafyTateRing_structurePresheaf_isSheafOfTopologicalRings` /
  `isSheafyTateRing_structurePresheaf_isSheaf` — Tate-ring level, taking an
  explicit completion model `P` and an explicit valid `Bplus` of it.
-/

noncomputable section

universe u

namespace ValuationSpectrum

section PairLevel

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **Pair-level sheafiness makes the public structure presheaf a sheaf of
topological rings** (Wedhorn Remark 8.20, generic form): the projective-limit
presheaf of `Spa (A, Aplus)` satisfies `Hom_cont(T, −)`-unique-gluing for every
topological commutative test ring. -/
theorem isSheafyFor_structurePresheaf_isSheafOfTopologicalRings
    (Aplus : RingOfIntegralElements A) (h : IsSheafyFor A Aplus) :
    letI := Aplus.toPlusSubring
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings (structurePresheaf A) := by
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  exact (structurePresheaf_isSheafOfTopologicalRings_iff A).mpr h

/-- **Pair-level sheafiness makes the public structure presheaf a categorical
sheaf** ([Stacks 00VR]). -/
theorem isSheafyFor_structurePresheaf_isSheaf
    (Aplus : RingOfIntegralElements A) (h : IsSheafyFor A Aplus) :
    letI := Aplus.toPlusSubring
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    (structurePresheaf A).IsSheaf := by
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  exact structurePresheaf_isSheaf A h

end PairLevel

section TateLevel

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTateRing A]

/-- **Ring-level (Tate) sheafiness makes the public structure presheaf of every
completion model, at every valid ring of integral elements, a sheaf of topological
rings** — the explicit-`P`-and-`Bplus` form. -/
theorem isSheafyTateRing_structurePresheaf_isSheafOfTopologicalRings
    (h : IsSheafyTateRing A) (P : PairOfDefinition A)
    (Bplus : RingOfIntegralElements (CompletionModel A P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel A P)⁺ : Subring (CompletionModel A P)) := Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel A P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (structurePresheaf (CompletionModel A P)) :=
  isSheafyFor_structurePresheaf_isSheafOfTopologicalRings Bplus (h P Bplus)

/-- **Ring-level (Tate) sheafiness makes the public structure presheaf of every
completion model a categorical sheaf** — the explicit-`P`-and-`Bplus` form. -/
theorem isSheafyTateRing_structurePresheaf_isSheaf
    (h : IsSheafyTateRing A) (P : PairOfDefinition A)
    (Bplus : RingOfIntegralElements (CompletionModel A P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel A P)⁺ : Subring (CompletionModel A P)) := Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel A P) :=
      hasLocLiftPowerBounded_faithful
    (structurePresheaf (CompletionModel A P)).IsSheaf :=
  isSheafyFor_structurePresheaf_isSheaf Bplus (h P Bplus)

/-- `IsSheafyTateRing` gives `IsLimitSheaf` at every completion model and valid
pair — the explicit projection (the public all-open structure presheaf is then a
sheaf of topological rings for every `P` and `B⁺`, by the two wrappers above). -/
theorem isSheafyTateRing_isLimitSheaf (h : IsSheafyTateRing A) (P : PairOfDefinition A)
    (Bplus : RingOfIntegralElements (CompletionModel A P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel A P)⁺ : Subring (CompletionModel A P)) := Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel A P) :=
      hasLocLiftPowerBounded_faithful
    IsLimitSheaf (CompletionModel A P) :=
  h P Bplus

end TateLevel

end ValuationSpectrum
