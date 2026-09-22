/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.CompleteHahnGerm
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CompleteGermRefinement

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Complete Hahn Germ Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.CompleteHahnGerm.Support

universe u v

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K]

private def seriesRingEquiv :
    NonpositiveSeries G K ≃+* HahnSeries.Nonpositive G K where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def seriesAlgEquiv :
    NonpositiveSeries G K ≃ₐ[K] HahnSeries.Nonpositive G K :=
  AlgEquiv.ofRingEquiv (f := seriesRingEquiv) fun k ↦ by
    apply Subtype.ext
    change (algebraMap K (HahnSeries G K)) k =
      ((HahnSeries.Nonpositive.C (Γ := G) k : HahnSeries.Nonpositive G K) : HahnSeries G K)
    rw [HahnSeries.Nonpositive.coe_C, HahnSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]

@[simp] private theorem coe_seriesEquiv (x : NonpositiveSeries G K) :
    ((seriesAlgEquiv x : HahnSeries.Nonpositive G K) : HahnSeries G K) = x := rfl

variable [NoMinOrder G]
variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]
variable [Nontrivial G] [CompleteSpace G] [CharZero K]

private theorem boundedAwayIdeal_map_eq :
    (HahnSeries.Nonpositive.cantorBendixsonValuation (G := G) (R := K)).supp =
      (BoundedAwayIdeal G K).map seriesAlgEquiv := by
  ext y
  rw [HahnSeries.Nonpositive.mem_cantorBendixsonValuation_supp,
    Ideal.mem_map_iff_of_surjective seriesAlgEquiv seriesAlgEquiv.surjective]
  constructor
  · rintro ⟨r, hr, hyr⟩
    refine ⟨seriesAlgEquiv.symm y, ⟨r, hr, ?_⟩, seriesAlgEquiv.apply_symm_apply y⟩
    change (y : HahnSeries G K).support ⊆ Set.Iic r
    exact hyr
  · rintro ⟨x, ⟨r, hr, hxr⟩, rfl⟩
    exact ⟨r, hr, by simpa only [coe_seriesEquiv] using hxr⟩

/-- The internal Cantor–Bendixson construction gives the standalone polynomial presentation. -/
theorem isPolynomialRing (G : Type u) (K : Type v)
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [NoMinOrder G] [Field K] :
    IsPolynomialRing G K := by
  intro _ _ _ _ _ _ _ _ _
  obtain ⟨ι, ⟨equiv⟩⟩ :=
    HahnSeries.Nonpositive.exists_mvPolynomial_algEquiv_germ (G := G) (K := K)
  let quotientEquiv : Germ G K ≃ₐ[K]
      HahnSeries.Nonpositive G K ⧸
        (HahnSeries.Nonpositive.cantorBendixsonValuation (G := G) (R := K)).supp :=
    Ideal.quotientEquivAlg (BoundedAwayIdeal G K)
      (HahnSeries.Nonpositive.cantorBendixsonValuation (G := G) (R := K)).supp
      seriesAlgEquiv boundedAwayIdeal_map_eq
  exact ⟨ι, ⟨equiv.trans quotientEquiv.symm⟩⟩

/-- A polynomial presentation gives four-factor refinement. -/
theorem hasRefinement (G : Type u) (K : Type v)
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [NoMinOrder G] [Field K] :
    HasRefinement G K := by
  intro _ _ _ _ _ _ _ _ _
  obtain ⟨ι, ⟨equiv⟩⟩ := isPolynomialRing G K
  let : IsDomain (Germ G K) :=
    Function.Injective.isDomain equiv.symm.toRingHom equiv.symm.injective
  let : DecompositionMonoid (Germ G K) :=
    MulEquiv.decompositionMonoid equiv.symm.toMulEquiv
  intro a b c d habcd
  exact (hasFourFactorRefinement_of_decompositionMonoid (R := Germ G K)).refine habcd

end ConwayRefinement.Standalone.CompleteHahnGerm.Support
