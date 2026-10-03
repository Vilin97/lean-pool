/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.H1.Definitions
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Periodic H¹ bridge to CoarseGraining

The carrier records its weak gradient on all of `ℝ²`. Compactly supported tests in the
open unit cube are also tests on all of `ℝ²`, so restricting the two L² witnesses gives the
CoarseGraining `H1Function` on that cube.
-/

@[expose] public section

open MeasureTheory Homogenization

namespace AVenhance.Proofs.IsPeriodicH1With

/-- A periodic weak-gradient witness restricts to `H1Function` on the open cell. -/
theorem exists_h1Function {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) :
    ∃ v : H1Function AVenhance.unitCube, v.toFun = u ∧ v.grad = Du := by
  rcases h with ⟨_hu_periodic, _hDu_periodic, hu_l2, hDu_l2, hu_weak⟩
  refine ⟨⟨u, Du, hu_l2, hDu_l2, ?_⟩, rfl, rfl⟩
  intro i φ hφ_smooth hφ_compact hφ_support
  have hderiv_support : tsupport (fun x => (fderiv ℝ φ x) (basisVec i)) ⊆ tsupport φ :=
    tsupport_fderiv_apply_subset ℝ (basisVec i)
  have hleft :
      ∫ x in AVenhance.unitCube,
        u x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      ∫ x, u x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport φ := fun hmem => hx (hφ_support hmem)
    have hderiv_not : x ∉ tsupport (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      fun hmem => hnot (hderiv_support hmem)
    simp [image_eq_zero_of_notMem_tsupport hderiv_not]
  have hright :
      ∫ x in AVenhance.unitCube, Du x i * φ x ∂volume =
      ∫ x, Du x i * φ x ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport φ := fun hmem => hx (hφ_support hmem)
    simp [image_eq_zero_of_notMem_tsupport hnot]
  rw [hleft, hright]
  have hglobal := hu_weak i φ hφ_smooth hφ_compact
    (hφ_support.trans (Set.subset_univ _))
  simpa using hglobal

end AVenhance.Proofs.IsPeriodicH1With
