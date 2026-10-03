/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain

/-! Spatial product-rule lemmas for a finite cutoff ansatz. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- Spatial gradient of a finite weighted sum, with the pointwise derivatives
of the summands as the only regularity input. -/
theorem spaceGrad_finiteWeightedSum
    {ι : Type*} (S : Finset ι) (T H : Vec 2 → ℝ)
    (c : ι → ℝ) (P : ι → Vec 2 → ℝ) (x : Vec 2)
    {LT LH : Vec 2 →L[ℝ] ℝ} (LP : ι → Vec 2 →L[ℝ] ℝ)
    (hT : HasFDerivAt T LT x) (hH : HasFDerivAt H LH x)
    (hP : ∀ k ∈ S, HasFDerivAt (P k) (LP k) x) (i : Fin 2) :
    spaceGrad (fun y => T y + (∑ k ∈ S, c k * P k y) + H y) x i =
      spaceGrad T x i + (∑ k ∈ S, c k * spaceGrad (P k) x i) +
        spaceGrad H x i := by
  let Lsum : Vec 2 →L[ℝ] ℝ := ∑ k ∈ S, c k • LP k
  have hfun : (fun y => ∑ k ∈ S, c k * P k y) =
      ∑ k ∈ S, (fun y => c k * P k y) := by
    funext y
    simp
  have hsum : HasFDerivAt (fun y => ∑ k ∈ S, c k * P k y) Lsum x := by
    rw [hfun]
    apply HasFDerivAt.sum
    intro k hk
    simpa [Lsum, smul_eq_mul] using (hP k hk).const_mul (c k)
  have hfull : HasFDerivAt
      (fun y => T y + (∑ k ∈ S, c k * P k y) + H y)
      (LT + Lsum + LH) x := by
    convert hT.add hsum |>.add hH using 1
  have hTcoord : spaceGrad T x i = LT (basisVec i) := by
    rw [spaceGrad, hT.fderiv]
  have hHcoord : spaceGrad H x i = LH (basisVec i) := by
    rw [spaceGrad, hH.fderiv]
  have hPcoord (k : ι) (hk : k ∈ S) :
      spaceGrad (P k) x i = LP k (basisVec i) := by
    rw [spaceGrad, (hP k hk).fderiv]
  rw [spaceGrad, hfull.fderiv, hTcoord, hHcoord]
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, add_left_inj, add_right_inj, Lsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hPcoord k hk]

end AVenhance.Infra.Section5
