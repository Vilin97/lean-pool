/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

lemma morrey_cylinder_lp_bound {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (cylinderPowerIntegral P f z r) ^ (1 / P) ≤
      (ENNReal.ofReal r) ^ (5 * (1 / P - 1 / θ)) * morreyNorm P θ f := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hθ0 : 0 < θ := lt_of_lt_of_le hP0 hPθ
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let d : ℝ := 5 * (1 / P - 1 / θ)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hcell : morreyCell P θ f z r ≤ morreyNorm P θ f := by
    unfold morreyNorm
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P θ f z s.1)
        ⟨r, hr⟩)
  have hexp : -(5 * (1 - P / θ) / P) = -d := by
    dsimp [d]
    field_simp [hP0.ne', hθ0.ne']
  have hcell' : A ^ (-d) * (cylinderPowerIntegral P f z r) ^ (1 / P) ≤
      morreyNorm P θ f := by
    simpa only [morreyCell, A, hexp] using hcell
  have hcancel : A ^ d * A ^ (-d) = 1 := by
    rw [← ENNReal.rpow_add _ _ hA0 hAtop, add_neg_cancel, ENNReal.rpow_zero]
  calc
    (cylinderPowerIntegral P f z r) ^ (1 / P) =
        A ^ d * (A ^ (-d) * (cylinderPowerIntegral P f z r) ^ (1 / P)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ A ^ d * morreyNorm P θ f := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_left hcell' (A ^ d))
    _ = (ENNReal.ofReal r) ^ (5 * (1 / P - 1 / θ)) * morreyNorm P θ f := by
      rfl

end CKN.Core.HeatPotential
