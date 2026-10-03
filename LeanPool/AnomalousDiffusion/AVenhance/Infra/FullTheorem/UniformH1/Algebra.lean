/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TLemmasNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction

/-! # Helpers for the `H¹` case of `r.LeBron.2`

Abstract-real rpow algebra, `L²` triangle inequality for differences, and positivity of the
gradient for mean-zero `H¹` data. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.UniformH1

open AVenhance

/-- `(h^ν / 2)^{-p} · h^μ = 2^p · h^ν` when `μ = ν (1 + p)`. -/
theorem rpow_scale_identity {h ν μ p : ℝ} (hh : 0 < h) (hμ : μ = ν * (1 + p)) :
    (h ^ ν / 2) ^ (-p) * h ^ μ = (2 : ℝ) ^ p * h ^ ν := by
  have e : h ^ (ν * (-p)) * h ^ μ = h ^ ν := by
    rw [← Real.rpow_add hh, hμ]
    congr 1
    ring
  have hh' : (h ^ ν / 2) ^ (-p) = h ^ (ν * (-p)) * 2 ^ p := by
    rw [Real.div_rpow (Real.rpow_nonneg hh.le _) (by norm_num), ← Real.rpow_mul hh.le,
      Real.rpow_neg (by norm_num)]
    field_simp
  calc (h ^ ν / 2) ^ (-p) * h ^ μ = (h ^ (ν * (-p)) * h ^ μ) * 2 ^ p := by rw [hh']; ring
    _ = _ := by rw [e]; ring

/-- `1 ≤ (h^ν / 2)^{-p}` for `0 < h ≤ 1`, `p ≥ 0`, `0 < ν`. -/
theorem one_le_scale {h ν p : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hν : 0 ≤ ν)
    (hp : 0 ≤ p) : 1 ≤ (h ^ ν / 2) ^ (-p) := by
  have hpos : 0 < h ^ ν / 2 := by positivity
  have h1 : h ^ ν ≤ 1 := Real.rpow_le_one hh.le hh1 hν
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos (by linarith) (by linarith)

/-- Triangle inequality for a difference. -/
theorem sqrt_l2_sub_le {a b : Vec 2 → ℝ} (ha : MemL2On unitCube a) (hb : MemL2On unitCube b) :
    Real.sqrt (l2NormSq (fun x => a x - b x)) ≤ Real.sqrt (l2NormSq a) + Real.sqrt (l2NormSq b) :=
        by
  have hb' : MemL2On unitCube (fun x => -b x) := by
    change MemLp b 2 (volume.restrict unitCube) at hb
    exact hb.neg
  have := Infra.Section4.sqrt_l2NormSq_add_le ha hb'
  simpa [sub_eq_add_neg, l2NormSq] using this

theorem sqrt_l2_tri {a b c : Vec 2 → ℝ} (ha : MemL2On unitCube a) (hb : MemL2On unitCube b)
    (hc : MemL2On unitCube c) :
    Real.sqrt (l2NormSq (fun x => a x - c x)) ≤
      Real.sqrt (l2NormSq (fun x => a x - b x)) + Real.sqrt (l2NormSq (fun x => b x - c x)) := by
  have h := Infra.Section4.sqrt_l2NormSq_add_le (ha.sub hb) (hb.sub hc)
  have e : (fun x => (a x - b x) + (b x - c x)) = fun x => a x - c x := by
    funext x; ring
  rw [← e]
  exact h

theorem l2NormSq_nonneg (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  integral_nonneg fun x => sq_nonneg (f x)

theorem gradNormSq_nonneg (Df : Vec 2 → Vec 2) : 0 ≤ gradNormSq Df :=
  integral_nonneg fun x => vecNormSq_nonneg (Df x)

theorem gradient_pos {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    0 < gradNormSq Df := by
  have hP := AVenhance.Infra.Heat.meanZero_frozenPeriodicH1_fourierPoincare hf hm
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (by positivity : 0 ≤ 4 * Real.pi ^ 2)) (le_of_not_gt h)
  exact (not_le_of_gt hA) (hP.trans hh)

end AVenhance.Infra.FullTheorem.UniformH1
