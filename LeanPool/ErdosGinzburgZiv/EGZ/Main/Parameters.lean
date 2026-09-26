/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic

/-!
# Error margins and the driving function in the main argument

These estimates use a uniform bound `C` for the hollow constant.  They avoid
the particular exponential constants in the paper; only a positive margin
after rounding and balancing is needed.
-/

@[expose] public section

namespace EGZ.MainProof

/-- A sufficiently small internal loss parameter. -/
noncomputable def errorScale (C ζ : ℝ) : ℝ := ζ / (100 * (C + 1))

theorem errorScale_pos {C ζ : ℝ} (hC : 0 ≤ C) (hζ : 0 < ζ) :
    0 < errorScale C ζ := by unfold errorScale; positivity

theorem errorScale_le {C ζ : ℝ} (hC : 0 ≤ C) (hζ : ζ ≤ 1) :
    errorScale C ζ ≤ 1 / 100 := by
  unfold errorScale
  apply (div_le_iff₀ (by positivity : 0 < 100 * (C + 1))).2
  linarith

theorem errorScale_le_inv {C ζ W : ℝ} (hC : 0 ≤ C)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hW : 0 < W) (hWC : W ≤ C) :
    errorScale C ζ ≤ W⁻¹ := by
  have he := (errorScale_pos hC hζ).le
  have heq : errorScale C ζ * (100 * (C + 1)) = ζ := by
    unfold errorScale
    exact div_mul_cancel₀ _ (by positivity)
  rw [← one_div, le_div_iff₀ hW]
  exact ((mul_le_mul_of_nonneg_left (by linarith : W ≤ 100 * (C + 1)) he).trans_eq
    heq).trans hζ1

/-- The flag lemma supplies this fraction of `p` in every nonempty fibre,
because the normalized input contains at least `p` terms. -/
noncomputable def gapScale (d : ℕ) (δ : ℝ) (K : ℕ) : ℝ :=
  δ ^ 3 * (K : ℝ)⁻¹ ^ d

theorem gapScale_pos {d K : ℕ} {δ : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K) :
    0 < gapScale d δ K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  unfold gapScale
  positivity

/-- A fourth power accounts for the two rounding factors, the retained
mass loss, and the final reserve in each fibre. -/
theorem balancing_margin {C ζ W : ℝ} (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hW : 0 ≤ W) (hWC : W ≤ C) :
    (1 + errorScale C ζ) * W ≤
      (1 - errorScale C ζ) ^ 4 * (W + ζ) := by
  let e := errorScale C ζ
  have he0 : 0 ≤ e := (errorScale_pos hC hζ).le
  have heq : e * (100 * (C + 1)) = ζ := by
    dsimp [e, errorScale]
    exact div_mul_cancel₀ _ (by positivity)
  have hcoeff : 5 * W + 4 * ζ ≤ 100 * (C + 1) := by linarith
  have hsmall : e * (5 * W + 4 * ζ) ≤ ζ := by
    exact (mul_le_mul_of_nonneg_left hcoeff he0).trans_eq heq
  have hbern : 1 - 4 * e ≤ (1 - e) ^ 4 := by
    have hprod := mul_nonneg (sq_nonneg e) (show 0 ≤ (e - 2) ^ 2 + 2 by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hbern (show 0 ≤ W + ζ by positivity)
  change (1 + e) * W ≤ (1 - e) ^ 4 * (W + ζ)
  nlinarith

/-- The numerical step after rounding and balanced combination.  The
centrality denominator `θ M` is bounded below by retained mass divided by
the hollow constant. -/
theorem coefficient_le_reserve {C ζ W p m R a : ℝ}
    (hC : 0 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hW : 0 ≤ W) (hWC : W ≤ C)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hR : 0 < R)
    (hretained : (1 - errorScale C ζ) * (W + ζ) * p ≤ R)
    (ha : a ≤ (1 + errorScale C ζ) / (1 - errorScale C ζ) ^ 2 * p * W * m / R) :
    a ≤ (1 - errorScale C ζ) * m := by
  let e := errorScale C ζ
  have he1 : e < 1 := (errorScale_le hC hζ1).trans_lt (by norm_num)
  have he : 0 < 1 - e := sub_pos.mpr he1
  have hmargin := balancing_margin hC hζ hζ1 hW hWC
  change (1 + e) * W ≤ (1 - e) ^ 4 * (W + ζ) at hmargin
  have hscaled := mul_le_mul_of_nonneg_right hmargin (mul_nonneg hp hm)
  have hret := mul_le_mul_of_nonneg_left hretained
    (show 0 ≤ (1 - e) ^ 3 * m by positivity)
  have hnum : (1 + e) * p * W * m ≤ (1 - e) ^ 3 * m * R := by
    dsimp only [e] at hret ⊢
    nlinarith [hscaled]
  apply ha.trans
  change (1 + e) / (1 - e) ^ 2 * p * W * m / R ≤ (1 - e) * m
  apply (div_le_iff₀ hR).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos he)).2
  nlinarith [hnum]

/-- A pointwise prescribed threshold has a monotone majorant strictly
larger than the identity.  No monotonicity of expansion thresholds is
assumed. -/
def drivingFunction (threshold : ℕ → ℕ) (K : ℕ) : ℕ :=
  K + 1 + (Finset.range (K + 1)).sup threshold

theorem drivingFunction_isGrowing (threshold : ℕ → ℕ) :
    IsGrowing (drivingFunction threshold) := by
  constructor
  · intro a b hab
    exact Nat.add_le_add (Nat.add_le_add_right hab 1)
      (Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hab 1)))
  · intro K
    unfold drivingFunction
    omega

theorem threshold_lt_drivingFunction (threshold : ℕ → ℕ) (K : ℕ) :
    threshold K < drivingFunction threshold K := by
  have h : threshold K ≤ (Finset.range (K + 1)).sup threshold :=
    Finset.le_sup (f := threshold) (Finset.mem_range.mpr (Nat.lt_succ_self K))
  unfold drivingFunction
  omega

end EGZ.MainProof
