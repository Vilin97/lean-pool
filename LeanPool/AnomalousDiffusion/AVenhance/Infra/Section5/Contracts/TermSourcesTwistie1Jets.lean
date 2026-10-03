/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Term
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureSpatialWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2

/-! # Jets of the coefficient and of `T` in the form used by the `twistie1` estimate

* regularity and periodicity of the coefficient `B_t = K_m(t) + s_{m-1}(t,·)`;
* the jets of `B_t` from those of `K_m - κ_{m-1} I + s_{m-1}` (adding the constant `κ_{m-1} I`);
* the positive jets of `T` in `L²(unitCell)` from the `l2NormSq` bounds of
  `RelativeError.PositiveTemperatureJets`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

theorem se_B_smooth {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) :
    ∀ i j, ContDiff ℝ ∞ (fun x => (I.Kmat κ m t + I.sMat hΦ m κ t x) i j) := by
  have hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞) (fun x => I.flowGrad hΦ m l t x) := fun l =>
    (iterate_flowGrad_joint_smooth I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hS := sMat_spatial_contDiff I hΦ m hm κ t hflow
  intro i j
  have := RelativeError.contDiff_matrix_entry hS i j
  simpa [Matrix.add_apply] using contDiff_const.add this

theorem se_B_periodic {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ t : ℝ) :
    IsZ2Periodic (fun x => I.Kmat κ m t + I.sMat hΦ m κ t x) := by
  intro n x
  simp only
  rw [RelativeError.sMat_isZ2Periodic I hΦ m κ t n x]

/-- The jets of `B = K_m + s_{m-1}` from those of `K_m - κ_{m-1} I + s_{m-1}`. -/
theorem se_B_jets {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κp t : ℝ) {CB r L : ℝ} (hκp : 0 ≤ κp)
    (hCB : 0 ≤ CB) (hr0 : 0 ≤ r) (hrL : r ≤ L)
    (hcoef : ∀ (x : Vec 2) (p : List (Fin 2)) (j k : Fin 2),
      |iterateMatrixWord (fun y => I.Kmat κm m t - κp • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y) p x j k| ≤ κp * CB * (p.length.factorial : ℝ) * r ^ p.length) :
    ∀ i j w x, |amnrSpaceWord w (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) x| ≤
      (κp * (CB + 1)) * w.length.factorial * L ^ w.length := by
  intro i j w x
  have hshift : (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) =
      fun y => (I.Kmat κm m t - κp • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) i j +
        κp * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    funext y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  by_cases hw : w = []
  · subst hw
    have h0 := hcoef x [] i j
    simp only [iterateMatrixWord, iterateSpatialWord, List.length_nil, Nat.factorial_zero,
      Nat.cast_one, pow_zero, mul_one] at h0
    rw [hshift]
    simp only [amnrSpaceWord, List.length_nil, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one]
    have h1 : |κp * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ κp := by
      rw [abs_mul, abs_of_nonneg hκp]
      have : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
        simp only [Matrix.one_apply]; split_ifs <;> norm_num
      nlinarith
    calc _ ≤ |(I.Kmat κm m t - κp • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t x) i j| + |κp * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := abs_add_le _ _
      _ ≤ κp * CB + κp := add_le_add h0 h1
      _ = κp * (CB + 1) := by ring
  · rw [hshift, se_amnrSpaceWord_add_const _ _ w hw, ←
      RelativeError.iterateSpatialWord_eq_amnrSpaceWord]
    have h0 := hcoef x w i j
    simp only [iterateMatrixWord] at h0
    refine h0.trans ?_
    have hf : (0 : ℝ) ≤ (w.length.factorial : ℝ) := Nat.cast_nonneg _
    calc κp * CB * (w.length.factorial : ℝ) * r ^ w.length
        ≤ κp * (CB + 1) * (w.length.factorial : ℝ) * L ^ w.length := by
          apply mul_le_mul _ (pow_le_pow_left₀ hr0 hrL _) (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hκp) hf

/-- From the `L²` jets on the unit cube to the `eLpNorm` jets on the unit cell. -/
theorem se_hTb_of_l2 {Tt : Vec 2 → ℝ} (hT : ContDiff ℝ ∞ Tt) {M L : ℝ}
    (hjets : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n Tt x (fun j => basisVec (i j)))) ≤
        M * n.factorial * L ^ n) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w Tt) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal (M * w.length.factorial * L ^ w.length) := by
  intro w hw
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → Fin 2), w = List.ofFn α :=
    ⟨w.length, w.get, (List.ofFn_get w).symm⟩
  rw [List.length_ofFn] at hw ⊢
  rw [amnrSpaceWord_ofFn_eq_iteratedFDeriv hT n α,
    Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube]
  have hc : Continuous (fun x => iteratedFDeriv ℝ n Tt x (fun j => basisVec (α j))) := by
    have := hT.continuous_iteratedFDeriv (m := n) (by simp)
    fun_prop
  set f : Vec 2 → ℝ := fun x => iteratedFDeriv ℝ n Tt x (fun j => basisVec (α j)) with hf
  have hB : 0 ≤ M * n.factorial * L ^ n := by positivity
  have hsq : Integrable (fun x => f x ^ 2) (volume.restrict unitCube) :=
    LeftToShow.integrableOn_unitCube_of_continuous (f := fun x => f x ^ 2) (hc.pow 2)
  have hEnergy : (∫ x in unitCube, f x ^ 2) ≤ (M * n.factorial * L ^ n) ^ 2 :=
    (Real.sqrt_le_iff.mp (hjets n α hw)).2
  exact amnr_scalar_eLpNorm_two_le_of_square hc.aestronglyMeasurable hsq hB hEnergy

end AVenhance.Infra.Section5.Contracts
end
