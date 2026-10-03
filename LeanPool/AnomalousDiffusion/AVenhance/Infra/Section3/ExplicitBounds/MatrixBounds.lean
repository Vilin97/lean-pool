/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory

/-! # Matrix Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section3
open AVenhance

/-- The common indicator between the two cutoff envelopes implies
`ζ̂ ≤ ξ̂`, so the large-scale coefficients have total weight at most one. -/
theorem hatZetaML_le_hatXiML {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ) :
    I.hatZetaML m l t ≤ I.hatXiML m l t :=
  (I.hatZeta_le m hm l t).trans (I.hatXi_ge m hm l t)

/-- Zeroth-order `e.Lmn.bound`, with explicit `n! 2ⁿ` dependence. -/
theorem LMN_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (t : ℝ) :
    |I.LMN κ m n t| ≤ (n.factorial : ℝ) * 2 ^ n *
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ := by
  classical
  let S := (I.hatZetaML_support_finite hm t).toFinset
  let B := (n.factorial : ℝ) * 2 ^ n *
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum : I.LMN κ m n t = ∑ l ∈ S,
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) := by
    unfold Ingredients.LMN
    apply tsum_eq_sum
    intro l hl
    have hz : I.hatZetaML m l t = 0 := by
      by_contra hne
      exact hl ((Set.Finite.mem_toFinset _).2 hne)
    simp [hz]
  have hzsum : (∑ l ∈ S, I.hatZetaML m l t) ≤ 1 := by
    calc
      (∑ l ∈ S, I.hatZetaML m l t) ≤ ∑ l ∈ S, I.hatXiML m l t :=
        Finset.sum_le_sum (fun l _ => hatZetaML_le_hatXiML I hm l t)
      _ ≤ ∑' l : ℤ, I.hatXiML m l t :=
        (summable_of_hasFiniteSupport (I.hatXiML_support_finite hm t)).sum_le_tsum S
          (fun l _ => (Infra.Ingredients.hatXiML_mem_Icc I hm l t).1)
      _ = 1 := Infra.Ingredients.hatXiML_partition I hm t
  rw [hsum]
  calc
    |∑ l ∈ S, I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))| ≤
      ∑ l ∈ S, |I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ S, I.hatZetaML m l t * B := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_of_nonneg (hatZetaML_mem_Icc I hm l t).1]
      exact mul_le_mul_of_nonneg_left (LMN_memory_integral_abs_le I hm hκ n l t)
        (hatZetaML_mem_Icc I hm l t).1
    _ ≤ B := by
      rw [← Finset.sum_mul]
      simpa using mul_le_mul_of_nonneg_right hzsum hB

/-- Unit-time averaging preserves the entrywise bound for `j`. -/
theorem jMN_average_entry_abs_le {β : ℝ} (I : Ingredients β) (m : ℕ)
    {n : ℕ} (hn : n ≤ Nstar β) {κ : ℝ} (hκ : 0 < κ) (i j : Fin 2) :
    |timeAvgMat (I.jMN κ m n) i j| ≤
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.Czeta / tau β I.Λ m ^ n) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => I.jMN κ m n t i j)
    (fun t _ => by simpa only [Real.norm_eq_abs] using jMN_entry_abs_le I m hn hκ t i j)
  simpa [timeAvgMat, Real.norm_eq_abs] using h

/-- Exact cancellation of the factorial and relaxation factors. -/
theorem MatrixBounds.memory_j_bound_product {β : ℝ} (I : Ingredients β) (m n : ℕ)
    {κ : ℝ} (hκ : 0 < κ) :
    ((n.factorial : ℝ) * 2 ^ n *
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
      ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.Czeta / tau β I.Λ m ^ n)) =
      (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (2 * epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ^ n := by
  have hτ := (I.tau_pos' m).ne'
  have hπ := Real.pi_pos.ne'
  have hε := (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [div_pow, mul_pow, inv_div]
  field_simp
  ring

/-- Zeroth-order `K` estimate, including the molecular identity term.
The ratio condition is weaker than the paper's `ε² ≤ κτ/2`. -/
theorem Kmat_entry_abs_le_zero {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hratio : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m)
    (t : ℝ) (i j : Fin 2) :
    |I.Kmat κ m t i j| ≤ κ + (Nstar β : ℝ) *
      (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  classical
  let D := I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hτ := I.tau_pos' m
  have hr : 0 ≤ 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) := by positivity
  have hr1 : 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    have hπ : 2 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    calc
      2 * epsilon β I.Λ m ^ 2 ≤ 2 * (κ * tau β I.Λ m) := by gcongr
      _ ≤ (4 * Real.pi ^ 2) * (κ * tau β I.Λ m) :=
        mul_le_mul_of_nonneg_right hπ (mul_nonneg hκ.le hτ.le)
      _ = _ := by ring
  have hterm : ∀ n ∈ Finset.range (Nstar β),
      |I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| ≤ D := by
    intro n hn
    have hn' : n ≤ Nstar β := by simp only [Finset.mem_range] at hn; omega
    rw [abs_mul]
    calc
      |I.LMN κ m n t| * |timeAvgMat (I.jMN κ m n) i j| ≤
        ((n.factorial : ℝ) * 2 ^ n *
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
        ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
          (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
          (I.Czeta / tau β I.Λ m ^ n)) := by
            apply mul_le_mul (LMN_abs_le I hm hκ n t)
              (jMN_average_entry_abs_le I m hn' hκ i j) (abs_nonneg _)
            positivity
      _ = D * (2 * epsilon β I.Λ m ^ 2 /
          (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ^ n := MatrixBounds.memory_j_bound_product I m n hκ
      _ ≤ D := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) hD
  have hid : |κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ κ := by
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij, abs_of_pos hκ]
    · simp [hij, hκ.le]
  have hform : I.Kmat κ m t i j = κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j := by
    unfold Ingredients.Kmat
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  rw [hform]
  calc
    |κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
        ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| ≤
      |κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| +
        ∑ n ∈ Finset.range (Nstar β),
          |I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| :=
        (abs_add_le _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ κ + ∑ n ∈ Finset.range (Nstar β), D :=
      add_le_add hid (Finset.sum_le_sum hterm)
    _ = _ := by simp [D]

/-- The positive-order derivative formula keeps only the memory factors:
unit-time averages of `j` are constant in time. -/
theorem Kmat_entry_derivative_eq_sum {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {ℓ : ℕ}
    (hpos : 0 < ℓ) (hℓ : ℓ ≤ Nstar β) (t : ℝ) (i j : Fin 2) :
    iteratedDeriv ℓ (fun s => I.Kmat κ m s i j) t =
      ∑ n ∈ Finset.range (Nstar β),
        iteratedDeriv ℓ (I.LMN κ m n) t * timeAvgMat (I.jMN κ m n) i j := by
  classical
  have hform : (fun s => I.Kmat κ m s i j) = fun s =>
      κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
        ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n s * timeAvgMat (I.jMN κ m n) i j := by
    funext s
    simp only [Ingredients.Kmat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply]
  have hterm : ∀ n ∈ Finset.range (Nstar β), ContDiff ℝ (ℓ : ℕ∞)
      (fun s => I.LMN κ m n s * timeAvgMat (I.jMN κ m n) i j) := by
    intro n _
    exact ((LMN_contDiff I hm hκ n).of_le (by exact_mod_cast hℓ)).mul contDiff_const
  rw [hform, iteratedDeriv_fun_add (by fun_prop) (ContDiff.sum hterm).contDiffAt,
    iteratedDeriv_const, ite_eq_right (by omega), zero_add,
    iteratedDeriv_fun_sum (fun n hn => (hterm n hn).contDiffAt)]
  apply Finset.sum_congr rfl
  intro n _
  exact iteratedDeriv_mul_const_field _ _

/-- Positive-order `e.bfK.dervs`, with explicit constants, for `ℓ ≤ N_*`.
The small-ratio premise is weaker than the printed `ε² ≤ κτ/2`. -/
theorem Kmat_entry_derivative_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hratio : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m) {ℓ : ℕ}
    (hpos : 0 < ℓ) (hℓ : ℓ ≤ Nstar β) (t : ℝ) (i j : Fin 2) :
    |iteratedDeriv ℓ (fun s => I.Kmat κ m s i j) t| ≤
      (Nstar β : ℝ) * (2 ^ ℓ * I.Chat ^ 2 / tauP β I.Λ m ^ ℓ) *
        (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  let A := 2 ^ ℓ * I.Chat ^ 2 / tauP β I.Λ m ^ ℓ
  let D := I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  have hτP := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr : 0 ≤ 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) := by positivity
  have hr1 : 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    have hπ : 2 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    calc
      2 * epsilon β I.Λ m ^ 2 ≤ 2 * (κ * tau β I.Λ m) := by gcongr
      _ ≤ (4 * Real.pi ^ 2) * (κ * tau β I.Λ m) :=
        mul_le_mul_of_nonneg_right hπ (mul_nonneg hκ.le hτ.le)
      _ = _ := by ring
  have hterm : ∀ n ∈ Finset.range (Nstar β),
      |iteratedDeriv ℓ (I.LMN κ m n) t * timeAvgMat (I.jMN κ m n) i j| ≤ A * D := by
    intro n hn
    have hn' : n ≤ Nstar β := by simp only [Finset.mem_range] at hn; omega
    rw [abs_mul]
    calc
      _ ≤ (A * ((n.factorial : ℝ) * 2 ^ n) *
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
        ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
          (I.Czeta / tau β I.Λ m ^ n)) := by
            apply mul_le_mul (LMN_derivative_abs_le I hm hκ n hℓ t)
              (jMN_average_entry_abs_le I m hn' hκ i j) (abs_nonneg _)
            positivity
      _ = A * (D * (2 * epsilon β I.Λ m ^ 2 /
          (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ^ n) := by
        rw [mul_assoc A, mul_assoc A, MatrixBounds.memory_j_bound_product I m n hκ]
      _ ≤ A * D := mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) hD) hA
  rw [Kmat_entry_derivative_eq_sum I hm hκ hpos hℓ]
  calc
    |∑ n ∈ Finset.range (Nstar β),
        iteratedDeriv ℓ (I.LMN κ m n) t * timeAvgMat (I.jMN κ m n) i j| ≤
      ∑ n ∈ Finset.range (Nstar β),
        |iteratedDeriv ℓ (I.LMN κ m n) t * timeAvgMat (I.jMN κ m n) i j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (Nstar β), A * D := Finset.sum_le_sum hterm
    _ = _ := by simp [A, D, mul_assoc]

/-- Uniform `C(β,C₀)` version for every order `0 ≤ ℓ ≤ N_*`.
The entrywise derivative matrix is measured in the elementwise supremum norm. -/
theorem Kmat_derivative_norm_le {β C₀ : ℝ} (I : Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {m : ℕ} (hm : 1 ≤ m)
    {κ : ℝ} (hκ : 0 < κ) (hratio : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m)
    {ℓ : ℕ} (hℓ : ℓ ≤ Nstar β) (t : ℝ) :
    ‖(fun i j : Fin 2 => iteratedDeriv ℓ (fun s => I.Kmat κ m s i j) t)‖ ≤
      (1 + (Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 3) /
        tauP β I.Λ m ^ ℓ * (κ + a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  have hz0 : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hh0 : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hC : 1 ≤ C₀ := I.one_le_Czeta.trans hz
  have hC0 : 0 ≤ C₀ := by linarith
  have hτ := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hB : 0 ≤ (1 + (Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 3) /
      tauP β I.Λ m ^ ℓ * (κ + a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by positivity
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro j
  rw [Real.norm_eq_abs]
  by_cases hl0 : ℓ = 0
  · subst ℓ
    simp only [iteratedDeriv_zero, pow_zero, div_one]
    apply (Kmat_entry_abs_le_zero I hm hκ hratio t i j).trans
    have hcf : I.Czeta ≤ 2 ^ Nstar β * C₀ ^ 3 := by
      calc
        I.Czeta ≤ C₀ := hz
        _ ≤ C₀ ^ 3 := le_self_pow₀ hC (by norm_num)
        _ ≤ 2 ^ Nstar β * C₀ ^ 3 := le_mul_of_one_le_left (by positivity)
          (one_le_pow₀ (by norm_num))
    have hX : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by positivity
    have hN : 0 ≤ (Nstar β : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ κ + ((Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 3) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
        rw [show (Nstar β : ℝ) * (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) =
          (Nstar β : ℝ) * I.Czeta * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) by ring]
        have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcf hN) hX
        convert add_le_add_left hmul κ using 1 <;> ring
      _ ≤ _ := by
        have hprod : 0 ≤ ((Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 3) * κ := by positivity
        nlinarith
  · apply (Kmat_entry_derivative_abs_le I hm hκ hratio (by omega) hℓ t i j).trans
    have hpow : (2 : ℝ) ^ ℓ ≤ 2 ^ Nstar β := pow_le_pow_right₀ (by norm_num) hℓ
    calc
      _ = ((Nstar β : ℝ) * 2 ^ ℓ * I.Chat ^ 2 * I.Czeta) /
          tauP β I.Λ m ^ ℓ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by ring
      _ ≤ ((Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 2 * C₀) /
          tauP β I.Λ m ^ ℓ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by gcongr
      _ ≤ _ := by
        rw [show (Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 2 * C₀ =
          (Nstar β : ℝ) * 2 ^ Nstar β * C₀ ^ 3 by ring]
        gcongr
        · linarith
        · exact le_add_of_nonneg_left hκ.le

/-- Smoothness of the matrix coefficient through the cutoff budget. -/
theorem Kmat_contDiff {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    {κ : ℝ} (hκ : 0 < κ) : ContDiff ℝ (Nstar β : ℕ∞) (I.Kmat κ m) :=
  contDiff_const.add (ContDiff.sum (fun n _ => (LMN_contDiff I hm hκ n).smul contDiff_const))

theorem MatrixBounds.iteratedDeriv_matrix_entries {F : ℝ → Fin 2 → Fin 2 → ℝ}
    {N ℓ : ℕ} (hf : ∀ i j, ContDiff ℝ (N : ℕ∞) (fun t => F t i j)) (hℓ : ℓ ≤ N) :
    iteratedDeriv ℓ F = fun t i j => iteratedDeriv ℓ (fun s => F s i j) t := by
  induction ℓ with
  | zero => simp only [iteratedDeriv_zero]
  | succ ℓ ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext t
    have hd : ∀ i j, Differentiable ℝ (iteratedDeriv ℓ (fun s => F s i j)) :=
      fun i j => (hf i j).differentiable_iteratedDeriv ℓ (by exact_mod_cast (show ℓ < N by omega))
    rw [deriv_pi (fun i => differentiableAt_pi.mpr (fun j => (hd i j).differentiableAt))]
    funext i j
    rw [deriv_pi (fun j => (hd i j).differentiableAt), iteratedDeriv_succ]

theorem MatrixBounds.diffusivity_scale_eq {β : ℝ} (I : Ingredients β) (m : ℕ) :
    a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β) =
      epsilon β I.Λ m ^ (β + gamma β) := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  unfold a
  rw [← Real.rpow_add he]
  congr 1
  ring

theorem MatrixBounds.amplitude_div_scale_eq {x β γ c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    (x ^ (β - 2)) ^ 2 * x ^ 4 / (c * x ^ (β + γ)) = (1 / c) * x ^ (β - γ) := by
  rw [← Real.rpow_natCast (x ^ (β - 2)) 2, ← Real.rpow_mul hx.le,
    ← Real.rpow_natCast x 4, ← Real.rpow_add hx]
  norm_num only [Nat.cast_ofNat]
  have he : (β - 2) * (2 : ℝ) + 4 = (β - γ) + (β + γ) := by ring
  rw [he, Real.rpow_add hx]
  field_simp

theorem MatrixBounds.length_power_previous_bound {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 2 ≤ m) :
    epsilon β I.Λ m ^ (β - gamma β) ≤
      (1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) *
        epsilon β I.Λ (m - 1) ^ (β + gamma β) := by
  have hq := Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt
  have hgpos := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hden : 0 < q β + 1 := by linarith only [hq]
  have hγlt : gamma β < β := by
    unfold gamma
    apply (div_lt_iff₀ hden).2
    have hβpos : 0 < β := by linarith [I.one_lt_beta]
    nlinarith only [hβpos]
  have hp : 0 ≤ β - gamma β := sub_nonneg.mpr hγlt.le
  have hbal : q β * (β - gamma β) = β + gamma β := by
    unfold gamma
    field_simp [hden.ne']
    ring
  have hA : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    unfold Infra.Ingredients.supergeoConstant
    positivity
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 := by
    have h := Infra.Ingredients.epsilon_le_lambda_pow I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hΛ : 1 ≤ (I.Λ : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7)
        I.two_pow_seven_le)
    exact h.trans (Real.rpow_le_one_of_one_le_of_nonpos hΛ (by simp))
  have hecur := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have heprev := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have hscale := (Infra.Ingredients.epsilon_supergeo I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1) (by omega)).2
  rw [show m - 1 + 1 = m by omega] at hscale
  have hscale' : epsilon β I.Λ m ≤
      (1 + Infra.Ingredients.supergeoConstant β) * epsilon β I.Λ (m - 1) ^ q β := by
    apply hscale.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg heprev.le _)
    exact add_le_add (le_refl 1) (mul_le_of_le_one_right hA he1)
  calc
    _ ≤ ((1 + Infra.Ingredients.supergeoConstant β) *
        epsilon β I.Λ (m - 1) ^ q β) ^ (β - gamma β) :=
          Real.rpow_le_rpow hecur.le hscale' hp
    _ = _ := by
      rw [Real.mul_rpow (by linarith only [hA]) (Real.rpow_nonneg heprev.le _),
        ← Real.rpow_mul heprev.le, hbal]

end AVenhance.Infra.Section3
