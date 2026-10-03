/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorGradient

/-! The pairwise spatial orthogonality behind the double-sum formula for the
moving-cutoff corrector energy. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance
open Homogenization

theorem MovingEnergyReduction.xiMK_mem_support_window {β : ℝ} (I : Ingredients β)
    {m : ℕ} (k : ℤ) (t : ℝ) (hξ : I.xiMK m k t ≠ 0) :
    (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∈
      Set.Icc (-(5 / 4 : ℝ)) (5 / 4) := by
  by_contra h
  exact hξ (xiMK_eq_zero_outside I k t h)

theorem MovingEnergyReduction.odd_mode_distance_le_two_of_xi_overlap {β : ℝ}
    (I : Ingredients β) {m : ℕ} {k l : ℤ}
    (t : ℝ) (hξk : I.xiMK m k t ≠ 0) (hξl : I.xiMK m l t ≠ 0) :
    |k - l| ≤ 2 := by
  have hτ := I.tau_pos' m
  have huk := MovingEnergyReduction.xiMK_mem_support_window I k t hξk
  have hul := MovingEnergyReduction.xiMK_mem_support_window I l t hξl
  have hcoord :
      (t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m -
        (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m =
      (k : ℝ) - (l : ℝ) := by
    field_simp [ne_of_gt hτ]
    ring
  have habs : |(k : ℝ) - (l : ℝ)| ≤ 5 / 2 := by
    rw [← hcoord]
    calc
      |(t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m -
          (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m| ≤
        |(t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m| +
          |(t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m| := abs_sub _ _
      _ ≤ 5 / 4 + 5 / 4 := add_le_add
        (abs_le.mpr ⟨by linarith [hul.1], by linarith [hul.2]⟩)
        (abs_le.mpr ⟨by linarith [huk.1], by linarith [huk.2]⟩)
      _ = 5 / 2 := by norm_num
  have habs' : |((k - l : ℤ) : ℝ)| ≤ 5 / 2 := by
    simpa only [Int.cast_sub] using habs
  by_contra hnot
  have hlarge : 3 ≤ |k - l| := by omega
  have hlargeReal : (3 : ℝ) ≤ |((k - l : ℤ) : ℝ)| := by
    have hcast : (3 : ℝ) ≤ ((|k - l| : ℤ) : ℝ) := by exact_mod_cast hlarge
    simpa only [Int.cast_abs] using hcast
  linarith

theorem MovingEnergyReduction.chiMK_horizontal_other_component {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) : (fun y => I.chiMK κ m k t y 0) = fun _ => 0 := by
  funext y
  simp [Ingredients.chiMK, uShear, hk]

theorem MovingEnergyReduction.chiMK_vertical_other_component {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) : (fun y => I.chiMK κ m k t y 1) = fun _ => 0 := by
  funext y
  simp [Ingredients.chiMK, uShear, hk]

theorem MovingEnergyReduction.chiMKGrad_horizontal {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 1)
    (hε : epsilon β I.Λ m ≠ 0) (x : Vec 2) :
    gradMatrix (I.chiMK κ m k t) x =
      (4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t *
        Real.sin (2 * Real.pi * x 0 / epsilon β I.Λ m)) •
          Matrix.single 0 1 (1 : ℝ) := by
  ext i j
  change spaceGrad (fun y => I.chiMK κ m k t y j) x i =
    (4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t *
      Real.sin (2 * Real.pi * x 0 / epsilon β I.Λ m)) * Matrix.single 0 1 1 i j
  by_cases hj : j = 1
  · subst j
    rw [chiMK_spaceGrad_one_all I κ k t x i hk hε]
    fin_cases i <;> simp [Matrix.single]
  · have hj0 : j = 0 := by fin_cases j <;> simp_all
    subst j
    rw [MovingEnergyReduction.chiMK_horizontal_other_component I κ k t hk]
    simp [AVenhance.spaceGrad, Matrix.single]

theorem MovingEnergyReduction.chiMKGrad_vertical {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 3)
    (hε : epsilon β I.Λ m ≠ 0) (x : Vec 2) :
    gradMatrix (I.chiMK κ m k t) x =
      (-(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) *
        Real.sin (2 * Real.pi * x 1 / epsilon β I.Λ m)) •
          Matrix.single 1 0 (1 : ℝ) := by
  ext i j
  change spaceGrad (fun y => I.chiMK κ m k t y j) x i =
    (-(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) *
      Real.sin (2 * Real.pi * x 1 / epsilon β I.Λ m)) * Matrix.single 1 0 1 i j
  by_cases hj : j = 0
  · subst j
    rw [chiMK_spaceGrad_three_all I κ k t x i hk hε]
    fin_cases i <;> simp [Matrix.single]
  · have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst j
    rw [MovingEnergyReduction.chiMK_vertical_other_component I κ k t hk]
    simp [AVenhance.spaceGrad, Matrix.single]

/-- If two distinct odd transition windows are simultaneously nonzero, their
indices differ by exactly two. -/
theorem xiMK_odd_overlap_distance {β : ℝ} (I : Ingredients β)
    {m : ℕ} {k l : ℤ} (hk : Odd k) (hl : Odd l) (t : ℝ)
    (hξk : I.xiMK m k t ≠ 0) (hξl : I.xiMK m l t ≠ 0)
    (hne : k ≠ l) : |k - l| = 2 := by
  have hle := MovingEnergyReduction.odd_mode_distance_le_two_of_xi_overlap I t hξk hξl
  have hne' : k - l ≠ 0 := by omega
  have hlow : 2 ≤ |k - l| := by
    rcases hk with ⟨a, rfl⟩
    rcases hl with ⟨b, rfl⟩
    have hab : a ≠ b := by
      intro hab
      apply hne
      simp [hab]
    have habs : 1 ≤ |a - b| := by
      by_cases hnonneg : 0 ≤ a - b
      · rw [abs_of_nonneg hnonneg]
        omega
      · rw [abs_of_neg (lt_of_not_ge hnonneg)]
        omega
    have hdiff : (2 * a + 1) - (2 * b + 1) = 2 * (a - b) := by ring
    rw [hdiff, abs_mul]
    norm_num
    omega
  omega

/-- Adjacent odd shear correctors have orthogonal gradient tensors, pointwise
in both spatial arguments. -/
theorem chiMK_grad_cross_eq_zero_of_odd_overlap {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ)
    {k l : ℤ} (hk : Odd k) (hl : Odd l) (hne : k ≠ l) (t : ℝ)
    (hξk : I.xiMK m k t ≠ 0) (hξl : I.xiMK m l t ≠ 0)
    (x y : Vec 2) :
    Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
      gradMatrix (I.chiMK κ m l t) y = 0 := by
  have hdist := xiMK_odd_overlap_distance I hk hl t hξk hξl hne
  have hmods : (k % 4 = 1 ∧ l % 4 = 3) ∨
      (k % 4 = 3 ∧ l % 4 = 1) := by
    have hcases : k - l = 2 ∨ k - l = -2 := by
      by_cases hnonneg : 0 ≤ k - l
      · rw [abs_of_nonneg hnonneg] at hdist
        omega
      · rw [abs_of_neg (lt_of_not_ge hnonneg)] at hdist
        omega
    rcases hk with ⟨a, rfl⟩
    rcases hl with ⟨b, hb⟩
    omega
  have hε : epsilon β I.Λ m ≠ 0 := by
    exact ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  rcases hmods with ⟨hk1, hl3⟩ | ⟨hk3, hl1⟩
  · rw [MovingEnergyReduction.chiMKGrad_horizontal I κ k t hk1 hε x,
      MovingEnergyReduction.chiMKGrad_vertical I κ l t hl3 hε y]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single]
  · rw [MovingEnergyReduction.chiMKGrad_vertical I κ k t hk3 hε x,
      MovingEnergyReduction.chiMKGrad_horizontal I κ l t hl1 hε y]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single]

/-- The moving-cutoff double sum of gradient Gram matrices has only its
diagonal terms. This is the exact reduction of the quadratic part of the
source's `E_m` formula; it uses support overlap before discarding cross terms. -/
theorem movingEnergy_gram_double_sum_reduces {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (t : ℝ)
    (S : Finset {k : ℤ // Odd k}) (x : Vec 2)
    (hS : ∀ k ∈ S, I.xiMK m k.1 t ≠ 0) :
    (∑ k ∈ S, ∑ l ∈ S,
      (I.xiMK m k.1 t * I.xiMK m l.1 t) •
        (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
          gradMatrix (I.chiMK κ m l.1 t) x)) =
      ∑ k ∈ S, I.xiMK m k.1 t ^ 2 •
        (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
          gradMatrix (I.chiMK κ m k.1 t) x) := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · simp [pow_two]
  · intro l hl hkl
    have hneval : k.1 ≠ l.1 := by
      intro heq
      apply hkl
      exact Subtype.ext heq.symm
    have hcross := chiMK_grad_cross_eq_zero_of_odd_overlap I κ k.2 l.2
      hneval
      t (hS k hk) (hS l hl) x x
    simp [hcross]
  · intro hnot
    exact (hnot hk).elim

/-- The complete double-sum energy keeps the full molecular baseline.  The
cutoff partition enters as `(∑ ξ_k)^2 = 1`; only the gradient correction is
reduced to the diagonal.  This is the correction to the printed `Σ ξ_k² I`
baseline used in the source. -/
theorem movingEnergy_double_sum_reduces {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (t : ℝ)
    (S : Finset {k : ℤ // Odd k}) (x : Vec 2)
    (hS : ∀ k ∈ S, I.xiMK m k.1 t ≠ 0)
    (hpartition : (∑ k ∈ S, I.xiMK m k.1 t) = 1) :
    (∑ k ∈ S, ∑ l ∈ S,
      (I.xiMK m k.1 t * I.xiMK m l.1 t) •
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m l.1 t) x)) =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, I.xiMK m k.1 t ^ 2 •
          (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m k.1 t) x) := by
  classical
  let ξ : {k : ℤ // Odd k} → ℝ := fun k => I.xiMK m k.1 t
  let G : {k : ℤ // Odd k} → {k : ℤ // Odd k} →
      Matrix (Fin 2) (Fin 2) ℝ := fun k l =>
        Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
          gradMatrix (I.chiMK κ m l.1 t) x
  have hcoeff : (∑ k ∈ S, ∑ l ∈ S, ξ k * ξ l) = 1 := by
    calc
      (∑ k ∈ S, ∑ l ∈ S, ξ k * ξ l) =
          (∑ k ∈ S, ξ k) * (∑ l ∈ S, ξ l) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
      _ = 1 := by simpa [ξ] using congrArg (fun z : ℝ => z * z) hpartition
  have hgram := movingEnergy_gram_double_sum_reduces I κ t S x hS
  have hsplit :
      (∑ k ∈ S, ∑ l ∈ S,
        (ξ k * ξ l) • (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + G k l)) =
        (∑ k ∈ S, ∑ l ∈ S, ξ k * ξ l) •
            (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
          ∑ k ∈ S, ∑ l ∈ S, (ξ k * ξ l) • G k l := by
    simp_rw [smul_add, Finset.sum_add_distrib]
    simp only [Finset.sum_smul]
  calc
    _ = (∑ k ∈ S, ∑ l ∈ S, ξ k * ξ l) •
          (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
        ∑ k ∈ S, ∑ l ∈ S, (ξ k * ξ l) • G k l := by
      simpa [ξ, G] using hsplit
    _ = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, ξ k ^ 2 • G k k := by
      rw [hcoeff]
      have hgram' :
          (∑ k ∈ S, ∑ l ∈ S, (ξ k * ξ l) • G k l) =
            ∑ k ∈ S, ξ k ^ 2 • G k k := by
        simpa [ξ, G, pow_two] using hgram
      rw [hgram']
      simp

/-- The finite support selected by the moving cutoffs carries the full
partition of unity. This is the finite-sum form needed to apply the double-sum
reduction at a fixed time. -/
theorem xiMK_odd_partition_finset {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    let S := (xiMK_odd_support_finite I hm t).toFinset
    ∑ k ∈ S, I.xiMK m k.1 t = 1 := by
  let S := (xiMK_odd_support_finite I hm t).toFinset
  have hzero (k : {k : ℤ // Odd k}) (hk : k ∉ S) :
      I.xiMK m k.1 t = 0 := by
    by_contra hne
    apply hk
    simpa [S] using hne
  change (∑ k ∈ S, I.xiMK m k.1 t) = 1
  rw [← tsum_eq_sum
    (L := SummationFilter.unconditional {k : ℤ // Odd k}) (s := S) hzero]
  exact xiMK_odd_partition I hm t

/-- The source's full odd-mode double sum reduces on the actual finite cutoff
support. This specializes the overlap cancellation and molecular partition
identity to the `E_m` sum at a fixed time. -/
theorem movingEnergy_odd_cutoff_double_sum_reduces {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ)
    (x : Vec 2) :
    let S := (xiMK_odd_support_finite I hm t).toFinset
    (∑ k ∈ S, ∑ l ∈ S,
      (I.xiMK m k.1 t * I.xiMK m l.1 t) •
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m l.1 t) x)) =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, I.xiMK m k.1 t ^ 2 •
          (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m k.1 t) x) := by
  let S := (xiMK_odd_support_finite I hm t).toFinset
  have hS : ∀ k ∈ S, I.xiMK m k.1 t ≠ 0 := by
    intro k hk
    have hk' : k ∈ {l : {k : ℤ // Odd k} | I.xiMK m l.1 t ≠ 0} := by
      simpa [S] using hk
    exact Set.mem_ofPred_eq.mp hk'
  have hpartition : (∑ k ∈ S, I.xiMK m k.1 t) = 1 := by
    simpa [S] using xiMK_odd_partition_finset I hm t
  change (∑ k ∈ S, ∑ l ∈ S,
      (I.xiMK m k.1 t * I.xiMK m l.1 t) •
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m l.1 t) x)) =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, I.xiMK m k.1 t ^ 2 •
          (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
            gradMatrix (I.chiMK κ m k.1 t) x)
  exact movingEnergy_double_sum_reduces I κ t S x hS hpartition

end AVenhance.Infra.Section3

end
