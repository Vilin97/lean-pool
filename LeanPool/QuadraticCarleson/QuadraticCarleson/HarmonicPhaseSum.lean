/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.BohrIntersection

/-!
# Almost constant phases in a harmonic sum

This file proves the arithmetic lower bound used after the construction of
`E_N` in the negative endpoint argument. All sums are finite, and `phase`
has the paper's exact normalization `exp(2π i s)`.
-/

open Set

namespace QuadraticCarleson

@[simp]
theorem phase_int (z : ℤ) : phase (z : ℝ) = 1 := by
  rw [phase]
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  congr 1
  push_cast
  ring

@[simp]
theorem phase_add_int (x : ℝ) (z : ℤ) : phase (x + z) = phase x := by
  rw [phase_add, phase_int, mul_one]

/-- The elementary phase error in the paper's `2π` normalization. -/
theorem norm_phase_sub_one_le (x : ℝ) : ‖phase x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * x)
  have heq : phase x = Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    rw [phase]
    congr 1
    ring
  rw [heq]
  exact h.trans_eq (by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos])

theorem norm_phase_sub_one_le_abs_sub_int (x : ℝ) (z : ℤ) :
    ‖phase x - 1‖ ≤ 2 * Real.pi * |x - z| := by
  have h : phase x = phase (x - z) := by
    simpa using phase_add_int (x - z) z
  rw [h]
  exact norm_phase_sub_one_le _

/-- Integer modulation and a Bohr condition make each phase close to one. -/
theorem norm_phase_integer_modulation_sub_one_le {ell : ℤ} {τ δ : ℝ}
    (hδ : torusNorm ((ell : ℝ) * τ) ≤ δ) (k j : ℕ) :
    ‖phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) - 1‖ ≤ 4 * Real.pi * j * δ := by
  obtain ⟨a, ha⟩ := exists_int_abs_sub_le_of_torusNorm_le hδ
  let z : ℤ := 2 * ell * j * k + 2 * j * a
  have heq : 2 * (ell : ℝ) * j * ((k : ℝ) + τ) - z =
      (2 * (j : ℝ)) * ((ell : ℝ) * τ - a) := by
    dsimp [z]
    push_cast
    ring
  calc
    ‖phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) - 1‖ ≤
        2 * Real.pi * |2 * (ell : ℝ) * j * ((k : ℝ) + τ) - z| :=
      norm_phase_sub_one_le_abs_sub_int _ z
    _ = 2 * Real.pi * (2 * (j : ℝ)) * |(ell : ℝ) * τ - a| := by
      rw [heq, abs_mul, abs_of_nonneg (by positivity)]
      ring
    _ ≤ 2 * Real.pi * (2 * (j : ℝ)) * δ := by gcongr
    _ = 4 * Real.pi * j * δ := by ring

/-- The positive reciprocal sum obtained after shifting `j = k+i+1`. -/
noncomputable def reciprocalMass (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1 - τ)

private theorem shifted_denominator_pos {τ : ℝ} (hτ : τ < 1) (i : ℕ) :
    0 < (i : ℝ) + 1 - τ := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem reciprocalMass_nonneg (n : ℕ) {τ : ℝ} (hτ : τ < 1) :
    0 ≤ reciprocalMass n τ := by
  apply Finset.sum_nonneg
  intro i hi
  exact le_of_lt (one_div_pos.mpr (shifted_denominator_pos hτ i))

/-- Comparison with the ordinary harmonic number, below. -/
theorem harmonic_le_reciprocalMass (n : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) :
    (harmonic n : ℝ) ≤ reciprocalMass n τ := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one, reciprocalMass, one_div]
  apply Finset.sum_le_sum
  intro i hi
  exact inv_anti₀ (shifted_denominator_pos hτ i) (by linarith)

/-- Comparison with the ordinary harmonic number, above. -/
theorem reciprocalMass_le_two_mul_harmonic (n : ℕ) {τ : ℝ} (hτ : τ ≤ 1 / 2) :
    reciprocalMass n τ ≤ 2 * (harmonic n : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one, reciprocalMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hd : 0 < (i : ℝ) + 1 - τ := shifted_denominator_pos (by linarith) i
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd (by positivity)).mpr
  nlinarith

/-- A complex weighted version of the shifted harmonic sum. -/
noncomputable def weightedPhaseSum (n : ℕ) (τ : ℝ) (z : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range n, z i / (((i : ℝ) + 1 - τ : ℝ) : ℂ)

/-- The exact phase-error estimate relative to the positive reciprocal mass. -/
theorem weightedPhaseSum_error_le (n : ℕ) {τ ε : ℝ} (z : ℕ → ℂ)
    (hτ : τ < 1) (hz : ∀ i ∈ Finset.range n, ‖z i - 1‖ ≤ ε) :
    ‖weightedPhaseSum n τ z - (reciprocalMass n τ : ℂ)‖ ≤ ε * reciprocalMass n τ := by
  have heq : weightedPhaseSum n τ z - (reciprocalMass n τ : ℂ) =
      ∑ i ∈ Finset.range n, (z i - 1) / (((i : ℝ) + 1 - τ : ℝ) : ℂ) := by
    rw [weightedPhaseSum, reciprocalMass, Complex.ofReal_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [heq]
  calc
    ‖∑ i ∈ Finset.range n, (z i - 1) / (((i : ℝ) + 1 - τ : ℝ) : ℂ)‖ ≤
        ∑ i ∈ Finset.range n, ‖(z i - 1) / (((i : ℝ) + 1 - τ : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, ε / ((i : ℝ) + 1 - τ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hd := shifted_denominator_pos hτ i
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      exact div_le_div_of_nonneg_right (hz i hi) hd.le
    _ = ε * reciprocalMass n τ := by
      rw [reciprocalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem weightedPhaseSum_norm_ge (n : ℕ) {τ ε : ℝ} (z : ℕ → ℂ)
    (hτ : τ < 1) (hz : ∀ i ∈ Finset.range n, ‖z i - 1‖ ≤ ε) :
    (1 - ε) * reciprocalMass n τ ≤ ‖weightedPhaseSum n τ z‖ := by
  have h := norm_sub_norm_le (reciprocalMass n τ : ℂ) (weightedPhaseSum n τ z)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (reciprocalMass_nonneg n hτ)] at h
  have he := weightedPhaseSum_error_le n z hτ hz
  rw [norm_sub_rev] at he
  nlinarith

private theorem paper_reciprocal_length_bounds {N k : ℕ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10) :
    k ≤ N ∧ (N : ℝ) / 4 ≤ ((N - k : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((N - k : ℕ) : ℝ) := by
  have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hkn : k ≤ N := by
    have : (k : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hd : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub hkn
  exact ⟨hkn, by nlinarith, by nlinarith⟩

/-- The shifted reciprocal sum has logarithmic size throughout the paper's
index interval; the explicit large-`N` threshold is `100`. -/
theorem reciprocalMass_paper_lower {N k : ℕ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10)
    (hτ0 : 0 ≤ τ) (hτ : τ < 1) :
    Real.log N / 2 ≤ reciprocalMass (N - k) τ := by
  obtain ⟨hkn, hnquarter, hn4⟩ := paper_reciprocal_length_bounds hN hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn0 : (0 : ℝ) ≤ (N - k : ℕ) := Nat.cast_nonneg _
  have hsq : (N : ℝ) ≤ (((N - k : ℕ) : ℝ) + 1) ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn4)]
  have hlog := Real.log_le_log hN0 hsq
  rw [Real.log_pow] at hlog
  have hh := log_add_one_le_harmonic (N - k)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hh hlog
  have hm := harmonic_le_reciprocalMass (N - k) hτ0 hτ
  linarith

/-- The matching logarithmic upper bound controls the total phase error. -/
theorem reciprocalMass_paper_upper {N k : ℕ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10) (hτ : τ ≤ 1 / 2) :
    reciprocalMass (N - k) τ ≤ 2 * (1 + Real.log N) := by
  obtain ⟨hkn, hnquarter, hn4⟩ := paper_reciprocal_length_bounds hN hk
  have hnpos : (0 : ℝ) < (N - k : ℕ) := by linarith
  have hnN : ((N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N k
  have hlog := Real.log_le_log hnpos hnN
  have hh := harmonic_le_one_add_log (N - k)
  have hm := reciprocalMass_le_two_mul_harmonic (N - k) hτ
  linarith

/-- The explicit phase error furnished by the paper's Bohr radius. -/
noncomputable def paperPhaseError : ℝ := 4 * Real.pi / (2 : ℝ) ^ 100

theorem paperPhaseError_nonneg : 0 ≤ paperPhaseError := by
  unfold paperPhaseError
  positivity

theorem paperPhaseError_le_half : paperPhaseError ≤ 1 / 2 := by
  unfold paperPhaseError
  apply (div_le_iff₀ (by positivity)).mpr
  have hp := Real.pi_lt_four
  have hpow : (32 : ℝ) ≤ 2 ^ 100 := by norm_num
  nlinarith

theorem norm_paper_phase_sub_one_le {N k j : ℕ} {ell : ℤ} {τ : ℝ}
    (hN : 0 < N) (hj : j ≤ N)
    (hbohr : torusNorm ((ell : ℝ) * τ) ≤ 1 / ((2 : ℝ) ^ 100 * N)) :
    ‖phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) - 1‖ ≤ paperPhaseError := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ‖phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) - 1‖ ≤
        4 * Real.pi * j * (1 / ((2 : ℝ) ^ 100 * N)) :=
      norm_phase_integer_modulation_sub_one_le hbohr k j
    _ ≤ 4 * Real.pi * N * (1 / ((2 : ℝ) ^ 100 * N)) := by
      gcongr
    _ = paperPhaseError := by
      unfold paperPhaseError
      field_simp

private theorem sum_Icc_eq_sum_range_shift {N k : ℕ} (hkn : k ≤ N) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.Icc (k + 1) N, f j) =
      ∑ i ∈ Finset.range (N - k), f (k + i + 1) := by
  have h := Finset.sum_Ico_add' f 0 (N - k) (k + 1)
  have htop : N - k + (k + 1) = N + 1 := by omega
  rw [zero_add, htop, Finset.Ico_add_one_right_eq_Icc, ← Finset.range_eq_Ico] at h
  calc
    (∑ j ∈ Finset.Icc (k + 1) N, f j) =
        ∑ i ∈ Finset.range (N - k), f (i + (k + 1)) := h.symm
    _ = ∑ i ∈ Finset.range (N - k), f (k + i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega

private theorem sum_paper_denominator_eq {N k : ℕ} (hkn : k ≤ N)
    (τ : ℝ) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.Icc (k + 1) N, f j / (((k : ℝ) + τ - j : ℝ) : ℂ)) =
      -weightedPhaseSum (N - k) τ (fun i => f (k + i + 1)) := by
  rw [sum_Icc_eq_sum_range_shift hkn, weightedPhaseSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : (((k : ℝ) + τ - (k + i + 1 : ℕ) : ℝ) : ℂ) =
      -(((i : ℝ) + 1 - τ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hd, div_neg]

private theorem weightedPhaseSum_one (n : ℕ) (τ : ℝ) :
    weightedPhaseSum n τ (fun _ => 1) = (reciprocalMass n τ : ℂ) := by
  rw [weightedPhaseSum, reciprocalMass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  rfl

/-- The exact normalized finite phase sum displayed in the paper. -/
noncomputable def harmonicPhaseSum (N k : ℕ) (ell : ℤ) (τ : ℝ) : ℂ :=
  (1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k + 1) N,
    phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) / (((k : ℝ) + τ - j : ℝ) : ℂ)

/-- The same normalized reciprocal sum with every phase replaced by one. -/
noncomputable def harmonicReciprocalSum (N k : ℕ) (τ : ℝ) : ℂ :=
  (1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k + 1) N,
    (1 : ℂ) / (((k : ℝ) + τ - j : ℝ) : ℂ)

private theorem harmonicPhaseSum_eq_shifted {N k : ℕ} (hkn : k ≤ N) (ell : ℤ) (τ : ℝ) :
    harmonicPhaseSum N k ell τ = -((1 / (N : ℂ)) * weightedPhaseSum (N - k) τ
      (fun i => phase (2 * (ell : ℝ) * (k + i + 1 : ℕ) * ((k : ℝ) + τ)))) := by
  rw [harmonicPhaseSum, sum_paper_denominator_eq hkn, mul_neg]

theorem harmonicReciprocalSum_eq {N k : ℕ} (hkn : k ≤ N) (τ : ℝ) :
    harmonicReciprocalSum N k τ = -((reciprocalMass (N - k) τ / N : ℝ) : ℂ) := by
  rw [harmonicReciprocalSum, sum_paper_denominator_eq hkn, weightedPhaseSum_one]
  push_cast
  ring

theorem norm_harmonicReciprocalSum {N k : ℕ} {τ : ℝ} (hkn : k ≤ N) (hτ : τ < 1) :
    ‖harmonicReciprocalSum N k τ‖ = reciprocalMass (N - k) τ / N := by
  rw [harmonicReciprocalSum_eq hkn, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (reciprocalMass_nonneg _ hτ) (Nat.cast_nonneg N))]

/-- The normalized reciprocal sum alone is at least `(log N)/(2N)`. -/
theorem harmonicReciprocalSum_norm_ge {N k : ℕ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10)
    (hτ0 : 0 ≤ τ) (hτ : τ < 1) :
    Real.log N / (2 * N) ≤ ‖harmonicReciprocalSum N k τ‖ := by
  have hkn := (paper_reciprocal_length_bounds hN hk).1
  rw [norm_harmonicReciprocalSum hkn hτ]
  calc
    Real.log N / (2 * N) = (Real.log N / 2) / N := by ring
    _ ≤ reciprocalMass (N - k) τ / N :=
      div_le_div_of_nonneg_right (reciprocalMass_paper_lower hN hk hτ0 hτ) (Nat.cast_nonneg N)

/-- The normalized phase error, before invoking the logarithmic upper bound. -/
theorem harmonicPhaseSum_error_relative {N k : ℕ} {ell : ℤ} {τ : ℝ}
    (hN : 0 < N) (hkn : k ≤ N) (hτ : τ < 1)
    (hbohr : torusNorm ((ell : ℝ) * τ) ≤ 1 / ((2 : ℝ) ^ 100 * N)) :
    ‖harmonicPhaseSum N k ell τ - harmonicReciprocalSum N k τ‖ ≤
      paperPhaseError * reciprocalMass (N - k) τ / N := by
  let z : ℕ → ℂ := fun i =>
    phase (2 * (ell : ℝ) * (k + i + 1 : ℕ) * ((k : ℝ) + τ))
  have hz : ∀ i ∈ Finset.range (N - k), ‖z i - 1‖ ≤ paperPhaseError := by
    intro i hi
    exact norm_paper_phase_sub_one_le hN (by have := Finset.mem_range.mp hi; omega) hbohr
  have he := weightedPhaseSum_error_le (N - k) z hτ hz
  have hid : harmonicPhaseSum N k ell τ - harmonicReciprocalSum N k τ =
      -(1 / (N : ℂ)) * (weightedPhaseSum (N - k) τ z - (reciprocalMass (N - k) τ : ℂ)) := by
    rw [harmonicPhaseSum_eq_shifted hkn, harmonicReciprocalSum_eq hkn]
    dsimp [z]
    push_cast
    ring
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hid, norm_mul, norm_neg, norm_div, norm_one, hn]
  calc
    1 / (N : ℝ) * ‖weightedPhaseSum (N - k) τ z - (reciprocalMass (N - k) τ : ℂ)‖ ≤
        1 / (N : ℝ) * (paperPhaseError * reciprocalMass (N - k) τ) := by
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = paperPhaseError * reciprocalMass (N - k) τ / N := by ring

private theorem one_le_log_of_paper_large {N : ℕ} (hN : 100 ≤ N) :
    1 ≤ Real.log N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
  have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hN')
  simpa only [Real.log_exp] using h

/-- An explicit version of the paper's `O(2⁻⁹⁹ log(N)/N)` phase error.
The displayed coefficient is `8π · 2⁻⁹⁹`. -/
theorem harmonicPhaseSum_error_le {N k : ℕ} {ell : ℤ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10) (hτ : τ ≤ 1 / 2)
    (hbohr : torusNorm ((ell : ℝ) * τ) ≤ 1 / ((2 : ℝ) ^ 100 * N)) :
    ‖harmonicPhaseSum N k ell τ - harmonicReciprocalSum N k τ‖ ≤
      (16 * Real.pi / (2 : ℝ) ^ 100) * (Real.log N / N) := by
  have hkn := (paper_reciprocal_length_bounds hN hk).1
  have hN0 : 0 < N := by omega
  have hm := reciprocalMass_paper_upper hN hk hτ
  have hlog := one_le_log_of_paper_large hN
  have hm' : reciprocalMass (N - k) τ ≤ 4 * Real.log N := by linarith
  calc
    ‖harmonicPhaseSum N k ell τ - harmonicReciprocalSum N k τ‖ ≤
        paperPhaseError * reciprocalMass (N - k) τ / N :=
      harmonicPhaseSum_error_relative hN0 hkn (by linarith) hbohr
    _ ≤ paperPhaseError * (4 * Real.log N) / N := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm' paperPhaseError_nonneg) (Nat.cast_nonneg N)
    _ = (16 * Real.pi / (2 : ℝ) ^ 100) * (Real.log N / N) := by
      unfold paperPhaseError
      ring

/-- The almost constant phases retain a fixed fraction of the harmonic
lower bound. This applies throughout `3N/5 ≤ k ≤ 7N/10`; only the upper
endpoint is needed by the estimate itself. -/
theorem harmonicPhaseSum_norm_ge {N k : ℕ} {ell : ℤ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hbohr : torusNorm ((ell : ℝ) * τ) ≤ 1 / ((2 : ℝ) ^ 100 * N)) :
    Real.log N / (4 * N) ≤ ‖harmonicPhaseSum N k ell τ‖ := by
  have hkn := (paper_reciprocal_length_bounds hN hk).1
  have hτ' : τ < 1 := by linarith [hτ.2]
  have hτ0 : 0 ≤ τ := by linarith [hτ.1]
  have hm0 := reciprocalMass_nonneg (N - k) hτ'
  have hmain := harmonicReciprocalSum_norm_ge hN hk hτ0 hτ'
  rw [norm_harmonicReciprocalSum hkn hτ'] at hmain
  have he := harmonicPhaseSum_error_relative (by omega : 0 < N) hkn hτ' hbohr
  have ht := norm_sub_norm_le (harmonicReciprocalSum N k τ) (harmonicPhaseSum N k ell τ)
  rw [norm_harmonicReciprocalSum hkn hτ'] at ht
  rw [norm_sub_rev] at he
  have hhalf : paperPhaseError * reciprocalMass (N - k) τ / N ≤
      (reciprocalMass (N - k) τ / N) / 2 := by
    have h := mul_le_mul_of_nonneg_right paperPhaseError_le_half
      (div_nonneg hm0 (Nat.cast_nonneg N))
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    Real.log N / (4 * N) = (Real.log N / (2 * N)) / 2 := by ring
    _ ≤ (reciprocalMass (N - k) τ / N) / 2 := by linarith
    _ ≤ ‖harmonicPhaseSum N k ell τ‖ := by linarith

/-- Direct specialization to membership in the localized Bohr set, covering
in particular every dyadic modulation `ell = 2^r`. -/
theorem harmonicPhaseSum_norm_ge_of_mem_bohrSet {N k ell : ℕ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : (k : ℝ) ≤ 7 * (N : ℝ) / 10)
    (hτ : τ ∈ bohrSet ell (1 / ((2 : ℝ) ^ 100 * N))) :
    Real.log N / (4 * N) ≤ ‖harmonicPhaseSum N k (ell : ℤ) τ‖ := by
  exact harmonicPhaseSum_norm_ge hN hk hτ.1 (by simpa using hτ.2)

/-- Including the possible endpoint `j=k` changes the normalized sum by at
most `4/N`, accounting for the paper's first `O(1/N)` term. -/
theorem harmonicPhaseSum_endpoint_error_le {N k : ℕ} (ell : ℤ) {τ : ℝ}
    (hkn : k ≤ N) (hτ : 1 / 4 ≤ τ) :
    ‖((1 / (N : ℂ)) * ∑ j ∈ Finset.Icc k N,
        phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) / (((k : ℝ) + τ - j : ℝ) : ℂ)) -
      harmonicPhaseSum N k ell τ‖ ≤ 4 / (N : ℝ) := by
  let f : ℕ → ℂ := fun j =>
    phase (2 * (ell : ℝ) * j * ((k : ℝ) + τ)) / (((k : ℝ) + τ - j : ℝ) : ℂ)
  have hsum := Finset.sum_eq_sum_Ico_succ_bot (show k < N + 1 by omega) f
  simp only [Finset.Ico_add_one_right_eq_Icc] at hsum
  have hdiff : ((1 / (N : ℂ)) * ∑ j ∈ Finset.Icc k N, f j) -
      harmonicPhaseSum N k ell τ = (1 / (N : ℂ)) * f k := by
    rw [harmonicPhaseSum]
    change ((1 / (N : ℂ)) * ∑ j ∈ Finset.Icc k N, f j) -
      (1 / (N : ℂ)) * (∑ j ∈ Finset.Icc (k + 1) N, f j) = _
    rw [hsum]
    ring
  have hτpos : 0 < τ := by linarith
  have hτinv : 1 / τ ≤ 4 := (div_le_iff₀ hτpos).mpr (by linarith)
  change ‖((1 / (N : ℂ)) * ∑ j ∈ Finset.Icc k N, f j) -
    harmonicPhaseSum N k ell τ‖ ≤ _
  rw [hdiff, norm_mul]
  have hfactor : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by simp
  have hfk : ‖f k‖ = 1 / τ := by
    simp [f, norm_phase, abs_of_pos hτpos]
  rw [hfactor, hfk]
  calc
    1 / (N : ℝ) * (1 / τ) ≤ 1 / (N : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hτinv (by positivity)
    _ = 4 / (N : ℝ) := by ring

end QuadraticCarleson
