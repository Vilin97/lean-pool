/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Appendix B.2 transport estimates

This module records the numerical estimates used in the transport induction.
The corrected coefficient is kept in its source-correct form; its equal-radius
specialization is the one consumed by the paper's later application.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open MeasureTheory

/-- For equal forcing and transport radii, the corrected coefficient is
at most `1/8` throughout the time interval in (10578). -/
theorem transportE18_equalRadius_le_eighth {n : ℕ} {d C_f R_f t : ℝ}
    (hd : 1 ≤ d) (hCf : 0 < C_f) (hRf : 0 < R_f)
    (ht : 0 ≤ t) (hT : t ≤ 1 / (4 * d * C_f * R_f)) :
    (n * (R_f + 4 * t * d * C_f * R_f ^ 2) /
      (16 * (n + 1) * R_f)) ≤ 1 / 8 := by
  have hden : 0 < 4 * d * C_f * R_f := by positivity
  have htime : 4 * t * d * C_f * R_f ≤ 1 := by
    have := (le_div_iff₀ hden).mp hT
    nlinarith only [this]
  have hratio :
      (R_f + 4 * t * d * C_f * R_f ^ 2) / R_f ≤ 2 := by
    rw [div_le_iff₀ hRf]
    nlinarith only [mul_le_mul_of_nonneg_right htime hRf.le]
  have hn : (n : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one₀ (by positivity : 0 < (n + 1 : ℝ))]
    norm_num
  have hnnonneg : 0 ≤ (n : ℝ) / (n + 1) := by positivity
  have hrnonneg : 0 ≤
      (R_f + 4 * t * d * C_f * R_f ^ 2) / R_f := by positivity
  calc
    _ = ((n : ℝ) / (n + 1)) *
        ((R_f + 4 * t * d * C_f * R_f ^ 2) / R_f) / 16 := by
          field_simp
    _ ≤ 1 * 2 / 16 := by
      gcongr
    _ = 1 / 8 := by norm_num

/-- The absorption step in Lemma 10577 after the correction, when
`R_g = R_f` and hence the coefficient is bounded by `1/8`. -/
theorem transportE18_equalRadius_absorption {d C_g S : ℝ}
    (hd : 1 ≤ d) (hCg : 0 ≤ C_g)
    (hS : S ≤ C_g + S / 8 + 6 * d * C_g) :
    S ≤ 8 * d * C_g := by
  have hlin : (7 / 8 : ℝ) * S ≤ (1 + 6 * d) * C_g := by linarith only [hS]
  have hfactor : (8 / 7 : ℝ) * (1 + 6 * d) ≤ 8 * d := by linarith only [hd]
  calc
    S ≤ (8 / 7 : ℝ) * ((7 / 8 : ℝ) * S) := le_of_eq (by ring)
    _ ≤ (8 / 7 : ℝ) * ((1 + 6 * d) * C_g) :=
      mul_le_mul_of_nonneg_left hlin (by norm_num)
    _ ≤ (8 * d) * C_g := by
      calc
        (8 / 7 : ℝ) * ((1 + 6 * d) * C_g) =
            ((8 / 7 : ℝ) * (1 + 6 * d)) * C_g := by ring
        _ ≤ (8 * d) * C_g := mul_le_mul_of_nonneg_right hfactor hCg

/-- The radius integral estimate (10650), with the affine radius written
explicitly. The proof uses `s ≤ t` and integrates the exact power primitive. -/
theorem transportRadiusIntegral_bound {j : ℕ} {d C_f R_f R_g t : ℝ}
    (hd : 0 < d) (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hRg : 0 ≤ R_g) (ht : 0 ≤ t) :
    (∫ s in 0..t, s * (R_g + (4 * d * C_f * R_f ^ 2) * s) ^ j) ≤
      t * (R_g + (4 * d * C_f * R_f ^ 2) * t) ^ (j + 1) /
        ((4 * d * C_f * R_f ^ 2) * (j + 1 : ℝ)) := by
  let A : ℝ := 4 * d * C_f * R_f ^ 2
  have hA : 0 < A := by positivity
  have hAne : A ≠ 0 := ne_of_gt hA
  have hprimitive :
      (∫ s in 0..t, (R_g + A * s) ^ j) =
        ((R_g + A * t) ^ (j + 1) - R_g ^ (j + 1)) /
          (A * (j + 1 : ℝ)) := by
    rw [intervalIntegral.integral_comp_add_mul (f := fun x : ℝ => x ^ j) hAne R_g]
    rw [integral_pow]
    simp only [smul_eq_mul]
    field_simp [hAne]
    ring
  have hmono :
      (∫ s in 0..t, s * (R_g + A * s) ^ j) ≤
        ∫ s in 0..t, t * (R_g + A * s) ^ j := by
    have hfcont : Continuous (fun s : ℝ => s * (R_g + A * s) ^ j) := by
      fun_prop
    have hgcont : Continuous (fun s : ℝ => t * (R_g + A * s) ^ j) := by
      fun_prop
    apply intervalIntegral.integral_mono_on (a := 0) (b := t) (μ := volume) ht
      (hfcont.intervalIntegrable 0 t) (hgcont.intervalIntegrable 0 t)
    intro s hs
    have hbase : 0 ≤ R_g + A * s := by
      exact add_nonneg hRg (mul_nonneg hA.le hs.1)
    have hp : 0 ≤ (R_g + A * s) ^ j := by positivity
    exact mul_le_mul_of_nonneg_right hs.2 hp
  have hpow_nonneg : 0 ≤ R_g ^ (j + 1) := by positivity
  have hden : 0 < A * (j + 1 : ℝ) := by positivity
  calc
    _ ≤ t * ∫ s in 0..t, (R_g + A * s) ^ j := by
      rw [intervalIntegral.integral_const_mul] at hmono
      exact hmono
    _ = t * (((R_g + A * t) ^ (j + 1) - R_g ^ (j + 1)) /
          (A * (j + 1 : ℝ))) := by rw [hprimitive]
    _ ≤ t * ((R_g + A * t) ^ (j + 1) /
          (A * (j + 1 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ ht
      exact div_le_div_of_nonneg_right (by linarith) hden.le
    _ = t * (R_g + A * t) ^ (j + 1) /
          (A * (j + 1 : ℝ)) := by ring

theorem Transport.reciprocalSquareShift_le (c m : ℕ) (hc : 2 ≤ c) :
    (∑ k ∈ Finset.range m, 1 / ((k + c : ℝ) ^ 2)) ≤ 1 / (c - 1 : ℝ) := by
  let f : ℕ → ℝ := fun k => 1 / ((k : ℝ) + (c : ℝ) - 1)
  have hterm (k : ℕ) :
      1 / ((k + c : ℝ) ^ 2) ≤ f k - f (k + 1) := by
    have hcR : 2 ≤ (c : ℝ) := by exact_mod_cast hc
    have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    let x : ℝ := (k : ℝ) + (c : ℝ)
    have hx : 2 ≤ x := by dsimp [x]; linarith
    have hxminus : 0 < x - 1 := by linarith
    have hprodpos : 0 < (x - 1) * x := mul_pos hxminus (by linarith)
    have hprodle : (x - 1) * x ≤ x ^ 2 := by nlinarith [hx]
    have hxcast : (k + c : ℝ) = x := rfl
    calc
      1 / ((k + c : ℝ) ^ 2) = 1 / x ^ 2 := by rw [hxcast]
      _ ≤ 1 / ((x - 1) * x) := one_div_le_one_div_of_le hprodpos hprodle
      _ = f k - f (k + 1) := by
        have hfk : f k = 1 / (x - 1) := by dsimp [f, x]
        have hfk1 : f (k + 1) = 1 / x := by
          dsimp [f, x]
          push_cast
          congr 1
          ring
        rw [hfk, hfk1]
        field_simp
        ring_nf
  calc
    _ ≤ ∑ k ∈ Finset.range m, (f k - f (k + 1)) :=
      Finset.sum_le_sum fun k hk => hterm k
    _ = f 0 - f m := by rw [Finset.sum_range_sub']
    _ ≤ 1 / (c - 1 : ℝ) := by
      dsimp [f]
      have hcR : 1 < (c : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hc)
      have hdenpos : 0 < (m : ℝ) + (c : ℝ) - 1 := by
        have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hmnonneg : 0 ≤ 1 / ((m : ℝ) + (c : ℝ) - 1) :=
        div_nonneg (by norm_num) hdenpos.le
      simpa [Nat.cast_zero] using
        (sub_le_self (1 / ((c : ℝ) - 1)) hmnonneg)

private theorem transportE22_shifted_sum_le_three_halves_term1 :
  ∀ (n : ℕ),
    (81 : ℕ) ≤ n →
      let rangeN : Finset ℕ := Finset.range (n - (1 : ℕ));
      let sqA : ℕ → ℝ := fun (k : ℕ) => (1 : ℝ) / (↑(n - k + (1 : ℕ)) : ℝ) ^ (2 : ℕ);
      let sqB : ℕ → ℝ := fun (k : ℕ) => (1 : ℝ) / ((↑k : ℝ) + (2 : ℝ)) ^ (2 : ℕ);
      let cross : ℕ → ℝ := fun (k : ℕ) => (1 : ℝ) / ((↑(n - k + (1 : ℕ)) : ℝ) * ((↑k : ℝ) + (2 :
          ℝ)));
      ∀ k ∈ rangeN,
        ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) / ((↑(n - k + (1 : ℕ)) : ℝ) ^ (2 : ℕ) * ((↑k : ℝ) + (2 :
            ℝ)) ^ (2 : ℕ)) ≤
          sqA k + sqB k + (2 : ℝ) * cross k
    := by
  intro n hn81 rangeN sqA sqB cross k hk
  have hk' : k < n - 1 := Finset.mem_range.mp hk
  let a : ℝ := ((n - k + 1 : ℕ) : ℝ)
  let b : ℝ := (k + 2 : ℝ)
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hN : (n + 1 : ℝ) ≤ a + b := by
    have hnat : n + 1 ≤ n - k + 1 + (k + 2) := by omega
    dsimp [a, b]
    exact_mod_cast hnat
  have hfrac : (n + 1 : ℝ) / (a * b) ≤ 1 / a + 1 / b := by
    have hrewrite : (a + b) / (a * b) = 1 / a + 1 / b := by
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring
    rw [← hrewrite]
    exact div_le_div_of_nonneg_right hN (mul_pos ha hb).le
  have hleft : 0 ≤ (n + 1 : ℝ) / (a * b) := by positivity
  have hright : 0 ≤ 1 / a + 1 / b := by positivity
  have hsq := (sq_le_sq₀ hleft hright).2 hfrac
  calc
    _ = ((n + 1 : ℝ) / (a * b)) ^ 2 := by
      dsimp [a, b]
      field_simp [ne_of_gt ha, ne_of_gt hb]
    _ ≤ (1 / a + 1 / b) ^ 2 := hsq
    _ = sqA k + sqB k + 2 * cross k := by
      dsimp [sqA, sqB, cross, a, b]
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring_nf

/-- The corrected shifted reciprocal-square sum used at (10660) is at most
`3/2`. The unshifted `(k+1)^{-2}` version printed at (10663) is false. -/
theorem transportE22_shifted_sum_le_three_halves (n : ℕ) :
    (∑ k ∈ Finset.range (n - 1 : ℕ),
      (n + 1 : ℝ) ^ 2 /
        (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) ≤ 3 / 2 := by
  by_cases hn : n < 81
  · have hnle : n ≤ 80 := by omega
    interval_cases n <;> norm_num [Finset.sum_range_succ]
  · have hn81 : 81 ≤ n := by omega
    let rangeN := Finset.range (n - 1)
    let sqA (k : ℕ) : ℝ := 1 / ((n - k + 1 : ℕ) : ℝ) ^ 2
    let sqB (k : ℕ) : ℝ := 1 / (k + 2 : ℝ) ^ 2
    let recA (k : ℕ) : ℝ := 1 / ((n - k + 1 : ℕ) : ℝ)
    let recB (k : ℕ) : ℝ := 1 / (k + 2 : ℝ)
    let cross (k : ℕ) : ℝ :=
      1 / (((n - k + 1 : ℕ) : ℝ) * (k + 2 : ℝ))
    have hAeq : (∑ k ∈ rangeN, sqA k) =
        ∑ k ∈ rangeN, 1 / (k + 3 : ℝ) ^ 2 := by
      unfold rangeN sqA
      apply Finset.sum_bij (i := fun k _ => n - 2 - k)
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.mem_range] at hk₁ hk₂
        omega
      · intro b hb
        simp only [Finset.mem_range] at hb
        refine ⟨n - 2 - b, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        have hidx : n - k + 1 = (n - 2 - k) + 3 := by omega
        rw [hidx]
        push_cast
        rfl
    have hAsh : (∑ k ∈ rangeN, 1 / (k + 3 : ℝ) ^ 2) ≤ 4 / 9 := by
      unfold rangeN
      rw [show n - 1 = 1 + (n - 2) by omega, Finset.sum_range_add]
      calc
        _ = 1 / (3 : ℝ) ^ 2 +
            ∑ k ∈ Finset.range (n - 2), 1 / (k + 4 : ℝ) ^ 2 := by
              congr 1
              · norm_num [Finset.sum_range_succ]
              · apply Finset.sum_congr rfl
                intro k hk
                push_cast
                ring_nf
        _ ≤ 1 / (3 : ℝ) ^ 2 + 1 / (4 - 1 : ℝ) := by
              exact add_le_add_right
                (Transport.reciprocalSquareShift_le 4 (n - 2) (by norm_num)) _
        _ = 4 / 9 := by norm_num
    have hAsq : (∑ k ∈ rangeN, sqA k) ≤ 4 / 9 := by
      rw [hAeq]
      exact hAsh
    have hBprefix : (∑ k ∈ rangeN, sqB k) ≤
        ∑ k ∈ Finset.range n, sqB k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega))
      intro k hk hnot
      positivity
    have hBfull : (∑ k ∈ Finset.range n, sqB k) ≤ 25 / 36 := by
      unfold sqB
      rw [show n = 2 + (n - 2) by omega, Finset.sum_range_add]
      calc
        _ = 1 / (2 : ℝ) ^ 2 + 1 / (3 : ℝ) ^ 2 +
            ∑ k ∈ Finset.range (n - 2), 1 / (k + 4 : ℝ) ^ 2 := by
              congr 1
              · norm_num [Finset.sum_range_succ]
              · apply Finset.sum_congr rfl
                intro k hk
                push_cast
                ring_nf
        _ ≤ 1 / (2 : ℝ) ^ 2 + 1 / (3 : ℝ) ^ 2 + 1 / (4 - 1 : ℝ) := by
              exact add_le_add_right
                (Transport.reciprocalSquareShift_le 4 (n - 2) (by norm_num)) _
        _ = 25 / 36 := by norm_num
    have hBsq : (∑ k ∈ rangeN, sqB k) ≤ 25 / 36 := hBprefix.trans hBfull
    have hCauchyA : (∑ k ∈ rangeN, recA k) ^ 2 ≤
        ((n - 1 : ℕ) : ℝ) * (∑ k ∈ rangeN, sqA k) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq rangeN
        (fun _ : ℕ => (1 : ℝ)) (fun k => recA k)
      simpa [rangeN, recA, sqA, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
        div_pow] using h
    have hCauchyB : (∑ k ∈ rangeN, recB k) ^ 2 ≤
        ((n - 1 : ℕ) : ℝ) * (∑ k ∈ rangeN, sqB k) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq rangeN
        (fun _ : ℕ => (1 : ℝ)) (fun k => recB k)
      simpa [rangeN, recB, sqB, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
        div_pow] using h
    have hrecA : (∑ k ∈ rangeN, recA k) ≤ (2 / 3 : ℝ) * Real.sqrt n := by
      have hsum : 0 ≤ ∑ k ∈ rangeN, recA k := by
        apply Finset.sum_nonneg
        intro k hk
        positivity
      have hsq : (∑ k ∈ rangeN, recA k) ^ 2 ≤ (n : ℝ) * (4 / 9) := by
        calc
          _ ≤ ((n - 1 : ℕ) : ℝ) * (∑ k ∈ rangeN, sqA k) := hCauchyA
          _ ≤ ((n - 1 : ℕ) : ℝ) * (4 / 9) :=
            mul_le_mul_of_nonneg_left hAsq (by positivity)
          _ ≤ (n : ℝ) * (4 / 9) := by
            have hnsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast Nat.sub_le n 1
            exact mul_le_mul_of_nonneg_right hnsub (by norm_num)
      have htarget : ((2 / 3 : ℝ) * Real.sqrt n) ^ 2 =
          (n : ℝ) * (4 / 9) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      have htargetNonneg : 0 ≤ (2 / 3 : ℝ) * Real.sqrt n := by positivity
      exact (sq_le_sq₀ hsum htargetNonneg).mp (by rw [htarget]; exact hsq)
    have hrecB : (∑ k ∈ rangeN, recB k) ≤ (5 / 6 : ℝ) * Real.sqrt n := by
      have hsum : 0 ≤ ∑ k ∈ rangeN, recB k := by
        apply Finset.sum_nonneg
        intro k hk
        positivity
      have hsq : (∑ k ∈ rangeN, recB k) ^ 2 ≤ (n : ℝ) * (25 / 36) := by
        calc
          _ ≤ ((n - 1 : ℕ) : ℝ) * (∑ k ∈ rangeN, sqB k) := hCauchyB
          _ ≤ ((n - 1 : ℕ) : ℝ) * (25 / 36) :=
            mul_le_mul_of_nonneg_left hBsq (by positivity)
          _ ≤ (n : ℝ) * (25 / 36) := by
            have hnsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast Nat.sub_le n 1
            exact mul_le_mul_of_nonneg_right hnsub (by norm_num)
      have htarget : ((5 / 6 : ℝ) * Real.sqrt n) ^ 2 =
          (n : ℝ) * (25 / 36) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      have htargetNonneg : 0 ≤ (5 / 6 : ℝ) * Real.sqrt n := by positivity
      exact (sq_le_sq₀ hsum htargetNonneg).mp (by rw [htarget]; exact hsq)
    have hcrossEq : (∑ k ∈ rangeN, cross k) =
        (1 / (n + 3 : ℝ)) *
          ((∑ k ∈ rangeN, recA k) + (∑ k ∈ rangeN, recB k)) := by
      calc
        _ = ∑ k ∈ rangeN,
            (1 / (n + 3 : ℝ)) * (recA k + recB k) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk' : k < n - 1 := Finset.mem_range.mp hk
              have hsumidx : n - k + 1 + (k + 2) = n + 3 := by omega
              have hcast : ((n - k + 1 : ℕ) : ℝ) + (k + 2 : ℝ) =
                  (n + 3 : ℝ) := by exact_mod_cast hsumidx
              have ha : 0 < ((n - k + 1 : ℕ) : ℝ) := by positivity
              have hb : 0 < (k + 2 : ℝ) := by positivity
              have hc : 0 < (n + 3 : ℝ) := by positivity
              dsimp [cross, recA, recB]
              rw [← hcast]
              field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
              ring
        _ = (1 / (n + 3 : ℝ)) *
            ((∑ k ∈ rangeN, recA k) + (∑ k ∈ rangeN, recB k)) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hncast : (81 : ℝ) ≤ n := by exact_mod_cast hn81
    have hroot : 9 ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).2
      nlinarith
    have hcrossBound : 2 * (∑ k ∈ rangeN, cross k) ≤ 1 / 3 := by
      have hrec : (∑ k ∈ rangeN, recA k) +
          (∑ k ∈ rangeN, recB k) ≤ (3 / 2 : ℝ) * Real.sqrt n := by
        calc
          _ ≤ (2 / 3 : ℝ) * Real.sqrt n + (5 / 6 : ℝ) * Real.sqrt n :=
            add_le_add hrecA hrecB
          _ = (3 / 2 : ℝ) * Real.sqrt n := by ring
      have hden : 0 < (n + 3 : ℝ) := by positivity
      rw [hcrossEq]
      calc
        2 * ((1 / (n + 3 : ℝ)) *
            ((∑ k ∈ rangeN, recA k) + (∑ k ∈ rangeN, recB k))) ≤
          2 * ((1 / (n + 3 : ℝ)) * ((3 / 2 : ℝ) * Real.sqrt n)) := by
            gcongr
        _ = 3 * Real.sqrt n / (n + 3 : ℝ) := by ring
        _ ≤ 1 / 3 := by
          rw [div_le_iff₀ hden]
          have hsq : 0 ≤ (Real.sqrt n - 9) ^ 2 := sq_nonneg _
          have hprod : 0 ≤ Real.sqrt n * (Real.sqrt n - 9) :=
            mul_nonneg (Real.sqrt_nonneg _) (by linarith)
          have hnnonneg : 0 ≤ (n : ℝ) := by positivity
          have hsquare : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnnonneg
          nlinarith [hsquare, hroot, hsq, hprod]
    have hterm (k : ℕ) (hk : k ∈ rangeN) :
        (n + 1 : ℝ) ^ 2 /
            (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2) ≤
          sqA k + sqB k + 2 * cross k := by
      exact @transportE22_shifted_sum_le_three_halves_term1 n hn81 k hk
    have hsumBound :
        (∑ k ∈ rangeN,
          (n + 1 : ℝ) ^ 2 /
            (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) ≤
          (∑ k ∈ rangeN, sqA k) + (∑ k ∈ rangeN, sqB k) +
            2 * (∑ k ∈ rangeN, cross k) := by
      calc
        _ ≤ ∑ k ∈ rangeN, (sqA k + sqB k + 2 * cross k) :=
          Finset.sum_le_sum fun k hk => hterm k hk
        _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
    calc
      _ ≤ (∑ k ∈ rangeN, sqA k) + (∑ k ∈ rangeN, sqB k) +
          2 * (∑ k ∈ rangeN, cross k) := hsumBound
      _ ≤ 4 / 9 + 25 / 36 + 1 / 3 := by
        linarith [hAsq, hBsq, hcrossBound]
      _ ≤ 3 / 2 := by norm_num

/-- The time-space convolution used in the induction for Lemma 10698. The
`(k+2)` shift makes it bounded by the Appendix B product convolution. -/
theorem transportTimeAnalyticConvolution_le_four (n m : ℕ) :
    (∑ _j ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        (n + 1 : ℝ) ^ 2 /
          (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2 * (m + 1 : ℝ))) ≤ 4 := by
  let a (k : ℕ) : ℝ := (n + 1 : ℝ) ^ 2 /
    (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)
  have hcollapse :
      (∑ _j ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1), a k / (m + 1 : ℝ)) =
        ∑ k ∈ Finset.range (n + 1), a k := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
          ((∑ k ∈ Finset.range (n + 1), a k) / (m + 1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro _j _hj
            rw [Finset.sum_div]
      _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
            push_cast
            have hm : (m + 1 : ℝ) ≠ 0 := by positivity
            field_simp [hm]
  rw [show (∑ _j ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        (n + 1 : ℝ) ^ 2 /
          (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2 * (m + 1 : ℝ))) =
      ∑ _j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1), a k / (m + 1 : ℝ) by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        have hm : (m + 1 : ℝ) ≠ 0 := by positivity
        dsimp [a]
        field_simp [hm]
        ]
  rw [hcollapse]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      a k ≤ (n + 1 : ℝ) ^ 2 /
        (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 1 : ℝ) ^ 2) := by
    have hden : 0 < ((n - k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hkk : 0 < (k + 1 : ℝ) ^ 2 := by positivity
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hshift : (k + 1 : ℝ) ^ 2 ≤ (k + 2 : ℝ) ^ 2 := by nlinarith
    dsimp [a]
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos hden hkk) (mul_le_mul_of_nonneg_left hshift hden.le)
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (n + 1 : ℝ) ^ 2 /
          (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 1 : ℝ) ^ 2) :=
      Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ ≤ 4 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        weightedConvolution_le_four_paper n

end AVenhance.FaaDiBruno

end
