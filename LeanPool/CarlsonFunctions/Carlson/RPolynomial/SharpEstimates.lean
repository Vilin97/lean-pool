/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Estimates
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Generating
import LeanPool.CarlsonFunctions.Pochhammer.Vandermonde
import LeanPool.CarlsonFunctions.Pochhammer.Estimates
import LeanPool.CarlsonFunctions.Pochhammer.BinomialSeries
import LeanPool.CarlsonFunctions.Pochhammer.Identities

/-!
# Sharp bounds for Carlson polynomials

Carlson's inequality 6.2-7(24) uses the maximum node norm, not the sum
of node norms. This distinction preserves the full Taylor disk in Section 6.3.
-/

open Complex Finset Polynomial Set
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Carlson 6.2-7(24), with independent nonnegative bounds for the parameter norms. -/
theorem norm_carlsonRPolynomialNumerator_le_pochhammer (n : ℕ) (b z : ι → ℂ)
    {B : ι → ℝ} (hb : ∀ i, ‖b i‖ ≤ B i)
    {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) :
    ‖carlsonRPolynomialNumerator n b z‖ ≤
      (ascPochhammer ℝ n).eval (∑ i, B i) * r ^ n := by
  rw [carlsonRPolynomialNumerator_eq_sum_piAntidiag, carlsonGeneratingCoeff]
  have hp (m : ι → ℕ) (i : ι) :
      ‖(ascPochhammer ℂ (m i)).eval (b i)‖ ≤ (ascPochhammer ℝ (m i)).eval (B i) :=
    norm_ascPochhammer_eval_le_ascPochhammer (b i) (m i) (hb i)
  calc
    _ ≤ ∑ m ∈ piAntidiag univ n,
        (Nat.multinomial univ m : ℝ) * (∏ i, (ascPochhammer ℝ (m i)).eval (B i)) * r ^ n := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m hm
      have hsum : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
      have hnodes : ‖∏ i, z i ^ m i‖ ≤ r ^ n := by
        rw [Complex.norm_prod]
        calc
          _ ≤ ∏ i, r ^ m i := prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun i _ => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _)
          _ = _ := by rw [prod_pow_eq_pow_sum, hsum]
      have hparams : ‖∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ ≤
          ∏ i, (ascPochhammer ℝ (m i)).eval (B i) := by
        rw [Complex.norm_prod]
        exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hp m i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (Nat.multinomial univ m : ℝ) * r ^ n *
            ∏ i, (ascPochhammer ℝ (m i)).eval (B i) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hnodes (by positivity)) hparams
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by rw [← sum_mul, ascPochhammer_eval_sum]

/-- The parameter majorant in 6.2-7 can be chosen to be the parameter norms themselves. -/
theorem norm_carlsonRPolynomialNumerator_le_sum_norm (n : ℕ) (b z : ι → ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) :
    ‖carlsonRPolynomialNumerator n b z‖ ≤
      (ascPochhammer ℝ n).eval (∑ i, ‖b i‖) * r ^ n :=
  norm_carlsonRPolynomialNumerator_le_pochhammer n b z (fun _ => le_rfl) hr hz

/-- Uniform factorial decay for reciprocal Gamma after sufficiently many shifts
of the total parameter on a compact set. -/
theorem exists_uniform_norm_invGamma_sum_add_nat {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma ((∑ i, b i) + (n + m)))⁻¹‖ ≤ C / n.factorial := by
  have hS : Continuous (fun b : ι → ℂ => ∑ i, b i) := by fun_prop
  obtain ⟨B, hB⟩ := hK.bddAbove_image hS.norm.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt (B + 1)
  have hre (b : ι → ℂ) (hb : b ∈ K) : 1 ≤ ((∑ i, b i) + m).re := by
    have hbnd := hB (mem_image_of_mem _ hb)
    have hr := neg_le_of_abs_le (abs_re_le_norm (∑ i, b i))
    simp only [add_re, natCast_re]
    linarith
  have hc : Continuous (fun b : ι → ℂ => (Gamma ((∑ i, b i) + m))⁻¹) :=
    differentiable_one_div_Gamma.continuous.comp (hS.add continuous_const)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
  refine ⟨m, max C 0, le_max_right _ _, fun b hb n => ?_⟩
  have h := (norm_invGamma_add_nat_le (hre b hb) n).trans
    (div_le_div_of_nonneg_right ((hC (mem_image_of_mem _ hb)).trans (le_max_left C 0))
      (by positivity))
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

/-- A normally convergent majorant for the Taylor construction on compact parameter
sets and bounded node vectors. The only radius restriction is `q * r < 1`. -/
theorem exists_summable_norm_carlsonTaylor_bounded_variables
    {K : Set (ι → ℂ)} (hK : IsCompact K) {a : ℕ → ℂ}
    {C q r : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q * r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * q ^ n) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n b, b ∈ K → ∀ z : ι → ℂ,
      (∀ i, ‖z i‖ ≤ r) → ‖a n * regCarlsonR n z b‖ ≤ M n := by
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image continuous_norm.continuousOn
  obtain ⟨B, hB⟩ := exists_nat_gt (max B₀ 0)
  have hbnd (b : ι → ℂ) (hb : b ∈ K) (i : ι) : ‖b i‖ ≤ (B : ℝ) :=
    (norm_le_pi_norm b i).trans ((hB₀ (mem_image_of_mem _ hb)).trans
      ((le_max_left _ _).trans hB.le))
  let T : ℕ := Fintype.card ι * B
  have hnumer (n : ℕ) (b : ι → ℂ) (hb : b ∈ K) (z : ι → ℂ)
      (hz : ∀ i, ‖z i‖ ≤ r) : ‖carlsonRPolynomialNumerator n b z‖ ≤
        (ascPochhammer ℝ n).eval (T : ℝ) * r ^ n := by
    simpa [T, Nat.cast_mul] using norm_carlsonRPolynomialNumerator_le_pochhammer n b z
      (hbnd b hb) hr hz
  have hS : Continuous (fun b : ι → ℂ => ∑ i, b i) := by fun_prop
  have hD (n : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ b ∈ K,
      ‖(Gamma ((∑ i, b i) + n))⁻¹‖ ≤ D := by
    have hc := differentiable_one_div_Gamma.continuous.comp (hS.add (continuous_const (y := (n : ℂ))))
    obtain ⟨D, hD⟩ := hK.bddAbove_image hc.norm.continuousOn
    exact ⟨max D 0, le_max_right _ _, fun b hb =>
      (hD (mem_image_of_mem _ hb)).trans (le_max_left _ _)⟩
  choose D hDpos hD using hD
  obtain ⟨m, G, hG, hgamma⟩ := exists_uniform_norm_invGamma_sum_add_nat hK
  let tail := fun k : ℕ => C * G * (ascPochhammer ℝ m).eval (T : ℝ) * (q * r) ^ m *
    ((ascPochhammer ℝ k).eval ((T + m : ℕ) : ℝ) / k.factorial * (q * r) ^ k)
  have htail : Summable tail := by
    have hbin := summable_norm_ascPochhammer_mul_pow_div_factorial
      ((T + m : ℕ) : ℂ) ((q * r : ℝ) : ℂ)
      (by simpa [abs_of_nonneg hq, abs_of_nonneg hr] using hqr)
    have hreal : Summable (fun k : ℕ =>
        (ascPochhammer ℝ k).eval ((T + m : ℕ) : ℝ) / k.factorial * (q * r) ^ k) := by
      simpa only [← Nat.cast_ascFactorial, norm_mul, norm_div, norm_pow,
        Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hq, abs_of_nonneg hr] using hbin
    exact hreal.mul_left _
  let M := fun n : ℕ => if n < m then
    C * (ascPochhammer ℝ n).eval (T : ℝ) * (q * r) ^ n * D n else tail (n - m)
  have hM : Summable M := by
    apply (summable_nat_add_iff m).mp
    simpa [M, Nat.not_lt.mpr (Nat.le_add_left m _)] using htail
  refine ⟨M, hM, fun n b hb z hz => ?_⟩
  have hraw : ‖a n * regCarlsonR n z b‖ ≤
      C * (ascPochhammer ℝ n).eval (T : ℝ) * (q * r) ^ n *
        ‖(Gamma ((∑ i, b i) + n))⁻¹‖ := by
    simp only [regCarlsonR, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, norm_mul]
    calc
      _ ≤ C * q ^ n * (((ascPochhammer ℝ n).eval (T : ℝ) * r ^ n) *
          ‖(Gamma ((∑ i, b i) + n))⁻¹‖) := by
        gcongr
        · exact ha n
        · exact hnumer n b hb z hz
      _ = _ := by rw [mul_pow]; ring
  by_cases hnm : n < m
  · refine hraw.trans ?_
    dsimp only [M]
    rw [if_pos hnm]
    apply mul_le_mul_of_nonneg_left (hD n b hb)
    rw [← Nat.cast_ascFactorial]
    positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnm)
  have hg := hgamma b hb k
  rw [add_comm (k : ℂ) (m : ℂ)] at hg
  refine hraw.trans ?_
  calc
    _ ≤ C * (ascPochhammer ℝ (m + k)).eval (T : ℝ) * (q * r) ^ (m + k) *
        (G / k.factorial) := by
      rw [Nat.cast_add]
      apply mul_le_mul_of_nonneg_left hg
      rw [← Nat.cast_ascFactorial]
      positivity
    _ = M (m + k) := by
      simp only [M, Nat.not_lt.mpr (Nat.le_add_right m k), if_false,
        Nat.add_sub_cancel_left, tail, ascPochhammer_add_eval, Nat.cast_add, pow_add]
      ring

end DirichletTransform
end
