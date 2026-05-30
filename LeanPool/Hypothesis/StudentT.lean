/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

-- import IO

/-!
# Student t distribution

-/

open Real
/-- The probability density function for the Student t distribution with `ν` degrees of freedom.
-/
noncomputable def t_pdf (ν : ℝ) : ℝ → ℝ := fun x =>
((Gamma ((ν + 1) / 2)) / (√(π * ν) * Gamma (ν/2))) *  (1 + x^2/ν) ^ (- ((ν + 1) / 2))


/-- The probability density function for lognormal distribution with parameters `μ`
and `σ`.
-/
noncomputable def logNormalPdf (μ σ : ℝ) : ℝ → ℝ := fun x =>
  (1 / (σ * √(2 * π))) * (x ^ (-(1:ℝ) ) * exp ((-1 / (2 * σ^2)) * (log x - μ) ^ 2))

/-- An equivalent form of the lognormal density `logNormalPdf` using inverses. -/
noncomputable def logNormalPdf' (μ σ : ℝ) : ℝ → ℝ := fun x =>
  (σ * √(2 * π))⁻¹ * x⁻¹ * exp (- (2 * σ^2)⁻¹ * (log x - μ) ^ 2)

lemma logNormalPdf_eq_logNormalPdf' (μ σ : ℝ) :
    logNormalPdf μ σ = logNormalPdf' μ σ := by
    ext x
    unfold logNormalPdf
    unfold logNormalPdf'
    rw [mul_assoc]
    congr
    · simp
    · exact rpow_neg_one x
    · ring_nf

lemma rpow_neg_one_int {x : ℝ} (hx : x ≠ 0) (s e : ℝ) :
    e * (x ^ (-1 : ℝ)) ^ (2) * s * x ^ (2:ℤ) = e * s := by
    rw [rpow_neg_one]
    field_simp

lemma rpow_neg_one_int' {x : ℝ} (hx : x ≠ 0) (s e : ℝ) :
    e * (x⁻¹) ^ (2) * s * x ^ (2:ℤ) = e * s := by
    field_simp


/-- A bit surprising that `σ` does not need to be positive here. -/
/-

if (-1 + ((-1 / (2 * σ ^ 2) * (2 * (log x - μ) )) = 0 then
(log x - μ)= - σ²/2
x = e^(μ - σ²/2)
-/
theorem derivStudent.extracted_1_1 {d e g h : ℝ} (f : ℝ) (this : d * e = g * h) :
      d * -f * e = -(f * g * h) := by
  ring_nf at this ⊢
  simp only [neg_inj, mul_eq_mul_right_iff]
  rw [this]
  left
  rfl

lemma tHelper {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) : 0 < 1 + x ^ 2 / ν := by
    by_cases H : ν = 0
    · subst H;simp
    · calc (0:ℝ) < 1 := by simp
        _ ≤ _ := by
          suffices 0 ≤ x^2/ν by linarith
          positivity

/-- The messy formula for the derivative of Student's `t`. -/
lemma derivStudent {ν : ℝ} (hν : 0 ≤ ν) : deriv (t_pdf ν) =
    fun x => ((Gamma ((ν + 1) / 2)) / (√(π * ν) * Gamma (ν/2)))
           * ((- ((ν + 1) / 2)) * (1 + x^2/ν) ^ (- ((ν + 3) / 2))
           * (2*x/ν)) := by
  ext x
  have h₀ :  1 + x ^ 2 / ν ≠ 0 := ne_of_gt <| tHelper hν _
  unfold t_pdf
  rw [deriv_const_mul]
  · congr
    simp only [neg_mul]
    rw [_root_.deriv_rpow_const (p :=  (-((ν + 1) / 2)))]
    · suffices deriv (fun x ↦ 1 + x ^ 2 / ν) x * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2) - 1) =
       (1 + x ^ 2 / ν) ^ (-((ν + 3) / 2)) * (2 * x / ν) by
        by_cases H : ((ν + 1) / 2) = 0
        · rw [H]
          simp
        · apply derivStudent.extracted_1_1 _ this
      conv =>
        left; left; left
        change (fun x => 1) + (fun x => x ^ 2 / ν)
      rw [deriv_add]
      · simp only [
          deriv_const', deriv_div_const, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat,
          Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
        rw [mul_comm]
        simp only [mul_eq_mul_right_iff, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
          false_or]
        left
        congr
        ring_nf
      · simp
      · simp
    · simp
    · simp only [ne_eq]
      left
      exact h₀
  · refine DifferentiableAt.rpow ?_ ?_ h₀
    · apply Differentiable.fun_add <;> simp
    · exact differentiableAt_const _

-- /-- The messy formula for the derivative of Student's `t`. -/
-- lemma derivStudent₂ {ν : ℝ} (hν : 0 < ν) : deriv (deriv (t_pdf ν)) =
--     fun x => ((Gamma ((ν + 1) / 2)) / (√(π * ν) * Gamma (ν/2)))
--            * (2*x/ν)) +
--            ((Gamma ((ν + 1) / 2)) / (√(π * ν) * Gamma (ν/2)))
--            * ((- ((ν + 1) / 2)) * (1 + x^2/ν) ^ (- ((ν + 3) / 2))
--            * (2/ν))
--            := by
--   rw [derivStudent hν]
--   ext x
--   rw [deriv_const_mul]
--   sorry
--   -- refine DifferentiableAt.fun_mul ?_ ?_
--   -- refine DifferentiableAt.const_mul ?_ (-((ν + 1) / 2))
--   -- refine DifferentiableAt.rpow ?_ ?_ ?_

--   sorry

/-- The only place the derivative of Student's `t` is 0 is 0. -/
lemma derivStudent' (x ν : ℝ) (hν : 0 < ν) :
    deriv (t_pdf ν) x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [derivStudent (by linarith)] at h
    simp only [
      neg_mul, mul_neg, neg_eq_zero, mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
      false_or] at h
    cases h with
    | inl h => cases h with
      | inl h =>
        exfalso;revert h;simp only [imp_false]
        refine Gamma_ne_zero ?_
        intro m
        linarith
      | inr h => cases h with
        | inl h =>
          rw [sqrt_eq_zero, mul_eq_zero] at h
          · rcases h <;> linarith [pi_pos]
          · apply mul_nonneg pi_nonneg
            linarith
        | inr h =>
          exfalso;simp only at h
          revert h
          simp only [imp_false]
          refine Gamma_ne_zero ?_
          intro m
          linarith
    | inr h => cases h with
      | inl h => cases h with
        | inl h => linarith
        | inr h =>
          exfalso
          revert h
          simp only [imp_false]
          refine (rpow_ne_zero ?_ ?_).mpr ?_
          · apply le_of_lt
            exact tHelper (by linarith) _
          · simp
            linarith
          · apply ne_of_gt <| tHelper (by linarith) _
      | inr h =>
          cases h <;> linarith
  · intro h
    rw [derivStudent (by linarith), h]
    simp


/-- The Student t distribution with one df is the Cauchy distribution. -/
lemma t_pdf_one (x : ℝ) : t_pdf 1 x = 1 / (π * (1 + x^2)) := by
  unfold t_pdf
  simp only [add_self_div_two, Gamma_one, mul_one, one_div, mul_inv_rev, div_one]
  have : Gamma 2⁻¹ = √π := by simpa using Real.Gamma_nat_add_half 0
  rw [this]
  rw [mul_comm]
  congr
  · exact rpow_neg_one _
  · ring_nf
    simp only [inv_pow, inv_inj]
    refine sq_sqrt pi_nonneg

/-- The t distribution pdf has an everywhere-positive pdf. -/
lemma t_pdf_pos (x ν : ℝ) (hν : ν > 0) : t_pdf ν x > 0 := by
  simp only [t_pdf, gt_iff_lt]
  refine mul_pos ?_ ?_
  · refine div_pos ?_ ?_
    · exact Gamma_pos_of_pos (by linarith)
    · refine mul_pos ?_ <| Gamma_pos_of_pos (by linarith)
      rw [sqrt_pos]
      exact mul_pos pi_pos hν
  · refine rpow_pos_of_pos ?_ _
    apply tHelper <| le_of_lt hν

/-- The pdf of the Student `t` distribution with 2 degrees of freedom. -/
  lemma studentT2Pdf (x : ℝ) : t_pdf 2 x = (1 / (2 * √2)) * (1 + x^2/2) ^ (- (3:ℝ)/2) := by
  simp only [
    t_pdf, Nat.ofNat_nonneg, sqrt_mul', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self,
    Gamma_one, mul_one, one_div, mul_inv_rev]
  rw [show Gamma ((2+1)/2) = Gamma (1 + 2⁻¹) by ring_nf]
  have := Real.Gamma_nat_add_half 1
  simp only [Nat.cast_one, one_div, Nat.doubleFactorial, one_mul, pow_one] at this
  rw [this]
  ring_nf
  have : √π * (√π)⁻¹ = 1 :=
    mul_inv_cancel₀ fun h => pi_ne_zero <| (sqrt_eq_zero pi_nonneg).mp h
  rw [this]
  simp

lemma studentTSymmetric (x ν : ℝ) : t_pdf ν x = t_pdf ν (-x) := by
  simp [t_pdf]

lemma studentTMode (x ν : ℝ) (hν : 0 ≤ ν) : t_pdf ν x ≤ t_pdf ν 0 := by
  refine mul_le_mul ?_ ?_ ?_ ?_
  · simp
  · apply Real.rpow_le_rpow_of_nonpos
    all_goals simp only [
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, zero_lt_one,
      le_add_iff_nonneg_right, Left.neg_nonpos_iff]
    · refine div_nonneg ?_ ?_
      · positivity
      · tauto
    · linarith
  · positivity
  · apply div_nonneg <;> positivity

lemma studentTMax (ν : ℝ) (hν : 0 ≤ ν) :
  IsLocalMax (t_pdf ν) 0 := by
  rw [IsLocalMax, IsMaxFilter]
  refine eventually_nhds_iff.mpr ?_
  use Set.univ
  simp only [Set.mem_univ, forall_const, isOpen_univ, and_self, and_true]
  intro y
  apply studentTMode _ _ hν

/-!

# RANDOM VARIABLES

-/

/-- The sample mean. -/
noncomputable def Bar {n : ℕ} : (Fin n → ℝ) → ℝ := fun X => (1 / n) * ∑ i, X i

/-- The sample standard deviation. -/
noncomputable def sampleStdDev {n : ℕ} : (Fin n → ℝ) → ℝ := fun X =>
    √(1 / (n - 1) * ∑ i, (X i - Bar X) ^ 2)



/-- The function underlying the t distribution.
If `X i` are `iid` and `N(μ, σ^2)` then this T has the t distribution.
-/
noncomputable def T {μ : ℝ} {n : ℕ} : (Fin n → ℝ) → ℝ := fun X =>
    (Bar X - μ) / (sampleStdDev X / √(n:ℝ))

section Behrens
/-- The pooled standard deviation estimate of two samples `X`, `Y`. -/
noncomputable def S₂ {m n : ℕ} : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun X Y =>
    √((1 / (m - 1) * ∑ i, (X i - Bar X) ^ 2) + (1 / (n - 1) * ∑ i, (Y i - Bar Y) ^ 2))

/-- Behrens-Fisher distribution. -/
noncomputable def BF {n : ℕ} : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun X Y =>
    (Bar X - Bar Y) / (S₂ X Y)


-- wrong
-- def BehrensFisher : Prop :=
--     ∀ (m n : ℕ), ∃ T : (Fin (m + n) → ℝ) → ℝ,
--         ∀ (σ₁ σ₂ : NNReal) (r : ℝ),
--         MeasureTheory.Measure.pi
--             (fun _ => ProbabilityTheory.gaussianReal 0 σ₁)
--             (fun x  => T x ≤ r) =
--         MeasureTheory.Measure.pi
--             (fun _ => ProbabilityTheory.gaussianReal 0 σ₂)
--             (fun x => T x ≤ r)
--         -- and 𝔼 T = 0 and ...
end Behrens

lemma compute_sample_mean_example : Bar ![1,1,(5:ℝ)] = 7/3 := by
    unfold Bar;simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.cast_ofNat, one_div]
    have : ∑ x, ![(1:ℝ),1,5] x = 1 + ∑ x, ![(1:ℝ),5] x := by rfl
    rw [this]
    have : ∑ x, ![(1:ℝ),5] x = 1 + ∑ x, ![5] x := by rfl
    rw [this]
    simp
    linarith

/-- This example corrects an error in `s4cs` (2019). -/
example {Ω : Type*} (X : Fin 2 → (Ω → ℝ)) (μX : ℝ)
  (T S Xbar : (Fin 2 → Ω) → ℝ)
  (hX : Xbar = fun ω => (1 / 2) * ∑ i, X i (ω i)) -- so the X i are "independent by construction"
  (hS : S = fun ω =>
    √((1 / (2 - 1)) * ∑ i, (X i (ω i) - Xbar ω) ^ 2))
  (hT : T = fun ω =>
    (Xbar ω - μX) / ((1 / √2) * S ω)) :
  T = fun ω =>
    ((1/2) * (X 0 (ω 0) + X 1 (ω 1) ) - μX) /
    ((1/2) * abs (X 0 (ω 0) - X 1 (ω 1) ) ) := by
  ext ω
  rw [hT, hS, hX]
  simp only [
    one_div, Fin.sum_univ_two, Fin.isValue, inv_nonneg, sub_nonneg, Nat.one_le_ofNat, sqrt_mul,
    sqrt_inv]
  have : (√(2 - 1))⁻¹ = 1 := by
    simp
    linarith
  rw [this]
  set x₀ := X 0 (ω 0)
  set x₁ := X 1 (ω 1)
  simp only [one_mul]
  suffices ((√2)⁻¹ * √((x₀ - 2⁻¹ * (x₀ + x₁)) ^ 2 + (x₁ - 2⁻¹ * (x₀ + x₁)) ^ 2)) =
    (2⁻¹ * |x₀ - x₁|) by exact congrArg (HDiv.hDiv (2⁻¹ * (x₀ + x₁) - μX)) this
  have : |x₀ - x₁| = √((x₀ - x₁)^2) := Eq.symm (sqrt_sq_eq_abs (x₀ - x₁))
  rw [this]
  have : 2⁻¹ = (√2)⁻¹ * (√2)⁻¹ := by ring_nf;simp
  nth_rw 3 [this]
  rw [mul_assoc]
  congr
  have : (√2)⁻¹ * √((x₀ - x₁) ^ 2) = √ (2⁻¹ * ((x₀ - x₁) ^ 2)) := by simp
  rw [this]
  congr
  linarith


/-- The Welch–Satterthwaite effective degrees of freedom for a two-sample t-test. -/
noncomputable def welch_df (s₁ s₂ n₁ n₂ ν₁ ν₂ : ℝ) :=
  (s₁^2/n₁ + s₂^2/n₂)^2 / ((s₁^4/(n₁^2 * ν₁)) + (s₂^4/(n₂^2 * ν₂)))

-- Now let us check the Welch test df lower bound on page 67.
lemma welch₀ {s₁ s₂ n₁ n₂ ν₁ ν₂ : ℝ}
  (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
  (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
  (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
  (h : ν₁ ≤ ν₂) :
  welch_df s₁ s₂ n₁ n₂ ν₁ ν₂ ≥ min ν₁ ν₂ := by
    unfold welch_df
    have : min ν₁ ν₂ = ν₁ := min_eq_left h
    rw [this]
    suffices  (s₁ ^ 2 / n₁ + s₂ ^ 2 / n₂) ^ 2
        ≥ (s₁ ^ 4 / (n₁ ^ 2 * ν₁) + s₂ ^ 4 / (n₂ ^ 2 * ν₂)) * ν₁ by
      generalize (s₁ ^ 2 / n₁ + s₂ ^ 2 / n₂) ^ 2 = A at *
      refine (le_div_iff₀' ?_).mpr this
      apply add_pos
        (div_pos (pow_pos hs₁ 4) (mul_pos (sq_pos_of_pos hn₁) hν₁))
        (div_pos (pow_pos hs₂ 4) (mul_pos (sq_pos_of_pos hn₂) hν₂))
    rw [add_sq]
    have : (s₁ ^ 4 / (n₁ ^ 2 * ν₁) + s₂ ^ 4 / (n₂ ^ 2 * ν₂)) * ν₁
      = (s₁ ^ 4 / (n₁ ^ 2 * ν₁)) * ν₁ + (s₂ ^ 4 / (n₂ ^ 2 * ν₂)) * ν₁ := by
        apply right_distrib
    rw [this]
    have :  s₁ ^ 4 / (n₁ ^ 2 * ν₁) * ν₁ =  s₁ ^ 4 / (n₁ ^ 2) := by
        field_simp
    rw [this]
    have : (s₁ ^ 2 / n₁) ^ 2 = s₁ ^ 4 / n₁ ^ 2 := by ring_nf
    rw [this]
    suffices 2 * (s₁ ^ 2 / n₁) * (s₂ ^ 2 / n₂) + (s₂ ^ 2 / n₂) ^ 2 ≥ s₂ ^ 4 / (n₂ ^ 2 * ν₂) * ν₁ by
      linarith
    calc _ ≥ (s₂ ^ 2 / n₂) ^ 2  := by
            suffices 0 < 2 * (s₁ ^ 2 / n₁) * (s₂ ^ 2 / n₂) by linarith
            apply mul_pos
            · apply mul_pos (by simp) (div_pos (sq_pos_of_pos hs₁) hn₁)
            · apply div_pos (sq_pos_of_pos hs₂) hn₂
         _ ≥ _ := by
            have : s₂ ^ 4 / (n₂ ^ 2 * ν₂) * ν₁ = s₂ ^ 4 * (ν₁ / (n₂ ^ 2 * ν₂)) :=
                mul_comm_div (s₂ ^ 4) (n₂ ^ 2 * ν₂) ν₁
            rw [this]
            have : (s₂ ^ 2 / n₂) ^ 2 = s₂ ^ 4 / n₂ ^ 2 := by ring_nf
            rw [this]
            have : (ν₁ / (n₂ ^ 2 * ν₂))
              = ((ν₁/ν₂) / (n₂ ^ 2)) := div_mul_eq_div_div_swap ν₁ (n₂ ^ 2) ν₂
            rw [this]
            have hA : 0 < s₂ ^ 4 := pow_pos hs₂ 4
            generalize s₂ ^ 4 = A at *
            have hB : 0 < n₂ ^ 2 := sq_pos_of_pos hn₂
            generalize n₂ ^ 2 = B at *
            have : A / B = A * (1 / B) := by ring_nf
            rw [this]
            apply mul_le_mul
            · simp
            · apply div_le_div₀ (by simp) ((div_le_one₀ hν₂).mpr h) hB (by simp)
            · apply div_nonneg
              · apply div_nonneg <;> linarith
              · linarith
            · linarith

/-- The welch_df lower bound when s₁ or s₂ is 0. -/
lemma welch' {s₁ s₂ n₁ n₂ ν₁ ν₂ : ℝ}
  (hs₁ : 0 = s₁) (hs₂ : 0 < s₂) (hn₂ : 0 < n₂) :
  welch_df s₁ s₂ n₁ n₂ ν₁ ν₂ ≥ min ν₁ ν₂ := by
  unfold welch_df
  rw [← hs₁]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_add, ge_iff_le]
  have :  (s₂ ^ 2 / n₂) ^ 2 = s₂ ^ 4 / (n₂^2) := by
    ring_nf
  rw [this]
  have hA : 0 < s₂ ^ 4 := by
    exact pow_pos hs₂ 4
  generalize s₂^4 = A at *
  have hB : 0 < n₂^2 := by exact sq_pos_of_pos hn₂
  generalize n₂^2 = B at *
  calc _ ≤ ν₂ := by simp
       _ ≤ _ := by
        ring_nf
        simp only [inv_inv]
        apply le_of_eq
        rw [mul_comm]
        nth_rw 1 [← mul_one ν₂]
        congr
        ring_nf
        field_simp

/-- Slightly amusingly, if one of `s₁, s₂` is zero the result still holds
but if both are it does not.
-/
lemma welch {s₁ s₂ n₁ n₂ ν₁ ν₂ : ℝ}
  (hs₁ : 0 ≤ s₁) (hs₂ : 0 < s₂)
  (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
  (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
  welch_df s₁ s₂ n₁ n₂ ν₁ ν₂ ≥ min ν₁ ν₂ := by
  unfold welch_df
  have : 0 = s₁ ∨ 0 < s₁ := Or.symm (Decidable.lt_or_eq_of_le hs₁)
  cases this with
  | inl h => apply welch' <;> tauto
  | inr hs₁ =>
  have : ν₁ ≤ ν₂ ∨ ν₂ ≤ ν₁ := LinearOrder.le_total ν₁ ν₂
  cases this with
  | inl h => apply welch₀ <;> tauto
  | inr h =>
    have := @welch₀ s₂ s₁ n₂ n₁ ν₂ ν₁ hs₂ hs₁ hn₂ hn₁ hν₂ hν₁ h
    unfold welch_df at this
    convert this using 1
    · nth_rw 1 [add_comm]
      nth_rw 2 [add_comm]
    · exact min_comm ν₁ ν₂

/-- A claim on the bottom of page 67:
"We see that when n₁ = n₂, the difference between
the Welch df and the conservative df is at most 1"
That seems to be wrong.

But the claim at
https://stats.stackexchange.com/questions/48636/are-the-degrees-of-freedom-for-welchs-test-always-less-than-the-df-of-the-poole
is verified below.
-/
lemma howell {s₁ s₂ n₁ n₂ ν₁ ν₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hn₁ : 0 < n₁ - 1) (hn₂ : 0 < n₂ - 1)
    (hνn₁ : ν₁ = n₁ - 1) (hνn₂ : ν₂ = n₂ - 1) :
    welch_df s₁ s₂ n₁ n₂ ν₁ ν₂ ≤ ν₁ + ν₂ := by
    rw [hνn₁, hνn₂]
    unfold welch_df
    suffices (s₁ ^ 2 / n₁ + s₂ ^ 2 / n₂) ^ 2
        ≤ (s₁ ^ 4 / (n₁ ^ 2 * (n₁ - 1)) + s₂ ^ 4 / (n₂ ^ 2 * (n₂ - 1))) * (n₁ - 1 + (n₂ - 1)) by
      generalize (s₁ ^ 2 / n₁ + s₂ ^ 2 / n₂) ^ 2 = A at *
      have hB : 0 < (s₁ ^ 4 / (n₁ ^ 2 * (n₁ - 1)) + s₂ ^ 4 / (n₂ ^ 2 * (n₂ - 1))) := by
        apply add_pos
        · apply div_pos
          · exact pow_pos hs₁ 4
          · apply mul_pos
            · rw [pow_two]
              apply mul_pos
              · linarith
              · linarith
            · linarith
        · apply div_pos
          · exact pow_pos hs₂ 4
          · apply mul_pos
            · rw [pow_two]
              apply mul_pos
              · linarith
              · linarith
            · linarith
      generalize (s₁ ^ 4 / (n₁ ^ 2 * (n₁ - 1)) + s₂ ^ 4 / (n₂ ^ 2 * (n₂ - 1))) = B at *
      generalize  n₁ - 1 + (n₂ - 1) = C at *
      exact (div_le_iff₀' hB).mpr this
    have : s₁ ^ 4 / (n₁ ^ 2 * (n₁ - 1))
      = (s₁ ^ 2 / n₁)^2 / (n₁ - 1) := by
        field_simp
    rw [this]
    have : s₂ ^ 4 / (n₂ ^ 2 * (n₂ - 1))
      = (s₂ ^ 2 / n₂)^2 / (n₂ - 1) := by
        field_simp
    rw [this]
    have hA : 0 < s₂^2/n₂ := by
      apply div_pos
      · exact sq_pos_of_pos hs₂
      · linarith
    have hB : 0 < s₁^2/n₁ := by
      apply div_pos
      · exact sq_pos_of_pos hs₁
      · linarith
    generalize s₂^2/n₂ = A at *
    generalize s₁^2/n₁ = B at *
    rw [mul_add]
    rw [add_mul]
    rw [add_mul]
    have : B ^ 2 / (n₁ - 1) * (n₁ - 1) = B^2 := by
      refine div_mul_cancel₀ (B ^ 2) ?_
      linarith
    rw [this]
    have : A ^ 2 / (n₂ - 1) * (n₂ - 1) = A^2 := by
      refine div_mul_cancel₀ (A ^ 2) ?_
      linarith
    rw [this]
    rw [add_sq]
    suffices 2 * B * A ≤ A ^ 2 / (n₂ - 1) * (n₁ - 1) + (B ^ 2 / (n₁ - 1) * (n₂ - 1)) by
      linarith
    have :  A ^ 2 / (n₂ - 1) * (n₁ - 1)
      = A ^2 * ((n₁-1)/(n₂-1)) := by field_simp
    rw [this]
    have : B ^ 2 / (n₁ - 1) * (n₂ - 1)
      = B ^ 2 / ((n₁-1)/(n₂-1)) := by field_simp
    rw [this]
    have hC : 0 < ((n₁-1)/(n₂-1)) := by apply div_pos <;> tauto
    generalize ((n₁-1)/(n₂-1)) = C at *
    suffices  (2 * B * A) * C ≤ (A ^ 2 * C + B ^ 2 / C) * C by
      exact le_of_mul_le_mul_right this hC
    suffices 2 * B * A * C ≤ A ^ 2 * C ^ 2 + B ^ 2 by
      convert this using 1
      ring_nf
      field_simp
    have : A^2 * C ^ 2 = (A * C)^2 := by ring_nf
    rw [this]
    have : 2 * B * A * C = 2 * B * (A * C) := by ring_nf
    rw [this]
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    have : 0 ≤ (A*C - B)^2 := by positivity
    rw [sub_sq] at this
    linarith

/-- I don't think this is true without the
assumption n=2. -/
lemma claimFromBook {s₁ s₂ n ν₁ ν₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hνn₁ : ν₁ = n - 1) (hνn₂ : ν₂ = n - 1)
    (h₂₀₂₅ : n = 2) :
    welch_df s₁ s₂ n n ν₁ ν₂ ≤ (min ν₁ ν₂) + 1 := by
  subst hνn₁ hνn₂ h₂₀₂₅
  have := @howell s₁ s₂ 2 2 1 1 hs₁ hs₂
   (by linarith) (by linarith)
    (by linarith) (by linarith)
  convert this
  all_goals try simp
  all_goals linarith


-- χ²

/-- The normalizing constant `(2^(k/2) Γ(k/2))⁻¹` of the χ²(k) density. -/
noncomputable def cχ (k : ℝ) := ((2 ^ (k / 2) * Gamma (k / 2)))⁻¹

/-- The probability density function of the χ² distribution with
`k` degrees of freedom. -/
noncomputable def χ2pdf (k : ℝ) : ℝ → ℝ := fun x =>
  cχ k * (x ^ (k / 2 - 1) * exp (- x / 2))

/-- A "junk theorem" about the χ² distribution with 0,
or more generally any integer of the form -2k, degrees of freedom. -/
example (x : ℝ) (k : ℕ) : χ2pdf (- 2 * k) x = 0 := by
unfold χ2pdf cχ
simp only [neg_mul, mul_inv_rev, mul_eq_zero, inv_eq_zero, exp_ne_zero, or_false]
left
left
refine (Gamma_eq_zero_iff (-(2 * ↑k) / 2)).mpr ?_
use k
show @Eq ℝ (-(2 * ↑k) / 2) (-↑k)
suffices @Eq ℝ ((2 * ↑k) / 2) (↑k) by linarith
simp

/-- The exponential distribution with parameter `λ` (written `μ`).
We do not enforce `x≥0` here.
-/
noncomputable def exponential_pdf (μ : ℝ) : ℝ → ℝ := fun x => μ * rexp (- μ * x)

/-- The χ² distribution with 2 degrees of freedom is
the exponential distribution with parameter `λ = 2⁻¹`. -/
lemma χ2_exponential (x : ℝ) : χ2pdf 2 x = exponential_pdf (2⁻¹) x := by
  simp [χ2pdf, cχ, exponential_pdf]
  ring_nf

lemma auxχ (k x : ℝ) (hx : x ≠ 0) :
  DifferentiableAt ℝ (fun x ↦ x ^ (k / 2 - 1) * rexp (-x / 2)) x := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.rpow (by simp) (by simp) hx
  · change DifferentiableAt ℝ (rexp ∘ fun x => -x/2) x
    apply DifferentiableAt.comp
    · simp
    · suffices DifferentiableAt ℝ (fun x => (-(1:ℝ)/2)*x) x by
        convert this using 2
        ring_nf
      apply Differentiable.const_mul (by simp)

/-- A formula for the derivative of the χ² pdf. -/
theorem deriv_χ (k x : ℝ) (hx : x ≠ 0) : deriv (χ2pdf k) x =
  cχ k * rexp (-x/2) * (x ^ (k / 2 - 2)) * ((k / 2 - 1) - 2⁻¹ * x) := by
  unfold χ2pdf
  have hrpow : DifferentiableAt ℝ (fun x ↦ x ^ (k / 2 - 1)) x :=
    DifferentiableAt.rpow (by simp) (by simp) hx
  have hexp : DifferentiableAt ℝ (fun x ↦ rexp (-x / 2)) x := by
    refine Differentiable.differentiableAt ?_
    change Differentiable ℝ (rexp ∘ fun x ↦ -x/2)
    apply Differentiable.comp
    · simp
    · suffices Differentiable ℝ (fun x => (-(1:ℝ)/2)*x) by
        convert this using 2
        ring_nf
      apply Differentiable.const_mul
      simp
  rw [deriv_const_mul (cχ k) (auxχ k x hx)]
  nth_rw 2 [mul_assoc]
  nth_rw 1 [mul_assoc]
  congr
  conv =>
    left
    left
    change (fun x ↦ x ^ (k / 2 - 1)) * fun x => rexp (-x / 2)
  rw [deriv_mul hrpow hexp, Real.deriv_rpow_const]
  have : (fun x ↦ rexp (-x / 2))
    = rexp ∘ fun x ↦ ((-1/2) * x) := by ext i;simp;grind
  rw [this]
  rw [deriv_comp _ Real.differentiable_exp.differentiableAt
      (differentiableAt_id.const_mul _), Real.deriv_exp,
      deriv_const_mul _ differentiableAt_id, mul_comm]
  conv =>
    rw [mul_assoc]
  conv =>
    left
    right
    rw [← mul_assoc]
  nth_rw 4 [mul_comm]
  nth_rw 1 [mul_assoc]
  have : -1/2*x = -x/2 := by ring_nf
  rw [this]
  rw [← left_distrib]
  congr
  simp only [deriv_id'', mul_one]
  have : k / 2 - 1 - 1 = k / 2 - 2 := by linarith
  rw [this]
  have : x ^ (k / 2 - 1) = x ^ (k / 2 - 2 + 1) := by
    congr
    linarith
  rw [this]
  rw [rpow_add_one hx (k / 2 - 2), mul_comm, mul_assoc, ← left_distrib]
  congr
  ring_nf


example : cχ 0 = 0 := by simp [cχ]

/-- The multiplicative constant in the χ² pdf is nonzero. -/
lemma cχ_ne_zero (k : ℝ) (hk : 0 < k) : cχ k ≠ 0 := by
  unfold cχ
  apply inv_ne_zero
  apply mul_ne_zero
  · simp only [ne_eq]
    refine (rpow_ne_zero ?_ ?_).mpr ?_
    · simp
    · exact ne_of_gt (by positivity)
    · norm_num
  · simp only [ne_eq]
    refine Gamma_ne_zero ?_
    intro m hc
    have : 0 < k / 2 := by linarith
    revert this
    rw [hc]
    simp

lemma need₄ (x k : ℝ) (hk : k ≠ 4) (hx : 0 < x)
   (h : x ^ (k / 2 - 2) = 0) :
  x = k - 2 := by
    exfalso;revert h;simp only [imp_false];refine (rpow_ne_zero ?_ ?_).mpr ?_
    · linarith
    · intro hc
      have : k = 4 := by linarith
      tauto
    · linarith

/-- The only critical point of a χ²(k) pdf is `k-2`. -/
theorem deriv_χ_zero {x k : ℝ} (hk₀ : 0 < k) (hx : 0 < x) (h : deriv (χ2pdf k) x = 0) :
  x = k - 2 := by
  rw [deriv_χ k x (ne_of_gt hx)] at h
  have : cχ k ≠ 0 := by apply cχ_ne_zero;linarith
  have h :  cχ k * (rexp (-x / 2) * x ^ (k / 2 - 2) * (k / 2 - 1 - 2⁻¹ * x)) = 0 := by
    rw [← h]
    ring_nf
  have h₀ : rexp (-x / 2) * x ^ (k / 2 - 2) * (k / 2 - 1 - 2⁻¹ * x) = 0 := by
    rcases mul_eq_zero.mp h <;> tauto
  rw [mul_assoc] at h₀
  by_cases hk : k = 4
  · subst hk
    simp_all only [Nat.ofNat_pos, mul_eq_zero, exp_ne_zero, or_self, false_or, ne_eq, or_true]
    cases h with
    | inl h =>
      exfalso
      have : x ^ 0 = 0 := by
        convert h using 2;
        have : (4:ℝ) / 2 - 2 = 0 := by ring_nf
        rw [this]
        simp
      revert this
      simp
    | inr h₁ =>
      simp at h₁
      linarith
  · simp only [mul_eq_zero, exp_ne_zero, false_or] at h₀
    cases h₀ with
    | inl h =>
      apply need₄
      · tauto
      · linarith
      · tauto
    | inr h₁ =>
      simp at h₁
      linarith

/-- The χ² distribution with `0 < k ≤ 2` df has no critical point. -/
theorem no_deriv_χ_zero (x k : ℝ)
  (hk₀ : 0 < k)
  (hx : 0 < x) (h₀ : k ≤ 2) : deriv (χ2pdf k) x ≠ 0 := by
  intro hc
  have := @deriv_χ_zero _ _ hk₀ hx hc
  linarith

lemma eventually_of_punctured {a b : ℝ} (hb : a ≠ b) {P : ℝ → Prop} (h₀ : ∀ (x : ℝ), x ≠ b → P x) :
  ∀ᶠ (x : ℝ) in nhds a, P x := by
      refine eventually_nhds_iff.mpr ?_
      use Metric.ball a (|b - a|/2)
      constructor
      · intro y hy
        apply h₀
        intro hc
        symm at hc
        subst hc
        change |b - a| < |b - a| / 2 at hy
        have : 0 ≤ |b - a| := by simp
        have : |b - a| = 0 := by linarith
        rw [this] at hy
        simp at hy
      · constructor
        · simp
        · simp only [
            Metric.mem_ball, dist_self, Nat.ofNat_pos, div_pos_iff_of_pos_right, abs_pos, ne_eq]
          contrapose! hb
          linarith

/-- The sub-σ-algebra on `Fin 2 → Bool` generated by reading the `i`-th coordinate. -/
@[reducible] def σ : Fin 2 → MeasurableSpace (Fin 2 → Bool) :=
  fun i => MeasurableSpace.comap (fun v => v i) Bool.instMeasurableSpace

/-- The fair coin as a probability mass function on `Bool`. -/
noncomputable def fairCoin : PMF Bool := PMF.bernoulli (1/2) (by simp)

/-- The fair-coin measure on `Bool`. -/
noncomputable def μ : MeasureTheory.Measure Bool := fairCoin.toMeasure

example : μ {true} = 1/2 := by unfold μ fairCoin PMF.bernoulli;simp

/-- The product of two fair-coin measures on `Fin 2 → Bool`. -/
noncomputable def μ' : MeasureTheory.Measure (Fin 2 → Bool) := MeasureTheory.Measure.pi <| fun _ =>
    μ

/-- Maybe easier to work with than Measure.pi -/
noncomputable def μ'' : PMF (Fin 2 → Bool) := by
  refine PMF.ofFintype ?_ ?_
  · intro v
    exact 1/4
  · simp only [
      one_div, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Fintype.card_fin, Nat.reducePow, nsmul_eq_mul, Nat.cast_ofNat]
    refine ENNReal.mul_inv_cancel ?_ ?_
    · simp
    · simp

/-- The measure on `Fin 2 → Bool` induced by the uniform PMF `μ''`. -/
noncomputable def ν := μ''.toMeasure

open MeasureTheory
lemma basic_ν (b c : Bool) : ν {![b,c]} = (1/2) * (1/2) := by
  unfold ν μ''
  simp only [
    one_div, Nat.succ_eq_add_one, Nat.reduceAdd, PMF.toMeasure_apply_fintype, Set.indicator,
    Set.mem_singleton_iff, PMF.ofFintype_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
  · simp
  · exact ENNReal.mul_ne_top (by simp) (by simp)
  · have : (2⁻¹ : ENNReal) * 2⁻¹ = (2*2)⁻¹ := by
      refine Eq.symm (ENNReal.mul_inv ?_ ?_)
      · left
        simp
      · right
        simp
    rw [this]
    norm_num

-- noncomputable def faircoin : PMF Bool := {
--   val := fun b => (1:ENNReal)/2
--   property := by
--     have h₀ :=  @hasSum_fintype ENNReal Bool _ _ _ (fun b => 1/2)
--     have h₁ : ∑ b : Bool, (1:ENNReal)/2 = 1 := by
--       simp
--       field_simp
--       refine (ENNReal.div_eq_one_iff ?hb₀ ?hb₁).mpr rfl
--       simp
--       simp
--     aesop
-- }

-- noncomputable def β : MeasureTheory.ProbabilityMeasure Bool := {
--   val := faircoin.toMeasure
--   property := PMF.toMeasure.isProbabilityMeasure _
-- }

-- noncomputable def β : Measure Bool := {
--   measureOf := by
--     intro s
--     by_cases ht : true ∈ s
--     by_cases hf : false ∈ s
--     exact 1
--     exact 1/2
--     by_cases hf : false ∈ s
--     exact 1/2
--     exact 0
--   empty := by
--     simp
--   mono := by
--     intro s₁ s₂ h
--     simp
--     split_ifs with g₀ g₁ g₂ g₃ g₄
--     all_goals (try simp; try tauto)
--   iUnion_nat := by
--     intro s hs
--     split_ifs with g₀ g₁ g₂
--     all_goals (try simp; try tauto)
--     obtain ⟨A,hA⟩ := g₀
--     sorry
--     sorry
--     sorry
-- }

-- noncomputable def α : MeasureTheory.ProbabilityMeasure (Fin 2 → Bool) := {
--   val := MeasureTheory.Measure.pi (fun _ => β)
--   property := by apply Measure.pi.instIsProbabilityMeasure
-- }

-- example : α {![true,true]} = (1/2) * (1/2) := by
--   unfold α β faircoin
--   simp
--   sorry

example : μ {true} = 1/2 := by
  simp [μ, fairCoin]

/-- As a first steps towards understanding σ-algebras in Lean,
and thereby indepdendence of random variables,
we characterize the σ-algebra σ₀ above. -/
lemma what_is_σ (A : Set (Fin 2 → Bool)) (i : Fin 2) (hA : (σ i).MeasurableSet' A) : A = ∅ ∨
    A = {x | x i = true}
  ∨ A = {x | x i = false} ∨ A = Set.univ := by
  have ⟨s',hs'⟩  : ∃ s', MeasurableSet s' ∧ (fun v => v i) ⁻¹' s' = A := hA
  by_cases hf : false ∈ s'
  · by_cases ht : true ∈ s'
    · right;right;right
      have : s' = Set.univ := by
        ext b
        cases b <;> tauto
      rw [this] at hs'
      simp only [Bool.univ_eq, MeasurableSpace.measurableSet_top, true_and] at hs'
      rw [← hs']
      simp
    · right;right;left
      have : s' = {false} := by
        ext b
        cases b <;> tauto
      rw [this] at hs'
      simp only [MeasurableSpace.measurableSet_top, true_and] at hs'
      rw [← hs']
      rfl
  · by_cases ht : true ∈ s'
    · right;left
      have : s' = {true} := by
        ext b
        cases b <;> tauto
      rw [this] at hs'
      simp only [MeasurableSpace.measurableSet_top, true_and] at hs'
      rw [← hs']
      rfl
    · left
      have : s' = {} := by
        ext b
        cases b <;> tauto
      rw [this] at hs'
      simp only [MeasurableSpace.measurableSet_top, Set.preimage_empty, true_and] at hs'
      rw [← hs']


theorem prob_μ' : μ' Set.univ = 1 := by
    unfold μ' μ
    simp


/-- shows ν is a probability measure in fact -/
theorem prob_ν : ν Set.univ = 1 := by
  have : Set.univ = {![false, false]} ∪ {![false, true]}
                   ∪ {![true, false]} ∪ {![true, true]} := by
    ext v;simp only [
      Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_univ, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_iff]
    by_cases h₀ : v 0 = true
    · by_cases h₁ : v 1 = true
      · left; ext i;fin_cases i <;> tauto
      · right;left
        have : v 1 = false := eq_false_of_ne_true h₁
        ext i;fin_cases i <;> tauto
    · have : v 0 = false := eq_false_of_ne_true h₀
      by_cases h₁ : v 1 = true
      · right;right;left
        ext i;fin_cases i <;> tauto
      · have : v 1 = false := eq_false_of_ne_true h₁
        right;right;right
        ext i;fin_cases i <;> tauto
  rw [this]
  repeat rw [measure_union₀, basic_ν]
  · rw [basic_ν]
    simp only [one_div]
    have : (2:ENNReal)⁻¹ * 2⁻¹ = (2*2)⁻¹ := by
      refine
        Eq.symm (ENNReal.mul_inv ?_ ?_)
      · simp
      · simp
    rw [this]
    have : (2:ENNReal) * 2 = 4 := by ring_nf
    rw [this]
    ring_nf
    refine ENNReal.inv_mul_cancel ?_ ?_ <;> simp
  all_goals (try simp only [
    Nat.succ_eq_add_one, Nat.reduceAdd, MeasurableSet.singleton, MeasurableSet.nullMeasurableSet,
    Set.union_singleton]; try refine Disjoint.aedisjoint ?_; simp)


lemma what_is_σ₀_not (A : Set (Fin 2 → Bool)) (hA : (σ 0).MeasurableSet' A) :
    A ≠ {![false,false]} :=
    by
  intro hc
  have := what_is_σ A 0 hA
  rw [hc] at this
  revert this
  simp only [
    Nat.succ_eq_add_one, Nat.reduceAdd, Set.singleton_ne_empty, Fin.isValue, Set.singleton_ne_univ,
    or_false, false_or, imp_false, not_or]
  constructor
  · intro hc
    have : ![true,true] ∈ {x | x 0 = true} := by simp
    rw [← hc] at this
    simp at this
  · intro hc
    have : ![false,true] ∈ {x | x 0 = false} := by simp
    rw [← hc] at this
    simp at this


/-- August 21, 2025
Existenc eof `n` independent real variables, e.g.,
`m = gaussianReal 0 1`.
-/
lemma realIndependenceGENERAL {n : ℕ} (m : Measure ℝ) [IsProbabilityMeasure m] :
    ProbabilityTheory.iIndepFun
    (fun (i : Fin n) (v : Fin n → ℝ) => v i)
    (μ := MeasureTheory.Measure.pi (fun _ => m)) := by
    have := @ProbabilityTheory.iIndepFun_pi (Fin n) _ (fun _ => ℝ) (by
        intro i
        simp only
        exact measurableSpace) (fun _ => m) (fun _ => (by (expose_names; exact inst)))
            (fun _ => ℝ) _ (by intro i r;exact r) (by
                intro i;simp only;exact aemeasurable_id')
    exact this
    -- rw [ProbabilityTheory.iIndepFun_iff]
    -- intro t T h
    -- have h₀ : ∀ i ∈ t, ∃ s,  MeasurableSet s ∧ (fun v ↦ v i) ⁻¹' s = T i := h
    -- let ⟨S,hS⟩ : ∃ S : t → Set ℝ, ∀ i, ∀ (hi : i ∈ t),
    --     MeasurableSet (S ⟨i,hi⟩) ∧ (fun v ↦ v i) ⁻¹' (S ⟨i,hi⟩) = T i := by
    --     have := (@skolem t (fun _ => Set ℝ) (fun i => by
    --         intro s
    --         exact MeasurableSet s ∧ (fun v ↦ v i) ⁻¹' s = T i)).mp
    --     obtain ⟨a,ha⟩ := this (fun i => h₀ i i.2)
    --     simp at a ha
    --     use a
    -- have : ⋂ i ∈ t, T i = ⋂ i ∈ t, (fun v ↦ v i) ⁻¹' (S ⟨i,by tauto⟩) := by
    --     simp_rw [hS]
    -- rw [this]
    -- let inv (i : Fin n) (A : Set ℝ) := (@Function.eval (Fin n) (fun _ => ℝ) i) ⁻¹' A
    -- have h₁ (i : Fin n) (A : Set ℝ) (h₀ : NullMeasurableSet A m) (h :  m A ≠ ⊤) :
    --     Measure.pi (fun i : Fin n => m) (inv i A) = m A := by
    --     unfold inv
    --     refine MeasurePreserving.measure_preimage ?_ ?_
    --     exact measurePreserving_eval (fun i ↦ m) i
    --     tauto
    -- unfold inv at q
    -- simp at q ⊢
    -- have : ∀ (a : Fin n) (b : a ∈ t), (Function.eval a ⁻¹' S ⟨a, b⟩)
    --     = {v : Fin n → ℝ | v a ∈ S ⟨a,b⟩} := by
    --   intro i hi
    --   ext v
    --   simp
    -- simp_rw [this]
    -- have pp := MeasureTheory.Measure.pi_pi (fun (_ : Fin n) => m) (by
    --     intro i
    --     by_cases H : i ∈ t
    --     exact S ⟨i,H⟩
    --     exact Set.univ)
    -- simp only at pp
    -- convert pp using 1
    -- · congr
    --   ext v
    --   simp
    --   constructor
    --   · intro h i
    --     split_ifs with g₀
    --     · simp at h
    --       apply h
    --       tauto
    --     · trivial
    --   · intro h
    --     intro i hi
    --     specialize h i
    --     rw [dif_pos hi] at h
    --     exact h
    -- ·   have : (fun i : Fin n => m (if H : i ∈ t then S ⟨i, H⟩ else Set.univ)) =
    --         (fun i => if H : i ∈ t then m (S ⟨i,H⟩) else 1) := by
    --         ext i
    --         split_ifs <;> simp
    --     simp_rw [this]

    --     have :  (∏ i : Fin n, if H : i ∈ t then m (S ⟨i, H⟩) else 1)
    --            = ∏ i ∈ t, m ((fun v => v i) '' (T i)) := by
    --       sorry
    --     rw [this]

    --     have :  ∏ i ∈ t, (Measure.pi fun x ↦ m) (T i)
    --           = ∏ i ∈ t, m ((fun v => v i) '' (T i)) := by


    --         sorry
    --     rw [this]


/-  pepperoni; sausage; pineapple
    boston special
-/
/-- Using this we can construct the t distribution with 1 df
and state its Behrens-Fisher-like property.
-/
lemma realIndependence (m : Measure ℝ) [IsProbabilityMeasure m] :
    ProbabilityTheory.IndepFun
    (fun (v : Fin 2 → ℝ) => v 0)
    (fun (v : Fin 2 → ℝ) => v 1)
    (μ := MeasureTheory.Measure.pi (fun _ => m)) := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro t₁ t₂ ⟨s₀,hs₀⟩ ⟨s₁,hs₁⟩
    rw [← hs₀.2, ← hs₁.2]
    let inv (i : Fin 2) (A : Set ℝ) := (@Function.eval (Fin 2) (fun _ => ℝ) i) ⁻¹' A
    have h₀ (i : Fin 2) (A : Set ℝ) (h₀ : NullMeasurableSet A m) (h :  m A ≠ ⊤) :
        Measure.pi (fun i : Fin 2 => m) (inv i A) = m A := by
        unfold inv
        refine MeasurePreserving.measure_preimage ?_ ?_
        · exact measurePreserving_eval (fun i ↦ m) i
        · tauto
    rw [h₀ 0 s₀ (MeasurableSet.nullMeasurableSet hs₀.1) (measure_ne_top m s₀)]
    rw [h₀ 1 s₁ (MeasurableSet.nullMeasurableSet hs₁.1) (measure_ne_top m s₁)]
    have := MeasureTheory.Measure.pi_pi (fun (_ : Fin 2) => m) ![s₀,s₁]
    simp only [Fin.prod_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [← this]
    congr
    ext v
    simp



    -- have : @MeasurableSet (Fin 2 → ℝ) (MeasurableSpace.comap (fun r ↦ r 0)
    -- measurableSpace) {v | v 0 = 1} := by
    --     refine measurableSet_eq_fun ?_ ?_
    --     exact Measurable.of_comap_le fun s a ↦ a
    --     exact measurable_const

--   let X := fun (i : Fin 2) (v : Fin 2 → ℝ) => v i
--   have : MeasureTheory.volume {x : Fin 2 → ℝ | x 0 = 5} = 0 := by
--     sorry
--   let f : (Fin 2 → ℝ) → ℝ := fun r => X 0 r
--   let g : (Fin 2 → ℝ) → ℝ := fun r => X 1 r
--   have : ProbabilityTheory.IndepFun
--       rw [ProbabilityTheory.IndepFun_iff]
--       intro t₁ t₂ ht₁ ht₂
--       -- have : (MeasureTheory.Measure.pi fun i ↦ ProbabilityTheory.gaussianReal 0 1) t₁)
--       --   = ProbabilityTheory.gaussianReal 0 1 (t₁
--       have : @MeasurableSet (Fin 2 → ℝ) (MeasurableSpace.comap (fun r ↦ r 0)
--         measurableSpace) {v | v 0 = 1} := by
--         refine measurableSet_eq_fun ?_ ?_
--         exact Measurable.of_comap_le fun s a ↦ a
--         exact measurable_const
--     --   have (A : Set ℝ)
--     --   (h : @MeasurableSet (ℝ) _ A)
--     --     :  @MeasurableSet (Fin 2 → ℝ) (MeasurableSpace.comap (fun r ↦ r 0)
--     --     measurableSpace) ((fun v : Fin 2 → ℝ => v 0)⁻¹' A) := by
--     --     refine MeasurableSpace.map_def.mp ?_

--     --     sorry
--       simp
--       have : Measure.pi (fun i : Fin 2 ↦ Measure.dirac 0) t₁
--         = Set.indicator t₁ (fun _ => 1) 0 := by
--         by_cases H : 0 ∈ t₁
--         simp [Set.indicator]
--         rw [if_pos H]
--         -- rw [Measure.pi_def]
--         have := @MeasureTheory.Measure.pi_map_eval (Fin 2)
--             (fun _ => ℝ) _ _ (fun _ => ProbabilityTheory.gaussianReal 0 0)
--             (fun i => sigmaFinite_of_locallyFinite) _
--             0
--         simp at this
--         sorry
--         sorry
--       sorry
--   sorry
-- example (X : Fin 2 → (Fin 2 → ℝ) → ℝ)
--   -- [MeasureTheory.MeasureSpace (Fin 2 → ℝ)]
--   -- [OpensMeasurableSpace (Fin 2 → ℝ)]
--   (h : X = fun (i : Fin 2) (v : Fin 2 → ℝ) => v i)
--   -- (μ : MeasureTheory.Measure (Fin 2 → ℝ))
--   -- (hμ : μ Set.univ = 1)
--   (A : Set (Fin 2 → ℝ))
--   (h₀ : MeasurableSet A)
--   (hA : MeasureTheory.volume A = 2)
--   :
--   ¬ ProbabilityTheory.iIndepFun (fun (i : Fin 2) (v : Fin 2 → ℝ) => v i)
--   := by
--   intro hc
--   rw [ProbabilityTheory.iIndepFun_iff] at hc
--   specialize hc Finset.univ
--   exact ![A,A]
--   specialize hc (by
--     intro i _
--     fin_cases i
--     simp

--     -- have := @measurableSet_Icc (Fin 2 → ℝ) _ _
--     sorry
--     simp
--     sorry)
--   simp at hc
--   -- have : MeasureTheory.volume (Set.Icc (0:ℝ) 2⁻¹) = 2⁻¹ := by
--   --   simp
--   --   refine ENNReal.eq_inv_of_mul_eq_one_left ?_
--   --   refine Eq.symm ((fun {x y} hx hy ↦ (ENNReal.toReal_eq_toReal_iff' hx hy).mp) ?_ ?_ ?_)
--   --   simp
--   --   simp
--   --   exact not_eq_of_beq_eq_false rfl
--   --   simp
--   -- simp_rw [this] at hc
--   sorry

-- example (X : Fin 2 → (Fin 2 → ℝ) → ℝ)
--   [MeasureTheory.MeasureSpace (Fin 2 → ℝ)]
--   (h : X = fun (i : Fin 2) (v : Fin 2 → ℝ) => v i)
--   (μ : MeasureTheory.Measure (Fin 2 → ℝ))
--   (hμ : μ Set.univ = 1)
--   :
--   ProbabilityTheory.iIndepFun (fun (i : Fin 2) (v : Fin 2 → ℝ) => v i) μ
--   ∧
--   ProbabilityTheory.iIndepFun (fun (i : Fin 2) (v : Fin 2 → ℝ) => v i)
--   := by
--   constructor
--     intro s f h
--     fin_cases s
--     · simp
--       exact hμ
--     · simp
--     · simp
--     · simp
--       simp at h
--       sorry
--   · sorry

/- The standard error S is SE_xbar (section 4.2) at a particular ω.

 -/
-- example {n : ℕ} {Ω : Type*} (X : Fin n → (Ω → ℝ))
--   [MeasureTheory.MeasureSpace Ω]
--   (μ : MeasureTheory.Measure Ω)
--   (μX : ℝ)
--   (h : ProbabilityTheory.iIndepFun X)
--   -- could it even fail? if Ω is (Fin n → ℝ) and X i v = v i?
--   (T S Xbar : (Fin n → Ω) → ℝ)
--   (hS : ∀ ω, S ω = √((1/(n - 1)) * ∑ i, (X i (ω i) - Xbar ω)^2))
--   (hT : ∀ v, T v = (Xbar v - μX) / ((1 / √n) * S v))
--   (hn : n = 2) :
--   Unit
--   -- T = (1/2) * (X 0 + X 1) * T

--   := by
--   unfold ProbabilityTheory.iIndepFun at h

--   sorry
