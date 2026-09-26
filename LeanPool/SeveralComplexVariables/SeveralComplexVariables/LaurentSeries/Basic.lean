/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.OneVariable
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Polydisc

/-!
# Torus coefficients for Laurent series

Integer-indexed coefficients are defined by integration on a coordinate torus. Their bounds and
their action on monomials do not require a Laurent expansion theorem. Negative powers are
written `z i ^ (-m i - 1)` in the integrand; this is compatible with Lean's totalized integer
powers at zero once the torus avoids the coordinate hyperplanes.

## Main results

`multivariableLaurentCoeff` is the coefficient of multi-index `m` on the torus of radii `r`.
`multivariableLaurentTerm` is the corresponding monomial term.
`norm_multivariableLaurentCoeff_le` is the Cauchy bound. `multivariableLaurentCoeff_monomial`
evaluates the coefficient on a monomial. `multivariableLaurentCoeff_fin_one` recovers the
one-variable `circleLaurentCoeff`.
-/

public noncomputable section

open Complex Set MeasureTheory Metric
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Laurent coefficient obtained by integrating over a positive-radius coordinate torus. -/
@[expose] def multivariableLaurentCoeff (f : (Fin n → ℂ) → F) (r : Fin n → ℝ)
    (m : Fin n → ℤ) : F :=
  ((2 * π * I : ℂ) ^ n)⁻¹ •
    torusIntegral (fun z => (∏ i, z i ^ (-m i - 1)) • f z) 0 r

omit [CompleteSpace F] in
/-- The multivariable circle coefficient in dimension one is the ordinary Laurent coefficient. -/
theorem multivariableLaurentCoeff_fin_one (f : ℂ → F) (r : ℝ) (k : ℤ) :
    multivariableLaurentCoeff (fun z : Fin 1 → ℂ => f (z 0)) (fun _ => r) (fun _ => k) =
      circleLaurentCoeff f r k := by
  simp [multivariableLaurentCoeff, torusIntegral_dim1, circleLaurentCoeff]

/-- An integer-indexed Laurent term. Negative powers at zero are totalized; the expansion theorem
separately forces their coefficients to vanish whenever necessary. -/
@[expose] def multivariableLaurentTerm (c : (Fin n → ℤ) → F) (m : Fin n → ℤ) (z : Fin n → ℂ) : F :=
  (∏ i, z i ^ m i) • c m

omit [CompleteSpace F] in
/-- Cauchy's bound for an integer-indexed torus coefficient. -/
theorem norm_multivariableLaurentCoeff_le {f : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) {M : ℝ} (hM : ∀ θ, ‖f (torusMap 0 r θ)‖ ≤ M)
    (m : Fin n → ℤ) : ‖multivariableLaurentCoeff f r m‖ ≤ M * ∏ i, r i ^ (-m i) := by
  have hker (θ : Fin n → ℝ) : ‖∏ i, torusMap 0 r θ i ^ (-m i - 1)‖ =
      ∏ i, r i ^ (-m i - 1) := by
    simp [norm_prod, norm_zpow, torusMap, abs_of_pos (hr _)]
  rw [multivariableLaurentCoeff, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_torusIntegral_le_of_norm_le_const
    (C := M * ∏ i, r i ^ (-m i - 1)) ?_) (norm_nonneg _)).trans_eq ?_
  · intro θ
    rw [norm_smul, hker]
    exact (mul_le_mul_of_nonneg_left (hM θ)
      (Finset.prod_nonneg fun i _ => zpow_nonneg (hr i).le _)).trans_eq (mul_comm _ _)
  · simp only [norm_inv, norm_pow, norm_mul, norm_ofNat, norm_real, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (hr _)]
    have hp : (∏ i, r i) * (∏ i, r i ^ (-m i - 1)) = ∏ i, r i ^ (-m i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      calc
        r i * r i ^ (-m i - 1) = r i ^ (1 : ℤ) * r i ^ (-m i - 1) := by rw [zpow_one]
        _ = r i ^ (-m i) := by rw [← zpow_add₀ (hr i).ne']; congr 1; omega
    calc
      ((2 * π) ^ n)⁻¹ * (((2 * π) ^ n * ∏ i, r i) * (M * ∏ i, r i ^ (-m i - 1))) =
          M * ((∏ i, r i) * ∏ i, r i ^ (-m i - 1)) := by field_simp
      _ = _ := by rw [hp]

/-- A product of scalar functions separates into a product of circle integrals. -/
theorem torusIntegral_prod (g : Fin n → ℂ → ℂ) (r : Fin n → ℝ) :
    torusIntegral (fun z => ∏ i, g i (z i)) 0 r =
      ∏ i, ∮ w in C(0, r i), g i w := by
  have hbox : Icc (0 : Fin n → ℝ) (fun _ => 2 * π) =
      Set.pi univ (fun _ : Fin n => Icc (0 : ℝ) (2 * π)) := by ext θ; simp [Set.mem_Icc, Pi.le_def]
  simp only [torusIntegral, smul_eq_mul, ← Finset.prod_mul_distrib]
  simp only [torusMap, Pi.zero_apply, zero_add]
  rw [hbox, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun i (θ : ℝ) => (r i : ℂ) * exp (θ * I) * I * g i ((r i : ℂ) * exp (θ * I)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [circleIntegral_def_Icc]
  congr 1
  funext θ
  simp [circleMap, deriv_circleMap]

/-- Integer monomials have zero torus integral unless every exponent is `-1`. -/
theorem torusIntegral_zpow_prod (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (m : Fin n → ℤ) :
    torusIntegral (fun z => ∏ i, z i ^ m i) 0 r =
      ∏ i, if m i = -1 then (2 * π * I : ℂ) else 0 := by
  rw [torusIntegral_prod (fun i w => w ^ m i)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : m i = -1
  · simp only [hi, ite_true, zpow_neg_one]
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self (x := (0 : ℂ)) (hr i))
  · simp only [hi, ite_false]
    simpa using circleIntegral.integral_sub_zpow_of_ne hi 0 0 (r i)

omit [CompleteSpace F] in
/-- Torus integrals depend only on values on the parametrized torus. -/
theorem torusIntegral_congr {f g : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (h : ∀ θ, f (torusMap 0 r θ) = g (torusMap 0 r θ)) :
    torusIntegral f 0 r = torusIntegral g 0 r := by
  unfold torusIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => congrArg (_ • ·) (h θ)

/-- A constant vector can be taken outside a scalar torus integral. -/
theorem torusIntegral_smul_const (f : (Fin n → ℂ) → ℂ) (r : Fin n → ℝ) (v : F) :
    torusIntegral (fun z => f z • v) 0 r = torusIntegral f 0 r • v := by
  simp only [torusIntegral, ← smul_assoc, integral_smul_const]

/-- A Laurent monomial has exactly its prescribed coefficient on every positive torus. -/
theorem multivariableLaurentCoeff_monomial (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (k m : Fin n → ℤ) (v : F) :
    multivariableLaurentCoeff (fun z => (∏ i, z i ^ k i) • v) r m =
      if m = k then v else 0 := by
  classical
  have he : torusIntegral (fun z => (∏ i, z i ^ (-m i - 1)) • ((∏ i, z i ^ k i) • v)) 0 r =
      torusIntegral (fun z => (∏ i, z i ^ (k i - m i - 1)) • v) 0 r := by
    apply torusIntegral_congr
    intro θ
    rw [smul_smul, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have hi : torusMap 0 r θ i ≠ 0 := by simp [torusMap, (hr i).ne']
    rw [← zpow_add₀ hi]
    congr 1
    omega
  rw [multivariableLaurentCoeff, he, torusIntegral_smul_const, torusIntegral_zpow_prod r hr]
  by_cases hmk : m = k
  · subst m
    simp only [sub_self, zero_sub, ite_true, Fin.prod_const]
    exact inv_smul_smul₀ (pow_ne_zero _ two_pi_I_ne_zero) v
  · rw [ite_eq_right hmk]
    have hi : ∃ i, m i ≠ k i := Function.ne_iff.mp hmk
    obtain ⟨i, hi⟩ := hi
    have hp : (∏ i, if k i - m i - 1 = -1 then (2 * π * I : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right (by omega)]
    rw [hp, zero_smul, smul_zero]

omit [CompleteSpace F] in
/-- Multiplying by an integer monomial preserves continuity along a positive torus. -/
theorem continuous_laurentMonomial_smul_torus {f : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hf : Continuous (fun θ => f (torusMap 0 r θ))) (m : Fin n → ℤ) :
    Continuous (fun θ => (∏ i, torusMap 0 r θ i ^ m i) • f (torusMap 0 r θ)) := by
  apply Continuous.smul _ hf
  apply continuous_finsetProd
  intro i _
  exact ((continuous_apply i).comp (continuous_torusMap 0 r)).zpow₀ _
    (fun θ => Or.inl (by simp [torusMap, (hr i).ne']))

omit [CompleteSpace F] in
/-- A continuous function on a positive torus has integrable Laurent kernels. -/
theorem torusIntegrable_laurentKernel {f : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hf : Continuous (fun θ => f (torusMap 0 r θ))) (m : Fin n → ℤ) :
    TorusIntegrable (fun z => (∏ i, z i ^ (-m i - 1)) • f z) 0 r :=
  ((continuous_laurentMonomial_smul_torus hr hf (fun i => -m i -
    1)).continuousOn).integrableOn_compact
    isCompact_Icc

omit [CompleteSpace F] in
/-- Laurent coefficients commute with finite sums of functions continuous on the torus. -/
theorem multivariableLaurentCoeff_sum {α : Type*} (s : Finset α)
    {f : α → (Fin n → ℂ) → F} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hf : ∀ a ∈ s, Continuous (fun θ => f a (torusMap 0 r θ))) (m : Fin n → ℤ) :
    multivariableLaurentCoeff (fun z => ∑ a ∈ s, f a z) r m =
      ∑ a ∈ s, multivariableLaurentCoeff (f a) r m := by
  simp only [multivariableLaurentCoeff, torusIntegral, Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.smul_sum
  · intro a ha
    exact (torusIntegrable_laurentKernel hr (hf a ha) m).function_integrable

omit [CompleteSpace F] in
/-- Laurent coefficients commute with subtraction for functions continuous on the torus. -/
theorem multivariableLaurentCoeff_sub {f g : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hf : Continuous (fun θ => f (torusMap 0 r θ)))
    (hg : Continuous (fun θ => g (torusMap 0 r θ))) (m : Fin n → ℤ) :
    multivariableLaurentCoeff (fun z => f z - g z) r m =
      multivariableLaurentCoeff f r m - multivariableLaurentCoeff g r m := by
  simp only [multivariableLaurentCoeff, smul_sub]
  rw [torusIntegral_sub (torusIntegrable_laurentKernel hr hf m)
    (torusIntegrable_laurentKernel hr hg m), smul_sub]

omit [CompleteSpace F] in
/-- Laurent coefficients depend only on values on their coefficient torus. -/
theorem multivariableLaurentCoeff_congr {f g : (Fin n → ℂ) → F} {r : Fin n → ℝ}
    (h : ∀ θ, f (torusMap 0 r θ) = g (torusMap 0 r θ)) :
    multivariableLaurentCoeff f r = multivariableLaurentCoeff g r := by
  funext m
  unfold multivariableLaurentCoeff
  congr 1
  exact torusIntegral_congr fun θ => congrArg (_ • ·) (h θ)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
