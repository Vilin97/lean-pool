/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import LeanPool.IsTranscendentalPi.IncrementalDerivatives
import LeanPool.IsTranscendentalPi.SymmetricPolynomials

/-!
# The complex exponential and subset sums

Properties of `t ↦ exp(-(t · x))` and the expansion of `∏ (1 + exp x)` over a
multiset of roots into zero- and nonzero-sum subset contributions, the analytic
heart of Niven's proof of the transcendence of `π`.
-/

open Polynomial

open Set
open Multiset
open Complex

open scoped Polynomial
open scoped BigOperators

local notation "rexp" => Real.exp
local notation "π" => Real.pi

noncomputable section

/-- For `x ∈ ℂ`, one has `exp(x) * exp(-x) = 1`. -/
lemma cexp_mul_cexp_neg (x : ℂ) : cexp x * cexp (-x) = 1 := by
  rw [Complex.exp_neg, mul_inv_cancel₀ (Complex.exp_ne_zero x)]

/-- For `x ∈ ℂ`, the map `t ↦ exp(-(t * x))` is continuous on `[0, 1]` at `t`. -/
lemma continuousWithinAt_exp_neg_mul (x : ℂ) (t : ℝ) :
  ContinuousWithinAt (fun t : ℝ => cexp (-(t * x))) (uIcc (0:ℝ) 1) t :=
  (differentiableAt_exp_neg_mul x t).continuousAt.continuousWithinAt

/-- For `t ∈ ℝ` and `x ∈ ℂ`, it holds that `d/dt exp(-(t * x)) = -x * exp(-(t * x))`. -/
lemma deriv_exp_neg_mul_real (x : ℂ) (t : ℝ) :
  deriv (fun t : ℝ => cexp ( -(t * x) )) t = (-x * cexp ( -(t * x) )) := by
  simpa [mul_comm] using (((hasDerivAt_mul_const x).neg.cexp.comp_ofReal : HasDerivAt
    (fun t : ℝ => cexp (-((t : ℂ) * x))) (cexp (-((t : ℂ) * x)) * -x) t).deriv)

/-- For `a ∈ ℂ` and `t ∈ [0, 1]`, one has `‖exp(-(t * a))‖ ≤ exp(‖a‖)`. -/
lemma norm_cexp_neg_mul_le_exp_norm (a : ℂ) :
  ∀ t ∈ uIcc (0 : ℝ) 1, ‖cexp (-(t * a))‖ ≤ rexp ‖a‖ := by
  intro t ht
  have habs : |t| ≤ 1 := by
    simpa using (abs_sub_left_of_mem_uIcc (a := (0 : ℝ)) (b := 1) (c := t) ht)
  have hnorm : ‖(t : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using habs
  calc
    ‖cexp (-(t * a))‖ ≤ rexp ‖-(t * a)‖ := by
      simpa using Complex.norm_exp_le_exp_norm (-(t * a))
    _ = rexp ‖(t : ℂ) * a‖ := by simp
    _ = rexp (‖(t : ℂ)‖ * ‖a‖) := by simp
    _ ≤ rexp (1 * ‖a‖) := by gcongr
    _ = rexp ‖a‖ := by simp

/-- If `P(π i) = 0` and `P ≠ 0`, then `∏_{x ∈ roots(P)} (1 + e^x) = 0`. -/
lemma prod_one_add_cexp_aroots_eq_zero
    (P : ℚ[X]) (hP : P ≠ 0) (hroot : aeval (π * I) P = 0) :
    (map (fun x : ℂ => 1 + cexp x) (P.aroots ℂ)).prod = 0 := by
  have hIpi_mem : π * I ∈ P.aroots ℂ :=
    (Polynomial.mem_aroots (p := P) (a := π * I)).2 ⟨hP, hroot⟩
  have hfactor_zero : 1 + cexp (π * I) = 0 := by simp [Complex.exp_pi_mul_I]
  exact prod_eq_zero_iff.2 (mem_map.2 ⟨π * I, hIpi_mem, hfactor_zero⟩)

/-- The map `t ↦ e^(∑_{x ∈ t} x)` on multisets of complex numbers. -/
def cexpMultisetSum : Multiset ℂ → ℂ := fun t ↦ cexp t.sum

/-- The submultisets `t ⊆ s` with `∑_{x ∈ t} x = 0`. -/
def zeroSumPowerset (s : Multiset ℂ) : Multiset (Multiset ℂ) :=
  s.powerset.filter (·.sum = 0)

/-- The submultisets `t ⊆ s` with `∑_{x ∈ t} x ≠ 0`. -/
def nonZeroSumPowerset (s : Multiset ℂ) : Multiset (Multiset ℂ) :=
  s.powerset.filter (·.sum ≠ 0)

/-- The sum `∑_{t ⊆ s} e^(∑_{x ∈ t} x)` splits into the zero-sum and nonzero-sum parts. -/
lemma sum_cexp_powerset_split (s : Multiset ℂ) :
    (map cexpMultisetSum s.powerset).sum =
      (map cexpMultisetSum (zeroSumPowerset s)).sum +
        (map cexpMultisetSum (nonZeroSumPowerset s)).sum := by
  rw [← filter_add_not (s := s.powerset) (p := fun t : Multiset ℂ => t.sum = 0)]
  simp [zeroSumPowerset, nonZeroSumPowerset, Multiset.map_add, Multiset.sum_add]

/-- The product `∏_{x ∈ s} (1 + e^x)` equals to
`∑_{t ⊆ s, ∑_{y ∈ t} y = 0} e^(∑_{y ∈ t} y) + ∑_{t ⊆ s, ∑_{y ∈ t} y ≠ 0} e^(∑_{y ∈ t} y)`. -/
lemma prod_one_add_cexp_split (s : Multiset ℂ) :
    (map (fun x : ℂ => 1 + cexp x) s).prod =
      (map cexpMultisetSum (zeroSumPowerset s)).sum +
        (map cexpMultisetSum (nonZeroSumPowerset s)).sum := by
  rw [prod_map_add, antidiagonal_eq_map_powerset]
  simpa [cexpMultisetSum, Complex.exp_multiset_sum] using sum_cexp_powerset_split s

/-- The multiset of all subset sums of `s`, i.e. `{ ∑_{x ∈ t} x | t ⊆ s }`. -/
def subsetSums {α : Type*} [AddCommMonoid α] (s : Multiset α) : Multiset α :=
  (s.powerset).map sum

/-- The multiset of all nonzero subset sums of `s`, i.e. `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`. -/
def nonzeroSubsetSums {α : Type*} [AddCommMonoid α] [DecidableEq α] (s : Multiset α) :
    Multiset α := (subsetSums s).filter (· ≠ 0)

/-- Every element of `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }` is nonzero. -/
lemma ne_zero_of_mem_nonzeroSubsetSums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {s : Multiset α} {x : α} (hx : x ∈ nonzeroSubsetSums s) : x ≠ 0 := by
  simpa [nonzeroSubsetSums] using (Multiset.mem_filter.1 hx).2

/-- If `x ∈ s` and `x ≠ 0`, then `x ∈ { ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`. -/
lemma mem_nonzeroSubsetSums_of_mem_of_ne_zero {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {s : Multiset α} {x : α} (hx : x ∈ s) (hx0 : x ≠ 0) :
    x ∈ nonzeroSubsetSums s := by
  rw [nonzeroSubsetSums, subsetSums]
  exact Multiset.mem_filter.2
    ⟨Multiset.mem_map.2 ⟨{x}, Multiset.mem_powerset.2 (by simpa using hx), by simp⟩, hx0⟩

/-- If `t ⊆ s` and `∑_{x ∈ t} x = 0`, then `e^(∑_{x ∈ t} x) = 1`. -/
lemma cexpMultisetSum_eq_one_of_mem_zeroSumPowerset {s t : Multiset ℂ}
    (ht : t ∈ zeroSumPowerset s) : cexpMultisetSum t = 1 := by
  have ht0 : t.sum = 0 := by
    simp only [zeroSumPowerset, mem_filter, Multiset.mem_powerset] at ht
    exact ht.2
  rw [cexpMultisetSum, ht0, Complex.exp_zero]

/-- Applying `t ↦ e^(∑_{x ∈ t} x)` to all `t ⊆ s` with `∑_{x ∈ t} x = 0` gives only `1`s. -/
lemma map_cexpMultisetSum_zeroSumPowerset_eq_replicate (s : Multiset ℂ) :
    map cexpMultisetSum (zeroSumPowerset s) =
      Multiset.replicate (card (zeroSumPowerset s)) (1 : ℂ) := by
  simpa using (Multiset.eq_replicate_of_mem
    (s := map cexpMultisetSum (zeroSumPowerset s)) (a := (1 : ℂ))
    (by
      intro z hz
      rcases mem_map.1 hz with ⟨t, ht, rfl⟩
      exact cexpMultisetSum_eq_one_of_mem_zeroSumPowerset ht))

/-- The sum `∑_{t ⊆ s, ∑_{x ∈ t} x = 0} e^(∑_{x ∈ t} x)` equals
`#{t ⊆ s | ∑_{x ∈ t} x = 0}`. -/
lemma sum_cexp_zeroSumPowerset_eq_count_zero_subsetSums (s : Multiset ℂ) :
    (map cexpMultisetSum (zeroSumPowerset s)).sum = (((subsetSums s).count 0 : ℤ) : ℂ) := by
  rw [map_cexpMultisetSum_zeroSumPowerset_eq_replicate, Multiset.sum_replicate]
  simp [eq_comm, count_eq_card_filter_eq, subsetSums, zeroSumPowerset, filter_map, Function.comp]

/-- If `B(π i) = 0` and `roots(B)` is the multiset of roots of `B`, then
`∑_{t ⊆ roots(B), ∑_{x ∈ t} x ≠ 0} e^(∑_{x ∈ t} x) = -#{t ⊆ roots(B) | ∑_{x ∈ t} x = 0}`. -/
lemma sum_cexp_subsetSums_aroots_filter_ne_zero_eq_neg_count_zero
    (B : ℚ[X]) (hB : B ≠ 0) (hroot : aeval (π * I) B = 0) :
    (map cexp (nonzeroSubsetSums (B.aroots ℂ))).sum =
      -(((subsetSums (B.aroots ℂ)).count 0) : ℂ) := by
  have hprod : (map (fun x : ℂ => 1 + cexp x) (B.aroots ℂ)).prod = 0 := by
    exact prod_one_add_cexp_aroots_eq_zero B hB hroot
  rw [prod_one_add_cexp_split (s := B.aroots ℂ)] at hprod
  have hzero := sum_cexp_zeroSumPowerset_eq_count_zero_subsetSums (B.aroots ℂ)
  rw [hzero] at hprod
  exact eq_neg_of_add_eq_zero_right <| by
    simpa [nonzeroSubsetSums, subsetSums, nonZeroSumPowerset, cexpMultisetSum, filter_map,
      Function.comp] using hprod

/-- If `f⁽ᵏ⁾` is differentiable at `t * x` for every `k ≤ n` and every `t ∈ [0, 1]`, then
`t ↦ exp(-t * x) *  ( f⁽ⁿ⁾(t * x) - f(t * x) )` is continuous on `[0, 1]`. -/
lemma continuousOn_exp_neg_mul_iteratedDeriv_sub
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ)
  (hderiv : ∀ k ≤ n, ∀ t ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    ContinuousOn (fun t : ℝ => x * cexp (-(t * x)) * (iteratedDeriv n f (t * x) - f (t * x)))
      (Set.uIcc (0 : ℝ) 1) := by
  intro t ht
  exact
    (continuousWithinAt_const.mul (continuousWithinAt_exp_neg_mul x t)).mul
      ((continuousWithinAt_iteratedDeriv_comp_mul f x n t (hderiv n le_rfl t ht)).sub
        (continuousWithinAt_iteratedDeriv_comp_mul f x 0 t (hderiv 0 (Nat.zero_le _) t ht)))

/-- If `f⁽ᵏ⁾` is differentiable at `t x` for every `k ≤ n`, then
`t ↦ exp(-t * x) *  ∑ₖ₌₀ⁿ⁺¹ f⁽ᵏ⁾(t * x)` is differentiable at `t`. -/
lemma differentiableAt_exp_neg_mul_sum_iteratedDeriv
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : ∀ k ≤ n, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    DifferentiableAt ℝ (fun t : ℝ => cexp (-(t * x)) *
          ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) t :=
  (differentiableAt_exp_neg_mul x t).fun_mul
    (differentiableAt_sum_iteratedDeriv f x n t hderiv)

/-- If `f⁽ᵏ⁾` is differentiable at `t x` for every `k ≤ n`, then with hasDeriv we have
`d/dt (exp(-t * x) *  ∑ₖ₌₀ⁿ⁺¹ f⁽ᵏ⁾(t * x)) = x * exp(- t * x) * (f⁽ⁿ⁺¹⁾(t * x) - f(t * x))`. -/
lemma deriv_exp_neg_mul_sum_iteratedDeriv
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : ∀ k ≤ n, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
  deriv (fun t : ℝ => cexp (-(t * x)) * ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) t
    = x * cexp (-(t * x)) * (iteratedDeriv (n + 1) f (t * x) - f (t * x)) := by
  calc
    _ = deriv (fun t : ℝ => cexp (-(t * x))) t *
          (∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) + cexp (-(t * x)) *
            deriv (fun t : ℝ => ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) t := by
          simpa using (deriv_fun_mul (differentiableAt_exp_neg_mul x t)
                        (differentiableAt_sum_iteratedDeriv f x n t hderiv))
    _ = (-x * cexp (-(t * x))) * (∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) +
          cexp (-(t * x)) * (∑ k ∈ Finset.range (n + 1), x * iteratedDeriv (k + 1) f (t * x)) := by
          rw [deriv_exp_neg_mul_real, sum_deriv_iteratedDeriv_comp_mul f x n t hderiv]
    _ = (-x * cexp (-(t * x))) * (∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x)) +
          cexp (-(t * x)) * (x * ∑ k ∈ Finset.range (n + 1), iteratedDeriv (k + 1) f (t * x)) := by
          rw [← Finset.mul_sum]
    _ = x * cexp (-(t * x)) * (iteratedDeriv (n + 1) f (t * x) - f (t * x)) := by
          rw [Finset.sum_range_succ', Finset.sum_range_succ]
          simp
          ring

/-- If `f⁽ᵏ⁾` is differentiable at `t x` for every `k ≤ n`, then with deriv we have
`d/dt (exp(-t * x) *  ∑ₖ₌₀ⁿ⁺¹ f⁽ᵏ⁾(t * x)) = x * exp(- t * x) * (f⁽ⁿ⁺¹⁾(t * x) - f(t * x))`. -/
lemma hasDerivAt_exp_neg_mul_sum_iteratedDeriv
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ) (t : ℝ)
  (hderiv : ∀ k ≤ n, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    HasDerivAt (fun t : ℝ => cexp (-(t * x)) *
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x))
      (x * cexp (-(t * x)) * (iteratedDeriv (n + 1) f (t * x) - f (t * x))) t := by
  simpa [deriv_exp_neg_mul_sum_iteratedDeriv f x n t hderiv] using
      (differentiableAt_exp_neg_mul_sum_iteratedDeriv f x n t hderiv).hasDerivAt

/-- If `f⁽ᵏ⁾` is differentiable at `t x` for every `k ≤ n + 1` and every `t ∈ [0, 1]`, then
`∫₀¹ x * exp(-t x) * (f⁽ⁿ⁺¹⁾(t x) - f(t x)) dt = exp(- x) * ∑ₖ₌₀ⁿ f⁽ᵏ⁾(x) - ∑ₖ₌₀ⁿ f⁽ᵏ⁾(0)`. -/
lemma int_exp_neg_mul_fun
  (f : ℂ → ℂ) (x : ℂ) (n : ℕ)
  (hderiv : ∀ k ≤ n + 1, ∀ t ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℂ (iteratedDeriv k f) (t * x)) :
    ∫ t in 0..1, (fun (t : ℝ) ↦ x * cexp (-(t * x)) *
      (iteratedDeriv (n + 1) f (t * x) - f (t * x))) t
      = cexp (-x) * ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x
        - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f 0 := by
  simpa using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := 1)
      (f := fun t : ℝ =>
        cexp (-(t * x)) *
          ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f (t * x))
      (f' := fun t : ℝ =>
        x * cexp (-(t * x)) *
          (iteratedDeriv (n + 1) f (t * x) - f (t * x)))
      (fun t ht =>
        hasDerivAt_exp_neg_mul_sum_iteratedDeriv f x n t
          (fun k hk => hderiv k (Nat.le_trans hk (Nat.le_succ n)) t ht))
      ((continuousOn_exp_neg_mul_iteratedDeriv_sub f x (n + 1)
          (fun k hk t ht => hderiv k hk t ht)).intervalIntegrable)

/-- If `a₀, …, aₙ₋₁` enumerate the nonzero subset sums of the roots of `B`
and `bᵢ = 1` for all `i`, then `∑ᵢ bᵢ exp(aᵢ) = -k`. -/
lemma sum_weighted_cexp_nonzeroSubsetSums_eq_neg_count_zero_subsetSums {n : ℕ}
  (B : ℚ[X]) (hB : B ≠ 0) (hroot : aeval (Real.pi * I) B = 0)
  (a : Fin n → ℂ) (ha : nonzeroSubsetSums (B.aroots ℂ) = valuesFin a)
  (b : Fin n → ℂ) (hb : ∀ i : Fin n, b i = 1)
  (k : ℕ) (hk : k = (subsetSums (B.aroots ℂ)).count 0) :
    ∑ i : Fin n, b i * cexp (a i) = -k := by
  simpa [hk, ha, valuesFin, hb, Fin.sum_ofFn, Function.comp_apply] using
    (sum_cexp_subsetSums_aroots_filter_ne_zero_eq_neg_count_zero B hB hroot)
