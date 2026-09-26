/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Sobolev spaces on the torus — definitions

This file defines the weighted ℓ² spaces ℓ²_(s)(ℤⁿ) and the Fourier
exponential functions eₘ.

## Main definitions

* `NashEmbedding.Sobolev.weight n s m` — the weight `(1 + |m|²)^s` for `m : Fin n → ℤ`
* `NashEmbedding.Sobolev.memSobolev n s a` — membership in ℓ²_(s)(ℤⁿ)
* `NashEmbedding.Sobolev.sobolevNormSq n s a` — the squared norm `‖a‖²_(s)`
* `NashEmbedding.Sobolev.fourierExp n m θ` — the exponential `eₘ(θ)`
-/

@[expose] public section

open scoped BigOperators ComplexConjugate ContDiff
open Complex Real

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Weight function -/

/-- The weight function `(1 + |m|²)^s` for `m : Fin n → ℤ`. Here `|m|²` is the
sum of squares of coordinates, viewed as real numbers. -/
def weight (n : ℕ) (s : ℝ) (m : Fin n → ℤ) : ℝ :=
  (1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) ^ s

lemma weight_pos (s : ℝ) (m : Fin n → ℤ) : 0 < weight n s m := by
  exact Real.rpow_pos_of_pos ( add_pos_of_pos_of_nonneg zero_lt_one ( Finset.sum_nonneg fun _ _
      => sq_nonneg _ ) ) _

lemma weight_nonneg (s : ℝ) (m : Fin n → ℤ) : 0 ≤ weight n s m :=
  le_of_lt (weight_pos s m)

/-
The base of the weight is always ≥ 1.
-/
lemma one_le_weight_base (m : Fin n → ℤ) :
    1 ≤ 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) := by
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
`weight n 0 m = 1` for all `m`.
-/
lemma weight_zero (m : Fin n → ℤ) : weight n 0 m = 1 := by
  unfold weight; norm_num;

/-
`weight n s m * weight n t m = weight n (s + t) m`.
-/
lemma weight_mul (s t : ℝ) (m : Fin n → ℤ) :
    weight n s m * weight n t m = weight n (s + t) m := by
  unfold weight;
  rw [ Real.rpow_add ( by exact add_pos_of_pos_of_nonneg zero_lt_one ( Finset.sum_nonneg fun _ _
      => sq_nonneg _ ) ) ]

/-
For `s ≤ t`, `weight n s m ≤ weight n t m`.
-/
lemma weight_mono {s t : ℝ} (hst : s ≤ t) (m : Fin n → ℤ) :
    weight n s m ≤ weight n t m := by
  exact Real.rpow_le_rpow_of_exponent_le ( one_le_weight_base m ) hst

/-
For `s ≤ 0`, `weight n s m ≤ 1`.
-/
lemma weight_le_one_of_nonpos {s : ℝ} (hs : s ≤ 0) (m : Fin n → ℤ) :
    weight n s m ≤ 1 := by
  exact le_trans ( weight_mono hs m ) ( by norm_num [ weight_zero ] )

/-! ## Membership in the Sobolev space -/

/-- A sequence `a : (Fin n → ℤ) → ℂ` belongs to `ℓ²_(s)(ℤⁿ)` iff
`∑ₘ (1 + |m|²)^s |aₘ|² < ∞`. -/
def MemSobolev (n : ℕ) (s : ℝ) (a : (Fin n → ℤ) → ℂ) : Prop :=
  Summable (fun m => weight n s m * ‖a m‖ ^ 2)

/-- The squared Sobolev norm `‖a‖²_(s) = ∑ₘ (1 + |m|²)^s |aₘ|²`. -/
def sobolevNormSq (n : ℕ) (s : ℝ) (a : (Fin n → ℤ) → ℂ) : ℝ :=
  ∑' m, weight n s m * ‖a m‖ ^ 2

/-- The Sobolev inner product `⟨a, b⟩_(s) = ∑ₘ (1 + |m|²)^s conj(aₘ) bₘ`. -/
def sobolevInner (n : ℕ) (s : ℝ) (a b : (Fin n → ℤ) → ℂ) : ℂ :=
  ∑' m, (weight n s m : ℂ) * starRingEnd ℂ (a m) * b m

/-
If `a ∈ ℓ²_(t)` and `s ≤ t`, then `a ∈ ℓ²_(s)`.
-/
lemma MemSobolev.mono {s t : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n t a) (hst : s ≤ t) : MemSobolev n s a := by
  exact .of_nonneg_of_le ( fun _ => by exact mul_nonneg ( weight_nonneg s _ ) ( sq_nonneg _ ) )
      ( fun m => by exact mul_le_mul_of_nonneg_right ( weight_mono hst m ) ( sq_nonneg _ ) ) ha

/-
Sobolev norm monotonicity: if `s ≤ t` then `‖a‖²_(s) ≤ ‖a‖²_(t)`.
-/
lemma sobolevNormSq_mono {s t : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n t a) (hst : s ≤ t) :
    sobolevNormSq n s a ≤ sobolevNormSq n t a := by
  exact Summable.tsum_le_tsum ( fun m => mul_le_mul_of_nonneg_right ( weight_mono hst m ) (
      sq_nonneg _ ) ) ( MemSobolev.mono ha hst ) ha

/-! ## Smoothness helpers -/

lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

lemma one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

lemma infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp

/-- Directional derivative along a coordinate as a one-variable derivative. -/
lemma hasDerivAt_update_of_hasFDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : (Fin n → ℝ) → V} {F' : (Fin n → ℝ) →L[ℝ] V}
    {θ : Fin n → ℝ} (h : HasFDerivAt F F' θ) (j : Fin n) :
    HasDerivAt (fun t : ℝ => F (Function.update θ j t)) (F' (Pi.single j 1)) (θ j) := by
  have h1 := hasDerivAt_update θ j (θ j)
  have h2 : HasFDerivAt F F' (Function.update θ j (θ j)) := by rwa [Function.update_eq_self]
  exact h2.comp_hasDerivAt (θ j) h1

/-! ## Fourier exponentials -/

/-- The Fourier exponential `eₘ(θ) = exp(i ∑ⱼ mⱼ θⱼ)` for `m : Fin n → ℤ`
and `θ : Fin n → ℝ`. -/
def fourierExp (n : ℕ) (m : Fin n → ℤ) (θ : Fin n → ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(∑ j : Fin n, (m j : ℝ) * θ j))

/-
`|eₘ(θ)| = 1` for all `m` and `θ`.
-/
lemma norm_fourierExp (m : Fin n → ℤ) (θ : Fin n → ℝ) :
    ‖fourierExp n m θ‖ = 1 := by
  unfold fourierExp; norm_num [ Complex.norm_exp ] ;

/-
`eₘ` is `2π`-periodic in each coordinate.
-/
lemma fourierExp_add_two_pi (m : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) :
    fourierExp n m (Function.update θ j (θ j + 2 * π)) = fourierExp n m θ := by
  unfold fourierExp;
  convert Complex.exp_periodic.int_mul ( m j ) _ using 2; ring;
  rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_univ j ) ]; ring;
  rw [ Finset.sum_congr rfl fun x hx => by aesop ]; norm_num; ring

lemma fourierExp_contDiff (c : Fin n → ℤ) : ContDiff ℝ ∞ (fourierExp n c) := by
  unfold fourierExp
  have h1 : ContDiff ℝ ∞ (fun θ : Fin n → ℝ => ∑ j, (c j : ℝ) * θ j) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun θ : Fin n → ℝ => ((∑ j, (c j : ℝ) * θ j : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact Complex.contDiff_exp.comp (contDiff_const.mul h2)

end NashEmbedding.Sobolev

end
