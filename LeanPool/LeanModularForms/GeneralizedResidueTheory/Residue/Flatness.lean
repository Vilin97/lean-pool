/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue
import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber
import Mathlib.Analysis.Meromorphic.Order

/-!
# Flatness and Higher-Order Pole Conditions (Definition 3.2)

Flatness of curves at crossing points and conditions (A)/(B) for
the generalized residue theorem with higher-order poles.

## Main Definitions

* `orthogonalProjectionComplex` — projection of w onto direction L in C viewed as R^2
* `tangentDeviation` — orthogonal deviation of w from direction L
* `IsFlatOfOrder` — curve is flat of order n at a crossing point (Definition 3.2)
* `SatisfiesConditionA` — flatness condition for higher-order poles
* `SatisfiesConditionB` — angle/Laurent compatibility condition

## Main Results

* `isFlatOfOrder_one` — every piecewise C^1 immersion is flat of order 1
* `satisfiesConditionA_of_simple_poles` — condition A automatic for simple poles
* `satisfiesConditionB_of_simple_poles` — condition B automatic for simple poles
* `conditions_automatic_simple_poles` — both conditions automatic for simple poles

Reference: Hungerbuhler-Wasem, arXiv:1808.00997v2, Definition 3.2.
-/

open Complex Set Filter Topology Asymptotics
open scoped Real Interval

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass

noncomputable section

/-! ### Orthogonal projection in C (viewed as R^2) -/

/-- The orthogonal projection of `w` onto the real line spanned by `L` in C,
where C is viewed as R^2. This computes `(Re(w * conj L) / ||L||^2) * L`. -/
def orthogonalProjectionComplex (w L : ℂ) : ℂ :=
  ((w * starRingEnd ℂ L).re / Complex.normSq L) • L

/-- The tangent deviation: the component of `w` orthogonal to `L`. -/
def tangentDeviation (w L : ℂ) : ℂ :=
  w - orthogonalProjectionComplex w L

theorem orthogonalProjectionComplex_zero_left (L : ℂ) :
    orthogonalProjectionComplex 0 L = 0 := by simp [orthogonalProjectionComplex]

theorem tangentDeviation_zero_left (L : ℂ) :
    tangentDeviation 0 L = 0 := by simp [tangentDeviation, orthogonalProjectionComplex_zero_left]

theorem tangentDeviation_zero_right (w : ℂ) :
    tangentDeviation w 0 = w := by
  simp [tangentDeviation, orthogonalProjectionComplex, Complex.normSq_zero]

/-- Projection onto a nonzero direction `L` gives a real multiple of `L`. -/
theorem orthogonalProjectionComplex_smul (w L : ℂ) :
    ∃ c : ℝ, orthogonalProjectionComplex w L = c • L :=
  ⟨(w * starRingEnd ℂ L).re / Complex.normSq L, rfl⟩

/-- Projection of a real scalar multiple of L onto L is itself. -/
theorem orthogonalProjectionComplex_real_smul_self (c : ℝ) (L : ℂ) (hL : L ≠ 0) :
    orthogonalProjectionComplex (c • L) L = c • L := by
  have hns : Complex.normSq L ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  simp only [orthogonalProjectionComplex]
  have h_coeff : (c • L * starRingEnd ℂ L).re / Complex.normSq L = c := by
    rw [Complex.real_smul, mul_assoc, starRingEnd_apply]
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_div_cancel_of_imp fun h => absurd h hns
  rw [h_coeff]

/-- Tangent deviation of a real scalar multiple of L vanishes. -/
theorem tangentDeviation_real_smul_self (c : ℝ) (L : ℂ) (hL : L ≠ 0) :
    tangentDeviation (c • L) L = 0 := by
  rw [tangentDeviation, orthogonalProjectionComplex_real_smul_self c L hL, sub_self]

/-- Tangent deviation is additive in the first argument. -/
theorem tangentDeviation_add (w₁ w₂ L : ℂ) :
    tangentDeviation (w₁ + w₂) L = tangentDeviation w₁ L + tangentDeviation w₂ L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, add_mul, Complex.add_re,
    add_div]
  erw [add_smul]; abel

/-- Norm bound: ‖tangentDeviation w L‖ ≤ 2 * ‖w‖ for L ≠ 0. -/
theorem norm_tangentDeviation_le (w L : ℂ) (hL : L ≠ 0) :
    ‖tangentDeviation w L‖ ≤ 2 * ‖w‖ := by
  have hns : 0 < Complex.normSq L := Complex.normSq_pos.mpr hL
  unfold tangentDeviation orthogonalProjectionComplex
  suffices h : ‖((w * starRingEnd ℂ L).re / Complex.normSq L) • L‖ ≤ ‖w‖ by
    linarith [norm_sub_le w (((w * starRingEnd ℂ L).re / Complex.normSq L) • L)]
  rw [norm_smul, Real.norm_eq_abs]
  calc |(w * starRingEnd ℂ L).re / Complex.normSq L| * ‖L‖
      ≤ (‖w‖ * ‖L‖ / Complex.normSq L) * ‖L‖ := by
        gcongr
        rw [abs_div, abs_of_pos hns]
        gcongr
        exact (Complex.abs_re_le_norm _).trans
          (by rw [norm_mul, starRingEnd_apply, norm_star])
    _ = ‖w‖ * (‖L‖ * ‖L‖ / Complex.normSq L) := by ring
    _ = ‖w‖ := by rw [Complex.norm_mul_self_eq_normSq L, div_self hns.ne', mul_one]

/-! ### Flatness of order n (Definition 3.2)

A piecewise C^1 curve gamma is flat of order n at a parameter t_0 if the
orthogonal deviation from the tangent line at gamma(t_0) is o(||gamma(t) - gamma(t_0)||^n)
as t -> t_0, where the tangent line is determined by the one-sided derivative
limits. -/

/-- A curve gamma is **flat of order n** at parameter t_0 if:
- From the right: the deviation from the right tangent is o(||gamma(t) - gamma(t_0)||^n)
- From the left: the deviation from the left tangent is o(||gamma(t) - gamma(t_0)||^n)

This captures Definition 3.2 from Hungerbuhler-Wasem: the curve stays within
o(|Gamma(x) - z_1|^n) of the tangent lines at the crossing point z_1. -/
structure IsFlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop where
  /-- From the right: deviation from right tangent direction is o(||gamma(t) - gamma(t_0)||^n). -/
  right_flat : ∀ L : ℂ, L ≠ 0 → Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)
  /-- From the left: deviation from left tangent direction is o(||gamma(t) - gamma(t_0)||^n). -/
  left_flat : ∀ L : ℂ, L ≠ 0 → Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)

/-- Flatness of order m implies flatness of order n for n <= m.
The key point is that o(||w||^m) implies o(||w||^n) when n <= m and ||w|| -> 0. -/
theorem IsFlatOfOrder.of_le {γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ}
    (h : IsFlatOfOrder γ t₀ m) (hmn : n ≤ m)
    (hγ_cont : ContinuousAt γ t₀) :
    IsFlatOfOrder γ t₀ n := by
  have h_le_one : ∀ᶠ t in 𝓝 t₀, ‖γ t - γ t₀‖ ≤ 1 := by
    have : Tendsto (fun t => ‖γ t - γ t₀‖) (𝓝 t₀) (𝓝 0) := by
      rw [← norm_zero (E := ℂ), ← sub_self (γ t₀)]
      exact (hγ_cont.sub continuousAt_const).norm
    exact this (Iic_mem_nhds one_pos)
  have h_big_O : ∀ (l : Filter ℝ), l ≤ 𝓝 t₀ →
      (fun t => ‖γ t - γ t₀‖ ^ m) =O[l] (fun t => ‖γ t - γ t₀‖ ^ n) := fun l hl => by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hl h_le_one] with t ht
    simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) ht hmn
  exact ⟨fun L hL hR => (h.right_flat L hL hR).trans_isBigO (h_big_O _ nhdsWithin_le_nhds),
    fun L hL hL' => (h.left_flat L hL hL').trans_isBigO (h_big_O _ nhdsWithin_le_nhds)⟩

/-! ### Flatness of order 1 is automatic

Every piecewise C^1 immersion is flat of order 1 at every point. This is
because the derivative approximation gamma(t) - gamma(t_0) ~ gamma'(t_0)(t - t_0) ensures
the curve direction is asymptotically aligned with the tangent. -/

/-- Shared core of the order-1 flatness lemmas: on any filter `l` where the
first-order Taylor remainder `r t = γ t - γ t₀ - (t - t₀) • L` is `o(t - t₀)`,
the tangent deviation of `γ t - γ t₀` from `L` is `o(γ t - γ t₀)`. -/
private theorem tangentDeviation_isLittleO_of_remainder
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0) (l : Filter ℝ)
    (hr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[l] fun t => t - t₀) :
    (fun t => tangentDeviation (γ t - γ t₀) L) =o[l] fun t => γ t - γ t₀ := by
  set r := fun t => γ t - γ t₀ - (t - t₀) • L with hr_def
  have h_eq : ∀ t, tangentDeviation (γ t - γ t₀) L = tangentDeviation (r t) L := fun t => by
    rw [show γ t - γ t₀ = (t - t₀) • L + r t from by simp [hr_def],
      tangentDeviation_add, tangentDeviation_real_smul_self _ _ hL, zero_add]
  have hO : (fun t => tangentDeviation (r t) L) =O[l] r :=
    Asymptotics.isBigO_iff.mpr
      ⟨2, Eventually.of_forall fun t => norm_tangentDeviation_le _ _ hL⟩
  have ho1 := hO.trans_isLittleO hr
  have hO2 : (fun t => t - t₀) =O[l] (fun t => γ t - γ t₀) := by
    have hL_pos : (0 : ℝ) < ‖L‖ := norm_pos_iff.mpr hL
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 / ‖L‖, ?_⟩
    filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖ / 2)] with t ht
    have h1 : ‖t - t₀‖ * ‖L‖ = ‖(t - t₀) • L‖ := (norm_smul _ _).symm
    have h2 : ‖(t - t₀) • L‖ ≤ ‖γ t - γ t₀‖ + ‖r t‖ :=
      (show (t - t₀) • L = (γ t - γ t₀) - r t by simp [hr_def]) ▸ norm_sub_le _ _
    rw [div_mul_eq_mul_div, le_div_iff₀ hL_pos]
    nlinarith [norm_nonneg (γ t - γ t₀), ht]
  exact (ho1.trans_isBigO hO2).congr_left fun t => (h_eq t).symm

/-- Key lemma: if gamma has derivative L at t_0, then the tangent deviation of
`gamma(t) - gamma(t_0)` from L is o(||gamma(t) - gamma(t_0)||) as t -> t_0. This is the
essential content of flatness of order 1.

The argument: `gamma(t) - gamma(t_0) = (t - t_0) * L + o(t - t_0)`, so the
deviation from L is exactly the remainder term, which is `o(t - t_0)`.
Meanwhile `||gamma(t) - gamma(t_0)|| >= (||L||/2)|t - t_0|` eventually, giving
`o(t - t_0) = o(||gamma(t) - gamma(t_0)||)`. -/
theorem tangentDeviation_isLittleO_of_hasDerivAt
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ : HasDerivAt γ L t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝 t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  simp only [pow_one]
  rw [Asymptotics.isLittleO_norm_norm]
  exact tangentDeviation_isLittleO_of_remainder γ t₀ L hL _
    (hasDerivAt_iff_isLittleO.mp hγ)

/-- Tangent deviation from right derivative limit is o(||gamma(t) - gamma(t_0)||) as t -> t_0+.
This is the right-sided version needed for flatness of order 1. -/
theorem tangentDeviation_isLittleO_right
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  simp only [pow_one]
  rw [Asymptotics.isLittleO_norm_norm]
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact tangentDeviation_isLittleO_of_remainder γ t₀ L hL _
    (hasDerivWithinAt_iff_isLittleO.mp (hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hs_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hs_mem hγ_right)))

/-- Tangent deviation from left derivative limit is o(||gamma(t) - gamma(t_0)||) as t -> t_0-.
This is the left-sided version needed for flatness of order 1. -/
theorem tangentDeviation_isLittleO_left
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  simp only [pow_one]
  rw [Asymptotics.isLittleO_norm_norm]
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact tangentDeviation_isLittleO_of_remainder γ t₀ L hL _
    (hasDerivWithinAt_iff_isLittleO.mp (hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hs_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hs_mem hγ_left)))

/-- Every piecewise C^1 immersion is flat of order 1 at any interior point.
This is because the first-order Taylor approximation gamma(t) - gamma(t_0) ~ L*(t-t_0)
lies exactly on the tangent line, so the deviation is the remainder
o(t-t_0) = o(||gamma(t)-gamma(t_0)||). -/
theorem isFlatOfOrder_one (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    IsFlatOfOrder γ.toFun t₀ 1 := by
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
    (γ.partition.finite_toSet.subset Set.sdiff_subset).isClosed
  have hdiff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ.toFun t := by
    filter_upwards [
      nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (Set.mem_compl (fun h => h.2 rfl))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂ fun hm =>
      ht₁ ⟨hm, ne_of_gt (Set.mem_Ioi.mp ht₃)⟩
  have hdiff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ.toFun t := by
    filter_upwards [
      nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (Set.mem_compl (fun h => h.2 rfl))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂ fun hm =>
      ht₁ ⟨hm, ne_of_lt (Set.mem_Iio.mp ht₃)⟩
  constructor
  · intro L hL hL_right
    exact tangentDeviation_isLittleO_right γ.toFun t₀ L hL hL_right hcont hdiff_right
  · intro L hL hL_left
    exact tangentDeviation_isLittleO_left γ.toFun t₀ L hL hL_left hcont hdiff_left

/-! ### Pole order -/

/-- The pole order of a meromorphic function at a point, as a natural number.
Returns 0 if `f` is analytic at `x` (including the case where `f` is identically zero
near `x`). Returns `n` if `f` has a pole of order `n` (i.e., `meromorphicOrderAt f x = -n`). -/
noncomputable def poleOrderAt (f : ℂ → ℂ) (x : ℂ) : ℕ :=
  (-(meromorphicOrderAt f x).untop₀).toNat

/-! ### Condition (A): Flatness condition for higher-order poles -/

/-- **Condition (A)** from Hungerbuhler-Wasem: if z_0 is a pole of order n of f
on the curve, then the curve is flat of order n at z_0.

More precisely: for each singular point s in S_0 and each parameter t_0 where
gamma(t_0) = s, if f has a pole of order n at s, then gamma must be flat of order n
at t_0.

For the current formalization, which focuses on simple poles, this is stated
using `HasSimplePoleAt`. The condition is that the curve is flat of order 1
at each crossing, which is automatic (see `isFlatOfOrder_one`). -/
def SatisfiesConditionA (γ : PiecewiseC1Immersion) (S0 : Finset ℂ) : Prop :=
  ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
    t₀ ∈ Ioo γ.a γ.b →
    IsFlatOfOrder γ.toFun t₀ 1

/-- Condition (A) for a specific pole order function. Given a function assigning
pole orders to singular points, the curve must be flat of the corresponding
order at each crossing. -/
def SatisfiesConditionA' (γ : PiecewiseC1Immersion) (S0 : Finset ℂ)
    (poleOrder : ℂ → ℕ) : Prop :=
  ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
    t₀ ∈ Ioo γ.a γ.b →
    IsFlatOfOrder γ.toFun t₀ (poleOrder s)

/-! ### Condition (B): Angle/Laurent compatibility -/

/-- **Condition (B)** from Hungerbuhler-Wasem (Theorem 3.3): at each crossing point,
the angle α is a rational multiple of π, and the Laurent coefficients of `f` satisfy
angle compatibility.

Concretely: if `f` has a pole of order `N` at `s`, then near `s` we can write
`f(z) = Res(f,s)/(z-s) + Σ_{k=2}^{N} cₖ/(z-s)^k + g(z)` where `g` is analytic.
Condition (B) requires that for each `k ≥ 2` with `cₖ ≠ 0`, the angle `α` at the
crossing satisfies `(k-1) · α ∈ 2πℤ`. This ensures `PV ∮ dz/(z-s)^k = 0`
on the model sector curve (equation 3.4 in the paper). -/
structure SatisfiesConditionB (γ : PiecewiseC1Immersion) (f : ℂ → ℂ)
    (S0 : Finset ℂ) : Prop where
  /-- The angle at each crossing point on the curve is a rational multiple of π. -/
  angle_rational : ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
    ∀ ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b,
      ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
        angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q
  /-- Laurent coefficient compatibility: there exists a Laurent decomposition of `f`
      near each pole `s` into `f(z) = Σ_{k=1}^{N} aₖ/(z-s)^k + g(z)` where `g` is
      analytic, and each nonzero coefficient `aₖ` with `k ≥ 2` satisfies
      `(k-1)·α ∈ 2πℤ`. This ensures PV ∮ aₖ/(z-s)^k dz = 0 on the model sector.

      For simple poles (N = 0 higher-order terms), this is vacuously true. -/
  laurent_compatible : ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
    ∀ ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b,
      ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
        AnalyticAt ℂ g s ∧
        (∀ᶠ z in 𝓝[≠] s, f z = g z +
          ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
        (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 →
          ∃ m : ℤ, (↑k.val : ℝ) * angleAtCrossing γ t₀ ht₀_Ioo =
            ↑m * (2 * Real.pi))

/-! ### Conditions are automatic for simple poles

For simple poles (order 1), both conditions are automatically satisfied:

- **(A)**: Simple poles have order 1, and every piecewise C^1 curve is flat
  of order 1 (proved above as `isFlatOfOrder_one`).

- **(B)**: A simple pole has Laurent series f(z) = c_1/(z-z_0) + g(z), so
  the only singular term is k = 1 (the residue term). The condition
  "q does not divide (k-1) for k != 1" is vacuously true since there are no other
  singular terms. The angle rationality is trivially satisfied. -/

/-- Condition (A) is automatically satisfied when all poles are simple,
because every piecewise C^1 curve is flat of order 1. -/
theorem satisfiesConditionA_of_simple_poles
    (γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) :
    SatisfiesConditionA γ S0 := by
  intro _s _hs t₀ _ht₀ _hcross ht₀_Ioo
  exact isFlatOfOrder_one γ t₀ ht₀_Ioo

open Classical in
/-- Condition (B) for simple poles requires angle rationality at corner crossings
as an explicit hypothesis. The Laurent coefficient condition is vacuously true
(the only singular term is k = 1), so any q works; but the angle itself must
be expressible as pπ/q. At smooth crossings the angle is π = 1·π/1, so this
is automatic. At corner crossings, the angle depends on the curve geometry
and is not guaranteed to be rational without additional assumptions.

Note: For simple poles, the main theorem (Proposition 2.2 / `generalizedResidueTheorem'`)
does NOT require condition (B). This lemma is only needed when using the
higher-order theorem (Theorem 3.3) with simple poles. -/
theorem satisfiesConditionB_of_simple_poles
    (γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hAngles : ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
      ∀ ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b,
        t₀ ∈ γ.toPiecewiseC1Curve.partition →
          ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
            angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q) :
    SatisfiesConditionB γ f S0 := by
  constructor
  · -- angle_rational
    intro s hs t₀ ht₀ hcross ht₀_Ioo
    by_cases hp : t₀ ∈ γ.toPiecewiseC1Curve.partition
    · exact hAngles s hs t₀ ht₀ hcross ht₀_Ioo hp
    · -- Smooth point: angle = pi = 1*pi/1
      refine ⟨1, 1, one_ne_zero, Nat.coprime_one_left 1, ?_⟩
      rw [angleAtCrossing_smooth γ t₀ ht₀_Ioo hp]
      push_cast
      ring
  · intro s hs t₀ _ht₀ _hcross _ht₀_Ioo
    obtain ⟨c, g, hg, hf_eq⟩ := _hSimplePoles s hs
    refine ⟨1, ![c], g, hg, ?_, ?_⟩
    · filter_upwards [hf_eq] with z hz
      rw [hz]
      simp [pow_one]
      ring
    · intro ⟨k, hk⟩ _ hk1
      exact absurd hk1 (by omega)

/-- Both conditions (A) and (B) are satisfied for simple poles, provided
corner crossing angles are rational multiples of π. Condition (A) is fully
automatic; condition (B) requires the angle hypothesis only at corners.

Note: For simple poles, one should typically use `generalizedResidueTheorem'`
(Proposition 2.2) which requires neither condition. -/
theorem conditions_automatic_simple_poles
    (γ : PiecewiseC1Immersion) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hAngles : ∀ s ∈ S0, ∀ t₀ ∈ Icc γ.a γ.b, γ.toFun t₀ = s →
      ∀ ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b,
        t₀ ∈ γ.toPiecewiseC1Curve.partition →
          ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
            angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q) :
    SatisfiesConditionA γ S0 ∧ SatisfiesConditionB γ f S0 :=
  ⟨satisfiesConditionA_of_simple_poles γ f S0 hSimplePoles,
   satisfiesConditionB_of_simple_poles γ f S0 hSimplePoles hAngles⟩

end
