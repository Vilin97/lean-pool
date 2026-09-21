/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaBranchFree
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal

/-! # Tan Two Theta Approximate Pair -/

open TauCeti.DavisKahan.ExactSinTheta

/-!
# Branch-free equation (7.6) for *approximate* singular pairs

Davis and Kahan's Section 7 argument sandwiches the invariance relation
between a matched singular pair of the graph coordinate `T`.  In finite
dimension such a pair exists for every index, and
`DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean` runs the printed argument
on it.  On an arbitrary Hilbert space `T` need not have singular vectors at
all, and that -- not the compression to a finite carrier -- is the sole reason
the compiled branch-free theorem carried `[FiniteDimensional 𝕜 U]`.

This module removes the need for exact singular pairs.  Everything here is
`RCLike`-generic and dimension-free; the input is an *approximate* pair

* `u ∈ U`, `v ∈ Uᗮ`, both unit vectors, and `t ≥ 0`;
* `‖T u - t v‖ ≤ ε` and `‖T* v - t u‖ ≤ ε`,

which is exactly the per-index content of the repository's
`ApproximateLeadingSingularFamily`, and which exists for every bounded
operator with no compactness assumption.

## What is proved

1. `paired_approximate_gap_inequality` -- equation (7.6) in cleared form with
   an explicit error `(‖A‖ + ‖H‖)(2 + ‖T‖ + t) ε`.  Exactly as in the exact
   case, `1 - t²` is only ever *multiplied*, never inverted, so no branch is
   chosen.

2. `abs_one_sub_sq_pos_of_paired_approximate` -- the paper's `cos 2θⱼ ≠ 0` for
   an approximate pair, proved without any division so that it is valid even
   when `H = 0`.

3. `penalty_le_of_paired_approximate` -- the *quantitative* separation from the
   pole.  In infinite dimension pointwise nonvanishing of `cos 2θ` is **not** a
   uniform separation, and none is assumed: equation (7.6) itself forces
   `|1 - t²| ‖H‖ ≥ (b-a)/4` once `t > 1/2` and the error is at most `(b-a)/4`,
   while for `t ≤ 1/2` the pole is simply far away.

4. `absDoubleAngleTangent_approximate_scalar` -- the branch-free per-pair
   estimate `(b-a)|tan 2θ| ≤ 2|Re ⟪v, H u⟫| + C ε`.

5. `sum_absDoubleAngleTangent_le_of_approximatePairs` -- the summed form over
   an orthonormal family of approximate pairs, through the magnitude Ky Fan
   variational bound `sum_abs_le_kyFanApproximationGauge_of_orthonormal`.
   The rephasing in that bound is the paper's "choose the sign according to
   `cos 2θⱼ`".

Nothing in this file assumes `[FiniteDimensional]`, a contraction bound on
`T`, `IsQuarterAcute`, or spectral placement for the blocks of `A + H`.
-/

namespace TauCeti
namespace DavisKahan.TanTwoTheta


open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

noncomputable section

/-! ### The scalar arithmetic

These three are pure real-arithmetic facts, isolated so that the geometric
argument below reads as the printed one. -/

/-- The cleared inequality of equation (7.6) assembled from the sandwiched
scalar identity.  `1 - t²` is never inverted, so no branch is chosen. -/
private theorem cleared_of_scalar_identity
    {t α β c e₁ e₂ ry a b L Tn ε : ℝ}
    (hid : t * β + c + e₁ - t * α - t ^ 2 * c - t * e₂ = ry)
    (hα : b ≤ α) (hβ : β ≤ a) (ht0 : 0 ≤ t)
    (he₁ : |e₁| ≤ L * ε) (he₂ : |e₂| ≤ L * ε)
    (hry : |ry| ≤ ε * (L * (1 + Tn))) :
    (b - a) * t ≤ (1 - t ^ 2) * c + L * (2 + Tn + t) * ε := by
  have hta : t * b ≤ t * α := mul_le_mul_of_nonneg_left hα ht0
  have htb : t * β ≤ t * a := mul_le_mul_of_nonneg_left hβ ht0
  have he₁hi : e₁ ≤ L * ε := (le_abs_self e₁).trans he₁
  have he₂t : t * -(L * ε) ≤ t * e₂ :=
    mul_le_mul_of_nonneg_left (neg_le_of_abs_le he₂) ht0
  have hrylo : -(ε * (L * (1 + Tn))) ≤ ry := neg_le_of_abs_le hry
  nlinarith [hid, hta, htb, he₁hi, he₂t, hrylo]

/-- The cleared inequality of equation (7.6), rewritten with both sides in
modulus.  This is the single fact both pole statements rest on. -/
private theorem abs_mul_abs_ge_of_paired_approximate
    {t c d err : ℝ} (hkey : d * t ≤ (1 - t ^ 2) * c + err) :
    d * t - err ≤ |1 - t ^ 2| * |c| := by
  have h1 : (1 - t ^ 2) * c ≤ |1 - t ^ 2| * |c| := by
    calc (1 - t ^ 2) * c ≤ |(1 - t ^ 2) * c| := le_abs_self _
      _ = |1 - t ^ 2| * |c| := abs_mul _ _
  linarith

/-- **`cos 2θ ≠ 0` for an approximate singular pair.**

Davis and Kahan's first move after equation (7.6): a principal angle of exactly
`π/4` would force the gap to close.  For an approximate pair the same argument
works once the error is at most a quarter of the gap, and it uses no division,
so it is valid even when `H = 0`.

This is the honest infinite-dimensional analogue of `singularValue_ne_one`.
Note what it does *not* say: nonvanishing at every index is not a uniform
separation from the pole, and no such separation is assumed.  The quantitative
statement that replaces it is `penalty_le_of_paired_approximate`. -/
theorem abs_one_sub_sq_pos_of_paired_approximate
    {t c d err : ℝ} (hd : 0 < d) (ht0 : 0 ≤ t)
    (hkey : d * t ≤ (1 - t ^ 2) * c + err)
    (herr : err ≤ d / 4) :
    0 < |1 - t ^ 2| := by
  have hstar := abs_mul_abs_ge_of_paired_approximate hkey
  by_cases hthalf : t ≤ 1 / 2
  · have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
    calc (0 : ℝ) < 3 / 4 := by norm_num
      _ ≤ 1 - t ^ 2 := by linarith
      _ ≤ |1 - t ^ 2| := le_abs_self _
  · have hthalf' : 1 / 2 < t := not_le.mp hthalf
    have hpos : 0 < |1 - t ^ 2| * |c| := by nlinarith
    rcases (abs_nonneg (1 - t ^ 2)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- **The quantitative pole separation.**

The error produced by an approximate pair must be divided by `|1 - t²|`, and in
infinite dimension there is no a priori uniform lower bound on that quantity:
singular values *may* accumulate at the pole.  What rules that out is equation
(7.6) itself, which gives `d t - err ≤ |1 - t²| |c| ≤ |1 - t²| h` for any bound
`h` on `|c|`.

* For `t ≤ 1/2` the pole is far away and `|1 - t²| ≥ 3/4`.
* For `t > 1/2` and `err ≤ d/4`, the left side is at least `d/4 > 0`, so
  `|1 - t²| h ≥ d/4`; in particular `h > 0`, and the penalty is at most
  `8 h err / d`.

So the separation is **derived from the gap**, never assumed, and the penalty is
`O(ε)` with a constant depending only on `h` and the gap. -/
theorem penalty_le_of_paired_approximate
    {t c d err M₀ ε h : ℝ} (hd : 0 < d) (ht0 : 0 ≤ t)
    (hh : 0 ≤ h) (hcH : |c| ≤ h)
    (hkey : d * t ≤ (1 - t ^ 2) * c + err)
    (herr4 : err ≤ d / 4) (herrE : err ≤ M₀ * ε) (herr0 : 0 ≤ err) :
    2 * err / |1 - t ^ 2| ≤ max (8 / 3) (8 * h / d) * (M₀ * ε) := by
  have hstar := abs_mul_abs_ge_of_paired_approximate hkey
  have hden0 : 0 < |1 - t ^ 2| :=
    abs_one_sub_sq_pos_of_paired_approximate hd ht0 hkey herr4
  have hM₀ε : 0 ≤ M₀ * ε := herr0.trans herrE
  by_cases hthalf : t ≤ 1 / 2
  · -- the pole is far away: the penalty is at most `(8/3) err`
    have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
    have h34 : (3 : ℝ) / 4 ≤ |1 - t ^ 2| :=
      le_trans (by linarith) (le_abs_self (1 - t ^ 2))
    have hstep : 2 * err / |1 - t ^ 2| ≤ 8 / 3 * err := by
      rw [div_le_iff₀ hden0]
      nlinarith
    refine hstep.trans ?_
    calc 8 / 3 * err ≤ 8 / 3 * (M₀ * ε) := by linarith
      _ ≤ max (8 / 3) (8 * h / d) * (M₀ * ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hM₀ε
  · -- the gap forces a positive separation, quantitatively
    have hthalf' : 1 / 2 < t := not_le.mp hthalf
    have hquarter : d / 4 ≤ |1 - t ^ 2| * |c| := by nlinarith
    have hHsep : d / 4 ≤ |1 - t ^ 2| * h :=
      hquarter.trans (mul_le_mul_of_nonneg_left hcH (abs_nonneg _))
    have hHpos : 0 < h := by
      rcases hh.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, mul_zero] at hHsep; linarith
    have hstep : 2 * err / |1 - t ^ 2| ≤ 8 * h / d * err := by
      rw [div_le_iff₀ hden0]
      have hmul : 2 * err * d ≤ 8 * err * (|1 - t ^ 2| * h) := by nlinarith
      have hdiv : 8 * h / d * err * |1 - t ^ 2| =
          8 * err * (|1 - t ^ 2| * h) / d := by
        field_simp
      rw [hdiv, le_div_iff₀ hd]
      exact hmul
    refine hstep.trans ?_
    have hcoef : 0 ≤ 8 * h / d := by positivity
    calc 8 * h / d * err ≤ 8 * h / d * (M₀ * ε) :=
          mul_le_mul_of_nonneg_left herrE hcoef
      _ ≤ max (8 / 3) (8 * h / d) * (M₀ * ε) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hM₀ε

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section Configuration

variable {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} {a b : ℝ}

/-- The `ε`-coefficient of the per-pair error, uniform in the singular value:
`(‖A‖ + ‖H‖)(3 + 2‖T‖)` dominates `(‖A‖ + ‖H‖)(2 + ‖T‖ + t)` for every
`t ≤ ‖T‖ + 1`. -/
def approximatePairErrorCoefficient (A H T : E →L[𝕜] E) : ℝ :=
  (‖A‖ + ‖H‖) * (3 + 2 * ‖T‖)

/-- The `ε`-coefficient of the branch-free per-pair estimate.  The first factor
is the price of dividing by `|1 - t²|`, controlled by the derived pole
separation `penalty_le_of_paired_approximate`; it depends only on `‖H‖` and the
gap, never on the location of the angles. -/
def branchFreeTangentErrorCoefficient (A H T : E →L[𝕜] E) (d : ℝ) : ℝ :=
  max (8 / 3) (8 * ‖H‖ / d) * approximatePairErrorCoefficient A H T

omit [CompleteSpace E] in
/-- The approximate-pair error coefficient is nonnegative. -/
theorem approximatePairErrorCoefficient_nonneg (A H T : E →L[𝕜] E) :
    0 ≤ approximatePairErrorCoefficient A H T := by
  unfold approximatePairErrorCoefficient; positivity

omit [CompleteSpace E] in
/-- The branch-free tangent error coefficient is nonnegative. -/
theorem branchFreeTangentErrorCoefficient_nonneg (A H T : E →L[𝕜] E) (d : ℝ) :
    0 ≤ branchFreeTangentErrorCoefficient A H T d := by
  unfold branchFreeTangentErrorCoefficient
  have h1 : (0 : ℝ) ≤ max (8 / 3) (8 * ‖H‖ / d) :=
    le_trans (by norm_num) (le_max_left _ _)
  exact mul_nonneg h1 (approximatePairErrorCoefficient_nonneg A H T)

/-- **Equation (7.6) in cleared form for an approximate singular pair.**

The exact statement `paired_singularVector_gap_inequality` is the case `ε = 0`
with `u`, `v` a genuine matched singular pair.  The error is explicit and
linear in `ε`, and `1 - t²` appears only as a multiplier, so the inequality is
branch-free exactly as the printed one is: no hypothesis says on which side of
the quarter turn the angle lies. -/
theorem paired_approximate_gap_inequality
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    {u v : E} {t ε : ℝ}
    (humem : u ∈ U) (hvmem : v ∈ Uᗮ) (hun : ‖u‖ = 1) (hvn : ‖v‖ = 1)
    (ht0 : 0 ≤ t)
    (hTu : ‖T u - ((t : ℝ) : 𝕜) • v‖ ≤ ε)
    (hTv : ‖ContinuousLinearMap.adjoint T v - ((t : ℝ) : 𝕜) • u‖ ≤ ε) :
    (b - a) * t ≤ (1 - t ^ 2) * RCLike.re ⟪v, H u⟫_𝕜 +
      (‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε := by
  have hAsym : ∀ x y : E, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜 :=
    fun x y => hA.isSymmetric x y
  have hHsym : ∀ x y : E, ⟪H x, y⟫_𝕜 = ⟪x, H y⟫_𝕜 :=
    fun x y => hH.isSymmetric x y
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hTu
  have hL0 : (0 : ℝ) ≤ ‖A‖ + ‖H‖ := by positivity
  set p : E := T u - ((t : ℝ) : 𝕜) • v with hpdef
  set w : E := ContinuousLinearMap.adjoint T v - ((t : ℝ) : 𝕜) • u with hwdef
  have hTueq : T u = ((t : ℝ) : 𝕜) • v + p := by rw [hpdef]; abel
  have hTveq : ContinuousLinearMap.adjoint T v = ((t : ℝ) : 𝕜) • u + w := by
    rw [hwdef]; abel
  obtain ⟨y, hyU, hy⟩ := hinv u humem
  -- the two orthogonality directions
  have hzw : ∀ z ∈ U, ∀ x ∈ Uᗮ, ⟪z, x⟫_𝕜 = 0 := fun z hz x hx =>
    (Submodule.mem_orthogonal U x).mp hx z hz
  have hwz : ∀ x ∈ Uᗮ, ∀ z ∈ U, ⟪x, z⟫_𝕜 = 0 := fun x hx z hz =>
    (Submodule.mem_orthogonal' U x).mp hx z hz
  have hAv : A v ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← hAsym z v]
    exact (Submodule.mem_orthogonal U v).mp hvmem (A z) (hAU z hz)
  -- `y` is bounded because the graph decomposition is orthogonal
  have hynorm : ‖y‖ ≤ (‖A‖ + ‖H‖) * (1 + ‖T‖) := by
    have hortho : ⟪y, T y⟫_𝕜 = 0 := hzw y hyU (T y) (hTmem y)
    have hpy :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (T y) hortho
    have hy1 : ‖y‖ ≤ ‖y + T y‖ := by
      nlinarith [norm_nonneg y, norm_nonneg (y + T y), norm_nonneg (T y)]
    rw [← hy] at hy1
    refine hy1.trans ?_
    have hTun : ‖T u‖ ≤ ‖T‖ := by
      calc ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖T‖ := by rw [hun, mul_one]
    have h2 : ‖u + T u‖ ≤ 1 + ‖T‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [hun]
      linarith
    have hAH : ‖A + H‖ ≤ ‖A‖ + ‖H‖ := ContinuousLinearMap.opNorm_add_le A H
    calc ‖(A + H) (u + T u)‖ ≤ ‖A + H‖ * ‖u + T u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A‖ + ‖H‖) * (1 + ‖T‖) := by
          refine mul_le_mul hAH h2 (norm_nonneg _) hL0
  -- sandwich the invariance relation between `v` and `u`
  have hL1 : ⟪v, (A + H) (u + T u)⟫_𝕜 =
      ((t : ℝ) : 𝕜) * ⟪u, y⟫_𝕜 + ⟪w, y⟫_𝕜 := by
    rw [hy, inner_add_right, hwz v hvmem y hyU, zero_add,
      ← ContinuousLinearMap.adjoint_inner_left T y v, hTveq, inner_add_left,
      inner_smul_left, RCLike.conj_ofReal]
  have hR1 : ⟪u, (A + H) (u + T u)⟫_𝕜 = ⟪u, y⟫_𝕜 := by
    rw [hy, inner_add_right, hzw u humem (T y) (hTmem y), add_zero]
  -- expand both sides through off-diagonality
  have hzexp : (A + H) (u + T u) =
      A u + ((t : ℝ) : 𝕜) • A v + A p + (H u + ((t : ℝ) : 𝕜) • H v + H p) := by
    rw [hTueq]
    simp only [add_apply, map_add, map_smul, smul_add]
    abel
  have hL2 : ⟪v, (A + H) (u + T u)⟫_𝕜 =
      ((t : ℝ) : 𝕜) * ⟪v, A v⟫_𝕜 + ⟪v, H u⟫_𝕜 +
        (⟪v, A p⟫_𝕜 + ⟪v, H p⟫_𝕜) := by
    rw [hzexp]
    simp only [inner_add_right, inner_smul_right,
      hwz v hvmem (A u) (hAU u humem), hwz v hvmem (H v) (hHUperp v hvmem)]
    ring
  have hR2 : ⟪u, (A + H) (u + T u)⟫_𝕜 =
      ⟪u, A u⟫_𝕜 + ((t : ℝ) : 𝕜) * ⟪u, H v⟫_𝕜 +
        (⟪u, A p⟫_𝕜 + ⟪u, H p⟫_𝕜) := by
    rw [hzexp]
    simp only [inner_add_right, inner_smul_right, hzw u humem (A v) hAv,
      hzw u humem (H u) (hHU u humem)]
    ring
  -- the sandwiched scalar identity, in real parts
  have hHc : RCLike.re ⟪u, H v⟫_𝕜 = RCLike.re ⟪v, H u⟫_𝕜 := by
    rw [← hHsym u v]
    exact inner_re_symm (𝕜 := 𝕜) (H u) v
  have hid : t * RCLike.re ⟪v, A v⟫_𝕜 + RCLike.re ⟪v, H u⟫_𝕜 +
        (RCLike.re ⟪v, A p⟫_𝕜 + RCLike.re ⟪v, H p⟫_𝕜) -
      t * RCLike.re ⟪u, A u⟫_𝕜 - t ^ 2 * RCLike.re ⟪v, H u⟫_𝕜 -
      t * (RCLike.re ⟪u, A p⟫_𝕜 + RCLike.re ⟪u, H p⟫_𝕜) =
        RCLike.re ⟪w, y⟫_𝕜 := by
    have hkey : ⟪v, (A + H) (u + T u)⟫_𝕜 -
        ((t : ℝ) : 𝕜) * ⟪u, (A + H) (u + T u)⟫_𝕜 = ⟪w, y⟫_𝕜 := by
      rw [hL1, hR1]; ring
    rw [hL2, hR2] at hkey
    have hre := congrArg RCLike.re hkey
    simp only [map_sub, map_add, RCLike.re_ofReal_mul] at hre
    rw [hHc] at hre
    nlinarith [hre]
  -- the form bounds at the two unit vectors
  have hα : b ≤ RCLike.re ⟪u, A u⟫_𝕜 := by
    have h := hUb u humem
    rw [hun] at h
    rw [← hAsym u u]
    simpa using h
  have hβ : RCLike.re ⟪v, A v⟫_𝕜 ≤ a := by
    have h := hUa v hvmem
    rw [hvn] at h
    rw [← hAsym v v]
    simpa using h
  -- the three error bounds
  have habs : ∀ x : E, ‖x‖ = 1 →
      |RCLike.re ⟪x, A p⟫_𝕜 + RCLike.re ⟪x, H p⟫_𝕜| ≤ (‖A‖ + ‖H‖) * ε := by
    intro x hx
    have hbnd : ∀ (B : E →L[𝕜] E), |RCLike.re ⟪x, B p⟫_𝕜| ≤ ‖B‖ * ε := by
      intro B
      refine (RCLike.abs_re_le_norm _).trans ?_
      calc ‖⟪x, B p⟫_𝕜‖ ≤ ‖x‖ * ‖B p‖ := norm_inner_le_norm _ _
        _ = ‖B p‖ := by rw [hx, one_mul]
        _ ≤ ‖B‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖B‖ * ε := by
            refine mul_le_mul_of_nonneg_left hTu (norm_nonneg _)
    have h1 := hbnd A
    have h2 := hbnd H
    have := abs_add_le (RCLike.re ⟪x, A p⟫_𝕜) (RCLike.re ⟪x, H p⟫_𝕜)
    linarith
  have hry : |RCLike.re ⟪w, y⟫_𝕜| ≤ ε * ((‖A‖ + ‖H‖) * (1 + ‖T‖)) := by
    refine (RCLike.abs_re_le_norm _).trans ?_
    calc ‖⟪w, y⟫_𝕜‖ ≤ ‖w‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ ε * ((‖A‖ + ‖H‖) * (1 + ‖T‖)) :=
          mul_le_mul hTv hynorm (norm_nonneg _) hε0
  exact cleared_of_scalar_identity hid hα hβ ht0 (habs v hvn) (habs u hun) hry

/-- **The branch-free per-pair estimate for an approximate singular pair.**

`(b - a) |tan 2θ| ≤ 2 |Re ⟪v, H u⟫| + C ε`, with the sign of the matched
coefficient absorbed into the modulus exactly as in the printed proof, and with
an explicit constant.  The smallness hypothesis on `ε` is what turns the
pointwise `cos 2θ ≠ 0` into the quantitative separation needed to divide by
`|1 - t²|`; it constrains the *approximation*, not the geometry. -/
theorem absDoubleAngleTangent_approximate_scalar
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    {u v : E} {t ε : ℝ}
    (humem : u ∈ U) (hvmem : v ∈ Uᗮ) (hun : ‖u‖ = 1) (hvn : ‖v‖ = 1)
    (ht0 : 0 ≤ t) (hε1 : ε ≤ 1)
    (hTu : ‖T u - ((t : ℝ) : 𝕜) • v‖ ≤ ε)
    (hTv : ‖ContinuousLinearMap.adjoint T v - ((t : ℝ) : 𝕜) • u‖ ≤ ε)
    (hsmall : approximatePairErrorCoefficient A H T * ε ≤ (b - a) / 4) :
    (b - a) * absDoubleAngleTangent t ≤
      2 * |RCLike.re ⟪v, H u⟫_𝕜| +
        branchFreeTangentErrorCoefficient A H T (b - a) * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hTu
  have hd : 0 < b - a := by linarith
  have hL0 : (0 : ℝ) ≤ ‖A‖ + ‖H‖ := by positivity
  -- the singular value is bounded by `‖T‖ + 1`, which makes the error uniform
  have htT : t ≤ ‖T‖ + 1 := by
    have h1 : ‖((t : ℝ) : 𝕜) • v‖ = t := by
      rw [norm_smul, hvn, mul_one, RCLike.norm_ofReal, abs_of_nonneg ht0]
    have h2 : ‖((t : ℝ) : 𝕜) • v‖ ≤ ‖T u‖ + ε := by
      have := norm_sub_norm_le (T u) (((t : ℝ) : 𝕜) • v)
      have h3 : ‖T u - ((t : ℝ) : 𝕜) • v‖ ≤ ε := hTu
      have h4 : ‖((t : ℝ) : 𝕜) • v - T u‖ ≤ ε := by
        rwa [norm_sub_rev]
      have h5 := norm_sub_norm_le (((t : ℝ) : 𝕜) • v) (T u)
      linarith
    have hTun : ‖T u‖ ≤ ‖T‖ := by
      calc ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖T‖ := by rw [hun, mul_one]
    rw [h1] at h2
    linarith
  have hkey := paired_approximate_gap_inequality hA hH hAU hHU hHUperp hTmem
    hUb hUa hinv humem hvmem hun hvn ht0 hTu hTv
  -- the `t`-dependent error is dominated by the uniform coefficient
  have herrle : (‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε ≤
      approximatePairErrorCoefficient A H T * ε := by
    unfold approximatePairErrorCoefficient
    have hmono : 2 + ‖T‖ + t ≤ 3 + 2 * ‖T‖ := by linarith
    have := mul_le_mul_of_nonneg_left hmono hL0
    exact mul_le_mul_of_nonneg_right this hε0
  have herr0 : (0 : ℝ) ≤ (‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε := by
    have : (0 : ℝ) ≤ 2 + ‖T‖ + t := by positivity
    positivity
  have herr4 : (‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε ≤ (b - a) / 4 :=
    herrle.trans hsmall
  -- the modulus of the matched coefficient is bounded by the perturbation
  have hcH : |RCLike.re ⟪v, H u⟫_𝕜| ≤ ‖H‖ := by
    refine (RCLike.abs_re_le_norm _).trans ?_
    calc ‖⟪v, H u⟫_𝕜‖ ≤ ‖v‖ * ‖H u‖ := norm_inner_le_norm _ _
      _ = ‖H u‖ := by rw [hvn, one_mul]
      _ ≤ ‖H‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖H‖ := by rw [hun, mul_one]
  -- the derived quantitative separation from the pole
  have hden0 : 0 < |1 - t ^ 2| :=
    abs_one_sub_sq_pos_of_paired_approximate hd ht0 hkey herr4
  have hpen := penalty_le_of_paired_approximate (h := ‖H‖) (M₀ :=
    approximatePairErrorCoefficient A H T) hd ht0 (norm_nonneg H) hcH hkey
    herr4 herrle herr0
  -- divide the cleared inequality by `|1 - t²|`
  have hstar := abs_mul_abs_ge_of_paired_approximate hkey
  have hdiv : (b - a) * absDoubleAngleTangent t ≤
      2 * |RCLike.re ⟪v, H u⟫_𝕜| +
        2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) / |1 - t ^ 2| := by
    refine le_of_mul_le_mul_right ?_ hden0
    have h1 : absDoubleAngleTangent t * |1 - t ^ 2| = 2 * t := by
      rw [absDoubleAngleTangent]
      field_simp
    have h2 : 2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) / |1 - t ^ 2| *
        |1 - t ^ 2| = 2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) :=
      div_mul_cancel₀ _ (ne_of_gt hden0)
    calc (b - a) * absDoubleAngleTangent t * |1 - t ^ 2|
        = (b - a) * (absDoubleAngleTangent t * |1 - t ^ 2|) := by ring
      _ = (b - a) * (2 * t) := by rw [h1]
      _ ≤ 2 * (|1 - t ^ 2| * |RCLike.re ⟪v, H u⟫_𝕜|) +
            2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) := by linarith
      _ = 2 * |RCLike.re ⟪v, H u⟫_𝕜| * |1 - t ^ 2| +
            2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) / |1 - t ^ 2| *
              |1 - t ^ 2| := by rw [h2]; ring
      _ = (2 * |RCLike.re ⟪v, H u⟫_𝕜| +
            2 * ((‖A‖ + ‖H‖) * (2 + ‖T‖ + t) * ε) / |1 - t ^ 2|) *
              |1 - t ^ 2| := by ring
  refine hdiv.trans ?_
  unfold branchFreeTangentErrorCoefficient
  have : max (8 / 3) (8 * ‖H‖ / (b - a)) *
      (approximatePairErrorCoefficient A H T * ε) =
      max (8 / 3) (8 * ‖H‖ / (b - a)) *
        approximatePairErrorCoefficient A H T * ε := by ring
  linarith [hpen, this.symm.le, this.le]

/-- **The branch-free `tan 2Θ` Ky Fan estimate over a family of approximate
singular pairs, on an arbitrary Hilbert space.**

This is the printed Section 7 argument with *no* dimension hypothesis and *no*
branch hypothesis.  The magnitude Ky Fan variational bound performs the paper's
sign choice by rephasing each left vector according to the sign of `cos 2θⱼ`.
The `m ε` error is what the limiting argument in the source layer sends to
zero. -/
theorem sum_absDoubleAngleTangent_le_of_approximatePairs
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    {m : ℕ} {u v : Fin m → E} {t : Fin m → ℝ} {ε : ℝ}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (humem : ∀ i, u i ∈ U) (hvmem : ∀ i, v i ∈ Uᗮ)
    (ht0 : ∀ i, 0 ≤ t i) (hε1 : ε ≤ 1)
    (hTu : ∀ i, ‖T (u i) - ((t i : ℝ) : 𝕜) • v i‖ ≤ ε)
    (hTv : ∀ i, ‖ContinuousLinearMap.adjoint T (v i) -
      ((t i : ℝ) : 𝕜) • u i‖ ≤ ε)
    (hsmall : approximatePairErrorCoefficient A H T * ε ≤ (b - a) / 4) :
    (b - a) * ∑ i, absDoubleAngleTangent (t i) ≤
      2 * kyFanApproximationGauge m H +
        m * (branchFreeTangentErrorCoefficient A H T (b - a) * ε) := by
  classical
  set C : ℝ := branchFreeTangentErrorCoefficient A H T (b - a) with hC
  -- per-pair estimates, rearranged as witnesses for the variational bound
  have hpair : ∀ i, ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2 ≤
      |RCLike.re ⟪v i, H (u i)⟫_𝕜| := by
    intro i
    have h := absDoubleAngleTangent_approximate_scalar hA hH hAU hHU hHUperp
      hTmem hUb hUa hinv hab (humem i) (hvmem i) (hu.norm_eq_one i)
      (hv.norm_eq_one i) (ht0 i) hε1 (hTu i) (hTv i) hsmall
    rw [← hC] at h
    linarith
  have hvar := sum_abs_le_kyFanApproximationGauge_of_orthonormal H hv hu
    (t := fun i => ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2) hpair
  -- evaluate the witness sum
  have hsum : ∑ i : Fin m, ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2 =
      ((b - a) * ∑ i, absDoubleAngleTangent (t i) - m * (C * ε)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hvar
  linarith

end Configuration

end

end DavisKahan.TanTwoTheta
end TauCeti
