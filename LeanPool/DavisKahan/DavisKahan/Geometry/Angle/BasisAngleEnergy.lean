/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare
-- the principal-angle sequence and its basis-sum dictionary, used below to
-- identify the right-hand side with the printed `∑ₖ sin² θₖ`
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PrincipalAngleSequence

/-!
# Davis--Kahan 1970, Proposition 4.2: displacement-angle energy over a basis

Proposition 4.2 says that for **every** orthonormal basis of `U` and every
unitary carrying `U` onto `V`, the total squared displacement sine is at least
the sum of squared principal sines,

```
∑ᵢ sin²(bᵢ, W bᵢ)  ≥  ∑ₖ sin² θₖ,
```

with equality for the direct rotation on a principal basis.

## The proof is two Cauchy--Schwarz steps and no majorization

Write `C = |S|` for the positive Halmos cosine.  For a unit `x ∈ U`:

* `W x ∈ V` and `‖W x‖ = 1`, so `⟪x, W x⟫ = ⟪P_V x, W x⟫` has modulus at most
  `‖P_V x‖`;
* `‖P_V x‖ = ‖C x‖`, because `C² = P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ` and the second
  summand kills a source vector.

So `(re ⟪x, W x⟫)² ≤ ‖C x‖²` termwise, and summing over the basis is the whole
proof.  The right-hand side `∑ᵢ (1 - ‖C bᵢ‖²)` is `dim U - tr((C|_U)²)`, hence
independent of the basis, and it is the sum of squared principal sines: the
eigenvalues of `C|_U` are the principal cosines.

`displacementAngleSineSq_directRotation_eq_of_smul` supplies the equality case
— on an eigenvector of `C` the direct rotation's cost is exactly `1 - ‖C x‖²`
— so the bound is attained, by the direct rotation, on a principal basis.

## A transcription trap, refuted

It is tempting to state the right-hand side as the *same* sum evaluated at the
direct rotation, `∑ᵢ (1 - (re ⟪bᵢ, D bᵢ⟫)²)`, since on a principal basis the two
agree.  **On a non-principal basis they do not, and in that form the statement
is false.**  `re ⟪bᵢ, D bᵢ⟫ = ⟪C bᵢ, bᵢ⟫` is strictly below `‖C bᵢ‖` whenever
`bᵢ` is not an eigenvector, and the deficit is not recovered by summing.

Explicitly, in `ℝ⁴` take `U = span(e₁, e₂)` and `V` at principal angles `0` and
`arccos (1/10)` — acute, since `‖P_U − P_V‖ = √(1 − 1/100) < 1`.  Rotate the
basis of `U` by `0.2` radians.  Then the direct rotation costs `1.05142`, while
an admissible competitor (an orthogonal `4 × 4` matrix `W` with
`W P_U = P_V W`) costs `1.02824`.  Both exceed the principal-sine sum `0.99`,
which is what Proposition 4.2 actually asserts.

The competitor is not exotic: the maximiser of `∑ᵢ (re ⟪bᵢ, W bᵢ⟫)²` over the
admissible class is computed by a rank-one pencil, and it beats the direct
rotation on every basis that is not principal.  This is the *second* defect
found in the transcription of this proposition — the first is recorded next —
so the statement below is written against the paper's basis-free right-hand
side.

## The first trap: no proper subfamily inherits the inequality

The earlier transcription quantified over an arbitrary `Finset` of an arbitrary
orthonormal family in `U`, with no completeness requirement, and **in that form
it is false**.  The singleton instance is the natural thing to attack first, so
the refutation is recorded here rather than left to be rediscovered.

Take one unit `x ∈ U`; the claim becomes `(re ⟪x, D x⟫)² ≥ (re ⟪x, W x⟫)²`.  Now
`re ⟪x, D x⟫ = ⟪C x, x⟫` with `C = |S|` the positive Halmos cosine, and
`‖C x‖ = ‖P_V x‖` on `U` (`norm_absoluteValue_apply_eq_norm_projection`).  Any
admissible `W` sends `x` into `V` with `‖W x‖ = 1`, so
`re ⟪x, W x⟫ = re ⟪P_V x, W x⟫ ≤ ‖P_V x‖`, **with equality** for the `W`
determined by `W x = P_V x / ‖P_V x‖`, which exists whenever `U` and `V` have
equal finite dimension — any unit vector of `U` maps to any unit vector of `V`
under some isometry, and `Uᗮ → Vᗮ` may be chosen freely.  Cauchy--Schwarz gives
`⟪C x, x⟫ ≤ ‖C x‖` **strictly** unless `x` is an eigenvector of `C`.  So *every*
unit `x ∈ U` that is not a principal vector refutes the singleton case.

Concretely, in `ℂ⁴` with principal angles `0` and `π/3` (acute, since
`sin(π/3) < 1`) and `x = (e₁ + e₂)/√2`: `⟪C x, x⟫ = 3/4` while
`‖P_V x‖ = √(5/8) ≈ 0.7906`, so the competitor's cost `1 - 5/8 = 3/8` is
*smaller* than the direct rotation's `1 - 9/16 = 7/16`.

The defect is a missing hypothesis, not a wrong theorem: the source quantifies
over an orthonormal **basis** of `U`, and the inequality is a statement about
total energy, which no proper subfamily inherits.  Summing the same `ℂ⁴` example
over the full basis `{(e₁ ± e₂)/√2}` restores it: `1.025 < 1.125`.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Section4

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Squared sine of the angle a unit vector is displaced through by a unitary.

For unit `x` and unitary `W` the cosine of the angle between `x` and `W x` is
`re ⟪x, W x⟫`, so this is the squared sine.  It is Proposition 4.2's summand. -/
noncomputable def displacementAngleSineSq (W : H →L[ℂ] H) (x : H) : ℝ :=
  1 - (RCLike.re ⟪x, W x⟫_ℂ) ^ 2

/-- **On a source vector the canonical modulus has the length of the target
projection**: `‖C x‖ = ‖P_V x‖` for `x ∈ U`.

`C² = P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`, and the second summand annihilates a
vector of `U`, so the quadratic form of `C²` at `x` is `⟪P_V x, x⟫ = ‖P_V x‖²`.
This is the identity that converts the geometric bound `|⟪x, W x⟫| ≤ ‖P_V x‖`
into a statement about the angle operator. -/
theorem norm_absoluteValue_apply_eq_norm_projection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ U) :
    ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ =
      ‖V.starProjection x‖ := by
  let C : H →L[ℂ] H :=
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  let P : H →L[ℂ] H := U.starProjection
  let Q : H →L[ℂ] H := V.starProjection
  have hxP : P x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hCsa : star C = C :=
    (ContinuousLinearMap.modulus_isSelfAdjoint
      (spectraCanonicalIntertwiner U V)).star_eq
  have hC2 : C * C = halmosCosineSq U V :=
    spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq U V
  have hCosx : halmosCosineSq U V x = P (Q x) := by
    simp only [halmosCosineSq, add_apply, mul_apply_eq_comp]
    rw [hxP]
    have hxPc : (Uᗮ).starProjection x = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      rw [Submodule.orthogonal_orthogonal]
      exact hx
    rw [hxPc, map_zero, map_zero, add_zero]
  have hleft : ‖C x‖ ^ 2 = RCLike.re ⟪halmosCosineSq U V x, x⟫_ℂ := by
    calc
      ‖C x‖ ^ 2 = RCLike.re ⟪(star C * C) x, x⟫_ℂ := by
        simpa only [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.mul_def] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left C x
      _ = RCLike.re ⟪halmosCosineSq U V x, x⟫_ℂ := by rw [hCsa, hC2]
  have hright : RCLike.re ⟪P (Q x), x⟫_ℂ = ‖Q x‖ ^ 2 := by
    calc
      RCLike.re ⟪P (Q x), x⟫_ℂ = RCLike.re ⟪Q x, P x⟫_ℂ := by
        rw [U.inner_starProjection_left_eq_right]
      _ = RCLike.re ⟪Q x, x⟫_ℂ := by rw [hxP]
      _ = ‖Q x‖ ^ 2 := by
        have hQfix : Q (Q x) = Q x := by
          dsimp only [Q]
          exact V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
        calc
          RCLike.re ⟪Q x, x⟫_ℂ = RCLike.re ⟪Q (Q x), x⟫_ℂ := by rw [hQfix]
          _ = RCLike.re ⟪Q x, Q x⟫_ℂ :=
            congrArg RCLike.re (V.inner_starProjection_left_eq_right (Q x) x)
          _ = ‖Q x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) (Q x)).symm
  have hsquares : ‖C x‖ ^ 2 = ‖Q x‖ ^ 2 := by rw [hleft, hCosx, hright]
  nlinarith [norm_nonneg (C x), norm_nonneg (Q x)]

/-- **A competitor's numerical value at a source vector is bounded by the angle
operator**: `|⟪x, W x⟫| ≤ ‖C x‖ ‖x‖` for `x ∈ U`.

`W x` lies in `V`, so only the `V`-component of `x` pairs with it; Cauchy--
Schwarz and `‖W x‖ = ‖x‖` give `‖P_V x‖ ‖x‖`, which is `‖C x‖ ‖x‖`.

Unlike the one-sided estimate that Proposition 4.1 uses, this bounds the
*modulus*, which is what a squared cost needs. -/
theorem norm_inner_competitor_le
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) {x : H} (hx : x ∈ U) :
    ‖⟪x, W x⟫_ℂ‖ ≤
      ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ *
        ‖x‖ := by
  have hWxV : W x ∈ V := by
    apply V.starProjection_eq_self_iff.mp
    have happ := congrArg (fun T : H →L[ℂ] H => T x) hWmap
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hx] at happ
    exact happ.symm
  have hQWx : V.starProjection (W x) = W x :=
    Submodule.starProjection_eq_self_iff.mpr hWxV
  have hinner : ⟪x, W x⟫_ℂ = ⟪V.starProjection x, W x⟫_ℂ := by
    calc
      ⟪x, W x⟫_ℂ = ⟪x, V.starProjection (W x)⟫_ℂ := by rw [hQWx]
      _ = ⟪V.starProjection x, W x⟫_ℂ :=
        (V.inner_starProjection_left_eq_right x (W x)).symm
  have hWnorm : ‖W x‖ = ‖x‖ :=
    Unitary.norm_map (⟨W, hWunitary⟩ : unitary (H →L[ℂ] H)) x
  calc
    ‖⟪x, W x⟫_ℂ‖ = ‖⟪V.starProjection x, W x⟫_ℂ‖ := by rw [hinner]
    _ ≤ ‖V.starProjection x‖ * ‖W x‖ := norm_inner_le_norm _ _
    _ = ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ *
        ‖x‖ := by
      rw [hWnorm, norm_absoluteValue_apply_eq_norm_projection U V hx]

/-- **Termwise Proposition 4.2**: a unit source vector is displaced by at least
the angle its own `C`-length prescribes. -/
theorem displacementAngleSineSq_ge_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) {x : H} (hx : x ∈ U)
    (hxnorm : ‖x‖ = 1) :
    1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ ^ 2 ≤
      displacementAngleSineSq W x := by
  have hbound := norm_inner_competitor_le U V W hWunitary hWmap hx
  rw [hxnorm, mul_one] at hbound
  have hre : |RCLike.re ⟪x, W x⟫_ℂ| ≤ ‖⟪x, W x⟫_ℂ‖ := RCLike.abs_re_le_norm _
  have hsq : (RCLike.re ⟪x, W x⟫_ℂ) ^ 2 ≤
      ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ ^ 2 := by
    have h := hre.trans hbound
    have habs : (RCLike.re ⟪x, W x⟫_ℂ) ^ 2 = |RCLike.re ⟪x, W x⟫_ℂ| ^ 2 :=
      (sq_abs _).symm
    rw [habs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  simp only [displacementAngleSineSq]
  linarith

/-- **Davis--Kahan 1970, Proposition 4.2.**

For every orthonormal basis of `U` and every unitary carrying `U` onto `V`, the
total squared displacement sine is at least `∑ᵢ (1 - ‖C bᵢ‖²)`, the sum of
squared principal sines.

The right-hand side is `dim U - tr((C|_U)²)`, so it does not depend on the basis
even though it is written with one, and
`displacementAngleSineSq_directRotation_eq_of_smul` shows the direct rotation
attains it on a principal basis.  It is *not* the same as evaluating the
left-hand side at the direct rotation — see the module docstring for a
counterexample. -/
theorem sum_displacementAngleSineSq_ge
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ U) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∑ i, (1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
        ((b i : U) : H)‖ ^ 2) ≤
      ∑ i, displacementAngleSineSq W ((b i : U) : H) := by
  refine Finset.sum_le_sum fun i _ => ?_
  refine displacementAngleSineSq_ge_complex U V W hWunitary hWmap (b i).property ?_
  have h : ‖((b i : U) : H)‖ = ‖(b i : U)‖ := rfl
  rw [h]
  exact b.orthonormal.1 i

/-! ### The infinite-dimensional summability convention

`DK-4.2-prop` recorded the infinite-dimensional form as needing a convention for
summing `1 - ‖C bᵢ‖²` over an infinite basis.  With the paper's basis-free
right-hand side there is nothing to settle, for two reasons.

First, the estimate is **termwise** — `displacementAngleSineSq_ge_complex` constrains one
unit vector of `U` at a time — so no completeness or even orthogonality is used
and the inequality survives passage to any subfamily.  (That is exactly what
fails for the wrong right-hand side `∑ᵢ cost D bᵢ`, which is a genuine total
statement; see the module docstring.)

Second, taking the sums in `ℝ≥0∞` makes them unconditionally defined: divergence
is a value, not a failure, and `ENNReal.tsum_le_tsum` turns the termwise bound
into the infinite one with no hypothesis at all. -/

/-- Proposition 4.2 over an arbitrary finite subfamily of unit vectors of `U`.

Orthonormality is not needed for the inequality — it is what makes the two sides
the paper's *energies* — so the estimate does not depend on the family being a
basis, or even orthogonal. -/
theorem sum_displacementAngleSineSq_ge_of_mem_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    {ι : Type*} (b : ι → H) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1)
    (s : Finset ι) :
    ∑ i ∈ s, (1 - ‖ContinuousLinearMap.modulus
        (spectraCanonicalIntertwiner U V) (b i)‖ ^ 2) ≤
      ∑ i ∈ s, displacementAngleSineSq W (b i) :=
  Finset.sum_le_sum fun i _ =>
    displacementAngleSineSq_ge_complex U V W hWunitary hWmap (hb i) (hbnorm i)

/-- **Proposition 4.2, infinite-dimensional form, with no summability
convention.**

In `ℝ≥0∞` both sums are unconditionally defined and the inequality is the
termwise one.  The index type is arbitrary — in particular it may be infinite,
and the family need not be complete. -/
theorem tsum_displacementAngleSineSq_ge_of_mem_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    {ι : Type*} (b : ι → H) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1) :
    ∑' i, ENNReal.ofReal (1 - ‖ContinuousLinearMap.modulus
        (spectraCanonicalIntertwiner U V) (b i)‖ ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSq W (b i)) :=
  ENNReal.tsum_le_tsum fun i =>
    ENNReal.ofReal_le_ofReal
      (displacementAngleSineSq_ge_complex U V W hWunitary hWmap (hb i) (hbnorm i))

/-- **The bound of Proposition 4.2 is attained by the direct rotation on a
principal vector.**

If `C x = μ • x` with `μ ≥ 0` and `‖x‖ = 1` then the direct rotation's cost at
`x` is exactly `1 - ‖C x‖²`.  Applied to an orthonormal eigenbasis of `C|_U` —
a principal basis — this turns `sum_displacementAngleSineSq_ge` into an
equality, so the right-hand side really is the minimum and the direct rotation
really is a minimiser. -/
theorem displacementAngleSineSq_directRotation_eq_of_smul
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) {x : H} {μ : ℝ}
    (hμ : 0 ≤ μ) (hxnorm : ‖x‖ = 1)
    (hCx : ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x =
      (μ : ℂ) • x) :
    displacementAngleSineSq (spectraDirectRotation U V hacute) x =
      1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ ^ 2 := by
  have hnorm : ‖ContinuousLinearMap.modulus
      (spectraCanonicalIntertwiner U V) x‖ = μ := by
    rw [hCx, norm_smul, hxnorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hμ]
  have hform := re_inner_spectraDirectRotation_eq_absoluteValue U V hacute x
  have hCform : RCLike.re ⟪ContinuousLinearMap.modulus
      (spectraCanonicalIntertwiner U V) x, x⟫_ℂ = μ := by
    rw [hCx, inner_smul_left]
    have hxx : ⟪x, x⟫_ℂ = ((‖x‖ : ℝ) ^ 2 : ℝ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_num
    rw [hxx, hxnorm]
    simp
  have hDre : RCLike.re ⟪x, spectraDirectRotation U V hacute x⟫_ℂ = μ := by
    rw [← hCform, ← hform]
    exact inner_re_symm (𝕜 := ℂ) x (spectraDirectRotation U V hacute x)
  simp only [displacementAngleSineSq, hDre, hnorm]

/-! ### The printed right-hand side in arbitrary Hilbert dimension -/

/-- On a unit source vector, the basis-free right-hand-side summand is the
squared norm of the directed sine operator. -/
theorem ofReal_one_sub_sq_norm_absoluteValue_eq_enorm_principalSineOperator
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H} (hx : x ∈ U) (hxnorm : ‖x‖ = 1) :
    ENNReal.ofReal
        (1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ ^ 2) =
      ‖TauCeti.principalSineOperator U V ⟨x, hx⟩‖ₑ ^ 2 := by
  have hC := norm_absoluteValue_apply_eq_norm_projection U V hx
  have hpy := V.norm_sq_eq_add_norm_sq_starProjection x
  have hreal :
      1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x‖ ^ 2 =
        ‖Vᗮ.starProjection x‖ ^ 2 := by
    rw [hxnorm, one_pow] at hpy
    rw [hC]
    linarith
  rw [hreal, TauCeti.principalSineOperator_apply]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The basis-free right-hand side of Proposition 4.2 is the squared
principal-sine sequence in arbitrary Hilbert dimension.  Both sides are
extended-real sums, so the equality includes the divergent case. -/
theorem tsum_one_sub_sq_norm_absoluteValue_eq_tsum_sq_principalSineSequence
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {ι : Type u} (b : HilbertBasis ι ℂ U) :
    (∑' i, ENNReal.ofReal
        (1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
          ((b i : U) : H)‖ ^ 2)) =
      ∑' n : ℕ, ENNReal.ofReal (TauCeti.principalSineSequence U V n) ^ 2 := by
  rw [TauCeti.tsum_sq_principalSineSequence_eq_tsum_enorm_projection U V b]
  refine tsum_congr fun i => ?_
  exact ofReal_one_sub_sq_norm_absoluteValue_eq_enorm_principalSineOperator
    U V (b i).property (b.orthonormal.1 i)

/-- **Davis--Kahan 1970, Proposition 4.2, in arbitrary Hilbert dimension with
its printed right-hand side.**

For every Hilbert basis of `U` and every unitary `W` carrying `U` onto `V`, the
sum of squared displacement sines dominates the sum of squared principal sines.
The sums take values in `ℝ≥0∞`; the theorem therefore includes the paper's case
where the principal-sine sum is infinite. -/
theorem tsum_displacementAngleSineSq_ge_tsum_sq_principalSineSequence
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {ι : Type u} (b : HilbertBasis ι ℂ U)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal (TauCeti.principalSineSequence U V n) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (displacementAngleSineSq W ((b i : U) : H)) := by
  rw [← tsum_one_sub_sq_norm_absoluteValue_eq_tsum_sq_principalSineSequence U V b]
  exact tsum_displacementAngleSineSq_ge_of_mem_complex U V W hWunitary hWmap
    (fun i => ((b i : U) : H)) (fun i => (b i).property)
    (fun i => b.orthonormal.1 i)

/-- **Davis--Kahan 1970, Proposition 4.2, literal principal-angle form.**

For every Hilbert basis of `U` and every unitary `W` carrying `U` onto `V`,
`∑ₙ sin² θₙ` is bounded by the total squared displacement sine.  Here `θₙ` is
the canonical principal-angle sequence, whose sine is the approximation-number
principal-sine sequence.  Both sums are in `ℝ≥0∞`, so the statement includes
the case where the printed right-hand side is infinite. -/
theorem tsum_displacementAngleSineSq_ge_tsum_sq_sin_principalAngleSequence
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {ι : Type u} (b : HilbertBasis ι ℂ U)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (displacementAngleSineSq W ((b i : U) : H)) := by
  rw [TauCeti.tsum_sq_sin_principalAngleSequence_eq_tsum_sq_principalSineSequence]
  exact tsum_displacementAngleSineSq_ge_tsum_sq_principalSineSequence
    U V b W hWunitary hWmap

/-! ### Finite-dimensional compatibility with the original principal-sine list

The arbitrary-dimensional source theorem above uses
`TauCeti.principalSineSequence`, the approximation-number sequence of
`P_{Vᗮ}|_U`.  In finite dimension the existing `TauCeti.principalSines` list is
the same singular-value data.  The declarations below retain that finite
dictionary for existing consumers.

The finite identity
`TauCeti.sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection` reads the
principal-sine list off any orthonormal basis of `U`.  That lemma is the
Frobenius identity `∑ᵢ σᵢ² = ∑ₖ ‖A bₖ‖²` applied to the cross projections
`P_V P_U` and `P_{Vᗮ} P_U` restricted to `U`, which is legitimate because both
vanish on `Uᗮ`. -/

/-- **The right-hand side of Proposition 4.2 is `∑ₖ sin² θₖ`.**

For every orthonormal basis `b` of `U`,

  `∑ᵢ (1 - ‖C bᵢ‖²) = ∑ₖ sin² θₖ`,

with `C` the positive Halmos cosine and `sin θₖ` the principal sines of the
pair `(U, V)` — the singular values of `P_{Vᗮ} P_U`.  In particular the left
side does not depend on the basis, which is what the paper's basis-free
statement asserts.

This is the finite-dimensional compatibility form of the arbitrary-dimensional
identity `tsum_one_sub_sq_norm_absoluteValue_eq_tsum_sq_principalSineSequence`.
It uses `TauCeti.principalSines` and a basis indexed by `Fin (finrank ℂ U)`. -/
theorem sum_one_sub_sq_norm_absoluteValue_eq_sum_sq_principalSines
    [FiniteDimensional ℂ H]
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ U)) ℂ U) :
    ∑ i, (1 - ‖ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
        ((b i : U) : H)‖ ^ 2) =
      ∑ i : Fin (Module.finrank ℂ U),
        TauCeti.principalSines U V (i : ℕ) ^ 2 := by
  rw [TauCeti.sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection U V b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_absoluteValue_apply_eq_norm_projection U V (b i).2]
  -- the two spellings of the orthogonal projector: the bounded-operator
  -- `projection` of this package and the linear-map `TauCeti.projection`
  rfl

/-- **Davis--Kahan 1970, Proposition 4.2, with the printed right-hand side.**

For every orthonormal basis of `U` and every unitary `W` carrying `U` onto `V`,

  `∑ᵢ sin²(bᵢ, W bᵢ)  ≥  ∑ₖ sin² θₖ`.

This is the finite-dimensional compatibility form of
`tsum_displacementAngleSineSq_ge_tsum_sq_principalSineSequence`, expressed with
the existing `TauCeti.principalSines` list. -/
theorem sum_displacementAngleSineSq_ge_sum_sq_principalSines
    [FiniteDimensional ℂ H]
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ U)) ℂ U) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∑ i : Fin (Module.finrank ℂ U), TauCeti.principalSines U V (i : ℕ) ^ 2 ≤
      ∑ i, displacementAngleSineSq W ((b i : U) : H) := by
  rw [← sum_one_sub_sq_norm_absoluteValue_eq_sum_sq_principalSines U V b]
  exact sum_displacementAngleSineSq_ge U V b W hWunitary hWmap

end Section4
end DavisKahan
end TauCeti
