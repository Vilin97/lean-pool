/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.RestrictedDisplacementExtremal
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Pinching
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSquare
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare

/-! # Displacement Square Extremal -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Squared-displacement extremality by pinching and block sums

Davis--Kahan Proposition 4.3 says the direct rotation minimizes every unitarily invariant
norm of the *squared full displacement* `(1−W)†(1−W)`.  At the scope a unitarily invariant
norm actually sees, that is the Ky Fan statement proved here.

## The chain

```
kyFan_k(2 − 2C)                        -- D's squared displacement, already pinch-diagonal
  = kyFan_k(blockSum of D's two blocks)
  ≤ kyFan_k(blockSum of W's two blocks)
  = kyFan_k(pinch((1−W)†(1−W)))
  ≤ kyFan_k((1−W)†(1−W))
```

* The first and third steps are the chart
  `orthogonalDecomposition_conj_diagonalPart` together with invariance of the gauge under
  conjugation by the isometry `H ≃ₗᵢ WithLp 2 (U × Uᗮ)`.
* The second is `kyFanApproximationGauge_blockSum_le` fed by Proposition 4.1 on `U` and on
  `Uᗮ`, squared through `approximationNumber_gramOperator_complex` (`aₙ(X†X) = aₙ(X)²`).
* The last is the Fan--Hoffman pinching contraction
  `kyFanApproximationGauge_diagonalPart_le_complex`.

## Two things that are *not* extra work

**Proposition 4.1 for the complementary pair is the same theorem.**  The canonical
intertwiner `P_V P_U + P_Vᗮ P_Uᗮ` is symmetric under exchanging each subspace for its
complement, so `spectraDirectRotation Uᗮ Vᗮ = spectraDirectRotation U V` on the nose
(`spectraDirectRotation_orthogonal`), and acuteness is literally the same number.  Only the
competitor's admissibility has to be transported, and that is one subtraction.

**The direct rotation's squared displacement is already block diagonal.**
`(1 − D†)(1 − D) = 2 − (D + D†) = 2 − 2C`, and `C` commutes with `P_U`, so its pinch is
itself and the first step of the chain is an equality rather than an estimate.

## Why the squares are the crux

Proposition 4.1 dominates approximation numbers at the *first* power; Proposition 4.3 is
about the Gram operator of the displacement.  `aₙ(X†X) = aₙ(X)²`
(`ForTauCeti/.../ApproximationNumber/GramSquare.lean`) is the only bridge, and it did not
exist before this development.  It is also exactly why Proposition 4.3 survives while
Proposition 4.4 does not: sums of *squares* of the approximation numbers are dominated at
every `k`, while the sums themselves are not -- the repository carries a compiled
counterexample to the latter.

## The pointwise reading of Proposition 4.3 is false

The obvious reading of the printed proposition -- that every *individual* approximation
number `aₙ((1−W)†(1−W))` is minimized by the direct rotation -- does not hold, and the
configuration that kills it is the same equal-angle multiplicity mixing that refutes
Proposition 4.4 (`shortRotation_fullDisplacement_refuted`, census row `DK-4.4-prop`).  For a
Ky Fan norm the pointwise domination would imply the Ky Fan one and hence 4.4, so it cannot
hold.

Explicitly, in `ℝ⁴` take `U = span(e₁, e₂)` and `V` at principal angles `π/4, π/4` -- acute,
since `‖P_U − P_V‖ = sin(π/4) < 1`.  Let `W` carry `U` onto `V` by a quarter turn in the
`V`-frame and `Uᗮ` onto `Vᗮ` by the identity; it is orthogonal and satisfies
`W P_U = P_V W`.  Then

* `aₙ(1 − D) = (0.765367, 0.765367, 0.765367, 0.765367)` -- four equal values `2 sin(π/8)`,
  one per principal direction;
* `aₙ(1 − W) = (1.586707, 1.586707, 0.261052, 0.261052)`;

so at `n = 2` the competitor is strictly smaller, and squaring preserves that:
`aₙ((1−D)†(1−D))` is `0.585786` at `n = 2` against the competitor's `0.068148`.

Proposition 4.3 itself is untouched.  Its Ky Fan sums of *squares* are
`(0.586, 1.172, 1.757, 2.343)` for the direct rotation against
`(2.518, 5.035, 5.103, 5.172)` for the competitor, dominated at every `k`.  The statement
proved here is therefore at Ky Fan level, which is what a unitarily invariant norm sees.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Section4

open ExactSinTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ky Fan gauges of Gram operators are monotone in the approximation numbers.

This is where `aₙ(X†X) = aₙ(X)²` is spent: a pointwise domination at the first power
squares termwise, and sums of squares are then compared summand by summand. -/
theorem kyFanApproximationGauge_gramOperator_mono_complex {E F G : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] F) (B : E →L[ℂ] G)
    (h : ∀ n, A.approximationNumber n ≤ B.approximationNumber n) (k : ℕ) :
    kyFanApproximationGauge k (gramOperator A) ≤
      kyFanApproximationGauge k (gramOperator B) := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  refine Finset.sum_le_sum fun n _ => ?_
  rw [approximationNumber_gramOperator_complex, approximationNumber_gramOperator_complex]
  have h0 : 0 ≤ A.approximationNumber n := A.approximationNumber_nonneg n
  nlinarith [h n, h0]

/-- The `U`-compression of a Gram operator is the Gram operator of the compression, since
`ι_U† = Π_U`. -/
theorem orthogonalProjectionOnto_comp_gram_comp_subtypeL_complex (T : H →L[ℂ] H)
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] [CompleteSpace (U : Type u)] :
    U.orthogonalProjectionOnto ∘L (star T * T) ∘L U.subtypeL =
      gramOperator (T ∘L U.subtypeL) := by
  rw [gramOperator, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
  rfl

omit [CompleteSpace H] in
/-- Admissibility of a competitor passes to the complementary pair: subtract
`W P_U = P_V W` from `W = W`. -/
theorem competitor_admissible_orthogonal_complex (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (W : H →L[ℂ] H)
    (hWmap : W * U.starProjection = V.starProjection * W) :
    W * Uᗮ.starProjection = Vᗮ.starProjection * W := by
  show W * Uᗮ.starProjection = Vᗮ.starProjection * W
  rw [Submodule.starProjection_orthogonal' U, Submodule.starProjection_orthogonal' V,
    mul_sub, sub_mul, mul_one, one_mul, hWmap]

/-- **The direct rotation's squared displacement is the affine image `2 − 2C`.**

`(1 − D†)(1 − D) = 1 + D†D − (D + D†)`, and `D` is unitary with Hermitian part `C`. -/
theorem directRotation_displacementSquare_eq (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    (1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute) =
      2 - (2 : ℂ) • ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  have h1 : star (spectraDirectRotation U V hacute) *
      spectraDirectRotation U V hacute = 1 :=
    star_spectraDirectRotation_mul_self U V hacute
  have h2 : spectraDirectRotation U V hacute +
      star (spectraDirectRotation U V hacute) =
      (2 : ℂ) • ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) :=
    spectraDirectRotation_add_star_eq_two_smul_absoluteValue U V hacute
  have hexp : (1 - star (spectraDirectRotation U V hacute)) *
      (1 - spectraDirectRotation U V hacute) =
      1 + star (spectraDirectRotation U V hacute) *
          spectraDirectRotation U V hacute -
        (spectraDirectRotation U V hacute +
          star (spectraDirectRotation U V hacute)) := by
    noncomm_ring
  rw [hexp, h1, h2]
  norm_num

/-- **The direct rotation's squared displacement is already block diagonal.**

`2 − 2C` commutes with `P_U` because `C` does, so it equals its own pinch and the first
step of Proposition 4.3's chain is an equality. -/
theorem diagonalPart_directRotation_displacementSquare (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    U.diagonalPart ((1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute)) =
      (1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute) := by
  set C : H →L[ℂ] H :=
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) with hC
  set A : H →L[ℂ] H := (1 - star (spectraDirectRotation U V hacute)) *
    (1 - spectraDirectRotation U V hacute) with hA
  have hAeq : A = 2 - (2 : ℂ) • C := directRotation_displacementSquare_eq U V hacute
  have hCcomm : C * U.starProjection = U.starProjection * C :=
    (spectraCanonicalAbsoluteValue_commute_projection U V).eq
  have hcomm : A * U.starProjection = U.starProjection * A := by
    rw [hAeq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hCcomm]
    congr 1
    rw [two_mul, mul_two]
  apply Submodule.diagonalPart_eq_self_of_reflectionConjugate
  have hAJ : A * U.reflectionOperator = U.reflectionOperator * A := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, hcomm]
    rw [show (ContinuousLinearMap.id ℂ H) = 1 from rfl, mul_one, one_mul]
  have hJJ : U.reflectionOperator * U.reflectionOperator = (1 : H →L[ℂ] H) :=
    Submodule.reflectionOperator_involutive (𝕜 := ℂ) (E := H) U
  calc U.reflectionOperator ∘L A ∘L U.reflectionOperator
      = U.reflectionOperator * (A * U.reflectionOperator) := rfl
    _ = U.reflectionOperator * (U.reflectionOperator * A) := by rw [hAJ]
    _ = (U.reflectionOperator * U.reflectionOperator) * A := by rw [mul_assoc]
    _ = A := by rw [hJJ, one_mul]

/-- The squared displacement of a completed nonacute direct rotation is the same affine image of
the canonical positive cosine as in the acute case. -/
theorem nonacuteDirectRotation_displacementSquare_eq (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    (1 - star (nonacuteDirectRotation U V J)) * (1 - nonacuteDirectRotation U V J) =
      2 - (2 : ℂ) • ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  have hunit := star_nonacuteDirectRotation_mul_self U V J
  have hsum := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hexp : (1 - star (nonacuteDirectRotation U V J)) *
      (1 - nonacuteDirectRotation U V J) =
      1 + star (nonacuteDirectRotation U V J) * nonacuteDirectRotation U V J -
        (nonacuteDirectRotation U V J + star (nonacuteDirectRotation U V J)) := by
    noncomm_ring
  rw [hexp, hunit, hsum]
  norm_num [two_smul ℂ]

/-- The completed nonacute direct rotation's squared displacement is already block diagonal. -/
theorem diagonalPart_nonacuteDirectRotation_displacementSquare_complex (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    U.diagonalPart ((1 - star (nonacuteDirectRotation U V J)) *
        (1 - nonacuteDirectRotation U V J)) =
      (1 - star (nonacuteDirectRotation U V J)) *
        (1 - nonacuteDirectRotation U V J) := by
  set C : H →L[ℂ] H :=
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  set A : H →L[ℂ] H := (1 - star (nonacuteDirectRotation U V J)) *
    (1 - nonacuteDirectRotation U V J)
  have hAeq : A = 2 - (2 : ℂ) • C := nonacuteDirectRotation_displacementSquare_eq U V J
  have hCcomm : C * U.starProjection = U.starProjection * C :=
    (spectraCanonicalAbsoluteValue_commute_projection U V).eq
  have hcomm : A * U.starProjection = U.starProjection * A := by
    rw [hAeq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hCcomm]
    congr 1
    rw [two_mul, mul_two]
  apply Submodule.diagonalPart_eq_self_of_reflectionConjugate
  have hAJ : A * U.reflectionOperator = U.reflectionOperator * A := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, hcomm]
    rw [show (ContinuousLinearMap.id ℂ H) = 1 from rfl, mul_one, one_mul]
  have hJJ : U.reflectionOperator * U.reflectionOperator = (1 : H →L[ℂ] H) :=
    Submodule.reflectionOperator_involutive (𝕜 := ℂ) (E := H) U
  calc U.reflectionOperator ∘L A ∘L U.reflectionOperator
      = U.reflectionOperator * (A * U.reflectionOperator) := rfl
    _ = U.reflectionOperator * (U.reflectionOperator * A) := by rw [hAJ]
    _ = (U.reflectionOperator * U.reflectionOperator) * A := by rw [mul_assoc]
    _ = A := by rw [hJJ, one_mul]

/-- **Infinite-dimensional Davis--Kahan Proposition 4.3, at Ky Fan scope.**

Every Ky Fan sum of the approximation numbers of the squared full displacement is
minimized by the direct rotation.  This is the scope a unitarily invariant norm sees; the
individual approximation numbers are *not* dominated, and the repository carries the
configuration that refutes that reading. -/
theorem proposition4_3_squaredDisplacement_kyFan (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) := by
  let : CompleteSpace (U : Type u) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  let : CompleteSpace ((Uᗮ : Submodule ℂ H) : Type u) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection Uᗮ).completeSpace_coe
  have hL : ‖(U.orthogonalDecomposition : H →L[ℂ] WithLp 2 (U × Uᗮ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.norm_map x)
  have hR : ‖(U.orthogonalDecomposition.symm : WithLp 2 (U × Uᗮ) →L[ℂ] H)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.symm.norm_map x)
  have hRL : (U.orthogonalDecomposition.symm : WithLp 2 (U × Uᗮ) →L[ℂ] H) ∘L
      (U.orthogonalDecomposition : H →L[ℂ] WithLp 2 (U × Uᗮ)) =
      ContinuousLinearMap.id ℂ H := by
    ext x
    simp
  have hchart : ∀ T : H →L[ℂ] H,
      kyFanApproximationGauge k (U.diagonalPart ((1 - star T) * (1 - T))) =
        kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - T) ∘L U.subtypeL))
          (gramOperator ((1 - T) ∘L Uᗮ.subtypeL))) := by
    intro T
    have hst : (1 - star T) * (1 - T) = star (1 - T) * (1 - T) := by
      rw [star_sub, star_one]
    rw [hst,
      ← kyFanApproximationGauge_conj_eq_complex hL hR hRL
        (U.diagonalPart (star (1 - T) * (1 - T))) k,
      orthogonalDecomposition_conj_diagonalPart U (star (1 - T) * (1 - T)),
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_complex,
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_complex]
  have hU : ∀ n,
      ((1 - spectraDirectRotation U V hacute) ∘L U.subtypeL).approximationNumber n ≤
        ((1 - W) ∘L U.subtypeL).approximationNumber n :=
    proposition4_1_approximationNumbers U V hacute W hWunitary hWmap
  have hUperp : ∀ n,
      ((1 - spectraDirectRotation U V hacute) ∘L Uᗮ.subtypeL).approximationNumber n ≤
        ((1 - W) ∘L Uᗮ.subtypeL).approximationNumber n := by
    intro n
    have h := proposition4_1_approximationNumbers Uᗮ Vᗮ
      (isUniformlyAcute_orthogonal hacute) W hWunitary
      (competitor_admissible_orthogonal_complex U V W hWmap) n
    rwa [spectraDirectRotation_orthogonal U V hacute] at h
  have hblock := kyFanApproximationGauge_blockSum_le
    (fun j => kyFanApproximationGauge_gramOperator_mono_complex _ _ hU j)
    (fun j => kyFanApproximationGauge_gramOperator_mono_complex _ _ hUperp j) k
  calc kyFanApproximationGauge k
        ((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute))
      = kyFanApproximationGauge k (U.diagonalPart
          ((1 - star (spectraDirectRotation U V hacute)) *
            (1 - spectraDirectRotation U V hacute))) := by
        rw [diagonalPart_directRotation_displacementSquare U V hacute]
    _ = kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - spectraDirectRotation U V hacute) ∘L U.subtypeL))
          (gramOperator ((1 - spectraDirectRotation U V hacute) ∘L Uᗮ.subtypeL))) :=
        hchart _
    _ ≤ kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - W) ∘L U.subtypeL))
          (gramOperator ((1 - W) ∘L Uᗮ.subtypeL))) := hblock
    _ = kyFanApproximationGauge k
          (U.diagonalPart ((1 - star W) * (1 - W))) := (hchart W).symm
    _ ≤ kyFanApproximationGauge k ((1 - star W) * (1 - W)) :=
        kyFanApproximationGauge_diagonalPart_le_complex U _ k

/-- **Davis--Kahan Proposition 4.3 at the matched-crossed-defect nonacute scope.** -/
theorem proposition4_3_nonacute_squaredDisplacement_kyFan (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (nonacuteDirectRotation U V J)) *
          (1 - nonacuteDirectRotation U V J)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) := by
  let : CompleteSpace (U : Type u) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  let : CompleteSpace ((U.orthogonal : Submodule ℂ H) : Type u) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U.orthogonal).completeSpace_coe
  have hL : ‖(U.orthogonalDecomposition : H →L[ℂ] WithLp 2 (U × U.orthogonal))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.norm_map x)
  have hR : ‖(U.orthogonalDecomposition.symm : WithLp 2 (U × U.orthogonal) →L[ℂ] H)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.symm.norm_map x)
  have hRL : (U.orthogonalDecomposition.symm : WithLp 2 (U × U.orthogonal) →L[ℂ] H) ∘L
      (U.orthogonalDecomposition : H →L[ℂ] WithLp 2 (U × U.orthogonal)) =
      ContinuousLinearMap.id ℂ H := by
    ext x
    simp
  have hchart : ∀ T : H →L[ℂ] H,
      kyFanApproximationGauge k (U.diagonalPart ((1 - star T) * (1 - T))) =
        kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - T) ∘L U.subtypeL))
          (gramOperator ((1 - T) ∘L U.orthogonal.subtypeL))) := by
    intro T
    have hst : (1 - star T) * (1 - T) = star (1 - T) * (1 - T) := by
      rw [star_sub, star_one]
    rw [hst,
      ← kyFanApproximationGauge_conj_eq_complex hL hR hRL
        (U.diagonalPart (star (1 - T) * (1 - T))) k,
      orthogonalDecomposition_conj_diagonalPart U (star (1 - T) * (1 - T)),
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_complex,
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_complex]
  have hU : ∀ n,
      ((1 - nonacuteDirectRotation U V J) ∘L U.subtypeL).approximationNumber n ≤
        ((1 - W) ∘L U.subtypeL).approximationNumber n :=
    proposition4_1_nonacute_approximationNumbers U V J W hWunitary hWmap
  have hUperp : ∀ n,
      ((1 - nonacuteDirectRotation U V J) ∘L U.orthogonal.subtypeL).approximationNumber n ≤
        ((1 - W) ∘L U.orthogonal.subtypeL).approximationNumber n := by
    intro n
    have h := proposition4_1_nonacute_approximationNumbers U.orthogonal V.orthogonal
      (orthogonalCrossedDefectEquiv U V J) W hWunitary
      (competitor_admissible_orthogonal_complex U V W hWmap) n
    rwa [nonacuteDirectRotation_orthogonal U V J] at h
  have hblock := kyFanApproximationGauge_blockSum_le
    (fun j => kyFanApproximationGauge_gramOperator_mono_complex _ _ hU j)
    (fun j => kyFanApproximationGauge_gramOperator_mono_complex _ _ hUperp j) k
  calc kyFanApproximationGauge k
        ((1 - star (nonacuteDirectRotation U V J)) *
          (1 - nonacuteDirectRotation U V J))
      = kyFanApproximationGauge k (U.diagonalPart
          ((1 - star (nonacuteDirectRotation U V J)) *
            (1 - nonacuteDirectRotation U V J))) := by
        rw [diagonalPart_nonacuteDirectRotation_displacementSquare_complex U V J]
    _ = kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - nonacuteDirectRotation U V J) ∘L U.subtypeL))
          (gramOperator ((1 - nonacuteDirectRotation U V J) ∘L U.orthogonal.subtypeL))) := hchart _
    _ ≤ kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperator ((1 - W) ∘L U.subtypeL))
          (gramOperator ((1 - W) ∘L U.orthogonal.subtypeL))) := hblock
    _ = kyFanApproximationGauge k
          (U.diagonalPart ((1 - star W) * (1 - W))) := (hchart W).symm
    _ ≤ kyFanApproximationGauge k ((1 - star W) * (1 - W)) :=
        kyFanApproximationGauge_diagonalPart_le_complex U _ k

end

end Section4
end DavisKahan
end TauCeti
