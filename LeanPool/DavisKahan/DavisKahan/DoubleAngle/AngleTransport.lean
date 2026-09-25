/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.Unbounded
public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-! # Angle Transport -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Angle doubling at the operator level, and the ideal transport it gives

The unbounded `sin 2Θ` theorems conclude about `sinTwoThetaIdealBlock U V`, the
overlap of `U` with the `V`-reflection of `Uᗮ`.  That block is an excellent proof
vehicle in a symmetric ideal, and it is not the object the paper names.  Until
now the only bridge to the paper's `sin 2Θ` was
`norm_starProjection_reflectedComplementary_eq_sinTwoAngle`, an equality of
**operator norms**, which is exactly one number and therefore says nothing in any
other unitarily invariant norm.

This module proves the bridge at full strength:

`directedSinAngleOperatorC U (U.map V.reflection) = directedSinTwoAngleOperatorC U V`

-- the directed sine of the angle between `U` and its `V`-reflection **is** the
sine of twice the angle between `U` and `V`, as operators.  Everything a
symmetric ideal can see is then automatic: approximation numbers agree term by
term, so membership and gauge agree in every symmetric ideal family, not just at
the operator norm.

## The proof

With `p = P_U`, `q = P_V` and `t = p q p`, the reflection is `r = 2q - 1` and the
whole content is one identity in the ring of bounded operators, needing only
`p² = p`:

`p r p r p = 4 t² - 4 t + p`.

Both sides of the theorem square to `4(t - t²)`:

* the reflected sine, because `|P_{Wᗮ} P_U|² = p - p P_W p = p - p r p r p`;
* the paper's operator, because `sin²Θ = p - t`, `cos²Θ = t`, they commute, and
  `(2 sin cos)² = 4 sin² cos² = 4(p - t)t = 4(t - t²)`.

Both are nonnegative, so the positive square root is unique and they are equal.
-/

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta


universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The whole content of angle doubling, as ring algebra.**

Only idempotence of `p` is used; `q` is arbitrary.  With `r = 2q - 1` the
reflection and `t = p q p`, sandwiching the reflected idempotent between two
copies of `p` gives `4t² - 4t + p`. -/
private theorem proj_reflect_sandwich {A : Type*} [Ring A] {p q : A}
    (hp : p * p = p) :
    p * (2 * q - 1) * (p * ((2 * q - 1) * p))
      = 4 * ((p * q * p) * (p * q * p)) - 4 * (p * q * p) + p := by
  have hppqp : p * (p * q * p) = p * q * p := by
    rw [← mul_assoc, ← mul_assoc, hp]
  have hpqpp : (p * q * p) * p = p * q * p := by
    rw [mul_assoc, hp]
  noncomm_ring
  simp only [mul_assoc] at *
  noncomm_ring [hp, hppqp, hpqpp]

omit [CompleteSpace E] in
/-- Orthogonal projections are idempotent, as an operator identity. -/
private theorem starProjection_mul_self (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] :
    W.starProjection * W.starProjection = W.starProjection := by
  ext x
  change W.starProjection (W.starProjection x) = W.starProjection x
  rw [Submodule.starProjection_eq_self_iff]
  exact W.starProjection_apply_mem x

omit [CompleteSpace E] in
/-- The reflection in `V`, as a bounded operator, is `2 P_V - 1`. -/
theorem reflection_toContinuousLinearMap (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] :
    V.reflection.toLinearIsometry.toContinuousLinearMap
      = 2 * V.starProjection - (1 : E →L[ℂ] E) := by
  ext x
  simp [Submodule.reflection_apply, two_smul]


/-- The Gram operator of a cross projection product, with both projections
self-adjoint. -/
private theorem gram_cross (U W : Submodule ℂ E)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    (W.starProjection ∘L U.starProjection).adjoint ∘L
        (W.starProjection ∘L U.starProjection)
      = U.starProjection * W.starProjection * U.starProjection := by
  rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection W).star_eq]
  have h : W.starProjection * W.starProjection = W.starProjection :=
    starProjection_mul_self W
  calc U.starProjection ∘L W.starProjection ∘L W.starProjection ∘L U.starProjection
      = U.starProjection * (W.starProjection * W.starProjection) * U.starProjection := by
        simp only [mul_assoc]; rfl
    _ = U.starProjection * W.starProjection * U.starProjection := by rw [h]

/-- The square of the directed sine operator is `P_U P_{Vᗮ} P_U`. -/
theorem directedSinAngleOperatorC_mul_self (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSinAngleOperatorC U V * directedSinAngleOperatorC U V
      = U.starProjection * Vᗮ.starProjection * U.starProjection := by
  rw [directedSinAngleOperatorC, ContinuousLinearMap.modulus_mul_self]
  exact gram_cross U Vᗮ

/-- The square of the cosine operator is `P_U P_V P_U`. -/
theorem directedCosAngleOperatorC_mul_self (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedCosAngleOperatorC U V * directedCosAngleOperatorC U V
      = U.starProjection * V.starProjection * U.starProjection := by
  rw [directedCosAngleOperatorC, ContinuousLinearMap.modulus_mul_self]
  exact gram_cross U V

omit [CompleteSpace E] in
/-- `P_{Uᗮ} = 1 - P_U` as bounded operators. -/
theorem starProjection_orthogonal_eq (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = (1 : E →L[ℂ] E) - U.starProjection := by
  ext x
  simp



section Doubling

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Abbreviation for the two-projection operator `t = P_U P_V P_U`, whose
spectrum carries the squared principal cosines. -/
private noncomputable def crossT : E →L[ℂ] E :=
  U.starProjection * V.starProjection * U.starProjection

omit [CompleteSpace E] in
private theorem starProjection_mul_crossT :
    U.starProjection * crossT U V = crossT U V := by
  rw [crossT, ← mul_assoc, ← mul_assoc, starProjection_mul_self]

/-- **The paper's `sin 2Θ` squares to `4(t - t²)`.** -/
theorem directedSinTwoAngleOperatorC_mul_self :
    directedSinTwoAngleOperatorC U V * directedSinTwoAngleOperatorC U V
      = (4 : ℝ) • (crossT U V - crossT U V * crossT U V) := by
  have hcomm := commute_directedSinAngleOperatorC_directedCosAngleOperatorC U V
  have hsin : directedSinAngleOperatorC U V * directedSinAngleOperatorC U V
      = U.starProjection - crossT U V := by
    rw [directedSinAngleOperatorC_mul_self, starProjection_orthogonal_eq, crossT]
    noncomm_ring [starProjection_mul_self U]
  have hcos : directedCosAngleOperatorC U V * directedCosAngleOperatorC U V = crossT U V :=
    directedCosAngleOperatorC_mul_self U V
  rw [directedSinTwoAngleOperatorC, smul_mul_smul_comm]
  have hrearrange :
      directedSinAngleOperatorC U V * directedCosAngleOperatorC U V *
          (directedSinAngleOperatorC U V * directedCosAngleOperatorC U V)
        = (directedSinAngleOperatorC U V * directedSinAngleOperatorC U V) *
            (directedCosAngleOperatorC U V * directedCosAngleOperatorC U V) := by
    calc directedSinAngleOperatorC U V * directedCosAngleOperatorC U V *
            (directedSinAngleOperatorC U V * directedCosAngleOperatorC U V)
        = directedSinAngleOperatorC U V *
            (directedCosAngleOperatorC U V * directedSinAngleOperatorC U V) *
              directedCosAngleOperatorC U V := by noncomm_ring
      _ = directedSinAngleOperatorC U V *
            (directedSinAngleOperatorC U V * directedCosAngleOperatorC U V) *
              directedCosAngleOperatorC U V := by rw [hcomm.symm.eq]
      _ = (directedSinAngleOperatorC U V * directedSinAngleOperatorC U V) *
            (directedCosAngleOperatorC U V * directedCosAngleOperatorC U V) := by noncomm_ring
  rw [hrearrange, hsin, hcos, sub_mul, starProjection_mul_crossT]
  norm_num

/-- The paper's `sin 2Θ` operator is nonnegative: it is twice a product of two
commuting nonnegative operators. -/
theorem directedSinTwoAngleOperatorC_nonneg : 0 ≤ directedSinTwoAngleOperatorC U V := by
  rw [directedSinTwoAngleOperatorC]
  refine smul_nonneg (by norm_num) ?_
  exact (commute_iff_mul_nonneg (directedSinAngleOperatorC_nonneg U V)
    (directedCosAngleOperatorC_nonneg U V)).mp
      (commute_directedSinAngleOperatorC_directedCosAngleOperatorC U V)

end Doubling



section Reflected

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The `V`-reflection of `U`**: the image of `U` under the reflection in `V`.
This is the subspace the unbounded `sin 2Θ` ideal block overlaps `U` with, and the
subspace whose angle with `U` is twice the angle between `U` and `V`. -/
noncomputable abbrev reflectedU : Submodule ℂ E :=
  U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)

omit [CompleteSpace E] in
/-- The projection onto the reflected subspace is the reflection conjugate of the
projection, written out as `R P_U R`. -/
theorem starProjection_reflectedU :
    (reflectedU U V).starProjection
      = (2 * V.starProjection - 1) * U.starProjection *
          (2 * V.starProjection - 1) := by
  rw [starProjection_map_unitary U V.reflection, boundedUnitaryConjugate,
    Submodule.reflection_symm]
  rw [← reflection_toContinuousLinearMap V]
  rfl

/-- **The reflected directed sine squares to `4(t - t²)` as well.** -/
theorem directedSinAngleOperatorC_reflected_mul_self :
    directedSinAngleOperatorC U (reflectedU U V) *
        directedSinAngleOperatorC U (reflectedU U V)
      = (4 : ℝ) • (crossT U V - crossT U V * crossT U V) := by
  have hfour : ∀ z : E →L[ℂ] E, (4 : ℝ) • z = 4 * z := by
    intro z; ext y; simp; module
  have hp : U.starProjection * U.starProjection = U.starProjection :=
    starProjection_mul_self U
  have hsandwich := proj_reflect_sandwich (p := U.starProjection)
    (q := V.starProjection) hp
  rw [directedSinAngleOperatorC_mul_self, starProjection_orthogonal_eq,
    starProjection_reflectedU]
  have hgoal :
      U.starProjection *
          ((1 : E →L[ℂ] E) -
            (2 * V.starProjection - 1) * U.starProjection *
              (2 * V.starProjection - 1)) * U.starProjection
        = U.starProjection -
            U.starProjection * (2 * V.starProjection - 1) *
              (U.starProjection *
                ((2 * V.starProjection - 1) * U.starProjection)) := by
    rw [mul_sub, sub_mul, mul_one, hp]
    noncomm_ring
  rw [hgoal, hsandwich, crossT, hfour]
  noncomm_ring

end Reflected



section Transport

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Angle doubling, as an operator identity.**

The directed sine of the angle between `U` and its `V`-reflection *is* the sine
of twice the angle between `U` and `V`.  The previously available bridge,
`norm_starProjection_reflectedComplementary_eq_sinTwoAngle`, is the norm of this
equation and therefore says nothing about any other unitarily invariant norm;
this says everything, because the two operators are equal. -/
theorem directedSinAngleOperatorC_reflected_eq_directedSinTwoAngleOperatorC :
    directedSinAngleOperatorC U (reflectedU U V) = directedSinTwoAngleOperatorC U V := by
  have hsq : directedSinAngleOperatorC U (reflectedU U V) ^ 2
      = directedSinTwoAngleOperatorC U V ^ 2 := by
    rw [pow_two, pow_two, directedSinAngleOperatorC_reflected_mul_self,
      directedSinTwoAngleOperatorC_mul_self]
  calc directedSinAngleOperatorC U (reflectedU U V)
      = CFC.sqrt (directedSinAngleOperatorC U (reflectedU U V) ^ 2) :=
        (CFC.sqrt_sq _ (directedSinAngleOperatorC_nonneg _ _)).symm
    _ = CFC.sqrt (directedSinTwoAngleOperatorC U V ^ 2) := by rw [hsq]
    _ = directedSinTwoAngleOperatorC U V :=
        CFC.sqrt_sq _ (directedSinTwoAngleOperatorC_nonneg U V)

omit [CompleteSpace E] in
/-- The reflected complement of `U` is the orthogonal complement of the reflected
`U`, at the level of their projections. -/
theorem starProjection_map_orthogonal_reflection :
    (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection
      = (reflectedU U V)ᗮ.starProjection := by
  have h : (reflectedU U V)ᗮ.starProjection
      = boundedUnitaryConjugate V.reflection Uᗮ.starProjection := by
    ext x
    rw [Submodule.starProjection_orthogonal_apply, boundedUnitaryConjugate_apply,
      Submodule.starProjection_orthogonal_apply, map_sub,
      V.reflection.apply_symm_apply, Submodule.starProjection_map_apply]
  rw [h, starProjection_map_unitary Uᗮ V.reflection]

/-- **The ideal block and the paper's `sin 2Θ` have the same approximation
numbers.**

This is the transport the unbounded `sin 2Θ` theorems need: approximation numbers
determine membership and gauge in *every* symmetric operator ideal, so a bound
proved for `sinTwoThetaIdealBlock U V` is a bound for the paper's object in every
unitarily invariant norm, not only at the operator norm. -/
theorem sinTwoThetaIdealBlock_hasSameApproximationNumbers :
    (sinTwoThetaIdealBlock U V).HasSameApproximationNumbers
      (directedSinTwoAngleOperatorC U V) := by
  intro n
  have hblock : sinTwoThetaIdealBlock U V
      = U.starProjection ∘L (reflectedU U V)ᗮ.starProjection := by
    rw [sinTwoThetaIdealBlock, starProjection_map_orthogonal_reflection]
  have hadj : (sinTwoThetaIdealBlock U V).adjoint
      = (reflectedU U V)ᗮ.starProjection ∘L U.starProjection := by
    rw [hblock, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection (reflectedU U V)ᗮ).star_eq]
  have hmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers
    ((reflectedU U V)ᗮ.starProjection ∘L U.starProjection) n
  rw [show ((reflectedU U V)ᗮ.starProjection ∘L U.starProjection).modulus
      = directedSinTwoAngleOperatorC U V from by
        rw [← directedSinAngleOperatorC,
          directedSinAngleOperatorC_reflected_eq_directedSinTwoAngleOperatorC]] at hmod
  rw [hmod, ← hadj, ContinuousLinearMap.approximationNumber_adjoint]

end Transport



section NormTransport


variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The ideal block and the paper's `sin 2Θ` have the same gauge in every
source unitarily invariant norm**, and one lies in the norm's ideal exactly when
the other does.

This is the statement the unbounded theorems consume: it upgrades the old
operator-norm identification to every `SymmetricNormingFunction` at once,
because a paper norm's extended gauge is determined by the approximation
singular-value sequence and the two sequences are equal. -/
theorem extendedGauge_sinTwoThetaIdealBlock_complex (N : SymmetricNormingFunction) :
    N.extendedGauge (sinTwoThetaIdealBlock U V)
      = N.extendedGauge (directedSinTwoAngleOperatorC U V) :=
  N.gauge_eq_of_sameApproximationSingularValues
    (sinTwoThetaIdealBlock_hasSameApproximationNumbers U V)

/-- Ideal membership transfers between the block and the paper's operator. -/
theorem mem_directedSinTwoAngleOperatorC_iff (N : SymmetricNormingFunction) :
    N.Mem (directedSinTwoAngleOperatorC U V) ↔ N.Mem (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_sinTwoThetaIdealBlock_complex U V N]

/-- The gauge transfers between the block and the paper's operator. -/
theorem gauge_directedSinTwoAngleOperatorC (N : SymmetricNormingFunction) :
    N.gauge (directedSinTwoAngleOperatorC U V) = N.gauge (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_sinTwoThetaIdealBlock_complex U V N]

end NormTransport


end DavisKahan
end TauCeti
