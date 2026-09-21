/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaAmbient
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.TangentTransfer

/-! # Tangent Singular Values -/

open TauCeti.DavisKahan.Angle


/-!
# The ambient tangents have the tangents of the principal angles as singular values

Davis and Kahan's Section 2 tangent conclusions are inequalities about `‖tan Θ‖` and
`‖tan 2Θ‖`, where a unitarily invariant norm is a symmetric norming function of a
*singular-value sequence*.  So the source content of `δ ‖tan Θ‖ ≤ ‖H‖` is a statement
about the sequence

```
tan θ₀, tan θ₁, …
```

of tangents of the principal angles, and the repository's operator `tan Θ` carries that
content only once its approximation numbers are known to be exactly those tangents.

This module proves that, for both ambient angle operators:

* `aₙ(tan Θ) = tan (arcsin aₙ(sin Θ))` under uniform transversality;
* `aₙ(|tan 2Θ|) = tan (arcsin aₙ(sin 2Θ))` under uniform *quarter* transversality.

Together with `directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub`, which identifies
`sin 2Θ` with the modulus of the projector difference between `U` and its mirror image in
`V`, the second statement reads the doubled tangent off the same projector geometry the
`sin 2Θ` theorem uses.

## Why the identity, and not just one inequality

`ForTauCeti`'s Gram resolvent estimate already gave `aₙ(tan Θ) ≤ tan (arcsin aₙ(sin Θ))`,
which is the direction the operator-level Section 2 estimate needs.  The *reverse*
direction is what a sequence-level statement needs, and its own module used to record it
as out of reach.  It is not: the reverse inequality for the monotone transfer
`u ↦ u/(1−u)` is the forward inequality for its inverse `u ↦ u/(1+u)`, which is
`TauCeti.ApproximationNumber.approximationNumber_le_of_gramContraction`.  Both directions
together are `approximationNumber_eq_tanArcsin`, and the only input either needs is the
Pythagorean operator identity `tan²Θ (1 − sin²Θ) = sin²Θ`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46: the Section 2 `tan θ` and `tan 2θ` theorems, and
  Section 1 on unitarily invariant norms as symmetric norming functions.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.ApproximationNumber

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

section SingleAngle

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The ambient tangent's singular values are the tangents of the principal angles.**

`aₙ(tan Θ) = tan (arcsin aₙ(sin Θ))` for every `n`, under the uniform transversality the
Section 2 tangent theorem derives from its own hypotheses.

This is the statement that makes `‖tan Θ‖` in the printed theorem a norm of the sequence
`tan θ₀, tan θ₁, …` rather than merely of some operator called `tan Θ`. -/
theorem approximationNumber_tanAngleOperatorC
    (htr : ‖sinAngleOperatorC U V‖ < 1) (n : ℕ) :
    (tanAngleOperatorC U V).approximationNumber n =
      Real.tan (Real.arcsin ((sinAngleOperatorC U V).approximationNumber n)) := by
  refine approximationNumber_eq_tanArcsin (isSelfAdjoint_sinAngleOperatorC U V)
    (isSelfAdjoint_tanAngleOperatorC U V) htr ?_ n
  have h := tan_sq_mul_one_sub_sin_sq (U := U) (V := V) htr
  rw [mul_sub, mul_one] at h
  exact sub_eq_iff_eq_add.mp h

/-- The ambient sine's singular values are those of the projector difference: the modulus
does not move an approximation number. -/
theorem approximationNumber_sinAngleOperatorC (n : ℕ) :
    (sinAngleOperatorC U V).approximationNumber n =
      (V.starProjection - U.starProjection).approximationNumber n := by
  rw [sinAngleOperatorC,
    ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (U.starProjection - V.starProjection) n]
  have hneg : U.starProjection - V.starProjection =
      ((-1 : ℂ)) • (V.starProjection - U.starProjection) := by
    module
  rw [hneg, ContinuousLinearMap.approximationNumber_smul]
  simp

end SingleAngle

section DoubleAngle

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The doubled angle avoids the tangent's poles exactly when the ambient double-angle
sine is a strict contraction: `|sin 2θ| < 1` is `cos 2θ ≠ 0`. -/
theorem norm_sinTwoAngleOperatorC_lt_one
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ‖sinTwoAngleOperatorC U V‖ < 1 := by
  rw [sinTwoAngleOperatorC]
  refine norm_cfc_lt one_pos fun t ht => ?_
  have hc := hcos t ht
  have hpyth : Real.sin (2 * t) ^ 2 + Real.cos (2 * t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc2 : 0 < Real.cos (2 * t) ^ 2 := by positivity
  have hs2 : Real.sin (2 * t) ^ 2 < 1 := by nlinarith
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (Real.sin (2 * t)), sq_abs (Real.sin (2 * t))]

/-- **`tan²2Θ · cos²2Θ = sin²2Θ`**, the doubled-angle Pythagoras, as an operator identity
of functional calculi of the operator angle.

The hypothesis is the printed theorem's own pole exclusion, which Section 7 *derives*:
`cos 2θ ≠ 0` throughout the spectrum of the angle.  No branch condition is needed, because
`|tan 2θ|` is what a unitarily invariant norm sees. -/
theorem absTanTwo_sq_mul_one_sub_sinTwo_sq
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    absTanTwoAngleOperatorC U V * absTanTwoAngleOperatorC U V *
        (1 - sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V) =
      sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V := by
  have hsa : IsSelfAdjoint (angleOperatorC U V) := isSelfAdjoint_angleOperatorC U V
  have hs : ContinuousOn (fun t : ℝ => Real.sin (2 * t))
      (spectrum ℝ (angleOperatorC U V)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have ht : ContinuousOn (fun t : ℝ => |Real.tan (2 * t)|)
      (spectrum ℝ (angleOperatorC U V)) := by
    refine ContinuousOn.abs ?_
    exact Real.continuousOn_tan.comp
      ((continuous_const.mul continuous_id).continuousOn) hcos
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ))
      (spectrum ℝ (angleOperatorC U V)) := continuousOn_const
  have hSS : sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V =
      cfc (fun t : ℝ => Real.sin (2 * t) * Real.sin (2 * t)) (angleOperatorC U V) := by
    rw [sinTwoAngleOperatorC,
      ← cfc_mul (fun t : ℝ => Real.sin (2 * t)) (fun t : ℝ => Real.sin (2 * t))
        (angleOperatorC U V) hs hs]
  have hcosop : 1 - sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V =
      cfc (fun t : ℝ => 1 - Real.sin (2 * t) * Real.sin (2 * t))
        (angleOperatorC U V) := by
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ))
      (fun t : ℝ => Real.sin (2 * t) * Real.sin (2 * t)) (angleOperatorC U V)
      hone (hs.mul hs), cfc_const_one ℝ (angleOperatorC U V), ← hSS]
  rw [absTanTwoAngleOperatorC, hcosop,
    ← cfc_mul (fun t : ℝ => |Real.tan (2 * t)|) (fun t : ℝ => |Real.tan (2 * t)|)
      (angleOperatorC U V) ht ht,
    ← cfc_mul (fun t : ℝ => |Real.tan (2 * t)| * |Real.tan (2 * t)|)
      (fun t : ℝ => 1 - Real.sin (2 * t) * Real.sin (2 * t)) (angleOperatorC U V)
      (ht.mul ht) (hone.sub (hs.mul hs)), hSS]
  refine cfc_congr fun t htmem => ?_
  have hc := hcos t htmem
  have hpyth : Real.sin (2 * t) ^ 2 + Real.cos (2 * t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have htan : Real.tan (2 * t) = Real.sin (2 * t) / Real.cos (2 * t) :=
    Real.tan_eq_sin_div_cos _
  have habs : |Real.tan (2 * t)| * |Real.tan (2 * t)| =
      Real.tan (2 * t) * Real.tan (2 * t) := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  rw [habs, htan]
  field_simp
  nlinarith [hpyth]

/-- **The ambient doubled tangent's singular values are the tangents of the doubled
principal angles.**

`aₙ(|tan 2Θ|) = tan (arcsin aₙ(sin 2Θ))` under the printed theorem's own derived pole
exclusion.  Note the right-hand side is `tan ∘ arcsin` of a *sine*, so it is `|tan 2θₙ|`
however far the doubled angle runs past a right angle — the branch-free reading a
unitarily invariant norm forces. -/
theorem approximationNumber_absTanTwoAngleOperatorC
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) (n : ℕ) :
    (absTanTwoAngleOperatorC U V).approximationNumber n =
      Real.tan (Real.arcsin
        ((sinTwoAngleOperatorC U V).approximationNumber n)) := by
  refine approximationNumber_eq_tanArcsin (isSelfAdjoint_sinTwoAngleOperatorC U V)
    (isSelfAdjoint_absTanTwoAngleOperatorC U V)
    (norm_sinTwoAngleOperatorC_lt_one U V hcos) ?_ n
  have h := absTanTwo_sq_mul_one_sub_sinTwo_sq U V hcos
  rw [mul_sub, mul_one] at h
  exact sub_eq_iff_eq_add.mp h

/-- The ambient double-angle sine's singular values are those of the projector difference
between `U` and its mirror image in `V` — the operator the `sin 2Θ` theorem bounds. -/
theorem approximationNumber_sinTwoAngleOperatorC (n : ℕ) :
    (sinTwoAngleOperatorC U V).approximationNumber n =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
        U.starProjection).approximationNumber n := by
  rw [directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub]
  exact ContinuousLinearMap.modulus_hasSameApproximationNumbers _ n

/-- **The ambient doubled tangent, read off the ambient double-angle sine.**

`aₙ(|tan 2Θ|) = tan (arcsin aₙ(sin 2Θ))` with the double-angle sine presented as
the projector difference between `U` and its mirror image in `V` -- the very
operator the `sin 2Θ` theorem bounds, so a `tan 2Θ` statement and a `sin 2Θ`
statement speak about the same angle with the same multiplicity.

**The doubled angle must be presented by its own sine.**  It is *not* true in
general that `aₙ(sin 2Θ) = sin (2 arcsin aₙ(sin Θ))`: `θ ↦ sin 2θ` is not
monotone on `[0, π/2]`, so applying it index by index to the ordered sequence of
`sin Θ` need not produce an ordered sequence.  Principal angles `75°` and `30°`
already break it -- `sin 75° > sin 30°` while `sin 150° < sin 60°`.  Only the
monotone `u ↦ tan (arcsin u)` may be applied to an approximation-number
sequence, and here it is applied to the doubled sine, not the single one. -/
theorem approximationNumber_absTanTwoAngleOperatorC_projectorDifference
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (n : ℕ) :
    (absTanTwoAngleOperatorC U V).approximationNumber n =
      Real.tan (Real.arcsin
        (((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
          U.starProjection).approximationNumber n)) := by
  rw [approximationNumber_absTanTwoAngleOperatorC U V hcos n,
    approximationNumber_sinTwoAngleOperatorC U V n]

/-- Under the derived pole exclusion the ambient double-angle sine is a strict
contraction, so each `tan (arcsin aₙ)` above is a genuine tangent and not the
value Lean's field division assigns at a pole. -/
theorem approximationNumber_projectorDifference_lt_one
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (n : ℕ) :
    ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
      U.starProjection).approximationNumber n < 1 := by
  rw [← approximationNumber_sinTwoAngleOperatorC U V n]
  exact lt_of_le_of_lt (ContinuousLinearMap.approximationNumber_le_norm _ n)
    (norm_sinTwoAngleOperatorC_lt_one U V hcos)

end DoubleAngle

end

end DavisKahan1970
end TauCeti
