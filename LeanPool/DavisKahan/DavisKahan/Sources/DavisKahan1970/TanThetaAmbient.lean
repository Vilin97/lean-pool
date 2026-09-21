/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TanAngleFunctionalCalculus
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientBlockVocabulary
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CrossedDefectGap
-- supplies the standing assumption (3.5) and the gap identity it buys, which is what
-- turns this file's directed sine estimate into the ambient uniform transversality the
-- tangent theorem consumes.  That module imports only `BoundedOperator/Compat` and
-- `Geometry/Halmos/GenericRotationPredicates`, so the dependency is acyclic.
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramResolvent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Tan Theta Ambient -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The whole-space half of the `tan Θ` theorem

Section 2 of Davis--Kahan 1970 states the `tan θ` theorem with **two**
conclusions,

`δ ‖tan Θ₀‖ ≤ ‖R‖`  and  `δ ‖tan Θ‖ ≤ ‖H‖`,

for every unitarily invariant norm.  The directed `Θ₀` half is in the build
through Theorem 6.3.  This module proves the ambient `Θ` half, the assertion the
paper settles in Section 7 just after equation (7.6).

## The route, and where it departs from the printed one

The paper writes the ambient tangent as an off-diagonal `2 × 2` block operator

`tan Θ ≅ [[0, -J₀⋆ tan Θ₁], [J₀ tan Θ₀, 0]]`,

bounds each corner by `‖B‖/δ` using `‖J₀ tan Θ₀‖ = ‖J₀⋆ tan Θ₁‖ = ‖tan Θ₀‖`,
couples the two corners with Lemma 6.1 and contracts with the Lemma 6.2 pinch
applied with the two decompositions crossed.

The formalisation follows that shape but builds the off-diagonal representative
*explicitly*, which removes both the direct-rotation polar factor `J₀` and the
complementary angle `Θ₁` from the argument.  Writing `p` for the orthogonal
projection onto `U`, `D = P_V − P_U`, and `s = D²` (`= sin²Θ`), the operator

`Ξ = ((1−p) D p + p D (1−p)) (1 − s)⁻¹`

is off-diagonal for `U ⊕ U^⊥` by construction, and

`Ξ⋆Ξ = s (1 − s)⁻¹ = tan²Θ`,

so `|Ξ| = tan Θ` exactly — the ambient tangent and the block representative have
the same modulus, hence the same value under every unitarily invariant norm.
The only geometric input is the two-projection identity `D p + p D + D² = D`.

Because `D` is self-adjoint and commutes with `(1 − s)⁻¹`, the two corners of
`Ξ` are adjoints of one another, and so are the two corners of the self-adjoint
perturbation `H`.  The complementary estimate the paper obtains from
`‖J₀⋆ tan Θ₁‖ = ‖tan Θ₀‖` is therefore free here: it is the adjoint of the
directed one, and the equality of the nonzero spectra of `Θ₀` and `Θ₁` never has
to be proved.

The directed corner is Theorem 6.3.  Its Ky Fan core is stated in terms of the
scalars `tan (arcsin σₙ)` of the directed sine block, so the corner's own
approximation numbers have to be transferred through the monotone map
`u ↦ u/(1−u)`; `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent`
is that transfer, proved by a Gram spectral cut.

## Scope

Arbitrary complete complex Hilbert space, no dimension or compactness
hypothesis, every Ky Fan gauge and hence every unitarily invariant norm in the
paper's sense.  The trial subspace `U` is arbitrary: the infinite-dimensional
passage is already carried by `theorem6_3_all_kyFan_core_infiniteTrial`.

Uniform transversality `‖sin Θ‖ < 1` is a hypothesis.  It is what makes `tan Θ`
a tangent at all — Mathlib's `Real.tan` is total, so `cfc Real.tan Θ` exists
without it but is not the paper's object — and it is exactly the condition under
which the printed right-hand side can be finite.

## Main results

* `TauCeti.DavisKahan1970.tanBlockRepresentative`: the explicit off-diagonal
  representative `Ξ`.
* `TauCeti.DavisKahan1970.directedTanAngleOperatorC_eq_modulus_blockRepresentative`:
  `|Ξ| = tan Θ`.
* `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_kyFan_complex_of_transversality`: the Ky Fan form,
  `δ · kyFan_k (tan Θ) ≤ kyFan_k H` for every `k`.
* `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality`: the source form,
  `δ N(tan Θ) ≤ N(H)` for every unitarily invariant norm `N` in the paper's
  sense.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the `tan θ` theorem of Section 2,
  Lemmas 6.1 and 6.2, Theorem 6.3, and the Section 7 derivation around equation
  (7.6).
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ApproximationNumber

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

/-! ### Two-projection algebra

Everything the block representative needs about the geometry of a pair of
subspaces follows from a single relation between `D = q − p` and one of the two
idempotents.  The lemmas below are stated for an abstract ring so that the
projection-specific rewriting happens exactly once. -/

section ProjectionAlgebra

variable {A : Type*} [Ring A]

/-- **The two-projection relation.**  For idempotents `p`, `q` and their
difference `D = q − p`, the anticommutator of `D` with `p` is `D − D²`.  This is
the only geometric input the ambient tangent argument uses. -/
theorem twoProjection_anticommutator {p q : A} (hp : p * p = p) (hq : q * q = q) :
    (q - p) * p + p * (q - p) + (q - p) * (q - p) = q - p := by
  simp only [sub_mul, mul_sub, hp, hq]
  abel

variable {p D : A}

private theorem sq_eq_sub (hkey : D * p + p * D + D * D = D) :
    D * D = D - D * p - p * D := by
  have h : D * D = D - (D * p + p * D) := eq_sub_of_add_eq' hkey
  rw [h]
  abel

private theorem proj_mul_sq (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = -(p * D * p) := by
  have e1 : p * (D * p) = p * D * p := (mul_assoc p D p).symm
  have e2 : p * (p * D) = p * D := by rw [← mul_assoc, hp]
  rw [sq_eq_sub hkey, mul_sub, mul_sub, e1, e2]
  abel

private theorem sq_mul_proj (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    D * D * p = -(p * D * p) := by
  have e3 : D * p * p = D * p := by rw [mul_assoc, hp]
  rw [sq_eq_sub hkey, sub_mul, sub_mul, e3]
  abel

private theorem proj_mul_mul_proj (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    p * D * p = -(D * D * p) := by
  rw [sq_mul_proj hp hkey, neg_neg]

private theorem proj_comm_sq (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = D * D * p := by
  rw [proj_mul_sq hp hkey, sq_mul_proj hp hkey]

private theorem compl_comm_sq (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    (1 - p) * (D * D) = D * D * (1 - p) := by
  have h := proj_comm_sq hp hkey
  simp only [sub_mul, mul_sub, one_mul, mul_one, h]

private theorem compl_idem (hp : p * p = p) : (1 - p) * (1 - p) = 1 - p := by
  have h : (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
  rw [h, hp]
  abel

private theorem compl_mul_mul_compl (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    (1 - p) * D * (1 - p) = D * D * (1 - p) := by
  have hexp : (1 - p) * D * (1 - p) = D - D * p - p * D + p * D * p := by noncomm_ring
  rw [hexp, ← sq_eq_sub hkey, proj_mul_mul_proj hp hkey, mul_sub, mul_one]
  abel

/-- The upper-left corner of the off-diagonal part of `D`, squared. -/
private theorem upper_mul_lower (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    (p * D * (1 - p)) * ((1 - p) * D * p) = (D * D - D * D * (D * D)) * p := by
  have hfold : (p * D * (1 - p)) * ((1 - p) * D * p)
      = p * D * ((1 - p) * (1 - p)) * D * p := by noncomm_ring
  have hsplit : p * D * (1 - p) * D * p = p * D * D * p - (p * D * p) * (D * p) := by
    noncomm_ring
  have h2 : p * D * D * p = D * D * p := by
    rw [mul_assoc p D D, proj_comm_sq hp hkey, mul_assoc (D * D) p p, hp]
  have h3 : (p * D * p) * (D * p) = D * D * (D * D) * p := by
    rw [proj_mul_mul_proj hp hkey]
    have e2 : (-(D * D * p)) * (D * p) = -(D * D * (p * D * p)) := by noncomm_ring
    rw [e2, proj_mul_mul_proj hp hkey]
    noncomm_ring
  rw [hfold, compl_idem hp, hsplit, h2, h3]
  noncomm_ring

/-- The lower-right corner of the off-diagonal part of `D`, squared. -/
private theorem lower_mul_upper (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    ((1 - p) * D * p) * (p * D * (1 - p))
      = (D * D - D * D * (D * D)) * (1 - p) := by
  have hfold : ((1 - p) * D * p) * (p * D * (1 - p))
      = (1 - p) * D * (p * p) * D * (1 - p) := by noncomm_ring
  have hsplit : (1 - p) * D * p * D * (1 - p)
      = (1 - p) * D * D * (1 - p)
        - ((1 - p) * D * (1 - p)) * (D * (1 - p)) := by
    have hp' : p = 1 - (1 - p) := by abel
    rw [hp']
    noncomm_ring
  have h2 : (1 - p) * D * D * (1 - p) = D * D * (1 - p) := by
    rw [mul_assoc (1 - p) D D, compl_comm_sq hp hkey,
      mul_assoc (D * D) (1 - p) (1 - p), compl_idem hp]
  have h3 : ((1 - p) * D * (1 - p)) * (D * (1 - p)) = D * D * (D * D) * (1 - p) := by
    rw [compl_mul_mul_compl hp hkey]
    have e : (D * D * (1 - p)) * (D * (1 - p)) = D * D * ((1 - p) * D * (1 - p)) := by
      noncomm_ring
    rw [e, compl_mul_mul_compl hp hkey]
    noncomm_ring
  rw [hfold, hp, hsplit, h2, h3]
  noncomm_ring

private theorem lower_sq (hp : p * p = p) :
    ((1 - p) * D * p) * ((1 - p) * D * p) = 0 := by
  have hfold : ((1 - p) * D * p) * ((1 - p) * D * p)
      = (1 - p) * D * (p * (1 - p)) * D * p := by noncomm_ring
  have hzero : p * (1 - p) = 0 := by
    have h : p * (1 - p) = p - p * p := by noncomm_ring
    rw [h, hp, sub_self]
  rw [hfold, hzero]
  noncomm_ring

private theorem upper_sq (hp : p * p = p) :
    (p * D * (1 - p)) * (p * D * (1 - p)) = 0 := by
  have hfold : (p * D * (1 - p)) * (p * D * (1 - p))
      = p * D * ((1 - p) * p) * D * (1 - p) := by noncomm_ring
  have hzero : (1 - p) * p = 0 := by
    have h : (1 - p) * p = p - p * p := by noncomm_ring
    rw [h, hp, sub_self]
  rw [hfold, hzero]
  noncomm_ring

/-- **The off-diagonal part of `D` squares to `D² − D⁴`.**  Equivalently
`|off-diagonal part| = sin Θ cos Θ`: it is the half-double-angle operator, and
the tangent representative is obtained from it by dividing by `cos²Θ`. -/
theorem offDiagonal_sq (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    ((1 - p) * D * p + p * D * (1 - p)) * ((1 - p) * D * p + p * D * (1 - p))
      = D * D - D * D * (D * D) := by
  have hexpand : ((1 - p) * D * p + p * D * (1 - p))
        * ((1 - p) * D * p + p * D * (1 - p))
      = ((1 - p) * D * p) * ((1 - p) * D * p)
        + ((1 - p) * D * p) * (p * D * (1 - p))
        + (p * D * (1 - p)) * ((1 - p) * D * p)
        + (p * D * (1 - p)) * (p * D * (1 - p)) := by
    noncomm_ring
  rw [hexpand, lower_sq hp, upper_sq hp, lower_mul_upper hp hkey,
    upper_mul_lower hp hkey]
  noncomm_ring


/-! Ring identities for the Möbius transform `s ↦ s (1 − s)⁻¹` in the commutative
subalgebra generated by `sin²Θ`, the projection, and the resolvent. -/

section Moebius

variable {s R : A}

private theorem moebius_gram (hps : p * s = s * p) (hRs : R * s = s * R)
    (hRp : R * p = p * R) (hcancel : (1 - s) * R = 1) :
    R * ((s - s * s) * p) * R = s * p * R := by
  have hRc : R * (1 - s) = (1 - s) * R := by
    have h : R * (1 - s) = R - R * s := by noncomm_ring
    rw [h, hRs]
    noncomm_ring
  have hpc : (1 - s) * p = p * (1 - s) := by
    have h : (1 - s) * p = p - s * p := by noncomm_ring
    rw [h, ← hps]
    noncomm_ring
  calc R * ((s - s * s) * p) * R
      = (R * (1 - s)) * (s * p) * R := by noncomm_ring
    _ = ((1 - s) * R) * (s * p) * R := by rw [hRc]
    _ = (1 - s) * (R * s) * (p * R) := by noncomm_ring
    _ = (1 - s) * (s * R) * (p * R) := by rw [hRs]
    _ = (1 - s) * s * (R * p) * R := by noncomm_ring
    _ = (1 - s) * s * (p * R) * R := by rw [hRp]
    _ = s * ((1 - s) * p) * R * R := by noncomm_ring
    _ = s * (p * (1 - s)) * R * R := by rw [hpc]
    _ = s * p * ((1 - s) * R) * R := by noncomm_ring
    _ = s * p * R := by rw [hcancel, mul_one]

private theorem moebius_algebra (hps : p * s = s * p) (hpp : p * p = p)
    (_hRp : R * p = p * R) (hcancel : (1 - s) * R = 1) :
    s * p * R = s * p + s * p * (s * p * R) := by
  have hpc : (1 - s) * p = p * (1 - s) := by
    have h : (1 - s) * p = p - s * p := by noncomm_ring
    rw [h, ← hps]
    noncomm_ring
  have h1 : s * p * (s * p * R) = s * s * p * R := by
    calc s * p * (s * p * R) = s * (p * s) * (p * R) := by noncomm_ring
      _ = s * (s * p) * (p * R) := by rw [hps]
      _ = s * s * (p * p) * R := by noncomm_ring
      _ = s * s * p * R := by rw [hpp]
  rw [h1]
  refine sub_eq_iff_eq_add.mp ?_
  calc s * p * R - s * s * p * R
      = s * ((1 - s) * p) * R := by noncomm_ring
    _ = s * (p * (1 - s)) * R := by rw [hpc]
    _ = s * p * ((1 - s) * R) := by noncomm_ring
    _ = s * p := by rw [hcancel, mul_one]

end Moebius

end ProjectionAlgebra

/-! ### Inverses in a ring -/

section RingInverse

variable {A : Type*} [Ring A]

private theorem inverse_comm {a x : A} (ha : IsUnit a) (h : x * a = a * x) :
    x * Ring.inverse a = Ring.inverse a * x := by
  have h1 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a ha
  have h2 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  calc x * Ring.inverse a
      = (Ring.inverse a * a) * (x * Ring.inverse a) := by rw [h1, one_mul]
    _ = Ring.inverse a * ((a * x) * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * ((x * a) * Ring.inverse a) := by rw [h]
    _ = Ring.inverse a * x * (a * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * x := by rw [h2, mul_one]

private theorem star_inverse [StarRing A] {a : A} (ha : IsUnit a) :
    star (Ring.inverse a) = Ring.inverse (star a) := by
  have hstar : IsUnit (star a) := ha.star
  have h1 : star a * Ring.inverse (star a) = 1 := Ring.mul_inverse_cancel _ hstar
  have h2 : star (Ring.inverse a) * star a = 1 := by
    rw [← star_mul, Ring.mul_inverse_cancel a ha, star_one]
  calc star (Ring.inverse a)
      = star (Ring.inverse a) * (star a * Ring.inverse (star a)) := by rw [h1, mul_one]
    _ = (star (Ring.inverse a) * star a) * Ring.inverse (star a) := by rw [mul_assoc]
    _ = Ring.inverse (star a) := by rw [h2, one_mul]

end RingInverse

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-! ### The block representative of the ambient tangent -/

section Representative

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The off-diagonal block representative of the ambient tangent.**  It is
supported entirely on the two cross blocks of `U ⊕ U^⊥`, and under uniform
transversality its modulus is exactly `tan Θ`. -/
def tanBlockRepresentative : E →L[ℂ] E :=
  diagonalPair Uᗮ U
    (projectorDifference U V * secantSquared U V)

variable {U V}

omit [CompleteSpace E] in
private theorem comp_eq_mul (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem starProjection_idem (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] : W.starProjection * W.starProjection =
      W.starProjection := W.isIdempotentElem_starProjection

omit [CompleteSpace E] in
/-- The two-projection relation for a pair of closed subspaces. -/
theorem projectorDifference_anticommutator :
    projectorDifference U V * U.starProjection +
        U.starProjection * projectorDifference U V +
        projectorDifference U V * projectorDifference U V =
      projectorDifference U V :=
  twoProjection_anticommutator (starProjection_idem U) (starProjection_idem V)

/-- The projector difference is self-adjoint. -/
theorem isSelfAdjoint_projectorDifference :
    IsSelfAdjoint (projectorDifference U V) :=
  (isSelfAdjoint_starProjection V).sub (isSelfAdjoint_starProjection U)

/-- The square of the projector difference is `sin²Θ`. -/
theorem projectorDifference_sq :
    projectorDifference U V * projectorDifference U V =
      sinAngleOperatorC U V * sinAngleOperatorC U V := by
  rw [sinAngleOperatorC, ContinuousLinearMap.modulus_mul_self,
    ((isSelfAdjoint_starProjection U).sub
      (isSelfAdjoint_starProjection V)).adjoint_eq, comp_eq_mul,
    projectorDifference]
  noncomm_ring

/-- The projector difference has the norm of the sine. -/
theorem norm_projectorDifference :
    ‖projectorDifference U V‖ = ‖sinAngleOperatorC U V‖ := by
  rw [sinAngleOperatorC, ContinuousLinearMap.norm_modulus, projectorDifference,
    show V.starProjection - U.starProjection =
      -(U.starProjection - V.starProjection) from by abel, norm_neg]

/-- Under uniform transversality the operator `1 − sin²Θ` is invertible: it is
`cos²Θ`, bounded below. -/
theorem isUnit_one_sub_projectorDifference_sq
    (htr : ‖sinAngleOperatorC U V‖ < 1) :
    IsUnit (1 - projectorDifference U V * projectorDifference U V) := by
  have hnorm : ‖projectorDifference U V * projectorDifference U V‖ < 1 := by
    refine lt_of_le_of_lt (norm_mul_le _ _) ?_
    rw [norm_projectorDifference]
    nlinarith [norm_nonneg (sinAngleOperatorC U V)]
  rw [← Units.val_oneSub _ hnorm]
  exact Units.isUnit _

end Representative

/-! ### Identifying the representative with the ambient tangent -/

section Identification

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The spectrum of the ambient sine stays strictly below `1` under uniform
transversality. -/
theorem spectrum_sinAngleOperatorC_lt_one (htr : ‖sinAngleOperatorC U V‖ < 1)
    {t : ℝ} (ht : t ∈ spectrum ℝ (sinAngleOperatorC U V)) : 0 ≤ t ∧ t < 1 := by
  refine ⟨(spectrum_sinAngleOperatorC_subset_Icc U V ht).1, ?_⟩
  have habs : |t| ≤ ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem ht
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hle : t ≤ ‖sinAngleOperatorC U V‖ := by
    refine (le_abs_self t).trans (habs.trans ?_)
    nlinarith [norm_nonneg (sinAngleOperatorC U V)]
  linarith

private theorem continuousOn_tan_image (htr : ‖sinAngleOperatorC U V‖ < 1) :
    ContinuousOn Real.tan
      (Real.arcsin '' spectrum ℝ (sinAngleOperatorC U V)) := by
  refine Real.continuousOn_tan.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  have h := spectrum_sinAngleOperatorC_lt_one htr ht
  refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := Real.arcsin_nonneg.mpr h.1
    linarith [Real.pi_pos]
  · exact Real.arcsin_lt_pi_div_two.mpr h.2

private theorem continuousOn_tanArcsin (htr : ‖sinAngleOperatorC U V‖ < 1) :
    ContinuousOn (Real.tan ∘ Real.arcsin)
      (spectrum ℝ (sinAngleOperatorC U V)) :=
  (continuousOn_tan_image htr).comp Real.continuous_arcsin.continuousOn
    (Set.mapsTo_image _ _)

/-- The ambient tangent as one functional calculus of the ambient sine. -/
theorem directedTanAngleOperatorC_eq_cfc (htr : ‖sinAngleOperatorC U V‖ < 1) :
    tanAngleOperatorC U V =
      cfc (Real.tan ∘ Real.arcsin) (sinAngleOperatorC U V) := by
  rw [tanAngleOperatorC, angleOperatorC,
    ← cfc_comp Real.tan Real.arcsin (sinAngleOperatorC U V)
      (isSelfAdjoint_sinAngleOperatorC U V) (continuousOn_tan_image htr)
      Real.continuous_arcsin.continuousOn]

/-- **`tan²Θ · cos²Θ = sin²Θ`**, the scalar Pythagoras of the tangent, as an
operator identity of functional calculi. -/
theorem tan_sq_mul_one_sub_sin_sq (htr : ‖sinAngleOperatorC U V‖ < 1) :
    tanAngleOperatorC U V * tanAngleOperatorC U V *
        (1 - sinAngleOperatorC U V * sinAngleOperatorC U V) =
      sinAngleOperatorC U V * sinAngleOperatorC U V := by
  have hsa : IsSelfAdjoint (sinAngleOperatorC U V) := isSelfAdjoint_sinAngleOperatorC U V
  have hf := continuousOn_tanArcsin htr
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ (sinAngleOperatorC U V)) :=
    continuousOn_id
  have hsq : ContinuousOn (fun t : ℝ => t * t)
      (spectrum ℝ (sinAngleOperatorC U V)) := hid.mul hid
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ))
      (spectrum ℝ (sinAngleOperatorC U V)) := continuousOn_const
  have hSS : sinAngleOperatorC U V * sinAngleOperatorC U V =
      cfc (fun t : ℝ => t * t) (sinAngleOperatorC U V) := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) (sinAngleOperatorC U V) hid hid,
      cfc_id' ℝ (sinAngleOperatorC U V)]
  have hcos : 1 - sinAngleOperatorC U V * sinAngleOperatorC U V =
      cfc (fun t : ℝ => 1 - t * t) (sinAngleOperatorC U V) := by
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t * t) (sinAngleOperatorC U V)
      hone hsq, cfc_const_one ℝ (sinAngleOperatorC U V), ← hSS]
  rw [directedTanAngleOperatorC_eq_cfc (U := U) (V := V) htr, hcos,
    ← cfc_mul (Real.tan ∘ Real.arcsin) (Real.tan ∘ Real.arcsin)
      (sinAngleOperatorC U V) hf hf,
    ← cfc_mul (fun x : ℝ => (Real.tan ∘ Real.arcsin) x * (Real.tan ∘ Real.arcsin) x)
      (fun t : ℝ => 1 - t * t) (sinAngleOperatorC U V) (hf.mul hf)
      (hone.sub hsq), hSS]
  refine cfc_congr fun t ht => ?_
  have h := spectrum_sinAngleOperatorC_lt_one htr ht
  have h1 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [h.1, h.2]
  have hsqrt : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
    Real.mul_self_sqrt h1.le
  have hne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  simp only [Function.comp_apply, Real.tan_arcsin]
  field_simp
  nlinarith [hsqrt]

end Identification

/-! ### The block representative has the ambient tangent as its modulus -/

section Modulus

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  (htr : ‖sinAngleOperatorC U V‖ < 1)

include htr

private theorem secant_mul_cancel :
    (1 - projectorDifference U V * projectorDifference U V) *
      secantSquared U V = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_sub_projectorDifference_sq htr)

private theorem secant_comm_projectorDifference :
    projectorDifference U V * secantSquared U V =
      secantSquared U V * projectorDifference U V :=
  inverse_comm (isUnit_one_sub_projectorDifference_sq htr) (by noncomm_ring)

private theorem secant_comm_starProjection :
    secantSquared U V * U.starProjection =
      U.starProjection * secantSquared U V :=
  (inverse_comm (isUnit_one_sub_projectorDifference_sq htr)
    (by
      have h := proj_comm_sq (starProjection_idem U)
        (projectorDifference_anticommutator (U := U) (V := V))
      simp only [mul_sub, sub_mul, mul_one, one_mul, h])).symm

private theorem secant_comm_starProjection_compl :
    secantSquared U V * (1 - U.starProjection) =
      (1 - U.starProjection) * secantSquared U V := by
  have h : secantSquared U V * (1 - U.starProjection) =
      secantSquared U V - secantSquared U V * U.starProjection := by
    noncomm_ring
  rw [h, secant_comm_starProjection htr]
  noncomm_ring

private theorem secant_selfAdjoint :
    star (secantSquared U V) = secantSquared U V := by
  rw [secantSquared, star_inverse (isUnit_one_sub_projectorDifference_sq htr)]
  congr 1
  rw [star_sub, star_one, star_mul,
    isSelfAdjoint_projectorDifference.star_eq]

private theorem secant_comm_lower :
    ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
        secantSquared U V =
      secantSquared U V *
        ((1 - U.starProjection) * projectorDifference U V *
          U.starProjection) := by
  have hRp := secant_comm_starProjection htr
  have hRD := secant_comm_projectorDifference htr
  have hRc := secant_comm_starProjection_compl htr
  calc ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
        secantSquared U V
      = (1 - U.starProjection) * projectorDifference U V *
          (U.starProjection * secantSquared U V) := by noncomm_ring
    _ = (1 - U.starProjection) * projectorDifference U V *
          (secantSquared U V * U.starProjection) := by rw [hRp]
    _ = (1 - U.starProjection) *
          (projectorDifference U V * secantSquared U V) *
          U.starProjection := by noncomm_ring
    _ = (1 - U.starProjection) *
          (secantSquared U V * projectorDifference U V) *
          U.starProjection := by rw [hRD]
    _ = ((1 - U.starProjection) * secantSquared U V) *
          projectorDifference U V * U.starProjection := by noncomm_ring
    _ = (secantSquared U V * (1 - U.starProjection)) *
          projectorDifference U V * U.starProjection := by rw [hRc]
    _ = secantSquared U V *
          ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection) := by noncomm_ring

private theorem secant_comm_upper :
    (U.starProjection * projectorDifference U V *
          (1 - U.starProjection)) * secantSquared U V =
      secantSquared U V *
        (U.starProjection * projectorDifference U V *
          (1 - U.starProjection)) := by
  have hRp := secant_comm_starProjection htr
  have hRD := secant_comm_projectorDifference htr
  have hRc := secant_comm_starProjection_compl htr
  calc (U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) * secantSquared U V
      = U.starProjection * projectorDifference U V *
          ((1 - U.starProjection) * secantSquared U V) := by noncomm_ring
    _ = U.starProjection * projectorDifference U V *
          (secantSquared U V * (1 - U.starProjection)) := by rw [hRc]
    _ = U.starProjection *
          (projectorDifference U V * secantSquared U V) *
          (1 - U.starProjection) := by noncomm_ring
    _ = U.starProjection *
          (secantSquared U V * projectorDifference U V) *
          (1 - U.starProjection) := by rw [hRD]
    _ = (U.starProjection * secantSquared U V) *
          projectorDifference U V * (1 - U.starProjection) := by noncomm_ring
    _ = (secantSquared U V * U.starProjection) *
          projectorDifference U V * (1 - U.starProjection) := by rw [hRp]
    _ = secantSquared U V *
          (U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) := by noncomm_ring

/-- The block representative in the explicit `U ⊕ U^⊥` corner form. -/
theorem tanBlockRepresentative_eq :
    tanBlockRepresentative U V =
      ((1 - U.starProjection) * projectorDifference U V * U.starProjection +
          U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) * secantSquared U V := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  have hRp := secant_comm_starProjection htr
  have hRc := secant_comm_starProjection_compl htr
  rw [tanBlockRepresentative, diagonalPair]
  simp only [hUperp, Submodule.starProjection_orthogonal', comp_eq_mul]
  have h1 : (1 - U.starProjection) *
        (projectorDifference U V * secantSquared U V *
          U.starProjection) =
      (1 - U.starProjection) * projectorDifference U V * U.starProjection *
        secantSquared U V := by
    calc (1 - U.starProjection) *
          (projectorDifference U V * secantSquared U V *
            U.starProjection)
        = (1 - U.starProjection) * projectorDifference U V *
            (secantSquared U V * U.starProjection) := by noncomm_ring
      _ = (1 - U.starProjection) * projectorDifference U V *
            (U.starProjection * secantSquared U V) := by rw [hRp]
      _ = (1 - U.starProjection) * projectorDifference U V *
            U.starProjection * secantSquared U V := by noncomm_ring
  have h2 : U.starProjection *
        (projectorDifference U V * secantSquared U V *
          (1 - U.starProjection)) =
      U.starProjection * projectorDifference U V * (1 - U.starProjection) *
        secantSquared U V := by
    calc U.starProjection *
          (projectorDifference U V * secantSquared U V *
            (1 - U.starProjection))
        = U.starProjection * projectorDifference U V *
            (secantSquared U V * (1 - U.starProjection)) := by noncomm_ring
      _ = U.starProjection * projectorDifference U V *
            ((1 - U.starProjection) * secantSquared U V) := by rw [hRc]
      _ = U.starProjection * projectorDifference U V *
            (1 - U.starProjection) * secantSquared U V := by noncomm_ring
  rw [add_mul, h1, h2]

/-- The block representative is self-adjoint: its two corners are adjoints of
one another. -/
theorem isSelfAdjoint_tanBlockRepresentative :
    IsSelfAdjoint (tanBlockRepresentative U V) := by
  have hD := isSelfAdjoint_projectorDifference (U := U) (V := V)
  have hp := isSelfAdjoint_starProjection U
  have hcross : star ((1 - U.starProjection) * projectorDifference U V *
      U.starProjection) = U.starProjection * projectorDifference U V *
        (1 - U.starProjection) := by
    rw [star_mul, star_mul, star_sub, star_one, hp.star_eq, hD.star_eq]
    noncomm_ring
  have hcross' : star (U.starProjection * projectorDifference U V *
      (1 - U.starProjection)) = (1 - U.starProjection) *
        projectorDifference U V * U.starProjection := by
    rw [star_mul, star_mul, star_sub, star_one, hp.star_eq, hD.star_eq]
    noncomm_ring
  rw [IsSelfAdjoint, tanBlockRepresentative_eq htr, star_mul,
    secant_selfAdjoint htr, star_add, hcross, hcross', add_comm, add_mul, mul_add,
    ← secant_comm_lower htr, ← secant_comm_upper htr]

/-- **`Ξ⋆Ξ = tan²Θ`.**  The block representative squares to `sin²Θ · cos⁻²Θ`. -/
theorem tanBlockRepresentative_mul_self :
    tanBlockRepresentative U V * tanBlockRepresentative U V =
      sinAngleOperatorC U V * sinAngleOperatorC U V * secantSquared U V := by
  have hcancel := secant_mul_cancel htr
  have hsq := offDiagonal_sq (starProjection_idem U)
    (projectorDifference_anticommutator (U := U) (V := V))
  have hXR : ((1 - U.starProjection) * projectorDifference U V *
        U.starProjection + U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) * secantSquared U V =
      secantSquared U V * ((1 - U.starProjection) *
        projectorDifference U V * U.starProjection +
        U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) := by
    rw [add_mul, mul_add, secant_comm_lower htr, secant_comm_upper htr]
  rw [tanBlockRepresentative_eq htr]
  calc ((1 - U.starProjection) * projectorDifference U V * U.starProjection +
          U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) * secantSquared U V *
        (((1 - U.starProjection) * projectorDifference U V *
            U.starProjection + U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) * secantSquared U V)
      = ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection + U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) *
          (secantSquared U V * ((1 - U.starProjection) *
            projectorDifference U V * U.starProjection +
            U.starProjection * projectorDifference U V *
            (1 - U.starProjection))) * secantSquared U V := by noncomm_ring
    _ = (((1 - U.starProjection) * projectorDifference U V *
            U.starProjection + U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) *
          ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection + U.starProjection * projectorDifference U V *
            (1 - U.starProjection))) * secantSquared U V *
          secantSquared U V := by rw [← hXR]; noncomm_ring
    _ = (projectorDifference U V * projectorDifference U V -
          projectorDifference U V * projectorDifference U V *
            (projectorDifference U V * projectorDifference U V)) *
          secantSquared U V * secantSquared U V := by rw [hsq]
    _ = projectorDifference U V * projectorDifference U V *
          ((1 - projectorDifference U V * projectorDifference U V) *
            secantSquared U V) * secantSquared U V := by noncomm_ring
    _ = sinAngleOperatorC U V * sinAngleOperatorC U V *
          secantSquared U V := by
        rw [hcancel, mul_one, projectorDifference_sq]

/-- **The ambient tangent is the modulus of the block representative.**

This is the operator form of the paper's `‖tan Θ‖ = ‖[[0, −J₀⋆ tan Θ₁],
[J₀ tan Θ₀, 0]]‖`: not merely equality of norms, and not merely of
singular-value lists, but equality of the two moduli, so the substitution is
legitimate inside every unitarily invariant norm. -/
theorem directedTanAngleOperatorC_eq_modulus_blockRepresentative :
    tanAngleOperatorC U V = (tanBlockRepresentative U V).modulus := by
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (directedTanAngleOperatorC_nonneg U V) ?_
  have hself := isSelfAdjoint_tanBlockRepresentative htr
  have hadj : (tanBlockRepresentative U V).adjoint ∘L
      tanBlockRepresentative U V =
      tanBlockRepresentative U V * tanBlockRepresentative U V := by
    rw [comp_eq_mul, hself.adjoint_eq]
  rw [hadj, tanBlockRepresentative_mul_self htr]
  have hcancel := secant_mul_cancel htr
  rw [projectorDifference_sq] at hcancel
  calc tanAngleOperatorC U V * tanAngleOperatorC U V
      = tanAngleOperatorC U V * tanAngleOperatorC U V *
          ((1 - sinAngleOperatorC U V * sinAngleOperatorC U V) *
            secantSquared U V) := by rw [hcancel, mul_one]
    _ = (tanAngleOperatorC U V * tanAngleOperatorC U V *
          (1 - sinAngleOperatorC U V * sinAngleOperatorC U V)) *
          secantSquared U V := by noncomm_ring
    _ = sinAngleOperatorC U V * sinAngleOperatorC U V *
          secantSquared U V := by
        rw [tan_sq_mul_one_sub_sin_sq htr]

end Modulus

/-! ### The directed corner -/

section Corner

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The ambient form of the directed sine block, `P_{V^⊥} P_U`. -/
def directedSineAmbient : E →L[ℂ] E :=
  Vᗮ.starProjection ∘L U.starProjection

variable {U V}

omit [CompleteSpace E] in
private theorem projectionBlock_lower (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal', comp_eq_mul,
    comp_eq_mul, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper (K : E →L[ℂ] E) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal', comp_eq_mul]
  rw [mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_smul (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    projectionBlock Ω Γ (c • K) = c • projectionBlock Ω Γ K := by
  ext x
  simp [projectionBlock]

/-- The Gram operator of the ambient directed sine block is `sin²Θ` compressed
to `U`. -/
theorem gramOperator_directedSineAmbient :
    gramOperator (directedSineAmbient U V) =
      projectorDifference U V * projectorDifference U V *
        U.starProjection := by
  have hp := starProjection_idem U
  have hq := starProjection_idem V
  rw [sq_mul_proj hp (projectorDifference_anticommutator (U := U) (V := V)),
    gramOperator, directedSineAmbient, ContinuousLinearMap.adjoint_comp,
    (isSelfAdjoint_starProjection U).adjoint_eq,
    (isSelfAdjoint_starProjection Vᗮ).adjoint_eq, projectorDifference]
  simp only [comp_eq_mul, Submodule.starProjection_orthogonal']
  have hpp : ∀ x : E →L[ℂ] E, U.starProjection * (U.starProjection * x) =
      U.starProjection * x := fun x => by rw [← mul_assoc, hp]
  have hqq : ∀ x : E →L[ℂ] E, V.starProjection * (V.starProjection * x) =
      V.starProjection * x := fun x => by rw [← mul_assoc, hq]
  simp only [mul_assoc, sub_mul, mul_sub, mul_one, one_mul, hqq, hp]
  abel

variable (htr : ‖sinAngleOperatorC U V‖ < 1)

include htr

private theorem secant_comm_sq :
    secantSquared U V *
        (projectorDifference U V * projectorDifference U V) =
      projectorDifference U V * projectorDifference U V *
        secantSquared U V := by
  have hRD := secant_comm_projectorDifference htr
  calc secantSquared U V *
        (projectorDifference U V * projectorDifference U V)
      = (secantSquared U V * projectorDifference U V) *
          projectorDifference U V := by noncomm_ring
    _ = (projectorDifference U V * secantSquared U V) *
          projectorDifference U V := by rw [← hRD]
    _ = projectorDifference U V *
          (secantSquared U V * projectorDifference U V) := by
        noncomm_ring
    _ = projectorDifference U V *
          (projectorDifference U V * secantSquared U V) := by
        rw [← hRD]
    _ = projectorDifference U V * projectorDifference U V *
          secantSquared U V := by noncomm_ring

/-- The lower corner of the block representative, in explicit form. -/
theorem lowerCorner_eq :
    projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V) =
      ((1 - U.starProjection) * projectorDifference U V *
        U.starProjection) * secantSquared U V := by
  rw [projectionBlock_lower]
  calc (1 - U.starProjection) *
        (projectorDifference U V * secantSquared U V) * U.starProjection
      = (1 - U.starProjection) * projectorDifference U V *
          (secantSquared U V * U.starProjection) := by noncomm_ring
    _ = (1 - U.starProjection) * projectorDifference U V *
          (U.starProjection * secantSquared U V) := by
        rw [secant_comm_starProjection htr]
    _ = ((1 - U.starProjection) * projectorDifference U V *
          U.starProjection) * secantSquared U V := by noncomm_ring

/-- The block's symbol is self-adjoint. -/
theorem star_projectorDifference_mul_secant :
    star (projectorDifference U V * secantSquared U V) =
      projectorDifference U V * secantSquared U V := by
  rw [star_mul, secant_selfAdjoint htr,
    isSelfAdjoint_projectorDifference.star_eq,
    ← secant_comm_projectorDifference htr]

/-- The upper corner is the adjoint of the lower one. -/
theorem upperCorner_eq_adjoint_lowerCorner :
    projectionBlock Uᗮᗮ Uᗮ
        (projectorDifference U V * secantSquared U V) =
      star (projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V)) := by
  have hp := isSelfAdjoint_starProjection U
  rw [projectionBlock_upper, projectionBlock_lower, star_mul, star_mul, star_sub,
    star_one, hp.star_eq, star_projectorDifference_mul_secant htr]
  noncomm_ring

/-- **The Gram operator of the lower corner is `tan²Θ` compressed to `U`**, in
the Möbius form `Q (1 − Q)⁻¹` of the directed sine's Gram operator `Q`. -/
theorem gramOperator_lowerCorner :
    gramOperator (projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V)) =
      projectorDifference U V * projectorDifference U V *
        U.starProjection * secantSquared U V := by
  have hp := starProjection_idem U
  have hkey := projectorDifference_anticommutator (U := U) (V := V)
  have hpsa := isSelfAdjoint_starProjection U
  have hD := isSelfAdjoint_projectorDifference (U := U) (V := V)
  have hstar : star (((1 - U.starProjection) * projectorDifference U V *
      U.starProjection) * secantSquared U V) =
      secantSquared U V * (U.starProjection *
        projectorDifference U V * (1 - U.starProjection)) := by
    rw [star_mul, star_mul, star_mul, star_sub, star_one, hpsa.star_eq,
      hD.star_eq, secant_selfAdjoint htr]
    noncomm_ring
  rw [gramOperator, comp_eq_mul, lowerCorner_eq htr]
  rw [show (((1 - U.starProjection) * projectorDifference U V *
      U.starProjection) * secantSquared U V).adjoint =
      secantSquared U V * (U.starProjection *
        projectorDifference U V * (1 - U.starProjection)) from hstar]
  calc secantSquared U V * (U.starProjection *
          projectorDifference U V * (1 - U.starProjection)) *
        (((1 - U.starProjection) * projectorDifference U V *
          U.starProjection) * secantSquared U V)
      = secantSquared U V * ((U.starProjection *
            projectorDifference U V * (1 - U.starProjection)) *
          ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection)) * secantSquared U V := by noncomm_ring
    _ = secantSquared U V *
          ((projectorDifference U V * projectorDifference U V -
            projectorDifference U V * projectorDifference U V *
              (projectorDifference U V * projectorDifference U V)) *
            U.starProjection) * secantSquared U V := by
        rw [upper_mul_lower hp hkey]
    _ = projectorDifference U V * projectorDifference U V *
          U.starProjection * secantSquared U V :=
        moebius_gram (proj_comm_sq hp hkey) (secant_comm_sq htr)
          (secant_comm_starProjection htr) (secant_mul_cancel htr)

/-- The defining relation of the Möbius transform, pointwise: this is exactly
the hypothesis of `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent`. -/
theorem gramOperator_lowerCorner_moebius (y : E) :
    gramOperator (projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V)) y =
      gramOperator (directedSineAmbient U V) y +
        gramOperator (directedSineAmbient U V)
          (gramOperator (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V)) y) := by
  have hp := starProjection_idem U
  have hkey := projectorDifference_anticommutator (U := U) (V := V)
  have halg := moebius_algebra (s := projectorDifference U V *
      projectorDifference U V) (p := U.starProjection)
    (R := secantSquared U V) (proj_comm_sq hp hkey) hp
    (secant_comm_starProjection htr) (secant_mul_cancel htr)
  have h := congrArg (fun S : E →L[ℂ] E => S y) halg
  simpa only [gramOperator_lowerCorner htr, gramOperator_directedSineAmbient,
    add_apply, mul_apply_eq_comp] using h

end Corner

/-! ### The Davis--Kahan whole-space tangent theorem -/

section WholeSpace

variable {T A : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Under uniform transversality the ambient directed sine block is a strict
contraction. -/
theorem norm_directedSineAmbient_lt_one
    (htr : ‖sinAngleOperatorC U V‖ < 1) :
    ‖directedSineAmbient U V‖ < 1 := by
  have h := norm_gramOperator (directedSineAmbient U V)
  rw [gramOperator_directedSineAmbient] at h
  have hp : ‖U.starProjection‖ ≤ 1 := U.starProjection_norm_le
  have e1 : ‖projectorDifference U V * projectorDifference U V *
      U.starProjection‖ ≤ ‖projectorDifference U V *
        projectorDifference U V‖ * ‖U.starProjection‖ := norm_mul_le _ _
  have e2 : ‖projectorDifference U V * projectorDifference U V‖ ≤
      ‖projectorDifference U V‖ * ‖projectorDifference U V‖ :=
    norm_mul_le _ _
  rw [norm_projectorDifference] at e2
  have hb : ‖projectorDifference U V * projectorDifference U V *
      U.starProjection‖ ≤ ‖sinAngleOperatorC U V‖ * ‖sinAngleOperatorC U V‖ := by
    nlinarith [norm_nonneg (projectorDifference U V *
      projectorDifference U V), norm_nonneg (sinAngleOperatorC U V),
      norm_nonneg U.starProjection]
  nlinarith [norm_nonneg (directedSineAmbient U V),
    norm_nonneg (sinAngleOperatorC U V)]

omit [CompleteSpace E] in
/-- The ambient directed sine block factors through the trial subspace's own
sine block, so it has no larger approximation numbers. -/
theorem approximationNumber_directedSineAmbient_le (n : ℕ) :
    (directedSineAmbient U V).approximationNumber n ≤
      approximationSingularValue n (theorem63DirectedSineBlock U V) := by
  have hfactor : directedSineAmbient U V =
      theorem63DirectedSineBlock U V ∘L U.orthogonalProjectionOnto := by
    rw [directedSineAmbient, theorem63DirectedSineBlock,
      ContinuousLinearMap.comp_assoc]
    congr 1
  rw [hfactor]
  refine le_trans (ContinuousLinearMap.approximationNumber_comp_le_mul_norm _ _ n) ?_
  have h1 : ‖U.orthogonalProjectionOnto‖ ≤ (1 : ℝ) := U.orthogonalProjectionOnto_norm_le
  have h0 : 0 ≤ (theorem63DirectedSineBlock U V).approximationNumber n :=
    ContinuousLinearMap.approximationNumber_nonneg _ _
  calc (theorem63DirectedSineBlock U V).approximationNumber n *
        ‖U.orthogonalProjectionOnto‖
      ≤ (theorem63DirectedSineBlock U V).approximationNumber n * 1 := by gcongr
    _ = approximationSingularValue n (theorem63DirectedSineBlock U V) := mul_one _

/-- The trial-space sine block is a strict contraction as well. -/
theorem approximationSingularValue_theorem63DirectedSineBlock_lt_one
    (htr : ‖sinAngleOperatorC U V‖ < 1) (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock U V) < 1 := by
  have hfac : theorem63DirectedSineBlock U V =
      directedSineAmbient U V ∘L U.subtypeL := by
    rw [directedSineAmbient, theorem63DirectedSineBlock,
      ContinuousLinearMap.comp_assoc]
    congr 1
    ext x
    change (x : E) = U.starProjection (x : E)
    exact (Submodule.starProjection_eq_self_iff.mpr x.2).symm
  have hle : approximationSingularValue n (theorem63DirectedSineBlock U V) ≤
      ‖directedSineAmbient U V‖ := by
    refine le_trans (ContinuousLinearMap.approximationNumber_le_norm _ n) ?_
    rw [hfac]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have h1 : ‖U.subtypeL‖ ≤ (1 : ℝ) := U.norm_subtypeL_le
    nlinarith [norm_nonneg (directedSineAmbient U V)]
  exact lt_of_le_of_lt hle (norm_directedSineAmbient_lt_one htr)

/-- **The directed corner is dominated by the paper's directed tangent
scalars.**  This is where the Möbius transfer of approximation numbers is
used. -/
theorem approximationNumber_lowerCorner_le
    (htr : ‖sinAngleOperatorC U V‖ < 1) (n : ℕ) :
    (projectionBlock Uᗮ U (projectorDifference U V *
        secantSquared U V)).approximationNumber n ≤
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock U V))) := by
  set c := projectionBlock Uᗮ U (projectorDifference U V *
    secantSquared U V) with hcdef
  set sig := (directedSineAmbient U V).approximationNumber n with hsigdef
  have hsig0 : 0 ≤ sig := ContinuousLinearMap.approximationNumber_nonneg _ _
  have hsiglt : sig < 1 :=
    lt_of_le_of_lt (ContinuousLinearMap.approximationNumber_le_norm _ n)
      (norm_directedSineAmbient_lt_one htr)
  have hres := approximationNumber_le_of_gramResolvent (directedSineAmbient U V)
    (norm_directedSineAmbient_lt_one htr)
    (gramOperator_lowerCorner_moebius htr) n
  rw [approximationNumber_gramOperator_complex c n] at hres
  -- the scalar identity `tan (arcsin σ)² = σ²/(1 − σ²)`
  have hden : (0 : ℝ) < 1 - sig ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 - sig ^ 2) * Real.sqrt (1 - sig ^ 2) = 1 - sig ^ 2 :=
    Real.mul_self_sqrt hden.le
  have htanSq : Real.tan (Real.arcsin sig) ^ 2 = sig ^ 2 / (1 - sig ^ 2) := by
    rw [Real.tan_arcsin, div_pow]
    congr 1
    nlinarith [hsqrt]
  have hstep : c.approximationNumber n ≤ Real.tan (Real.arcsin sig) := by
    have hc0 : 0 ≤ c.approximationNumber n :=
      ContinuousLinearMap.approximationNumber_nonneg _ _
    have ht0 : 0 ≤ Real.tan (Real.arcsin sig) := TanArcsin.tanArcsin_nonneg hsig0
    nlinarith [hres, htanSq]
  refine hstep.trans (TanArcsin.tanArcsin_le_tanArcsin hsig0 ?_ ?_)
  · exact approximationNumber_directedSineAmbient_le n
  · exact approximationSingularValue_theorem63DirectedSineBlock_lt_one htr n

/-- The Ky Fan gauge of the directed corner is dominated by the paper's directed
tangent prefix sums. -/
theorem kyFan_lowerCorner_le (htr : ‖sinAngleOperatorC U V‖ < 1) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V)) ≤
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock U V))) := by
  rw [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  exact Finset.sum_le_sum fun n _ => approximationNumber_lowerCorner_le htr n

omit [CompleteSpace E] in
/-- With `U` invariant for the unperturbed operator, the Ritz residual of `U` is
the lower corner of the perturbation. -/
theorem approximationNumber_theorem63Residual_le
    (hAU : ∀ x ∈ U, A x ∈ U) (n : ℕ) :
    (theorem63Residual T U).approximationNumber n ≤
      (projectionBlock Uᗮ U (T - A)).approximationNumber n := by
  have hfac : theorem63Residual T U =
      projectionBlock Uᗮ U (T - A) ∘L U.subtypeL := by
    rw [theorem63Residual_eq_complementaryProjection, projectionBlock]
    ext z
    have hAz : Uᗮ.starProjection (A (z : E)) = 0 := by
      refine (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr ?_
      rw [Submodule.orthogonal_orthogonal]
      exact hAU (z : E) z.2
    have hpz : U.starProjection (z : E) = (z : E) :=
      Submodule.starProjection_eq_self_iff.mpr z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hpz,
      sub_apply, map_sub, hAz, sub_zero]
  rw [hfac]
  refine le_trans (ContinuousLinearMap.approximationNumber_comp_le_mul_norm _ _ n) ?_
  have h1 : ‖U.subtypeL‖ ≤ (1 : ℝ) := U.norm_subtypeL_le
  have h0 : 0 ≤ (projectionBlock Uᗮ U (T - A)).approximationNumber n :=
    ContinuousLinearMap.approximationNumber_nonneg _ _
  nlinarith

/-- **The directed corner estimate**, in the shape Lemma 6.1 consumes:
`δ · kyFan_k (corner of tan Θ) ≤ kyFan_k (corner of H)`. -/
theorem corner_all_kyFan
    (hT : T.IsSymmetric) (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1) (k : ℕ) :
    delta * kyFanApproximationGauge k (projectionBlock Uᗮ U
        (projectorDifference U V * secantSquared U V)) ≤
      kyFanApproximationGauge k (projectionBlock Uᗮ U (T - A)) := by
  have hdirected := theorem6_3_all_kyFan_core_infiniteTrial T V U hT hV hdelta
    hCompressionUpper hUnwantedLower k
  have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
  have hresidual : kyFanApproximationGauge k (theorem63Residual T U) ≤
      kyFanApproximationGauge k (projectionBlock Uᗮ U (T - A)) := by
    rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge, ContinuousLinearMap.kyFanGauge]
    exact Finset.sum_le_sum fun n _ =>
      approximationNumber_theorem63Residual_le hAU n
  nlinarith [hdirected, hcorner, hresidual]

/-- **The whole-space `tan Θ` theorem, Ky Fan form.**  The second conclusion of
the Section 2 tangent theorem, at every finite Ky Fan gauge. -/
theorem tanTheta_ambient_bounded_kyFan_complex_of_transversality
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k (tanAngleOperatorC U V) ≤
        kyFanApproximationGauge k (T - A) := by
  intro k
  have hTsa : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hHsa : IsSelfAdjoint (T - A) := hTsa.sub hA
  have hdeltac : ‖((delta : ℝ) : ℂ)‖ = delta := by simp [abs_of_pos hdelta]
  set K := projectorDifference U V * secantSquared U V with hKdef
  -- the two corner hypotheses of Lemma 6.1
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (projectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮ U (T - A)) := by
    intro j
    rw [projectionBlock_smul, kyFanApproximationGauge_smul, hdeltac]
    exact corner_all_kyFan hT hV hAU hdelta hCompressionUpper hUnwantedLower htr j
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ (T - A)) := by
    intro j
    have hleft : projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
        (((delta : ℝ) : ℂ) • projectionBlock Uᗮ U K).adjoint := by
      rw [projectionBlock_smul, upperCorner_eq_adjoint_lowerCorner htr]
      show ((delta : ℝ) : ℂ) • star (projectionBlock Uᗮ U K) =
        star (((delta : ℝ) : ℂ) • projectionBlock Uᗮ U K)
      rw [star_smul, RCLike.star_def, Complex.conj_ofReal]
    have hright : projectionBlock Uᗮᗮ Uᗮ (T - A) =
        (projectionBlock Uᗮ U (T - A)).adjoint := by
      have hp := isSelfAdjoint_starProjection U
      rw [projectionBlock_upper, projectionBlock_lower]
      show _ = star _
      simp only [star_mul, star_sub, star_one, hp.star_eq, hHsa.star_eq]
      noncomm_ring
    rw [hleft, hright, kyFanApproximationGauge_adjoint,
      kyFanApproximationGauge_adjoint, kyFanApproximationGauge_smul, hdeltac]
    exact corner_all_kyFan hT hV hAU hdelta hCompressionUpper hUnwantedLower htr j
  have hcombine := lemma61_all_kyFan Uᗮ U (((delta : ℝ) : ℂ) • K)
    (((delta : ℝ) : ℂ) • K) (T - A) (T - A) h₀ h₁ k
  have hsum : projectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K) +
      projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
      ((delta : ℝ) : ℂ) • tanBlockRepresentative U V := by
    rw [tanBlockRepresentative, diagonalPair, projectionBlock_smul,
      projectionBlock_smul, ← smul_add]
    rfl
  have hsumH : projectionBlock Uᗮ U (T - A) +
      projectionBlock Uᗮᗮ Uᗮ (T - A) = diagonalPair Uᗮ U (T - A) := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hdeltac] at hcombine
  have hpinch := diagonalPair_all_kyFan_le Uᗮ U (T - A) k
  have hmodulus : kyFanApproximationGauge k (tanAngleOperatorC U V) =
      kyFanApproximationGauge k (tanBlockRepresentative U V) := by
    rw [directedTanAngleOperatorC_eq_modulus_blockRepresentative htr]
    exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (tanBlockRepresentative U V)).kyFanGauge_eq k
  rw [hmodulus]
  exact hcombine.trans hpinch

/-- **The whole-space `tan Θ` theorem for every source unitarily invariant
norm**: `δ ‖tan Θ‖ ≤ ‖H‖`, the second conclusion of the Section 2 tangent
theorem and the assertion the paper settles just after equation (7.6). -/
theorem tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality
    (N : SymmetricNormingFunction)
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hMem : N.Mem (T - A)) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge (T - A) :=
  N.mul_gauge_le_of_all_mul_kyFan_le hdelta hMem
    (tanTheta_ambient_bounded_kyFan_complex_of_transversality hT hA hV hAU hdelta hCompressionUpper
      hUnwantedLower htr)

/-! ### Uniform transversality is derived, not assumed

The three theorems above take `‖sin Θ‖ < 1` as a hypothesis, whereas Davis and Kahan read
it off the standing assumptions of the section.  The derivation below closes that gap.

The quantitative work is done by the form bounds alone:
`approximationSingularValue_sineBlock_lt_one_infiniteTrial` already bounds every
approximation singular value of the **directed** sine block `P_{V^⊥} P_U|_U` strictly below
one, with no dimension hypothesis anywhere.  The ambient block `P_{V^⊥} P_U` factors through
it, so its operator norm — which is the directed gap by definition — inherits the bound.

The only thing left is that the paper's `sin Θ` is the **symmetric** gap `‖P_U − P_V‖`,
which in general merely dominates the directed one.  That is exactly what the printed
standing assumption (3.5) supplies, through
`subspaceGap_eq_directedGap_of_crossedDefectsEquivalent`.  Equation (1.5) is not needed
separately: the directed bound is unconditional here. -/

/-- **Davis--Kahan 1970, Section 2: uniform transversality is a consequence.**

`‖sin Θ‖ < 1` follows from the tangent theorem's own form bounds together with the printed
standing assumption (3.5), so it need not be assumed.

Grounded by `:=` on `approximationSingularValue_sineBlock_lt_one_infiniteTrial` (the
directed estimate, dimension-free) and
`subspaceGap_eq_directedGap_of_crossedDefectsEquivalent` (the effect of (3.5)); the tangent
estimate itself is untouched. -/
theorem norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent
    (hT : T.IsSymmetric) (hV : T.Reduces V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ‖sinAngleOperatorC U V‖ < 1 := by
  have hdirected : approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    approximationSingularValue_sineBlock_lt_one_infiniteTrial T V U hT hV hdelta
      hCompressionUpper hUnwantedLower 0
  have hambient : ‖directedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_directedSineAmbient_le (U := U) (V := V) 0
    rw [(directedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  rw [norm_sinAngleOperatorC U V,
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
      U V h35]
  exact hambient

/-- **The whole-space `tan Θ` theorem, Ky Fan form, with transversality derived.**

The same conclusion as `tanTheta_ambient_bounded_kyFan_complex_of_transversality`, with the uniform transversality
hypothesis replaced by the printed standing assumption (3.5). -/
theorem tanTheta_ambient_bounded_kyFan_complex_of_crossedDefects
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k (tanAngleOperatorC U V) ≤
        kyFanApproximationGauge k (T - A) :=
  tanTheta_ambient_bounded_kyFan_complex_of_transversality hT hA hV hAU hdelta hCompressionUpper hUnwantedLower
    (norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent hT hV hdelta
      hCompressionUpper hUnwantedLower h35)

/-- **Davis--Kahan 1970, the whole-space `tan Θ` theorem for every source unitarily
invariant norm, under the printed standing assumptions only.**

Identical to `tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality` except that uniform transversality is no
longer a hypothesis: it is derived from the form bounds and the printed (3.5). -/
theorem tanTheta_ambient_bounded_symmetricNorming_complex_of_crossedDefects
    (N : SymmetricNormingFunction)
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hMem : N.Mem (T - A)) :
    ‖sinAngleOperatorC U V‖ < 1 ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge (T - A) :=
  ⟨norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent hT hV hdelta
      hCompressionUpper hUnwantedLower h35,
    tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality N hT hA hV hAU hdelta hCompressionUpper hUnwantedLower
      (norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent hT hV hdelta
        hCompressionUpper hUnwantedLower h35) hMem⟩

end WholeSpace

end

end DavisKahan1970
end TauCeti
