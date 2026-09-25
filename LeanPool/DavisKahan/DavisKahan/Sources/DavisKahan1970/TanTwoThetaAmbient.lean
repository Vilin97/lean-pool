/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TanAngleFunctionalCalculus
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientBlockVocabulary
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.CanonicalTangentBridge
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.SelectedBranchSymmetricNorming
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAcuteFormGap
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SharpIdeal
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaAmbient
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Tan Two Theta Ambient -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The whole-space half of the `tan 2Θ` theorem

Section 2 of Davis--Kahan 1970 states the `tan 2θ` theorem with **two**
conclusions,

`δ ‖tan 2Θ₀‖ ≤ 2‖R‖`  and  `δ ‖tan 2Θ‖ ≤ 2‖H‖`,

for every unitarily invariant norm.  Only the directed `Θ₀` half was in the
build.  This module proves the ambient `Θ` half.

## The route, and where it departs from the printed one

The paper writes the ambient double-angle tangent as an off-diagonal `2 × 2`
block operator whose corners are `J₀ tan 2Θ₀` and `J₀⋆ tan 2Θ₁`, bounds each
corner by `2‖R‖/δ`, couples the two corners with Lemma 6.1 and contracts with
the Lemma 6.2 pinch.

As in `TanThetaAmbient.lean`, the formalisation follows that shape but
builds the off-diagonal representative *explicitly*, which removes both the
direct-rotation polar factor `J₀` and the complementary angle `Θ₁`.  Writing
`p` for the orthogonal projection onto `U`, `D = P_V − P_U` and `s = D²`
(`= sin²Θ`), the operator

`Ξ = 2 ((1−p) D p + p D (1−p)) (1 − 2s)⁻¹`

is off-diagonal for `U ⊕ U^⊥` by construction, and, by the two-projection
identity `((1−p)Dp + pD(1−p))² = s − s²`,

`Ξ⋆Ξ = 4 (s − s²) (1 − 2s)⁻² = tan² 2Θ`,

so `|Ξ| = tan 2Θ` exactly.  The `2` in the numerator and the `1 − 2s = cos 2Θ`
in the denominator are the whole difference from the single-angle module; the
projection algebra is the same.

Because `D` is self-adjoint and commutes with `(1 − 2s)⁻¹`, the two corners of
`Ξ` are adjoints of one another, and so are the two corners of the self-adjoint
perturbation `H`.  The complementary estimate the paper obtains from
`‖J₀⋆ tan 2Θ₁‖ = ‖tan 2Θ₀‖` is therefore free here.

The directed corner is identified, *as an operator*, with the ambient graph
tangent `2 Y (1 − Y⋆Y)⁻¹` of the contractive angular operator `Y` whose graph
is `V` — this is `tanTwoBlockRepresentative_lowerBlock` — and hence with
the rectangular coordinate tangent `2 X (1 − X⋆X)⁻¹`, for which the sharp
Ky Fan estimate `δ · kyFanₖ(2X(1−X⋆X)⁻¹) ≤ 2 · kyFanₖ(B₀₁)` is already proved
on an arbitrary Hilbert space.

## The right-hand side is the residual, not the perturbation

The printed directed conclusion carries `2‖R‖`; the printed ambient one carries
`2‖H‖`.  That distinction is *not* cosmetic here: `H` is fully off-diagonal, so
its singular values are those of its corner `R` taken twice, and
`kyFanₖ(H) ≤ 2 kyFanₖ(R)` is sharp.  Feeding Lemma 6.1 a corner estimate
against `‖H‖` therefore yields the ambient bound only with the constant `4`.
The corner estimate used below is against `B₀₁`, i.e. against the residual, and
that is exactly what produces the printed constant `2`.

## Scope

Arbitrary complete complex Hilbert space, no dimension and no compactness
hypothesis, every Ky Fan gauge and hence every unitarily invariant norm in the
paper's sense.

**Where the branch enters, and where it does not.**  The geometry — the
representative `Ξ`, its self-adjointness, `Ξ⋆Ξ = tan²2Θ`, the modulus identity,
the identification of the lower corner with the graph tangent, Lemma 6.1 and
the Lemma 6.2 pinch — is *branch-free*.  It needs only the paper's own
`cos 2θ ≠ 0`, which is what makes `tan 2Θ` a bounded operator at all; principal
angles may exceed `π/4`, and where they do, `tan 2θ` turns negative and the
object every unitarily invariant norm sees is `|tan 2Θ|`.  This is recorded as
`tanTwoTheta_ambient_bounded_branchFree_symmetricNorming_complex_of_corner`, which derives the
  whole ambient
conclusion from the directed corner estimate with no branch anywhere.

The branch enters at exactly **one** place: the directed corner estimate
itself, `tanTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex`, which routes
  through
the contractive Riccati coordinate and therefore needs `IsQuarterAcute U V`
(`‖sin Θ‖ < √2/2`, every principal angle below `π/4`).  Quarter-acuteness is
**concluded, not assumed**, from the paper's four ordered form bounds — the
same configuration under which the directed `tanTwoTheta_selectedBranch_symmetricNorming`
is proved, and the one Theorem 8.1 supplies.  The genuinely branch-free ambient
statement is *not* proved here; see the module note below.

## Main results

* `TauCeti.DavisKahan1970.tanTwoBlockRepresentative`: the explicit
  off-diagonal representative `Ξ`.
* `TauCeti.DavisKahan1970.isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero`:
  `cos 2Θ` is invertible as soon as no principal angle is `π/4` — the
  branch-free replacement for the quarter-acute norm bound.
* `TauCeti.DavisKahan1970.absTanTwoAngleOperatorC_eq_modulus_blockRepresentative`:
  `|Ξ| = |tan 2Θ|`, branch-free.
* `TauCeti.DavisKahan1970.directedTanTwoAngleOperatorC_eq_modulus_blockRepresentative`:
  its quarter-acute specialisation, `|Ξ| = tan 2Θ`.
* `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_branchFree_kyFan_complex_of_corner` and
  `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_branchFree_symmetricNorming_complex_of_corner`: the
  **branch-free reduction** of the ambient conclusion to the directed corner
  estimate, `δ N(|tan 2Θ|) ≤ 2 N(H)` given `δ · kyFan_k (corner) ≤ 2 ·
  kyFan_k R`.
* `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_orderedForm_kyFan_complex`: the Ky Fan form,
  `δ · kyFan_k (tan 2Θ) ≤ 2 · kyFan_k H` for every `k`.
* `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_orderedForm_symmetricNorming_complex`: the
  source form,
  `δ N(tan 2Θ) ≤ 2 N(H)` for every unitarily invariant norm `N` in the paper's
  sense.
* `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex`: the
  printed *residual* form of the directed half, `δ · kyFan_k (tan 2Θ₀) ≤
  2 · kyFan_k R`, which the ambient half consumes.

## What is not proved here

The branch-free ambient statement, in which principal angles may exceed `π/4`.
By the reduction above, the whole of it is one missing input: the directed
corner estimate `δ · kyFan_k (corner of Ξ) ≤ 2 · kyFan_k R` without a branch.

Two routes are already closed off.

*Through the approximation numbers of the graph coordinate.*  The corner of the
ambient representative has Gram operator `4 G (1 − G)⁻²` with `G = X⋆X`, and
`x ↦ 4x/(1−x)²` is *not* monotone across `x = 1`, so the corner's approximation
numbers need not be any rearrangement of the branch-free double-angle tangents
of the approximation numbers of `X`.  A positive `G` with essential spectrum
`{100}` and an isolated eigenvalue at `4` already refutes it: `aₙ(G) = 100` for
every `n`, so every `2√(aₙ)/|1 − aₙ|` is `20/99`, while the corner has an
isolated singular value `4/3`.  Approximation numbers are blind to a singular
value of `X` *below* its essential norm that the non-monotone map sends *above*
it.  So the existing branch-free representative hypothesis cannot be discharged
for this corner.

*Through singular pairs of the graph coordinate.*  The failure is not only in
the sorting.  Take principal angles `θ' < π/4 < θ''` with
`tan 2θ' = −tan 2θ''`, and unit principal vectors `u', u'' ∈ U`, `v', v'' ∈ U^⊥`.
Then `u = (u' + u'')/√2`, `v = (v' − v'')/√2` is an *exact* singular pair of the
corner — the sign flip is the paper's "choose the sign according to `cos 2θⱼ`"
— but it is not even an approximate singular pair of `X`, whose two components
carry the *unequal* positive values `tan θ' ≠ tan θ''`.  A per-pair estimate for
the corner therefore cannot be transported from one for `X`; it has to be
derived from the invariance of `V` directly.  Doing that with the Sylvester
identity `A₁ G − G A₀ = σR + Rσ − R` (`G = P_{U^⊥} P_V P_U`, `σ = sin²Θ`, `R`
the residual) produces a term `Re⟪σu, Au⟫ − Re⟪Av, σv⟫` that the ordered form
bounds on `A` do not control, because `σ` and `A` do not commute.  That is the
open point.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the `tan 2θ` theorem of Section 2,
  Lemmas 6.1 and 6.2, and the Section 7 derivation around equation (7.6).
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-! ### The central numeral `2`

`noncomm_ring` normalises products but does not know that the ring numeral `2`
is central, so the three facts it needs are isolated here. -/

omit [CompleteSpace E] in
private theorem two_eq_one_add_one' : (2 : E →L[ℂ] E) = 1 + 1 :=
  (one_add_one_eq_two).symm

omit [CompleteSpace E] in
private theorem two_comm' (T : E →L[ℂ] E) : T * 2 = 2 * T := by
  rw [two_eq_one_add_one']
  noncomm_ring

private theorem two_star' : star (2 : E →L[ℂ] E) = 2 := by
  rw [two_eq_one_add_one', star_add, star_one]

/-! ### Two-projection algebra reused at the doubled angle

The single-angle module proves the two facts the representative needs about a
pair of idempotents; the three helpers below are the small consequences the
doubled angle uses, restated for an abstract ring so that the
projection-specific rewriting happens once. -/

section ProjectionAlgebra

variable {A : Type*} [Ring A] {p D : A}

private theorem sq_eq_sub' (hkey : D * p + p * D + D * D = D) :
    D * D = D - D * p - p * D := by
  have h : D * D = D - (D * p + p * D) := eq_sub_of_add_eq' hkey
  rw [h]
  abel

private theorem proj_sq' (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = -(p * D * p) := by
  have e1 : p * (D * p) = p * D * p := (mul_assoc p D p).symm
  have e2 : p * (p * D) = p * D := by rw [← mul_assoc, hp]
  rw [sq_eq_sub' hkey, mul_sub, mul_sub, e1, e2]
  abel

private theorem sq_proj' (hp : p * p = p) (hkey : D * p + p * D + D * D = D) :
    D * D * p = -(p * D * p) := by
  have e3 : D * p * p = D * p := by rw [mul_assoc, hp]
  rw [sq_eq_sub' hkey, sub_mul, sub_mul, e3]
  abel

/-- The projection commutes with `sin²Θ`. -/
private theorem proj_comm_sq' (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = D * D * p := by
  rw [proj_sq' hp hkey, sq_proj' hp hkey]

end ProjectionAlgebra

/-! ### Inverses in a ring -/

section RingInverse

variable {A : Type*} [Ring A]

private theorem inverse_comm' {a x : A} (ha : IsUnit a) (h : x * a = a * x) :
    x * Ring.inverse a = Ring.inverse a * x := by
  have h1 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a ha
  have h2 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  calc x * Ring.inverse a
      = (Ring.inverse a * a) * (x * Ring.inverse a) := by rw [h1, one_mul]
    _ = Ring.inverse a * ((a * x) * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * ((x * a) * Ring.inverse a) := by rw [h]
    _ = Ring.inverse a * x * (a * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * x := by rw [h2, mul_one]

private theorem star_inverse' [StarRing A] {a : A} (ha : IsUnit a) :
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

/-! ### The block representative of the ambient double-angle tangent -/

section Representative

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The off-diagonal block representative of the ambient double-angle
tangent.**  It is supported entirely on the two cross blocks of `U ⊕ U^⊥`, and
under uniform quarter transversality its modulus is exactly `tan 2Θ`. -/
def tanTwoBlockRepresentative : E →L[ℂ] E :=
  diagonalPair Uᗮ U
    (2 * (projectorDifference U V * doubleSecant U V))

/-- **The directed `tan 2Θ₀` corner, over `ℂ`.**

The `U → Uᗮ` corner of the ambient double-angle tangent, read as an ambient
operator.  This is the object the paper's directed `tan 2Θ₀` bound is stated on,
and the complex counterpart of `tanTwoDirectedCornerR`; `tanTwoBlockRepresentative`
is the same expression carried on both cross blocks, so the two differ exactly by
which corner is kept. -/
noncomputable def tanTwoDirectedCornerC : E →L[ℂ] E :=
  projectionBlock Uᗮ U
    (2 * (projectorDifference U V * doubleSecant U V))

variable {U V}

omit [CompleteSpace E] in
private theorem comp_eq_mul' (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem starProjection_idem' (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] : W.starProjection * W.starProjection =
      W.starProjection := W.isIdempotentElem_starProjection

/-- Under uniform quarter transversality the operator `1 − 2 sin²Θ` is
invertible: it is `cos 2Θ`, bounded away from `0`. -/
theorem isUnit_one_sub_two_mul_projectorDifference_sq
    (htr : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2) :
    IsUnit (1 - 2 * (projectorDifference U V *
      projectorDifference U V)) := by
  have hsq : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [h2]
  have hD : ‖projectorDifference U V‖ < Real.sqrt 2 / 2 := by
    rw [norm_projectorDifference]; exact htr
  have hD0 : 0 ≤ ‖projectorDifference U V‖ := norm_nonneg _
  have hnorm : ‖2 * (projectorDifference U V *
      projectorDifference U V)‖ < 1 := by
    have hdouble : (2 : E →L[ℂ] E) *
        (projectorDifference U V * projectorDifference U V) =
        projectorDifference U V * projectorDifference U V +
          projectorDifference U V * projectorDifference U V := by
      rw [two_mul]
    rw [hdouble]
    have hsum := norm_add_le (projectorDifference U V *
      projectorDifference U V) (projectorDifference U V *
      projectorDifference U V)
    have hmul := norm_mul_le (projectorDifference U V)
      (projectorDifference U V)
    nlinarith [Real.sqrt_nonneg 2]
  rw [← Units.val_oneSub _ hnorm]
  exact Units.isUnit _

end Representative

/-! ### Identifying the representative with the ambient double-angle tangent -/

section Identification

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The paper's `cos 2θ ≠ 0`, read on the spectrum of `sin Θ`.**

Davis and Kahan's Section 7 argument never assumes a *side* of the quarter
turn; what it does need, and derives from the gap, is that no principal angle
is exactly `π/4`.  Since `cos (2 arcsin s) = 1 − 2s²`, the condition on the
angle spectrum is this condition on the sine spectrum. -/
theorem one_sub_two_sq_ne_zero_of_cos_two_ne_zero
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    {s : ℝ} (hs : s ∈ spectrum ℝ (sinAngleOperatorC U V)) :
    (1 : ℝ) - 2 * (s * s) ≠ 0 := by
  have hsi := spectrum_sinAngleOperatorC_subset_Icc U V hs
  have hmem : Real.arcsin s ∈ spectrum ℝ (angleOperatorC U V) := by
    rw [angleOperatorC,
      cfc_map_spectrum (R := ℝ) (f := Real.arcsin) (a := sinAngleOperatorC U V)
        (isSelfAdjoint_sinAngleOperatorC U V)
        Real.continuous_arcsin.continuousOn]
    exact ⟨s, hs, rfl⟩
  have h := hcos _ hmem
  have hroot : Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - s ^ 2) = 1 - s ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [hsi.1, hsi.2])
  have hcos2 : Real.cos (2 * Real.arcsin s) = 1 - 2 * (s * s) := by
    rw [Real.cos_two_mul', Real.sin_arcsin (by linarith [hsi.1]) hsi.2,
      Real.cos_arcsin, sq, hroot]
    ring
  rwa [hcos2] at h

/-- Quarter-acuteness implies the paper's `cos 2θ ≠ 0`: every angle is below
`π/4`, so the doubled angle is below `π/2`. -/
theorem cos_two_ne_zero_of_norm_sinAngleOperatorC_lt
    (htr : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2)
    {t : ℝ} (ht : t ∈ spectrum ℝ (angleOperatorC U V)) :
    Real.cos (2 * t) ≠ 0 := by
  have h := spectrum_angleOperatorC_lt_pi_div_four U V htr ht
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, h.1], by linarith [h.2]⟩)

/-- `1 − 2 sin²Θ` is the functional calculus of `t ↦ 1 − 2t²` at `sin Θ`. -/
private theorem cfc_one_sub_two_sq' :
    (1 : E →L[ℂ] E) - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V) =
      cfc (fun t : ℝ => 1 - 2 * (t * t)) (sinAngleOperatorC U V) := by
  set S := sinAngleOperatorC U V with hS
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_sinAngleOperatorC U V
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ S) := continuousOn_id
  have hsq : ContinuousOn (fun t : ℝ => t * t) (spectrum ℝ S) := hid.mul hid
  have hSS : S * S = cfc (fun t : ℝ => t * t) S := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) S hid hid, cfc_id' ℝ S]
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ S) :=
    continuousOn_const
  have htwo : ContinuousOn (fun t : ℝ => 2 * (t * t)) (spectrum ℝ S) := by
    fun_prop
  have h2 : (2 : E →L[ℂ] E) * (S * S) = cfc (fun t : ℝ => 2 * (t * t)) S := by
    have hrewrite : cfc (fun t : ℝ => 2 * (t * t)) S =
        cfc (fun t : ℝ => t * t + t * t) S :=
      cfc_congr fun t _ => by ring
    rw [hrewrite, cfc_add (a := S) (fun t : ℝ => t * t) (fun t : ℝ => t * t) hsq hsq,
      ← hSS, two_mul]
  rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => 2 * (t * t)) S hone htwo,
    cfc_const_one ℝ S, ← h2]

/-- **`cos 2Θ` is invertible as soon as no principal angle is `π/4`.**

This is the branch-free replacement for
`isUnit_one_sub_two_mul_projectorDifference_sq`: it asks only that the
angles avoid the pole of the doubled tangent, not that they lie on one
particular side of it.  Compactness of the spectrum turns the pointwise
condition into the uniform separation invertibility needs. -/
theorem isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    IsUnit (1 - 2 * (projectorDifference U V *
      projectorDifference U V)) := by
  rw [projectorDifference_sq, cfc_one_sub_two_sq']
  exact (isUnit_cfc_iff (fun t : ℝ => 1 - 2 * (t * t)) (sinAngleOperatorC U V)
      (by fun_prop) (isSelfAdjoint_sinAngleOperatorC U V)).mpr
    fun t ht => one_sub_two_sq_ne_zero_of_cos_two_ne_zero hcos ht

/-- **Conversely, invertibility of the signed doubled cosine excludes every
quarter-turn pole.**

This is the direction needed by the literal Section 2 `tan 2θ` wrapper: the
ordered gap first proves invertibility of the reflection's diagonal part, and
that operator is the signed doubled cosine.  The source does not assume pole
exclusion; it is recovered here from the resulting unit. -/
theorem cos_two_ne_zero_of_isUnit_one_sub_two_mul_projectorDifference_sq
    (hinv : IsUnit (1 - 2 * (projectorDifference U V *
      projectorDifference U V))) :
    ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0 := by
  have hinv' : IsUnit
      (cfc (fun s : ℝ => 1 - 2 * (s * s)) (sinAngleOperatorC U V)) := by
    rw [← cfc_one_sub_two_sq', ← projectorDifference_sq]
    exact hinv
  have hnonzero : ∀ s ∈ spectrum ℝ (sinAngleOperatorC U V),
      (1 : ℝ) - 2 * (s * s) ≠ 0 :=
    (isUnit_cfc_iff (fun s : ℝ => 1 - 2 * (s * s)) (sinAngleOperatorC U V)
      (by fun_prop) (isSelfAdjoint_sinAngleOperatorC U V)).mp hinv'
  intro t ht
  rw [angleOperatorC,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin) (a := sinAngleOperatorC U V)
      (isSelfAdjoint_sinAngleOperatorC U V)
      Real.continuous_arcsin.continuousOn] at ht
  rcases ht with ⟨s, hs, rfl⟩
  have hsi := spectrum_sinAngleOperatorC_subset_Icc U V hs
  have hroot : Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - s ^ 2) = 1 - s ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [hsi.1, hsi.2])
  have hcos2 : Real.cos (2 * Real.arcsin s) = 1 - 2 * (s * s) := by
    rw [Real.cos_two_mul', Real.sin_arcsin (by linarith [hsi.1]) hsi.2,
      Real.cos_arcsin, sq, hroot]
    ring
  rw [hcos2]
  exact hnonzero s hs

/-- **`|tan 2Θ|² · cos²2Θ = sin²2Θ`**, the scalar Pythagoras of the doubled
tangent, as an operator identity of functional calculi — and **branch-free**:
the hypothesis is only the paper's `cos 2θ ≠ 0`, so principal angles past
`π/4` are allowed. -/
theorem absTanTwo_sq_mul_cos_two_sq
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    absTanTwoAngleOperatorC U V * absTanTwoAngleOperatorC U V *
        ((1 - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V)) *
          (1 - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V))) =
      4 * (sinAngleOperatorC U V * sinAngleOperatorC U V -
        sinAngleOperatorC U V * sinAngleOperatorC U V *
          (sinAngleOperatorC U V * sinAngleOperatorC U V)) := by
  set S := sinAngleOperatorC U V with hS
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_sinAngleOperatorC U V
  have hcontTan : ContinuousOn (fun t : ℝ => |Real.tan (2 * t)|)
      (spectrum ℝ (angleOperatorC U V)) := by
    refine ContinuousOn.abs (Real.continuousOn_tan.comp (by fun_prop) ?_)
    intro t ht
    exact hcos t ht
  have harcsin : ContinuousOn Real.arcsin (spectrum ℝ S) :=
    Real.continuous_arcsin.continuousOn
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ S) := continuousOn_id
  have hsq : ContinuousOn (fun t : ℝ => t * t) (spectrum ℝ S) := hid.mul hid
  have hSS : S * S = cfc (fun t : ℝ => t * t) S := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) S hid hid, cfc_id' ℝ S]
  -- the tangent square as one functional calculus of the sine
  have hcompSq : ContinuousOn
      (fun t : ℝ => |Real.tan (2 * t)| * |Real.tan (2 * t)|)
      (Real.arcsin '' spectrum ℝ S) := by
    have : (Real.arcsin '' spectrum ℝ S) ⊆ spectrum ℝ (angleOperatorC U V) := by
      rw [angleOperatorC,
        cfc_map_spectrum (R := ℝ) (f := Real.arcsin) (a := S) hSsa harcsin]
    exact (hcontTan.mul hcontTan).mono this
  have htanSq :
      absTanTwoAngleOperatorC U V * absTanTwoAngleOperatorC U V =
      cfc ((fun t : ℝ => |Real.tan (2 * t)| * |Real.tan (2 * t)|) ∘ Real.arcsin)
        S := by
    rw [absTanTwoAngleOperatorC,
      ← cfc_mul (fun t : ℝ => |Real.tan (2 * t)|)
        (fun t : ℝ => |Real.tan (2 * t)|)
        (angleOperatorC U V) hcontTan hcontTan,
      angleOperatorC, ← hS,
      ← cfc_comp (fun t : ℝ => |Real.tan (2 * t)| * |Real.tan (2 * t)|)
        Real.arcsin S hSsa hcompSq harcsin]
  have hcosop : (1 : E →L[ℂ] E) - 2 * (S * S) =
      cfc (fun t : ℝ => 1 - 2 * (t * t)) S := by
    have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ S) :=
      continuousOn_const
    have htwo : ContinuousOn (fun t : ℝ => 2 * (t * t)) (spectrum ℝ S) := by
      fun_prop
    have h2 : (2 : E →L[ℂ] E) * (S * S) = cfc (fun t : ℝ => 2 * (t * t)) S := by
      have hrewrite : cfc (fun t : ℝ => 2 * (t * t)) S =
          cfc (fun t : ℝ => t * t + t * t) S :=
        cfc_congr fun t _ => by ring
      rw [hrewrite, cfc_add (a := S) (fun t : ℝ => t * t) (fun t : ℝ => t * t) hsq hsq,
        ← hSS, two_mul]
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => 2 * (t * t)) S hone htwo,
      cfc_const_one ℝ S, ← h2]
  have hfour : (4 : E →L[ℂ] E) * (S * S - S * S * (S * S)) =
      cfc (fun t : ℝ => 4 * (t * t - t * t * (t * t))) S := by
    have hcont : ContinuousOn (fun t : ℝ => t * t - t * t * (t * t))
        (spectrum ℝ S) := by fun_prop
    have hbase : cfc (fun t : ℝ => t * t - t * t * (t * t)) S =
        S * S - S * S * (S * S) := by
      rw [cfc_sub (fun t : ℝ => t * t) (fun t : ℝ => t * t * (t * t)) S hsq
        (by fun_prop), ← hSS,
        cfc_mul (fun t : ℝ => t * t) (fun t : ℝ => t * t) S hsq hsq, ← hSS]
    have hrewrite : cfc (fun t : ℝ => 4 * (t * t - t * t * (t * t))) S =
        cfc (fun t : ℝ =>
          (t * t - t * t * (t * t) + (t * t - t * t * (t * t))) +
            (t * t - t * t * (t * t) + (t * t - t * t * (t * t)))) S :=
      cfc_congr fun t _ => by ring
    rw [hrewrite,
      cfc_add (a := S) (fun t : ℝ => t * t - t * t * (t * t) +
          (t * t - t * t * (t * t)))
        (fun t : ℝ => t * t - t * t * (t * t) + (t * t - t * t * (t * t)))
        (hcont.add hcont) (hcont.add hcont),
      cfc_add (a := S) (fun t : ℝ => t * t - t * t * (t * t))
        (fun t : ℝ => t * t - t * t * (t * t)) hcont hcont, hbase]
    noncomm_ring
  rw [htanSq, hcosop, hfour,
    ← cfc_mul (fun t : ℝ => 1 - 2 * (t * t)) (fun t : ℝ => 1 - 2 * (t * t)) S
      (by fun_prop) (by fun_prop),
    ← cfc_mul
      ((fun t : ℝ => |Real.tan (2 * t)| * |Real.tan (2 * t)|) ∘ Real.arcsin)
      (fun t : ℝ => (1 - 2 * (t * t)) * (1 - 2 * (t * t))) S
      (by
        refine ContinuousOn.comp ?_ harcsin (Set.mapsTo_image _ _)
        exact hcompSq)
      (by fun_prop)]
  refine cfc_congr fun t ht => ?_
  have hti := spectrum_sinAngleOperatorC_subset_Icc U V ht
  have hcosne : (1 : ℝ) - 2 * (t * t) ≠ 0 :=
    one_sub_two_sq_ne_zero_of_cos_two_ne_zero hcos (by rw [hS] at ht; exact ht)
  have hsin2 : Real.sin (2 * Real.arcsin t) =
      2 * t * Real.sqrt (1 - t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arcsin (by linarith [hti.1]) hti.2,
      Real.cos_arcsin]
  have hroot : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [hti.1, hti.2])
  have hcos2 : Real.cos (2 * Real.arcsin t) = 1 - 2 * (t * t) := by
    rw [Real.cos_two_mul', Real.sin_arcsin (by linarith [hti.1]) hti.2,
      Real.cos_arcsin, sq, hroot]
    ring
  have hcc : ((1 : ℝ) - 2 * (t * t)) * (1 - 2 * (t * t)) ≠ 0 :=
    mul_ne_zero hcosne hcosne
  simp only [Function.comp_apply]
  rw [abs_mul_abs_self, Real.tan_eq_sin_div_cos, hsin2, hcos2, div_mul_div_comm,
    div_mul_cancel₀ _ hcc]
  have hexpand : 2 * t * Real.sqrt (1 - t ^ 2) * (2 * t * Real.sqrt (1 - t ^ 2)) =
      4 * (t * t) * (Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2)) := by ring
  rw [hexpand, hroot]
  ring

/-- **The branch-free positive tangent is exactly the modulus of the paper's
literal signed `tan 2Θ`.**

The printed theorem is stated for `tan 2Θ`, not for a separately named
absolute-value operator.  Once the ordered gap has excluded the poles of the
tangent, the signed functional calculus is continuous on the angle spectrum,
and taking its operator modulus is the same as applying `t ↦ |tan (2t)|`
pointwise.  This bridge lets the branch-free proof below expose a literally
paper-facing conclusion while retaining the positive representative internally. -/
theorem absTanTwoAngleOperatorC_eq_modulus_directedTanTwoAngleOperatorC
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    absTanTwoAngleOperatorC U V =
      (tanTwoAngleOperatorC U V).modulus := by
  have hcontTan : ContinuousOn (fun t : ℝ => Real.tan (2 * t))
      (spectrum ℝ (angleOperatorC U V)) :=
    Real.continuousOn_tan.comp (by fun_prop) hcos
  have hcontAbs : ContinuousOn (fun t : ℝ => |Real.tan (2 * t)|)
      (spectrum ℝ (angleOperatorC U V)) :=
    ContinuousOn.abs hcontTan
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (absTanTwoAngleOperatorC_nonneg U V) ?_
  have hself := isSelfAdjoint_tanTwoAngleOperatorC U V
  rw [comp_eq_mul', hself.adjoint_eq, absTanTwoAngleOperatorC,
    tanTwoAngleOperatorC,
    ← cfc_mul (fun t : ℝ => |Real.tan (2 * t)|)
      (fun t : ℝ => |Real.tan (2 * t)|) (angleOperatorC U V)
      hcontAbs hcontAbs,
    ← cfc_mul (fun t : ℝ => Real.tan (2 * t))
      (fun t : ℝ => Real.tan (2 * t)) (angleOperatorC U V)
      hcontTan hcontTan]
  exact cfc_congr fun _ _ => abs_mul_abs_self _

/-- **`tan²2Θ · cos²2Θ = sin²2Θ`** in the quarter-acute branch, where the
ambient double-angle tangent is nonnegative and therefore equal to its
branch-free counterpart. -/
theorem tanTwo_sq_mul_cos_two_sq
    (htr : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2) :
    tanTwoAngleOperatorC U V * tanTwoAngleOperatorC U V *
        ((1 - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V)) *
          (1 - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V))) =
      4 * (sinAngleOperatorC U V * sinAngleOperatorC U V -
        sinAngleOperatorC U V * sinAngleOperatorC U V *
          (sinAngleOperatorC U V * sinAngleOperatorC U V)) := by
  have h := absTanTwo_sq_mul_cos_two_sq
    (fun _ ht => cos_two_ne_zero_of_norm_sinAngleOperatorC_lt htr ht)
  rwa [absTanTwoAngleOperatorC_eq_directedTanTwoAngleOperatorC U V htr] at h

end Identification

/-! ### The block representative has the ambient double-angle tangent as its
modulus -/

section Modulus

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  (hinv : IsUnit (1 - 2 * (projectorDifference U V *
    projectorDifference U V)))

include hinv

omit [CompleteSpace E] in
private theorem doubleSecant_mul_cancel :
    (1 - 2 * (projectorDifference U V * projectorDifference U V)) *
      doubleSecant U V = 1 :=
  Ring.mul_inverse_cancel _
    (hinv)

omit [CompleteSpace E] in
private theorem doubleSecant_mul_cancel' :
    doubleSecant U V *
      (1 - 2 * (projectorDifference U V * projectorDifference U V)) = 1 :=
  Ring.inverse_mul_cancel _
    (hinv)

omit [CompleteSpace E] in
private theorem doubleSecant_comm_projectorDifference :
    projectorDifference U V * doubleSecant U V =
      doubleSecant U V * projectorDifference U V :=
  inverse_comm' (hinv)
    (by noncomm_ring)

omit [CompleteSpace E] in
private theorem doubleSecant_comm_starProjection :
    doubleSecant U V * U.starProjection =
      U.starProjection * doubleSecant U V :=
  (inverse_comm' (hinv)
    (by
      have h := proj_comm_sq' (starProjection_idem' U)
        (projectorDifference_anticommutator (U := U) (V := V))
      have hp2 : U.starProjection *
            (2 * (projectorDifference U V * projectorDifference U V)) =
          2 * (projectorDifference U V * projectorDifference U V) *
            U.starProjection := by
        calc U.starProjection *
              (2 * (projectorDifference U V * projectorDifference U V))
            = 2 * (U.starProjection *
                (projectorDifference U V * projectorDifference U V)) := by
              rw [← mul_assoc, two_comm' U.starProjection, mul_assoc]
          _ = 2 * (projectorDifference U V * projectorDifference U V *
                U.starProjection) := by rw [h]
          _ = 2 * (projectorDifference U V * projectorDifference U V) *
                U.starProjection := by noncomm_ring
      rw [mul_sub, sub_mul, mul_one, one_mul, hp2])).symm

omit [CompleteSpace E] in
private theorem doubleSecant_comm_starProjection_compl :
    doubleSecant U V * (1 - U.starProjection) =
      (1 - U.starProjection) * doubleSecant U V := by
  have h : doubleSecant U V * (1 - U.starProjection) =
      doubleSecant U V - doubleSecant U V * U.starProjection := by
    noncomm_ring
  rw [h, doubleSecant_comm_starProjection hinv]
  noncomm_ring

private theorem doubleSecant_selfAdjoint :
    star (doubleSecant U V) = doubleSecant U V := by
  rw [doubleSecant,
    star_inverse' (hinv)]
  congr 1
  rw [star_sub, star_one, star_mul, two_star', star_mul,
    isSelfAdjoint_projectorDifference.star_eq, two_comm']

omit [CompleteSpace E] in
private theorem doubleSecant_comm_lower :
    ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
        doubleSecant U V =
      doubleSecant U V *
        ((1 - U.starProjection) * projectorDifference U V *
          U.starProjection) := by
  have hRp := doubleSecant_comm_starProjection hinv
  have hRD := doubleSecant_comm_projectorDifference hinv
  have hRc := doubleSecant_comm_starProjection_compl hinv
  calc ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
        doubleSecant U V
      = (1 - U.starProjection) * projectorDifference U V *
          (U.starProjection * doubleSecant U V) := by noncomm_ring
    _ = (1 - U.starProjection) * projectorDifference U V *
          (doubleSecant U V * U.starProjection) := by rw [hRp]
    _ = (1 - U.starProjection) *
          (projectorDifference U V * doubleSecant U V) *
          U.starProjection := by noncomm_ring
    _ = (1 - U.starProjection) *
          (doubleSecant U V * projectorDifference U V) *
          U.starProjection := by rw [hRD]
    _ = ((1 - U.starProjection) * doubleSecant U V) *
          projectorDifference U V * U.starProjection := by noncomm_ring
    _ = (doubleSecant U V * (1 - U.starProjection)) *
          projectorDifference U V * U.starProjection := by rw [hRc]
    _ = doubleSecant U V *
          ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection) := by noncomm_ring

omit [CompleteSpace E] in
private theorem doubleSecant_comm_upper :
    (U.starProjection * projectorDifference U V *
          (1 - U.starProjection)) * doubleSecant U V =
      doubleSecant U V *
        (U.starProjection * projectorDifference U V *
          (1 - U.starProjection)) := by
  have hRp := doubleSecant_comm_starProjection hinv
  have hRD := doubleSecant_comm_projectorDifference hinv
  have hRc := doubleSecant_comm_starProjection_compl hinv
  calc (U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) * doubleSecant U V
      = U.starProjection * projectorDifference U V *
          ((1 - U.starProjection) * doubleSecant U V) := by noncomm_ring
    _ = U.starProjection * projectorDifference U V *
          (doubleSecant U V * (1 - U.starProjection)) := by rw [hRc]
    _ = U.starProjection *
          (projectorDifference U V * doubleSecant U V) *
          (1 - U.starProjection) := by noncomm_ring
    _ = U.starProjection *
          (doubleSecant U V * projectorDifference U V) *
          (1 - U.starProjection) := by rw [hRD]
    _ = (U.starProjection * doubleSecant U V) *
          projectorDifference U V * (1 - U.starProjection) := by noncomm_ring
    _ = (doubleSecant U V * U.starProjection) *
          projectorDifference U V * (1 - U.starProjection) := by rw [hRp]
    _ = doubleSecant U V *
          (U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) := by noncomm_ring

omit [CompleteSpace E] in
/-- The block representative in the explicit `U ⊕ U^⊥` corner form. -/
theorem tanTwoBlockRepresentative_eq :
    tanTwoBlockRepresentative U V =
      2 * (((1 - U.starProjection) * projectorDifference U V *
            U.starProjection +
          U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) * doubleSecant U V) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  have hRp := doubleSecant_comm_starProjection hinv
  have hRc := doubleSecant_comm_starProjection_compl hinv
  rw [tanTwoBlockRepresentative, diagonalPair]
  simp only [hUperp, Submodule.starProjection_orthogonal', comp_eq_mul']
  have h1 : (1 - U.starProjection) *
        (2 * (projectorDifference U V * doubleSecant U V) *
          U.starProjection) =
      2 * ((1 - U.starProjection) * projectorDifference U V *
        U.starProjection * doubleSecant U V) := by
    calc (1 - U.starProjection) *
          (2 * (projectorDifference U V * doubleSecant U V) *
            U.starProjection)
        = 2 * ((1 - U.starProjection) * projectorDifference U V *
            (doubleSecant U V * U.starProjection)) := by noncomm_ring
      _ = 2 * ((1 - U.starProjection) * projectorDifference U V *
            (U.starProjection * doubleSecant U V)) := by rw [hRp]
      _ = 2 * ((1 - U.starProjection) * projectorDifference U V *
            U.starProjection * doubleSecant U V) := by noncomm_ring
  have h2 : U.starProjection *
        (2 * (projectorDifference U V * doubleSecant U V) *
          (1 - U.starProjection)) =
      2 * (U.starProjection * projectorDifference U V *
        (1 - U.starProjection) * doubleSecant U V) := by
    calc U.starProjection *
          (2 * (projectorDifference U V * doubleSecant U V) *
            (1 - U.starProjection))
        = 2 * (U.starProjection * projectorDifference U V *
            (doubleSecant U V * (1 - U.starProjection))) := by noncomm_ring
      _ = 2 * (U.starProjection * projectorDifference U V *
            ((1 - U.starProjection) * doubleSecant U V)) := by rw [hRc]
      _ = 2 * (U.starProjection * projectorDifference U V *
            (1 - U.starProjection) * doubleSecant U V) := by noncomm_ring
  rw [h1, h2]
  noncomm_ring

/-- The block representative is self-adjoint: its two corners are adjoints of
one another. -/
theorem isSelfAdjoint_tanTwoBlockRepresentative :
    IsSelfAdjoint (tanTwoBlockRepresentative U V) := by
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
  rw [IsSelfAdjoint, tanTwoBlockRepresentative_eq hinv, star_mul, two_star',
    star_mul, doubleSecant_selfAdjoint hinv, star_add, hcross, hcross', add_comm,
    add_mul, mul_add, ← doubleSecant_comm_lower hinv, ← doubleSecant_comm_upper hinv,
    two_comm']

/-- **`Ξ⋆Ξ = tan²2Θ`.**  The block representative squares to
`4 sin²Θ cos²Θ · cos⁻²2Θ`. -/
theorem tanTwoBlockRepresentative_mul_self :
    tanTwoBlockRepresentative U V * tanTwoBlockRepresentative U V =
      4 * ((sinAngleOperatorC U V * sinAngleOperatorC U V -
          sinAngleOperatorC U V * sinAngleOperatorC U V *
            (sinAngleOperatorC U V * sinAngleOperatorC U V)) *
        (doubleSecant U V * doubleSecant U V)) := by
  have hsq := offDiagonal_sq (starProjection_idem' U)
    (projectorDifference_anticommutator (U := U) (V := V))
  have hXR : ((1 - U.starProjection) * projectorDifference U V *
        U.starProjection + U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) * doubleSecant U V =
      doubleSecant U V * ((1 - U.starProjection) *
        projectorDifference U V * U.starProjection +
        U.starProjection * projectorDifference U V *
        (1 - U.starProjection)) := by
    rw [add_mul, mul_add, doubleSecant_comm_lower hinv, doubleSecant_comm_upper hinv]
  rw [tanTwoBlockRepresentative_eq hinv]
  set X : E →L[ℂ] E := (1 - U.starProjection) * projectorDifference U V *
    U.starProjection + U.starProjection * projectorDifference U V *
    (1 - U.starProjection) with hXdef
  calc 2 * (X * doubleSecant U V) * (2 * (X * doubleSecant U V))
      = 4 * (X * (doubleSecant U V * X) * doubleSecant U V) := by
        noncomm_ring
    _ = 4 * ((X * X) * (doubleSecant U V * doubleSecant U V)) := by
        rw [← hXR]; noncomm_ring
    _ = 4 * ((sinAngleOperatorC U V * sinAngleOperatorC U V -
          sinAngleOperatorC U V * sinAngleOperatorC U V *
            (sinAngleOperatorC U V * sinAngleOperatorC U V)) *
        (doubleSecant U V * doubleSecant U V)) := by
        rw [hXdef, hsq, projectorDifference_sq]

end Modulus

/-! ### The modulus identity, branch-free

Everything above depends on the branch only through `IsUnit (1 − 2 sin²Θ)`,
i.e. through invertibility of `cos 2Θ`.  The identification of the modulus with
the ambient double-angle tangent needs one thing more — that the tangent be the
*nonnegative* square root — and that is the single place where the quarter turn
genuinely matters.  Replacing `tan 2Θ` by `|tan 2Θ|`, which every unitarily
invariant norm cannot tell apart from it, removes even that. -/

section ModulusBranchFree

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)

include hcos

/-- **The branch-free ambient double-angle tangent is the modulus of the block
representative.**

This is the operator form of the paper's off-diagonal `2 × 2` presentation of
`tan 2Θ`: not merely equality of norms, and not merely of singular-value lists,
but equality of the two moduli, so the substitution is legitimate inside every
unitarily invariant norm.

**No branch is chosen.**  The hypothesis is the paper's own `cos 2θ ≠ 0`, which
is what makes `tan 2Θ` a bounded operator at all; principal angles are free to
exceed `π/4`, and where they do, `tan 2θ` is negative and `|tan 2Θ|` is the
object the norm sees. -/
theorem absTanTwoAngleOperatorC_eq_modulus_blockRepresentative :
    absTanTwoAngleOperatorC U V =
      (tanTwoBlockRepresentative U V).modulus := by
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero
    hcos
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (absTanTwoAngleOperatorC_nonneg U V) ?_
  have hself := isSelfAdjoint_tanTwoBlockRepresentative hinv
  have hadj : (tanTwoBlockRepresentative U V).adjoint ∘L
      tanTwoBlockRepresentative U V =
      tanTwoBlockRepresentative U V * tanTwoBlockRepresentative U V := by
    rw [comp_eq_mul', hself.adjoint_eq]
  rw [hadj, tanTwoBlockRepresentative_mul_self hinv]
  have hcancel := doubleSecant_mul_cancel hinv
  have hcancel' := doubleSecant_mul_cancel' hinv
  rw [projectorDifference_sq] at hcancel hcancel'
  set T := absTanTwoAngleOperatorC U V with hT
  set N2 : E →L[ℂ] E :=
    1 - 2 * (sinAngleOperatorC U V * sinAngleOperatorC U V) with hN2
  set S2 : E →L[ℂ] E := doubleSecant U V with hS2
  calc T * T
      = T * T * ((N2 * S2) * (N2 * S2)) := by rw [hcancel, mul_one, mul_one]
    _ = (T * T * (N2 * N2)) * (S2 * S2) := by
        have hcomm : S2 * N2 = N2 * S2 := by rw [hcancel, hcancel']
        calc T * T * ((N2 * S2) * (N2 * S2))
            = T * T * (N2 * (S2 * N2) * S2) := by noncomm_ring
          _ = T * T * (N2 * (N2 * S2) * S2) := by rw [hcomm]
          _ = (T * T * (N2 * N2)) * (S2 * S2) := by noncomm_ring
    _ = 4 * ((sinAngleOperatorC U V * sinAngleOperatorC U V -
          sinAngleOperatorC U V * sinAngleOperatorC U V *
            (sinAngleOperatorC U V * sinAngleOperatorC U V))) * (S2 * S2) := by
        rw [hT, hN2, absTanTwo_sq_mul_cos_two_sq hcos]
    _ = 4 * ((sinAngleOperatorC U V * sinAngleOperatorC U V -
          sinAngleOperatorC U V * sinAngleOperatorC U V *
            (sinAngleOperatorC U V * sinAngleOperatorC U V)) *
        (S2 * S2)) := by noncomm_ring

end ModulusBranchFree

section ModulusQuarterAcute

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The quarter-acute specialisation of
`absTanTwoAngleOperatorC_eq_modulus_blockRepresentative`, in which the
ambient tangent is nonnegative and the modulus is the literal `tan 2Θ`. -/
theorem directedTanTwoAngleOperatorC_eq_modulus_blockRepresentative
    (htr : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2) :
    tanTwoAngleOperatorC U V =
      (tanTwoBlockRepresentative U V).modulus := by
  have h := absTanTwoAngleOperatorC_eq_modulus_blockRepresentative
    (fun _ ht => cos_two_ne_zero_of_norm_sinAngleOperatorC_lt htr ht)
  rwa [absTanTwoAngleOperatorC_eq_directedTanTwoAngleOperatorC U V htr] at h

end ModulusQuarterAcute

/-! ### The directed corner is the graph tangent

All of the graph geometry is a ring computation once the projection onto `V`
is written through the normal-equation formula
`Q = (p + Y) (1 + Y⋆Y)⁻¹ (p + Y⋆)`, so it is done in an abstract star ring. -/

section GraphAlgebra

variable {A : Type*} [Ring A] [StarRing A] {p Y R Mi S2 Q D : A}

omit [StarRing A] in
private theorem two_central' (T : A) : T * 2 = 2 * T := by
  rw [show (2 : A) = 1 + 1 from (one_add_one_eq_two).symm]
  noncomm_ring

private theorem graph_pQp (hpp : p * p = p) (hpY : p * Y = 0)
    (hsYp : star Y * p = 0) (hRp : R * p = p * R)
    (hQ : Q = (p + Y) * R * (p + star Y)) :
    p * Q * p = R * p := by
  have h1 : p * (p + Y) = p := by rw [mul_add, hpp, hpY, add_zero]
  have h2 : (p + star Y) * p = p := by rw [add_mul, hpp, hsYp, add_zero]
  calc p * Q * p = (p * (p + Y)) * R * ((p + star Y) * p) := by
        rw [hQ]; noncomm_ring
    _ = p * R * p := by rw [h1, h2]
    _ = R * p := by rw [show p * R * p = (p * R) * p from rfl, ← hRp,
        mul_assoc, hpp]

private theorem graph_lowQp (hpp : p * p = p) (hpY : p * Y = 0)
    (hsYp : star Y * p = 0)
    (hQ : Q = (p + Y) * R * (p + star Y)) :
    (1 - p) * Q * p = Y * R * p := by
  have h1 : (1 - p) * (p + Y) = Y := by
    rw [sub_mul, one_mul, mul_add, hpp, hpY, add_zero]
    abel
  have h2 : (p + star Y) * p = p := by rw [add_mul, hpp, hsYp, add_zero]
  calc (1 - p) * Q * p = ((1 - p) * (p + Y)) * R * ((p + star Y) * p) := by
        rw [hQ]; noncomm_ring
    _ = Y * R * p := by rw [h1, h2]

private theorem graph_sq_p (hpp : p * p = p) (hQQ : Q * Q = Q)
    (hpY : p * Y = 0) (hsYp : star Y * p = 0) (hRp : R * p = p * R)
    (hQ : Q = (p + Y) * R * (p + star Y)) (hD : D = Q - p) :
    D * D * p = (1 - R) * p := by
  have hkey : D * p + p * D + D * D = D := by
    rw [hD]
    exact twoProjection_anticommutator hpp hQQ
  have hpDp : p * D * p = R * p - p := by
    have hexp : p * D * p = p * Q * p - p * p * p := by rw [hD]; noncomm_ring
    rw [hexp, graph_pQp hpp hpY hsYp hRp hQ, hpp, hpp]
  rw [sq_proj' hpp hkey, hpDp]
  noncomm_ring

private theorem graph_secant_p (hpp : p * p = p) (hQQ : Q * Q = Q)
    (hpY : p * Y = 0) (hsYp : star Y * p = 0) (hRp : R * p = p * R)
    (hQ : Q = (p + Y) * R * (p + star Y)) (hD : D = Q - p)
    (hRR : R * (1 + star Y * Y) = 1)
    (hML : (1 - star Y * Y) * Mi = 1)
    (hGp : star Y * Y * p = star Y * Y) (hpG : p * (star Y * Y) = star Y * Y)
    (hMip : Mi * p = p * Mi)
    (hS2R : S2 * (1 - 2 * (D * D)) = 1) :
    S2 * p = (1 + star Y * Y) * Mi * p := by
  have hD2p := graph_sq_p hpp hQQ hpY hsYp hRp hQ hD
  have hNp : (1 + star Y * Y) * p = p * (1 + star Y * Y) := by
    rw [add_mul, mul_add, one_mul, mul_one, hGp, hpG]
  have hZp : (1 + star Y * Y) * Mi * p = p * ((1 + star Y * Y) * Mi) := by
    calc (1 + star Y * Y) * Mi * p = (1 + star Y * Y) * (Mi * p) := by noncomm_ring
      _ = (1 + star Y * Y) * (p * Mi) := by rw [hMip]
      _ = ((1 + star Y * Y) * p) * Mi := by noncomm_ring
      _ = (p * (1 + star Y * Y)) * Mi := by rw [hNp]
      _ = p * ((1 + star Y * Y) * Mi) := by noncomm_ring
  have hZR : (2 * R - 1) * ((1 + star Y * Y) * Mi) = 1 := by
    have hstep : (2 * R - 1) * (1 + star Y * Y) = 1 - star Y * Y := by
      calc (2 * R - 1) * (1 + star Y * Y)
          = 2 * (R * (1 + star Y * Y)) - (1 + star Y * Y) := by noncomm_ring
        _ = 2 * 1 - (1 + star Y * Y) := by rw [hRR]
        _ = 1 - star Y * Y := by noncomm_ring
    calc (2 * R - 1) * ((1 + star Y * Y) * Mi)
        = ((2 * R - 1) * (1 + star Y * Y)) * Mi := by noncomm_ring
      _ = (1 - star Y * Y) * Mi := by rw [hstep]
      _ = 1 := hML
  have hcancel : (1 - 2 * (D * D)) * ((1 + star Y * Y) * Mi * p) = p := by
    calc (1 - 2 * (D * D)) * ((1 + star Y * Y) * Mi * p)
        = (1 + star Y * Y) * Mi * p -
            2 * (D * D * ((1 + star Y * Y) * Mi * p)) := by noncomm_ring
      _ = (1 + star Y * Y) * Mi * p -
            2 * (D * D * (p * ((1 + star Y * Y) * Mi))) := by rw [hZp]
      _ = (1 + star Y * Y) * Mi * p -
            2 * ((D * D * p) * ((1 + star Y * Y) * Mi)) := by noncomm_ring
      _ = (1 + star Y * Y) * Mi * p -
            2 * (((1 - R) * p) * ((1 + star Y * Y) * Mi)) := by rw [hD2p]
      _ = (1 + star Y * Y) * Mi * p -
            2 * ((1 - R) * ((1 + star Y * Y) * Mi * p)) := by
          rw [show ((1 : A) - R) * p * ((1 + star Y * Y) * Mi) =
            (1 - R) * (p * ((1 + star Y * Y) * Mi)) from by noncomm_ring, ← hZp]
      _ = (2 * R - 1) * ((1 + star Y * Y) * Mi) * p := by noncomm_ring
      _ = 1 * p := by rw [hZR]
      _ = p := one_mul p
  calc S2 * p = S2 * ((1 - 2 * (D * D)) * ((1 + star Y * Y) * Mi * p)) := by
        rw [hcancel]
    _ = (S2 * (1 - 2 * (D * D))) * ((1 + star Y * Y) * Mi * p) := by noncomm_ring
    _ = (1 + star Y * Y) * Mi * p := by rw [hS2R, one_mul]

/-- **The lower corner of the block representative is the graph tangent.**
Purely algebraic form: `(1 − p) · 2 D (1 − 2D²)⁻¹ · p = 2 Y (1 − Y⋆Y)⁻¹`. -/
private theorem graph_corner (hpp : p * p = p) (hQQ : Q * Q = Q)
    (hYp : Y * p = Y) (hpY : p * Y = 0) (hsYp : star Y * p = 0)
    (hRp : R * p = p * R)
    (hQ : Q = (p + Y) * R * (p + star Y)) (hD : D = Q - p)
    (hRR : R * (1 + star Y * Y) = 1)
    (hML : (1 - star Y * Y) * Mi = 1)
    (hGp : star Y * Y * p = star Y * Y) (hpG : p * (star Y * Y) = star Y * Y)
    (hMip : Mi * p = p * Mi)
    (hS2R : S2 * (1 - 2 * (D * D)) = 1) :
    (1 - p) * (2 * (D * S2)) * p = 2 * (Y * Mi) := by
  have hS2p := graph_secant_p hpp hQQ hpY hsYp hRp hQ hD hRR hML hGp hpG hMip hS2R
  have hZp : (1 + star Y * Y) * Mi * p = p * ((1 + star Y * Y) * Mi) := by
    have hNp : (1 + star Y * Y) * p = p * (1 + star Y * Y) := by
      rw [add_mul, mul_add, one_mul, mul_one, hGp, hpG]
    calc (1 + star Y * Y) * Mi * p = (1 + star Y * Y) * (Mi * p) := by noncomm_ring
      _ = (1 + star Y * Y) * (p * Mi) := by rw [hMip]
      _ = ((1 + star Y * Y) * p) * Mi := by noncomm_ring
      _ = (p * (1 + star Y * Y)) * Mi := by rw [hNp]
      _ = p * ((1 + star Y * Y) * Mi) := by noncomm_ring
  have hlowD : (1 - p) * D * p = Y * R * p := by
    have hexp : (1 - p) * D * p = (1 - p) * Q * p - ((1 - p) * p) * p := by
      rw [hD]; noncomm_ring
    have hzero : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hpp, sub_self]
    rw [hexp, hzero, graph_lowQp hpp hpY hsYp hQ, zero_mul, sub_zero]
  calc (1 - p) * (2 * (D * S2)) * p
      = 2 * ((1 - p) * D * (S2 * p)) := by
        rw [show (1 - p) * (2 * (D * S2)) * p = ((1 - p) * 2) * (D * S2) * p from by
          noncomm_ring, two_central' (1 - p)]
        noncomm_ring
    _ = 2 * ((1 - p) * D * ((1 + star Y * Y) * Mi * p)) := by rw [hS2p]
    _ = 2 * ((1 - p) * D * (p * ((1 + star Y * Y) * Mi))) := by rw [hZp]
    _ = 2 * (((1 - p) * D * p) * ((1 + star Y * Y) * Mi)) := by noncomm_ring
    _ = 2 * ((Y * R * p) * ((1 + star Y * Y) * Mi)) := by rw [hlowD]
    _ = 2 * (Y * R * ((1 + star Y * Y) * Mi * p)) := by rw [hZp]; noncomm_ring
    _ = 2 * (Y * (R * (1 + star Y * Y)) * (Mi * p)) := by noncomm_ring
    _ = 2 * (Y * (Mi * p)) := by rw [hRR, mul_one]
    _ = 2 * (Y * (p * Mi)) := by rw [hMip]
    _ = 2 * ((Y * p) * Mi) := by noncomm_ring
    _ = 2 * (Y * Mi) := by rw [hYp]

end GraphAlgebra

section Corner

variable {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- `IsQuarterAcute` *is* uniform transversality at the quarter turn. -/
theorem norm_sinAngleOperatorC_lt_of_isQuarterAcute (hq : IsQuarterAcute U V) :
    ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2 := by
  rw [← norm_projectorDifference, projectorDifference,
    show V.starProjection - U.starProjection =
      -(U.starProjection - V.starProjection) from by abel, norm_neg]
  exact hq

omit [CompleteSpace E] in
private theorem projectionBlock_lower' (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal', comp_eq_mul',
    comp_eq_mul', mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper' (K : E →L[ℂ] E) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal']
  rw [mul_assoc]
  rfl

omit [CompleteSpace E] in
private theorem projectionBlock_smul' (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    projectionBlock Ω Γ (c • K) = c • projectionBlock Ω Γ K := by
  ext x
  simp [projectionBlock]

/-- **The directed corner of the block representative is the ambient graph
tangent.**  This is the operator identity that lets the sharp Riccati Ky Fan
estimate, stated for `2 X (1 − X⋆X)⁻¹`, be read as an estimate on the corner. -/
theorem tanTwoBlockRepresentative_lowerBlock (hq : IsQuarterAcute U V) :
    projectionBlock Uᗮ U
        (2 * (projectorDifference U V * doubleSecant U V)) =
      doubleAngleTangentOperator (quarterAcuteAngularOperator U V hq)
        (norm_quarterAcuteAngularOperator_lt_one U V hq) := by
  have htr := norm_sinAngleOperatorC_lt_of_isQuarterAcute hq
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq htr
  have hang : IsAngularOperator U (quarterAcuteAngularOperator U V hq) :=
    quarterAcuteAngularOperator_isAngularOperator U V hq
  have hYc : ‖quarterAcuteAngularOperator U V hq‖ < 1 :=
    norm_quarterAcuteAngularOperator_lt_one U V hq
  have hpp : U.starProjection * U.starProjection = U.starProjection :=
    starProjection_idem' U
  have hpsa : star U.starProjection = U.starProjection :=
    (isSelfAdjoint_starProjection U).star_eq
  have hYp : quarterAcuteAngularOperator U V hq * U.starProjection =
      quarterAcuteAngularOperator U V hq := hang.1
  have hpY : U.starProjection * quarterAcuteAngularOperator U V hq = 0 := hang.2
  have hpsY : U.starProjection * star (quarterAcuteAngularOperator U V hq) =
      star (quarterAcuteAngularOperator U V hq) := by
    have h := congrArg star hYp
    rwa [star_mul, hpsa] at h
  have hsYp : star (quarterAcuteAngularOperator U V hq) * U.starProjection = 0 := by
    have h := congrArg star hpY
    rwa [star_mul, hpsa, star_zero] at h
  have hGnorm : ‖star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq‖ < 1 := by
    have h := norm_mul_le (star (quarterAcuteAngularOperator U V hq))
      (quarterAcuteAngularOperator U V hq)
    rw [norm_star] at h
    nlinarith [norm_nonneg (quarterAcuteAngularOperator U V hq)]
  have hGp : star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq * U.starProjection =
      star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq := by
    rw [mul_assoc, hYp]
  have hpG : U.starProjection * (star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq) =
      star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq := by
    rw [← mul_assoc, hpsY]
  have hNunit : IsUnit (1 + star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq) := by
    have hneg : ‖-(star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq)‖ < 1 := by rwa [norm_neg]
    rw [show (1 : E →L[ℂ] E) + star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq =
        1 - -(star (quarterAcuteAngularOperator U V hq) *
          quarterAcuteAngularOperator U V hq) from by abel,
      ← Units.val_oneSub _ hneg]
    exact Units.isUnit _
  have hMunit : IsUnit (1 - star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq) := by
    rw [← Units.val_oneSub _ hGnorm]
    exact Units.isUnit _
  have hNp : (1 + star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) * U.starProjection =
      U.starProjection * (1 + star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) := by
    rw [add_mul, mul_add, one_mul, mul_one, hGp, hpG]
  have hMp : (1 - star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) * U.starProjection =
      U.starProjection * (1 - star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hGp, hpG]
  have hRp : Ring.inverse (1 + star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) * U.starProjection =
      U.starProjection * Ring.inverse (1 +
        star (quarterAcuteAngularOperator U V hq) *
          quarterAcuteAngularOperator U V hq) :=
    (inverse_comm' hNunit hNp.symm).symm
  have hMip : Ring.inverse (1 - star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq) * U.starProjection =
      U.starProjection * Ring.inverse (1 -
        star (quarterAcuteAngularOperator U V hq) *
          quarterAcuteAngularOperator U V hq) :=
    (inverse_comm' hMunit hMp.symm).symm
  have hQQ : V.starProjection * V.starProjection = V.starProjection :=
    starProjection_idem' V
  have hQ : V.starProjection =
      (U.starProjection + quarterAcuteAngularOperator U V hq) *
        Ring.inverse (1 + star (quarterAcuteAngularOperator U V hq) *
          quarterAcuteAngularOperator U V hq) *
        (U.starProjection + star (quarterAcuteAngularOperator U V hq)) := by
    have h := projection_graphSubspace_formula U (quarterAcuteAngularOperator U V hq)
      hang
    simp only [graphSubspace_quarterAcuteAngularOperator U V hq] at h
    rw [show (V.starProjection : E →L[ℂ] E) = V.starProjection from rfl, h,
      graphProjectionFormula,
      show (U.starProjection : E →L[ℂ] E) = U.starProjection from rfl, hYp,
      star_add, hpsa]
  have hcorner := graph_corner (p := U.starProjection)
    (Y := quarterAcuteAngularOperator U V hq)
    (R := Ring.inverse (1 + star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq))
    (Mi := Ring.inverse (1 - star (quarterAcuteAngularOperator U V hq) *
      quarterAcuteAngularOperator U V hq))
    (S2 := doubleSecant U V) (Q := V.starProjection)
    (D := projectorDifference U V)
    hpp hQQ hYp hpY hsYp hRp hQ rfl
    (Ring.inverse_mul_cancel _ hNunit) (Ring.mul_inverse_cancel _ hMunit)
    hGp hpG hMip (doubleSecant_mul_cancel' hinv)
  rw [projectionBlock_lower', hcorner, doubleAngleTangentOperator,
    doubleAngleDenominator]
  change 2 * (quarterAcuteAngularOperator U V hq *
      Ring.inverse (1 - star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq)) =
    (2 : ℂ) • (quarterAcuteAngularOperator U V hq *
      Ring.inverse (1 - star (quarterAcuteAngularOperator U V hq) *
        quarterAcuteAngularOperator U V hq))
  rw [two_smul, two_mul]

end Corner

/-! ### The Davis--Kahan whole-space double-angle tangent theorem -/

section Estimate

variable {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {a b : ℝ}

omit [CompleteSpace E] in
private theorem isOffDiagonal_of_maps_orthogonal'
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    Submodule.IsOffDiagonal U H := by
  change U.diagonalPart H = 0
  apply ContinuousLinearMap.ext
  intro x
  have hPzero : U.starProjection (H (U.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2
      (hHU (U.starProjection x) (U.starProjection_apply_mem x))
  have hQzero : Uᗮ.starProjection (H (Uᗮ.starProjection x)) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr
        (hHUperp (Uᗮ.starProjection x) (Uᗮ.starProjection_apply_mem x)),
      sub_self]
  simp only [Submodule.diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, hPzero, hQzero, add_zero, zero_apply]

private theorem kyFan_upperBlock_eq_compression (K : E →L[ℂ] E) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) =
      kyFanApproximationGauge k (blockCompression U Uᗮ K) := by
  have heq : projectionBlock Uᗮᗮ Uᗮ K = projectionBlock U Uᗮ K := by
    simp only [projectionBlock, Submodule.orthogonal_orthogonal]
  rw [heq]
  exact (projectionBlock_same_compression U Uᗮ K).kyFanApproximationGauge_eq k

private theorem kyFan_lowerBlock_eq_upperBlock (K : E →L[ℂ] E)
    (hK : IsSelfAdjoint K) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮ U K) =
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) := by
  have hadj : projectionBlock Uᗮᗮ Uᗮ K =
      (projectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper', projectionBlock_lower']
    change _ = star _
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hK.star_eq]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_adjoint]

/-- **The printed residual form of the directed half of the `tan 2θ` theorem.**

`δ · kyFanₖ(tan 2Θ₀) ≤ 2 · kyFanₖ(R)`, with the *residual* `R = P_{U^⊥} H P_U`
on the right rather than the whole perturbation.  The directed object is the
lower corner of the ambient block representative, which
`tanTwoBlockRepresentative_lowerBlock` identifies with the graph tangent
`2 X (1 − X⋆X)⁻¹`.

This strengthening is what makes the ambient half sharp: `H` is fully
off-diagonal, so `kyFanₖ(H)` can be twice `kyFanₖ(R)`, and Lemma 6.1 fed with
the weaker corner estimate would produce the constant `4`. -/
theorem tanTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hq : IsQuarterAcute U V) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k
        (projectionBlock Uᗮ U
          (2 * (projectorDifference U V * doubleSecant U V))) ≤
      2 * kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ H) := by
  have hAsym : A.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hHsym : H.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hAHsym : (A + H).IsSymmetric := by
    have h := hAsym.add hHsym
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  have hUreduces : A.Reduces U := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hVreduces : ContinuousLinearMap.Reduces (A + H) V :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAHsym hAplusH_V
  have hoff : Submodule.IsOffDiagonal U H := isOffDiagonal_of_maps_orthogonal' hHU hHUperp
  let B : BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) :=
    TauCeti.DavisKahanExt.subspaceBlockOperatorData (A + H) U hAHsym
  let X : U →L[ℂ] Uᗮ := TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate U V hq
  let C := TauCeti.DavisKahanExt.negBlockOperatorData B
  let Dd := TauCeti.DavisKahanExt.shiftBlockOperatorData C (-b)
  have hsolveB : SolvesRiccati B X := by
    simpa only [B, X] using
      TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate_solvesRiccati
        A H hAsym hHsym U V hVreduces hq
  have hsolveC : SolvesRiccati C X :=
    (TauCeti.DavisKahanExt.solvesRiccati_negBlockOperatorData_iff B X).2 hsolveB
  have hsolveD : SolvesRiccati Dd X :=
    (TauCeti.DavisKahanExt.solvesRiccati_shiftBlockOperatorData_iff C (-b) X).2 hsolveC
  have hB0 : B.A0 = compressOperator U A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A0_add_offDiagonal
        A H U hAHsym hoff
  have hB1 : B.A1 = compressOperator Uᗮ A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A1_add_offDiagonal
        A H U hAHsym hoff
  have hB01 : B.B01 = U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_B01_add_of_reduces
        A H U hAHsym hUreduces
  have hB0high : ∀ z : U, b * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A0 z, z⟫_ℂ := by
    intro z
    rw [hB0]
    have hAz : A (z : E) ∈ U := hAU (z : E) z.property
    change b * ‖(z : E)‖ ^ 2 ≤
      RCLike.re ⟪U.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUhigh (z : E) z.property
  have hB1low : ∀ z : Uᗮ, RCLike.re ⟪B.A1 z, z⟫_ℂ ≤ a * ‖z‖ ^ 2 := by
    intro z
    rw [hB1]
    have hAz : A (z : E) ∈ Uᗮ := hUreduces.2 (z : E) z.property
    change RCLike.re ⟪Uᗮ.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ ≤
      a * ‖(z : E)‖ ^ 2
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUperpLow (z : E) z.property
  have hC0upper : ∀ z : U, RCLike.re ⟪C.A0 z, z⟫_ℂ ≤ (-b) * ‖z‖ ^ 2 := by
    intro z
    have hz := hB0high z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hC1lower : ∀ z : Uᗮ,
      ((-b) + (b - a)) * ‖z‖ ^ 2 ≤ RCLike.re ⟪C.A1 z, z⟫_ℂ := by
    intro z
    have hz := hB1low z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hD0 : ∀ z : U, RCLike.re ⟪Dd.A0 z, z⟫_ℂ ≤ 0 := by
    simpa only [Dd] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A0_nonpos C (-b) hC0upper
  have hD1 : ∀ z : Uᗮ, (b - a) * ‖z‖ ^ 2 ≤ RCLike.re ⟪Dd.A1 z, z⟫_ℂ := by
    simpa only [Dd] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A1_lower C (-b) (b - a) hC1lower
  have hXc : ‖X‖ < 1 := by
    simpa only [X] using
      TauCeti.DavisKahanExt.norm_quarterAcuteAngularCoordinate_lt_one U V hq
  have hraw := sharp_doubleAngleTangentOperator_kyFan Dd (by linarith : (0:ℝ) ≤ b - a)
    hD0 hD1 hsolveD hXc k
  -- the left-hand side: the corner is the ambient graph tangent, whose
  -- approximation numbers are those of the rectangular coordinate tangent
  have hYc : ‖TauCeti.DavisKahanExt.quarterAcuteAngularOperator U V hq‖ < 1 :=
    TauCeti.DavisKahanExt.norm_quarterAcuteAngularOperator_lt_one U V hq
  have hambient :
      doubleAngleTangentOperator
          (TauCeti.DavisKahanExt.quarterAcuteAngularOperator U V hq) hYc =
        Uᗮ.subtypeL ∘L doubleAngleTangentOperator X hXc ∘L
          U.subtypeL.adjoint := by
    simpa only [X, TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate] using
      ambient_doubleAngleTangent_eq_extendCoordinate U
        (TauCeti.DavisKahanExt.quarterAcuteAngularOperator U V hq)
        (TauCeti.DavisKahanExt.quarterAcuteAngularOperator_isAngularOperator U V hq)
        hYc
  have hleft : kyFanApproximationGauge k
      (projectionBlock Uᗮ U
        (2 * (projectorDifference U V * doubleSecant U V))) =
      kyFanApproximationGauge k (doubleAngleTangentOperator X hXc) := by
    rw [tanTwoBlockRepresentative_lowerBlock hq, hambient]
    exact (sameApproximationSingularValues_ambientSubspaceBlock U Uᗮ
      (doubleAngleTangentOperator X hXc)).kyFanApproximationGauge_eq k
  -- the right-hand side: the shifted block's cross entry is the upper block of `H`
  have hDB01 : Dd.B01 = -B.B01 := rfl
  have hright : kyFanApproximationGauge k Dd.B01 =
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ H) := by
    rw [hDB01, kyFanApproximationGauge_neg, kyFan_upperBlock_eq_compression H k,
      hB01, blockCompression, Submodule.adjoint_subtypeL]
  rw [hleft, ← hright]
  exact hraw

/-- **The whole-space `tan 2Θ` theorem reduced to its directed corner, with no
branch anywhere.**

The passage from the printed *directed* conclusion to the printed *ambient*
conclusion — the two corner estimates, Lemma 6.1 and the Lemma 6.2 pinch, and
the identification of the ambient tangent with the modulus of the off-diagonal
representative — uses **no** hypothesis about where the principal angles lie
beyond the paper's own `cos 2θ ≠ 0`, which is exactly what makes `tan 2Θ` a
bounded operator.

So the whole branch dependence of the ambient half sits in the single remaining
hypothesis `hcorner`, the printed residual estimate on the directed corner.
`tanTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex` supplies it in the
  quarter-acute
branch, through the contractive Riccati coordinate; a branch-free supply of the
same estimate is the one thing the branch-free ambient theorem still needs. -/
theorem tanTwoTheta_ambient_bounded_branchFree_kyFan_complex_of_corner
    (hH : IsSelfAdjoint H) (hab : a < b)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hcorner : ∀ j : ℕ,
      (b - a) * kyFanApproximationGauge j
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ H)) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (absTanTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k H := by
  intro k
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero
    hcos
  have hd : (0 : ℝ) < (b - a) / 2 := by linarith
  have hcnorm : ‖((((b - a) / 2 : ℝ)) : ℂ)‖ = (b - a) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hKsa : IsSelfAdjoint
      (2 * (projectorDifference U V * doubleSecant U V)) := by
    rw [IsSelfAdjoint, star_mul, star_mul, two_star',
      doubleSecant_selfAdjoint hinv,
      isSelfAdjoint_projectorDifference.star_eq,
      ← doubleSecant_comm_projectorDifference hinv, two_comm']
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j (projectionBlock Uᗮ U
          (((((b - a) / 2 : ℝ)) : ℂ) •
            (2 * (projectorDifference U V * doubleSecant U V)))) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮ U H) := by
    intro j
    rw [projectionBlock_smul', kyFanApproximationGauge_smul, hcnorm,
      kyFan_lowerBlock_eq_upperBlock H hH j]
    linarith [hcorner j]
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ
          (((((b - a) / 2 : ℝ)) : ℂ) •
            (2 * (projectorDifference U V * doubleSecant U V)))) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ H) := by
    intro j
    rw [projectionBlock_smul', kyFanApproximationGauge_smul, hcnorm,
      ← kyFan_lowerBlock_eq_upperBlock _ hKsa j]
    linarith [hcorner j]
  have hcombine := lemma61_all_kyFan Uᗮ U
    (((((b - a) / 2 : ℝ)) : ℂ) •
      (2 * (projectorDifference U V * doubleSecant U V)))
    (((((b - a) / 2 : ℝ)) : ℂ) •
      (2 * (projectorDifference U V * doubleSecant U V)))
    H H h₀ h₁ k
  have hsum : projectionBlock Uᗮ U
        (((((b - a) / 2 : ℝ)) : ℂ) •
          (2 * (projectorDifference U V * doubleSecant U V))) +
      projectionBlock Uᗮᗮ Uᗮ
        (((((b - a) / 2 : ℝ)) : ℂ) •
          (2 * (projectorDifference U V * doubleSecant U V))) =
      ((((b - a) / 2 : ℝ)) : ℂ) • tanTwoBlockRepresentative U V := by
    rw [tanTwoBlockRepresentative, diagonalPair, projectionBlock_smul',
      projectionBlock_smul', ← smul_add]
    rfl
  have hsumH : projectionBlock Uᗮ U H + projectionBlock Uᗮᗮ Uᗮ H =
      diagonalPair Uᗮ U H := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hcnorm] at hcombine
  have hpinch := diagonalPair_all_kyFan_le Uᗮ U H k
  have hmodulus : kyFanApproximationGauge k (absTanTwoAngleOperatorC U V) =
      kyFanApproximationGauge k (tanTwoBlockRepresentative U V) := by
    rw [absTanTwoAngleOperatorC_eq_modulus_blockRepresentative hcos]
    exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (tanTwoBlockRepresentative U V)).kyFanGauge_eq k
  rw [hmodulus]
  linarith [hcombine.trans hpinch]

/-- **The whole-space `tan 2Θ` theorem, Ky Fan form.**  The second conclusion of
the Section 2 double-angle tangent theorem, at every finite Ky Fan gauge, for
the *ambient* tangent `tan 2Θ`.

The strict quarter-angle branch is concluded, not assumed. -/
theorem tanTwoTheta_ambient_bounded_orderedForm_kyFan_complex
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ, RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (tanTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k H := by
  intro k
  have hq : IsQuarterAcute U V :=
    isQuarterAcute_of_orderedFormGap A H U V hA hH hAU hAplusH_V hab
      hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp
  have htr := norm_sinAngleOperatorC_lt_of_isQuarterAcute hq
  have h := tanTwoTheta_ambient_bounded_branchFree_kyFan_complex_of_corner hH hab
    (fun _ ht => cos_two_ne_zero_of_norm_sinAngleOperatorC_lt htr ht)
    (fun j => tanTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex hA hH hAU
      hAplusH_V
      hab hUhigh hUperpLow hHU hHUperp hq j) k
  rwa [absTanTwoAngleOperatorC_eq_directedTanTwoAngleOperatorC U V htr] at h

/-- **The source-norm ambient conclusion, reduced to the directed corner with no
branch anywhere.**

`δ N(|tan 2Θ|) ≤ 2 N(H)` for every unitarily invariant norm in the paper's
sense, given only the printed residual estimate on the directed corner and the
paper's `cos 2θ ≠ 0`.  Membership of the ambient tangent in the norm's ideal is
*concluded*, not hypothesised.

This is the exact statement of what is left to do for the branch-free ambient
half: supply `hcorner` without a branch. -/
theorem tanTwoTheta_ambient_bounded_branchFree_symmetricNorming_complex_of_corner
    (N : SymmetricNormingFunction)
    (hH : IsSelfAdjoint H) (hab : a < b)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hcorner : ∀ j : ℕ,
      (b - a) * kyFanApproximationGauge j
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ H))
    (hHmem : N.Mem H) :
    N.Mem (absTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (absTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hd : (0 : ℝ) < b - a := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (absTanTwoAngleOperatorC U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • H) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    exact tanTwoTheta_ambient_bounded_branchFree_kyFan_complex_of_corner hH hab hcos hcorner k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • H) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hHmem h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rwa [N.gauge_smul _ hHmem, htwo] at hle

/-- **The whole-space `tan 2Θ` theorem for every source unitarily invariant
norm**: `δ ‖tan 2Θ‖ ≤ 2‖H‖`, the second conclusion of the Section 2 double-angle
tangent theorem.

Membership of the ambient tangent in the norm's ideal is *concluded*, not
hypothesised: the theorem is what forces `tan 2Θ` to be bounded. -/
theorem tanTwoTheta_ambient_bounded_orderedForm_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ, RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    N.Mem (tanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (tanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hd : (0 : ℝ) < b - a := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (tanTwoAngleOperatorC U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • H) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    exact tanTwoTheta_ambient_bounded_orderedForm_kyFan_complex hA hH hAU hAplusH_V hab hUhigh
      hUperpLow hVhigh hVperpLow hHU hHUperp k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • H) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hHmem h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rwa [N.gauge_smul _ hHmem, htwo] at hle

end Estimate

end

end DavisKahan1970
end TauCeti
