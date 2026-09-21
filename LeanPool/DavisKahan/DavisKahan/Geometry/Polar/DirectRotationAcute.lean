/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Direct Rotation Acute -/

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-!
# The direct rotation at Davis--Kahan's printed acuteness hypothesis

Davis--Kahan 1970 Definition 3.2 calls a pair of subspaces *acute* when the two
crossed intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` vanish, and Proposition 3.1 asserts
that in the acute case the direct rotation exists, is unique, and is
characterised by property (i) — positivity of the two diagonal blocks — alone.

Every other module in this development states the Section 3 endpoints at
`IsUniformlyAcute`, i.e. `‖P_U - P_V‖ < 1`.  That is strictly stronger in
infinite dimension (`TauCeti.isAcute_of_projectionGap_lt_one` is the only
implication that survives without `FiniteDimensional`), and Section 3 of the
paper is explicitly infinite-dimensional.  This module removes the gap.

## Why the polar route survives where the spectral one does not

`spectraDirectRotation` carries its acuteness hypothesis as an underscore
binder: the *object* is `spectraCanonicalPolarFactor U V`, the polar partial
isometry of `S = P_V P_U + P_Vᗮ P_Uᗮ`, which is defined for every pair.  What
uniform acuteness buys elsewhere is invertibility of `S`, and with it the
continuous-functional-calculus branch `spectraDirectRotation_eq_reflectionProductHalfPhase`,
which genuinely needs `-1 ∉ spectrum (J_V J_U)` — a spectral condition that
merely acute pairs can fail.

The polar decomposition needs less.  `Geometry/Polar/Section3Nonacute.lean`
already proves, with no acuteness at all, that `ker S` is exactly the sum of the
two crossed defects, that the polar factor's initial and final projections are
both the projection off that sum, that it intertwines `P_U` with `P_V`, and that
`W + W⋆ = 2|S|`.  Printed Definition 3.2 says precisely that the crossed defects
vanish; so it says precisely that `S` is injective with dense range, which is
exactly what makes the partial isometry a *unitary*.  That is the paper's own
argument — its `Z₀` is an isometry onto the closure of a range, and it is
unitary as soon as `C₀` and `C₀⋆` have zero null space.

## The uniqueness argument

The converse here is shorter than the `IsUniformlyAcute` one it replaces and
does not reproduce the paper's property-(ii) derivation.  If `W` is unitary with
`W P_U = P_V W` and both diagonal blocks positive, then `P_V = W P_U W⋆` and
`P_Vᗮ = W P_Uᗮ W⋆`, so

`S = W (P_U W⋆ P_U + P_Uᗮ W⋆ P_Uᗮ) = W T`,

where `T` is the diagonal part of `W`; self-adjointness of the blocks — which is
part of positivity, and is what a pointwise sign condition would not give over
`ℝ` — is what turns `W⋆` into `W` inside the two compressions.  Then
`S⋆S = T²` with `T ≥ 0`, so `|S| = T` and `W |S| = S`; acuteness makes `ker S`
trivial, so the uniqueness clause of the bounded polar decomposition applies and
`W` is the polar factor.

Nothing in the argument is field-specific, so the statements below hold over any
`RCLike` field: real and complex Hilbert spaces alike, in arbitrary dimension.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Definitions 3.1 and 3.2 and
  Proposition 3.1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-! ## Acuteness as triviality of the kernel -/

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- **Printed Definition 3.2 kills the crossed-defect block.**  The two crossed
defects of the Halmos decomposition *are* the two crossed intersections, so the
paper's acute case is exactly the vanishing of their orthogonal sum. -/
theorem crossedDefectSum_eq_bot (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    crossedDefectSum U V = ⊥ := by
  show (U ⊓ Vᗮ) ⊔ (Uᗮ ⊓ V) = ⊥
  rw [hUV, hVU, bot_sup_eq]

omit [CompleteSpace H] in
/-- **The canonical intertwiner of an acute pair is injective.**  This is the
paper's `Null(C₀) = Null(C₀⋆) = 0`, in the single-operator form. -/
theorem ker_spectraCanonicalIntertwiner_eq_bot
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    LinearMap.ker (spectraCanonicalIntertwiner U V).toLinearMap = ⊥ := by
  rw [ker_canonicalIntertwiner_eq_crossedDefectSum,
    crossedDefectSum_eq_bot U V hUV hVU]

/-- In the acute case the regular block is everything. -/
theorem regularProjection_eq_one (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    regularProjection U V = 1 := by
  have hbot := crossedDefectSum_eq_bot U V hUV hVU
  ext x
  have hmem : x ∈ (crossedDefectSum U V)ᗮ := by
    rw [hbot]; simp
  show (crossedDefectSum U V)ᗮ.starProjection x = (1 : H →L[𝕜] H) x
  rw [one_apply_eq_self]
  exact Submodule.starProjection_eq_self_iff.mpr hmem

/-- The modulus of the canonical intertwiner of an acute pair is injective; it
has the same pointwise norms as the intertwiner. -/
theorem ker_spectraCanonicalAbsoluteValue_eq_bot
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    LinearMap.ker
        (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)).toLinearMap
      = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hax : ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x = 0 := hx
  have hnorm :=
    ContinuousLinearMap.norm_modulus_apply (spectraCanonicalIntertwiner U V) x
  rw [hax, norm_zero, eq_comm, norm_eq_zero] at hnorm
  have hmem : x ∈ LinearMap.ker (spectraCanonicalIntertwiner U V).toLinearMap := hnorm
  rw [ker_spectraCanonicalIntertwiner_eq_bot U V hUV hVU] at hmem
  exact hmem

/-! ## Proposition 3.1(a): existence -/

/-- **The canonical polar factor of an acute pair is unitary.**  Its initial and
final projections are both the regular projection, which acuteness makes `1`.

This is Proposition 3.1's existence clause: the object is the polar factor of
`S`, defined for every pair, and acuteness is what promotes the partial isometry
to a unitary. -/
theorem spectraCanonicalPolarFactor_mem_unitary
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    spectraCanonicalPolarFactor U V ∈ unitary (H →L[𝕜] H) := by
  obtain ⟨h1, h2⟩ := canonicalPolarFactor_initial_final_projection U V
  rw [regularProjection_eq_one U V hUV hVU] at h1 h2
  exact Unitary.mem_iff.mpr ⟨h1, h2⟩

/-- Right cancellation of a self-adjoint operator with trivial kernel: such an
operator has dense range, and a bounded map vanishing on it vanishes. -/
private theorem eq_of_mul_right_cancel_of_ker_eq_bot
    {A T₁ T₂ : H →L[𝕜] H} (hA : IsSelfAdjoint A)
    (hker : LinearMap.ker A.toLinearMap = ⊥) (h : T₁ * A = T₂ * A) : T₁ = T₂ := by
  have hrange : (LinearMap.range A.toLinearMap)ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range,
      ← ContinuousLinearMap.star_eq_adjoint, hA.star_eq]
    exact hker
  have hdense : (LinearMap.range A.toLinearMap).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hrange]
    simp
  have hle : LinearMap.range A.toLinearMap ≤ LinearMap.ker (T₁ - T₂).toLinearMap := by
    rintro y ⟨x, rfl⟩
    have hx := congrArg (fun S : H →L[𝕜] H => S x) h
    simp only [mul_apply_eq_comp] at hx
    show (T₁ - T₂) (A x) = 0
    simp only [sub_apply]
    rw [hx]
    exact sub_self _
  have hclosure := Submodule.topologicalClosure_minimal _ hle (T₁ - T₂).isClosed_ker
  rw [hdense] at hclosure
  have hzero : T₁ - T₂ = 0 := by
    ext x
    exact hclosure (Submodule.mem_top)
  exact sub_eq_zero.mp hzero

/-- **The source diagonal block is the positive Halmos cosine, at the printed
hypothesis.**  Both sides agree after right multiplication by `|S|`, and
acuteness makes `|S|` injective, hence of dense range.  The compiled
`IsUniformlyAcute` version cancels an invertible `|S|` instead. -/
theorem projection_mul_spectraCanonicalPolarFactor_mul_projection
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    U.starProjection * spectraCanonicalPolarFactor U V * U.starProjection =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * U.starProjection := by
  set S : H →L[𝕜] H := spectraCanonicalIntertwiner U V with hSdef
  set A : H →L[𝕜] H := ContinuousLinearMap.modulus S with hAdef
  set W : H →L[𝕜] H := spectraCanonicalPolarFactor U V with hWdef
  set P : H →L[𝕜] H := U.starProjection with hPdef
  set Q : H →L[𝕜] H := V.starProjection with hQdef
  have hWA : W * A = S := by
    rw [ContinuousLinearMap.mul_def]
    exact spectraCanonicalPolarFactor_decomposition U V
  have hAP : Commute A P := spectraCanonicalAbsoluteValue_commute_projection U V
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  have hQi : V.starProjection * V.starProjection = V.starProjection :=
    V.isIdempotentElem_starProjection
  have hQc : Vᗮ.starProjection * Vᗮ.starProjection = Vᗮ.starProjection :=
    Vᗮ.isIdempotentElem_starProjection
  have hPcP : Uᗮ.starProjection * U.starProjection = 0 := by
    rw [Submodule.starProjection_orthogonal' U, sub_mul, one_mul, hP, sub_self]
  have hQcQ : Vᗮ.starProjection * V.starProjection = 0 := by
    rw [Submodule.starProjection_orthogonal' V, sub_mul, one_mul, hQi, sub_self]
  have hQQc : V.starProjection * Vᗮ.starProjection = 0 := by
    rw [Submodule.starProjection_orthogonal' V, mul_sub, mul_one, hQi, sub_self]
  have hSP : S * P = Q * P := by
    show (V.starProjection * U.starProjection +
      Vᗮ.starProjection * Uᗮ.starProjection) * U.starProjection =
      V.starProjection * U.starProjection
    calc (V.starProjection * U.starProjection +
          Vᗮ.starProjection * Uᗮ.starProjection) * U.starProjection
        = V.starProjection * (U.starProjection * U.starProjection) +
            Vᗮ.starProjection * (Uᗮ.starProjection * U.starProjection) := by noncomm_ring
      _ = V.starProjection * U.starProjection := by rw [hP, hPcP, mul_zero, add_zero]
  have hAA : A * A = star S * S := ContinuousLinearMap.modulus_mul_self_eq_star_mul_self S
  have hGram : star S * S * P = P * Q * P := by
    rw [mul_assoc, hSP, star_spectraCanonicalIntertwiner]
    show (U.starProjection * V.starProjection +
      Uᗮ.starProjection * Vᗮ.starProjection) *
      (V.starProjection * U.starProjection) =
      U.starProjection * V.starProjection * U.starProjection
    calc (U.starProjection * V.starProjection +
          Uᗮ.starProjection * Vᗮ.starProjection) * (V.starProjection * U.starProjection)
        = U.starProjection * (V.starProjection * V.starProjection) * U.starProjection +
            Uᗮ.starProjection * (Vᗮ.starProjection * V.starProjection) *
              U.starProjection := by noncomm_ring
      _ = U.starProjection * V.starProjection * U.starProjection := by
            rw [hQi, hQcQ, mul_zero, zero_mul, add_zero]
  refine eq_of_mul_right_cancel_of_ker_eq_bot
    (ContinuousLinearMap.modulus_isSelfAdjoint S)
    (ker_spectraCanonicalAbsoluteValue_eq_bot U V hUV hVU) ?_
  calc P * W * P * A = P * W * (A * P) := by rw [hAP.eq, mul_assoc, mul_assoc]
    _ = P * (W * A) * P := by noncomm_ring
    _ = P * (S * P) := by rw [hWA, mul_assoc]
    _ = P * (Q * P) := by rw [hSP]
    _ = star S * S * P := by rw [hGram, mul_assoc]
    _ = A * A * P := by rw [hAA]
    _ = A * P * A := by rw [mul_assoc, mul_assoc, hAP.eq]

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- A compression of a positive operator is positive. -/
private theorem isPositive_starProjection_compression {A : H →L[𝕜] H}
    (hA : A.IsPositive) (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    (K.starProjection * A * K.starProjection).IsPositive := by
  constructor
  · intro x y
    show ⟪K.starProjection (A (K.starProjection x)), y⟫_𝕜 =
      ⟪x, K.starProjection (A (K.starProjection y))⟫_𝕜
    calc ⟪K.starProjection (A (K.starProjection x)), y⟫_𝕜
        = ⟪A (K.starProjection x), K.starProjection y⟫_𝕜 :=
          Submodule.inner_starProjection_left_eq_right K _ _
      _ = ⟪K.starProjection x, A (K.starProjection y)⟫_𝕜 := hA.1 _ _
      _ = ⟪x, K.starProjection (A (K.starProjection y))⟫_𝕜 :=
          Submodule.inner_starProjection_left_eq_right K _ _
  · intro x
    show 0 ≤ RCLike.re ⟪K.starProjection (A (K.starProjection x)), x⟫_𝕜
    have h : ⟪K.starProjection (A (K.starProjection x)), x⟫_𝕜 =
        ⟪A (K.starProjection x), K.starProjection x⟫_𝕜 :=
      Submodule.inner_starProjection_left_eq_right K _ _
    rw [h]
    exact hA.2 (K.starProjection x)

/-- **Property (i) for the source block, at the printed hypothesis.**  The block
is `|S| P_U`, which is the compression of a positive operator. -/
theorem isPositive_projection_mul_spectraCanonicalPolarFactor_mul_projection
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    (U.starProjection * spectraCanonicalPolarFactor U V * U.starProjection).IsPositive := by
  have hblk := projection_mul_spectraCanonicalPolarFactor_mul_projection U V hUV hVU
  have hAP : Commute (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V))
      (U.starProjection) := spectraCanonicalAbsoluteValue_commute_projection U V
  have hPP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  have hpos : (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (ContinuousLinearMap.modulus_nonneg _)
  have hcomp := isPositive_starProjection_compression hpos U
  have hrw : U.starProjection *
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * U.starProjection =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * U.starProjection := by
    calc U.starProjection *
          ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * U.starProjection
        = ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) *
            (U.starProjection * U.starProjection) := by
          rw [← hAP.eq]; noncomm_ring
      _ = ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) *
            U.starProjection := by rw [hPP]
  rw [hblk, ← hrw]
  exact hcomp

/-- The complementary diagonal block, obtained from the source one by the
orthogonal swap: the canonical intertwiner of `(Uᗮ, Vᗮ)` *is* that of `(U, V)`,
and acuteness of the pair is symmetric under the swap. -/
theorem complementaryProjection_mul_spectraCanonicalPolarFactor_mul_complementaryProjection
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    Uᗮ.starProjection * spectraCanonicalPolarFactor U V * Uᗮ.starProjection =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * Uᗮ.starProjection := by
  have hI : spectraCanonicalIntertwiner Uᗮ Vᗮ = spectraCanonicalIntertwiner U V :=
    spectraCanonicalIntertwiner_orthogonal U V
  have hW : spectraCanonicalPolarFactor Uᗮ Vᗮ = spectraCanonicalPolarFactor U V := by
    unfold spectraCanonicalPolarFactor
    rw [hI]
  have h := projection_mul_spectraCanonicalPolarFactor_mul_projection Uᗮ Vᗮ
    (by rw [Submodule.orthogonal_orthogonal]; exact hVU)
    (by rw [Submodule.orthogonal_orthogonal]; exact hUV)
  rw [hW, hI] at h
  exact h

/-- **Property (i) for the complementary block, at the printed hypothesis.** -/
theorem isPositive_complementaryProjection_mul_spectraCanonicalPolarFactor
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    (Uᗮ.starProjection * spectraCanonicalPolarFactor U V * Uᗮ.starProjection).IsPositive := by
  have hI : spectraCanonicalIntertwiner Uᗮ Vᗮ = spectraCanonicalIntertwiner U V :=
    spectraCanonicalIntertwiner_orthogonal U V
  have hW : spectraCanonicalPolarFactor Uᗮ Vᗮ = spectraCanonicalPolarFactor U V := by
    unfold spectraCanonicalPolarFactor
    rw [hI]
  have h := isPositive_projection_mul_spectraCanonicalPolarFactor_mul_projection Uᗮ Vᗮ
    (by rw [Submodule.orthogonal_orthogonal]; exact hVU)
    (by rw [Submodule.orthogonal_orthogonal]; exact hUV)
  rw [hW] at h
  exact h

/-- **The canonical polar factor of an acute pair carries `U` onto `V`.**
Membership is concluded, not assumed. -/
theorem spectraCanonicalPolarFactor_maps_subspace
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    U.map (spectraCanonicalPolarFactor U V).toLinearMap = V := by
  have hunit := spectraCanonicalPolarFactor_mem_unitary U V hUV hVU
  have hss : star (spectraCanonicalPolarFactor U V) *
      spectraCanonicalPolarFactor U V = 1 := Unitary.star_mul_self_of_mem hunit
  have hs : spectraCanonicalPolarFactor U V *
      star (spectraCanonicalPolarFactor U V) = 1 := Unitary.mul_star_self_of_mem hunit
  have hinj : Function.Injective (spectraCanonicalPolarFactor U V) := by
    intro x y hxy
    have hx := congrArg (fun T : H →L[𝕜] H => T x) hss
    have hy := congrArg (fun T : H →L[𝕜] H => T y) hss
    simp only [mul_apply_eq_comp, one_apply_eq_self] at hx hy
    rw [← hx, ← hy, hxy]
  have hsurj : Function.Surjective (spectraCanonicalPolarFactor U V) := by
    intro y
    refine ⟨star (spectraCanonicalPolarFactor U V) y, ?_⟩
    have h := congrArg (fun T : H →L[𝕜] H => T y) hs
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (canonicalPolarFactor_intertwines_general U V)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      U.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨x, ?_, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    apply hinj
    have h := congrArg (fun T : H →L[𝕜] H => T x)
      (canonicalPolarFactor_intertwines_general U V)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      V.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-! ## Proposition 3.1(b) and (c): uniqueness and the characterisation -/

/-- **Proposition 3.1's third clause at the printed hypothesis: property (i)
alone characterises the direct rotation.**

Among the unitaries intertwining `P_U` with `P_V`, the polar factor of `S` is
the only one whose two diagonal blocks are positive.  Neither equation (3.8) nor
the projection-gap bound is assumed; positivity of the blocks supplies their own
self-adjointness, and that is what makes `S = W T` with `T` the diagonal part of
`W`.  Over `ℝ` the self-adjointness half is not free — a plane rotation by
`π/3` has a diagonal block with nonnegative but non-symmetric quadratic form —
which is why the hypothesis is `IsPositive` rather than a pointwise sign. -/
theorem eq_spectraCanonicalPolarFactor_of_diagonalBlocks_isPositive
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) (W : H →L[𝕜] H)
    (hWunit : W ∈ unitary (H →L[𝕜] H))
    (hint : W * U.starProjection = V.starProjection * W)
    (hblockU : (U.starProjection * W * U.starProjection).IsPositive)
    (hblockUperp : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive) :
    W = spectraCanonicalPolarFactor U V := by
  set P : H →L[𝕜] H := U.starProjection with hPdef
  set P' : H →L[𝕜] H := Uᗮ.starProjection with hP'def
  set Q : H →L[𝕜] H := V.starProjection with hQdef
  set S : H →L[𝕜] H := spectraCanonicalIntertwiner U V with hSdef
  set T : H →L[𝕜] H := P * W * P + P' * W * P' with hTdef
  have hWsW : star W * W = 1 := Unitary.star_mul_self_of_mem hWunit
  have hWWs : W * star W = 1 := Unitary.mul_star_self_of_mem hWunit
  have hPsa : star P = P := (isSelfAdjoint_starProjection U).star_eq
  have hP'sa : star P' = P' := (isSelfAdjoint_starProjection Uᗮ).star_eq
  have hP'eq : P' = 1 - P := Submodule.starProjection_orthogonal' U
  have hC₀ : P * star W * P = P * W * P := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hblockU.1).star_eq
    rwa [star_mul, star_mul, hPsa, mul_assoc] at h
  have hC₁ : P' * star W * P' = P' * W * P' := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hblockUperp.1).star_eq
    rwa [star_mul, star_mul, hP'sa, mul_assoc] at h
  have hQeq : W * P * star W = Q := by
    rw [hint, mul_assoc, hWWs, mul_one]
  have hQ'eq : W * P' * star W = Vᗮ.starProjection := by
    have hstep : W * P' * star W = W * star W - W * P * star W := by
      rw [hP'eq]; noncomm_ring
    rw [hstep, hWWs, hQeq, Submodule.starProjection_orthogonal' V]
  have hSeq : S = W * T := by
    have hexpand : W * T = W * P * star W * P + W * P' * star W * P' := by
      rw [hTdef, ← hC₀, ← hC₁]; noncomm_ring
    rw [hexpand, hQeq, hQ'eq]
    rfl
  have hblocksum : (T).IsPositive := hblockU.add hblockUperp
  have hTpos : (0 : H →L[𝕜] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).mpr hblocksum
  have hTsa : star T = T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hblocksum.1).star_eq
  have hGram : star S * S = T * T := by
    rw [hSeq, star_mul, hTsa]
    calc T * star W * (W * T) = T * (star W * W) * T := by noncomm_ring
      _ = T * T := by rw [hWsW, mul_one]
  have hAeqT : S.modulus = T := by
    rw [ContinuousLinearMap.modulus_eq_sqrt_star_mul_self, hGram]
    exact CFC.sqrt_mul_self T hTpos
  have hcomp : W ∘L S.modulus = S := by
    rw [hAeqT, ← ContinuousLinearMap.mul_def]
    exact hSeq.symm
  have hker : ∀ y ∈ S.polarInitialᗮ, W y = 0 := by
    intro y hy
    rw [ContinuousLinearMap.polarInitial_orthogonal_eq_ker,
      ker_spectraCanonicalIntertwiner_eq_bot U V hUV hVU, Submodule.mem_bot] at hy
    rw [hy, map_zero]
  exact ContinuousLinearMap.eq_polarPartial_of_comp_modulus S W hcomp hker

/-- **Proposition 3.1 at the printed hypothesis, as a biconditional.** -/
theorem eq_spectraCanonicalPolarFactor_iff_diagonalBlocks_isPositive
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) (W : H →L[𝕜] H) :
    W = spectraCanonicalPolarFactor U V ↔
      W ∈ unitary (H →L[𝕜] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive := by
  constructor
  · rintro rfl
    exact ⟨spectraCanonicalPolarFactor_mem_unitary U V hUV hVU,
      canonicalPolarFactor_intertwines_general U V,
      isPositive_projection_mul_spectraCanonicalPolarFactor_mul_projection U V hUV hVU,
      isPositive_complementaryProjection_mul_spectraCanonicalPolarFactor U V hUV hVU⟩
  · rintro ⟨hWunit, hint, hblockU, hblockUperp⟩
    exact eq_spectraCanonicalPolarFactor_of_diagonalBlocks_isPositive U V hUV hVU W hWunit
      hint hblockU hblockUperp

/-- **Proposition 3.1 at the printed hypothesis, in one sentence: in the acute
case the direct rotation exists and is unique.** -/
theorem existsUnique_spectraCanonicalPolarFactor
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    ∃! W : H →L[𝕜] H,
      W ∈ unitary (H →L[𝕜] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive := by
  refine ⟨spectraCanonicalPolarFactor U V,
    (eq_spectraCanonicalPolarFactor_iff_diagonalBlocks_isPositive U V hUV hVU _).mp rfl,
    fun W hW => ?_⟩
  exact (eq_spectraCanonicalPolarFactor_iff_diagonalBlocks_isPositive U V hUV hVU W).mpr hW

end

end DavisKahan
end TauCeti
