/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.AlmostInvariant

/-! # Bounded Almost Invariant -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded spectral bands over a real Hilbert space, by descent

`DavisKahan/SpectralTheory/Real/SpectralRestriction.lean` descends the *unbounded*
spectral projections of a real self-adjoint closed operator from the Cayley
projection-valued measure.  This module does the same one level down, for the
**bounded** projection-valued measure
`TauCeti.BorelCalculus.boundedPVM`, which is the object the Appendix
almost-invariance argument actually consumes.

The single new ingredient is `conjugateOperator_boundedPVM_proj`: every band
projection of `complexify T`, for a self-adjoint `T : E →L[ℝ] E`, is fixed by the
canonical conjugation.  A conjugation-fixed operator *is* a complexification
(`complexify_realPartOperator`), so each band projection descends to a real
bounded operator `realBandProjection`, and the whole projection algebra
(idempotence, self-adjointness, orthogonality of distinct bands, commutation with
`T`, the band norm estimate, and the resolution of the identity) transports
through the isometric injective `⋆`-algebra map `complexify`.

## Why this is not a scalar generalization

`TauCeti.BorelCalculus` is complex in a way that is not a binder convention: it is
built from `cfcHom` at `IsStarNormal` over `spectrum ℂ a`, and
`ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) IsSelfAdjoint` is not an instance in
the pinned dependencies (`ContinuousFunctionalCalculus ℝ · IsSelfAdjoint` is the
one that exists at both scalar fields).  So this module descends rather than
generalizes, exactly as `SpectralRestriction.lean` does for the unbounded case.
-/

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction


open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Eℂ" => RealComplexification E

section BoundedBands

variable {T : E →L[ℝ] E}

/-- The complexification of a real self-adjoint bounded operator is self-adjoint. -/
theorem isSelfAdjoint_complexify_bounded (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (complexify T) :=
  (complexify_isSelfAdjoint_iff T).2 hT

/-- The complexification of a real bounded operator satisfies the hypothesis of
`conjugateOperator_cfcHom`: canonical conjugation sends it to its adjoint.  For a
*self-adjoint* operator this is `conjugateOperator_complexify` composed with
self-adjointness, no resolvent argument needed. -/
theorem conjugateOperator_complexify_eq_star (hT : IsSelfAdjoint T) :
    conjugateOperator (complexify T) = star (complexify T) :=
  (conjugateOperator_complexify T).trans (isSelfAdjoint_complexify_bounded hT).symm

/-- **The diagonal measures of a complexified real self-adjoint operator are
conjugation invariant.**  Bounded counterpart of `diagMeasure_conjugation`; the
symbols entering `diagFunctional` are real, and a real symbol has a
conjugation-fixed calculus image. -/
theorem diagMeasure_conjugation_complexify (hT : IsSelfAdjoint T) (η : Eℂ) :
    TauCeti.BorelCalculus.diagMeasure
        (isSelfAdjoint_complexify_bounded hT).isStarNormal (conjugation η)
      = TauCeti.BorelCalculus.diagMeasure
          (isSelfAdjoint_complexify_bounded hT).isStarNormal η := by
  have hUc := conjugateOperator_complexify_eq_star hT
  refine TauCeti.BorelCalculus.diagMeasure_congr _ (DFunLike.ext _ _ fun g => ?_)
  change (⟪conjugation η, cfcHom _ (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap)
      (conjugation η)⟫_ℂ).re
    = (⟪η, cfcHom _ (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap) η⟫_ℂ).re
  set S := cfcHom (isSelfAdjoint_complexify_bounded hT).isStarNormal
    (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap) with hS
  have hfix : conjugateOperator S = S := by
    rw [hS, conjugateOperator_cfcHom _ hUc, TauCeti.BorelCalculus.star_ofRealLM]
  have hstep : ⟪conjugation η, S (conjugation η)⟫_ℂ = ⟪S η, η⟫_ℂ := by
    have h1 : S (conjugation η) = conjugation (conjugateOperator S η) := by
      rw [conjugateOperator_apply, conjugation_involutive]
    rw [h1, hfix, inner_conjugation]
  rw [hstep, ← inner_conj_symm]
  simp

/-- **Every bounded spectral band projection of a complexified real self-adjoint
operator is fixed by the canonical conjugation.**

This is the ingredient the bounded lane was missing.  `SpectralRestriction.lean`
proves the same statement for the unbounded Cayley projections; the argument is
identical, with the real-part relabelling `TauCeti.BorelCalculus.reCoord`
replacing the inverse Cayley map.  Conjugation permutes the four polarisation
points and fixes the diagonal measures, and the indicator symbol is real, so the
polarisation sum is its own conjugate. -/
theorem conjugateOperator_boundedPVM_proj (hT : IsSelfAdjoint T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    conjugateOperator
        ((TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB)
      = (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB := by
  set hTc := isSelfAdjoint_complexify_bounded hT with hhTc
  set κ := TauCeti.BorelCalculus.reCoord (T := complexify T) with hκ
  have hSm : MeasurableSet (κ ⁻¹' B) :=
    TauCeti.BorelCalculus.measurable_reCoord (T := complexify T) hB
  set ind : _root_.spectrum ℂ (complexify T) → ℂ :=
    (κ ⁻¹' B).indicator (fun _ => (1 : ℂ)) with hind
  -- the four polarisation integrals are real
  have hIreal : ∀ η : Eℂ,
      (starRingEnd ℂ) (∫ w, ind w ∂(TauCeti.BorelCalculus.diagMeasure hTc.isStarNormal η))
        = ∫ w, ind w ∂(TauCeti.BorelCalculus.diagMeasure hTc.isStarNormal η) := by
    intro η
    rw [hind, MeasureTheory.integral_indicator_const _ hSm]
    simp
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [conjugateOperator_apply, inner_conjugation_right, ← inner_conj_symm,
    TauCeti.BorelCalculus.boundedPVM_proj hTc B hB,
    TauCeti.BorelCalculus.inner_borelCalculus, TauCeti.BorelCalculus.inner_borelCalculus]
  have h1 : conjugation ξ + conjugation ψ = conjugation (ξ + ψ) := (map_add _ _ _).symm
  have h2 : conjugation ξ + Complex.I • conjugation ψ
      = conjugation (ξ - Complex.I • ψ) := by
    rw [map_sub, conjugation_complex_smul, Complex.conj_I]
    module
  have h3 : conjugation ξ - conjugation ψ = conjugation (ξ - ψ) := (map_sub _ _ _).symm
  have h4 : conjugation ξ - Complex.I • conjugation ψ
      = conjugation (ξ + Complex.I • ψ) := by
    rw [map_add, conjugation_complex_smul, Complex.conj_I]
    module
  simp only [TauCeti.BorelCalculus.pair, h1, h2, h3, h4,
    diagMeasure_conjugation_complexify hT]
  have e1 := hIreal (ξ + ψ)
  have e2 := hIreal (ξ + Complex.I • ψ)
  have e3 := hIreal (ξ - ψ)
  have e4 := hIreal (ξ - Complex.I • ψ)
  simp only [map_mul, map_sub, map_add, map_one, map_div₀, Complex.conj_I,
    Complex.conj_ofNat]
  rw [e1, e2, e3, e4]
  ring

/-! ## The descended real band projections -/

/-- **The bounded spectral band projection of a real self-adjoint operator**, obtained by
descending the complex band projection of `complexify T`.  It is well defined because
`conjugateOperator_boundedPVM_proj` puts that projection in the fixed-point subalgebra of
the canonical conjugation, and a conjugation-fixed operator *is* a complexification. -/
def realBandProjection (hT : IsSelfAdjoint T) (B : Set ℝ) (hB : MeasurableSet B) :
    E →L[ℝ] E :=
  realPartOperator ((TauCeti.BorelCalculus.boundedPVM
    (isSelfAdjoint_complexify_bounded hT)).proj B hB)

/-- **The defining property of the descended band projection.**  Every law below is this
identity plus injectivity or isometry of `complexify`. -/
theorem complexify_realBandProjection (hT : IsSelfAdjoint T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    complexify (realBandProjection hT B hB)
      = (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB :=
  complexify_realPartOperator (conjugateOperator_boundedPVM_proj hT B hB)

/-- Descended band projections are self-adjoint. -/
theorem realBandProjection_isSelfAdjoint (hT : IsSelfAdjoint T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (realBandProjection hT B hB) :=
  (complexify_isSelfAdjoint_iff _).1 <| by
    rw [complexify_realBandProjection]
    exact (TauCeti.BorelCalculus.boundedPVM
      (isSelfAdjoint_complexify_bounded hT)).isSelfAdjoint_proj B hB

/-- Multiplicativity: intersection of Borel sets is composition of descended band
projections. -/
theorem realBandProjection_inter (hT : IsSelfAdjoint T)
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    realBandProjection hT B₁ hB₁ * realBandProjection hT B₂ hB₂
      = realBandProjection hT (B₁ ∩ B₂) (hB₁.inter hB₂) :=
  complexify_injective <| by
    rw [complexify_mul, complexify_realBandProjection, complexify_realBandProjection,
      complexify_realBandProjection]
    exact (TauCeti.BorelCalculus.boundedPVM
      (isSelfAdjoint_complexify_bounded hT)).proj_inter B₁ B₂ hB₁ hB₂

/-- Descended band projections are idempotent. -/
theorem realBandProjection_idem (hT : IsSelfAdjoint T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    realBandProjection hT B hB * realBandProjection hT B hB
      = realBandProjection hT B hB :=
  complexify_injective <| by
    rw [complexify_mul, complexify_realBandProjection]
    exact (TauCeti.BorelCalculus.boundedPVM
      (isSelfAdjoint_complexify_bounded hT)).proj_idem B hB

/-- Disjoint bands give orthogonal descended projections. -/
theorem realBandProjection_mul_eq_zero (hT : IsSelfAdjoint T)
    {B₁ B₂ : Set ℝ} (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hdisj : B₁ ∩ B₂ = ∅) :
    realBandProjection hT B₁ hB₁ * realBandProjection hT B₂ hB₂ = 0 :=
  complexify_injective <| by
    rw [complexify_mul, complexify_realBandProjection,
      complexify_realBandProjection, complexify_zero,
      (TauCeti.BorelCalculus.boundedPVM
        (isSelfAdjoint_complexify_bounded hT)).proj_inter B₁ B₂ hB₁ hB₂,
      (TauCeti.BorelCalculus.boundedPVM
        (isSelfAdjoint_complexify_bounded hT)).proj_congr hdisj
        (hB₁.inter hB₂) MeasurableSet.empty,
      (TauCeti.BorelCalculus.boundedPVM
        (isSelfAdjoint_complexify_bounded hT)).proj_empty]

/-- The whole line carries the identity. -/
theorem realBandProjection_univ (hT : IsSelfAdjoint T) :
    realBandProjection hT Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℝ E :=
  complexify_injective <| by
    rw [complexify_realBandProjection, complexify_id]
    exact (TauCeti.BorelCalculus.boundedPVM
      (isSelfAdjoint_complexify_bounded hT)).proj_univ

/-- **A descended band projection commutes with its operator**, so every real spectral
band reduces `T`. -/
theorem realBandProjection_comm (hT : IsSelfAdjoint T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    T * realBandProjection hT B hB = realBandProjection hT B hB * T :=
  complexify_injective <| by
    rw [complexify_mul, complexify_mul, complexify_realBandProjection]
    exact TauCeti.BorelCalculus.boundedPVM_proj_comm
      (isSelfAdjoint_complexify_bounded hT) B hB

/-- **The real band estimate.**  If every point of `B` lies within `r` of `lam`, then on the
range of the descended band projection `T` deviates from the scalar `lam` by at most `2 * r`
in operator norm.  The bound transports on the nose because `complexify` is an isometry. -/
theorem norm_comp_realBandProjection_sub_smul_le (hT : IsSelfAdjoint T)
    {B : Set ℝ} (hB : MeasurableSet B) {lam r : ℝ} (hr : 0 ≤ r)
    (hband : ∀ t ∈ B, |t - lam| ≤ r) :
    ‖T ∘L realBandProjection hT B hB - lam • realBandProjection hT B hB‖ ≤ 2 * r := by
  have hc : complexify (T ∘L realBandProjection hT B hB
      - lam • realBandProjection hT B hB)
      = complexify T ∘L (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB
        - ((lam : ℝ) : ℂ) • (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB := by
    rw [complexify_sub, complexify_comp, complexify_real_smul,
      complexify_realBandProjection]
  have hnorm : ‖T ∘L realBandProjection hT B hB - lam • realBandProjection hT B hB‖
      = ‖complexify T ∘L (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB
        - ((lam : ℝ) : ℂ) • (TauCeti.BorelCalculus.boundedPVM
          (isSelfAdjoint_complexify_bounded hT)).proj B hB‖ := by
    rw [← hc, norm_complexify]
  rw [hnorm]
  exact TauCeti.BorelCalculus.norm_comp_boundedPVM_proj_sub_smul_le
    (isSelfAdjoint_complexify_bounded hT) hB hr hband

end BoundedBands

end

end RealSpectralRestriction
end DavisKahan
end TauCeti
