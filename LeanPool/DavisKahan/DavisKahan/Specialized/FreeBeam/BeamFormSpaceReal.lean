/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar

/-! # Beam Form Space Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# The real free-beam form model

This file is the explicit real-scalar instantiation of the scalar-generic concrete free-beam
form construction.  Davis--Kahan Section 9 uses the real Hilbert space `L²(0,1)`, so these
names provide the source-facing real model without duplicating the analytic proof.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real


noncomputable section

/-- The real `L²(0,1]` of the free-beam model. -/
abbrev BeamL2 : Type := Scalar.BeamL2 (𝕜 := ℝ)
/-- The real pair space `L² ⊕₂ L²` carrying a function and its second
derivative. -/
abbrev BeamPairSpace : Type := Scalar.BeamPairSpace (𝕜 := ℝ)
/-- The real form domain: the pairs that are genuinely a function and its
second derivative. -/
abbrev BeamV : Type := Scalar.BeamV (𝕜 := ℝ)

/-- First coordinate of a pair: the function. -/
abbrev pairFst : BeamPairSpace →L[ℝ] BeamL2 := Scalar.pairFst (𝕜 := ℝ)
/-- Second coordinate of a pair: its second derivative. -/
abbrev pairSnd : BeamPairSpace →L[ℝ] BeamL2 := Scalar.pairSnd (𝕜 := ℝ)
/-- The form domain as a submodule of the pair space, cut out by the weak
second-derivative identity against every bump. -/
abbrev beamFormSubmodule : Submodule ℝ BeamPairSpace := Scalar.beamFormSubmodule (𝕜 := ℝ)

/-- The form domain's inclusion into `L²`, reading off the function. -/
abbrev beamEmbed : BeamV →L[ℝ] BeamL2 := Scalar.beamEmbed (𝕜 := ℝ)
/-- The form domain's second-derivative map into `L²`. -/
abbrev beamSnd : BeamV →L[ℝ] BeamL2 := Scalar.beamSnd (𝕜 := ℝ)

/-- A continuous function as an element of `L²(0,1]`. -/
abbrev contToLp := Scalar.contToLp (𝕜 := ℝ)
/-- The constant function `1` in `L²(0,1]`. -/
abbrev beamOneLp : BeamL2 := Scalar.beamOneLp (𝕜 := ℝ)
/-- The identity function `t ↦ t` in `L²(0,1]`. -/
abbrev beamIdLp : BeamL2 := Scalar.beamIdLp (𝕜 := ℝ)

/-- The coercive bending form of the real model, as form data. -/
abbrev beamCoerciveFormData := Scalar.beamCoerciveFormData (𝕜 := ℝ)
/-- The shifted bending form of the real model, as form data. -/
abbrev beamShiftedFormData := Scalar.beamShiftedFormData (𝕜 := ℝ)

/-- Membership in the form domain, tested against every interval bump. -/
theorem mem_beamFormSubmodule_iff (p : BeamPairSpace) :
    p ∈ beamFormSubmodule ↔
      ∀ k : ℕ,
        ∫ t, (pairFst p : ℝ → ℝ) t * intervalBumpD2 k t ∂unitIocMeasure =
          ∫ t, (pairSnd p : ℝ → ℝ) t * intervalBump k t ∂unitIocMeasure :=
  Scalar.mem_beamFormSubmodule_iff (𝕜 := ℝ) p

/-- Every form-domain element is affine plus the second primitive of its
second derivative. -/
theorem beamV_repr (p : BeamV) :
    ∃ a b : ℝ, (beamEmbed p : ℝ → ℝ) =ᵐ[unitIocMeasure]
      fun t => a + b * t + secondPrimitive ((beamSnd p : ℝ → ℝ)) t :=
  Scalar.beamV_repr (𝕜 := ℝ) p

/-- A twice continuously differentiable function pairs with its second
derivative inside the form domain. -/
theorem contPair_mem {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x)
    (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (contToLp f hf, contToLp f2 hf2) ∈ beamFormSubmodule :=
  Scalar.contPair_mem (𝕜 := ℝ) hf hf1 hf2 hd hd1

/-- A continuous function represents itself almost everywhere. -/
theorem coeFn_contToLp (g : ℝ → ℝ) (hg : Continuous g) :
    (contToLp g hg : ℝ → ℝ) =ᵐ[unitIocMeasure] g :=
  Scalar.coeFn_contToLp (𝕜 := ℝ) g hg

/-- `beamOneLp` is the constant `1` almost everywhere. -/
theorem coeFn_beamOneLp :
    (beamOneLp : ℝ → ℝ) =ᵐ[unitIocMeasure] fun _ => 1 :=
  Scalar.coeFn_beamOneLp (𝕜 := ℝ)

/-- `beamIdLp` is `t ↦ t` almost everywhere. -/
theorem coeFn_beamIdLp :
    (beamIdLp : ℝ → ℝ) =ᵐ[unitIocMeasure] fun t => t :=
  Scalar.coeFn_beamIdLp (𝕜 := ℝ)

/-- The real `L²(0,1]` free-beam operator represented by the shifted bending form. -/
abbrev beamOperator : BeamL2 →ₗ.[ℝ] BeamL2 :=
  Scalar.beamOperator (𝕜 := ℝ)

/-- The real free-beam realization is self-adjoint. -/
theorem beamOperator_isSelfAdjoint : IsSelfAdjoint beamOperator :=
  Scalar.beamOperator_isSelfAdjoint (𝕜 := ℝ)

/-- The real free-beam realization is nonnegative. -/
theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℝ :=
  Scalar.beamOperator_nonneg (𝕜 := ℝ) x

/-- The real form-domain embedding is compact. -/
theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed :=
  Scalar.isCompactOperator_beamEmbed (𝕜 := ℝ)

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
