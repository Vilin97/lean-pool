/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar

/-!
# Complex free-beam form space

The public complex declarations specialize the scalar generic construction.
-/

@[expose] public section

open TauCeti.DavisKahan.Sylvester
open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

noncomputable section

/-- Complex `L²` functions on the unit interval, the ambient beam Hilbert space. -/
abbrev BeamL2 : Type :=
  Scalar.BeamL2 (𝕜 := ℂ)

/-- Pairs of complex `L²` functions representing a beam and its second derivative. -/
abbrev BeamPairSpace : Type :=
  Scalar.BeamPairSpace (𝕜 := ℂ)

/-- The continuous linear projection onto the beam function coordinate. -/
abbrev pairFst : BeamPairSpace →L[ℂ] BeamL2 :=
  Scalar.pairFst (𝕜 := ℂ)

/-- The continuous linear projection onto the second derivative coordinate. -/
abbrev pairSnd : BeamPairSpace →L[ℂ] BeamL2 :=
  Scalar.pairSnd (𝕜 := ℂ)

theorem pairFst_apply (p : BeamPairSpace) :
    pairFst p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).1 := by
  exact Scalar.pairFst_apply (𝕜 := ℂ) p

theorem pairSnd_apply (p : BeamPairSpace) :
    pairSnd p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).2 := by
  exact Scalar.pairSnd_apply (𝕜 := ℂ) p

/-- A uniform norm bound for a continuous complex weight on the unit interval. -/
abbrev pairingBound (g : ℝ → ℂ) (hg : Continuous g) : ℝ :=
  Scalar.pairingBound (𝕜 := ℂ) g hg

theorem pairingBound_spec (g : ℝ → ℂ) (hg : Continuous g) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ pairingBound g hg := by
  exact Scalar.pairingBound_spec (𝕜 := ℂ) g hg

theorem pairingBound_nonneg (g : ℝ → ℂ) (hg : Continuous g) : 0 ≤ pairingBound g hg := by
  exact Scalar.pairingBound_nonneg (𝕜 := ℂ) g hg

/-- Integration against a continuous complex weight as a functional on beam `L²`. -/
abbrev pairingCLM (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 →L[ℂ] ℂ :=
  Scalar.pairingCLM (𝕜 := ℂ) g hg

@[simp] theorem pairingCLM_apply (g : ℝ → ℂ) (hg : Continuous g) (W : BeamL2) :
    pairingCLM g hg W = ∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure := by
  exact Scalar.pairingCLM_apply (𝕜 := ℂ) g hg W

/-- The complex lift of the second derivative of the `k`-th interval bump. -/
abbrev bumpD2C (k : ℕ) (t : ℝ) : ℂ :=
  Scalar.bumpD2Scalar (𝕜 := ℂ) k t

/-- The complex lift of the `k`-th interval bump. -/
abbrev bumpC (k : ℕ) (t : ℝ) : ℂ :=
  Scalar.bumpScalar (𝕜 := ℂ) k t

theorem continuous_bumpD2C (k : ℕ) : Continuous (bumpD2C k) := by
  exact Scalar.continuous_bumpD2Scalar (𝕜 := ℂ) k

theorem continuous_bumpC (k : ℕ) : Continuous (bumpC k) := by
  exact Scalar.continuous_bumpScalar (𝕜 := ℂ) k

/-- The weak second derivative constraint tested against the `k`-th interval bump. -/
abbrev constraintCLM (k : ℕ) : BeamPairSpace →L[ℂ] ℂ :=
  Scalar.constraintCLM (𝕜 := ℂ) k

/-- Complex beam pairs satisfying every bump test for the weak second derivative. -/
abbrev beamFormSubmodule : Submodule ℂ BeamPairSpace :=
  Scalar.beamFormSubmodule (𝕜 := ℂ)

theorem mem_beamFormSubmodule_iff (p : BeamPairSpace) :
    p ∈ beamFormSubmodule ↔ ∀ k : ℕ,
      ∫ t, (pairFst p : ℝ → ℂ) t * bumpD2C k t ∂unitIocMeasure
        = ∫ t, (pairSnd p : ℝ → ℂ) t * bumpC k t ∂unitIocMeasure := by
  exact Scalar.mem_beamFormSubmodule_iff (𝕜 := ℂ) p

theorem isClosed_beamFormSubmodule :
    IsClosed (beamFormSubmodule : Set BeamPairSpace) := by
  exact Scalar.isClosed_beamFormSubmodule (𝕜 := ℂ)

/-- The complex free-beam form domain, viewed as the constrained pair subspace. -/
abbrev BeamV : Type :=
  Scalar.BeamV (𝕜 := ℂ)

/-- The continuous inclusion of the complex form domain into its ambient `L²` space. -/
abbrev beamEmbed : BeamV →L[ℂ] BeamL2 :=
  Scalar.beamEmbed (𝕜 := ℂ)

/-- The continuous map assigning the weak second derivative to a complex beam. -/
abbrev beamSnd : BeamV →L[ℂ] BeamL2 :=
  Scalar.beamSnd (𝕜 := ℂ)

theorem beamEmbed_apply (p : BeamV) : beamEmbed p = pairFst (p : BeamPairSpace) := by
  exact Scalar.beamEmbed_apply (𝕜 := ℂ) p

theorem beamSnd_apply (p : BeamV) : beamSnd p = pairSnd (p : BeamPairSpace) := by
  exact Scalar.beamSnd_apply (𝕜 := ℂ) p

theorem beamV_weak (p : BeamV) (k : ℕ) :
    ∫ t, (beamEmbed p : ℝ → ℂ) t * (intervalBumpD2 k t : ℂ) ∂unitIocMeasure
      = ∫ t, (beamSnd p : ℝ → ℂ) t * (intervalBump k t : ℂ) ∂unitIocMeasure := by
  exact Scalar.beamV_weak (𝕜 := ℂ) p k

theorem beamV_repr (p : BeamV) :
    ∃ a b : ℂ, (beamEmbed p : ℝ → ℂ) =ᵐ[unitIocMeasure]
      fun t => a + b * (t : ℂ) + secondPrimitive ((beamSnd p : ℝ → ℂ)) t := by
  exact Scalar.beamV_repr (𝕜 := ℂ) p

theorem beamEmbed_injective : Function.Injective beamEmbed := by
  exact Scalar.beamEmbed_injective (𝕜 := ℂ)

/-- A continuous complex function represented in `L²` of the unit interval. -/
abbrev contToLp (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 :=
  Scalar.contToLp (𝕜 := ℂ) g hg

theorem coeFn_contToLp (g : ℝ → ℂ) (hg : Continuous g) :
    (contToLp g hg : ℝ → ℂ) =ᵐ[unitIocMeasure] g := by
  exact Scalar.coeFn_contToLp (𝕜 := ℂ) g hg

theorem integral_mul_intervalBumpD2_eq_of_hasDerivAt {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, f t * intervalBumpD2 k t
      = ∫ t in (0 : ℝ)..1, f2 t * intervalBump k t := by
  exact Scalar.integral_mul_intervalBumpD2_eq_of_hasDerivAt hf hf1 hf2 hd hd1 k

theorem contPair_mem {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
        (contToLp (fun t => (f t : ℂ)) (by fun_prop),
          contToLp (fun t => (f2 t : ℂ)) (by fun_prop)))
      ∈ beamFormSubmodule := by
  exact Scalar.contPair_mem (𝕜 := ℂ) hf hf1 hf2 hd hd1

theorem contToLp_polynomial_mem_range (q : Polynomial ℝ) :
    contToLp (fun t => ((q.eval t : ℝ) : ℂ)) (by fun_prop)
      ∈ LinearMap.range (beamEmbed : BeamV →ₗ[ℂ] BeamL2) := by
  exact Scalar.contToLp_polynomial_mem_range (𝕜 := ℂ) q

theorem denseRange_beamEmbed : DenseRange beamEmbed := by
  exact Scalar.denseRange_beamEmbed (𝕜 := ℂ)

theorem beamEmbed_adjoint_injective :
    Function.Injective (ContinuousLinearMap.adjoint beamEmbed) := by
  exact Scalar.beamEmbed_adjoint_injective (𝕜 := ℂ)

/-- Coercive form data for the complex beam, using the shifted bending inner product. -/
abbrev beamCoerciveFormData : Abstract.CoerciveFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) :=
  Scalar.beamCoerciveFormData (𝕜 := ℂ)

theorem beamV_re_inner_self (u : BeamV) :
    RCLike.re ⟪u, u⟫_ℂ = ‖beamEmbed u‖ ^ 2 + ‖beamSnd u‖ ^ 2 := by
  exact Scalar.beamV_re_inner_self (𝕜 := ℂ) u

/-- The complex shifted beam form, with bending energy given by the second derivative norm. -/
abbrev beamShiftedFormData :
    Analytic.ShiftedBeamFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) :=
  Scalar.beamShiftedFormData (𝕜 := ℂ)

/-- The nonnegative self-adjoint complex free-beam operator defined by the shifted form. -/
abbrev beamOperator : BeamL2 →ₗ.[ℂ] BeamL2 :=
  Scalar.beamOperator (𝕜 := ℂ)

theorem beamOperator_isSelfAdjoint : IsSelfAdjoint beamOperator := by
  exact Scalar.beamOperator_isSelfAdjoint (𝕜 := ℂ)

theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℂ := by
  exact Scalar.beamOperator_nonneg (𝕜 := ℂ) x

/-- The constant-one complex function in the beam `L²` space. -/
abbrev beamOneLp : BeamL2 :=
  Scalar.beamOneLp (𝕜 := ℂ)

/-- The complex coordinate function `t ↦ t` in the beam `L²` space. -/
abbrev beamIdLp : BeamL2 :=
  Scalar.beamIdLp (𝕜 := ℂ)

theorem coeFn_beamOneLp : (beamOneLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun _ => (1 : ℂ) := by
  exact Scalar.coeFn_beamOneLp (𝕜 := ℂ)

theorem coeFn_beamIdLp : (beamIdLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun t => (t : ℂ) := by
  exact Scalar.coeFn_beamIdLp (𝕜 := ℂ)

theorem exists_affine_of_beamEmbed_sub (p : BeamV) :
    ∃ a b : ℂ, beamEmbed p - secondPrimitiveCLM (beamSnd p)
      = a • beamOneLp + b • beamIdLp := by
  exact Scalar.exists_affine_of_beamEmbed_sub (𝕜 := ℂ) p

theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed := by
  exact Scalar.isCompactOperator_beamEmbed (𝕜 := ℂ)

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
