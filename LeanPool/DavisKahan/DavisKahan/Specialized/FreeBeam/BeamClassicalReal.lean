/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamModeUniqueness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristicConverse
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamOrthogonality
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootLocalization
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Beam Classical Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Classical identification of the real free-beam realization

This module closes the differential-operator gap in the Section 9 model.  The form-method
operator on real `L²(0,1)` is shown to have a graph-dense classical core whose elements have
four classical derivatives on `[0,1]`, act by the fourth derivative, and satisfy the four
free-end conditions

`u''(0) = u'''(0) = u''(1) = u'''(1) = 0`.

The same regularity bootstrap classifies every positive eigenfunction by the classical
free-beam characteristic equation.  Thus the real form realization is not merely an abstract
self-adjoint operator with the right quadratic form: it is the closed self-adjoint extension
obtained as the graph closure of the classical free-end fourth-derivative operator.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real


noncomputable section

/-! ## Plumbing for the shifted realization -/

/-- The domain of the real beam operator is the domain of its shifted realization. -/
theorem beamOperator_domain_eq :
    beamOperator.domain = beamShiftedFormData.shiftedOperator.domain := rfl

/-- The shifted realization acts as the free-beam operator plus the identity. -/
theorem shifted_apply_of_beam {x : beamOperator.domain} :
    beamShiftedFormData.shiftedOperator x =
      beamOperator x + (x : BeamL2) := by
  have h : beamOperator x =
      beamShiftedFormData.shiftedOperator x - (x : BeamL2) :=
    beamShiftedFormData.beamOperator_apply x
  rw [h]
  abel

/-- The real form-space inner product decomposes along the ambient and bending slots. -/
theorem beamV_inner_decompose (p v : BeamV) :
    ⟪p, v⟫_ℝ = ⟪beamEmbed p, beamEmbed v⟫_ℝ + ⟪beamSnd p, beamSnd v⟫_ℝ := by
  have hcoe : ⟪p, v⟫_ℝ = ⟪(p : BeamPairSpace), (v : BeamPairSpace)⟫_ℝ := rfl
  rw [hcoe, WithLp.prod_inner_apply]
  rfl

/-- Variational identity for an arbitrary domain vector: the bending slot represents the
unshifted beam action. -/
theorem exists_form_representative_of_beam_apply (x : beamOperator.domain) :
    ∃ p : BeamV, beamEmbed p = (x : BeamL2) ∧
      ∀ v : BeamV,
        ⟪beamSnd p, beamSnd v⟫_ℝ =
          ⟪beamOperator x, beamEmbed v⟫_ℝ := by
  set p : BeamV := beamShiftedFormData.formRepresentative x with hpdef
  have hembed : beamEmbed p = (x : BeamL2) :=
    beamShiftedFormData.embed_formRepresentative x
  refine ⟨p, hembed, ?_⟩
  intro v
  have hvar := beamCoerciveFormData.variational_identity
    (beamShiftedFormData.shiftedOperator x) v
  have hform : beamCoerciveFormData.formOperator
      (beamCoerciveFormData.solutionOperator
        (beamShiftedFormData.shiftedOperator x)) = p := by
    rw [show beamCoerciveFormData.formOperator = ContinuousLinearMap.id ℝ BeamV from rfl]
    rfl
  rw [hform] at hvar
  have hforce : beamShiftedFormData.shiftedOperator x =
      beamOperator x + (x : BeamL2) := shifted_apply_of_beam
  have hlhs : ⟪p, v⟫_ℝ =
      ⟪(x : BeamL2), beamEmbed v⟫_ℝ + ⟪beamSnd p, beamSnd v⟫_ℝ := by
    rw [beamV_inner_decompose, hembed]
  have hrhs : ⟪beamShiftedFormData.shiftedOperator x,
      beamCoerciveFormData.embed v⟫_ℝ =
      ⟪beamOperator x, beamEmbed v⟫_ℝ +
        ⟪(x : BeamL2), beamEmbed v⟫_ℝ := by
    rw [hforce, inner_add_left]
    rfl
  rw [hlhs, hrhs] at hvar
  linear_combination hvar

/-! ## The affine kernel -/

/-- Both real bump moments of the second derivative vanish. -/
theorem integral_intervalBumpD2_unit_eq_zero (k : ℕ) :
    ∫ t, intervalBumpD2 k t ∂unitIocMeasure = 0 := by
  rw [integral_unitIocMeasure_eq_intervalIntegral, integral_intervalBumpD2]

/-- The first real moment of the second bump derivative vanishes. -/
theorem integral_id_mul_intervalBumpD2_unit_eq_zero (k : ℕ) :
    ∫ t, t * intervalBumpD2 k t ∂unitIocMeasure = 0 := by
  rw [integral_unitIocMeasure_eq_intervalIntegral, integral_id_mul_intervalBumpD2]

/-- The affine pair `(a + bt, 0)` lies in the real beam form space. -/
theorem affinePair_mem (a b : ℝ) :
    ((WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) ∈ beamFormSubmodule := by
  rw [mem_beamFormSubmodule_iff]
  intro k
  have hfst : pairFst ((WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = a • beamOneLp + b • beamIdLp := by
    rw [Scalar.pairFst_apply]
    simp
  have hsnd : pairSnd ((WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = 0 := by
    rw [Scalar.pairSnd_apply]
    simp
  rw [hfst, hsnd]
  have hrhs : ∫ t, ((0 : BeamL2) : ℝ → ℝ) t * intervalBump k t ∂unitIocMeasure = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℝ 2 unitIocMeasure] with t ht
      rw [ht]
      simp
  rw [hrhs]
  have hlhs : ∫ t, ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℝ) t *
      intervalBumpD2 k t ∂unitIocMeasure =
      a * (∫ t, intervalBumpD2 k t ∂unitIocMeasure) +
        b * ∫ t, t * intervalBumpD2 k t ∂unitIocMeasure := by
    have ha : Integrable (fun t : ℝ => a * intervalBumpD2 k t) unitIocMeasure :=
      (integrable_unitIocMeasure_of_continuous (continuous_intervalBumpD2 k)).const_mul a
    have hb : Integrable (fun t : ℝ => b * (t * intervalBumpD2 k t)) unitIocMeasure :=
      (integrable_mul_of_continuous
        (integrable_unitIocMeasure_of_continuous continuous_id)
        (continuous_intervalBumpD2 k)).const_mul b
    calc
      ∫ t, ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℝ) t *
          intervalBumpD2 k t ∂unitIocMeasure =
          ∫ t, (a * intervalBumpD2 k t + b * (t * intervalBumpD2 k t))
            ∂unitIocMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
          Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp,
          coeFn_beamOneLp, coeFn_beamIdLp] with t hadd hsa hsb h1 hT
        rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
          smul_eq_mul, smul_eq_mul]
        ring
      _ = (∫ t, a * intervalBumpD2 k t ∂unitIocMeasure) +
          ∫ t, b * (t * intervalBumpD2 k t) ∂unitIocMeasure := integral_add ha hb
      _ = a * (∫ t, intervalBumpD2 k t ∂unitIocMeasure) +
          b * ∫ t, t * intervalBumpD2 k t ∂unitIocMeasure := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hlhs, integral_intervalBumpD2_unit_eq_zero,
    integral_id_mul_intervalBumpD2_unit_eq_zero]
  ring

/-- The real affine ambient element `a + bt`. -/
def affineLp (a b : ℝ) : BeamL2 := a • beamOneLp + b • beamIdLp

/-- The real form representative of an affine element. -/
def affineV (a b : ℝ) : BeamV :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm (affineLp a b, 0),
    affinePair_mem a b⟩

/-- The inclusion of an affine form-domain element is the affine function. -/
theorem beamEmbed_affineV (a b : ℝ) : beamEmbed (affineV a b) = affineLp a b := by
  rw [show beamEmbed (affineV a b) = pairFst ((affineV a b : BeamV) : BeamPairSpace) from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace) =
    (WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm (affineLp a b, 0) from rfl]
  rw [Scalar.pairFst_apply]
  simp

/-- An affine form-domain element has vanishing second derivative. -/
theorem beamSnd_affineV (a b : ℝ) : beamSnd (affineV a b) = 0 := by
  rw [show beamSnd (affineV a b) = pairSnd ((affineV a b : BeamV) : BeamPairSpace) from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace) =
    (WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm (affineLp a b, 0) from rfl]
  rw [Scalar.pairSnd_apply]
  simp

/-- The adjoint embedding sends a real affine element to its form representative. -/
theorem adjoint_beamEmbed_affine (a b : ℝ) :
    ContinuousLinearMap.adjoint beamEmbed (affineLp a b) = affineV a b := by
  refine ext_inner_right ℝ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, beamV_inner_decompose,
    beamEmbed_affineV, beamSnd_affineV, inner_zero_left, add_zero]

/-- Real affine elements lie in the beam-operator domain and are annihilated. -/
theorem beamOperator_affine_mem_and_zero (a b : ℝ) :
    ∃ h : affineLp a b ∈ beamOperator.domain,
      beamOperator ⟨affineLp a b, h⟩ = 0 := by
  have hres : beamCoerciveFormData.resolvent (affineLp a b) = affineLp a b := by
    rw [show beamCoerciveFormData.resolvent =
      beamCoerciveFormData.embed ∘L beamCoerciveFormData.solutionOperator from rfl]
    have hsol : beamCoerciveFormData.solutionOperator (affineLp a b) = affineV a b := by
      rw [show beamCoerciveFormData.solutionOperator =
        beamCoerciveFormData.formInverse ∘L
          ContinuousLinearMap.adjoint beamCoerciveFormData.embed from rfl]
      have hinv : beamCoerciveFormData.formInverse = 1 := by
        rw [show beamCoerciveFormData.formInverse =
          Ring.inverse beamCoerciveFormData.formOperator from rfl]
        rw [show beamCoerciveFormData.formOperator = ContinuousLinearMap.id ℝ BeamV from rfl]
        exact Ring.inverse_one _
      rw [ContinuousLinearMap.comp_apply, hinv]
      rw [show ContinuousLinearMap.adjoint beamCoerciveFormData.embed (affineLp a b) =
        affineV a b from adjoint_beamEmbed_affine a b]
      rfl
    rw [ContinuousLinearMap.comp_apply, hsol]
    exact beamEmbed_affineV a b
  have hmem : affineLp a b ∈ beamOperator.domain := by
    rw [show beamOperator.domain =
      LinearMap.range (beamCoerciveFormData.resolvent : BeamL2 →ₗ[ℝ] BeamL2) from rfl]
    exact ⟨affineLp a b, hres⟩
  refine ⟨hmem, ?_⟩
  have hshift : beamShiftedFormData.shiftedOperator ⟨affineLp a b, hmem⟩ =
      affineLp a b := by
    have happ := Abstract.inversePartialMap_apply_R beamCoerciveFormData.resolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective (affineLp a b)
    have hsub : (⟨beamCoerciveFormData.resolvent (affineLp a b),
        LinearMap.mem_range_self _ (affineLp a b)⟩ :
          beamShiftedFormData.shiftedOperator.domain) = ⟨affineLp a b, hmem⟩ :=
      Subtype.ext hres
    rw [← hsub]
    exact happ
  have happly : beamOperator ⟨affineLp a b, hmem⟩ =
      beamShiftedFormData.shiftedOperator ⟨affineLp a b, hmem⟩ - affineLp a b :=
    beamShiftedFormData.beamOperator_apply _
  rw [happly, hshift, sub_self]

/-- Conversely, every real zero mode is affine. -/
theorem exists_affine_of_beamOperator_eq_zero {x : beamOperator.domain}
    (hx : beamOperator x = 0) :
    ∃ a b : ℝ, (x : BeamL2) = affineLp a b := by
  have hquad : RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℝ =
      beamShiftedFormData.bendingEnergy (beamShiftedFormData.formRepresentative x) :=
    beamShiftedFormData.beam_quadratic_eq_bendingEnergy x
  rw [hx, inner_zero_left] at hquad
  have hbend0 : beamShiftedFormData.bendingEnergy
      (beamShiftedFormData.formRepresentative x) = 0 := by
    rw [← hquad]
    simp
  have hbend : ‖beamSnd (beamShiftedFormData.formRepresentative x)‖ ^ 2 = 0 := hbend0
  have hsnd0 : beamSnd (beamShiftedFormData.formRepresentative x) = 0 := by
    have hnorm : ‖beamSnd (beamShiftedFormData.formRepresentative x)‖ = 0 := by
      nlinarith [norm_nonneg (beamSnd (beamShiftedFormData.formRepresentative x))]
    exact norm_eq_zero.mp hnorm
  obtain ⟨a, b, hab⟩ := beamV_repr (beamShiftedFormData.formRepresentative x)
  have hembed := beamShiftedFormData.embed_formRepresentative x
  refine ⟨a, b, ?_⟩
  have hK0 : secondPrimitive (𝕜 := ℝ)
      ((beamSnd (beamShiftedFormData.formRepresentative x) : ℝ → ℝ)) =
      secondPrimitive (𝕜 := ℝ) (fun _ : ℝ => (0 : ℝ)) := by
    apply secondPrimitive_congr_ae
    rw [hsnd0]
    exact Lp.coeFn_zero ℝ 2 unitIocMeasure
  have hKzero : ∀ t : ℝ, secondPrimitive (𝕜 := ℝ) (fun _ : ℝ => (0 : ℝ)) t = 0 := by
    intro t
    rw [secondPrimitive_def]
    simp
  refine Lp.ext ?_
  have hxcoe : ((x : BeamL2) : ℝ → ℝ) =ᵐ[unitIocMeasure]
      (beamEmbed (beamShiftedFormData.formRepresentative x) : ℝ → ℝ) := by
    rw [show beamEmbed (beamShiftedFormData.formRepresentative x) = (x : BeamL2) from hembed]
  filter_upwards [hxcoe, hab, Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp,
    coeFn_beamOneLp, coeFn_beamIdLp] with t hx1 hx2 hadd hsa hsb h1 hT
  rw [hx1, hx2, hK0, hKzero, add_zero]
  rw [show (affineLp a b : ℝ → ℝ) t =
    ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℝ) t from rfl]
  rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply,
    h1, hT, smul_eq_mul, smul_eq_mul]
  ring

/-! ## Distributional pairing and the classical bootstrap -/

/-- Test the variational beam identity against a real `C²` function. -/
theorem beam_pairing_integral {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV,
      ⟪beamSnd p, beamSnd v⟫_ℝ = ⟪beamOperator x, beamEmbed v⟫_ℝ)
    {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ t, HasDerivAt f (f1 t) t) (hd1 : ∀ t, HasDerivAt f1 (f2 t) t) :
    ∫ t, (beamSnd p : ℝ → ℝ) t * f2 t ∂unitIocMeasure =
      ∫ t, ((beamOperator x : BeamL2) : ℝ → ℝ) t * f t ∂unitIocMeasure := by
  set v : BeamV := ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (contToLp f hf, contToLp f2 hf2),
    contPair_mem hf hf1 hf2 hd hd1⟩ with hvdef
  have hvfst : beamEmbed v = contToLp f hf := by
    rw [show beamEmbed v = pairFst ((v : BeamV) : BeamPairSpace) from rfl,
      hvdef, Scalar.pairFst_apply]
    simp
  have hvsnd : beamSnd v = contToLp f2 hf2 := by
    rw [show beamSnd v = pairSnd ((v : BeamV) : BeamPairSpace) from rfl,
      hvdef, Scalar.pairSnd_apply]
    simp
  have hid := hpair v
  rw [hvfst, hvsnd] at hid
  have hL : ⟪beamSnd p, contToLp f2 hf2⟫_ℝ =
      ∫ t, (beamSnd p : ℝ → ℝ) t * f2 t ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp f2 hf2] with t ht
    rw [RCLike.inner_apply, ht]
    simp only [starRingEnd_apply, star_trivial]
    exact mul_comm _ _
  have hR : ⟪(beamOperator x : BeamL2), contToLp f hf⟫_ℝ =
      ∫ t, ((beamOperator x : BeamL2) : ℝ → ℝ) t * f t ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp f hf] with t ht
    rw [RCLike.inner_apply, ht]
    simp only [starRingEnd_apply, star_trivial]
    exact mul_comm _ _
  rwa [hL, hR] at hid

/-- A classical representative of a graph point of the real beam operator. -/
structure ClassicalFreeBeamRepresentative (x y : BeamL2) where
  /-- A classical function representing the first component of the beam graph point. -/
  u0 : ℝ → ℝ
  /-- The first derivative in the classical representative's derivative chain. -/
  u1 : ℝ → ℝ
  /-- The second derivative in the classical representative's derivative chain. -/
  u2 : ℝ → ℝ
  /-- The third derivative in the classical representative's derivative chain. -/
  u3 : ℝ → ℝ
  /-- The fourth derivative representing the beam operator's value. -/
  u4 : ℝ → ℝ
  x_ae : (x : ℝ → ℝ) =ᵐ[unitIocMeasure] u0
  y_ae : (y : ℝ → ℝ) =ᵐ[unitIocMeasure] u4
  u0_continuous : Continuous u0
  u2_continuous : Continuous u2
  u4_continuous : Continuous u4
  deriv0 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt u0 (u1 t) (Set.Icc 0 1) t
  deriv1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt u1 (u2 t) (Set.Icc 0 1) t
  deriv2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt u2 (u3 t) (Set.Icc 0 1) t
  deriv3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt u3 (u4 t) (Set.Icc 0 1) t
  second_left : u2 0 = 0
  third_left : u3 0 = 0
  second_right : u2 1 = 0
  third_right : u3 1 = 0

/-- The graph of the classical real free-beam fourth derivative: a pair `(u, f)` belongs
when `u` has a classical fourth-derivative representative on `[0,1]`, that fourth derivative
represents `f`, and the four free-end traces vanish. -/
def classicalFreeBeamGraph : Set (BeamL2 × BeamL2) :=
  {z | Nonempty (ClassicalFreeBeamRepresentative z.1 z.2)}

/-- Green's identity for two classical free-beam representatives.  The derivative chains are
only required within `[0,1]`; the four endpoint terms vanish by the free-end conditions. -/
private theorem green_identity_of_classicalFreeBeamRepresentatives
    {x y x' y' : BeamL2}
    (U : ClassicalFreeBeamRepresentative x y)
    (V : ClassicalFreeBeamRepresentative x' y') :
    ∫ t in (0 : ℝ)..1, V.u0 t * U.u4 t =
      ∫ t in (0 : ℝ)..1, U.u0 t * V.u4 t := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hU1 : ContinuousOn U.u1 (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (U.deriv1 t ht).continuousWithinAt
  have hU3 : ContinuousOn U.u3 (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (U.deriv3 t ht).continuousWithinAt
  have hV1 : ContinuousOn V.u1 (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (V.deriv1 t ht).continuousWithinAt
  have hV3 : ContinuousOn V.u3 (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (V.deriv3 t ht).continuousWithinAt
  have hU1u : ContinuousOn U.u1 (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hU1
  have hU3u : ContinuousOn U.u3 (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hU3
  have hV1u : ContinuousOn V.u1 (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hV1
  have hV3u : ContinuousOn V.u3 (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hV3
  have hDerivAt
      {f f' : ℝ → ℝ}
      (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt f (f' t) (Set.Icc 0 1) t) :
      ∀ t ∈ Set.uIoo (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    rw [Set.uIoo_of_le h01] at ht
    exact (h t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have h1 : ∫ t in (0 : ℝ)..1, V.u0 t * U.u4 t =
      V.u0 1 * U.u3 1 - V.u0 0 * U.u3 0 -
        ∫ t in (0 : ℝ)..1, V.u1 t * U.u3 t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      V.u0_continuous.continuousOn hU3u
      (hDerivAt V.deriv0) (hDerivAt U.deriv3)
      hV1u.intervalIntegrable (U.u4_continuous.intervalIntegrable 0 1)
  have h2 : ∫ t in (0 : ℝ)..1, V.u1 t * U.u3 t =
      V.u1 1 * U.u2 1 - V.u1 0 * U.u2 0 -
        ∫ t in (0 : ℝ)..1, V.u2 t * U.u2 t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hV1u U.u2_continuous.continuousOn
      (hDerivAt V.deriv1) (hDerivAt U.deriv2)
      (V.u2_continuous.intervalIntegrable 0 1) hU3u.intervalIntegrable
  have h3 : ∫ t in (0 : ℝ)..1, V.u2 t * U.u2 t =
      V.u2 1 * U.u1 1 - V.u2 0 * U.u1 0 -
        ∫ t in (0 : ℝ)..1, V.u3 t * U.u1 t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      V.u2_continuous.continuousOn hU1u
      (hDerivAt V.deriv2) (hDerivAt U.deriv1)
      hV3u.intervalIntegrable (U.u2_continuous.intervalIntegrable 0 1)
  have h4 : ∫ t in (0 : ℝ)..1, V.u3 t * U.u1 t =
      V.u3 1 * U.u0 1 - V.u3 0 * U.u0 0 -
        ∫ t in (0 : ℝ)..1, V.u4 t * U.u0 t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hV3u U.u0_continuous.continuousOn
      (hDerivAt V.deriv3) (hDerivAt U.deriv0)
      (V.u4_continuous.intervalIntegrable 0 1) hU1u.intervalIntegrable
  calc
    ∫ t in (0 : ℝ)..1, V.u0 t * U.u4 t
        = -(∫ t in (0 : ℝ)..1, V.u1 t * U.u3 t) := by
          rw [h1, U.third_right, U.third_left]
          ring
    _ = ∫ t in (0 : ℝ)..1, V.u2 t * U.u2 t := by
          rw [h2, U.second_right, U.second_left]
          ring
    _ = -(∫ t in (0 : ℝ)..1, V.u3 t * U.u1 t) := by
          rw [h3, V.second_right, V.second_left]
          ring
    _ = ∫ t in (0 : ℝ)..1, V.u4 t * U.u0 t := by
          rw [h4, V.third_right, V.third_left]
          ring
    _ = ∫ t in (0 : ℝ)..1, U.u0 t * V.u4 t := by
          congr 1 with t
          ring

/-- Green's identity written on the ambient `L²` representatives. -/
private theorem inner_eq_of_classicalFreeBeamRepresentatives
    {x y x' y' : BeamL2}
    (U : ClassicalFreeBeamRepresentative x y)
    (V : ClassicalFreeBeamRepresentative x' y') :
    ⟪y, x'⟫_ℝ = ⟪x, y'⟫_ℝ := by
  have hgreen := green_identity_of_classicalFreeBeamRepresentatives U V
  have hL : ⟪y, x'⟫_ℝ =
      ∫ t, V.u0 t * U.u4 t ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [U.y_ae, V.x_ae] with t hy hx
    rw [RCLike.inner_apply, hy, hx]
    simp only [starRingEnd_apply, star_trivial]
  have hR : ⟪x, y'⟫_ℝ =
      ∫ t, U.u0 t * V.u4 t ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [U.x_ae, V.y_ae] with t hx hy
    rw [RCLike.inner_apply, hx, hy]
    simp only [starRingEnd_apply, star_trivial]
    exact mul_comm _ _
  rw [hL, hR, integral_unitIocMeasure_eq_intervalIntegral,
    integral_unitIocMeasure_eq_intervalIntegral]
  exact hgreen

/-- Cubic test function used to isolate the four endpoint traces. -/
private def cubic (c0 c1 c2 c3 t : ℝ) : ℝ := c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3
private def cubicD1 (_c0 c1 c2 c3 t : ℝ) : ℝ := c1 + 2 * c2 * t + 3 * c3 * t ^ 2
private def cubicD2 (_c0 _c1 c2 c3 t : ℝ) : ℝ := 2 * c2 + 6 * c3 * t

private theorem continuous_cubic (c0 c1 c2 c3 : ℝ) : Continuous (cubic c0 c1 c2 c3) := by
  unfold cubic
  fun_prop
private theorem continuous_cubicD1 (_c0 c1 c2 c3 : ℝ) : Continuous (cubicD1 _c0 c1 c2 c3) := by
  unfold cubicD1
  fun_prop
private theorem continuous_cubicD2 (_c0 _c1 c2 c3 : ℝ) : Continuous (cubicD2 _c0 _c1 c2 c3) := by
  unfold cubicD2
  fun_prop
private theorem hasDerivAt_cubic (c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3 t) t := by
  have h := (((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
    ((hasDerivAt_pow 2 t).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)
  refine h.congr_deriv ?_
  unfold cubicD1
  ring
private theorem hasDerivAt_cubicD1 (_c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubicD1 _c0 c1 c2 c3) (cubicD2 _c0 0 c2 c3 t) t := by
  have h := ((hasDerivAt_const t c1).add
    ((hasDerivAt_id t).const_mul (2 * c2))).add
    ((hasDerivAt_pow 2 t).const_mul (3 * c3))
  refine h.congr_deriv ?_
  unfold cubicD2
  ring

/-- The classical boundary form vanishes for a graph point whose action has a continuous
representative. -/
private theorem boundary_form_eq_zero {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV,
      ⟪beamSnd p, beamSnd v⟫_ℝ = ⟪beamOperator x, beamEmbed v⟫_ℝ)
    {u2 u3 u4 : ℝ → ℝ}
    (hu2ae : (beamSnd p : ℝ → ℝ) =ᵐ[unitIocMeasure] u2)
    (hu4ae : ((beamOperator x : BeamL2) : ℝ → ℝ) =ᵐ[unitIocMeasure] u4)
    (hu4cont : Continuous u4)
    (hu2cont : Continuous u2)
    (hu2' : ∀ t, HasDerivAt u2 (u3 t) t)
    (hu3cont : ContinuousOn u3 (Set.Icc 0 1))
    (hu3' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 (u4 t) (Set.Icc 0 1) t)
    (q q1 q2 : ℝ → ℝ)
    (hq : Continuous q) (hq1 : Continuous q1) (hq2 : Continuous q2)
    (hdq : ∀ t, HasDerivAt q (q1 t) t)
    (hdq1 : ∀ t, HasDerivAt q1 (q2 t) t) :
    u2 1 * q1 1 - u2 0 * q1 0 - (u3 1 * q 1 - u3 0 * q 0) = 0 := by
  have hbridge : ∀ f : ℝ → ℝ,
      ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
    intro f
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure_def]
  have hInt := beam_pairing_integral hpair hq hq1 hq2 hdq hdq1
  have hIntBar : ∫ t in (0 : ℝ)..1, u2 t * q2 t =
      ∫ t in (0 : ℝ)..1, u4 t * q t := by
    rw [← hbridge, ← hbridge]
    rw [show ∫ t, u2 t * q2 t ∂unitIocMeasure =
        ∫ t, (beamSnd p : ℝ → ℝ) t * q2 t ∂unitIocMeasure from
      integral_congr_ae (by filter_upwards [hu2ae] with t ht; rw [ht])]
    rw [show ∫ t, u4 t * q t ∂unitIocMeasure =
        ∫ t, ((beamOperator x : BeamL2) : ℝ → ℝ) t * q t ∂unitIocMeasure from
      integral_congr_ae (by filter_upwards [hu4ae] with t ht; rw [ht])]
    exact hInt
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hu3u : ContinuousOn u3 (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hu3cont
  have hu3At : ∀ t ∈ Set.uIoo (0 : ℝ) 1, HasDerivAt u3 (u4 t) t := by
    intro t ht
    rw [Set.uIoo_of_le h01] at ht
    exact (hu3' t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hIBP1 : ∫ t in (0 : ℝ)..1, u2 t * q2 t =
      u2 1 * q1 1 - u2 0 * q1 0 - ∫ t in (0 : ℝ)..1, u3 t * q1 t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu2cont.continuousOn hq1.continuousOn (fun t _ => hu2' t)
      (fun t _ => hdq1 t) hu3u.intervalIntegrable (hq2.intervalIntegrable 0 1)
  have hIBP2 : ∫ t in (0 : ℝ)..1, u3 t * q1 t =
      u3 1 * q 1 - u3 0 * q 0 - ∫ t in (0 : ℝ)..1, u4 t * q t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu3u hq.continuousOn hu3At (fun t _ => hdq t)
      (hu4cont.intervalIntegrable 0 1) (hq1.intervalIntegrable 0 1)
  rw [hIBP1, hIBP2] at hIntBar
  linarith

/-- **Classical regularity for a beam graph point with continuous forcing.**  If the value
`B x` has a continuous representative `u4`, then `x` has a four-derivative classical
representative on `[0,1]`, `u'''' = u4`, and all four free-end traces vanish. -/
theorem exists_classicalFreeBeamRepresentative_of_continuous_apply
    (x : beamOperator.domain) {u4 : ℝ → ℝ}
    (hu4cont : Continuous u4)
    (hu4ae : ((beamOperator x : BeamL2) : ℝ → ℝ) =ᵐ[unitIocMeasure] u4) :
    Nonempty (ClassicalFreeBeamRepresentative (x : BeamL2)
      (beamOperator x : BeamL2)) := by
  classical
  obtain ⟨p, hembed, hpair⟩ := exists_form_representative_of_beam_apply x
  set xfn : ℝ → ℝ := ((x : BeamL2) : ℝ → ℝ) with hxfn
  set wfn : ℝ → ℝ := ((beamSnd p : BeamL2) : ℝ → ℝ) with hwfn
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, xfn =ᵐ[unitIocMeasure]
      fun t => a + b * t + secondPrimitive wfn t := by
    obtain ⟨a, b, h⟩ := beamV_repr p
    rw [hembed] at h
    exact ⟨a, b, h⟩
  have hw2 : ∀ k : ℕ,
      ∫ t, wfn t * intervalBumpD2 k t ∂unitIocMeasure =
        ∫ t, u4 t * intervalBump k t ∂unitIocMeasure := by
    intro k
    have h := beam_pairing_integral hpair (continuous_intervalBump k)
      (continuous_intervalBumpD1 k) (continuous_intervalBumpD2 k)
      (hasDerivAt_intervalBump k) (hasDerivAt_intervalBumpD1 k)
    rw [show ∫ t, ((beamOperator x : BeamL2) : ℝ → ℝ) t *
        intervalBump k t ∂unitIocMeasure =
      ∫ t, u4 t * intervalBump k t ∂unitIocMeasure from
        integral_congr_ae (by filter_upwards [hu4ae] with t ht; rw [ht])] at h
    exact h
  set yfn : ℝ → ℝ := ((beamOperator x : BeamL2) : ℝ → ℝ) with hyfn
  have hw2y : ∀ k : ℕ,
      ∫ t, wfn t * intervalBumpD2 k t ∂unitIocMeasure =
        ∫ t, yfn t * intervalBump k t ∂unitIocMeasure := by
    intro k
    rw [hw2 k]
    exact integral_congr_ae (by
      filter_upwards [hu4ae] with t ht
      rw [ht])
  obtain ⟨c, d, hcd⟩ := eq_affine_add_secondPrimitive_of_forall_integral_bumpD2
    (Lp.memLp _) (Lp.memLp _) hw2y
  have hKyu4 : secondPrimitive yfn = secondPrimitive u4 :=
    secondPrimitive_congr_ae (by simpa [yfn] using hu4ae)
  set u0 : ℝ → ℝ := fun t => a + b * t + secondPrimitive wfn t with hu0
  set u2 : ℝ → ℝ := fun t => c + d * t + secondPrimitive u4 t with hu2
  have hxuae : xfn =ᵐ[unitIocMeasure] u0 := hab
  have hwu2ae : wfn =ᵐ[unitIocMeasure] u2 := by
    refine hcd.trans (Filter.Eventually.of_forall fun t => ?_)
    change c + d * t + secondPrimitive yfn t = c + d * t + secondPrimitive u4 t
    rw [congrFun hKyu4 t]
  have hKw : secondPrimitive wfn = secondPrimitive u2 := secondPrimitive_congr_ae hwu2ae
  have hwint : Integrable wfn unitIocMeasure := integrable_coeFn _
  have hKcont : Continuous (secondPrimitive wfn) := continuous_secondPrimitive hwint
  have hu0cont : Continuous u0 := by
    rw [hu0]
    exact (continuous_const.add (continuous_const.mul continuous_id)).add hKcont
  have hu4int : Integrable u4 unitIocMeasure := integrable_unitIocMeasure_of_continuous hu4cont
  have hu2cont : Continuous u2 := by
    rw [hu2]
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_secondPrimitive hu4int)
  have hu2int : Integrable u2 unitIocMeasure := integrable_unitIocMeasure_of_continuous hu2cont
  set u1 : ℝ → ℝ := fun t => b + firstPrimitive u2 t with hu1
  set u3 : ℝ → ℝ := fun t => d + firstPrimitive u4 t with hu3
  have hu0eq : u0 = fun t : ℝ => a + b * t + secondPrimitive u2 t := by
    funext t
    change a + b * t + secondPrimitive wfn t = a + b * t + secondPrimitive u2 t
    rw [congrFun hKw t]
  have hd0at : ∀ t, HasDerivAt u0 (u1 t) t := by
    intro t
    rw [hu0eq]
    have h := ((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).add
      (hasDerivAt_secondPrimitive hu2int t)
    refine h.congr_deriv ?_
    simp only [hu1]
    ring
  have hd1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u1 (u2 t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu1]
    exact (hasDerivWithinAt_firstPrimitive_of_continuous hu2cont ht).const_add b
  have hd2at : ∀ t, HasDerivAt u2 (u3 t) t := by
    intro t
    rw [hu2]
    have h := ((hasDerivAt_const t c).add ((hasDerivAt_id t).const_mul d)).add
      (hasDerivAt_secondPrimitive hu4int t)
    refine h.congr_deriv ?_
    simp only [hu3]
    ring
  have hd3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 (u4 t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu3]
    exact (hasDerivWithinAt_firstPrimitive_of_continuous hu4cont ht).const_add d
  have hu3cont : ContinuousOn u3 (Set.Icc 0 1) :=
    fun t ht => (hd3 t ht).continuousWithinAt
  have hB := fun (c0 c1 c2 c3 : ℝ) => boundary_form_eq_zero hpair hwu2ae hu4ae hu4cont
    hu2cont hd2at hu3cont hd3
    (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3) (cubicD2 c0 c1 c2 c3)
    (continuous_cubic _ _ _ _) (continuous_cubicD1 _ _ _ _) (continuous_cubicD2 _ _ _ _)
    (hasDerivAt_cubic _ _ _ _) (hasDerivAt_cubicD1 _ _ _ _)
  have hu30 : u3 0 = 0 := by
    have h := hB 1 0 (-3) 2
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu20 : u2 0 = 0 := by
    have h := hB 0 1 (-2) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu31 : u3 1 = 0 := by
    have h := hB 0 0 3 (-2)
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu21 : u2 1 = 0 := by
    have h := hB 0 0 (-1) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  exact ⟨{
    u0 := u0
    u1 := u1
    u2 := u2
    u3 := u3
    u4 := u4
    x_ae := hxuae
    y_ae := hu4ae
    u0_continuous := hu0cont
    u2_continuous := hu2cont
    u4_continuous := hu4cont
    deriv0 := fun t ht => (hd0at t).hasDerivWithinAt
    deriv1 := hd1
    deriv2 := fun t ht => (hd2at t).hasDerivWithinAt
    deriv3 := hd3
    second_left := hu20
    third_left := hu30
    second_right := hu21
    third_right := hu31 }⟩

/-! ## A classical graph core and closure identification -/

/-- The bounded-continuous forcing vectors used to build the classical core. -/
def continuousForcing : Set BeamL2 := Lp.boundedContinuousFunction ℝ 2 unitIocMeasure

/-- Parameterization of the beam graph by the shifted forcing `g = (B+1)u`. -/
def beamGraphParam : BeamL2 →L[ℝ] (BeamL2 × BeamL2) :=
  beamCoerciveFormData.resolvent.prod
    ((ContinuousLinearMap.id ℝ BeamL2) - beamCoerciveFormData.resolvent)

/-- Evaluating the graph parametrization of the beam trial subspace. -/
@[simp] theorem beamGraphParam_apply (g : BeamL2) :
    beamGraphParam g =
      (beamCoerciveFormData.resolvent g, g - beamCoerciveFormData.resolvent g) := rfl

/-- The graph points generated by continuous shifted forcing form a classical free-beam
fourth-derivative core. -/
def classicalFreeBeamCoreGraph : Set (BeamL2 × BeamL2) :=
  beamGraphParam '' continuousForcing

/-- Every point of the continuous-forcing core is a graph point of `beamOperator`. -/
theorem classicalFreeBeamCoreGraph_subset_graph :
    classicalFreeBeamCoreGraph ⊆ (beamOperator.graph : Set (BeamL2 × BeamL2)) := by
  rintro z ⟨g, hg, rfl⟩
  have hmem : beamCoerciveFormData.resolvent g ∈ beamOperator.domain :=
    LinearMap.mem_range_self _ g
  have hshift := Abstract.inversePartialMap_apply_R beamCoerciveFormData.resolvent
    beamCoerciveFormData.resolvent_isSelfAdjoint beamCoerciveFormData.resolvent_injective g
  have hsub : (⟨beamCoerciveFormData.resolvent g, LinearMap.mem_range_self _ g⟩ :
      beamShiftedFormData.shiftedOperator.domain) =
      ⟨beamCoerciveFormData.resolvent g, hmem⟩ := Subtype.ext rfl
  have hshift' : beamShiftedFormData.shiftedOperator
      ⟨beamCoerciveFormData.resolvent g, hmem⟩ = g := by
    rw [← hsub]
    exact hshift
  have hsum := shifted_apply_of_beam
    (x := ⟨beamCoerciveFormData.resolvent g, hmem⟩)
  have hadd : beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ +
      beamCoerciveFormData.resolvent g = g := by
    calc
      beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ +
          beamCoerciveFormData.resolvent g =
          beamShiftedFormData.shiftedOperator
            ⟨beamCoerciveFormData.resolvent g, hmem⟩ := hsum.symm
      _ = g := hshift'
  have hB : beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ =
      g - beamCoerciveFormData.resolvent g :=
    eq_sub_of_add_eq hadd
  change beamGraphParam g ∈ beamOperator.graph
  exact (LinearPMap.mem_graph_iff beamOperator).2
    ⟨⟨beamCoerciveFormData.resolvent g, hmem⟩, rfl, hB⟩

/-- Each graph point in the continuous-forcing core has a genuine classical fourth-derivative
representative with the four printed free-end boundary conditions. -/
theorem classicalFreeBeamCoreGraph_has_classical_representative
    {z : BeamL2 × BeamL2} (hz : z ∈ classicalFreeBeamCoreGraph) :
    ∃ h : z.1 ∈ beamOperator.domain,
      beamOperator ⟨z.1, h⟩ = z.2 ∧
      Nonempty (ClassicalFreeBeamRepresentative z.1 z.2) := by
  rcases hz with ⟨g, hg, rfl⟩
  obtain ⟨gbar, hgbar⟩ := Lp.mem_boundedContinuousFunction_iff.mp hg
  have hgae : (g : ℝ → ℝ) =ᵐ[unitIocMeasure] gbar := by
    have h := ContinuousMap.coeFn_toAEEqFun unitIocMeasure gbar.toContinuousMap
    rw [hgbar] at h
    exact h
  have hmem : beamCoerciveFormData.resolvent g ∈ beamOperator.domain :=
    LinearMap.mem_range_self _ g
  have hshift := Abstract.inversePartialMap_apply_R beamCoerciveFormData.resolvent
    beamCoerciveFormData.resolvent_isSelfAdjoint beamCoerciveFormData.resolvent_injective g
  have hsub : (⟨beamCoerciveFormData.resolvent g, LinearMap.mem_range_self _ g⟩ :
      beamShiftedFormData.shiftedOperator.domain) =
      ⟨beamCoerciveFormData.resolvent g, hmem⟩ := Subtype.ext rfl
  have hshift' : beamShiftedFormData.shiftedOperator
      ⟨beamCoerciveFormData.resolvent g, hmem⟩ = g := by
    rw [← hsub]
    exact hshift
  have hsum := shifted_apply_of_beam
    (x := ⟨beamCoerciveFormData.resolvent g, hmem⟩)
  have hadd : beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ +
      beamCoerciveFormData.resolvent g = g := by
    calc
      beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ +
          beamCoerciveFormData.resolvent g =
          beamShiftedFormData.shiftedOperator
            ⟨beamCoerciveFormData.resolvent g, hmem⟩ := hsum.symm
      _ = g := hshift'
  have hB : beamOperator ⟨beamCoerciveFormData.resolvent g, hmem⟩ =
      g - beamCoerciveFormData.resolvent g :=
    eq_sub_of_add_eq hadd
  obtain ⟨p, hembed, -⟩ := exists_form_representative_of_beam_apply
    ⟨beamCoerciveFormData.resolvent g, hmem⟩
  obtain ⟨a, b, hab⟩ := beamV_repr p
  have hKa : Continuous (secondPrimitive ((beamSnd p : BeamL2) : ℝ → ℝ)) :=
    continuous_secondPrimitive (integrable_coeFn _)
  set ubar : ℝ → ℝ := fun t => a + b * t +
    secondPrimitive ((beamSnd p : BeamL2) : ℝ → ℝ) t with hubar
  have hucont : Continuous ubar := by
    rw [hubar]
    exact (continuous_const.add (continuous_const.mul continuous_id)).add hKa
  have hRae : (beamCoerciveFormData.resolvent g : ℝ → ℝ) =ᵐ[unitIocMeasure] ubar := by
    rw [hembed] at hab
    exact hab
  set ybar : ℝ → ℝ := fun t => gbar t - ubar t with hybar
  have hycont : Continuous ybar := by
    rw [hybar]
    exact gbar.continuous.sub hucont
  have hyae : ((g - beamCoerciveFormData.resolvent g : BeamL2) : ℝ → ℝ) =ᵐ[unitIocMeasure] ybar := by
    filter_upwards [Lp.coeFn_sub g (beamCoerciveFormData.resolvent g), hgae, hRae] with
      t hsub hga hRa
    rw [hsub]
    change (g : ℝ → ℝ) t - (beamCoerciveFormData.resolvent g : ℝ → ℝ) t = ybar t
    rw [hga, hRa, hybar]
  obtain ⟨hrep⟩ := exists_classicalFreeBeamRepresentative_of_continuous_apply
    ⟨beamCoerciveFormData.resolvent g, hmem⟩ hycont (by rw [hB]; exact hyae)
  have hrep' : ClassicalFreeBeamRepresentative
      (beamCoerciveFormData.resolvent g)
      (g - beamCoerciveFormData.resolvent g) := by
    rw [← hB]
    exact hrep
  refine ⟨?_, ?_, ?_⟩
  · simpa [beamGraphParam_apply] using hmem
  · simpa [beamGraphParam_apply] using hB
  · simpa [beamGraphParam_apply] using (show Nonempty (ClassicalFreeBeamRepresentative
      (beamCoerciveFormData.resolvent g)
      (g - beamCoerciveFormData.resolvent g)) from ⟨hrep'⟩)

/-- Every point of the continuous-forcing core belongs to the full classical free-beam
fourth-derivative graph. -/
theorem classicalFreeBeamCoreGraph_subset_classicalFreeBeamGraph :
    classicalFreeBeamCoreGraph ⊆ classicalFreeBeamGraph := by
  intro z hz
  obtain ⟨-, -, ⟨hrep⟩⟩ := classicalFreeBeamCoreGraph_has_classical_representative hz
  exact ⟨hrep⟩

/-- The continuous-forcing classical graph core is dense in the full graph of the real beam
operator. -/
theorem closure_classicalFreeBeamCoreGraph_eq_graph :
    closure classicalFreeBeamCoreGraph =
      (beamOperator.graph : Set (BeamL2 × BeamL2)) := by
  apply Set.Subset.antisymm
  · exact (beamOperator_isSelfAdjoint.isClosed.closure_subset_iff.mpr
      classicalFreeBeamCoreGraph_subset_graph)
  · intro z hz
    obtain ⟨x, hx, hBx⟩ := (LinearPMap.mem_graph_iff beamOperator).1 hz
    let xb : beamOperator.domain := x
    have hBxb : beamOperator xb = z.2 := by
      change beamOperator x = z.2
      exact hBx
    have hxb : (xb : BeamL2) = z.1 := by
      change (x : BeamL2) = z.1
      exact hx
    set g : BeamL2 := z.2 + z.1 with hgdef
    have hparam : beamGraphParam g = z := by
      have hR : beamCoerciveFormData.resolvent g = z.1 := by
        have hshift : beamShiftedFormData.shiftedOperator xb = g := by
          calc
            beamShiftedFormData.shiftedOperator xb =
                beamOperator xb + (xb : BeamL2) := shifted_apply_of_beam
            _ = z.2 + z.1 := by rw [hBxb, hxb]
            _ = g := hgdef.symm
        have hRinv :
            beamCoerciveFormData.resolvent
                (beamShiftedFormData.shiftedOperator xb) = (xb : BeamL2) := by
          exact Abstract.R_inversePartialMap_apply beamCoerciveFormData.resolvent
            beamCoerciveFormData.resolvent_isSelfAdjoint beamCoerciveFormData.resolvent_injective xb
        calc
          beamCoerciveFormData.resolvent g =
              beamCoerciveFormData.resolvent
                (beamShiftedFormData.shiftedOperator xb) :=
            congrArg beamCoerciveFormData.resolvent hshift.symm
          _ = (xb : BeamL2) := hRinv
          _ = z.1 := hxb
      rw [beamGraphParam_apply, hR, hgdef]
      ext <;> simp
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδ : 0 < ε / (‖beamGraphParam‖ + 1) := by
      positivity
    have hgcl : g ∈ closure continuousForcing :=
      (Lp.boundedContinuousFunction_dense ℝ unitIocMeasure
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) g
    rw [Metric.mem_closure_iff] at hgcl
    obtain ⟨g', hg', hdist⟩ := hgcl (ε / (‖beamGraphParam‖ + 1)) hδ
    refine ⟨beamGraphParam g', ⟨g', hg', rfl⟩, ?_⟩
    rw [← hparam, dist_eq_norm, ← map_sub]
    have hdist' : ‖g - g'‖ < ε / (‖beamGraphParam‖ + 1) := by
      rw [← dist_eq_norm]
      exact hdist
    calc
      ‖beamGraphParam (g - g')‖ ≤ ‖beamGraphParam‖ * ‖g - g'‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖beamGraphParam‖ + 1) * ‖g - g'‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg beamGraphParam])
          (norm_nonneg _)
      _ < (‖beamGraphParam‖ + 1) * (ε / (‖beamGraphParam‖ + 1)) := by
        exact mul_lt_mul_of_pos_left hdist' (by positivity)
      _ = ε := by
        field_simp

/-- Every classical free-end fourth-derivative graph point belongs to the form realization.
The proof uses Green's identity on the graph-dense classical core and self-adjoint maximality:
the classical pair defines an adjoint-domain vector, and self-adjointness identifies it with the
beam operator itself. -/
theorem classicalFreeBeamGraph_subset_graph :
    classicalFreeBeamGraph ⊆
      (beamOperator.graph : Set (BeamL2 × BeamL2)) := by
  intro z hz
  rcases hz with ⟨hrep⟩
  let S : Set (BeamL2 × BeamL2) :=
    {q | ⟪z.2, q.1⟫_ℝ = ⟪z.1, q.2⟫_ℝ}
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
  have hcore : classicalFreeBeamCoreGraph ⊆ S := by
    intro q hq
    obtain ⟨-, -, ⟨hqrep⟩⟩ := classicalFreeBeamCoreGraph_has_classical_representative hq
    exact inner_eq_of_classicalFreeBeamRepresentatives hrep hqrep
  have hclosure : closure classicalFreeBeamCoreGraph ⊆ S :=
    hSclosed.closure_subset_iff.mpr hcore
  have hgraph : (beamOperator.graph : Set (BeamL2 × BeamL2)) ⊆ S := by
    rwa [closure_classicalFreeBeamCoreGraph_eq_graph] at hclosure
  have hEq : ∀ v : beamOperator.domain,
      ⟪z.2, (v : BeamL2)⟫_ℝ =
        ⟪z.1, beamOperator v⟫_ℝ := by
    intro v
    have hv := hgraph (beamOperator.mem_graph v)
    simpa [S] using hv
  have hmemAdj : z.1 ∈ beamOperator.adjoint.domain :=
    _root_.LinearPMap.mem_adjoint_domain_of_exists _ ⟨z.2, hEq⟩
  have hsa := (LinearPMap.isSelfAdjoint_def.mp beamOperator_isSelfAdjoint)
  have hmem : z.1 ∈ beamOperator.domain := by
    have hmem' := hmemAdj
    rw [hsa] at hmem'
    exact hmem'
  have hadj : beamOperator.adjoint ⟨z.1, hmemAdj⟩ = z.2 :=
    _root_.LinearPMap.adjoint_apply_eq beamOperator_isSelfAdjoint.dense_domain
      ⟨z.1, hmemAdj⟩ hEq
  have hB : beamOperator ⟨z.1, hmem⟩ = z.2 := by
    have htrans := (_root_.LinearPMap.ext_iff.mp hsa).2
      (x := z.1) (hf := hmemAdj) (hg := hmem)
    rw [← htrans, hadj]
  have hm := beamOperator.mem_graph ⟨z.1, hmem⟩
  simpa [hB] using hm

/-- The full classical free-end fourth-derivative graph is a core for the real form
realization.  This is the source-level closure statement: the closure of the operator acting by
`D⁴u` on functions satisfying the four printed free-end boundary conditions is exactly the
self-adjoint beam operator. -/
theorem closure_classicalFreeBeamGraph_eq_graph :
    closure classicalFreeBeamGraph =
      (beamOperator.graph : Set (BeamL2 × BeamL2)) := by
  apply Set.Subset.antisymm
  · exact (beamOperator_isSelfAdjoint.isClosed.closure_subset_iff.mpr
      classicalFreeBeamGraph_subset_graph)
  · rw [← closure_classicalFreeBeamCoreGraph_eq_graph]
    exact closure_mono classicalFreeBeamCoreGraph_subset_classicalFreeBeamGraph

/-- The real form realization is the self-adjoint closure of the classical free-end
fourth-derivative operator appearing in Davis--Kahan Section 9. -/
theorem beamOperator_is_closure_of_classical_freeBeam_fourthDerivative :
    _root_.IsSelfAdjoint beamOperator ∧
      closure classicalFreeBeamGraph =
        (beamOperator.graph : Set (BeamL2 × BeamL2)) :=
  ⟨beamOperator_isSelfAdjoint, closure_classicalFreeBeamGraph_eq_graph⟩

/-! ## Characteristic roots produce operator eigenpairs -/

/-- The `L²(0,1)` class of a classical free-beam mode. -/
def classicalModeLp (beta a b c d : ℝ) : BeamL2 :=
  contToLp (mode beta a b c d) (continuous_mode beta a b c d)

/-- The `L²` representative of `classicalModeLp` is the classical mode almost everywhere. -/
theorem coeFn_classicalModeLp (beta a b c d : ℝ) :
    (classicalModeLp beta a b c d : ℝ → ℝ) =ᵐ[unitIocMeasure]
      mode beta a b c d :=
  coeFn_contToLp (mode beta a b c d) (continuous_mode beta a b c d)

private theorem exists_Ioo_ne_zero_of_continuous_of_ne_zero_at_zero
    {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 ≠ 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, f t ≠ 0 := by
  have hclosed : IsClosed {t : ℝ | f t = 0} :=
    isClosed_eq hf continuous_const
  have hopen : IsOpen {t : ℝ | f t ≠ 0} := by
    have hset : {t : ℝ | f t ≠ 0} = ({t : ℝ | f t = 0})ᶜ := by
      ext t
      simp
    rw [hset]
    exact hclosed.isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen 0 h0
  let t : ℝ := min (ε / 2) (1 / 2)
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min (by linarith) (by norm_num)
  have htone : t < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨t, ⟨htpos, htone⟩, hball htball⟩

/-- A positive-frequency identified mode with nontrivial reduced coefficients is nonzero in
`L²(0,1)`. -/
theorem classicalModeLp_ne_zero_of_identified_coefficients
    {beta a b : ℝ} (hbeta : 0 < beta) (hab : a ≠ 0 ∨ b ≠ 0) :
    classicalModeLp beta a b a b ≠ 0 := by
  have hpoint : ∃ t ∈ Set.Ioo (0 : ℝ) 1, mode beta a b a b t ≠ 0 := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        rcases hab with ha' | hb
        · exact False.elim (ha' ha)
        · exact hb
      let t : ℝ := 1 / (beta + 1)
      let z : ℝ := beta / (beta + 1)
      have hden : 0 < beta + 1 := by linarith
      have htpos : 0 < t := by
        dsimp [t]
        positivity
      have htone : t < 1 := by
        dsimp [t]
        exact (div_lt_one hden).2 (by linarith)
      have hzt : beta * t = z := by
        simp [t, z, div_eq_mul_inv]
      have hzpos : 0 < z := by
        dsimp [z]
        exact div_pos hbeta hden
      have hzone : z < 1 := by
        dsimp [z]
        exact (div_lt_one hden).2 (by linarith)
      have honepi : (1 : ℝ) < Real.pi :=
        lt_trans (by norm_num) Real.pi_gt_three
      have hsin : 0 < Real.sin z :=
        Real.sin_pos_of_pos_of_lt_pi hzpos (lt_trans hzone honepi)
      have hsinh : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hzpos
      have hmode : mode beta a b a b t = b * (Real.sin z + Real.sinh z) := by
        unfold mode
        rw [ha, hzt]
        ring
      refine ⟨t, ⟨htpos, htone⟩, ?_⟩
      rw [hmode]
      exact mul_ne_zero hb (ne_of_gt (add_pos hsin hsinh))
    · have hzero : mode beta a b a b 0 = 2 * a := by
        rw [mode_eval_zero]
        ring
      have hzero_ne : mode beta a b a b 0 ≠ 0 := by
        rw [hzero]
        exact mul_ne_zero (by norm_num) ha
      exact exists_Ioo_ne_zero_of_continuous_of_ne_zero_at_zero
        (continuous_mode beta a b a b) hzero_ne
  obtain ⟨t, ht, hmode_ne⟩ := hpoint
  have hpos : 0 < ∫ x in (0 : ℝ)..1, mode beta a b a b x ^ 2 :=
    integral_mode_sq_pos ht hmode_ne
  intro hzero
  have hae : mode beta a b a b =ᵐ[unitIocMeasure] (fun _ : ℝ => 0) := by
    have hcoe := coeFn_classicalModeLp beta a b a b
    rw [hzero] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℝ 2 unitIocMeasure)
  have hsq : (fun x => mode beta a b a b x ^ 2) =ᵐ[unitIocMeasure]
      (fun _ : ℝ => 0) := by
    filter_upwards [hae] with x hx
    rw [hx]
    norm_num
  have hzint : ∫ x, mode beta a b a b x ^ 2 ∂unitIocMeasure = 0 := by
    calc
      ∫ x, mode beta a b a b x ^ 2 ∂unitIocMeasure =
          ∫ _x, (0 : ℝ) ∂unitIocMeasure := integral_congr_ae hsq
      _ = 0 := by simp
  have hzinterval : ∫ x in (0 : ℝ)..1, mode beta a b a b x ^ 2 = 0 := by
    rw [← integral_unitIocMeasure_eq_intervalIntegral]
    exact hzint
  exact (ne_of_gt hpos) hzinterval

/-- Scaling the two reduced free-beam coefficients scales the corresponding
`L²(0,1)` mode.  Keeping this bridge explicit lets the simplicity proof stay at
the paper's two-by-two boundary system rather than at the quotient-space level. -/
theorem classicalModeLp_smul_identified (beta c a b : ℝ) :
    classicalModeLp beta (c * a) (c * b) (c * a) (c * b) =
      c • classicalModeLp beta a b a b := by
  apply Lp.ext
  filter_upwards [
    coeFn_classicalModeLp beta (c * a) (c * b) (c * a) (c * b),
    coeFn_classicalModeLp beta a b a b,
    Lp.coeFn_smul c (classicalModeLp beta a b a b)] with t hleft hright hsmul
  rw [hleft, hsmul, Pi.smul_apply, smul_eq_mul, hright]
  unfold mode
  ring

/-- A classical mode satisfying the four free-end boundary equations gives a point of the
classical fourth-derivative graph, with output `beta^4` times its `L²` class. -/
def classicalFreeBeamRepresentativeMode
    {beta a b c d : ℝ} (hfree : FreeBoundary beta a b c d) :
    ClassicalFreeBeamRepresentative
      (classicalModeLp beta a b c d)
      (beta ^ 4 • classicalModeLp beta a b c d) := by
  rcases hfree with ⟨h20, h30, h21, h31⟩
  refine
    { u0 := mode beta a b c d
      u1 := modeD1 beta a b c d
      u2 := modeD2 beta a b c d
      u3 := modeD3 beta a b c d
      u4 := modeD4 beta a b c d
      x_ae := coeFn_classicalModeLp beta a b c d
      y_ae := ?_
      u0_continuous := continuous_mode beta a b c d
      u2_continuous := continuous_modeD2 beta a b c d
      u4_continuous := continuous_modeD4 beta a b c d
      deriv0 := fun t _ => (hasDerivAt_mode beta a b c d t).hasDerivWithinAt
      deriv1 := fun t _ => (hasDerivAt_modeD1 beta a b c d t).hasDerivWithinAt
      deriv2 := fun t _ => (hasDerivAt_modeD2 beta a b c d t).hasDerivWithinAt
      deriv3 := fun t _ => (hasDerivAt_modeD3 beta a b c d t).hasDerivWithinAt
      second_left := h20
      third_left := h30
      second_right := h21
      third_right := h31 }
  filter_upwards [Lp.coeFn_smul (beta ^ 4) (classicalModeLp beta a b c d),
    coeFn_classicalModeLp beta a b c d] with t hsmul hmode
  rw [hsmul, Pi.smul_apply, hmode, smul_eq_mul]
  rfl

/-- Every positive characteristic root produces a genuine nonzero eigenpair of the real
self-adjoint free-beam operator. -/
theorem exists_eigenpair_of_characteristic {beta : ℝ} (hbeta : 0 < beta)
    (hroot : characteristic beta = 0) :
    ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
      beamOperator x = beta ^ 4 • (x : BeamL2) := by
  obtain ⟨a, b, hab, hfree⟩ :=
    TauCeti.DavisKahan.FreeBeam.Classical.exists_nontrivial_freeBoundary_of_characteristic
      hbeta.ne' hroot
  let u : BeamL2 := classicalModeLp beta a b a b
  have hu0 : u ≠ 0 := by
    simpa [u] using classicalModeLp_ne_zero_of_identified_coefficients hbeta hab
  have hrep : ClassicalFreeBeamRepresentative u (beta ^ 4 • u) := by
    simpa [u] using classicalFreeBeamRepresentativeMode hfree
  have hclassical : (u, beta ^ 4 • u) ∈ classicalFreeBeamGraph :=
    (show Nonempty (ClassicalFreeBeamRepresentative u (beta ^ 4 • u)) from ⟨hrep⟩)
  have hgraph : (u, beta ^ 4 • u) ∈
      (beamOperator.graph : Set (BeamL2 × BeamL2)) :=
    classicalFreeBeamGraph_subset_graph hclassical
  obtain ⟨x, hxu, hBx⟩ :=
    (LinearPMap.mem_graph_iff beamOperator).1 hgraph
  let xb : beamOperator.domain := x
  have hxb : (xb : BeamL2) = u := by
    change (x : BeamL2) = u
    exact hxu
  have hBxb : beamOperator xb = beta ^ 4 • u := by
    change beamOperator x = beta ^ 4 • u
    exact hBx
  refine ⟨xb, ?_, ?_⟩
  · intro hzero
    apply hu0
    rw [← hxb, hzero]
  · rw [hBxb, hxb]

/-! ## Positive eigenfunctions satisfy the characteristic equation -/

/-- Every positive eigenvector of the real beam is represented by an identified
classical free-beam mode at the canonical positive fourth root of its eigenvalue.
This strengthens the characteristic-equation classification with the actual mode
representation needed to certify geometric multiplicity. -/
theorem exists_characteristic_mode_of_eigen {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = lam • (x : BeamL2)) :
    ∃ beta a b : ℝ,
      beta = lam ^ ((1 : ℝ) / 4) ∧
      0 < beta ∧
      characteristic beta = 0 ∧
      lam = beta ^ 4 ∧
      (a ≠ 0 ∨ b ≠ 0) ∧
      FreeBoundary beta a b a b ∧
      (x : BeamL2) = classicalModeLp beta a b a b := by
  classical
  obtain ⟨p, hembed, hpair⟩ := exists_form_representative_of_beam_apply x
  set xfn : ℝ → ℝ := ((x : BeamL2) : ℝ → ℝ) with hxfn
  set wfn : ℝ → ℝ := ((beamSnd p : BeamL2) : ℝ → ℝ) with hwfn
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, xfn =ᵐ[unitIocMeasure]
      fun t => a + b * t + secondPrimitive wfn t := by
    obtain ⟨a, b, h⟩ := beamV_repr p
    rw [hembed] at h
    exact ⟨a, b, h⟩
  have hxapply : (((beamOperator x : BeamL2) : ℝ → ℝ)) =ᵐ[unitIocMeasure]
      fun t => lam * xfn t := by
    rw [heig]
    filter_upwards [Lp.coeFn_smul lam (x : BeamL2)] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
  have hw2 : ∀ k : ℕ,
      ∫ t, wfn t * intervalBumpD2 k t ∂unitIocMeasure =
        ∫ t, (lam * xfn t) * intervalBump k t ∂unitIocMeasure := by
    intro k
    have h := beam_pairing_integral hpair (continuous_intervalBump k)
      (continuous_intervalBumpD1 k) (continuous_intervalBumpD2 k)
      (hasDerivAt_intervalBump k) (hasDerivAt_intervalBumpD1 k)
    rw [show ∫ t, ((beamOperator x : BeamL2) : ℝ → ℝ) t *
        intervalBump k t ∂unitIocMeasure =
      ∫ t, (lam * xfn t) * intervalBump k t ∂unitIocMeasure from
        integral_congr_ae (by filter_upwards [hxapply] with t ht; rw [ht])] at h
    exact h
  obtain ⟨c, d, hcd⟩ := eq_affine_add_secondPrimitive_of_forall_integral_bumpD2
    (Lp.memLp _) ((Lp.memLp _).const_mul lam) hw2
  have hKsm : ∀ t,
      secondPrimitive (fun s => lam * xfn s) t = lam * secondPrimitive xfn t := by
    intro t
    have hfun : (fun s => lam * xfn s) = lam • xfn := rfl
    rw [hfun, secondPrimitive_smul]
    rfl
  set u0 : ℝ → ℝ := fun t => a + b * t + secondPrimitive wfn t with hu0
  set u2 : ℝ → ℝ := fun t => c + d * t + lam * secondPrimitive xfn t with hu2
  have hxuae : xfn =ᵐ[unitIocMeasure] u0 := hab
  have hwu2ae : wfn =ᵐ[unitIocMeasure] u2 := by
    refine hcd.trans (Filter.Eventually.of_forall fun t => ?_)
    simp only [hKsm, hu2]
    rfl
  have hKw : secondPrimitive wfn = secondPrimitive u2 := secondPrimitive_congr_ae hwu2ae
  have hKx : secondPrimitive xfn = secondPrimitive u0 := secondPrimitive_congr_ae hxuae
  have hwint : Integrable wfn unitIocMeasure := integrable_coeFn _
  have hxint : Integrable xfn unitIocMeasure := integrable_coeFn _
  have hu0cont : Continuous u0 := by
    rw [hu0]
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_secondPrimitive hwint)
  have hu2cont : Continuous u2 := by
    rw [hu2]
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_secondPrimitive hxint))
  have hu0int : Integrable u0 unitIocMeasure := integrable_unitIocMeasure_of_continuous hu0cont
  have hu2int : Integrable u2 unitIocMeasure := integrable_unitIocMeasure_of_continuous hu2cont
  set u1 : ℝ → ℝ := fun t => b + firstPrimitive u2 t with hu1
  set u3 : ℝ → ℝ := fun t => d + lam * firstPrimitive u0 t with hu3
  have hu0eq : u0 = fun t : ℝ => a + b * t + secondPrimitive u2 t := by
    funext t
    simp only [hu0]
    rw [show secondPrimitive wfn t = secondPrimitive u2 t from congrFun hKw t]
  have hu2eq : u2 = fun t : ℝ => c + d * t + lam * secondPrimitive u0 t := by
    funext t
    simp only [hu2]
    rw [show secondPrimitive xfn t = secondPrimitive u0 t from congrFun hKx t]
  have hd0 : ∀ t, HasDerivAt u0 (u1 t) t := by
    intro t
    rw [hu0eq]
    have h := ((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).add
      (hasDerivAt_secondPrimitive hu2int t)
    refine h.congr_deriv ?_
    simp only [hu1]
    ring
  have hd1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u1 (u2 t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu1]
    exact (hasDerivWithinAt_firstPrimitive_of_continuous hu2cont ht).const_add b
  have hd2 : ∀ t, HasDerivAt u2 (u3 t) t := by
    intro t
    rw [hu2eq]
    have h := ((hasDerivAt_const t c).add ((hasDerivAt_id t).const_mul d)).add
      ((hasDerivAt_secondPrimitive hu0int t).const_mul lam)
    refine h.congr_deriv ?_
    simp only [hu3]
    ring
  have hd3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 (lam * u0 t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu3]
    exact ((hasDerivWithinAt_firstPrimitive_of_continuous hu0cont ht).const_mul lam).const_add d
  have hu3cont : ContinuousOn u3 (Set.Icc 0 1) :=
    fun t ht => (hd3 t ht).continuousWithinAt
  have hu4ae : ((beamOperator x : BeamL2) : ℝ → ℝ) =ᵐ[unitIocMeasure]
      fun t => lam * u0 t := by
    filter_upwards [hxapply, hxuae] with t happly hx
    rw [happly, hx]
  have hu4cont : Continuous (fun t => lam * u0 t) := continuous_const.mul hu0cont
  have hB := fun (c0 c1 c2 c3 : ℝ) => boundary_form_eq_zero hpair hwu2ae hu4ae hu4cont
    hu2cont hd2 hu3cont hd3
    (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3) (cubicD2 c0 c1 c2 c3)
    (continuous_cubic _ _ _ _) (continuous_cubicD1 _ _ _ _) (continuous_cubicD2 _ _ _ _)
    (hasDerivAt_cubic _ _ _ _) (hasDerivAt_cubicD1 _ _ _ _)
  have hu30 : u3 0 = 0 := by
    have h := hB 1 0 (-3) 2
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu20 : u2 0 = 0 := by
    have h := hB 0 1 (-2) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu31 : u3 1 = 0 := by
    have h := hB 0 0 3 (-2)
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu21 : u2 1 = 0 := by
    have h := hB 0 0 (-1) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  set beta : ℝ := lam ^ ((1 : ℝ) / 4) with hbeta
  have hβpos : 0 < beta := Real.rpow_pos_of_pos hlam _
  have hβ4 : beta ^ 4 = lam := by
    rw [hbeta, ← Real.rpow_natCast (lam ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul hlam.le]
    norm_num
  obtain ⟨aR, bR, cR, dR, hm0, hm1, hm2, hm3⟩ :=
    exists_mode_eqOn_of_fourth_deriv_within beta hβpos.ne'
      (u := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (fun t ht => (hd0 t).hasDerivWithinAt)
      hd1
      (fun t ht => (hd2 t).hasDerivWithinAt)
      (fun t ht => by
        have h := hd3 t ht
        simpa [hβ4] using h)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hbd : FreeBoundary beta aR bR cR dR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hm2 h0mem, hu20]
    · rw [← hm3 h0mem, hu30]
    · rw [← hm2 h1mem, hu21]
    · rw [← hm3 h1mem, hu31]
  have hnontriv : aR ≠ 0 ∨ bR ≠ 0 ∨ cR ≠ 0 ∨ dR ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    refine Lp.ext ?_
    filter_upwards [hxuae, ae_mem_unitIocMeasure, Lp.coeFn_zero ℝ 2 unitIocMeasure] with
      t hxt htI hzero
    have hu : u0 t = mode beta aR bR cR dR t := hm0 ⟨htI.1.le, htI.2⟩
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2] at hu
    simp [mode] at hu
    calc
      (((x : BeamL2) : ℝ → ℝ) t) = xfn t := by rw [hxfn]
      _ = u0 t := hxt
      _ = 0 := hu
      _ = (((0 : BeamL2) : ℝ → ℝ) t) := hzero.symm
  have hchar : characteristic beta = 0 :=
    characteristic_eq_zero_of_freeBoundary hβpos.ne' hbd hnontriv
  obtain ⟨hcR, hdR⟩ := left_boundary_coefficients hβpos.ne' hbd.1 hbd.2.1
  have habR : aR ≠ 0 ∨ bR ≠ 0 := by
    rcases hnontriv with ha | hb | hc | hd
    · exact Or.inl ha
    · exact Or.inr hb
    · exact Or.inl (fun ha => hc (hcR.trans ha))
    · exact Or.inr (fun hb => hd (hdR.trans hb))
  have hbdR : FreeBoundary beta aR bR aR bR := by
    simpa [hcR, hdR] using hbd
  have hxmode : (x : BeamL2) = classicalModeLp beta aR bR aR bR := by
    apply Lp.ext
    filter_upwards [hxuae, ae_mem_unitIocMeasure,
      coeFn_classicalModeLp beta aR bR aR bR] with t hxt htI hmode
    have hu : u0 t = mode beta aR bR cR dR t := hm0 ⟨htI.1.le, htI.2⟩
    rw [hcR, hdR] at hu
    calc
      (((x : BeamL2) : ℝ → ℝ) t) = xfn t := by rw [hxfn]
      _ = u0 t := hxt
      _ = mode beta aR bR aR bR t := hu
      _ = ((classicalModeLp beta aR bR aR bR : BeamL2) : ℝ → ℝ) t := hmode.symm
  exact ⟨beta, aR, bR, hbeta, hβpos, hchar, hβ4.symm, habR, hbdR, hxmode⟩

/-- Every positive eigenvalue of the real beam is the fourth power of a positive free-beam
characteristic root. -/
theorem exists_characteristic_of_eigen {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = lam • (x : BeamL2)) :
    ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4 := by
  obtain ⟨beta, _a, _b, _hbeta, hβpos, hchar, hβ4, _hab, _hfree, _hxmode⟩ :=
    exists_characteristic_mode_of_eigen hlam hx0 heig
  exact ⟨beta, hβpos, hchar, hβ4⟩

/-- **Positive free-beam eigenvalues are geometrically simple.**  Any two
nonzero eigenvectors with the same positive eigenvalue are scalar multiples.
This is the multiplicity statement needed to justify the strict paper indexing
`alpha_1 = alpha_2 = 0 < alpha_3 < alpha_4 < ...`; enumerating only the set of
distinct positive spectral values is not enough. -/
theorem positive_eigenvectors_eq_smul {lam : ℝ} (hlam : 0 < lam)
    {x y : beamOperator.domain}
    (hx0 : (x : BeamL2) ≠ 0) (hy0 : (y : BeamL2) ≠ 0)
    (hx : beamOperator x = lam • (x : BeamL2))
    (hy : beamOperator y = lam • (y : BeamL2)) :
    ∃ c : ℝ, (y : BeamL2) = c • (x : BeamL2) := by
  obtain ⟨betax, ax, bx, hbetax, hbetaxPos, _hcharx, _hpowx, habx, hfreex, hmodex⟩ :=
    exists_characteristic_mode_of_eigen hlam hx0 hx
  obtain ⟨betay, ay, byCoeff, hbetay, _hbetayPos, _hchary, _hpowy, _haby, hfreey, hmodey⟩ :=
    exists_characteristic_mode_of_eigen hlam hy0 hy
  have hfreey' : FreeBoundary betax ay byCoeff ay byCoeff := by
    simpa [hbetay, hbetax] using hfreey
  have hmodey' : (y : BeamL2) = classicalModeLp betax ay byCoeff ay byCoeff := by
    simpa [hbetay, hbetax] using hmodey
  obtain ⟨hrowx, _⟩ :=
    right_boundary_reduced hbetaxPos.ne' hfreex.2.2.1 hfreex.2.2.2
  obtain ⟨hrowy, _⟩ :=
    right_boundary_reduced hbetaxPos.ne' hfreey'.2.2.1 hfreey'.2.2.2
  obtain ⟨c, hay, hby⟩ :=
    TauCeti.DavisKahan.FreeBeam.Classical.reduced_boundary_solution_eq_smul
      hbetaxPos hrowx habx hrowy
  refine ⟨c, ?_⟩
  calc
    (y : BeamL2) = classicalModeLp betax ay byCoeff ay byCoeff := hmodey'
    _ = classicalModeLp betax (c * ax) (c * bx) (c * ax) (c * bx) := by
      rw [hay, hby]
    _ = c • classicalModeLp betax ax bx ax bx :=
      classicalModeLp_smul_identified betax c ax bx
    _ = c • (x : BeamL2) := by rw [hmodex]

/-- Every positive eigenvalue of the real free-beam realization exceeds `500`. -/
theorem eigenvalue_gt_five_hundred {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = lam • (x : BeamL2)) :
    500 < lam := by
  obtain ⟨beta, hβ, hchar, hlameq⟩ := exists_characteristic_of_eigen hlam hx0 heig
  rw [hlameq]
  exact Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero hβ hchar

/-- Eigenvalues of the real free beam are nonnegative. -/
theorem nonneg_of_beamOperator_eigen {lam : ℝ} {x : beamOperator.domain}
    (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = lam • (x : BeamL2)) : 0 ≤ lam := by
  have hpos : 0 ≤ lam * ‖(x : BeamL2)‖ ^ 2 := by
    have h := beamOperator_nonneg x
    simpa [heig, real_inner_smul_left, inner_self_eq_norm_sq] using h
  have hn2 : 0 < ‖(x : BeamL2)‖ ^ 2 := by
    have : 0 < ‖(x : BeamL2)‖ := norm_pos_iff.mpr hx0
    positivity
  nlinarith

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
