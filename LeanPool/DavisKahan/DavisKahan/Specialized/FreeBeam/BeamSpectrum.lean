/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpace
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamModeUniqueness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootLocalization
import Mathlib.Tactic

/-!
# Kernel and eigenfunctions of the free-beam operator

With the operator in hand (`BeamFormSpace`), this file starts its spectral analysis:

* the **variational eigen-identity**: an eigenpair of `beamOperator` pairs the bending slot
  of its form representative against every test pair;
* the **kernel is the affine plane**: `beamOperator u = 0` exactly when `u` is a complex
  combination of `1` and `t`.

The eigenfunction bootstrap and the full spectrum characterization build on these.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

noncomputable section

/-! ## Plumbing for the shifted realization -/

/-- The domain of the beam operator is the domain of its shifted realization. -/
theorem beamOperator_domain_eq :
    beamOperator.domain = beamShiftedFormData.shiftedOperator.domain := rfl

/-- The shifted operator acts as the beam operator plus the identity. -/
theorem shifted_apply_of_beam {x : beamOperator.domain} :
    beamShiftedFormData.shiftedOperator x
      = beamOperator x + (x : BeamL2) := by
  have h : beamOperator x
      = beamShiftedFormData.shiftedOperator x - (x : BeamL2) :=
    beamShiftedFormData.beamOperator_apply x
  rw [h]
  abel

/-- The inner product of the form space decomposes along the two slots. -/
theorem beamV_inner_decompose (p v : BeamV) :
    ⟪p, v⟫_ℂ = ⟪beamEmbed p, beamEmbed v⟫_ℂ + ⟪beamSnd p, beamSnd v⟫_ℂ := by
  have hcoe : ⟪p, v⟫_ℂ = ⟪(p : BeamPairSpace), (v : BeamPairSpace)⟫_ℂ := rfl
  rw [hcoe, WithLp.prod_inner_apply]
  rfl

/-- **The variational eigen-identity.**  If `x` is an eigenvector of the beam operator with
real eigenvalue `lam`, there is a form-space representative `p` with first slot `x` whose
bending slot pairs against every test pair by `lam` times the ambient pairing. -/
theorem exists_form_representative_of_eigen {lam : ℝ} {x : beamOperator.domain}
    (heig : beamOperator x = (lam : ℂ) • (x : BeamL2)) :
    ∃ p : BeamV, beamEmbed p = (x : BeamL2) ∧
      ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
        = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
  set p : BeamV := beamShiftedFormData.formRepresentative x with hpdef
  have hembed : beamEmbed p = (x : BeamL2) := by
    have := beamShiftedFormData.embed_formRepresentative x
    exact this
  refine ⟨p, hembed, ?_⟩
  intro v
  -- the variational identity for the forcing `(shifted) x = (1 + lam) x`
  have hvar := beamCoerciveFormData.variational_identity
    (beamShiftedFormData.shiftedOperator x) v
  have hform : beamCoerciveFormData.formOperator
      (beamCoerciveFormData.solutionOperator
        (beamShiftedFormData.shiftedOperator x))
      = p := by
    rw [show beamCoerciveFormData.formOperator = 1 from rfl]
    rfl
  rw [hform] at hvar
  -- identify the forcing
  have hforce : beamShiftedFormData.shiftedOperator x
      = ((1 + lam : ℝ) : ℂ) • (x : BeamL2) := by
    rw [shifted_apply_of_beam, heig]
    push_cast
    rw [add_smul, one_smul]
    abel
  rw [hforce] at hvar
  -- expand both sides
  have hlhs : ⟪p, v⟫_ℂ = ⟪(x : BeamL2), beamEmbed v⟫_ℂ + ⟪beamSnd p, beamSnd v⟫_ℂ := by
    rw [beamV_inner_decompose, hembed]
  have hrhs : ⟪((1 + lam : ℝ) : ℂ) • (x : BeamL2),
      beamCoerciveFormData.embed v⟫_ℂ
      = ((1 + lam : ℝ) : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
    rw [inner_smul_left]
    rw [show beamCoerciveFormData.embed = beamEmbed from rfl]
    congr 1
    rw [Complex.conj_ofReal]
  rw [hlhs, hrhs] at hvar
  have : ⟪beamSnd p, beamSnd v⟫_ℂ
      = ((1 + lam : ℝ) : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ
        - ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
    linear_combination hvar
  rw [this]
  push_cast
  ring

/-! ## The affine kernel -/

/-- Both bump moments against the ambient measure vanish. -/
theorem integral_bumpD2C_eq_zero (k : ℕ) :
    ∫ t, bumpD2C k t ∂unitIocMeasure = 0 := by
  have : ∫ t, bumpD2C k t ∂unitIocMeasure
      = ((∫ t, intervalBumpD2 k t ∂unitIocMeasure : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    rfl
  rw [this, integral_unitIocMeasure_eq_intervalIntegral, integral_intervalBumpD2]
  norm_num

/-- The first moment of the second bump derivative vanishes as well. -/
theorem integral_id_mul_bumpD2C_eq_zero (k : ℕ) :
    ∫ t, ((t : ℝ) : ℂ) * bumpD2C k t ∂unitIocMeasure = 0 := by
  have hpt : ∀ t : ℝ, ((t : ℝ) : ℂ) * bumpD2C k t
      = ((t * intervalBumpD2 k t : ℝ) : ℂ) := by
    intro t
    rw [bumpD2C]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal,
    integral_unitIocMeasure_eq_intervalIntegral, integral_id_mul_intervalBumpD2]
  norm_num

/-- The affine pair `(a·1 + b·t, 0)` lies in the form subspace. -/
theorem affinePair_mem (a b : ℂ) :
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
        (a • beamOneLp + b • beamIdLp, 0)) ∈ beamFormSubmodule := by
  rw [mem_beamFormSubmodule_iff]
  intro k
  have hfst : pairFst ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = a • beamOneLp + b • beamIdLp := by
    rw [pairFst_apply]
    simp
  have hsnd : pairSnd ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = 0 := by
    rw [pairSnd_apply]
    simp
  rw [hfst, hsnd]
  have hrhs : ∫ t, ((0 : BeamL2) : ℝ → ℂ) t * bumpC k t ∂unitIocMeasure = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℂ 2 unitIocMeasure] with t ht
      rw [ht]
      simp
  rw [hrhs]
  have hlhs : ∫ t, ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t * bumpD2C k t
      ∂unitIocMeasure
      = a * (∫ t, bumpD2C k t ∂unitIocMeasure)
        + b * ∫ t, ((t : ℝ) : ℂ) * bumpD2C k t ∂unitIocMeasure := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← integral_add (((integrable_unitIocMeasure_of_continuous
          (continuous_bumpD2C k)).const_mul a))
        ((integrable_mul_of_continuous (integrable_unitIocMeasure_of_continuous
          (by fun_prop)) (continuous_bumpD2C k)).const_mul b)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
      Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
      coeFn_beamIdLp] with t hadd hsa hsb h1 hT
    rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hlhs, integral_bumpD2C_eq_zero, integral_id_mul_bumpD2C_eq_zero]
  ring

/-- The affine element of the ambient space attached to a coefficient pair. -/
def affineLp (a b : ℂ) : BeamL2 := a • beamOneLp + b • beamIdLp

/-- The form representative of an affine element. -/
def affineV (a b : ℂ) : BeamV :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0),
    affinePair_mem a b⟩

/-- The inclusion of an affine form-domain element is the affine function. -/
@[simp] theorem beamEmbed_affineV (a b : ℂ) : beamEmbed (affineV a b) = affineLp a b := by
  rw [show beamEmbed (affineV a b) = pairFst ((affineV a b : BeamV) : BeamPairSpace)
    from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace)
    = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0)
    from rfl]
  rw [pairFst_apply]
  simp

/-- An affine form-domain element has vanishing second derivative. -/
@[simp] theorem beamSnd_affineV (a b : ℂ) : beamSnd (affineV a b) = 0 := by
  rw [show beamSnd (affineV a b) = pairSnd ((affineV a b : BeamV) : BeamPairSpace)
    from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace)
    = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0)
    from rfl]
  rw [pairSnd_apply]
  simp

/-- The adjoint of the embedding sends an affine element to its form representative. -/
theorem adjoint_beamEmbed_affine (a b : ℂ) :
    ContinuousLinearMap.adjoint beamEmbed (affineLp a b) = affineV a b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, beamV_inner_decompose,
    beamEmbed_affineV, beamSnd_affineV, inner_zero_left, add_zero]

/-- Affine elements lie in the beam operator's domain and are annihilated by it. -/
theorem beamOperator_affine_mem_and_zero (a b : ℂ) :
    ∃ h : affineLp a b ∈ beamOperator.domain,
      beamOperator ⟨affineLp a b, h⟩ = 0 := by
  -- the resolvent fixes affine elements
  have hres : beamCoerciveFormData.resolvent (affineLp a b) = affineLp a b := by
    rw [show beamCoerciveFormData.resolvent
        = beamCoerciveFormData.embed ∘L beamCoerciveFormData.solutionOperator from rfl]
    have hsol : beamCoerciveFormData.solutionOperator (affineLp a b) = affineV a b := by
      rw [show beamCoerciveFormData.solutionOperator
          = beamCoerciveFormData.formInverse ∘L
            (ContinuousLinearMap.adjoint beamCoerciveFormData.embed) from rfl]
      have hinv : beamCoerciveFormData.formInverse = 1 := by
        rw [show beamCoerciveFormData.formInverse
            = Ring.inverse beamCoerciveFormData.formOperator from rfl]
        rw [show beamCoerciveFormData.formOperator = 1 from rfl]
        exact Ring.inverse_one _
      rw [ContinuousLinearMap.comp_apply, hinv]
      rw [show (ContinuousLinearMap.adjoint beamCoerciveFormData.embed)
          (affineLp a b) = affineV a b from adjoint_beamEmbed_affine a b]
      rfl
    rw [ContinuousLinearMap.comp_apply, hsol]
    exact beamEmbed_affineV a b
  have hmem : affineLp a b ∈ beamOperator.domain := by
    rw [show beamOperator.domain
        = LinearMap.range (beamCoerciveFormData.resolvent :
            BeamL2 →ₗ[ℂ] BeamL2) from rfl]
    exact ⟨affineLp a b, hres⟩
  refine ⟨hmem, ?_⟩
  -- the shifted operator fixes affine elements, so the beam operator kills them
  have hshift : beamShiftedFormData.shiftedOperator ⟨affineLp a b, hmem⟩
      = affineLp a b := by
    have := Abstract.inversePartialMap_apply_R beamCoerciveFormData.resolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective (affineLp a b)
    have hsub : (⟨beamCoerciveFormData.resolvent (affineLp a b),
        LinearMap.mem_range_self _ (affineLp a b)⟩ :
          beamShiftedFormData.shiftedOperator.domain)
        = ⟨affineLp a b, hmem⟩ := Subtype.ext hres
    rw [← hsub]
    exact this
  have happly : beamOperator ⟨affineLp a b, hmem⟩
      = beamShiftedFormData.shiftedOperator ⟨affineLp a b, hmem⟩
        - affineLp a b :=
    beamShiftedFormData.beamOperator_apply _
  rw [happly, hshift, sub_self]

/-- Conversely, an element of the kernel is affine. -/
theorem exists_affine_of_beamOperator_eq_zero {x : beamOperator.domain}
    (hx : beamOperator x = 0) :
    ∃ a b : ℂ, (x : BeamL2) = affineLp a b := by
  -- the quadratic form vanishes, hence so does the bending slot
  have hquad : RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℂ
      = beamShiftedFormData.bendingEnergy (beamShiftedFormData.formRepresentative x) :=
    beamShiftedFormData.beam_quadratic_eq_bendingEnergy x
  rw [hx, inner_zero_left] at hquad
  have hbend0 : beamShiftedFormData.bendingEnergy
      (beamShiftedFormData.formRepresentative x) = 0 := by
    rw [← hquad]
    simp
  have hbend : ‖beamSnd (beamShiftedFormData.formRepresentative x)‖ ^ 2 = 0 := hbend0
  have hsnd0 : beamSnd (beamShiftedFormData.formRepresentative x) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hbend
    exact norm_eq_zero.mp this
  -- the representation theorem with vanishing density
  obtain ⟨a, b, hab⟩ := beamV_repr (beamShiftedFormData.formRepresentative x)
  have hembed := beamShiftedFormData.embed_formRepresentative x
  refine ⟨a, b, ?_⟩
  have hK0 : secondPrimitive ((beamSnd (beamShiftedFormData.formRepresentative x)
      : ℝ → ℂ)) = secondPrimitive (fun _ => 0) := by
    apply secondPrimitive_congr_ae
    rw [hsnd0]
    exact Lp.coeFn_zero ℂ 2 unitIocMeasure
  have hKzero : ∀ t : ℝ, secondPrimitive (fun _ : ℝ => (0 : ℂ)) t = 0 := by
    intro t
    rw [secondPrimitive_def]
    simp
  refine Lp.ext ?_
  have hxcoe : ((x : BeamL2) : ℝ → ℂ)
      =ᵐ[unitIocMeasure] (beamEmbed (beamShiftedFormData.formRepresentative x)
        : ℝ → ℂ) := by
    rw [show beamEmbed (beamShiftedFormData.formRepresentative x) = (x : BeamL2)
      from hembed]
  filter_upwards [hxcoe, hab, Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
    coeFn_beamIdLp] with t hx1 hx2 hadd hsa hsb h1 hT
  rw [hx1, hx2, hK0, hKzero, add_zero]
  rw [show (affineLp a b : ℝ → ℂ) t = ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t
    from rfl]
  rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
    smul_eq_mul, smul_eq_mul]
  ring

/-! ## The eigen-pairing against smooth test functions -/

/-- Test the variational eigen-identity against the pair of a real `C²` function and its
second derivative, and conjugate away: the bending slot integrates against `f''` as `lam`
times the eigenvector against `f`. -/
theorem eigen_pairing_integral {lam : ℝ} {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
      = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ)
    {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ t, HasDerivAt f (f1 t) t) (hd1 : ∀ t, HasDerivAt f1 (f2 t) t) :
    ∫ t, (beamSnd p : ℝ → ℂ) t * (f2 t : ℂ) ∂unitIocMeasure
      = (lam : ℂ) * ∫ t, ((x : BeamL2) : ℝ → ℂ) t * (f t : ℂ) ∂unitIocMeasure := by
  set v : BeamV := ⟨(WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
    (contToLp (fun t => (f t : ℂ)) (by fun_prop),
      contToLp (fun t => (f2 t : ℂ)) (by fun_prop)),
    contPair_mem hf hf1 hf2 hd hd1⟩ with hvdef
  have hvfst : beamEmbed v = contToLp (fun t => (f t : ℂ)) (by fun_prop) := by
    rw [show beamEmbed v = pairFst ((v : BeamV) : BeamPairSpace) from rfl, hvdef,
      pairFst_apply]
    simp
  have hvsnd : beamSnd v = contToLp (fun t => (f2 t : ℂ)) (by fun_prop) := by
    rw [show beamSnd v = pairSnd ((v : BeamV) : BeamPairSpace) from rfl, hvdef,
      pairSnd_apply]
    simp
  have hid := hpair v
  rw [hvfst, hvsnd] at hid
  -- expand the two inner products as integrals
  have hL : ⟪beamSnd p, contToLp (fun t => (f2 t : ℂ)) (by fun_prop)⟫_ℂ
      = ∫ t, (starRingEnd ℂ) ((beamSnd p : ℝ → ℂ) t) * (f2 t : ℂ) ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f2 t : ℂ)) (by fun_prop)] with t ht
    rw [RCLike.inner_apply, ht]
    ring
  have hR : ⟪(x : BeamL2), contToLp (fun t => (f t : ℂ)) (by fun_prop)⟫_ℂ
      = ∫ t, (starRingEnd ℂ) (((x : BeamL2) : ℝ → ℂ) t) * (f t : ℂ) ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f t : ℂ)) (by fun_prop)] with t ht
    rw [RCLike.inner_apply, ht]
    ring
  rw [hL, hR] at hid
  -- conjugate the identity
  have hconj := congrArg (starRingEnd ℂ) hid
  rw [map_mul, Complex.conj_ofReal, ← integral_conj, ← integral_conj] at hconj
  have h1 : (fun t => (starRingEnd ℂ)
        ((starRingEnd ℂ) ((beamSnd p : ℝ → ℂ) t) * (f2 t : ℂ)))
      = fun t => (beamSnd p : ℝ → ℂ) t * (f2 t : ℂ) := by
    funext t
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have h2 : (fun t => (starRingEnd ℂ)
        ((starRingEnd ℂ) (((x : BeamL2) : ℝ → ℂ) t) * (f t : ℂ)))
      = fun t => ((x : BeamL2) : ℝ → ℂ) t * (f t : ℂ) := by
    funext t
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [h1, h2] at hconj
  exact hconj

/-! ## Cubic test functions -/

/-- Cubic polynomial test function. -/
def cubic (c0 c1 c2 c3 t : ℝ) : ℝ := c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3

/-- First derivative of the cubic. -/
def cubicD1 (_c0 c1 c2 c3 t : ℝ) : ℝ := c1 + 2 * c2 * t + 3 * c3 * t ^ 2

/-- Second derivative of the cubic. -/
def cubicD2 (_c0 _c1 c2 c3 t : ℝ) : ℝ := 2 * c2 + 6 * c3 * t

/-- The model cubic is continuous. -/
theorem continuous_cubic (c0 c1 c2 c3 : ℝ) : Continuous (cubic c0 c1 c2 c3) := by
  unfold cubic
  fun_prop

/-- The model cubic's first derivative is continuous. -/
theorem continuous_cubicD1 (c0 c1 c2 c3 : ℝ) : Continuous (cubicD1 c0 c1 c2 c3) := by
  unfold cubicD1
  fun_prop

/-- The model cubic's second derivative is continuous. -/
theorem continuous_cubicD2 (c0 c1 c2 c3 : ℝ) : Continuous (cubicD2 c0 c1 c2 c3) := by
  unfold cubicD2
  fun_prop

/-- The model cubic differentiates to `cubicD1`. -/
theorem hasDerivAt_cubic (c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3 t) t := by
  have h := (((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
    (((hasDerivAt_pow 2 t)).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)
  refine h.congr_deriv ?_
  unfold cubicD1
  push_cast
  ring

/-- `cubicD1` differentiates to `cubicD2`. -/
theorem hasDerivAt_cubicD1 (c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubicD1 c0 c1 c2 c3) (cubicD2 c0 c1 c2 c3 t) t := by
  have h := ((hasDerivAt_const t c1).add
    (((hasDerivAt_id t).const_mul (2 * c2)))).add
    (((hasDerivAt_pow 2 t)).const_mul (3 * c3))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold cubicD2
    push_cast
    ring
  · refine Filter.Eventually.of_forall fun s => ?_
    unfold cubicD1
    simp only [Pi.add_apply, id_eq]

/-! ## The boundary form of an eigenfunction vanishes -/

/-- The classical boundary form of an eigenfunction's continuous representatives against any
cubic test function vanishes: two integrations by parts against the distributional
eigen-identity. -/
theorem boundary_form_eq_zero {lam : ℝ} {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
      = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ)
    {ubar wbar u3 : ℝ → ℂ}
    (hxu : ((x : BeamL2) : ℝ → ℂ) =ᵐ[unitIocMeasure] ubar)
    (hwu : (beamSnd p : ℝ → ℂ) =ᵐ[unitIocMeasure] wbar)
    (hucont : Continuous ubar) (hwcont : Continuous wbar)
    (hw' : ∀ t, HasDerivAt wbar (u3 t) t)
    (hu3cont : ContinuousOn u3 (Set.Icc 0 1))
    (hu3' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 ((lam : ℂ) * ubar t) (Set.Icc 0 1) t)
    (q q1 q2 : ℝ → ℝ)
    (hq : Continuous q) (hq1 : Continuous q1) (hq2 : Continuous q2)
    (hdq : ∀ t, HasDerivAt q (q1 t) t) (hdq1 : ∀ t, HasDerivAt q1 (q2 t) t) :
    wbar 1 * (q1 1 : ℂ) - wbar 0 * (q1 0 : ℂ)
      - (u3 1 * (q 1 : ℂ) - u3 0 * (q 0 : ℂ)) = 0 := by
  have hbridgeC : ∀ f : ℝ → ℂ, ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
    intro f
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure_def]
  -- the distributional identity for the continuous representatives
  have hInt := eigen_pairing_integral hpair hq hq1 hq2 hdq hdq1
  have hIntBar : ∫ t in (0 : ℝ)..1, wbar t * (q2 t : ℂ)
      = (lam : ℂ) * ∫ t in (0 : ℝ)..1, ubar t * (q t : ℂ) := by
    rw [← hbridgeC, ← hbridgeC]
    rw [show ∫ t, wbar t * (q2 t : ℂ) ∂unitIocMeasure
        = ∫ t, (beamSnd p : ℝ → ℂ) t * (q2 t : ℂ) ∂unitIocMeasure from
      integral_congr_ae (by
        filter_upwards [hwu] with t ht
        rw [ht])]
    rw [show ∫ t, ubar t * (q t : ℂ) ∂unitIocMeasure
        = ∫ t, ((x : BeamL2) : ℝ → ℂ) t * (q t : ℂ) ∂unitIocMeasure from
      integral_congr_ae (by
        filter_upwards [hxu] with t ht
        rw [ht])]
    exact hInt
  -- first integration by parts: differentiate the cubic side down
  have hIBP1 : ∫ t in (0 : ℝ)..1, wbar t * (q2 t : ℂ)
      = wbar 1 * (q1 1 : ℂ) - wbar 0 * (q1 0 : ℂ)
        - ∫ t in (0 : ℝ)..1, u3 t * (q1 t : ℂ) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hwcont.continuousOn (by fun_prop : Continuous fun t : ℝ => (q1 t : ℂ)).continuousOn
      (fun t _ => hw' t) (fun t _ => (hdq1 t).ofReal_comp)
      ?_ ((by fun_prop : Continuous fun t : ℝ => (q2 t : ℂ)).intervalIntegrable 0 1)
    have : ContinuousOn u3 (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hu3cont
    exact this.intervalIntegrable
  -- second integration by parts: interior two-sided derivatives of the third slot
  have hIBP2 : ∫ t in (0 : ℝ)..1, u3 t * (q1 t : ℂ)
      = u3 1 * (q 1 : ℂ) - u3 0 * (q 0 : ℂ)
        - ∫ t in (0 : ℝ)..1, ((lam : ℂ) * ubar t) * (q t : ℂ) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      ?_ (by fun_prop : Continuous fun t : ℝ => (q t : ℂ)).continuousOn
      ?_ (fun t _ => (hdq t).ofReal_comp)
      ((hucont.const_smul ((lam : ℂ))).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (q1 t : ℂ)).intervalIntegrable 0 1)
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hu3cont
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
      exact (hu3' t (Set.Ioo_subset_Icc_self ht')).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)
  -- combine
  have hlin : ∫ t in (0 : ℝ)..1, ((lam : ℂ) * ubar t) * (q t : ℂ)
      = (lam : ℂ) * ∫ t in (0 : ℝ)..1, ubar t * (q t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with t
    ring
  rw [hIBP2, hlin] at hIBP1
  rw [hIntBar] at hIBP1
  linear_combination -hIBP1

/-! ## The eigenvalue classification -/

/-- **Every positive eigenvalue of the free-beam operator is the fourth power of a
characteristic root.**  The bootstrap: the eigen-identity plus the representation theorem
produce continuous representatives with a full fourth-order derivative chain within `[0,1]`;
the interval ODE classification identifies them with classical modes; the vanishing boundary
form forces the free boundary conditions; and a nontrivial mode with free ends satisfies
`cos β cosh β = 1`. -/
theorem exists_characteristic_of_eigen {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = (lam : ℂ) • (x : BeamL2)) :
    ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4 := by
  classical
  obtain ⟨p, hembed, hpair⟩ := exists_form_representative_of_eigen heig
  set xfn : ℝ → ℂ := ((x : BeamL2) : ℝ → ℂ) with hxfn
  set wfn : ℝ → ℂ := ((beamSnd p : BeamL2) : ℝ → ℂ) with hwfn
  -- first representation: the eigenvector itself
  obtain ⟨a, b, hab⟩ : ∃ a b : ℂ, xfn =ᵐ[unitIocMeasure]
      fun t => a + b * (t : ℂ) + secondPrimitive wfn t := by
    obtain ⟨a, b, h⟩ := beamV_repr p
    rw [hembed] at h
    exact ⟨a, b, h⟩
  -- second representation: the bending slot against `lam` times the eigenvector
  have hw2 : ∀ k : ℕ,
      ∫ t, wfn t * (intervalBumpD2 k t : ℂ) ∂unitIocMeasure
        = ∫ t, (fun s => (lam : ℂ) * xfn s) t * (intervalBump k t : ℂ)
            ∂unitIocMeasure := by
    intro k
    have h := eigen_pairing_integral hpair (continuous_intervalBump k)
      (continuous_intervalBumpD1 k) (continuous_intervalBumpD2 k)
      (hasDerivAt_intervalBump k) (hasDerivAt_intervalBumpD1 k)
    rw [h, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  obtain ⟨c, d, hcd⟩ := eq_affine_add_secondPrimitive_of_forall_integral_bumpD2
    (Lp.memLp _) ((Lp.memLp _).const_mul ((lam : ℂ))) hw2
  -- continuous representatives
  have hKsm : ∀ t, secondPrimitive (fun s => (lam : ℂ) * xfn s) t
      = (lam : ℂ) * secondPrimitive xfn t := by
    intro t
    have h1 : (fun s => (lam : ℂ) * xfn s) = (lam : ℂ) • xfn := rfl
    rw [h1, secondPrimitive_smul]
    rfl
  set ubar : ℝ → ℂ := fun t => a + b * (t : ℂ) + secondPrimitive wfn t with hubar
  set wbar : ℝ → ℂ := fun t => c + d * (t : ℂ) + (lam : ℂ) * secondPrimitive xfn t
    with hwbar
  have hxubar : xfn =ᵐ[unitIocMeasure] ubar := hab
  have hwwbar : wfn =ᵐ[unitIocMeasure] wbar := by
    refine hcd.trans (Filter.Eventually.of_forall fun t => ?_)
    simp only [hKsm, hwbar]
    rfl
  have hKw : secondPrimitive wfn = secondPrimitive wbar := secondPrimitive_congr_ae hwwbar
  have hKx : secondPrimitive xfn = secondPrimitive ubar := secondPrimitive_congr_ae hxubar
  have hwint : Integrable wfn unitIocMeasure := integrable_coeFn _
  have hxint : Integrable xfn unitIocMeasure := integrable_coeFn _
  have hKwcont : Continuous (secondPrimitive wfn) := continuous_secondPrimitive hwint
  have hKxcont : Continuous (secondPrimitive xfn) := continuous_secondPrimitive hxint
  have hucont : Continuous ubar := by
    rw [hubar]
    exact (continuous_const.add
      (continuous_const.mul Complex.continuous_ofReal)).add hKwcont
  have hwcont : Continuous wbar := by
    rw [hwbar]
    exact (continuous_const.add
      (continuous_const.mul Complex.continuous_ofReal)).add
      (continuous_const.mul hKxcont)
  have hwbint : Integrable wbar unitIocMeasure :=
    integrable_unitIocMeasure_of_continuous hwcont
  have hubint : Integrable ubar unitIocMeasure :=
    integrable_unitIocMeasure_of_continuous hucont
  -- the derivative chain
  set u1 : ℝ → ℂ := fun t => b + firstPrimitive wbar t with hu1
  set u3 : ℝ → ℂ := fun t => d + (lam : ℂ) * firstPrimitive ubar t with hu3
  have hueq : ubar = fun t : ℝ => a + b * (t : ℂ) + secondPrimitive wbar t := by
    funext t
    simp only [hubar]
    rw [show secondPrimitive wfn t = secondPrimitive wbar t from congrFun hKw t]
  have hweq : wbar = fun t : ℝ => c + d * (t : ℂ)
      + (lam : ℂ) * secondPrimitive ubar t := by
    funext t
    simp only [hwbar]
    rw [show secondPrimitive xfn t = secondPrimitive ubar t from congrFun hKx t]
  have hd1 : ∀ t, HasDerivAt ubar (u1 t) t := by
    intro t
    rw [hueq]
    have h := ((hasDerivAt_const t a).add
      (((hasDerivAt_id t).ofReal_comp).const_mul b)).add
      (hasDerivAt_secondPrimitive hwbint t)
    refine h.congr_deriv ?_
    simp only [hu1]
    push_cast
    ring
  have hd2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt u1 (wbar t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu1]
    have h := (hasDerivWithinAt_firstPrimitive_of_continuous hwcont ht).const_add b
    exact h
  have hd3 : ∀ t, HasDerivAt wbar (u3 t) t := by
    intro t
    rw [hweq]
    have h := ((hasDerivAt_const t c).add
      (((hasDerivAt_id t).ofReal_comp).const_mul d)).add
      ((hasDerivAt_secondPrimitive hubint t).const_mul ((lam : ℂ)))
    refine h.congr_deriv ?_
    simp only [hu3]
    push_cast
    ring
  have hd4 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 ((lam : ℂ) * ubar t) (Set.Icc 0 1) t := by
    intro t ht
    rw [hu3]
    have h := ((hasDerivWithinAt_firstPrimitive_of_continuous hucont ht).const_mul
      ((lam : ℂ))).const_add d
    exact h
  have hu3cont : ContinuousOn u3 (Set.Icc 0 1) := fun t ht => (hd4 t ht).continuousWithinAt
  -- boundary values via the four Hermite cubics
  have hB := fun (c0 c1 c2 c3 : ℝ) => boundary_form_eq_zero hpair hxubar hwwbar
    hucont hwcont hd3 hu3cont hd4 (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3)
    (cubicD2 c0 c1 c2 c3) (continuous_cubic _ _ _ _) (continuous_cubicD1 _ _ _ _)
    (continuous_cubicD2 _ _ _ _) (hasDerivAt_cubic _ _ _ _) (hasDerivAt_cubicD1 _ _ _ _)
  have hu30 : u3 0 = 0 := by
    have h := hB 1 0 (-3) 2
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hw0 : wbar 0 = 0 := by
    have h := hB 0 1 (-2) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hu31 : u3 1 = 0 := by
    have h := hB 0 0 3 (-2)
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  have hw1 : wbar 1 = 0 := by
    have h := hB 0 0 (-1) 1
    simp only [cubic, cubicD1] at h
    norm_num at h
    linear_combination h
  -- the fourth root of the eigenvalue
  set beta : ℝ := lam ^ ((1 : ℝ) / 4) with hbeta
  have hβpos : 0 < beta := Real.rpow_pos_of_pos hlam _
  have hβ4 : beta ^ 4 = lam := by
    rw [hbeta, ← Real.rpow_natCast (lam ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hlam.le]
    norm_num
  -- real and imaginary chains and their mode classifications
  have hre_at : ∀ {f : ℝ → ℂ} {dv : ℂ} {t : ℝ}, HasDerivAt f dv t →
      HasDerivAt (fun s => (f s).re) dv.re t := fun hf =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ hf
  have him_at : ∀ {f : ℝ → ℂ} {dv : ℂ} {t : ℝ}, HasDerivAt f dv t →
      HasDerivAt (fun s => (f s).im) dv.im t := fun hf =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt _ hf
  have hre_within : ∀ {f : ℝ → ℂ} {dv : ℂ} {t : ℝ},
      HasDerivWithinAt f dv (Set.Icc 0 1) t →
      HasDerivWithinAt (fun s => (f s).re) dv.re (Set.Icc 0 1) t := fun hf =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt _ hf
  have him_within : ∀ {f : ℝ → ℂ} {dv : ℂ} {t : ℝ},
      HasDerivWithinAt f dv (Set.Icc 0 1) t →
      HasDerivWithinAt (fun s => (f s).im) dv.im (Set.Icc 0 1) t := fun hf =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt _ hf
  have hmulre : ∀ z : ℂ, ((lam : ℂ) * z).re = beta ^ 4 * z.re := by
    intro z
    rw [hβ4]
    simp [Complex.mul_re]
  have hmulim : ∀ z : ℂ, ((lam : ℂ) * z).im = beta ^ 4 * z.im := by
    intro z
    rw [hβ4]
    simp [Complex.mul_im]
  obtain ⟨aR, bR, cR, dR, hRe0, hRe1, hRe2, hRe3⟩ :=
    exists_mode_eqOn_of_fourth_deriv_within beta hβpos.ne'
      (u := fun s => (ubar s).re) (u1 := fun s => (u1 s).re)
      (u2 := fun s => (wbar s).re) (u3 := fun s => (u3 s).re)
      (fun t ht => hre_within (hd1 t).hasDerivWithinAt)
      (fun t ht => hre_within (hd2 t ht))
      (fun t ht => hre_within (hd3 t).hasDerivWithinAt)
      (fun t ht => by
        have h := hre_within (hd4 t ht)
        rwa [hmulre] at h)
  obtain ⟨aI, bI, cI, dI, hIm0, hIm1, hIm2, hIm3⟩ :=
    exists_mode_eqOn_of_fourth_deriv_within beta hβpos.ne'
      (u := fun s => (ubar s).im) (u1 := fun s => (u1 s).im)
      (u2 := fun s => (wbar s).im) (u3 := fun s => (u3 s).im)
      (fun t ht => him_within (hd1 t).hasDerivWithinAt)
      (fun t ht => him_within (hd2 t ht))
      (fun t ht => him_within (hd3 t).hasDerivWithinAt)
      (fun t ht => by
        have h := him_within (hd4 t ht)
        rwa [hmulim] at h)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- free boundary conditions for both modes
  have hbdRe : FreeBoundary beta aR bR cR dR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hRe2 h0mem]
      simp only [hw0, Complex.zero_re]
    · rw [← hRe3 h0mem]
      simp only [hu30, Complex.zero_re]
    · rw [← hRe2 h1mem]
      simp only [hw1, Complex.zero_re]
    · rw [← hRe3 h1mem]
      simp only [hu31, Complex.zero_re]
  have hbdIm : FreeBoundary beta aI bI cI dI := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hIm2 h0mem]
      simp only [hw0, Complex.zero_im]
    · rw [← hIm3 h0mem]
      simp only [hu30, Complex.zero_im]
    · rw [← hIm2 h1mem]
      simp only [hw1, Complex.zero_im]
    · rw [← hIm3 h1mem]
      simp only [hu31, Complex.zero_im]
  -- at least one of the two modes is nontrivial
  by_cases hRtriv : aR = 0 ∧ bR = 0 ∧ cR = 0 ∧ dR = 0
  · by_cases hItriv : aI = 0 ∧ bI = 0 ∧ cI = 0 ∧ dI = 0
    · -- both trivial: the eigenvector vanishes, contradiction
      exfalso
      apply hx0
      refine Lp.ext ?_
      have hzero : ∀ t ∈ Set.Icc (0 : ℝ) 1, ubar t = 0 := by
        intro t ht
        have h1 : (ubar t).re = 0 := by
          have hm : (ubar t).re = mode beta aR bR cR dR t := hRe0 ht
          obtain ⟨e1, e2, e3, e4⟩ := hRtriv
          rw [e1, e2, e3, e4] at hm
          simpa [mode] using hm
        have h2 : (ubar t).im = 0 := by
          have hm : (ubar t).im = mode beta aI bI cI dI t := hIm0 ht
          obtain ⟨e1, e2, e3, e4⟩ := hItriv
          rw [e1, e2, e3, e4] at hm
          simpa [mode] using hm
        exact Complex.ext h1 h2
      filter_upwards [hxubar, ae_mem_unitIocMeasure,
        Lp.coeFn_zero ℂ 2 unitIocMeasure] with t h1 h2 h3
      have hx1 : ((x : BeamL2) : ℝ → ℂ) t = ubar t := h1
      rw [hx1, hzero t ⟨h2.1.le, h2.2⟩, h3]
      rfl
    · -- the imaginary mode is nontrivial
      have hchar : characteristic beta = 0 := by
        refine characteristic_eq_zero_of_freeBoundary hβpos.ne' hbdIm ?_
        by_contra hcon
        push Not at hcon
        exact hItriv ⟨hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩
      exact ⟨beta, hβpos, hchar, hβ4.symm⟩
  · -- the real mode is nontrivial
    have hchar : characteristic beta = 0 := by
      refine characteristic_eq_zero_of_freeBoundary hβpos.ne' hbdRe ?_
      by_contra hcon
      push Not at hcon
      exact hRtriv ⟨hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩
    exact ⟨beta, hβpos, hchar, hβ4.symm⟩

/-- **The paper's `α₃ > 500`, for the actual operator**: every positive eigenvalue of the
free-beam realization exceeds `500`.  The margin is thin — the first positive root is
`4.7300407…`, whose fourth power is `500.56…`. -/
theorem eigenvalue_gt_five_hundred {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = (lam : ℂ) • (x : BeamL2)) :
    500 < lam := by
  obtain ⟨beta, hβ, hchar, hlameq⟩ := exists_characteristic_of_eigen hlam hx0 heig
  rw [hlameq]
  exact Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero hβ hchar

/-- **Eigenvalues of the free-beam operator are nonnegative**, because the operator is: the
Rayleigh quotient of an eigenvector is the eigenvalue times the squared norm. -/
theorem nonneg_of_beamOperator_eigen {lam : ℝ} {x : beamOperator.domain}
    (hx0 : (x : BeamL2) ≠ 0)
    (heig : beamOperator x = (lam : ℂ) • (x : BeamL2)) : 0 ≤ lam := by
  have hpos := beamOperator_nonneg x
  have hval : ⟪beamOperator x, (x : BeamL2)⟫_ℂ
      = ((lam * ‖(x : BeamL2)‖ ^ 2 : ℝ) : ℂ) := by
    rw [heig, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hval] at hpos
  have hre : RCLike.re (((lam * ‖(x : BeamL2)‖ ^ 2 : ℝ) : ℂ)) = lam * ‖(x : BeamL2)‖ ^ 2 :=
    Complex.ofReal_re _
  rw [hre] at hpos
  have hn2 : (0 : ℝ) < ‖(x : BeamL2)‖ ^ 2 := by
    have : (0 : ℝ) < ‖(x : BeamL2)‖ := norm_pos_iff.mpr hx0
    positivity
  nlinarith

/-! ## The Fredholm bridge: the full real spectrum -/

/-- The variational resolvent is the embedding composed with its own adjoint. -/
theorem beamResolvent_eq :
    beamCoerciveFormData.resolvent
      = beamEmbed.comp (ContinuousLinearMap.adjoint beamEmbed) := by
  have h1 : beamCoerciveFormData.resolvent
      = beamCoerciveFormData.embed ∘L beamCoerciveFormData.solutionOperator := rfl
  have h2 : beamCoerciveFormData.solutionOperator
      = beamCoerciveFormData.formInverse ∘L
        ContinuousLinearMap.adjoint beamCoerciveFormData.embed := rfl
  have h3 : beamCoerciveFormData.formInverse = 1 := by
    rw [show beamCoerciveFormData.formInverse
        = Ring.inverse beamCoerciveFormData.formOperator from rfl]
    rw [show beamCoerciveFormData.formOperator = 1 from rfl]
    exact Ring.inverse_one _
  rw [h1, h2, h3]
  rfl

/-- The variational resolvent is a compact operator. -/
theorem isCompactOperator_beamResolvent :
    IsCompactOperator beamCoerciveFormData.resolvent := by
  rw [beamResolvent_eq]
  exact isCompactOperator_beamEmbed.comp_clm (ContinuousLinearMap.adjoint beamEmbed)

/-- **Inverting the resolvent eigenvalue relation.**  A nonzero scalar `mu` with
`R u = mu • u` places `u` in the operator domain and makes it an eigenvector of the beam
operator for `mu⁻¹ - 1`.  No nondegeneracy of `u` is needed: at `u = 0` both statements
hold trivially. -/
theorem exists_beamOperator_apply_of_beamResolvent_smul {mu : ℂ} (hmu : mu ≠ 0)
    {u : BeamL2} (huv : beamCoerciveFormData.resolvent u = mu • u) :
    ∃ h : u ∈ beamOperator.domain,
      beamOperator ⟨u, h⟩ = (mu⁻¹ - 1) • u := by
  set R := beamCoerciveFormData.resolvent with hR
  -- the eigenvector is in the domain of the shifted operator
  have humem : u ∈ beamOperator.domain := by
    have hmem : u ∈ LinearMap.range ((R : BeamL2 →ₗ[ℂ] BeamL2)) := by
      refine ⟨mu⁻¹ • u, ?_⟩
      rw [show ((R : BeamL2 →ₗ[ℂ] BeamL2)) (mu⁻¹ • u) = R (mu⁻¹ • u) from rfl,
        map_smul, huv, smul_smul, inv_mul_cancel₀ hmu, one_smul]
    exact hmem
  refine ⟨humem, ?_⟩
  -- the shifted operator scales the eigenvector by `mu⁻¹`
  have hRmu : R (mu⁻¹ • u) = u := by
    rw [map_smul, huv, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  have hshift : beamShiftedFormData.shiftedOperator ⟨u, humem⟩
      = mu⁻¹ • u := by
    have happ := Abstract.inversePartialMap_apply_R R
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective (mu⁻¹ • u)
    have hsub : (⟨R (mu⁻¹ • u), LinearMap.mem_range_self _ _⟩ :
        beamShiftedFormData.shiftedOperator.domain) = ⟨u, humem⟩ := Subtype.ext hRmu
    exact (congrArg beamShiftedFormData.shiftedOperator hsub).symm.trans happ
  have h : beamOperator ⟨u, humem⟩
      = beamShiftedFormData.shiftedOperator ⟨u, humem⟩ - u :=
    beamShiftedFormData.beamOperator_apply _
  rw [h, hshift, sub_smul, one_smul]

/-- A fixed vector of the variational resolvent is affine: `1` is the resolvent eigenvalue
that corresponds to the operator's zero mode. -/
theorem exists_affine_of_beamResolvent_eq_self {u : BeamL2}
    (huv : beamCoerciveFormData.resolvent u = u) :
    ∃ a b : ℂ, u = affineLp a b := by
  obtain ⟨humem, hbeam⟩ :=
    exists_beamOperator_apply_of_beamResolvent_smul (mu := 1) one_ne_zero
      (by rw [huv, one_smul])
  refine exists_affine_of_beamOperator_eq_zero (x := ⟨u, humem⟩) ?_
  rw [hbeam, inv_one, sub_self, zero_smul]

/-- Classification of the nonzero eigenvalues of the variational resolvent: `1` (from the
affine kernel side) or `(1+β⁴)⁻¹` for a characteristic root `β`. -/
theorem beamResolvent_eigenvalue_classify {mu : ℂ} (hmu : mu ≠ 0)
    {u : BeamL2} (hu0 : u ≠ 0)
    (huv : beamCoerciveFormData.resolvent u = mu • u) :
    mu = 1 ∨ ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0
      ∧ mu = (((1 + beta ^ 4)⁻¹ : ℝ) : ℂ) := by
  have hN : ((‖u‖ : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu0))
  -- the beam operator has eigenvalue `mu⁻¹ - 1`
  obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu huv
  -- the eigenvalue is real
  have hL : ⟪beamOperator ⟨u, humem⟩, u⟫_ℂ
      = (starRingEnd ℂ) (mu⁻¹ - 1) * ((‖u‖ : ℂ)) ^ 2 := by
    rw [hbeam, inner_smul_left]
    congr 1
    exact inner_self_eq_norm_sq_to_K u
  have hRt : ⟪u, beamOperator ⟨u, humem⟩⟫_ℂ
      = (mu⁻¹ - 1) * ((‖u‖ : ℂ)) ^ 2 := by
    rw [hbeam, inner_smul_right]
    congr 1
    exact inner_self_eq_norm_sq_to_K u
  have hsymm : ⟪beamOperator ⟨u, humem⟩, u⟫_ℂ
      = ⟪u, beamOperator ⟨u, humem⟩⟫_ℂ :=
    (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint beamOperator_isSelfAdjoint)
      ⟨u, humem⟩ ⟨u, humem⟩
  have hreal : (starRingEnd ℂ) (mu⁻¹ - 1) = mu⁻¹ - 1 := by
    have hchain : (starRingEnd ℂ) (mu⁻¹ - 1) * ((‖u‖ : ℂ)) ^ 2
        = (mu⁻¹ - 1) * ((‖u‖ : ℂ)) ^ 2 := hL.symm.trans (hsymm.trans hRt)
    exact mul_right_cancel₀ hN hchain
  set nu : ℝ := (mu⁻¹ - 1).re with hnu
  have hmunu : mu⁻¹ - 1 = (nu : ℂ) := by
    rw [hnu]
    exact (Complex.conj_eq_iff_re.mp hreal).symm
  have hnu_nonneg : 0 ≤ nu := by
    have hpos := beamOperator_nonneg ⟨u, humem⟩
    have hval : ⟪beamOperator ⟨u, humem⟩, u⟫_ℂ
        = ((nu * ‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [hL, hmunu, Complex.conj_ofReal]
      push_cast
      ring
    rw [hval] at hpos
    have hre : RCLike.re (((nu * ‖u‖ ^ 2 : ℝ) : ℂ)) = nu * ‖u‖ ^ 2 :=
      Complex.ofReal_re _
    rw [hre] at hpos
    have hn2 : (0 : ℝ) < ‖u‖ ^ 2 := by
      have : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
      positivity
    nlinarith
  rcases eq_or_lt_of_le hnu_nonneg with hzero | hposnu
  · -- `nu = 0` gives `mu = 1`
    left
    have h1 : mu⁻¹ = 1 := by
      have h := hmunu
      rw [← hzero] at h
      push_cast at h
      linear_combination h
    exact inv_eq_one.mp h1
  · -- `nu > 0` is a genuine positive eigenvalue: classify it
    right
    have heig : beamOperator ⟨u, humem⟩ = ((nu : ℝ) : ℂ) • u := by
      rw [hbeam, hmunu]
    obtain ⟨beta, hβ, hchar, hnueq⟩ :=
      exists_characteristic_of_eigen hposnu (x := ⟨u, humem⟩) hu0 heig
    refine ⟨beta, hβ, hchar, ?_⟩
    have hmuinv : mu⁻¹ = ((1 + beta ^ 4 : ℝ) : ℂ) := by
      have := hmunu
      rw [hnueq] at this
      push_cast at this ⊢
      linear_combination this
    rw [show ((((1 + beta ^ 4)⁻¹ : ℝ)) : ℂ) = (((1 + beta ^ 4 : ℝ) : ℂ))⁻¹ from by
      push_cast; ring, ← hmuinv, inv_inv]

/-- **Every real spectral point of the free beam is an eigenvalue.**  The free beam has no
continuous or residual real spectrum at all: if `lam` is in `TauCeti.LinearPMap.realSpectrum beamOperator` then
`B x = lam x` for some nonzero `x` in the domain.

This is the Fredholm alternative for the compact variational resolvent, run in the direction
that produces the eigenvector rather than in the direction that produces a containment.  If
`(1 + lam)⁻¹` is *not* an eigenvalue of the resolvent it lies in the resolvent set, and
rescaling turns the inverse of `(1+lam)⁻¹ - R` into a bounded two-sided inverse of `B - lam`,
contradicting `lam ∈ realSpectrum`; if it *is* an eigenvalue, then
`exists_beamOperator_apply_of_beamResolvent_smul` inverts it to an eigenvector of `B` for
`((1+lam)⁻¹)⁻¹ - 1 = lam`. -/
theorem exists_eigenvector_of_mem_realSpectrum_beamOperator {lam : ℝ}
    (hlam : lam ∈ TauCeti.LinearPMap.realSpectrum beamOperator) :
    ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
      beamOperator x = (lam : ℂ) • (x : BeamL2) := by
  by_contra hcon
  push Not at hcon
  set R := beamCoerciveFormData.resolvent with hRdef
  set c : ℂ := 1 + (lam : ℂ) with hcdef
  -- the shift operator `1 - c R` is invertible
  have hunit : IsUnit ((1 : BeamL2 →L[ℂ] BeamL2) - c • R) := by
    by_cases hc : c = 0
    · rw [hc, zero_smul, sub_zero]
      exact isUnit_one
    · have hmu : c⁻¹ ≠ 0 := inv_ne_zero hc
      rcases isCompactOperator_beamResolvent.hasEigenvalue_or_mem_resolventSet hmu with
        hev | hres
      · -- an eigenvalue at `c⁻¹` inverts to an eigenvector of `B` for `lam`
        exfalso
        obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
        have hveq : R v = c⁻¹ • v := by
          have hv := hvmem
          simp only [Module.End.mem_genEigenspace_one] at hv
          exact hv
        obtain ⟨hvdom, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu hveq
        have hcc : c⁻¹⁻¹ - 1 = (lam : ℂ) := by
          rw [inv_inv, hcdef]
          ring
        refine hcon ⟨v, hvdom⟩ hv0 ?_
        rw [← hcc]
        exact hbeam
      · -- otherwise `c⁻¹` is in the resolvent set, and we rescale
        have hres' := spectrum.mem_resolventSet_iff.mp hres
        have hkey : (1 : BeamL2 →L[ℂ] BeamL2) - c • R
            = c • (algebraMap ℂ (BeamL2 →L[ℂ] BeamL2) c⁻¹ - R) := by
          rw [smul_sub]
          congr 1
          rw [Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]
        rw [hkey]
        have hcu : IsUnit (algebraMap ℂ (BeamL2 →L[ℂ] BeamL2) c) :=
          (IsUnit.map _ (isUnit_iff_ne_zero.mpr hc))
        have := hcu.mul hres'
        rwa [show algebraMap ℂ (BeamL2 →L[ℂ] BeamL2) c
              * (algebraMap ℂ (BeamL2 →L[ℂ] BeamL2) c⁻¹ - R)
            = c • (algebraMap ℂ (BeamL2 →L[ℂ] BeamL2) c⁻¹ - R) from by
          rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]] at this
  -- assemble the two-sided inverse of `B - lam`
  obtain ⟨U, hU⟩ := hunit
  set S : BeamL2 →L[ℂ] BeamL2 := ↑U⁻¹ with hSdef
  have hcommU : Commute R ↑U := by
    rw [hU]
    change R * ((1 : BeamL2 →L[ℂ] BeamL2) - c • R)
      = ((1 : BeamL2 →L[ℂ] BeamL2) - c • R) * R
    rw [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  have hcommS : Commute R S := hcommU.units_inv_right
  have hSU : S * ↑U = 1 := U.inv_mul
  have hUS : (↑U : BeamL2 →L[ℂ] BeamL2) * S = 1 := U.mul_inv
  refine hlam ⟨R * S, ?_, ?_⟩
  · -- left inverse on the domain
    intro x
    have hxdom : (x : BeamL2) ∈ beamOperator.domain := x.2
    have hz := Abstract.R_inversePartialMap_apply R
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective x
    set z : BeamL2 := beamShiftedFormData.shiftedOperator x with hzdef
    have hRz : R z = (x : BeamL2) := hz
    have hBx : beamOperator x - ((lam : ℝ) : ℂ) • (x : BeamL2)
        = (↑U : BeamL2 →L[ℂ] BeamL2) z := by
      have h1 : beamOperator x
          = beamShiftedFormData.shiftedOperator x - (x : BeamL2) :=
        beamShiftedFormData.beamOperator_apply x
      have hUz : ((1 : BeamL2 →L[ℂ] BeamL2) - c • R) z = z - c • (x : BeamL2) := by
        rw [sub_apply]
        rw [show ((1 : BeamL2 →L[ℂ] BeamL2)) z = z from rfl,
          show (c • R) z = c • (R z) from rfl, hRz]
      rw [h1, hU, hUz, hcdef]
      rw [add_smul, one_smul]
      abel
    calc (R * S) (beamOperator x - ((lam : ℝ) : ℂ) • (x : BeamL2))
        = (R * S) ((↑U : BeamL2 →L[ℂ] BeamL2) z) := congrArg (R * S) hBx
      _ = R ((S * ↑U) z) := rfl
      _ = R z := by rw [hSU]; rfl
      _ = (x : BeamL2) := hRz
  · -- right inverse
    intro y
    have hmem : (R * S) y ∈ beamOperator.domain := by
      have : (R * S) y = R (S y) := rfl
      rw [this]
      exact LinearMap.mem_range_self _ _
    refine ⟨hmem, ?_⟩
    have hshifted : beamShiftedFormData.shiftedOperator ⟨(R * S) y, hmem⟩
        = S y := by
      have happ := Abstract.inversePartialMap_apply_R R
        beamCoerciveFormData.resolvent_isSelfAdjoint
        beamCoerciveFormData.resolvent_injective (S y)
      have hsub : (⟨R (S y), LinearMap.mem_range_self _ _⟩ :
          beamShiftedFormData.shiftedOperator.domain) = ⟨(R * S) y, hmem⟩ :=
        Subtype.ext rfl
      exact (congrArg beamShiftedFormData.shiftedOperator hsub).symm.trans happ
    have h1 : beamOperator ⟨(R * S) y, hmem⟩
        = beamShiftedFormData.shiftedOperator ⟨(R * S) y, hmem⟩
          - (R * S) y :=
      beamShiftedFormData.beamOperator_apply _
    have hfinal : S y - (R * S) y - ((lam : ℝ) : ℂ) • (R * S) y
        = ((↑U : BeamL2 →L[ℂ] BeamL2) * S) y := by
      rw [hU]
      rw [show (((1 : BeamL2 →L[ℂ] BeamL2) - c • R) * S) y
          = S y - c • (R (S y)) from by
        rw [sub_mul, one_mul]
        rfl]
      rw [show ((R * S) y : BeamL2) = R (S y) from rfl, hcdef]
      rw [add_smul, one_smul]
      abel
    calc beamOperator ⟨(R * S) y, hmem⟩
          - ((lam : ℝ) : ℂ) • ((R * S) y)
        = beamShiftedFormData.shiftedOperator ⟨(R * S) y, hmem⟩
            - (R * S) y - ((lam : ℝ) : ℂ) • ((R * S) y) := by rw [h1]
      _ = S y - (R * S) y - ((lam : ℝ) : ℂ) • (R * S) y := by rw [hshifted]
      _ = ((↑U : BeamL2 →L[ℂ] BeamL2) * S) y := hfinal
      _ = y := by rw [hUS]; rfl

/-- **The real spectrum of the free-beam operator**: contained in `{0}` together with the
fourth powers of the characteristic roots.  Every spectral point is now an eigenvalue
(`exists_eigenvector_of_mem_realSpectrum_beamOperator`), it is nonnegative because the
operator is, and a positive one carries a characteristic root. -/
theorem realSpectrum_beamOperator_subset :
    TauCeti.LinearPMap.realSpectrum beamOperator
      ⊆ {0} ∪ {lam : ℝ | ∃ beta : ℝ,
          0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4} := by
  intro lam hlam
  obtain ⟨x, hx0, heig⟩ := exists_eigenvector_of_mem_realSpectrum_beamOperator hlam
  rcases eq_or_lt_of_le (nonneg_of_beamOperator_eigen hx0 heig) with h0 | hpos
  · exact Or.inl (Set.mem_singleton_iff.mpr h0.symm)
  · exact Or.inr (exists_characteristic_of_eigen hpos hx0 heig)

/-- **The spectral gap of the free beam**: the real spectrum lies in `{0} ∪ (500, ∞)`.
This is Davis--Kahan 1970 Section 9's `α₃ > 500` — including that the whole positive
spectrum, not just the third eigenvalue, clears the bound — proved for the genuine
self-adjoint fourth-derivative realization. -/
theorem realSpectrum_beamOperator_subset_gap :
    TauCeti.LinearPMap.realSpectrum beamOperator ⊆ ({0} : Set ℝ) ∪ Set.Ioi 500 := by
  intro lam hlam
  rcases realSpectrum_beamOperator_subset hlam with h0 | ⟨beta, hβ, hchar, hlameq⟩
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Set.mem_Ioi, hlameq]
    exact Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero hβ hchar

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
