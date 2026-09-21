/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrumReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExactData
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.TrialSubspace
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.RadonNikodymL2
import Mathlib.Tactic

/-! # Beam Trial Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real Section 9 trial space and perturbation

This file realizes the finite Rayleigh--Ritz data of Davis--Kahan Section 9 directly on the
paper's real `L²(0,1)` space.  The affine trial plane is the zero eigenspace of the real
free-beam operator, multiplication by `epsilon t` is a bounded self-adjoint perturbation, and
the printed Ritz and residual matrices are literal `L²` inner-product matrices.
-/

open MeasureTheory
open TauCeti.DavisKahan
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real


noncomputable section

/-! ## Exact unit-interval moments -/

/-- Exact real monomial moments on `(0,1]`. -/
theorem integral_unitIocMeasure_pow (n : ℕ) :
    ∫ t : ℝ, t ^ n ∂unitIocMeasure = 1 / (n + 1 : ℝ) := by
  rw [integral_unitIocMeasure_eq_intervalIntegral, integral_pow]
  norm_num

/-! ## The affine trial plane -/

/-- The paper's two-dimensional affine trial subspace. -/
def beamTrial : Submodule ℝ BeamL2 := Submodule.span ℝ {beamOneLp, beamIdLp}

/-- Membership in the beam trial subspace. -/
theorem mem_beamTrial_iff {x : BeamL2} :
    x ∈ beamTrial ↔ ∃ a b : ℝ, x = affineLp a b := by
  rw [beamTrial, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩

/-- Every affine function lies in the beam trial subspace. -/
theorem affineLp_mem_beamTrial (a b : ℝ) : affineLp a b ∈ beamTrial :=
  mem_beamTrial_iff.2 ⟨a, b, rfl⟩

/-- The trial subspace is spanned by two functions, so it is finite
dimensional. -/
instance : FiniteDimensional ℝ beamTrial := by
  rw [beamTrial]
  exact FiniteDimensional.span_of_finite ℝ (Set.toFinite _)

/-- A finite-dimensional subspace is complete. -/
instance : CompleteSpace beamTrial := FiniteDimensional.complete ℝ _

/-- The affine trial plane is contained in the beam-operator domain. -/
theorem beamTrial_le_domain {x : BeamL2} (hx : x ∈ beamTrial) :
    x ∈ beamOperator.domain := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose

/-- The free beam annihilates the affine trial plane. -/
theorem beamOperator_apply_trial {x : BeamL2} (hx : x ∈ beamTrial)
    (h : x ∈ beamOperator.domain) :
    beamOperator ⟨x, h⟩ = 0 := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose_spec

/-- Isometric inclusion of the trial plane. -/
def beamTrialIncl : beamTrial →L[ℝ] BeamL2 := beamTrial.subtypeL

/-- Evaluating the trial subspace's inclusion. -/
@[simp] theorem beamTrialIncl_apply (x : beamTrial) : beamTrialIncl x = (x : BeamL2) := rfl

/-! ## Multiplication by `epsilon t` -/

/-- Globally bounded extension of the unit-interval coordinate. -/
def beamClamp (t : ℝ) : ℝ := max 0 (min t 1)

/-- The clamping symbol is measurable. -/
theorem measurable_beamClamp : Measurable beamClamp :=
  measurable_const.max (measurable_id.min measurable_const)

/-- The clamping symbol is nonnegative. -/
theorem beamClamp_nonneg (t : ℝ) : 0 ≤ beamClamp t := le_max_left _ _

/-- The clamping symbol is bounded by one. -/
theorem beamClamp_le_one (t : ℝ) : beamClamp t ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

/-- The clamping symbol is the identity below the threshold. -/
theorem beamClamp_eq_self {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : beamClamp t = t := by
  rw [beamClamp, min_eq_left ht.2, max_eq_right ht.1.le]

/-- Symbol of the real Section 9 perturbation. -/
def beamSymbol (ε : ℝ) (t : ℝ) : ℝ := ε * beamClamp t

/-- The beam symbol is measurable. -/
theorem measurable_beamSymbol (ε : ℝ) : Measurable (beamSymbol ε) :=
  measurable_const.mul measurable_beamClamp

/-- The beam symbol is bounded by the clamping threshold. -/
theorem norm_beamSymbol_le (ε : ℝ) (t : ℝ) : ‖beamSymbol ε t‖ ≤ |ε| := by
  rw [beamSymbol, Real.norm_eq_abs, abs_mul, abs_of_nonneg (beamClamp_nonneg t)]
  calc
    |ε| * beamClamp t ≤ |ε| * 1 :=
      mul_le_mul_of_nonneg_left (beamClamp_le_one t) (abs_nonneg ε)
    _ = |ε| := mul_one _

/-- A bounded real symbol multiplies real `L²` into itself.  This is kept local because the
reusable `TauCeti.mulLp` API is intentionally the complex multiplication model. -/
theorem memLp_two_mul_real {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ t, ‖g t‖ ≤ C) (F : BeamL2) :
    MemLp (fun t => g t * F t) 2 unitIocMeasure := by
  refine MemLp.mono' ((Lp.memLp F).norm.const_mul C)
    (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)) ?_
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hgC t) (norm_nonneg _)

/-- `L²` seminorm estimate for multiplication by a bounded real symbol. -/
theorem eLpNorm_two_mul_real_le {g : ℝ → ℝ} {C : ℝ} (hgC : ∀ t, ‖g t‖ ≤ C)
    (f : ℝ → ℝ) :
    eLpNorm (fun t => g t * f t) 2 unitIocMeasure ≤
      ENNReal.ofReal |C| * eLpNorm f 2 unitIocMeasure := by
  have hle : eLpNorm (fun t => g t * f t) 2 unitIocMeasure ≤
      eLpNorm ((|C| : ℝ) • f) 2 unitIocMeasure := by
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hgC t).trans (le_abs_self C)) (abs_nonneg (f t))
  rw [eLpNorm_const_smul] at hle
  refine hle.trans_eq ?_
  congr 1
  rw [← ofReal_norm, Real.norm_eq_abs, abs_abs]

/-- `L²` norm estimate for multiplication by a bounded real symbol. -/
theorem norm_toLp_mul_real_le {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ t, ‖g t‖ ≤ C) (F : BeamL2) :
    ‖MemLp.toLp (fun t => g t * F t) (memLp_two_mul_real hg hgC F)‖ ≤ |C| * ‖F‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_ofReal (abs_nonneg C), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ (eLpNorm_two_mul_real_le hgC _)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)

/-- Specialized norm bound for the Section 9 real multiplier. -/
theorem norm_toLp_beamSymbol_le (ε : ℝ) (F : BeamL2) :
    ‖MemLp.toLp (fun t => beamSymbol ε t * F t)
        (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) F)‖
      ≤ |ε| * ‖F‖ := by
  simpa only [abs_abs] using
    (norm_toLp_mul_real_le (measurable_beamSymbol ε) (norm_beamSymbol_le ε) F)

/-- Multiplication by `epsilon t` on real `L²(0,1)`. -/
def beamPerturbation (ε : ℝ) : BeamL2 →L[ℝ] BeamL2 :=
  LinearMap.mkContinuous
    { toFun := fun F => MemLp.toLp (fun t => beamSymbol ε t * F t)
        (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) F)
      map_add' := fun F G => by
        rw [← MemLp.toLp_add
          (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) F)
          (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) G)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_add F G] with t ht
        simp only [Pi.add_apply, ht]
        ring
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c
          (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) F)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_smul c F] with t ht
        simp only [Pi.smul_apply, ht, smul_eq_mul]
        ring }
    |ε| (norm_toLp_beamSymbol_le ε)

/-- Multiplication by `epsilon t`, unfolded to the defining `L²` class. -/
theorem beamPerturbation_apply (ε : ℝ) (x : BeamL2) :
    beamPerturbation ε x =
      MemLp.toLp (fun t => beamSymbol ε t * x t)
        (memLp_two_mul_real (measurable_beamSymbol ε) (norm_beamSymbol_le ε) x) := rfl

/-- The beam perturbation, as a function. -/
theorem coeFn_beamPerturbation (ε : ℝ) (x : BeamL2) :
    (beamPerturbation ε x : ℝ → ℝ) =ᵐ[unitIocMeasure]
      fun t => (ε * t) * (x : ℝ → ℝ) t := by
  have hmul : (beamPerturbation ε x : ℝ → ℝ) =ᵐ[unitIocMeasure]
      fun t => beamSymbol ε t * (x : ℝ → ℝ) t := by
    rw [beamPerturbation_apply]
    exact MemLp.coeFn_toLp _
  filter_upwards [hmul, ae_mem_unitIocMeasure] with t ht hmem
  rw [ht, beamSymbol, beamClamp_eq_self hmem]

/-- The beam perturbation is bounded in norm by the clamping threshold. -/
theorem norm_beamPerturbation_le (ε : ℝ) : ‖beamPerturbation ε‖ ≤ |ε| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg ε) ?_
  intro F
  rw [beamPerturbation_apply]
  exact norm_toLp_beamSymbol_le ε F

/-- The multiplication perturbation is self-adjoint. -/
theorem beamPerturbation_isSelfAdjoint (ε : ℝ) :
    (beamPerturbation ε).IsSymmetric := by
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_beamPerturbation ε x, coeFn_beamPerturbation ε y] with t hx hy
  simp only [RCLike.inner_apply, ContinuousLinearMap.coe_coe, hx, hy, map_mul,
    starRingEnd_apply, star_trivial]
  ring

/-- The perturbed real free beam `A + H`. -/
def beamPerturbed (ε : ℝ) : BeamL2 →ₗ.[ℝ] BeamL2 :=
  TauCeti.LinearPMap.addBounded beamOperator (beamPerturbation ε)

/-- The perturbed real free beam is self-adjoint. -/
theorem beamPerturbed_isSelfAdjoint (ε : ℝ) : _root_.IsSelfAdjoint (beamPerturbed ε) :=
  addBounded_isSelfAdjoint beamOperator beamOperator_isSelfAdjoint
    (beamPerturbation ε) (beamPerturbation_isSelfAdjoint ε)

/-! ## Continuous representatives and affine moments -/

/-- Inner product of continuous real representatives. -/
theorem inner_contToLp (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h) :
    ⟪contToLp g hg, contToLp h hh⟫_ℝ = ∫ t, g t * h t ∂unitIocMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_contToLp g hg, coeFn_contToLp h hh] with t hgt hht
  rw [RCLike.inner_apply, hgt, hht]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Squared norm of a continuous real representative. -/
theorem norm_sq_contToLp (g : ℝ → ℝ) (hg : Continuous g) {r : ℝ}
    (h : ∫ t, g t * g t ∂unitIocMeasure = r) :
    ‖contToLp g hg‖ ^ 2 = r := by
  have hself := inner_self_eq_norm_sq (𝕜 := ℝ) (contToLp g hg)
  rw [inner_contToLp g g hg hg, h] at hself
  exact hself.symm

/-- An affine `L²` element is the continuous function `a + bt`. -/
theorem affineLp_eq_contToLp (a b : ℝ) :
    affineLp a b = contToLp (fun t => a + b * t) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp,
    coeFn_beamOneLp, coeFn_beamIdLp,
    coeFn_contToLp (fun t => a + b * t) (by fun_prop)]
      with t hadd hsa hsb h1 hT hc
  rw [show (affineLp a b : ℝ → ℝ) t =
      ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℝ) t from rfl,
    hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
    smul_eq_mul, smul_eq_mul, hc]
  ring

/-- Multiplication by `epsilon t` on an affine element. -/
theorem beamPerturbation_affineLp (ε a b : ℝ) :
    beamPerturbation ε (affineLp a b) =
      contToLp (fun t => (ε * t) * (a + b * t)) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_beamPerturbation ε (affineLp a b),
    coeFn_contToLp (fun t => (ε * t) * (a + b * t)) (by fun_prop),
    coeFn_contToLp (fun t => a + b * t) (by fun_prop)] with t hp hc ha
  rw [hp, hc, affineLp_eq_contToLp, ha]

/-- Continuous functions are integrable against the finite unit-interval measure. -/
theorem integrable_contFn (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable g unitIocMeasure :=
  (integrable_coeFn (contToLp g hg)).congr (coeFn_contToLp g hg)

/-- Integral of a real constant on `(0,1]`. -/
theorem integral_unitIocMeasure_const (c : ℝ) :
    ∫ _ : ℝ, c ∂unitIocMeasure = c := by
  rw [MeasureTheory.integral_const]
  have huniv : unitIocMeasure.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ]
    simp
  rw [huniv, one_smul]

/-- First real monomial moment on `(0,1]`. -/
theorem integral_unitIocMeasure_id :
    ∫ t : ℝ, t ∂unitIocMeasure = (1 : ℝ) / 2 := by
  have h := integral_unitIocMeasure_pow 1
  simp only [pow_one, one_div] at h ⊢
  norm_num at h ⊢
  exact h

/-- Exact integral of a real quadratic. -/
theorem integral_unitIocMeasure_quadratic (c0 c1 c2 : ℝ) :
    ∫ t, (c0 + c1 * t + c2 * t ^ 2) ∂unitIocMeasure =
      c0 + c1 / 2 + c2 / 3 := by
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * t) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * t) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * t ^ 2) unitIocMeasure := integrable_contFn _ (by fun_prop)
  rw [integral_add hi01 hi2, integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_const, integral_unitIocMeasure_id, integral_unitIocMeasure_pow 2]
  norm_num
  ring

/-- Exact integral of a real quartic. -/
theorem integral_unitIocMeasure_quartic (c0 c1 c2 c3 c4 : ℝ) :
    ∫ t, (c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4) ∂unitIocMeasure =
      c0 + c1 / 2 + c2 / 3 + c3 / 4 + c4 / 5 := by
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * t) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * t ^ 2) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi3 : Integrable (fun t : ℝ => c3 * t ^ 3) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi4 : Integrable (fun t : ℝ => c4 * t ^ 4) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * t) unitIocMeasure := integrable_contFn _ (by fun_prop)
  have hi012 : Integrable (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0123 : Integrable (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3)
      unitIocMeasure := integrable_contFn _ (by fun_prop)
  rw [integral_add hi0123 hi4, integral_add hi012 hi3, integral_add hi01 hi2,
    integral_add hi0 hi1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_const, integral_unitIocMeasure_id, integral_unitIocMeasure_pow 2,
    integral_unitIocMeasure_pow 3, integral_unitIocMeasure_pow 4]
  norm_num
  ring

/-- Inner product of two real affine elements. -/
theorem inner_affineLp (a b c d : ℝ) :
    ⟪affineLp a b, affineLp c d⟫_ℝ =
      a * c + (a * d + b * c) / 2 + b * d / 3 := by
  rw [affineLp_eq_contToLp, affineLp_eq_contToLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (a + b * t) * (c + d * t) = a * c + (a * d + b * c) * t + (b * d) * t ^ 2 := by
    intro t
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quadratic]

/-- `t`-weighted affine inner product. -/
theorem inner_affineLp_beamPerturbation (ε a b c d : ℝ) :
    ⟪affineLp a b, beamPerturbation ε (affineLp c d)⟫_ℝ =
      ε * (a * c / 2 + (a * d + b * c) / 3 + b * d / 4) := by
  rw [affineLp_eq_contToLp, beamPerturbation_affineLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (a + b * t) * ((ε * t) * (c + d * t)) =
        0 + (ε * (a * c)) * t + (ε * (a * d + b * c)) * t ^ 2 +
          (ε * (b * d)) * t ^ 3 + 0 * t ^ 4 := by
    intro t
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- `t²`-weighted affine inner product. -/
theorem inner_beamPerturbation_affineLp (ε a b c d : ℝ) :
    ⟪beamPerturbation ε (affineLp a b), beamPerturbation ε (affineLp c d)⟫_ℝ =
      ε ^ 2 * (a * c / 3 + (a * d + b * c) / 4 + b * d / 5) := by
  rw [beamPerturbation_affineLp, beamPerturbation_affineLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      ((ε * t) * (a + b * t)) * ((ε * t) * (c + d * t)) =
        0 + 0 * t + (ε ^ 2 * (a * c)) * t ^ 2 +
          (ε ^ 2 * (a * d + b * c)) * t ^ 3 + (ε ^ 2 * (b * d)) * t ^ 4 := by
    intro t
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- Exact squared norm of a real affine element. -/
theorem norm_affineLp_sq (a b : ℝ) :
    ‖affineLp a b‖ ^ 2 = a ^ 2 + a * b + b ^ 2 / 3 := by
  rw [← real_inner_self_eq_norm_sq, inner_affineLp]
  ring

/-- The constant zero mode is nonzero. -/
theorem beamOneLp_ne_zero : beamOneLp ≠ 0 := by
  intro hzero
  have h := norm_affineLp_sq 1 0
  rw [show affineLp 1 0 = beamOneLp from by simp [affineLp], hzero, norm_zero] at h
  norm_num at h

/-! ## Centered affine basis and matrices -/

/-- Real `L²` realization of the source centered-affine coordinates. -/
def centeredAffineLp (p : DavisKahan1970.Section9.CenteredAffine) : BeamL2 :=
  affineLp (p.constant - p.centered) (2 * p.centered)

/-- The centred affine function lies in the beam trial subspace. -/
theorem centeredAffineLp_mem_beamTrial (p : DavisKahan1970.Section9.CenteredAffine) :
    centeredAffineLp p ∈ beamTrial := affineLp_mem_beamTrial _ _

/-- Inner product against the centred affine function. -/
theorem inner_centeredAffineLp (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, centeredAffineLp q⟫_ℝ =
      DavisKahan1970.Section9.CenteredAffine.inner p q := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp,
    DavisKahan1970.Section9.CenteredAffine.inner]
  ring

/-- Inner product against a multiple of the centred affine function. -/
theorem inner_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, beamPerturbation ε (centeredAffineLp q)⟫_ℝ =
      ε * DavisKahan1970.Section9.CenteredAffine.tInner p q := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp_beamPerturbation,
    DavisKahan1970.Section9.CenteredAffine.tInner]
  ring

/-- Inner product of two multiples of the centred affine function. -/
theorem inner_mul_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪beamPerturbation ε (centeredAffineLp p),
      beamPerturbation ε (centeredAffineLp q)⟫_ℝ =
      ε ^ 2 * DavisKahan1970.Section9.CenteredAffine.tSqInner p q := by
  rw [centeredAffineLp, centeredAffineLp, inner_beamPerturbation_affineLp,
    DavisKahan1970.Section9.CenteredAffine.tSqInner]
  ring

open DavisKahan1970.Section9 in
/-- The paper's two real trial functions are orthonormal zero modes. -/
theorem beamTrial_orthonormal :
    ‖centeredAffineLp trialOne‖ ^ 2 = 1 ∧
      ‖centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
      ⟪centeredAffineLp trialOne, centeredAffineLp trialTwo⟫_ℝ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← real_inner_self_eq_norm_sq, inner_centeredAffineLp, trialOne_norm_sq]
  · rw [← real_inner_self_eq_norm_sq, inner_centeredAffineLp, trialTwo_norm_sq]
  · rw [inner_centeredAffineLp, trialOne_inner_trialTwo]

/-- The first printed affine trial vector, regarded as a vector of the trial subspace. -/
def beamTrialVecOne : beamTrial :=
  ⟨centeredAffineLp DavisKahan1970.Section9.trialOne,
    centeredAffineLp_mem_beamTrial DavisKahan1970.Section9.trialOne⟩

/-- The second printed affine trial vector, regarded as a vector of the trial subspace. -/
def beamTrialVecTwo : beamTrial :=
  ⟨centeredAffineLp DavisKahan1970.Section9.trialTwo,
    centeredAffineLp_mem_beamTrial DavisKahan1970.Section9.trialTwo⟩

/-- The paper's affine zero-mode trial space is exactly two-dimensional. -/
theorem finrank_beamTrial : Module.finrank ℝ beamTrial = 2 := by
  classical
  obtain ⟨hnorm1, hnorm2, h12ambient⟩ := beamTrial_orthonormal
  have h1 : ⟪beamTrialVecOne, beamTrialVecOne⟫_ℝ = 1 := by
    show ⟪centeredAffineLp DavisKahan1970.Section9.trialOne,
      centeredAffineLp DavisKahan1970.Section9.trialOne⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, hnorm1]
  have h2 : ⟪beamTrialVecTwo, beamTrialVecTwo⟫_ℝ = 1 := by
    show ⟪centeredAffineLp DavisKahan1970.Section9.trialTwo,
      centeredAffineLp DavisKahan1970.Section9.trialTwo⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, hnorm2]
  have h12 : ⟪beamTrialVecOne, beamTrialVecTwo⟫_ℝ = 0 := by
    show ⟪centeredAffineLp DavisKahan1970.Section9.trialOne,
      centeredAffineLp DavisKahan1970.Section9.trialTwo⟫_ℝ = 0
    exact h12ambient
  have h21 : ⟪beamTrialVecTwo, beamTrialVecOne⟫_ℝ = 0 := by
    rw [real_inner_comm, h12]
  have hne1 : beamTrialVecOne ≠ 0 := by
    intro hzero
    simp [hzero] at h1
  have hne2 : beamTrialVecTwo ≠ 0 := by
    intro hzero
    simp [hzero] at h2
  have hli : LinearIndependent ℝ ![beamTrialVecOne, beamTrialVecTwo] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have hA : α = 0 := by
      have h := congrArg (fun z => ⟪beamTrialVecOne, z⟫_ℝ) hαβ
      simpa [inner_add_right, inner_smul_right, h1, h12, hne1] using h
    have hB : β = 0 := by
      have h := congrArg (fun z => ⟪beamTrialVecTwo, z⟫_ℝ) hαβ
      simpa [inner_add_right, inner_smul_right, h2, h21, hne2] using h
    exact ⟨hA, hB⟩
  have hrange : Set.range ![beamTrialVecOne, beamTrialVecTwo] =
      ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial) := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  have hspan : Module.finrank ℝ
      (Submodule.span ℝ ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial)) = 2 := by
    rw [← hrange, finrank_span_eq_card hli]
    simp
  have hle : Module.finrank ℝ (beamTrial : Submodule ℝ BeamL2) ≤ 2 := by
    have hcard : Cardinal.mk ({beamOneLp, beamIdLp} : Set BeamL2) ≤ 2 := by
      refine le_trans Cardinal.mk_insert_le ?_
      rw [Cardinal.mk_singleton]
      exact le_of_eq one_add_one_eq_two
    have hrk : Module.rank ℝ (beamTrial : Submodule ℝ BeamL2) ≤ 2 :=
      le_trans (by rw [beamTrial]; exact rank_span_le _) hcard
    exact_mod_cast Module.finrank_le_of_rank_le hrk
  have hge : 2 ≤ Module.finrank ℝ (beamTrial : Submodule ℝ BeamL2) := by
    rw [← hspan]
    exact Submodule.finrank_le _
  omega

/-- The kernel of the real free-beam operator is exactly the affine trial plane. -/
theorem beamOperator_eq_zero_iff_mem_beamTrial {x : BeamL2}
    (h : x ∈ beamOperator.domain) :
    beamOperator ⟨x, h⟩ = 0 ↔ x ∈ beamTrial := by
  constructor
  · intro hzero
    obtain ⟨a, b, hab⟩ :=
      exists_affine_of_beamOperator_eq_zero (x := ⟨x, h⟩) hzero
    exact mem_beamTrial_iff.2 ⟨a, b, hab⟩
  · intro hx
    exact beamOperator_apply_trial hx h

open DavisKahan1970.Section9 in
/-- Equation (9.5): the real Ritz compression of multiplication by `epsilon t`. -/
theorem beamRitz_matrix (ε : ℝ) :
    ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialOne)⟫_ℝ =
        ritzLow ε ∧
      ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℝ = 0 ∧
      ⟪centeredAffineLp trialTwo, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℝ =
        ritzHigh ε := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialOne]
    rfl
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialTwo]
    norm_num
  · rw [inner_centeredAffineLp_mul, trialTwo_tInner_trialTwo]
    rfl

open DavisKahan1970.Section9 in
/-- Equation (9.1): the printed residual Gram matrix is the genuine real `L²` Gram matrix. -/
theorem beamResidualGram_matrix (ε : ℝ) :
    ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialOne)⟫_ℝ = (residualGram ε).a₀₀ ∧
      ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℝ = (residualGram ε).a₀₁ ∧
      ⟪beamPerturbation ε (centeredAffineLp trialTwo),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℝ = (residualGram ε).a₁₁ := by
  have hgram := initial_residual_gram_from_affine_moments ε
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_mul_centeredAffineLp_mul]
    exact congrArg SymmetricTwoByTwo.a₀₀ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    exact congrArg SymmetricTwoByTwo.a₀₁ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    exact congrArg SymmetricTwoByTwo.a₁₁ hgram

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
