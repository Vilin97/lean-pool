/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrum
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExactData
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.TrialSubspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RayleighRitz
import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MulLpAlgebra

/-! # Beam Section9 -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The Davis--Kahan Section 9 free-beam example, on the genuine operator

`BeamSpectrum` produced the self-adjoint fourth-derivative realization
`beamOperator`, identified its kernel as the affine plane, and proved the spectral
gap `realSpectrum ⊆ {0} ∪ (500, ∞)`.  This file assembles the remaining *finite*
data of the paper's numerical example around that operator:

* `beamTrial`, the two-dimensional affine trial subspace, is exactly the kernel;
* `beamPerturbation ε`, multiplication by `ε t`, is the paper's bounded perturbation,
  self-adjoint with norm at most `ε`;
* the exact `L²` moments of affine functions against `1`, `t` and `t²` — this is the
  "moments to integrals" identification that the Section 9 finite layer
  (`TrialSubspace.lean`) was written against;
* the residual norm bound `‖(ε t)|_trial‖ ≤ residualTopSingularValue ε`, whose
  constant is the square root of the top eigenvalue of the residual Gram matrix.

It also closes the existence half of the paper's spectral picture: the containment
proved in `BeamSpectrum` has no lower bound on the spectrum and is vacuously compatible
with there being no nonzero spectral point at all.  The centred quadratic mode
`t² - t + 1/6` is a nonzero vector orthogonal to the affine plane, so the compact
variational resolvent must have an eigenvalue other than `0` and `1`, and inverting that
relation exhibits a genuine eigenvalue of `beamOperator` above `500`.

## Main results

* `TauCeti.…FreeBeam.Model.beamOperator_apply_trial`: the trial space is annihilated.
* `TauCeti.…FreeBeam.Model.norm_beamPerturbation_comp_trialIncl_le`: the residual bound.
* `TauCeti.…FreeBeam.Model.exists_five_hundred_lt_mem_realSpectrum_beamOperator`:
  the positive real spectrum is nonempty.
-/

open MeasureTheory
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model


section

/-! ## Complex integrals on the unit interval -/

/-- The ambient measure integrates complex integrands as interval integrals. -/
theorem integral_unitIocMeasure_complex (f : ℝ → ℂ) :
    ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure_def]

/-- Exact monomial moments of the unit interval. -/
theorem integral_unitIocMeasure_pow (n : ℕ) :
    ∫ t, ((t : ℂ)) ^ n ∂unitIocMeasure = 1 / (n + 1) := by
  have hre : ∀ t : ℝ, ((t : ℂ)) ^ n = (((t ^ n : ℝ)) : ℂ) := by
    intro t
    push_cast
    ring
  simp only [hre]
  rw [integral_complex_ofReal, integral_unitIocMeasure_eq_intervalIntegral]
  rw [integral_pow]
  push_cast
  ring

/-! ## The affine trial subspace -/

/-- The two-dimensional affine trial subspace of the paper's numerical example. -/
noncomputable def beamTrial : Submodule ℂ BeamL2 := Submodule.span ℂ {beamOneLp, beamIdLp}

/-- Membership in the beam trial subspace. -/
theorem mem_beamTrial_iff {x : BeamL2} :
    x ∈ beamTrial ↔ ∃ a b : ℂ, x = affineLp a b := by
  rw [beamTrial, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩

/-- Every affine function lies in the beam trial subspace. -/
theorem affineLp_mem_beamTrial (a b : ℂ) : affineLp a b ∈ beamTrial :=
  mem_beamTrial_iff.2 ⟨a, b, rfl⟩

/-- The trial subspace is spanned by two functions, so it is finite
dimensional. -/
noncomputable instance : FiniteDimensional ℂ beamTrial := by
  rw [beamTrial]
  exact FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-- A finite-dimensional subspace is complete. -/
noncomputable instance : CompleteSpace beamTrial := FiniteDimensional.complete ℂ _

/-- The trial subspace lies in the operator's domain: it is the affine kernel
identified in `BeamSpectrum`. -/
theorem beamTrial_le_domain {x : BeamL2} (hx : x ∈ beamTrial) :
    x ∈ beamOperator.domain := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose

/-- The beam operator annihilates the trial subspace. -/
theorem beamOperator_apply_trial {x : BeamL2} (hx : x ∈ beamTrial)
    (h : x ∈ beamOperator.domain) :
    beamOperator ⟨x, h⟩ = 0 := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose_spec

/-- The isometric inclusion of the trial subspace. -/
noncomputable def beamTrialIncl : beamTrial →L[ℂ] BeamL2 := beamTrial.subtypeL

/-- Evaluating the trial subspace's inclusion. -/
@[simp] theorem beamTrialIncl_apply (x : beamTrial) :
    beamTrialIncl x = (x : BeamL2) := rfl

/-! ## The multiplication perturbation `ε t` -/

/-- The unit-interval coordinate, clamped so that the symbol is globally bounded. -/
noncomputable def beamClamp (t : ℝ) : ℝ := max 0 (min t 1)

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

/-- The symbol of the paper's perturbation: `ε` times the clamped coordinate. -/
noncomputable def beamSymbol (ε : ℝ) (t : ℝ) : ℂ := ((ε * beamClamp t : ℝ) : ℂ)

/-- The beam symbol is measurable. -/
theorem measurable_beamSymbol (ε : ℝ) : Measurable (beamSymbol ε) :=
  Complex.measurable_ofReal.comp (measurable_const.mul measurable_beamClamp)

/-- The beam symbol is bounded by the clamping threshold. -/
theorem norm_beamSymbol_le (ε : ℝ) (t : ℝ) : ‖beamSymbol ε t‖ ≤ |ε| := by
  rw [beamSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (beamClamp_nonneg t)]
  calc |ε| * beamClamp t ≤ |ε| * 1 :=
        mul_le_mul_of_nonneg_left (beamClamp_le_one t) (abs_nonneg ε)
    _ = |ε| := mul_one _

/-- **The Section 9 perturbation**: multiplication by `ε t` on `L²(0,1]`. -/
noncomputable def beamPerturbation (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  mulLp unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε)

/-- The beam perturbation, as a function. -/
theorem coeFn_beamPerturbation (ε : ℝ) (x : BeamL2) :
    (beamPerturbation ε x : ℝ → ℂ) =ᵐ[unitIocMeasure]
      fun t => ((ε * t : ℝ) : ℂ) * (x : ℝ → ℂ) t := by
  filter_upwards [coeFn_mulLp unitIocMeasure (measurable_beamSymbol ε)
    (norm_beamSymbol_le ε) x, ae_mem_unitIocMeasure] with t ht hmem
  rw [show (beamPerturbation ε x : ℝ → ℂ) t
    = (mulLp unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε) x :
        ℝ → ℂ) t from rfl, ht, beamSymbol, beamClamp_eq_self hmem]

/-- The beam perturbation is bounded in norm by the clamping threshold. -/
theorem norm_beamPerturbation_le (ε : ℝ) : ‖beamPerturbation ε‖ ≤ |ε| := by
  have := norm_mulLp_le unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε)
  simpa [beamPerturbation, abs_abs] using this

/-! ## Inner products of continuous representatives -/

/-- The `L²` inner product of two continuous representatives is the integral of the
pointwise product. -/
theorem inner_contToLp (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) :
    ⟪contToLp g hg, contToLp h hh⟫_ℂ
      = ∫ t, (starRingEnd ℂ) (g t) * h t ∂unitIocMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_contToLp g hg, coeFn_contToLp h hh] with t htg hth
  rw [htg, hth, RCLike.inner_apply]
  ring

/-- Read off the squared `L²` norm of a continuous representative from an explicit
value of its self-pairing integral. -/
theorem norm_sq_contToLp (g : ℝ → ℂ) (hg : Continuous g) {r : ℝ}
    (h : ∫ t, (starRingEnd ℂ) (g t) * g t ∂unitIocMeasure = (r : ℂ)) :
    ‖contToLp g hg‖ ^ 2 = r := by
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (contToLp g hg)
  rw [inner_contToLp g g hg hg, h] at hself
  have hcast : (((‖contToLp g hg‖ ^ 2 : ℝ)) : ℂ) = ((r : ℝ) : ℂ) := by
    push_cast
    exact hself.symm
  exact_mod_cast hcast

/-! ## Affine elements as continuous representatives -/

/-- Affine elements of the trial space are the continuous affine functions. -/
theorem affineLp_eq_contToLp (a b : ℂ) :
    affineLp a b = contToLp (fun t => a + b * t) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
    coeFn_beamIdLp, coeFn_contToLp (fun t => a + b * t) (by fun_prop)] with
    t hadd hsa hsb h1 hT hc
  rw [show (affineLp a b : ℝ → ℂ) t
    = ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t from rfl, hadd, hc]
  simp only [Pi.add_apply, hsa, hsb, Pi.smul_apply, smul_eq_mul, h1, hT]
  ring

/-- The perturbation of an affine element is the continuous function `ε t (a + b t)`. -/
theorem beamPerturbation_affineLp (ε : ℝ) (a b : ℂ) :
    beamPerturbation ε (affineLp a b)
      = contToLp (fun t => ((ε : ℂ) * t) * (a + b * t)) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_beamPerturbation ε (affineLp a b),
    coeFn_contToLp (fun t => ((ε : ℂ) * t) * (a + b * t)) (by fun_prop),
    coeFn_contToLp (fun t => a + b * t) (by fun_prop)] with t hp hc ha
  rw [hp, hc, affineLp_eq_contToLp, ha]
  push_cast
  ring

/-! ## The exact affine moments -/

/-- Continuous functions are integrable against the finite unit-interval measure. -/
theorem integrable_contFn (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable g unitIocMeasure :=
  (integrable_coeFn (contToLp g hg)).congr (coeFn_contToLp g hg)

/-- Exact monomial moments, in the normalized form the polynomial lemmas consume. -/
theorem integral_unitIocMeasure_coe : ∫ t : ℝ, (t : ℂ) ∂unitIocMeasure = 1 / 2 := by
  have h := integral_unitIocMeasure_pow 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h]
  norm_num

/-- `∫₀¹ t² = 1/3`. -/
theorem integral_unitIocMeasure_coe_sq :
    ∫ t : ℝ, (t : ℂ) ^ 2 ∂unitIocMeasure = 1 / 3 := by
  have h := integral_unitIocMeasure_pow 2
  rw [h]
  norm_num

/-- `∫₀¹ t³ = 1/4`. -/
theorem integral_unitIocMeasure_coe_cube :
    ∫ t : ℝ, (t : ℂ) ^ 3 ∂unitIocMeasure = 1 / 4 := by
  have h := integral_unitIocMeasure_pow 3
  rw [h]
  norm_num

/-- `∫₀¹ t⁴ = 1/5`. -/
theorem integral_unitIocMeasure_coe_four :
    ∫ t : ℝ, (t : ℂ) ^ 4 ∂unitIocMeasure = 1 / 5 := by
  have h := integral_unitIocMeasure_pow 4
  rw [h]
  norm_num

/-- Exact integral of a quadratic with complex coefficients. -/
theorem integral_unitIocMeasure_quadratic (c0 c1 c2 : ℂ) :
    ∫ t, (c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2) ∂unitIocMeasure
      = c0 + c1 / 2 + c2 / 3 := by
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  rw [integral_add hi01 hi2, integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_coe, integral_unitIocMeasure_coe_sq,
    MeasureTheory.integral_const]
  have huniv : unitIocMeasure.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ]
    simp
  rw [huniv, one_smul]
  ring

/-- Exact integral of a quartic with complex coefficients. -/
theorem integral_unitIocMeasure_quartic (c0 c1 c2 c3 c4 : ℂ) :
    ∫ t, (c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2 + c3 * (t : ℂ) ^ 3
        + c4 * (t : ℂ) ^ 4) ∂unitIocMeasure
      = c0 + c1 / 2 + c2 / 3 + c3 / 4 + c4 / 5 := by
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi3 : Integrable (fun t : ℝ => c3 * (t : ℂ) ^ 3) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi4 : Integrable (fun t : ℝ => c4 * (t : ℂ) ^ 4) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi012 : Integrable
      (fun t : ℝ => c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0123 : Integrable
      (fun t : ℝ => c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2 + c3 * (t : ℂ) ^ 3)
      unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  rw [integral_add hi0123 hi4, integral_add hi012 hi3, integral_add hi01 hi2,
    integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_coe, integral_unitIocMeasure_coe_sq,
    integral_unitIocMeasure_coe_cube, integral_unitIocMeasure_coe_four,
    MeasureTheory.integral_const]
  have huniv : unitIocMeasure.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ]
    simp
  rw [huniv, one_smul]
  ring

/-! ## The positive spectrum is nonempty

`realSpectrum_beamOperator_subset_gap` is an upper-bound-free containment, so on its own it
does not exhibit the paper's `α₃`.  What is missing is one nonzero vector orthogonal to the
kernel: the compact self-adjoint variational resolvent then has an eigenvalue outside
`{0, 1}`, and `exists_beamOperator_apply_of_beamResolvent_smul` inverts that relation into a
positive eigenvalue of the operator itself. -/

/-- The centred quadratic mode `t² - t + 1/6` — the degree-two Legendre polynomial of the
unit interval, whose zeroth and first moments both vanish. -/
noncomputable def beamQuadLp : BeamL2 :=
  contToLp (fun t => (t : ℂ) ^ 2 - (t : ℂ) + 1 / 6) (by fun_prop)

/-- The centred quadratic mode is orthogonal to every affine element: its first two exact
unit-interval moments are `1/3 - 1/2 + 1/6` and `1/4 - 1/3 + 1/12`, both zero. -/
theorem inner_affineLp_beamQuadLp (a b : ℂ) : ⟪affineLp a b, beamQuadLp⟫_ℂ = 0 := by
  rw [affineLp_eq_contToLp, beamQuadLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (a + b * (t : ℂ)) * ((t : ℂ) ^ 2 - (t : ℂ) + 1 / 6)
      = (starRingEnd ℂ) a / 6
        + ((starRingEnd ℂ) b / 6 - (starRingEnd ℂ) a) * (t : ℂ)
        + ((starRingEnd ℂ) a - (starRingEnd ℂ) b) * (t : ℂ) ^ 2
        + (starRingEnd ℂ) b * (t : ℂ) ^ 3
        + 0 * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- The centred quadratic mode lies in the orthogonal complement of the trial plane. -/
theorem beamQuadLp_mem_beamTrial_orthogonal : beamQuadLp ∈ beamTrialᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hu
  exact inner_affineLp_beamQuadLp a b

/-- The exact squared `L²` norm of the centred quadratic mode. -/
theorem norm_beamQuadLp_sq : ‖beamQuadLp‖ ^ 2 = 1 / 180 := by
  rw [beamQuadLp]
  refine norm_sq_contToLp _ _ ?_
  have hconj : ∀ t : ℝ, (starRingEnd ℂ) ((t : ℂ) ^ 2 - (t : ℂ) + 1 / 6)
      = (t : ℂ) ^ 2 - (t : ℂ) + 1 / 6 := by
    intro t
    have hre : ((t : ℂ) ^ 2 - (t : ℂ) + 1 / 6) = (((t ^ 2 - t + 1 / 6 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hre, Complex.conj_ofReal]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) ((t : ℂ) ^ 2 - (t : ℂ) + 1 / 6)
        * ((t : ℂ) ^ 2 - (t : ℂ) + 1 / 6)
      = (1 / 36 : ℂ) + (-(1 / 3) : ℂ) * (t : ℂ) + (4 / 3 : ℂ) * (t : ℂ) ^ 2
        + (-2 : ℂ) * (t : ℂ) ^ 3 + (1 : ℂ) * (t : ℂ) ^ 4 := by
    intro t
    rw [hconj t]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  push_cast
  ring

/-- The centred quadratic mode is nonzero, so the trial plane is not the whole space. -/
theorem beamQuadLp_ne_zero : beamQuadLp ≠ 0 := by
  intro h
  have hn := norm_beamQuadLp_sq
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The resolvent eigenvalue `1` sees only the affine plane, because it inverts to the
operator eigenvalue `0` and the kernel is exactly the trial subspace. -/
theorem eigenspace_beamResolvent_one_le_beamTrial :
    Module.End.eigenspace beamCoerciveFormData.resolvent.toLinearMap 1 ≤ beamTrial := by
  intro u hu
  have huv : beamCoerciveFormData.resolvent u = u := by
    have hmem := Module.End.mem_eigenspace_iff.mp hu
    rwa [one_smul] at hmem
  obtain ⟨a, b, rfl⟩ := exists_affine_of_beamResolvent_eq_self huv
  exact affineLp_mem_beamTrial a b

/-- **The free beam has a positive eigenvalue.**  The variational resolvent is compact,
self-adjoint and injective, and its eigenvector for the eigenvalue `1` spans no more than
the affine plane; since the centred quadratic mode is a nonzero vector orthogonal to that
plane, the spectral theorem for compact self-adjoint operators forces a further eigenvalue,
which inverts to a genuine positive eigenpair of the operator. -/
theorem exists_pos_eigenpair_beamOperator :
    ∃ (lam : ℝ) (x : beamOperator.domain), 0 < lam ∧ (x : BeamL2) ≠ 0 ∧
      beamOperator x = (lam : ℂ) • (x : BeamL2) := by
  obtain ⟨mu, -, hnotle⟩ :=
    TauCeti.exists_hasEigenvalue_eigenspace_not_le isCompactOperator_beamResolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamQuadLp_mem_beamTrial_orthogonal beamQuadLp_ne_zero
  obtain ⟨u, hu, hunot⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hRu : beamCoerciveFormData.resolvent u = mu • u := Module.End.mem_eigenspace_iff.mp hu
  have hu0 : u ≠ 0 := fun h => hunot (h ▸ Submodule.zero_mem beamTrial)
  have hmu0 : mu ≠ 0 := by
    intro h
    apply hu0
    apply beamCoerciveFormData.resolvent_injective
    rw [hRu, h, zero_smul, map_zero]
  have hmu1 : mu ≠ 1 := by
    intro h
    exact hunot (eigenspace_beamResolvent_one_le_beamTrial (h ▸ hu))
  obtain ⟨beta, hbeta, hchar, hmueq⟩ :=
    (beamResolvent_eigenvalue_classify hmu0 hu0 hRu).resolve_left hmu1
  obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu0 hRu
  have hbeta4 : (0 : ℝ) < beta ^ 4 := by positivity
  have hinv : mu⁻¹ - 1 = ((beta ^ 4 : ℝ) : ℂ) := by
    have hpos : ((1 + beta ^ 4 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 1 + beta ^ 4 := by linarith
      exact_mod_cast this.ne'
    rw [hmueq, show ((((1 + beta ^ 4)⁻¹ : ℝ)) : ℂ) = (((1 + beta ^ 4 : ℝ) : ℂ))⁻¹ from by
      push_cast; ring, inv_inv]
    push_cast
    ring
  refine ⟨beta ^ 4, ⟨u, humem⟩, hbeta4, hu0, ?_⟩
  rw [hbeam, hinv]

/-- **The positive real spectrum of the free beam is nonempty**, with every witness above
the paper's `500`.  This is Davis--Kahan Section 9's `α₃`, exhibited rather than assumed. -/
theorem exists_five_hundred_lt_mem_realSpectrum_beamOperator :
    ∃ alpha : ℝ, 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨lam, x, hlam, hx0, heig⟩ := exists_pos_eigenpair_beamOperator
  exact ⟨lam, eigenvalue_gt_five_hundred hlam hx0 heig,
    TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
      (x := x) hx0 heig⟩

/-- The real spectrum of the free beam contains a nonzero point.  This is the form in which
the Section 9 finite-data certificate consumes the existence of `α₃`. -/
theorem exists_mem_realSpectrum_beamOperator_ne_zero :
    ∃ alpha : ℝ, alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator ∧ alpha ≠ 0 := by
  obtain ⟨alpha, halpha, hmem⟩ := exists_five_hundred_lt_mem_realSpectrum_beamOperator
  exact ⟨alpha, hmem, by linarith⟩

/-! ## The exact affine norms -/

/-- The `L²` norm of an affine element, in the real coordinates
`‖a‖²`, `2 Re(conj a · b)`, `‖b‖²` of its coefficient pair.  This is the
`moments to integrals` identification: the value is
`CenteredAffine.inner` of the pair with itself. -/
theorem norm_affineLp_sq (a b : ℂ) :
    ‖affineLp a b‖ ^ 2
      = ‖a‖ ^ 2 + (2 * ((starRingEnd ℂ) a * b).re) / 2 + ‖b‖ ^ 2 / 3 := by
  rw [affineLp_eq_contToLp]
  refine norm_sq_contToLp _ _ ?_
  have hpt : ∀ t : ℝ, (starRingEnd ℂ) (a + b * (t : ℂ)) * (a + b * (t : ℂ))
      = ((starRingEnd ℂ) a * a)
        + ((starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a) * (t : ℂ)
        + ((starRingEnd ℂ) b * b) * (t : ℂ) ^ 2 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quadratic]
  have ha : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hb : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcross : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a
      = ((2 * ((starRingEnd ℂ) a * b).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj ((starRingEnd ℂ) a * b)]
    congr 1
    simp [mul_comm]
  rw [ha, hb, hcross]
  push_cast
  ring

/-- The `L²` norm of the perturbed affine element: the `t²`-weighted moments. -/
theorem norm_beamPerturbation_affineLp_sq (ε : ℝ) (a b : ℂ) :
    ‖beamPerturbation ε (affineLp a b)‖ ^ 2
      = ε ^ 2 * (‖a‖ ^ 2 / 3 + (2 * ((starRingEnd ℂ) a * b).re) / 4
        + ‖b‖ ^ 2 / 5) := by
  rw [beamPerturbation_affineLp]
  refine norm_sq_contToLp _ _ ?_
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
          * (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
      = 0 + 0 * (t : ℂ)
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * a)) * (t : ℂ) ^ 2
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a))
            * (t : ℂ) ^ 3
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) b * b)) * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  have ha : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hb : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcross : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a
      = ((2 * ((starRingEnd ℂ) a * b).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj ((starRingEnd ℂ) a * b)]
    congr 1
    simp [mul_comm]
  rw [ha, hb, hcross]
  push_cast
  ring

/-! ## The residual bound -/

/-- The exact Rayleigh quotient inequality behind the residual singular value: the
`t²` moment form is dominated by `(11 + √76)/30` times the `L²` form.  The constant
is sharp — it is the top eigenvalue of the residual Gram matrix — so the
discriminant of the difference vanishes identically. -/
theorem residual_quadratic_bound {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ^ 2 ≤ 4 * A * C) :
    A / 3 + B / 4 + C / 5 ≤ (11 + Real.sqrt 76) / 30 * (A + B / 2 + C / 3) := by
  have hs : Real.sqrt 76 ^ 2 = 76 := Real.sq_sqrt (by norm_num)
  have hsnn : 0 ≤ Real.sqrt 76 := Real.sqrt_nonneg _
  have hs8 : 8 < Real.sqrt 76 := by nlinarith
  set s := Real.sqrt 76 with hsdef
  -- the claim is `0 ≤ u A + v B + w C` with `u = 6 + 6 s`, `v = 3 s - 12`,
  -- `w = 2 s - 14`, all positive, and `u w = v ^ 2`
  have hkey : 0 ≤ (6 + 6 * s) * A + (3 * s - 12) * B + (2 * s - 14) * C := by
    rcases le_or_gt 0 B with hBpos | hBneg
    · have h1 : 0 ≤ (6 + 6 * s) * A := by positivity
      have h2 : 0 ≤ (3 * s - 12) * B := mul_nonneg (by linarith) hBpos
      have h3 : 0 ≤ (2 * s - 14) * C := mul_nonneg (by linarith) hC
      linarith
    · -- `(u A + w C)² ≥ 4 u w A C = 4 v² A C ≥ v² B²`, and both sides are nonnegative
      have huw : (6 + 6 * s) * (2 * s - 14) = (3 * s - 12) ^ 2 := by nlinarith
      have hsum : 0 ≤ (6 + 6 * s) * A + (2 * s - 14) * C := by
        have h1 : 0 ≤ (6 + 6 * s) * A := by positivity
        have h3 : 0 ≤ (2 * s - 14) * C := mul_nonneg (by linarith) hC
        linarith
      have hsq : ((3 * s - 12) * B) ^ 2
          ≤ ((6 + 6 * s) * A + (2 * s - 14) * C) ^ 2 := by
        have hAC : (3 * s - 12) ^ 2 * B ^ 2 ≤ (3 * s - 12) ^ 2 * (4 * A * C) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
        nlinarith [sq_nonneg ((6 + 6 * s) * A - (2 * s - 14) * C)]
      nlinarith [hsq, hsum]
  linarith

/-- Every affine element is compressed by the perturbation with the residual's top
singular value.  This is the exact operator-norm content of the Section 9 residual
Gram matrix. -/
theorem norm_beamPerturbation_affineLp_le (ε : ℝ) (a b : ℂ) :
    ‖beamPerturbation ε (affineLp a b)‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖ := by
  set A : ℝ := ‖a‖ ^ 2 with hAdef
  set C : ℝ := ‖b‖ ^ 2 with hCdef
  set B : ℝ := 2 * ((starRingEnd ℂ) a * b).re with hBdef
  have hA : 0 ≤ A := by positivity
  have hC : 0 ≤ C := by positivity
  have hBsq : B ^ 2 ≤ 4 * A * C := by
    have hre : |((starRingEnd ℂ) a * b).re| ≤ ‖(starRingEnd ℂ) a * b‖ :=
      Complex.abs_re_le_norm _
    have hnorm : ‖(starRingEnd ℂ) a * b‖ = ‖a‖ * ‖b‖ := by
      rw [norm_mul, RCLike.norm_conj]
    rw [hnorm] at hre
    have := sq_le_sq' (neg_abs_le _) (le_abs_self ((((starRingEnd ℂ) a * b)).re))
    nlinarith [abs_nonneg ((((starRingEnd ℂ) a * b)).re), norm_nonneg a, norm_nonneg b]
  -- both sides are nonnegative, so compare squares
  have hlhs := norm_beamPerturbation_affineLp_sq ε a b
  have hrhs := norm_affineLp_sq a b
  have hsq : ‖beamPerturbation ε (affineLp a b)‖ ^ 2
      ≤ (DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖) ^ 2 := by
    rw [mul_pow, DavisKahan1970.Section9.residualTopSingularValue_sq, hlhs, hrhs]
    rw [DavisKahan1970.Section9.residualGramEigenvalueHigh]
    have hq := residual_quadratic_bound hA hC hBsq
    nlinarith [sq_nonneg ε, hq]
  have hnn : 0 ≤ DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖ := by
    refine mul_nonneg ?_ (norm_nonneg _)
    rw [DavisKahan1970.Section9.residualTopSingularValue]
    positivity
  nlinarith [norm_nonneg (beamPerturbation ε (affineLp a b)), hsq, hnn]

/-- **The Section 9 residual bound.**  Restricted to the affine trial subspace, the
perturbation `ε t` has operator norm at most `residualTopSingularValue ε`. -/
theorem norm_beamPerturbation_comp_trialIncl_le (ε : ℝ) :
    ‖beamPerturbation ε ∘L beamTrialIncl‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · rw [DavisKahan1970.Section9.residualTopSingularValue]
    positivity
  · intro x
    obtain ⟨a, b, hab⟩ := mem_beamTrial_iff.1 x.2
    have hx : (x : BeamL2) = affineLp a b := hab
    have hnorm : ‖x‖ = ‖affineLp a b‖ := by rw [← hx]; rfl
    rw [ContinuousLinearMap.comp_apply, beamTrialIncl_apply, hx, hnorm]
    exact norm_beamPerturbation_affineLp_le ε a b

/-! ## The perturbed operator and its high spectral subspace -/

/-- The perturbation is self-adjoint: its symbol is real. -/
theorem beamPerturbation_isSelfAdjoint (ε : ℝ) :
    (beamPerturbation ε).IsSymmetric := by
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_beamPerturbation ε x, coeFn_beamPerturbation ε y] with t hx hy
  simp only [RCLike.inner_apply, ContinuousLinearMap.coe_coe, hx, hy, map_mul,
    Complex.conj_ofReal]
  ring

/-- **The exact operator of the Section 9 example**: the free beam perturbed by
multiplication by `ε t`. -/
noncomputable def beamPerturbed (ε : ℝ) : BeamL2 →ₗ.[ℂ] BeamL2 :=
  TauCeti.LinearPMap.addBounded beamOperator (beamPerturbation ε)

/-- The perturbed beam operator is self-adjoint. -/
theorem beamPerturbed_isSelfAdjoint (ε : ℝ) : _root_.IsSelfAdjoint (beamPerturbed ε) :=
  addBounded_isSelfAdjoint beamOperator beamOperator_isSelfAdjoint _
    (beamPerturbation_isSelfAdjoint ε)

/-- The spectral set that isolates everything above the free-beam gap. -/
noncomputable def beamHighSet : Set ℝ := Set.Ici 500

/-- The high spectral set of the beam model is measurable. -/
theorem measurableSet_beamHighSet : MeasurableSet beamHighSet := measurableSet_Ici

/-- The zero operator on the trial subspace: the compression of the free beam to its
own kernel, which is the trial subspace itself. -/
noncomputable def beamTrialZero : beamTrial →ₗ.[ℂ] beamTrial :=
  ((0 : beamTrial →L[ℂ] beamTrial).toLinearMap.toPMap ⊤)

/-- The trial-block compression of the unperturbed beam operator is
self-adjoint. -/
theorem beamTrialZero_isSelfAdjoint : _root_.IsSelfAdjoint beamTrialZero :=
  TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := 0)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (fun _ _ => by simp))

/-- **The largest sine of the angle** between the affine trial subspace and the exact
low spectral subspace of the perturbed beam: the operator norm of the cross projection
onto the exact spectral subspace above the gap. -/
noncomputable def beamSinTheta (ε : ℝ) : ℝ :=
  ‖ContinuousLinearMap.adjoint beamTrialIncl ∘L
      selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖

/-- The beam model's `sin Θ` is nonnegative. -/
theorem beamSinTheta_nonneg (ε : ℝ) : 0 ≤ beamSinTheta ε :=
  norm_nonneg (ContinuousLinearMap.adjoint beamTrialIncl ∘L
    selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)

/-- **Davis--Kahan 1970, equation (9.1), for the genuine free-beam operator.**  The
sine of the angle between the affine trial subspace and the exact low spectral
subspace of `A + ε t` is bounded by the residual's top singular value over the
spectral gap `500`.  Nothing here is assumed: the gap comes from
`realSpectrum_beamOperator_subset_gap`, the trial space is the proved kernel, and the
residual norm is the proved `t²`-moment bound. -/
theorem beamSinTheta_le (ε : ℝ) :
    beamSinTheta ε ≤ DavisKahan1970.Section9.residualTopSingularValue ε / 500 := by
  classical
  have hXdom : ∀ x : beamTrialZero.domain,
      beamTrialIncl (x : beamTrial) ∈ beamOperator.domain := fun x =>
    beamTrial_le_domain (x : beamTrial).2
  have hXint : ∀ x : beamTrialZero.domain,
      beamOperator ⟨beamTrialIncl (x : beamTrial), hXdom x⟩
        = beamTrialIncl (beamTrialZero x) := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, map_zero]
    exact beamOperator_apply_trial (x : beamTrial).2 _
  have hlow : TauCeti.LinearPMap.SemiboundedBelow beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hhigh : TauCeti.LinearPMap.SemiboundedAbove beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hspec := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) beamHighSet
      measurableSet_beamHighSet (a := (0 : ℝ) - 500) (b := (0 : ℝ) + 500) (by
        refine Set.eq_empty_iff_forall_notMem.2 ?_
        rintro lam ⟨hlam, -, h2⟩
        have hge : (500 : ℝ) ≤ lam := hlam
        have hlt : lam < (0 : ℝ) + 500 := h2
        linarith)
  have hmain := sinTheta_unbounded_opNorm_of_spectrum_gap
    (boundedPerturbationSinThetaData beamOperator (beamPerturbation ε) beamTrialZero
      (selfAdjointSpectralRestriction (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamHighSet measurableSet_beamHighSet)
      beamTrialIncl
      (selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      hXdom hXint
      (selfAdjointSpectralRestriction_inclusion_mem_domain (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      (selfAdjointSpectralRestriction_inclusion_intertwines (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet))
    (beamPerturbed_isSelfAdjoint ε) beamTrialZero_isSelfAdjoint
    (selfAdjointSpectralRestriction_isSelfAdjoint (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
    (β := 0) (α := 0) (δ := 500) le_rfl (by norm_num) hlow hhigh hspec
  have hF₁norm : ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ ≤ 1 :=
    opNorm_le_one_of_isometry
      (selfAdjointSpectralSubspaceInclusion_isometric (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
  have hres : ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
        selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
          (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := by
    calc ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
            selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖
        ≤ ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl)‖ *
            ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖beamPerturbation ε ∘L beamTrialIncl‖ *
            ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ ‖beamPerturbation ε ∘L beamTrialIncl‖ * 1 :=
          mul_le_mul_of_nonneg_left hF₁norm
            (norm_nonneg (beamPerturbation ε ∘L beamTrialIncl))
      _ = ‖beamPerturbation ε ∘L beamTrialIncl‖ := mul_one _
      _ ≤ DavisKahan1970.Section9.residualTopSingularValue ε :=
          norm_beamPerturbation_comp_trialIncl_le ε
  have hchain : 500 * beamSinTheta ε
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := le_trans hmain hres
  linarith

/-! ## The spectral subspace below the gap -/

/-- The spectral set below the free-beam gap.  The threshold `1001/2 = 500.5` is chosen
below `4.73⁴ = 500.546…` and above the paper's rounded `500`, so it separates the zero
modes from the whole positive spectrum with room to spare. -/
noncomputable def beamLowSet : Set ℝ := Set.Iic (1001 / 2)

/-- The low spectral set of the beam model is measurable. -/
theorem measurableSet_beamLowSet : MeasurableSet beamLowSet := measurableSet_Iic

/-- **The free-beam gap, sharpened past the paper's rounding.**  The positive spectrum
clears `500.5`, not merely `500`: the characteristic roots exceed `4.73` and
`4.73⁴ = 500.5466…`. -/
theorem realSpectrum_beamOperator_subset_sharp :
    TauCeti.LinearPMap.realSpectrum beamOperator ⊆ ({0} : Set ℝ) ∪ Set.Ioi (1001 / 2) := by
  intro lam hlam
  rcases realSpectrum_beamOperator_subset hlam with h0 | ⟨beta, hbeta, hchar, hlameq⟩
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Set.mem_Ioi, hlameq]
    have h473 := Classical.four_seventy_three_lt_of_characteristic_eq_zero hbeta hchar
    have hpow : ((473 : ℝ) / 100) ^ 4 < beta ^ 4 :=
      pow_lt_pow_left₀ h473 (by norm_num) (by norm_num)
    have hnum : (1001 : ℝ) / 2 < ((473 : ℝ) / 100) ^ 4 := by norm_num
    linarith

/-- Every nonzero point below the gap is a resolvent point of the free beam. -/
theorem beamOperator_mem_resolventSet_of_mem_lowSet_diff {lam : ℝ}
    (hlam : lam ∈ beamLowSet \ ({0} : Set ℝ)) :
    (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet beamOperator := by
  by_contra hcon
  -- `realSpectrum` is the complement of `realResolventSet`, which inverts `A - lam`; the
  -- canonical `resolventSet` inverts `lam • I - A`.  The two agree, but only through the
  -- bridge -- this step used to be `fun hr => hcon hr` by definitional unfolding.
  have hmem : lam ∈ TauCeti.LinearPMap.realSpectrum beamOperator := fun hr =>
    hcon ((mem_realResolventSet_iff_mem_spectraResolvent beamOperator lam).mp hr)
  rcases realSpectrum_beamOperator_subset_sharp hmem with h0 | hgt
  · exact hlam.2 h0
  · have hle : lam ≤ (1001 : ℝ) / 2 := hlam.1
    exact absurd hgt (by simp only [Set.mem_Ioi, not_lt]; exact hle)

/-- The spectral measure of the punctured region below the gap vanishes. -/
theorem beamSpecProjection_lowSet_diff_eq_zero :
    TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint
        (beamLowSet \ ({0} : Set ℝ))
        (measurableSet_beamLowSet.diff (measurableSet_singleton 0)) = 0 :=
  TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet
    beamOperator_isSelfAdjoint _ _
    (fun _ hlam => beamOperator_mem_resolventSet_of_mem_lowSet_diff hlam)

/-- **Everything below the gap is a zero mode**: the spectral projection of the whole
region below `500.5` is the projection onto the kernel eigenvalue `{0}`. -/
theorem beamSpecProjection_lowSet_eq_singleton :
    TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet
      = TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint
        ({0} : Set ℝ) (measurableSet_singleton 0) := by
  have hsplit : ({0} : Set ℝ) ∪ (beamLowSet \ ({0} : Set ℝ)) = beamLowSet := by
    refine Set.union_sdiff_cancel ?_
    intro lam hlam
    rw [Set.mem_singleton_iff] at hlam
    rw [hlam]
    exact Set.mem_Iic.2 (by norm_num)
  have hdisj : Disjoint ({0} : Set ℝ) (beamLowSet \ ({0} : Set ℝ)) :=
    Set.disjoint_sdiff_right
  have hunion := (TauCeti.LinearPMap.spectralPVM beamOperator_isSelfAdjoint).proj_union
    (measurableSet_singleton 0)
    (measurableSet_beamLowSet.diff (measurableSet_singleton 0)) hdisj
  rw [TauCeti.LinearPMap.specProjection_def, TauCeti.LinearPMap.specProjection_def]
  rw [← (TauCeti.LinearPMap.spectralPVM beamOperator_isSelfAdjoint).proj_congr hsplit
    ((measurableSet_singleton 0).union
      (measurableSet_beamLowSet.diff (measurableSet_singleton 0)))
    measurableSet_beamLowSet, hunion]
  have hzero := beamSpecProjection_lowSet_diff_eq_zero
  rw [TauCeti.LinearPMap.specProjection_def] at hzero
  rw [hzero, add_zero]

/-- A vector selected below the gap is selected by the kernel eigenvalue. -/
theorem mem_specRange_singleton_of_mem_lowSet {y : BeamL2}
    (hy : y ∈ TauCeti.LinearPMap.specRange beamOperator_isSelfAdjoint beamLowSet
      measurableSet_beamLowSet) :
    y ∈ TauCeti.LinearPMap.specRange beamOperator_isSelfAdjoint ({0} : Set ℝ)
      (measurableSet_singleton 0) := by
  rw [TauCeti.LinearPMap.mem_specRange_iff] at hy ⊢
  rw [← beamSpecProjection_lowSet_eq_singleton]
  exact hy

/-- The compression of the free beam to the spectral subspace below the gap is zero:
both form bounds are `0`. -/
theorem beamLow_semiboundedBelow :
    TauCeti.LinearPMap.SemiboundedBelow (selfAdjointSpectralRestriction beamOperator
      beamOperator_isSelfAdjoint beamLowSet measurableSet_beamLowSet) 0 := by
  intro x
  exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc
    beamOperator_isSelfAdjoint ({0} : Set ℝ) (measurableSet_singleton 0)
    (β := 0) (α := 0) (by simp) (mem_specRange_singleton_of_mem_lowSet x.1.2) x.2).1

/-- The beam operator is bounded above on the low spectral set. -/
theorem beamLow_semiboundedAbove :
    TauCeti.LinearPMap.SemiboundedAbove (selfAdjointSpectralRestriction beamOperator
      beamOperator_isSelfAdjoint beamLowSet measurableSet_beamLowSet) 0 := by
  intro x
  exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc
    beamOperator_isSelfAdjoint ({0} : Set ℝ) (measurableSet_singleton 0)
    (β := 0) (α := 0) (by simp) (mem_specRange_singleton_of_mem_lowSet x.1.2) x.2).2

/-! ## Equation (9.2): the double-angle bound -/

/-- **The largest sine of twice the angle** between the free beam's zero-mode spectral
subspace and the low spectral subspace of the perturbed operator. -/
noncomputable def beamSinTwoTheta (ε : ℝ) : ℝ :=
  ‖DavisKahan.Angle.directedSinTwoAngleOperatorC
      (selfAdjointSpectralSubspace beamOperator beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet)
      (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamLowSet measurableSet_beamLowSet)‖

/-- The beam model's `sin 2Θ` is nonnegative. -/
theorem beamSinTwoTheta_nonneg (ε : ℝ) : 0 ≤ beamSinTwoTheta ε :=
  norm_nonneg (DavisKahan.Angle.directedSinTwoAngleOperatorC
      (selfAdjointSpectralSubspace beamOperator beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet)
      (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamLowSet measurableSet_beamLowSet))

/-- The complement of the low set avoids the gap interval, so the free beam's
complementary block has no spectrum there. -/
theorem beamHigh_spectrum_avoids :
    ∀ lam ∈ Set.Ioo ((0 : ℝ) - 1001 / 2) ((0 : ℝ) + 1001 / 2),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction beamOperator beamOperator_isSelfAdjoint
          beamLowSetᶜ measurableSet_beamLowSet.compl) :=
  selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    beamOperator beamOperator_isSelfAdjoint beamLowSetᶜ measurableSet_beamLowSet.compl
    (by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro lam ⟨hlam, -, h2⟩
      have hgt : (1001 : ℝ) / 2 < lam := by
        simpa only [beamLowSet, Set.mem_compl_iff, Set.mem_Iic, not_le] using hlam
      have hlt : lam < (0 : ℝ) + 1001 / 2 := h2
      linarith)

/-- **Davis--Kahan 1970, equation (9.2), for the genuine free-beam operator.**  The
double-angle sine between the zero-mode subspace and the perturbed low subspace is
below `2 ε / 500`.  The `sin 2Θ` theorem contributes the factor two and the perturbation
norm; the gap `500.5` comes from `realSpectrum_beamOperator_subset_sharp`, which is why
the strict inequality of the printed bound survives. -/
theorem beamSinTwoTheta_lt (ε : ℝ) (hε : 0 < ε) :
    beamSinTwoTheta ε < 2 * ε / 500 := by
  have hmain := sinTwoTheta_addBounded_of_spectrum_gap beamOperator
    beamOperator_isSelfAdjoint (beamPerturbation ε) (beamPerturbation_isSelfAdjoint ε)
    beamLowSet beamLowSet measurableSet_beamLowSet measurableSet_beamLowSet
    (β := 0) (α := 0) (δ := 1001 / 2) le_rfl (by norm_num)
    beamLow_semiboundedBelow beamLow_semiboundedAbove beamHigh_spectrum_avoids
  have hnorm : ‖beamPerturbation ε‖ ≤ ε := by
    have := norm_beamPerturbation_le ε
    rwa [abs_of_pos hε] at this
  have hchain : (1001 / 2 : ℝ) * beamSinTwoTheta ε ≤ 2 * ε := by
    refine le_trans hmain ?_
    linarith
  nlinarith [beamSinTwoTheta_nonneg ε, hchain]

/-! ## Moments to integrals: the finite layer is about the operator

`Section9/TrialSubspace.lean` builds the Ritz and residual matrices out of three
bilinear forms on `CenteredAffine`, declared there as exact finite data with the note
that "a later integration lemma may identify these forms with actual Lebesgue integrals
on the unit interval".  These are those lemmas. -/

/-- The `L²` inner product of two affine elements. -/
theorem inner_affineLp (a b c d : ℂ) :
    ⟪affineLp a b, affineLp c d⟫_ℂ
      = (starRingEnd ℂ) a * c
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 2
        + (starRingEnd ℂ) b * d / 3 := by
  rw [affineLp_eq_contToLp, affineLp_eq_contToLp, inner_contToLp]
  have hpt : ∀ t : ℝ, (starRingEnd ℂ) (a + b * (t : ℂ)) * (c + d * (t : ℂ))
      = (starRingEnd ℂ) a * c
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) * (t : ℂ)
        + ((starRingEnd ℂ) b * d) * (t : ℂ) ^ 2 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quadratic]

/-- The `t`-weighted inner product of two affine elements. -/
theorem inner_affineLp_beamPerturbation (ε : ℝ) (a b c d : ℂ) :
    ⟪affineLp a b, beamPerturbation ε (affineLp c d)⟫_ℂ
      = (ε : ℂ) * ((starRingEnd ℂ) a * c / 2
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 3
        + (starRingEnd ℂ) b * d / 4) := by
  rw [affineLp_eq_contToLp, beamPerturbation_affineLp, ← affineLp_eq_contToLp,
    affineLp_eq_contToLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (a + b * (t : ℂ)) * (((ε : ℂ) * (t : ℂ)) * (c + d * (t : ℂ)))
      = 0 + ((ε : ℂ) * ((starRingEnd ℂ) a * c)) * (t : ℂ)
        + ((ε : ℂ) * ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c)) * (t : ℂ) ^ 2
        + ((ε : ℂ) * ((starRingEnd ℂ) b * d)) * (t : ℂ) ^ 3
        + 0 * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- The `t²`-weighted inner product of two affine elements. -/
theorem inner_beamPerturbation_affineLp (ε : ℝ) (a b c d : ℂ) :
    ⟪beamPerturbation ε (affineLp a b), beamPerturbation ε (affineLp c d)⟫_ℂ
      = (ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * c / 3
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 4
        + (starRingEnd ℂ) b * d / 5) := by
  rw [beamPerturbation_affineLp, beamPerturbation_affineLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
          * (((ε : ℂ) * (t : ℂ)) * (c + d * (t : ℂ)))
      = 0 + 0 * (t : ℂ)
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * c)) * (t : ℂ) ^ 2
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c)) * (t : ℂ) ^ 3
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) b * d)) * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- The `L²` realization of a centered-affine trial function `c + d (2t - 1)`. -/
noncomputable def centeredAffineLp (p : DavisKahan1970.Section9.CenteredAffine) : BeamL2 :=
  affineLp ((p.fixedValue - p.centered : ℝ) : ℂ) ((2 * p.centered : ℝ) : ℂ)

/-- The centred affine function lies in the beam trial subspace. -/
theorem centeredAffineLp_mem_beamTrial (p : DavisKahan1970.Section9.CenteredAffine) :
    centeredAffineLp p ∈ beamTrial :=
  affineLp_mem_beamTrial _ _

/-- **The affine inner product is the `L²` inner product.** -/
theorem inner_centeredAffineLp (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, centeredAffineLp q⟫_ℂ
      = ((DavisKahan1970.Section9.CenteredAffine.inner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp,
    DavisKahan1970.Section9.CenteredAffine.inner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- **The `t`-weighted affine form is the `L²` pairing against multiplication by `t`.** -/
theorem inner_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, beamPerturbation ε (centeredAffineLp q)⟫_ℂ
      = ((ε * DavisKahan1970.Section9.CenteredAffine.tInner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp_beamPerturbation,
    DavisKahan1970.Section9.CenteredAffine.tInner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- **The `t²`-weighted affine form is the `L²` norm of the multiplied pair.** -/
theorem inner_mul_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪beamPerturbation ε (centeredAffineLp p), beamPerturbation ε (centeredAffineLp q)⟫_ℂ
      = ((ε ^ 2 * DavisKahan1970.Section9.CenteredAffine.tSqInner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_beamPerturbation_affineLp,
    DavisKahan1970.Section9.CenteredAffine.tSqInner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-! ## The Ritz and residual matrices of the genuine operator -/

open DavisKahan1970.Section9 in
/-- The two trial functions are an orthonormal pair of zero modes. -/
theorem beamTrial_orthonormal :
    ‖centeredAffineLp trialOne‖ ^ 2 = 1 ∧ ‖centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
      ⟪centeredAffineLp trialOne, centeredAffineLp trialTwo⟫_ℂ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := inner_centeredAffineLp trialOne trialOne
    rw [trialOne_norm_sq] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    refine Complex.ofReal_inj.mp ?_
    push_cast
    exact h
  · have h := inner_centeredAffineLp trialTwo trialTwo
    rw [trialTwo_norm_sq] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    refine Complex.ofReal_inj.mp ?_
    push_cast
    exact h
  · rw [inner_centeredAffineLp, trialOne_inner_trialTwo]
    norm_num

open DavisKahan1970.Section9 in
/-- **The Ritz compression of `ε t` to the trial basis is the diagonal matrix of
equation (9.5)** — no longer as a finite-moment reconstruction, but as the genuine
`L²` compression of the genuine perturbation to the genuine kernel. -/
theorem beamRitz_matrix (ε : ℝ) :
    ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialOne)⟫_ℂ
        = ((ritzLow ε : ℝ) : ℂ) ∧
      ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ = 0 ∧
      ⟪centeredAffineLp trialTwo, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = ((ritzHigh ε : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialOne]
    rfl
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialTwo]
    norm_num
  · rw [inner_centeredAffineLp_mul, trialTwo_tInner_trialTwo]
    rfl

open DavisKahan1970.Section9 in
/-- **The residual Gram matrix of equation (9.1) is the genuine Gram matrix** of the
residual `ε t` restricted to the trial subspace. -/
theorem beamResidualGram_matrix (ε : ℝ) :
    ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialOne)⟫_ℂ
        = (((residualGram ε).a₀₀ : ℝ) : ℂ) ∧
      ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = (((residualGram ε).a₀₁ : ℝ) : ℂ) ∧
      ⟪beamPerturbation ε (centeredAffineLp trialTwo),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = (((residualGram ε).a₁₁ : ℝ) : ℂ) := by
  have hgram := initial_residual_gram_from_affine_moments ε
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₀₀ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₀₁ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₁₁ hgram

/-! ## The finite-data certificate, constructed -/

open DavisKahan1970.Section9 in
/-- **The Section 9 finite-data certificate, constructed from the genuine operator.**

Every field is now discharged rather than postulated: the two Gram matrices and the two
Ritz values are the compressions computed in `beamRitz_matrix` and
`beamResidualGram_matrix`, and the third eigenvalue is a point of
`TauCeti.LinearPMap.realSpectrum beamOperator` supplied by
`exists_five_hundred_lt_mem_realSpectrum_beamOperator`, whose lower bound `500` comes with
it.  The record no longer takes a spectral point as a hypothesis; the only inputs are the
paper's two numerical constraints on `ε`. -/
noncomputable def beamFiniteDataCertificate (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    FreeBeamFiniteDataCertificate ε where
  epsilon_pos := hε
  epsilon_lt_hundred := hε100
  third_eigenvalue := exists_five_hundred_lt_mem_realSpectrum_beamOperator.choose
  third_eigenvalue_gt_five_hundred :=
    exists_five_hundred_lt_mem_realSpectrum_beamOperator.choose_spec.1
  initial_residual_gram := residualGram ε
  initial_residual_gram_eq := rfl
  ritz_low := ritzLow ε
  ritz_high := ritzHigh ε
  ritz_low_eq := rfl
  ritz_high_eq := rfl
  recentered_residual_gram := orthogonalResidualGram ε
  recentered_residual_gram_eq := rfl

/-! ## Equation (9.4): the two-term Ky Fan sum -/

/-- The two-term Ky Fan ideal family over `ℂ`, the gauge equation (9.4) is stated in. -/
noncomputable def beamKyFanTwo : TauCeti.SymmetricOperatorIdealFamily.{0, 0} ℂ :=
  kyFanSymmetricIdealFamily (𝕜 := ℂ) 2 (by norm_num)

/-- The two-term Ky Fan family is a complete operator ideal family. -/
noncomputable instance : beamKyFanTwo.toOperatorIdealFamily.IsComplete :=
  isComplete_kyFanSymmetricIdealFamily (𝕜 := ℂ) 2 (by norm_num)

/-- The two-term Ky Fan gauge of any bounded operator is at most twice its norm: both
approximation numbers in the sum are bounded by the operator norm. -/
theorem beamKyFanTwo_gaugeReal_le (T : BeamL2 →L[ℂ] BeamL2) :
    beamKyFanTwo.gaugeReal T ≤ 2 * ‖T‖ := by
  have hsum : ContinuousLinearMap.kyFanGauge T 2 ≤ 2 * ‖T‖ := by
    rw [ContinuousLinearMap.kyFanGauge, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    have h0 := T.approximationNumber_le_norm 0
    have h1 := T.approximationNumber_le_norm 1
    linarith
  have hnonneg : 0 ≤ ContinuousLinearMap.kyFanGauge T 2 :=
    le_trans (norm_nonneg T)
      (opNorm_le_kyFanApproximationGauge (k := 2) (by norm_num) T)
  have hval : beamKyFanTwo.gaugeReal T
      = (ENNReal.ofReal (kyFanApproximationGauge 2 T)).toReal := rfl
  rw [hval, kyFanApproximationGauge_eq_kyFanGauge, ENNReal.toReal_ofReal hnonneg]
  exact hsum

/-- Every bounded operator lies in the two-term Ky Fan ideal. -/
theorem beamKyFanTwo_mem (T : BeamL2 →L[ℂ] BeamL2) : beamKyFanTwo.Mem T :=
  gauge_kyFanSymmetricIdealFamily_ne_top (𝕜 := ℂ) 2 (by norm_num) T

/-- **The two-term Ky Fan sum of the double-angle sines** between the free beam's
zero-mode subspace and the perturbed operator's low subspace. -/
noncomputable def beamSinTwoThetaSum (ε : ℝ) : ℝ :=
  beamKyFanTwo.gaugeReal (sinTwoThetaIdealBlock
    (selfAdjointSpectralSubspace beamOperator beamOperator_isSelfAdjoint beamLowSet
      measurableSet_beamLowSet)
    (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
      beamLowSet measurableSet_beamLowSet))

/-- **Davis--Kahan 1970, equation (9.4), for the genuine free-beam operator.**  The
two-term Ky Fan sum of the double-angle sines is below `4 ε / 500`.  The double-angle
theorem contributes the factor two, the two-term Ky Fan gauge of the perturbation
contributes another, and the gap `500.5` again supplies the strict inequality. -/
theorem beamSinTwoThetaSum_lt (ε : ℝ) (hε : 0 < ε) :
    beamSinTwoThetaSum ε < 4 * ε / 500 := by
  have hmain := sinTwoTheta_addBounded_gauge_of_spectrum_gap beamKyFanTwo beamOperator
    beamOperator_isSelfAdjoint (beamPerturbation ε) (beamPerturbation_isSelfAdjoint ε)
    beamLowSet beamLowSet measurableSet_beamLowSet measurableSet_beamLowSet
    (β := 0) (α := 0) (δ := 1001 / 2) le_rfl (by norm_num)
    beamLow_semiboundedBelow beamLow_semiboundedAbove beamHigh_spectrum_avoids
    (beamKyFanTwo_mem _)
  have hnorm : ‖beamPerturbation ε‖ ≤ ε := by
    have := norm_beamPerturbation_le ε
    rwa [abs_of_pos hε] at this
  have hgauge : beamKyFanTwo.gaugeReal (beamPerturbation ε) ≤ 2 * ε :=
    le_trans (beamKyFanTwo_gaugeReal_le _) (by linarith)
  have hnn : 0 ≤ beamSinTwoThetaSum ε :=
    ENNReal.toReal_nonneg
  have hchain : (1001 / 2 : ℝ) * beamSinTwoThetaSum ε ≤ 4 * ε := by
    refine le_trans hmain.2 ?_
    linarith
  nlinarith [hnn, hchain]


/-! ## Equation (9.3): the second approximation number of the residual

The Ky Fan-2 form of the sine theorem needs *both* singular values of the
residual, where (9.1) needed only the top one.  The residual has a
two-dimensional domain, so its second approximation number is computed by a
single explicit rank-one approximant along the top eigendirection of the
residual Gram matrix.

In the orthonormal trial basis the Gram matrix of equation (9.1) is
`(ε²/30) · [[11 - √75, -1], [-1, 11 + √75]]`, whose eigenvalues are
`(ε²/30)(11 ± √76)`.  Its top eigenvector is `φ₁ + c φ₂` with
`c = -(√75 + √76)`, and the whole computation reduces to the radical identity

`c²(11 - √75) + 2c + (11 + √75) = (1 + c²)(11 - √76)`,

which is `(√75 + √76)(√75 - √76) = -1` in disguise.  No shortcut through
`a₁ ≤ a₀` works: `2 · residualTopSingularValue / 500` exceeds the printed
`109/50000 · ε`. -/

open DavisKahan1970.Section9 in
/-- The Section 9 residual as an operator: multiplication by `ε t` restricted to
the affine trial subspace. -/
noncomputable def beamResidual (ε : ℝ) : beamTrial →L[ℂ] BeamL2 :=
  beamPerturbation ε ∘L beamTrialIncl

open DavisKahan1970.Section9 in
/-- The first trial vector, as an element of the trial subspace. -/
noncomputable def beamTrialVecOne : beamTrial :=
  ⟨centeredAffineLp trialOne, centeredAffineLp_mem_beamTrial _⟩

open DavisKahan1970.Section9 in
/-- The second trial vector, as an element of the trial subspace. -/
noncomputable def beamTrialVecTwo : beamTrial :=
  ⟨centeredAffineLp trialTwo, centeredAffineLp_mem_beamTrial _⟩

open DavisKahan1970.Section9 in
/-- The beam residual on the first trial basis vector. -/
theorem beamResidual_apply_vecOne (ε : ℝ) :
    beamResidual ε beamTrialVecOne = beamPerturbation ε (centeredAffineLp trialOne) :=
  rfl

open DavisKahan1970.Section9 in
/-- The beam residual on the second trial basis vector. -/
theorem beamResidual_apply_vecTwo (ε : ℝ) :
    beamResidual ε beamTrialVecTwo = beamPerturbation ε (centeredAffineLp trialTwo) :=
  rfl

/-- The two trial vectors are orthonormal inside the trial subspace. -/
theorem beamTrialVec_orthonormal :
    ⟪beamTrialVecOne, beamTrialVecOne⟫_ℂ = 1 ∧
      ⟪beamTrialVecTwo, beamTrialVecTwo⟫_ℂ = 1 ∧
        ⟪beamTrialVecOne, beamTrialVecTwo⟫_ℂ = 0 := by
  obtain ⟨h1, h2, h12⟩ := beamTrial_orthonormal
  refine ⟨?_, ?_, ?_⟩
  · change ⟪(beamTrialVecOne : BeamL2), (beamTrialVecOne : BeamL2)⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖centeredAffineLp DavisKahan1970.Section9.trialOne‖ : ℂ)) ^ 2 = 1
    rw [← Complex.ofReal_pow, h1]
    norm_num
  · change ⟪(beamTrialVecTwo : BeamL2), (beamTrialVecTwo : BeamL2)⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖centeredAffineLp DavisKahan1970.Section9.trialTwo‖ : ℂ)) ^ 2 = 1
    rw [← Complex.ofReal_pow, h2]
    norm_num
  · exact h12

/-- The two trial vectors span the trial subspace: it is two-dimensional and they
are an orthonormal pair. -/
theorem beamTrialVec_span_eq_top :
    Submodule.span ℂ ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial) = ⊤ := by
  classical
  obtain ⟨h1, h2, h12⟩ := beamTrialVec_orthonormal
  have h21 : ⟪beamTrialVecTwo, beamTrialVecOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) beamTrialVecTwo beamTrialVecOne, h12, map_zero]
  have hne1 : beamTrialVecOne ≠ 0 := by
    intro hzero
    simp [hzero] at h1
  have hne2 : beamTrialVecTwo ≠ 0 := by
    intro hzero
    simp [hzero] at h2
  have hli : LinearIndependent ℂ ![beamTrialVecOne, beamTrialVecTwo] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have hA : α = 0 := by
      have := congrArg (fun z => ⟪beamTrialVecOne, z⟫_ℂ) hαβ
      simpa [inner_add_right, inner_smul_right, h1, h12, hne1] using this
    have hB : β = 0 := by
      have := congrArg (fun z => ⟪beamTrialVecTwo, z⟫_ℂ) hαβ
      simpa [inner_add_right, inner_smul_right, h2, h21, hne2] using this
    exact ⟨hA, hB⟩
  have hrange : Set.range ![beamTrialVecOne, beamTrialVecTwo] =
      ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial) := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  have hspan : Module.finrank ℂ
      (Submodule.span ℂ ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial)) = 2 := by
    rw [← hrange, finrank_span_eq_card hli]
    simp
  have hle : Module.finrank ℂ (beamTrial : Submodule ℂ BeamL2) ≤ 2 := by
    have hcard : (Cardinal.mk ({beamOneLp, beamIdLp} : Set BeamL2)) ≤ 2 := by
      refine le_trans Cardinal.mk_insert_le ?_
      rw [Cardinal.mk_singleton]
      exact le_of_eq one_add_one_eq_two
    have hrk : Module.rank ℂ (beamTrial : Submodule ℂ BeamL2) ≤ 2 :=
      le_trans (by rw [beamTrial]; exact rank_span_le _) hcard
    exact_mod_cast Module.finrank_le_of_rank_le hrk
  have hge : 2 ≤ Module.finrank ℂ (beamTrial : Submodule ℂ BeamL2) := by
    rw [← hspan]
    exact Submodule.finrank_le _
  have heq : Module.finrank ℂ
      (Submodule.span ℂ ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial)) =
      Module.finrank ℂ (beamTrial : Submodule ℂ BeamL2) := by
    omega
  exact Submodule.eq_top_of_finrank_eq heq

/-- Every trial vector is a combination of the two orthonormal trial vectors. -/
theorem exists_beamTrialVec_repr (x : beamTrial) :
    ∃ α β : ℂ, x = α • beamTrialVecOne + β • beamTrialVecTwo := by
  have hx : x ∈ Submodule.span ℂ ({beamTrialVecOne, beamTrialVecTwo} : Set beamTrial) := by
    rw [beamTrialVec_span_eq_top]; trivial
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hx
  exact ⟨α, β, hαβ.symm⟩

open DavisKahan1970.Section9 in
/-- The exact Gram values of the residual on the orthonormal trial basis: this is
the residual Gram matrix of equation (9.1), read as inner products of the genuine
`L²` residual. -/
theorem beamResidual_gram (ε : ℝ) :
    ⟪beamResidual ε beamTrialVecOne, beamResidual ε beamTrialVecOne⟫_ℂ
        = (((residualGram ε).a₀₀ : ℝ) : ℂ) ∧
      ⟪beamResidual ε beamTrialVecOne, beamResidual ε beamTrialVecTwo⟫_ℂ
        = (((residualGram ε).a₀₁ : ℝ) : ℂ) ∧
      ⟪beamResidual ε beamTrialVecTwo, beamResidual ε beamTrialVecTwo⟫_ℂ
        = (((residualGram ε).a₁₁ : ℝ) : ℂ) :=
  beamResidualGram_matrix ε

/-- The top eigendirection coefficient of the residual Gram matrix:
`c = -(√75 + √76)`, so that `φ₁ + c φ₂` is a top eigenvector. -/
noncomputable def beamGramTopCoefficient : ℝ := -(Real.sqrt 75 + Real.sqrt 76)

open DavisKahan1970.Section9 in
/-- **The radical identity behind equation (9.3).**  Along the direction
`c φ₁ - φ₂` orthogonal to the top eigenvector, the residual Gram form equals
`(1 + c²)` times the *lower* eigenvalue.  Equivalently
`(√75 + √76)(√75 - √76) = -1`. -/
theorem beamGram_orthogonal_direction (ε : ℝ) :
    beamGramTopCoefficient ^ 2 * (residualGram ε).a₀₀
        - 2 * beamGramTopCoefficient * (residualGram ε).a₀₁
        + (residualGram ε).a₁₁
      = (1 + beamGramTopCoefficient ^ 2) * residualGramEigenvalueLow ε := by
  have hs : Real.sqrt 75 ^ 2 = 75 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 76 ^ 2 = 76 := Real.sq_sqrt (by norm_num)
  unfold beamGramTopCoefficient residualGram residualGramEigenvalueLow
  dsimp only
  linear_combination (ε ^ 2 / 30 * (-Real.sqrt 75 - Real.sqrt 76)) * hs
    + (ε ^ 2 / 30 * (Real.sqrt 75 + Real.sqrt 76)) * hr
open DavisKahan1970.Section9 in
/-- The residual Gram form along the direction `c φ₁ - φ₂` orthogonal to the top
eigenvector: it carries exactly the *lower* Gram eigenvalue, scaled by `1 + c²`. -/
theorem beamResidual_orthogonal_inner (ε : ℝ) :
    ⟪beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
        beamTrialVecTwo),
      beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
        beamTrialVecTwo)⟫_ℂ
      = ((((1 + beamGramTopCoefficient ^ 2) * residualGramEigenvalueLow ε : ℝ)) : ℂ) := by
  obtain ⟨g00, g01, g11⟩ := beamResidual_gram ε
  have hg10 : ⟪beamResidual ε beamTrialVecTwo, beamResidual ε beamTrialVecOne⟫_ℂ
      = (((residualGram ε).a₀₁ : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (beamResidual ε beamTrialVecOne), g01, Complex.conj_ofReal]
  rw [← beamGram_orthogonal_direction ε, map_sub, map_smul]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    g00, g01, g11, hg10, Complex.conj_ofReal]
  push_cast
  ring

open DavisKahan1970.Section9 in
/-- The squared norm of the residual's component orthogonal to the trial
subspace. -/
theorem beamResidual_orthogonal_norm_sq (ε : ℝ) :
    ‖beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
        beamTrialVecTwo)‖ ^ 2
      = (1 + beamGramTopCoefficient ^ 2) * residualGramEigenvalueLow ε := by
  have h := beamResidual_orthogonal_inner ε
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : (((‖beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
        beamTrialVecTwo)‖ ^ 2 : ℝ)) : ℂ)
      = ((((1 + beamGramTopCoefficient ^ 2) * residualGramEigenvalueLow ε : ℝ)) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  exact Complex.ofReal_inj.mp h2

/-- The normalising constant `1 + c²` of the top eigendirection is positive. -/
theorem beamGramTopDenom_pos : (0 : ℝ) < 1 + beamGramTopCoefficient ^ 2 := by
  positivity

open DavisKahan1970.Section9 in
/-- The top eigenvector of the residual Gram matrix, unnormalised:
`φ₁ + c φ₂` with `c = -(√75 + √76)`. -/
noncomputable def beamGramTopVector : beamTrial :=
  beamTrialVecOne + ((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecTwo

open DavisKahan1970.Section9 in
/-- **The explicit rank-one approximant of the Section 9 residual**: the residual
composed with the orthogonal projection onto the top eigendirection of the
residual Gram matrix. -/
noncomputable def beamResidualRankOne (ε : ℝ) : beamTrial →L[ℂ] BeamL2 :=
  (innerSL ℂ beamGramTopVector).smulRight
    ((((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ)⁻¹) •
      beamResidual ε beamGramTopVector)

/-- Evaluating the rank-one model of the beam residual. -/
theorem beamResidualRankOne_apply (ε : ℝ) (x : beamTrial) :
    beamResidualRankOne ε x = ⟪beamGramTopVector, x⟫_ℂ •
      ((((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ)⁻¹) •
        beamResidual ε beamGramTopVector) := rfl

/-- The rank-one model of the beam residual has rank at most one. -/
theorem beamResidualRankOne_rank_le (ε : ℝ) :
    (beamResidualRankOne ε).rank ≤ (1 : Cardinal) := by
  classical
  set v : BeamL2 := (((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ)⁻¹) •
    beamResidual ε beamGramTopVector with hv
  have hle : LinearMap.range
      ((beamResidualRankOne ε : beamTrial →L[ℂ] BeamL2) : beamTrial →ₗ[ℂ] BeamL2)
      ≤ Submodule.span ℂ ({v} : Set BeamL2) := by
    rintro y ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨⟪beamGramTopVector, x⟫_ℂ, rfl⟩
  calc (beamResidualRankOne ε).rank
      ≤ Module.rank ℂ (Submodule.span ℂ ({v} : Set BeamL2)) := Submodule.rank_mono hle
    _ ≤ 1 := by simpa using rank_span_le ({v} : Set BeamL2)

open DavisKahan1970.Section9 in
/-- The four ambient inner products of the orthonormal trial pair. -/
theorem inner_beamTrialLp :
    ⟪centeredAffineLp trialOne, centeredAffineLp trialOne⟫_ℂ = 1 ∧
      ⟪centeredAffineLp trialTwo, centeredAffineLp trialTwo⟫_ℂ = 1 ∧
        ⟪centeredAffineLp trialOne, centeredAffineLp trialTwo⟫_ℂ = 0 ∧
          ⟪centeredAffineLp trialTwo, centeredAffineLp trialOne⟫_ℂ = 0 := by
  obtain ⟨h1, h2, h12⟩ := beamTrial_orthonormal
  have q1 : ⟪centeredAffineLp trialOne, centeredAffineLp trialOne⟫_ℂ = 1 := by
    have hn : ‖centeredAffineLp trialOne‖ = 1 := by
      nlinarith [norm_nonneg (centeredAffineLp trialOne), h1]
    rw [inner_self_eq_norm_sq_to_K, hn]
    norm_num
  have q2 : ⟪centeredAffineLp trialTwo, centeredAffineLp trialTwo⟫_ℂ = 1 := by
    have hn : ‖centeredAffineLp trialTwo‖ = 1 := by
      nlinarith [norm_nonneg (centeredAffineLp trialTwo), h2]
    rw [inner_self_eq_norm_sq_to_K, hn]
    norm_num
  refine ⟨q1, q2, h12, ?_⟩
  rw [← inner_conj_symm (𝕜 := ℂ) (centeredAffineLp trialTwo) (centeredAffineLp trialOne),
    h12, map_zero]

/-- The pairing of the top eigenvector against a trial vector in the orthonormal
coordinates. -/
theorem inner_beamGramTopVector (α β : ℂ) :
    ⟪beamGramTopVector, α • beamTrialVecOne + β • beamTrialVecTwo⟫_ℂ
      = α + ((beamGramTopCoefficient : ℝ) : ℂ) * β := by
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  have hw : ((beamGramTopVector : beamTrial) : BeamL2)
      = centeredAffineLp DavisKahan1970.Section9.trialOne
        + ((beamGramTopCoefficient : ℝ) : ℂ) •
          centeredAffineLp DavisKahan1970.Section9.trialTwo := rfl
  have hxc : ((α • beamTrialVecOne + β • beamTrialVecTwo : beamTrial) : BeamL2)
      = α • centeredAffineLp DavisKahan1970.Section9.trialOne
        + β • centeredAffineLp DavisKahan1970.Section9.trialTwo := rfl
  rw [Submodule.coe_inner, hw, hxc]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    q1, q2, q12, q21, Complex.conj_ofReal]
  ring

/-- The norm of a trial vector in the orthonormal coordinates. -/
theorem norm_sq_beamTrialVec_comb (α β : ℂ) :
    ‖α • beamTrialVecOne + β • beamTrialVecTwo‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 := by
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  have hxc : ((α • beamTrialVecOne + β • beamTrialVecTwo : beamTrial) : BeamL2)
      = α • centeredAffineLp DavisKahan1970.Section9.trialOne
        + β • centeredAffineLp DavisKahan1970.Section9.trialTwo := rfl
  have hnorm : ‖α • beamTrialVecOne + β • beamTrialVecTwo‖
      = ‖α • centeredAffineLp DavisKahan1970.Section9.trialOne
          + β • centeredAffineLp DavisKahan1970.Section9.trialTwo‖ := by
    rw [← hxc]
    rfl
  have hinner : ⟪α • centeredAffineLp DavisKahan1970.Section9.trialOne
        + β • centeredAffineLp DavisKahan1970.Section9.trialTwo,
      α • centeredAffineLp DavisKahan1970.Section9.trialOne
        + β • centeredAffineLp DavisKahan1970.Section9.trialTwo⟫_ℂ
      = (((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ)) : ℂ) := by
    have hα : α * (starRingEnd ℂ) α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hβ : β * (starRingEnd ℂ) β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      q1, q2, q12, q21]
    rw [show α * ((starRingEnd ℂ) α * 1 + (starRingEnd ℂ) β * 0)
        + β * ((starRingEnd ℂ) α * 0 + (starRingEnd ℂ) β * 1)
        = α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β from by ring, hα, hβ]
    push_cast
    ring
  rw [hnorm]
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have h2' : (((‖α • centeredAffineLp DavisKahan1970.Section9.trialOne
        + β • centeredAffineLp DavisKahan1970.Section9.trialTwo‖ ^ 2 : ℝ)) : ℂ)
      = (((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast
    push_cast at hinner
    exact hinner
  exact Complex.ofReal_inj.mp h2'

open DavisKahan1970.Section9 in
/-- **The rank-one approximant leaves exactly the orthogonal direction.**  For
`x = α φ₁ + β φ₂` the error is `(c α − β)/(1 + c²)` times the residual of the
direction `c φ₁ − φ₂` orthogonal to the top eigenvector. -/
theorem beamResidual_sub_rankOne_apply (ε : ℝ) (α β : ℂ) :
    (beamResidual ε - beamResidualRankOne ε)
        (α • beamTrialVecOne + β • beamTrialVecTwo)
      = ((((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ)⁻¹) *
            (((beamGramTopCoefficient : ℝ) : ℂ) * α - β)) •
          beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
            beamTrialVecTwo) := by
  have hD : (((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt beamGramTopDenom_pos
  have hD' : (1 : ℂ) + ((beamGramTopCoefficient : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have h := hD
    push_cast at h
    exact h
  have hx : beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo)
      = α • beamResidual ε beamTrialVecOne + β • beamResidual ε beamTrialVecTwo := by
    rw [map_add, map_smul, map_smul]
  have hw : beamResidual ε beamGramTopVector
      = beamResidual ε beamTrialVecOne
        + ((beamGramTopCoefficient : ℝ) : ℂ) • beamResidual ε beamTrialVecTwo := by
    rw [beamGramTopVector, map_add, map_smul]
  have hz : beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne -
        beamTrialVecTwo)
      = ((beamGramTopCoefficient : ℝ) : ℂ) • beamResidual ε beamTrialVecOne
        - beamResidual ε beamTrialVecTwo := by
    rw [map_sub, map_smul]
  rw [sub_apply, beamResidualRankOne_apply,
    inner_beamGramTopVector, hx, hw, hz]
  match_scalars <;> field_simp <;> ring

private theorem le_of_sq_le_sq' {A B : ℝ} (hB : 0 ≤ B)
    (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by nlinarith

open DavisKahan1970.Section9 in
/-- **The rank-one approximation error of the Section 9 residual is exactly the
second singular value.**  This is the sharp Eckart--Young step: the approximant
along the top Gram eigendirection leaves the orthogonal direction, whose norm is
`residualBottomSingularValue ε`. -/
theorem norm_beamResidual_sub_rankOne_le (ε : ℝ) :
    ‖beamResidual ε - beamResidualRankOne ε‖ ≤ residualBottomSingularValue ε := by
  have hσ0 : 0 ≤ residualBottomSingularValue ε := by
    rw [residualBottomSingularValue]
    positivity
  have hDpos : (0 : ℝ) < 1 + beamGramTopCoefficient ^ 2 := beamGramTopDenom_pos
  have hzsq : ‖beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne
        - beamTrialVecTwo)‖ ^ 2
      = (1 + beamGramTopCoefficient ^ 2) * residualBottomSingularValue ε ^ 2 := by
    rw [beamResidual_orthogonal_norm_sq, residualBottomSingularValue_sq]
  refine ContinuousLinearMap.opNorm_le_bound _ hσ0 fun x => ?_
  obtain ⟨α, β, hx⟩ := exists_beamTrialVec_repr x
  subst hx
  rw [beamResidual_sub_rankOne_apply, norm_smul]
  have hγ : ‖(((1 + beamGramTopCoefficient ^ 2 : ℝ) : ℂ))⁻¹ *
        (((beamGramTopCoefficient : ℝ) : ℂ) * α - β)‖
      = (1 + beamGramTopCoefficient ^ 2)⁻¹ *
        ‖((beamGramTopCoefficient : ℝ) : ℂ) * α - β‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos]
  rw [hγ]
  have hcs : ‖((beamGramTopCoefficient : ℝ) : ℂ) * α - β‖ ^ 2
      ≤ (1 + beamGramTopCoefficient ^ 2) *
        ‖α • beamTrialVecOne + β • beamTrialVecTwo‖ ^ 2 := by
    rw [norm_sq_beamTrialVec_comb]
    have htri : ‖((beamGramTopCoefficient : ℝ) : ℂ) * α - β‖
        ≤ |beamGramTopCoefficient| * ‖α‖ + ‖β‖ := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg α, norm_nonneg β, abs_nonneg beamGramTopCoefficient,
      sq_abs beamGramTopCoefficient,
      sq_nonneg (|beamGramTopCoefficient| * ‖β‖ - ‖α‖),
      norm_nonneg (((beamGramTopCoefficient : ℝ) : ℂ) * α - β), htri]
  rw [show (1 + beamGramTopCoefficient ^ 2)⁻¹ *
        ‖((beamGramTopCoefficient : ℝ) : ℂ) * α - β‖ *
        ‖beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne
          - beamTrialVecTwo)‖
      = (‖((beamGramTopCoefficient : ℝ) : ℂ) * α - β‖ *
          ‖beamResidual ε (((beamGramTopCoefficient : ℝ) : ℂ) • beamTrialVecOne
            - beamTrialVecTwo)‖) / (1 + beamGramTopCoefficient ^ 2) from by ring,
    div_le_iff₀ hDpos]
  refine le_of_sq_le_sq' (by positivity) ?_
  rw [mul_pow, hzsq]
  nlinarith [hcs, sq_nonneg (residualBottomSingularValue ε),
    norm_nonneg (α • beamTrialVecOne + β • beamTrialVecTwo),
    sq_nonneg (‖α • beamTrialVecOne + β • beamTrialVecTwo‖),
    hDpos]

open DavisKahan1970.Section9 in
/-- **The second approximation number of the Section 9 residual.**  The rank-one
approximant along the top Gram eigendirection realises it. -/
theorem approximationSingularValue_one_beamResidual_le (ε : ℝ) :
    approximationSingularValue 1 (beamResidual ε) ≤ residualBottomSingularValue ε := by
  have hrank : (beamResidualRankOne ε).rank ≤ ((1 : ℕ) : Cardinal) := by
    simpa using beamResidualRankOne_rank_le ε
  exact le_trans ((beamResidual ε).approximationNumber_le_norm_sub hrank)
    (norm_beamResidual_sub_rankOne_le ε)

open DavisKahan1970.Section9 in
/-- **Both singular values of the Section 9 residual at once**: the two-term Ky Fan
gauge of the residual is at most `residualKyFanTwo ε`.  This is what equation (9.3)
needs and equation (9.1) did not: (9.1) used only the top singular value. -/
theorem kyFanTwo_beamResidual_le (ε : ℝ) :
    kyFanApproximationGauge 2 (beamResidual ε) ≤ residualKyFanTwo ε := by
  have h0 : approximationSingularValue 0 (beamResidual ε)
      ≤ residualTopSingularValue ε := by
    have hz : approximationSingularValue 0 (beamResidual ε) = ‖beamResidual ε‖ :=
      (beamResidual ε).approximationNumber_index_zero
    rw [hz]
    exact norm_beamPerturbation_comp_trialIncl_le ε
  have h1 := approximationSingularValue_one_beamResidual_le ε
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, residualKyFanTwo]
  exact add_le_add h0 h1

open DavisKahan1970.Section9 in
/-- **The two-term Ky Fan sum of the sines** of the angles between the affine trial
subspace and the exact low spectral subspace of the perturbed beam. -/
noncomputable def beamSinThetaSum (ε : ℝ) : ℝ :=
  beamKyFanTwo.gaugeReal (ContinuousLinearMap.adjoint beamTrialIncl ∘L
    selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)

open DavisKahan1970.Section9 in
/-- **Davis--Kahan 1970, equation (9.3), for the genuine free-beam operator.**

The two-term Ky Fan sum of the sines of the angles between the affine trial
subspace and the exact low spectral subspace of `A + ε t` is at most
`residualKyFanTwo ε / 500`.

Nothing is assumed: the gap comes from `realSpectrum_beamOperator_subset_gap`
through the set-localization lemma, the trial space is the proved kernel, and the
residual's *two* singular values are `kyFanTwo_beamResidual_le`, whose second one is
realised by an explicit rank-one approximant along the top eigendirection of the
residual Gram matrix. -/
theorem beamSinThetaSum_le (ε : ℝ) :
    beamSinThetaSum ε ≤ residualKyFanTwo ε / 500 := by
  classical
  have hXdom : ∀ x : beamTrialZero.domain,
      beamTrialIncl (x : beamTrial) ∈ beamOperator.domain := fun x =>
    beamTrial_le_domain (x : beamTrial).2
  have hXint : ∀ x : beamTrialZero.domain,
      beamOperator ⟨beamTrialIncl (x : beamTrial), hXdom x⟩
        = beamTrialIncl (beamTrialZero x) := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, map_zero]
    exact beamOperator_apply_trial (x : beamTrial).2 _
  have hlow : TauCeti.LinearPMap.SemiboundedBelow beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hhigh : TauCeti.LinearPMap.SemiboundedAbove beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hspec := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) beamHighSet
      measurableSet_beamHighSet (a := (0 : ℝ) - 500) (b := (0 : ℝ) + 500) (by
        refine Set.eq_empty_iff_forall_notMem.2 ?_
        rintro lam ⟨hlam, -, h2⟩
        have hge : (500 : ℝ) ≤ lam := hlam
        have hlt : lam < (0 : ℝ) + 500 := h2
        linarith)
  have hmain := sinTheta_unbounded_gauge_of_spectrum_gap beamKyFanTwo
    (boundedPerturbationSinThetaData beamOperator (beamPerturbation ε) beamTrialZero
      (selfAdjointSpectralRestriction (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamHighSet measurableSet_beamHighSet)
      beamTrialIncl
      (selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      hXdom hXint
      (selfAdjointSpectralRestriction_inclusion_mem_domain (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      (selfAdjointSpectralRestriction_inclusion_intertwines (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet))
    (beamPerturbed_isSelfAdjoint ε) beamTrialZero_isSelfAdjoint
    (selfAdjointSpectralRestriction_isSelfAdjoint (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
    (β := 0) (α := 0) (δ := 500) le_rfl (by norm_num) hlow hhigh hspec
    (gauge_kyFanSymmetricIdealFamily_ne_top (𝕜 := ℂ) 2 (by norm_num) _)
  have hF₁norm : ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ ≤ 1 :=
    opNorm_le_one_of_isometry
      (selfAdjointSpectralSubspaceInclusion_isometric (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
  -- the residual side: both singular values, transported across the isometric inclusion
  have hres : beamKyFanTwo.gaugeReal
        (ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
          selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
            (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      ≤ residualKyFanTwo ε := by
    have hgauge : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
        [CompleteSpace G] (T : G →L[ℂ] beamTrial),
        beamKyFanTwo.gaugeReal T = kyFanApproximationGauge 2 T := by
      intro G _ _ _ T
      have hval : beamKyFanTwo.gaugeReal T
          = (ENNReal.ofReal (kyFanApproximationGauge 2 T)).toReal := rfl
      rw [hval, ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg 2 T)]
    rw [hgauge]
    calc kyFanApproximationGauge 2
          (ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
            selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
        = kyFanApproximationGauge 2
            (ContinuousLinearMap.id ℂ beamTrial ∘L
              ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
              selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
                (beamPerturbed_isSelfAdjoint ε) beamHighSet
                measurableSet_beamHighSet) := by
          congr 1
      _ ≤ ‖ContinuousLinearMap.id ℂ beamTrial‖ *
            kyFanApproximationGauge 2
              (ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl)) *
            ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ :=
          kyFanApproximationGauge_comp_le _ _ _ _
      _ ≤ 1 * kyFanApproximationGauge 2 (beamResidual ε) * 1 := by
          rw [kyFanApproximationGauge_adjoint,
            show (beamPerturbation ε ∘L beamTrialIncl) = beamResidual ε from rfl]
          have hid : ‖ContinuousLinearMap.id ℂ beamTrial‖ ≤ 1 :=
            ContinuousLinearMap.norm_id_le
          have hnn : 0 ≤ kyFanApproximationGauge 2 (beamResidual ε) :=
            kyFanApproximationGauge_nonneg 2 _
          have h1 : ‖ContinuousLinearMap.id ℂ beamTrial‖ *
              kyFanApproximationGauge 2 (beamResidual ε) ≤
                1 * kyFanApproximationGauge 2 (beamResidual ε) :=
            mul_le_mul_of_nonneg_right hid hnn
          nlinarith [hF₁norm, norm_nonneg (selfAdjointSpectralSubspaceInclusion
            (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) beamHighSet
            measurableSet_beamHighSet), hnn, h1,
            mul_nonneg (norm_nonneg (ContinuousLinearMap.id ℂ beamTrial)) hnn]
      _ = kyFanApproximationGauge 2 (beamResidual ε) := by ring
      _ ≤ residualKyFanTwo ε := kyFanTwo_beamResidual_le ε
  have hchain : 500 * beamSinThetaSum ε ≤ residualKyFanTwo ε :=
    le_trans hmain.2 hres
  linarith

/-! ## Towards equations (9.5)--(9.7): the Rayleigh--Ritz residual

The tangent envelopes of Section 9 are `(eps * sqrt 15 / 15) / (500 - ritzHigh eps)`,
so the data an unbounded tangent theorem needs is: the Ritz compression, whose form is
bounded above by `ritzHigh eps`, and the Rayleigh--Ritz residual, whose norm is exactly
`orthogonalResidualSingularValue eps = |eps| * sqrt 15 / 15`.  Both are proved here.

The residual norm is obtained without computing the orthogonal projection: the
projection is the nearest point of the trial subspace, so testing against the explicit
competitor `ritzLow eps * alpha * phi_1 + ritzHigh eps * beta * phi_2` suffices, and the
resulting Gram form is exactly the recentered `orthogonalResidualGram eps`. -/

open DavisKahan1970.Section9 in
/-- The Ritz matrix of the perturbation against the orthonormal trial basis, in the
four-inner-product form the residual computation consumes. -/
theorem beamResidual_inner_trial (ε : ℝ) :
    ⟪centeredAffineLp trialOne, beamResidual ε beamTrialVecOne⟫_ℂ
        = ((ritzLow ε : ℝ) : ℂ) ∧
      ⟪centeredAffineLp trialOne, beamResidual ε beamTrialVecTwo⟫_ℂ = 0 ∧
        ⟪centeredAffineLp trialTwo, beamResidual ε beamTrialVecOne⟫_ℂ = 0 ∧
          ⟪centeredAffineLp trialTwo, beamResidual ε beamTrialVecTwo⟫_ℂ
            = ((ritzHigh ε : ℝ) : ℂ) := by
  obtain ⟨r00, r01, r11⟩ := beamRitz_matrix ε
  simp only [beamResidual_apply_vecOne, beamResidual_apply_vecTwo]
  refine ⟨r00, r01, ?_, r11⟩
  rw [← inner_conj_symm (𝕜 := ℂ) (centeredAffineLp trialTwo)
    (beamPerturbation ε (centeredAffineLp trialOne))]
  have hsa : ⟪beamPerturbation ε (centeredAffineLp trialOne),
      centeredAffineLp trialTwo⟫_ℂ
      = ⟪centeredAffineLp trialOne,
          beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ :=
    beamPerturbation_isSelfAdjoint ε _ _
  rw [hsa, r01, map_zero]

open DavisKahan1970.Section9 in
/-- **The recentered residual Gram form, in the orthonormal Ritz coordinates.**

For `x = α φ₁ + β φ₂` the part of `ε t x` orthogonal to the trial subspace has squared
norm at most `(ε²/30) |α − β|²`.  This is the *recentered* residual Gram matrix
`orthogonalResidualGram ε = (ε²/30) [[1, -1], [-1, 1]]` read as a quadratic form: it is
exactly rank one, and its kernel is the direction `α = β`.

The bound is obtained without computing the orthogonal projection: the projection is the
nearest point of the trial subspace, so testing against the explicit competitor
`ritzLow ε · α · φ₁ + ritzHigh ε · β · φ₂` suffices, and the resulting form collapses to
`(ε²/30) |α − β|²`. -/
theorem norm_beamRitzResidual_sq_le (ε : ℝ) (α β : ℂ) :
    ‖beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo)
        - beamTrial.starProjection
            (beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo))‖ ^ 2
      ≤ ε ^ 2 / 30 * ‖α - β‖ ^ 2 := by
  classical
  obtain ⟨g00, g01, g11⟩ := beamResidual_gram ε
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  obtain ⟨m00, m01, m10, m11⟩ := beamResidual_inner_trial ε
  have hg10 : ⟪beamResidual ε beamTrialVecTwo, beamResidual ε beamTrialVecOne⟫_ℂ
      = (((residualGram ε).a₀₁ : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (beamResidual ε beamTrialVecOne), g01, Complex.conj_ofReal]
  have m10' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialOne⟫_ℂ
      = ((ritzLow ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialOne), m00, Complex.conj_ofReal]
  have m01' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialOne), m01, map_zero]
  have m11' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialTwo⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialTwo), m10, map_zero]
  have m22' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialTwo⟫_ℂ
      = ((ritzHigh ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialTwo), m11, Complex.conj_ofReal]
  -- the explicit competitor in the trial subspace
  set u : BeamL2 := beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo) with hu
  set w : BeamL2 := (((ritzLow ε : ℝ) : ℂ) * α) • centeredAffineLp trialOne
    + (((ritzHigh ε : ℝ) : ℂ) * β) • centeredAffineLp trialTwo with hw
  have hwmem : w ∈ beamTrial := by
    rw [hw]
    exact beamTrial.add_mem
      (beamTrial.smul_mem _ (centeredAffineLp_mem_beamTrial _))
      (beamTrial.smul_mem _ (centeredAffineLp_mem_beamTrial _))
  have hmin : ‖u - beamTrial.starProjection u‖ ≤ ‖u - w‖ := by
    rw [beamTrial.starProjection_minimal u]
    exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨w, hwmem⟩ : beamTrial)
  -- expand `‖u - w‖²` against the two Gram matrices
  have hu' : u = α • beamResidual ε beamTrialVecOne
      + β • beamResidual ε beamTrialVecTwo := by
    rw [hu, map_add, map_smul, map_smul]
  have hinner : ⟪u - w, u - w⟫_ℂ
      = (((ε ^ 2 / 30 * ‖α - β‖ ^ 2 : ℝ)) : ℂ) := by
    have hα : α * (starRingEnd ℂ) α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hβ : β * (starRingEnd ℂ) β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hab : (α - β) * (starRingEnd ℂ) (α - β) = ((‖α - β‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have h75 : ((Real.sqrt 75 : ℝ) : ℂ) = 5 * ((Real.sqrt 3 : ℝ) : ℂ) := by
      norm_cast
      rw [show (75 : ℝ) = 5 ^ 2 * 3 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have hrhs : (((ε ^ 2 / 30 * ‖α - β‖ ^ 2 : ℝ)) : ℂ)
        = ((ε : ℂ) ^ 2 / 30) *
          ((α - β) * ((starRingEnd ℂ) α - (starRingEnd ℂ) β)) := by
      rw [show ((α - β) * ((starRingEnd ℂ) α - (starRingEnd ℂ) β))
          = (α - β) * (starRingEnd ℂ) (α - β) from by rw [map_sub], hab]
      push_cast
      ring
    rw [hu', hw]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, g00, g01, g11, hg10, q1, q2, q12, q21,
      m00, m01, m10, m11, m10', m01', m11', m22', map_mul, Complex.conj_ofReal]
    rw [hrhs]
    unfold residualGram ritzLow ritzHigh ritzLowCoefficient ritzHighCoefficient
    dsimp only
    push_cast
    rw [h75]
    linear_combination (-((ε : ℂ) ^ 2) / 36 *
      (α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β)) * h3
  have hnormsq : ‖u - w‖ ^ 2 = ε ^ 2 / 30 * ‖α - β‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := u - w)] at hinner
    have h2' : (((‖u - w‖ ^ 2 : ℝ)) : ℂ) = (((ε ^ 2 / 30 * ‖α - β‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast
      push_cast at hinner
      exact hinner
    exact Complex.ofReal_inj.mp h2'
  rw [← hnormsq]
  nlinarith [hmin, norm_nonneg (u - beamTrial.starProjection u), norm_nonneg (u - w)]

open DavisKahan1970.Section9 in
/-- **The Rayleigh--Ritz residual bound.**  The part of `ε t x` orthogonal to the trial
subspace has norm at most `orthogonalResidualSingularValue ε = |ε| √15/15`.  This is the
exact operator-norm content of the *recentered* residual Gram matrix
`orthogonalResidualGram ε = (ε²/30) [[1, -1], [-1, 1]]`, whose nonzero eigenvalue is
`ε²/15`. -/
theorem norm_beamRitzResidual_le (ε : ℝ) (x : beamTrial) :
    ‖beamResidual ε x - beamTrial.starProjection (beamResidual ε x)‖
      ≤ orthogonalResidualSingularValue ε * ‖x‖ := by
  classical
  obtain ⟨α, β, hx⟩ := exists_beamTrialVec_repr x
  subst hx
  have hsq := norm_beamRitzResidual_sq_le ε α β
  have hxnorm : ‖α • beamTrialVecOne + β • beamTrialVecTwo‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 :=
    norm_sq_beamTrialVec_comb α β
  have hσ : orthogonalResidualSingularValue ε ^ 2 = ε ^ 2 / 15 := by
    unfold orthogonalResidualSingularValue
    have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
    have : |ε| ^ 2 = ε ^ 2 := sq_abs ε
    nlinarith [Real.sqrt_nonneg (15 : ℝ), abs_nonneg ε]
  have hsub : ‖α - β‖ ^ 2 ≤ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) := by
    have htri : ‖α - β‖ ≤ ‖α‖ + ‖β‖ := norm_sub_le α β
    nlinarith [norm_nonneg α, norm_nonneg β, norm_nonneg (α - β),
      sq_nonneg (‖α‖ - ‖β‖)]
  refine le_of_sq_le_sq'
    (mul_nonneg (by unfold orthogonalResidualSingularValue; positivity)
      (norm_nonneg _)) ?_
  rw [mul_pow, hσ, hxnorm]
  nlinarith [hsq, hsub, sq_nonneg ε]

open DavisKahan1970.Section9 in
/-- **The recentered residual annihilates the constant direction.**

`orthogonalResidualGram ε = (ε²/30) [[1, -1], [-1, 1]]` is exactly rank one, and
`φ₁ + φ₂` spans its kernel.  Concretely, `φ₁ + φ₂` is a multiple of the constant
function, and `ε t · 1 = ε t` is itself affine, so the Rayleigh--Ritz residual there
vanishes identically rather than merely being small. -/
theorem beamRitzResidual_vecOne_add_vecTwo_eq_zero (ε : ℝ) :
    beamResidual ε (beamTrialVecOne + beamTrialVecTwo)
        - beamTrial.starProjection
            (beamResidual ε (beamTrialVecOne + beamTrialVecTwo)) = 0 := by
  have h := norm_beamRitzResidual_sq_le ε 1 1
  rw [one_smul, one_smul, sub_self, norm_zero] at h
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  nlinarith [h, norm_nonneg (beamResidual ε (beamTrialVecOne + beamTrialVecTwo)
    - beamTrial.starProjection (beamResidual ε (beamTrialVecOne + beamTrialVecTwo)))]

open DavisKahan1970.Section9 in
/-- **The Ritz compression form bound.**  The Rayleigh--Ritz compression of `ε t` to the
affine trial subspace has quadratic form bounded above by the upper Ritz value
`ritzHigh ε`.  This is the `hCompression` hypothesis of the unbounded tangent theorem,
read off from `beamRitz_matrix`: the compression is diagonal with entries `ritzLow ε` and
`ritzHigh ε`. -/
theorem beamRitz_form_le (ε : ℝ) (hε : 0 ≤ ε) (x : beamTrial) :
    RCLike.re ⟪beamResidual ε x, (x : BeamL2)⟫_ℂ ≤ ritzHigh ε * ‖x‖ ^ 2 := by
  classical
  obtain ⟨α, β, hx⟩ := exists_beamTrialVec_repr x
  subst hx
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  obtain ⟨m00, m01, m10, m11⟩ := beamResidual_inner_trial ε
  have m10' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialOne⟫_ℂ
      = ((ritzLow ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialOne), m00, Complex.conj_ofReal]
  have m01' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialOne), m01, map_zero]
  have m11' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialTwo⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialTwo), m10, map_zero]
  have m22' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialTwo⟫_ℂ
      = ((ritzHigh ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialTwo), m11, Complex.conj_ofReal]
  have hu' : beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo)
      = α • beamResidual ε beamTrialVecOne
        + β • beamResidual ε beamTrialVecTwo := by
    rw [map_add, map_smul, map_smul]
  have hxc : ((α • beamTrialVecOne + β • beamTrialVecTwo : beamTrial) : BeamL2)
      = α • centeredAffineLp trialOne + β • centeredAffineLp trialTwo := rfl
  have hα : α * (starRingEnd ℂ) α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hβ : β * (starRingEnd ℂ) β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hinner : ⟪beamResidual ε (α • beamTrialVecOne + β • beamTrialVecTwo),
        ((α • beamTrialVecOne + β • beamTrialVecTwo : beamTrial) : BeamL2)⟫_ℂ
      = (((‖α‖ ^ 2 * ritzLow ε + ‖β‖ ^ 2 * ritzHigh ε : ℝ)) : ℂ) := by
    rw [hu', hxc]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      m10', m01', m11', m22']
    rw [show α * ((starRingEnd ℂ) α * ((ritzLow ε : ℝ) : ℂ) + (starRingEnd ℂ) β * 0)
          + β * ((starRingEnd ℂ) α * 0
            + (starRingEnd ℂ) β * ((ritzHigh ε : ℝ) : ℂ))
        = (α * (starRingEnd ℂ) α) * ((ritzLow ε : ℝ) : ℂ)
          + (β * (starRingEnd ℂ) β) * ((ritzHigh ε : ℝ) : ℂ) from by ring,
      hα, hβ]
    push_cast
    ring
  rw [hinner]
  have hre : RCLike.re ((((‖α‖ ^ 2 * ritzLow ε + ‖β‖ ^ 2 * ritzHigh ε : ℝ)) : ℂ))
      = ‖α‖ ^ 2 * ritzLow ε + ‖β‖ ^ 2 * ritzHigh ε := rfl
  rw [hre, norm_sq_beamTrialVec_comb]
  have hgap : ritzLow ε ≤ ritzHigh ε := by
    have h := ritzHigh_sub_ritzLow ε
    have : 0 ≤ ε * (Real.sqrt 3 / 3) := by positivity
    linarith
  nlinarith [sq_nonneg ‖α‖, sq_nonneg ‖β‖, norm_nonneg α, norm_nonneg β]

/-! ## Equations (9.5)--(9.7), part (b): the perturbed spectral gap

The tangent theorems need a gap for the *perturbed* operator: no spectrum between the
upper Ritz value and `500`.  Equations (9.1), (9.2) and (9.4) never needed one --
they are stated against a spectral set, so the restriction's spectrum is inside it by
construction.  A tangent bound needs both spectra separated.

The gap is Rayleigh--Ritz, and the general theorem is
`TauCeti.LinearPMap.specProjection_Ioo_eq_zero_of_rayleighRitz`: a trial subspace on
which the form is at most `α`, whose orthogonal complement carries a form bound of at
least `β`, forces the spectrum to avoid `(α, β)`.  Here the trial subspace is the
kernel `beamTrial`, the Ritz bound is `beamRitz_form_le`, and coercivity off the trial
subspace comes from the *sharp* free-beam gap `500.5` together with positivity of the
perturbation. -/

/-- The perturbation is positive: its symbol `ε t` is nonnegative on `(0, 1]`. -/
theorem re_inner_beamPerturbation_nonneg (ε : ℝ) (hε : 0 ≤ ε) (x : BeamL2) :
    0 ≤ (⟪beamPerturbation ε x, x⟫_ℂ).re := by
  have hconv : ⟪beamPerturbation ε x, x⟫_ℂ
      = (((∫ t, ε * t * ‖(x : ℝ → ℂ) t‖ ^ 2 ∂unitIocMeasure : ℝ)) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← _root_.integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_beamPerturbation ε x] with t ht
    have hz : (x : ℝ → ℂ) t * (starRingEnd ℂ) ((x : ℝ → ℂ) t)
        = ((‖(x : ℝ → ℂ) t‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [RCLike.inner_apply, ht, map_mul, Complex.conj_ofReal]
    push_cast at hz ⊢
    linear_combination ((ε : ℂ) * (t : ℂ)) * hz
  rw [hconv, Complex.ofReal_re]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_mem_unitIocMeasure] with t ht
  have h0 : (0 : ℝ) ≤ t := le_of_lt ht.1
  positivity

/-- **The kernel spectral range is inside the trial subspace.**  A vector selected by
the eigenvalue `{0}` lies in the domain, is annihilated by the free beam, and is
therefore affine. -/
theorem mem_beamTrial_of_mem_specRange_singleton {y : BeamL2}
    (hy : y ∈ TauCeti.LinearPMap.specRange beamOperator_isSelfAdjoint ({0} : Set ℝ)
      (measurableSet_singleton 0)) :
    y ∈ beamTrial := by
  have hbnd : ∀ s ∈ ({0} : Set ℝ), |s| ≤ 0 := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    simp [hs]
  have hdom : y ∈ beamOperator.domain :=
    TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded beamOperator_isSelfAdjoint
      _ _ hbnd hy
  have hzero : beamOperator ⟨y, hdom⟩ = 0 := by
    have hle := TauCeti.LinearPMap.norm_sub_smul_le_of_mem_specRange
      beamOperator_isSelfAdjoint ({0} : Set ℝ) (measurableSet_singleton 0)
      (M := 0) (c := 0) (r := 0) hbnd le_rfl
      (fun s hs => by rw [Set.mem_singleton_iff] at hs; simp [hs]) hy hdom
    rw [Complex.ofReal_zero, zero_smul, sub_zero, zero_mul] at hle
    exact norm_le_zero_iff.mp hle
  obtain ⟨a, b, hab⟩ := exists_affine_of_beamOperator_eq_zero hzero
  rw [show y = affineLp a b from hab]
  exact affineLp_mem_beamTrial a b

/-- A vector orthogonal to the trial subspace carries no kernel spectral mass. -/
theorem beamSpecProjection_singleton_apply_eq_zero_of_mem_orthogonal {x : BeamL2}
    (hx : x ∈ beamTrialᗮ) :
    TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint ({0} : Set ℝ)
      (measurableSet_singleton 0) x = 0 := by
  set P := TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint ({0} : Set ℝ)
    (measurableSet_singleton 0) with hP
  have hmem : P x ∈ beamTrial :=
    mem_beamTrial_of_mem_specRange_singleton
      (TauCeti.LinearPMap.specProjection_mem_specRange beamOperator_isSelfAdjoint _ _ x)
  have hfix : P (P x) = P x :=
    TauCeti.LinearPMap.specProjection_apply_self beamOperator_isSelfAdjoint _ _ x
  have hadj : (P : BeamL2 →L[ℂ] BeamL2).adjoint = P :=
    (TauCeti.LinearPMap.isSelfAdjoint_specProjection beamOperator_isSelfAdjoint _ _).adjoint_eq
  have hzero : ⟪P x, P x⟫_ℂ = 0 := by
    nth_rewrite 1 [← hadj]
    rw [ContinuousLinearMap.adjoint_inner_left, hfix, ← inner_conj_symm, hx _ hmem, map_zero]
  simpa using inner_self_eq_zero.mp hzero

/-- **Coercivity of the free beam off its kernel.**  The sharp gap `500.5` is a form
bound on the orthogonal complement of the trial subspace. -/
theorem beamOperator_form_ge_of_mem_orthogonal (x : beamOperator.domain)
    (hx : (x : BeamL2) ∈ beamTrialᗮ) :
    (1001 / 2 : ℝ) * ‖(x : BeamL2)‖ ^ 2
      ≤ (⟪beamOperator x, (x : BeamL2)⟫_ℂ).re := by
  refine TauCeti.LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
    beamOperator_isSelfAdjoint (c := 1001 / 2) x ?_
  have hlow : TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint beamLowSet
      measurableSet_beamLowSet (x : BeamL2) = 0 := by
    rw [beamSpecProjection_lowSet_eq_singleton]
    exact beamSpecProjection_singleton_apply_eq_zero_of_mem_orthogonal hx
  exact hlow

/-- **Coercivity of the perturbed beam off the trial subspace.**  The perturbation is
positive, so it only helps. -/
theorem beamPerturbed_form_ge_of_mem_orthogonal (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamPerturbed ε).domain) (hx : (x : BeamL2) ∈ beamTrialᗮ) :
    (1001 / 2 : ℝ) * ‖(x : BeamL2)‖ ^ 2
      ≤ (⟪(beamPerturbed ε) x, (x : BeamL2)⟫_ℂ).re := by
  have hxdom : (x : BeamL2) ∈ beamOperator.domain := x.2
  have hsplit : (beamPerturbed ε) x
      = beamOperator ⟨(x : BeamL2), hxdom⟩ + beamPerturbation ε (x : BeamL2) :=
    rfl
  rw [hsplit, inner_add_left, Complex.add_re]
  have h1 := beamOperator_form_ge_of_mem_orthogonal ⟨(x : BeamL2), hxdom⟩ hx
  have h2 := re_inner_beamPerturbation_nonneg ε hε (x : BeamL2)
  linarith

/-- **The Ritz bound on the trial subspace.**  On the kernel the free beam contributes
nothing, so the form is exactly the perturbation's, bounded by the upper Ritz value. -/
theorem beamPerturbed_form_le_of_mem_beamTrial (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamPerturbed ε).domain) (hx : (x : BeamL2) ∈ beamTrial) :
    (⟪(beamPerturbed ε) x, (x : BeamL2)⟫_ℂ).re
      ≤ DavisKahan1970.Section9.ritzHigh ε * ‖(x : BeamL2)‖ ^ 2 := by
  have hxdom : (x : BeamL2) ∈ beamOperator.domain := x.2
  have hsplit : (beamPerturbed ε) x
      = beamOperator ⟨(x : BeamL2), hxdom⟩ + beamPerturbation ε (x : BeamL2) :=
    rfl
  have hker : beamOperator ⟨(x : BeamL2), hxdom⟩ = 0 :=
    beamOperator_apply_trial hx hxdom
  have hres : beamPerturbation ε (x : BeamL2)
      = beamResidual ε (⟨(x : BeamL2), hx⟩ : beamTrial) := rfl
  rw [hsplit, hker, zero_add, hres]
  have h := beamRitz_form_le ε hε (⟨(x : BeamL2), hx⟩ : beamTrial)
  exact h

open DavisKahan1970.Section9 in
/-- **The perturbed spectral gap, equations (9.5)--(9.7) part (b).**
`A + ε t` has no spectrum between the upper Ritz value and `500`.

Nothing is assumed beyond `0 ≤ ε`.  The two Rayleigh--Ritz inputs are proved for the
genuine operator: the compression to the affine trial subspace has form at most
`ritzHigh ε`, and the complement of that subspace carries the sharp free-beam gap
`500.5`, which the positive perturbation cannot lower. -/
theorem beamPerturbed_specProjection_Ioo_eq_zero (ε : ℝ) (hε : 0 ≤ ε) :
    TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Ioo (ritzHigh ε) 500) measurableSet_Ioo = 0 := by
  refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset
    (beamPerturbed_isSelfAdjoint ε) (C := Set.Ioo (ritzHigh ε) (1001 / 2))
    measurableSet_Ioo measurableSet_Ioo
    (Set.Ioo_subset_Ioo le_rfl (by norm_num)) ?_
  exact TauCeti.LinearPMap.specProjection_Ioo_eq_zero_of_rayleighRitz
    (beamPerturbed_isSelfAdjoint ε) (K := beamTrial)
    (fun _ hy => beamTrial_le_domain hy)
    (fun y hy => beamPerturbed_form_le_of_mem_beamTrial ε hε y hy)
    (fun y hy => beamPerturbed_form_ge_of_mem_orthogonal ε hε y hy)

end

open DavisKahan1970.Section9 in
/-- **Equation (9.1) for the beam, in the printed numerals.**

`beamSinTheta_le` bounds the angle by the residual's exact top singular value over
the gap; `equation_9_1` turns that exact value into the source's decimal.  Composing
them is what makes the row's evidence *unconditional*: the numeric wrapper alone is
conditional on an analytic bound the reader has to supply, and this supplies it. -/
theorem beamSinTheta_lt_printed (ε : ℝ) (hε : 0 < ε) :
    beamSinTheta ε < (811 : ℝ) / 500000 * ε :=
  equation_9_1 ε (beamSinTheta ε) hε (beamSinTheta_le ε)

open DavisKahan1970.Section9 in
/-- **Equation (9.3) for the beam, in the printed numerals.**  The two-term Ky Fan
norm version of the previous theorem. -/
theorem beamSinThetaSum_lt_printed (ε : ℝ) (hε : 0 < ε) :
    beamSinThetaSum ε < (109 : ℝ) / 50000 * ε :=
  equation_9_3 ε (beamSinThetaSum ε) hε (beamSinThetaSum_le ε)

end Model
end FreeBeam
end DavisKahan
end TauCeti
