/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BoundaryAxisJets
import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
public import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricEvenDescent
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveAxisSystem
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSmoothFamily
import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily

/-!
# Local slow-order recursion from actual lower profiles

The source algebra consists of genuine smooth, even radial functions with
holomorphic parameter dependence. No preconstructed all-order jet family
is assumed.
-/

section

/-!
# Actual positive-order axis solutions

This module connects the sparse six-component Volterra construction to the
explicit positive-order system, and to smooth profiles in the squared radius.
All existence assertions are obtained from the actual convergent series.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PositiveAxisExistence

open Set Filter
open scoped Topology ContDiff
open VolterraAnalyticBounds VolterraParity VolterraRegularity
open NilpotentVolterra (equationRHS weightedMean regularPrimitive)

/-- Cache the standard `NormedAddCommGroup (Matrix (Fin 6) (Fin 6) ℂ)` instance to shorten
typeclass synthesis. -/
local instance instPositiveAxisExistence1 : NormedAddCommGroup (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedAddCommGroup (Fin 6 → Fin 6 → ℂ))
/-- Cache the standard `NormedSpace ℝ (Matrix (Fin 6) (Fin 6) ℂ)` instance to shorten typeclass
synthesis. -/
local instance instPositiveAxisExistence2 : NormedSpace ℝ (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedSpace ℝ (Fin 6 → Fin 6 → ℂ))
/-- Cache the standard `NormedSpace ℂ (Matrix (Fin 6) (Fin 6) ℂ)` instance to shorten typeclass
synthesis. -/
local instance instPositiveAxisExistence3 : NormedSpace ℂ (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedSpace ℂ (Fin 6 → Fin 6 → ℂ))

section DifferentialEquation

variable {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
  {A₀ A₁ : Coeff} {f W : Field}
  (hW : IsSymmetricIntegralSolution R U A₀ A₁ f W)
  (hdata : SmoothCoefficientData R U A₀ A₁ f)

include hR hU hW hdata

/-- The right side of the actual integral equation is radially continuous;
the parameter derivative is supplied by the proved disk-space bootstrap. -/
theorem equationRHS_radial_continuous {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    ContinuousOn (fun r => equationRHS A₀ A₁ f W r z i) (radialDomain R) := by
  have hf : ContinuousOn (fun r => f r z i) (radialDomain R) :=
    (hdata.forcing i).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, hz⟩)
  have ha₀ (j : Fin 6) : ContinuousOn (fun r => A₀ r z i j) (radialDomain R) :=
    (hdata.zeroth i j).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, hz⟩)
  have ha₁ (j : Fin 6) : ContinuousOn (fun r => A₁ r z i j) (radialDomain R) :=
    (hdata.first i j).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, hz⟩)
  have hw (j : Fin 6) : ContinuousOn (fun r => W r z j) (radialDomain R) := by
    simpa only [iteratedDeriv_zero] using
      (symmetric_solution_parameterJets_radial_contDiffOn_local hR hU hW hdata hz 0 j).continuousOn
  have hd (j : Fin 6) : ContinuousOn (fun r => deriv (fun v => W r v j) z)
      (radialDomain R) := by
    simpa only [iteratedDeriv_one] using
      (symmetric_solution_parameterJets_radial_contDiffOn_local hR hU hW hdata hz 1 j).continuousOn
  exact hf.add ((continuousOn_finsetSum Finset.univ fun j _ => (ha₀ j).mul (hw j)).add
    (continuousOn_finsetSum Finset.univ fun j _ => (ha₁ j).mul (hd j)))

/-- The actual symmetric solution has the regular, nonsingular derivative
formula at every interior radius, including the axis. -/
theorem solution_hasDerivAt {r : ℝ} (hr : r ∈ radialDomain R)
    {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    HasDerivAt (fun s => W s z i)
      (equationRHS A₀ A₁ f W r z i - (exponent i : ℝ) •
        weightedMean (exponent i) (fun s => equationRHS A₀ A₁ f W s z i) r) r := by
  have heq : (fun s => W s z i) =ᶠ[𝓝 r]
      regularPrimitive (exponent i) (fun s => equationRHS A₀ A₁ f W s z i) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hr] with s hs
    exact congrFun (hW.integral_equation s (radialDomain_subset_Icc R hs) z hz) i
  exact (regularPrimitive_hasDerivAt_on (exponent i)
    (equationRHS_radial_continuous hR hU hW hdata hz i) hr).congr_of_eventuallyEq heq

/-- The singular first-order equation holds with genuine derivatives at
every nonzero interior radius. -/
theorem solution_differential_equation {r : ℝ} (hr : r ∈ radialDomain R)
    (hr0 : r ≠ 0) {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    deriv (fun s => W s z i) r + ((exponent i : ℝ) / r) • W r z i =
      equationRHS A₀ A₁ f W r z i := by
  rw [(solution_hasDerivAt hR hU hW hdata hr hz i).deriv]
  have heq := congrFun (hW.integral_equation r (radialDomain_subset_Icc R hr) z hz) i
  change W r z i = regularPrimitive (exponent i)
    (fun s => equationRHS A₀ A₁ f W s z i) r at heq
  rw [heq, regularPrimitive, smul_smul, div_mul_cancel₀ _ hr0, sub_add_cancel]

end DifferentialEquation

section CoefficientPaths

/-- The standard matrix representation, as an actual bounded operator on the
six-component space. -/
noncomputable def matrixOperator : Matrix (Fin 6) (Fin 6) ℂ →L[ℂ] (Vec →L[ℂ] Vec) :=
  ((Matrix.toLin' : Matrix (Fin 6) (Fin 6) ℂ ≃ₗ[ℂ] Vec →ₗ[ℂ] Vec).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem matrixOperator_apply (A : Matrix (Fin 6) (Fin 6) ℂ) (v : Vec) :
    matrixOperator A v = A.mulVec v := rfl

@[simp] theorem matrixOperator_toMatrix (A : Matrix (Fin 6) (Fin 6) ℂ) :
    LinearMap.toMatrix' (matrixOperator A).toLinearMap = A :=
  LinearMap.toMatrix'_toLin' A

/-- Packaging the actual radial matrix coefficient in the compact path space. -/
noncomputable def matrixPath (R : ℝ) (A : Coeff) : ℂ → SymmetricCoefficientPath R :=
  CompactSmoothFamily.family (Icc (-R) R) (fun p : ℂ × ℝ => matrixOperator (A p.2 p.1))

/-- Packaging the actual forcing in the compact path space. -/
noncomputable def forcingPath (R : ℝ) (f : Field) : ℂ → SymmetricPath R Vec :=
  CompactSmoothFamily.family (Icc (-R) R) (fun p : ℂ × ℝ => f p.2 p.1)

theorem matrixPath_apply {R : ℝ} {A : Coeff} {z : ℂ}
    (hA : Continuous (fun r : Icc (-R) R => A r z)) (r : Icc (-R) R) :
    matrixPath R A z r = matrixOperator (A r z) :=
  CompactSmoothFamily.family_apply _ _ _ (matrixOperator.continuous.comp hA) r

theorem forcingPath_apply {R : ℝ} {f : Field} {z : ℂ}
    (hf : Continuous (fun r : Icc (-R) R => f r z)) (r : Icc (-R) R) :
    forcingPath R f z r = f r z :=
  CompactSmoothFamily.family_apply _ _ _ hf r

theorem raw_matrixPath {R : ℝ} (hR : 0 ≤ R) {A : Coeff} {z : ℂ}
    (hA : Continuous (fun r : Icc (-R) R => A r z))
    {r : ℝ} (hr : r ∈ Icc (-R) R) :
    symmetricRawCoefficient hR (matrixPath R A) r z = A r z := by
  unfold symmetricRawCoefficient
  rw [matrixPath_apply hA, matrixOperator_toMatrix, projIcc_of_mem (by linarith) hr]

theorem raw_forcingPath {R : ℝ} (hR : 0 ≤ R) {f : Field} {z : ℂ}
    (hf : Continuous (fun r : Icc (-R) R => f r z))
    {r : ℝ} (hr : r ∈ Icc (-R) R) :
    symmetricRawField hR (forcingPath R f) r z = f r z := by
  unfold symmetricRawField
  rw [forcingPath_apply hf, projIcc_of_mem (by linarith) hr]

theorem matrixPath_shape {R : ℝ} (hR : 0 ≤ R) {A : Coeff}
    (hA : DerivativeShape A) : DerivativeShape (symmetricRawCoefficient hR (matrixPath R A)) := by
  intro r z i j hij
  classical
  by_cases hc : Continuous (fun x : Icc (-R) R => matrixOperator (A x z))
  · simp only [symmetricRawCoefficient, matrixPath, CompactSmoothFamily.family,
      dite_eq_left hc, ContinuousMap.coe_mk, matrixOperator_toMatrix]
    exact hA _ z i j hij
  · simp [symmetricRawCoefficient, matrixPath, CompactSmoothFamily.family, hc]

theorem scaled_mem_symmetricInterval {R r t : ℝ} (hr : r ∈ Icc (-R) R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (-R) R := by
  apply abs_le.mp
  calc
    |t * r| = t * |r| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ |r| := mul_le_of_le_one_left (abs_nonneg r) ht.2
    _ ≤ R := abs_le.mpr hr

theorem solution_change_data {R : ℝ} {U : Set ℂ}
    {A₀ A₁ B₀ B₁ : Coeff} {f g W : Field}
    (h : IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (h₀ : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, A₀ r z = B₀ r z)
    (h₁ : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, A₁ r z = B₁ r z)
    (hf : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, f r z = g r z) :
    IsSymmetricIntegralSolution R U B₀ B₁ g W := by
  refine { h with integral_equation := ?_ }
  intro r hr z hz
  rw [h.integral_equation r hr z hz]
  apply radialInverse_congr_at
  intro t ht
  have htr := scaled_mem_symmetricInterval hr ht
  simp only [equationRHS, matrixAction, h₀ _ htr _ hz, h₁ _ htr _ hz, hf _ htr _ hz]

/-- Smoothness and parameter holomorphy of the given coefficients. These
are hypotheses only on input functions. -/
structure SmoothHolomorphicSystem (T : ℝ) (U : Set ℂ) (A₀ A₁ : Coeff) (f : Field) : Prop where
  smooth : SmoothCoefficientData T U A₀ A₁ f
  zeroth_holomorphic : ∀ r ∈ radialDomain T, DifferentiableOn ℂ (A₀ r) U
  first_holomorphic : ∀ r ∈ radialDomain T, DifferentiableOn ℂ (A₁ r) U
  forcing_holomorphic : ∀ r ∈ radialDomain T, DifferentiableOn ℂ (f r) U

theorem symmetricInterval_subset_radialDomain {R T : ℝ} (hRT : R < T) :
    Icc (-R) R ⊆ radialDomain T := by
  intro r hr
  simpa only [radialDomain, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
    (abs_le.mpr hr).trans_lt hRT

theorem radialDomain_mono {R T : ℝ} (hRT : R ≤ T) : radialDomain R ⊆ radialDomain T :=
  Metric.ball_subset_ball hRT

theorem SmoothHolomorphicSystem.restrict {R T : ℝ} {U : Set ℂ} {A₀ A₁ : Coeff} {f : Field}
    (h : SmoothHolomorphicSystem T U A₀ A₁ f) (hRT : R ≤ T) :
    SmoothHolomorphicSystem R U A₀ A₁ f := by
  let hs : radialDomain R ×ˢ U ⊆ radialDomain T ×ˢ U :=
    Set.prod_mono (radialDomain_mono hRT) Subset.rfl
  exact {
    smooth := {
      forcing := fun i => (h.smooth.forcing i).mono hs
      zeroth := fun i j => (h.smooth.zeroth i j).mono hs
      first := fun i j => (h.smooth.first i j).mono hs }
    zeroth_holomorphic := fun r hr => h.zeroth_holomorphic r (radialDomain_mono hRT hr)
    first_holomorphic := fun r hr => h.first_holomorphic r (radialDomain_mono hRT hr)
    forcing_holomorphic := fun r hr => h.forcing_holomorphic r (radialDomain_mono hRT hr) }

end CoefficientPaths

section AnalyticAssembly

theorem matrixPath_holomorphic {R T : ℝ} (hRT : R < T) {U : Set ℂ} (hU : IsOpen U)
    {A : Coeff}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A p.1 p.2 i j)
      (radialDomain T ×ˢ U))
    (hhol : ∀ r ∈ radialDomain T, DifferentiableOn ℂ (A r) U) :
    DifferentiableOn ℂ (matrixPath R A) U := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A p.1 p.2) (radialDomain T ×ˢ U) :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr (hA i)
  apply HolomorphicFamily.differentiableOn_family_of_joint (Icc (-R) R) U (radialDomain T)
    hU Metric.isOpen_ball (symmetricInterval_subset_radialDomain hRT)
  · exact (matrixOperator.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hs.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩))
  · intro r hr
    exact matrixOperator.differentiable.comp_differentiableOn
      (hhol r (symmetricInterval_subset_radialDomain hRT hr))

theorem forcingPath_holomorphic {R T : ℝ} (hRT : R < T) {U : Set ℂ} (hU : IsOpen U)
    {f : Field}
    (hf : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f p.1 p.2 i) (radialDomain T ×ˢ U))
    (hhol : ∀ r ∈ radialDomain T, DifferentiableOn ℂ (f r) U) :
    DifferentiableOn ℂ (forcingPath R f) U := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f p.1 p.2) (radialDomain T ×ˢ U) :=
    contDiffOn_pi.mpr hf
  apply HolomorphicFamily.differentiableOn_family_of_joint (Icc (-R) R) U (radialDomain T)
    hU Metric.isOpen_ball (symmetricInterval_subset_radialDomain hRT)
  · exact hs.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩)
  · intro r hr
    exact hhol r (symmetricInterval_subset_radialDomain hRT hr)

theorem matrix_slice_continuous {R T : ℝ} (hRT : R < T) {U : Set ℂ} {A : Coeff}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A p.1 p.2 i j)
      (radialDomain T ×ˢ U)) {z : ℂ} (hz : z ∈ U) :
    Continuous (fun r : Icc (-R) R => A r z) := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A p.1 p.2) (radialDomain T ×ˢ U) :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr (hA i)
  exact hs.continuousOn.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun r => ⟨symmetricInterval_subset_radialDomain hRT r.2, hz⟩)

theorem forcing_slice_continuous {R T : ℝ} (hRT : R < T) {U : Set ℂ} {f : Field}
    (hf : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f p.1 p.2 i) (radialDomain T ×ˢ U))
    {z : ℂ} (hz : z ∈ U) : Continuous (fun r : Icc (-R) R => f r z) := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f p.1 p.2) (radialDomain T ×ˢ U) :=
    contDiffOn_pi.mpr hf
  exact hs.continuousOn.comp_continuous (continuous_subtype_val.prodMk continuous_const)
    (fun r => ⟨symmetricInterval_subset_radialDomain hRT r.2, hz⟩)

/-- The actual canonical solution for raw matrix coefficients. -/
noncomputable def assembledSolution {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : Coeff) (f : Field) : Field :=
  symmetricSolution hR (matrixPath R A₀) (matrixPath R A₁) (forcingPath R f)

theorem assembledSolution_spec {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {A₀ A₁ : Coeff} {f : Field}
    (hdata : SmoothHolomorphicSystem T U A₀ A₁ f) (hshape : DerivativeShape A₁) :
    IsSymmetricIntegralSolution R U A₀ A₁ f (assembledSolution hR A₀ A₁ f) := by
  have h := symmetricSolution_spec hR hU
    (matrixPath_holomorphic hRT hU hdata.smooth.zeroth hdata.zeroth_holomorphic)
    (matrixPath_holomorphic hRT hU hdata.smooth.first hdata.first_holomorphic)
    (forcingPath_holomorphic hRT hU hdata.smooth.forcing hdata.forcing_holomorphic)
    (matrixPath_shape hR hshape)
  exact solution_change_data h
    (fun r hr z hz => raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.zeroth hz) hr)
    (fun r hr z hz => raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.first hz) hr)
    (fun r hr z hz => raw_forcingPath hR (forcing_slice_continuous hRT hdata.smooth.forcing hz) hr)

theorem assembledSolution_parity {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {A₀ A₁ : Coeff} {f : Field}
    (hdata : SmoothHolomorphicSystem T U A₀ A₁ f) (hshape : DerivativeShape A₁)
    (hp₀ : CoefficientParity A₀) (hp₁ : CoefficientParity A₁) (hpf : ForcingParity f)
    {r : ℝ} (hr : r ∈ Icc (-R) R) {z : ℂ} (hz : z ∈ U) :
    assembledSolution hR A₀ A₁ f (-r) z = parityVec (assembledSolution hR A₀ A₁ f r z) := by
  apply symmetricSolution_parity hR hU
    (matrixPath_holomorphic hRT hU hdata.smooth.zeroth hdata.zeroth_holomorphic)
    (matrixPath_holomorphic hRT hU hdata.smooth.first hdata.first_holomorphic)
    (forcingPath_holomorphic hRT hU hdata.smooth.forcing hdata.forcing_holomorphic)
    (matrixPath_shape hR hshape) _ _ _ hr hz
  · intro s hs v hv i j
    rw [raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.zeroth hv)
        (show -s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2]),
      raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.zeroth hv)
        (show s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2])]
    exact hp₀ s v i j
  · intro s hs v hv i j
    rw [raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.first hv)
        (show -s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2]),
      raw_matrixPath hR (matrix_slice_continuous hRT hdata.smooth.first hv)
        (show s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2])]
    exact hp₁ s v i j
  · intro s hs v hv i
    rw [raw_forcingPath hR (forcing_slice_continuous hRT hdata.smooth.forcing hv)
        (show -s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2]),
      raw_forcingPath hR (forcing_slice_continuous hRT hdata.smooth.forcing hv)
        (show s ∈ Icc (-R) R by constructor <;> linarith [hs.1, hs.2])]
    exact hpf s v i

/-- The disk-valued radial bootstrap and the Cauchy integral combine to
give joint real smoothness, rather than merely separate smoothness. -/
theorem solution_jointly_smooth {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field} (hW : IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U) := by
  apply contDiffOn_pi.mpr
  intro i p hp
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.2)
  let ρ := interiorRadii δ
  have hρ := interiorRadii_increasing hδ
  have hDisk := interiorRadii_subset hδ p.2 hball
  let V := fun r => fieldDiskCurve R hR W hW.jointly_continuous p.2 (ρ 0) (hDisk 0) r i
  have hV : ContDiffOn ℝ ∞ V (radialDomain R) :=
    symmetric_solution_disk_curves_of_smooth_coefficients hR hU hW hdata p.2 ρ hρ hDisk 0 i
  have hj := HolomorphicFamily.contDiffOn_of_disk_family p.2 (interiorRadii_pos hδ 0)
    V (fun r z => W r z i) hV
    (fun r hr => (hW.parameter_holomorphic r (radialDomain_subset_Icc R hr) i).mono
      (fun z hz => hDisk 0 (Metric.ball_subset_closedBall hz)))
    (fun r hr z => fieldDiskCurve_apply R hR W hW.jointly_continuous p.2 (ρ 0) (hDisk 0)
      (radialDomain_subset_Icc R hr) i z)
  exact (hj.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
    ⟨hp.1, Metric.mem_ball_self (interiorRadii_pos hδ 0)⟩)).contDiffWithinAt

end AnalyticAssembly

section ExplicitInputs

open PositiveAxisSystem

/-- Transparent regularity assumptions on the eleven finite lower-order
input functions. Smoothness is required of the signed square pullback, so
there is no artificial requirement on a negative-`X` extension. -/
structure LowerInputRegularity (T : ℝ) (U : Set ℂ) (h : ℂ)
    (F : CoefficientData) : Prop where
  radial_smooth : ∀ i, ContDiffOn ℝ ∞
    (fun p : ℝ × ℂ => F i (p.1 ^ 2, p.2)) (radialDomain T ×ˢ U)
  holomorphic : ∀ r ∈ radialDomain T, ∀ i,
    DifferentiableOn ℂ (fun z => F i (r ^ 2, z)) U
  denominator : ∀ z ∈ U, ell h z ≠ 0

theorem LowerInputRegularity.system {T : ℝ} {U : Set ℂ} (hU : IsOpen U)
    {h : ℂ} (lam C : ℂ) {F : CoefficientData} (hF : LowerInputRegularity T U h F) :
    SmoothHolomorphicSystem T U (coefficient0 h lam C F) (coefficient1 h F)
      (sourceField h C F) := by
  have hs (w : ℝ × ℂ) (hw : w ∈ radialDomain T ×ˢ U) (i : Fin 11) :
      ContDiffAt ℝ ∞ (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w :=
    (hF.radial_smooth i).contDiffAt ((Metric.isOpen_ball.prod hU).mem_nhds hw)
  refine {
    smooth := {
      forcing := fun i => sourceField_contDiffOn_of_pullback hs
        (fun w hw => hF.denominator w.2 hw.2) i
      zeroth := fun i j => coefficient0_contDiffOn_of_pullback hs
        (fun w hw => hF.denominator w.2 hw.2) i j
      first := fun i j => coefficient1_contDiffOn_of_pullback hs
        (fun w hw => hF.denominator w.2 hw.2) i j }
    zeroth_holomorphic := ?_
    first_holomorphic := ?_
    forcing_holomorphic := ?_ }
  · intro r hr
    apply differentiableOn_pi.mpr
    intro i
    apply differentiableOn_pi.mpr
    intro j z hz
    exact (coefficient0_analyticAt
      (fun k => (hF.holomorphic r hr k).analyticAt (hU.mem_nhds hz))
      (hF.denominator z hz) i j).differentiableAt.differentiableWithinAt
  · intro r hr
    apply differentiableOn_pi.mpr
    intro i
    apply differentiableOn_pi.mpr
    intro j z hz
    exact (coefficient1_analyticAt
      (fun k => (hF.holomorphic r hr k).analyticAt (hU.mem_nhds hz))
      (hF.denominator z hz) i j).differentiableAt.differentiableWithinAt
  · intro r hr
    apply differentiableOn_pi.mpr
    intro i z hz
    exact (sourceField_analyticAt
      (fun k => (hF.holomorphic r hr k).analyticAt (hU.mem_nhds hz))
      (hF.denominator z hz) i).differentiableAt.differentiableWithinAt

/-- The concrete series solution for the explicit positive-order matrices. -/
noncomputable def positiveSolution {R : ℝ} (hR : 0 ≤ R) (h lam C : ℂ)
    (F : CoefficientData) : Field :=
  symmetricSolution hR (matrixPath R (coefficient0 h lam C F))
    (matrixPath R (coefficient1 h F)) (forcingPath R (sourceField h C F))

theorem positiveSolution_spec {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {h : ℂ} (lam C : ℂ) {F : CoefficientData}
    (hF : LowerInputRegularity T U h F) :
    IsSymmetricIntegralSolution R U (coefficient0 h lam C F) (coefficient1 h F)
      (sourceField h C F) (positiveSolution hR h lam C F) :=
  assembledSolution_spec hR hRT hU (hF.system hU lam C) (coefficient1_shape h F)

theorem positiveSolution_jointly_smooth {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {h : ℂ} (lam C : ℂ) {F : CoefficientData}
    (hF : LowerInputRegularity T U h F) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => positiveSolution hR h lam C F p.1 p.2)
      (radialDomain R ×ˢ U) :=
  solution_jointly_smooth hR hU (positiveSolution_spec hR hRT hU lam C hF)
    (((hF.system hU lam C).restrict hRT.le).smooth)

theorem positiveSolution_parity {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {h : ℂ} (lam C : ℂ) {F : CoefficientData}
    (hF : LowerInputRegularity T U h F) {r : ℝ} (hr : r ∈ Icc (-R) R)
    {z : ℂ} (hz : z ∈ U) :
    positiveSolution hR h lam C F (-r) z = parityVec (positiveSolution hR h lam C F r z) :=
  assembledSolution_parity hR hRT hU (hF.system hU lam C) (coefficient1_shape h F)
    (coefficient0_parity h lam C F) (coefficient1_parity h F) (sourceField_parity h C F) hr hz

theorem positiveSolution_equation {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {h : ℂ} (lam C : ℂ) {F : CoefficientData}
    (hF : LowerInputRegularity T U h F) {r : ℝ} (hr : r ∈ radialDomain R)
    (hr0 : r ≠ 0) {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    deriv (fun s => positiveSolution hR h lam C F s z i) r +
      ((exponent i : ℝ) / r) • positiveSolution hR h lam C F r z i =
      equationRHS (coefficient0 h lam C F) (coefficient1 h F) (sourceField h C F)
        (positiveSolution hR h lam C F) r z i :=
  solution_differential_equation hR hU (positiveSolution_spec hR hRT hU lam C hF)
    (((hF.system hU lam C).restrict hRT.le).smooth) hr hr0 hz i

end ExplicitInputs

section SquaredRadius

/-- Real parameter domain, given by `{eta | (eta : ℂ) ∈ U}`. -/
noncomputable def realParameterDomain (U : Set ℂ) : Set ℝ :=
  {eta | (eta : ℂ) ∈ U}

theorem realParameterDomain_isOpen {U : Set ℂ} (hU : IsOpen U) :
    IsOpen (realParameterDomain U) := hU.preimage Complex.continuous_ofReal

/-- Real radial component, given by `(W p.2 (p.1 : ℂ) i).re`. -/
noncomputable def realRadialComponent (W : Field) (i : Fin 6) (p : ℝ × ℝ) : ℝ :=
  (W p.2 (p.1 : ℂ) i).re

/-- Actual profiles, with the physical coordinate order `(X,eta)`. -/
noncomputable def xProfile (W : Field) (i : Fin 6) (p : ℝ × ℝ) : ℝ :=
  ParametricEvenDescent.descend (realRadialComponent W i) (p.2, p.1)

@[simp] theorem xProfile_apply (W : Field) (i : Fin 6) (X eta : ℝ) :
    xProfile W i (X, eta) = (W (Real.sqrt X) (eta : ℂ) i).re := rfl

theorem realRadialComponent_smooth {R : ℝ} {U : Set ℂ} {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (i : Fin 6) :
    ContDiffOn ℝ ∞ (realRadialComponent W i) (realParameterDomain U ×ˢ Ioo (-R) R) := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  apply (contDiffOn_pi.mp hW i).comp
    (contDiff_snd.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_fst)).contDiffOn
  intro p hp
  exact ⟨by simpa [radialDomain, Real.ball_eq_Ioo] using hp.2, hp.1⟩

theorem realRadialComponent_even {R : ℝ} {U : Set ℂ} {W : Field}
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) :
    ∀ eta ∈ realParameterDomain U, ∀ r ∈ Ioo (-R) R,
      realRadialComponent W i (eta, -r) = realRadialComponent W i (eta, r) := by
  intro eta heta r hr
  exact congrArg Complex.re (first_components_even hparity i hi heta r hr)

theorem xProfile_smooth {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U) {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) :
    ContDiffOn ℝ ∞ (xProfile W i) (Ico (0 : ℝ) (R ^ 2) ×ˢ realParameterDomain U) := by
  have hs := ParametricEvenDescent.contDiffOn_descend_local
    (realParameterDomain_isOpen hU) hR (realRadialComponent_smooth hW i)
    (realRadialComponent_even hparity i hi)
  exact hs.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩)

theorem xProfile_square {R : ℝ} {U : Set ℂ} {W : Field}
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) {eta r : ℝ} (heta : eta ∈ realParameterDomain U)
    (hr : r ∈ Ioo (-R) R) : xProfile W i (r ^ 2, eta) = (W r (eta : ℂ) i).re :=
  ParametricEvenDescent.descend_square_local (realRadialComponent_even hparity i hi) heta hr

theorem xProfile_axis_zero {U : Set ℂ} {W : Field}
    (haxis : ∀ z ∈ U, W 0 z = 0) (i : Fin 6) {eta : ℝ}
    (heta : eta ∈ realParameterDomain U) : xProfile W i (0, eta) = 0 := by
  simp only [xProfile_apply, Real.sqrt_zero, haxis _ heta, Pi.zero_apply, Complex.zero_re]

theorem xProfile_axis_jet {R : ℝ} (hR : 0 < R) {U : Set ℂ} {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) {eta : ℝ} (heta : eta ∈ realParameterDomain U) (n : ℕ) :
    iteratedDerivWithin n (fun X => xProfile W i (X, eta)) (Ici 0) 0 =
      ((n.factorial : ℝ) / ((2 * n).factorial : ℝ)) •
        iteratedDeriv (2 * n) (fun r => (W r (eta : ℂ) i).re) 0 :=
  ParametricEvenDescent.iteratedDerivWithin_descend_axis_local hR
    (realRadialComponent_smooth hW i) (realRadialComponent_even hparity i hi) heta n

end SquaredRadius

section RealSystem

open PositiveAxisSystem

/-- Real coefficient data: an abbreviation for `Fin 11 → ℝ × ℝ → ℝ`. -/
abbrev RealCoefficientData := Fin 11 → ℝ × ℝ → ℝ
/-- Real field: an abbreviation for `ℝ → ℝ → Fin 6 → ℝ`. -/
abbrev RealField := ℝ → ℝ → Fin 6 → ℝ

/-- Real base, given by `⟨⟨G 0 p, G 1 p, 0, G 2 p⟩, ⟨G 3 p, G 4 p, 0, G 5 p⟩, G 6 p⟩`. -/
noncomputable def realBase (G : RealCoefficientData) (p : ℝ × ℝ) : BaseJet ℝ :=
  ⟨⟨G 0 p, G 1 p, 0, G 2 p⟩, ⟨G 3 p, G 4 p, 0, G 5 p⟩, G 6 p⟩

/-- Real source, given by `⟨G 7 p, G 8 p, G 9 p, G 10 p⟩`. -/
noncomputable def realSource (G : RealCoefficientData) (p : ℝ × ℝ) : SourceJet ℝ :=
  ⟨G 7 p, G 8 p, G 9 p, G 10 p⟩

/-- The complex inputs restrict to the given real finite input jets on the
positive physical domain. Their smooth radial extension supplies the axis
limits, without referring to ordinary derivatives of a negative-`X` continuation. -/
def RealCompatible (R : ℝ) (U : Set ℂ) (F : CoefficientData) (G : RealCoefficientData) : Prop :=
  ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta ∈ realParameterDomain U, ∀ i,
    F i (X, (eta : ℂ)) = (G i (X, eta) : ℂ)

theorem RealCompatible.base {R : ℝ} {U : Set ℂ} {F : CoefficientData} {G : RealCoefficientData}
    (h : RealCompatible R U F G) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : eta ∈ realParameterDomain U) :
    coefficientBase F X (eta : ℂ) = complexBase (realBase G (X, eta)) := by
  simp only [coefficientBase, complexBase, complexJet, realBase,
    h X hX eta heta 0, h X hX eta heta 1, h X hX eta heta 2,
    h X hX eta heta 3, h X hX eta heta 4, h X hX eta heta 5,
    h X hX eta heta 6, Complex.ofReal_zero]

theorem RealCompatible.source {R : ℝ} {U : Set ℂ} {F : CoefficientData} {G : RealCoefficientData}
    (h : RealCompatible R U F G) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : eta ∈ realParameterDomain U) :
    coefficientSource F X (eta : ℂ) = complexSource (realSource G (X, eta)) := by
  simp only [coefficientSource, complexSource, realSource,
    h X hX eta heta 7, h X hX eta heta 8, h X hX eta heta 9, h X hX eta heta 10]

theorem square_mem_Ico {R r : ℝ} (hr : r ∈ Ioo (-R) R) :
    r ^ 2 ∈ Ico (0 : ℝ) (R ^ 2) := by
  refine ⟨sq_nonneg _, ?_⟩
  have hprod : 0 < (R - r) * (R + r) := mul_pos (by linarith [hr.2]) (by linarith [hr.1])
  linarith

/-- The genuine real first-order system, with all six ordinary derivatives. -/
def RealSixSystem (R : ℝ) (J : Set ℝ) (h lam C : ℝ) (G : RealCoefficientData)
    (w : RealField) : Prop :=
  ∀ r ∈ Ioo (-R) R, r ≠ 0 → ∀ eta ∈ J, ∀ i,
    deriv (fun s => w s eta i) r + (diagonal i : ℝ) / r * w r eta i =
      matrixRHS h lam C r eta (realBase G (r ^ 2, eta)) (realSource G (r ^ 2, eta))
        (w r eta) (fun j => deriv (fun v => w r v j) eta) i

theorem positiveSolution_real_system {R T : ℝ} (hR : 0 < R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) (h lam C : ℝ) {F : CoefficientData}
    (hF : LowerInputRegularity T U (h : ℂ) F) {G : RealCoefficientData}
    (hreal : RealCompatible R U F G) :
    RealSixSystem R (realParameterDomain U) h lam C G
      (realTrace (positiveSolution hR.le (h : ℂ) (lam : ℂ) (C : ℂ) F)) := by
  let W := positiveSolution hR.le (h : ℂ) (lam : ℂ) (C : ℂ) F
  have hW := positiveSolution_spec hR.le hRT hU (lam : ℂ) (C : ℂ) hF
  have hdata := ((hF.system hU (lam : ℂ) (C : ℂ)).restrict hRT.le).smooth
  intro r hr hr0 eta heta
  have hr' : r ∈ radialDomain R := by simpa [radialDomain, Real.ball_eq_Ioo] using hr
  apply realTrace_solves_system h lam C r eta (realBase G (r ^ 2, eta))
    (realSource G (r ^ 2, eta)) W
  · intro i
    exact (solution_hasDerivAt hR.le hU hW hdata hr' heta i).differentiableAt
  · intro i
    exact (hW.parameter_holomorphic r ⟨hr.1.le, hr.2.le⟩ i).differentiableAt (hU.mem_nhds heta)
  · intro i
    have he := positiveSolution_equation hR.le hRT hU (lam : ℂ) (C : ℂ) hF hr' hr0 heta i
    rw [diagonal_eq_exponent]
    simp only [W, equationRHS, matrixAction, coefficient0, coefficient1, sourceField,
      matrixRHS, hreal.base ⟨sq_pos_of_ne_zero hr0, (square_mem_Ico hr).2⟩ heta,
      hreal.source ⟨sq_pos_of_ne_zero hr0, (square_mem_Ico hr).2⟩ heta,
      Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast, Pi.add_apply,
      add_comm, add_left_comm] at he ⊢
    exact he

theorem RealSixSystem.first_derivative {R : ℝ} {J : Set ℝ} {h lam C : ℝ}
    {G : RealCoefficientData} {w : RealField} (hw : RealSixSystem R J h lam C G w)
    {r eta : ℝ} (hr : r ∈ Ioo (-R) R) (hr0 : r ≠ 0) (heta : eta ∈ J) :
    deriv (fun s => w s eta 0) r = w r eta 4 ∧
      deriv (fun s => w s eta 1) r = w r eta 5 := by
  constructor
  · simpa [PositiveAxisSystem.diagonal, matrixRHS, A0, A1, forcing, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hw r hr hr0 eta heta 0
  · simpa [PositiveAxisSystem.diagonal, matrixRHS, A0, A1, forcing, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hw r hr hr0 eta heta 1

theorem xProfile_contDiffAt {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) {r eta : ℝ}
    (hr : r ∈ Ioo (-R) R) (hr0 : r ≠ 0) (heta : eta ∈ realParameterDomain U) :
    ContDiffAt ℝ ∞ (xProfile W i) (r ^ 2, eta) := by
  have hs := (xProfile_smooth hR hU hW hparity i hi).mono
    (Set.prod_mono Ioo_subset_Ico_self (Subset.refl (realParameterDomain U)))
  exact hs.contDiffAt ((isOpen_Ioo.prod (realParameterDomain_isOpen hU)).mem_nhds
    ⟨⟨sq_pos_of_ne_zero hr0, (square_mem_Ico hr).2⟩, heta⟩)

/-- The last two Volterra components are the actual radial derivatives of
the first two descended profiles; they are not independent jet variables. -/
theorem xProfile_vector_eq {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    {h lam C : ℝ} {G : RealCoefficientData}
    (heq : RealSixSystem R (realParameterDomain U) h lam C G (realTrace W))
    {r eta : ℝ} (hr : r ∈ Ioo (-R) R) (hr0 : r ≠ 0)
    (heta : eta ∈ realParameterDomain U) :
    profileVector (xProfile W 0) (xProfile W 1) (xProfile W 2) (xProfile W 3) r eta =
      realTrace W r eta := by
  have hrecovery (i : Fin 6) (hi : i.val < 4) :
      (fun s => xProfile W i (s ^ 2, eta)) =ᶠ[𝓝 r] (fun s => realTrace W s eta i) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact xProfile_square hparity i hi heta hs
  have hfirst := heq.first_derivative hr hr0 heta
  have hfour : 2 * r * SimilarityProfile.partialX (xProfile W 0) (r ^ 2, eta) =
      realTrace W r eta 4 := by
    have hd := hasDerivAt_squareProfile
      ((xProfile_contDiffAt hR hU hW hparity 0 (by
          norm_num) hr hr0 heta).differentiableAt (by simp))
    exact hd.deriv.symm.trans ((hrecovery 0 (by norm_num)).deriv_eq.trans hfirst.1)
  have hfive : 2 * r * SimilarityProfile.partialX (xProfile W 1) (r ^ 2, eta) =
      realTrace W r eta 5 := by
    have hd := hasDerivAt_squareProfile
      ((xProfile_contDiffAt hR hU hW hparity 1 (by
          norm_num) hr hr0 heta).differentiableAt (by simp))
    exact hd.deriv.symm.trans ((hrecovery 1 (by norm_num)).deriv_eq.trans hfirst.2)
  funext i
  fin_cases i
  · exact xProfile_square hparity 0 (by decide) heta hr
  · exact xProfile_square hparity 1 (by decide) heta hr
  · exact xProfile_square hparity 2 (by decide) heta hr
  · exact xProfile_square hparity 3 (by decide) heta hr
  · exact hfour
  · exact hfive

/-- The recovered profiles solve the true differentiated system. -/
theorem xProfiles_system {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {W : Field}
    (hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U))
    (hparity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    {h lam C : ℝ} {G : RealCoefficientData}
    (heq : RealSixSystem R (realParameterDomain U) h lam C G (realTrace W))
    {r eta : ℝ} (hr : r ∈ Ioo (-R) R) (hr0 : r ≠ 0)
    (heta : eta ∈ realParameterDomain U) :
    ProfileSystem h lam C r eta (realBase G (r ^ 2, eta)) (realSource G (r ^ 2, eta))
      (xProfile W 0) (xProfile W 1) (xProfile W 2) (xProfile W 3) := by
  let PV := profileVector (xProfile W 0) (xProfile W 1) (xProfile W 2) (xProfile W 3)
  have hpoint : PV r eta = realTrace W r eta :=
    xProfile_vector_eq hR hU hW hparity heq hr hr0 heta
  have hrad (i : Fin 6) : deriv (fun s => PV s eta i) r =
      deriv (fun s => realTrace W s eta i) r := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hr, eventually_ne_nhds hr0] with s hs hs0
    exact congrFun (xProfile_vector_eq hR hU hW hparity heq hs hs0 heta) i
  have hparam (i : Fin 6) : deriv (fun v => PV r v i) eta =
      deriv (fun v => realTrace W r v i) eta := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [(realParameterDomain_isOpen hU).mem_nhds heta] with v hv
    exact congrFun (xProfile_vector_eq hR hU hW hparity heq hr hr0 hv) i
  change (fun i => deriv (fun s => PV s eta i) r + (diagonal i : ℝ) / r * PV r eta i) =
    matrixRHS h lam C r eta (realBase G (r ^ 2, eta)) (realSource G (r ^ 2, eta))
      (PV r eta) (fun i => deriv (fun z => PV r z i) eta)
  funext i
  rw [hrad i, hpoint]
  simp_rw [hparam]
  exact heq r hr hr0 eta heta i

theorem positiveSolution_profiles_system {R T : ℝ} (hR : 0 < R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) (h lam C : ℝ) {F : CoefficientData}
    (hF : LowerInputRegularity T U (h : ℂ) F) {G : RealCoefficientData}
    (hreal : RealCompatible R U F G) {r eta : ℝ}
    (hr : r ∈ Ioo (-R) R) (hr0 : r ≠ 0) (heta : eta ∈ realParameterDomain U) :
    let W := positiveSolution hR.le (h : ℂ) (lam : ℂ) (C : ℂ) F
    ProfileSystem h lam C r eta (realBase G (r ^ 2, eta)) (realSource G (r ^ 2, eta))
      (xProfile W 0) (xProfile W 1) (xProfile W 2) (xProfile W 3) := by
  exact xProfiles_system hR hU
    (positiveSolution_jointly_smooth hR.le hRT hU (lam : ℂ) (C : ℂ) hF)
    (fun r hr z hz => positiveSolution_parity hR.le hRT hU (lam : ℂ) (C : ℂ) hF hr hz)
    (positiveSolution_real_system hR hRT hU h lam C hF hreal) hr hr0 heta

end RealSystem

section PositiveOrder

open PositiveAxisSystem SimilarityProfile

/-- The eleven real inputs are computed from the given lower-order history.
The unknown order is not used in the finite source, as proved separately by
`actualLowerSource_update`. -/
noncomputable def lowerHistoryData (h : ℝ) (n : ℕ) (phi u beta : ℕ → InnerProfile)
    (omegaQuotient : InnerProfile) : RealCoefficientData :=
  fun i w =>
    ![phi 0 w, partialX (phi 0) w, partialEta (phi 0) w,
      u 0 w, partialX (u 0) w, partialEta (u 0) w, beta 0 w,
      (actualLowerSource h n phi u beta omegaQuotient w).angular,
      (actualLowerSource h n phi u beta omegaQuotient w).axial,
      (actualLowerSource h n phi u beta omegaQuotient w).pressureProduct,
      (actualLowerSource h n phi u beta omegaQuotient w).omegaQuotient] i

/-- New beta, defined pointwise by `betaValue h (slowPower h n) w.2 (actualJet u w) (actualJet k
w)`. -/
noncomputable def newBeta (h : ℝ) (n : ℕ) (u k : InnerProfile) : InnerProfile :=
  fun w => betaValue h (slowPower h n) w.2 (actualJet u w) (actualJet k w)

/-- The original positive-order convolution equations evaluated on the
history after inserting the newly constructed profiles. -/
def ExtendsPositiveOrder (h C : ℝ) (n : ℕ) (phi u beta : ℕ → InnerProfile)
    (phiNew uNew k p omegaQuotient : InnerProfile) (w : InnerPoint) : Prop :=
  let phi' := Function.update phi n phiNew
  let u' := Function.update u n uNew
  let beta' := Function.update beta n (newBeta h n uNew k)
  PositiveOrderEquations h C w.2 w.1 n
    (fun j => actualJet (phi' j) w) (fun j => actualJet (u' j) w)
    (fun j => beta' j w) (actualJet k w) (actualJet p w)
    (precedingDiffusion h (angularPower h) phi' n w)
    (precedingDiffusion h (axialPower h) u' n w) (omegaQuotient w)

theorem profileSystem_lowerHistoryData (h lam C r eta : ℝ) (n : ℕ)
    (phi u beta : ℕ → InnerProfile) (omegaQuotient phiNew uNew k p : InnerProfile) :
    ProfileSystem h lam C r eta
      (realBase (lowerHistoryData h n phi u beta omegaQuotient) (r ^ 2, eta))
      (realSource (lowerHistoryData h n phi u beta omegaQuotient) (r ^ 2, eta))
      phiNew uNew k p ↔
    ProfileSystem h lam C r eta
      (baseAtOrderZero (fun j => actualJet (phi j) (r ^ 2, eta))
        (fun j => actualJet (u j) (r ^ 2, eta)) (fun j => beta j (r ^ 2, eta)))
      (actualLowerSource h n phi u beta omegaQuotient (r ^ 2, eta)) phiNew uNew k p := by
  rfl

theorem positiveSolution_extends_order {R T : ℝ} (hR : 0 < R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) (h C : ℝ) {n : ℕ} (hn : 0 < n)
    (phi u beta : ℕ → InnerProfile) (omegaQuotient : InnerProfile)
    {F : CoefficientData} (hF : LowerInputRegularity T U (h : ℂ) F)
    (hreal : RealCompatible R U F (lowerHistoryData h n phi u beta omegaQuotient))
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : eta ∈ realParameterDomain U) :
    let W := positiveSolution hR.le (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F
    ExtendsPositiveOrder h C n phi u beta (xProfile W 0) (xProfile W 1)
      (xProfile W 2) (xProfile W 3) omegaQuotient (X, eta) := by
  let W := positiveSolution hR.le (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F
  let phiNew := xProfile W 0
  let uNew := xProfile W 1
  let k := xProfile W 2
  let p := xProfile W 3
  let phi' := Function.update phi n phiNew
  let u' := Function.update u n uNew
  let beta' := Function.update beta n (newBeta h n uNew k)
  let r := Real.sqrt X
  have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hX.1)
  have hr : r ∈ Ioo (-R) R := by
    constructor
    · linarith [Real.sqrt_nonneg X]
    · have hsq := Real.sq_sqrt hX.1.le
      dsimp [r]
      nlinarith [Real.sqrt_nonneg X, hX.2]
  have hrX : r ^ 2 = X := Real.sq_sqrt hX.1.le
  have hWsm := positiveSolution_jointly_smooth hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF
  have hpar : ∀ s ∈ Icc (-R) R, ∀ z ∈ U, W (-s) z = parityVec (W s z) :=
    fun s hs z hz => positiveSolution_parity hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF hs hz
  have hnew (i : Fin 6) (hi : i.val < 4) : ContDiffAt ℝ ∞ (xProfile W i) (r ^ 2, eta) :=
    xProfile_contDiffAt hR hU hWsm hpar i hi hr hr0 heta
  have hs := positiveSolution_profiles_system hR hRT hU h (slowPower h n) C hF hreal hr hr0 heta
  have hs' := (profileSystem_lowerHistoryData h (slowPower h n) C r eta n phi u beta
    omegaQuotient phiNew uNew k p).mp hs
  have hsUpdated : ProfileSystem h (slowPower h n) C r eta
      (baseAtOrderZero (fun j => actualJet (phi' j) (r ^ 2, eta))
        (fun j => actualJet (u' j) (r ^ 2, eta)) (fun j => beta' j (r ^ 2, eta)))
      (actualLowerSource h n phi' u' beta' omegaQuotient (r ^ 2, eta))
      (phi' n) (u' n) k p := by
    simpa only [phi', u', beta', baseAtOrderZero_update hn,
      actualLowerSource_update, Function.update_self] using hs'
  have hphi : ContDiffAt ℝ 2 (phi' n) (r ^ 2, eta) := by
    simpa only [phi', Function.update_self] using
      (show ContDiffAt ℝ 2 phiNew (r ^ 2, eta) from
        (hnew 0 (by decide)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hu : ContDiffAt ℝ 2 (u' n) (r ^ 2, eta) := by
    simpa only [u', Function.update_self] using
      (show ContDiffAt ℝ 2 uNew (r ^ 2, eta) from
        (hnew 1 (by decide)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hbet : beta' n (r ^ 2, eta) = betaValue h (slowPower h n) eta
      (actualJet (u' n) (r ^ 2, eta)) (actualJet k (r ^ 2, eta)) := by
    simp only [beta', u', Function.update_self, newBeta]
  have hresult := (profileSystem_iff_positiveOrder hr0 hn phi' u' beta' k p omegaQuotient
    hphi hu ((hnew 2 (by decide)).differentiableAt (by simp))
    ((hnew 3 (by decide)).differentiableAt (by simp)) hbet).mp hsUpdated
  simpa only [ExtendsPositiveOrder, hrX] using hresult

end PositiveOrder

section Uniqueness

/-- A competing solution is given by actual holomorphic continuous paths
on the positive and reflected negative radial intervals. -/
def SidePathSolution {R : ℝ} (hR : 0 ≤ R) (U : Set ℂ) (A₀ A₁ : Coeff) (f : Field)
    (V : Bool → ℂ → NilpotentVolterra.Path R) : Prop :=
  (∀ b, DifferentiableOn ℂ (V b) U) ∧
  ∀ b z, z ∈ U → V b z = NilpotentVolterra.pathInverse hR exponent
    (NilpotentVolterra.rhsPath (sideData hR b (matrixPath R A₀))
      (sideData hR b (matrixPath R A₁)) (sideData hR b (forcingPath R f)) (V b) z)

/-- Candidate lift, constructed using `glue`. -/
noncomputable def candidateLift {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : Coeff) (f : Field)
    (V : Bool → ℂ → NilpotentVolterra.Path R) : Field :=
  glue
    (NilpotentVolterra.liftedField hR (sideData hR false (matrixPath R A₀))
      (sideData hR false (matrixPath R A₁)) (sideData hR false (forcingPath R f)) (V false))
    (NilpotentVolterra.liftedField hR (sideData hR true (matrixPath R A₀))
      (sideData hR true (matrixPath R A₁)) (sideData hR true (forcingPath R f)) (V true))

/-- Actual uniqueness in the holomorphic continuous-path class. It is
deduced from the decaying Volterra-word majorant, with no norm smallness. -/
theorem assembledSolution_unique {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) {A₀ A₁ : Coeff} {f : Field}
    (hdata : SmoothHolomorphicSystem T U A₀ A₁ f) (hshape : DerivativeShape A₁)
    {V : Bool → ℂ → NilpotentVolterra.Path R} (hV : SidePathSolution hR U A₀ A₁ f V)
    (r : ℝ) {z : ℂ} (hz : z ∈ U) :
    candidateLift hR A₀ A₁ f V r z = assembledSolution hR A₀ A₁ f r z := by
  let B₀ := fun b => sideData hR b (matrixPath R A₀)
  let B₁ := fun b => sideData hR b (matrixPath R A₁)
  let g := fun b => sideData hR b (forcingPath R f)
  let C := fun b => NilpotentVolterra.integralSolution hR (B₀ b) (B₁ b) (g b)
  have hB₀ (b : Bool) : DifferentiableOn ℂ (B₀ b) U :=
    sideData_holomorphic hR b
      (matrixPath_holomorphic hRT hU hdata.smooth.zeroth hdata.zeroth_holomorphic)
  have hB₁ (b : Bool) : DifferentiableOn ℂ (B₁ b) U :=
    sideData_holomorphic hR b
      (matrixPath_holomorphic hRT hU hdata.smooth.first hdata.first_holomorphic)
  have hg (b : Bool) : DifferentiableOn ℂ (g b) U :=
    sideData_holomorphic hR b
      (forcingPath_holomorphic hRT hU hdata.smooth.forcing hdata.forcing_holomorphic)
  have hshapeB (b : Bool) : DerivativeShape (NilpotentVolterra.rawCoefficient hR (B₁ b)) :=
    side_shape hR (matrixPath_shape hR hshape) b
  have hc (b : Bool) : DifferentiableOn ℂ (C b) U ∧
      ∀ z ∈ U, C b z = NilpotentVolterra.pathInverse hR exponent
        (NilpotentVolterra.rhsPath (B₀ b) (B₁ b) (g b) (C b) z) :=
    NilpotentVolterra.integralSolution_spec_open hR hU (hB₀ b) (hB₁ b) (hg b) (hshapeB b)
  exact glued_solution_unique hR hU hB₀ hB₁ hV.1 (fun b => (hc b).1) hshapeB
    hV.2 (fun b => (hc b).2) r hz

end Uniqueness

section FinalExistence

open PositiveAxisSystem SimilarityProfile

/-- The actual positive-order output: a smooth symmetric six-component
field, its physical squared-radius profiles, and their exact equations and
axis jets. Uniqueness is stated separately below. -/
structure IsPositiveOrderSolution (R : ℝ) (U : Set ℂ) (h C : ℝ) (n : ℕ)
    (phi u beta : ℕ → InnerProfile) (omegaQuotient : InnerProfile)
    (F : CoefficientData) (W : Field) : Prop where
  integral : IsSymmetricIntegralSolution R U
    (coefficient0 (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F)
    (coefficient1 (h : ℂ) F) (sourceField (h : ℂ) (C : ℂ) F) W
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2) (radialDomain R ×ˢ U)
  parity : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z)
  equation : ∀ r ∈ radialDomain R, r ≠ 0 → ∀ z ∈ U, ∀ i,
    deriv (fun s => W s z i) r + ((exponent i : ℝ) / r) • W r z i =
      equationRHS (coefficient0 (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F)
        (coefficient1 (h : ℂ) F) (sourceField (h : ℂ) (C : ℂ) F) W r z i
  profiles_smooth : ∀ i : Fin 6, i.val < 4 →
    ContDiffOn ℝ ∞ (xProfile W i) (Ico (0 : ℝ) (R ^ 2) ×ˢ realParameterDomain U)
  profiles_zero : ∀ i : Fin 6, ∀ eta ∈ realParameterDomain U, xProfile W i (0, eta) = 0
  profiles_axis_jets : ∀ i : Fin 6, i.val < 4 → ∀ eta ∈ realParameterDomain U, ∀ k : ℕ,
    iteratedDerivWithin k (fun X => xProfile W i (X, eta)) (Ici 0) 0 =
      ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
        iteratedDeriv (2 * k) (fun r => (W r (eta : ℂ) i).re) 0
  positive_order : ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta ∈ realParameterDomain U,
    ExtendsPositiveOrder h C n phi u beta (xProfile W 0) (xProfile W 1)
      (xProfile W 2) (xProfile W 3) omegaQuotient (X, eta)

/-- Concrete positive-order existence from smooth radial, holomorphic
parameter input jets of the lower history. No solution, convergence,
positive-order equation, or output smoothness is an input assumption. -/
theorem exists_positive_order_solution {R T : ℝ} (hR : 0 < R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) (h C : ℝ) {n : ℕ} (hn : 0 < n)
    (phi u beta : ℕ → InnerProfile) (omegaQuotient : InnerProfile)
    {F : CoefficientData} (hF : LowerInputRegularity T U (h : ℂ) F)
    (hreal : RealCompatible R U F (lowerHistoryData h n phi u beta omegaQuotient)) :
    ∃ W : Field, IsPositiveOrderSolution R U h C n phi u beta omegaQuotient F W := by
  let W := positiveSolution hR.le (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F
  have hi := positiveSolution_spec hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF
  have hs := positiveSolution_jointly_smooth hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF
  have hp : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z) :=
    fun r hr z hz => positiveSolution_parity hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF hr hz
  refine ⟨W, {
    integral := hi
    smooth := hs
    parity := hp
    equation := fun r hr hr0 z hz i =>
      positiveSolution_equation hR.le hRT hU ((slowPower h n : ℝ) : ℂ) (C : ℂ) hF hr hr0 hz i
    profiles_smooth := fun i hi => xProfile_smooth hR hU hs hp i hi
    profiles_zero := fun i eta heta => xProfile_axis_zero hi.axis_zero i heta
    profiles_axis_jets := fun i hi eta heta k => xProfile_axis_jet hR hs hp i hi heta k
    positive_order := ?_ }⟩
  intro X hX eta heta
  exact positiveSolution_extends_order hR hRT hU h C hn phi u beta omegaQuotient hF hreal hX heta

/-- Uniqueness for the same explicit lower-data problem, for any competing
pair of actual holomorphic continuous-path integral solutions. -/
theorem positive_order_solution_unique {R T : ℝ} (hR : 0 ≤ R) (hRT : R < T)
    {U : Set ℂ} (hU : IsOpen U) (h C : ℝ) (n : ℕ)
    {F : CoefficientData} (hF : LowerInputRegularity T U (h : ℂ) F)
    {V : Bool → ℂ → NilpotentVolterra.Path R}
    (hV : SidePathSolution hR U
      (coefficient0 (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F)
      (coefficient1 (h : ℂ) F) (sourceField (h : ℂ) (C : ℂ) F) V)
    (r : ℝ) {z : ℂ} (hz : z ∈ U) :
    candidateLift hR
      (coefficient0 (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F)
      (coefficient1 (h : ℂ) F) (sourceField (h : ℂ) (C : ℂ) F) V r z =
      positiveSolution hR (h : ℂ) ((slowPower h n : ℝ) : ℂ) (C : ℂ) F r z :=
  assembledSolution_unique hR hRT hU (hF.system hU ((slowPower h n : ℝ) : ℂ) (C : ℂ))
    (coefficient1_shape (h : ℂ) F) hV r hz

end FinalExistence

end NavierStokes.PositiveAxisExistence

end
end

end

section

/-!
# Radial divisibility and regular slow-order sources

This module removes the apparent `1/X` singularities in the radial source
of equation (22), using the actual differential operators from SimilarityProfile.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.AxisSourceRegularity

open SimilarityProfile Set Filter
open scoped BigOperators Topology ContDiff

/-- Axis factor, given by `w.1 * v w`. -/
noncomputable def axisFactor (v : InnerProfile) (w : InnerPoint) : ℝ := w.1 * v w

theorem partialX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialX (axisFactor v) w = v w + w.1 * partialX v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (1, 0) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialX]
  ring

theorem partialEta_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialEta (axisFactor v) w = w.1 * partialEta v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (0, 1) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialEta]

/-- Factoring out X shifts the similarity exponent by one. -/
theorem T_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    T h b (axisFactor v) w = w.1 * T h (b - 1) v w := by
  simp only [T, CoordinateAlgebra.timeCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    Z h b (axisFactor v) w = w.1 * Z h (b - 1) v w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : Z h b f w = Z h b g w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX, partialEta,
    hfg.eq_of_nhds, hfg.fderiv_eq]

theorem partialXX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) :
    partialX (partialX (axisFactor v)) w =
      2 * partialX v w + w.1 * partialX (partialX v) w := by
  have heq : partialX (axisFactor v) =ᶠ[𝓝 w] (fun y => v y + y.1 * partialX v y) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact partialX_axisFactor (hy.differentiableAt (by norm_num))
  have hx := (partialX_smoothAt hv (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change (fderiv ℝ (partialX (axisFactor v)) w) (1, 0) = _
  rw [heq.fderiv_eq,
    ((hv.differentiableAt (by norm_num)).hasFDerivAt.fun_add
      (hasFDerivAt_fst.fun_mul hx.hasFDerivAt)).fderiv]
  simp [partialX]
  ring

/-- Z2, given by `Z h (b - D h) (Z h b v)`. -/
noncomputable def Z2 (h b : ℝ) (v : InnerProfile) : InnerProfile :=
  Z h (b - D h) (Z h b v)

theorem Z2_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    Z2 h b (axisFactor v) w = w.1 * Z2 h (b - 1) v w := by
  have heq : Z h b (axisFactor v) =ᶠ[𝓝 w] axisFactor (Z h (b - 1) v) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact Z_axisFactor h b (hy.differentiableAt (by norm_num))
  change Z h (b - D h) (Z h b (axisFactor v)) w = _
  rw [Z_congr_germ h (b - D h) heq,
    Z_axisFactor h (b - D h) ((Z_smoothAt hv hL).differentiableAt (by norm_num))]
  have he : b - D h - 1 = b - 1 - D h := by ring
  rw [he]
  rfl

theorem radial_advection_axisFactor {vi vj : InnerProfile} {w : InnerPoint}
    (hvj : DifferentiableAt ℝ vj w) :
    axisFactor vi w * (partialX (axisFactor vj) w - axisFactor vj w / (2 * w.1)) =
      w.1 * (vi w * (vj w / 2 + w.1 * partialX vj w)) := by
  rw [partialX_axisFactor hvj]
  unfold axisFactor
  by_cases hX : w.1 = 0
  · simp [hX]
  · field_simp [hX]
    ring

/-- Slow order, given by `2 * (k : ℝ) * h`. -/
noncomputable def slowOrder (h : ℝ) (k : ℕ) : ℝ := 2 * (k : ℝ) * h

/-- Shifted axial as an element of `ℕ → InnerProfile | 0 => fun _ => 0 | k + 1 => Z2 h
(slowOrder h k) (V k)`. -/
noncomputable def shiftedAxial (h : ℝ) (V : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k) (V k)

/-- Shifted axial factor as an element of `ℕ → InnerProfile | 0 => fun _ => 0 | k + 1 => Z2 h
(slowOrder h k - 1) (v k)`. -/
noncomputable def shiftedAxialFactor (h : ℝ) (v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k - 1) (v k)

/-- The displayed Ω_k source before canceling its radial factor. -/
noncomputable def omega (h : ℝ) (U V : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k) (V k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (V ij.1 w * (partialX (V ij.2) w - V ij.2 w / (2 * w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (V ij.2) w)) -
    2 * w.1 * partialX (partialX (V k)) w - shiftedAxial h V k w

/-- An explicit expression for Ω_k/X with no division by X. -/
noncomputable def omegaDivX (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k - 1) (v k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w)) -
    (4 * partialX (v k) w + 2 * w.1 * partialX (partialX (v k)) w) -
    shiftedAxialFactor h v k w

theorem shiftedAxial_axisFactor (h : ℝ) (v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    shiftedAxial h (fun j => axisFactor (v j)) k w = w.1 * shiftedAxialFactor h v k w := by
  cases k with
  | zero => simp [shiftedAxial, shiftedAxialFactor]
  | succ k => exact Z2_axisFactor h (slowOrder h k) (hv k (Nat.le_succ k)) hL

/-- Every term in the actual finite Ω_k source has the factor X. -/
theorem omega_axisFactor (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w = w.1 * omegaDivX h U v k w := by
  have hpair : ∀ ij ∈ Finset.antidiagonal k,
      axisFactor (v ij.1) w * (partialX (axisFactor (v ij.2)) w - axisFactor (v ij.2) w / (2 *
          w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (axisFactor (v ij.2)) w =
      w.1 * (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w) := by
    intro ij hij
    have hj : ij.2 ≤ k := by
      have he := Finset.mem_antidiagonal.mp hij
      omega
    rw [radial_advection_axisFactor ((hv ij.2 hj).differentiableAt (by norm_num)),
      Z_axisFactor h (slowOrder h ij.2) ((hv ij.2 hj).differentiableAt (by norm_num))]
    ring
  unfold omega omegaDivX
  rw [T_axisFactor h (slowOrder h k) ((hv k le_rfl).differentiableAt (by norm_num)),
    Finset.sum_congr rfl hpair, ← Finset.mul_sum,
    partialXX_axisFactor (hv k le_rfl), shiftedAxial_axisFactor h v k w hv hL]
  ring

theorem omega_quotient_eq (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w / w.1 = omegaDivX h U v k w := by
  rw [omega_axisFactor h U v k w hv hL, mul_div_cancel_left₀ _ hX]

theorem partialX_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialX v) w :=
  partialX_smoothAt hv (by simp)

theorem partialEta_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialEta v) w :=
  partialEta_smoothAt hv (by simp)

theorem T_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (T h b v) w := by
  exact (((contDiffAt_const.mul hv).add
    ((contDiffAt_const.mul contDiffAt_snd).mul (partialEta_smooth hv))).add
    (contDiffAt_fst.mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z h b v) w := by
  exact ((((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul hv).add
    ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul (partialEta_smooth hv)) |>.sub
    (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_fst).mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z2_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z2 h b v) w :=
  Z_smooth h (b - D h) (Z_smooth h b hv hL) hL

theorem antidiagonal_indices_le {i j k : ℕ} (hij : (i, j) ∈ Finset.antidiagonal k) :
    i ≤ k ∧ j ≤ k := by
  have he := Finset.mem_antidiagonal.mp hij
  omega

/-- The quotient formula is smooth at the axis, using only the finite input
profiles occurring at this order. No division by the radial coordinate remains. -/
theorem omegaDivX_smooth (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hU : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (U j) w)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (v j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (omegaDivX h U v k) w := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 y * (v ij.2 y / 2 + y.1 * partialX (v ij.2) y) +
        U ij.1 y * Z h (slowOrder h ij.2 - 1) (v ij.2) y)) w := by
    apply ContDiffAt.sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).mul (((hv ij.2 hj).div contDiffAt_const (by norm_num)).add
      (contDiffAt_fst.mul (partialX_smooth (hv ij.2 hj))))).add
      ((hU ij.1 hi).mul (Z_smooth h _ (hv ij.2 hj) hL))
  have hp : ContDiffAt ℝ ∞ (shiftedAxialFactor h v k) w := by
    cases k with
    | zero => exact contDiffAt_const
    | succ k => exact Z2_smooth h _ (hv k (Nat.le_succ k)) hL
  exact (((T_smooth h _ (hv k le_rfl) hL).add hs).sub
    ((contDiffAt_const.mul (partialX_smooth (hv k le_rfl))).add
      ((contDiffAt_const.mul contDiffAt_fst).mul
        (partialX_smooth (partialX_smooth (hv k le_rfl)))))).sub hp

theorem omegaDivX_smooth_extension_at_axis (h : ℝ) (U v : ℕ → InnerProfile)
    (k : ℕ) (η : ℝ)
    (hU : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (U j) (0, η))
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (v j) (0, η)) (hL : L h η ≠ 0) :
    ContDiffAt ℝ ∞ (omegaDivX h U v k) (0, η) :=
  omegaDivX_smooth h U v k (0, η) hU hv hL

theorem partialX_analytic {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) : AnalyticAt ℝ (partialX v) w :=
  ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : InnerPoint)).analyticAt _).comp hv.fderiv

theorem partialEta_analytic {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) : AnalyticAt ℝ (partialEta v) w :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : InnerPoint)).analyticAt _).comp hv.fderiv

theorem T_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (T h b v) w := by
  exact (((analyticAt_const.mul hv).add
    ((analyticAt_const.mul analyticAt_snd).mul (partialEta_analytic hv))).add
    (analyticAt_fst.mul (partialX_analytic hv))).fun_div
    (analyticAt_const.sub (analyticAt_const.mul (analyticAt_snd.pow 2))) hL

theorem Z_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (Z h b v) w := by
  exact ((((analyticAt_const.mul analyticAt_snd).mul analyticAt_const).mul hv).add
    ((analyticAt_const.sub (analyticAt_snd.pow 2)).mul (partialEta_analytic hv)) |>.sub
    (((analyticAt_const.mul analyticAt_snd).mul analyticAt_fst).mul (partialX_analytic hv))).fun_div
    (analyticAt_const.sub (analyticAt_const.mul (analyticAt_snd.pow 2))) hL

theorem Z2_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (Z2 h b v) w :=
  Z_analytic h (b - D h) (Z_analytic h b hv hL) hL

/-- Joint analytic input germs give an analytic quotient germ, including at X=0. -/
theorem omegaDivX_analytic (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hU : ∀ j, j ≤ k → AnalyticAt ℝ (U j) w)
    (hv : ∀ j, j ≤ k → AnalyticAt ℝ (v j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (omegaDivX h U v k) w := by
  have hs : AnalyticAt ℝ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 y * (v ij.2 y / 2 + y.1 * partialX (v ij.2) y) +
        U ij.1 y * Z h (slowOrder h ij.2 - 1) (v ij.2) y)) w := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).mul (((hv ij.2 hj).fun_div analyticAt_const (by norm_num)).add
      (analyticAt_fst.mul (partialX_analytic (hv ij.2 hj))))).add
      ((hU ij.1 hi).mul (Z_analytic h _ (hv ij.2 hj) hL))
  have hp : AnalyticAt ℝ (shiftedAxialFactor h v k) w := by
    cases k with
    | zero => exact analyticAt_const
    | succ k => exact Z2_analytic h _ (hv k (Nat.le_succ k)) hL
  exact (((T_analytic h _ (hv k le_rfl) hL).add hs).sub
    ((analyticAt_const.mul (partialX_analytic (hv k le_rfl))).add
      ((analyticAt_const.mul analyticAt_fst).mul
        (partialX_analytic (partialX_analytic (hv k le_rfl)))))).sub hp

/-! ## Explicit finite jets and parameter-analytic source formulas -/

/-- Jet2 data, collecting `value`, `dx`, `de`, `dxx`, `dxe`, `dex` and their compatibility
conditions. -/
structure Jet2 (K : Type*) where
  /-- Value of `Jet2`, of type `K`. -/
  value : K
  /-- Dx of `Jet2`, of type `K`. -/
  dx : K
  /-- De of `Jet2`, of type `K`. -/
  de : K
  /-- Dxx of `Jet2`, of type `K`. -/
  dxx : K
  /-- Dxe of `Jet2`, of type `K`. -/
  dxe : K
  /-- Dex of `Jet2`, of type `K`. -/
  dex : K
  /-- Dee of `Jet2`, of type `K`. -/
  dee : K

/-- Profile jet, bundling `value`, `dx`, `de`, `dxx` and the required compatibility proofs. -/
noncomputable def profileJet (v : InnerProfile) (w : InnerPoint) : Jet2 ℝ where
  value := v w
  dx := partialX v w
  de := partialEta v w
  dxx := partialX (partialX v) w
  dxe := partialEta (partialX v) w
  dex := partialX (partialEta v) w
  dee := partialEta (partialEta v) w

/-- Jet L, given by `1 - 2 * h * e ^ 2`. -/
noncomputable def jetL {K : Type*} [Field K] (h e : K) : K := 1 - 2 * h * e ^ 2

/-- Jet T, given by `(-b * j.value + (1 / 2 - h) * e * j.de + X * j.dx) / jetL h e`. -/
noncomputable def jetT {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (-b * j.value + (1 / 2 - h) * e * j.de + X * j.dx) / jetL h e

/-- Jet Z numerator, given by `2 * e * b * j.value + (1 - e ^ 2) * j.de - 2 * e * X * j.dx`. -/
noncomputable def jetZNumerator {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * e * b * j.value + (1 - e ^ 2) * j.de - 2 * e * X * j.dx

/-- Jet Z numerator X, given by `2 * e * b * j.dx + (1 - e ^ 2) * j.dex - 2 * e * (j.dx + X *
j.dxx)`. -/
noncomputable def jetZNumeratorX {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * e * b * j.dx + (1 - e ^ 2) * j.dex - 2 * e * (j.dx + X * j.dxx)

/-- Jet Z numerator E, given by `2 * b * j.value + 2 * e * b * j.de - 2 * e * j.de + (1 - e ^ 2)
* j.dee - 2 * X * j.dx - 2 * e * X * j.dxe`. -/
noncomputable def jetZNumeratorE {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * b * j.value + 2 * e * b * j.de - 2 * e * j.de +
    (1 - e ^ 2) * j.dee - 2 * X * j.dx - 2 * e * X * j.dxe

/-- Jet Z, given by `jetZNumerator b X e j / jetL h e`. -/
noncomputable def jetZ {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  jetZNumerator b X e j / jetL h e

/-- Jet ZX, given by `jetZNumeratorX b X e j / jetL h e`. -/
noncomputable def jetZX {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  jetZNumeratorX b X e j / jetL h e

/-- Jet ZE, given by `(jetZNumeratorE b X e j * jetL h e + 4 * h * e * jetZNumerator b X e j) /
jetL h e ^ 2`. -/
noncomputable def jetZE {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (jetZNumeratorE b X e j * jetL h e + 4 * h * e * jetZNumerator b X e j) /
    jetL h e ^ 2

/-- Jet Z2, given by `(2 * e * (b - (1 / 2 - h)) * jetZ h b X e j + (1 - e ^ 2) * jetZE h b X e
j - 2 * e * X * jetZX h b X e j) / jetL h e`. -/
noncomputable def jetZ2 {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (2 * e * (b - (1 / 2 - h)) * jetZ h b X e j +
    (1 - e ^ 2) * jetZE h b X e j - 2 * e * X * jetZX h b X e j) / jetL h e

theorem T_eq_jet (h b : ℝ) (v : InnerProfile) (w : InnerPoint) :
    T h b v w = jetT h b w.1 w.2 (profileJet v w) := rfl

theorem Z_eq_jet (h b : ℝ) (v : InnerProfile) (w : InnerPoint) :
    Z h b v w = jetZ h b w.1 w.2 (profileJet v w) := rfl

theorem Z_partials_eq_jet (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    partialX (Z h b v) w = jetZX h b w.1 w.2 (profileJet v w) ∧
      partialEta (Z h b v) w = jetZE h b w.1 w.2 (profileJet v w) := by
  have hvd := (hv.differentiableAt (by norm_num)).hasFDerivAt
  have hxd := ((partialX_smoothAt hv (m := 1) (by
      norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hed := ((partialEta_smoothAt hv (m := 1) (by
      norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hx : HasFDerivAt (fun y : InnerPoint => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w :=
    hasFDerivAt_fst
  have he : HasFDerivAt (fun y : InnerPoint => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) w :=
    hasFDerivAt_snd
  have hn := (((he.const_mul 2).mul_const b).mul hvd).add
    (((hasFDerivAt_const (1 : ℝ) w).sub (he.mul he)).mul hed) |>.sub
    (((he.const_mul 2).mul hx).mul hxd)
  have hl := (hasFDerivAt_const (1 : ℝ) w).sub ((he.mul he).const_mul (2 * h))
  have hL₀ : 1 - 2 * h * (w.2 * w.2) ≠ 0 := by
    simpa only [L, CoordinateAlgebra.L, pow_two] using hL
  have hL₁ : 1 - 2 * h * w.2 ^ 2 ≠ 0 := hL
  have hz := hn.mul ((hasDerivAt_inv hL₀).comp_hasFDerivAt w hl)
  simp only [Function.comp_def, ← pow_two] at hz
  change HasFDerivAt (Z h b v) _ w at hz
  constructor
  · change (fderiv ℝ (Z h b v) w) (1, 0) = _
    rw [hz.fderiv]
    simp [jetZX, jetZNumeratorX, jetL, profileJet, partialX, partialEta, smul_eq_mul]
    field_simp [hL₁]; ring
  · change (fderiv ℝ (Z h b v) w) (0, 1) = _
    rw [hz.fderiv]
    simp [jetZE, jetZNumeratorE, jetZNumerator, jetL, profileJet, partialX, partialEta,
      smul_eq_mul]
    field_simp [hL₁]; ring

theorem Z2_eq_jet (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    Z2 h b v w = jetZ2 h b w.1 w.2 (profileJet v w) := by
  obtain ⟨hx, he⟩ := Z_partials_eq_jet h b hv hL
  change (2 * w.2 * (b - D h) * Z h b v w + d w.2 * partialEta (Z h b v) w -
    2 * w.2 * w.1 * partialX (Z h b v) w) / L h w.2 = _
  rw [hx, he, Z_eq_jet]
  rfl

/-- Jet shifted as an element of `ℕ → K | 0 => 0 | k + 1 => jetZ2 h (2 * (k : K) * h - 1) X e (v
k)`. -/
noncomputable def jetShifted {K : Type*} [Field K] (h X e : K) (v : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetZ2 h (2 * (k : K) * h - 1) X e (v k)

/-- The same regular source formula over any field, so complex parameter
extensions use precisely the algebra verified for the real profile derivatives. -/
noncomputable def jetOmegaDivX {K : Type*} [Field K] (h X e : K)
    (U : ℕ → K) (v : ℕ → Jet2 K) (k : ℕ) : K :=
  jetT h (2 * (k : K) * h - 1) X e (v k) +
    (∑ ij ∈ Finset.antidiagonal k,
      ((v ij.1).value * ((v ij.2).value / 2 + X * (v ij.2).dx) +
        U ij.1 * jetZ h (2 * (ij.2 : K) * h - 1) X e (v ij.2))) -
    (4 * (v k).dx + 2 * X * (v k).dxx) - jetShifted h X e v k

theorem omegaDivX_eq_jet (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    omegaDivX h U v k w = jetOmegaDivX h w.1 w.2 (fun j => U j w)
      (fun j => profileJet (v j) w) k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [omegaDivX, jetOmegaDivX, shiftedAxialFactor, jetShifted]
    rw [Z2_eq_jet h (slowOrder h k - 1) (hv k (Nat.le_succ k)) hL]
    rfl

/-- Holomorphic extensions of the seven actual input jets. This is stronger
than separate analyticity of v alone and is the precise parameter hypothesis used. -/
structure AnalyticJetAt (J : ℂ → Jet2 ℂ) (e : ℂ) : Prop where
  value : AnalyticAt ℂ (fun z => (J z).value) e
  dx : AnalyticAt ℂ (fun z => (J z).dx) e
  de : AnalyticAt ℂ (fun z => (J z).de) e
  dxx : AnalyticAt ℂ (fun z => (J z).dxx) e
  dxe : AnalyticAt ℂ (fun z => (J z).dxe) e
  dex : AnalyticAt ℂ (fun z => (J z).dex) e
  dee : AnalyticAt ℂ (fun z => (J z).dee) e

theorem jetL_analytic (h e : ℂ) : AnalyticAt ℂ (jetL h) e :=
  analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))

theorem jetT_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetT h b X z (J z)) e := by
  exact (((analyticAt_const.mul hJ.value).add
    ((analyticAt_const.mul analyticAt_id).mul hJ.de)).add
    (analyticAt_const.mul hJ.dx)).fun_div (jetL_analytic h e) hL

theorem jetZNumerator_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumerator b X z (J z)) e := by
  exact ((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.value).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.de)).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dx)

theorem jetZNumeratorX_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumeratorX b X z (J z)) e := by
  exact ((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dx).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.dex)).sub
    ((analyticAt_const.mul analyticAt_id).mul (hJ.dx.add (analyticAt_const.mul hJ.dxx)))

theorem jetZNumeratorE_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumeratorE b X z (J z)) e := by
  exact (((((analyticAt_const.mul hJ.value).add
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.de)).sub
    ((analyticAt_const.mul analyticAt_id).mul hJ.de)).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.dee)).sub
    (analyticAt_const.mul hJ.dx)).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dxe)

theorem jetZ_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZ h b X z (J z)) e :=
  (jetZNumerator_analytic b X hJ).fun_div (jetL_analytic h e) hL

theorem jetZX_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZX h b X z (J z)) e :=
  (jetZNumeratorX_analytic b X hJ).fun_div (jetL_analytic h e) hL

theorem jetZE_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZE h b X z (J z)) e := by
  exact (((jetZNumeratorE_analytic b X hJ).mul (jetL_analytic h e)).add
    ((analyticAt_const.mul analyticAt_id).mul (jetZNumerator_analytic b X hJ))).fun_div
    ((jetL_analytic h e).pow 2) (pow_ne_zero _ hL)

theorem jetZ2_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZ2 h b X z (J z)) e := by
  exact (((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
    (jetZ_analytic h b X hJ hL)).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul (jetZE_analytic h b X hJ hL))).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
      (jetZX_analytic h b X hJ hL))).fun_div (jetL_analytic h e) hL

/-- The finite quotient source is holomorphic in the parameter whenever the
finite input jets have holomorphic extensions and the sole denominator is nonzero. -/
theorem jetOmegaDivX_analytic (h X : ℂ) (U : ℕ → ℂ → ℂ)
    (v : ℕ → ℂ → Jet2 ℂ) (k : ℕ) (e : ℂ)
    (hU : ∀ j, j ≤ k → AnalyticAt ℂ (U j) e)
    (hv : ∀ j, j ≤ k → AnalyticJetAt (v j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetOmegaDivX h X z (fun j => U j z) (fun j => v j z) k) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ Finset.antidiagonal k,
      ((v ij.1 z).value * ((v ij.2 z).value / 2 + X * (v ij.2 z).dx) +
        U ij.1 z * jetZ h (2 * (ij.2 : ℂ) * h - 1) X z (v ij.2 z))) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).value.mul (((hv ij.2 hj).value.fun_div analyticAt_const
      (by norm_num)).add (analyticAt_const.mul (hv ij.2 hj).dx))).add
      ((hU ij.1 hi).mul (jetZ_analytic h _ X (hv ij.2 hj) hL))
  have hp : AnalyticAt ℂ (fun z => jetShifted h X z (fun j => v j z) k) e := by
    cases k with
    | zero => exact analyticAt_const
    | succ k => exact jetZ2_analytic h _ X (hv k (Nat.le_succ k)) hL
  exact (((jetT_analytic h _ X (hv k le_rfl) hL).add hs).sub
    ((analyticAt_const.mul (hv k le_rfl).dx).add
      (analyticAt_const.mul (hv k le_rfl).dxx))).sub hp

/-- Complexify jet, bundling `value`, `dx`, `de`, `dxx` and the required compatibility proofs. -/
noncomputable def complexifyJet (j : Jet2 ℝ) : Jet2 ℂ where
  value := j.value
  dx := j.dx
  de := j.de
  dxx := j.dxx
  dxe := j.dxe
  dex := j.dex
  dee := j.dee

/-- The holomorphic algebra uses the exact real source formula on real inputs. -/
theorem jetOmegaDivX_ofReal (h X e : ℝ) (U : ℕ → ℝ) (v : ℕ → Jet2 ℝ) (k : ℕ) :
    ((jetOmegaDivX h X e U v k : ℝ) : ℂ) =
      jetOmegaDivX (h : ℂ) (X : ℂ) (e : ℂ) (fun j => (U j : ℂ))
        (fun j => complexifyJet (v j)) k := by
  cases k <;> simp [jetOmegaDivX, jetShifted, jetT, jetZ2, jetZ, jetZE, jetZX,
    jetZNumerator, jetZNumeratorX, jetZNumeratorE, jetL, complexifyJet]

theorem omegaDivX_complex_formula (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    (omegaDivX h U v k w : ℂ) =
      jetOmegaDivX (h : ℂ) (w.1 : ℂ) (w.2 : ℂ) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (v j) w)) k := by
  rw [omegaDivX_eq_jet h U v k w hv hL, jetOmegaDivX_ofReal]

/-- Lower pairs, given by `(Finset.antidiagonal n).filter (fun ij => 0 < ij.1 ∧ 0 < ij.2)`. -/
noncomputable def lowerPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal n).filter (fun ij => 0 < ij.1 ∧ 0 < ij.2)

theorem lowerPairs_lt {n i j : ℕ} (hij : (i, j) ∈ lowerPairs n) : i < n ∧ j < n := by
  obtain ⟨ha, hi, hj⟩ := Finset.mem_filter.mp hij
  have he := Finset.mem_antidiagonal.mp ha
  omega

/-- Lower convolution, given by `∑ ij ∈ lowerPairs n, a ij.1 w * b ij.2 w`. -/
noncomputable def lowerConvolution (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint) : ℝ :=
  ∑ ij ∈ lowerPairs n, a ij.1 w * b ij.2 w

/-- Previous omega div X as an element of `ℕ → InnerProfile | 0 => fun _ => 0 | k + 1 =>
omegaDivX h U v k`. -/
noncomputable def previousOmegaDivX (h : ℝ) (U v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => omegaDivX h U v k

/-- The known lower-order pressure source after its radial cancellation. -/
noncomputable def lowerPressureSource (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) : ℝ :=
  C⁻¹ ^ 2 * lowerConvolution φ φ n w - previousOmegaDivX h U v n w / 2

theorem lowerConvolution_smooth (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint)
    (ha : ∀ j, j < n → ContDiffAt ℝ ∞ (a j) w)
    (hb : ∀ j, j < n → ContDiffAt ℝ ∞ (b j) w) :
    ContDiffAt ℝ ∞ (lowerConvolution a b n) w := by
  apply ContDiffAt.sum
  intro ij hij
  obtain ⟨hi, hj⟩ := lowerPairs_lt hij
  exact (ha ij.1 hi).mul (hb ij.2 hj)

theorem lowerPressureSource_smooth (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hφ : ∀ j, j < n → ContDiffAt ℝ ∞ (φ j) w)
    (hU : ∀ j, j < n → ContDiffAt ℝ ∞ (U j) w)
    (hv : ∀ j, j < n → ContDiffAt ℝ ∞ (v j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (lowerPressureSource h C φ U v n) w := by
  have hp : ContDiffAt ℝ ∞ (previousOmegaDivX h U v n) w := by
    cases n with
    | zero => exact contDiffAt_const
    | succ k =>
      exact omegaDivX_smooth h U v k w (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (contDiffAt_const.mul (lowerConvolution_smooth φ φ n w hφ hφ)).sub
    (hp.div contDiffAt_const (by norm_num))

theorem lowerConvolution_analytic (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint)
    (ha : ∀ j, j < n → AnalyticAt ℝ (a j) w)
    (hb : ∀ j, j < n → AnalyticAt ℝ (b j) w) :
    AnalyticAt ℝ (lowerConvolution a b n) w := by
  apply Finset.analyticAt_fun_sum
  intro ij hij
  obtain ⟨hi, hj⟩ := lowerPairs_lt hij
  exact (ha ij.1 hi).mul (hb ij.2 hj)

theorem lowerPressureSource_analytic (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hφ : ∀ j, j < n → AnalyticAt ℝ (φ j) w)
    (hU : ∀ j, j < n → AnalyticAt ℝ (U j) w)
    (hv : ∀ j, j < n → AnalyticAt ℝ (v j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (lowerPressureSource h C φ U v n) w := by
  have hp : AnalyticAt ℝ (previousOmegaDivX h U v n) w := by
    cases n with
    | zero => exact analyticAt_const
    | succ k =>
      exact omegaDivX_analytic h U v k w (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (analyticAt_const.mul (lowerConvolution_analytic φ φ n w hφ hφ)).sub
    (hp.fun_div analyticAt_const (by norm_num))

/-- The regular lower-order source agrees with the displayed pressure source
away from the axis. -/
theorem lowerPressureSource_eq_quotient (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w)
    (hL : L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    lowerPressureSource h C φ U v (k + 1) w =
      C⁻¹ ^ 2 * lowerConvolution φ φ (k + 1) w -
        (omega h U (fun j => axisFactor (v j)) k w / w.1) / 2 := by
  rw [omega_quotient_eq h U v k w hv hL hX]
  rfl

/-- Jet previous omega as an element of `ℕ → K | 0 => 0 | k + 1 => jetOmegaDivX h X e U v k`. -/
noncomputable def jetPreviousOmega {K : Type*} [Field K] (h X e : K)
    (U : ℕ → K) (v : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetOmegaDivX h X e U v k

/-- Parameter-analytic algebra for the same finite lower pressure source. -/
noncomputable def jetLowerPressureSource {K : Type*} [Field K] (h C X e : K)
    (φ U : ℕ → K) (v : ℕ → Jet2 K) (n : ℕ) : K :=
  C⁻¹ ^ 2 * (∑ ij ∈ lowerPairs n, φ ij.1 * φ ij.2) -
    jetPreviousOmega h X e U v n / 2

theorem lowerPressureSource_eq_jet (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    lowerPressureSource h C φ U v n w =
      jetLowerPressureSource h C w.1 w.2 (fun j => φ j w) (fun j => U j w)
        (fun j => profileJet (v j) w) n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [lowerPressureSource, previousOmegaDivX, jetLowerPressureSource,
      jetPreviousOmega]
    rw [omegaDivX_eq_jet h U v k w (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL]
    rfl

theorem jetLowerPressureSource_ofReal (h C X e : ℝ) (φ U : ℕ → ℝ)
    (v : ℕ → Jet2 ℝ) (n : ℕ) :
    ((jetLowerPressureSource h C X e φ U v n : ℝ) : ℂ) =
      jetLowerPressureSource (h : ℂ) (C : ℂ) (X : ℂ) (e : ℂ)
        (fun j => (φ j : ℂ)) (fun j => (U j : ℂ))
        (fun j => complexifyJet (v j)) n := by
  cases n <;> simp [jetLowerPressureSource, jetPreviousOmega, jetOmegaDivX_ofReal]

theorem lowerPressureSource_complex_formula (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    (lowerPressureSource h C φ U v n w : ℂ) =
      jetLowerPressureSource (h : ℂ) (C : ℂ) (w.1 : ℂ) (w.2 : ℂ)
        (fun j => (φ j w : ℂ)) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (v j) w)) n := by
  rw [lowerPressureSource_eq_jet h C φ U v n w hv hL, jetLowerPressureSource_ofReal]

/-- Only previously constructed profiles, indexed strictly below n, are needed
for holomorphy of the known source at order n. -/
theorem jetLowerPressureSource_analytic (h C X : ℂ) (φ U : ℕ → ℂ → ℂ)
    (v : ℕ → ℂ → Jet2 ℂ) (n : ℕ) (e : ℂ)
    (hφ : ∀ j, j < n → AnalyticAt ℂ (φ j) e)
    (hU : ∀ j, j < n → AnalyticAt ℂ (U j) e)
    (hv : ∀ j, j < n → AnalyticJetAt (v j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetLowerPressureSource h C X z
      (fun j => φ j z) (fun j => U j z) (fun j => v j z) n) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ lowerPairs n, φ ij.1 z * φ ij.2 z) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact (hφ ij.1 hi).mul (hφ ij.2 hj)
  have hp : AnalyticAt ℂ (fun z => jetPreviousOmega h X z
      (fun j => U j z) (fun j => v j z) n) e := by
    cases n with
    | zero => exact analyticAt_const
    | succ k =>
      exact jetOmegaDivX_analytic h X U v k e
        (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (analyticAt_const.mul hs).sub (hp.fun_div analyticAt_const (by norm_num))

/-! ## The other finite lower-order transport sources -/

theorem transport_axisFactor (σ : ℝ) (v f : InnerProfile) (w : InnerPoint)
    (hX : w.1 ≠ 0) :
    axisFactor v w * (partialX f w + σ * f w / w.1) =
      v w * (w.1 * partialX f w + σ * f w) := by
  unfold axisFactor
  field_simp [hX]

/-- Shifted profile axial as an element of `ℕ → InnerProfile | 0 => fun _ => 0 | k + 1 => Z2 h
(b + slowOrder h k) (f k)`. -/
noncomputable def shiftedProfileAxial (h b : ℝ) (f : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (b + slowOrder h k) (f k)

/-- The finite known transport part of the angular row has σ=1, and that of
the axial row has σ=0. The base exponents b are supplied separately. -/
noncomputable def lowerTransportSource (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) : ℝ :=
  (∑ ij ∈ lowerPairs n,
    (v ij.1 w * (w.1 * partialX (f ij.2) w + σ * f ij.2 w) +
      U ij.1 w * Z h (b + slowOrder h ij.2) (f ij.2) w)) -
    shiftedProfileAxial h b f n w

theorem lowerTransportSource_eq_quotient (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) (hX : w.1 ≠ 0) :
    lowerTransportSource h b σ v U f n w =
      (∑ ij ∈ lowerPairs n,
        (axisFactor (v ij.1) w * (partialX (f ij.2) w + σ * f ij.2 w / w.1) +
          U ij.1 w * Z h (b + slowOrder h ij.2) (f ij.2) w)) -
        shiftedProfileAxial h b f n w := by
  simp only [lowerTransportSource, transport_axisFactor σ _ _ w hX]

theorem lowerTransportSource_smooth (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ ∞ (v j) w)
    (hU : ∀ j, j < n → ContDiffAt ℝ ∞ (U j) w)
    (hf : ∀ j, j < n → ContDiffAt ℝ ∞ (f j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (lowerTransportSource h b σ v U f n) w := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ ij ∈ lowerPairs n,
      (v ij.1 y * (y.1 * partialX (f ij.2) y + σ * f ij.2 y) +
        U ij.1 y * Z h (b + slowOrder h ij.2) (f ij.2) y)) w := by
    apply ContDiffAt.sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((contDiffAt_fst.mul (partialX_smooth (hf ij.2 hj))).add
      (contDiffAt_const.mul (hf ij.2 hj)))).add
      ((hU ij.1 hi).mul (Z_smooth h _ (hf ij.2 hj) hL))
  have hp : ContDiffAt ℝ ∞ (shiftedProfileAxial h b f n) w := by
    cases n with
    | zero => exact contDiffAt_const
    | succ k => exact Z2_smooth h _ (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

theorem lowerTransportSource_analytic (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → AnalyticAt ℝ (v j) w)
    (hU : ∀ j, j < n → AnalyticAt ℝ (U j) w)
    (hf : ∀ j, j < n → AnalyticAt ℝ (f j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (lowerTransportSource h b σ v U f n) w := by
  have hs : AnalyticAt ℝ (fun y => ∑ ij ∈ lowerPairs n,
      (v ij.1 y * (y.1 * partialX (f ij.2) y + σ * f ij.2 y) +
        U ij.1 y * Z h (b + slowOrder h ij.2) (f ij.2) y)) w := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((analyticAt_fst.mul (partialX_analytic (hf ij.2 hj))).add
      (analyticAt_const.mul (hf ij.2 hj)))).add
      ((hU ij.1 hi).mul (Z_analytic h _ (hf ij.2 hj) hL))
  have hp : AnalyticAt ℝ (shiftedProfileAxial h b f n) w := by
    cases n with
    | zero => exact analyticAt_const
    | succ k => exact Z2_analytic h _ (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

/-- Jet shifted profile axial as an element of `ℕ → K | 0 => 0 | k + 1 => jetZ2 h (b + 2 * (k :
K) * h) X e (f k)`. -/
noncomputable def jetShiftedProfileAxial {K : Type*} [Field K] (h b X e : K)
    (f : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetZ2 h (b + 2 * (k : K) * h) X e (f k)

/-- Jet lower transport source as an element of `K`. -/
noncomputable def jetLowerTransportSource {K : Type*} [Field K] (h b σ X e : K)
    (v U : ℕ → K) (f : ℕ → Jet2 K) (n : ℕ) : K :=
  (∑ ij ∈ lowerPairs n,
    (v ij.1 * (X * (f ij.2).dx + σ * (f ij.2).value) +
      U ij.1 * jetZ h (b + 2 * (ij.2 : K) * h) X e (f ij.2))) -
    jetShiftedProfileAxial h b X e f n

theorem lowerTransportSource_eq_jet (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hf : ∀ j, j < n → ContDiffAt ℝ 2 (f j) w) (hL : L h w.2 ≠ 0) :
    lowerTransportSource h b σ v U f n w =
      jetLowerTransportSource h b σ w.1 w.2 (fun j => v j w) (fun j => U j w)
        (fun j => profileJet (f j) w) n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [lowerTransportSource, jetLowerTransportSource, shiftedProfileAxial,
      jetShiftedProfileAxial]
    rw [Z2_eq_jet h (b + slowOrder h k) (hf k (Nat.lt_succ_self k)) hL]
    rfl

theorem jetLowerTransportSource_ofReal (h b σ X e : ℝ) (v U : ℕ → ℝ)
    (f : ℕ → Jet2 ℝ) (n : ℕ) :
    ((jetLowerTransportSource h b σ X e v U f n : ℝ) : ℂ) =
      jetLowerTransportSource (h : ℂ) (b : ℂ) (σ : ℂ) (X : ℂ) (e : ℂ)
        (fun j => (v j : ℂ)) (fun j => (U j : ℂ))
        (fun j => complexifyJet (f j)) n := by
  cases n <;> simp [jetLowerTransportSource, jetShiftedProfileAxial,
    jetZ2, jetZ, jetZE, jetZX, jetZNumerator, jetZNumeratorX, jetZNumeratorE,
    jetL, complexifyJet]

theorem lowerTransportSource_complex_formula (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hf : ∀ j, j < n → ContDiffAt ℝ 2 (f j) w) (hL : L h w.2 ≠ 0) :
    (lowerTransportSource h b σ v U f n w : ℂ) =
      jetLowerTransportSource (h : ℂ) (b : ℂ) (σ : ℂ) (w.1 : ℂ) (w.2 : ℂ)
        (fun j => (v j w : ℂ)) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (f j) w)) n := by
  rw [lowerTransportSource_eq_jet h b σ v U f n w hf hL, jetLowerTransportSource_ofReal]

theorem jetLowerTransportSource_analytic (h b σ X : ℂ) (v U : ℕ → ℂ → ℂ)
    (f : ℕ → ℂ → Jet2 ℂ) (n : ℕ) (e : ℂ)
    (hv : ∀ j, j < n → AnalyticAt ℂ (v j) e)
    (hU : ∀ j, j < n → AnalyticAt ℂ (U j) e)
    (hf : ∀ j, j < n → AnalyticJetAt (f j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetLowerTransportSource h b σ X z
      (fun j => v j z) (fun j => U j z) (fun j => f j z) n) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ lowerPairs n,
      (v ij.1 z * (X * (f ij.2 z).dx + σ * (f ij.2 z).value) +
        U ij.1 z * jetZ h (b + 2 * (ij.2 : ℂ) * h) X z (f ij.2 z))) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((analyticAt_const.mul (hf ij.2 hj).dx).add
      (analyticAt_const.mul (hf ij.2 hj).value))).add
      ((hU ij.1 hi).mul (jetZ_analytic h _ X (hf ij.2 hj) hL))
  have hp : AnalyticAt ℂ (fun z => jetShiftedProfileAxial h b X z
      (fun j => f j z) n) e := by
    cases n with
    | zero => exact analyticAt_const
    | succ k => exact jetZ2_analytic h _ X (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

end NavierStokes.AxisSourceRegularity

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.SlowRecursion

open Set Filter
open scoped Topology ContDiff

/-- Raw: an abbreviation for `ℝ × ℂ → ℂ`. -/
abbrev Raw := ℝ × ℂ → ℂ

/-- The induction class for actual scalar radial profiles. -/
structure Regular (R : ℝ) (U : Set ℂ) (F : Raw) : Prop where
  smooth : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)
  holomorphic : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U
  even : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)
  real : ∀ r ∈ Ioo (-R) R, ∀ eta : ℝ, (eta : ℂ) ∈ U → (F (r, (eta : ℂ))).im = 0

theorem Regular.const (R : ℝ) (U : Set ℂ) (c : ℝ) :
    Regular R U (fun _ => (c : ℂ)) :=
  ⟨contDiffOn_const, fun _ _ => differentiableOn_const _, fun _ _ _ _ => rfl,
    fun _ _ _ _ => Complex.ofReal_im c⟩

theorem Regular.add {R : ℝ} {U : Set ℂ} {F G : Raw}
    (hF : Regular R U F) (hG : Regular R U G) : Regular R U (F + G) := by
  refine ⟨hF.smooth.add hG.smooth, fun r hr => (hF.holomorphic r hr).add (hG.holomorphic r hr), ?_,
      ?_⟩
  · intro z hz r hr
    change F (-r, z) + G (-r, z) = F (r, z) + G (r, z)
    rw [hF.even z hz r hr, hG.even z hz r hr]
  · intro r hr eta heta
    change (F (r, (eta : ℂ)) + G (r, (eta : ℂ))).im = 0
    simp only [Complex.add_im, hF.real r hr eta heta, hG.real r hr eta heta, add_zero]

theorem Regular.mul {R : ℝ} {U : Set ℂ} {F G : Raw}
    (hF : Regular R U F) (hG : Regular R U G) : Regular R U (F * G) := by
  refine ⟨hF.smooth.mul hG.smooth, fun r hr => (hF.holomorphic r hr).mul (hG.holomorphic r hr), ?_,
      ?_⟩
  · intro z hz r hr
    change F (-r, z) * G (-r, z) = F (r, z) * G (r, z)
    rw [hF.even z hz r hr, hG.even z hz r hr]
  · intro r hr eta heta
    change (F (r, (eta : ℂ)) * G (r, (eta : ℂ))).im = 0
    simp only [Complex.mul_im, hF.real r hr eta heta, hG.real r hr eta heta,
      mul_zero, zero_mul, add_zero]

/-- The class is an actual real algebra of functions. -/
noncomputable def regularAlgebra (R : ℝ) (U : Set ℂ) : Subalgebra ℝ Raw where
  carrier := {F | Regular R U F}
  zero_mem' := Regular.const R U 0
  one_mem' := Regular.const R U 1
  add_mem' := Regular.add
  mul_mem' := Regular.mul
  algebraMap_mem' := fun r => Regular.const R U r

/-- Axis function: an abbreviation for `↥(regularAlgebra R U) instance {R : ℝ} {U : Set ℂ} :
CoeFun (AxisFunction R U) (fun _ => Raw) := ⟨fun F => F.1⟩`. -/
abbrev AxisFunction (R : ℝ) (U : Set ℂ) : Type := ↥(regularAlgebra R U)

instance {R : ℝ} {U : Set ℂ} : CoeFun (AxisFunction R U) (fun _ => Raw) := ⟨fun F => F.1⟩

theorem AxisFunction.smooth {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) :
    ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U) := F.2.smooth

theorem AxisFunction.holomorphic {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) : DifferentiableOn ℂ (fun z => F (r, z)) U :=
  F.2.holomorphic r hr

theorem AxisFunction.even {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ U) : F (-r, z) = F (r, z) :=
  F.2.even z hz r hr

theorem AxisFunction.real {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (F (r, (eta : ℂ))).im = 0 := F.2.real r hr eta heta

/-- Real constant, given by `algebraMap ℝ (AxisFunction R U) c`. -/
noncomputable def realConstant (R : ℝ) (U : Set ℂ) (c : ℝ) : AxisFunction R U :=
  algebraMap ℝ (AxisFunction R U) c

@[simp] theorem realConstant_apply (R : ℝ) (U : Set ℂ) (c : ℝ) (p : ℝ × ℂ) :
    realConstant R U c p = (c : ℂ) := rfl

@[simp] theorem add_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F + G) p = F p + G p := rfl
@[simp] theorem mul_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F * G) p = F p * G p := rfl
@[simp] theorem sub_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F - G) p = F p - G p := rfl
@[simp] theorem neg_apply {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (p : ℝ × ℂ) :
    (-F) p = -F p := rfl
@[simp] theorem zero_apply {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    (0 : AxisFunction R U) p = 0 := rfl
@[simp] theorem one_apply {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    (1 : AxisFunction R U) p = 1 := rfl

/-- Squared radius as an element of `AxisFunction R U`. -/
noncomputable def squaredRadius (R : ℝ) (U : Set ℂ) : AxisFunction R U :=
  ⟨fun p : ℝ × ℂ => ((p.1 ^ 2 : ℝ) : ℂ), {
    smooth := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_fst.pow 2)
    holomorphic := fun r _ => differentiableOn_const ((r ^ 2 : ℝ) : ℂ)
    even := fun _ _ _ _ => by simp only [neg_sq]
    real := fun _ _ _ _ => Complex.ofReal_im _ }⟩

/-- Parameter as an element of `AxisFunction R U`. -/
noncomputable def parameter (R : ℝ) (U : Set ℂ) : AxisFunction R U :=
  ⟨Prod.snd, {
    smooth := contDiffOn_snd
    holomorphic := fun _ _ => differentiableOn_id
    even := fun _ _ _ _ => rfl
    real := fun _ _ _ _ => Complex.ofReal_im _ }⟩

theorem interval_mono {R S : ℝ} (hSR : S ≤ R) : Ioo (-S) S ⊆ Ioo (-R) R := by
  intro r hr
  exact ⟨lt_of_le_of_lt (neg_le_neg hSR) hr.1, lt_of_lt_of_le hr.2 hSR⟩

/-- Restrict as an element of `AxisFunction S U`. -/
noncomputable def restrict {R S : ℝ} {U : Set ℂ} (hSR : S ≤ R)
    (F : AxisFunction R U) : AxisFunction S U :=
  ⟨F, {
    smooth := F.2.smooth.mono (Set.prod_mono (interval_mono hSR) Subset.rfl)
    holomorphic := fun r hr => F.2.holomorphic r (interval_mono hSR hr)
    even := fun z hz r hr => F.2.even z hz r (interval_mono hSR hr)
    real := fun r hr eta heta => F.2.real r (interval_mono hSR hr) eta heta }⟩

@[simp] theorem restrict_apply {R S : ℝ} {U : Set ℂ} (hSR : S ≤ R)
    (F : AxisFunction R U) (p : ℝ × ℂ) : restrict hSR F p = F p := rfl

/-- Inverse as an element of `AxisFunction R U`. -/
noncomputable def inverse {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (hF : ∀ p ∈ Ioo (-R) R ×ˢ U, F p ≠ 0) : AxisFunction R U :=
  ⟨fun p => (F p)⁻¹, {
    smooth := F.2.smooth.inv hF
    holomorphic := fun r hr => (F.2.holomorphic r hr).inv (fun z hz => hF (r, z) ⟨hr, hz⟩)
    even := fun z hz r hr => congrArg Inv.inv (F.2.even z hz r hr)
    real := fun r hr eta heta => by simp [Complex.inv_im, F.2.real r hr eta heta] }⟩

theorem im_iteratedDeriv_zero {S : Set ℝ} (hS : IsOpen S) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hreal : ∀ x ∈ S, (f x).im = 0)
    {x : ℝ} (hx : x ∈ S) (n : ℕ) : (iteratedDeriv n f x).im = 0 := by
  have hc := Complex.imCLM.iteratedFDerivWithin_comp_left (hf x hx) hS.uniqueDiffOn hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hv := congrArg (fun L : ℝ [×n]→L[ℝ] ℝ => L (fun _ => 1)) hc.symm
  have hm : (iteratedDeriv n f x).im = iteratedDeriv n (fun t => (f t).im) x := by
    simp only [iteratedFDerivWithin_of_isOpen n hS hx,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Complex.imCLM_apply, Function.comp_def]
          at hv
    exact hv
  have he : (fun t => (f t).im) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hS.mem_nhds hx] with t ht
    exact hreal t ht
  rw [hm, he.iteratedDeriv_eq n]
  have hz (k : ℕ) : iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact deriv_const t 0
  exact congrFun (hz n) x

theorem scaled_mem_open {R r t : ℝ} (hr : r ∈ Ioo (-R) R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Ioo (-R) R := by
  apply abs_lt.mp
  calc
    |t * r| = t * |r| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ |r| := mul_le_of_le_one_left (abs_nonneg r) ht.2
    _ < R := abs_lt.mpr hr

theorem radialJet_one_real {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (BoundaryAxisJets.radialJet F 1 r (eta : ℂ)).im = 0 := by
  let f : ℝ → ℂ := fun s => F (s, (eta : ℂ))
  have hf : ContDiffOn ℝ ∞ f (Ioo (-R) R) :=
    F.2.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => ⟨hs, heta⟩)
  have hd := VolterraRegularity.real_iteratedDeriv_contDiffOn isOpen_Ioo hf 2
  have hi : IntervalIntegrable (fun t => iteratedDeriv 2 f (t * r))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hd.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
      (fun t ht => scaled_mem_open hr ht)
  change Complex.imCLM ((1 / 2 : ℝ) • ∫ t in (0 : ℝ)..1, iteratedDeriv 2 f (t * r)) = 0
  rw [map_smul, ← Complex.imCLM.intervalIntegral_comp_comm hi]
  have hz : (∫ t in (0 : ℝ)..1, Complex.imCLM (iteratedDeriv 2 f (t * r))) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
        exact im_iteratedDeriv_zero isOpen_Ioo hf
          (fun s hs => F.2.real s hs eta heta) (scaled_mem_open hr ht') 2
      _ = 0 := by simp
  rw [hz, smul_zero]

/-- Radial derivative as an element of `AxisFunction R U`. -/
noncomputable def radialDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) : AxisFunction R U :=
  ⟨fun p => BoundaryAxisJets.radialJet F 1 p.1 p.2, {
    smooth := BoundaryAxisJets.radialJet_joint_contDiffOn_full hR hU F.2.smooth 1
    holomorphic := fun _ hr => BoundaryAxisJets.radialJet_holomorphic_full hR hU
      F.2.smooth F.2.holomorphic 1 hr
    even := fun z hz _ hr => BoundaryAxisJets.radialJet_even_full hR (F.2.even z hz) 1 hr
    real := fun _ hr _ heta => radialJet_one_real F hr heta }⟩

theorem parameterDerivative_real {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {r : ℝ} (hr : r ∈ Ioo (-R) R)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (BoundaryAxisJets.complexPartial F (r, (eta : ℂ))).im = 0 := by
  have hd := ((F.2.holomorphic r hr).differentiableAt (hU.mem_nhds heta)).hasDerivAt.comp_ofReal
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt eta hd).deriv
  have he : (fun t : ℝ => (F (r, (t : ℂ))).im) =ᶠ[𝓝 eta] fun _ => (0 : ℝ) := by
    filter_upwards [Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds heta)]
      with t ht
    exact F.2.real r hr t ht
  change deriv (fun t : ℝ => (F (r, (t : ℂ))).im) eta = _ at hi
  rw [he.deriv_eq, deriv_const] at hi
  exact hi.symm

/-- Parameter derivative as an element of `AxisFunction R U`. -/
noncomputable def parameterDerivative {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) : AxisFunction R U :=
  ⟨BoundaryAxisJets.complexPartial F, {
    smooth := BoundaryAxisJets.complexPartial_contDiffOn isOpen_Ioo hU F.2.smooth F.2.holomorphic
    holomorphic := fun r hr => (F.2.holomorphic r hr).deriv hU
    even := by
      intro z hz r hr
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hU.mem_nhds hz] with w hw
      exact F.2.even w hw r hr
    real := fun _ hr _ heta => parameterDerivative_real hU F hr heta }⟩

theorem hasDerivAt_conjugate {f : ℂ → ℂ} {d z : ℂ}
    (hf : HasDerivAt f d (starRingEnd ℂ z)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  let J := Complex.conjCLE.toContinuousLinearMap
  have hh := J.hasFDerivAt.comp z ((hf.hasFDerivAt.restrictScalars ℝ).comp z J.hasFDerivAt)
  change HasFDerivAt _ ((1 : ℂ →L[ℂ] ℂ).smulRight (starRingEnd ℂ d)) z
  apply hasFDerivAt_of_restrictScalars ℝ hh
  ext v
  simp [J, map_mul]

/-- Reflection gives a holomorphic extension of the actual real trace. -/
noncomputable def realSymmetrization (F : Raw) (p : ℝ × ℂ) : ℂ :=
  (F p + starRingEnd ℂ (F (p.1, starRingEnd ℂ p.2))) / 2

theorem realSymmetrization_real (F : Raw) (r eta : ℝ) :
    realSymmetrization F (r, (eta : ℂ)) = ((F (r, (eta : ℂ))).re : ℂ) := by
  apply Complex.ext <;> simp [realSymmetrization]

/-- Symmetrize as an element of `AxisFunction R U`. -/
noncomputable def symmetrize {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : ∀ z ∈ U, starRingEnd ℂ z ∈ U) (F : Raw)
    (hs : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hh : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) : AxisFunction R U :=
  ⟨realSymmetrization F, {
    smooth := by
      apply ContDiffOn.div_const
      apply hs.add
      apply Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn
      apply hs.comp
        (contDiff_fst.prodMk (Complex.conjCLE.toContinuousLinearMap.contDiff.comp
            contDiff_snd)).contDiffOn
      exact fun p hp => ⟨hp.1, hconj p.2 hp.2⟩
    holomorphic := by
      intro r hr
      apply DifferentiableOn.div_const
      apply (hh r hr).add
      intro z hz
      exact (hasDerivAt_conjugate ((hh r hr).differentiableAt
        (hU.mem_nhds (hconj z hz))).hasDerivAt).differentiableAt.differentiableWithinAt
    even := by
      intro z hz r hr
      dsimp [realSymmetrization]
      rw [he z hz r hr, he _ (hconj z hz) r hr]
    real := by
      intro r _ eta _
      rw [realSymmetrization_real]
      rfl }⟩

/-- Profile, given by `(F (Real.sqrt p.1, (p.2 : ℂ))).re`. -/
noncomputable def profile {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (p : ℝ × ℝ) : ℝ := (F (Real.sqrt p.1, (p.2 : ℂ))).re

/-- Complex profile, given by `F (Real.sqrt p.1, p.2)`. -/
noncomputable def complexProfile {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (p : ℝ × ℂ) : ℂ := F (Real.sqrt p.1, p.2)

theorem sqrt_mem {R X : ℝ} (hR : 0 < R) (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) :
    Real.sqrt X ∈ Ioo (-R) R := by
  constructor
  · linarith [Real.sqrt_nonneg X]
  · nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]

theorem complexProfile_real {R : ℝ} (hR : 0 < R) {U : Set ℂ} (F : AxisFunction R U)
    {X eta : ℝ} (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile F (X, (eta : ℂ)) = (profile F (X, eta) : ℂ) := by
  apply Complex.ext
  · rfl
  · exact F.2.real _ (sqrt_mem hR hX) eta heta

theorem complexProfile_square {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ U) :
    complexProfile F (r ^ 2, z) = F (r, z) := by
  change F (Real.sqrt (r ^ 2), z) = _
  rw [Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 r with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg hs, F.2.even z hz r hr]

theorem profile_smooth {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) :
    ContDiffOn ℝ ∞ (profile F)
      (Ico (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) := by
  let G : ℝ × ℝ → ℝ := fun p => (F (p.2, (p.1 : ℂ))).re
  have hg : ContDiffOn ℝ ∞ G
      (PositiveAxisExistence.realParameterDomain U ×ˢ Ioo (-R) R) :=
    Complex.reCLM.contDiff.comp_contDiffOn (F.2.smooth.comp
      (contDiff_snd.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_fst)).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩))
  have he : ∀ eta ∈ PositiveAxisExistence.realParameterDomain U,
      ∀ r ∈ Ioo (-R) R, G (eta, -r) = G (eta, r) := by
    intro eta heta r hr
    exact congrArg Complex.re (F.2.even _ heta r hr)
  exact (ParametricEvenDescent.contDiffOn_descend_local
    (PositiveAxisExistence.realParameterDomain_isOpen hU) hR hg he).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩)

theorem profile_contDiffAt {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) : ContDiffAt ℝ ∞ (profile F) (X, eta) :=
  ((profile_smooth hR hU F).mono (Set.prod_mono Ioo_subset_Ico_self (Subset.refl _))).contDiffAt
    ((isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds ⟨hX, heta⟩)

theorem radialDerivative_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialDerivative hR hU F) (X, (eta : ℂ)) =
      (SimilarityProfile.partialX (profile F) (X, eta) : ℂ) := by
  have hb := BoundaryAxisJets.axisJet_eq_ordinary_full hR hU F.2.smooth F.2.even 1 hX heta
  have hd := ((profile_contDiffAt hR hU F hX heta).differentiableAt (by
      simp)).hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X eta))
  change HasDerivAt (fun Y => profile F (Y, eta)) (SimilarityProfile.partialX (profile F) (X, eta))
      X at hd
  have he : (fun Y => F (Real.sqrt Y, (eta : ℂ))) =ᶠ[𝓝 X]
      (fun Y => (profile F (Y, eta) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hX] with Y hY
    exact complexProfile_real hR F ⟨hY.1.le, hY.2⟩ heta
  simp only [iteratedDeriv_one, he.deriv_eq, hd.ofReal_comp.deriv] at hb
  exact hb

theorem parameterDerivative_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (parameterDerivative hU F) (X, (eta : ℂ)) =
      (SimilarityProfile.partialEta (profile F) (X, eta) : ℂ) := by
  have hr := sqrt_mem hR ⟨hX.1.le, hX.2⟩
  have hdC := ((F.2.holomorphic _ hr).differentiableAt (hU.mem_nhds heta)).hasDerivAt
  have hdR := PositiveAxisSystem.hasDerivAt_parameterProfile
    ((profile_contDiffAt hR hU F hX heta).differentiableAt (by simp))
  apply Complex.ext
  · exact hdC.real_of_complex.deriv.symm.trans hdR.deriv
  · exact parameterDerivative_real hU F hr heta

theorem profile_radialDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (radialDerivative hR hU F) (X, eta) =
      SimilarityProfile.partialX (profile F) (X, eta) :=
  congrArg Complex.re (radialDerivative_value hR hU F hX heta)

theorem profile_parameterDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (parameterDerivative hU F) (X, eta) =
      SimilarityProfile.partialEta (profile F) (X, eta) :=
  congrArg Complex.re (parameterDerivative_value hR hU F hX heta)

theorem profile_radialDerivative_germ {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (radialDerivative hR hU F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.partialX (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
        heta⟩)] with p hp
  exact profile_radialDerivative hR hU F hp.1 hp.2

theorem profile_parameterDerivative_germ {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (parameterDerivative hU F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.partialEta (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
        heta⟩)] with p hp
  exact profile_parameterDerivative hR hU F hp.1 hp.2

theorem radialDerivative_twice_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialDerivative hR hU (radialDerivative hR hU F)) (X, (eta : ℂ)) =
      (SimilarityProfile.partialX (SimilarityProfile.partialX (profile F)) (X, eta) : ℂ) := by
  rw [radialDerivative_value hR hU _ hX heta]
  unfold SimilarityProfile.partialX
  rw [(profile_radialDerivative_germ hR hU F hX heta).fderiv_eq]
  rfl

/-- Fixed geometric data for one analytic parameter neighborhood. -/
structure Domain (R : ℝ) (U : Set ℂ) (h : ℝ) : Prop where
  positive : 0 < R
  open_set : IsOpen U
  conjugate : ∀ z ∈ U, starRingEnd ℂ z ∈ U
  denominator : ∀ z ∈ U, PositiveAxisSystem.ell (h : ℂ) z ≠ 0

theorem Domain.restrict {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) : Domain S U h := ⟨hS, c.open_set, c.conjugate, c.denominator⟩

/-- Denominator function, given by `1 - realConstant R U (2 * h) * parameter R U ^ 2`. -/
noncomputable def denominatorFunction (R : ℝ) (U : Set ℂ) (h : ℝ) : AxisFunction R U :=
  1 - realConstant R U (2 * h) * parameter R U ^ 2

theorem denominatorFunction_apply (R : ℝ) (U : Set ℂ) (h : ℝ) (p : ℝ × ℂ) :
    denominatorFunction R U h p = PositiveAxisSystem.ell (h : ℂ) p.2 := by
  simp [denominatorFunction, parameter, realConstant, PositiveAxisSystem.ell]

/-- Inverse denominator, given by `inverse (denominatorFunction R U h) (fun p hp => by rw
[denominatorFunction_apply] exact c.denominator p.2 hp.2)`. -/
noncomputable def inverseDenominator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h) :
    AxisFunction R U :=
  inverse (denominatorFunction R U h) (fun p hp => by
    rw [denominatorFunction_apply]
    exact c.denominator p.2 hp.2)

/-- Time operator as an element of `AxisFunction R U`. -/
noncomputable def timeOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) : AxisFunction R U :=
  (-realConstant R U b * F + realConstant R U (1 / 2 - h) * parameter R U *
    parameterDerivative c.open_set F + squaredRadius R U * radialDerivative c.positive c.open_set
        F) *
    inverseDenominator c

/-- Axial operator as an element of `AxisFunction R U`. -/
noncomputable def axialOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) : AxisFunction R U :=
  (realConstant R U 2 * parameter R U * realConstant R U b * F +
    (1 - parameter R U ^ 2) * parameterDerivative c.open_set F -
    realConstant R U 2 * parameter R U * squaredRadius R U *
      radialDerivative c.positive c.open_set F) * inverseDenominator c

@[simp] theorem complexProfile_add {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F + G) p = complexProfile F p + complexProfile G p := rfl
@[simp] theorem complexProfile_sub {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F - G) p = complexProfile F p - complexProfile G p := rfl
@[simp] theorem complexProfile_mul {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F * G) p = complexProfile F p * complexProfile G p := rfl
@[simp] theorem complexProfile_neg {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (-F) p = -complexProfile F p := rfl
@[simp] theorem complexProfile_pow {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (k : ℕ) (p : ℝ × ℂ) :
    complexProfile (F ^ k) p = complexProfile F p ^ k := rfl
@[simp] theorem complexProfile_zero {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    complexProfile (0 : AxisFunction R U) p = 0 := rfl
@[simp] theorem complexProfile_one {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    complexProfile (1 : AxisFunction R U) p = 1 := rfl
@[simp] theorem complexProfile_realConstant (R : ℝ) (U : Set ℂ) (b : ℝ) (p : ℝ × ℂ) :
    complexProfile (realConstant R U b) p = (b : ℂ) := rfl
@[simp] theorem complexProfile_parameter (R : ℝ) (U : Set ℂ) (p : ℝ × ℂ) :
    complexProfile (parameter R U) p = p.2 := rfl
@[simp] theorem complexProfile_squaredRadius (R : ℝ) (U : Set ℂ) {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    complexProfile (squaredRadius R U) (X, z) = (X : ℂ) := by
  change ((Real.sqrt X ^ 2 : ℝ) : ℂ) = _
  rw [Real.sq_sqrt hX]
@[simp] theorem complexProfile_inverseDenominator {R : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain R U h) (p : ℝ × ℂ) :
    complexProfile (inverseDenominator c) p = (PositiveAxisSystem.ell (h : ℂ) p.2)⁻¹ := by
  change (denominatorFunction R U h (Real.sqrt p.1, p.2))⁻¹ = _
  rw [denominatorFunction_apply]

theorem timeOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (timeOperator c b F) (X, (eta : ℂ)) =
      (SimilarityProfile.T h b (profile F) (X, eta) : ℂ) := by
  simp only [timeOperator, complexProfile_mul, complexProfile_add, complexProfile_neg,
    complexProfile_realConstant, complexProfile_parameter, complexProfile_squaredRadius R U hX.1.le,
    complexProfile_inverseDenominator, complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta,
    radialDerivative_value c.positive c.open_set F hX heta,
    parameterDerivative_value c.positive c.open_set F hX heta,
    SimilarityProfile.T, CoordinateAlgebra.timeCoeff, CoordinateAlgebra.L,
    PositiveAxisSystem.ell, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, div_eq_mul_inv]
  norm_num [CoordinateAlgebra.D]

theorem axialOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (axialOperator c b F) (X, (eta : ℂ)) =
      (SimilarityProfile.Z h b (profile F) (X, eta) : ℂ) := by
  simp only [axialOperator, complexProfile_mul, complexProfile_sub, complexProfile_add,
    complexProfile_pow, complexProfile_one, complexProfile_realConstant, complexProfile_parameter,
    complexProfile_squaredRadius R U hX.1.le, complexProfile_inverseDenominator,
    complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta,
    radialDerivative_value c.positive c.open_set F hX heta,
    parameterDerivative_value c.positive c.open_set F hX heta,
    SimilarityProfile.Z, CoordinateAlgebra.axialCoeff, CoordinateAlgebra.L,
    PositiveAxisSystem.ell, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat, div_eq_mul_inv]
  simp [CoordinateAlgebra.d]

theorem axialOperator_germ {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (axialOperator c b F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.Z h b (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen
      c.open_set)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
        heta⟩)] with p hp
  exact congrArg Complex.re (axialOperator_value c b F hp.1 hp.2)

theorem axialOperator_twice_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b₁ b₂ : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (axialOperator c b₂ (axialOperator c b₁ F)) (X, (eta : ℂ)) =
      (SimilarityProfile.Z h b₂ (SimilarityProfile.Z h b₁ (profile F)) (X, eta) : ℂ) := by
  rw [axialOperator_value c b₂ _ hX heta,
    AxisSourceRegularity.Z_congr_germ h b₂ (axialOperator_germ c b₁ F hX heta)]

@[simp] theorem complexProfile_sum {ι : Type*} {R : ℝ} {U : Set ℂ}
    (s : Finset ι) (F : ι → AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (∑ i ∈ s, F i) p = ∑ i ∈ s, complexProfile (F i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, complexProfile_add, ih]

/-- Prior diffusion, with branches according to `n = 0`. -/
noncomputable def priorDiffusion {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  if n = 0 then 0 else
    axialOperator c (b + PositiveAxisSystem.slowPower h (n - 1) - PositiveAxisSystem.dScale h)
      (axialOperator c (b + PositiveAxisSystem.slowPower h (n - 1)) (F (n - 1)))

theorem priorDiffusion_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : ℕ → AxisFunction R U) (n : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (priorDiffusion c b F n) (X, (eta : ℂ)) =
      (PositiveAxisSystem.precedingDiffusion h b (fun j => profile (F j)) n (X, eta) : ℂ) := by
  by_cases hn : n = 0
  · simp [priorDiffusion, PositiveAxisSystem.precedingDiffusion, hn]
  · simp only [priorDiffusion, PositiveAxisSystem.precedingDiffusion, ite_eq_right hn]
    exact axialOperator_twice_value c _ _ _ hX heta

/-- Shifted beta diffusion used in slow recursion. -/
noncomputable def shiftedBetaDiffusion {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (F : ℕ → AxisFunction R U) : ℕ → AxisFunction R U
  | 0 => 0
  | k + 1 => axialOperator c (AxisSourceRegularity.slowOrder h k - 1 - SimilarityProfile.D h)
      (axialOperator c (AxisSourceRegularity.slowOrder h k - 1) (F k))

theorem shiftedBetaDiffusion_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (F : ℕ → AxisFunction R U) (k : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (shiftedBetaDiffusion c F k) (X, (eta : ℂ)) =
      (AxisSourceRegularity.shiftedAxialFactor h (fun j => profile (F j)) k (X, eta) : ℂ) := by
  cases k with
  | zero => rfl
  | succ k => exact axialOperator_twice_value c _ _ _ hX heta

/-- Radial source, constructed using `timeOperator`. -/
noncomputable def radialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (k : ℕ) : AxisFunction R U :=
  timeOperator c (AxisSourceRegularity.slowOrder h k - 1) (beta k) +
    (∑ ij ∈ Finset.antidiagonal k,
      (beta ij.1 * (realConstant R U (1 / 2) * beta ij.2 +
        squaredRadius R U * radialDerivative c.positive c.open_set (beta ij.2)) +
      u ij.1 * axialOperator c (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2))) -
    (realConstant R U 4 * radialDerivative c.positive c.open_set (beta k) +
      realConstant R U 2 * squaredRadius R U *
        radialDerivative c.positive c.open_set (radialDerivative c.positive c.open_set (beta k))) -
    shiftedBetaDiffusion c beta k

theorem radialSource_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (k : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialSource c u beta k) (X, (eta : ℂ)) =
      (AxisSourceRegularity.omegaDivX h (fun j => profile (u j)) (fun j => profile (beta j))
        k (X, eta) : ℂ) := by
  simp only [radialSource, AxisSourceRegularity.omegaDivX, complexProfile_sub, complexProfile_add,
    complexProfile_mul, complexProfile_realConstant, complexProfile_sum,
    complexProfile_squaredRadius R U hX.1.le, timeOperator_value c _ _ hX heta,
    axialOperator_value c _ _ hX heta, shiftedBetaDiffusion_value c _ _ hX heta,
    radialDerivative_value c.positive c.open_set _ hX heta,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [complexProfile_real c.positive _ ⟨hX.1.le, hX.2⟩ heta]
  congr 3
  · apply Finset.sum_congr rfl
    intro ij _
    ring
  · unfold SimilarityProfile.partialX
    rw [(profile_radialDerivative_germ c.positive c.open_set (beta k) hX heta).fderiv_eq]
    rfl

/-- Previous radial source as an element of `ℕ → AxisFunction R U | 0 => 0 | k + 1 =>
radialSource c u beta k`. -/
noncomputable def previousRadialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) : ℕ → AxisFunction R U
  | 0 => 0
  | k + 1 => radialSource c u beta k

theorem previousRadialSource_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (n : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (previousRadialSource c u beta n) (X, (eta : ℂ)) =
      (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (u j))
        (fun j => profile (beta j)) n (X, eta) : ℂ) := by
  cases n with
  | zero => rfl
  | succ k => exact radialSource_value c u beta k hX heta

/-- Angular source as an element of `AxisFunction R U`. -/
noncomputable def angularSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  (∑ i ∈ Finset.range (n - 1),
    (beta (i + 1) * (squaredRadius R U * radialDerivative c.positive c.open_set (phi (n - (i + 1)))
        +
      phi (n - (i + 1))) + u (i + 1) *
      axialOperator c (PositiveAxisSystem.angularPower h + PositiveAxisSystem.slowPower h (n - (i +
          1)))
        (phi (n - (i + 1))))) - priorDiffusion c (PositiveAxisSystem.angularPower h) phi n

/-- Axial source as an element of `AxisFunction R U`. -/
noncomputable def axialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  (∑ i ∈ Finset.range (n - 1),
    (beta (i + 1) * squaredRadius R U * radialDerivative c.positive c.open_set (u (n - (i + 1))) +
      u (i + 1) * axialOperator c
        (PositiveAxisSystem.axialPower h + PositiveAxisSystem.slowPower h (n - (i + 1))) (u (n - (i
            + 1))))) -
    priorDiffusion c (PositiveAxisSystem.axialPower h) u n

/-- Pressure product, given by `∑ i ∈ Finset.range (n - 1), phi (i + 1) * phi (n - (i + 1))`. -/
noncomputable def pressureProduct {R : ℝ} {U : Set ℂ} (phi : ℕ → AxisFunction R U)
    (n : ℕ) : AxisFunction R U :=
  ∑ i ∈ Finset.range (n - 1), phi (i + 1) * phi (n - (i + 1))

/-- Each of the eleven inputs is an actual member of the smooth function
algebra; their regularity follows by construction from the lower profiles. -/
noncomputable def sourceFunctions {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : Fin 11 → AxisFunction R U :=
  ![phi 0, radialDerivative c.positive c.open_set (phi 0), parameterDerivative c.open_set (phi 0),
    u 0, radialDerivative c.positive c.open_set (u 0), parameterDerivative c.open_set (u 0), beta 0,
    angularSource c phi u beta n, axialSource c u beta n, pressureProduct phi n,
    previousRadialSource c u beta n]

/-- Source data, defined pointwise by `complexProfile (sourceFunctions c phi u beta n i)`. -/
noncomputable def sourceData {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : PositiveAxisSystem.CoefficientData :=
  fun i => complexProfile (sourceFunctions c phi u beta n i)

theorem sourceData_regular {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.LowerInputRegularity R U (h : ℂ) (sourceData c phi u beta n) := by
  refine ⟨?_, ?_, c.denominator⟩
  · intro i
    have hs := (sourceFunctions c phi u beta n i).2.smooth
    have hs' : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => sourceData c phi u beta n i (p.1 ^ 2, p.2))
        (Ioo (-R) R ×ˢ U) := hs.congr (fun p hp => complexProfile_square _ hp.1 hp.2)
    simpa only [VolterraRegularity.radialDomain, Real.ball_eq_Ioo, sub_self, zero_sub, zero_add]
        using hs'
  · intro r hr i
    have hr' : r ∈ Ioo (-R) R := by
        simpa [VolterraRegularity.radialDomain, Real.ball_eq_Ioo] using hr
    exact ((sourceFunctions c phi u beta n i).2.holomorphic r hr').congr
      (fun z hz => complexProfile_square _ hr' hz)

theorem sourceData_real {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.RealCompatible R U (sourceData c phi u beta n)
      (PositiveAxisExistence.lowerHistoryData h n (fun j => profile (phi j)) (fun j => profile (u
          j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n)) := by
  intro X hX eta heta i
  have hv (F : AxisFunction R U) := complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta
  have hd (F : AxisFunction R U) := radialDerivative_value c.positive c.open_set F hX heta
  have he (F : AxisFunction R U) := parameterDerivative_value c.positive c.open_set F hX heta
  fin_cases i <;>
    simp only [sourceData, sourceFunctions, PositiveAxisExistence.lowerHistoryData]
  · exact hv _
  · exact hd _
  · exact he _
  · exact hv _
  · exact hd _
  · exact he _
  · exact hv _
  · change complexProfile (angularSource c phi u beta n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).angular : ℂ)
    simp only [angularSource, PositiveAxisSystem.actualLowerSource, PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, PositiveAxisSystem.angularConvection,
      complexProfile_sub, complexProfile_sum, complexProfile_add, complexProfile_mul,
      complexProfile_squaredRadius R U hX.1.le, hd,
      axialOperator_value c _ _ hX heta, priorDiffusion_value c _ _ _ hX heta,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
          PositiveAxisSystem.actualJet]
    simp only [hv]
    rfl
  · change complexProfile (axialSource c u beta n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).axial : ℂ)
    simp only [axialSource, PositiveAxisSystem.actualLowerSource, PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, PositiveAxisSystem.axialConvection,
      complexProfile_sub, complexProfile_sum, complexProfile_add, complexProfile_mul,
      complexProfile_squaredRadius R U hX.1.le, hd,
      axialOperator_value c _ _ hX heta, priorDiffusion_value c _ _ _ hX heta,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
          PositiveAxisSystem.actualJet]
    simp only [hv]
    rfl
  · change complexProfile (pressureProduct phi n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).pressureProduct : ℂ)
    simp only [pressureProduct, PositiveAxisSystem.actualLowerSource,
        PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, complexProfile_sum, complexProfile_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, PositiveAxisSystem.actualJet]
    simp only [hv]
  · exact previousRadialSource_value c u beta n hX heta

/-- Beta operator as an element of `AxisFunction R U`. -/
noncomputable def betaOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U) : AxisFunction R U :=
  (realConstant R U 2 * parameter R U *
      realConstant R U (PositiveAxisSystem.a h - PositiveAxisSystem.slowPower h n) * u -
    realConstant R U 2 * parameter R U *
      realConstant R U (PositiveAxisSystem.dScale h + PositiveAxisSystem.slowPower h n) * k -
    (1 - parameter R U ^ 2) * (parameterDerivative c.open_set u + parameterDerivative c.open_set
        k)) *
    inverseDenominator c

theorem betaOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (betaOperator c n u k) (X, (eta : ℂ)) =
      (PositiveAxisExistence.newBeta h n (profile u) (profile k) (X, eta) : ℂ) := by
  simp only [betaOperator, complexProfile_mul, complexProfile_sub, complexProfile_add,
    complexProfile_pow, complexProfile_one, complexProfile_realConstant, complexProfile_parameter,
    complexProfile_inverseDenominator, parameterDerivative_value c.positive c.open_set _ hX heta,
    PositiveAxisExistence.newBeta, PositiveAxisSystem.betaValue, PositiveAxisSystem.actualJet,
    PositiveAxisSystem.ell, PositiveAxisSystem.edge,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [complexProfile_real c.positive _ ⟨hX.1.le, hX.2⟩ heta]
  rw [div_eq_mul_inv]

/-- Coefficient: an abbreviation for `Fin 5 → AxisFunction R U`. -/
abbrev Coefficient (R : ℝ) (U : Set ℂ) := Fin 5 → AxisFunction R U

/-- Step raw, constructed using `PositiveAxisExistence.positiveSolution`. -/
noncomputable def stepRaw {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U) : VolterraAnalyticBounds.Field :=
  PositiveAxisExistence.positiveSolution hS.le (h : ℂ)
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ)
    (sourceData c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n)

/-- Step component as an element of `AxisFunction S U`. -/
noncomputable def stepComponent {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) : AxisFunction S U := by
  let W := stepRaw c hS C n F
  have hdata := sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2 i) (Ioo (-S) S ×ˢ U) := by
    simpa only [W, stepRaw, VolterraRegularity.radialDomain, Real.ball_eq_Ioo,
      zero_sub, zero_add] using
      (contDiffOn_pi.mp (PositiveAxisExistence.positiveSolution_jointly_smooth hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata) i)
  have hw := PositiveAxisExistence.positiveSolution_spec hS.le hSR c.open_set
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata
  have hh : ∀ r ∈ Ioo (-S) S, DifferentiableOn ℂ (fun z => W r z i) U :=
    fun r hr => hw.parameter_holomorphic r ⟨hr.1.le, hr.2.le⟩ i
  have he : ∀ z ∈ U, ∀ r ∈ Ioo (-S) S, W (-r) z i = W r z i := by
    intro z hz r hr
    apply VolterraParity.first_components_even (i := i)
      (fun r hr z hz => PositiveAxisExistence.positiveSolution_parity hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata hr hz) hi hz r hr
  exact symmetrize c.open_set c.conjugate (fun p => W p.1 p.2 i) hs hh he

theorem stepComponent_profile {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) :
    profile (stepComponent c hS hSR C n F i hi) = PositiveAxisExistence.xProfile (stepRaw c hS C n
        F) i := by
  funext p
  change (realSymmetrization (fun q => stepRaw c hS C n F q.1 q.2 i)
    (Real.sqrt p.1, (p.2 : ℂ))).re = _
  rw [realSymmetrization_real]
  rfl

theorem stepComponent_axis_zero {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) {z : ℂ} (hz : z ∈ U) :
    stepComponent c hS hSR C n F i hi (0, z) = 0 := by
  have hw := PositiveAxisExistence.positiveSolution_spec hS.le hSR c.open_set
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ)
    (sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n)
  change (stepRaw c hS C n F 0 z i + starRingEnd ℂ (stepRaw c hS C n F 0 (starRingEnd ℂ z) i)) / 2
      = 0
  have hz₁ : stepRaw c hS C n F 0 z i = 0 := congrFun (hw.axis_zero z hz) i
  have hz₂ : stepRaw c hS C n F 0 (starRingEnd ℂ z) i = 0 :=
    congrFun (hw.axis_zero _ (c.conjugate z hz)) i
  rw [hz₁, hz₂, map_zero, add_zero, zero_div]

/-- One actual inductive step. The first four profiles come from the
convergent Volterra solution; the fifth is the genuine divergence formula. -/
noncomputable def step {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U) : Coefficient S U :=
  let a := stepComponent c hS hSR C n F 0 (by decide)
  let u := stepComponent c hS hSR C n F 1 (by decide)
  let k := stepComponent c hS hSR C n F 2 (by decide)
  let p := stepComponent c hS hSR C n F 3 (by decide)
  ![a, u, k, p, betaOperator (c.restrict hS) n u k]

theorem step_profile {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 4) :
    profile (step c hS hSR C n F ⟨i.val, by omega⟩) =
      PositiveAxisExistence.xProfile (stepRaw c hS C n F) ⟨i.val, by omega⟩ := by
  fin_cases i <;> exact stepComponent_profile c hS hSR C n F _ (by decide)

theorem sourceData_real_smaller {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S ≤ R) (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.RealCompatible S U (sourceData c phi u beta n)
      (PositiveAxisExistence.lowerHistoryData h n (fun j => profile (phi j)) (fun j => profile (u
          j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n)) := by
  intro X hX eta heta i
  apply sourceData_real c phi u beta n X _ eta heta i
  exact ⟨hX.1, lt_of_lt_of_le hX.2 (sq_le_sq₀ hS.le c.positive.le |>.2 hSR)⟩

theorem step_beta {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2)) (heta : (eta : ℂ) ∈ U) :
    profile (step c hS hSR C n F 4) (X, eta) = PositiveAxisExistence.newBeta h n
      (profile (step c hS hSR C n F 1)) (profile (step c hS hSR C n F 2)) (X, eta) :=
  congrArg Complex.re (betaOperator_value (c.restrict hS) n _ _ hX heta)

theorem step_expanded {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2)) (heta : (eta : ℂ) ∈ U) :
    PositiveAxisSystem.ExpandedEquations h (PositiveAxisSystem.slowPower h n) C eta X
      (PositiveAxisSystem.baseAtOrderZero
        (fun j => PositiveAxisSystem.actualJet (profile (F j 0)) (X, eta))
        (fun j => PositiveAxisSystem.actualJet (profile (F j 1)) (X, eta))
        (fun j => profile (F j 4) (X, eta)))
      (PositiveAxisSystem.actualLowerSource h n (fun j => profile (F j 0)) (fun j => profile (F j
          1))
        (fun j => profile (F j 4)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (F j 1)) (fun j => profile (F j 4)) n) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 0)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 1)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 3)) (X, eta)) := by
  let r := Real.sqrt X
  have hr : r ∈ Ioo (-S) S := sqrt_mem hS ⟨hX.1.le, hX.2⟩
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hX.1).ne'
  have hrX : r ^ 2 = X := Real.sq_sqrt hX.1.le
  have hd := sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n
  have hreal := sourceData_real_smaller c hS hSR.le (fun j => F j 0) (fun j => F j 1) (fun j => F j
      4) n
  have he := PositiveAxisExistence.positiveSolution_profiles_system hS hSR c.open_set
    h (PositiveAxisSystem.slowPower h n) C hd hreal hr hr0 heta
  have h0 : profile (step c hS hSR C n F 0) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 0
      :=
    step_profile c hS hSR C n F 0
  have h1 : profile (step c hS hSR C n F 1) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 1
      :=
    step_profile c hS hSR C n F 1
  have h2 : profile (step c hS hSR C n F 2) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 2
      :=
    step_profile c hS hSR C n F 2
  have h3 : profile (step c hS hSR C n F 3) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 3
      :=
    step_profile c hS hSR C n F 3
  have hsm (i : Fin 5) : ContDiffAt ℝ ∞ (profile (step c hS hSR C n F i)) (r ^ 2, eta) := by
    rw [hrX]
    exact profile_contDiffAt hS c.open_set _ hX heta
  let G := PositiveAxisExistence.lowerHistoryData h n (fun j => profile (F j 0))
    (fun j => profile (F j 1)) (fun j => profile (F j 4))
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (F j 1)) (fun j => profile (F j 4))
        n)
  have he' : PositiveAxisSystem.ProfileSystem h (PositiveAxisSystem.slowPower h n) C r eta
      (PositiveAxisExistence.realBase G (r ^ 2, eta)) (PositiveAxisExistence.realSource G (r ^ 2,
          eta))
      (profile (step c hS hSR C n F 0)) (profile (step c hS hSR C n F 1))
      (profile (step c hS hSR C n F 2)) (profile (step c hS hSR C n F 3)) := by
    rw [h0, h1, h2, h3]
    exact he
  have hout := (PositiveAxisSystem.profileSystem_iff_expanded hr0 _ _
    ((hsm 0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((hsm 1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((hsm 2).differentiableAt (by simp)) ((hsm 3).differentiableAt (by simp))).mp he'
  simp only [hrX] at hout ⊢
  exact hout

theorem betaOperator_axis_zero {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U)
    (hu : ∀ z ∈ U, u (0, z) = 0) (hk : ∀ z ∈ U, k (0, z) = 0)
    {z : ℂ} (hz : z ∈ U) : betaOperator c n u k (0, z) = 0 := by
  have hd (F : AxisFunction R U) (hF : ∀ z ∈ U, F (0, z) = 0) :
      parameterDerivative c.open_set F (0, z) = 0 := by
    have he : (fun w => F (0, w)) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [c.open_set.mem_nhds hz] with w hw
      exact hF w hw
    exact he.deriv_eq.trans (deriv_const z 0)
  change (2 * z * _ * u (0, z) - 2 * z * _ * k (0, z) -
    (1 - z ^ 2) * (parameterDerivative c.open_set u (0, z) + parameterDerivative c.open_set k (0,
        z))) * _ = 0
  rw [hu z hz, hk z hz, hd u hu, hd k hk]
  ring

theorem step_axis_zero {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 5) {z : ℂ} (hz : z ∈ U) : step c hS hSR C n F i (0, z) = 0 := by
  fin_cases i
  · exact stepComponent_axis_zero c hS hSR C n F 0 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 3 (by decide) hz
  · exact betaOperator_axis_zero (c.restrict hS) n _ _
      (fun _ hz => stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz)
      (fun _ hz => stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz) hz

/-- Buffer radii approach a fixed positive core without ever reaching it. -/
noncomputable def radius (core buffer : ℝ) (n : ℕ) : ℝ :=
  core + buffer / ((n : ℝ) + 1)

theorem core_lt_radius {core buffer : ℝ} (hbuffer : 0 < buffer) (n : ℕ) :
    core < radius core buffer n := by
  unfold radius
  have hd : 0 < buffer / ((n : ℝ) + 1) := div_pos hbuffer (by positivity)
  linarith

theorem radius_pos {core buffer : ℝ} (hcore : 0 < core) (hbuffer : 0 < buffer) (n : ℕ) :
    0 < radius core buffer n := lt_trans hcore (core_lt_radius hbuffer n)

theorem radius_antitone {core buffer : ℝ} (hbuffer : 0 ≤ buffer) : Antitone (radius core buffer) :=
    by
  intro m n hmn
  unfold radius
  apply add_le_add_right
  apply div_le_div_of_nonneg_left hbuffer (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem radius_succ_lt {core buffer : ℝ} (hbuffer : 0 < buffer) (n : ℕ) :
    radius core buffer (n + 1) < radius core buffer n := by
  unfold radius
  apply add_lt_add_right
  apply div_lt_div_of_pos_left hbuffer (by positivity)
  norm_num

theorem radiusDomain {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer) (n : ℕ) :
    Domain (radius core buffer n) U h := c.restrict (radius_pos hcore hbuffer n)

/-- Only coefficients with index below `n` are accessed. The zero branch
is outside every finite source sum and is not an assumed future coefficient. -/
noncomputable def lowerHistory {core buffer : ℝ} {U : Set ℂ} (hbuffer : 0 < buffer) (n : ℕ)
    (previous : (j : ℕ) → j < n → Coefficient (radius core buffer j) U) :
    ℕ → Coefficient (radius core buffer (n - 1)) U :=
  fun j => if hj : j < n then
    fun i => restrict (radius_antitone hbuffer.le (by omega : j ≤ n - 1)) (previous j hj i)
  else 0

theorem lowerHistory_apply {core buffer : ℝ} {U : Set ℂ} (hbuffer : 0 < buffer) (n : ℕ)
    (previous : (j : ℕ) → j < n → Coefficient (radius core buffer j) U)
    {j : ℕ} (hj : j < n) (i : Fin 5) (p : ℝ × ℂ) :
    lowerHistory hbuffer n previous j i p = previous j hj i p := by
  simp only [lowerHistory, dite_eq_left hj, restrict_apply]

/-- Recursion step used in slow recursion. -/
noncomputable def recursionStep {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    (n : ℕ) → ((j : ℕ) → j < n → Coefficient (radius core buffer j) U) → Coefficient (radius core
        buffer n) U
  | 0, _ => base
  | n + 1, previous => step (radiusDomain c hcore hbuffer n)
      (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
      (lowerHistory hbuffer (n + 1) previous)

/-- The actual sequence is built by well-founded recursion from one base
coefficient. Every recursive input has a strictly smaller slow index. -/
noncomputable def hierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) :
    Coefficient (radius core buffer n) U :=
  Nat.lt_wfRel.wf.fix (recursionStep c hcore hbuffer C base) n

theorem hierarchy_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    hierarchy c hcore hbuffer C base 0 = base := by
  unfold hierarchy
  rw [WellFounded.fix_eq]
  rfl

theorem hierarchy_succ {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) :
    hierarchy c hcore hbuffer C base (n + 1) =
      step (radiusDomain c hcore hbuffer n)
        (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
        (lowerHistory hbuffer (n + 1) (fun j _ => hierarchy c hcore hbuffer C base j)) := by
  unfold hierarchy
  rw [WellFounded.fix_eq]
  rfl

/-- All orders on the same radial rectangle and the same complex
parameter neighborhood. Restriction changes no pointwise function value. -/
noncomputable def sequence {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) : Coefficient core U :=
  fun i => restrict (core_lt_radius hbuffer n).le (hierarchy c hcore hbuffer C base n i)

theorem sequence_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base n i) = profile (hierarchy c hcore hbuffer C base n i)
        := rfl

theorem sequence_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base 0 i) = profile (base i) := by
  rw [sequence_profile, hierarchy_zero]

theorem lowerHistory_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n j : ℕ} (hj : j < n) (i : Fin 5) :
    profile (lowerHistory hbuffer n (fun j _ => hierarchy c hcore hbuffer C base j) j i) =
      profile (sequence c hcore hbuffer C base j i) := by
  funext p
  exact congrArg Complex.re (lowerHistory_apply hbuffer n _ hj i (Real.sqrt p.1, (p.2 : ℂ)))

theorem previousOmega_congr (h : ℝ) {n : ℕ}
    {u beta u' beta' : ℕ → SimilarityProfile.InnerProfile}
    (hu : ∀ j, j < n → u j = u' j) (hb : ∀ j, j < n → beta j = beta' j) :
    AxisSourceRegularity.previousOmegaDivX h u beta n =
      AxisSourceRegularity.previousOmegaDivX h u' beta' n := by
  cases n with
  | zero => rfl
  | succ k =>
    funext w
    have hs : (∑ ij ∈ Finset.antidiagonal k,
        (beta ij.1 w * (beta ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta ij.2) w) +
          u ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2)
              w)) =
        ∑ ij ∈ Finset.antidiagonal k,
        (beta' ij.1 w * (beta' ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta' ij.2) w) +
          u' ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta'
              ij.2) w) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      rw [hb ij.1 (by omega), hb ij.2 (by omega), hu ij.1 (by omega)]
    have hp : AxisSourceRegularity.shiftedAxialFactor h beta k =
        AxisSourceRegularity.shiftedAxialFactor h beta' k := by
      cases k with
      | zero => rfl
      | succ k => simp only [AxisSourceRegularity.shiftedAxialFactor, hb k (by omega)]
    simp only [AxisSourceRegularity.previousOmegaDivX, AxisSourceRegularity.omegaDivX,
      hb k (Nat.lt_succ_self k), hs, hp]

theorem sequence_succ_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base (n + 1) i) =
      profile (step (radiusDomain c hcore hbuffer n)
        (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
        (lowerHistory hbuffer (n + 1) (fun j _ => hierarchy c hcore hbuffer C base j)) i) := by
  rw [sequence_profile, hierarchy_succ]

theorem core_square_lt {core buffer X : ℝ} (hcore : 0 < core) (hbuffer : 0 < buffer)
    (hX : X < core ^ 2) (n : ℕ) : X < radius core buffer n ^ 2 := by
  have hr := core_lt_radius (core := core) hbuffer n
  nlinarith

theorem sequence_beta {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    profile (sequence c hcore hbuffer C base n 4) (X, eta) =
      PositiveAxisExistence.newBeta h n (profile (sequence c hcore hbuffer C base n 1))
        (profile (sequence c hcore hbuffer C base n 2)) (X, eta) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [sequence_succ_profile]
  exact step_beta (radiusDomain c hcore hbuffer m) (radius_pos hcore hbuffer (m + 1))
    (radius_succ_lt hbuffer m) C (m + 1) _
    ⟨hX.1, core_square_lt hcore hbuffer hX.2 (m + 1)⟩ heta

theorem sequence_expanded {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    PositiveAxisSystem.ExpandedEquations h (PositiveAxisSystem.slowPower h n) C eta X
      (PositiveAxisSystem.baseAtOrderZero
        (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
        (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
        (fun j => profile (A j 4) (X, eta)))
      (PositiveAxisSystem.actualLowerSource h n (fun j => profile (A j 0)) (fun j => profile (A j
          1))
        (fun j => profile (A j 4)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (A j 1)) (fun j => profile (A j 4)) n) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 0)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 1)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 3)) (X, eta)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let A := sequence c hcore hbuffer C base
  let H := lowerHistory hbuffer (m + 1) (fun j _ => hierarchy c hcore hbuffer C base j)
  have hH (j : ℕ) (hj : j < m + 1) (i : Fin 5) : profile (H j i) = profile (A j i) :=
    lowerHistory_profile c hcore hbuffer C base hj i
  have hO := previousOmega_congr h (fun j hj => hH j hj 1) (fun j hj => hH j hj 4)
  have hS := PositiveAxisSystem.actualLowerSource_congr h
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j 4))
        (m + 1))
    (fun j hj => hH j hj 0) (fun j hj => hH j hj 1) (fun j hj => hH j hj 4) (X, eta)
  have hB : PositiveAxisSystem.baseAtOrderZero
      (fun j => PositiveAxisSystem.actualJet (profile (H j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (H j 1)) (X, eta))
      (fun j => profile (H j 4) (X, eta)) =
      PositiveAxisSystem.baseAtOrderZero
      (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
      (fun j => profile (A j 4) (X, eta)) := by
    simp only [PositiveAxisSystem.baseAtOrderZero, hH 0 (Nat.zero_lt_succ m)]
  have hout := step_expanded (radiusDomain c hcore hbuffer m)
    (radius_pos hcore hbuffer (m + 1)) (radius_succ_lt hbuffer m) C (m + 1) H
    ⟨hX.1, core_square_lt hcore hbuffer hX.2 (m + 1)⟩ heta
  rw [hO, hS, hB] at hout
  simpa only [A, H, ← sequence_succ_profile] using hout

/-- Every positive slow coefficient solves the actual finite convolution
equations, with the lower radial residual computed from the same hierarchy. -/
theorem sequence_positive_order {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    PositiveAxisSystem.PositiveOrderEquations h C eta X n
      (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
      (fun j => profile (A j 4) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 3)) (X, eta))
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) (fun j =>
          profile (A j 0)) n (X, eta))
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) (fun j => profile
          (A j 1)) n (X, eta))
      (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j
          4)) n (X, eta)) := by
  apply (PositiveAxisSystem.expanded_iff_positiveOrder h C eta X hn _ _ _ _ _ _ _ _
    (sequence_beta c hcore hbuffer C base hn hX heta)).mp
  exact sequence_expanded c hcore hbuffer C base hn hX heta

theorem sequence_axis_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    (i : Fin 5) {z : ℂ} (hz : z ∈ U) : sequence c hcore hbuffer C base n i (0, z) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change hierarchy c hcore hbuffer C base (m + 1) i (0, z) = 0
  rw [hierarchy_succ]
  exact step_axis_zero _ _ _ _ _ _ _ hz

theorem domain_real_denominator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) : SimilarityProfile.L h eta ≠ 0 := by
  have he : ((SimilarityProfile.L h eta : ℝ) : ℂ) = PositiveAxisSystem.ell (h : ℂ) (eta : ℂ) := by
    simp [SimilarityProfile.L, CoordinateAlgebra.L, PositiveAxisSystem.ell]
  intro hh
  apply c.denominator (eta : ℂ) heta
  rw [← he, hh, Complex.ofReal_zero]

/-- The supplied regular representative really is the original radial
residual divided by X, for every previously constructed order. -/
theorem sequence_omega_quotient {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (k : ℕ)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    AxisSourceRegularity.omega h (fun j => profile (A j 1))
        (fun j => AxisSourceRegularity.axisFactor (profile (A j 4))) k (X, eta) / X =
      AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1))
        (fun j => profile (A j 4)) (k + 1) (X, eta) := by
  apply AxisSourceRegularity.omega_quotient_eq
  · intro j _
    exact (profile_contDiffAt hcore c.open_set _ hX heta).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · exact domain_real_denominator c heta
  · exact hX.1.ne'

theorem average_from_equation {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (u k : AxisFunction R U) {eta X : ℝ} (heta : (eta : ℂ) ∈ U)
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heq : ∀ Y ∈ Ioo (0 : ℝ) (R ^ 2),
      Y * (SimilarityProfile.partialX (profile u) (Y, eta) +
        SimilarityProfile.partialX (profile k) (Y, eta)) + profile k (Y, eta) = 0) :
    ProfileHistories.average (profile u) (X, eta) = profile u (X, eta) + profile k (X, eta) := by
  have hc (F : AxisFunction R U) : ContinuousOn (fun Y => profile F (Y, eta)) (Icc (0 : ℝ) X) :=
    (profile_smooth hR hU F).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun Y hY => ⟨⟨hY.1, lt_of_le_of_lt hY.2 hX.2⟩, heta⟩)
  have hd (F : AxisFunction R U) (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) X) :
      HasDerivAt (fun Z => profile F (Z, eta)) (SimilarityProfile.partialX (profile F) (Y, eta)) Y
          := by
    exact ((profile_contDiffAt hR hU F ⟨hY.1, lt_trans hY.2 hX.2⟩ heta).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt Y ((hasDerivAt_id Y).prodMk (hasDerivAt_const Y eta))
  have hi : IntervalIntegrable (fun Y => profile u (Y, eta)) MeasureTheory.volume 0 X := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hX.1.le] using hc u
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le
    (continuousOn_id.fun_mul ((hc u).fun_add (hc k)))
    (fun Y hY => show HasDerivAt (fun Z => Z * (profile u (Z, eta) + profile k (Z, eta)))
      (profile u (Y, eta)) Y from by
      convert! (hasDerivAt_id Y).fun_mul ((hd u Y hY).fun_add (hd k Y hY)) using 1
      have hh := heq Y ⟨hY.1, lt_trans hY.2 hX.2⟩
      simp only [id_eq, one_mul]
      linarith) hi
  have hmean : X * ProfileHistories.average (profile u) (X, eta) =
      ∫ Y in (0 : ℝ)..X, profile u (Y, eta) := by
    change X • (∫ t in (0 : ℝ)..1, profile u (t * X, eta)) = _
    rw [intervalIntegral.smul_integral_comp_mul_right (f := fun Y => profile u (Y, eta)), zero_mul,
        one_mul]
  rw [he] at hmean
  simp only [id_eq, zero_mul, sub_zero] at hmean
  exact (mul_left_cancel₀ hX.1.ne' hmean)

/-- The stored average defect is the literal integral average, including
the axis. No free integration constant survives the regular zero trace. -/
theorem sequence_average {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ico (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    ProfileHistories.average (profile (A n 1)) (X, eta) =
      profile (A n 1) (X, eta) + profile (A n 2) (X, eta) := by
  by_cases hz : X = 0
  · subst X
    have hk : profile (sequence c hcore hbuffer C base n 2) (0, eta) = 0 := by
      change (sequence c hcore hbuffer C base n 2 (Real.sqrt 0, (eta : ℂ))).re = 0
      rw [Real.sqrt_zero, sequence_axis_zero c hcore hbuffer C base hn 2 heta]
      rfl
    simp [ProfileHistories.average, hk]
  · exact average_from_equation hcore c.open_set _ _ heta ⟨lt_of_le_of_ne hX.1 (Ne.symm hz), hX.2⟩
      (fun Y hY => (sequence_positive_order c hcore hbuffer C base hn hY heta).1)

theorem profile_axis_jet {R : ℝ} (hR : 0 < R) {U : Set ℂ} (F : AxisFunction R U)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) (k : ℕ) :
    iteratedDerivWithin k (fun X => profile F (X, eta)) (Ici 0) 0 =
      ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
        iteratedDeriv (2 * k) (fun r => (F (r, (eta : ℂ))).re) 0 := by
  apply EvenSmoothDescent.iteratedDerivWithin_descent_zero_local
    (f := fun r => (F (r, (eta : ℂ))).re) hR
  · exact Complex.reCLM.contDiff.comp_contDiffOn
      (F.2.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, heta⟩))
  · exact fun r hr => congrArg Complex.re (F.2.even _ heta r hr)

/-- A base made from four genuine profiles; its divergence coefficient is
computed by the same canonical derivative operator used in the recursion. -/
noncomputable def makeBase {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u average pressure : AxisFunction R U) : Coefficient R U :=
  ![phi, u, average - u, pressure, betaOperator c 0 u (average - u)]

theorem sequence_smooth {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞ (profile (sequence c hcore hbuffer C base n i))
      (Ico (0 : ℝ) (core ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) :=
  profile_smooth hcore c.open_set _

theorem sequence_mixed_pullback_smooth {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => BoundaryAxisJets.mixedAxisJet (sequence c hcore hbuffer C base n i) k m
          (p.1 ^ 2, p.2))
      (Ioo (-core) core ×ˢ U) :=
  BoundaryAxisJets.mixedAxisJet_pullback_contDiffOn_full hcore c.open_set
    (sequence c hcore hbuffer C base n i).2.smooth
    (sequence c hcore hbuffer C base n i).2.holomorphic
    (sequence c hcore hbuffer C base n i).2.even k m

theorem sequence_mixed_pullback_holomorphic {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) (k m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-core) core) :
    DifferentiableOn ℂ
      (fun z => BoundaryAxisJets.mixedAxisJet (sequence c hcore hbuffer C base n i) k m (r ^ 2, z))
          U :=
  BoundaryAxisJets.mixedAxisJet_pullback_holomorphic_full hcore c.open_set
    (sequence c hcore hbuffer C base n i).2.smooth
    (sequence c hcore hbuffer C base n i).2.holomorphic
    (sequence c hcore hbuffer C base n i).2.even k m hr

/-- The concrete finite equations of an actual sequence of profile functions. -/
def OrderEquations {R : ℝ} {U : Set ℂ} (h C : ℝ) (A : ℕ → Coefficient R U)
    (n : ℕ) (w : SimilarityProfile.InnerPoint) : Prop :=
  PositiveAxisSystem.PositiveOrderEquations h C w.2 w.1 n
    (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) w)
    (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) w)
    (fun j => profile (A j 4) w)
    (PositiveAxisSystem.actualJet (profile (A n 2)) w)
    (PositiveAxisSystem.actualJet (profile (A n 3)) w)
    (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) (fun j => profile
        (A j 0)) n w)
    (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) (fun j => profile (A
        j 1)) n w)
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j 4))
        n w)

/-- A local slow hierarchy is the output, not a hypothesis on the data.
Its underlying type supplies genuine compatible smooth coefficient functions. -/
structure LocalHierarchy (R : ℝ) (U : Set ℂ) (h C : ℝ)
    (base : Fin 5 → SimilarityProfile.InnerProfile) where
  /-- Coefficients of `LocalHierarchy`, of type `ℕ → Coefficient R U`. -/
  coefficients : ℕ → Coefficient R U
  starts : ∀ i, profile (coefficients 0 i) = base i
  zero_axis : ∀ n, 0 < n → ∀ i : Fin 5, ∀ z ∈ U, coefficients n i (0, z) = 0
  beta : ∀ n, 0 < n → ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    profile (coefficients n 4) (X, eta) = PositiveAxisExistence.newBeta h n
      (profile (coefficients n 1)) (profile (coefficients n 2)) (X, eta)
  equations : ∀ n, 0 < n → ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    OrderEquations h C coefficients n (X, eta)
  average : ∀ n, 0 < n → ∀ X ∈ Ico (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    ProfileHistories.average (profile (coefficients n 1)) (X, eta) =
      profile (coefficients n 1) (X, eta) + profile (coefficients n 2) (X, eta)

/-- Construct every positive slow order from a single finite base profile.
The entire sequence uses one fixed radial core and one fixed parameter domain. -/
noncomputable def buildLocalHierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    LocalHierarchy core U h C (fun i => profile (base i)) where
  coefficients := sequence c hcore hbuffer C base
  starts := sequence_zero c hcore hbuffer C base
  zero_axis := fun _ hn i _ hz => sequence_axis_zero c hcore hbuffer C base hn i hz
  beta := fun _ hn _ hX _ heta => sequence_beta c hcore hbuffer C base hn hX heta
  equations := fun _ hn _ hX _ heta => sequence_positive_order c hcore hbuffer C base hn hX heta
  average := fun _ hn _ hX _ heta => sequence_average c hcore hbuffer C base hn hX heta

theorem exists_local_slow_hierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    Nonempty (LocalHierarchy core U h C (fun i => profile (base i))) :=
  ⟨buildLocalHierarchy c hcore hbuffer C base⟩

theorem LocalHierarchy.profiles_smooth {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (A : LocalHierarchy R U h C base)
    (hR : 0 < R) (hU : IsOpen U) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞ (profile (A.coefficients n i))
      (Ico (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) :=
  profile_smooth hR hU _

/-- Any fixed real parameter window contained in the input neighborhood is
retained at every slow order; the recursion consumes no further strip width. -/
theorem LocalHierarchy.equations_on_window {R : ℝ} {U : Set ℂ} {h C a b : ℝ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (A : LocalHierarchy R U h C base)
    (hwindow : ∀ eta ∈ Icc a b, (eta : ℂ) ∈ U)
    {n : ℕ} (hn : 0 < n) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : eta ∈ Icc a b) : OrderEquations h C A.coefficients n (X, eta) :=
  A.equations n hn X hX eta (hwindow eta heta)

end NavierStokes.SlowRecursion
