/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricEvenDescent
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveAxisSystem
public import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Actual positive-order axis solutions

This module connects the sparse six-component Volterra construction to the
explicit positive-order system, and to smooth profiles in the squared radius.
All existence assertions are obtained from the actual convergent series.
-/

noncomputable section

namespace NavierStokes.PositiveAxisExistence

open Set Filter
open scoped Topology ContDiff
open VolterraAnalyticBounds VolterraParity VolterraRegularity
open NilpotentVolterra (equationRHS weightedMean regularPrimitive)

local instance : NormedAddCommGroup (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedAddCommGroup (Fin 6 → Fin 6 → ℂ))
local instance : NormedSpace ℝ (Matrix (Fin 6) (Fin 6) ℂ) :=
  inferInstanceAs (NormedSpace ℝ (Fin 6 → Fin 6 → ℂ))
local instance : NormedSpace ℂ (Matrix (Fin 6) (Fin 6) ℂ) :=
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

noncomputable def realParameterDomain (U : Set ℂ) : Set ℝ :=
  {eta | (eta : ℂ) ∈ U}

theorem realParameterDomain_isOpen {U : Set ℂ} (hU : IsOpen U) :
    IsOpen (realParameterDomain U) := hU.preimage Complex.continuous_ofReal

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

abbrev RealCoefficientData := Fin 11 → ℝ × ℝ → ℝ
abbrev RealField := ℝ → ℝ → Fin 6 → ℝ

noncomputable def realBase (G : RealCoefficientData) (p : ℝ × ℝ) : BaseJet ℝ :=
  ⟨⟨G 0 p, G 1 p, 0, G 2 p⟩, ⟨G 3 p, G 4 p, 0, G 5 p⟩, G 6 p⟩

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
  nlinarith

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
      ((xProfile_contDiffAt hR hU hW hparity 0 (by norm_num) hr hr0 heta).differentiableAt (by
        simp))
    exact hd.deriv.symm.trans ((hrecovery 0 (by norm_num)).deriv_eq.trans hfirst.1)
  have hfive : 2 * r * SimilarityProfile.partialX (xProfile W 1) (r ^ 2, eta) =
      realTrace W r eta 5 := by
    have hd := hasDerivAt_squareProfile
      ((xProfile_contDiffAt hR hU hW hparity 1 (by norm_num) hr hr0 heta).differentiableAt (by
        simp))
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
