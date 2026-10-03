/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentTestAdmissibility
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentCutoffProduct
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Physical weak equation for smooth Fourier cutoffs

The synchronized product-space identity is transferred to the Euclidean cell using the
physical time-torus measure-preserving map and the selected scalar and gradient representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance limitWeakEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitWeakEquationMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitWeakEquationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance limitWeakEquationProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance limitWeakEquationProbabilityTime : IsProbabilityMeasure GalerkinTimeMeasure := by
  refine ⟨?_⟩
  simp [GalerkinTimeMeasure, Real.volume_Ioc]

/-- Lebesgue measure restricted to the physical time-space unit cell. -/
abbrev LimitWeakEquation.limitWeakEquationCellMeasure := volume.restrict AVenhance.timeCube
/-- Product of the Galerkin time measure and the normalized torus measure. -/
abbrev LimitWeakEquation.limitWeakEquationProductMeasure :=
  GalerkinTimeMeasure.prod (volume : Measure Torus)

theorem LimitWeakEquation.integral_product_eq_physical_pullback
    {f : ℝ × Torus → ℝ}
    (hf : Integrable f LimitWeakEquation.limitWeakEquationProductMeasure) :
    ∫ q, f q ∂LimitWeakEquation.limitWeakEquationProductMeasure =
      ∫ p, f (physicalTimeTorusMap p) ∂LimitWeakEquation.limitWeakEquationCellMeasure := by
  change ∫ q, f q ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) =
    ∫ p, f (physicalTimeTorusMap p) ∂(volume.restrict AVenhance.timeCube)
  rw [← measurePreserving_physicalTimeTorusMap.map_eq]
  have hfmap : AEStronglyMeasurable f
      (Measure.map physicalTimeTorusMap (volume.restrict AVenhance.timeCube)) := by
    rw [measurePreserving_physicalTimeTorusMap.map_eq]
    exact hf.aestronglyMeasurable
  exact MeasureTheory.integral_map
    measurePreserving_physicalTimeTorusMap.measurable.aemeasurable hfmap

theorem LimitWeakEquation.scalarFourierModeL2_eq_fin_ae_product (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
    (fun p : ℝ × Torus => realFourierModeL2 N j p.2)
        =ᵐ[LimitWeakEquation.limitWeakEquationProductMeasure]
      fun p => realFourierModeFin N j p.2 := by
  have htorus : (fun y : Torus => realFourierModeL2 N j y) =ᵐ[volume]
      realFourierModeFin N j := (realFourierModeFin_memLp N j).coeFn_toLp
  have hmp : MeasurePreserving Prod.snd
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) (volume : Measure Torus) :=
    measurePreserving_snd
  exact hmp.quasiMeasurePreserving.ae htorus

theorem LimitWeakEquation.gradientFourierModeL2_eq_fin_ae_product (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
    (fun p : ℝ × Torus => realFourierModeGradL2 N j p.2)
        =ᵐ[LimitWeakEquation.limitWeakEquationProductMeasure]
      fun p => WithLp.toLp 2 (realFourierModeGradFin N j p.2) := by
  have htorus : (fun y : Torus => realFourierModeGradL2 N j y) =ᵐ[volume]
      fun y => WithLp.toLp 2 (realFourierModeGradFin N j y) :=
    (realFourierModeGradFin_memLp N j).coeFn_toLp
  have hmp : MeasurePreserving Prod.snd
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) (volume : Measure Torus) :=
    measurePreserving_snd
  exact hmp.quasiMeasurePreserving.ae htorus

theorem LimitWeakEquation.realFourierModeFin_at_cell (N : ℕ) (j : Fin (RealFourierDimension N))
    {x : Vec 2} (hx : x ∈ AVenhance.unitCube) :
    realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 x) =
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
  rw [realFourierModeFin_eq_periodicToTorus]
  have hcell : x ∈ AVenhance.Infra.Torus.unitCell 2 := by
    simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      Set.mem_ofPred_eq, Set.mem_Ioc, zero_add]
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ,
      forall_true_left] at hx
    intro i
    exact ⟨(hx i).1, le_of_lt (hx i).2⟩
  rw [AVenhance.Infra.Torus.periodicToTorus,
    AVenhance.Infra.Torus.unitTorusRepresentative_eq_of_mem_unitCell hcell]

theorem LimitWeakEquation.realFourierModeGradFin_at_cell
    (N : ℕ) (j : Fin (RealFourierDimension N)) {x : Vec 2}
    (hx : x ∈ AVenhance.unitCube) :
    realFourierModeGradFin N j (AVenhance.Infra.Torus.toUnitTorus 2 x) =
      realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) x := by
  rw [realFourierModeGradFin_eq_periodicToTorus]
  have hcell : x ∈ AVenhance.Infra.Torus.unitCell 2 := by
    simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      Set.mem_ofPred_eq, Set.mem_Ioc, zero_add]
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ,
      forall_true_left] at hx
    intro i
    exact ⟨(hx i).1, le_of_lt (hx i).2⟩
  rw [AVenhance.Infra.Torus.periodicToTorus,
    AVenhance.Infra.Torus.unitTorusRepresentative_eq_of_mem_unitCell hcell]

theorem LimitWeakEquation.spacetimeCutoff_spaceGrad_expansion
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) (t : ℝ) :
    AVenhance.spaceGrad (AVenhance.Infra.Section5.testFourierCutoff (φ t) N) =
      fun x => ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j t •
          realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) x := by
  have hsum : AVenhance.Infra.Section5.testFourierCutoff (φ t) N =
      fun x => ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
    funext x
    exact spacetimeTestFourierCutoff_expansion hφ hperiodic N t x
  have hterm (j : Fin (RealFourierDimension N)) (x : Vec 2) :
      HasFDerivAt
        (fun y : Vec 2 => spacetimeRealFourierCoefficient φ N j t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y)
        (spacetimeRealFourierCoefficient φ N j t •
          fderiv ℝ (realFourierModeAmbient N
            ((realFourierIndexEquivFin N).symm j)) x) x := by
    have hmode := (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm j)).differentiable (by simp) x
    exact hmode.hasFDerivAt.const_mul _
  have hderiv (x : Vec 2) :
      fderiv ℝ (fun y => ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y) x =
        ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j t •
            fderiv ℝ (realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm j)) x := by
    have hsum := HasFDerivAt.sum (u := Finset.univ)
      (fun j hj => hterm j x)
    have hfun : (fun y : Vec 2 => ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y) =ᶠ[nhds x]
        (∑ j : Fin (RealFourierDimension N),
          (fun y : Vec 2 => spacetimeRealFourierCoefficient φ N j t *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y)) := by
      filter_upwards [] with y
      simp
    exact (hsum.congr_of_eventuallyEq hfun).fderiv
  funext x i
  rw [show AVenhance.spaceGrad
      (AVenhance.Infra.Section5.testFourierCutoff (φ t) N) x i =
      AVenhance.spaceGrad
        (fun y => ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j t *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y) x i by
        rw [hsum]]
  simp only [AVenhance.spaceGrad]
  rw [hderiv]
  simp [realFourierModeAmbientGrad, AVenhance.spaceGrad, smul_eq_mul]

private theorem synchronized_limit_fourierCutoff_cell_identity_Ceq1 :
  ∀ (Gprod : ↥GradientProductTimeL2) {φ : ℝ → Vec (2 : ℕ) → ℝ}, (ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop
    ℕ∞) fun (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2) → (∀ (t : ℝ), IsZ2Periodic (φ t)) → ∀ (N : ℕ),
  let θN : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) (x : Vec (2 : ℕ)) => Section5.testFourierCutoff (φ
    t) N x;
  let qC : ℝ × Torus → ℝ := fun (p : ℝ × Torus) => ∑ j : Fin (RealFourierDimension N),
    ⟪(↑(↑Gprod : ℝ × Torus →ₘ[GalerkinTimeMeasure.prod volume] SpatialVector) : ℝ × Torus →
    SpatialVector) p, spacetimeRealFourierCoefficient φ N j p.1 • (↑(↑(realFourierModeGradL2 N
    j) : Torus →ₘ[volume] SpatialVector) : Torus → SpatialVector) p.2⟫;
  MeasurableSet timeCube → (∀ᵐ (p : ℝ × Vec (2 : ℕ))
    ∂LimitWeakEquation.limitWeakEquationCellMeasure, ∀ (j : Fin (RealFourierDimension N)),
    (↑(↑(realFourierModeGradL2 N j) : Torus →ₘ[volume] SpatialVector) : Torus → SpatialVector)
    (physicalTimeTorusMap p).2 = WithLp.toLp (2 : ℝ≥0∞) (realFourierModeGradFin N j
    (physicalTimeTorusMap p).2)) → (fun (p : ℝ × Vec (2 : ℕ)) => qC (physicalTimeTorusMap p))
    =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure] fun (p : ℝ × Vec (2 : ℕ)) =>
    Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2) (spaceGrad (θN p.1)
    p.2)
    := by
  intro Gprod φ hφ hperiodic N θN qC htimecube hModeCall
  filter_upwards [hModeCall, ae_restrict_mem htimecube] with p hmodes hp
  rcases hp with ⟨ht, hx⟩
  have hcell : p.2 ∈ AVenhance.Infra.Torus.unitCell 2 := by
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx
    simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      Set.mem_ofPred_eq, zero_add]
    intro i
    exact ⟨(hx i).1, le_of_lt (hx i).2⟩
  have hvec (j : Fin (RealFourierDimension N)) :
      realFourierModeGradL2 N j (physicalTimeTorusMap p).2 =
        WithLp.toLp 2
          (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) p.2) := by
    have hAt := hmodes j
    change realFourierModeGradL2 N j
        (AVenhance.Infra.Torus.toUnitTorus 2 p.2) = _ at hAt
    calc
      _ = WithLp.toLp 2 (realFourierModeGradFin N j
          (AVenhance.Infra.Torus.toUnitTorus 2 p.2)) := hAt
      _ = _ := congrArg (WithLp.toLp 2) (LimitWeakEquation.realFourierModeGradFin_at_cell N j hx)
  have hgrad := LimitWeakEquation.spacetimeCutoff_spaceGrad_expansion hφ hperiodic N p.1
  have hsumVec :
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j p.1 •
          WithLp.toLp 2
            (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) p.2) =
        WithLp.toLp 2 (spaceGrad (θN p.1) p.2) := by
    ext i
    have hi := congrFun (congrFun hgrad p.2) i
    simpa [θN, WithLp.toLp, smul_eq_mul] using hi.symm
  calc
    qC (physicalTimeTorusMap p) =
        ∑ j : Fin (RealFourierDimension N),
          inner ℝ (Gprod (physicalTimeTorusMap p))
            (spacetimeRealFourierCoefficient φ N j p.1 •
              WithLp.toLp 2
                (realFourierModeAmbientGrad N
                  ((realFourierIndexEquivFin N).symm j) p.2)) := by
      simp only [qC, physicalTimeTorusMap]
      apply Finset.sum_congr rfl
      intro j hj
      have hvec' : realFourierModeGradL2 N j
          (AVenhance.Infra.Torus.toUnitTorus 2 p.2) =
          WithLp.toLp 2
            (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) p.2) := by
        simpa [physicalTimeTorusMap] using hvec j
      rw [hvec']
    _ = inner ℝ (Gprod (physicalTimeTorusMap p))
        (WithLp.toLp 2 (spaceGrad (θN p.1) p.2)) := by
      rw [← inner_sum]
      rw [hsumVec]
    _ = Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
        (spaceGrad (θN p.1) p.2) := by
      rw [PiLp.inner_apply]
      simp [synchronizedGradientRepresentative, physicalTimeTorusMap,
        Homogenization.vecDot, mul_comm]

private theorem synchronized_limit_fourierCutoff_cell_identity_Beq2 :
  ∀ (P : FrozenDriftProblem) (Gprod : ↥GradientProductTimeL2) {φ : ℝ → Vec (2 : ℕ) → ℝ},
    (ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) fun (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2) → (∀ (t : ℝ),
    IsZ2Periodic (φ t)) → ∀ (N : ℕ),
  let θN : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) (x : Vec (2 : ℕ)) => Section5.testFourierCutoff (φ
    t) N x;
  let qB : ℝ × Torus → ℝ := fun (p : ℝ × Torus) => ∑ j : Fin (RealFourierDimension N),
    ⟪(↑(↑Gprod : ℝ × Torus →ₘ[GalerkinTimeMeasure.prod volume] SpatialVector) : ℝ × Torus →
    SpatialVector) p, (spacetimeRealFourierCoefficient φ N j p.1 * modeExpansion
    (RealFourierDimension N) (realFourierModeFin N) (realFourierUnitCoefficient N j) p.2) •
    WithLp.toLp (2 : ℝ≥0∞) (Torus.periodicToTorus (P.b p.1) p.2)⟫;
  MeasurableSet timeCube → (fun (p : ℝ × Vec (2 : ℕ)) => qB (physicalTimeTorusMap p))
    =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure] fun (p : ℝ × Vec (2 : ℕ)) =>
    Homogenization.vecDot (P.b p.1 p.2) (synchronizedGradientRepresentative Gprod p.1 p.2) * θN
    p.1 p.2
    := by
  intro P Gprod φ hφ hperiodic N θN qB htimecube
  filter_upwards [ae_restrict_mem htimecube] with p hp
  rcases hp with ⟨ht, hx⟩
  have hcell : p.2 ∈ AVenhance.Infra.Torus.unitCell 2 := by
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx
    simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      Set.mem_ofPred_eq, zero_add]
    intro i
    exact ⟨(hx i).1, le_of_lt (hx i).2⟩
  have hrepr := AVenhance.Infra.Torus.unitTorusRepresentative_eq_of_mem_unitCell hcell
  have hb : AVenhance.Infra.Torus.periodicToTorus (P.b p.1)
      (AVenhance.Infra.Torus.toUnitTorus 2 p.2) = P.b p.1 p.2 := by
    simp [AVenhance.Infra.Torus.periodicToTorus, hrepr]
  have hvalue : ∑ j : Fin (RealFourierDimension N),
      spacetimeRealFourierCoefficient φ N j p.1 *
        realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 p.2) =
      θN p.1 p.2 := by
    change (∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j p.1 *
          realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 p.2)) =
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2
    rw [spacetimeTestFourierCutoff_expansion hφ hperiodic N p.1 p.2]
    apply Finset.sum_congr rfl
    intro j hj
    rw [LimitWeakEquation.realFourierModeFin_at_cell N j hx]
  have hdot : inner ℝ (Gprod (p.1, AVenhance.Infra.Torus.toUnitTorus 2 p.2))
      (WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus
        (P.b p.1) (AVenhance.Infra.Torus.toUnitTorus 2 p.2))) =
    Homogenization.vecDot (P.b p.1 p.2)
      (synchronizedGradientRepresentative Gprod p.1 p.2) := by
    rw [PiLp.inner_apply]
    simp [synchronizedGradientRepresentative, hb, Homogenization.vecDot]
  calc
    qB (physicalTimeTorusMap p) =
        ∑ j : Fin (RealFourierDimension N),
          (spacetimeRealFourierCoefficient φ N j p.1 *
            realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 p.2)) *
            Homogenization.vecDot (P.b p.1 p.2)
              (synchronizedGradientRepresentative Gprod p.1 p.2) := by
      simp only [qB, physicalTimeTorusMap, modeExpansion_unit]
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_smul_right, hdot]
    _ = (∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j p.1 *
            realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 p.2)) *
            Homogenization.vecDot (P.b p.1 p.2)
              (synchronizedGradientRepresentative Gprod p.1 p.2) := by
      rw [Finset.sum_mul]
    _ = Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative Gprod p.1 p.2) *
        θN p.1 p.2 := by rw [hvalue]; ring

private theorem synchronized_limit_fourierCutoff_cell_identity_Aeq3 :
  ∀ (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) (Uprod : ↥ScalarProductTimeL2) (S :
    Set ℝ) {φ : ℝ → Vec (2 : ℕ) → ℝ}, (ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) fun (p : ℝ × Vec (2 :
    ℕ)) => φ p.1 p.2) → (∀ (t : ℝ), IsZ2Periodic (φ t)) → ∀ (N : ℕ),
  let θN : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) (x : Vec (2 : ℕ)) => Section5.testFourierCutoff (φ
    t) N x;
  let qA : ℝ × Torus → ℝ := fun (p : ℝ × Torus) => (↑(↑Uprod : ℝ × Torus
    →ₘ[GalerkinTimeMeasure.prod volume] ℝ) : ℝ × Torus → ℝ) p * ∑ j : Fin (RealFourierDimension
    N), deriv (spacetimeRealFourierCoefficient φ N j) p.1 * (↑(↑(realFourierModeL2 N j) : Torus
    →ₘ[volume] ℝ) : Torus → ℝ) p.2;
  ((fun (p : ℝ × Vec (2 : ℕ)) => synchronizedScalarRepresentative Uprod u S p.1 p.2)
    =ᵐ[volume.restrict timeCube] fun (p : ℝ × Vec (2 : ℕ)) => (↑(↑Uprod : ℝ × Torus
    →ₘ[GalerkinTimeMeasure.prod volume] ℝ) : ℝ × Torus → ℝ) (physicalTimeTorusMap p)) → (∀ᵐ (p :
    ℝ × Vec (2 : ℕ)) ∂LimitWeakEquation.limitWeakEquationCellMeasure, ∀ (j : Fin
    (RealFourierDimension N)), (↑(↑(realFourierModeL2 N j) : Torus →ₘ[volume] ℝ) : Torus → ℝ)
    (physicalTimeTorusMap p).2 = realFourierModeFin N j (physicalTimeTorusMap p).2) →
    MeasurableSet timeCube → (fun (p : ℝ × Vec (2 : ℕ)) => qA (physicalTimeTorusMap p))
    =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure] fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedScalarRepresentative Uprod u S p.1 p.2 * deriv (fun (s : ℝ) => θN s p.2) p.1
    := by
  intro u Uprod S φ hφ hperiodic N θN qA hUrep hModeAall htimecube
  filter_upwards [hUrep, ae_restrict_mem htimecube, hModeAall] with p hUp hp hmodes
  rcases hp with ⟨ht, hx⟩
  have hcell : p.2 ∈ AVenhance.Infra.Torus.unitCell 2 := by
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx
    simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      Set.mem_ofPred_eq, zero_add]
    intro i
    exact ⟨(hx i).1, le_of_lt (hx i).2⟩
  have hModes : ∀ j : Fin (RealFourierDimension N),
      realFourierModeL2 N j (physicalTimeTorusMap p).2 =
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2 := by
    intro j
    have hm := hmodes j
    have hm' : realFourierModeL2 N j
        (AVenhance.Infra.Torus.toUnitTorus 2 p.2) =
        realFourierModeFin N j (AVenhance.Infra.Torus.toUnitTorus 2 p.2) := by
      simpa [physicalTimeTorusMap] using hm
    rw [show (physicalTimeTorusMap p).2 =
        AVenhance.Infra.Torus.toUnitTorus 2 p.2 by rfl, hm',
      LimitWeakEquation.realFourierModeFin_at_cell N j hx]
  have hsumL2 :
      ∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
          realFourierModeL2 N j (physicalTimeTorusMap p).2 =
        deriv (fun s => θN s p.2) p.1 := by
    calc
      _ = ∑ j : Fin (RealFourierDimension N),
          deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hModes j]
      _ = _ := by
            simpa [θN] using
              (spacetimeTestFourierCutoff_timeDerivative hφ hperiodic N p.1 p.2).symm
  change Uprod (physicalTimeTorusMap p) *
      ∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
          realFourierModeL2 N j (physicalTimeTorusMap p).2 = _
  rw [hsumL2, ← hUp]

/-- The product-limit equation gives the physical weak equation for every smooth spatial Fourier
cutoff of a spacetime test. -/
theorem FrozenDriftProblem.synchronized_limit_fourierCutoff_cell_identity
    (P : FrozenDriftProblem) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (S : Set ℝ) (hSmeas : MeasurableSet S)
    (hSae : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S)
    (_hS : ∀ t ∈ S, synchronizedScalarSliceGood Uprod u t)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (hterminal : ∀ t, 1 ≤ t → ∀ x, φ t x = 0) (N : ℕ) :
    ∫ p in AVenhance.timeCube,
      (-(synchronizedScalarRepresentative Uprod u S p.1 p.2) *
          deriv (fun s => AVenhance.Infra.Section5.testFourierCutoff
            (φ s) N p.2) p.1
        + Homogenization.vecDot (P.b p.1 p.2)
            (synchronizedGradientRepresentative Gprod p.1 p.2) *
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2
        + P.κ * Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
            (spaceGrad (AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N) p.2)) =
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
  classical
  let θN : ℝ → Vec 2 → ℝ := fun t x =>
    AVenhance.Infra.Section5.testFourierCutoff (φ t) N x
  have hFourier := P.synchronized_limit_spacetimeFourierCutoff_identity
    σ hσ Uprod Gprod hUweak hGweak hφ hperiodic hterminal N
  have hProductIntegrable := P.spacetimeFourierCutoff_product_integrable Uprod Gprod hφ N
  have hFourierProduct := P.synchronized_limit_spacetimeFourierCutoff_product_identity
    Uprod Gprod hφ N hFourier
  let qA : ℝ × Torus → ℝ := fun p => Uprod p *
    ∑ j : Fin (RealFourierDimension N),
      deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
        realFourierModeL2 N j p.2
  let qB : ℝ × Torus → ℝ := fun p =>
    ∑ j : Fin (RealFourierDimension N),
      inner ℝ (Gprod p)
        ((spacetimeRealFourierCoefficient φ N j p.1 *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N)
            (realFourierUnitCoefficient N j) p.2) •
          WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2))
  let qC : ℝ × Torus → ℝ := fun p =>
    ∑ j : Fin (RealFourierDimension N),
      inner ℝ (Gprod p)
        (spacetimeRealFourierCoefficient φ N j p.1 • realFourierModeGradL2 N j p.2)
  have hIntA : Integrable qA LimitWeakEquation.limitWeakEquationProductMeasure := by
    simpa [qA] using hProductIntegrable.1
  have hIntB : Integrable qB LimitWeakEquation.limitWeakEquationProductMeasure := by
    simpa [qB, modeExpansion_unit] using hProductIntegrable.2.1
  have hIntC : Integrable qC LimitWeakEquation.limitWeakEquationProductMeasure := by
    simpa [qC] using hProductIntegrable.2.2
  have hUrep := synchronizedScalarRepresentative_pullback_ae
    Uprod u S hSmeas hSae
  have hModeA (j : Fin (RealFourierDimension N)) :=
    (measurePreserving_physicalTimeTorusMap.quasiMeasurePreserving.ae
      (LimitWeakEquation.scalarFourierModeL2_eq_fin_ae_product N j))
  have hModeAall : ∀ᵐ p ∂LimitWeakEquation.limitWeakEquationCellMeasure,
      ∀ j : Fin (RealFourierDimension N),
        realFourierModeL2 N j (physicalTimeTorusMap p).2 =
          realFourierModeFin N j (physicalTimeTorusMap p).2 := by
    rw [ae_all_iff]
    intro j
    exact hModeA j
  have hModeC (j : Fin (RealFourierDimension N)) :=
    (measurePreserving_physicalTimeTorusMap.quasiMeasurePreserving.ae
      (LimitWeakEquation.gradientFourierModeL2_eq_fin_ae_product N j))
  have htimecube : MeasurableSet AVenhance.timeCube := by
    rw [AVenhance.timeCube]
    refine measurableSet_Ioo.prod ?_
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hAeq : (fun p => qA (physicalTimeTorusMap p))
      =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure]
      fun p => synchronizedScalarRepresentative Uprod u S p.1 p.2 *
        deriv (fun s => θN s p.2) p.1 := by
    exact @synchronized_limit_fourierCutoff_cell_identity_Aeq3 u Uprod S φ hφ hperiodic N hUrep
        hModeAall htimecube
  have hAmapInt : Integrable (fun p => qA (physicalTimeTorusMap p))
      LimitWeakEquation.limitWeakEquationCellMeasure :=
    (measurePreserving_physicalTimeTorusMap.integrable_comp
      hIntA.aestronglyMeasurable).2 hIntA
  have hAcellInt : Integrable
      (fun p => synchronizedScalarRepresentative Uprod u S p.1 p.2 *
        deriv (fun s => θN s p.2) p.1) LimitWeakEquation.limitWeakEquationCellMeasure :=
    hAmapInt.congr hAeq
  have hprodA : ∫ q, qA q ∂LimitWeakEquation.limitWeakEquationProductMeasure =
      ∫ p in AVenhance.timeCube,
        synchronizedScalarRepresentative Uprod u S p.1 p.2 *
          deriv (fun s => θN s p.2) p.1 := by
    rw [LimitWeakEquation.integral_product_eq_physical_pullback hIntA]
    exact integral_congr_ae hAeq
  have hBeq : (fun p => qB (physicalTimeTorusMap p))
      =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure]
      fun p => Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2 := by
    exact @synchronized_limit_fourierCutoff_cell_identity_Beq2 P Gprod φ hφ hperiodic N htimecube
  have hBmapInt : Integrable (fun p => qB (physicalTimeTorusMap p))
      LimitWeakEquation.limitWeakEquationCellMeasure :=
    (measurePreserving_physicalTimeTorusMap.integrable_comp
      hIntB.aestronglyMeasurable).2 hIntB
  have hBcellInt : Integrable
      (fun p => Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2)
      LimitWeakEquation.limitWeakEquationCellMeasure := hBmapInt.congr hBeq
  have hprodB : ∫ q, qB q ∂LimitWeakEquation.limitWeakEquationProductMeasure =
      ∫ p in AVenhance.timeCube,
        Homogenization.vecDot (P.b p.1 p.2)
          (synchronizedGradientRepresentative Gprod p.1 p.2) *
          θN p.1 p.2 := by
    rw [LimitWeakEquation.integral_product_eq_physical_pullback hIntB]
    exact integral_congr_ae hBeq
  have hModeCall : ∀ᵐ p ∂LimitWeakEquation.limitWeakEquationCellMeasure,
        ∀ j : Fin (RealFourierDimension N),
          realFourierModeGradL2 N j (physicalTimeTorusMap p).2 =
            WithLp.toLp 2 (realFourierModeGradFin N j (physicalTimeTorusMap p).2) := by
    rw [ae_all_iff]
    intro j
    exact hModeC j
  have hCeq : (fun p => qC (physicalTimeTorusMap p))
      =ᵐ[LimitWeakEquation.limitWeakEquationCellMeasure]
      fun p => Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
        (spaceGrad (θN p.1) p.2) := by
    exact @synchronized_limit_fourierCutoff_cell_identity_Ceq1 Gprod φ hφ hperiodic N htimecube
        hModeCall
  have hCmapInt : Integrable (fun p => qC (physicalTimeTorusMap p))
      LimitWeakEquation.limitWeakEquationCellMeasure :=
    (measurePreserving_physicalTimeTorusMap.integrable_comp
      hIntC.aestronglyMeasurable).2 hIntC
  have hCcellInt : Integrable
      (fun p => Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
        (spaceGrad (θN p.1) p.2)) LimitWeakEquation.limitWeakEquationCellMeasure := hCmapInt.congr
            hCeq
  have hprodC : ∫ q, qC q ∂LimitWeakEquation.limitWeakEquationProductMeasure =
      ∫ p in AVenhance.timeCube,
        Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
          (spaceGrad (θN p.1) p.2) := by
    rw [LimitWeakEquation.integral_product_eq_physical_pullback hIntC]
    exact integral_congr_ae hCeq
  have hAnegativeCellInt : Integrable
      (fun p => (-(synchronizedScalarRepresentative Uprod u S p.1 p.2)) *
        deriv (fun s => θN s p.2) p.1) LimitWeakEquation.limitWeakEquationCellMeasure := by
    apply hAcellInt.neg.congr
    filter_upwards [] with p
    change -(synchronizedScalarRepresentative Uprod u S p.1 p.2 *
      deriv (fun s => θN s p.2) p.1) = _
    ring
  have hABcellInt : Integrable
      (fun p => (-(synchronizedScalarRepresentative Uprod u S p.1 p.2)) *
          deriv (fun s => θN s p.2) p.1 +
        Homogenization.vecDot (P.b p.1 p.2)
          (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2)
      LimitWeakEquation.limitWeakEquationCellMeasure := hAnegativeCellInt.add hBcellInt
  have hCscaledInt : Integrable
      (fun p => P.κ * Homogenization.vecDot
        (synchronizedGradientRepresentative Gprod p.1 p.2)
        (spaceGrad (θN p.1) p.2)) LimitWeakEquation.limitWeakEquationCellMeasure :=
    hCcellInt.const_mul P.κ
  have hcellIntegral :
      (∫ p in AVenhance.timeCube,
        (-(synchronizedScalarRepresentative Uprod u S p.1 p.2)) *
            deriv (fun s => θN s p.2) p.1 +
          Homogenization.vecDot (P.b p.1 p.2)
            (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2 +
          P.κ * Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
            (spaceGrad (θN p.1) p.2)) =
        -(∫ p in AVenhance.timeCube,
            synchronizedScalarRepresentative Uprod u S p.1 p.2 *
              deriv (fun s => θN s p.2) p.1) +
          (∫ p in AVenhance.timeCube,
            Homogenization.vecDot (P.b p.1 p.2)
              (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2) +
          P.κ * (∫ p in AVenhance.timeCube,
            Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
              (spaceGrad (θN p.1) p.2)) := by
    rw [integral_add hABcellInt hCscaledInt,
      integral_add hAnegativeCellInt hBcellInt]
    have hAnegativeIntegral :
        (∫ p in AVenhance.timeCube,
          (-(synchronizedScalarRepresentative Uprod u S p.1 p.2)) *
            deriv (fun s => θN s p.2) p.1) =
          -(∫ p in AVenhance.timeCube,
            synchronizedScalarRepresentative Uprod u S p.1 p.2 *
              deriv (fun s => θN s p.2) p.1) := by
      have heq : (fun p : ℝ × Vec 2 =>
          (-(synchronizedScalarRepresentative Uprod u S p.1 p.2)) *
            deriv (fun s => θN s p.2) p.1) =
          fun p => -(synchronizedScalarRepresentative Uprod u S p.1 p.2 *
            deriv (fun s => θN s p.2) p.1) := by
        funext p
        ring
      rw [heq, integral_neg]
    rw [hAnegativeIntegral, integral_const_mul]
  change -(∫ q, qA q ∂LimitWeakEquation.limitWeakEquationProductMeasure) +
      (∫ q, qB q ∂LimitWeakEquation.limitWeakEquationProductMeasure) +
      P.κ * (∫ q, qC q ∂LimitWeakEquation.limitWeakEquationProductMeasure) = _ at hFourierProduct
  rw [hprodA, hprodB, hprodC] at hFourierProduct
  calc
    _ = -(∫ p in AVenhance.timeCube,
          synchronizedScalarRepresentative Uprod u S p.1 p.2 *
            deriv (fun s => θN s p.2) p.1) +
        (∫ p in AVenhance.timeCube,
          Homogenization.vecDot (P.b p.1 p.2)
            (synchronizedGradientRepresentative Gprod p.1 p.2) * θN p.1 p.2) +
        P.κ * (∫ p in AVenhance.timeCube,
          Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
            (spaceGrad (θN p.1) p.2)) := by simpa [θN] using hcellIntegral
    _ = _ := by simpa [θN] using hFourierProduct

end AVenhance.Infra.Parabolic.FourierGalerkin

end
