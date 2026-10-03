/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitWeakEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitRepresentation
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Arbitrary tests for the synchronized Galerkin limit

The finite Fourier cutoff weak identity passes to every spacetime test by the spacetime
`L²` tail estimates and the Cauchy--Schwarz inequality on the physical cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance arbitraryTestMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance arbitraryTestMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance arbitraryTestProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance arbitraryTestProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance arbitraryTestTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 :=
  ENNReal.HolderTriple.symm
local instance arbitraryTestFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
/-- Closed time-space unit cell used for arbitrary weak test functions. -/
def LimitArbitraryTest.arbitraryTestClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def LimitArbitraryTest.arbitraryTestSpatialClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem LimitArbitraryTest.arbitraryTest_unitCube_measurable : MeasurableSet AVenhance.unitCube :=
    by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem LimitArbitraryTest.arbitraryTest_timeCube_measurable : MeasurableSet AVenhance.timeCube :=
    by
  rw [AVenhance.timeCube]
  exact measurableSet_Ioo.prod LimitArbitraryTest.arbitraryTest_unitCube_measurable

theorem LimitArbitraryTest.arbitraryTestClosedCell_compact : IsCompact
    LimitArbitraryTest.arbitraryTestClosedCell := by
  simpa [LimitArbitraryTest.arbitraryTestClosedCell] using
    isCompact_Icc.prod (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem LimitArbitraryTest.arbitraryTestSpatialClosedCell_compact :
    IsCompact LimitArbitraryTest.arbitraryTestSpatialClosedCell := by
  simpa [LimitArbitraryTest.arbitraryTestSpatialClosedCell] using
    isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc

theorem LimitArbitraryTest.unitCube_subset_arbitraryTestSpatialClosedCell :
    AVenhance.unitCube ⊆ LimitArbitraryTest.arbitraryTestSpatialClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, LimitArbitraryTest.arbitraryTestSpatialClosedCell,
    Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i
  have hxi := hx i
  exact ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩

theorem LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell :
    AVenhance.timeCube ⊆ LimitArbitraryTest.arbitraryTestClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  have hxi := hx i (Set.mem_univ _)
  exact ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩

theorem LimitArbitraryTest.arbitraryTest_continuous_memLp_two {f : ℝ × Vec 2 → ℝ}
    (hf : Continuous f) :
    MemLp f 2 (volume.restrict AVenhance.timeCube) := by
  have hsq : Integrable (fun p : ℝ × Vec 2 => f p ^ 2)
      (volume.restrict AVenhance.timeCube) := by
    exact (hf.pow 2).continuousOn.integrableOn_compact
        LimitArbitraryTest.arbitraryTestClosedCell_compact |>.mono_set
      LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hsq

theorem LimitArbitraryTest.arbitraryTest_continuous_memL2On {f : Vec 2 → ℝ}
    (hf : Continuous f) : MemL2On AVenhance.unitCube f := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  exact (hf.pow 2).continuousOn.integrableOn_compact
    LimitArbitraryTest.arbitraryTestSpatialClosedCell_compact |>.mono_set
      LimitArbitraryTest.unitCube_subset_arbitraryTestSpatialClosedCell

theorem LimitArbitraryTest.arbitraryTest_smoothPeriodicTestL2_ae {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
    (fun y : Torus => smoothPeriodicTestL2 hψ hperiodic y) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus ψ := by
  have hmem := frozenInitialData_memLp_torus
    (LimitArbitraryTest.arbitraryTest_continuous_memL2On hψ.continuous)
  have hclass : smoothPeriodicTestL2 hψ hperiodic = hmem.toLp
      (AVenhance.Infra.Torus.periodicToTorus ψ) := by
    apply Lp.ext
    rfl
  rw [hclass]
  exact hmem.coeFn_toLp

theorem LimitArbitraryTest.spacetimeCutoff_initialClass_eq_mode_sum
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    smoothPeriodicTestL2
        ((AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top)
        (AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N) =
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j := by
  classical
  let ψN : Vec 2 → ℝ := AVenhance.Infra.Section5.testFourierCutoff (φ 0) N
  let hψN : ContDiff ℝ (⊤ : ℕ∞) ψN :=
    (AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top
  let hψNperiodic : AVenhance.IsZ2Periodic ψN :=
    AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N
  have hleft := LimitArbitraryTest.arbitraryTest_smoothPeriodicTestL2_ae hψN hψNperiodic
  have hmode : ∀ᵐ y : Torus ∂volume,
      ∀ j : Fin (RealFourierDimension N),
        realFourierModeL2 N j y = realFourierModeFin N j y := by
    rw [ae_all_iff]
    intro j
    exact (realFourierModeFin_memLp N j).coeFn_toLp
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin (RealFourierDimension N) =>
      spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j)
  have hsmul : ∀ᵐ y : Torus ∂volume,
      ∀ j : Fin (RealFourierDimension N),
        (spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) y =
          spacetimeRealFourierCoefficient φ N j 0 * realFourierModeFin N j y := by
    apply ae_all_iff.2
    intro j
    filter_upwards [Lp.coeFn_smul (spacetimeRealFourierCoefficient φ N j 0)
      (realFourierModeL2 N j), hmode] with y hs hm
    calc
      (spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) y =
          spacetimeRealFourierCoefficient φ N j 0 * realFourierModeL2 N j y := by
            simpa [PiLp.smul_apply, smul_eq_mul] using hs
      _ = spacetimeRealFourierCoefficient φ N j 0 * realFourierModeFin N j y := by
            rw [hm]
  apply Lp.ext
  filter_upwards [hleft, hmode, hsum, hsmul] with y hleftY hmodeY hsumY hsmulY
  rw [hleftY]
  have hexp := spacetimeTestFourierCutoff_expansion hφ hperiodic N 0
    (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)
  calc
    AVenhance.Infra.Torus.periodicToTorus ψN y =
        ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j 0 *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)
              (AVenhance.Infra.Torus.unitTorusRepresentative 2 y) := by
        change AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.Infra.Section5.testFourierCutoff (φ 0) N) y = _
        exact hexp
    _ = ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j 0 * realFourierModeFin N j y := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [realFourierModeFin_eq_periodicToTorus]
        rfl
    _ = ∑ j : Fin (RealFourierDimension N),
          (spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hsmulY j).symm
    _ = (∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) y :=
        by simpa only [Finset.sum_apply] using hsumY.symm

theorem LimitArbitraryTest.timeCube_measure_eq_iterated :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

local instance arbitraryTestFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [LimitArbitraryTest.timeCube_measure_eq_iterated]
  infer_instance

theorem LimitArbitraryTest.galTime_eq_Ioo_measure :
    GalerkinTimeMeasure = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  change volume.restrict (Set.Ioc (0 : ℝ) 1) = _
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm

theorem LimitArbitraryTest.timeCube_square_integral_eq_time_l2 {f : ℝ × Vec 2 → ℝ}
    (hf : Continuous f) :
    (∫ p in AVenhance.timeCube, f p ^ 2) =
      ∫ t, AVenhance.l2NormSq (fun x => f (t, x)) ∂GalerkinTimeMeasure := by
  have hInt : Integrable (fun p : ℝ × Vec 2 => f p ^ 2)
      (volume.restrict AVenhance.timeCube) := by
    exact (hf.pow 2).continuousOn.integrableOn_compact
        LimitArbitraryTest.arbitraryTestClosedCell_compact |>.mono_set
      LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
  have hIntProd : Integrable (fun p : ℝ × Vec 2 => f p ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rw [← LimitArbitraryTest.timeCube_measure_eq_iterated]
    exact hInt
  rw [LimitArbitraryTest.timeCube_measure_eq_iterated]
  calc
    (∫ p, f p ^ 2 ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
      (volume.restrict AVenhance.unitCube))) =
        ∫ t : ℝ, ∫ x : Vec 2, f (t, x) ^ 2
          ∂(volume.restrict AVenhance.unitCube)
          ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            exact integral_prod _ hIntProd
    _ = ∫ t, AVenhance.l2NormSq (fun x => f (t, x))
          ∂GalerkinTimeMeasure := by
            rw [LimitArbitraryTest.galTime_eq_Ioo_measure]
            rfl

theorem LimitArbitraryTest.arbitraryTest_l2_pairing_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun x => |f x|)
    (g := fun x => |g x|) (μ := μ) Real.HolderConjugate.two_two
    (ae_of_all _ (fun x => abs_nonneg _)) (ae_of_all _ (fun x => abs_nonneg _))
    (by simpa [Real.norm_eq_abs] using hf.norm)
    (by simpa [Real.norm_eq_abs] using hg.norm)
  have hAbs : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
    simpa [Real.norm_eq_abs, abs_mul] using norm_integral_le_integral_norm (fun x => f x * g x)
  exact hAbs.trans (by
    simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div] using hHolder)

theorem LimitArbitraryTest.arbitraryTest_memLp_square_integrable {α : Type*} [MeasurableSpace α]
    {f : α → ℝ} {μ : Measure α}
    (hf : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf

theorem LimitArbitraryTest.arbitraryTest_memLp_vectorCoord {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p => f p ^ 2) (volume.restrict AVenhance.timeCube) :=
  LimitArbitraryTest.arbitraryTest_memLp_square_integrable hf

theorem LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2) := by
  apply continuous_pi
  intro i
  have hFderiv : Continuous
      (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) :=
    hφ.continuous_fderiv (by norm_num)
  have h : Continuous (fun p : ℝ × Vec 2 =>
      (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
        (0, Homogenization.basisVec i)) :=
    hFderiv.clm_apply continuous_const
  have heq (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (φ p.1) p.2 i =
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
          (0, Homogenization.basisVec i) := by
    let F : ℝ × Vec 2 → ℝ := fun q => φ q.1 q.2
    have houter : HasFDerivAt F (fderiv ℝ F (p.1, p.2)) (p.1, p.2) :=
      (hφ.differentiable (by norm_num) (p.1, p.2)).hasFDerivAt
    have hline : HasFDerivAt (fun x : Vec 2 => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := HasFDerivAt.comp p.2 houter hline
    have hlineEval : (ContinuousLinearMap.inr ℝ ℝ (Vec 2))
        (Homogenization.basisVec i) = (0, Homogenization.basisVec i) := by
      simp [ContinuousLinearMap.inr]
    change fderiv ℝ (F ∘ fun x : Vec 2 => (p.1, x)) p.2
        (Homogenization.basisVec i) = _
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, hlineEval]
    rfl
  exact h.congr fun p => (heq p).symm

theorem LimitArbitraryTest.arbitraryTest_cell_coord_le_grad
    {F : Vec 2 → Vec 2} (hF : Continuous F) (i : Fin 2) :
    AVenhance.l2NormSq (fun x => F x i) ≤ AVenhance.gradNormSq F := by
  have hcoord : Integrable (fun x : Vec 2 => (F x i) ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    exact (((continuous_apply i).comp hF).pow 2).continuousOn.integrableOn_compact
      LimitArbitraryTest.arbitraryTestSpatialClosedCell_compact |>.mono_set
        LimitArbitraryTest.unitCube_subset_arbitraryTestSpatialClosedCell
  have hvec : Integrable (fun x : Vec 2 => Homogenization.vecNormSq (F x))
      (volume.restrict AVenhance.unitCube) := by
    have hsq : Continuous (fun x : Vec 2 => Homogenization.vecNormSq (F x)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact continuous_finsetSum Finset.univ fun j hj =>
        ((continuous_apply j).comp hF).mul ((continuous_apply j).comp hF)
    exact hsq.continuousOn.integrableOn_compact
        LimitArbitraryTest.arbitraryTestSpatialClosedCell_compact |>.mono_set
      LimitArbitraryTest.unitCube_subset_arbitraryTestSpatialClosedCell
  unfold AVenhance.l2NormSq AVenhance.gradNormSq
  apply setIntegral_mono_on hcoord hvec LimitArbitraryTest.arbitraryTest_unitCube_measurable
  intro x hx
  simp only [Homogenization.vecNormSq, Homogenization.vecDot]
  simpa [pow_two] using (Finset.single_le_sum (s := Finset.univ)
    (fun j hj => sq_nonneg (F x j)) (Finset.mem_univ i))

theorem LimitArbitraryTest.arbitraryTest_timeCube_vectorEnergy_eq
    {F : ℝ × Vec 2 → Vec 2} (hF : Continuous F) :
    (∫ p in AVenhance.timeCube, Homogenization.vecNormSq (F p)) =
      ∫ t, AVenhance.gradNormSq (fun x => F (t, x)) ∂GalerkinTimeMeasure := by
  have hsq : Continuous (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p)) := by
    unfold Homogenization.vecNormSq Homogenization.vecDot
    exact continuous_finsetSum Finset.univ fun i hi =>
      ((continuous_apply i).comp hF).mul ((continuous_apply i).comp hF)
  have hInt : Integrable (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p))
      (volume.restrict AVenhance.timeCube) := by
    exact hsq.continuousOn.integrableOn_compact LimitArbitraryTest.arbitraryTestClosedCell_compact
        |>.mono_set
      LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
  have hIntProd : Integrable (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rw [← LimitArbitraryTest.timeCube_measure_eq_iterated]
    exact hInt
  rw [LimitArbitraryTest.timeCube_measure_eq_iterated]
  calc
    (∫ p, Homogenization.vecNormSq (F p) ∂
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube))) =
      ∫ t : ℝ, ∫ x : Vec 2, Homogenization.vecNormSq (F (t, x))
        ∂(volume.restrict AVenhance.unitCube)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := integral_prod _ hIntProd
    _ = ∫ t, AVenhance.gradNormSq (fun x => F (t, x))
        ∂GalerkinTimeMeasure := by rw [LimitArbitraryTest.galTime_eq_Ioo_measure]; rfl

theorem LimitArbitraryTest.arbitraryTest_driftCoordinate_memLp
    (P : FrozenDriftProblem) (i : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 => P.b p.1 p.2 i) ⊤
      (volume.restrict AVenhance.timeCube) := by
  obtain ⟨B, hB⟩ := P.drift_bounded
  have hsubset : AVenhance.timeCube ⊆ Icc (0 : ℝ) 1 ×ˢ Set.univ := by
    intro p hp
    rcases hp with ⟨ht, hx⟩
    exact ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, Set.mem_univ _⟩
  have hbMeas := P.drift_measurable.mono_set hsubset
  have hcoordMeas : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => P.b p.1 p.2 i)
      (volume.restrict AVenhance.timeCube) := by
    exact (continuous_apply i).comp_aestronglyMeasurable hbMeas
  apply MemLp.of_bound hcoordMeas B
  filter_upwards [ae_restrict_mem (by
    rw [AVenhance.timeCube]
    exact measurableSet_Ioo.prod (by
      unfold AVenhance.unitCube
      exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
  rcases hp with ⟨ht, hx⟩
  have hb := hB p.1 ⟨le_of_lt ht.1, le_of_lt ht.2⟩ p.2
  have hcoord := (pi_norm_le_iff_of_nonempty (P.b p.1 p.2)).1 hb i
  simpa [Real.norm_eq_abs] using hcoord

theorem LimitArbitraryTest.arbitraryTest_driftGradient_memLp_two
    (P : FrozenDriftProblem) (G : GradientProductTimeL2) :
    MemLp (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative G p.1 p.2)) 2
      (volume.restrict AVenhance.timeCube) := by
  have hprod (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 =>
      P.b p.1 p.2 i * synchronizedGradientRepresentative G p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube) :=
    (LimitArbitraryTest.arbitraryTest_driftCoordinate_memLp P i).mul
      (synchronizedGradientRepresentative_memLp_timeCube G i)
  have hsum : MemLp
      ((fun p : ℝ × Vec 2 =>
        P.b p.1 p.2 0 * synchronizedGradientRepresentative G p.1 p.2 0) +
       (fun p =>
        P.b p.1 p.2 1 * synchronizedGradientRepresentative G p.1 p.2 1)) 2
      (volume.restrict AVenhance.timeCube) := (hprod 0).add (hprod 1)
  have heq : ((fun p : ℝ × Vec 2 =>
      P.b p.1 p.2 0 * synchronizedGradientRepresentative G p.1 p.2 0) +
      (fun p =>
      P.b p.1 p.2 1 * synchronizedGradientRepresentative G p.1 p.2 1)) =ᵐ[
          volume.restrict AVenhance.timeCube]
      fun p => Homogenization.vecDot (P.b p.1 p.2)
        (synchronizedGradientRepresentative G p.1 p.2) := by
    filter_upwards with p
    simp [Homogenization.vecDot, Fin.sum_univ_succ]
  exact (memLp_congr_ae heq).1 hsum

theorem LimitArbitraryTest.arbitraryTest_timeCutoffError_l2Sq_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (spacetimeTestTimeDerivative φ p.1 p.2 -
        AVenhance.Infra.Section5.testFourierCutoff
          (spacetimeTestTimeDerivative φ p.1) N p.2) ^ 2)
      atTop (𝓝 0) := by
  let hdt := spacetimeTestTimeDerivative_contDiff hφ
  have hdtperiodic : ∀ t, AVenhance.IsZ2Periodic (spacetimeTestTimeDerivative φ t) :=
    spacetimeTestTimeDerivative_periodic hperiodic
  have herr (N : ℕ) : Continuous (fun p : ℝ × Vec 2 =>
      spacetimeTestTimeDerivative φ p.1 p.2 -
        AVenhance.Infra.Section5.testFourierCutoff
          (spacetimeTestTimeDerivative φ p.1) N p.2) := by
    have hcut := spacetimeTestFourierCutoff_contDiff_top hdt hdtperiodic N
    exact hdt.continuous.sub hcut.continuous
  have henergy := spacetimeTestTimeDerivativeCutoff_error_integral_tendsto hφ hperiodic
  have heq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (spacetimeTestTimeDerivative φ p.1 p.2 -
          AVenhance.Infra.Section5.testFourierCutoff
            (spacetimeTestTimeDerivative φ p.1) N p.2) ^ 2) =
      ∫ t, AVenhance.l2NormSq (fun x =>
        spacetimeTestTimeDerivative φ t x -
          AVenhance.Infra.Section5.testFourierCutoff
            (spacetimeTestTimeDerivative φ t) N x) ∂GalerkinTimeMeasure := by
    simpa [AVenhance.l2NormSq] using
      LimitArbitraryTest.timeCube_square_integral_eq_time_l2 (herr N)
  simpa only [heq] using henergy

theorem LimitArbitraryTest.arbitraryTest_valueCutoffError_l2Sq_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (φ p.1 p.2 -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) ^ 2)
      atTop (𝓝 0) := by
  have herr (N : ℕ) : Continuous (fun p : ℝ × Vec 2 =>
      φ p.1 p.2 - AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) := by
    have hcut := spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N
    exact hφ.continuous.sub hcut.continuous
  have henergy := spacetimeTestValueCutoff_error_integral_tendsto hφ hperiodic
  have heq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (φ p.1 p.2 -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) ^ 2) =
      ∫ t, AVenhance.l2NormSq (fun x =>
        φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x)
          ∂GalerkinTimeMeasure := by
    simpa [AVenhance.l2NormSq] using LimitArbitraryTest.timeCube_square_integral_eq_time_l2 (herr N)
  simpa only [heq] using henergy

theorem LimitArbitraryTest.arbitraryTest_gradientCutoffCoordError_l2Sq_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (i : Fin 2) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2)
      atTop (𝓝 0) := by
  have hφone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    hφ.of_le (by norm_num)
  have hcutone (N : ℕ) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 =>
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) :=
    (spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N).of_le (by norm_num)
  have herrOne (N : ℕ) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => φ p.1 p.2 -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) :=
    hφone.sub (hcutone N)
  let η (N : ℕ) : ℝ → Vec 2 → ℝ := fun t x =>
    φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x
  have hηone (N : ℕ) : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => η N p.1 p.2) := by
    simpa [η] using herrOne N
  have hgradCont (N : ℕ) : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2) := by
    simpa [η] using LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous (φ := η N)
        (hηone N)
  have hcoordEnergy (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2) ≤
      ∫ p in AVenhance.timeCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2) := by
    have hcoordInt : Integrable (fun p : ℝ × Vec 2 =>
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2)
        (volume.restrict AVenhance.timeCube) := by
      have hcont : Continuous (fun p : ℝ × Vec 2 =>
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2) :=
        (((continuous_apply i).comp (hgradCont N)).pow 2)
      exact (hcont.continuousOn.integrableOn_compact
          LimitArbitraryTest.arbitraryTestClosedCell_compact).mono_set
        LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
    have hvecInt : Integrable (fun p : ℝ × Vec 2 =>
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2))
        (volume.restrict AVenhance.timeCube) := by
      have hsq : Continuous (fun p : ℝ × Vec 2 =>
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (fun x => φ p.1 x -
              AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2)) := by
        unfold Homogenization.vecNormSq Homogenization.vecDot
        exact continuous_finsetSum Finset.univ (fun j hj =>
          ((continuous_apply j).comp (hgradCont N)).mul
            ((continuous_apply j).comp (hgradCont N)))
      exact (hsq.continuousOn.integrableOn_compact
          LimitArbitraryTest.arbitraryTestClosedCell_compact).mono_set
        LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
    apply setIntegral_mono_on hcoordInt hvecInt LimitArbitraryTest.arbitraryTest_timeCube_measurable
    intro p hp
    simp only [Homogenization.vecNormSq, Homogenization.vecDot]
    simpa [pow_two] using (Finset.single_le_sum (s := Finset.univ)
      (fun j hj => sq_nonneg
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 j))
      (Finset.mem_univ i))
  have hvector := spacetimeTestGradientCutoff_error_integral_tendsto hφ hperiodic
  have hvectorEq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2)) =
      ∫ t, AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
        φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
          ∂GalerkinTimeMeasure := by
    simpa [AVenhance.gradNormSq] using LimitArbitraryTest.arbitraryTest_timeCube_vectorEnergy_eq
      (hgradCont N)
  have hbound : ∀ᶠ N in atTop,
      ∫ p in AVenhance.timeCube,
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2 ≤
        ∫ t, AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
          φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
            ∂GalerkinTimeMeasure := by
    filter_upwards with N
    exact (hcoordEnergy N).trans_eq (hvectorEq N)
  have hnonneg : ∀ N, 0 ≤ ∫ p in AVenhance.timeCube,
      (AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2 := by
    intro N
    exact setIntegral_nonneg LimitArbitraryTest.arbitraryTest_timeCube_measurable
      (fun p hp => sq_nonneg _)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound (by simpa [hvectorEq] using hvector)

theorem LimitArbitraryTest.arbitraryTest_pairing_error_tendsto_zero
    {g : ℝ × Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict AVenhance.timeCube))
    (e : ℕ → ℝ × Vec 2 → ℝ)
    (he : ∀ N, Continuous (e N))
    (henergy : Tendsto (fun N => ∫ p in AVenhance.timeCube, e N p ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube, g p * e N p) atTop (𝓝 0) := by
  have hroot := (Real.continuous_sqrt.tendsto 0).comp henergy
  have hupper : Tendsto (fun N =>
      Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) *
        Real.sqrt (∫ p in AVenhance.timeCube, e N p ^ 2)) atTop (𝓝 0) := by
    simpa using hroot.const_mul (Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2))
  have habs : Tendsto (fun N =>
      |∫ p in AVenhance.timeCube, g p * e N p|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) _ hupper
    filter_upwards with N
    exact LimitArbitraryTest.arbitraryTest_l2_pairing_bound hg
      (LimitArbitraryTest.arbitraryTest_continuous_memLp_two (he N))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

theorem LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    [IsFiniteMeasure μ]
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x * g x) μ := by
  exact ((hf.mul hg : MemLp (fun x => f x * g x) 1 μ).integrable le_rfl)

theorem LimitArbitraryTest.arbitraryTest_spaceGrad_sub
    {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    AVenhance.spaceGrad (fun x => f x - g x) =
      fun x => AVenhance.spaceGrad f x - AVenhance.spaceGrad g x := by
  funext x i
  simp only [AVenhance.spaceGrad]
  rw [fderiv_fun_sub
    ((hf.differentiable (by norm_num)).differentiableAt)
    ((hg.differentiable (by norm_num)).differentiableAt)]
  simp [AVenhance.spaceGrad]

theorem LimitArbitraryTest.arbitraryTest_initialCutoff_pairing_tendsto
    (P : FrozenDriftProblem) {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto (fun N =>
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j))
      atTop (𝓝 (∫ x in AVenhance.unitCube, P.θ₀ x * φ 0 x)) := by
  have hcutoff := AVenhance.Infra.Section5.testFourierCutoff_pairing_tendsto
    P.initial_memL2 ((hφ.comp (contDiff_prodMk_right 0)).of_le (by norm_num))
  have hcutoff' : Tendsto (fun N =>
      ∫ x in AVenhance.unitCube, P.θ₀ x *
        AVenhance.Infra.Section5.testFourierCutoff (φ 0) N x)
      atTop (𝓝 (∫ x in AVenhance.unitCube, P.θ₀ x * φ 0 x)) := by
    simpa [Function.comp_def] using hcutoff
  have hsum_eq (N : ℕ) :
      (∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j)) =
      inner ℝ P.initialTorusL2
        (smoothPeriodicTestL2
          ((AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top)
          (AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N)) := by
    calc
      (∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j)) =
        ∑ j : Fin (RealFourierDimension N),
          inner ℝ P.initialTorusL2
            (spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) := by
              simp [inner_smul_right]
      _ = inner ℝ P.initialTorusL2
          (∑ j : Fin (RealFourierDimension N),
            spacetimeRealFourierCoefficient φ N j 0 • realFourierModeL2 N j) := by
              rw [← inner_sum]
      _ = inner ℝ P.initialTorusL2
          (smoothPeriodicTestL2
            ((AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top)
            (AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N)) := by
              rw [LimitArbitraryTest.spacetimeCutoff_initialClass_eq_mode_sum hφ hperiodic N]
  have hcell (N : ℕ) :
      inner ℝ P.initialTorusL2
        (smoothPeriodicTestL2
          ((AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top)
          (AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N)) =
      ∫ x in AVenhance.unitCube, P.θ₀ x *
        AVenhance.Infra.Section5.testFourierCutoff (φ 0) N x := by
    exact P.initial_pairing_eq_cell_integral
      ((AVenhance.Infra.Section5.testFourierCutoff_analytic (φ 0) N).of_le le_top)
      (AVenhance.Infra.Section5.testFourierCutoff_periodic (φ 0) N)
  simpa only [hsum_eq, hcell] using hcutoff'

theorem LimitArbitraryTest.arbitraryTest_vectorDot_pairing_integrable
    {μ : Measure (ℝ × Vec 2)} [IsFiniteMeasure μ]
    (D V : ℝ × Vec 2 → Vec 2)
    (hD : ∀ i : Fin 2, MemLp (fun p => D p i) 2 μ)
    (hV : ∀ i : Fin 2, MemLp (fun p => V p i) 2 μ) :
    Integrable (fun p => Homogenization.vecDot (D p) (V p)) μ := by
  have hterm (i : Fin 2) : Integrable (fun p => D p i * V p i) μ :=
    LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two (hD i) (hV i)
  have hsum : Integrable (fun p : ℝ × Vec 2 =>
      ∑ i : Fin 2, D p i * V p i) μ :=
    integrable_finsetSum Finset.univ (fun i hi => hterm i)
  have heq : (fun p : ℝ × Vec 2 => ∑ i : Fin 2, D p i * V p i) =
      fun p => Homogenization.vecDot (D p) (V p) := by
    funext p
    simp [Homogenization.vecDot]
  exact heq ▸ hsum

private theorem synchronized_limit_arbitrary_test_cell_identity_RemIntegral1 :
  ∀ (P : FrozenDriftProblem) (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) (Uprod :
    ↥ScalarProductTimeL2) (Gprod : ↥GradientProductTimeL2) (S : Set ℝ) {φ : ℝ → Vec (2 : ℕ) →
    ℝ},
  let θ : ℝ → Vec (2 : ℕ) → ℝ := synchronizedScalarRepresentative Uprod u S;
  let D : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedGradientRepresentative Gprod p.1 p.2;
  let fD : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => Homogenization.vecDot (P.b p.1
    p.2) (D p);
  let dφ : ℝ → Vec (2 : ℕ) → ℝ := spacetimeTestTimeDerivative φ;
  let cutValue : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (φ
    t) N;
  let cutTime : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (dφ
    t) N;
  let errTime : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => dφ p.1 p.2 -
    cutTime N p.1 p.2;
  let errValue : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2 -
    cutValue N p.1 p.2;
  let errGrad : ℕ → ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) =>
    spaceGrad (fun (x : Vec (2 : ℕ)) => φ p.1 x - cutValue N p.1 x) p.2;
  let remainderF : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 *
    errTime N p + fD p * errValue N p + P.κ * Homogenization.vecDot (D p) (errGrad N p);
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  MemLp (fun (p : ℝ × Vec (2 : ℕ)) => θ p.1 p.2) (2 : ℝ≥0∞) μ → (∀ (i : Fin (2 : ℕ)), MemLp (fun
    (p : ℝ × Vec (2 : ℕ)) => D p i) (2 : ℝ≥0∞) μ) → MemLp fD (2 : ℝ≥0∞) μ → (∀ (N : ℕ),
    Continuous (errTime N)) → (∀ (N : ℕ), Continuous (errValue N)) → (∀ (N : ℕ), Continuous
    (errGrad N)) → (∀ (N : ℕ) (i : Fin (2 : ℕ)), Integrable (fun (p : ℝ × Vec (2 : ℕ)) => D p i
    * errGrad N p i) μ) → ∀ (N : ℕ), ∫ (p : ℝ × Vec (2 : ℕ)) in timeCube, remainderF N p = ((-∫
    (p : ℝ × Vec (2 : ℕ)) in timeCube, θ p.1 p.2 * errTime N p) + ∫ (p : ℝ × Vec (2 : ℕ)) in
    timeCube, fD p * errValue N p) + P.κ * ∑ i : Fin (2 : ℕ), ∫ (p : ℝ × Vec (2 : ℕ)) in
    timeCube, D p i * errGrad N p i
    := by
  intro P u Uprod Gprod S φ θ D fD dφ cutValue cutTime errTime errValue errGrad remainderF μ hθ hD
      hfD herrTimeCont herrValueCont herrGradCont hgradPairingInt N
  have hTInt := LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hθ
    (LimitArbitraryTest.arbitraryTest_continuous_memLp_two (herrTimeCont N))
  have hBInt := LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hfD
    (LimitArbitraryTest.arbitraryTest_continuous_memLp_two (herrValueCont N))
  have hdot := LimitArbitraryTest.arbitraryTest_vectorDot_pairing_integrable D (errGrad N) hD
    (fun i => LimitArbitraryTest.arbitraryTest_continuous_memLp_two
      ((continuous_apply i).comp (herrGradCont N)))
  have hdotSum : (fun p : ℝ × Vec 2 => Homogenization.vecDot (D p) (errGrad N p)) =
      fun p => ∑ i : Fin 2, D p i * errGrad N p i := by
    funext p
    simp [Homogenization.vecDot]
  have hTneg : Integrable (fun p : ℝ × Vec 2 =>
      -(θ p.1 p.2 * errTime N p)) μ := by
    simpa using hTInt.neg
  have hdotScaled : Integrable (fun p : ℝ × Vec 2 =>
      P.κ * Homogenization.vecDot (D p) (errGrad N p)) μ := by
    simpa [mul_comm] using hdot.const_mul P.κ
  have hsumTermInt : Integrable
      ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
        (fun p => fD p * errValue N p)) μ := hTneg.add hBInt
  have hIntegralAddOuter :
      (∫ p in AVenhance.timeCube,
        (((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
          (fun p => fD p * errValue N p)) +
          (fun p => P.κ * Homogenization.vecDot (D p) (errGrad N p))) p) =
        (∫ p in AVenhance.timeCube,
          ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
            (fun p => fD p * errValue N p)) p) +
          (∫ p in AVenhance.timeCube,
            P.κ * Homogenization.vecDot (D p) (errGrad N p)) := by
    exact integral_add hsumTermInt hdotScaled
  have hIntegralAddInner :
      (∫ p in AVenhance.timeCube,
        ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
          (fun p => fD p * errValue N p)) p) =
        (∫ p in AVenhance.timeCube, -(θ p.1 p.2 * errTime N p)) +
        (∫ p in AVenhance.timeCube, fD p * errValue N p) := by
    exact integral_add hTneg hBInt
  have hDotSumIntegral :
      (∫ p in AVenhance.timeCube, Homogenization.vecDot (D p) (errGrad N p)) =
        ∑ i : Fin 2, ∫ p in AVenhance.timeCube, D p i * errGrad N p i := by
    rw [hdotSum]
    exact integral_finsetSum Finset.univ (fun i hi => hgradPairingInt N i)
  calc
    (∫ p in AVenhance.timeCube, remainderF N p) =
        ∫ p in AVenhance.timeCube,
          (((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
            (fun p => fD p * errValue N p)) +
            (fun p => P.κ * Homogenization.vecDot (D p) (errGrad N p))) p := by
              apply integral_congr_ae
              filter_upwards with p
              simp [remainderF]
    _ = (∫ p in AVenhance.timeCube,
          ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
            (fun p => fD p * errValue N p)) p) +
          (∫ p in AVenhance.timeCube,
            P.κ * Homogenization.vecDot (D p) (errGrad N p)) :=
              hIntegralAddOuter
    _ = ((∫ p in AVenhance.timeCube,
            -(θ p.1 p.2 * errTime N p)) +
          (∫ p in AVenhance.timeCube, fD p * errValue N p)) +
          P.κ * (∫ p in AVenhance.timeCube,
            Homogenization.vecDot (D p) (errGrad N p)) := by
              rw [hIntegralAddInner, integral_neg, integral_const_mul]
    _ = ((-∫ p in AVenhance.timeCube, θ p.1 p.2 * errTime N p) +
          (∫ p in AVenhance.timeCube, fD p * errValue N p)) +
          P.κ * ∑ i : Fin 2,
            ∫ p in AVenhance.timeCube, D p i * errGrad N p i := by
              rw [integral_neg, hDotSumIntegral]

private theorem synchronized_limit_arbitrary_test_cell_identity_RemInt2 :
  ∀ (P : FrozenDriftProblem) (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) (Uprod :
    ↥ScalarProductTimeL2) (Gprod : ↥GradientProductTimeL2) (S : Set ℝ) {φ : ℝ → Vec (2 : ℕ) →
    ℝ},
  let θ : ℝ → Vec (2 : ℕ) → ℝ := synchronizedScalarRepresentative Uprod u S;
  let D : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedGradientRepresentative Gprod p.1 p.2;
  let fD : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => Homogenization.vecDot (P.b p.1
    p.2) (D p);
  let dφ : ℝ → Vec (2 : ℕ) → ℝ := spacetimeTestTimeDerivative φ;
  let cutValue : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (φ
    t) N;
  let cutTime : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (dφ
    t) N;
  let errTime : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => dφ p.1 p.2 -
    cutTime N p.1 p.2;
  let errValue : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2 -
    cutValue N p.1 p.2;
  let errGrad : ℕ → ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) =>
    spaceGrad (fun (x : Vec (2 : ℕ)) => φ p.1 x - cutValue N p.1 x) p.2;
  let remainderF : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 *
    errTime N p + fD p * errValue N p + P.κ * Homogenization.vecDot (D p) (errGrad N p);
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  MemLp (fun (p : ℝ × Vec (2 : ℕ)) => θ p.1 p.2) (2 : ℝ≥0∞) μ → MemLp fD (2 : ℝ≥0∞) μ → (∀ (N :
    ℕ), Continuous (errTime N)) → (∀ (N : ℕ), Continuous (errValue N)) → (∀ (N : ℕ), Continuous
    (errGrad N)) → (∀ (V : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)), (∀ (i : Fin (2 : ℕ)), MemLp (fun (p :
    ℝ × Vec (2 : ℕ)) => V p i) (2 : ℝ≥0∞) μ) → Integrable (fun (p : ℝ × Vec (2 : ℕ)) => P.κ *
    Homogenization.vecDot (D p) (V p)) μ) → ∀ (N : ℕ), Integrable (remainderF N) μ
    := by
  intro P u Uprod Gprod S φ θ D fD dφ cutValue cutTime errTime errValue errGrad remainderF μ hθ
      hfD herrTimeCont herrValueCont herrGradCont hdotInt N
  have hT := (LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hθ
    (LimitArbitraryTest.arbitraryTest_continuous_memLp_two (herrTimeCont N))).neg
  have hB := LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hfD
    (LimitArbitraryTest.arbitraryTest_continuous_memLp_two (herrValueCont N))
  have hC := hdotInt (errGrad N) (fun i =>
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two ((continuous_apply i).comp
        (herrGradCont N)))
  have hsum := hT.add hB |>.add hC
  have heq : ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * errTime N p)) +
      (fun p => fD p * errValue N p) +
      (fun p => P.κ * Homogenization.vecDot (D p) (errGrad N p))) = remainderF N := by
    funext p
    simp [remainderF]
  exact heq ▸ hsum

private theorem synchronized_limit_arbitrary_test_cell_identity_CutInt3 :
  ∀ (P : FrozenDriftProblem) (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) (Uprod :
    ↥ScalarProductTimeL2) (Gprod : ↥GradientProductTimeL2) (S : Set ℝ) {φ : ℝ → Vec (2 : ℕ) →
    ℝ},
  let θ : ℝ → Vec (2 : ℕ) → ℝ := synchronizedScalarRepresentative Uprod u S;
  let D : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedGradientRepresentative Gprod p.1 p.2;
  let fD : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => Homogenization.vecDot (P.b p.1
    p.2) (D p);
  let cutValue : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (φ
    t) N;
  let cutoffF : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 *
    deriv (fun (s : ℝ) => cutValue N s p.2) p.1 + fD p * cutValue N p.1 p.2 + P.κ *
    Homogenization.vecDot (D p) (spaceGrad (cutValue N p.1) p.2);
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  MemLp (fun (p : ℝ × Vec (2 : ℕ)) => θ p.1 p.2) (2 : ℝ≥0∞) μ → MemLp fD (2 : ℝ≥0∞) μ → (∀ (V :
    ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)), (∀ (i : Fin (2 : ℕ)), MemLp (fun (p : ℝ × Vec (2 : ℕ)) => V
    p i) (2 : ℝ≥0∞) μ) → Integrable (fun (p : ℝ × Vec (2 : ℕ)) => P.κ * Homogenization.vecDot (D
    p) (V p)) μ) → (∀ (N : ℕ), MemLp (fun (p : ℝ × Vec (2 : ℕ)) => deriv (fun (s : ℝ) =>
    cutValue N s p.2) p.1) (2 : ℝ≥0∞) μ) → (∀ (N : ℕ), MemLp (fun (p : ℝ × Vec (2 : ℕ)) =>
    cutValue N p.1 p.2) (2 : ℝ≥0∞) μ) → (∀ (N : ℕ) (i : Fin (2 : ℕ)), MemLp (fun (p : ℝ × Vec (2
    : ℕ)) => spaceGrad (cutValue N p.1) p.2 i) (2 : ℝ≥0∞) μ) → ∀ (N : ℕ), Integrable (cutoffF N)
    μ
    := by
  intro P u Uprod Gprod S φ θ D fD cutValue cutoffF μ hθ hfD hdotInt hcutDtMem hcutValueMem
      hcutGradMem N
  have hT := (LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hθ (hcutDtMem
      N)).neg
  have hB := LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hfD (hcutValueMem N)
  have hC := hdotInt (fun p => AVenhance.spaceGrad (cutValue N p.1) p.2)
    (hcutGradMem N)
  have hsum := hT.add hB |>.add hC
  have heq : ((fun p : ℝ × Vec 2 =>
      -(θ p.1 p.2 * deriv (fun s => cutValue N s p.2) p.1)) +
      (fun p => fD p * cutValue N p.1 p.2) +
      (fun p => P.κ * Homogenization.vecDot (D p)
        (AVenhance.spaceGrad (cutValue N p.1) p.2))) = cutoffF N := by
    funext p
    simp [cutoffF]
  exact heq ▸ hsum

private theorem synchronized_limit_arbitrary_test_cell_identity_gradSub1 :
  ∀ {φ : ℝ → Vec (2 : ℕ) → ℝ}, (ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) fun (p : ℝ × Vec (2 : ℕ)) =>
    φ p.1 p.2) → (∀ (t : ℝ), IsZ2Periodic (φ t)) →
  let cutValue : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (φ
    t) N;
  let errGrad : ℕ → ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) =>
    spaceGrad (fun (x : Vec (2 : ℕ)) => φ p.1 x - cutValue N p.1 x) p.2;
  ∀ (N : ℕ) (p : ℝ × Vec (2 : ℕ)), errGrad N p = spaceGrad (φ p.1) p.2 - spaceGrad (cutValue N
    p.1) p.2
    := by
  intro φ hφ hperiodic cutValue errGrad N p
  have hφslice : ContDiff ℝ 1 (φ p.1) :=
    (hφ.comp (contDiff_prodMk_right p.1)).of_le (by norm_num)
  have hcutslice : ContDiff ℝ 1 (cutValue N p.1) := by
    have hcut : ContDiff ℝ 1
        (fun q : ℝ × Vec 2 => cutValue N q.1 q.2) := by
      simpa [cutValue] using
        (spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N).of_le
          (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by
            exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    simpa [Function.comp_def, cutValue] using hcut.comp (contDiff_prodMk_right p.1)
  have hh := LimitArbitraryTest.arbitraryTest_spaceGrad_sub hφslice hcutslice
  simpa [errGrad] using congrFun hh p.2

private theorem synchronized_limit_arbitrary_test_cell_identity_TargetInt2 :
  ∀ (P : FrozenDriftProblem) (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) (Uprod :
    ↥ScalarProductTimeL2) (Gprod : ↥GradientProductTimeL2) (S : Set ℝ) {φ : ℝ → Vec (2 : ℕ) →
    ℝ},
  let θ : ℝ → Vec (2 : ℕ) → ℝ := synchronizedScalarRepresentative Uprod u S;
  let D : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedGradientRepresentative Gprod p.1 p.2;
  let fD : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => Homogenization.vecDot (P.b p.1
    p.2) (D p);
  let dφ : ℝ → Vec (2 : ℕ) → ℝ := spacetimeTestTimeDerivative φ;
  let targetF : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 * dφ p.1 p.2 + fD
    p * φ p.1 p.2 + P.κ * Homogenization.vecDot (D p) (spaceGrad (φ p.1) p.2);
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  MemLp (fun (p : ℝ × Vec (2 : ℕ)) => θ p.1 p.2) (2 : ℝ≥0∞) μ → MemLp fD (2 : ℝ≥0∞) μ → MemLp
    (fun (p : ℝ × Vec (2 : ℕ)) => dφ p.1 p.2) (2 : ℝ≥0∞) μ → MemLp (fun (p : ℝ × Vec (2 : ℕ)) =>
    φ p.1 p.2) (2 : ℝ≥0∞) μ → (∀ (i : Fin (2 : ℕ)), MemLp (fun (p : ℝ × Vec (2 : ℕ)) =>
    spaceGrad (φ p.1) p.2 i) (2 : ℝ≥0∞) μ) → (∀ (V : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)), (∀ (i : Fin
    (2 : ℕ)), MemLp (fun (p : ℝ × Vec (2 : ℕ)) => V p i) (2 : ℝ≥0∞) μ) → Integrable (fun (p : ℝ
    × Vec (2 : ℕ)) => P.κ * Homogenization.vecDot (D p) (V p)) μ) → Integrable targetF μ
    := by
  intro P u Uprod Gprod S φ θ D fD dφ targetF μ hθ hfD hdtMem hφMem hgradφMem hdotInt
  have hT := (LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hθ hdtMem).neg
  have hB := LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two hfD hφMem
  have hC := hdotInt (fun p => AVenhance.spaceGrad (φ p.1) p.2) hgradφMem
  have hsum := hT.add hB |>.add hC
  have heq : ((fun p : ℝ × Vec 2 => -(θ p.1 p.2 * dφ p.1 p.2)) +
      (fun p => fD p * φ p.1 p.2) +
      (fun p => P.κ * Homogenization.vecDot (D p)
        (AVenhance.spaceGrad (φ p.1) p.2))) = targetF := by
    funext p
    simp [targetF]
  exact heq ▸ hsum

private theorem synchronized_limit_arbitrary_test_cell_identity_conclusion3 :
  ∀ (P : FrozenDriftProblem) (σ : ℕ → ℕ), StrictMono σ → ∀ (u : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)
    → ↥ScalarTorusL2) (Uprod : ↥ScalarProductTimeL2) (Gprod : ↥GradientProductTimeL2), (∀ (v :
    ↥ScalarProductTimeL2), Tendsto (fun (n : ℕ) => ⟪P.scalarProductLp (σ n), v⟫) atTop (𝓝
    ⟪Uprod, v⟫)) → (∀ (v : ↥GradientProductTimeL2), Tendsto (fun (n : ℕ) => ⟪P.gradientProductLp
    (σ n), v⟫) atTop (𝓝 ⟪Gprod, v⟫)) → ∀ (S : Set ℝ), MeasurableSet S → (∀ᵐ (t : ℝ)
    ∂GalerkinTimeMeasure, t ∈ S) → (∀ t ∈ S, synchronizedScalarSliceGood Uprod u t) → ∀ {φ : ℝ →
    Vec (2 : ℕ) → ℝ}, (ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) fun (p : ℝ × Vec (2 : ℕ)) => φ p.1
    p.2) → (∀ (t : ℝ), IsZ2Periodic (φ t)) → (∀ (t : ℝ), (1 : ℝ) ≤ t → ∀ (x : Vec (2 : ℕ)), φ t
    x = (0 : ℝ)) →
  let θ : ℝ → Vec (2 : ℕ) → ℝ := synchronizedScalarRepresentative Uprod u S;
  let D : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (p : ℝ × Vec (2 : ℕ)) =>
    synchronizedGradientRepresentative Gprod p.1 p.2;
  let fD : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => Homogenization.vecDot (P.b p.1
    p.2) (D p);
  let dφ : ℝ → Vec (2 : ℕ) → ℝ := spacetimeTestTimeDerivative φ;
  let cutValue : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (φ
    t) N;
  let cutTime : ℕ → ℝ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (t : ℝ) => Section5.testFourierCutoff (dφ
    t) N;
  let errTime : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => dφ p.1 p.2 -
    cutTime N p.1 p.2;
  let errValue : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2 -
    cutValue N p.1 p.2;
  let errGrad : ℕ → ℝ × Vec (2 : ℕ) → Vec (2 : ℕ) := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) =>
    spaceGrad (fun (x : Vec (2 : ℕ)) => φ p.1 x - cutValue N p.1 x) p.2;
  let _ : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 * dφ p.1 p.2 + fD
    p * φ p.1 p.2 + P.κ * Homogenization.vecDot (D p) (spaceGrad (φ p.1) p.2);
  let _ : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 *
    deriv (fun (s : ℝ) => cutValue N s p.2) p.1 + fD p * cutValue N p.1 p.2 + P.κ *
    Homogenization.vecDot (D p) (spaceGrad (cutValue N p.1) p.2);
  let _ : ℕ → ℝ × Vec (2 : ℕ) → ℝ := fun (N : ℕ) (p : ℝ × Vec (2 : ℕ)) => -θ p.1 p.2 *
    errTime N p + fD p * errValue N p + P.κ * Homogenization.vecDot (D p) (errGrad N p);
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  MemLp (fun (p : ℝ × Vec (2 : ℕ)) => θ p.1 p.2) (2 : ℝ≥0∞) μ → (∀ (i : Fin (2 : ℕ)), MemLp (fun
    (p : ℝ × Vec (2 : ℕ)) => D p i) (2 : ℝ≥0∞) μ) → MemLp fD (2 : ℝ≥0∞) μ → (∀ (N : ℕ),
    Continuous fun (p : ℝ × Vec (2 : ℕ)) => cutValue N p.1 p.2) → (∀ (N : ℕ), Continuous
    (errTime N)) → (∀ (N : ℕ), Continuous (errValue N)) → (∀ (N : ℕ), Continuous (errGrad N)) →
    Tendsto (fun (N : ℕ) => ∫ (p : ℝ × Vec (2 : ℕ)) in timeCube, θ p.1 p.2 * errTime N p) atTop
    (𝓝 (0 : ℝ)) → Tendsto (fun (N : ℕ) => ∫ (p : ℝ × Vec (2 : ℕ)) in timeCube, fD p * errValue N
    p) atTop (𝓝 (0 : ℝ)) → (∀ (i : Fin (2 : ℕ)), Tendsto (fun (N : ℕ) => ∫ (p : ℝ × Vec (2 : ℕ))
    in timeCube, D p i * errGrad N p i) atTop (𝓝 (0 : ℝ))) → MemLp (fun (p : ℝ × Vec (2 : ℕ)) =>
    dφ p.1 p.2) (2 : ℝ≥0∞) μ → MemLp (fun (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2) (2 : ℝ≥0∞) μ → (∀
    (i : Fin (2 : ℕ)), MemLp (fun (p : ℝ × Vec (2 : ℕ)) => spaceGrad (φ p.1) p.2 i) (2 : ℝ≥0∞)
    μ) → (∀ (V : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)), (∀ (i : Fin (2 : ℕ)), MemLp (fun (p : ℝ × Vec
    (2 : ℕ)) => V p i) (2 : ℝ≥0∞) μ) → Integrable (fun (p : ℝ × Vec (2 : ℕ)) => P.κ *
    Homogenization.vecDot (D p) (V p)) μ) → (∀ (N : ℕ) (p : ℝ × Vec (2 : ℕ)), deriv (fun (s : ℝ)
    => cutValue N s p.2) p.1 = cutTime N p.1 p.2) → (∀ (N : ℕ), Continuous fun (p : ℝ × Vec (2 :
    ℕ)) => deriv (fun (s : ℝ) => cutValue N s p.2) p.1) → (∀ (N : ℕ), Continuous fun (p : ℝ ×
    Vec (2 : ℕ)) => spaceGrad (cutValue N p.1) p.2) → ∫ (p : ℝ × Vec (2 : ℕ)) in timeCube,
    -synchronizedScalarRepresentative Uprod u S p.1 p.2 * deriv (fun (s : ℝ) => φ s p.2) p.1 +
    Homogenization.vecDot (P.b p.1 p.2) (synchronizedGradientRepresentative Gprod p.1 p.2) * φ
    p.1 p.2 + P.κ * Homogenization.vecDot (synchronizedGradientRepresentative Gprod p.1 p.2)
    (spaceGrad (φ p.1) p.2) = ∫ (x : Vec (2 : ℕ)) in unitCube, P.θ₀ x * φ (0 : ℝ) x
    := by
  intro P σ hσ u Uprod Gprod hUweak hGweak S hSmeas hSae hS φ hφ hperiodic hterminal θ D fD dφ
      cutValue cutTime errTime errValue errGrad targetF cutoffF remainderF μ hθ hD hfD
      hcutValueCont herrTimeCont herrValueCont herrGradCont htimePair hvaluePair hgradPair hdtMem
      hφMem hgradφMem hdotInt hcutDerivEq hcutDerivCont hcutGradCont
  have hcutDtMem (N : ℕ) : MemLp
      (fun p : ℝ × Vec 2 => deriv (fun s => cutValue N s p.2) p.1) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two (hcutDerivCont N)
  have hcutValueMem (N : ℕ) : MemLp
      (fun p : ℝ × Vec 2 => cutValue N p.1 p.2) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two (hcutValueCont N)
  have hcutGradMem (N : ℕ) (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (cutValue N p.1) p.2 i) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two ((continuous_apply i).comp (hcutGradCont
        N))
  have hTargetInt : Integrable targetF μ := by
    exact @synchronized_limit_arbitrary_test_cell_identity_TargetInt2 P u Uprod Gprod S φ hθ hfD
        hdtMem hφMem hgradφMem hdotInt
  have hCutInt (N : ℕ) : Integrable (cutoffF N) μ := by
    exact @synchronized_limit_arbitrary_test_cell_identity_CutInt3 P u Uprod Gprod S φ hθ hfD
        hdotInt hcutDtMem hcutValueMem hcutGradMem N
  have hRemInt (N : ℕ) : Integrable (remainderF N) μ := by
    exact @synchronized_limit_arbitrary_test_cell_identity_RemInt2 P u Uprod Gprod S φ hθ hfD
        herrTimeCont herrValueCont herrGradCont hdotInt N
  have hgradSub (N : ℕ) (p : ℝ × Vec 2) :
      errGrad N p = AVenhance.spaceGrad (φ p.1) p.2 -
        AVenhance.spaceGrad (cutValue N p.1) p.2 := by
    exact @synchronized_limit_arbitrary_test_cell_identity_gradSub1 φ hφ hperiodic N p
  have hgradSplit (N : ℕ) (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (φ p.1) p.2 =
        AVenhance.spaceGrad (cutValue N p.1) p.2 + errGrad N p := by
    rw [hgradSub N p]
    ext i
    simp
  have hdecompPoint (N : ℕ) (p : ℝ × Vec 2) :
      targetF p = cutoffF N p + remainderF N p := by
    have hdotSplit : Homogenization.vecDot (D p) (AVenhance.spaceGrad (φ p.1) p.2) =
        Homogenization.vecDot (D p) (AVenhance.spaceGrad (cutValue N p.1) p.2) +
          Homogenization.vecDot (D p) (errGrad N p) := by
      rw [hgradSplit N p]
      simp [Homogenization.vecDot]
      ring
    unfold targetF cutoffF remainderF
    rw [hcutDerivEq N p, hdotSplit]
    simp [errTime, errValue, dφ]
    ring
  have hdecomp (N : ℕ) :
      (∫ p in AVenhance.timeCube, targetF p) =
        (∫ p in AVenhance.timeCube, cutoffF N p) +
          (∫ p in AVenhance.timeCube, remainderF N p) := by
    calc
      (∫ p in AVenhance.timeCube, targetF p) =
          ∫ p in AVenhance.timeCube, cutoffF N p + remainderF N p := by
            apply integral_congr_ae
            filter_upwards with p
            exact hdecompPoint N p
      _ = (∫ p in AVenhance.timeCube, cutoffF N p) +
            (∫ p in AVenhance.timeCube, remainderF N p) :=
          integral_add (hCutInt N) (hRemInt N)
  have hgradPairingInt (N : ℕ) (i : Fin 2) :
      Integrable (fun p : ℝ × Vec 2 => D p i * errGrad N p i) μ :=
    LimitArbitraryTest.arbitraryTest_product_integrable_of_memLp_two (hD i)
      (LimitArbitraryTest.arbitraryTest_continuous_memLp_two ((continuous_apply i).comp
          (herrGradCont N)))
  have hRemIntegral (N : ℕ) :
      (∫ p in AVenhance.timeCube, remainderF N p) =
        -(∫ p in AVenhance.timeCube, θ p.1 p.2 * errTime N p) +
          (∫ p in AVenhance.timeCube, fD p * errValue N p) +
          P.κ * ∑ i : Fin 2,
            ∫ p in AVenhance.timeCube, D p i * errGrad N p i := by
    exact @synchronized_limit_arbitrary_test_cell_identity_RemIntegral1 P u Uprod Gprod S φ hθ hD
        hfD herrTimeCont herrValueCont herrGradCont hgradPairingInt N
  have htimePair' : Tendsto
      (fun N => ∫ p in AVenhance.timeCube, θ p.1 p.2 * errTime N p)
      atTop (𝓝 0) := by
    simpa [θ, errTime, dφ, μ] using htimePair
  have hvaluePair' : Tendsto
      (fun N => ∫ p in AVenhance.timeCube, fD p * errValue N p)
      atTop (𝓝 0) := by
    simpa [errValue, μ] using hvaluePair
  have hgradPair' (i : Fin 2) : Tendsto
      (fun N => ∫ p in AVenhance.timeCube, D p i * errGrad N p i)
      atTop (𝓝 0) := by
    simpa [D, errGrad, μ] using hgradPair i
  have hgradSumPair : Tendsto
      (fun N => ∑ i : Fin 2,
        ∫ p in AVenhance.timeCube, D p i * errGrad N p i) atTop (𝓝 0) := by
    have hsum := (hgradPair' 0).add (hgradPair' 1)
    simpa [Fin.sum_univ_succ] using hsum
  have hremTendsto : Tendsto (fun N => ∫ p in AVenhance.timeCube,
      remainderF N p) atTop (𝓝 0) := by
    have hsum := htimePair'.neg.add hvaluePair'
    have hsum' := hsum.add (hgradSumPair.const_mul P.κ)
    simpa [hRemIntegral] using hsum'
  have hcutTendsto : Tendsto (fun N => ∫ p in AVenhance.timeCube,
      cutoffF N p) atTop (𝓝 (∫ p in AVenhance.timeCube, targetF p)) := by
    have heq (N : ℕ) :
        (∫ p in AVenhance.timeCube, cutoffF N p) =
          (∫ p in AVenhance.timeCube, targetF p) -
            (∫ p in AVenhance.timeCube, remainderF N p) := by
      linarith [hdecomp N]
    simpa [heq] using tendsto_const_nhds.sub hremTendsto
  have hfinite (N : ℕ) :
      (∫ p in AVenhance.timeCube, cutoffF N p) =
        ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j 0 *
            inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
    simpa [θ, D, cutValue, fD, cutoffF, dφ] using
      P.synchronized_limit_fourierCutoff_cell_identity σ hσ u Uprod Gprod
        hUweak hGweak S hSmeas hSae hS hφ hperiodic hterminal N
  have hinitial := LimitArbitraryTest.arbitraryTest_initialCutoff_pairing_tendsto P hφ hperiodic
  have hfiniteTransfer : Tendsto (fun N =>
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j)) atTop
      (𝓝 (∫ x in AVenhance.unitCube, P.θ₀ x * φ 0 x)) := hinitial
  have hcutRhsTendsto : Tendsto (fun N => ∫ p in AVenhance.timeCube, cutoffF N p)
      atTop (𝓝 (∫ x in AVenhance.unitCube, P.θ₀ x * φ 0 x)) := by
    have heq : (fun N => ∫ p in AVenhance.timeCube, cutoffF N p) =ᶠ[atTop]
        fun N => ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j 0 *
            inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
      filter_upwards with N
      exact hfinite N
    exact Filter.Tendsto.congr' heq.symm hfiniteTransfer
  exact tendsto_nhds_unique hcutTendsto hcutRhsTendsto

theorem FrozenDriftProblem.synchronized_limit_arbitrary_test_cell_identity
    (P : FrozenDriftProblem) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (S : Set ℝ) (hSmeas : MeasurableSet S)
    (hSae : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S)
    (hS : ∀ t ∈ S, synchronizedScalarSliceGood Uprod u t)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (hterminal : ∀ t, 1 ≤ t → ∀ x, φ t x = 0) :
    ∫ p in AVenhance.timeCube,
      (-(synchronizedScalarRepresentative Uprod u S p.1 p.2) *
          deriv (fun s => φ s p.2) p.1 +
        Homogenization.vecDot (P.b p.1 p.2)
          (synchronizedGradientRepresentative Gprod p.1 p.2) * φ p.1 p.2 +
        P.κ * Homogenization.vecDot
          (synchronizedGradientRepresentative Gprod p.1 p.2)
          (AVenhance.spaceGrad (φ p.1) p.2)) =
      ∫ x in AVenhance.unitCube, P.θ₀ x * φ 0 x := by
  classical
  let θ : ℝ → Vec 2 → ℝ := synchronizedScalarRepresentative Uprod u S
  let D : ℝ × Vec 2 → Vec 2 := fun p => synchronizedGradientRepresentative Gprod p.1 p.2
  let fD : ℝ × Vec 2 → ℝ := fun p => Homogenization.vecDot (P.b p.1 p.2) (D p)
  let dφ : ℝ → Vec 2 → ℝ := spacetimeTestTimeDerivative φ
  let cutValue (N : ℕ) : ℝ → Vec 2 → ℝ := fun t =>
    AVenhance.Infra.Section5.testFourierCutoff (φ t) N
  let cutTime (N : ℕ) : ℝ → Vec 2 → ℝ := fun t =>
    AVenhance.Infra.Section5.testFourierCutoff (dφ t) N
  let errTime (N : ℕ) : ℝ × Vec 2 → ℝ := fun p => dφ p.1 p.2 - cutTime N p.1 p.2
  let errValue (N : ℕ) : ℝ × Vec 2 → ℝ := fun p => φ p.1 p.2 - cutValue N p.1 p.2
  let errGrad (N : ℕ) : ℝ × Vec 2 → Vec 2 := fun p =>
    AVenhance.spaceGrad (fun x => φ p.1 x - cutValue N p.1 x) p.2
  let targetF : ℝ × Vec 2 → ℝ := fun p =>
    -(θ p.1 p.2) * dφ p.1 p.2 + fD p * φ p.1 p.2 +
      P.κ * Homogenization.vecDot (D p) (AVenhance.spaceGrad (φ p.1) p.2)
  let cutoffF (N : ℕ) : ℝ × Vec 2 → ℝ := fun p =>
    -(θ p.1 p.2) * deriv (fun s => cutValue N s p.2) p.1 +
      fD p * cutValue N p.1 p.2 +
      P.κ * Homogenization.vecDot (D p) (AVenhance.spaceGrad (cutValue N p.1) p.2)
  let remainderF (N : ℕ) : ℝ × Vec 2 → ℝ := fun p =>
    -(θ p.1 p.2) * errTime N p + fD p * errValue N p +
      P.κ * Homogenization.vecDot (D p) (errGrad N p)
  let μ : Measure (ℝ × Vec 2) := volume.restrict AVenhance.timeCube
  have hθ : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 μ := by
    simpa [θ, μ] using synchronizedScalarRepresentative_memLp_timeCube
      Uprod u S hSmeas hSae
  have hD (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 => D p i) 2 μ := by
    simpa [D, μ] using synchronizedGradientRepresentative_memLp_timeCube Gprod i
  have hfD : MemLp fD 2 μ := by
    simpa [fD, D, μ] using LimitArbitraryTest.arbitraryTest_driftGradient_memLp_two P Gprod
  have hdφ : Continuous (fun p : ℝ × Vec 2 => dφ p.1 p.2) :=
    (spacetimeTestTimeDerivative_contDiff hφ).continuous
  have hφcont : Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2) := hφ.continuous
  have hφone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    hφ.of_le (by norm_num)
  have hgradφ : Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2) :=
    LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous hφone
  have hdφperiodic : ∀ t, AVenhance.IsZ2Periodic (dφ t) :=
    spacetimeTestTimeDerivative_periodic hperiodic
  have hcutValueCont (N : ℕ) : Continuous (fun p : ℝ × Vec 2 => cutValue N p.1 p.2) := by
    have hc := spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N
    simpa [cutValue] using hc.continuous
  have hcutTimeCont (N : ℕ) : Continuous (fun p : ℝ × Vec 2 => cutTime N p.1 p.2) := by
    have hc := spacetimeTestFourierCutoff_contDiff_top
      (spacetimeTestTimeDerivative_contDiff hφ) hdφperiodic N
    simpa [cutTime, dφ] using hc.continuous
  have herrTimeCont (N : ℕ) : Continuous (errTime N) := by
    exact hdφ.sub (hcutTimeCont N)
  have herrValueCont (N : ℕ) : Continuous (errValue N) := by
    exact hφcont.sub (hcutValueCont N)
  have hηone (N : ℕ) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => φ p.1 p.2 - cutValue N p.1 p.2) := by
    have hc : ContDiff ℝ 1
        (fun p : ℝ × Vec 2 => cutValue N p.1 p.2) := by
      simpa [cutValue] using
        (spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N).of_le
          (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by
            exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    simpa [cutValue] using hφone.sub hc
  have herrGradCont (N : ℕ) : Continuous (errGrad N) := by
    let η : ℝ → Vec 2 → ℝ := fun t x => φ t x - cutValue N t x
    have hη : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => η p.1 p.2) := by
      simpa [η] using hηone N
    simpa [errGrad, η] using LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous (φ :=
        η) hη
  have hdtSq := LimitArbitraryTest.arbitraryTest_timeCutoffError_l2Sq_tendsto hφ hperiodic
  have hvalueSq := LimitArbitraryTest.arbitraryTest_valueCutoffError_l2Sq_tendsto hφ hperiodic
  have hgradSq (i : Fin 2) :=
    LimitArbitraryTest.arbitraryTest_gradientCutoffCoordError_l2Sq_tendsto hφ hperiodic i
  have htimePair := LimitArbitraryTest.arbitraryTest_pairing_error_tendsto_zero hθ errTime
      herrTimeCont hdtSq
  have hvaluePair := LimitArbitraryTest.arbitraryTest_pairing_error_tendsto_zero hfD errValue
      herrValueCont hvalueSq
  have hgradPair (i : Fin 2) := LimitArbitraryTest.arbitraryTest_pairing_error_tendsto_zero
    (hD i) (fun N p => errGrad N p i)
    (fun N => (continuous_apply i).comp (herrGradCont N)) (hgradSq i)
  have hdtMem : MemLp (fun p : ℝ × Vec 2 => dφ p.1 p.2) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two hdφ
  have hφMem : MemLp (fun p : ℝ × Vec 2 => φ p.1 p.2) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two hφcont
  have hgradφMem (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2 i) 2 μ :=
    LimitArbitraryTest.arbitraryTest_continuous_memLp_two ((continuous_apply i).comp hgradφ)
  have hdotInt (V : ℝ × Vec 2 → Vec 2)
      (hV : ∀ i : Fin 2, MemLp (fun p => V p i) 2 μ) :
      Integrable (fun p => P.κ * Homogenization.vecDot (D p) (V p)) μ := by
    have hbase := LimitArbitraryTest.arbitraryTest_vectorDot_pairing_integrable D V hD hV
    simpa [mul_comm] using hbase.const_mul P.κ
  have hcutDerivEq (N : ℕ) (p : ℝ × Vec 2) :
      deriv (fun s => cutValue N s p.2) p.1 = cutTime N p.1 p.2 := by
    simpa [cutValue, cutTime, dφ] using
      spacetimeTestFourierCutoff_timeDerivative_eq_spatialCutoff hφ hperiodic N p.1 p.2
  have hcutDerivCont (N : ℕ) : Continuous (fun p : ℝ × Vec 2 =>
      deriv (fun s => cutValue N s p.2) p.1) := by
    have heq : (fun p : ℝ × Vec 2 => deriv (fun s => cutValue N s p.2) p.1) =
        fun p => cutTime N p.1 p.2 := by
      funext p
      exact hcutDerivEq N p
    rw [heq]
    exact hcutTimeCont N
  have hcutGradCont (N : ℕ) : Continuous
      (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (cutValue N p.1) p.2) := by
    let ψ : ℝ → Vec 2 → ℝ := cutValue N
    have hψ : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => ψ p.1 p.2) := by
      simpa [ψ, cutValue] using
        (spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N).of_le (by norm_num)
    simpa [ψ] using LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous (φ := ψ) hψ
  exact @synchronized_limit_arbitrary_test_cell_identity_conclusion3 P σ hσ u Uprod Gprod hUweak
      hGweak S hSmeas hSae hS φ hφ hperiodic hterminal hθ hD hfD hcutValueCont herrTimeCont
      herrValueCont herrGradCont htimePair hvaluePair hgradPair hdtMem hφMem hgradφMem hdotInt
      hcutDerivEq hcutDerivCont hcutGradCont
end AVenhance.Infra.Parabolic.FourierGalerkin

end
