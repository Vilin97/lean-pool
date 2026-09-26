/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
public import LeanPool.CoarseGraining.Homogenization.Multiscale.Projection
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # Neumann Corrector -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Mean-zero Neumann correctors for the RHS weak-flux lane

This file packages the local correction used in Section 3.2.3.  The key
feature, absent from the zero-trace Dirichlet corrector, is that the Neumann
residual has zero normal trace; on a cube this forces the residual flux average
to vanish.
-/

private theorem isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS {d : ℕ}
    (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
  let U : Set (Vec d) := cubeSet Q
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)
  infer_instance

private theorem isBoundedDomain_cubeSet_weakFluxRHS {d : ℕ} (Q : TriadicCube d) :
    IsBoundedDomain (cubeSet Q) := by
  refine ⟨‖cubeCenter Q‖ + cubeRadius Q + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ ‖cubeCenter Q‖ + cubeRadius Q :=
      add_nonneg (norm_nonneg _) (cubeRadius_nonneg Q)
    linarith
  · intro x hx i
    have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
      cubeSet_subset_closedBall Q hx
    have hdist : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hxnorm : ‖x‖ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by
      calc
        ‖x‖ = ‖(x - cubeCenter Q) + cubeCenter Q‖ := by
          congr 1
          abel
        _ ≤ ‖x - cubeCenter Q‖ + ‖cubeCenter Q‖ := norm_add_le _ _
        _ ≤ cubeRadius Q + ‖cubeCenter Q‖ := add_le_add hdist le_rfl
        _ = ‖cubeCenter Q‖ + cubeRadius Q := by ring
        _ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by linarith
    exact (by simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hxnorm)

private theorem isSobolevRegularDomain_cubeSet_weakFluxRHS {d : ℕ}
    (Q : TriadicCube d) :
    IsSobolevRegularDomain (cubeSet Q) :=
  ⟨measurableSet_cubeSet Q, isBoundedDomain_cubeSet_weakFluxRHS Q⟩

/-- The half-open triadic cube inherits the mean-zero `H¹` coercive estimate
from the corresponding open cube, since the two realizations differ only by a
Lebesgue-null boundary. -/
noncomputable def h1CoerciveEstimate_cubeSet {d : ℕ} [NeZero d]
    (Q : TriadicCube d) :
    H1CoerciveEstimate (cubeSet Q) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hCopen : H1CoerciveEstimate (openCubeSet Q) :=
    h1CoerciveEstimate_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  refine
    { fixedValue := hCopen.fixedValue
      constant_nonneg := hCopen.constant_nonneg
      bound := ?_ }
  intro u
  let uOpen : H1MeanZeroFunction (openCubeSet Q) :=
    { toH1Function := u.toH1Function.toOpenCubeSet
      meanZero := by
        unfold MeanZeroOn
        have hset := setIntegral_cubeSet_eq_setIntegral_openCubeSet
          (Q := Q) (f := u.toH1Function.toFun)
        simpa using hset.symm.trans u.meanZero }
  have hvalue :
      u.valueL2Norm = uOpen.valueL2Norm := by
    dsimp only [H1MeanZeroFunction.valueL2Norm, H1MeanZeroFunction.toScalarL2,
      H1Function.toScalarL2, Homogenization.toScalarL2, uOpen]
    rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
    refine congrArg ENNReal.toReal ?_
    rw [volumeMeasureOn, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q,
      H1Function.toFun_toOpenCubeSet]
  have hgrad :
      u.gradientL2Norm = uOpen.gradientL2Norm := by
    dsimp only [H1MeanZeroFunction.gradientL2Norm, H1MeanZeroFunction.gradToVectorL2,
      H1Function.gradToVectorL2, Homogenization.toVectorL2, uOpen]
    rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
    refine congrArg ENNReal.toReal ?_
    rw [volumeMeasureOn, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q,
      H1Function.grad_toOpenCubeSet]
  calc
    u.valueL2Norm = uOpen.valueL2Norm := hvalue
    _ ≤ hCopen.fixedValue * uOpen.gradientL2Norm := hCopen.bound uOpen
    _ = hCopen.fixedValue * u.gradientL2Norm := by rw [hgrad]

private theorem cubeAverageVec_sub_of_memVectorL2 {d : ℕ} (Q : TriadicCube d)
    (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) :
    cubeAverageVec Q (fun x => u x - v x) =
      cubeAverageVec Q u - cubeAverageVec Q v := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  funext i
  have hui :
      MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hvi :
      MeasureTheory.MemLp (fun x => v x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  have hui_int :
      MeasureTheory.Integrable (fun x => u x i) (volumeMeasureOn (cubeSet Q)) :=
    hui.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hvi_int :
      MeasureTheory.Integrable (fun x => v x i) (volumeMeasureOn (cubeSet Q)) :=
    hvi.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  show cubeAverage Q (fun x => (u x - v x) i) =
    cubeAverage Q (fun x => u x i) - cubeAverage Q (fun x => v x i)
  have hfun : (fun x => (u x - v x) i) = fun x => u x i - v x i := by
    funext x
    simp
  unfold cubeAverage
  rw [hfun, MeasureTheory.integral_sub hui_int hvi_int]
  ring

private theorem cubeAverageVec_eq_of_eq_on_cubeSet_weakFluxRHS {d : ℕ}
    {Q : TriadicCube d} {f g : Vec d → Vec d}
    (hfg : ∀ x ∈ cubeSet Q, f x = g x) :
    cubeAverageVec Q f = cubeAverageVec Q g := by
  funext i
  unfold cubeAverageVec cubeAverage
  refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
  refine MeasureTheory.integral_congr_ae ?_
  exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
    Filter.Eventually.of_forall fun x hx => congrArg (fun v => v i) (hfg x hx)

theorem cubeAverageVec_centered_eq_zero {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) (hg : MemVectorL2 (cubeSet Q) g) :
    cubeAverageVec Q (fun x => g x - cubeAverageVec Q g) = 0 := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  have hconst_mem :
      MemVectorL2 (cubeSet Q) (fun _ : Vec d => cubeAverageVec Q g) :=
    memVectorL2_const (cubeAverageVec Q g)
  have hsub :=
    cubeAverageVec_sub_of_memVectorL2 Q g (fun _ : Vec d => cubeAverageVec Q g)
      hg hconst_mem
  have hconst_avg :
      cubeAverageVec Q (fun _ : Vec d => cubeAverageVec Q g) = cubeAverageVec Q g := by
    funext i
    simp [cubeAverageVec, cubeAverage_const]
  calc
    cubeAverageVec Q (fun x => g x - cubeAverageVec Q g)
        = cubeAverageVec Q g - cubeAverageVec Q (fun _ : Vec d => cubeAverageVec Q g) :=
          hsub
    _ = cubeAverageVec Q g - cubeAverageVec Q g := by rw [hconst_avg]
    _ = 0 := by simp

/-- A local mean-zero Neumann corrector on one cube for the weak equation
`- div(a grad omega) = div g`. -/
structure MeanZeroNeumannCorrectorData {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d) where
  toH1MeanZero : H1MeanZeroFunction (cubeSet Q)
  weakSolution :
    IsMeanZeroNeumannRhsWeakSolution a (cubeSet Q) toH1MeanZero g

/-- Package a local mean-zero Neumann corrector from a supplied coercive
estimate on the half-open cube.  A later cube-realization bridge can discharge
the coercive input from the open-cube Poincare estimate. -/
noncomputable def meanZeroNeumannCorrectorDataOf_h1CoerciveEstimate
    {d : ℕ} (Q : TriadicCube d) {a : CoeffField d} {g : Vec d → Vec d}
    {lam Lam : ℝ}
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hne : Set.Nonempty (cubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    MeanZeroNeumannCorrectorData Q a g := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  exact
    ⟨H1MeanZeroFunction.coeffGradientProblemSolution
        (U := cubeSet Q) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll,
      isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
        (U := cubeSet Q) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll⟩

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

/-- The Neumann-corrector residual has zero normal trace. -/
theorem residualFlux_zeroNormalTrace
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g) :
    IsSolenoidalZeroNormalTraceOn (cubeSet Q)
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) - g x) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  exact ω.weakSolution.residual_zeroNormalTrace hEll hg

/-- The averaged residual flux of a Neumann corrector vanishes on a cube. -/
theorem cubeAverageVec_residualFlux_eq_zero
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g) :
    cubeAverageVec Q
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) - g x) = 0 := by
  have hzero :
      (fun i =>
        ∫ x in cubeSet Q,
          (matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) - g x) i
            ∂MeasureTheory.volume) = 0 :=
    IsSolenoidalZeroNormalTraceOn.integral_eq_zero
      (isSobolevRegularDomain_cubeSet_weakFluxRHS Q)
      (ω.residualFlux_zeroNormalTrace hEll hg)
  funext i
  unfold cubeAverageVec cubeAverage
  rw [show
      ∫ x in cubeSet Q,
          (matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) - g x) i
            ∂MeasureTheory.volume = 0 by
        simpa using congrFun hzero i]
  simp

/-- If the Neumann RHS is centered, then the corrector flux itself has zero
cube average, the algebraic cancellation used in manuscript Section 3.2.3. -/
theorem cubeAverageVec_flux_eq_zero_of_cubeAverageVec_rhs_eq_zero
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g)
    (havg_g : cubeAverageVec Q g = 0) :
    cubeAverageVec Q
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) = 0 := by
  have hflux_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hsub :=
    cubeAverageVec_sub_of_memVectorL2 Q
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) g
      hflux_mem hg
  have hres := ω.cubeAverageVec_residualFlux_eq_zero hEll hg
  calc
    cubeAverageVec Q (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x))
        = cubeAverageVec Q (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) -
            cubeAverageVec Q g := by rw [havg_g, sub_zero]
    _ =
        cubeAverageVec Q
          (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) - g x) := by
          rw [hsub]
    _ = 0 := hres

/-- Centered-RHS form of the zero-average corrector-flux cancellation. -/
theorem cubeAverageVec_flux_eq_zero_of_centered_rhs
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a
      (fun x => g x - cubeAverageVec Q g))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g) :
    cubeAverageVec Q
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) = 0 := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  have hconst_mem :
      MemVectorL2 (cubeSet Q) (fun _ : Vec d => cubeAverageVec Q g) :=
    memVectorL2_const (cubeAverageVec Q g)
  have hg_centered :
      MemVectorL2 (cubeSet Q) (fun x => g x - cubeAverageVec Q g) :=
    hg.sub hconst_mem
  exact
    ω.cubeAverageVec_flux_eq_zero_of_cubeAverageVec_rhs_eq_zero
      hEll hg_centered (cubeAverageVec_centered_eq_zero Q g hg)

/-- Correcting a potential weak solution by the mean-zero Neumann solution with
centered RHS produces an `a`-harmonic remainder on the cube. -/
theorem exists_aHarmonicRemainder_of_potential_solenoidal_centered
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a
      (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MemVectorL2 (cubeSet Q) g) :
    ∃ w : AHarmonicFunction a (cubeSet Q),
      ∀ x ∈ cubeSet Q,
        u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS Q
  rcases hu_potential with ⟨v, hv⟩
  let wH1 : H1Function (cubeSet Q) := v - ω.toH1MeanZero.toH1Function
  have hconst_mem :
      MemVectorL2 (cubeSet Q) (fun _ : Vec d => cubeAverageVec Q g) :=
    memVectorL2_const (cubeAverageVec Q g)
  have hg_centered :
      MemVectorL2 (cubeSet Q) (fun x => g x - cubeAverageVec Q g) :=
    hg.sub hconst_mem
  have hu_mem : MemVectorL2 (cubeSet Q) u := by
    simpa [← hv] using v.grad_memVectorL2
  have hflux_u_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hu_mem
  have hres_u_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x) :=
    hflux_u_mem.sub hg
  have hflux_ω_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hres_ω_mem :
      MemVectorL2 (cubeSet Q)
        (fun x =>
          matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) -
            (g x - cubeAverageVec Q g)) :=
    hflux_ω_mem.sub hg_centered
  have hω_residual :
      IsSolenoidalOn (cubeSet Q)
        (fun x =>
          matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) -
            (g x - cubeAverageVec Q g)) :=
    (ω.residualFlux_zeroNormalTrace hEll hg_centered).isSolenoidalOn
  have hsol_diff :
      IsSolenoidalOn (cubeSet Q)
        ((fun x => matVecMul (a x) (u x) - g x) +
          (-1 : ℝ) •
            (fun x =>
              matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) -
                (g x - cubeAverageVec Q g))) :=
    isSolenoidalOn_add_of_memVectorL2 hres_u_mem (hres_ω_mem.const_smul (-1))
      hu_residual (isSolenoidalOn_smul hω_residual (-1))
  have hdiff_mem :
      MemVectorL2 (cubeSet Q)
        ((fun x => matVecMul (a x) (u x) - g x) +
          (-1 : ℝ) •
            (fun x =>
              matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) -
                (g x - cubeAverageVec Q g))) :=
    hres_u_mem.add (hres_ω_mem.const_smul (-1))
  have hvol : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hconst_sol :
      IsSolenoidalOn (cubeSet Q) (fun _ : Vec d => cubeAverageVec Q g) :=
    IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain
      (isSobolevRegularDomain_cubeSet_weakFluxRHS Q) hvol (cubeAverageVec Q g)
  have hsol_with_const :
      IsSolenoidalOn (cubeSet Q)
        (((fun x => matVecMul (a x) (u x) - g x) +
          (-1 : ℝ) •
            (fun x =>
              matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x) -
                (g x - cubeAverageVec Q g))) +
          fun _ : Vec d => cubeAverageVec Q g) :=
    isSolenoidalOn_add_of_memVectorL2 hdiff_mem hconst_mem hsol_diff hconst_sol
  have hsol :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (wH1.grad x)) := by
    convert hsol_with_const using 1
    funext x
    ext i
    simp [wH1, hv, sub_eq_add_neg, matVecMul_add, matVecMul_neg, Pi.add_apply]
    ring
  let w : AHarmonicFunction a (cubeSet Q) :=
    { toH1 := wH1
      isHarmonic := ⟨wH1.isPotentialOn, hsol⟩ }
  refine ⟨w, ?_⟩
  intro x hx
  change u x = wH1.grad x + ω.toH1MeanZero.toH1Function.grad x
  simp [wH1, hv, sub_eq_add_neg]

/-- The zero average of the centered Neumann corrector flux lets the local
flux average of the original field be replaced by the harmonic remainder's
flux average. -/
theorem cubeAverageVec_flux_eq_harmonicRemainderFlux_of_centered_rhs
    {lam Lam : ℝ} (ω : MeanZeroNeumannCorrectorData Q a
      (fun x => g x - cubeAverageVec Q g))
    (w : AHarmonicFunction a (cubeSet Q)) {u : Vec d → Vec d}
    (hdecomp :
      ∀ x ∈ cubeSet Q,
        u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g) :
    cubeAverageVec Q (fun x => matVecMul (a x) (u x)) =
      cubeAverageVec Q (fun x => matVecMul (a x) (w.toH1.grad x)) := by
  have hflux_u_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hu_mem
  have hflux_ω_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hsub :=
    cubeAverageVec_sub_of_memVectorL2 Q
      (fun x => matVecMul (a x) (u x))
      (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x))
      hflux_u_mem hflux_ω_mem
  have hω_avg :
      cubeAverageVec Q
        (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) = 0 :=
    ω.cubeAverageVec_flux_eq_zero_of_centered_rhs hEll hg
  have hsub_eq :
      cubeAverageVec Q
          (fun x =>
            matVecMul (a x) (u x) -
              matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) =
        cubeAverageVec Q (fun x => matVecMul (a x) (w.toH1.grad x)) := by
    apply cubeAverageVec_eq_of_eq_on_cubeSet_weakFluxRHS
    intro x hx
    rw [hdecomp x hx]
    ext i
    simp [matVecMul_add]
  calc
    cubeAverageVec Q (fun x => matVecMul (a x) (u x))
        =
          cubeAverageVec Q (fun x => matVecMul (a x) (u x)) -
            cubeAverageVec Q
              (fun x => matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) := by
          rw [hω_avg, sub_zero]
    _ =
        cubeAverageVec Q
          (fun x =>
            matVecMul (a x) (u x) -
              matVecMul (a x) (ω.toH1MeanZero.toH1Function.grad x)) := by
          rw [hsub]
    _ = cubeAverageVec Q (fun x => matVecMul (a x) (w.toH1.grad x)) := hsub_eq

/-- Cube-average form of the Neumann corrector energy identity obtained by
testing the centered corrector equation with the corrector itself. -/
theorem cubeAverage_coefficientEnergyDensity_eq_centered_rhs_pairing
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g)) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) =
      cubeAverage Q
        (fun x =>
          vecDot (g x - cubeAverageVec Q g)
            (ω.toH1MeanZero.toH1Function.grad x)) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  have henergy_eq :
      ∫ x in cubeSet Q, coefficientEnergyDensity a ωgrad x ∂MeasureTheory.volume =
        ∫ x in cubeSet Q,
          vecDot (ωgrad x) (matVecMul (a x) (ωgrad x)) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [ωgrad] using coefficientEnergyDensity_eq_unsymmetrized a ωgrad x
  have hweak := ω.weakSolution.energy_identity
  unfold cubeAverage
  rw [henergy_eq]
  rw [hweak]

/-- Coefficient-energy version of the split
`w = u - grad omega` for the mean-zero Neumann corrector. -/
theorem cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hu : MemVectorL2 (cubeSet Q) u) :
    cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
      2 * cubeAverage Q (coefficientEnergyDensity a u) +
        2 * cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  have hwEnergy_int :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      w.toH1.grad_memVectorL2
  have huEnergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hu
  have hωEnergy_int :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a ωgrad) (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hpoint :
      ∀ x ∈ cubeSet Q,
        coefficientEnergyDensity a (fun y => w.toH1.grad y) x ≤
          2 *
            (coefficientEnergyDensity a u x +
              coefficientEnergyDensity a ωgrad x) := by
    intro x hx
    have hwsub : w.toH1.grad x = u x - ωgrad x := by
      ext i
      change w.toH1.grad x i = u x i - ω.toH1MeanZero.toH1Function.grad x i
      have hcoord : u x i = w.toH1.grad x i +
          ω.toH1MeanZero.toH1Function.grad x i := by
        simpa using congrArg (fun z => z i) (huw x hx)
      linarith
    have hsub :=
      coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
        hEll u ωgrad x hx
    have hEq :
        coefficientEnergyDensity a (fun y => w.toH1.grad y) x =
          coefficientEnergyDensity a (fun y => u y - ωgrad y) x := by
      simp [coefficientEnergyDensity, hwsub]
    exact hEq.trans_le hsub
  have havg_raw :
      cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
        cubeAverage Q
          (fun x =>
            2 *
              (coefficientEnergyDensity a u x +
                coefficientEnergyDensity a ωgrad x)) := by
    unfold cubeAverage
    have hvol_inv_nonneg : 0 ≤ (cubeVolume Q)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))
    refine mul_le_mul_of_nonneg_left ?_ hvol_inv_nonneg
    exact
      MeasureTheory.integral_mono_ae hwEnergy_int
        ((huEnergy_int.add hωEnergy_int).const_mul (2 : ℝ))
        ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
          Filter.Eventually.of_forall fun x hx => hpoint x hx)
  have hsplit :
      cubeAverage Q
          (fun x =>
            2 *
              (coefficientEnergyDensity a u x +
                coefficientEnergyDensity a ωgrad x)) =
        2 * cubeAverage Q (coefficientEnergyDensity a u) +
          2 * cubeAverage Q (coefficientEnergyDensity a ωgrad) := by
    unfold cubeAverage
    have hfun :
        (fun x =>
          2 *
            (coefficientEnergyDensity a u x +
              coefficientEnergyDensity a ωgrad x)) =
          (fun x =>
            2 * coefficientEnergyDensity a u x +
              2 * coefficientEnergyDensity a ωgrad x) := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_add (huEnergy_int.const_mul (2 : ℝ))
      (hωEnergy_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  exact havg_raw.trans_eq hsplit

/-- Descendant-cube form of the centered Neumann corrector harmonic-remainder
construction.  The parent potential/solenoidal predicates are restricted to
the descendant cube, matching the local step used in the weak-flux recurrence.
-/
theorem exists_aHarmonicRemainder_of_parent_potential_solenoidal_centered
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam : ℝ}
    (ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g))
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g) :
    ∃ w : AHarmonicFunction a (cubeSet R),
      ∀ x ∈ cubeSet R,
        u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x := by
  have hu_potential_R :
      IsPotentialOn (cubeSet R) u :=
    hu_potential.restrict_cubeSet_of_mem_descendantsAtDepth hR
  have hflux_memR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllR hu_memR
  have hres_memR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u x) - g x) :=
    hflux_memR.sub hg_memR
  have hu_residual_R :
      IsSolenoidalOn (cubeSet R) (fun x => matVecMul (a x) (u x) - g x) :=
    hu_residual.restrict_cubeSet_of_mem_descendantsAtDepth hR hres_memR
  exact
    ω.exists_aHarmonicRemainder_of_potential_solenoidal_centered
      hu_potential_R hu_residual_R hEllR hg_memR

/-- Fully constructed descendant-cube centered Neumann corrector and harmonic
remainder from parent potential/solenoidal PDE data, assuming the local
mean-zero coercive estimate on the descendant half-open cube. -/
theorem exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam : ℝ}
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R)) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        ∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet R)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_weakFluxRHS R
  have hconst_mem :
      MemVectorL2 (cubeSet R) (fun _ : Vec d => cubeAverageVec R g) :=
    memVectorL2_const (cubeAverageVec R g)
  have hg_centered :
      MemVectorL2 (cubeSet R) (fun x => g x - cubeAverageVec R g) :=
    hg_memR.sub hconst_mem
  have hne : Set.Nonempty (cubeSet R) := by
    refine ⟨cubeCenter R, openCubeSet_subset_cubeSet R ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    simpa [Metric.mem_ball] using cubeRadius_pos R
  let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
    meanZeroNeumannCorrectorDataOf_h1CoerciveEstimate
      (Q := R) (a := a) (g := fun x => g x - cubeAverageVec R g)
      (lam := lam) (Lam := Lam) hg_centered hC hne hEllR
  rcases
      ω.exists_aHarmonicRemainder_of_parent_potential_solenoidal_centered
        (P := P) (R := R) (n := n) (u := u)
        hu_potential hu_residual hR hEllR hu_memR hg_memR with
    ⟨w, hw⟩
  exact ⟨ω, w, hw⟩

end MeanZeroNeumannCorrectorData

end

end Homogenization
