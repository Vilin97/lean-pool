/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.WeakBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong convergence of weak Fourier cutoffs

The finite real Fourier cutoffs of a weak path converge in spacetime `L²`, together with
their spatial gradients. This is the strong convergence needed to pass the finite coefficient
energy balances to the weak path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.WeakUniqueness


open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance weakProjectionConvergenceMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionConvergenceMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

theorem weakProjection_scalarTransfer_normSq {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    ‖(weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)‖ ^ 2 = AVenhance.l2NormSq f := by
  rw [l2_norm_sq_eq_integral_sq]
  calc
    ∫ x : Torus, ‖(weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f) x‖ ^ 2 =
        ∫ x : Torus, ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(weakProjection_realCellToTorus_memLp hf).coeFn_toLp] with x hx
          rw [hx]
    _ = ∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus
        (fun y => f y ^ 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [AVenhance.Infra.Torus.periodicToTorus, Real.norm_eq_abs, sq_abs]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, f x ^ 2 :=
      AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
    _ = AVenhance.l2NormSq f := by
      rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
      rfl

theorem WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
    {u : ℝ → Vec 2 → ℝ} {t : ℝ} {N : ℕ}
    :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus (u t)) =
    weakFourierCoefficientPath N u t := by
  ext i
  let a := (realFourierIndexEquivFin N).symm i
  change (∫ x : Torus,
      AVenhance.Infra.Torus.periodicToTorus (u t) x * realFourierModeFin N i x) = _
  rw [realFourierModeFin_eq_periodicToTorus]
  change (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus
      (fun y => u t y * realFourierModeAmbient N a y) x) = _
  rw [AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell,
    AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  simp [weakFourierCoefficientPath, weakModePairing, a]

open WeakProjectionConvergence

theorem WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing
    {f : Vec 2 → ℝ} (hf : MemL2On AVenhance.unitCube f) (N : ℕ) :
    realFourierProjectionCoefficients N
        ((weakProjection_realCellToTorus_memLp hf).toLp
          (AVenhance.Infra.Torus.periodicToTorus f)) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus f) := by
  ext i
  unfold realFourierProjectionCoefficients modeProjectionCoefficients
  change (∫ x : Torus,
      ((weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)) x * realFourierModeFin N i x) = _
  apply integral_congr_ae
  filter_upwards [(weakProjection_realCellToTorus_memLp hf).coeFn_toLp] with x hx
  rw [hx]

theorem WeakProjectionConvergence.weakProjection_pythagorean (N : ℕ) (v : ScalarTorusL2) :
    ‖v - realFourierScalarMap N (realFourierProjectionCoefficients N v)‖ ^ 2 =
      ‖v‖ ^ 2 - ‖realFourierScalarMap N (realFourierProjectionCoefficients N v)‖ ^ 2 := by
  let c := realFourierProjectionCoefficients N v
  have hc (i : Fin (RealFourierDimension N)) :
      inner ℝ v (realFourierModeL2 N i) = c i := by
    have hinner : inner ℝ v (realFourierModeL2 N i) =
        ∫ x : Torus, v x * realFourierModeFin N i x := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [realFourierModeFin_memLp N i |>.coeFn_toLp] with x hm
      simp [realFourierModeL2, hm, mul_comm]
    rw [hinner]
    simp [c, realFourierProjectionCoefficients, modeProjectionCoefficients]
  have hcross : inner ℝ v (realFourierScalarMap N c) =
      ∑ i : Fin (RealFourierDimension N), c i ^ 2 := by
    rw [realFourierScalarMap_apply, inner_sum]
    simp_rw [inner_smul_right, hc]
    simp [pow_two]
  have hcoeffNorm : ‖c‖ ^ 2 =
      ∑ i : Fin (RealFourierDimension N), c i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq c, PiLp.inner_apply]
    simp [pow_two]
  have hcrossNorm : inner ℝ v (realFourierScalarMap N c) =
      ‖realFourierScalarMap N c‖ ^ 2 := by
    rw [hcross]
    calc
      ∑ i : Fin (RealFourierDimension N), c i ^ 2 = ‖c‖ ^ 2 := hcoeffNorm.symm
      _ = ‖realFourierScalarMap N c‖ ^ 2 := by rw [realFourierScalarMap_norm]
  rw [norm_sub_sq_real, hcrossNorm]
  ring

theorem WeakProjectionConvergence.weakProjection_gradientCoefficient_eq_derivative
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (h : AVenhance.IsPeriodicH1With (u t) (Du t)) (N : ℕ) (i : Fin 2) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)) =
    realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i := by
  have hcoeff := weakGradient_realFourierProjectionCoefficients h N i
  rw [
    WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing (u := u) (t := t)
  ] at hcoeff
  exact hcoeff.symm

/-- The cell Fourier coefficient path is the coefficient vector of the orthogonal real Fourier
projection of the transferred slice. -/
noncomputable def weakFourierProjectionL2 (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    ScalarTorusL2 :=
  realFourierScalarMap N (weakFourierCoefficientPath N u t)

/-- The ambient smooth Fourier polynomial associated to a weak path at one time. -/
noncomputable def weakFourierModeProjection (N : ℕ) (u : ℝ → Vec 2 → ℝ)
    (t : ℝ) : Vec 2 → ℝ :=
  realFourierModeAmbientExpansion N (weakFourierCoefficientPath N u t)

/-- The finite projected weak-gradient component in torus `L²`. -/
noncomputable def weakFourierProjectionGradientL2 (N : ℕ) (u : ℝ → Vec 2 → ℝ)
    (t : ℝ) (i : Fin 2) : ScalarTorusL2 :=
  realFourierScalarMap N
    (realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i)

theorem WeakProjectionConvergence.weakFourierModeAmbientExpansion_periodicToTorus (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientExpansion N c) =
      modeExpansion (RealFourierDimension N) (realFourierModeFin N) c := by
  funext x
  change (∑ j : Fin (RealFourierDimension N), c j *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)) = _
  apply Finset.sum_congr rfl
  intro j hj
  rw [realFourierModeFin_eq_periodicToTorus]
  rfl

theorem WeakProjectionConvergence.weakFourierSynthesis_eq_expansionTransfer (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierScalarMap N c =
      (weakProjection_realCellToTorus_memLp
        (weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N c).continuous)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientExpansion N c)) := by
  let hmem := weak_continuous_memL2On
    (realFourierModeAmbientExpansion_contDiff N c).continuous
  let htor := weakProjection_realCellToTorus_memLp hmem
  apply Lp.ext
  filter_upwards [htor.coeFn_toLp,
    realFourierScalarMap_coeFn N c] with x hx hproj
  rw [hx, hproj, WeakProjectionConvergence.weakFourierModeAmbientExpansion_periodicToTorus]

theorem weakFourierProjectionL2_eq_expansionTransfer
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    weakFourierProjectionL2 N u t =
      (weakProjection_realCellToTorus_memLp
        (weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N
          (weakFourierCoefficientPath N u t)).continuous)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (weakFourierModeProjection N u t)) := by
  exact WeakProjectionConvergence.weakFourierSynthesis_eq_expansionTransfer N
      (weakFourierCoefficientPath N u t)

theorem weakFourierProjectionGradientL2_eq_expansionTransfer
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (i : Fin 2) :
    weakFourierProjectionGradientL2 N u t i =
      (weakProjection_realCellToTorus_memLp
        (weak_continuous_memL2On
          (by
            have hc := realFourierModeAmbientExpansion_contDiff N
              (weakFourierCoefficientPath N u t)
            change Continuous (fun x : Vec 2 =>
              fderiv ℝ (realFourierModeAmbientExpansion N
                (weakFourierCoefficientPath N u t)) x (Homogenization.basisVec i))
            exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const))).toLp
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad (weakFourierModeProjection N u t) x i)) := by
  let c := weakFourierCoefficientPath N u t
  let dc := realFourierModeDerivativeCoefficients N c i
  have hgrad := spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion N c i
  have htransfer := congrArg AVenhance.Infra.Torus.periodicToTorus hgrad
  have hgradCont : Continuous (fun x : Vec 2 =>
      AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i) := by
    change Continuous (fun x : Vec 2 =>
      fderiv ℝ (realFourierModeAmbientExpansion N c) x (Homogenization.basisVec i))
    exact (realFourierModeAmbientExpansion_contDiff N c).continuous_fderiv
      (by simp) |>.clm_apply continuous_const
  have hgradMem : MemL2On AVenhance.unitCube
      (fun x : Vec 2 => AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i) :=
    weak_continuous_memL2On hgradCont
  have hderivMem : MemL2On AVenhance.unitCube (realFourierModeAmbientExpansion N dc) :=
    weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N dc).continuous
  calc
    realFourierScalarMap N dc =
        (weakProjection_realCellToTorus_memLp hderivMem).toLp
          (AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientExpansion N dc)) :=
      WeakProjectionConvergence.weakFourierSynthesis_eq_expansionTransfer N dc
    _ = (weakProjection_realCellToTorus_memLp hgradMem).toLp
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i)) := by
      apply Lp.ext
      filter_upwards [(weakProjection_realCellToTorus_memLp hderivMem).coeFn_toLp,
        (weakProjection_realCellToTorus_memLp hgradMem).coeFn_toLp] with x hderiv hgrad
      rw [hderiv, hgrad]
      exact (congrFun htransfer x).symm

theorem WeakProjectionConvergence.weakFourierProjection_scalarCellError_normSq
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (fun x => u t x - weakFourierModeProjection N u t x) =
      ‖(weakProjection_realCellToTorus_memLp (hu.1 t ht).2).toLp
          (AVenhance.Infra.Torus.periodicToTorus (u t)) -
        weakFourierProjectionL2 N u t‖ ^ 2 := by
  let hvalue := (hu.1 t ht).2
  let p := weakFourierModeProjection N u t
  have hp : MemL2On AVenhance.unitCube p :=
    weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N u t) |>.continuous)
  let hdiff : MemL2On AVenhance.unitCube (fun x => u t x - p x) := hvalue.sub hp
  have hclass : (weakProjection_realCellToTorus_memLp hdiff).toLp
      (AVenhance.Infra.Torus.periodicToTorus (fun x => u t x - p x)) =
      (weakProjection_realCellToTorus_memLp hvalue).toLp
          (AVenhance.Infra.Torus.periodicToTorus (u t)) -
        weakFourierProjectionL2 N u t := by
    apply Lp.ext
    filter_upwards [(weakProjection_realCellToTorus_memLp hdiff).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hvalue).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hp).coeFn_toLp,
      Lp.coeFn_sub ((weakProjection_realCellToTorus_memLp hvalue).toLp
        (AVenhance.Infra.Torus.periodicToTorus (u t)))
        (weakFourierProjectionL2 N u t)] with x hdiffX huX hpX hsub
    have hPNclass : weakFourierProjectionL2 N u t =
        (weakProjection_realCellToTorus_memLp hp).toLp
          (AVenhance.Infra.Torus.periodicToTorus p) := by
      simpa [p, weakFourierModeProjection] using
        weakFourierProjectionL2_eq_expansionTransfer N u t
    have hPNclassAt := congrArg (fun v : ScalarTorusL2 => v x) hPNclass
    have hPN : weakFourierProjectionL2 N u t x =
        AVenhance.Infra.Torus.periodicToTorus p x := by
      rw [hPNclassAt, hpX]
    rw [hdiffX, hsub]
    simp only [Pi.sub_apply]
    rw [huX, hPN]
    simp [AVenhance.Infra.Torus.periodicToTorus]
  have hnorm := weakProjection_scalarTransfer_normSq hdiff
  calc
    AVenhance.l2NormSq (fun x => u t x - p x) =
        ‖(weakProjection_realCellToTorus_memLp hdiff).toLp
          (AVenhance.Infra.Torus.periodicToTorus (fun x => u t x - p x))‖ ^ 2 :=
      hnorm.symm
    _ = ‖(weakProjection_realCellToTorus_memLp hvalue).toLp
          (AVenhance.Infra.Torus.periodicToTorus (u t)) -
        weakFourierProjectionL2 N u t‖ ^ 2 := by rw [hclass]

/-- The cell `L²` error of a projected weak-gradient component is exactly its torus `L²` error. -/
theorem WeakProjectionConvergence.weakFourierProjection_gradientCellError_normSq
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (h : AVenhance.IsPeriodicH1With (u t) (Du t)) (N : ℕ) (i : Fin 2) :
    AVenhance.l2NormSq (fun x => Du t x i -
      AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) =
      ‖(weakProjection_realCellToTorus_memLp (h.2.2.2.1 i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)) -
        weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by
  let hvalue := h.2.2.2.1 i
  let p := weakFourierModeProjection N u t
  have hgradCont : Continuous (fun x : Vec 2 => AVenhance.spaceGrad p x i) := by
    have hc := realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N u t)
    change Continuous (fun x : Vec 2 =>
      fderiv ℝ (realFourierModeAmbientExpansion N
        (weakFourierCoefficientPath N u t)) x (Homogenization.basisVec i))
    exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp : MemL2On AVenhance.unitCube (fun x => AVenhance.spaceGrad p x i) :=
    weak_continuous_memL2On hgradCont
  let hdiff : MemL2On AVenhance.unitCube
      (fun x => Du t x i - AVenhance.spaceGrad p x i) := hvalue.sub hp
  have hclass : (weakProjection_realCellToTorus_memLp hdiff).toLp
      (AVenhance.Infra.Torus.periodicToTorus
        (fun x => Du t x i - AVenhance.spaceGrad p x i)) =
      (weakProjection_realCellToTorus_memLp hvalue).toLp
          (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)) -
        weakFourierProjectionGradientL2 N u t i := by
    apply Lp.ext
    filter_upwards [(weakProjection_realCellToTorus_memLp hdiff).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hvalue).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hp).coeFn_toLp,
      Lp.coeFn_sub ((weakProjection_realCellToTorus_memLp hvalue).toLp
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)))
        (weakFourierProjectionGradientL2 N u t i)] with x hdiffX huX hpX hsub
    have hPNclass : weakFourierProjectionGradientL2 N u t i =
        (weakProjection_realCellToTorus_memLp hp).toLp
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => AVenhance.spaceGrad p x i)) := by
      simpa [p, weakFourierModeProjection] using
        weakFourierProjectionGradientL2_eq_expansionTransfer N u t i
    have hPNclassAt := congrArg (fun v : ScalarTorusL2 => v x) hPNclass
    have hPN : weakFourierProjectionGradientL2 N u t i x =
        AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad p x i) x := by
      rw [hPNclassAt, hpX]
    rw [hdiffX, hsub]
    simp only [Pi.sub_apply]
    rw [huX, hPN]
    simp [AVenhance.Infra.Torus.periodicToTorus]
  have hnorm := weakProjection_scalarTransfer_normSq hdiff
  calc
    AVenhance.l2NormSq (fun x => Du t x i - AVenhance.spaceGrad p x i) =
        ‖(weakProjection_realCellToTorus_memLp hdiff).toLp
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => Du t x i - AVenhance.spaceGrad p x i))‖ ^ 2 := hnorm.symm
    _ = ‖(weakProjection_realCellToTorus_memLp hvalue).toLp
          (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)) -
        weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by rw [hclass]

theorem WeakProjectionConvergence.weakFourierProjection_scalarCellError_eq_deficit
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (fun x => u t x - weakFourierModeProjection N u t x) =
      AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2 := by
  let hmem := (hu.1 t ht).2
  let v := (weakProjection_realCellToTorus_memLp hmem).toLp
    (AVenhance.Infra.Torus.periodicToTorus (u t))
  have hcoeff : realFourierProjectionCoefficients N v =
      weakFourierCoefficientPath N u t := by
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hmem]
    exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
  have hPyth : ‖v - weakFourierProjectionL2 N u t‖ ^ 2 =
      ‖v‖ ^ 2 - ‖weakFourierProjectionL2 N u t‖ ^ 2 := by
    simpa [weakFourierProjectionL2, hcoeff] using
        WeakProjectionConvergence.weakProjection_pythagorean N v
  calc
    AVenhance.l2NormSq (fun x => u t x - weakFourierModeProjection N u t x) =
        ‖v - weakFourierProjectionL2 N u t‖ ^ 2 :=
      WeakProjectionConvergence.weakFourierProjection_scalarCellError_normSq hu N ht
    _ = ‖v‖ ^ 2 - ‖weakFourierProjectionL2 N u t‖ ^ 2 := hPyth
    _ = AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2 := by
      rw [weakProjection_scalarTransfer_normSq hmem]

theorem WeakProjectionConvergence.weakFourierProjection_gradientCellError_eq_deficit
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (h : AVenhance.IsPeriodicH1With (u t) (Du t)) (N : ℕ) (i : Fin 2) :
    AVenhance.l2NormSq (fun x => Du t x i -
      AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) =
      AVenhance.l2NormSq (fun x => Du t x i) -
        ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by
  let hmem := h.2.2.2.1 i
  let v := (weakProjection_realCellToTorus_memLp hmem).toLp
    (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i))
  have hcoeff : realFourierProjectionCoefficients N v =
      realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i := by
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hmem]
    exact WeakProjectionConvergence.weakProjection_gradientCoefficient_eq_derivative h N i
  have hPyth : ‖v - weakFourierProjectionGradientL2 N u t i‖ ^ 2 =
      ‖v‖ ^ 2 - ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by
    simpa [weakFourierProjectionGradientL2, hcoeff] using
        WeakProjectionConvergence.weakProjection_pythagorean N v
  calc
    AVenhance.l2NormSq (fun x => Du t x i -
        AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) =
        ‖v - weakFourierProjectionGradientL2 N u t i‖ ^ 2 :=
      WeakProjectionConvergence.weakFourierProjection_gradientCellError_normSq h N i
    _ = ‖v‖ ^ 2 - ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 := hPyth
    _ = AVenhance.l2NormSq (fun x => Du t x i) -
          ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by
      rw [weakProjection_scalarTransfer_normSq hmem]

/-- The finite weak Fourier projection converges to every `L²` slice in torus `L²`. -/
theorem weakFourierProjectionL2_tendsto
    {u : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hu : MemL2On AVenhance.unitCube (u t)) :
    Tendsto (fun N => weakFourierProjectionL2 N u t) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hu).toLp
        (AVenhance.Infra.Torus.periodicToTorus (u t)))) := by
  let v := (weakProjection_realCellToTorus_memLp hu).toLp
    (AVenhance.Infra.Torus.periodicToTorus (u t))
  have hcoeff : ∀ N, realFourierProjectionCoefficients N v =
      weakFourierCoefficientPath N u t := by
    intro N
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hu]
    exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
  have hsequence : (fun N => weakFourierProjectionL2 N u t) =
      fun N => realFourierScalarMap N (realFourierProjectionCoefficients N v) := by
    funext N
    simp [weakFourierProjectionL2, hcoeff N]
  rw [hsequence]
  exact tendsto_realFourierProjection v

/-- The derivatives of the finite weak Fourier projections converge to the weak-gradient
components in torus `L²` on every slice with periodic `H¹` data. -/
theorem weakFourierProjectionGradientL2_tendsto
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (h : AVenhance.IsPeriodicH1With (u t) (Du t)) (i : Fin 2) :
    Tendsto (fun N => realFourierScalarMap N
        (realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i))
      atTop (𝓝 ((weakProjection_realCellToTorus_memLp (h.2.2.2.1 i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i)))) := by
  let v := (weakProjection_realCellToTorus_memLp (h.2.2.2.1 i)).toLp
    (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i))
  have hcoeff : ∀ N, realFourierProjectionCoefficients N v =
      realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i := by
    intro N
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing (h.2.2.2.1 i)]
    exact WeakProjectionConvergence.weakProjection_gradientCoefficient_eq_derivative h N i
  have hsequence : (fun N => realFourierScalarMap N
      (realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i)) =
      fun N => realFourierScalarMap N (realFourierProjectionCoefficients N v) := by
    funext N
    simp [hcoeff N]
  rw [hsequence]
  exact tendsto_realFourierProjection v

theorem WeakProjectionConvergence.weakFourierMode_smooth (N : ℕ) (i : Fin (RealFourierDimension
    N)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm i)).of_le (by simp)

theorem WeakProjectionConvergence.weakFourierMode_periodic (N : ℕ) (i : Fin (RealFourierDimension
    N)) :
    AVenhance.IsZ2Periodic
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i)

theorem WeakProjectionConvergence.weakFourierCoefficientPath_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    ContinuousOn (fun t => weakFourierCoefficientPath N u t)
      (Set.Icc (0 : ℝ) 1) := by
  let g : ℝ → Fin (RealFourierDimension N) → ℝ := fun t i =>
    weakModePairing u
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_pi.2
    intro i
    exact hu.2.2.2.2.2.2.1
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
      (WeakProjectionConvergence.weakFourierMode_smooth N i)
          (WeakProjectionConvergence.weakFourierMode_periodic N i)
  have htoLp : Continuous (WithLp.toLp 2 :
      (Fin (RealFourierDimension N) → ℝ) → Coefficients (RealFourierDimension N)) :=
    PiLp.continuous_toLp 2 (fun _ : Fin (RealFourierDimension N) => ℝ)
  have hcomp := htoLp.continuousOn.comp hg (fun _ _ => Set.mem_univ _)
  convert hcomp using 1
  funext t
  rfl

theorem weakFourierProjectionL2_normSq_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq (u t))) := by
  have htmem := (hu.1 t ht).2
  have hprojection := weakFourierProjectionL2_tendsto htmem
  have hnorm := (continuous_norm.pow 2).continuousAt.tendsto.comp hprojection
  have hlimit : ‖(weakProjection_realCellToTorus_memLp htmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))‖ ^ 2 =
      AVenhance.l2NormSq (u t) := weakProjection_scalarTransfer_normSq htmem
  change Tendsto (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
    (𝓝 (‖(weakProjection_realCellToTorus_memLp htmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))‖ ^ 2)) at hnorm
  simpa only [hlimit] using hnorm

theorem WeakProjectionConvergence.weakFourierProjectionL2_normSq_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    ContinuousOn (fun t => ‖weakFourierProjectionL2 N u t‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := by
  have hcoeff := WeakProjectionConvergence.weakFourierCoefficientPath_continuousOn hu N
  have hprojection : ContinuousOn (fun t => weakFourierProjectionL2 N u t)
      (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t => realFourierScalarMap N
      (weakFourierCoefficientPath N u t)) (Set.Icc (0 : ℝ) 1)
    exact (realFourierScalarMap N).continuous.continuousOn.comp hcoeff
      (fun _ _ => Set.mem_univ _)
  exact hprojection.norm.pow 2

theorem WeakProjectionConvergence.weakFourierDerivativeCoefficientPath_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) (i : Fin 2) :
    ContinuousOn (fun t => realFourierModeDerivativeCoefficients N
      (weakFourierCoefficientPath N u t) i) (Set.Icc (0 : ℝ) 1) := by
  have hc := WeakProjectionConvergence.weakFourierCoefficientPath_continuousOn hu N
  let g : ℝ → Fin (RealFourierDimension N) → ℝ := fun t j =>
    weakFourierCoefficientPath N u t
      (realFourierIndexEquivFin N (realFourierModeIndexSwap
        ((realFourierIndexEquivFin N).symm j))) *
      realFourierModeDerivativeScale
        (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) i
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_pi.2
    intro j
    have hcoord : ContinuousOn (fun t => weakFourierCoefficientPath N u t
        (realFourierIndexEquivFin N (realFourierModeIndexSwap
          ((realFourierIndexEquivFin N).symm j)))) (Set.Icc (0 : ℝ) 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin (RealFourierDimension N) => ℝ)
        (realFourierIndexEquivFin N (realFourierModeIndexSwap
          ((realFourierIndexEquivFin N).symm j)))).continuousOn.comp hc
            (fun _ _ => Set.mem_univ _)
    exact hcoord.mul continuousOn_const
  have htoLp : Continuous (WithLp.toLp 2 :
      (Fin (RealFourierDimension N) → ℝ) → Coefficients (RealFourierDimension N)) :=
    PiLp.continuous_toLp 2 (fun _ : Fin (RealFourierDimension N) => ℝ)
  have hcomp := htoLp.continuousOn.comp hg (fun _ _ => Set.mem_univ _)
  convert hcomp using 1
  funext t
  simp [g, realFourierModeDerivativeCoefficients]

theorem WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) (i : Fin 2) :
    ContinuousOn (fun t => ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := by
  have hcoeff := WeakProjectionConvergence.weakFourierDerivativeCoefficientPath_continuousOn hu N i
  have hprojection : ContinuousOn (fun t => weakFourierProjectionGradientL2 N u t i)
      (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t => realFourierScalarMap N
      (realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i)) _
    exact (realFourierScalarMap N).continuous.continuousOn.comp hcoeff
      (fun _ _ => Set.mem_univ _)
  exact hprojection.norm.pow 2

theorem WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_tendsto
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (h : AVenhance.IsPeriodicH1With (u t) (Du t)) (i : Fin 2) :
    Tendsto (fun M => ‖weakFourierProjectionGradientL2 M u t i‖ ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq (fun x => Du t x i))) := by
  have hprojection := weakFourierProjectionGradientL2_tendsto h i
  have hnorm := (continuous_norm.pow 2).continuousAt.tendsto.comp hprojection
  have hmem := h.2.2.2.1 i
  have hlimit : ‖(weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i))‖ ^ 2 =
      AVenhance.l2NormSq (fun x => Du t x i) := weakProjection_scalarTransfer_normSq hmem
  change Tendsto (fun M => ‖weakFourierProjectionGradientL2 M u t i‖ ^ 2) atTop
    (𝓝 (‖(weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i))‖ ^ 2)) at hnorm
  simpa only [hlimit] using hnorm

theorem WeakProjectionConvergence.weakProjection_timeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

theorem WeakProjectionConvergence.weakGradientComponent_l2NormSq_time_integrable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (i : Fin 2) :
    Integrable (fun t => AVenhance.l2NormSq (fun x => Du t x i))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hDi := hu.2.2.2.1 i
  have hsq : Integrable (fun p : ℝ × Vec 2 => (Du p.1 p.2 i) ^ 2)
      (volume.restrict AVenhance.timeCube) :=
    (memLp_two_iff_integrable_sq hDi.aestronglyMeasurable).1 hDi
  have hproduct : Integrable (fun p : ℝ × Vec 2 => (Du p.1 p.2 i) ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← WeakProjectionConvergence.weakProjection_timeCube_measure_eq_product]
  have htime := hproduct.integral_prod_left
  have heq : (fun t => ∫ x, (Du t x i) ^ 2
      ∂(volume.restrict AVenhance.unitCube)) =
      fun t => AVenhance.l2NormSq (fun x => Du t x i) := by
    funext t
    rfl
  rw [heq] at htime
  exact htime

theorem WeakProjectionConvergence.weakGradientComponent_l2NormSq_aestronglyMeasurable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (i : Fin 2) :
    AEStronglyMeasurable (fun t => AVenhance.l2NormSq (fun x => Du t x i))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let G : ℝ → ℝ := fun t => Filter.limsup
    (fun N => ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2) atTop
  have hG : AEMeasurable G μ :=
    AEMeasurable.limsup (fun N =>
      (ContinuousOn.aestronglyMeasurable_of_subset_isCompact
        (WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_continuousOn hu N i)
        isCompact_Icc measurableSet_Ioo
        (by intro t ht; exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)).aemeasurable)
  have hEq : G =ᵐ[μ] fun t => AVenhance.l2NormSq (fun x => Du t x i) := by
    filter_upwards [hu.2.2.2.2.1] with t ht
    exact (WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_tendsto ht i).limsup_eq
  exact hG.aestronglyMeasurable.congr hEq

/-- Each projected weak-gradient component converges strongly in time `L²`. -/
theorem weakFourierProjection_gradientComponent_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (i : Fin 2) :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (fun x => Du t x i) -
        ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let e : ℕ → ℝ → ℝ := fun N t =>
    AVenhance.l2NormSq (fun x => Du t x i) -
      ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2
  have heMeas (N : ℕ) : AEStronglyMeasurable (e N) μ := by
    exact (WeakProjectionConvergence.weakGradientComponent_l2NormSq_aestronglyMeasurable hu i).sub
      (ContinuousOn.aestronglyMeasurable_of_subset_isCompact
        (WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_continuousOn hu N i)
        isCompact_Icc measurableSet_Ioo
        (by intro t ht; exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hdom : Integrable (fun t => AVenhance.l2NormSq (fun x => Du t x i)) μ :=
    WeakProjectionConvergence.weakGradientComponent_l2NormSq_time_integrable hu i
  have hbound (N : ℕ) : ∀ᵐ t ∂μ, ‖e N t‖ ≤
      AVenhance.l2NormSq (fun x => Du t x i) := by
    filter_upwards [hu.2.2.2.2.1] with t ht
    have hmem := ht.2.2.2.1 i
    let v := (weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (fun x => Du t x i))
    have hnormv : ‖v‖ ^ 2 = AVenhance.l2NormSq (fun x => Du t x i) :=
      weakProjection_scalarTransfer_normSq hmem
    have hcoeff : realFourierProjectionCoefficients N v =
        realFourierModeDerivativeCoefficients N (weakFourierCoefficientPath N u t) i := by
      rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hmem]
      exact WeakProjectionConvergence.weakProjection_gradientCoefficient_eq_derivative ht N i
    have hcontractCoeff : ‖realFourierProjectionCoefficients N v‖ ≤ ‖v‖ := by
      have hcontract := realFourierModeFin_projectionCoefficients_norm_le N
        (weakProjection_realCellToTorus_memLp hmem)
      rw [
        ← WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hmem
      ] at hcontract
      simpa [v] using hcontract
    have hcontract : ‖weakFourierProjectionGradientL2 N u t i‖ ≤ ‖v‖ := by
      rw [weakFourierProjectionGradientL2, ← hcoeff, realFourierScalarMap_norm]
      exact hcontractCoeff
    have hprojSq : ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 ≤
        AVenhance.l2NormSq (fun x => Du t x i) := by
      rw [← hnormv]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcontract
    have hfullNonneg : 0 ≤ AVenhance.l2NormSq (fun x => Du t x i) := by
      rw [← hnormv]
      positivity
    change |AVenhance.l2NormSq (fun x => Du t x i) -
      ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2| ≤ _
    apply abs_le.mpr
    constructor <;> nlinarith
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun N => e N t) atTop (𝓝 0) := by
    filter_upwards [hu.2.2.2.2.1] with t ht
    have hnorm := WeakProjectionConvergence.weakFourierProjectionGradientL2_normSq_tendsto ht i
    have hconst : Tendsto (fun _ : ℕ => AVenhance.l2NormSq (fun x => Du t x i))
        atTop (𝓝 (AVenhance.l2NormSq (fun x => Du t x i))) := tendsto_const_nhds
    simpa [e] using hconst.sub hnorm
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun t => AVenhance.l2NormSq (fun x => Du t x i)) heMeas hdom hbound hpoint
  simpa [e, μ] using hDCT

theorem WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    AEStronglyMeasurable (fun t => ‖weakFourierProjectionL2 N u t‖ ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact
    (WeakProjectionConvergence.weakFourierProjectionL2_normSq_continuousOn hu N) isCompact_Icc
        measurableSet_Ioo
    (by intro t ht; exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- The full scalar slice norm is measurable because it is the pointwise limit of the continuous
finite Fourier coefficient norms. -/
theorem WeakProjectionConvergence.weakPath_l2NormSq_aestronglyMeasurable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    AEStronglyMeasurable (fun t => AVenhance.l2NormSq (u t))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let G : ℝ → ℝ := fun t => Filter.limsup
    (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
  have hG : AEMeasurable G μ :=
    AEMeasurable.limsup (fun N =>
      (WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable hu
          N).aemeasurable)
  have hEq : G =ᵐ[μ] fun t => AVenhance.l2NormSq (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (weakFourierProjectionL2_normSq_tendsto hu t
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩).limsup_eq
  exact hG.aestronglyMeasurable.congr hEq

/-- The scalar Fourier projection errors converge strongly in time `L²`. The equality with the
cell error is the Pythagorean identity for the finite orthogonal projection. -/
theorem weakFourierProjection_scalarL2_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let e : ℕ → ℝ → ℝ := fun N t =>
    AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2
  have heMeas (N : ℕ) : AEStronglyMeasurable (e N) μ := by
    exact (WeakProjectionConvergence.weakPath_l2NormSq_aestronglyMeasurable hu).sub
      (WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable hu N)
  obtain ⟨C, hC⟩ := hu.2.1
  have hCnonneg : 0 ≤ C := by
    have hzero := hC 0 ⟨le_rfl, by norm_num⟩
    have hmem := (hu.1 0 ⟨le_rfl, by norm_num⟩).2
    rw [← weakProjection_scalarTransfer_normSq hmem] at hzero
    exact le_trans (sq_nonneg ‖(weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u 0))‖) hzero
  have hbound (N : ℕ) : ∀ᵐ t ∂μ, ‖e N t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    let v := (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))
    have hnormv : ‖v‖ ^ 2 = AVenhance.l2NormSq (u t) :=
      weakProjection_scalarTransfer_normSq (hu.1 t htcc).2
    have hprojcoeff : realFourierProjectionCoefficients N v =
        weakFourierCoefficientPath N u t := by
      rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t htcc).2]
      exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
    have hcoeffcontract : ‖realFourierProjectionCoefficients N v‖ ≤ ‖v‖ := by
      have hcoeff := realFourierModeFin_projectionCoefficients_norm_le N
        (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2)
      rw [← WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t
          htcc).2] at hcoeff
      simpa [v] using hcoeff
    have hcontract : ‖weakFourierProjectionL2 N u t‖ ≤ ‖v‖ := by
      rw [weakFourierProjectionL2, ← hprojcoeff, realFourierScalarMap_norm]
      exact hcoeffcontract
    have hprojSq : ‖weakFourierProjectionL2 N u t‖ ^ 2 ≤
        AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcontract
    have hfull : AVenhance.l2NormSq (u t) ≤ C := hC t htcc
    have hfullNonneg : 0 ≤ AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      positivity
    have herror : |e N t| ≤ C := by
      change |AVenhance.l2NormSq (u t) -
        ‖weakFourierProjectionL2 N u t‖ ^ 2| ≤ C
      apply abs_le.mpr
      constructor <;> nlinarith
    simpa [Real.norm_eq_abs] using herror
  have hdom : Integrable (fun _ : ℝ => C) μ := by
    have hs : volume (Set.Ioo (0 : ℝ) 1) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Ioo]
      norm_num
    exact integrableOn_const (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
      (C := C) hs (by simp)
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun N => e N t) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hnorm := weakFourierProjectionL2_normSq_tendsto hu t htcc
    have hconst : Tendsto (fun _ : ℕ => AVenhance.l2NormSq (u t)) atTop
        (𝓝 (AVenhance.l2NormSq (u t))) := tendsto_const_nhds
    simpa [e] using hconst.sub hnorm
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => C) heMeas hdom hbound hpoint
  simpa [e, μ] using hDCT

/-- The actual cell scalar cutoff error converges in spacetime `L²`. -/
theorem WeakProjectionConvergence.weakFourierProjection_scalarCellError_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (fun x => u t x - weakFourierModeProjection N u t x))
      atTop (𝓝 0) := by
  have hproxy := weakFourierProjection_scalarL2_time_integral_tendsto hu
  have hseq : (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x)) =ᶠ[atTop]
      fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2 := by
    filter_upwards with N
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact WeakProjectionConvergence.weakFourierProjection_scalarCellError_eq_deficit hu N
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  exact hproxy.congr' hseq.symm

/-- The actual cell weak-gradient cutoff error converges in spacetime `L²`, componentwise. -/
theorem WeakProjectionConvergence.weakFourierProjection_gradientCellError_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (i : Fin 2) :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (fun x => Du t x i -
        AVenhance.spaceGrad (weakFourierModeProjection N u t) x i))
      atTop (𝓝 0) := by
  have hproxy := weakFourierProjection_gradientComponent_time_integral_tendsto hu i
  have hseq : (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => Du t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i)) =ᶠ[atTop]
      fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => Du t x i) -
          ‖weakFourierProjectionGradientL2 N u t i‖ ^ 2 := by
    filter_upwards with N
    apply integral_congr_ae
    filter_upwards [hu.2.2.2.2.1] with t ht
    exact WeakProjectionConvergence.weakFourierProjection_gradientCellError_eq_deficit ht N i
  exact hproxy.congr' hseq.symm

/-- Real Fourier projection of a weak path converges strongly in spacetime `H¹`:
the squared time integral of the cell value error plus both weak-gradient component errors tends
to zero. -/
theorem weakFourierProjection_strong_H1_time_convergence
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    Tendsto (fun N =>
      (∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x)) +
      ∑ i : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => Du t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i))
      atTop (𝓝 0) := by
  have hvalue := weakFourierProjection_scalarCellError_time_integral_tendsto hu
  have hgradient : Tendsto (fun N => ∑ i : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => Du t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i))
      atTop (𝓝 (∑ _ : Fin 2, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro i hi
    exact WeakProjectionConvergence.weakFourierProjection_gradientCellError_time_integral_tendsto
        hu i
  simpa using hvalue.add hgradient

end AVenhance.Infra.Parabolic.WeakUniqueness

end
