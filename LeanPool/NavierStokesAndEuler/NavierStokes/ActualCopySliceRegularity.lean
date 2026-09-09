/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCoreSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling

/-!
# Continuity on the actual finite tangent-copy intervals

The projected operator is built from the selected frame's normal, normal
motion, base action, and damping. Only the native slow point and finite
clock interval enter its regularity; the transverse coordinate is free.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCopySliceRegularity

open Set Function Filter
open CommonCoverSolve PhaseJetBounds PrimaryPulseBounds
open CorrectionInitialization
open scoped ContDiff Topology InnerProductSpace


/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Parameter: an abbreviation for `PhysicalParticularWave.Parameter`. -/
abbrev Parameter := PhysicalParticularWave.Parameter
/-- Label: an abbreviation for `ActualParticularStageControls.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualParticularStageControls.Label B N0

theorem negativeProjection_continuousOn {X : Type*} [TopologicalSpace X]
    {U : Set X} {N : X → Space} (hN : ContinuousOn N U)
    (hne : ∀ x ∈ U, N x ≠ 0) :
    ContinuousOn (fun x => negativeTangentProjection (N x)) U := by
  have hv : ContinuousOn (fun x => (⟪N x, N x⟫_ℝ)⁻¹ • N x) U :=
    ((hN.inner hN).inv₀ (fun x hx => inner_self_ne_zero.mpr (hne x hx))).fun_smul hN
  have hi := (innerSL ℝ).continuous.comp_continuousOn hN
  exact (continuousOn_const.sub
    (isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (hi.prodMk hv))).neg

section Frame

variable {ι : Type} {D : Domain ι PhaseCalculus.Slow}

/-- The actual ambient projected operator and forcing projection of the
selected frame are continuous on the entire closed slot. -/
theorem frame_slices (F : PhaseConstruction D) (i : ι) (j : ℤ)
    (p : PhaseCalculus.Slow) (hp : p ∈ D.carrier i) :
    Continuous (fun s : Icc (0 : ℝ) (F.L i) =>
      TangentODE.projectedOperator ((F.frame i).normal (p, s))
        ((F.frame i).normalMotion (p, s))
        (PrimaryCopyBridge.baseOperator ((F.frame i).F (p, s)) ((F.frame i).shear (p, s)))
        ((F.frame i).damping j (p, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (F.L i) => negativeTangentProjection ((F.frame i).normal (p,
        s))) := by
  have hd := (ActualParticularControl.selected_frame_jets F).smoothOn i
  have hmap : MapsTo (fun s : ℝ => (p, s)) (Icc 0 (F.L i)) ((D.slot F.V F.openV).carrier i) :=
    fun s hs => ⟨hp, F.interval i hs⟩
  have hn := (PrimaryCopyBridge.frame_normal_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hnd := (PrimaryCopyBridge.frame_normalMotion_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hA := (PrimaryCopyBridge.frame_baseOperator_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hδ : ContinuousOn (fun s : ℝ => (F.frame i).damping j (p, s)) (Icc 0 (F.L i)) :=
    (continuousOn_const.mul hd.viscosity.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hne : ∀ s ∈ Icc 0 (F.L i), (F.frame i).normal (p, s) ≠ 0 := by
    intro s hs
    exact MovingFrameODE.normal_ne_zero _
      ((ActualParticularControl.selected_kinematics F i hp).beta_ne_zero s hs)
  exact ⟨(PrimaryCopyBridge.projectedOperator_continuousOn hn hnd hA hδ hne).domRestrict,
    (negativeProjection_continuousOn hn hne).domRestrict⟩

end Frame

section Transport

variable {P Q : Type}

theorem transported_coefficient (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal : ℝ) (hn : normal ≠ 0) (q : Q) (Y : Plane) :
    (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
        normal).linearData.coefficient (q, Y) =
      rate • t.linearData.coefficient (φ q, CopySolveCompatibility.nativeTimeMap 0 rate Y) :=
  NormalScaling.projectedOperator_rescale _ _ _ rate _ hn

theorem transported_forcingMap (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal : ℝ) (hn : normal ≠ 0) (q : Q) (Y : Plane) :
    (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude normal).linearData.forcingMap
        (q, Y) =
      t.linearData.forcingMap (φ q, CopySolveCompatibility.nativeTimeMap 0 rate Y) :=
  NormalScaling.negativeTangentProjection_smul _ hn

theorem transported_slices (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal L : ℝ) (hrate : 0 < rate) (hn : normal ≠ 0)
    (q : Q) (xi : ℝ)
    (hA : Continuous (fun s : Icc (0 : ℝ) L => t.linearData.coefficient (φ q, (xi, s))))
    (hB : Continuous (fun s : Icc (0 : ℝ) L => t.linearData.forcingMap (φ q, (xi, s)))) :
    Continuous (fun s : Icc (0 : ℝ) (L / rate) =>
      (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
          normal).linearData.coefficient (q, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (L / rate) =>
      (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
          normal).linearData.forcingMap (q, (xi, s))) := by
  let clock : Icc (0 : ℝ) (L / rate) → Icc (0 : ℝ) L := fun s =>
    ⟨rate * s, mul_nonneg hrate.le s.property.1,
      by simpa only [mul_comm] using (le_div_iff₀ hrate).mp s.property.2⟩
  have hc : Continuous clock :=
    Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  constructor
  · apply ((hA.comp hc).fun_const_smul rate).congr
    intro s
    simpa only [Function.comp_apply, clock, CopySolveCompatibility.nativeTimeMap, zero_add] using
      (transported_coefficient t φ gap rate amplitude normal hn q (xi, s)).symm
  · apply (hB.comp hc).congr
    intro s
    simpa only [Function.comp_apply, clock, CopySolveCompatibility.nativeTimeMap, zero_add] using
      (transported_forcingMap t φ gap rate amplitude normal hn q (xi, s)).symm

end Transport

section Actual

open ActualParticularStageControls

variable {B N0 : ℕ}

theorem reference_slices (l : Label B N0) (j : ℤ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter p ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) (reference l).length =>
      ((reference l).tangent j).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (reference l).length =>
      ((reference l).tangent j).linearData.forcingMap (p, (xi, s))) :=
  frame_slices (ActualPrimary.phases B N0 l.1) l.2 j (ActualSignedGeometry.swapParameter p) hp

theorem normalWeight_ne (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (reference l).band)
      ((j : ℝ) * ChartScales.carrier ActualPrimary.h n)
      ((j : ℝ) * ChartScales.carrier ActualPrimary.h (reference l).band) ≠ 0 := by
  rw [ScaledActualParticularControl.normalWeight_harmonic _ _ _ _ j hj]
  apply mul_ne_zero
  · exact div_ne_zero (ActualPrimary.chartCoefficients_frequency_pos l.1 l.2 _).ne'
      (ActualPrimary.chartCoefficients_frequency_pos l.1 l.2 _).ne'
  · exact (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _).ne'

/-- No transverse or copy restriction occurs in these two primitive slice
continuities. The only spatial hypothesis is the actual native phase cell. -/
theorem canonical_slices (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) ((canonicalParameters l).length n) =>
      ((canonicalParameters l).tangent j n).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) ((canonicalParameters l).length n) =>
      ((canonicalParameters l).tangent j n).linearData.forcingMap (p, (xi, s))) := by
  obtain ⟨hA, hB⟩ := reference_slices l j _ hp xi
  exact transported_slices ((reference l).tangent j) _ _ _ _ _ _
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _)
    (normalWeight_ne l j hj n) p xi hA hB

theorem actual_slices (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap (p, (xi, s))) := by
  rw [parameters_eq_canonical x l hfrequency]
  exact canonical_slices l j hj n p hp xi

theorem actual_copy_slices (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (Y : Plane) (k : TorusInverse.Frequency) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficientAlong ((parameters x l).geometry n) k
          ((p, Y), s)) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap
        (p, ((((parameters x l).geometry n).coordinates k Y).1, s))) :=
  actual_slices x l hfrequency j hj n p hp _

end Actual

section SourceFiber

open ActualParticularStageControls

variable {B N0 : ℕ}

theorem native_parameter_eq (l : Label B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) =
      ActualPrimaryCovariance.nativePoint n (p.1, (p.2, Y)) l.2 := by
  ext <;> simp [ActualSignedGeometry.swapParameter, PhysicalParticularWave.parameterChange,
    PhysicalParticularWave.ratioPower, ActualPrimaryCovariance.nativePoint,
    ActualPrimary.nativeSlow, ActualPrimary.toAbsolute, reference, Real.sqrt_eq_rpow,
    div_eq_mul_inv, mul_assoc, mul_comm]

theorem native_cell_of_refinedCarrier (l : Label B N0) (n : ℕ) (p : Parameter)
    (hT : 0 < p.2.1) {Y : Plane}
    (hY : (p.1, (p.2, Y)) ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2 := by
  rw [native_parameter_eq l n p Y]
  exact ActualCarrierGeometry.labelCarrier_in_cell l n hT
    (ActualCoreSupport.refinedCarrier_subset_broad (l.2, l.1) n hY)

/-- A nonempty refined source fiber supplies the native phase-cell
hypothesis. All copies and every transverse coordinate are then covered. -/
theorem actual_copy_slices_of_refinedFiber (x : CorrectionStep.CycleState (Label B N0)) (l : Label
    B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter) (hT : 0 < p.2.1)
    (hs : ∃ Z : Plane, (p.1, (p.2, Z)) ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n)
    (Y : Plane) (k : TorusInverse.Frequency) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficientAlong ((parameters x l).geometry n) k
          ((p, Y), s)) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap
        (p, ((((parameters x l).geometry n).coordinates k Y).1, s))) := by
  obtain ⟨Z, hZ⟩ := hs
  exact actual_copy_slices x l hfrequency j hj n p (native_cell_of_refinedCarrier l n p hT hZ) Y k

end SourceFiber

end NavierStokes.ActualCopySliceRegularity
