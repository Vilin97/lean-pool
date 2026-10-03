/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.SolutionIntegrability

/-!
# Common Fourier weak-derivative identities for the physical limit representative

The synchronized product limit gives a single full-measure set on which the scalar and gradient
representatives satisfy the distributional derivative relation for every real Fourier mode.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance scalarFourierDerivativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarFourierDerivativeIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarFourierDerivativeProbabilityCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance scalarFourierDerivativeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def ScalarFourierDerivative.scalarFourierDerivativeClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem ScalarFourierDerivative.scalarFourierDerivativeClosedCell_compact :
    IsCompact ScalarFourierDerivative.scalarFourierDerivativeClosedCell := by
  simpa [ScalarFourierDerivative.scalarFourierDerivativeClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem ScalarFourierDerivative.scalarFourierDerivative_cube_subset_closedCell :
    AVenhance.unitCube ⊆ ScalarFourierDerivative.scalarFourierDerivativeClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, ScalarFourierDerivative.scalarFourierDerivativeClosedCell,
    Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem ScalarFourierDerivative.scalarFourierDerivative_smooth_memL2On {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : MemL2On AVenhance.unitCube ψ := by
  apply (memLp_two_iff_integrable_sq hψ.continuous.measurable.aestronglyMeasurable).2
  exact (hψ.continuous.pow 2).continuousOn.integrableOn_compact
    ScalarFourierDerivative.scalarFourierDerivativeClosedCell_compact |>.mono_set
      ScalarFourierDerivative.scalarFourierDerivative_cube_subset_closedCell

theorem ScalarFourierDerivative.smoothPeriodicTestL2_ae_periodicToTorus {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
    (fun y : Torus => smoothPeriodicTestL2 hψ hperiodic y) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus ψ := by
  have hmem := frozenInitialData_memLp_torus
    (ScalarFourierDerivative.scalarFourierDerivative_smooth_memL2On hψ)
  have hcoe := hmem.coeFn_toLp
  simpa [smoothPeriodicTestL2] using hcoe

/-- The torus gradient pairing against a smooth periodic scalar test is the cell pairing
with the synchronized Euclidean representative. -/
theorem synchronizedGradientRepresentative_pairing_eq_cell_integral
    (G : GradientProductTimeL2) (t : ℝ)
    (hsection : MemLp (fun y : Torus => G (t, y)) 2 (volume : Measure Torus))
    (i : Fin 2) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ∫ y : Torus, inner ℝ (G (t, y))
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic) y) =
      ∫ x in AVenhance.unitCube,
        synchronizedGradientRepresentative G t x i * ψ x := by
  let test : ScalarTorusL2 := smoothPeriodicTestL2 hψ hperiodic
  let vectorTest : SpatialGradientL2 := scalarToSpatialGradientL2 i test
  have hslice := gradientProductTimeL2_slice_coeFn G t hsection
  have htest := ScalarFourierDerivative.smoothPeriodicTestL2_ae_periodicToTorus hψ hperiodic
  have hvec : (fun y : Torus => vectorTest y) =ᵐ[volume]
      fun y => WithLp.toLp 2 (Pi.single i (test y)) := by
    change (fun y => (scalarToSpatialVector i).compLp test y) =ᵐ[volume] _
    exact (scalarToSpatialVector i).coeFn_compLp test
  have hrep (y : Torus) :
      AVenhance.Infra.Torus.periodicToTorus
        (fun x : Vec 2 => synchronizedGradientRepresentative G t x i) y = G (t, y) i := by
    change G (t, AVenhance.Infra.Torus.toUnitTorus 2
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)) i = G (t, y) i
    rw [AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative]
  calc
    ∫ y : Torus, inner ℝ (G (t, y)) (vectorTest y) =
        ∫ y : Torus, inner ℝ (gradientProductTimeL2Slice G t y) (vectorTest y) := by
          apply integral_congr_ae
          filter_upwards [hslice] with y hGy
          rw [hGy]
    _ = inner ℝ (gradientProductTimeL2Slice G t) vectorTest :=
          (MeasureTheory.L2.inner_def _ _).symm
    _ = ∫ y : Torus, G (t, y) i * test y := by
          apply integral_congr_ae
          filter_upwards [hslice, hvec] with y hGy htesty
          rw [hGy, htesty, PiLp.inner_apply]
          simp [Pi.single_apply]
          ring
    _ = ∫ y : Torus,
        AVenhance.Infra.Torus.periodicToTorus
          (fun x : Vec 2 => synchronizedGradientRepresentative G t x i * ψ x) y := by
          apply integral_congr_ae
          filter_upwards [htest] with y hy
          rw [show AVenhance.Infra.Torus.periodicToTorus
            (fun x : Vec 2 => synchronizedGradientRepresentative G t x i * ψ x) y =
              AVenhance.Infra.Torus.periodicToTorus
                  (fun x : Vec 2 => synchronizedGradientRepresentative G t x i) y *
                AVenhance.Infra.Torus.periodicToTorus ψ y by rfl]
          rw [hrep y, hy]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
        synchronizedGradientRepresentative G t x i * ψ x := by
          rw [← AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell]
    _ = ∫ x in AVenhance.unitCube,
        synchronizedGradientRepresentative G t x i * ψ x :=
          AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _

theorem ScalarFourierDerivative.realFourierModeAmbient_contDiff_withTop (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (realFourierModeAmbient N
      ((realFourierIndexEquivFin N).symm j)) := by
  exact (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm j)).of_le le_top

theorem ScalarFourierDerivative.scalarFourierDerivative_clamp_eq {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : clampTimeToUnit t = ⟨t, ht⟩ := by
  apply Subtype.ext
  simp [clampTimeToUnit, max_eq_left ht.1, min_eq_left ht.2]

/-- The physical scalar and gradient representatives obey all real Fourier weak-derivative tests
on one common full-measure set of times. -/
theorem FrozenDriftProblem.synchronized_limit_cell_realFourier_derivative_ae
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (S : Set ℝ) (hS : ∀ t ∈ S, synchronizedScalarSliceGood Uprod u t)
    (hSae : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    (hUbound : ∀ t, ‖u t‖ ≤ P.scalarBound) :
    ∀ᵐ t ∂GalerkinTimeMeasure, ∀ i : Fin 2, ∀ N : ℕ,
      ∀ j : Fin (RealFourierDimension N),
        ∫ x in AVenhance.unitCube,
          synchronizedScalarRepresentative Uprod u S t x *
            AVenhance.spaceGrad
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
        -∫ x in AVenhance.unitCube,
          synchronizedGradientRepresentative Gprod t x i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm j) x := by
  have hfourier := P.synchronized_limit_realFourier_derivative_ae σ u Uprod Gprod
    hPathWeak hUweak hGweak hUcont hUbound
  have hsections := gradientProductTimeL2_memLp_sections Gprod
  have htime : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ Ioc (0 : ℝ) 1 := by
    exact ae_restrict_mem (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
  filter_upwards [hfourier, hsections, hSae, htime] with
    t hfourier_t hsection_t htS htIoc
  intro i N j
  let ψ : Vec 2 → ℝ := realFourierModeAmbient N
    ((realFourierIndexEquivFin N).symm j)
  let hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := by
    simpa [ψ] using ScalarFourierDerivative.realFourierModeAmbient_contDiff_withTop N j
  let hperiodic : AVenhance.IsZ2Periodic ψ := by
    exact realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm j)
  let hDψ := productWeakGradient_coord_contDiff hψ i
  let hDperiodic := productWeakGradient_coord_periodic hψ hperiodic i
  have htorus := hfourier_t i N j
  have hgrad := synchronizedGradientRepresentative_pairing_eq_cell_integral
    Gprod t hsection_t i hψ hperiodic
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hscalar := synchronizedScalarRepresentative_pairing_eq_inner
    Uprod u S hS htcc hDψ hDperiodic
  rw [hgrad] at htorus
  rw [ScalarFourierDerivative.scalarFourierDerivative_clamp_eq htcc] at htorus
  rw [← hscalar] at htorus
  dsimp [ψ] at htorus ⊢
  linarith

end AVenhance.Infra.Parabolic.FourierGalerkin

end
