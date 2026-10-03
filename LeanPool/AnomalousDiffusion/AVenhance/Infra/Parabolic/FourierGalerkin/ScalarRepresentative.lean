/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductGradientRepresentative
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A pointwise scalar representative of the synchronized limit

The product-space scalar limit supplies good spatial representatives at almost every time. A
measurable full-measure set of those slices is used to keep the physical representative measurable
while retaining a defined periodic `L²` slice at every time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance scalarRepresentativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarRepresentativeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarRepresentativeCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance scalarRepresentativeProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- A time is good when the scalar product representative has an `L²` slice equal to the weak path.
-/
def synchronizedScalarSliceGood (U : ScalarProductTimeL2)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (t : ℝ) : Prop :=
  MemLp (fun y : Torus => U (t, y)) 2 (volume : Measure Torus) ∧
    scalarProductTimeL2Slice U t = u (clampTimeToUnit t)

/-- The good scalar slices contain a measurable full-measure set of times. -/
theorem exists_measurable_synchronizedScalarSliceGood
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (U : ScalarProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ U v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v)) :
    ∃ S : Set ℝ, MeasurableSet S ∧ (∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S) ∧
      ∀ t ∈ S, synchronizedScalarSliceGood U u t := by
  have hsection := scalarProductTimeL2_memLp_sections U
  have hslice := P.synchronized_scalar_slice_eq_path_ae σ u U
    hPathWeak hUweak hUcont
  have hnull : GalerkinTimeMeasure {t | ¬ synchronizedScalarSliceGood U u t} = 0 := by
    rw [← ae_iff]
    filter_upwards [hsection, hslice] with t htSection htSlice
    exact ⟨htSection, htSlice⟩
  obtain ⟨B, hbadSubset, hBmeas, hBzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hnull
  refine ⟨Bᶜ, hBmeas.compl, ?_, ?_⟩
  · exact MeasureTheory.compl_mem_ae_iff.mpr hBzero
  · intro t ht
    by_contra hgood
    exact ht (hbadSubset hgood)

/-- The pointwise scalar representative uses the product limit on good time slices and the
weakly continuous path on the exceptional slices. -/
noncomputable def synchronizedScalarRepresentative (U : ScalarProductTimeL2)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ) : ℝ → Vec 2 → ℝ := by
  classical
  exact fun t x => if t ∈ S then U (t, AVenhance.Infra.Torus.toUnitTorus 2 x)
    else weakPathRepresentative u t x

theorem ScalarRepresentative.synchronizedScalarRepresentative_good_slice_eq_canonical
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (S : Set ℝ) (hS : ∀ t ∈ S, synchronizedScalarSliceGood U u t)
    {t : ℝ} (ht : t ∈ S) :
    (fun x : Vec 2 => synchronizedScalarRepresentative U u S t x) =ᵐ[
      volume.restrict AVenhance.unitCube]
      scalarTorusRepresentative (scalarProductTimeL2Slice U t) := by
  let hmem := (hS t ht).1
  have hclass : scalarProductTimeL2Slice U t =
      hmem.toLp (fun y : Torus => U (t, y)) := by
    simp [scalarProductTimeL2Slice, hmem]
  have hsection := hmem.coeFn_toLp
  have hpull := measurePreserving_toUnitTorus_unitCube.quasiMeasurePreserving.ae hsection
  filter_upwards [hpull] with x hx
  have hpoint : scalarTorusRepresentative (scalarProductTimeL2Slice U t) x =
      U (t, AVenhance.Infra.Torus.toUnitTorus 2 x) := by
    change scalarProductTimeL2Slice U t (AVenhance.Infra.Torus.toUnitTorus 2 x) = _
    rw [hclass]
    exact hx
  simpa [synchronizedScalarRepresentative, scalarTorusRepresentative,
    AVenhance.Infra.Torus.fromUnitTorus, ht] using hpoint.symm

/-- Every time slice of the representative is periodic and belongs to the cell `L²`
space; its cell norm is bounded by the path bound. -/
theorem synchronizedScalarRepresentative_pointwise_clauses
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hS : ∀ t ∈ S, synchronizedScalarSliceGood U u t)
    (hbound : ∀ t, ‖u t‖ ≤ B) :
    (∀ t ∈ Icc (0 : ℝ) 1,
      AVenhance.IsZ2Periodic (synchronizedScalarRepresentative U u S t) ∧
        MemL2On AVenhance.unitCube (synchronizedScalarRepresentative U u S t)) ∧
      ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
        AVenhance.l2NormSq (synchronizedScalarRepresentative U u S t) ≤ C := by
  classical
  refine ⟨?_, B ^ 2, ?_⟩
  · intro t ht
    by_cases hgood : t ∈ S
    · have hslice := hS t hgood
      have hperiodic : AVenhance.IsZ2Periodic
          (synchronizedScalarRepresentative U u S t) := by
        have hfun : synchronizedScalarRepresentative U u S t =
            AVenhance.Infra.Torus.fromUnitTorus (fun y : Torus => U (t, y)) := by
          funext x
          simp [synchronizedScalarRepresentative, hgood,
            AVenhance.Infra.Torus.fromUnitTorus]
        rw [hfun]
        exact (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).1
          (AVenhance.Infra.Torus.isZdPeriodic_fromUnitTorus (fun y => U (t, y)))
      have hmem : MemL2On AVenhance.unitCube
          (synchronizedScalarRepresentative U u S t) := by
        have hpull := hslice.1.comp_measurePreserving
          measurePreserving_toUnitTorus_unitCube
        change MemLp (fun x : Vec 2 =>
          synchronizedScalarRepresentative U u S t x) 2
          (volume.restrict AVenhance.unitCube)
        simpa [synchronizedScalarRepresentative, hgood,
          AVenhance.Infra.Torus.fromUnitTorus, Function.comp_def] using hpull
      exact ⟨hperiodic, hmem⟩
    · have hfun : synchronizedScalarRepresentative U u S t = weakPathRepresentative u t := by
        funext x
        simp [synchronizedScalarRepresentative, hgood]
      rw [hfun]
      exact ⟨weakPathRepresentative_isPeriodic u t,
        weakPathRepresentative_memL2On u ⟨t, ht⟩⟩
  · intro t ht
    by_cases hgood : t ∈ S
    · have hslice := hS t hgood
      have hrep : (fun x : Vec 2 => synchronizedScalarRepresentative U u S t x) =ᵐ[
          volume.restrict AVenhance.unitCube]
          scalarTorusRepresentative (scalarProductTimeL2Slice U t) :=
        ScalarRepresentative.synchronizedScalarRepresentative_good_slice_eq_canonical U u S hS hgood
      calc
        AVenhance.l2NormSq (synchronizedScalarRepresentative U u S t) =
            AVenhance.l2NormSq (scalarTorusRepresentative
              (scalarProductTimeL2Slice U t)) := by
                rw [AVenhance.l2NormSq]
                apply integral_congr_ae
                filter_upwards [hrep] with x hx
                rw [hx]
        _ = ‖scalarProductTimeL2Slice U t‖ ^ 2 :=
          scalarTorusRepresentative_l2NormSq _
        _ = ‖u (clampTimeToUnit t)‖ ^ 2 := by rw [hslice.2]
        _ ≤ B ^ 2 := by
          exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound (clampTimeToUnit t))
    · have hfun : synchronizedScalarRepresentative U u S t = weakPathRepresentative u t := by
        funext x
        simp [synchronizedScalarRepresentative, hgood]
      rw [hfun, weakPathRepresentative_l2NormSq u ⟨t, ht⟩]
      exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound ⟨t, ht⟩)

/-- The representative is in the exact scalar space-time `L²` carrier. -/
theorem synchronizedScalarRepresentative_memLp_timeCube
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (hSmeas : MeasurableSet S) (hSae : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S) :
    MemLp (fun p : ℝ × Vec 2 =>
      synchronizedScalarRepresentative U u S p.1 p.2) 2
      (volume.restrict AVenhance.timeCube) := by
  let μ := GalerkinTimeMeasure.prod (volume : Measure Torus)
  have hSprod : ∀ᵐ q ∂μ, q.1 ∈ S := by
    have hprod : ∀ᵐ q ∂μ, q ∈ S ×ˢ (Set.univ : Set Torus) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem
        (hSmeas.prod MeasurableSet.univ)]
      filter_upwards [hSae] with t ht
      filter_upwards with x
      exact ⟨ht, Set.mem_univ x⟩
    filter_upwards [hprod] with q hq
    exact hq.1
  have hSphysical :=
    measurePreserving_physicalTimeTorusMap.quasiMeasurePreserving.ae hSprod
  have hrepEq : (fun p : ℝ × Vec 2 =>
      synchronizedScalarRepresentative U u S p.1 p.2) =ᵐ[
        volume.restrict AVenhance.timeCube]
      fun p => U (physicalTimeTorusMap p) := by
    filter_upwards [hSphysical] with p hp
    have hp' : p.1 ∈ S := by simpa [physicalTimeTorusMap] using hp
    simp [synchronizedScalarRepresentative, physicalTimeTorusMap, hp']
  have hraw : MemLp (fun p : ℝ × Vec 2 => U (physicalTimeTorusMap p)) 2
      (volume.restrict AVenhance.timeCube) :=
    (Lp.memLp U).comp_measurePreserving measurePreserving_physicalTimeTorusMap
  exact (memLp_congr_ae hrepEq).2 hraw

theorem ScalarRepresentative.clampTimeToUnit_eq_of_mem_Icc {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    clampTimeToUnit t = ⟨t, ht⟩ := by
  apply Subtype.ext
  simp [clampTimeToUnit, max_eq_left ht.1, min_eq_left ht.2]

/-- On almost every physical spacetime point, the selected scalar representative is the pullback
of the synchronized product-space limit. -/
theorem synchronizedScalarRepresentative_pullback_ae
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (hSmeas : MeasurableSet S) (hSae : ∀ᵐ t ∂GalerkinTimeMeasure, t ∈ S) :
    (fun p : ℝ × Vec 2 => synchronizedScalarRepresentative U u S p.1 p.2) =ᵐ[
      volume.restrict AVenhance.timeCube]
      fun p => U (physicalTimeTorusMap p) := by
  have hSprod : ∀ᵐ q ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)), q.1 ∈ S := by
    have hprod : ∀ᵐ q ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)),
        q ∈ S ×ˢ (Set.univ : Set Torus) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (hSmeas.prod MeasurableSet.univ)]
      filter_upwards [hSae] with t ht
      filter_upwards with x
      exact ⟨ht, Set.mem_univ x⟩
    filter_upwards [hprod] with q hq
    exact hq.1
  have hSphysical :=
    measurePreserving_physicalTimeTorusMap.quasiMeasurePreserving.ae hSprod
  filter_upwards [hSphysical] with p hp
  have hp' : p.1 ∈ S := by simpa [physicalTimeTorusMap] using hp
  simp [synchronizedScalarRepresentative, physicalTimeTorusMap, hp']

/-- Every spatial smooth periodic pairing of the selected physical representative is exactly the
pairing of the weakly continuous torus path, including exceptional and endpoint times. -/
theorem synchronizedScalarRepresentative_pairing_eq_inner
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (hS : ∀ t ∈ S, synchronizedScalarSliceGood U u t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube,
      synchronizedScalarRepresentative U u S t x * ψ x =
        inner ℝ (u ⟨t, ht⟩) (smoothPeriodicTestL2 hψ hperiodic) := by
  classical
  by_cases hgood : t ∈ S
  · have hslice := hS t hgood
    have hpath : scalarProductTimeL2Slice U t = u ⟨t, ht⟩ := by
      rw [hslice.2, ScalarRepresentative.clampTimeToUnit_eq_of_mem_Icc ht]
    have hrep := ScalarRepresentative.synchronizedScalarRepresentative_good_slice_eq_canonical U u
        S hS hgood
    calc
      ∫ x in AVenhance.unitCube,
          synchronizedScalarRepresentative U u S t x * ψ x =
        ∫ x in AVenhance.unitCube,
          scalarTorusRepresentative (scalarProductTimeL2Slice U t) x * ψ x := by
            apply integral_congr_ae
            filter_upwards [hrep] with x hx
            rw [hx]
      _ = ∫ x in AVenhance.unitCube,
          weakPathRepresentative u t x * ψ x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hpath]
            simp [weakPathRepresentative, ht]
      _ = inner ℝ (u ⟨t, ht⟩) (smoothPeriodicTestL2 hψ hperiodic) :=
        weakPathRepresentative_pairing_eq_inner u ⟨t, ht⟩ hψ hperiodic
  · have hfun : synchronizedScalarRepresentative U u S t =
        weakPathRepresentative u t := by
      funext x
      simp [synchronizedScalarRepresentative, hgood]
    rw [hfun]
    exact weakPathRepresentative_pairing_eq_inner u ⟨t, ht⟩ hψ hperiodic

/-- Smooth periodic spatial pairings of the selected representative are continuous on the closed
time interval. -/
theorem synchronizedScalarRepresentative_testPairing_continuous
    (U : ScalarProductTimeL2) (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (hS : ∀ t ∈ S, synchronizedScalarSliceGood U u t)
    (hweakContinuous : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
  ContinuousOn (fun t => ∫ x in AVenhance.unitCube,
      synchronizedScalarRepresentative U u S t x * ψ x) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.congr
    (weakPathRepresentative_testPairing_continuous u hweakContinuous hψ hperiodic)
  intro t ht
  exact (synchronizedScalarRepresentative_pairing_eq_inner U u S hS ht hψ hperiodic).trans
    (weakPathRepresentative_pairing_eq_inner u (⟨t, ht⟩ : Icc (0 : ℝ) 1)
      hψ hperiodic).symm

end AVenhance.Infra.Parabolic.FourierGalerkin

end
