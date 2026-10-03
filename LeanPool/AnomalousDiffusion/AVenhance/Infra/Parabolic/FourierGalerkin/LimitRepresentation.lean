/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.SpacetimeCompactness
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq

/-!
# Physical representatives of weak scalar paths

Pulling a torus `L²` class back to the Euclidean covering space gives a periodic representative
with the exact unit-cell `L²` norm. These bridges are the pointwise-in-time part of the
eventual `IsWeakSolutionGrad` assembly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Topology
open Homogenization
open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance representationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance representationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance representationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def LimitRepresentation.representationClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem LimitRepresentation.representationClosedCell_compact : IsCompact
    LimitRepresentation.representationClosedCell := by
  simpa [LimitRepresentation.representationClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem LimitRepresentation.unitCube_subset_representationClosedCell :
    AVenhance.unitCube ⊆ LimitRepresentation.representationClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i _
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem LimitRepresentation.smoothPeriodicTest_memL2On {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : MemL2On AVenhance.unitCube ψ := by
  apply (memLp_two_iff_integrable_sq hψ.continuous.measurable.aestronglyMeasurable).2
  exact (hψ.continuous.pow 2).continuousOn.integrableOn_compact
    LimitRepresentation.representationClosedCell_compact |>.mono_set
        LimitRepresentation.unitCube_subset_representationClosedCell

/-- The torus `L²` class associated with a smooth periodic Euclidean test function. -/
noncomputable def smoothPeriodicTestL2 {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_hperiodic : AVenhance.IsZ2Periodic ψ) : ScalarTorusL2 :=
  (frozenInitialData_memLp_torus (LimitRepresentation.smoothPeriodicTest_memL2On hψ)).toLp
    (AVenhance.Infra.Torus.periodicToTorus ψ)

/-- The canonical periodic representative of a real torus `L²` class. -/
def scalarTorusRepresentative (f : ScalarTorusL2) : Vec 2 → ℝ :=
  AVenhance.Infra.Torus.fromUnitTorus fun x => f x

theorem scalarTorusRepresentative_periodic (f : ScalarTorusL2) :
    AVenhance.IsZ2Periodic (scalarTorusRepresentative f) := by
  exact (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).1
    (AVenhance.Infra.Torus.isZdPeriodic_fromUnitTorus (fun x => f x))

/-- A torus `L²` class pulls back to the open-cell `L²` carrier. -/
theorem scalarTorusRepresentative_memL2On (f : ScalarTorusL2) :
    MemL2On AVenhance.unitCube (scalarTorusRepresentative f) := by
  let cell : Set (Vec 2) := AVenhance.Infra.Torus.unitCell 2
  let cellSubtype := {x : Vec 2 // x ∈ cell}
  let cellMeasure : Measure cellSubtype := volume.comap (Subtype.val : cellSubtype → Vec 2)
  let equiv := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hcellMeas : MeasurableSet cell := AVenhance.Infra.Torus.measurableSet_unitCell 2
  have hmeasureCell : MeasurePreserving (fun x : cellSubtype => (x : Vec 2))
      cellMeasure ((volume : Measure (Vec 2)).restrict cell) := by
    change MeasurePreserving Subtype.val
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
      ((volume : Measure (Vec 2)).restrict cell)
    exact ⟨measurable_subtype_coe, map_comap_subtype_coe hcellMeas volume⟩
  have hmeasureTorus : MeasurePreserving equiv (volume : Measure Torus) cellMeasure := by
    change MeasurePreserving equiv (volume : Measure Torus)
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
    simpa [equiv, cell, AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt] using
      UnitAddTorus.measurePreserving_equivPiIoc (a := fun _ : Fin 2 => (0 : ℝ))
  have hsub : MemLp
      (fun x : cellSubtype => (fun y : Vec 2 => scalarTorusRepresentative f y) x.1)
      2 cellMeasure := by
    have htorus : MemLp (fun x : Torus => f x) 2 (volume : Measure Torus) := Lp.memLp f
    have hcomp := htorus.comp_measurePreserving hmeasureTorus.symm
    have hequiv (x : cellSubtype) : equiv.symm x =
        AVenhance.Infra.Torus.toUnitTorus 2 x.1 := by
      apply equiv.injective
      apply Subtype.ext
      funext i
      rfl
    have heq : (fun x : cellSubtype => (fun y : Vec 2 => scalarTorusRepresentative f y) x.1) =
        (fun x : cellSubtype => (fun z : Torus => f z) (equiv.symm x)) := by
      funext x
      simp [scalarTorusRepresentative, AVenhance.Infra.Torus.fromUnitTorus, hequiv]
    rw [heq]
    exact hcomp
  have hbase : MemLp (scalarTorusRepresentative f) 2
      ((volume : Measure (Vec 2)).restrict cell) := by
    rw [← hmeasureCell.map_eq]
    exact (MeasurableEmbedding.subtype_coe hcellMeas).memLp_map_measure_iff.mpr hsub
  have hcellLe : (volume : Measure (Vec 2)).restrict cell ≤
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube :=
    Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.le
  have hcubeLe : (volume : Measure (Vec 2)).restrict AVenhance.unitCube ≤
      (volume : Measure (Vec 2)).restrict cell :=
    Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.ge
  exact hbase.mono_measure hcubeLe

/-- The `l2NormSq` of a pulled-back torus class is its Hilbert norm squared. -/
theorem scalarTorusRepresentative_l2NormSq (f : ScalarTorusL2) :
    AVenhance.l2NormSq (scalarTorusRepresentative f) = ‖f‖ ^ 2 := by
  have hcell : ∫ x in AVenhance.Infra.Torus.unitCell 2,
      scalarTorusRepresentative f x ^ 2 = ∫ x : Torus, (f x) ^ 2 := by
    simpa [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
      scalarTorusRepresentative, AVenhance.Infra.Torus.fromUnitTorus] using
      (AVenhance.Infra.Torus.integral_fromUnitTorus_eq_unitCellAt
        (fun x : Torus => (f x) ^ 2) (fun _ : Fin 2 => 0)).symm
  calc
    AVenhance.l2NormSq (scalarTorusRepresentative f) =
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          scalarTorusRepresentative f x ^ 2 := by
            rw [AVenhance.l2NormSq, ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
    _ = ∫ x : Torus, (f x) ^ 2 := hcell
    _ = ‖f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.norm_eq_abs, sq_abs]

/-- The weakly continuous torus path, represented periodically at every real time. Outside the
closed solution interval its representative is set to zero. -/
def weakPathRepresentative (u : Icc (0 : ℝ) 1 → ScalarTorusL2) : ℝ → Vec 2 → ℝ :=
  fun t x => if ht : t ∈ Icc (0 : ℝ) 1 then
    scalarTorusRepresentative (u ⟨t, ht⟩) x else 0

theorem weakPathRepresentative_isPeriodic (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (t : ℝ) : AVenhance.IsZ2Periodic (weakPathRepresentative u t) := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u ⟨t, ht⟩) := by
      funext x
      simp [weakPathRepresentative, ht]
    rw [hfun]
    exact scalarTorusRepresentative_periodic (u ⟨t, ht⟩)
  · have hfun : weakPathRepresentative u t = fun _ : Vec 2 => 0 := by
      funext x
      simp [weakPathRepresentative, ht]
    rw [hfun]
    intro k x
    rfl

theorem weakPathRepresentative_memL2On (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (t : Icc (0 : ℝ) 1) :
    MemL2On AVenhance.unitCube (weakPathRepresentative u t) := by
  have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
    funext x
    simp [weakPathRepresentative, t.property]
  rw [hfun]
  exact scalarTorusRepresentative_memL2On (u t)

theorem weakPathRepresentative_l2NormSq (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (t : Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (weakPathRepresentative u t) = ‖u t‖ ^ 2 := by
  have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
    funext x
    simp [weakPathRepresentative, t.property]
  rw [hfun]
  exact scalarTorusRepresentative_l2NormSq (u t)

/-- Pairing the physical representative with a smooth periodic test is exactly the torus Hilbert
pairing. -/
theorem weakPathRepresentative_pairing_eq_inner
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (t : Icc (0 : ℝ) 1)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube, weakPathRepresentative u t x * ψ x =
      inner ℝ (u t) (smoothPeriodicTestL2 hψ hperiodic) := by
  let ψT : ScalarTorusL2 := smoothPeriodicTestL2 hψ hperiodic
  have htest : (fun x : Torus => ψT x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus ψ :=
    (frozenInitialData_memLp_torus (LimitRepresentation.smoothPeriodicTest_memL2On hψ)).coeFn_toLp
  have htheta (x : Torus) :
      AVenhance.Infra.Torus.periodicToTorus (weakPathRepresentative u t) x = u t x := by
    have hrep : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
      funext y
      simp [weakPathRepresentative, t.property]
    rw [hrep]
    exact congrFun
      (AVenhance.Infra.Torus.periodicToTorus_fromUnitTorus (fun y : Torus => u t y)) x
  calc
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          weakPathRepresentative u t x * ψ x :=
        (AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _).symm
    _ = ∫ x : Torus,
          AVenhance.Infra.Torus.periodicToTorus
            (fun y : Vec 2 => weakPathRepresentative u t y * ψ y) x :=
        (AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _).symm
    _ = ∫ x : Torus, (u t x) * ψT x := by
      apply integral_congr_ae
      filter_upwards [htest] with x hx
      rw [show AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => weakPathRepresentative u t y * ψ y) x =
          AVenhance.Infra.Torus.periodicToTorus (weakPathRepresentative u t) x *
            AVenhance.Infra.Torus.periodicToTorus ψ x from rfl,
        htheta x, hx]
    _ = ∫ x : Torus, inner ℝ (u t x) (ψT x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [mul_comm]
    _ = inner ℝ (u t) ψT := (MeasureTheory.L2.inner_def (u t) ψT).symm

/-- The datum and its torus `L²` class have the same pairing with every smooth periodic
test. -/
theorem FrozenDriftProblem.initial_pairing_eq_cell_integral
    (P : FrozenDriftProblem) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ P.initialTorusL2 (smoothPeriodicTestL2 hψ hperiodic) =
      ∫ x in AVenhance.unitCube, P.θ₀ x * ψ x := by
  let ψT : ScalarTorusL2 := smoothPeriodicTestL2 hψ hperiodic
  have hθ : (fun x : Torus => P.initialTorusL2 x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus P.θ₀ := by
    exact (frozenInitialData_memLp_torus P.initial_memL2).coeFn_toLp
  have hψT : (fun x : Torus => ψT x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus ψ :=
    (frozenInitialData_memLp_torus (LimitRepresentation.smoothPeriodicTest_memL2On hψ)).coeFn_toLp
  calc
    inner ℝ P.initialTorusL2 ψT =
        ∫ x : Torus, inner ℝ (P.initialTorusL2 x) (ψT x) :=
          (MeasureTheory.L2.inner_def P.initialTorusL2 ψT).symm
    _ = ∫ x : Torus, (P.initialTorusL2 x) * (ψT x) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [mul_comm]
    _ = ∫ x : Torus,
          AVenhance.Infra.Torus.periodicToTorus
            (fun y : Vec 2 => P.θ₀ y * ψ y) x := by
          apply integral_congr_ae
          filter_upwards [hθ, hψT] with x hx hψx
          rw [show AVenhance.Infra.Torus.periodicToTorus
            (fun y : Vec 2 => P.θ₀ y * ψ y) x =
            AVenhance.Infra.Torus.periodicToTorus P.θ₀ x *
            AVenhance.Infra.Torus.periodicToTorus ψ x from rfl,
            ← hx, ← hψx]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, P.θ₀ x * ψ x :=
      AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
    _ = ∫ x in AVenhance.unitCube, P.θ₀ x * ψ x :=
      AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _

/-- Smooth-test pairings of the physical weak path are continuous on the closed time interval. -/
theorem weakPathRepresentative_testPairing_continuous
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (hweakContinuous : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ContinuousOn
      (fun t : ℝ => ∫ x in AVenhance.unitCube,
        weakPathRepresentative u t x * ψ x) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : Icc (0 : ℝ) 1 =>
    ∫ x in AVenhance.unitCube, weakPathRepresentative u t x * ψ x)
  have heq : (fun t : Icc (0 : ℝ) 1 =>
      ∫ x in AVenhance.unitCube, weakPathRepresentative u t x * ψ x) =
      fun t => inner ℝ (u t) (smoothPeriodicTestL2 hψ hperiodic) := by
    funext t
    exact weakPathRepresentative_pairing_eq_inner u t hψ hperiodic
  rw [heq]
  exact hweakContinuous (smoothPeriodicTestL2 hψ hperiodic)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
