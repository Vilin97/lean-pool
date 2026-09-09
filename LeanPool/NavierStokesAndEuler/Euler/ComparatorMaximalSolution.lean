/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ComparatorMaximalFields
import LeanPool.NavierStokesAndEuler.Euler.ComparatorSobolevEvolution

/-! The canonical maximal solution in the reference's ordinary-function
Sobolev class. All regularity is inherited from its existing shorter evolutions. -/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open scoped Topology ContDiff

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Maximal derivative field, given by `eulerRhs (L.maximalField t) (L.maximalPressureField t)`. -/
def maximalDerivativeField (t : L.Time) : SmoothL2Field Space :=
  eulerRhs (L.maximalField t) (L.maximalPressureField t)

theorem maximalDerivativeField_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    maximalDerivativeField L (L.shorterTime S hSL t) =
      (L.evolution S hS hSL).derivative t := by
  rw [maximalDerivativeField, L.maximalField_eq_evolution S hS hSL,
    L.maximalPressureField_eq_evolution S hS hSL, Evolution.derivative_eq_eulerRhs]

theorem maximalDerivativeField_jet_continuous (n : ℕ) :
    Continuous (fun t : L.Time => (maximalDerivativeField L t).jetLp n) := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  simp only [maximalDerivativeField_eq_evolution L S hS hSL]
  exact (L.evolution S hS hSL).derivative_continuous n

/-- Maximal derivative extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalDerivativeExtension (x : Space) (t : ℝ) : Space :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then (maximalDerivativeField L ⟨t, ht⟩).field x else 0

theorem maximalDerivativeExtension_eq (t : L.Time) :
    (maximalDerivativeExtension L · (t : ℝ)) = (maximalDerivativeField L t).field := by
  funext x
  simp only [maximalDerivativeExtension, dite_eq_left t.property]

theorem maximalVelocityExtension_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    (maximalVelocityExtension L · (t : ℝ)) = ((L.evolution S hS hSL).velocity t).field :=
  (maximalVelocityExtension_eq L (L.shorterTime S hSL t)).trans
    (L.maximalVelocity_eq_evolution S hS hSL t)

theorem maximalVelocityExtension_sobolevSmooth :
    Euler.SobolevSmoothOn (Ico 0 L.duration) (maximalVelocityExtension L) :=
  sobolevSmoothOn_of_path L.maximalField L.maximalField_jet_continuous _
    (maximalVelocityExtension_eq L)

theorem maximalDerivativeExtension_sobolevSmooth :
    Euler.SobolevSmoothOn (Ico 0 L.duration) (maximalDerivativeExtension L) :=
  sobolevSmoothOn_of_path (maximalDerivativeField L)
    (maximalDerivativeField_jet_continuous L) _ (maximalDerivativeExtension_eq L)

theorem maximalVelocityExtension_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 L.duration) :
    HasDerivAt (fun s => Euler.toL2 (maximalVelocityExtension L · s))
      (Euler.toL2 (maximalDerivativeExtension L · t)) t := by
  let s : L.Time := ⟨t, ht.1.le, ht.2⟩
  let S := L.intermediateHorizon s
  have hS : 0 < S := L.intermediateHorizon_pos s
  have hSL : S < L.duration := L.intermediateHorizon_lt s
  have htS : t < S := L.time_lt_intermediateHorizon s
  let r : Icc (0 : ℝ) S := ⟨t, ht.1.le, htS.le⟩
  have hd := ((L.evolution S hS hSL).velocityPath_hasDerivWithinAt r).hasDerivAt
    (Icc_mem_nhds ht.1 htS)
  rw [Evolution.velocityPath_extend] at hd
  have he : Euler.toL2 (maximalDerivativeExtension L · t) =
      ((L.evolution S hS hSL).derivative r).toLp := by
    change Euler.toL2 (maximalDerivativeExtension L ·
      (L.shorterTime S hSL r : ℝ)) = _
    rw [maximalDerivativeExtension_eq L (L.shorterTime S hSL r), toL2_field,
      maximalDerivativeField_eq_evolution L S hS hSL]
  rw [he]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 htS] with u hu
  rw [maximalVelocityExtension_eq_evolution L S hS hSL ⟨u, hu.1.le, hu.2.le⟩,
    toL2_field, projIcc_of_mem hS.le ⟨hu.1.le, hu.2.le⟩]

theorem maximal_sobolevSolution :
    EulerSobolevExistenceAndSmoothnessR3On (Ico 0 L.duration) A.field
      (maximalVelocityExtension L) (maximalPressureExtension L) := by
  refine ⟨fun x t ht => maximalVelocityExtension_divergence L t ht x,
    fun x => congrFun (maximalVelocityExtension_initial L) x,
    maximalVelocityExtension_sobolevSmooth L, ?_, maximalDerivativeExtension L,
    maximalDerivativeExtension_sobolevSmooth L, ?_, ?_⟩
  · intro t ht
    have hi : t ∈ Ico 0 L.duration := interior_subset ht
    rw [maximalPressureExtension_eq L ⟨t, hi⟩]
    exact (L.maximalPressure_spec ⟨t, hi⟩).1.differentiable (by simp)
  · intro t ht
    exact maximalVelocityExtension_hasDerivAt L t (by simpa only [interior_Ico] using ht)
  · intro x t ht
    have hi : t ∈ Ico 0 L.duration := interior_subset ht
    have hd := congrFun (maximalDerivativeExtension_eq L ⟨t, hi⟩) x
    have hv := congrFun (maximalVelocityExtension_eq L ⟨t, hi⟩) x
    rw [hd, hv, maximalVelocityExtension_eq L ⟨t, hi⟩,
      maximalPressureExtension_eq L ⟨t, hi⟩, maximalDerivativeField, eulerRhs_field,
      (L.maximalPressure_spec ⟨t, hi⟩).2.2 x]
    change (-fderiv ℝ (L.maximalField ⟨t, hi⟩).field x
      ((L.maximalField ⟨t, hi⟩).field x) - (L.maximalPressureField ⟨t, hi⟩).field x) +
      fderiv ℝ (L.maximalField ⟨t, hi⟩).field x ((L.maximalField ⟨t, hi⟩).field x) = _
    abel

theorem maximal_sobolev_existence_iff (T : ℝ) (hT : 0 < T) :
    (∃ v p, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field v p) ↔
      T < L.duration := by
  rw [exists_sobolevSolution_iff A T hT, L.hasScalarEulerEvolution_iff]
  exact and_iff_right hT

end Euler.ComparatorBridge
