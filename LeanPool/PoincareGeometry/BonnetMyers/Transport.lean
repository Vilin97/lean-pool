/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Parallel

/-!
# Coordinate transport identities

The local ODEs in `Parallel.lean` live in the model fibre `E`, while the
connection and the metric live in the tangent fibres.  This file records the
conversion explicitly.  In particular, no identification of a tangent fibre
with `E` is made by definitional equality: the inverse of the tangent-bundle
trivialization is used throughout.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type _)]

def coordinateFrameCombination
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u : E) (y : M) : TM y :=
  ∑ j, (b.repr u j) •
    (trivializationAt E TM x₀).localFrame b j y

@[simp] lemma coordinateFrameCombination_neg
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (u : E) :
    coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (-u) y =
      -coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y := by
  simp [coordinateFrameCombination]

@[simp] lemma coordinateFrameCombination_smul
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (a : ℝ) (u : E) :
    coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (a • u) y =
      a • coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y := by
  simp [coordinateFrameCombination, Finset.smul_sum, smul_smul]

lemma localFrame_eq_symmL
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ (chartAt H x₀).source)
    (i : Fin (Module.finrank ℝ E)) :
    (trivializationAt E TM x₀).localFrame b i y =
      (trivializationAt E TM x₀).symmL ℝ y (b i) := by
  let e := trivializationAt E TM x₀
  have hlocal := e.localFrame_apply_of_mem_baseSet
    (b := b) (i := i) (by simpa [e] using hy)
  rw [hlocal]
  change (b.map (e.linearEquivAt ℝ y (by simpa [e] using hy)).symm) i =
    e.symmL ℝ y (b i)
  rw [Module.Basis.map_apply, Bundle.Trivialization.linearEquivAt_symm_apply]
  exact (Bundle.Trivialization.symmL_apply e (by simpa [e] using hy) (b i)).symm

lemma coordinateFrameCombination_eq_symmL
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ (chartAt H x₀).source) (u : E) :
    coordinateFrameCombination (x₀ := x₀) b u y =
      (trivializationAt E TM x₀).symmL ℝ y u := by
  let e := trivializationAt E TM x₀
  calc
    coordinateFrameCombination (x₀ := x₀) b u y =
        ∑ j, e.localFrameCoeff I b j y (e.symmL ℝ y u) • e.localFrame b j y := by
      unfold coordinateFrameCombination
      apply Finset.sum_congr rfl
      intro j hj
      have hcoeff := Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := e) (b := b) (x := y)
        (by simpa [e] using hy) (fun _ : M ↦ e.symmL ℝ y u) j
      have hback : (e.linearEquivAt ℝ y (by simpa [e] using hy))
          ((e.symmL ℝ y) u) = u := by
        rw [Bundle.Trivialization.linearEquivAt_apply]
        have hs : e.symmL ℝ y u = e.symm y u :=
          Bundle.Trivialization.symmL_apply e (by simpa [e] using hy) u
        rw [hs]
        simpa using congrArg Prod.snd
          (Bundle.Trivialization.apply_mk_symm e (by simpa [e] using hy) u)
      change (b.repr u j) • e.localFrame b j y =
        e.localFrameCoeff I b j y ((fun _ : M ↦ e.symmL ℝ y u) y) • e.localFrame b j y
      rw [hcoeff]
      simp [e, Bundle.Trivialization.basisAt, hback]
    _ = e.symmL ℝ y u := by
      symm
      exact e.eq_sum_localFrameCoeff_smul (I := I)
        (b := b) (s := fun _ : M ↦ e.symmL ℝ y u) (x' := y)
        (by simpa [e] using hy)
    _ = (trivializationAt E TM x₀).symmL ℝ y u := rfl

/-- Reading a tangent vector into the preferred trivialization and then
reconstructing it through any local coordinate frame gives the original
vector.  The frame basis affects the coefficient presentation, but not this
fibrewise inverse identity. -/
lemma coordinateFrameCombination_coordinateVelocity
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (v : TM x₀) :
    coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) x₀ = v := by
  rw [coordinateFrameCombination_eq_symmL (I := I) (M := M)
    (x₀ := x₀) b (mem_chart_source H x₀)]
  rw [coordinateVelocity]
  exact (trivializationAt E TM x₀).symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt E TM x₀) v

lemma tangentField_eq_coordinateFrameCombination
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (w : ℝ → E) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    tangentField cov x₀ b sol w t =
      coordinateFrameCombination (x₀ := x₀) b (w t)
        (BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t) := by
  have htarget := sol.coordinate_mem_target t ht
  have hsource : BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t ∈
      (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    change (extChartAt I x₀).symm (sol.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target htarget
  rw [tangentField]
  have hcurveeq := LocalChartSecondOrderSolution.curve_eq_chart sol ht
  have hsymm := TangentBundle.symmL_trivializationAt
    (I := I) (x₀ := x₀) (x :=
      BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t) hsource
  have hframe := coordinateFrameCombination_eq_symmL (I := I) (M := M)
    (x₀ := x₀) b hsource (w t)
  change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm
      (sol.coordinate t)) (w t) =
    coordinateFrameCombination (x₀ := x₀) b (w t)
      (BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t)
  rw [← hcurveeq]
  rw [← hsymm]
  exact hframe.symm

/-- Reading the tangent field reconstructed from a coordinate vector through
the same endpoint trivialization returns the original coordinate vector.
This is the fibre-level inverse needed when a local geodesic germ is used to
control a fixed-chart coefficient operator at a global time. -/
lemma continuousLinearMapAt_tangentField_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (w : ℝ → E) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    (trivializationAt E TM x₀).continuousLinearMapAt ℝ
      (BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t)
      (tangentField cov x₀ b sol w t) = w t := by
  have htarget := sol.coordinate_mem_target t ht
  have hsource : BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t ∈
      (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    change (extChartAt I x₀).symm (sol.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target htarget
  have hbase : BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t ∈
      (trivializationAt E TM x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) x₀,
      ← extChartAt_source (I := I) x₀]
    rw [← extChartAt_source (I := I) x₀] at hsource
    exact hsource
  rw [tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol w ht]
  rw [coordinateFrameCombination_eq_symmL (I := I) (M := M)
    (x₀ := x₀) b hsource]
  exact (trivializationAt E TM x₀).continuousLinearMapAt_symmL hbase (w t)

end LocalGeodesicData

end BonnetMyersEntry
