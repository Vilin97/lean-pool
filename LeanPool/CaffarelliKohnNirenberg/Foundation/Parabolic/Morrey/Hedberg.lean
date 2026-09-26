/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Tail

/-!
# Maximal-majorant interface for the Hedberg estimate

The maximal theorem is deliberately not reproved here.  This module gives
the parameter property used by the pointwise potential argument and records
the exponent identities needed by its eventual proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- A function is a parabolic uncentred maximal majorant for `f`. -/
@[expose] def IsParabolicMaximalMajorant (f : ParabolicPoint → ℝ)
    (M : ParabolicPoint → ℝ≥0∞) : Prop :=
  ∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
    (∫⁻ w in Metric.ball z R, ENNReal.ofReal |f w|) ≤
      M z * volume (Metric.ball z R)


/-- The Morrey exponent in the Hedberg inequality. -/
def hedbergMorreyExponent (β q : ℝ) : ℝ := β * q / 5





theorem parabolicRieszPotential_split {β : ℝ} {f : ParabolicPoint → ℝ}
    (z : ParabolicPoint) {R : ℝ} :
    parabolicRieszPotential β f z =
      (∫⁻ w in {w | parabolicRho₂ z w < R},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) +
      (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) := by
  let g : ParabolicPoint → ℝ≥0∞ := fun w =>
    parabolicRieszKernel β z w * ENNReal.ofReal |f w|
  let s : Set ParabolicPoint := {w | parabolicRho₂ z w < R}
  let t : Set ParabolicPoint := {w | R ≤ parabolicRho₂ z w}
  have hs : MeasurableSet s := by
    exact (measurable_parabolicRho₂ z) measurableSet_Iio
  have ht : MeasurableSet t := by
    exact (measurable_parabolicRho₂ z) measurableSet_Ici
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    intro w hws hwt
    change parabolicRho₂ z w < R at hws
    change R ≤ parabolicRho₂ z w at hwt
    exact (not_lt_of_ge hwt) hws
  have hunion : s ∪ t = Set.univ := by
    ext w
    change (parabolicRho₂ z w < R ∨ R ≤ parabolicRho₂ z w) ↔ True
    simp only [iff_true]
    exact lt_or_ge (parabolicRho₂ z w) R
  calc
    parabolicRieszPotential β f z = ∫⁻ w in Set.univ, g w := by
      simp [parabolicRieszPotential, g]
    _ = ∫⁻ w in s ∪ t, g w := by rw [hunion]
    _ = (∫⁻ w in s, g w) + (∫⁻ w in t, g w) := lintegral_union ht hdisj
    _ = _ := by rfl

theorem parabolicRieszPotential_split_le {β : ℝ} {f : ParabolicPoint → ℝ}
    (z : ParabolicPoint) {R : ℝ}
    {A B : ℝ≥0∞}
    (hnear : (∫⁻ w in {w | parabolicRho₂ z w < R},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤ A)
    (hfar : (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤ B) :
    parabolicRieszPotential β f z ≤ A + B := by
  rw [parabolicRieszPotential_split z]
  exact add_le_add hnear hfar

end CKN.Foundation.Parabolic.Morrey
