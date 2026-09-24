/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCorrectedSWS
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTBounds

/-!
# Identification of cell-selected pressure gradients

On each cell, a locally selected weak pressure gradient and the fixed glued
gradient are weak derivatives of the same pressure. Uniqueness identifies
them almost everywhere, preserving the cell's own quantitative bound.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section

namespace CKN.Core.Step4

/-- The selected weak-gradient witness on a doubled cell agrees locally with
the fixed glued field. Its norm bound retains the majorant belonging to that
cell. -/
theorem ae_glued_gradient_cell_selected_slice_identification
    {B : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {M : ℝ → ℝ≥0∞} (hball : vec3Ball x r ⊆ B)
    (htime : Ioc (t - r ^ 2) t ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
          (euclideanBall x ((2 * r) / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
          (fun y => p (y, s)) (fun y => D y k)) ∧
        (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s)) :
    ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
          (euclideanBall x ((2 * r) / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
          (fun y => p (y, s)) (fun y => D y k)) ∧
        (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s) ∧
        (∀ k : Fin 3, eLpNorm (fun y => Dp (y, s) k)
          (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s) ∧
        (∀ k : Fin 3,
          (fun y => Dp (y, s) k) =ᵐ[volume.restrict
            (euclideanBall x ((2 * r) / 2))] (fun y => D y k)) := by
  have hEeq : euclideanBall x ((2 * r) / 2) = vec3Ball x r := by
    rw [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)]
    exact euclideanBall_eq_vec3Ball_of_pos hr
  have hEopen : IsOpen (euclideanBall x ((2 * r) / 2)) := by
    rw [hEeq]
    exact isOpen_vec3Ball x r
  have hEball : euclideanBall x ((2 * r) / 2) ⊆ B := by
    rw [hEeq]
    exact hball
  have hwindow : Ioc (t - r ^ 2) t ⊆ Ioc (t - (2 * r) ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (by nlinarith only [sq_nonneg r]) hs.1, hs.2⟩
  filter_upwards
    [ae_restrict_of_ae_restrict_of_subset htime hfield,
      ae_restrict_of_ae_restrict_of_subset hwindow hslice] with s hf hs
  obtain ⟨D, hDloc, hDmem, hDweak, hDbound⟩ := hs
  have hEq : ∀ k : Fin 3,
      (fun y => Dp (y, s) k) =ᵐ[volume.restrict
        (euclideanBall x ((2 * r) / 2))] (fun y => D y k) := by
    intro k
    have hDpLoc : LocallyIntegrableOn (fun y => Dp (y, s) k)
        (euclideanBall x ((2 * r) / 2)) volume :=
      (hf k).1.mono_set hEball
    have hDpWeak : HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
        (fun y => p (y, s)) (fun y => Dp (y, s) k) :=
      (hf k).2.restrict hEopen hEball
    have hEq := CKN.hasWeakPartialDerivOn_unique_ae hEopen hDpLoc
      (hDloc k) hDpWeak (hDweak k)
    exact hEq
  refine ⟨D, hDloc, hDmem, hDweak, hDbound, ?_, hEq⟩
  intro k
  calc
    eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) =
      eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) :=
          eLpNorm_congr_ae (hEq k)
    _ ≤ M s := hDbound k

end CKN.Core.Step4
