/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSymmetricGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTMeasurable

/-!
# Cellwise bounds for one measurable pressure gradient

The slice bounds in `paper/ckn.tex`, Section `sec:pressure`, are
transported from the derivative selected at a cell's scale to a fixed field.
Spatial a.e. uniqueness preserves the complete quantitative majorant. Time
windows are restricted only along an explicit subset inclusion.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

namespace CKN.Core.Step4

/-- A vector slice bound on an open cell transfers, coordinate by coordinate,
to a fixed weak gradient on a larger spatial carrier and time set. -/
theorem ae_glued_gradient_bound_of_vector_slice_bound
    {B W : Set Vec3} {I J : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {q : ℝ≥0∞} {M : ℝ → ℝ≥0∞}
    (hW : IsOpen W) (hWB : W ⊆ B) (hJI : J ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun x => Dp (x, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun x => p (x, s)) (fun x => Dp (x, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict J, ∃ D : Vec3 → Vec3,
      (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k) W volume) ∧
      MemLp D q (volume.restrict W) ∧
      (∀ k : Fin 3, HasWeakPartialDerivOn W k (fun x => p (x, s)) (fun x => D x k)) ∧
      (∀ k : Fin 3, eLpNorm (fun x => D x k) q (volume.restrict W) ≤ M s)) :
    ∀ᵐ s ∂volume.restrict J, ∀ k : Fin 3,
      eLpNorm (fun x => Dp (x, s) k) q (volume.restrict W) ≤ M s := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hfield, hslice] with s hf hs k
  obtain ⟨D, hDloc, _hDmem, hDweak, hDbound⟩ := hs
  exact eLpNorm_le_of_hasWeakPartialDerivOn hW hWB (hf k).1 (hDloc k)
    (hf k).2 (hDweak k) (hDbound k)

/-- The cell bound on a doubled cylinder supplies the bound on its half-radius
spatial ball throughout the cell's shorter backward time window. -/
theorem ae_glued_gradient_cell_bound_of_doubled_slice_bound
    {B : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {M : ℝ → ℝ≥0∞} (hball : vec3Ball x r ⊆ B) (htime : Ioc (t - r ^ 2) t ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t), ∃ D : Vec3 → Vec3,
      (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
        (euclideanBall x ((2 * r) / 2)) volume) ∧
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
      (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
        (fun y => p (y, s)) (fun y => D y k)) ∧
      (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s)) :
    ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t), ∀ k : Fin 3,
      eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r)) ≤ M s := by
  have hwindow : Ioc (t - r ^ 2) t ⊆ Ioc (t - (2 * r) ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (by nlinarith only [sq_nonneg r]) hs.1, hs.2⟩
  have hballEq : euclideanBall x ((2 * r) / 2) = vec3Ball x r := by
    rw [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)]
    exact euclideanBall_eq_vec3Ball_of_pos hr
  apply ae_glued_gradient_bound_of_vector_slice_bound (isOpen_vec3Ball x r) hball htime hfield
  simpa only [hballEq] using ae_restrict_of_ae_restrict_of_subset hwindow hslice


/-- The same field supplies the existential cell datum required by the
cell-transfer theorem; the witness is its own restricted spatial slice. -/
theorem ae_glued_gradient_cell_data_of_doubled_slice_bound {B : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {M : ℝ → ℝ≥0∞} (hball : vec3Ball x r ⊆ B) (htime : Ioc (t - r ^ 2) t ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t), ∃ D : Vec3 → Vec3,
      (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
        (euclideanBall x ((2 * r) / 2)) volume) ∧
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
      (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
        (fun y => p (y, s)) (fun y => D y k)) ∧
      (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s)) :
    ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x r) volume ∧
      HasWeakPartialDerivOn (vec3Ball x r) k (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ≤ M s := by
  have hbound := ae_glued_gradient_cell_bound_of_doubled_slice_bound hr hball htime hfield hslice
  intro k
  filter_upwards [hbound, ae_restrict_of_ae_restrict_of_subset htime hfield] with s hb hf
  exact ⟨fun y => Dp (y, s) k, (hf k).1.mono_set hball,
    (hf k).2.restrict (isOpen_vec3Ball x r) hball, hb k⟩

end CKN.Core.Step4
