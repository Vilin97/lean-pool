/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTensorTime

/-!
# A bilinear bound for the centered tensor source

The source paired with `eq:Uij` contains the mean-free velocity in its second
factor. Spatial Hölder bounds this factor separately, retaining the cutoff
cost needed for the time estimate of `eq:pressure-gradient-morrey`.
The scalar Hölder proofs follow `PressureGradientSourceBounds`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

private theorem eLpNorm_mul_two_three_le
    {μ : Measure Vec3} {f g : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (2 : ℝ)) μ *
        eLpNorm g (ENNReal.ofReal (3 : ℝ)) μ := by
  have : (ENNReal.ofReal (2 : ℝ)).HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (6 / 5 : ℝ)) := by
    have h : (2 : ℝ).HolderTriple 3 (6 / 5 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g)
    (p := ENNReal.ofReal (2 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
    (r := ENNReal.ofReal (6 / 5 : ℝ)) (b := fun a b : ℝ => a * b)
    (c := (1 : NNReal)) (by exact continuous_mul) hf hg (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  simpa using h

private theorem eLpNorm_mul_three_three_le
    {μ : Measure Vec3} {f g : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (3 : ℝ)) μ *
        eLpNorm g (ENNReal.ofReal (3 : ℝ)) μ := by
  have : (ENNReal.ofReal (3 : ℝ)).HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g)
    (p := ENNReal.ofReal (3 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
    (r := ENNReal.ofReal (3 / 2 : ℝ)) (b := fun a b : ℝ => a * b)
    (c := (1 : NNReal)) (by exact continuous_mul) hf hg (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  simpa using h

private theorem eLpNorm_mul_const_le
    {μ : Measure Vec3} {a f : Vec3 → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hf : AEStronglyMeasurable f μ)
    (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C)
    {p : ℝ≥0∞} :
    eLpNorm (fun x => a x * f x) p μ ≤
      ENNReal.ofReal C * eLpNorm f p μ := by
  have hmono : eLpNorm (fun x => a x * f x) p μ ≤
      eLpNorm (fun x => C * f x) p μ := by
    apply eLpNorm_mono_ae (ha.mul hf)
    filter_upwards [haC] with x hx
    change |a x * f x| ≤ |C * f x|
    rw [abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))
  have hsmul : (fun x => C * f x) = C • f := by
    funext x
    rfl
  rw [hsmul, eLpNorm_const_smul] at hmono
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC] using hmono

private theorem eLpNorm_three_half_to_six_fifths
    {μ : Measure Vec3} {f : Vec3 → ℝ} (hf : AEStronglyMeasurable f μ)
    (hμ : μ Set.univ < ⊤) :
    eLpNorm f (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ *
        μ Set.univ ^ (1 / (6 / 5 : ℝ) - 1 / (3 / 2 : ℝ)) := by
  let : IsFiniteMeasure μ := ⟨hμ⟩
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := f) (p := ENNReal.ofReal (6 / 5 : ℝ))
    (q := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) hf
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h

/-- A centered tensor source component is controlled by a gradient product
and a cutoff-weighted quadratic product, with no force contribution. -/
theorem origin_centered_tensor_source_slice_bound
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3} {i : Fin 3}
    {Cη Cdη : ℝ} {KU KD KW : ℝ≥0∞}
    (hμ : (volume.restrict B) univ < ⊤)
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hηbound : ∀ᵐ x ∂volume.restrict B, |η x| ≤ Cη)
    (hdη : ∀ j, AEStronglyMeasurable (dη j) (volume.restrict B))
    (hdηbound : ∀ j, ∀ᵐ x ∂volume.restrict B, |dη j x| ≤ Cdη)
    (hU : eLpNorm (fun x => u x i) (ENNReal.ofReal (3 : ℝ)) (volume.restrict B) ≤ KU)
    (hD : ∀ j, eLpNorm (fun x => Du x i j) (ENNReal.ofReal (2 : ℝ)) (volume.restrict B) ≤ KD)
    (hW : ∀ j, eLpNorm (fun x => u x j - c j) (ENNReal.ofReal (3 : ℝ)) (volume.restrict B) ≤ KW)
    (hUm : ∀ j, AEStronglyMeasurable (fun x => u x j) (volume.restrict B))
    (hDm : ∀ j, AEStronglyMeasurable (fun x => Du x i j) (volume.restrict B)) :
    eLpNorm (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      3 * (ENNReal.ofReal Cη * KD * KW + ENNReal.ofReal Cdη *
        (KU * KW * volume B ^ (1 / 6 : ℝ))) := by
  have hWm (j : Fin 3) : AEStronglyMeasurable (fun x => u x j - c j)
      (volume.restrict B) := (hUm j).sub aestronglyMeasurable_const
  have hA (j : Fin 3) :
      eLpNorm (fun x => η x * Du x i j * (u x j - c j))
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
        ENNReal.ofReal Cη * KD * KW := by
    have hp := (eLpNorm_mul_two_three_le (hDm j) (hWm j)).trans
      (mul_le_mul' (hD j) (hW j))
    have hh := (eLpNorm_mul_const_le hη ((hDm j).mul (hWm j)) hCη hηbound).trans
      (mul_le_mul' le_rfl hp)
    simpa only [mul_assoc, Pi.mul_apply] using hh
  have hB (j : Fin 3) :
      eLpNorm (fun x => dη j x * u x i * (u x j - c j))
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
        ENNReal.ofReal Cdη * (KU * KW * volume B ^ (1 / 6 : ℝ)) := by
    have hp := (eLpNorm_mul_three_three_le (hUm i) (hWm j)).trans
      (mul_le_mul' hU (hW j))
    have hl := (eLpNorm_three_half_to_six_fifths ((hUm i).mul (hWm j)) hμ).trans
      (mul_le_mul' hp le_rfl)
    norm_num only [show (1 / (6 / 5 : ℝ) - 1 / (3 / 2 : ℝ)) = 1 / 6 by norm_num,
      Measure.restrict_apply_univ] at hl
    have hh := (eLpNorm_mul_const_le (hdη j) ((hUm i).mul (hWm j)) hCdη (hdηbound j)).trans
      (mul_le_mul' le_rfl hl)
    simpa only [mul_assoc, Pi.mul_apply] using hh
  have hterm (j : Fin 3) := (eLpNorm_add_le (μ := volume.restrict B)
    (f := fun x => η x * Du x i j * (u x j - c j))
    (g := fun x => dη j x * u x i * (u x j - c j))
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ))).trans
    (add_le_add (hA j) (hB j))
  have hsum := (eLpNorm_sum_le (μ := volume.restrict B) (s := Finset.univ)
    (f := fun j x => η x * Du x i j * (u x j - c j) + dη j x * u x i * (u x j - c j))
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ))).trans
    (Finset.sum_le_sum (fun j _ => hterm j))
  simpa only [pressureDivergenceCutoffSourceCentredTensor, Finset.sum_fn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hsum

end CKN.Core.Step4
