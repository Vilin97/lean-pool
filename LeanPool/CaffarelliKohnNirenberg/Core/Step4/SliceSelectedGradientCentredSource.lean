/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWSUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreySlice

/-!
# Slice Selected Gradient Centred Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-!
# The centred divergence-form source for the selected pressure gradient

The source below is the one paired with the singly centred tensor
`pressureUTensor u c`.  The constant vector `c` is spatially constant.  A
force term remains in the source, so its tested identity has an additional
force pairing unless that pairing is separately known to vanish.

The elementary reason for using the centred source is recorded here as a
compiled pointwise probe: with `u ≡ a`, `Du = 0`, `f = 0`, and `c = 0`, the
uncentred source is zero while the centred tensor has a nonzero `(0,0)` entry.
-/

/-- The centred divergence-form source paired with `pressureUTensor u c`. -/
def pressureDivergenceCutoffSourceCentred
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3)
    (c : Vec3) : Vec3 → Vec3 :=
  fun x i => ∑ j, (η x * Du x i j * (u x j - c j) +
      dη j x * u x i * (u x j - c j)) - η x * f x i

/-- Alias used by the source-Morrey and slice-selection interfaces. -/
def sourceMorreyCutoffVCentred
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3)
    (c : Vec3) : Vec3 → Vec3 :=
  pressureDivergenceCutoffSourceCentred η dη u Du f c

private theorem centred_eLpNorm_mul_bounded
    {μ : Measure Vec3} {a g : Vec3 → ℝ} {p : ℝ≥0∞} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hg : AEStronglyMeasurable g μ)
    (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    eLpNorm (fun x => a x * g x) p μ ≤
      ENNReal.ofReal C * eLpNorm g p μ := by
  have hmono : eLpNorm (fun x => a x * g x) p μ ≤
      eLpNorm (fun x => C * g x) p μ := by
    apply eLpNorm_mono_ae (ha.mul hg)
    filter_upwards [hbound] with x hx
    change ‖a x * g x‖ ≤ ‖C * g x‖
    simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC] using
      (mul_le_mul_of_nonneg_right hx (norm_nonneg (g x)))
  have hsmul : (fun x => C * g x) = C • g := by
    funext x
    rfl
  calc
    eLpNorm (fun x => a x * g x) p μ ≤ eLpNorm (C • g) p μ := by
      simpa only [hsmul] using hmono
    _ ≤ ‖C‖ₑ * eLpNorm g p μ :=
      eLpNorm_const_smul_le (c := C) (f := g) (p := p) (μ := μ)
    _ = ENNReal.ofReal C * eLpNorm g p μ := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]

/-- Quantitative form of the centred correction estimate. -/
theorem sourceMorreyCutoffVCentred_slice_bound_of_uncentred
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {c : Vec3} {i : Fin 3} {Cη Cdη Cc : ℝ}
    {KU KD Kunc : ℝ≥0∞}
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη) (hCc : 0 ≤ Cc)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hηbound : ∀ᵐ x ∂(volume.restrict B), ‖η x‖ ≤ Cη)
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ x ∂(volume.restrict B), ‖dη j x‖ ≤ Cdη)
    (hc : ∀ j : Fin 3, ‖c j‖ ≤ Cc)
    (hUmeas : AEStronglyMeasurable (fun x => u x i)
      (volume.restrict B))
    (hDmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => Du x i j)
        (volume.restrict B))
    (hU : eLpNorm (fun x => u x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ KU)
    (hD : ∀ j : Fin 3, eLpNorm (fun x => Du x i j)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ KD)
    (hunc : eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kunc) :
    eLpNorm (fun x => sourceMorreyCutoffVCentred η dη u Du f c x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      Kunc + ENNReal.ofReal Cc *
        ∑ _j : Fin 3, (ENNReal.ofReal Cη * KD +
          ENNReal.ofReal Cdη * KU) := by
  let μ : Measure Vec3 := volume.restrict B
  have hcorr (j : Fin 3) :
      eLpNorm (fun x => (η x * Du x i j + dη j x * u x i) * c j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal Cc * (ENNReal.ofReal Cη * KD +
        ENNReal.ofReal Cdη * KU) := by
    have hηD := centred_eLpNorm_mul_bounded (p := ENNReal.ofReal (6 / 5 : ℝ))
      hη (hDmeas j)
      hCη hηbound
    have hdU := centred_eLpNorm_mul_bounded (p := ENNReal.ofReal (6 / 5 : ℝ))
      (hdη j) hUmeas
      hCdη (hdηbound j)
    have hsum := eLpNorm_add_le (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (f := fun x => η x * Du x i j)
      (g := fun x => dη j x * u x i) (by norm_num)
    have hηD' := hηD.trans (mul_le_mul_of_nonneg_left (hD j) (by positivity))
    have hdU' := hdU.trans (mul_le_mul_of_nonneg_left hU (by positivity))
    have hsum' := hsum.trans (add_le_add hηD' hdU')
    have hcmeas : AEStronglyMeasurable (fun _ : Vec3 => c j) μ :=
      aestronglyMeasurable_const
    have hconst := centred_eLpNorm_mul_bounded
      (p := ENNReal.ofReal (6 / 5 : ℝ)) hcmeas
      ((hη.mul (hDmeas j)).add ((hdη j).mul hUmeas)) hCc
      (Filter.Eventually.of_forall fun _ => hc j)
    have hconst' := hconst.trans (mul_le_mul_of_nonneg_left hsum'
      (by positivity))
    have heq : (fun x => (η x * Du x i j + dη j x * u x i) * c j) =
        (fun x => dη j x * (c j * u x i) + η x * (c j * Du x i j)) := by
      funext x
      ring
    rw [heq]
    simpa [mul_add, mul_assoc, mul_left_comm, add_comm, add_left_comm] using hconst'
  have hcorrSum :
      eLpNorm (fun x => ∑ j, (η x * Du x i j + dη j x * u x i) * c j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal Cc *
        ∑ j : Fin 3, (ENNReal.ofReal Cη * KD +
          ENNReal.ofReal Cdη * KU) := by
    have h0 := hcorr (0 : Fin 3)
    have h1 := hcorr (1 : Fin 3)
    have h2 := hcorr (2 : Fin 3)
    have hs12 := eLpNorm_add_le (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ))
      (f := fun x => (η x * Du x i 1 + dη 1 x * u x i) * c 1)
      (g := fun x => (η x * Du x i 2 + dη 2 x * u x i) * c 2) (by norm_num)
    have hs := eLpNorm_add_le (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ))
      (f := fun x => (η x * Du x i 0 + dη 0 x * u x i) * c 0)
      (g := fun x => (η x * Du x i 1 + dη 1 x * u x i) * c 1 +
        (η x * Du x i 2 + dη 2 x * u x i) * c 2) (by norm_num)
    have hbound := hs.trans (add_le_add h0 (hs12.trans (add_le_add h1 h2)))
    have heq : (fun x => ∑ j, (η x * Du x i j + dη j x * u x i) * c j) =
        (fun x => (η x * Du x i 0 + dη 0 x * u x i) * c 0 +
          ((η x * Du x i 1 + dη 1 x * u x i) * c 1 +
            (η x * Du x i 2 + dη 2 x * u x i) * c 2)) := by
      funext x
      simp [Fin.sum_univ_succ]
    rw [heq]
    convert hbound using 1
    simp only [Fin.sum_univ_succ]
    ring
  have hsub := eLpNorm_add_le (μ := μ)
    (p := ENNReal.ofReal (6 / 5 : ℝ))
    (f := fun x => pressureDivergenceCutoffSource η dη u Du f x i)
    (g := fun x => -∑ j, (η x * Du x i j + dη j x * u x i) * c j) (by norm_num)
  have hneg : eLpNorm (fun x =>
      -∑ j, (η x * Du x i j + dη j x * u x i) * c j)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ =
      eLpNorm (fun x =>
        ∑ j, (η x * Du x i j + dη j x * u x i) * c j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ := by
    rw [show (fun x => -∑ j, (η x * Du x i j + dη j x * u x i) * c j) =
        -(fun x => ∑ j, (η x * Du x i j + dη j x * u x i) * c j) by
          rfl, eLpNorm_neg]
  have hneg' : eLpNorm (fun x =>
      -∑ j, (η x * Du x i j + dη j x * u x i) * c j)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal Cc *
        ∑ j : Fin 3, (ENNReal.ofReal Cη * KD +
          ENNReal.ofReal Cdη * KU) := by
    calc
      _ = eLpNorm (fun x =>
          ∑ j, (η x * Du x i j + dη j x * u x i) * c j)
          (ENNReal.ofReal (6 / 5 : ℝ)) μ := hneg
      _ ≤ _ := hcorrSum
  have hsub' := hsub.trans (add_le_add hunc hneg')
  rw [show (fun x => sourceMorreyCutoffVCentred η dη u Du f c x i) =
      (fun x => pressureDivergenceCutoffSource η dη u Du f x i -
        ∑ j, (η x * Du x i j + dη j x * u x i) * c j) by
    funext x
    simp only [sourceMorreyCutoffVCentred,
      pressureDivergenceCutoffSourceCentred,
      pressureDivergenceCutoffSource]
    have hsum : (∑ j, (η x * Du x i j * (u x j - c j) +
        dη j x * u x i * (u x j - c j))) =
        (∑ j, (η x * Du x i j * u x j +
          dη j x * u x i * u x j)) -
          ∑ j, (η x * Du x i j + dη j x * u x i) * c j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring]
  have heq2 : (fun x => pressureDivergenceCutoffSource η dη u Du f x i -
      ∑ j, (η x * Du x i j + dη j x * u x i) * c j) =
      (fun x => pressureDivergenceCutoffSource η dη u Du f x i) +
        (fun x => -∑ j, (η x * Du x i j + dη j x * u x i) * c j) := by
    funext x
    change pressureDivergenceCutoffSource η dη u Du f x i -
        ∑ j, (η x * Du x i j + dη j x * u x i) * c j =
      pressureDivergenceCutoffSource η dη u Du f x i +
        -∑ j, (η x * Du x i j + dη j x * u x i) * c j
    ring
  rw [heq2]
  exact hsub'


end CKN.Core.Step4
