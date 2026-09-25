/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceMorrey

/-!
# Source Morrey Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The slicewise interface for the divergence-form pressure source carrying a
spatial cutoff.  These bounds are source estimates only; they do not select a
weak pressure gradient or prove its spacetime pairing. -/

/-- Cutoff pressure-Poisson source used to estimate the selected gradient in Morrey spaces. -/
def sourceMorreyCutoffV
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3) : Vec3 → Vec3 :=
  pressureDivergenceCutoffSource η dη u Du f

theorem sourceMorreyCutoffV_slice_bound
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {q Cη Cdη : ℝ} {KU KD KF : ℝ≥0∞}
    (hq : 5 / 2 < q) (hμ : (volume.restrict B) Set.univ < ⊤)
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hηbound : ∀ᵐ x ∂(volume.restrict B), |η x| ≤ Cη)
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ x ∂(volume.restrict B), |dη j x| ≤ Cdη)
    (hU : ∀ j : Fin 3,
      eLpNorm (fun x => u x j) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict B) ≤ KU)
    (hD : ∀ i j : Fin 3,
      eLpNorm (fun x => Du x i j) (ENNReal.ofReal (2 : ℝ))
        (volume.restrict B) ≤ KD)
    (hF : ∀ i : Fin 3,
      eLpNorm (fun x => f x i) (ENNReal.ofReal q)
        (volume.restrict B) ≤ KF)
    (hUmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => u x j)
        (volume.restrict B))
    (hDmeas : ∀ i j : Fin 3,
      AEStronglyMeasurable (fun x => Du x i j)
        (volume.restrict B))
    (hFmeas : ∀ i : Fin 3,
      AEStronglyMeasurable (fun x => f x i)
        (volume.restrict B)) :
    eLpNorm (fun x => sourceMorreyCutoffV η dη
        u Du f x)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      3 * (3 * (ENNReal.ofReal Cη * KD * KU +
        ENNReal.ofReal Cdη *
          (KU * KU * (volume.restrict B) Set.univ ^ (1 / 6 : ℝ))) +
        ENNReal.ofReal Cη *
          (KF * (volume.restrict B) Set.univ ^ (5 / 6 - 1 / q))) := by
  exact pressure_divergence_cutoff_source_slice_le hq hμ hCη hCdη hη hηbound
    hdη hdηbound hU hD hF hUmeas hDmeas hFmeas

end CKN.Core.Step4
