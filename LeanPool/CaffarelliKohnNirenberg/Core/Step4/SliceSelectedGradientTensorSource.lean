/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef

/-!
# The centred tensor source

The source for the first potential in `eq:pressure-gradient-decomposition` is the
negative divergence of the cutoff tensor. The force belongs to the seventh
and eighth potentials.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- The tensor source vanishes for constant velocity centred at that same
constant, as required by `eq:pressure-gradient-decomposition`. -/
theorem pressureDivergenceCutoffSourceCentredTensor_const
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ) (a : Vec3) :
    pressureDivergenceCutoffSourceCentredTensor η dη (fun _ => a) (fun _ _ _ => 0) a = 0 := by
  funext x i
  simp only [pressureDivergenceCutoffSourceCentredTensor, sub_self, mul_zero, add_zero,
    Finset.sum_const_zero, Pi.zero_apply]

/-- Component membership at the source exponent follows from `L²` gradients
and `L³` velocity on a finite-measure set in `eq:pressure-gradient-decomposition`. -/
theorem pressureDivergenceCutoffSourceCentredTensor_memLp
    {B : Set Vec3} [IsFiniteMeasure (volume.restrict B)]
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hη : MemLp η ⊤ (volume.restrict B))
    (hdη : ∀ j, MemLp (dη j) ⊤ (volume.restrict B))
    (hu : ∀ j, MemLp (fun x => u x j) 3 (volume.restrict B))
    (hDu : ∀ i j, MemLp (fun x => Du x i j) 2 (volume.restrict B))
    (i : Fin 3) :
    MemLp (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 3 (ENNReal.ofReal (6 / 5 : ℝ)) := by
    have h : (2 : ℝ).HolderTriple 3 (6 / 5 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    convert h.ennrealOfReal using 1 <;> norm_num
  have hv (j : Fin 3) : MemLp (fun x => u x j - c j) 3 (volume.restrict B) :=
    (hu j).sub (memLp_const (c j))
  have hu₂ : MemLp (fun x => u x i) 2 (volume.restrict B) :=
    (hu i).mono_exponent (by norm_num)
  have hηD (j : Fin 3) : MemLp (fun x => η x * Du x i j) 2
      (volume.restrict B) := hη.mul (hDu i j)
  have hdU (j : Fin 3) : MemLp (fun x => dη j x * u x i) 2
      (volume.restrict B) := (hdη j).mul hu₂
  exact memLp_finsetSum' Finset.univ fun j _ =>
    ((hηD j).mul (hv j)).add ((hdU j).mul (hv j))

/-- Global `L^{6/5}` membership and compact support of the tensor source in
`eq:pressure-gradient-decomposition`, from the local velocity and gradient norms. -/
theorem pressureDivergenceCutoffSourceCentredTensor_memLp_hasCompactSupport
    {B : Set Vec3} {η : Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hB : IsCompact B) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηB : tsupport η ⊆ B)
    (hu : ∀ j, MemLp (fun x => u x j) 3 (volume.restrict B))
    (hDu : ∀ i j, MemLp (fun x => Du x i j) 2 (volume.restrict B)) :
    (∀ i, MemLp (fun x => pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
    (∀ i, HasCompactSupport
      (fun x => pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i)) := by
  have hηc : HasCompactSupport η :=
    HasCompactSupport.of_support_subset_isCompact hB ((subset_tsupport η).trans hηB)
  have hdB (j : Fin 3) : tsupport (spatialDeriv η j) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηB
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  have hlocal (i : Fin 3) := pressureDivergenceCutoffSourceCentredTensor_memLp
    (c := c) (hη.continuous.memLp_top_of_hasCompactSupport hηc (volume.restrict B))
    (fun j => (contDiff_spatialDeriv_smooth hη j).continuous.memLp_top_of_hasCompactSupport
      (hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)) (volume.restrict B)) hu hDu i
  refine ⟨?_, fun i => sourceMorreyCutoffVCentredTensor_hasCompactSupport hηB hdB hB i⟩
  intro i
  have hind := (memLp_indicator_iff_restrict hB.measurableSet).2 (hlocal i)
  have heq : B.indicator (fun x => pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η)
    u Du c x i) =
      (fun x => pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i) := by
    funext x
    by_cases hx : x ∈ B
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have he : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηB h))
      have hd (j : Fin 3) : spatialDeriv η j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hdB j h))
      simp only [pressureDivergenceCutoffSourceCentredTensor, he, hd, zero_mul, add_zero,
        Finset.sum_const_zero]
  rw [heq] at hind
  exact hind

end CKN.Core.Step4
