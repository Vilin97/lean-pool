/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.GeometricConvexity

/-!
# Reinhardt hulls and comparison of logarithmic convexity conventions

The complete Reinhardt hull allows coordinatewise shrinking. The logarithmic Reinhardt hull
closes the modulus trace under geometric interpolation, including zeros, and restores rotation
symmetry. Both are minimal hulls of sets; neither definition builds in openness. For open
complete Reinhardt sets in finite dimension, the two logarithmic convexity predicates agree.
References: [Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), §§2.2–2.5 and §2.8.

## Main results

`completeReinhardtHull` and `logarithmicReinhardtHull` are the two hulls.
`completeReinhardtHull_min` and `logarithmicReinhardtHull_min` are minimality.
`hasGeometricallyConvexModuli_iff` compares geometric and logarithmic convexity on open complete
Reinhardt sets.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Set Metric
open scoped NNReal Topology

namespace SeveralComplexVariables

variable {ι : Type*} {U V : Set (ι → ℂ)}

/-- An open Reinhardt set contains a strictly larger positive modulus vector above each point. -/
theorem IsReinhardt.exists_strict_modulus_majorant [Finite ι]
    (hU : IsReinhardt U) (ho : IsOpen U) {z : ι → ℂ} (hz : z ∈ U) :
    ∃ r : ι → ℝ≥0, (fun i => (r i : ℂ)) ∈ U ∧ ∀ i, ‖z i‖₊ < r i := by
  classical
  let := Fintype.ofFinite ι
  have hz' : (fun i => (‖z i‖ : ℂ)) ∈ U := hU hz (fun i => by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho _ hz'
  let r : ι → ℝ≥0 := fun i => ‖z i‖₊ + ⟨δ / 2, by positivity⟩
  refine ⟨r, hball ?_, fun i => ?_⟩
  · rw [mem_ball, dist_pi_lt_iff hδ]
    intro i
    change dist ((‖z i‖ + δ / 2 : ℝ) : ℂ) (‖z i‖ : ℂ) < δ
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith
  · change ‖z i‖₊ < ‖z i‖₊ + ⟨δ / 2, by positivity⟩
    exact lt_add_of_pos_right _ (by exact_mod_cast half_pos hδ)

/-- Positive geometric combinations are controlled by convexity of the logarithmic image. -/
theorem IsLogarithmicallyConvex.geometricCombination_mem {r s : ι → ℝ≥0}
    (h : IsLogarithmicallyConvex U) (hr : (fun i => (r i : ℂ)) ∈ U)
    (hs : (fun i => (s i : ℂ)) ∈ U) (hrp : ∀ i, 0 < r i) (hsp : ∀ i, 0 < s i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun i => (geometricCombination a b r s i : ℂ)) ∈ U := by
  have hx : (fun i => Real.log (r i)) ∈ logarithmicImage U := by
    simpa only [logarithmicImage, mem_ofPred_eq, Real.exp_log (show (0 : ℝ) < r _ from hrp _)]
      using hr
  have hy : (fun i => Real.log (s i)) ∈ logarithmicImage U := by
    simpa only [logarithmicImage, mem_ofPred_eq, Real.exp_log (show (0 : ℝ) < s _ from hsp _)]
      using hs
  have hm := h hx hy ha hb hab
  have he : (fun i => (Real.exp (a * Real.log (r i) + b * Real.log (s i)) : ℂ)) =
      (fun i => (geometricCombination a b r s i : ℂ)) := by
    ext i
    apply congrArg Complex.ofReal
    change Real.exp (a * Real.log (r i) + b * Real.log (s i)) =
      ((r i ^ a * s i ^ b : ℝ≥0) : ℝ)
    rw [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow,
      Real.rpow_def_of_pos (show (0 : ℝ) < (r i : ℝ) from hrp i),
      Real.rpow_def_of_pos (show (0 : ℝ) < (s i : ℝ) from hsp i), ← Real.exp_add]
    congr 1
    ring
  exact he ▸ hm

/-- On open complete Reinhardt sets the logarithmic-image convention also controls zeros. -/
theorem IsLogarithmicallyConvex.hasGeometricallyConvexModuli [Finite ι]
    (h : IsLogarithmicallyConvex U) (ho : IsOpen U) (hc : IsCompleteReinhardt U) :
    HasGeometricallyConvexModuli U := by
  classical
  let := Fintype.ofFinite ι
  rintro r ⟨z, hz, rfl⟩ s ⟨w, hw, rfl⟩ a b ha hb hab
  obtain ⟨r, hr, hzr⟩ := hc.isReinhardt.exists_strict_modulus_majorant ho hz
  obtain ⟨s, hs, hws⟩ := hc.isReinhardt.exists_strict_modulus_majorant ho hw
  apply hc.isReinhardt.mem_modulusTrace_iff.mpr
  apply hc (h.geometricCombination_mem hr hs
    (fun i => lt_of_le_of_lt (show (0 : ℝ≥0) ≤ _ from zero_le) (hzr i))
    (fun i => lt_of_le_of_lt (show (0 : ℝ≥0) ≤ _ from zero_le) (hws i)) ha hb hab)
  intro i
  simp only [Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast mul_le_mul' (NNReal.rpow_le_rpow (hzr i).le ha)
    (NNReal.rpow_le_rpow (hws i).le hb)

/-- Equivalence of the two conventions on open complete Reinhardt sets. -/
theorem hasGeometricallyConvexModuli_iff [Finite ι] (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) :
    HasGeometricallyConvexModuli U ↔ IsLogarithmicallyConvex U := by
  classical
  let := Fintype.ofFinite ι
  exact
    ⟨fun h => h.isLogarithmicallyConvex hc.isReinhardt,
        fun h => h.hasGeometricallyConvexModuli ho hc⟩

/-- Away from all coordinate hyperplanes, the two convexity conventions coincide without openness or
completeness assumptions. -/
theorem hasGeometricallyConvexModuli_iff_of_nonzero (hR : IsReinhardt U)
    (hne : ∀ z ∈ U, ∀ i, z i ≠ 0) :
    HasGeometricallyConvexModuli U ↔ IsLogarithmicallyConvex U := by
  refine ⟨fun h => h.isLogarithmicallyConvex hR, ?_⟩
  intro h r hr s hs a b ha hb hab
  obtain ⟨z, hz, rfl⟩ := hr
  obtain ⟨w, hw, rfl⟩ := hs
  exact hR.mem_modulusTrace_iff.mpr (h.geometricCombination_mem
    (hR.mem_modulusTrace_iff.mp ⟨z, hz, rfl⟩)
    (hR.mem_modulusTrace_iff.mp ⟨w, hw, rfl⟩)
    (fun i => nnnorm_pos.mpr (hne z hz i)) (fun i => nnnorm_pos.mpr (hne w hw i)) ha hb hab)

/-- The smallest complete Reinhardt set containing a given set. -/
@[expose] def completeReinhardtHull (U : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {w | ∃ z ∈ U, ∀ i, ‖w i‖ ≤ ‖z i‖}

/-- A set is contained in its complete Reinhardt hull. -/
theorem subset_completeReinhardtHull : U ⊆ completeReinhardtHull U :=
  fun z hz => ⟨z, hz, fun _ => le_rfl⟩

/-- The complete Reinhardt hull is complete Reinhardt. -/
theorem isCompleteReinhardt_completeReinhardtHull : IsCompleteReinhardt (completeReinhardtHull U)
  := by
  rintro z ⟨v, hv, hz⟩ w hw
  exact ⟨v, hv, fun i => (hw i).trans (hz i)⟩

/-- Minimality of the complete Reinhardt hull. -/
theorem completeReinhardtHull_min (hUV : U ⊆ V) (hV : IsCompleteReinhardt V) :
    completeReinhardtHull U ⊆ V := by
  rintro w ⟨z, hz, hw⟩
  exact hV (hUV hz) hw

/-- Complete Reinhardt sets are fixed by their hull. -/
theorem IsCompleteReinhardt.hull_eq (h : IsCompleteReinhardt U) : completeReinhardtHull U = U :=
  Subset.antisymm (completeReinhardtHull_min Subset.rfl h) subset_completeReinhardtHull

/-- Completing an open Reinhardt set preserves openness. -/
theorem isOpen_completeReinhardtHull [Finite ι] (ho : IsOpen U) (hR : IsReinhardt U) :
    IsOpen (completeReinhardtHull U) := by
  classical
  let := Fintype.ofFinite ι
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, hwz⟩
  obtain ⟨r, hrU, hzr⟩ := hR.exists_strict_modulus_majorant ho hz
  let W : Set (ι → ℂ) := {v | ∀ i, ‖v i‖ < (r i : ℝ)}
  have hW : IsOpen W := by
    simpa only [W, ofPred_forall] using
      (isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm
        (continuous_const (y := (r i : ℝ))))
  apply Filter.mem_of_superset (hW.mem_nhds (fun i => (hwz i).trans_lt (hzr i)))
  intro v hv
  exact ⟨_, hrU, fun i => by simpa only [Complex.norm_of_nonneg (NNReal.coe_nonneg _)] using (hv
    i).le⟩

/-- The logarithmic Reinhardt hull uses geometric convexity including coordinate hyperplanes. -/
@[expose] def logarithmicReinhardtHull (U : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {z | (fun i => ‖z i‖₊) ∈ geometricConvexHull (modulusTrace U)}

/-- A set is contained in its logarithmic Reinhardt hull. -/
theorem subset_logarithmicReinhardtHull : U ⊆ logarithmicReinhardtHull U :=
  fun z hz => subset_geometricConvexHull _ ⟨z, hz, rfl⟩

/-- The logarithmic Reinhardt hull has coordinate rotation symmetry. -/
theorem isReinhardt_logarithmicReinhardtHull : IsReinhardt (logarithmicReinhardtHull U) := by
  intro z hz w hw
  have he : (fun i => ‖w i‖₊) = (fun i => ‖z i‖₊) := funext fun i => Subtype.ext (hw i)
  change (fun i => ‖w i‖₊) ∈ geometricConvexHull (modulusTrace U)
  rw [he]
  exact hz

/-- The trace of the logarithmic Reinhardt hull is the geometric convex hull of the trace. -/
theorem modulusTrace_logarithmicReinhardtHull :
    modulusTrace (logarithmicReinhardtHull U) = geometricConvexHull (modulusTrace U) := by
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hr
    refine ⟨fun i => (r i : ℂ), ?_, ?_⟩
    · simpa [logarithmicReinhardtHull] using hr
    · ext i; simp

/-- The logarithmic Reinhardt hull satisfies geometric convexity including zeros. -/
theorem hasGeometricallyConvexModuli_logarithmicReinhardtHull :
    HasGeometricallyConvexModuli (logarithmicReinhardtHull U) := by
  rw [HasGeometricallyConvexModuli, modulusTrace_logarithmicReinhardtHull]
  exact isGeometricallyConvex_geometricConvexHull _

/-- Minimality of the logarithmic Reinhardt hull among Reinhardt sets with convex moduli. -/
theorem logarithmicReinhardtHull_min (hUV : U ⊆ V) (hV : IsReinhardt V)
    (hg : HasGeometricallyConvexModuli V) : logarithmicReinhardtHull U ⊆ V := by
  intro z hz
  have hm : (fun i => ‖z i‖₊) ∈ modulusTrace V :=
    geometricConvexHull_min (image_mono hUV) hg hz
  obtain ⟨w, hw, he⟩ := hm
  exact hV hw (fun i => (congrArg (fun r : ι → ℝ≥0 => (r i : ℝ)) he).symm)

/-- A Reinhardt set with geometrically convex moduli equals its logarithmic hull. -/
theorem logarithmicReinhardtHull_eq (hU : IsReinhardt U) (hg : HasGeometricallyConvexModuli U) :
    logarithmicReinhardtHull U = U :=
  Subset.antisymm (logarithmicReinhardtHull_min Subset.rfl hU hg) subset_logarithmicReinhardtHull

/-- Openness of the geometric logarithmic hull in finite dimension, including zero coordinates. The
modulus trace of an open Reinhardt set is open, and so is its geometric convex hull. -/
theorem isOpen_logarithmicReinhardtHull [Finite ι] (ho : IsOpen U) (hU : IsReinhardt U) :
    IsOpen (logarithmicReinhardtHull U) := by
  classical
  let := Fintype.ofFinite ι
  have htrace : modulusTrace U =
      (fun r : ι → ℝ≥0 => fun i => (r i : ℂ)) ⁻¹' U := by
    ext r
    exact hU.mem_modulusTrace_iff
  have hto : IsOpen (modulusTrace U) := by
    rw [htrace]
    apply ho.preimage
    fun_prop
  exact (isOpen_geometricConvexHull hto).preimage (by fun_prop)

/-- The logarithmic Reinhardt hull is monotone. -/
theorem logarithmicReinhardtHull_mono (hUV : U ⊆ V) :
    logarithmicReinhardtHull U ⊆ logarithmicReinhardtHull V :=
  logarithmicReinhardtHull_min (hUV.trans subset_logarithmicReinhardtHull)
    isReinhardt_logarithmicReinhardtHull hasGeometricallyConvexModuli_logarithmicReinhardtHull

/-- Taking the logarithmic Reinhardt hull twice has no further effect. -/
@[simp] theorem logarithmicReinhardtHull_idem :
    logarithmicReinhardtHull (logarithmicReinhardtHull U) = logarithmicReinhardtHull U :=
  logarithmicReinhardtHull_eq isReinhardt_logarithmicReinhardtHull
    hasGeometricallyConvexModuli_logarithmicReinhardtHull

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
