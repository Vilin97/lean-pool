/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginLatticeCover
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyMajorant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergySlices
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyTime
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableRiesz
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCaccioppoliQuantitative

/-! # The fixed lattice cover of the whole carrier

A finite portion of the radius-`1/16` lattice keeps exactly the centres whose
doubled source cylinders stay inside the unit cylinder. Its cardinality,
covering and parent-inclusion properties, together with the volume bound for
the radius-`1/8` ball, are the geometric inputs of the whole-carrier pressure
mass.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat CKN.Foundation.Euclidean
open scoped ENNReal BigOperators
noncomputable section
namespace CKN.Core.Step4
attribute [local instance] Classical.propDecidable

/-- A fixed finite portion of the radius-`1/16` lattice, keeping only centres
whose doubled source cylinders remain inside the unit cylinder. -/
@[irreducible] def originBSlotLatticeIndices : Finset ((Fin 3 → ℤ) × ℤ) := by
  exact ((Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-24 : ℤ) 24)).product
    (Finset.Icc (-242 : ℤ) 0)).filter
      (fun k => vec3EuclideanNorm (originLatticeCentre (1 / 16) k).1 ≤ 3 / 4)

private theorem originBSlotLatticeIndices_mem_iff (k : (Fin 3 → ℤ) × ℤ) :
    k ∈ originBSlotLatticeIndices ↔
      ((∀ j : Fin 3, k.1 j ∈ Finset.Icc (-24 : ℤ) 24) ∧ k.2 ∈ Finset.Icc (-242 : ℤ) 0) ∧
      vec3EuclideanNorm (originLatticeCentre (1 / 16) k).1 ≤ 3 / 4 := by
  unfold originBSlotLatticeIndices
  rw [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Fintype.mem_piFinset]

/-- The fixed finite lattice has an explicit absolute cardinality bound. -/
theorem originBSlotLatticeIndices_card_le :
    originBSlotLatticeIndices.card ≤ 49 ^ 3 * 243 := by
  unfold originBSlotLatticeIndices
  apply (Finset.card_filter_le _ _).trans_eq
  have hp := Finset.card_product
    (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-24 : ℤ) 24)) (Finset.Icc (-242 : ℤ) 0)
  rw [Fintype.card_piFinset] at hp
  norm_num [Int.card_Icc, Finset.prod_const] at hp ⊢

/-- The fixed finite lattice covers the entire origin carrier of radius
`11/16`, including its top time face. -/
theorem originBSlotLatticeIndices_covers
    (w : ParabolicPoint) (hw : w ∈ parabolicCylinder 0 0 (11 / 16)) :
    ∃ k ∈ originBSlotLatticeIndices,
      w ∈ parabolicCylinder (originLatticeCentre (1 / 16) k).1
        (originLatticeCentre (1 / 16) k).2 (1 / 16) := by
  obtain ⟨k, hk⟩ := originLattice_covers (1 / 16) (by norm_num) w
  let k' : (Fin 3 → ℤ) × ℤ := (k.1, min k.2 0)
  have hwx : vec3EuclideanNorm w.1 < 11 / 16 := by simpa [vec3Ball] using hw.1
  have hwt : -(121 / 256 : ℝ) < w.2 ∧ w.2 ≤ 0 := by
    simpa only [mem_Ioc, show (0 : ℝ) - (11 / 16) ^ 2 = -(121 / 256) by norm_num] using hw.2
  have hx : vec3EuclideanNorm (originLatticeCentre (1 / 16) k').1 ≤ 3 / 4 := by
    have htri := vec3EuclideanNorm_sub_le w.1 (w.1 - (originLatticeCentre (1 / 16) k).1)
    rw [sub_sub_cancel] at htri
    have hnear := hk.1
    change vec3EuclideanNorm (w.1 - (originLatticeCentre (1 / 16) k).1) < 1 / 16 at hnear
    change vec3EuclideanNorm (originLatticeCentre (1 / 16) k).1 ≤ 3 / 4
    linarith only [htri, hwx, hnear]
  have hkt : (min k.2 0 : ℤ) ≤ 0 := min_le_right _ _
  have ht : w ∈ parabolicCylinder (originLatticeCentre (1 / 16) k').1
      (originLatticeCentre (1 / 16) k').2 (1 / 16) := by
    refine ⟨hk.1, ?_⟩
    by_cases h : k.2 ≤ 0
    · simpa only [k', min_eq_left h] using hk.2
    · have hpos : (0 : ℝ) < (k.2 : ℝ) := by exact_mod_cast lt_of_not_ge h
      have hnear := hk.2.1
      change (1 / 16 : ℝ) ^ 2 / 2 * (k.2 : ℝ) - (1 / 16) ^ 2 < w.2 at hnear
      change (1 / 16 : ℝ) ^ 2 / 2 * (min k.2 0 : ℤ) - (1 / 16) ^ 2 < w.2 ∧
        w.2 ≤ (1 / 16 : ℝ) ^ 2 / 2 * (min k.2 0 : ℤ)
      rw [min_eq_right (le_of_not_ge h)]
      push_cast
      constructor
      · nlinarith only [hnear, hpos]
      · simpa using hwt.2
  have hidx (j : Fin 3) : k'.1 j ∈ Finset.Icc (-24 : ℤ) 24 := by
    have hh := (abs_apply_le_vec3EuclideanNorm (originLatticeCentre (1 / 16) k').1 j).trans hx
    change |(1 / 16 / 2 : ℝ) * (k'.1 j : ℝ)| ≤ 3 / 4 at hh
    obtain ⟨hl, hu⟩ := abs_le.mp hh
    have hl' : (-24 : ℝ) ≤ (k'.1 j : ℝ) := by linarith only [hl]
    have hu' : (k'.1 j : ℝ) ≤ 24 := by linarith only [hu]
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl', by exact_mod_cast hu'⟩
  have htidx : k'.2 ∈ Finset.Icc (-242 : ℤ) 0 := by
    have hh := ht.2.2
    change w.2 ≤ (1 / 16 : ℝ) ^ 2 / 2 * (k'.2 : ℝ) at hh
    have hh' : (-242 : ℝ) ≤ (k'.2 : ℝ) := by linarith only [hh, hwt.1]
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh', hkt⟩
  refine ⟨k', ?_, ht⟩
  unfold originBSlotLatticeIndices
  change k' ∈ ((Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-24 : ℤ) 24)).product
    (Finset.Icc (-242 : ℤ) 0)).filter _
  rw [Finset.mem_filter]
  refine ⟨?_, hx⟩
  rw [Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · rw [Fintype.mem_piFinset]
    exact hidx
  · exact htidx

/-- Every retained centre has its radius-`1/4` energy cylinder inside the
unit data cylinder. Its source radius is `1/8` and covered-cell radius `1/16`. -/
theorem originBSlotLatticeIndices_parent_subset
    {k : (Fin 3 → ℤ) × ℤ} (hk : k ∈ originBSlotLatticeIndices) :
    parabolicCylinder (originLatticeCentre (1 / 16) k).1
      (originLatticeCentre (1 / 16) k).2 (1 / 4) ⊆ parabolicCylinder 0 0 1 := by
  obtain ⟨⟨_hspace, htime⟩, hx⟩ := (originBSlotLatticeIndices_mem_iff k).mp hk
  have ht := Finset.mem_Icc.mp htime
  have htl : (-242 : ℝ) ≤ (k.2 : ℝ) := by exact_mod_cast ht.1
  have htu : (k.2 : ℝ) ≤ 0 := by exact_mod_cast ht.2
  intro w hw
  constructor
  · have htri := vec3EuclideanNorm_add_le
      (w.1 - (originLatticeCentre (1 / 16) k).1) (originLatticeCentre (1 / 16) k).1
    rw [sub_add_cancel] at htri
    have hnear := hw.1
    change vec3EuclideanNorm (w.1 - (originLatticeCentre (1 / 16) k).1) < 1 / 4 at hnear
    change vec3EuclideanNorm (w.1 - 0) < 1
    rw [sub_zero]
    linarith only [htri, hx, hnear]
  · have hnear := hw.2
    change (1 / 16 : ℝ) ^ 2 / 2 * (k.2 : ℝ) - (1 / 4) ^ 2 < w.2 ∧
      w.2 ≤ (1 / 16 : ℝ) ^ 2 / 2 * (k.2 : ℝ) at hnear
    change (0 : ℝ) - 1 ^ 2 < w.2 ∧ w.2 ≤ 0
    constructor <;> nlinarith only [hnear.1, hnear.2, htl, htu]

/-- The radius-`1/8` ball has volume at most one. -/
theorem bslot_eighth_ball_volume_le_one :
    volume (vec3Ball (0 : Vec3) (1 / 8)) ≤ 1 := by
  rw [volume_vec3Ball_zero]
  have hpi : ENNReal.ofReal (Real.pi * 4 / 3) ≤ ENNReal.ofReal (16 / 3 : ℝ) :=
    ENNReal.ofReal_le_ofReal (by linarith only [Real.pi_lt_four])
  calc
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) ^ 3 * ENNReal.ofReal (16 / 3 : ℝ) :=
      mul_le_mul' le_rfl hpi
    _ ≤ 1 := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 8),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

end CKN.Core.Step4
