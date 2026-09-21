/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.Process
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # Continuous State -/

namespace FD1D

noncomputable section

open Set MeasureTheory

namespace V5

/-!
# Continuous coordinate state

The spatial state records only the live coordinates. Their dyadic labels are
recovered deterministically, so replacing one coordinate updates the exact
spatial configuration and its finite count projection pathwise.
-/

/-- The `m` labeled live supply coordinates in the unit interval. -/
abbrev SpatialState (m : ℕ) := Fin m → unitInterval

/-- The dyadic leaf assigned to each coordinate of a spatial state. -/
def spatialLeaves (L : ℕ) (s : SpatialState m) : Fin m → DyadicNode L :=
  fun j => DyadicMass.uniformArrivalLeaf L (s j : ℝ)

/-- Convert a coordinate state to its certified spatial configuration. -/
def toConfiguration (L : ℕ) (s : SpatialState m) :
    SupplyConfiguration L m where
  location j := s j
  leaf := spatialLeaves L s
  location_mem_unit j := (s j).property
  location_mem_cell j :=
    DyadicMass.uniformArrival_mem_dyadicCell L (s j).property

@[simp]
theorem toConfiguration_location (L : ℕ) (s : SpatialState m) (j : Fin m) :
    (toConfiguration L s).location j = s j :=
  rfl

@[simp]
theorem toConfiguration_leaf (L : ℕ) (s : SpatialState m) (j : Fin m) :
    (toConfiguration L s).leaf j = spatialLeaves L s j :=
  rfl

/-- The finite inventory-count projection of a coordinate state. -/
def spatialCount (L : ℕ) (s : SpatialState m) :
    InventoryState (DyadicNode L) m :=
  (toConfiguration L s).countState

@[simp]
theorem toConfiguration_countState (L : ℕ) (s : SpatialState m) :
    (toConfiguration L s).countState = spatialCount L s :=
  rfl

private theorem supplyConfiguration_ext
    {C D : SupplyConfiguration L m}
    (hlocation : C.location = D.location) (hleaf : C.leaf = D.leaf) :
    C = D := by
  cases C
  cases D
  cases hlocation
  cases hleaf
  rfl

private def configurationOfLeaves (L : ℕ)
    (leaves : Fin m → DyadicNode L) : SupplyConfiguration L m where
  location j := dyadicCellLeft (leaves j)
  leaf := leaves
  location_mem_unit j :=
    dyadicCell_subset_unit (leaves j)
      ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩
  location_mem_cell _j :=
    ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩

private theorem configurationOfLeaves_countState_eq
    (L : ℕ) (s : SpatialState m) :
    (configurationOfLeaves L (spatialLeaves L s)).countState =
      spatialCount L s := by
  apply InventoryState.ext
  intro i
  rfl

/-! ## Measurable projections -/

theorem spatialState_eval_measurable (j : Fin m) :
    Measurable (fun s : SpatialState m => s j) :=
  measurable_pi_apply j

theorem spatialCoordinate_measurable (j : Fin m) :
    Measurable (fun s : SpatialState m => (s j : ℝ)) :=
  measurable_subtype_coe.comp (spatialState_eval_measurable j)

theorem spatialLeaf_measurable (L : ℕ) (j : Fin m) :
    Measurable (fun s : SpatialState m => spatialLeaves L s j) := by
  exact (DyadicMass.uniformArrivalMass L).selectedIndex_measurable.comp
    (spatialCoordinate_measurable j)

theorem spatialLeaves_measurable (L : ℕ) :
    Measurable (spatialLeaves L : SpatialState m → Fin m → DyadicNode L) := by
  rw [measurable_pi_iff]
  exact spatialLeaf_measurable L

theorem spatialCount_measurable (L : ℕ) :
    Measurable (spatialCount L :
      SpatialState m → InventoryState (DyadicNode L) m) := by
  have hcount :
      Measurable (fun leaves : Fin m → DyadicNode L =>
        (configurationOfLeaves L leaves).countState) :=
    measurable_of_finite _
  have hcomp := hcount.comp (spatialLeaves_measurable (m := m) L)
  have heq :
      (fun leaves : Fin m → DyadicNode L =>
        (configurationOfLeaves L leaves).countState) ∘ spatialLeaves L =
        spatialCount L := by
    funext s
    exact configurationOfLeaves_countState_eq L s
  rw [← heq]
  exact hcomp

/-! ## Selected labels and coordinate update -/

/-- The concrete supply label selected from a coordinate state. -/
def spatialSelectedLabel (L : ℕ) (a : ℝ) (fallback : Fin m)
    (s : SpatialState m) (u : unitInterval) : Fin m :=
  Dynamics.selectedSupplyLabel
    a (toConfiguration L s) fallback (u : ℝ)

private theorem selectedSupplyLabel_congr_leaf
    (a : ℝ) (fallback : Fin m) (u : ℝ)
    (C D : SupplyConfiguration L m) (hleaf : C.leaf = D.leaf) :
    Dynamics.selectedSupplyLabel a C fallback u =
      Dynamics.selectedSupplyLabel a D fallback u := by
  have hcount : C.countState = D.countState := by
    apply InventoryState.ext
    intro i
    change
      (Finset.univ.filter fun j : Fin m => C.leaf j = i).card =
        (Finset.univ.filter fun j : Fin m => D.leaf j = i).card
    rw [hleaf]
  have hrepresentative :
      ∀ i, C.representative fallback i = D.representative fallback i := by
    intro i
    unfold SupplyConfiguration.representative
    rw [hleaf]
  unfold Dynamics.selectedSupplyLabel
    SupplyConfiguration.selectedSupplyIndex
  rw [hcount]
  exact hrepresentative _

private theorem spatialSelectedLabel_eq_configurationOfLeaves
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (s : SpatialState m) (u : unitInterval) :
    spatialSelectedLabel L a fallback s u =
      Dynamics.selectedSupplyLabel a
        (configurationOfLeaves L (spatialLeaves L s)) fallback (u : ℝ) := by
  apply selectedSupplyLabel_congr_leaf
  rfl

private theorem selectedSupplyLabel_measurable_demand
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m) :
    Measurable (fun u : unitInterval =>
      Dynamics.selectedSupplyLabel a C fallback (u : ℝ)) := by
  exact
    (measurable_of_finite
      (fun i : DyadicNode L => C.representative fallback i)).comp
      ((Dynamics.stateDyadicMass a C.countState).selectedIndex_measurable.comp
        measurable_subtype_coe)

private theorem selectedSupplyLabel_configurationOfLeaves_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (fun p : (Fin m → DyadicNode L) × unitInterval =>
      Dynamics.selectedSupplyLabel a
        (configurationOfLeaves L p.1) fallback (p.2 : ℝ)) := by
  apply measurable_from_prod_countable_right
  intro leaves
  exact selectedSupplyLabel_measurable_demand
    a (configurationOfLeaves L leaves) fallback

/-- Joint measurability of the selected label in state and demand. -/
theorem spatialSelectedLabel_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (fun p : SpatialState m × unitInterval =>
      spatialSelectedLabel L a fallback p.1 p.2) := by
  have hsource :
      Measurable (fun p : SpatialState m × unitInterval =>
        (spatialLeaves L p.1, p.2)) :=
    ((spatialLeaves_measurable (m := m) L).comp measurable_fst).prodMk
      measurable_snd
  have hcomp :=
    (selectedSupplyLabel_configurationOfLeaves_measurable
      (m := m) L a fallback).comp hsource
  have heq :
      (fun p : (Fin m → DyadicNode L) × unitInterval =>
        Dynamics.selectedSupplyLabel a
          (configurationOfLeaves L p.1) fallback (p.2 : ℝ)) ∘
          (fun p : SpatialState m × unitInterval =>
            (spatialLeaves L p.1, p.2)) =
        fun p => spatialSelectedLabel L a fallback p.1 p.2 := by
    funext p
    exact (spatialSelectedLabel_eq_configurationOfLeaves
      L a fallback p.1 p.2).symm
  rw [← heq]
  exact hcomp

theorem spatialSelectedLabel_demand_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) (s : SpatialState m) :
    Measurable (fun u : unitInterval =>
      spatialSelectedLabel L a fallback s u) :=
  (spatialSelectedLabel_measurable L a fallback).comp
    (measurable_const.prodMk measurable_id)

/--
Replace the selected supply coordinate by a replenishment coordinate. The
noise pair consists of demand first and replenishment second.
-/
def spatialStep (L : ℕ) (a : ℝ) (fallback : Fin m)
    (s : SpatialState m) (z : unitInterval × unitInterval) :
    SpatialState m :=
  Function.update s (spatialSelectedLabel L a fallback s z.1) z.2

/-- Coordinate update and `actualStep` are the same certified configuration. -/
@[simp]
theorem toConfiguration_spatialStep
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (s : SpatialState m) (z : unitInterval × unitInterval) :
    toConfiguration L (spatialStep L a fallback s z) =
      Dynamics.actualStep a (toConfiguration L s) fallback
        (z.1 : ℝ) (z.2 : ℝ) z.2.property := by
  apply supplyConfiguration_ext
  · funext j
    by_cases hj :
        j = Dynamics.selectedSupplyLabel
          a (toConfiguration L s) fallback (z.1 : ℝ)
    · subst j
      rw [Dynamics.actualStep_location_selected]
      simp only [toConfiguration_location, spatialStep, spatialSelectedLabel,
        Function.update_self]
    · rw [Dynamics.actualStep_location_of_ne
        a (toConfiguration L s) fallback
        (z.1 : ℝ) (z.2 : ℝ) z.2.property j hj]
      simp only [toConfiguration_location, spatialStep, spatialSelectedLabel,
        Function.update_of_ne hj]
  · funext j
    by_cases hj :
        j = Dynamics.selectedSupplyLabel
          a (toConfiguration L s) fallback (z.1 : ℝ)
    · subst j
      rw [Dynamics.actualStep_leaf_selected]
      simp only [toConfiguration_leaf, spatialLeaves, spatialStep,
        spatialSelectedLabel, Function.update_self]
    · rw [Dynamics.actualStep_leaf_of_ne
        a (toConfiguration L s) fallback
        (z.1 : ℝ) (z.2 : ℝ) z.2.property j hj]
      simp only [toConfiguration_leaf, spatialLeaves, spatialStep,
        spatialSelectedLabel, Function.update_of_ne hj]

/-- The coordinate update projects to the corresponding finite leaf move. -/
@[simp]
theorem spatialCount_spatialStep
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (s : SpatialState m) (z : unitInterval × unitInterval) :
    spatialCount L (spatialStep L a fallback s z) =
      InventoryState.move (spatialCount L s)
        (Dynamics.selectedDeletedLeaf
          a (toConfiguration L s) fallback (z.1 : ℝ))
        (DyadicMass.uniformArrivalLeaf L (z.2 : ℝ)) := by
  simpa only [spatialCount, toConfiguration_spatialStep] using
    Dynamics.actualStep_countState
      a (toConfiguration L s) fallback
        (z.1 : ℝ) (z.2 : ℝ) z.2.property

/-- Away from demand zero, the deleted leaf is the policy's selected index. -/
theorem spatialCount_spatialStep_eq_selectedIndex
    (L : ℕ) (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (s : SpatialState m)
    (z : unitInterval × unitInterval) (hz : (z.1 : ℝ) ≠ 0) :
    spatialCount L (spatialStep L a fallback s z) =
      InventoryState.move (spatialCount L s)
        ((Dynamics.stateDyadicMass a (spatialCount L s)).selectedIndex
          (z.1 : ℝ))
        (DyadicMass.uniformArrivalLeaf L (z.2 : ℝ)) := by
  rw [spatialCount_spatialStep]
  rw [Dynamics.selectedDeletedLeaf_eq_selectedIndex
    a ha hm (toConfiguration L s) fallback z.1.property hz]
  rfl

/-- Joint measurability of one step in the state and its two noise inputs. -/
theorem spatialStep_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (fun p : SpatialState m × (unitInterval × unitInterval) =>
      spatialStep L a fallback p.1 p.2) := by
  rw [measurable_pi_iff]
  intro j
  have hlabel :
      Measurable (fun p : SpatialState m × (unitInterval × unitInterval) =>
        spatialSelectedLabel L a fallback p.1 p.2.1) :=
    (spatialSelectedLabel_measurable L a fallback).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hselected :
      MeasurableSet
        {p : SpatialState m × (unitInterval × unitInterval) |
          j = spatialSelectedLabel L a fallback p.1 p.2.1} :=
    measurableSet_eq_fun measurable_const hlabel
  have hreplenishment :
      Measurable
        (fun p : SpatialState m × (unitInterval × unitInterval) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hcurrent :
      Measurable
        (fun p : SpatialState m × (unitInterval × unitInterval) => p.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have heq :
      (fun p : SpatialState m × (unitInterval × unitInterval) =>
        spatialStep L a fallback p.1 p.2 j) =
        fun p =>
          if j = spatialSelectedLabel L a fallback p.1 p.2.1 then
            p.2.2
          else
            p.1 j := by
    funext p
    by_cases hj :
        j = spatialSelectedLabel L a fallback p.1 p.2.1
    · simp [spatialStep, hj]
    · simp [spatialStep, hj]
  rw [heq]
  exact Measurable.ite hselected hreplenishment hcurrent

theorem spatialStep_noise_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) (s : SpatialState m) :
    Measurable (spatialStep L a fallback s) :=
  (spatialStep_measurable L a fallback).comp
    (measurable_const.prodMk measurable_id)

end V5

end

end FD1D
