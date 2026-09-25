/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Tricycle.HelperLemma
import LeanPool.BrillNoetherGraphs.Utilities.Gonality.GonalityTransport
import Mathlib.Tactic

/-!
# Lemma 3.6 and Corollary 3.7

Van Dobben de Bruyn–Smit–van der Wegen, Lemma 3.6: *on any subdivision `H` of
the minimal tricycle, a positive-rank `v₀`-reduced divisor of degree at most `5`
carries exactly two chips on `v₀` and exactly one chip on each transition path.*
Corollary 3.7, `dgon(H) ≥ 5`, is then immediate, and holds for **every** length
vector — which is what makes the left-hand side of the tricycle gap a minimum
over all `σ_k` rather than a bound at one `k`.

## How the bookkeeping is kept linear

The source's regions `Cᵢ` and its closed transition paths overlap. To keep the
chip counting explicit, every count is expressed in the **slot coordinate system** of
`Utilities/Subdivision/SpecBurning.lean` — the seven core-vertex values
`D (coreVertex v)` and the fifteen slot-interior totals `slotInteriorChips D e`.
Each geometric conclusion is then a linear inequality in those twenty-two
integers, the degree identity is one more, and `linarith` finishes.  No `Finset`
union, no inclusion–exclusion.
-/

namespace Utilities.Tricycle

open Finset

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec
open Utilities.Gonality

variable {spec : Spec 7 15}

/-! ## Aggregates -/

/-- The chips on the closed transition path `i`, from `vᵢ⁺` to `vᵢ₊₁⁻`. -/
def transitionPathChips (spec : Spec 7 15) (D : CFDiv spec.graph) (i : Fin 3) : ℤ :=
  D (spec.coreVertex (vPlus i)) + spec.slotInteriorChips D (transitionSlot i)
    + D (spec.coreVertex (vMinus (i + 1)))

/-- The chips on the cycle `Cᵢ`. -/
def cycleChips (spec : Spec 7 15) (D : CFDiv spec.graph) (i : Fin 3) : ℤ :=
  D (spec.coreVertex (vMinus i)) + D (spec.coreVertex (vPlus i))
    + spec.slotInteriorChips D (cycleSlot i 0) + spec.slotInteriorChips D (cycleSlot i 1)

/-- The chips on the interiors of the two spokes meeting `Cᵢ`. -/
def spokePairChips (spec : Spec 7 15) (D : CFDiv spec.graph) (i : Fin 3) : ℤ :=
  spec.slotInteriorChips D (spokeMinus i) + spec.slotInteriorChips D (spokePlus i)

/-! ## Transporting the slot dictionary to an arbitrary subdivision -/

theorem cycleSlot_tail (hcore : spec.core = tricycleCore) (i : Fin 3) (j : Fin 2) :
    spec.core.tail (cycleSlot i j) = vMinus i := by
  rw [hcore]; exact (cycleSlot_ends i j).1

theorem cycleSlot_head (hcore : spec.core = tricycleCore) (i : Fin 3) (j : Fin 2) :
    spec.core.head (cycleSlot i j) = vPlus i := by
  rw [hcore]; exact (cycleSlot_ends i j).2

theorem transitionSlot_tail (hcore : spec.core = tricycleCore) (i : Fin 3) :
    spec.core.tail (transitionSlot i) = vPlus i := by
  rw [hcore]; exact (transitionSlot_ends i).1

theorem transitionSlot_head (hcore : spec.core = tricycleCore) (i : Fin 3) :
    spec.core.head (transitionSlot i) = vMinus (i + 1) := by
  rw [hcore]; exact (transitionSlot_ends i).2

theorem cycleSlot_ne (i : Fin 3) : cycleSlot i 0 ≠ cycleSlot i 1 := by
  fin_cases i <;> decide

/-! ## Cycle blocking on the tricycle -/

variable {D : CFDiv spec.graph} {w : spec.Vertex}

/-- If `vᵢ⁻` burns and `vᵢ⁺` does not, the cycle `Cᵢ` carries two chips. -/
theorem two_le_cycleChips_of_minus_burned (hcore : spec.core = tricycleCore)
    (hEff : effective D) (i : Fin 3)
    (hu : spec.coreVertex (vMinus i) ∈ burned spec.graph D w)
    (hu' : spec.coreVertex (vPlus i) ∉ burned spec.graph D w) :
    2 ≤ cycleChips spec D i := by
  have h := two_le_chips_of_cycle_tail_burned (spec := spec) (D := D) (w := w) hEff
    (e₁ := cycleSlot i 0) (e₂ := cycleSlot i 1) (cycleSlot_ne i)
    (by rw [cycleSlot_tail hcore, cycleSlot_tail hcore])
    (by rw [cycleSlot_head hcore, cycleSlot_head hcore])
    (by rw [cycleSlot_tail hcore]; exact hu)
    (by rw [cycleSlot_head hcore]; exact hu')
  rw [cycleSlot_head hcore] at h
  have hnn : 0 ≤ D (spec.coreVertex (vMinus i)) := hEff _
  unfold cycleChips
  omega

/-- If `vᵢ⁺` burns and `vᵢ⁻` does not, the cycle `Cᵢ` carries two chips. -/
theorem two_le_cycleChips_of_plus_burned (hcore : spec.core = tricycleCore)
    (hEff : effective D) (i : Fin 3)
    (hu : spec.coreVertex (vPlus i) ∈ burned spec.graph D w)
    (hu' : spec.coreVertex (vMinus i) ∉ burned spec.graph D w) :
    2 ≤ cycleChips spec D i := by
  have h := two_le_chips_of_cycle_head_burned (spec := spec) (D := D) (w := w) hEff
    (e₁ := cycleSlot i 0) (e₂ := cycleSlot i 1) (cycleSlot_ne i)
    (by rw [cycleSlot_tail hcore, cycleSlot_tail hcore])
    (by rw [cycleSlot_head hcore, cycleSlot_head hcore])
    (by rw [cycleSlot_head hcore]; exact hu)
    (by rw [cycleSlot_tail hcore]; exact hu')
  rw [cycleSlot_tail hcore] at h
  have hnn : 0 ≤ D (spec.coreVertex (vPlus i)) := hEff _
  unfold cycleChips
  omega

/-! ## Chips on a transition path from a burned/unburned split -/

/-- The fire enters transition path `i` at `vᵢ⁺` and is stopped before
`vᵢ₊₁⁻`: the path carries a chip strictly past `vᵢ⁺`. -/
theorem one_le_transitionPath_up (hcore : spec.core = tricycleCore)
    (hEff : effective D) (i : Fin 3)
    (hb : spec.coreVertex (vPlus i) ∈ burned spec.graph D w)
    (hnb : spec.coreVertex (vMinus (i + 1)) ∉ burned spec.graph D w) :
    1 ≤ spec.slotInteriorChips D (transitionSlot i)
      + D (spec.coreVertex (vMinus (i + 1))) := by
  have ha : spec.slotVertex (transitionSlot i) 0 ∈ burned spec.graph D w := by
    rw [slotVertex_zero, transitionSlot_tail hcore]; exact hb
  have hbb : spec.slotVertex (transitionSlot i) (spec.length (transitionSlot i))
      ∉ burned spec.graph D w := by
    rw [slotVertex_length, transitionSlot_head hcore]; exact hnb
  obtain ⟨k, hk0, hkle, hkchip, -, -⟩ :=
    exists_chip_up ha hbb (Nat.zero_le _) (le_refl _)
  have hnn1 : 0 ≤ spec.slotInteriorChips D (transitionSlot i) :=
    slotInteriorChips_nonneg hEff _
  have hnn2 : 0 ≤ D (spec.coreVertex (vMinus (i + 1))) := hEff _
  rcases eq_or_lt_of_le hkle with heq | hlt
  · rw [heq, slotVertex_length, transitionSlot_head hcore] at hkchip
    omega
  · have := apply_slotVertex_le_slotInteriorChips hEff (edge := transitionSlot i) hk0 hlt
    omega

/-- The fire enters transition path `i` at `vᵢ₊₁⁻` and is stopped before
`vᵢ⁺`. -/
theorem one_le_transitionPath_down (hcore : spec.core = tricycleCore)
    (hEff : effective D) (i : Fin 3)
    (hb : spec.coreVertex (vMinus (i + 1)) ∈ burned spec.graph D w)
    (hnb : spec.coreVertex (vPlus i) ∉ burned spec.graph D w) :
    1 ≤ spec.slotInteriorChips D (transitionSlot i)
      + D (spec.coreVertex (vPlus i)) := by
  have ha : spec.slotVertex (transitionSlot i) (spec.length (transitionSlot i))
      ∈ burned spec.graph D w := by
    rw [slotVertex_length, transitionSlot_head hcore]; exact hb
  have hbb : spec.slotVertex (transitionSlot i) 0 ∉ burned spec.graph D w := by
    rw [slotVertex_zero, transitionSlot_tail hcore]; exact hnb
  obtain ⟨k, -, hklt, hkchip, -, -⟩ :=
    exists_chip_down ha hbb (Nat.zero_le _) (le_refl _)
  have hnn1 : 0 ≤ spec.slotInteriorChips D (transitionSlot i) :=
    slotInteriorChips_nonneg hEff _
  have hnn2 : 0 ≤ D (spec.coreVertex (vPlus i)) := hEff _
  rcases Nat.eq_zero_or_pos k with hz | hpos
  · rw [hz, slotVertex_zero, transitionSlot_tail hcore] at hkchip
    omega
  · have := apply_slotVertex_le_slotInteriorChips hEff (edge := transitionSlot i) hpos hklt
    omega

/-- A chip-free transition path conducts the fire from `vᵢ⁺` to `vᵢ₊₁⁻`. -/
theorem burned_vMinus_of_chipFree (hcore : spec.core = tricycleCore)
    (hEff : effective D) (i : Fin 3)
    (hzero : transitionPathChips spec D i = 0)
    (hb : spec.coreVertex (vPlus i) ∈ burned spec.graph D w) :
    spec.coreVertex (vMinus (i + 1)) ∈ burned spec.graph D w := by
  have hnn1 : 0 ≤ D (spec.coreVertex (vPlus i)) := hEff _
  have hnn2 : 0 ≤ spec.slotInteriorChips D (transitionSlot i) :=
    slotInteriorChips_nonneg hEff _
  have hnn3 : 0 ≤ D (spec.coreVertex (vMinus (i + 1))) := hEff _
  have hic : spec.slotInteriorChips D (transitionSlot i) = 0 := by
    unfold transitionPathChips at hzero; omega
  have hhead : D (spec.coreVertex (vMinus (i + 1))) = 0 := by
    unfold transitionPathChips at hzero; omega
  have ha : spec.slotVertex (transitionSlot i) 0 ∈ burned spec.graph D w := by
    rw [slotVertex_zero, transitionSlot_tail hcore]; exact hb
  have hres := mem_burned_slotVertex_of_chipFree_up ha
    (Nat.zero_le (spec.length (transitionSlot i))) (le_refl _) ?_
  · rwa [slotVertex_length, transitionSlot_head hcore] at hres
  · intro k hk0 hkle
    rcases eq_or_lt_of_le hkle with heq | hlt
    · rw [heq, slotVertex_length, transitionSlot_head hcore]
      omega
    · have := apply_slotVertex_le_slotInteriorChips hEff (edge := transitionSlot i) hk0 hlt
      omega

/-! ## Evaluating the slot dictionary at concrete indices -/

section Eval

@[simp] theorem vMinus_0 : vMinus 0 = 1 := by decide
@[simp] theorem vMinus_1 : vMinus 1 = 3 := by decide
@[simp] theorem vMinus_2 : vMinus 2 = 5 := by decide
@[simp] theorem vPlus_0 : vPlus 0 = 2 := by decide
@[simp] theorem vPlus_1 : vPlus 1 = 4 := by decide
@[simp] theorem vPlus_2 : vPlus 2 = 6 := by decide
@[simp] theorem spokeMinus_0 : spokeMinus 0 = 0 := by decide
@[simp] theorem spokeMinus_1 : spokeMinus 1 = 2 := by decide
@[simp] theorem spokeMinus_2 : spokeMinus 2 = 4 := by decide
@[simp] theorem spokePlus_0 : spokePlus 0 = 1 := by decide
@[simp] theorem spokePlus_1 : spokePlus 1 = 3 := by decide
@[simp] theorem spokePlus_2 : spokePlus 2 = 5 := by decide
@[simp] theorem cycleSlot_00 : cycleSlot 0 0 = 6 := by decide
@[simp] theorem cycleSlot_01 : cycleSlot 0 1 = 7 := by decide
@[simp] theorem cycleSlot_10 : cycleSlot 1 0 = 8 := by decide
@[simp] theorem cycleSlot_11 : cycleSlot 1 1 = 9 := by decide
@[simp] theorem cycleSlot_20 : cycleSlot 2 0 = 10 := by decide
@[simp] theorem cycleSlot_21 : cycleSlot 2 1 = 11 := by decide
@[simp] theorem transitionSlot_0 : transitionSlot 0 = 12 := by decide
@[simp] theorem transitionSlot_1 : transitionSlot 1 = 13 := by decide
@[simp] theorem transitionSlot_2 : transitionSlot 2 = 14 := by decide
@[simp] theorem transitionOf_0 : transitionOf 0 = 1 := by decide
@[simp] theorem transitionOf_1 : transitionOf 1 = 2 := by decide
@[simp] theorem transitionOf_2 : transitionOf 2 = 3 := by decide
@[simp] theorem transitionOf_3 : transitionOf 3 = 4 := by decide
@[simp] theorem transitionOf_4 : transitionOf 4 = 5 := by decide
@[simp] theorem transitionOf_5 : transitionOf 5 = 6 := by decide
@[simp] theorem spokeOf_0 : spokeOf 0 = 0 := by decide
@[simp] theorem spokeOf_1 : spokeOf 1 = 1 := by decide
@[simp] theorem spokeOf_2 : spokeOf 2 = 2 := by decide
@[simp] theorem spokeOf_3 : spokeOf 3 = 3 := by decide
@[simp] theorem spokeOf_4 : spokeOf 4 = 4 := by decide
@[simp] theorem spokeOf_5 : spokeOf 5 = 5 := by decide
@[simp] theorem fin3_01 : (0 : Fin 3) + 1 = 1 := by decide
@[simp] theorem fin3_11 : (1 : Fin 3) + 1 = 2 := by decide
@[simp] theorem fin3_21 : (2 : Fin 3) + 1 = 0 := by decide
@[simp] theorem fin3_02 : (0 : Fin 3) + 2 = 2 := by decide
@[simp] theorem fin3_12 : (1 : Fin 3) + 2 = 0 := by decide
@[simp] theorem fin3_22 : (2 : Fin 3) + 2 = 1 := by decide

theorem fin3_add_two_add_one (j : Fin 3) : j + 2 + 1 = j := by decide +revert

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by decide +revert

/-- The `Fin 6` spoke index of `vᵢ⁻`. -/
def spokeIndexMinus : Fin 3 → Fin 6 := ![0, 2, 4]

/-- The `Fin 6` spoke index of `vᵢ⁺`. -/
def spokeIndexPlus : Fin 3 → Fin 6 := ![1, 3, 5]

theorem spokeIndex_ne (i : Fin 3) : spokeIndexMinus i ≠ spokeIndexPlus i := by
  decide +revert

theorem transitionOf_spokeIndexMinus (i : Fin 3) :
    transitionOf (spokeIndexMinus i) = vMinus i := by decide +revert

theorem transitionOf_spokeIndexPlus (i : Fin 3) :
    transitionOf (spokeIndexPlus i) = vPlus i := by decide +revert

theorem spokeOf_spokeIndexMinus (i : Fin 3) :
    spokeOf (spokeIndexMinus i) = spokeMinus i := by decide +revert

theorem spokeOf_spokeIndexPlus (i : Fin 3) :
    spokeOf (spokeIndexPlus i) = spokePlus i := by decide +revert

end Eval

/-! ## The degree identity in slot coordinates -/

/-- Total degree, written out in the twenty-two slot coordinates. -/
theorem deg_expand (spec : Spec 7 15) (D : CFDiv spec.graph) :
    deg D =
      (D (spec.coreVertex 0) + D (spec.coreVertex 1) + D (spec.coreVertex 2)
        + D (spec.coreVertex 3) + D (spec.coreVertex 4) + D (spec.coreVertex 5)
        + D (spec.coreVertex 6))
      + (spec.slotInteriorChips D 0 + spec.slotInteriorChips D 1
        + spec.slotInteriorChips D 2 + spec.slotInteriorChips D 3
        + spec.slotInteriorChips D 4 + spec.slotInteriorChips D 5
        + spec.slotInteriorChips D 6 + spec.slotInteriorChips D 7
        + spec.slotInteriorChips D 8 + spec.slotInteriorChips D 9
        + spec.slotInteriorChips D 10 + spec.slotInteriorChips D 11
        + spec.slotInteriorChips D 12 + spec.slotInteriorChips D 13
        + spec.slotInteriorChips D 14) := by
  rw [deg_eq_core_add_slotInteriorChips]
  congr 1
  · simp [Fin.sum_univ_seven]
  · simp [Fin.sum_univ_succ]
    ring

/-! ## The burned-transition-vertex indicator -/

/-- `1` if the transition vertex `v` is burned, `0` otherwise. -/
noncomputable def burnedInd (spec : Spec 7 15) (D : CFDiv spec.graph)
    (w : spec.Vertex) (v : Fin 7) : ℤ :=
  if spec.coreVertex v ∈ burned spec.graph D w then 1 else 0

theorem burnedInd_nonneg (spec : Spec 7 15) (D : CFDiv spec.graph) (w : spec.Vertex)
    (v : Fin 7) : 0 ≤ burnedInd spec D w v := by
  unfold burnedInd; split <;> omega

theorem burnedInd_le_one (spec : Spec 7 15) (D : CFDiv spec.graph) (w : spec.Vertex)
    (v : Fin 7) : burnedInd spec D w v ≤ 1 := by
  unfold burnedInd; split <;> omega

theorem burnedInd_of_mem {v : Fin 7} (h : spec.coreVertex v ∈ burned spec.graph D w) :
    burnedInd spec D w v = 1 := by
  unfold burnedInd; rw [if_pos h]

theorem burnedInd_of_not_mem {v : Fin 7}
    (h : spec.coreVertex v ∉ burned spec.graph D w) :
    burnedInd spec D w v = 0 := by
  unfold burnedInd; rw [if_neg h]

/-! ## Lemma 3.5(b) in slot coordinates -/

theorem helper_b_sum (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (hw : D w = 0) :
    burnedInd spec D w 1 + burnedInd spec D w 2 + burnedInd spec D w 3
        + burnedInd spec D w 4 + burnedInd spec D w 5 + burnedInd spec D w 6
      ≤ D (spec.coreVertex 0)
        + (spec.slotInteriorChips D 0 + spec.slotInteriorChips D 1
          + spec.slotInteriorChips D 2 + spec.slotInteriorChips D 3
          + spec.slotInteriorChips D 4 + spec.slotInteriorChips D 5) := by
  classical
  have h := helper_lemma_b hcore hEff hred hrank hw
    (Finset.univ.filter
      (fun j : Fin 6 => spec.coreVertex (transitionOf j) ∈ burned spec.graph D w))
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hcard :
      (((Finset.univ.filter
          (fun j : Fin 6 => spec.coreVertex (transitionOf j)
            ∈ burned spec.graph D w)).card : ℤ))
        = burnedInd spec D w 1 + burnedInd spec D w 2 + burnedInd spec D w 3
          + burnedInd spec D w 4 + burnedInd spec D w 5 + burnedInd spec D w 6 := by
    rw [← Finset.sum_boole]
    rw [Fin.sum_univ_six]
    simp only [burnedInd, transitionOf_0, transitionOf_1, transitionOf_2,
      transitionOf_3, transitionOf_4, transitionOf_5]
  have hmono :
      ∑ i ∈ Finset.univ.filter
        (fun j : Fin 6 => spec.coreVertex (transitionOf j) ∈ burned spec.graph D w),
          spec.slotInteriorChips D (spokeOf i)
        ≤ ∑ i : Fin 6, spec.slotInteriorChips D (spokeOf i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => slotInteriorChips_nonneg hEff _
  have hspokes : ∑ i : Fin 6, spec.slotInteriorChips D (spokeOf i)
      = spec.slotInteriorChips D 0 + spec.slotInteriorChips D 1
        + spec.slotInteriorChips D 2 + spec.slotInteriorChips D 3
        + spec.slotInteriorChips D 4 + spec.slotInteriorChips D 5 := by
    rw [Fin.sum_univ_six]
    simp only [spokeOf_0, spokeOf_1, spokeOf_2, spokeOf_3, spokeOf_4, spokeOf_5]
  rw [hcard] at h
  have hcentre : spec.coreVertex centre = spec.coreVertex 0 := rfl
  rw [hcentre] at h
  omega

/-! ## The two half-counts of Lemma 3.6's first paragraph -/

/-- **Forward half-count.**  If `vⱼ⁻` is burned, then `Cⱼ` together with the
closed transition path leaving `vⱼ⁺` carries three, counting each burned
transition vertex in it as one. -/
theorem three_le_forward (hcore : spec.core = tricycleCore) (hEff : effective D)
    (j : Fin 3) (hj : spec.coreVertex (vMinus j) ∈ burned spec.graph D w) :
    3 ≤ cycleChips spec D j + spec.slotInteriorChips D (transitionSlot j)
        + D (spec.coreVertex (vMinus (j + 1)))
      + burnedInd spec D w (vMinus j) + burnedInd spec D w (vPlus j)
      + burnedInd spec D w (vMinus (j + 1)) := by
  have hc0 : 0 ≤ D (spec.coreVertex (vMinus j)) := hEff _
  have hc1 : 0 ≤ D (spec.coreVertex (vPlus j)) := hEff _
  have hc2 : 0 ≤ spec.slotInteriorChips D (cycleSlot j 0) :=
    slotInteriorChips_nonneg hEff _
  have hc3 : 0 ≤ spec.slotInteriorChips D (cycleSlot j 1) :=
    slotInteriorChips_nonneg hEff _
  have hnn0 : 0 ≤ cycleChips spec D j := by unfold cycleChips; omega
  have hnn1 : 0 ≤ spec.slotInteriorChips D (transitionSlot j) :=
    slotInteriorChips_nonneg hEff _
  have hnn2 : 0 ≤ D (spec.coreVertex (vMinus (j + 1))) := hEff _
  have hi1 := burnedInd_nonneg spec D w (vPlus j)
  have hi2 := burnedInd_nonneg spec D w (vMinus (j + 1))
  have hj1 : burnedInd spec D w (vMinus j) = 1 := burnedInd_of_mem hj
  by_cases hp : spec.coreVertex (vPlus j) ∈ burned spec.graph D w
  · by_cases hm : spec.coreVertex (vMinus (j + 1)) ∈ burned spec.graph D w
    · rw [hj1, burnedInd_of_mem hp, burnedInd_of_mem hm]; omega
    · have hchip := one_le_transitionPath_up hcore hEff j hp hm
      rw [hj1, burnedInd_of_mem hp]; omega
  · have hcy := two_le_cycleChips_of_minus_burned hcore hEff j hj hp
    rw [hj1]; omega

/-- **Backward half-count.**  If `vⱼ⁺` is burned, then `Cⱼ` together with the
closed transition path entering `vⱼ⁻` carries three, counting each burned
transition vertex in it as one. -/
theorem three_le_backward (hcore : spec.core = tricycleCore) (hEff : effective D)
    (j : Fin 3) (hj : spec.coreVertex (vPlus j) ∈ burned spec.graph D w) :
    3 ≤ cycleChips spec D j + spec.slotInteriorChips D (transitionSlot (j + 2))
        + D (spec.coreVertex (vPlus (j + 2)))
      + burnedInd spec D w (vPlus j) + burnedInd spec D w (vMinus j)
      + burnedInd spec D w (vPlus (j + 2)) := by
  have hc0 : 0 ≤ D (spec.coreVertex (vMinus j)) := hEff _
  have hc1 : 0 ≤ D (spec.coreVertex (vPlus j)) := hEff _
  have hc2 : 0 ≤ spec.slotInteriorChips D (cycleSlot j 0) :=
    slotInteriorChips_nonneg hEff _
  have hc3 : 0 ≤ spec.slotInteriorChips D (cycleSlot j 1) :=
    slotInteriorChips_nonneg hEff _
  have hnn0 : 0 ≤ cycleChips spec D j := by unfold cycleChips; omega
  have hnn1 : 0 ≤ spec.slotInteriorChips D (transitionSlot (j + 2)) :=
    slotInteriorChips_nonneg hEff _
  have hnn2 : 0 ≤ D (spec.coreVertex (vPlus (j + 2))) := hEff _
  have hi1 := burnedInd_nonneg spec D w (vMinus j)
  have hi2 := burnedInd_nonneg spec D w (vPlus (j + 2))
  have hj1 : burnedInd spec D w (vPlus j) = 1 := burnedInd_of_mem hj
  by_cases hm : spec.coreVertex (vMinus j) ∈ burned spec.graph D w
  · by_cases hp : spec.coreVertex (vPlus (j + 2)) ∈ burned spec.graph D w
    · rw [hj1, burnedInd_of_mem hm, burnedInd_of_mem hp]; omega
    · have hmem : spec.coreVertex (vMinus (j + 2 + 1)) ∈ burned spec.graph D w := by
        rw [fin3_add_two_add_one]; exact hm
      have hchip := one_le_transitionPath_down hcore hEff (j + 2) hmem hp
      rw [hj1, burnedInd_of_mem hm]; omega
  · have hcy := two_le_cycleChips_of_plus_burned hcore hEff j hj hm
    rw [hj1]; omega

/-! ## Lemma 3.6, first paragraph: every transition path carries a chip -/

theorem one_le_transitionPathChips (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (hdeg : deg D ≤ 5) (i : Fin 3) :
    1 ≤ transitionPathChips spec D i := by
  by_contra hcon
  push Not at hcon
  have hcn : ∀ v : Fin 7, 0 ≤ D (spec.coreVertex v) := fun v => hEff _
  have hin : ∀ e : Fin 15, 0 ≤ spec.slotInteriorChips D e := fun e =>
    slotInteriorChips_nonneg hEff e
  have hzero : transitionPathChips spec D i = 0 := by
    have h1 := hcn (vPlus i)
    have h2 := hin (transitionSlot i)
    have h3 := hcn (vMinus (i + 1))
    unfold transitionPathChips at hcon ⊢
    omega
  have hw : D (spec.coreVertex (vPlus i)) = 0 := by
    have h1 := hcn (vPlus i)
    have h2 := hin (transitionSlot i)
    have h3 := hcn (vMinus (i + 1))
    unfold transitionPathChips at hzero
    omega
  have hwb : spec.coreVertex (vPlus i)
      ∈ burned spec.graph D (spec.coreVertex (vPlus i)) := mem_burned_self
  have hnext : spec.coreVertex (vMinus (i + 1))
      ∈ burned spec.graph D (spec.coreVertex (vPlus i)) :=
    burned_vMinus_of_chipFree hcore hEff i hzero hwb
  have hA := three_le_forward hcore hEff (i + 1) hnext
  have hB := three_le_backward hcore hEff i hwb
  have hb := helper_b_sum hcore hEff hred hrank hw
  have hd := deg_expand spec D
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp only [vMinus_0, vMinus_1, vMinus_2, vPlus_0, vPlus_1, vPlus_2,
      cycleSlot_00, cycleSlot_01, cycleSlot_10, cycleSlot_11, cycleSlot_20,
      cycleSlot_21, transitionSlot_0, transitionSlot_1, transitionSlot_2,
      fin3_01, fin3_11, fin3_21, fin3_02, fin3_12, fin3_22,
      cycleChips] at hA hB hb <;>
    linarith [hcn 0, hcn 1, hcn 2, hcn 3, hcn 4, hcn 5, hcn 6,
      hin 0, hin 1, hin 2, hin 3, hin 4, hin 5, hin 6, hin 7,
      hin 8, hin 9, hin 10, hin 11, hin 12, hin 13, hin 14]

/-! ## Lemma 3.6, second paragraph: two chips on the centre -/

/-- A cycle with at most one chip is entirely burned by the fire started at one
of its own chip-free transition vertices, so **both** of its spokes' transition
vertices are burned, and Lemma 3.5(b) charges two chips to the centre and those
two spokes. -/
theorem two_le_centre_add_spokePair (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (i : Fin 3)
    (hcy : cycleChips spec D i ≤ 1) :
    2 ≤ D (spec.coreVertex 0) + spokePairChips spec D i := by
  classical
  have hc0 : 0 ≤ D (spec.coreVertex (vMinus i)) := hEff _
  have hc1 : 0 ≤ D (spec.coreVertex (vPlus i)) := hEff _
  have hc2 : 0 ≤ spec.slotInteriorChips D (cycleSlot i 0) :=
    slotInteriorChips_nonneg hEff _
  have hc3 : 0 ≤ spec.slotInteriorChips D (cycleSlot i 1) :=
    slotInteriorChips_nonneg hEff _
  have hchoice : D (spec.coreVertex (vMinus i)) = 0 ∨ D (spec.coreVertex (vPlus i)) = 0 := by
    unfold cycleChips at hcy; omega
  have hboth : ∃ w : spec.Vertex, D w = 0 ∧
      spec.coreVertex (vMinus i) ∈ burned spec.graph D w ∧
      spec.coreVertex (vPlus i) ∈ burned spec.graph D w := by
    rcases hchoice with h | h
    · refine ⟨spec.coreVertex (vMinus i), h, mem_burned_self, ?_⟩
      by_contra hcon
      have := two_le_cycleChips_of_minus_burned hcore hEff i mem_burned_self hcon
      omega
    · refine ⟨spec.coreVertex (vPlus i), h, ?_, mem_burned_self⟩
      by_contra hcon
      have := two_le_cycleChips_of_plus_burned hcore hEff i mem_burned_self hcon
      omega
  obtain ⟨w, hw, hbm, hbp⟩ := hboth
  have hIsub : ∀ j ∈ ({spokeIndexMinus i, spokeIndexPlus i} : Finset (Fin 6)),
      spec.coreVertex (transitionOf j) ∈ burned spec.graph D w := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · rw [transitionOf_spokeIndexMinus]; exact hbm
    · rw [transitionOf_spokeIndexPlus]; exact hbp
  have h := helper_lemma_b hcore hEff hred hrank hw
    ({spokeIndexMinus i, spokeIndexPlus i} : Finset (Fin 6)) hIsub
  rw [Finset.card_pair (spokeIndex_ne i), Finset.sum_pair (spokeIndex_ne i),
    spokeOf_spokeIndexMinus, spokeOf_spokeIndexPlus] at h
  have hcentre : spec.coreVertex centre = spec.coreVertex 0 := rfl
  rw [hcentre] at h
  unfold spokePairChips
  push_cast at h
  omega

/-- The disjunctive form fed to the eight-way case split below. -/
theorem centre_spokePair_or_cycle (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (i : Fin 3) :
    2 ≤ D (spec.coreVertex 0) + spokePairChips spec D i ∨ 2 ≤ cycleChips spec D i := by
  rcases le_or_gt (cycleChips spec D i) 1 with h | h
  · exact Or.inl (two_le_centre_add_spokePair hcore hEff hred hrank i h)
  · exact Or.inr (by omega)

/-! ## Lemma 3.6 -/

/-- **Lemma 3.6.**  On any subdivision of the minimal tricycle, a positive-rank
`v₀`-reduced divisor of degree at most five has exactly two chips on `v₀` and
exactly one chip on each of the three transition paths. -/
theorem lemma_graad5 (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (hdeg : deg D ≤ 5) :
    D (spec.coreVertex 0) = 2 ∧ transitionPathChips spec D 0 = 1
      ∧ transitionPathChips spec D 1 = 1 ∧ transitionPathChips spec D 2 = 1 := by
  have hcn : ∀ v : Fin 7, 0 ≤ D (spec.coreVertex v) := fun v => hEff _
  have hin : ∀ e : Fin 15, 0 ≤ spec.slotInteriorChips D e := fun e =>
    slotInteriorChips_nonneg hEff e
  have htp0 := one_le_transitionPathChips hcore hEff hred hrank hdeg 0
  have htp1 := one_le_transitionPathChips hcore hEff hred hrank hdeg 1
  have htp2 := one_le_transitionPathChips hcore hEff hred hrank hdeg 2
  have hd := deg_expand spec D
  have hcentre : D (spec.coreVertex 0) = 2 := by
    rcases centre_spokePair_or_cycle hcore hEff hred hrank 0 with h0 | h0 <;>
    rcases centre_spokePair_or_cycle hcore hEff hred hrank 1 with h1 | h1 <;>
    rcases centre_spokePair_or_cycle hcore hEff hred hrank 2 with h2 | h2 <;>
      simp only [transitionPathChips, cycleChips, spokePairChips,
        vMinus_0, vMinus_1, vMinus_2, vPlus_0, vPlus_1, vPlus_2,
        spokeMinus_0, spokeMinus_1, spokeMinus_2,
        spokePlus_0, spokePlus_1, spokePlus_2,
        cycleSlot_00, cycleSlot_01, cycleSlot_10, cycleSlot_11, cycleSlot_20,
        cycleSlot_21, transitionSlot_0, transitionSlot_1, transitionSlot_2,
        fin3_01, fin3_11, fin3_21] at h0 h1 h2 htp0 htp1 htp2 <;>
      linarith [hcn 0, hcn 1, hcn 2, hcn 3, hcn 4, hcn 5, hcn 6,
        hin 0, hin 1, hin 2, hin 3, hin 4, hin 5, hin 6, hin 7,
        hin 8, hin 9, hin 10, hin 11, hin 12, hin 13, hin 14]
  refine ⟨hcentre, ?_, ?_, ?_⟩ <;>
    · simp only [transitionPathChips, vMinus_0, vMinus_1, vMinus_2,
        vPlus_0, vPlus_1, vPlus_2, transitionSlot_0, transitionSlot_1,
        transitionSlot_2, fin3_01, fin3_11, fin3_21] at htp0 htp1 htp2 ⊢
      linarith [hcn 0, hcn 1, hcn 2, hcn 3, hcn 4, hcn 5, hcn 6,
        hin 0, hin 1, hin 2, hin 3, hin 4, hin 5, hin 6, hin 7,
        hin 8, hin 9, hin 10, hin 11, hin 12, hin 13, hin 14]

/-! ## Corollary 3.7 -/

/-- **Corollary 3.7.**  *Every* subdivision of the minimal tricycle has
divisorial gonality at least five — for every length vector, hence for every
`σ_k`.  This is what makes the left-hand side of the tricycle gap a minimum
rather than a bound at one `k`. -/
theorem five_le_divisorialGonality (hcore : spec.core = tricycleCore)
    (hconn : graphConnected spec.graph) :
    5 ≤ divisorialGonality spec.graph := by
  refine le_divisorialGonality_of_no_small hconn ?_
  intro E hEeff hEdeg hErank
  obtain ⟨D', hequiv, hred⟩ :=
    exists_q_reduced_representative hconn (spec.coreVertex centre) E
  have hrank' : rank spec.graph D' ≥ 1 := by
    rwa [← Utilities.rank_eq_of_linear_equiv spec.graph hequiv]
  have hwin : winnable spec.graph D' :=
    (rank_nonneg_iff_winnable spec.graph D').mp
      ((rank_geq_iff spec.graph D' 0).mpr (by omega))
  have hEff' : effective D' :=
    effective_of_winnable_and_q_reduced spec.graph _ D' hwin hred
  have hdeg' : deg D' = 4 := by
    rw [← linear_equiv_preserves_deg spec.graph E D' hequiv]
    simpa using hEdeg
  obtain ⟨hc, h0, h1, h2⟩ :=
    lemma_graad5 hcore hEff' hred hrank' (by omega)
  have hcn : ∀ v : Fin 7, 0 ≤ D' (spec.coreVertex v) := fun v => hEff' _
  have hin : ∀ e : Fin 15, 0 ≤ spec.slotInteriorChips D' e := fun e =>
    slotInteriorChips_nonneg hEff' e
  have hd := deg_expand spec D'
  simp only [transitionPathChips, vMinus_0, vMinus_1, vMinus_2,
    vPlus_0, vPlus_1, vPlus_2, transitionSlot_0, transitionSlot_1,
    transitionSlot_2, fin3_01, fin3_11, fin3_21] at h0 h1 h2
  linarith [hcn 0, hcn 1, hcn 2, hcn 3, hcn 4, hcn 5, hcn 6,
    hin 0, hin 1, hin 2, hin 3, hin 4, hin 5, hin 6, hin 7,
    hin 8, hin 9, hin 10, hin 11, hin 12, hin 13, hin 14]

end Utilities.Tricycle
