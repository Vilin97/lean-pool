/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.CorrectedMidpointKGeneral
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaJacobian

/-!
# Slope arithmetic for torsion classes on banana graphs

This file generalizes the normalized-slope part of `ThetaPrincipal.lean` from
three strands to an arbitrary banana.  It is the potential-theoretic input to
the corrected Proposition 4.19: a principal multiple of a marked difference
has one common endpoint rise, while every unmarked strand carries a nonzero
integral slope when that rise is nonzero.
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Evaluate a firing script at a strand position, with value zero beyond the strand endpoint. -/
def bananaPathValue {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) (r : ℕ) : ℤ :=
  if hr : r ≤ B.length α then
    script (strandVertex B α ⟨r, by omega⟩)
  else 0

/-- The difference of consecutive firing-script values along a strand. -/
def bananaStepSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) (r : ℕ) : ℤ :=
  bananaPathValue B script α (r + 1) - bananaPathValue B script α r

theorem bananaPathValue_eq {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) (r : ℕ)
    (hr : r ≤ B.length α) :
    bananaPathValue B script α r =
      script (strandVertex B α ⟨r, by omega⟩) := by
  simp [bananaPathValue, hr]

theorem bananaStepSlope_eq {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) (r : ℕ)
    (hr : r < B.length α) :
    bananaStepSlope B script α r =
      script (strandVertex B α ⟨r + 1, by omega⟩) -
        script (strandVertex B α ⟨r, by omega⟩) := by
  unfold bananaStepSlope
  rw [bananaPathValue_eq B script α (r + 1) (by omega),
    bananaPathValue_eq B script α r (by omega)]

theorem sum_bananaStepSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) :
    ∑ r ∈ Finset.range (B.length α), bananaStepSlope B script α r =
      script (rightEndpoint B) - script (leftEndpoint B) := by
  unfold bananaStepSlope
  rw [Finset.sum_range_sub]
  rw [bananaPathValue_eq B script α (B.length α) (by omega),
    bananaPathValue_eq B script α 0 (by omega),
    strandVertex_length B α, strandVertex_zero B α]

/-- Express the strand slope in the stored edge orientation, reversing its order and sign when
needed. -/
def bananaStorageSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) (r : ℕ) : ℤ :=
  if B.core.tail α = 0 then
    bananaStepSlope B script α r
  else
    -bananaStepSlope B script α (B.length α - 1 - r)

theorem bananaStorageSlope_isStepSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) :
    B.IsStepSlope script (bananaStorageSlope B script) := by
  intro α o
  by_cases ht : B.core.tail α = 0
  · have hLeft : B.stepLeft α o =
        strandVertex B α ⟨o.val, by omega⟩ := by
      rw [← B.pathVertex_stepLeftPosition]
      simp only [strandVertex, ht, ↓reduceIte]
      congr 1
    have hRight : B.stepRight α o =
        strandVertex B α ⟨o.val + 1, by omega⟩ := by
      rw [← B.pathVertex_stepRightPosition]
      simp only [strandVertex, ht, ↓reduceIte]
      congr 1
    rw [hLeft, hRight]
    simp only [bananaStorageSlope, ht, ↓reduceIte]
    exact (bananaStepSlope_eq B script α o.val o.isLt).symm
  · have hLeft : B.stepLeft α o =
        strandVertex B α ⟨B.length α - o.val, by omega⟩ := by
      rw [← B.pathVertex_stepLeftPosition]
      simp only [strandVertex, ht, ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [stepLeftPosition]
      omega
    have hRight : B.stepRight α o =
        strandVertex B α ⟨B.length α - (o.val + 1), by omega⟩ := by
      rw [← B.pathVertex_stepRightPosition]
      simp only [strandVertex, ht, ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [stepRightPosition]
      omega
    rw [hLeft, hRight]
    simp only [bananaStorageSlope, ht, ↓reduceIte]
    have hr : B.length α - 1 - o.val < B.length α := by
      have := B.length_pos α
      omega
    rw [bananaStepSlope_eq B script α _ hr]
    have hPos1 :
        (⟨B.length α - 1 - o.val + 1, by omega⟩ : B.PathPosition α) =
          ⟨B.length α - o.val, by omega⟩ := by
      apply Fin.ext
      change B.length α - 1 - o.val + 1 = B.length α - o.val
      omega
    have hPos0 :
        (⟨B.length α - 1 - o.val, by omega⟩ : B.PathPosition α) =
          ⟨B.length α - (o.val + 1), by omega⟩ := by
      apply Fin.ext
      change B.length α - 1 - o.val = B.length α - (o.val + 1)
      omega
    rw [hPos1, hPos0]
    ring

theorem prin_normalized_interior_general {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1))
    (r : Fin (B.length α - 1)) :
    prin B.graph script (strandVertex B α ⟨r.val + 1, by omega⟩) =
      bananaStepSlope B script α (r.val + 1) -
        bananaStepSlope B script α r.val := by
  have hslope := bananaStorageSlope_isStepSlope B script
  let i : B.PathPosition α := ⟨r.val + 1, by omega⟩
  have hi : B.IsInteriorPosition α i := by
    constructor
    · simp [i]
    · have hr := r.isLt
      simp only [i]
      omega
  by_cases ht : B.core.tail α = 0
  · have hVertex : strandVertex B α i = B.interiorVertex α r := by
      simp only [strandVertex, ht, ↓reduceIte]
      rw [B.pathVertex_eq_interiorVertex α i hi]
      congr 1
    have hPrin := B.prin_interiorVertex_eq_slopeDifference hslope α r
    change prin B.graph script (strandVertex B α i) = _
    rw [hVertex, hPrin]
    simp only [bananaStorageSlope, ht, ↓reduceIte]
  · let q : Fin (B.length α - 1) :=
      ⟨B.length α - r.val - 2, by omega⟩
    let rawPosition : B.PathPosition α :=
      ⟨B.length α - i.val, by omega⟩
    have hrawInterior : B.IsInteriorPosition α rawPosition := by
      constructor
      · have hr := r.isLt
        simp only [rawPosition, i]
        omega
      · simp only [rawPosition]
        have hiPos : 0 < i.val := hi.1
        omega
    have hVertex : strandVertex B α i = B.interiorVertex α q := by
      simp only [strandVertex, ht, ↓reduceIte]
      change B.pathVertex α rawPosition = _
      rw [B.pathVertex_eq_interiorVertex α rawPosition hrawInterior]
      congr 1
    have hPrin := B.prin_interiorVertex_eq_slopeDifference hslope α q
    change prin B.graph script (strandVertex B α i) = _
    rw [hVertex, hPrin]
    have hqSucc : B.length α - 1 - (q.val + 1) = r.val := by
      simp only [q]
      omega
    have hq : B.length α - 1 - q.val = r.val + 1 := by
      simp only [q]
      omega
    simp only [bananaStorageSlope, ht, ↓reduceIte, hqSucc, hq]
    ring

theorem prin_leftEndpoint_eq_sum_initialSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) :
    prin B.graph script (leftEndpoint B) =
      ∑ α : Fin (g + 1), bananaStepSlope B script α 0 := by
  have h := B.prin_coreVertex_eq_endpointSum
    (bananaStorageSlope_isStepSlope B script) (0 : Fin 2)
  rw [show leftEndpoint B = B.coreVertex (0 : Fin 2) by rfl, h]
  apply Finset.sum_congr rfl
  intro α _
  by_cases ht : B.core.tail α = 0
  · have hh := head_eq_other_of_tail B α ht
    simp [ht, hh, bananaStorageSlope]
  · have ht1 : B.core.tail α = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail α) with h0 | h1
      · exact (ht h0).elim
      · exact h1
    have hh0 : B.core.head α = 0 := by
      rcases fin_two_eq_zero_or_one (B.core.head α) with h0 | h1
      · exact h0
      · exact (B.core_loopless α (ht1.trans h1.symm)).elim
    simp only [ht1, hh0, if_true, bananaStorageSlope]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, neg_neg]
    have hlen := B.length_pos α
    have hidx : B.length α - 1 - (B.length α - 1) = 0 := by omega
    rw [hidx]
    simp

theorem prin_rightEndpoint_eq_neg_sum_finalSlope {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) :
    prin B.graph script (rightEndpoint B) =
      -∑ α : Fin (g + 1),
        bananaStepSlope B script α (B.length α - 1) := by
  have h := B.prin_coreVertex_eq_endpointSum
    (bananaStorageSlope_isStepSlope B script) (1 : Fin 2)
  rw [show rightEndpoint B = B.coreVertex (1 : Fin 2) by rfl, h]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  by_cases ht : B.core.tail α = 0
  · have hh := head_eq_other_of_tail B α ht
    simp [ht, hh, bananaStorageSlope]
  · have ht1 : B.core.tail α = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail α) with h0 | h1
      · exact (ht h0).elim
      · exact h1
    have hh0 : B.core.head α = 0 := by
      rcases fin_two_eq_zero_or_one (B.core.head α) with h0 | h1
      · exact h0
      · exact (B.core_loopless α (ht1.trans h1.symm)).elim
    simp [ht1, hh0, bananaStorageSlope]

/-! ## Extracting the initial slope from a principal divisor -/

/-- The sum of a divisor's coefficients at the interior vertices of one strand. -/
def bananaInteriorSum {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (D : CFDiv B.graph) : ℤ :=
  ∑ r : Fin (B.length α - 1),
    D (strandVertex B α ⟨r.val + 1, by omega⟩)

/-- The sum of interior divisor coefficients weighted by their distance from the left endpoint. -/
def bananaInteriorMoment {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (D : CFDiv B.graph) : ℤ :=
  ∑ r : Fin (B.length α - 1),
    ((r.val + 1 : ℕ) : ℤ) *
      D (strandVertex B α ⟨r.val + 1, by omega⟩)

theorem bananaInteriorSum_prin {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) :
    bananaInteriorSum B α (prin B.graph script) =
      bananaStepSlope B script α (B.length α - 1) -
        bananaStepSlope B script α 0 := by
  unfold bananaInteriorSum
  have hrewrite : ∀ r : Fin (B.length α - 1),
      prin B.graph script (strandVertex B α ⟨r.val + 1, by omega⟩) =
        bananaStepSlope B script α (r.val + 1) -
          bananaStepSlope B script α r.val :=
    prin_normalized_interior_general B script α
  simp_rw [hrewrite]
  calc
    ∑ r : Fin (B.length α - 1),
        (bananaStepSlope B script α (r.val + 1) -
          bananaStepSlope B script α r.val) =
        ∑ r ∈ Finset.range (B.length α - 1),
          (bananaStepSlope B script α (r + 1) -
            bananaStepSlope B script α r) :=
      Fin.sum_univ_eq_sum_range
        (fun r => bananaStepSlope B script α (r + 1) -
          bananaStepSlope B script α r) (B.length α - 1)
    _ = _ := Finset.sum_range_sub _ _

theorem bananaInteriorMoment_prin {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) :
    bananaInteriorMoment B α (prin B.graph script) =
      (B.length α : ℤ) *
          bananaStepSlope B script α (B.length α - 1) -
        (script (rightEndpoint B) - script (leftEndpoint B)) := by
  unfold bananaInteriorMoment
  have hrewrite : ∀ r : Fin (B.length α - 1),
      prin B.graph script (strandVertex B α ⟨r.val + 1, by omega⟩) =
        bananaStepSlope B script α (r.val + 1) -
          bananaStepSlope B script α r.val :=
    prin_normalized_interior_general B script α
  simp_rw [hrewrite]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun r => ((r + 1 : ℕ) : ℤ) *
      (bananaStepSlope B script α (r + 1) -
        bananaStepSlope B script α r)) (B.length α - 1)
  rw [hfin]
  have htel := weighted_step_difference_telescope
    (B.length α) (fun r => bananaStepSlope B script α r)
  have hsum := sum_bananaStepSlope B script α
  rw [hsum] at htel
  linarith

/-- The initial slope on a strand is determined by the common rise and the
zeroth and first interior moments of the principal divisor. -/
theorem initialSlope_equation {g : ℕ} (B : Banana g)
    (script : firingScript B.graph) (α : Fin (g + 1)) :
    (B.length α : ℤ) * bananaStepSlope B script α 0 =
      (script (rightEndpoint B) - script (leftEndpoint B)) +
        bananaInteriorMoment B α (prin B.graph script) -
          (B.length α : ℤ) *
            bananaInteriorSum B α (prin B.graph script) := by
  have hsum := bananaInteriorSum_prin B script α
  have hmoment := bananaInteriorMoment_prin B script α
  rw [hsum, hmoment]
  ring

private theorem interior_position_eq_of_vertex_eq_general {g : ℕ}
    (B : Banana g) (α β : Fin (g + 1))
    (r : ℕ) (hr : r < B.length α - 1)
    (j : B.PathPosition β) (hj : B.IsInteriorPosition β j) :
    strandVertex B α ⟨r + 1, by omega⟩ = strandVertex B β j ↔
      α = β ∧ r + 1 = j.val := by
  constructor
  · intro h
    have hrInterior : B.IsInteriorPosition α
        ⟨r + 1, by have := B.length_pos α; omega⟩ := by
      change 0 < r + 1 ∧ r + 1 < B.length α
      omega
    have hαβ := strand_eq_of_interior_vertex_eq B α β
      ⟨r + 1, by have := B.length_pos α; omega⟩ j
      hrInterior hj h
    refine ⟨hαβ, ?_⟩
    subst β
    exact congrArg Fin.val (strandVertex_injective B α h)
  · rintro ⟨rfl, hval⟩
    exact congrArg (strandVertex B α) (Fin.ext hval)

theorem bananaInteriorSum_one_chip {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (j : B.PathPosition β)
    (hj : B.IsInteriorPosition β j) :
    bananaInteriorSum B α (oneChip (strandVertex B β j)) =
      if α = β then 1 else 0 := by
  classical
  unfold bananaInteriorSum
  by_cases hαβ : α = β
  · subst β
    have hj' : 0 < j.val ∧ j.val < B.length α := by exact hj
    let selected : Fin (B.length α - 1) := ⟨j.val - 1, by omega⟩
    rw [Finset.sum_eq_single selected]
    · have hpos : j.val - 1 + 1 = j.val := by omega
      simp [selected, oneChip, hpos]
    · intro r hr hrne
      have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠
          strandVertex B α j := by
        intro heq
        have hv := congrArg Fin.val (strandVertex_injective B α heq)
        have hsel : r = selected := by
          apply Fin.ext
          change r.val = j.val - 1
          exact Nat.eq_sub_of_add_eq hv
        exact hrne hsel
      simp [oneChip, hne]
    · exact fun h => (h (Finset.mem_univ selected)).elim
  · simp only [hαβ, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠
        strandVertex B β j := by
      intro heq
      exact hαβ (interior_position_eq_of_vertex_eq_general B α β r.val r.isLt j hj |>.mp heq).1
    simp [oneChip, hne]

theorem bananaInteriorMoment_one_chip {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (j : B.PathPosition β)
    (hj : B.IsInteriorPosition β j) :
    bananaInteriorMoment B α (oneChip (strandVertex B β j)) =
      if α = β then (j.val : ℤ) else 0 := by
  classical
  unfold bananaInteriorMoment
  by_cases hαβ : α = β
  · subst β
    have hj' : 0 < j.val ∧ j.val < B.length α := by exact hj
    let selected : Fin (B.length α - 1) := ⟨j.val - 1, by omega⟩
    rw [Finset.sum_eq_single selected]
    · have hpos : j.val - 1 + 1 = j.val := by omega
      simp [selected, oneChip, hpos]
    · intro r hr hrne
      have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠
          strandVertex B α j := by
        intro heq
        have hv := congrArg Fin.val (strandVertex_injective B α heq)
        have hsel : r = selected := by
          apply Fin.ext
          change r.val = j.val - 1
          exact Nat.eq_sub_of_add_eq hv
        exact hrne hsel
      simp [oneChip, hne]
    · exact fun h => (h (Finset.mem_univ selected)).elim
  · simp only [hαβ, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠
        strandVertex B β j := by
      intro heq
      exact hαβ (interior_position_eq_of_vertex_eq_general B α β r.val r.isLt j hj |>.mp heq).1
    simp [oneChip, hne]

theorem bananaInteriorSum_one_chip_leftEndpoint {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) :
    bananaInteriorSum B α (oneChip (leftEndpoint B)) = 0 := by
  unfold bananaInteriorSum
  apply Finset.sum_eq_zero
  intro r _hr
  have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B α _ (Nat.zero_lt_succ r.val)
  simp [oneChip, hne]

theorem bananaInteriorMoment_one_chip_leftEndpoint {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) :
    bananaInteriorMoment B α (oneChip (leftEndpoint B)) = 0 := by
  unfold bananaInteriorMoment
  apply Finset.sum_eq_zero
  intro r _hr
  have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B α _ (Nat.zero_lt_succ r.val)
  simp [oneChip, hne]

theorem bananaInteriorSum_one_chip_rightEndpoint {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) :
    bananaInteriorSum B α (oneChip (rightEndpoint B)) = 0 := by
  unfold bananaInteriorSum
  apply Finset.sum_eq_zero
  intro r _hr
  have hrlt := r.isLt
  have hlt : r.val + 1 < B.length α := by omega
  have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠ rightEndpoint B :=
    strandVertex_ne_rightEndpoint B α _ hlt
  simp [oneChip, hne]

theorem bananaInteriorMoment_one_chip_rightEndpoint {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) :
    bananaInteriorMoment B α (oneChip (rightEndpoint B)) = 0 := by
  unfold bananaInteriorMoment
  apply Finset.sum_eq_zero
  intro r _hr
  have hrlt := r.isLt
  have hlt : r.val + 1 < B.length α := by omega
  have hne : strandVertex B α ⟨r.val + 1, by omega⟩ ≠ rightEndpoint B :=
    strandVertex_ne_rightEndpoint B α _ hlt
  simp [oneChip, hne]

theorem bananaInteriorSum_sub {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (D E : CFDiv B.graph) :
    bananaInteriorSum B α (D - E) =
      bananaInteriorSum B α D - bananaInteriorSum B α E := by
  unfold bananaInteriorSum
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]

theorem bananaInteriorSum_zsmul {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (z : ℤ) (D : CFDiv B.graph) :
    bananaInteriorSum B α (z • D) = z * bananaInteriorSum B α D := by
  unfold bananaInteriorSum
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem bananaInteriorMoment_sub {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (D E : CFDiv B.graph) :
    bananaInteriorMoment B α (D - E) =
      bananaInteriorMoment B α D - bananaInteriorMoment B α E := by
  unfold bananaInteriorMoment
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem bananaInteriorMoment_zsmul {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (z : ℤ) (D : CFDiv B.graph) :
    bananaInteriorMoment B α (z • D) = z * bananaInteriorMoment B α D := by
  unfold bananaInteriorMoment
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- A torsion witness supplies a potential whose principal divisor is the
negative marked difference.  This orientation makes the left-endpoint sum
equal to `-k` in the endpoint cases. -/
theorem exists_prin_eq_neg_marked_difference_of_torsionWitness
    {G : CFGraph} (u v : G.V) (k : ℕ)
    (hk : TorsionWitness (mark G u v) k) :
    ∃ script : firingScript G,
      prin G script = (k : ℤ) • (oneChip v - oneChip u) := by
  have hequiv : linearEquiv G 0
      ((k : ℤ) • (oneChip u - oneChip v)) := hk.2.symm
  unfold linearEquiv at hequiv
  obtain ⟨script, hscript⟩ :=
    (principal_iff_eq_prin G
      (((k : ℤ) • (oneChip u - oneChip v)) - 0)).mp hequiv
  refine ⟨-script, ?_⟩
  rw [map_neg, ← hscript]
  ext x
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  ring

/-- Initial-slope equations for a principal multiple of two distinct
interior marks.  The three cases are the two marked strands and every
unmarked strand. -/
theorem torsion_interior_initialSlope_equations
    {g k : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) (hk : TorsionWitness
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    ∃ (script : firingScript B.graph) (rise : ℤ)
        (slope : Fin (g + 1) → ℤ),
      rise = script (rightEndpoint B) - script (leftEndpoint B) ∧
      (∑ γ, slope γ) = 0 ∧
      (B.length α : ℤ) * slope α =
        rise + ((B.length α - i.val : ℕ) : ℤ) * k ∧
      (B.length β : ℤ) * slope β =
        rise - ((B.length β - j.val : ℕ) : ℤ) * k ∧
      ∀ γ, γ ≠ α → γ ≠ β →
        (B.length γ : ℤ) * slope γ = rise := by
  obtain ⟨script, hprin⟩ :=
    exists_prin_eq_neg_marked_difference_of_torsionWitness
      (strandVertex B α i) (strandVertex B β j) k hk
  let rise := script (rightEndpoint B) - script (leftEndpoint B)
  let slope : Fin (g + 1) → ℤ := fun γ => bananaStepSlope B script γ 0
  refine ⟨script, rise, slope, rfl, ?_, ?_, ?_, ?_⟩
  · rw [← prin_leftEndpoint_eq_sum_initialSlope B script, hprin]
    have hu : strandVertex B α i ≠ leftEndpoint B :=
      strandVertex_ne_leftEndpoint B α i hi.1
    have hv : strandVertex B β j ≠ leftEndpoint B :=
      strandVertex_ne_leftEndpoint B β j hj.1
    have hu' : leftEndpoint B ≠ strandVertex B α i := Ne.symm hu
    have hv' : leftEndpoint B ≠ strandVertex B β j := Ne.symm hv
    simp [oneChip, hu', hv']
  · have hEq := initialSlope_equation B script α
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B α β j hj,
      bananaInteriorMoment_one_chip B α α i hi,
      bananaInteriorSum_one_chip B α β j hj,
      bananaInteriorSum_one_chip B α α i hi] at hEq
    simp only [hαβ, ↓reduceIte] at hEq
    dsimp [slope, rise]
    rw [Nat.cast_sub (Nat.le_of_lt hi.2)]
    nlinarith
  · have hEq := initialSlope_equation B script β
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B β β j hj,
      bananaInteriorMoment_one_chip B β α i hi,
      bananaInteriorSum_one_chip B β β j hj,
      bananaInteriorSum_one_chip B β α i hi] at hEq
    simp only [hαβ.symm, ↓reduceIte] at hEq
    dsimp [slope, rise]
    rw [Nat.cast_sub (Nat.le_of_lt hj.2)]
    nlinarith
  · intro γ hγα hγβ
    have hEq := initialSlope_equation B script γ
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B γ β j hj,
      bananaInteriorMoment_one_chip B γ α i hi,
      bananaInteriorSum_one_chip B γ β j hj,
      bananaInteriorSum_one_chip B γ α i hi] at hEq
    simp only [hγβ, hγα, ↓reduceIte, sub_zero, mul_zero] at hEq
    simpa [slope, rise] using hEq

/-! ## The finite-sum arithmetic behind the torsion lower bound -/

private theorem sum_le_neg_card_of_all_negative {n : ℕ}
    (s : Fin n → ℤ) (hneg : ∀ a, s a < 0) :
    ∑ a, s a ≤ -(n : ℤ) := by
  calc
    ∑ a, s a ≤ ∑ _a : Fin n, (-1 : ℤ) := by
      apply Finset.sum_le_sum
      intro a _ha
      have ha := hneg a
      omega
    _ = -(n : ℤ) := by simp

private theorem sum_erase_nonnegative {n : ℕ} (s : Fin n → ℤ)
    (a : Fin n) (hnonneg : ∀ b, b ≠ a → 0 ≤ s b) :
    0 ≤ ∑ b ∈ (Finset.univ.erase a), s b := by
  apply Finset.sum_nonneg
  intro b hb
  exact hnonneg b (Finset.ne_of_mem_erase hb)

private theorem sum_erase_ge_card {n : ℕ} (s : Fin n → ℤ)
    (a : Fin n) (hpos : ∀ b, b ≠ a → 0 < s b) :
    (n - 1 : ℕ) ≤ ∑ b ∈ (Finset.univ.erase a), s b := by
  have hcard : (Finset.univ.erase a).card = n - 1 := by simp
  calc
    ((n - 1 : ℕ) : ℤ) = ∑ _b ∈ (Finset.univ.erase a), (1 : ℤ) := by
      simp [hcard]
    _ ≤ ∑ b ∈ (Finset.univ.erase a), s b := by
      apply Finset.sum_le_sum
      intro b hb
      exact (show (1 : ℤ) ≤ s b by
        have := hpos b (Finset.ne_of_mem_erase hb)
        omega)

private theorem sum_erase_le_neg_card {n : ℕ} (s : Fin n → ℤ)
    (a : Fin n) (hneg : ∀ b, b ≠ a → s b < 0) :
    ∑ b ∈ (Finset.univ.erase a), s b ≤ -((n - 1 : ℕ) : ℤ) := by
  have hcard : (Finset.univ.erase a).card = n - 1 := by simp
  calc
    ∑ b ∈ (Finset.univ.erase a), s b ≤
        ∑ _b ∈ (Finset.univ.erase a), (-1 : ℤ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact (show s b ≤ -1 by
        have := hneg b (Finset.ne_of_mem_erase hb)
        omega)
    _ = -((n - 1 : ℕ) : ℤ) := by simp [hcard]

/-- If every strand has the same nonzero integral rise and the left endpoint
is one of the marks, the marked multiple is strictly larger than the genus.
This is the slope form of paper Lemma 4.20. -/
theorem endpoint_slope_period_gt_genus {g k : ℕ} (hk : 0 < k)
    (length : Fin (g + 1) → ℕ) (hlen : ∀ a, 0 < length a)
    (s : Fin (g + 1) → ℤ) (rise : ℤ)
    (hrise : ∀ a, rise = (length a : ℤ) * s a)
    (hsum : ∑ a, s a = -(k : ℤ)) :
    g < k := by
  have hriseNeg : rise < 0 := by
    by_contra hnot
    push Not at hnot
    have hsNonneg : ∀ a, 0 ≤ s a := by
      intro a
      have ha := hrise a
      have hla : (0 : ℤ) < length a := by exact_mod_cast hlen a
      nlinarith
    have hsumNonneg : 0 ≤ ∑ a, s a := Finset.sum_nonneg fun a _ => hsNonneg a
    rw [hsum] at hsumNonneg
    omega
  have hsNeg : ∀ a, s a < 0 := by
    intro a
    have ha := hrise a
    have hla : (0 : ℤ) < length a := by exact_mod_cast hlen a
    nlinarith
  have hbound := sum_le_neg_card_of_all_negative s hsNeg
  rw [hsum] at hbound
  push_cast at hbound
  omega

/-- Slope form of the endpoint/penultimate case (paper Lemma 4.23). -/
theorem endpoint_penultimate_slope_period_gt_genus
    {g k : ℕ} (hk : 0 < k) (distinguished : Fin (g + 1))
    (length : Fin (g + 1) → ℕ) (hlen : ∀ a, 0 < length a)
    (hdist : 2 ≤ length distinguished)
    (s : Fin (g + 1) → ℤ) (rise : ℤ)
    (hriseOther : ∀ a, a ≠ distinguished →
      rise = (length a : ℤ) * s a)
    (hriseDist : rise = (length distinguished : ℤ) * s distinguished + k)
    (hsum : ∑ a, s a = -(k : ℤ)) :
    g < k := by
  have hriseNeg : rise < 0 := by
    by_contra hnot
    push Not at hnot
    have hsOther : ∀ a, a ≠ distinguished → 0 ≤ s a := by
      intro a ha
      have hEq := hriseOther a ha
      have hla : (0 : ℤ) < length a := by exact_mod_cast hlen a
      nlinarith
    have hsDist : -(k : ℤ) < s distinguished := by
      have hld : (2 : ℤ) ≤ length distinguished := by exact_mod_cast hdist
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      nlinarith [hriseDist]
    have hErase := sum_erase_nonnegative s distinguished hsOther
    have hsplit : ∑ a, s a =
        s distinguished + ∑ a ∈ (Finset.univ.erase distinguished), s a := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ distinguished)]
    have htotal : -(k : ℤ) =
        s distinguished + ∑ a ∈ (Finset.univ.erase distinguished), s a := by
      rw [← hsum, hsplit]
    omega
  have hsNeg : ∀ a, s a < 0 := by
    intro a
    by_cases ha : a = distinguished
    · subst a
      have hld : (0 : ℤ) < length distinguished := by exact_mod_cast hlen distinguished
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      nlinarith [hriseDist]
    · have hEq := hriseOther a ha
      have hla : (0 : ℤ) < length a := by exact_mod_cast hlen a
      nlinarith
  have hbound := sum_le_neg_card_of_all_negative s hsNeg
  rw [hsum] at hbound
  push_cast at hbound
  omega

/-- For two distinct interior marks, a nonzero endpoint rise already forces
the torsion period to be at least the genus.  This is the common sign argument
behind all interior exceptional cases of Proposition 4.19. -/
theorem interior_torsion_rise_zero_or_period_ge_genus
    {g k : ℕ} (_hg : 1 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    ∃ (script : firingScript B.graph) (rise : ℤ)
        (slope : Fin (g + 1) → ℤ),
      rise = script (rightEndpoint B) - script (leftEndpoint B) ∧
      (∑ γ, slope γ) = 0 ∧
      (B.length α : ℤ) * slope α =
        rise + ((B.length α - i.val : ℕ) : ℤ) * k ∧
      (B.length β : ℤ) * slope β =
        rise - ((B.length β - j.val : ℕ) : ℤ) * k ∧
      (∀ γ, γ ≠ α → γ ≠ β →
        (B.length γ : ℤ) * slope γ = rise) ∧
      (rise = 0 ∨ g ≤ k) := by
  obtain ⟨script, rise, slope, hrise, hsum, hAlpha, hBeta, hOther⟩ :=
    torsion_interior_initialSlope_equations B α β i j
    hi hj hαβ hTO.1
  refine ⟨script, rise, slope, hrise, hsum, hAlpha, hBeta, hOther, ?_⟩
  have hk : 0 < k := hTO.1.1
  rcases lt_trichotomy rise 0 with hneg | hzero | hpos
  · right
    have hnegOther : ∀ γ, γ ≠ α → slope γ < 0 := by
      intro γ hγα
      by_cases hγβ : γ = β
      · subst γ
        have hlen : (0 : ℤ) < B.length β := by exact_mod_cast B.length_pos β
        have hnj : (0 : ℤ) < ((B.length β - j.val : ℕ) : ℤ) := by
          exact_mod_cast Nat.sub_pos_of_lt hj.2
        have hkz : (0 : ℤ) < k := by exact_mod_cast hk
        nlinarith [hBeta]
      · have hEq := hOther γ hγα hγβ
        have hlen : (0 : ℤ) < B.length γ := by exact_mod_cast B.length_pos γ
        nlinarith
    have hAlphaLt : slope α < k := by
      have hlen : (0 : ℤ) < B.length α := by exact_mod_cast B.length_pos α
      have hiPos : (0 : ℤ) < i.val := by exact_mod_cast hi.1
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      rw [Nat.cast_sub (Nat.le_of_lt hi.2)] at hAlpha
      nlinarith
    have hErase := sum_erase_le_neg_card slope α hnegOther
    have hsplit : ∑ γ, slope γ = slope α +
        ∑ γ ∈ (Finset.univ.erase α), slope γ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ α)]
    have hgCast : (((g + 1) - 1 : ℕ) : ℤ) = g := by norm_num
    rw [hgCast] at hErase
    rw [hsplit] at hsum
    have : (g : ℤ) < k := by nlinarith
    exact_mod_cast (show g ≤ k by omega)
  · exact Or.inl hzero
  · right
    have hposOther : ∀ γ, γ ≠ β → 0 < slope γ := by
      intro γ hγβ
      by_cases hγα : γ = α
      · subst γ
        have hlen : (0 : ℤ) < B.length α := by exact_mod_cast B.length_pos α
        have hni : (0 : ℤ) < ((B.length α - i.val : ℕ) : ℤ) := by
          exact_mod_cast Nat.sub_pos_of_lt hi.2
        have hkz : (0 : ℤ) < k := by exact_mod_cast hk
        nlinarith [hAlpha]
      · have hEq := hOther γ hγα hγβ
        have hlen : (0 : ℤ) < B.length γ := by exact_mod_cast B.length_pos γ
        nlinarith
    have hBetaGt : -(k : ℤ) < slope β := by
      have hlen : (0 : ℤ) < B.length β := by exact_mod_cast B.length_pos β
      have hjPos : (0 : ℤ) < j.val := by exact_mod_cast hj.1
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      rw [Nat.cast_sub (Nat.le_of_lt hj.2)] at hBeta
      nlinarith
    have hErase := sum_erase_ge_card slope β hposOther
    have hsplit : ∑ γ, slope γ = slope β +
        ∑ γ ∈ (Finset.univ.erase β), slope γ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ β)]
    have hgCast : (((g + 1) - 1 : ℕ) : ℤ) = g := by norm_num
    rw [hgCast] at hErase
    rw [hsplit] at hsum
    have : (g : ℤ) < k := by nlinarith
    exact_mod_cast (show g ≤ k by omega)

theorem fintype_sum_eq_two_of_zero_off {n : ℕ} (s : Fin n → ℤ)
    (a b : Fin n) (hab : a ≠ b)
    (hoff : ∀ c, c ≠ a → c ≠ b → s c = 0) :
    ∑ c, s c = s a + s b := by
  classical
  calc
    ∑ c, s c = s a + ∑ c ∈ (Finset.univ.erase a), s c := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    _ = s a + s b := by
      congr 1
      rw [Finset.sum_eq_single b]
      · intro c hc hcb
        exact hoff c (Finset.ne_of_mem_erase hc) hcb
      · exact fun hbmem =>
          (hbmem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)).elim

/-- In the zero-rise near-opposite case, both marked strands have length two.
This is the corrected zero-rise core of paper Lemma 4.27. -/
theorem zero_rise_cross_oneOff_forces_both_length_two
    {g k : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (hi : i.val = 1)
    (hj : j.val + 1 = B.length β)
    (hiInt : B.IsInteriorPosition α i) (hjInt : B.IsInteriorPosition β j)
    (hk : 0 < k) (slope : Fin (g + 1) → ℤ)
    (hsum : (∑ γ, slope γ) = 0)
    (hAlpha : (B.length α : ℤ) * slope α =
      ((B.length α - i.val : ℕ) : ℤ) * k)
    (hBeta : (B.length β : ℤ) * slope β =
      -((B.length β - j.val : ℕ) : ℤ) * k)
    (hOther : ∀ γ, γ ≠ α → γ ≠ β →
      (B.length γ : ℤ) * slope γ = 0) :
    B.length α = 2 ∧ B.length β = 2 := by
  have hiInt' : 0 < i.val ∧ i.val < B.length α := hiInt
  have hjInt' : 0 < j.val ∧ j.val < B.length β := hjInt
  have hOtherZero : ∀ γ, γ ≠ α → γ ≠ β → slope γ = 0 := by
    intro γ hγα hγβ
    have hEq := hOther γ hγα hγβ
    have hlen : (0 : ℤ) < B.length γ := by exact_mod_cast B.length_pos γ
    nlinarith
  have hTwo := fintype_sum_eq_two_of_zero_off slope α β hαβ hOtherZero
  rw [hTwo] at hsum
  have hAlpha' := hAlpha
  have hBeta' := hBeta
  have hdiffAlpha : B.length α - i.val = B.length α - 1 := by omega
  rw [hdiffAlpha] at hAlpha'
  have hnj : B.length β - j.val = 1 := by omega
  rw [hnj] at hBeta'
  norm_num at hBeta'
  have hslopePos : (0 : ℤ) < slope α := by
    have hkz : (0 : ℤ) < k := by exact_mod_cast hk
    have hlenNat : 1 < B.length α := by omega
    have hlen : (1 : ℤ) < B.length α := by exact_mod_cast hlenNat
    rw [Nat.cast_sub (by omega : 1 ≤ B.length α)] at hAlpha'
    nlinarith
  have hK : (k : ℤ) = (B.length β : ℤ) * slope α := by
    nlinarith [hBeta']
  have hAlphaCast := hAlpha'
  rw [Nat.cast_sub (by omega : 1 ≤ B.length α)] at hAlphaCast
  rw [hK] at hAlphaCast
  have hfactor : (B.length α : ℤ) =
      ((B.length α : ℤ) - 1) * B.length β := by
    apply mul_right_cancel₀ (ne_of_gt hslopePos)
    calc
      (B.length α : ℤ) * slope α =
          ((B.length α : ℤ) - 1) *
            ((B.length β : ℤ) * slope α) := hAlphaCast
      _ = (((B.length α : ℤ) - 1) * B.length β) * slope α := by ring
  have hαgeNat : 2 ≤ B.length α := by omega
  have hβgeNat : 2 ≤ B.length β := by omega
  have hαge : (2 : ℤ) ≤ B.length α := by exact_mod_cast hαgeNat
  have hβge : (2 : ℤ) ≤ B.length β := by exact_mod_cast hβgeNat
  have hαeq : B.length α = 2 := by
    exact_mod_cast (show (B.length α : ℤ) = 2 by nlinarith [hfactor])
  rw [hαeq] at hfactor
  norm_num at hfactor
  have hβeq : B.length β = 2 := by
    exact_mod_cast hfactor.symm
  exact ⟨hαeq, hβeq⟩

/-- Corrected Lemma 4.27 for the near-opposite interior family. -/
theorem cross_oneOff_torsion_dichotomy
    {g k : ℕ} (hg : 1 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (hiInt : B.IsInteriorPosition α i)
    (hjInt : B.IsInteriorPosition β j)
    (hi : i.val = 1) (hj : j.val + 1 = B.length β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k := by
  obtain ⟨script, rise, slope, _hrise, hsum, hAlpha, hBeta, hOther,
      hRise⟩ := interior_torsion_rise_zero_or_period_ge_genus hg B α β
        i j hiInt hjInt hαβ hTO
  rcases hRise with hzero | hge
  · left
    have hAlpha0 := hAlpha
    have hBeta0 := hBeta
    rw [hzero] at hAlpha0 hBeta0
    simp only [zero_add, zero_sub] at hAlpha0 hBeta0
    have hOther0 : ∀ γ, γ ≠ α → γ ≠ β →
        (B.length γ : ℤ) * slope γ = 0 := by
      intro γ hγα hγβ
      simpa [hzero] using hOther γ hγα hγβ
    obtain ⟨hαLen, hβLen⟩ := zero_rise_cross_oneOff_forces_both_length_two
      B α β i j hαβ hi hj hiInt hjInt hTO.1.1 slope hsum
        hAlpha0 (by simpa [neg_mul] using hBeta0) hOther0
    have hiMid : 2 * i.val = B.length α := by omega
    have hjMid : 2 * j.val = B.length β := by omega
    have hException : CorrectedMidpointException B α β i j :=
      ⟨hαβ, hiMid, hjMid, Or.inl hαLen⟩
    have hTwo := correctedMidpointException_torsionOrder_two B α β i j hException
    have hkLe : k ≤ 2 := hTO.2 2 hTwo.1
    have hTwoLe : 2 ≤ k := hTwo.2 k hTO.1
    exact ⟨hException, by omega⟩
  · exact Or.inr hge

theorem isTorsionOrder_swap_marks {G : CFGraph} (u v : G.V) {k : ℕ}
    (hTO : IsTorsionOrder (mark G u v) k) :
    IsTorsionOrder (mark G v u) k := by
  refine ⟨torsionWitness_swap u v hTO.1, ?_⟩
  intro m hm
  exact hTO.2 m (torsionWitness_swap v u hm)

/-- Corrected Lemma 4.23: an endpoint and the penultimate point of a strand
have torsion order strictly larger than the genus. -/
theorem leftEndpoint_penultimate_torsionOrder_gt_genus
    {g k : ℕ} (B : Banana g) (β : Fin (g + 1))
    (j : B.PathPosition β) (hjInt : B.IsInteriorPosition β j)
    (hj : j.val + 1 = B.length β)
    (hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (strandVertex B β j)) k) :
    g < k := by
  obtain ⟨script, hprin⟩ :=
    exists_prin_eq_neg_marked_difference_of_torsionWitness
      (leftEndpoint B) (strandVertex B β j) k hTO.1
  let rise : ℤ := script (rightEndpoint B) - script (leftEndpoint B)
  let slope : Fin (g + 1) → ℤ := fun γ => bananaStepSlope B script γ 0
  have hsum : ∑ γ, slope γ = -(k : ℤ) := by
    rw [← prin_leftEndpoint_eq_sum_initialSlope B script, hprin]
    have hne : leftEndpoint B ≠ strandVertex B β j :=
      (strandVertex_ne_leftEndpoint B β j hjInt.1).symm
    simp [oneChip, hne]
  have hDist : rise = (B.length β : ℤ) * slope β + k := by
    have hEq := initialSlope_equation B script β
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B β β j hjInt,
      bananaInteriorMoment_one_chip_leftEndpoint,
      bananaInteriorSum_one_chip B β β j hjInt,
      bananaInteriorSum_one_chip_leftEndpoint] at hEq
    simp at hEq
    have hjZ : (j.val : ℤ) + 1 = B.length β := by exact_mod_cast hj
    dsimp [rise, slope]
    nlinarith
  have hOther : ∀ γ, γ ≠ β →
      rise = (B.length γ : ℤ) * slope γ := by
    intro γ hγβ
    have hEq := initialSlope_equation B script γ
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B γ β j hjInt,
      bananaInteriorMoment_one_chip_leftEndpoint,
      bananaInteriorSum_one_chip B γ β j hjInt,
      bananaInteriorSum_one_chip_leftEndpoint] at hEq
    simp only [hγβ, ↓reduceIte, sub_zero, mul_zero] at hEq
    dsimp [rise, slope]
    nlinarith
  have hjInt' : 0 < j.val ∧ j.val < B.length β := hjInt
  have hlenTwo : 2 ≤ B.length β := by omega
  exact endpoint_penultimate_slope_period_gt_genus hTO.1.1 β B.length
    B.length_pos hlenTwo slope rise hOther hDist hsum

/-- Reflected endpoint/near-endpoint form of the preceding theorem. -/
theorem rightEndpoint_one_torsionOrder_gt_genus
    {g k : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (hiInt : B.IsInteriorPosition α i)
    (hi : i.val = 1)
    (hTO : IsTorsionOrder
      (mark B.graph (rightEndpoint B) (strandVertex B α i)) k) :
    g < k := by
  obtain ⟨script, hprin⟩ :=
    exists_prin_eq_neg_marked_difference_of_torsionWitness
      (rightEndpoint B) (strandVertex B α i) k hTO.1
  let rise : ℤ := script (rightEndpoint B) - script (leftEndpoint B)
  let finalSlope : Fin (g + 1) → ℤ := fun γ =>
    bananaStepSlope B script γ (B.length γ - 1)
  let reverseSlope : Fin (g + 1) → ℤ := fun γ => -finalSlope γ
  have hsum : ∑ γ, reverseSlope γ = -(k : ℤ) := by
    rw [show (∑ γ, reverseSlope γ) = -∑ γ, finalSlope γ by
      simp [reverseSlope]]
    rw [← prin_rightEndpoint_eq_neg_sum_finalSlope B script, hprin]
    have hne : rightEndpoint B ≠ strandVertex B α i :=
      (strandVertex_ne_rightEndpoint B α i hiInt.2).symm
    simp [oneChip, hne]
  have hDist : -rise = (B.length α : ℤ) * reverseSlope α + k := by
    have hInitial := initialSlope_equation B script α
    have hInterior := bananaInteriorSum_prin B script α
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B α α i hiInt,
      bananaInteriorMoment_one_chip_rightEndpoint,
      bananaInteriorSum_one_chip B α α i hiInt,
      bananaInteriorSum_one_chip_rightEndpoint] at hInitial
    rw [hprin, bananaInteriorSum_zsmul, bananaInteriorSum_sub,
      bananaInteriorSum_one_chip B α α i hiInt,
      bananaInteriorSum_one_chip_rightEndpoint] at hInterior
    simp at hInitial hInterior
    have hiZ : (i.val : ℤ) = 1 := by exact_mod_cast hi
    dsimp [rise, reverseSlope, finalSlope]
    nlinarith
  have hOther : ∀ γ, γ ≠ α →
      -rise = (B.length γ : ℤ) * reverseSlope γ := by
    intro γ hγα
    have hInitial := initialSlope_equation B script γ
    have hInterior := bananaInteriorSum_prin B script γ
    rw [hprin, bananaInteriorMoment_zsmul, bananaInteriorSum_zsmul,
      bananaInteriorMoment_sub, bananaInteriorSum_sub,
      bananaInteriorMoment_one_chip B γ α i hiInt,
      bananaInteriorMoment_one_chip_rightEndpoint,
      bananaInteriorSum_one_chip B γ α i hiInt,
      bananaInteriorSum_one_chip_rightEndpoint] at hInitial
    rw [hprin, bananaInteriorSum_zsmul, bananaInteriorSum_sub,
      bananaInteriorSum_one_chip B γ α i hiInt,
      bananaInteriorSum_one_chip_rightEndpoint] at hInterior
    simp only [hγα, ↓reduceIte, sub_zero, mul_zero] at hInitial hInterior
    dsimp [rise, reverseSlope, finalSlope]
    nlinarith
  have hiInt' : 0 < i.val ∧ i.val < B.length α := hiInt
  have hlenTwo : 2 ≤ B.length α := by omega
  exact endpoint_penultimate_slope_period_gt_genus hTO.1.1 α B.length
    B.length_pos hlenTwo reverseSlope (-rise) hOther hDist hsum

end Bananas
