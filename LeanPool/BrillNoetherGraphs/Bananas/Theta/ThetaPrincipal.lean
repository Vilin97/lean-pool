/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaMoment

/-! # Theta Principal -/

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! Firing-script values and slopes in the normalized strand coordinates. -/
def normalizedPathValue
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (r : ℕ) : ℤ :=
  if hr : r ≤ B.length α then
    script (strandVertex B α ⟨r, by omega⟩)
  else 0

def normalizedStepSlope
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (k : ℕ) : ℤ :=
  normalizedPathValue B script α (k + 1) -
    normalizedPathValue B script α k

theorem normalizedPathValue_eq
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (r : ℕ) (hr : r ≤ B.length α) :
    normalizedPathValue B script α r =
      script (strandVertex B α ⟨r, by omega⟩) := by
  simp [normalizedPathValue, hr]

theorem normalizedStepSlope_eq
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (k : ℕ) (hk : k < B.length α) :
    normalizedStepSlope B script α k =
      script (strandVertex B α ⟨k + 1, by omega⟩) -
        script (strandVertex B α ⟨k, by omega⟩) := by
  unfold normalizedStepSlope
  rw [normalizedPathValue_eq B script α (k + 1) (by omega),
    normalizedPathValue_eq B script α k (by omega)]

/- TeX label: `prop-JacBanana` (telescoping normalized slopes). -/
theorem sum_normalizedStepSlope
    (B : Banana 2) (script : firing_script B.graph) (α : Fin 3) :
    ∑ k ∈ Finset.range (B.length α),
        normalizedStepSlope B script α k =
      script (rightEndpoint B) - script (leftEndpoint B) := by
  unfold normalizedStepSlope
  rw [Finset.sum_range_sub]
  rw [normalizedPathValue_eq B script α (B.length α) (by omega),
    normalizedPathValue_eq B script α 0 (by omega),
    strandVertex_length B α, strandVertex_zero B α]

/-! `IsStepSlope` follows the stored orientation of each core edge, whereas
`normalizedStepSlope` always follows the common coordinate from core vertex
`0` to core vertex `1`.  Thus a reversed stored edge needs both a sign and an
index reversal. -/
def storageStepSlope
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (k : ℕ) : ℤ :=
  if B.core.tail α = 0 then
    normalizedStepSlope B script α k
  else
    -normalizedStepSlope B script α (B.length α - 1 - k)

/- TeX label: `prop-JacBanana` (orientation-normalized slope datum). -/
theorem storageStepSlope_isStepSlope
    (B : Banana 2) (script : firing_script B.graph) :
    B.IsStepSlope script (storageStepSlope B script) := by
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
    simp only [storageStepSlope, ht, ↓reduceIte]
    exact (normalizedStepSlope_eq B script α o.val o.isLt).symm
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
    simp only [storageStepSlope, ht, ↓reduceIte]
    have hk : B.length α - 1 - o.val < B.length α := by
      have hlen := B.length_pos α
      omega
    rw [normalizedStepSlope_eq B script α _ hk]
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

/- TeX label: `prop-JacBanana` (principal divisor at normalized interior
vertices). -/
theorem prin_normalized_interior
    (B : Banana 2) (script : firing_script B.graph)
    (α : Fin 3) (r : Fin (B.length α - 1)) :
    prin B.graph script
        (strandVertex B α ⟨r.val + 1, by omega⟩) =
      normalizedStepSlope B script α (r.val + 1) -
        normalizedStepSlope B script α r.val := by
  have hslope := storageStepSlope_isStepSlope B script
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
    simp only [storageStepSlope, ht, ↓reduceIte]
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
    simp only [storageStepSlope, ht, ↓reduceIte, hqSucc, hq]
    ring

/- TeX label: `prop-JacBanana` (interior moment of a principal divisor). -/
theorem interiorMoment_prin
    (B : Banana 2) (script : firing_script B.graph) (α : Fin 3) :
    interiorMoment B α (prin B.graph script) =
      (B.length α : ℤ) *
          normalizedStepSlope B script α (B.length α - 1) -
        (script (rightEndpoint B) - script (leftEndpoint B)) := by
  unfold interiorMoment
  have hsum :
      Finset.sum (Finset.range (B.length α - 1))
          (fun r => if h : r + 1 < B.length α then
            ((r + 1 : ℕ) : ℤ) *
              prin B.graph script (strandVertex B α ⟨r + 1, by omega⟩)
          else 0) =
        Finset.sum (Finset.range (B.length α - 1))
          (fun r => ((r + 1 : ℕ) : ℤ) *
            (normalizedStepSlope B script α (r + 1) -
              normalizedStepSlope B script α r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrange : r < B.length α - 1 := Finset.mem_range.mp hr
    have hrlt : r + 1 < B.length α := by omega
    rw [dif_pos hrlt]
    rw [prin_normalized_interior B script α ⟨r, hrange⟩]
  rw [hsum]
  have htel := weighted_step_difference_telescope
    (B.length α) (fun k => normalizedStepSlope B script α k)
  have hslopeSum := sum_normalizedStepSlope B script α
  rw [hslopeSum] at htel
  linarith

/- TeX label: `prop-JacBanana` (right endpoint principal coefficient). -/
theorem prin_rightEndpoint_eq
    (B : Banana 2) (script : firing_script B.graph) :
    prin B.graph script (rightEndpoint B) =
      -∑ α : Fin 3,
        normalizedStepSlope B script α (B.length α - 1) := by
  have h := B.prin_coreVertex_eq_endpointSum
    (storageStepSlope_isStepSlope B script) (1 : Fin 2)
  rw [show rightEndpoint B = B.coreVertex (1 : Fin 2) by rfl, h]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  by_cases ht : B.core.tail α = 0
  · have hh : B.core.head α = 1 := head_eq_other_of_tail B α ht
    simp [ht, hh, storageStepSlope]
  · have ht1 : B.core.tail α = 1 := by
      apply Fin.ext
      have hlt := (B.core.tail α).isLt
      have hne : (B.core.tail α).val ≠ 0 := by
        intro hval
        apply ht
        apply Fin.ext
        exact hval
      omega
    have hh1 : B.core.head α ≠ 1 := by
      intro hh
      apply B.core_loopless α
      exact ht1.trans hh.symm
    have hh0 : B.core.head α = 0 := by
      apply Fin.ext
      have hlt := (B.core.head α).isLt
      have hne : (B.core.head α).val ≠ 1 := by
        intro hval
        apply hh1
        apply Fin.ext
        exact hval
      omega
    simp [ht1, hh0, storageStepSlope]

/- TeX label: `prop-JacBanana` (principal divisor maps to the theta lattice). -/
theorem thetaJacobianMoment_prin_mem
    (B : Banana 2) (script : firing_script B.graph) :
    thetaJacobianMoment B (prin B.graph script) ∈
      thetaLattice (B.length 0) (B.length 1) (B.length 2) := by
  unfold thetaJacobianMoment
  rw [interiorMoment_prin, interiorMoment_prin, interiorMoment_prin]
  rw [prin_rightEndpoint_eq]
  let x := normalizedStepSlope B script 0 (B.length 0 - 1)
  let y := normalizedStepSlope B script 1 (B.length 1 - 1)
  let z := normalizedStepSlope B script 2 (B.length 2 - 1)
  have hxy : normalizedStepSlope B script 0 (B.length 0 - 1) = x := rfl
  have hyy : normalizedStepSlope B script 1 (B.length 1 - 1) = y := rfl
  have hzy : normalizedStepSlope B script 2 (B.length 2 - 1) = z := rfl
  have hsum3 :
      (∑ α : Fin 3,
        normalizedStepSlope B script α (B.length α - 1)) = x + y + z := by
    have hvalue : ∀ α : Fin 3,
        normalizedStepSlope B script α (B.length α - 1) =
          if α = 0 then x else if α = 1 then y else z := by
      intro α
      fin_cases α
      · simpa using hxy
      · simpa using hyy
      · simpa using hzy
    simp_rw [hvalue]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  simp only [hxy, hyy, hzy]
  rw [hsum3]
  apply (thetaLattice_mem_iff (B.length 0) (B.length 1) (B.length 2) _ _).mpr
  refine ⟨-z, y, ?_, ?_⟩
  · simp only [sub_eq_add_neg]
    simp only [Nat.cast_add]
    ring
  · ring

end Bananas
