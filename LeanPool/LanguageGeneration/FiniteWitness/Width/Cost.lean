/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Width.Value
import Mathlib.Order.Lattice.Nat

/-!
# Set-valued separators and their cardinality cost
-/

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- A positive set-valued assignment that separates every subfamily with finite intersection. -/
def IsSeparator (H : Set (Set α)) (P : Set α → Set α) : Prop :=
  (∀ L ∈ H, P L ⊆ L) ∧ SetSeparates H P

/-- The finite cardinality of a set, or the top width value for an infinite set. -/
noncomputable def setCost (S : Set α) : SeparationValue := by
  classical
  exact if h : S.Finite then finiteValue h.toFinset.card else ⊤

/-- The supremum of the assigned set costs over the target family. -/
noncomputable def assignmentCost (H : Set (Set α)) (P : Set α → Set α) : SeparationValue :=
  ⨆ L : H, setCost (P L)

theorem setCost_le_finite_iff (S : Set α) (d : ℕ) :
    setCost S ≤ finiteValue d ↔ ∃ h : S.Finite, h.toFinset.card ≤ d := by
  classical
  by_cases h : S.Finite
  · simp [setCost, h]
  · simp [setCost, h]

theorem setCost_le_omega_iff (S : Set α) : setCost S ≤ omegaValue ↔ S.Finite := by
  classical
  by_cases h : S.Finite
  · simp only [setCost, dite_eq_left h]
    exact iff_of_true (finiteValue_le_omega _) h
  · simp [setCost, h, omegaValue]

theorem cost_le_finite_iff (H : Set (Set α)) (P : Set α → Set α) (d : ℕ) :
    assignmentCost H P ≤ finiteValue d ↔
      ∀ L ∈ H, ∃ h : (P L).Finite, h.toFinset.card ≤ d := by
  simp only [assignmentCost, iSup_le_iff, setCost_le_finite_iff, Subtype.forall]

theorem cost_le_omega_iff (H : Set (Set α)) (P : Set α → Set α) :
    assignmentCost H P ≤ omegaValue ↔ ∀ L ∈ H, (P L).Finite := by
  simp only [assignmentCost, iSup_le_iff, setCost_le_omega_iff, Subtype.forall]

theorem separator_to_valid {H : Set (Set α)} {P : Set α → Set α}
    (hP : IsSeparator H P) (hf : ∀ L ∈ H, (P L).Finite) :
    ∃ T : Set α → Finset α, Valid H T ∧ ∀ L ∈ H, (↑(T L) : Set α) = P L := by
  classical
  let T : Set α → Finset α := fun L => if h : (P L).Finite then h.toFinset else ∅
  have he (L) (hL : L ∈ H) : (↑(T L) : Set α) = P L := by simp [T, hf L hL]
  refine ⟨T, (valid_iff_positive_separates H T).mpr ⟨?_, ?_⟩, he⟩
  · intro L hL
    rw [he L hL]
    exact hP.1 L hL
  · apply (setSeparates_finset H T).mp
    intro F hFH hF hfin
    obtain ⟨L, hL, K, hK, hn⟩ := hP.2 F hFH hF hfin
    exact ⟨L, hL, K, hK, by simpa only [he L (hFH hL)] using hn⟩

theorem valid_to_separator {H : Set (Set α)} {T : Set α → Finset α}
    (h : Valid H T) : IsSeparator H (fun L => (↑(T L) : Set α)) :=
  ⟨h.1, (setSeparates_finset H T).mpr ((valid_iff_positive_separates H T).mp h).2⟩

theorem bounded_iff_cost_le (H : Set (Set α)) (d : ℕ) :
    HasBoundedWitnesses H d ↔
      ∃ P, IsSeparator H P ∧ assignmentCost H P ≤ finiteValue d := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨fun L => (↑(T L) : Set α), valid_to_separator hT,
      (cost_le_finite_iff H _ d).mpr ?_⟩
    intro L hL
    refine ⟨(T L).finite_toSet, ?_⟩
    simpa using hd L hL
  · rintro ⟨P, hP, hc⟩
    have hcard := (cost_le_finite_iff H P d).mp hc
    obtain ⟨T, hT, he⟩ := separator_to_valid hP (fun L hL => (hcard L hL).choose)
    refine ⟨T, hT, ?_⟩
    intro L hL
    obtain ⟨hf, hb⟩ := hcard L hL
    have ht : T L = hf.toFinset := Finset.coe_injective ((he L hL).trans hf.coe_toFinset.symm)
    simpa only [ht] using hb

theorem finiteWitnesses_iff_cost_le_omega (H : Set (Set α)) :
    HasFiniteWitnesses H ↔
      ∃ P, IsSeparator H P ∧ assignmentCost H P ≤ omegaValue := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨fun L => (↑(T L) : Set α), valid_to_separator hT,
      (cost_le_omega_iff H _).mpr (fun L _ => (T L).finite_toSet)⟩
  · rintro ⟨P, hP, hc⟩
    obtain ⟨T, hT, _⟩ := separator_to_valid hP ((cost_le_omega_iff H P).mp hc)
    exact hT.hasFiniteWitnesses

theorem identity_separator {H : Set (Set α)} (hUUS : Generic.UUS H) :
    IsSeparator H id := by
  classical
  refine ⟨fun _ _ => Set.Subset.rfl, ?_⟩
  intro F hFH hF hcore
  obtain ⟨L, hL⟩ := hF
  obtain ⟨x, hxL, hx⟩ := (hUUS L (hFH hL)).exists_notMem_finset hcore.toFinset
  have hnot : x ∉ ⋂₀ F := fun h => hx (hcore.mem_toFinset.mpr h)
  simp only [Set.mem_sInter, not_forall] at hnot
  obtain ⟨K, hK, hxK⟩ := hnot
  exact ⟨L, hL, K, hK, fun h => hxK (h hxL)⟩

theorem width_le_assignmentCost {H : Set (Set α)} {P : Set α → Set α}
    (hP : IsSeparator H P) : separationWidth H ≤ assignmentCost H P := by
  generalize hc : assignmentCost H P = w
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe v =>
    induction v using WithTop.recTopCoe with
    | top =>
      apply (width_le_omega_iff H).mpr
      exact (finiteWitnesses_iff_cost_le_omega H).mpr ⟨P, hP, le_of_eq hc⟩
    | coe n =>
      apply (width_le_finite_iff H n).mpr
      exact (bounded_iff_cost_le H n).mpr ⟨P, hP, le_of_eq hc⟩

theorem width_cost_attained {H : Set (Set α)} (hUUS : Generic.UUS H) :
    ∃ P, IsSeparator H P ∧ assignmentCost H P = separationWidth H := by
  classical
  suffices ∃ P, IsSeparator H P ∧ assignmentCost H P ≤ separationWidth H by
    obtain ⟨P, hP, hc⟩ := this
    exact ⟨P, hP, le_antisymm hc (width_le_assignmentCost hP)⟩
  by_cases h : ∃ d, HasBoundedWitnesses H d
  · obtain ⟨P, hP, hc⟩ := (bounded_iff_cost_le H _).mp (Nat.find_spec h)
    exact ⟨P, hP, by simpa only [separationWidth, dite_eq_left h] using hc⟩
  · by_cases hw : HasFiniteWitnesses H
    · obtain ⟨P, hP, hc⟩ := (finiteWitnesses_iff_cost_le_omega H).mp hw
      exact ⟨P, hP, by simpa only [separationWidth, dite_eq_right h, ite_eq_left hw] using hc⟩
    · exact ⟨id, identity_separator hUUS, by simp [separationWidth, h, hw]⟩

/-- Exact correspondence with the minimum-over-assignments definition in the paper. -/
theorem width_isLeast_cost {H : Set (Set α)} (hUUS : Generic.UUS H) :
    IsLeast {w | ∃ P, IsSeparator H P ∧ assignmentCost H P = w} (separationWidth H) := by
  refine ⟨width_cost_attained hUUS, ?_⟩
  rintro w ⟨P, hP, rfl⟩
  exact width_le_assignmentCost hP

theorem width_eq_finite_of_bounds {H : Set (Set α)} {d : ℕ}
    (hu : HasBoundedWitnesses H d)
    (hl : ∀ q, HasBoundedWitnesses H q → d ≤ q) : separationWidth H = finiteValue d := by
  classical
  have hex : ∃ q, HasBoundedWitnesses H q := ⟨d, hu⟩
  rw [separationWidth, dite_eq_left hex]
  congr 1
  exact le_antisymm (Nat.find_min' hex hu) (hl _ (Nat.find_spec hex))

end GenLimit.FiniteWitness
