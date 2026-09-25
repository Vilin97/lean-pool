/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
/-!
# Natural-ceiling subgroup filtrations

Generic order-theoretic infrastructure for extending a natural-number-indexed
subgroup filtration to the real line by the natural-number ceiling.
-/

@[expose] public section

noncomputable section

namespace RamificationTheory

section IntegerStepFiltration

variable {G : Type*} [Group G]

/-- Extend a subgroup filtration indexed by natural numbers to the real line
by taking the natural-number ceiling.  This is the ceiling-indexed step
filtration relevant to the principal-unit filtration. -/
def natCeilStepFiltration
    (F : ℕ → Subgroup G) (t : ℝ) : Subgroup G :=
  F ⌈t⌉₊

/-- The right-limit subgroup of a natural-ceiling step filtration. -/
def natCeilStepFiltrationAfter
    (F : ℕ → Subgroup G) (t : ℝ) : Subgroup G :=
  ⨆ s : {s : ℝ // t < s}, natCeilStepFiltration F s

/-- A jump of a natural-ceiling step filtration is a strict drop from the
group at the index to its right-limit subgroup. -/
def IsNatCeilStepFiltrationJump
    (F : ℕ → Subgroup G) (t : ℝ) : Prop :=
  natCeilStepFiltration F t ≠ natCeilStepFiltrationAfter F t

/-- An antitone natural-number filtration remains antitone after extension by
the natural-number ceiling. -/
theorem natCeilStepFiltration_antitone
    {F : ℕ → Subgroup G} (hF : Antitone F) :
    Antitone (natCeilStepFiltration F) := by
  intro s t hst
  exact hF (Nat.ceil_mono hst)

/-- The right-limit subgroup of an antitone natural-ceiling filtration lies
in the group at the limiting index. -/
theorem natCeilStepFiltrationAfter_le
    {F : ℕ → Subgroup G} (hF : Antitone F) (t : ℝ) :
    natCeilStepFiltrationAfter F t ≤ natCeilStepFiltration F t := by
  apply iSup_le
  intro s
  exact natCeilStepFiltration_antitone hF (le_of_lt s.property)

/-- At a natural-number index, the right-limit of a ceiling-indexed
antitone filtration is exactly the next group. -/
theorem natCeilStepFiltrationAfter_natCast
    {F : ℕ → Subgroup G} (hF : Antitone F) (n : ℕ) :
    natCeilStepFiltrationAfter F (n : ℝ) = F (n + 1) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    exact hF (Nat.add_one_le_ceil_iff.mpr s.property)
  · let s : {s : ℝ // (n : ℝ) < s} :=
      ⟨((n + 1 : ℕ) : ℝ), by exact_mod_cast Nat.lt_succ_self n⟩
    exact le_iSup_of_le s (by
      simp only [natCeilStepFiltration]
      have hs : (s : ℝ) = (n : ℝ) + 1 := by
        simp [s]
      have hnat : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
        norm_num
      rw [hs, hnat, Nat.ceil_natCast])

/-- At a natural-number index, being a jump is equivalent to a strict change
between two consecutive groups. -/
theorem isNatCeilStepFiltrationJump_natCast_iff
    {F : ℕ → Subgroup G} (hF : Antitone F) (n : ℕ) :
    IsNatCeilStepFiltrationJump F (n : ℝ) ↔
      F n ≠ F (n + 1) := by
  simp [IsNatCeilStepFiltrationJump, natCeilStepFiltration,
    natCeilStepFiltrationAfter_natCast hF n]

/-- Every jump of an antitone natural-ceiling step filtration is a
nonnegative rational integer. -/
theorem isNatCeilStepFiltrationJump_integer
    {F : ℕ → Subgroup G} (hF : Antitone F) {t : ℝ}
    (ht : IsNatCeilStepFiltrationJump F t) :
    ∃ n : ℕ, t = n := by
  let n : ℕ := ⌈t⌉₊
  by_cases htn : t = (n : ℝ)
  · exact ⟨n, htn⟩
  · have ht_lt_n : t < (n : ℝ) :=
      lt_of_le_of_ne (Nat.le_ceil t) htn
    let s : ℝ := (t + n) / 2
    have hts : t < s := by
      dsimp [s]
      linarith
    have hs_lt_n : s < (n : ℝ) := by
      dsimp [s]
      linarith
    have hceil : ⌈s⌉₊ = n := by
      apply le_antisymm
      · exact Nat.ceil_le.mpr hs_lt_n.le
      · change ⌈t⌉₊ ≤ ⌈s⌉₊
        exact Nat.ceil_mono hts.le
    have hstep :
        natCeilStepFiltration F s = natCeilStepFiltration F t := by
      simp [natCeilStepFiltration, n, hceil]
    exfalso
    apply ht
    apply le_antisymm
    · exact le_iSup_of_le (⟨s, hts⟩ :
        {u : ℝ // t < u}) hstep.symm.le
    · exact natCeilStepFiltrationAfter_le hF t

end IntegerStepFiltration

end RamificationTheory
