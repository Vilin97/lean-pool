/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.PermCongr

/-!
# The block-cycle normal form

Every permutation is conjugate to a block sum of rotations whose
block lengths are its full cycle type (fixed points included):
the normal form against which the skein trace of a permutation
factors into cycle loops.
-/

@[expose] public section

namespace RS

open Equiv Equiv.Perm

/-- The block sum of rotations prescribed by a list of block
lengths. -/
noncomputable def blockCycles : (l : List ℕ) → Perm (Fin l.sum)
  | [] => 1
  | c :: rest =>
      (finSumFinEquiv.permCongr
        (Equiv.sumCongr (finRotate c) (blockCycles rest)) :
        Perm (Fin (c + rest.sum)))

/-- The full cycle type: the cycle type completed by the fixed
points as one-cycles. -/
noncomputable def fullCycleType {n : ℕ} (π : Perm (Fin n)) :
    Multiset ℕ :=
  π.cycleType + Multiset.replicate (n - π.cycleType.sum) 1

/-- The full cycle type sums to the degree. -/
theorem fullCycleType_sum {n : ℕ} (π : Perm (Fin n)) :
    (fullCycleType π).sum = n := by
  rw [fullCycleType, Multiset.sum_add,
    Multiset.sum_replicate, smul_eq_mul, mul_one]
  have h1 := π.sum_cycleType
  have h2 : π.support.card ≤ n := by
    have := Finset.card_le_card
      (Finset.subset_univ π.support)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  omega

/-! ## The cycle type of a block sum -/

/-- The block cycles realize a prescribed full cycle type. -/
theorem cycleType_blockCycles (l : List ℕ)
    (hl : ∀ c ∈ l, 1 ≤ c) :
    (blockCycles l).cycleType =
      (l.filter (fun c => 2 ≤ c) : Multiset ℕ) := by
  induction l with
  | nil =>
    simp only [blockCycles, cycleType_one, List.filter_nil]
    rfl
  | cons c rest ih =>
    have hc : 1 ≤ c := hl c (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hl x
      (List.mem_cons_of_mem _ hx)
    -- blockCycles (c :: rest) unfolds to finSumFinEquiv.permCongr (sumCongr
    --   ...)
    have key : (blockCycles (c :: rest)).cycleType =
        (finRotate c).cycleType + (blockCycles rest).cycleType := by
      change cycleType (finSumFinEquiv.permCongr
        (Equiv.sumCongr (finRotate c) (blockCycles rest))) = _
      rw [cycleType_permCongr, cycleType_sumCongr]
    rw [key, ih hrest]
    -- Handle finRotate c: either c = 1 or c ≥ 2
    rcases eq_or_lt_of_le hc with rfl | hc2
    · -- c = 1: finRotate 1 = 1, filter drops it
      rw [show finRotate 1 = (1 : Perm (Fin 1)) from finRotate_one]
      rw [cycleType_one, Multiset.zero_add]
      simp
    · -- c ≥ 2: cycleType = {c}, filter keeps it
      rw [cycleType_finRotate_of_le hc2]
      simp only [List.filter_cons]
      have hd : decide (2 ≤ c) = true := by
        rw [decide_eq_true_eq]; omega
      simp only [hd, ite_true]
      rw [← Multiset.cons_coe, Multiset.singleton_add]

/-- **The normal form**: every permutation is conjugate to the
block sum of rotations along its full cycle type. -/
theorem exists_conj_blockCycles {n : ℕ} (π : Perm (Fin n)) :
    ∃ (l : List ℕ) (h : l.sum = n) (σ : Perm (Fin n)),
      (∀ c ∈ l, 1 ≤ c) ∧
      (l : Multiset ℕ) = fullCycleType π ∧
      σ * (finCongr h).permCongr (blockCycles l) * σ⁻¹ = π := by
  set l := (fullCycleType π).toList
  have hcoe : (l : Multiset ℕ) = fullCycleType π := Multiset.coe_toList _
  have hsum : l.sum = n := by
    have := congr_arg Multiset.sum hcoe
    rw [Multiset.sum_coe] at this
    rw [this, fullCycleType_sum]
  have hmem : ∀ c ∈ l, 1 ≤ c := by
    intro c hc
    rw [← Multiset.mem_coe, hcoe, fullCycleType] at hc
    rcases Multiset.mem_add.mp hc with hct | hrep
    · exact le_of_lt (one_lt_of_mem_cycleType hct)
    · exact le_of_eq (Multiset.eq_of_mem_replicate hrep).symm
  have hct_eq : ((finCongr hsum).permCongr (blockCycles l)).cycleType =
      π.cycleType := by
    rw [cycleType_permCongr, cycleType_blockCycles _ hmem]
    rw [← Multiset.filter_coe, hcoe, fullCycleType]
    rw [Multiset.filter_add,
      Multiset.filter_eq_self.mpr (fun _ h => two_le_of_mem_cycleType h),
      Multiset.filter_eq_nil.mpr (fun a ha => by
        rw [Multiset.eq_of_mem_replicate ha]; omega),
      Multiset.add_zero]
  have hconj : IsConj ((finCongr hsum).permCongr (blockCycles l)) π :=
    isConj_iff_cycleType_eq.mpr hct_eq
  obtain ⟨σ, hσ⟩ := isConj_iff.mp hconj
  exact ⟨l, hsum, σ, hmem, hcoe, hσ⟩

end RS
