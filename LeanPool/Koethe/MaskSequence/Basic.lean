/-
Copyright (c) 2026 Tom Adamczewski and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Use
import LeanPool.Koethe.Pencil

/-!
# Sparse periodic masks

The bookkeeping in this file is purely combinatorial.  In particular it does
not use a matrix-mortality theorem: that theorem will be a hypothesis of the
sequence construction.

We use the integral invariant `4 * assigned < period`.  If a compatible word
has length `l`, repeating the old mask `4*l+1` times before installing the word
preserves this invariant.  Thus no limiting density or geometric-series
calculation is needed.
-/

noncomputable section

namespace KoetheCounterexample
namespace MaskSequence

variable {k : Type*} [Field k]

/-- All assignments, at all sites, of `M` persist in `N`. -/
def Extends (N M : PeriodicMask k) : Prop :=
  ∀ n z, M.lookup n = some z → N.lookup n = some z

@[refl] theorem Extends.refl (M : PeriodicMask k) : Extends M M :=
  fun _ _ h => h

theorem Extends.trans {L M N : PeriodicMask k}
    (hNM : Extends N M) (hML : Extends M L) : Extends N L :=
  fun n z h => hNM n z (hML n z h)

theorem lookup_nonzero (M : PeriodicMask k) {n : ℕ} {z : Triple k}
    (h : M.lookup n = some z) : z ≠ 0 :=
  M.nonzero _ z h

@[simp] theorem lookup_fin (M : PeriodicMask k) (i : Fin M.period) :
    M.lookup i.val = M.value i := by
  simp [PeriodicMask.lookup, Nat.mod_eq_of_lt i.is_lt]

theorem lookup_mod_of_dvd (M : PeriodicMask k) {p : ℕ}
    (hp : M.period ∣ p) (n : ℕ) : M.lookup (n % p) = M.lookup n := by
  simp only [PeriodicMask.lookup, Nat.mod_mod_of_dvd n hp]

theorem lookup_add_of_mod_eq_zero (M : PeriodicMask k) {b : ℕ}
    (hb : b % M.period = 0) (i : ℕ) : M.lookup (b + i) = M.lookup i := by
  simp [PeriodicMask.lookup, Nat.add_mod, hb]

theorem holes_add_assigned (M : PeriodicMask k) :
    M.holes + M.assigned = M.period := by
  classical
  simpa [PeriodicMask.holes, PeriodicMask.assigned] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin M.period => M.value i = none))

theorem enough_holes (M : PeriodicMask k)
    (h : 4 * M.assigned < M.period) : M.period < 2 * M.holes := by
  have := holes_add_assigned M
  omega

/-- The unassigned mask of period one. -/
def emptyMask : PeriodicMask k where
  period := 1
  period_pos := by decide
  value := fun _ => none
  nonzero := by simp

@[simp] theorem emptyMask_assigned : (emptyMask (k := k)).assigned = 0 := by
  classical
  simp [PeriodicMask.assigned, emptyMask]

/-- Exact cardinal count for lifting *all* old assignments to `c` periods. -/
theorem lifted_assigned_card (M : PeriodicMask k) (c : ℕ) :
    (Finset.univ.filter fun i : Fin (c * M.period) => M.lookup i.val ≠ none).card =
      c * M.assigned := by
  classical
  let e : {i : Fin (c * M.period) // M.lookup i.val ≠ none} ≃
      Fin c × {i : Fin M.period // M.value i ≠ none} :=
    { toFun := fun i =>
        ((finProdFinEquiv.symm i.val).1,
          ⟨(finProdFinEquiv.symm i.val).2, i.property⟩)
      invFun := fun i =>
        ⟨finProdFinEquiv (i.1, i.2.val), by
          simpa [PeriodicMask.lookup, finProdFinEquiv, Nat.mod_eq_of_lt i.2.val.is_lt]
            using i.2.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact finProdFinEquiv.apply_symm_apply i.val
      right_inv := by
        intro i
        apply Prod.ext
        · change (finProdFinEquiv.symm (finProdFinEquiv (i.1, i.2.val))).1 = i.1
          exact congrArg (fun p : Fin c × Fin M.period => p.1)
            (finProdFinEquiv.symm_apply_apply (i.1, i.2.val))
        · apply Subtype.ext
          change (finProdFinEquiv.symm (finProdFinEquiv (i.1, i.2.val))).2 = i.2.val
          exact congrArg (fun p : Fin c × Fin M.period => p.2)
            (finProdFinEquiv.symm_apply_apply (i.1, i.2.val)) }
  simpa [Fintype.card_subtype, PeriodicMask.assigned] using Fintype.card_congr e

/-- Refine a mask by installing a nonzero compatible word in its first block.
Outside that block every previous assignment is retained. -/
def install (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : PeriodicMask k where
  period := (4 * w.length + 1) * M.period
  period_pos := Nat.mul_pos (by omega) M.period_pos
  value := fun i => if h : i.val < w.length then some (w.get ⟨i.val, h⟩)
    else M.lookup i.val
  nonzero := by
    intro i z hz
    split_ifs at hz with hi
    · have heq : w.get ⟨i.val, hi⟩ = z := Option.some.inj hz
      subst z
      exact hw _ (List.get_mem w _)
    · exact lookup_nonzero M hz

@[simp] theorem install_period (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) :
    (install M w hw).period = (4 * w.length + 1) * M.period := rfl

theorem period_dvd_install (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : M.period ∣ (install M w hw).period :=
  dvd_mul_left _ _

theorem length_le_install_period (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : w.length ≤ (install M w hw).period := by
  have hQ : 1 ≤ M.period := M.period_pos
  change w.length ≤ (4 * w.length + 1) * M.period
  nlinarith

theorem install_extends (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (hc : M.Compatible w) : Extends (install M w hw) M := by
  intro n z hz
  let N := install M w hw
  have hlookup : M.lookup (n % N.period) = some z := by
    rw [lookup_mod_of_dvd M (period_dvd_install M w hw), hz]
  change (if h : n % N.period < w.length then
      some (w.get ⟨n % N.period, h⟩) else M.lookup (n % N.period)) = some z
  split_ifs with hn
  · rw [hc ⟨n % N.period, hn⟩ z hlookup]
  · exact hlookup

theorem install_word (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (i : Fin w.length) :
    (install M w hw).lookup i.val = some (w.get i) := by
  have hi : i.val < (install M w hw).period :=
    lt_of_lt_of_le i.is_lt (length_le_install_period M w hw)
  change (install M w hw).lookup (⟨i.val, hi⟩ : Fin (install M w hw).period).val = _
  rw [lookup_fin]
  exact dite_eq_left i.is_lt

/-- Installing the word adds at most its length to the lifted assigned set. -/
theorem install_assigned_le (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) :
    (install M w hw).assigned ≤
      (4 * w.length + 1) * M.assigned + w.length := by
  classical
  let N := install M w hw
  let old : Finset (Fin N.period) := Finset.univ.filter fun i => M.lookup i.val ≠ none
  let block : Finset (Fin N.period) := Finset.univ.filter fun i => i.val < w.length
  have hsub : (Finset.univ.filter fun i => N.value i ≠ none) ⊆ old ∪ block := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, old, block, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i.val < w.length
    · exact Or.inr h
    · exact Or.inl (by simpa [N, install, h] using hi)
  have hold : old.card = (4 * w.length + 1) * M.assigned :=
    lifted_assigned_card M _
  have hblock : block.card = w.length := by
    rw [show block.card = Fintype.card {i : Fin N.period // i.val < w.length} by
      simp [block, Fintype.card_subtype]]
    exact Fintype.card_fin_lt_of_le (length_le_install_period M w hw)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le old block).trans_eq (by rw [hold, hblock]))

/-- An adaptive integral density budget: the positive old slack is amplified
by `4 * length + 1`, whereas the cost of the new block is at most `4 * length`.
The new slack is therefore still at least one. -/
theorem install_sparse (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (hM : 4 * M.assigned < M.period) :
    4 * (install M w hw).assigned < (install M w hw).period := by
  have hcard := install_assigned_le M w hw
  have hslack : 4 * M.assigned + 1 ≤ M.period := hM
  have hmul := Nat.mul_le_mul_left (4 * w.length + 1) hslack
  rw [install_period]
  nlinarith

end MaskSequence
end KoetheCounterexample

end
