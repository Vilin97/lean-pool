/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SubsetEH

/-!
# The add-one-variable recurrence for `hSub`

`hSub (insert j A) (m+1) = hSub A (m+1) + X j * hSub (insert j A) m`
-/

namespace RS

open Finset MvPolynomial

open scoped Classical in
/-- The add-one-variable recurrence: terms either avoid the new
variable or use it at least once. -/
theorem hSub_insert {k : ℕ} {A : Finset (Fin k)} {j : Fin k}
    (hj : j ∉ A) (m : ℕ) :
    hSub (insert j A) (m + 1) = hSub A (m + 1) + X j * hSub (insert j A) m := by
  classical
  -- Rewrite all three hSub into explicit filtered sums over Sym, keeping
  -- the Sym type explicit to prevent Sym/Subtype transparency issues.
  change ∑ w ∈ Finset.univ.filter
      (fun w : Sym (Fin k) (m + 1) => ∀ i ∈ w.1, i ∈ insert j A),
      (w.1.map (X : Fin k → MvPolynomial (Fin k) ℂ)).prod =
    ∑ w ∈ Finset.univ.filter
      (fun w : Sym (Fin k) (m + 1) => ∀ i ∈ w.1, i ∈ A),
      (w.1.map X).prod +
    X j * ∑ w ∈ Finset.univ.filter
      (fun w : Sym (Fin k) m => ∀ i ∈ w.1, i ∈ insert j A),
      (w.1.map X).prod
  -- Split LHS by predicate j ∈ w.1
  conv_lhs =>
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter
        (fun w : Sym (Fin k) (m + 1) => ∀ i ∈ w.1, i ∈ insert j A))
      (fun w : Sym (Fin k) (m + 1) => j ∈ w.1)
      (fun w : Sym (Fin k) (m + 1) =>
        (w.1.map (X : Fin k → MvPolynomial (Fin k) ℂ)).prod)]
  -- Now LHS = ∑(j∈w) + ∑(j∉w); swap to match RHS order
  rw [add_comm]
  congr 1
  -- Part 1: ∑(j∉w, supp ⊆ insert j A) = ∑(supp ⊆ A)
  · apply Finset.sum_congr
    · rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro w _
      constructor
      · rintro ⟨hsup, hjnot⟩ i hi
        rcases Finset.mem_insert.mp (hsup i hi) with rfl | hmem
        · exact absurd hi hjnot
        · exact hmem
      · intro hsup
        exact ⟨fun i hi => Finset.mem_insert.mpr (Or.inr (hsup i hi)),
               fun hjw => hj (hsup j hjw)⟩
    · intros; rfl
  -- Part 2: ∑(j∈w, supp ⊆ insert j A) = X j * ∑(supp ⊆ insert j A, degree m)
  · rw [Finset.mul_sum]
    -- Save j under a let-alias; Finset.sum_bij' has a parameter also named j
    -- which would shadow the theorem's j inside by-blocks.
    let jj := j
    exact Finset.sum_bij'
      -- forward: w ↦ ⟨w.1.erase j, card_proof⟩
      (fun (w : Sym (Fin k) (m + 1)) (hw) =>
        (⟨w.1.erase jj, by
          have hmem : jj ∈ w.1 := (Finset.mem_filter.mp hw).2
          rw [Multiset.card_erase_of_mem hmem, w.2, Nat.pred_succ]⟩
        : Sym (Fin k) m))
      -- backward: w' ↦ ⟨j ::ₘ w'.1, card_proof⟩
      (fun (w' : Sym (Fin k) m) (_hw') =>
        (⟨jj ::ₘ w'.1, by rw [Multiset.card_cons, w'.2]⟩
        : Sym (Fin k) (m + 1)))
      -- forward membership: erase preserves support ⊆ insert j A
      (fun w hw => by
        have hmf := Finset.mem_filter.mp hw
        have hsup := (Finset.mem_filter.mp hmf.1).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi =>
          hsup i (Multiset.mem_of_mem_erase hi)⟩)
      -- backward membership: cons j preserves support and adds j ∈ w.1
      (fun w' hw' => by
        have hsup' := (Finset.mem_filter.mp hw').2
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩,
           Multiset.mem_cons_self jj w'.1⟩
        rcases Multiset.mem_cons.mp hi with rfl | hmem
        · exact Finset.mem_insert_self jj A
        · exact hsup' i hmem)
      -- left inverse: j ::ₘ (w.1.erase j) = w.1
      (fun w hw => by
        ext1
        exact Multiset.cons_erase (Finset.mem_filter.mp hw).2)
      -- right inverse: (j ::ₘ w'.1).erase j = w'.1
      (fun w' _ => by
        ext1
        exact Multiset.erase_cons_head jj w'.1)
      -- weight: (w.1.map X).prod = X j * ((w.1.erase j).map X).prod
      (fun w hw => by
        have hmem : jj ∈ w.1 := (Finset.mem_filter.mp hw).2
        change (w.1.map X).prod = X jj * ((w.1.erase jj).map X).prod
        conv_lhs => rw [(Multiset.cons_erase hmem).symm]
        rw [Multiset.map_cons, Multiset.prod_cons])

end RS
