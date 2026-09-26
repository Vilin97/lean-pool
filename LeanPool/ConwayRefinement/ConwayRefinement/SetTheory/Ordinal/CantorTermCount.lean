/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal

import Mathlib.Data.List.Sort

/-!
# Number of terms in an uncompressed Cantor normal form

LM24, Proposition 5.6.1 bounds the number of infinite-support irreducible factors by the number
of terms in the Cantor normal form of the degree. Finite coefficients are counted with
multiplicity: for example, `ω + ω` has two terms.

`NatOrdinal.cantorTermCount` is therefore the length of
`Ordinal.additivePrincipalTerms`. Its characteristic arithmetic theorem says that this count is
additive under Hessenberg sum, exactly as required when a series factorisation splits its degree.
-/

open scoped NatOrdinal

public noncomputable section

namespace NatOrdinal

/-- The number of terms in the uncompressed Cantor normal form of a natural ordinal. -/
def cantorTermCount (a : NatOrdinal) : ℕ :=
  a.val.additivePrincipalTerms.length

/-- Evaluation of the Cantor term count on an ordinary ordinal. -/
@[simp]
theorem cantorTermCount_of (o : Ordinal) :
    cantorTermCount (NatOrdinal.of o) = o.additivePrincipalTerms.length := by
  rw [cantorTermCount, NatOrdinal.val_of]

@[simp]
theorem cantorTermCount_zero : cantorTermCount 0 = 0 := by
  simp [cantorTermCount]

/-- A nonzero natural ordinal has at least one Cantor term. -/
theorem cantorTermCount_pos {a : NatOrdinal} (ha : a ≠ 0) :
    0 < cantorTermCount a := by
  rw [cantorTermCount, List.length_pos_iff_ne_nil]
  intro hnil
  have hsum := Ordinal.additivePrincipalTerms_sum a.val
  rw [hnil] at hsum
  apply ha
  apply NatOrdinal.val.injective
  simpa using hsum.symm

/-- A natural ordinal has no Cantor terms exactly when it is zero. -/
@[simp]
theorem cantorTermCount_eq_zero {a : NatOrdinal} :
    cantorTermCount a = 0 ↔ a = 0 := by
  constructor
  · intro hcount
    by_contra ha
    exact (Nat.ne_of_gt (cantorTermCount_pos ha)) hcount
  · rintro rfl
    exact cantorTermCount_zero

private def mergedTerms (a b : NatOrdinal) : List Ordinal :=
  (a.val.additivePrincipalTerms ++ b.val.additivePrincipalTerms).insertionSort (· ≥ ·)

private theorem mergedTerms_sorted (a b : NatOrdinal) :
    (mergedTerms a b).SortedGE := by
  exact List.sortedGE_insertionSort

private theorem mergedTerms_perm (a b : NatOrdinal) :
    List.Perm (mergedTerms a b)
      (a.val.additivePrincipalTerms ++ b.val.additivePrincipalTerms) := by
  exact List.perm_insertionSort _ _

private theorem mergedTerms_principal (a b : NatOrdinal) :
    ∀ o ∈ mergedTerms a b, Ordinal.IsAdditivelyPrincipal o := by
  intro o ho
  have ho' := (mergedTerms_perm a b).mem_iff.mp ho
  rw [List.mem_append] at ho'
  exact ho'.elim Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms
    Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms

private theorem mergedTerms_naturalSum (a b : NatOrdinal) :
    ((mergedTerms a b).map NatOrdinal.of).sum = a + b := by
  calc
    ((mergedTerms a b).map NatOrdinal.of).sum =
        ((a.val.additivePrincipalTerms ++
          b.val.additivePrincipalTerms).map NatOrdinal.of).sum :=
      ((mergedTerms_perm a b).map NatOrdinal.of).sum_eq
    _ = (a.val.additivePrincipalTerms.map NatOrdinal.of).sum +
        (b.val.additivePrincipalTerms.map NatOrdinal.of).sum := by
      rw [List.map_append, List.sum_append]
    _ = NatOrdinal.of a.val + NatOrdinal.of b.val := by
      rw [← Ordinal.natOrdinal_of_sum_eq_sum_map_of_sorted
          (fun _ h ↦ Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms h)
          (Ordinal.additivePrincipalTerms_sortedGE a.val),
        ← Ordinal.natOrdinal_of_sum_eq_sum_map_of_sorted
          (fun _ h ↦ Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms h)
          (Ordinal.additivePrincipalTerms_sortedGE b.val),
        Ordinal.additivePrincipalTerms_sum,
        Ordinal.additivePrincipalTerms_sum]
    _ = a + b := by simp

private theorem mergedTerms_eq_additivePrincipalTerms (a b : NatOrdinal) :
    mergedTerms a b = (a + b).val.additivePrincipalTerms := by
  apply Ordinal.additivePrincipalTerms_unique
  · apply NatOrdinal.of.injective
    calc
      NatOrdinal.of (mergedTerms a b).sum =
          ((mergedTerms a b).map NatOrdinal.of).sum :=
        Ordinal.natOrdinal_of_sum_eq_sum_map_of_sorted
          (mergedTerms_principal a b) (mergedTerms_sorted a b)
      _ = a + b := mergedTerms_naturalSum a b
      _ = NatOrdinal.of (a + b).val := by simp
  · exact mergedTerms_principal a b
  · exact mergedTerms_sorted a b

theorem additivePrincipalTerms_add_perm (a b : NatOrdinal) :
    List.Perm (a + b).val.additivePrincipalTerms
      (a.val.additivePrincipalTerms ++ b.val.additivePrincipalTerms) := by
  rw [← mergedTerms_eq_additivePrincipalTerms]
  exact mergedTerms_perm a b

/-- The number of uncompressed Cantor terms is additive under Hessenberg sum. -/
@[simp]
theorem cantorTermCount_add (a b : NatOrdinal) :
    cantorTermCount (a + b) = cantorTermCount a + cantorTermCount b := by
  rw [cantorTermCount, cantorTermCount, cantorTermCount,
    ← mergedTerms_eq_additivePrincipalTerms]
  calc
    (mergedTerms a b).length =
        (a.val.additivePrincipalTerms ++
          b.val.additivePrincipalTerms).length :=
      (mergedTerms_perm a b).length_eq
    _ = a.val.additivePrincipalTerms.length +
        b.val.additivePrincipalTerms.length := List.length_append

-- Not a simp lemma: `simp` normalizes `r • a` to `↑r * a`.
theorem cantorTermCount_nsmul (r : ℕ) (a : NatOrdinal) :
    cantorTermCount (r • a) = r * cantorTermCount a := by
  induction r with
  | zero => simp
  | succ r ih => rw [succ_nsmul, cantorTermCount_add, ih, Nat.succ_mul]

end NatOrdinal
