/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Branching
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Arbitrary-rank interlacing

Mickelsson operators, interlacing schedules, and canonical projected-axis witnesses.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonPathCommutator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

/-- The upper polarization path commutator used in the spherical-code argument. -/
def upperPolarizationPathCommutator {r n : ℕ}
    (a b : Fin (r + 1)) :
    List (Fin (r + 1)) →
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
  | [] => 0
  | [_] => 0
  | i :: j :: tail =>
      (polarization r n j i).comp
          (upperPolarizationPathCommutator a b (j :: tail)) +
        (if b = j then
          (polarization r n a i).comp
            (lowerPolarizationPath (j :: tail))
        else 0) -
        (if i = a then
          (polarization r n j b).comp
            (lowerPolarizationPath (j :: tail))
        else 0)

@[simp] theorem upperPolarizationPathCommutator_nil
    {r n : ℕ} (a b : Fin (r + 1)) :
    upperPolarizationPathCommutator (n := n) a b [] = 0 := rfl

@[simp] theorem upperPolarizationPathCommutator_singleton
    {r n : ℕ} (a b i : Fin (r + 1)) :
    upperPolarizationPathCommutator (n := n) a b [i] = 0 := rfl

theorem polarization_lowerPolarizationPath_commutator
    {r n : ℕ} (a b : Fin (r + 1))
    (path : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    polarization r n a b (lowerPolarizationPath path p) =
      lowerPolarizationPath path (polarization r n a b p) +
        upperPolarizationPathCommutator a b path p := by
  induction path generalizing p with
  | nil => simp only [lowerPolarizationPath, LinearMap.id_coe, id_eq, polarization_apply, map_sum,
             upperPolarizationPathCommutator_nil, LinearMap.zero_apply, add_zero]
  | cons i rest ih =>
      cases rest with
      | nil => simp only [lowerPolarizationPath, LinearMap.id_coe, id_eq, polarization_apply,
                 map_sum, upperPolarizationPathCommutator_singleton, LinearMap.zero_apply, add_zero]
      | cons j tail =>
          change
            polarization r n a b
                (polarization r n j i
                  (lowerPolarizationPath (j :: tail) p)) =
              polarization r n j i
                  (lowerPolarizationPath (j :: tail)
                    (polarization r n a b p)) +
                ((polarization r n j i).comp
                    (upperPolarizationPathCommutator a b (j :: tail)) +
                  (if b = j then
                    (polarization r n a i).comp
                      (lowerPolarizationPath (j :: tail))
                  else 0) -
                  (if i = a then
                    (polarization r n j b).comp
                      (lowerPolarizationPath (j :: tail))
                  else 0)) p
          rw [polarization_polarization_commutator,
            ih (p := p)]
          simp only [map_add, LinearMap.sub_apply,
            LinearMap.add_apply, LinearMap.comp_apply]
          split_ifs <;> simp <;> abel

theorem lowerPolarizationPath_append_cons_apply
    {r n : ℕ} (front : List (Fin (r + 1)))
    (middle : Fin (r + 1)) (suffix : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    lowerPolarizationPath (front ++ middle :: suffix) p =
      lowerPolarizationPath (front ++ [middle])
        (lowerPolarizationPath (middle :: suffix) p) := by
  induction front generalizing p with
  | nil => simp only [List.nil_append, lowerPolarizationPath, LinearMap.id_coe, id_eq]
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          change
            polarization r n j i
                (lowerPolarizationPath
                  ((j :: tail) ++ middle :: suffix) p) =
              polarization r n j i
                (lowerPolarizationPath
                  ((j :: tail) ++ [middle])
                  (lowerPolarizationPath (middle :: suffix) p))
          rw [ih]

theorem upperPolarizationPathCommutator_eq_zero_of_le
    {r n : ℕ} (a b : Fin (r + 1)) (hab : a < b)
    (path : List (Fin (r + 1)))
    (hpath : path.Pairwise (· < ·))
    (hle : ∀ i ∈ path, i ≤ a) :
    upperPolarizationPathCommutator (n := n) a b path = 0 := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          have hij : i < j :=
            (List.pairwise_cons.mp hpath).1 j (by simp only [List.mem_cons, true_or])
          have hrest : (j :: tail).Pairwise (· < ·) :=
            (List.pairwise_cons.mp hpath).2
          have hrestle : ∀ q ∈ (j :: tail), q ≤ a := by
            intro q hq
            exact hle q (by simp only [List.mem_cons, hq, or_true])
          have hjle : j ≤ a := hrestle j (by simp only [List.mem_cons, true_or])
          have hbj : b ≠ j := ne_of_gt (lt_of_le_of_lt hjle hab)
          have hia : i ≠ a := ne_of_lt (lt_of_lt_of_le hij hjle)
          change
            (polarization r n j i).comp
                (upperPolarizationPathCommutator a b (j :: tail)) +
              (if b = j then
                (polarization r n a i).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) -
              (if i = a then
                (polarization r n j b).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) = 0
          rw [ih hrest hrestle, ite_eq_right hbj, ite_eq_right hia]
          simp only [LinearMap.comp_zero, add_zero, sub_self]

theorem upperPolarizationPathCommutator_eq_zero_of_ge
    {r n : ℕ} (a b : Fin (r + 1)) (hab : a < b)
    (path : List (Fin (r + 1)))
    (hpath : path.Pairwise (· < ·))
    (hge : ∀ i ∈ path, b ≤ i) :
    upperPolarizationPathCommutator (n := n) a b path = 0 := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          have hij : i < j :=
            (List.pairwise_cons.mp hpath).1 j (by simp only [List.mem_cons, true_or])
          have hrest : (j :: tail).Pairwise (· < ·) :=
            (List.pairwise_cons.mp hpath).2
          have hrestge : ∀ q ∈ (j :: tail), b ≤ q := by
            intro q hq
            exact hge q (by simp only [List.mem_cons, hq, or_true])
          have hbi : b ≤ i := hge i (by simp only [List.mem_cons, true_or])
          have hbj : b ≠ j := ne_of_lt (lt_of_le_of_lt hbi hij)
          have hia : i ≠ a := ne_of_gt (lt_of_lt_of_le hab hbi)
          change
            (polarization r n j i).comp
                (upperPolarizationPathCommutator a b (j :: tail)) +
              (if b = j then
                (polarization r n a i).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) -
              (if i = a then
                (polarization r n j b).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) = 0
          rw [ih hrest hrestge, ite_eq_right hbj, ite_eq_right hia]
          simp only [LinearMap.comp_zero, add_zero, sub_self]

theorem polarization_lowerPolarizationPath_commute_prefix
    {r n : ℕ} (a b : Fin (r + 1)) (hab : a < b)
    (path : List (Fin (r + 1)))
    (hpath : path.Pairwise (· < ·))
    (hle : ∀ i ∈ path, i ≤ a)
    (p : PolynomialSpace r n) :
    polarization r n a b (lowerPolarizationPath path p) =
      lowerPolarizationPath path (polarization r n a b p) := by
  rw [polarization_lowerPolarizationPath_commutator,
    upperPolarizationPathCommutator_eq_zero_of_le
      a b hab path hpath hle]
  simp only [polarization_apply, map_sum, LinearMap.zero_apply, add_zero]

theorem polarization_lowerPolarizationPath_commute_suffix
    {r n : ℕ} (a b : Fin (r + 1)) (hab : a < b)
    (path : List (Fin (r + 1)))
    (hpath : path.Pairwise (· < ·))
    (hge : ∀ i ∈ path, b ≤ i)
    (p : PolynomialSpace r n) :
    polarization r n a b (lowerPolarizationPath path p) =
      lowerPolarizationPath path (polarization r n a b p) := by
  rw [polarization_lowerPolarizationPath_commutator,
    upperPolarizationPathCommutator_eq_zero_of_ge
      a b hab path hpath hge]
  simp only [polarization_apply, map_sum, LinearMap.zero_apply, add_zero]

end ArbitraryRowMickelssonPathCommutator

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonPathRecurrence

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

theorem polarizationPathCoefficient_insert
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a : Fin (r + 1)) (S : Finset (Fin (r + 1)))
    (ha : a < row) (haS : a ∉ S) :
    polarizationPathCoefficient lam row S =
      -shiftedRowGap lam row a *
        polarizationPathCoefficient lam row (insert a S) := by
  classical
  have hamem : a ∈ precedingRows row \ S := by
    simp only [Finset.mem_sdiff, mem_precedingRows, ha, haS, not_false_eq_true, and_self]
  have hprod := Finset.mul_prod_erase
    (precedingRows row \ S) (shiftedRowGap lam row) hamem
  have hdiff : precedingRows row \ insert a S =
      (precedingRows row \ S).erase a :=
    Finset.sdiff_insert (precedingRows row) S a
  unfold polarizationPathCoefficient
  rw [Finset.card_insert_of_notMem haS, hdiff]
  rw [pow_succ]
  rw [← hprod]
  ring

theorem shiftedRowGap_sub_adjacent
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1))
    (hab : a.val + 1 = b.val) (hbrow : b < row)
    (hweight : lam b ≤ lam a) (hlow : lam row ≤ lam b) :
    shiftedRowGap lam row a - shiftedRowGap lam row b =
      ((lam a - lam b : ℕ) : ℝ) + 1 := by
  have harow : a.val < row.val := by omega
  have hrowa : lam row ≤ lam a := hlow.trans hweight
  unfold shiftedRowGap
  rw [Nat.cast_sub hrowa, Nat.cast_sub hlow,
    Nat.cast_sub hweight]
  have hshiftb : 1 ≤ row.val - b.val := by omega
  have hshifta : 1 ≤ row.val - a.val := by omega
  rw [Nat.cast_sub hshifta, Nat.cast_sub hshiftb,
    Nat.cast_sub (by omega : a.val ≤ row.val),
    Nat.cast_sub (by omega : b.val ≤ row.val)]
  norm_num
  have habreal : (a.val : ℝ) + 1 = (b.val : ℝ) := by
    exact_mod_cast hab
  linarith

end ArbitraryRowMickelssonPathRecurrence

namespace ArbitraryRowFourStateSubsetSorting

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

theorem sort_union_of_forall_lt
    {α : Type*} [LinearOrder α]
    (L U : Finset α)
    (hsep : ∀ i ∈ L, ∀ j ∈ U, i < j) :
    (L ∪ U).sort (· ≤ ·) = L.sort (· ≤ ·) ++ U.sort (· ≤ ·) := by
  apply (Finset.sortedLT_sort (L ∪ U)).pairwise.eq_of_mem_iff
  · apply List.pairwise_append.mpr
    refine ⟨(Finset.sortedLT_sort L).pairwise,
      (Finset.sortedLT_sort U).pairwise, ?_⟩
    intro i hi j hj
    exact hsep i ((Finset.mem_sort (· ≤ ·)).mp hi)
      j ((Finset.mem_sort (· ≤ ·)).mp hj)
  · intro i
    simp only [Finset.mem_sort, Finset.mem_union, List.mem_append]

theorem adjacent_subset_filter_union
    {r : ℕ} (a b : Fin (r + 1))
    (hab : a.val + 1 = b.val)
    (T : Finset (Fin (r + 1)))
    (haT : a ∉ T) (hbT : b ∉ T) :
    T = T.filter (fun i => i < a) ∪ T.filter (fun i => b < i) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hi
    have hia : i.val ≠ a.val := by
      intro heq
      apply haT
      have heqi : i = a := Fin.ext heq
      simpa only [← heqi] using hi
    have hib : i.val ≠ b.val := by
      intro heq
      apply hbT
      have heqi : i = b := Fin.ext heq
      simpa only [← heqi] using hi
    by_cases hlt : i < a
    · exact Or.inl ⟨hi, hlt⟩
    · right
      refine ⟨hi, ?_⟩
      change b.val < i.val
      have hnot : ¬ i.val < a.val := hlt
      omega
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩)
    · exact hi
    · exact hi

theorem sorted_subset_neither
    {r : ℕ} (a b : Fin (r + 1))
    (hab : a.val + 1 = b.val)
    (T : Finset (Fin (r + 1)))
    (haT : a ∉ T) (hbT : b ∉ T) :
    T.sort (· ≤ ·) =
      (T.filter (fun i => i < a)).sort (· ≤ ·) ++
        (T.filter (fun i => b < i)).sort (· ≤ ·) := by
  conv_lhs => rw [adjacent_subset_filter_union a b hab T haT hbT]
  apply sort_union_of_forall_lt
  intro i hi j hj
  have hia : i < a := (Finset.mem_filter.mp hi).2
  have hbj : b < j := (Finset.mem_filter.mp hj).2
  change i.val < j.val
  have hia' : i.val < a.val := hia
  have hbj' : b.val < j.val := hbj
  omega

theorem sorted_subset_first
    {r : ℕ} (a b : Fin (r + 1))
    (hab : a.val + 1 = b.val)
    (T : Finset (Fin (r + 1)))
    (haT : a ∉ T) (hbT : b ∉ T) :
    (insert a T).sort (· ≤ ·) =
      (T.filter (fun i => i < a)).sort (· ≤ ·) ++
        a :: (T.filter (fun i => b < i)).sort (· ≤ ·) := by
  let L := T.filter (fun i => i < a)
  let U := T.filter (fun i => b < i)
  have hT : T = L ∪ U :=
    adjacent_subset_filter_union a b hab T haT hbT
  have hins : insert a T = L ∪ insert a U := by
    ext i
    rw [hT]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.union_insert]
  have hsep : ∀ i ∈ L, ∀ j ∈ insert a U, i < j := by
    intro i hi j hj
    have hia : i < a := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_insert.mp hj with hja | hj
    · subst j
      exact hia
    · have hbj : b < j := (Finset.mem_filter.mp hj).2
      change i.val < j.val
      have hia' : i.val < a.val := hia
      have hbj' : b.val < j.val := hbj
      omega
  have hsort : (insert a U).sort (· ≤ ·) =
      a :: U.sort (· ≤ ·) := by
    apply Finset.sort_insert (· ≤ ·)
    · intro j hj
      have hbj : b < j := (Finset.mem_filter.mp hj).2
      change a.val ≤ j.val
      have hbj' : b.val < j.val := hbj
      omega
    · intro h
      have hba : b < a := (Finset.mem_filter.mp h).2
      have hba' : b.val < a.val := hba
      omega
  rw [hins, sort_union_of_forall_lt L (insert a U) hsep, hsort]

theorem sorted_subset_second
    {r : ℕ} (a b : Fin (r + 1))
    (hab : a.val + 1 = b.val)
    (T : Finset (Fin (r + 1)))
    (haT : a ∉ T) (hbT : b ∉ T) :
    (insert b T).sort (· ≤ ·) =
      (T.filter (fun i => i < a)).sort (· ≤ ·) ++
        b :: (T.filter (fun i => b < i)).sort (· ≤ ·) := by
  let L := T.filter (fun i => i < a)
  let U := T.filter (fun i => b < i)
  have hT : T = L ∪ U :=
    adjacent_subset_filter_union a b hab T haT hbT
  have hins : insert b T = L ∪ insert b U := by
    ext i
    rw [hT]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.union_insert]
  have hsep : ∀ i ∈ L, ∀ j ∈ insert b U, i < j := by
    intro i hi j hj
    have hia : i < a := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_insert.mp hj with hjb | hj
    · subst j
      change i.val < b.val
      have hia' : i.val < a.val := hia
      omega
    · have hbj : b < j := (Finset.mem_filter.mp hj).2
      change i.val < j.val
      have hia' : i.val < a.val := hia
      have hbj' : b.val < j.val := hbj
      omega
  have hsort : (insert b U).sort (· ≤ ·) =
      b :: U.sort (· ≤ ·) := by
    apply Finset.sort_insert (· ≤ ·)
    · intro j hj
      exact le_of_lt ((Finset.mem_filter.mp hj).2)
    · intro h
      exact (lt_irrefl b) ((Finset.mem_filter.mp h).2)
  rw [hins, sort_union_of_forall_lt L (insert b U) hsep, hsort]

theorem sorted_subset_both
    {r : ℕ} (a b : Fin (r + 1))
    (hab : a.val + 1 = b.val)
    (T : Finset (Fin (r + 1)))
    (haT : a ∉ T) (hbT : b ∉ T) :
    (insert a (insert b T)).sort (· ≤ ·) =
      (T.filter (fun i => i < a)).sort (· ≤ ·) ++
        a :: b :: (T.filter (fun i => b < i)).sort (· ≤ ·) := by
  let L := T.filter (fun i => i < a)
  let U := T.filter (fun i => b < i)
  have hT : T = L ∪ U :=
    adjacent_subset_filter_union a b hab T haT hbT
  have hins : insert a (insert b T) = L ∪ insert a (insert b U) := by
    ext i
    rw [hT]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.union_insert]
  have hsep : ∀ i ∈ L, ∀ j ∈ insert a (insert b U), i < j := by
    intro i hi j hj
    have hia : i < a := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_insert.mp hj with hja | hj
    · subst j
      exact hia
    · rcases Finset.mem_insert.mp hj with hjb | hj
      · subst j
        change i.val < b.val
        have hia' : i.val < a.val := hia
        omega
      · have hbj : b < j := (Finset.mem_filter.mp hj).2
        change i.val < j.val
        have hia' : i.val < a.val := hia
        have hbj' : b.val < j.val := hbj
        omega
  have hsortb : (insert b U).sort (· ≤ ·) =
      b :: U.sort (· ≤ ·) := by
    apply Finset.sort_insert (· ≤ ·)
    · intro j hj
      exact le_of_lt ((Finset.mem_filter.mp hj).2)
    · intro h
      exact (lt_irrefl b) ((Finset.mem_filter.mp h).2)
  have hsorta : (insert a (insert b U)).sort (· ≤ ·) =
      a :: (insert b U).sort (· ≤ ·) := by
    apply Finset.sort_insert (· ≤ ·)
    · intro j hj
      rcases Finset.mem_insert.mp hj with hjb | hj
      · subst j
        change a.val ≤ b.val
        omega
      · have hbj : b < j := (Finset.mem_filter.mp hj).2
        change a.val ≤ j.val
        have hbj' : b.val < j.val := hbj
        omega
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · have h' : a.val = b.val := congrArg Fin.val h
        omega
      · have hba : b < a := (Finset.mem_filter.mp h).2
        have hba' : b.val < a.val := hba
        omega
  rw [hins, sort_union_of_forall_lt L (insert a (insert b U)) hsep,
    hsorta, hsortb]

end ArbitraryRowFourStateSubsetSorting

end

end HigherHarmonicYoung

end Spherical

end MetricCodes


section

open scoped BigOperators InnerProductSpace

namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathToggle

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonSimpleRoot

private def simpleRootToggleBridge {r n : ℕ}
    (front : List (Fin (r + 1))) (i a b j : Fin (r + 1))
    (tail : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    PolynomialSpace r n :=
  lowerPolarizationPath (front ++ [i])
    (polarization r n a i
      (polarization r n j b
        (lowerPolarizationPath (j :: tail) p)))

theorem simpleRoot_suffix_highest
    {r n : ℕ} (a b j : Fin (r + 1))
    (hab : a < b)
    (tail : List (Fin (r + 1)))
    (hordered : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
      (lowerPolarizationPath (j :: tail) p) = 0 := by
  rw [polarization_lowerPolarizationPath_commute_suffix
    a b hab (j :: tail) hordered hafter p, hp, map_zero]

theorem lowerPolarizationPath_toggle_neither_factor
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    lowerPolarizationPath (front ++ i :: j :: tail) p =
      lowerPolarizationPath (front ++ [i])
        (polarization r n j i
          (lowerPolarizationPath (j :: tail) p)) := by
  rw [lowerPolarizationPath_append_cons_apply front i (j :: tail) p]
  rfl

theorem lowerPolarizationPath_toggle_first_factor
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    lowerPolarizationPath (front ++ i :: a :: j :: tail) p =
      lowerPolarizationPath (front ++ [i])
        (polarization r n a i
          (polarization r n j a
            (lowerPolarizationPath (j :: tail) p))) := by
  rw [lowerPolarizationPath_append_cons_apply front i (a :: j :: tail) p]
  rfl

theorem lowerPolarizationPath_toggle_second_factor
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    lowerPolarizationPath (front ++ i :: b :: j :: tail) p =
      lowerPolarizationPath (front ++ [i])
        (polarization r n b i
          (polarization r n j b
            (lowerPolarizationPath (j :: tail) p))) := by
  rw [lowerPolarizationPath_append_cons_apply front i (b :: j :: tail) p]
  rfl

theorem lowerPolarizationPath_toggle_both_factor
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    lowerPolarizationPath (front ++ i :: a :: b :: j :: tail) p =
      lowerPolarizationPath (front ++ [i])
        (polarization r n a i
          (polarization r n b a
            (polarization r n j b
              (lowerPolarizationPath (j :: tail) p)))) := by
  rw [lowerPolarizationPath_append_cons_apply front i (a :: b :: j :: tail) p]
  rfl

theorem simpleRoot_polarization_path_neither
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
      (lowerPolarizationPath (front ++ i :: j :: tail) p) = 0 := by
  rw [lowerPolarizationPath_toggle_neither_factor,
    polarization_lowerPolarizationPath_commute_prefix
      a b hab (front ++ [i]) hfront hbefore]
  rw [simpleRoot_path_neither i a b j hia hbj
    (lowerPolarizationPath (j :: tail) p)
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp),
    map_zero]

theorem simpleRoot_polarization_path_first
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
      (lowerPolarizationPath (front ++ i :: a :: j :: tail) p) =
      -simpleRootToggleBridge front i a b j tail p := by
  rw [lowerPolarizationPath_toggle_first_factor,
    polarization_lowerPolarizationPath_commute_prefix
      a b hab (front ++ [i]) hfront hbefore]
  rw [simpleRoot_path_first_only i a b j hia hab hbj
    (lowerPolarizationPath (j :: tail) p)
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp),
    map_neg]
  rfl

theorem simpleRoot_polarization_path_second
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
      (lowerPolarizationPath (front ++ i :: b :: j :: tail) p) =
      simpleRootToggleBridge front i a b j tail p := by
  rw [lowerPolarizationPath_toggle_second_factor,
    polarization_lowerPolarizationPath_commute_prefix
      a b hab (front ++ [i]) hfront hbefore]
  rw [simpleRoot_path_second_only i a b j hia hab hbj
    (lowerPolarizationPath (j :: tail) p)
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp)]
  rfl

theorem simpleRoot_polarization_path_both
    {r n : ℕ} (front : List (Fin (r + 1)))
    (i a b j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n) (A B : ℝ)
    (hp : polarization r n a b p = 0)
    (ha : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        A • lowerPolarizationPath (j :: tail) p)
    (hb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        B • lowerPolarizationPath (j :: tail) p) :
    polarization r n a b
      (lowerPolarizationPath (front ++ i :: a :: b :: j :: tail) p) =
      (A - B + 1) • simpleRootToggleBridge front i a b j tail p := by
  rw [lowerPolarizationPath_toggle_both_factor,
    polarization_lowerPolarizationPath_commute_prefix
      a b hab (front ++ [i]) hfront hbefore]
  rw [simpleRoot_path_both i a b j hia hab hbj
    (lowerPolarizationPath (j :: tail) p) A B
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp)
    ha hb, map_smul]
  rfl

end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathToggle

end


namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonPathToggleCoordinate

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonSimpleRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathToggle

private def coordinateToggleBridge {r n : ℕ}
    (start : Fin (r + 1)) (k : Fin n)
    (front : List (Fin (r + 1))) (i a b j : Fin (r + 1))
    (tail : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    PolynomialSpace r n :=
  MvPolynomial.X (variableIndex start k) *
    simpleRootToggleBridge front i a b j tail p

theorem simpleRoot_coordinate_mul_of_earlier
    {r n : ℕ} (a b start : Fin (r + 1)) (k : Fin n)
    (hstart : start < a) (hab : a < b)
    (q : PolynomialSpace r n) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) * q) =
      MvPolynomial.X (variableIndex start k) *
        polarization r n a b q := by
  have hne : b ≠ start := ne_of_gt (hstart.trans hab)
  rw [polarization_mul_euler, polarization_X_euler,
    ite_eq_right hne, zero_mul, zero_add]

theorem simpleRoot_coordinate_path_neither
    {r n : ℕ} (front : List (Fin (r + 1)))
    (start i a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hstart : start < a) (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: j :: tail) p) = 0 := by
  rw [simpleRoot_coordinate_mul_of_earlier a b start k hstart hab,
    simpleRoot_polarization_path_neither front i a b j tail
      hia hab hbj hfront hbefore htail hafter p hp, mul_zero]

theorem simpleRoot_coordinate_path_first
    {r n : ℕ} (front : List (Fin (r + 1)))
    (start i a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hstart : start < a) (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: a :: j :: tail) p) =
      -coordinateToggleBridge start k front i a b j tail p := by
  rw [simpleRoot_coordinate_mul_of_earlier a b start k hstart hab,
    simpleRoot_polarization_path_first front i a b j tail
      hia hab hbj hfront hbefore htail hafter p hp, mul_neg]
  rfl

theorem simpleRoot_coordinate_path_second
    {r n : ℕ} (front : List (Fin (r + 1)))
    (start i a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hstart : start < a) (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: b :: j :: tail) p) =
      coordinateToggleBridge start k front i a b j tail p := by
  rw [simpleRoot_coordinate_mul_of_earlier a b start k hstart hab,
    simpleRoot_polarization_path_second front i a b j tail
      hia hab hbj hfront hbefore htail hafter p hp]
  rfl

theorem simpleRoot_coordinate_path_both
    {r n : ℕ} (front : List (Fin (r + 1)))
    (start i a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hstart : start < a) (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n) (A B : ℝ)
    (hp : polarization r n a b p = 0)
    (ha : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        A • lowerPolarizationPath (j :: tail) p)
    (hb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        B • lowerPolarizationPath (j :: tail) p) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: a :: b :: j :: tail) p) =
      (A - B + 1) •
        coordinateToggleBridge start k front i a b j tail p := by
  rw [simpleRoot_coordinate_mul_of_earlier a b start k hstart hab,
    simpleRoot_polarization_path_both front i a b j tail
      hia hab hbj hfront hbefore htail hafter p A B hp ha hb]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_1,
    coordinateToggleBridge]
  ring

theorem simpleRoot_coordinate_path_four_states
    {r n : ℕ} (front : List (Fin (r + 1)))
    (start i a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hstart : start < a) (hia : i < a) (hab : a < b) (hbj : b < j)
    (hfront : (front ++ [i]).Pairwise (· < ·))
    (hbefore : ∀ z ∈ (front ++ [i]), z ≤ a)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n) (A B : ℝ)
    (hp : polarization r n a b p = 0)
    (ha : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        A • lowerPolarizationPath (j :: tail) p)
    (hb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        B • lowerPolarizationPath (j :: tail) p) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: j :: tail) p) = 0 ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: a :: j :: tail) p) =
      -coordinateToggleBridge start k front i a b j tail p ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: b :: j :: tail) p) =
      coordinateToggleBridge start k front i a b j tail p ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath (front ++ i :: a :: b :: j :: tail) p) =
      (A - B + 1) •
        coordinateToggleBridge start k front i a b j tail p := by
  exact ⟨
    simpleRoot_coordinate_path_neither front start i a b j k tail
      hstart hia hab hbj hfront hbefore htail hafter p hp,
    simpleRoot_coordinate_path_first front start i a b j k tail
      hstart hia hab hbj hfront hbefore htail hafter p hp,
    simpleRoot_coordinate_path_second front start i a b j k tail
      hstart hia hab hbj hfront hbefore htail hafter p hp,
    simpleRoot_coordinate_path_both front start i a b j k tail
      hstart hia hab hbj hfront hbefore htail hafter p A B hp ha hb⟩

private def coordinateToggleBridgeNoFront {r n : ℕ}
    (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    PolynomialSpace r n :=
  MvPolynomial.X (variableIndex a k) *
    polarization r n j b (lowerPolarizationPath (j :: tail) p)

theorem simpleRoot_coordinate_path_neither_noFront
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex j k) *
          lowerPolarizationPath (j :: tail) p) = 0 := by
  rw [polarization_mul_euler, polarization_X_euler,
    ite_eq_right (ne_of_lt hbj),
    simpleRoot_suffix_highest a b j hab tail htail hafter p hp]
  simp only [zero_mul, mul_zero, add_zero]

theorem simpleRoot_coordinate_path_first_noFront
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath (a :: j :: tail) p) =
      -coordinateToggleBridgeNoFront a b j k tail p := by
  exact simpleRoot_coordinate_first_only a b j k hab hbj
    (lowerPolarizationPath (j :: tail) p)
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp)

theorem simpleRoot_coordinate_path_second_noFront
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n)
    (hp : polarization r n a b p = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex b k) *
          lowerPolarizationPath (b :: j :: tail) p) =
      coordinateToggleBridgeNoFront a b j k tail p := by
  exact simpleRoot_coordinate_second_only a b j k hab hbj
    (lowerPolarizationPath (j :: tail) p)
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp)

theorem simpleRoot_coordinate_path_both_noFront
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n) (A B : ℝ)
    (hp : polarization r n a b p = 0)
    (ha : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        A • lowerPolarizationPath (j :: tail) p)
    (hb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        B • lowerPolarizationPath (j :: tail) p) :
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath (a :: b :: j :: tail) p) =
      (A - B + 1) • coordinateToggleBridgeNoFront a b j k tail p := by
  exact simpleRoot_coordinate_both a b j k hab hbj
    (lowerPolarizationPath (j :: tail) p) A B
    (simpleRoot_suffix_highest a b j hab tail htail hafter p hp) ha hb

theorem simpleRoot_coordinate_path_four_states_noFront
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (p : PolynomialSpace r n) (A B : ℝ)
    (hp : polarization r n a b p = 0)
    (ha : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        A • lowerPolarizationPath (j :: tail) p)
    (hb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        B • lowerPolarizationPath (j :: tail) p) :
    polarization r n a b
        (MvPolynomial.X (variableIndex j k) *
          lowerPolarizationPath (j :: tail) p) = 0 ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath (a :: j :: tail) p) =
      -coordinateToggleBridgeNoFront a b j k tail p ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex b k) *
          lowerPolarizationPath (b :: j :: tail) p) =
      coordinateToggleBridgeNoFront a b j k tail p ∧
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath (a :: b :: j :: tail) p) =
      (A - B + 1) • coordinateToggleBridgeNoFront a b j k tail p := by
  exact ⟨
    simpleRoot_coordinate_path_neither_noFront a b j k tail
      hab hbj htail hafter p hp,
    simpleRoot_coordinate_path_first_noFront a b j k tail
      hab hbj htail hafter p hp,
    simpleRoot_coordinate_path_second_noFront a b j k tail
      hab hbj htail hafter p hp,
    simpleRoot_coordinate_path_both_noFront a b j k tail
      hab hbj htail hafter p A B hp ha hb⟩

end ArbitraryRowMickelssonPathToggleCoordinate

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonFourStatePathExtraction

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonSimpleRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFourStateSubsetSorting
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathToggleCoordinate

theorem rowEuler_lowerPolarizationPath_suffix_of_ne
    {r n : ℕ} (a target : Fin (r + 1))
    (rows : List (Fin (r + 1))) (p : PolynomialSpace r n)
    (c : ℝ)
    (hp : rowEuler r n a p = c • p)
    (hatarget : a ≠ target)
    (hastart : a ≠ rows.headD target) :
    rowEuler r n a (lowerPolarizationPath (rows ++ [target]) p) =
      c • lowerPolarizationPath (rows ++ [target]) p := by
  rw [rowEuler_lowerPolarizationPath_append_singleton
    a target rows p c hp]
  have hastart' : a ≠ rows.head?.getD target := by
    simpa only [ne_eq, List.headD_eq_head?_getD] using hastart
  simp only [hatarget, ↓reduceIte, add_zero, List.headD_eq_head?_getD, hastart', sub_zero]

private def actualMickelssonPathTerm {r n : ℕ}
    (row : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (p : PolynomialSpace r n) : PolynomialSpace r n :=
  MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
    lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p

theorem polarizationPathStart_eq_sort_headD
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1))) :
    polarizationPathStart row S = (S.sort (· ≤ ·)).headD row :=
  (sort_headD_eq_polarizationPathStart row S).symm

private theorem arbitraryRowMickelssonPathTerm_four_states_finish
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (T L U : Finset (Fin (r + 1)))
    (j : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hab : a < b) (hbj : b < j)
    (hsort0 : T.sort (· ≤ ·) = L.sort (· ≤ ·) ++ U.sort (· ≤ ·))
    (hsorta : (insert a T).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ a :: U.sort (· ≤ ·))
    (hsortb : (insert b T).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ b :: U.sort (· ≤ ·))
    (hsortab : (insert a (insert b T)).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ a :: b :: U.sort (· ≤ ·))
    (hlo : (L.sort (· ≤ ·)).Pairwise (· < ·))
    (hlo_bound : ∀ i ∈ L.sort (· ≤ ·), i < a)
    (hsplit : U.sort (· ≤ ·) ++ [row] = j :: tail)
    (hhead : (U.sort (· ≤ ·)).headD row = j)
    (htail : (j :: tail).Pairwise (· < ·))
    (hafter : ∀ z ∈ (j :: tail), b ≤ z)
    (hqa : rowEuler r n a (lowerPolarizationPath (j :: tail) p) =
      (lam a : ℝ) • lowerPolarizationPath (j :: tail) p)
    (hqb : rowEuler r n b (lowerPolarizationPath (j :: tail) p) =
      (lam b : ℝ) • lowerPolarizationPath (j :: tail) p)
    (hhighest : polarization r n a b p = 0)
    (hcast : (lam a : ℝ) - (lam b : ℝ) + 1 =
      (((lam a - lam b : ℕ) : ℝ) + 1)) :
    ∃ z : PolynomialSpace r n,
      polarization r n a b (actualMickelssonPathTerm row k T p) = 0 ∧
      polarization r n a b
          (actualMickelssonPathTerm row k (insert a T) p) = -z ∧
      polarization r n a b
          (actualMickelssonPathTerm row k (insert b T) p) = z ∧
      polarization r n a b
          (actualMickelssonPathTerm row k (insert a (insert b T)) p) =
        (((lam a - lam b : ℕ) : ℝ) + 1) • z := by
  classical
  by_cases hLempty : L.sort (· ≤ ·) = []
  · have hstart0 : polarizationPathStart row T = j := by
      rw [polarizationPathStart_eq_sort_headD, hsort0,
        hLempty, List.nil_append]
      exact hhead
    have hstarta : polarizationPathStart row (insert a T) = a := by
      rw [polarizationPathStart_eq_sort_headD, hsorta, hLempty]
      simp only [List.nil_append, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some]
    have hstartb : polarizationPathStart row (insert b T) = b := by
      rw [polarizationPathStart_eq_sort_headD, hsortb, hLempty]
      simp only [List.nil_append, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some]
    have hstartab :
        polarizationPathStart row (insert a (insert b T)) = a := by
      rw [polarizationPathStart_eq_sort_headD, hsortab, hLempty]
      simp only [List.nil_append, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some]
    refine ⟨coordinateToggleBridgeNoFront a b j k tail p, ?_⟩
    have hstates := simpleRoot_coordinate_path_four_states_noFront
      a b j k tail hab hbj htail hafter p (lam a) (lam b)
      hhighest hqa hqb
    have hp0 : T.sort (· ≤ ·) ++ [row] = j :: tail := by
      rw [hsort0, hLempty, List.nil_append]
      exact hsplit
    have hpa : (insert a T).sort (· ≤ ·) ++ [row] = a :: j :: tail := by
      rw [hsorta, hLempty, List.nil_append]
      simpa only [List.cons_append, List.cons.injEq, true_and] using
        congrArg (fun q : List (Fin (r + 1)) => a :: q) hsplit
    have hpb : (insert b T).sort (· ≤ ·) ++ [row] = b :: j :: tail := by
      rw [hsortb, hLempty, List.nil_append]
      simpa only [List.cons_append, List.cons.injEq, true_and] using
        congrArg (fun q : List (Fin (r + 1)) => b :: q) hsplit
    have hpab : (insert a (insert b T)).sort (· ≤ ·) ++ [row] =
        a :: b :: j :: tail := by
      rw [hsortab, hLempty, List.nil_append]
      simpa only [List.cons_append, List.cons.injEq, true_and] using
        congrArg (fun q : List (Fin (r + 1)) => a :: b :: q) hsplit
    simpa only [actualMickelssonPathTerm, hstart0, hstarta, hstartb,
      hstartab, hp0, hpa, hpb, hpab, hcast] using hstates
  · let front := (L.sort (· ≤ ·)).dropLast
    let i := (L.sort (· ≤ ·)).getLast hLempty
    have hfrontsplit : front ++ [i] = L.sort (· ≤ ·) :=
      List.dropLast_concat_getLast hLempty
    have hiL : i ∈ L.sort (· ≤ ·) := by
      rw [← hfrontsplit]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, or_true]
    have hia : i < a := hlo_bound i hiL
    have hfrontpair : (front ++ [i]).Pairwise (· < ·) := by
      rw [hfrontsplit]
      exact hlo
    have hbefore : ∀ z ∈ (front ++ [i]), z ≤ a := by
      intro z hz
      exact (hlo_bound z (by rwa [← hfrontsplit])).le
    let start := (L.sort (· ≤ ·)).headD row
    have hstartmem : start ∈ L.sort (· ≤ ·) := by
      cases hlist : L.sort (· ≤ ·) with
      | nil => exact False.elim (hLempty hlist)
      | cons z zs =>
          simp only [List.headD_eq_head?_getD, hlist, List.head?_cons,
            Option.getD_some, List.mem_cons, true_or, start]
    have hstart : start < a := hlo_bound start hstartmem
    have hstart0 : polarizationPathStart row T = start := by
      rw [polarizationPathStart_eq_sort_headD, hsort0]
      cases hlist : L.sort (· ≤ ·) with
      | nil => exact False.elim (hLempty hlist)
      | cons z zs =>
          simp only [List.cons_append, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some, hlist, start]
    have hstarta : polarizationPathStart row (insert a T) = start := by
      rw [polarizationPathStart_eq_sort_headD, hsorta]
      cases hlist : L.sort (· ≤ ·) with
      | nil => exact False.elim (hLempty hlist)
      | cons z zs =>
          simp only [List.cons_append, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some, hlist, start]
    have hstartb : polarizationPathStart row (insert b T) = start := by
      rw [polarizationPathStart_eq_sort_headD, hsortb]
      cases hlist : L.sort (· ≤ ·) with
      | nil => exact False.elim (hLempty hlist)
      | cons z zs =>
          simp only [List.cons_append, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some, hlist, start]
    have hstartab :
        polarizationPathStart row (insert a (insert b T)) = start := by
      rw [polarizationPathStart_eq_sort_headD, hsortab]
      cases hlist : L.sort (· ≤ ·) with
      | nil => exact False.elim (hLempty hlist)
      | cons z zs =>
          simp only [List.cons_append, List.headD_eq_head?_getD,
            List.head?_cons, Option.getD_some, hlist, start]
    refine ⟨coordinateToggleBridge start k front i a b j tail p, ?_⟩
    have hstates := simpleRoot_coordinate_path_four_states
      front start i a b j k tail hstart hia hab hbj
      hfrontpair hbefore htail hafter p (lam a) (lam b)
      hhighest hqa hqb
    have hp0 : T.sort (· ≤ ·) ++ [row] = front ++ i :: j :: tail := by
      rw [hsort0, ← hfrontsplit]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq, List.cons.injEq, true_and] using
          congrArg (fun q : List (Fin (r + 1)) => front ++ i :: q) hsplit
    have hpa : (insert a T).sort (· ≤ ·) ++ [row] =
        front ++ i :: a :: j :: tail := by
      rw [hsorta, ← hfrontsplit]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq, List.cons.injEq, true_and] using
          congrArg (fun q : List (Fin (r + 1)) => front ++ i :: a :: q) hsplit
    have hpb : (insert b T).sort (· ≤ ·) ++ [row] =
        front ++ i :: b :: j :: tail := by
      rw [hsortb, ← hfrontsplit]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq, List.cons.injEq, true_and] using
          congrArg (fun q : List (Fin (r + 1)) => front ++ i :: b :: q) hsplit
    have hpab : (insert a (insert b T)).sort (· ≤ ·) ++ [row] =
        front ++ i :: a :: b :: j :: tail := by
      rw [hsortab, ← hfrontsplit]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq, List.cons.injEq, true_and] using
          congrArg (fun q : List (Fin (r + 1)) =>
            front ++ i :: a :: b :: q) hsplit
    simpa only [actualMickelssonPathTerm, hstart0, hstarta, hstartb,
      hstartab, hp0, hpa, hpb, hpab, hcast] using hstates

theorem arbitraryRowMickelssonPathTerm_four_states
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (habadj : a.val + 1 = b.val) (hbrow : b < row)
    (hdom : lam b ≤ lam a)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hhighest : polarization r n a b p = 0)
    (T : Finset (Fin (r + 1)))
    (hT : T ∈ (((precedingRows row).erase a).erase b).powerset) :
    ∃ z : PolynomialSpace r n,
      polarization r n a b
          (actualMickelssonPathTerm row k T p) = 0 ∧
      polarization r n a b
          (actualMickelssonPathTerm row k (insert a T) p) = -z ∧
      polarization r n a b
          (actualMickelssonPathTerm row k (insert b T) p) = z ∧
      polarization r n a b
          (actualMickelssonPathTerm row k
            (insert a (insert b T)) p) =
        (((lam a - lam b : ℕ) : ℝ) + 1) • z := by
  classical
  have hab : a < b := by
    change a.val < b.val
    omega
  have harow : a < row := hab.trans hbrow
  have hsub0 : T ⊆ ((precedingRows row).erase a).erase b :=
    Finset.mem_powerset.mp hT
  have hsub : T ⊆ precedingRows row := by
    intro i hi
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp (hsub0 hi)).2).2
  have haT : a ∉ T := by
    intro ha
    have h := hsub0 ha
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, mem_precedingRows, false_and,
      and_false] at h
  have hbT : b ∉ T := by
    intro hb
    have h := hsub0 hb
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, mem_precedingRows, false_and] at h
  let L : Finset (Fin (r + 1)) := T.filter (fun i => i < a)
  let U : Finset (Fin (r + 1)) := T.filter (fun i => b < i)
  have hsort0 : T.sort (· ≤ ·) = L.sort (· ≤ ·) ++ U.sort (· ≤ ·) :=
    sorted_subset_neither a b habadj T haT hbT
  have hsorta : (insert a T).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ a :: U.sort (· ≤ ·) :=
    sorted_subset_first a b habadj T haT hbT
  have hsortb : (insert b T).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ b :: U.sort (· ≤ ·) :=
    sorted_subset_second a b habadj T haT hbT
  have hsortab : (insert a (insert b T)).sort (· ≤ ·) =
      L.sort (· ≤ ·) ++ a :: b :: U.sort (· ≤ ·) :=
    sorted_subset_both a b habadj T haT hbT
  have hlo : (L.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort L).pairwise
  have hlo_bound : ∀ i ∈ L.sort (· ≤ ·), i < a := by
    intro i hi
    have hiL : i ∈ L := (Finset.mem_sort (· ≤ ·)).mp hi
    exact (Finset.mem_filter.mp hiL).2
  have hup : ((U.sort (· ≤ ·)) ++ [row]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨(Finset.sortedLT_sort U).pairwise, by simp only [List.pairwise_cons, List.not_mem_nil,
                                                    IsEmpty.forall_iff, implies_true,
                                                    List.Pairwise.nil, and_self], ?_⟩
    intro i hi j hj
    have hjrow : j = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
    subst j
    have hiU : i ∈ U := (Finset.mem_sort (· ≤ ·)).mp hi
    exact (mem_precedingRows i row).mp
      (hsub (Finset.mem_filter.mp hiU).1)
  have hup_bound : ∀ i ∈ U.sort (· ≤ ·) ++ [row], b < i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have hiU : i ∈ U := (Finset.mem_sort (· ≤ ·)).mp hi
      exact (Finset.mem_filter.mp hiU).2
    · have hirow : i = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
      simpa only [hirow, gt_iff_lt] using hbrow
  obtain ⟨j, tail, hsplit⟩ :
      ∃ j : Fin (r + 1), ∃ tail : List (Fin (r + 1)),
        U.sort (· ≤ ·) ++ [row] = j :: tail := by
    cases hUsort : U.sort (· ≤ ·) with
    | nil => exact ⟨row, [], by simp only [List.nil_append]⟩
    | cons j tail => exact ⟨j, tail ++ [row], by simp only [List.cons_append]⟩
  have hbj : b < j := by
    apply hup_bound j
    rw [hsplit]
    simp only [List.mem_cons, true_or]
  have htail : (j :: tail).Pairwise (· < ·) := by
    rw [← hsplit]
    exact hup
  have hafter : ∀ z ∈ (j :: tail), b ≤ z := by
    intro z hz
    apply le_of_lt
    apply hup_bound z
    simpa only [hsplit, List.mem_cons] using hz
  have hhead : (U.sort (· ≤ ·)).headD row = j := by
    have hhead' := congrArg
      (fun l : List (Fin (r + 1)) => l.headD row) hsplit
    cases hUsort : U.sort (· ≤ ·) with
    | nil => simpa only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, hUsort,
               List.nil_append, List.head?_cons, Option.getD_some] using hhead'
    | cons i rest => simpa only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      hUsort, List.cons_append] using
                       hhead'
  have hqa : rowEuler r n a
      (lowerPolarizationPath (j :: tail) p) =
        (lam a : ℝ) • lowerPolarizationPath (j :: tail) p := by
    rw [← hsplit]
    apply rowEuler_lowerPolarizationPath_suffix_of_ne
      a row (U.sort (· ≤ ·)) p (lam a) (hweight a)
    · exact ne_of_lt harow
    · rw [hhead]
      exact ne_of_lt (hab.trans hbj)
  have hqb : rowEuler r n b
      (lowerPolarizationPath (j :: tail) p) =
        (lam b : ℝ) • lowerPolarizationPath (j :: tail) p := by
    rw [← hsplit]
    apply rowEuler_lowerPolarizationPath_suffix_of_ne
      b row (U.sort (· ≤ ·)) p (lam b) (hweight b)
    · exact ne_of_lt hbrow
    · rw [hhead]
      exact ne_of_lt hbj
  have hcast :
      ((lam a : ℝ) - (lam b : ℝ) + 1) =
        (((lam a - lam b : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_sub hdom]
  exact arbitraryRowMickelssonPathTerm_four_states_finish
    lam row a b k p T L U j tail hab hbj hsort0 hsorta hsortb hsortab
    hlo hlo_bound hsplit hhead htail hafter hqa hqb hhighest hcast

end ArbitraryRowMickelssonFourStatePathExtraction

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonLastRoot

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence

theorem precedingRows_succ {r : ℕ} (a : Fin r) :
    precedingRows a.succ = insert a.castSucc (precedingRows a.castSucc) := by
  ext i
  simp only [mem_precedingRows, Finset.mem_insert]
  constructor
  · intro hi
    by_cases h : i = a.castSucc
    · exact Or.inl h
    · right
      change i.val < a.val
      have hiv : i.val < a.val + 1 := hi
      have hne : i.val ≠ a.val := fun heq =>
        h (Fin.ext heq)
      omega
  · rintro (rfl | hi)
    · change a.val < a.val + 1
      omega
    · change i.val < a.val + 1
      have hiv : i.val < a.val := hi
      omega

@[simp] theorem shiftedRowGap_succ_castSucc {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin r) :
    shiftedRowGap lam a.succ a.castSucc =
      ((lam a.castSucc - lam a.succ : ℕ) : ℝ) := by
  unfold shiftedRowGap
  have h : a.succ.val - a.castSucc.val - 1 = 0 := by
    change (a.val + 1) - a.val - 1 = 0
    omega
  simp only [Fin.val_succ, Fin.val_castSucc, add_tsub_cancel_left, tsub_self, CharP.cast_eq_zero,
    add_zero]

theorem sort_insert_last_of_preceding {r : ℕ}
    (a : Fin r) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    (insert a.castSucc S).sort (· ≤ ·) =
      S.sort (· ≤ ·) ++ [a.castSucc] := by
  classical
  have hnot : a.castSucc ∉ S := by
    intro ha
    exact (not_lt_of_ge (le_refl a.castSucc))
      ((mem_precedingRows a.castSucc a.castSucc).mp (hS ha))
  let l : List (Fin (r + 1)) := S.sort (· ≤ ·) ++ [a.castSucc]
  have hnodup : l.Nodup := by
    exact (List.nodup_append.mpr
      ⟨Finset.sort_nodup S (· ≤ ·), by simp only [List.nodup_cons, List.not_mem_nil,
                                         not_false_eq_true, List.nodup_nil, and_self],
        by
          intro i hi j hj heq
          have hi' : i ∈ S := (Finset.mem_sort (· ≤ ·)).mp hi
          have hj' : j = a.castSucc := by simpa only [List.mem_cons, List.not_mem_nil,
                                            or_false] using hj
          exact hnot ((heq.trans hj') ▸ hi')⟩)
  have hpair : l.Pairwise (· ≤ ·) := by
    dsimp [l]
    apply List.pairwise_append.mpr
    refine ⟨Finset.pairwise_sort S (· ≤ ·), by simp only [List.pairwise_cons, List.not_mem_nil,
                                                 IsEmpty.forall_iff, implies_true,
                                                 List.Pairwise.nil, and_self], ?_⟩
    intro i hi j hj
    have hj' : j = a.castSucc := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
    subst j
    exact le_of_lt ((mem_precedingRows i a.castSucc).mp
      (hS ((Finset.mem_sort (· ≤ ·)).mp hi)))
  have hfin : l.toFinset = insert a.castSucc S := by
    ext i
    simp only [List.toFinset_append, Finset.sort_toFinset, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.union_singleton, Finset.mem_insert, l]
  have hsort := (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr hpair
  simpa only [hfin] using hsort

theorem polarizationPathStart_insert_last {r : ℕ}
    (a : Fin r) (S : Finset (Fin (r + 1)))
    (hS : S.Nonempty)
    (hsub : S ⊆ precedingRows a.castSucc) :
    polarizationPathStart a.succ (insert a.castSucc S) =
      polarizationPathStart a.succ S := by
  unfold polarizationPathStart
  rw [dite_eq_left (S.insert_nonempty a.castSucc), dite_eq_left hS,
    Finset.min'_insert a.castSucc S hS]
  apply min_eq_right
  exact le_of_lt ((mem_precedingRows (S.min' hS) a.castSucc).mp
    (hsub (Finset.min'_mem S hS)))

theorem polarization_lastRoot_lowerPath_without
    {r n : ℕ} (a : Fin r)
    (L : List (Fin (r + 1)))
    (hL : ∀ i ∈ L, i < a.castSucc) (hne : L ≠ [])
    (p : PolynomialSpace r n)
    (hp : polarization r n a.castSucc a.succ p = 0) :
    polarization r n a.castSucc a.succ
      (lowerPolarizationPath (L ++ [a.succ]) p) =
      lowerPolarizationPath (L ++ [a.castSucc]) p := by
  induction L generalizing p with
  | nil => exact (hne rfl).elim
  | cons i tail ih =>
      have hi : i < a.castSucc := hL i (by simp only [List.mem_cons, true_or])
      cases tail with
      | nil =>
          change
            polarization r n a.castSucc a.succ
              (polarization r n a.succ i p) =
              polarization r n a.castSucc i p
          rw [polarization_polarization_commutator
            a.castSucc a.succ a.succ i, hp, map_zero]
          have hia : i ≠ a.castSucc := ne_of_lt hi
          simp only [↓reduceIte, polarization_apply, zero_add, hia, sub_zero]
      | cons j rest =>
          have hj : j < a.castSucc := hL j (by simp only [List.mem_cons, true_or, or_true])
          have hsj : a.succ ≠ j := by
            exact ne_of_gt (lt_trans hj (by
              change a.val < a.val + 1
              omega))
          have hia : i ≠ a.castSucc := ne_of_lt hi
          change
            polarization r n a.castSucc a.succ
              (polarization r n j i
                (lowerPolarizationPath ((j :: rest) ++ [a.succ]) p)) =
              polarization r n j i
                (lowerPolarizationPath ((j :: rest) ++ [a.castSucc]) p)
          rw [polarization_polarization_commutator
            a.castSucc a.succ j i]
          simp only [ite_eq_right hsj, ite_eq_right hia, add_zero, sub_zero]
          rw [ih (by
            intro z hz
            exact hL z (by simp only [List.mem_cons, hz, or_true])) (by simp only [ne_eq,
              reduceCtorEq, not_false_eq_true]) p hp]

theorem polarization_lastRoot_lowerPath_with
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a : Fin r)
    (L : List (Fin (r + 1)))
    (hL : ∀ i ∈ L, i < a.castSucc)
    (hdom : lam a.succ ≤ lam a.castSucc)
    (p : PolynomialSpace r n)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hp : polarization r n a.castSucc a.succ p = 0) :
    polarization r n a.castSucc a.succ
      (lowerPolarizationPath (L ++ [a.castSucc, a.succ]) p) =
      ((lam a.castSucc - lam a.succ : ℕ) : ℝ) •
        lowerPolarizationPath (L ++ [a.castSucc]) p := by
  induction L generalizing p with
  | nil =>
      change
        polarization r n a.castSucc a.succ
          (polarization r n a.succ a.castSucc p) =
          ((lam a.castSucc - lam a.succ : ℕ) : ℝ) • p
      rw [polarization_polarization_commutator
        a.castSucc a.succ a.succ a.castSucc, hp, map_zero]
      simp only [ite_true, zero_add, polarization_self]
      rw [hweight a.castSucc, hweight a.succ]
      simp only [MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_sub hdom, MvPolynomial.C_sub]
      ring
  | cons i tail ih =>
      have hi : i < a.castSucc := hL i (by simp only [List.mem_cons, true_or])
      have hia : i ≠ a.castSucc := ne_of_lt hi
      cases tail with
      | nil =>
          change
            polarization r n a.castSucc a.succ
              (polarization r n a.castSucc i
                (polarization r n a.succ a.castSucc p)) =
              ((lam a.castSucc - lam a.succ : ℕ) : ℝ) •
                polarization r n a.castSucc i p
          rw [polarization_polarization_commutator
            a.castSucc a.succ a.castSucc i]
          have hs : a.succ ≠ a.castSucc := by
            exact ne_of_gt (by
              change a.val < a.val + 1
              omega)
          simp only [ite_eq_right hs, ite_eq_right hia, add_zero, sub_zero]
          rw [polarization_polarization_commutator
            a.castSucc a.succ a.succ a.castSucc, hp, map_zero]
          simp only [ite_true, zero_add, polarization_self]
          rw [hweight a.castSucc, hweight a.succ,
            map_sub, map_smul, map_smul]
          simp only [polarization_apply, MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_sub hdom,
            MvPolynomial.C_sub]
          ring
      | cons j rest =>
          have hj : j < a.castSucc := hL j (by simp only [List.mem_cons, true_or, or_true])
          have hsj : a.succ ≠ j := by
            exact ne_of_gt (lt_trans hj (by
              change a.val < a.val + 1
              omega))
          change
            polarization r n a.castSucc a.succ
              (polarization r n j i
                (lowerPolarizationPath
                  ((j :: rest) ++ [a.castSucc, a.succ]) p)) =
              ((lam a.castSucc - lam a.succ : ℕ) : ℝ) •
                polarization r n j i
                  (lowerPolarizationPath
                    ((j :: rest) ++ [a.castSucc]) p)
          rw [polarization_polarization_commutator
            a.castSucc a.succ j i]
          simp only [ite_eq_right hsj, ite_eq_right hia, add_zero, sub_zero]
          rw [ih (by
            intro z hz
            exact hL z (by simp only [List.mem_cons, hz, or_true])) p hweight hp,
            map_smul]

theorem polarization_lastRoot_pathTerm_without
    {r n : ℕ} (a : Fin r) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows a.castSucc)
    (p : PolynomialSpace r n)
    (hp : polarization r n a.castSucc a.succ p = 0) :
    polarization r n a.castSucc a.succ
      (MvPolynomial.X (variableIndex (polarizationPathStart a.succ S) k) *
        lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [a.succ]) p) =
      MvPolynomial.X
          (variableIndex
            (polarizationPathStart a.succ (insert a.castSucc S)) k) *
        lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [a.castSucc]) p := by
  classical
  by_cases hS : S.Nonempty
  · have hsortne : S.sort (· ≤ ·) ≠ [] := by
      have hlength : 0 < (S.sort (· ≤ ·)).length := by
        simpa only [Finset.length_sort, Finset.card_pos] using (Finset.card_pos.mpr hS)
      intro h
      simp only [h, List.length_nil, lt_self_iff_false] at hlength
    have hstart : polarizationPathStart a.succ S < a.castSucc := by
      unfold polarizationPathStart
      rw [dite_eq_left hS]
      exact (mem_precedingRows (S.min' hS) a.castSucc).mp
        (hsub (Finset.min'_mem S hS))
    have hne : a.succ ≠ polarizationPathStart a.succ S := by
      exact ne_of_gt (lt_trans hstart (by
        change a.val < a.val + 1
        omega))
    rw [polarization_mul_euler, polarization_X_euler, ite_eq_right hne,
      zero_mul, zero_add,
      polarization_lastRoot_lowerPath_without a (S.sort (· ≤ ·))
        (by
          intro i hi
          exact (mem_precedingRows i a.castSucc).mp
            (hsub ((Finset.mem_sort (· ≤ ·)).mp hi)))
        hsortne p hp,
      polarizationPathStart_insert_last a S hS hsub]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [Finset.sort_empty, List.nil_append,
      lowerPolarizationPath, LinearMap.id_apply,
      polarizationPathStart_empty, Finset.insert_empty]
    rw [show polarizationPathStart a.succ {a.castSucc} = a.castSucc by
      simp only [polarizationPathStart, Finset.singleton_nonempty, ↓reduceDIte,
        Finset.min'_singleton]]
    change
      polarization r n a.castSucc a.succ
        (MvPolynomial.X (variableIndex a.succ k) * p) =
        MvPolynomial.X (variableIndex a.castSucc k) * p
    rw [polarization_mul_euler, polarization_X_euler, hp]
    simp only [↓reduceIte, mul_zero, add_zero]

theorem polarization_lastRoot_pathTerm_with
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin r) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows a.castSucc)
    (hdom : lam a.succ ≤ lam a.castSucc)
    (p : PolynomialSpace r n)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hp : polarization r n a.castSucc a.succ p = 0) :
    polarization r n a.castSucc a.succ
      (MvPolynomial.X
          (variableIndex
            (polarizationPathStart a.succ (insert a.castSucc S)) k) *
        lowerPolarizationPath
          (((insert a.castSucc S).sort (· ≤ ·)) ++ [a.succ]) p) =
      ((lam a.castSucc - lam a.succ : ℕ) : ℝ) •
        (MvPolynomial.X
          (variableIndex
            (polarizationPathStart a.succ (insert a.castSucc S)) k) *
          lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [a.castSucc]) p) := by
  classical
  have hstart :
      polarizationPathStart a.succ (insert a.castSucc S) ≤ a.castSucc := by
    unfold polarizationPathStart
    rw [dite_eq_left (Finset.insert_nonempty a.castSucc S)]
    exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hne :
      a.succ ≠ polarizationPathStart a.succ (insert a.castSucc S) := by
    exact ne_of_gt (lt_of_le_of_lt hstart (by
      change a.val < a.val + 1
      omega))
  rw [polarization_mul_euler, polarization_X_euler, ite_eq_right hne,
    zero_mul, zero_add, sort_insert_last_of_preceding a S hsub]
  rw [List.append_assoc]
  change
    MvPolynomial.X
        (variableIndex
          (polarizationPathStart a.succ (insert a.castSucc S)) k) *
      polarization r n a.castSucc a.succ
        (lowerPolarizationPath
          ((S.sort (· ≤ ·)) ++ [a.castSucc, a.succ]) p) = _
  rw [polarization_lastRoot_lowerPath_with lam a (S.sort (· ≤ ·))
      (by
        intro i hi
        exact (mem_precedingRows i a.castSucc).mp
          (hsub ((Finset.mem_sort (· ≤ ·)).mp hi)))
      hdom p hweight hp]
  simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
  ring

theorem polarization_lastRoot_paired_terms
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin r) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows a.castSucc)
    (hdom : lam a.succ ≤ lam a.castSucc)
    (p : PolynomialSpace r n)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hp : polarization r n a.castSucc a.succ p = 0) :
    polarization r n a.castSucc a.succ
        (polarizationPathCoefficient lam a.succ S •
          (MvPolynomial.X
            (variableIndex (polarizationPathStart a.succ S) k) *
            lowerPolarizationPath
              ((S.sort (· ≤ ·)) ++ [a.succ]) p)) +
      polarization r n a.castSucc a.succ
        (polarizationPathCoefficient lam a.succ (insert a.castSucc S) •
          (MvPolynomial.X
            (variableIndex
              (polarizationPathStart a.succ (insert a.castSucc S)) k) *
            lowerPolarizationPath
              (((insert a.castSucc S).sort (· ≤ ·)) ++ [a.succ]) p)) = 0 := by
  have haS : a.castSucc ∉ S := by
    intro ha
    exact (not_lt_of_ge (le_refl a.castSucc))
      ((mem_precedingRows a.castSucc a.castSucc).mp (hsub ha))
  rw [map_smul, map_smul,
    polarization_lastRoot_pathTerm_without a k S hsub p hp,
    polarization_lastRoot_pathTerm_with lam a k S hsub hdom p hweight hp,
    polarizationPathCoefficient_insert lam a.succ a.castSucc S
      (by
        change a.val < a.val + 1
        omega) haS,
    shiftedRowGap_succ_castSucc lam a,
    smul_smul]
  simp only [neg_mul, neg_smul, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul, map_natCast]
  ring

theorem arbitraryRowAxialRaise_polarization_lastRoot
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin r) (k : Fin n)
    (hdom : lam a.succ ≤ lam a.castSucc)
    (p : PolynomialSpace r n)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hhighest : ∀ i j : Fin (r + 1), i < j →
      polarization r n i j p = 0) :
    polarization r n a.castSucc a.succ
      (arbitraryRowAxialRaise lam a.succ k p) = 0 := by
  classical
  have ha : a.castSucc ∉ precedingRows a.castSucc := by simp only [mem_precedingRows,
                                                          lt_self_iff_false, not_false_eq_true]
  have hp : polarization r n a.castSucc a.succ p = 0 :=
    hhighest a.castSucc a.succ (by
      change a.val < a.val + 1
      omega)
  rw [arbitraryRowAxialRaise_apply, precedingRows_succ,
    Finset.sum_powerset_insert ha, map_add, map_sum, map_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  exact polarization_lastRoot_paired_terms lam a k S
    (Finset.mem_powerset.mp hS) hdom p hweight hp

end ArbitraryRowMickelssonLastRoot

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowSimpleRootPathCancellation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonFourStatePathExtraction
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonLastRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence

theorem sum_powerset_pair {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (s : Finset α) (a b : α)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (f : Finset α → M) :
    (∑ t ∈ s.powerset, f t) =
      ∑ t ∈ ((s.erase a).erase b).powerset,
        (f t + f (insert b t) + f (insert a t) +
          f (insert a (insert b t))) := by
  classical
  let u : Finset α := (s.erase a).erase b
  have hau : a ∉ u := by
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, and_false, not_false_eq_true,
      u]
  have hbu : b ∉ u := by
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, u]
  have hdecomp : s = insert a (insert b u) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, u]
    grind
  conv_lhs => rw [hdecomp]
  change (∑ t ∈ (insert a (insert b u)).powerset, f t) =
    ∑ t ∈ u.powerset,
      (f t + f (insert b t) + f (insert a t) +
        f (insert a (insert b t)))
  rw [Finset.sum_powerset_insert (by simp only [Finset.mem_insert, hab, hau, or_self,
                                       not_false_eq_true])]
  rw [Finset.sum_powerset_insert hbu]
  rw [Finset.sum_powerset_insert hbu]
  simp_rw [Finset.sum_add_distrib]
  ac_rfl

theorem sum_powerset_eq_zero_of_pair_states
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (a b : α)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (f : Finset α → M)
    (hstates : ∀ t ∈ ((s.erase a).erase b).powerset,
      f t + f (insert b t) + f (insert a t) +
        f (insert a (insert b t)) = 0) :
    (∑ t ∈ s.powerset, f t) = 0 := by
  rw [sum_powerset_pair s a b ha hb hab f]
  exact Finset.sum_eq_zero hstates

private def arbitraryRowMickelssonPathTerm {r n : ℕ}
    (row : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) (p : PolynomialSpace r n) :
    PolynomialSpace r n :=
  MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
    lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p

theorem arbitraryRowAxialRaise_eq_sum_pathTerm
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam row k p =
      ∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          arbitraryRowMickelssonPathTerm row k S p := by
  rw [arbitraryRowAxialRaise_apply]
  rfl

theorem arbitraryRowAxialRaise_polarization_initial_simpleRoot_of_states
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (habadj : a.val + 1 = b.val) (hbrow : b < row)
    (hweight : lam b ≤ lam a) (hlow : lam row ≤ lam b)
    (hstates : ∀ T ∈ (((precedingRows row).erase a).erase b).powerset,
      ∃ z : PolynomialSpace r n,
        polarization r n a b
            (arbitraryRowMickelssonPathTerm row k T p) = 0 ∧
        polarization r n a b
            (arbitraryRowMickelssonPathTerm row k (insert a T) p) = -z ∧
        polarization r n a b
            (arbitraryRowMickelssonPathTerm row k (insert b T) p) = z ∧
        polarization r n a b
            (arbitraryRowMickelssonPathTerm row k
              (insert a (insert b T)) p) =
          (((lam a - lam b : ℕ) : ℝ) + 1) • z) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) = 0 := by
  classical
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have harow : a < row := by
    change a.val < row.val
    have hbrow' : b.val < row.val := hbrow
    omega
  have ha : a ∈ precedingRows row :=
    (mem_precedingRows a row).mpr harow
  have hb : b ∈ precedingRows row :=
    (mem_precedingRows b row).mpr hbrow
  rw [arbitraryRowAxialRaise_eq_sum_pathTerm, map_sum]
  simp_rw [map_smul]
  apply sum_powerset_eq_zero_of_pair_states
    (precedingRows row) a b ha hb hab
  intro T hT
  have hsub : T ⊆ ((precedingRows row).erase a).erase b :=
    Finset.mem_powerset.mp hT
  have haT : a ∉ T := by
    intro h
    have h' := hsub h
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, mem_precedingRows, false_and,
      and_false] at h'
  have hbT : b ∉ T := by
    intro h
    have h' := hsub h
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, mem_precedingRows, false_and] at h'
  obtain ⟨z, hzero, hfirst, hsecond, hboth⟩ := hstates T hT
  rw [hzero, hfirst, hsecond, hboth, smul_zero, zero_add]
  have hfirstcoef :
      polarizationPathCoefficient lam row (insert a T) =
        -shiftedRowGap lam row b *
          polarizationPathCoefficient lam row (insert a (insert b T)) := by
    rw [polarizationPathCoefficient_insert lam row b (insert a T)
      hbrow (by simp only [Finset.mem_insert, Ne.symm hab, hbT, or_self, not_false_eq_true])]
    rw [Finset.insert_comm b a]
  have hsecondcoef :
      polarizationPathCoefficient lam row (insert b T) =
        -shiftedRowGap lam row a *
          polarizationPathCoefficient lam row (insert a (insert b T)) :=
    polarizationPathCoefficient_insert lam row a (insert b T)
      harow (by simp only [Finset.mem_insert, hab, haT, or_self, not_false_eq_true])
  rw [hfirstcoef, hsecondcoef,
    ← shiftedRowGap_sub_adjacent lam row a b habadj hbrow hweight hlow]
  simp only [mul_smul, neg_smul]
  module

theorem arbitraryRowAxialRaise_polarization_of_initial_pathStates
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (hweight : ∀ a : Fin (r + 1),
      rowEuler r n a p = (lam a : ℝ) • p)
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b p = 0)
    (hstates : ∀ (a : Fin r) (_ : a.succ < row)
      (T : Finset (Fin (r + 1)))
      (_ : T ∈ (((precedingRows row).erase a.castSucc).erase a.succ).powerset),
      ∃ z : PolynomialSpace r n,
        polarization r n a.castSucc a.succ
            (arbitraryRowMickelssonPathTerm row k T p) = 0 ∧
        polarization r n a.castSucc a.succ
            (arbitraryRowMickelssonPathTerm row k (insert a.castSucc T) p) = -z ∧
        polarization r n a.castSucc a.succ
            (arbitraryRowMickelssonPathTerm row k (insert a.succ T) p) = z ∧
        polarization r n a.castSucc a.succ
            (arbitraryRowMickelssonPathTerm row k
              (insert a.castSucc (insert a.succ T)) p) =
          (((lam a.castSucc - lam a.succ : ℕ) : ℝ) + 1) • z)
    (a b : Fin (r + 1)) (hab : a < b) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) = 0 := by
  apply arbitraryRowAxialRaise_polarization_of_initial_simpleRoots
    lam row k p hhighest
  · intro c hc
    by_cases hbelow : c.succ < row
    · apply arbitraryRowAxialRaise_polarization_initial_simpleRoot_of_states
        lam row c.castSucc c.succ k p rfl hbelow
        (hdom (show c.castSucc ≤ c.succ by
          change c.val ≤ c.val + 1
          omega))
        (hdom (le_of_lt hbelow))
      exact hstates c hbelow
    · have heq : c.succ = row := by
        apply Fin.ext
        have hcast : c.val < row.val := by
          exact hc
        have hnot : ¬ c.val + 1 < row.val := by
          exact hbelow
        change c.val + 1 = row.val
        omega
      subst row
      exact arbitraryRowAxialRaise_polarization_lastRoot
        lam c k
        (hdom (show c.castSucc ≤ c.succ by
          change c.val ≤ c.val + 1
          omega))
        p hweight hhighest
  · exact hab

theorem arbitraryRowAxialRaise_polarization
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (hweight : ∀ c : Fin (r + 1),
      rowEuler r n c p = (lam c : ℝ) • p)
    (hhighest : ∀ c d : Fin (r + 1), c < d →
      polarization r n c d p = 0)
    (a b : Fin (r + 1)) (hab : a < b) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) = 0 := by
  apply arbitraryRowAxialRaise_polarization_of_initial_pathStates
    lam hdom row k p hweight hhighest
  · intro c hc T hT
    simpa only [↓existsAndEq, arbitraryRowMickelssonPathTerm, polarization_apply,
      Derivation.leibniz, smul_eq_mul,
      MvPolynomial.pderiv_X, true_and, actualMickelssonPathTerm] using
      arbitraryRowMickelssonPathTerm_four_states lam row c.castSucc c.succ k p rfl hc
        (hdom
          (show c.castSucc ≤ c.succ by
            change c.val ≤ c.val + 1
            omega))
        hweight
        (hhighest c.castSucc c.succ
          (by
            change c.val < c.val + 1
            omega))
        T hT
  · exact hab

end ArbitraryRowSimpleRootPathCancellation

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankInterlacingHighestWeightSeed

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisSchedule
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSimpleRootPathCancellation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

private def DominantAxialSchedule {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (rows : List (Fin (r + 1))) : Prop :=
  ∀ pref suff : List (Fin (r + 1)),
    rows = pref ++ suff → Antitone (arbitraryRowPathWeight lam pref)

theorem dominantAxialSchedule_tail
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (rows : List (Fin (r + 1)))
    (hlegal : DominantAxialSchedule lam (row :: rows)) :
    DominantAxialSchedule (raiseWeight lam row) rows := by
  intro pref suff heq
  have h := hlegal (row :: pref) suff (by
    simp only [List.cons_append]
    rw [← heq])
  simpa only [arbitraryRowPathWeight] using h

theorem dominantAxialSchedule_initial
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (rows : List (Fin (r + 1)))
    (hlegal : DominantAxialSchedule lam rows) : Antitone lam := by
  simpa only [arbitraryRowPathWeight] using hlegal [] rows rfl

theorem iteratedArbitraryRowAxialRaise_polarization_of_dominantSchedule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (k : Fin n) (rows : List (Fin (r + 1)))
    (hlegal : DominantAxialSchedule lam rows)
    (p : PolynomialSpace r n)
    (hweight : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (hhighest : ∀ i j : Fin (r + 1), i < j →
      polarization r n i j p = 0)
    (a b : Fin (r + 1)) (hab : a < b) :
    polarization r n a b
      (iteratedArbitraryRowAxialRaise lam k rows p) = 0 := by
  induction rows generalizing lam p with
  | nil =>
      simpa only [iteratedArbitraryRowAxialRaise, LinearMap.id_coe, id_eq, polarization_apply] using
        hhighest a b hab
  | cons row rows ih =>
      have hdom : Antitone lam :=
        dominantAxialSchedule_initial lam (row :: rows) hlegal
      have htail : DominantAxialSchedule (raiseWeight lam row) rows :=
        dominantAxialSchedule_tail lam row rows hlegal
      have hnextWeight : ∀ i : Fin (r + 1),
          rowEuler r n i (arbitraryRowAxialRaise lam row k p) =
            (raiseWeight lam row i : ℝ) •
              arbitraryRowAxialRaise lam row k p :=
        arbitraryRowAxialRaise_rowEuler lam row k p hweight
      have hnextHighest : ∀ i j : Fin (r + 1), i < j →
          polarization r n i j
            (arbitraryRowAxialRaise lam row k p) = 0 :=
        arbitraryRowAxialRaise_polarization lam hdom row k p
          hweight hhighest
      change polarization r n a b
        (iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
          (arbitraryRowAxialRaise lam row k p)) = 0
      exact ih (raiseWeight lam row) htail
        (arbitraryRowAxialRaise lam row k p)
        hnextWeight hnextHighest

theorem reverseInterlacingRowSchedule_dominantAxialSchedule
    {r : ℕ} {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) :
    DominantAxialSchedule (appendZeroWeight mu)
      (reverseInterlacingRowSchedule lam mu) := by
  intro pref suff heq
  have hcounts : ∀ row : Fin (r + 2),
      pref.count row ≤ interlacingGap lam mu row := by
    intro row
    have hfull := reverseInterlacingRowSchedule_count lam mu row
    rw [heq, List.count_append] at hfull
    omega
  rw [arbitraryRowPathWeight_eq_foldl]
  exact (foldl_interlaces_of_count_le_gap h pref hcounts).antitone_ambient

theorem reverseInterlacingPolynomialSeed_polarization
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu)
    (a b : Fin (r + 2)) (hab : a < b) :
    polarization (r + 1) (n + 1) a b
      (reverseInterlacingPolynomialSeed lam mu p) = 0 := by
  let q : HarmonicYoungSpace (n := n + 1)
      (appendZeroWeight mu) := terminalZeroSelectedBranchIsometry mu p
  have hq := (mem_harmonicYoungSubmodule (appendZeroWeight mu)
    (q : PolynomialSpace (r + 1) (n + 1))).mp q.property
  change polarization (r + 1) (n + 1) a b
    (iteratedArbitraryRowAxialRaise (appendZeroWeight mu) (Fin.last n)
      (reverseInterlacingRowSchedule lam mu)
      (q : PolynomialSpace (r + 1) (n + 1))) = 0
  exact iteratedArbitraryRowAxialRaise_polarization_of_dominantSchedule
    (appendZeroWeight mu) (Fin.last n)
    (reverseInterlacingRowSchedule lam mu)
    (reverseInterlacingRowSchedule_dominantAxialSchedule h)
    (q : PolynomialSpace (r + 1) (n + 1)) hq.2.1 hq.2.2.2 a b hab

end ArbitraryRankInterlacingHighestWeightSeed

end

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherYoungArbitraryRowAxialFiltrationIdeal

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

private def lowerAxisIdeal {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    Ideal (PolynomialSpace r n) :=
  Ideal.span {p : PolynomialSpace r n |
    ∃ i : Fin (r + 1), i < row ∧
      p = MvPolynomial.X (variableIndex i k)}

private def lowerAxisGramIdeal {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    Ideal (PolynomialSpace r n) :=
  youngGramRadialIdeal r n ⊔ lowerAxisIdeal k row

theorem axisPolynomial_mem_lowerAxisIdeal {r n : ℕ}
    (k : Fin n) (row i : Fin (r + 1)) (hi : i < row) :
    MvPolynomial.X (variableIndex i k) ∈ lowerAxisIdeal k row := by
  apply Ideal.subset_span
  exact ⟨i, hi, rfl⟩

theorem gram_le_lowerAxisGramIdeal {r n : ℕ}
    (k : Fin n) (row : Fin (r + 1)) :
    youngGramRadialIdeal r n ≤ lowerAxisGramIdeal k row :=
  le_sup_left

end HigherYoungArbitraryRowAxialFiltrationIdeal

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowAxialLeadingOrder

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal

theorem nonemptyMickelssonPathTerm_mem_lowerAxisIdeal
    {r n : ℕ} (row : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hS : S.Nonempty) (hsub : S ⊆ precedingRows row)
    (p : PolynomialSpace r n) :
    MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
        lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p ∈
      lowerAxisIdeal k row := by
  have hstart : polarizationPathStart row S < row :=
    polarizationPathStart_lt_of_nonempty row S hS hsub
  exact (lowerAxisIdeal k row).mul_mem_right
    (lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p)
    (axisPolynomial_mem_lowerAxisIdeal k row
      (polarizationPathStart row S) hstart)

theorem nonemptyMickelssonWeightedPathTerm_mem_lowerAxisIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hS : S.Nonempty) (hsub : S ⊆ precedingRows row)
    (p : PolynomialSpace r n) :
    polarizationPathCoefficient lam row S •
        (MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
          lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p) ∈
      lowerAxisIdeal k row := by
  rw [MvPolynomial.smul_eq_C_mul]
  exact (lowerAxisIdeal k row).mul_mem_left _
    (nonemptyMickelssonPathTerm_mem_lowerAxisIdeal row k S hS hsub p)

theorem emptyMickelssonPathTerm_eq_leading
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarizationPathCoefficient lam row ∅ •
        (MvPolynomial.X (variableIndex (polarizationPathStart row ∅) k) *
          lowerPolarizationPath
            (((∅ : Finset (Fin (r + 1))).sort (· ≤ ·)) ++ [row]) p) =
      MvPolynomial.C (arbitraryRowLeadingScalar lam row) *
        (MvPolynomial.X (variableIndex row k) * p) := by
  simp only [polarizationPathCoefficient, Finset.card_empty, pow_zero, Finset.sdiff_empty, one_mul,
    polarizationPathStart, Finset.not_nonempty_empty, ↓reduceDIte, Finset.sort_empty,
    List.nil_append, lowerPolarizationPath, LinearMap.id_coe, id_eq, MvPolynomial.smul_eq_C_mul,
    map_prod, arbitraryRowLeadingScalar]

theorem arbitraryRowAxialRaise_sub_leading_mul_mem_lowerAxisIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam row k p -
        MvPolynomial.C (arbitraryRowLeadingScalar lam row) *
          (MvPolynomial.X (variableIndex row k) * p) ∈
      lowerAxisIdeal k row := by
  classical
  rw [arbitraryRowAxialRaise_apply]
  have hempty : (∅ : Finset (Fin (r + 1))) ∈
      (precedingRows row).powerset := by simp only [Finset.mem_powerset, Finset.empty_subset]
  rw [← Finset.add_sum_erase _ _ hempty,
    emptyMickelssonPathTerm_eq_leading lam row k p]
  have hrest :
      (∑ S ∈ ((precedingRows row).powerset).erase ∅,
        polarizationPathCoefficient lam row S •
          (MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
            lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p)) ∈
        lowerAxisIdeal k row := by
    apply Ideal.sum_mem
    intro S hS
    have hnon : S.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hzero
      subst S
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_powerset,
        Finset.empty_subset, and_true] at hS
    have hsub : S ⊆ precedingRows row :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    exact nonemptyMickelssonWeightedPathTerm_mem_lowerAxisIdeal
      lam row k S hnon hsub p
  convert hrest using 1 ; ring

theorem arbitraryRowAxialRaise_sub_leading_mul_mem_lowerAxisGramIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam row k p -
        MvPolynomial.C (arbitraryRowLeadingScalar lam row) *
          (MvPolynomial.X (variableIndex row k) * p) ∈
      lowerAxisGramIdeal k row := by
  exact Ideal.mem_sup_right
    (arbitraryRowAxialRaise_sub_leading_mul_mem_lowerAxisIdeal
      lam row k p)

end ArbitraryRowAxialLeadingOrder

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankGelfandTsetlinTriangularNormalForm

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialLeadingOrder
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal

private def positiveLeadingAxialSchedule {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : List (Fin (r + 1)) → Prop
  | [] => True
  | row :: rows =>
      0 < arbitraryRowLeadingScalar lam row ∧
        positiveLeadingAxialSchedule (raiseWeight lam row) rows

theorem lowerAxisIdeal_mono
    {r n : ℕ} (k : Fin n)
    {i j : Fin (r + 1)} (hij : i ≤ j) :
    lowerAxisIdeal k i ≤ lowerAxisIdeal k j := by
  apply Ideal.span_le.mpr
  rintro q ⟨a, ha, rfl⟩
  exact axisPolynomial_mem_lowerAxisIdeal k j a (lt_of_lt_of_le ha hij)

theorem lowerAxisGramIdeal_mono
    {r n : ℕ} (k : Fin n)
    {i j : Fin (r + 1)} (hij : i ≤ j) :
    lowerAxisGramIdeal k i ≤ lowerAxisGramIdeal k j := by
  unfold lowerAxisGramIdeal
  exact sup_le_sup (le_refl _) (lowerAxisIdeal_mono k hij)

theorem C_mul_mem_ideal_iff
    {r n : ℕ} (I : Ideal (PolynomialSpace r n))
    {c : ℝ} (hc : c ≠ 0) (p : PolynomialSpace r n) :
    MvPolynomial.C c * p ∈ I ↔ p ∈ I := by
  constructor
  · intro hp
    have hinv := I.mul_mem_left (MvPolynomial.C c⁻¹) hp
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one,
      one_mul] at hinv
    exact hinv
  · exact I.mul_mem_left _

theorem arbitraryRowAxialRaise_not_mem_lowerAxisGramIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (hpositive : 0 < arbitraryRowLeadingScalar lam row)
    (hregular : ∀ q : PolynomialSpace r n,
      MvPolynomial.X (variableIndex row k) * q ∈
          lowerAxisGramIdeal k row ↔
        q ∈ lowerAxisGramIdeal k row)
    (p : PolynomialSpace r n)
    (hp : p ∉ lowerAxisGramIdeal k row) :
    arbitraryRowAxialRaise lam row k p ∉ lowerAxisGramIdeal k row := by
  intro hraise
  have hdifference :=
    arbitraryRowAxialRaise_sub_leading_mul_mem_lowerAxisGramIdeal
      lam row k p
  have hleading :
      MvPolynomial.C (arbitraryRowLeadingScalar lam row) *
          (MvPolynomial.X (variableIndex row k) * p) ∈
        lowerAxisGramIdeal k row := by
    have hsubtract :=
      (lowerAxisGramIdeal k row).sub_mem hraise hdifference
    convert hsubtract using 1 ; ring
  have haxis : MvPolynomial.X (variableIndex row k) * p ∈
      lowerAxisGramIdeal k row :=
    (C_mul_mem_ideal_iff (lowerAxisGramIdeal k row)
      hpositive.ne' _).mp hleading
  exact hp ((hregular p).mp haxis)

theorem iteratedArbitraryRowAxialRaise_not_mem_youngGramRadialIdeal_of_descending
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (k : Fin n) (rows : List (Fin (r + 1)))
    (bound : Fin (r + 1))
    (hdescending : rows.Pairwise (· ≥ ·))
    (hbounded : ∀ row ∈ rows, row ≤ bound)
    (hpositive : positiveLeadingAxialSchedule lam rows)
    (hregular : ∀ (row : Fin (r + 1)) (q : PolynomialSpace r n),
      MvPolynomial.X (variableIndex row k) * q ∈
          lowerAxisGramIdeal k row ↔
        q ∈ lowerAxisGramIdeal k row)
    (p : PolynomialSpace r n)
    (hp : p ∉ lowerAxisGramIdeal k bound) :
    iteratedArbitraryRowAxialRaise lam k rows p ∉
      youngGramRadialIdeal r n := by
  induction rows generalizing lam bound p with
  | nil =>
      change p ∉ youngGramRadialIdeal r n
      intro hgram
      exact hp (gram_le_lowerAxisGramIdeal k bound hgram)
  | cons row tail ih =>
      have hrowbound : row ≤ bound := hbounded row (by simp only [List.mem_cons, true_or])
      have hpstage : p ∉ lowerAxisGramIdeal k row := by
        intro hstage
        exact hp (lowerAxisGramIdeal_mono k hrowbound hstage)
      have hpair := List.pairwise_cons.mp hdescending
      have hstep :
          arbitraryRowAxialRaise lam row k p ∉
            lowerAxisGramIdeal k row :=
        arbitraryRowAxialRaise_not_mem_lowerAxisGramIdeal
          lam row k hpositive.1 (hregular row) p hpstage
      change iteratedArbitraryRowAxialRaise (raiseWeight lam row)
          k tail (arbitraryRowAxialRaise lam row k p) ∉
        youngGramRadialIdeal r n
      apply ih (lam := raiseWeight lam row) (bound := row)
        (p := arbitraryRowAxialRaise lam row k p)
      · exact hpair.2
      · intro j hj
        exact hpair.1 j hj
      · exact hpositive.2
      · exact hstep

end ArbitraryRankGelfandTsetlinTriangularNormalForm

end

section


open scoped BigOperators MonomialOrder

namespace ArbitraryRowMickelssonGramQuotient

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherYoungCoprimeLeadingBuchberger
open MetricCodes.Spherical.HigherYoungCoprimeLeadingRegularSequence

theorem rowAxis_not_mem_gramPair_weighted_leading_support_allRank
    {r n : ℕ} (hn : 2 * r < n)
    (row : Fin (r + 1)) (z : UpperGramPair r) :
    variableIndex row (Fin.last n) ∉
      ((weightedMonomialOrder (gramVariableNatWeight r (n + 1))).degree
        (gramPairPolynomial (n + 1) z)).support := by
  have hstable : 2 * r < n + 1 := by omega
  rw [gramPairPolynomial_weighted_degree hstable z,
    gramPivotExponent_support]
  simp only [gramPivotVariables, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · have hcoord :=
      ((variableIndex_eq_iff_harmonicLift
        row z.val.1 (Fin.last n) (gramPivot hstable z)).mp h).2
    have hval := congrArg Fin.val hcoord
    have hfirst := z.val.1.isLt
    have hsecond := z.val.2.isLt
    simp only [Fin.val_last, gramPivot_val] at hval
    omega
  · have hcoord :=
      ((variableIndex_eq_iff_harmonicLift
        row z.val.2 (Fin.last n) (gramPivot hstable z)).mp h).2
    have hval := congrArg Fin.val hcoord
    have hfirst := z.val.1.isLt
    have hsecond := z.val.2.isLt
    simp only [Fin.val_last, gramPivot_val] at hval
    omega

theorem rowAxis_not_mem_gramQuadraticList_weighted_leading_support_allRank
    {r n : ℕ} (hn : 2 * r < n) (row : Fin (r + 1))
    (g : PolynomialSpace r (n + 1))
    (hg : g ∈ gramQuadraticList r (n + 1)) :
    variableIndex row (Fin.last n) ∉
      ((weightedMonomialOrder (gramVariableNatWeight r (n + 1))).degree
        g).support := by
  unfold gramQuadraticList at hg
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
  exact rowAxis_not_mem_gramPair_weighted_leading_support_allRank hn row z

end ArbitraryRowMickelssonGramQuotient

end

end HigherHarmonicYoung

section


open scoped BigOperators MonomialOrder

namespace HigherYoungArbitraryRankAxialAssociatedGraded

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramQuotient
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal
open MetricCodes.Spherical.HigherYoungCoprimeLeadingBuchberger
open MetricCodes.Spherical.HigherYoungCoprimeLeadingRegularSequence

private def lowerAxisPolynomialList
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    List (PolynomialSpace r n) :=
  ((Finset.univ.filter (fun i : Fin (r + 1) => i < row)).toList).map
    (fun i => MvPolynomial.X (variableIndex i k))

theorem mem_lowerAxisPolynomialList_iff
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1))
    (p : PolynomialSpace r n) :
    p ∈ lowerAxisPolynomialList k row ↔
      ∃ i : Fin (r + 1), i < row ∧
        p = MvPolynomial.X (variableIndex i k) := by
  classical
  simp only [lowerAxisPolynomialList, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and, eq_comm]

theorem lowerAxisPolynomialList_ideal
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    Ideal.ofList (lowerAxisPolynomialList k row) =
      lowerAxisIdeal k row := by
  change
    Ideal.span {p : PolynomialSpace r n |
      p ∈ lowerAxisPolynomialList k row} =
      Ideal.span {p : PolynomialSpace r n |
        ∃ i : Fin (r + 1), i < row ∧
          p = MvPolynomial.X (variableIndex i k)}
  congr 1
  ext p
  exact mem_lowerAxisPolynomialList_iff k row p

private def lowerAxisGramPolynomialList
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    List (PolynomialSpace r n) :=
  gramQuadraticList r n ++ lowerAxisPolynomialList k row

theorem lowerAxisGramPolynomialList_ideal
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    Ideal.ofList (lowerAxisGramPolynomialList k row) =
      lowerAxisGramIdeal k row := by
  rw [lowerAxisGramPolynomialList, Ideal.ofList_append,
    gramQuadraticList_ideal_eq_youngGramRadialIdeal,
    lowerAxisPolynomialList_ideal]
  rfl

theorem lowerAxisGramPolynomialList_weighted_monic
    {r n : ℕ} (hn : 2 * r < n)
    (k : Fin n) (row : Fin (r + 1))
    (p : PolynomialSpace r n)
    (hp : p ∈ lowerAxisGramPolynomialList k row) :
    (weightedMonomialOrder (gramVariableNatWeight r n)).Monic p := by
  rcases List.mem_append.mp hp with hp | hp
  · exact gramQuadraticList_weighted_monic hn p hp
  · obtain ⟨i, _, rfl⟩ :=
      (mem_lowerAxisPolynomialList_iff k row p).mp hp
    exact MonomialOrder.monic_X

theorem lowerAxisPolynomialList_weighted_degree_pairwise_disjoint
    {r n : ℕ} (k : Fin n) (row : Fin (r + 1)) :
    (lowerAxisPolynomialList k row).Pairwise
      (fun p q => Disjoint
        ((weightedMonomialOrder (gramVariableNatWeight r n)).degree p).support
        ((weightedMonomialOrder (gramVariableNatWeight r n)).degree q).support) := by
  classical
  rw [lowerAxisPolynomialList, List.pairwise_map]
  apply (Finset.nodup_toList
    (Finset.univ.filter (fun i : Fin (r + 1) => i < row))).imp
  intro i j hij
  rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
  simp only [Finsupp.support_single _ one_ne_zero,
    Finset.disjoint_singleton]
  intro h
  exact hij ((variableIndex_eq_iff_harmonicLift i j k k).mp h).1

theorem gramPairPolynomial_lowerAxis_weighted_degree_disjoint
    {r n : ℕ} (hn : 2 * r < n)
    (axisRow : Fin (r + 1))
    (z : UpperGramPair r) :
    Disjoint
      ((weightedMonomialOrder
        (gramVariableNatWeight r (n + 1))).degree
          (gramPairPolynomial (n + 1) z)).support
      ((weightedMonomialOrder
        (gramVariableNatWeight r (n + 1))).degree
          (MvPolynomial.X
            (variableIndex axisRow (Fin.last n)) :
              PolynomialSpace r (n + 1))).support := by
  rw [MonomialOrder.degree_X]
  simp only [Finsupp.support_single _ one_ne_zero,
    Finset.disjoint_singleton_right]
  exact rowAxis_not_mem_gramPair_weighted_leading_support_allRank
    hn axisRow z

theorem lowerAxisGramPolynomialList_weighted_degree_pairwise_disjoint
    {r n : ℕ} (hn : 2 * r < n)
    (row : Fin (r + 1)) :
    (lowerAxisGramPolynomialList (Fin.last n) row).Pairwise
      (fun p q => Disjoint
        ((weightedMonomialOrder
          (gramVariableNatWeight r (n + 1))).degree p).support
        ((weightedMonomialOrder
          (gramVariableNatWeight r (n + 1))).degree q).support) := by
  rw [lowerAxisGramPolynomialList, List.pairwise_append]
  refine ⟨gramQuadraticList_weighted_degree_pairwise_disjoint
    (by omega),
    lowerAxisPolynomialList_weighted_degree_pairwise_disjoint
      (Fin.last n) row, ?_⟩
  intro g hg a ha
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, _, rfl⟩ :=
    (mem_lowerAxisPolynomialList_iff (Fin.last n) row a).mp ha
  exact gramPairPolynomial_lowerAxis_weighted_degree_disjoint
    hn i z

theorem selectedAxis_not_mem_lowerAxisGramPolynomialList_leading_support
    {r n : ℕ} (hn : 2 * r < n) (row : Fin (r + 1))
    (p : PolynomialSpace r (n + 1))
    (hp : p ∈ lowerAxisGramPolynomialList (Fin.last n) row) :
    variableIndex row (Fin.last n) ∉
      ((weightedMonomialOrder
        (gramVariableNatWeight r (n + 1))).degree p).support := by
  rcases List.mem_append.mp hp with hp | hp
  · exact rowAxis_not_mem_gramQuadraticList_weighted_leading_support_allRank
      hn row p hp
  · obtain ⟨i, hi, rfl⟩ :=
      (mem_lowerAxisPolynomialList_iff (Fin.last n) row p).mp hp
    rw [MonomialOrder.degree_X]
    simp only [Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton]
    intro h
    have heq :=
      ((variableIndex_eq_iff_harmonicLift row i
        (Fin.last n) (Fin.last n)).mp h).1
    exact (ne_of_lt hi) heq.symm

theorem lowerAxisGramIdeal_axis_mul_mem_iff
    {r n : ℕ} (hn : 2 * r < n)
    (row : Fin (r + 1)) (p : PolynomialSpace r (n + 1)) :
    MvPolynomial.X (variableIndex row (Fin.last n)) * p ∈
        lowerAxisGramIdeal (Fin.last n) row ↔
      p ∈ lowerAxisGramIdeal (Fin.last n) row := by
  constructor
  · intro hp
    rw [← lowerAxisGramPolynomialList_ideal] at hp ⊢
    exact mem_of_X_mul_mem_of_avoids_leading_support
      (weightedMonomialOrder (gramVariableNatWeight r (n + 1)))
      (lowerAxisGramPolynomialList (Fin.last n) row)
      (lowerAxisGramPolynomialList_weighted_monic (by omega)
        (Fin.last n) row)
      (pairwise_coprime_monic_leadingDivisibility
        (weightedMonomialOrder (gramVariableNatWeight r (n + 1)))
        (lowerAxisGramPolynomialList (Fin.last n) row)
        (lowerAxisGramPolynomialList_weighted_monic (by omega)
          (Fin.last n) row)
        (lowerAxisGramPolynomialList_weighted_degree_pairwise_disjoint
          hn row))
      (variableIndex row (Fin.last n))
      (selectedAxis_not_mem_lowerAxisGramPolynomialList_leading_support
        hn row) p hp
  · exact (lowerAxisGramIdeal (Fin.last n) row).mul_mem_left _

end HigherYoungArbitraryRankAxialAssociatedGraded

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungIteratedAxialProjectionSemigroup

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungMixedGapBranching
open MetricCodes.Spherical.HigherYoungSameAxisTraceIdeal

theorem simultaneousHarmonicProjection_residual_mem_gram_of_two_le
    {r n m : ℕ} (hm : 2 ≤ m)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    ((p : PolynomialSpace r n) -
      ((simultaneousHarmonicProjection r n m p).val :
        PolynomialSpace r n)) ∈ youngGramRadialIdeal r n := by
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ k =>
          exact
            simultaneousHarmonicProjection_residual_mem_youngGramRadialIdeal
              (r := r) (n := n) (m := k) p

theorem harmonicYoung_eq_zero_of_mem_youngGramRadialIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam)
    (hp : (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n) :
    p = 0 := by
  apply Subtype.ext
  apply (SpherePacking.Fischer.polynomialInner_self_eq_zero
    ((r + 1) * n) (p : PolynomialSpace r n)).mp
  exact polynomialInner_youngGramRadialIdeal_eq_zero_of_traceFree
    (p : PolynomialSpace r n) (p : PolynomialSpace r n)
    ((mem_harmonicYoungSubmodule lam (p : PolynomialSpace r n)).mp
      p.property).2.2.1 hp

end HigherYoungIteratedAxialProjectionSemigroup

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankAxialTransverseRetraction

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal
open MetricCodes.Spherical.HigherYoungIteratedAxialProjectionSemigroup
open MetricCodes.Spherical.ThreeRowYoungBranching

private def axialTransverseCoordinate {r n : ℕ} :
    Fin ((r + 2) * (n + 1)) → PolynomialSpace r n :=
  fun a =>
    let z := (finProdFinEquiv
      (m := r + 2) (n := n + 1)).symm a
    Fin.lastCases (0 : PolynomialSpace r n)
      (fun i : Fin (r + 1) =>
        Fin.lastCases (0 : PolynomialSpace r n)
          (fun j : Fin n => MvPolynomial.X (variableIndex i j)) z.2)
      z.1

private def axialTransverseRetraction {r n : ℕ} :
    PolynomialSpace (r + 1) (n + 1) →ₐ[ℝ]
      PolynomialSpace r n :=
  MvPolynomial.aeval axialTransverseCoordinate

@[simp] theorem axialTransverseRetraction_X_castSucc
    {r n : ℕ} (i : Fin (r + 1)) (j : Fin n) :
    axialTransverseRetraction
        (MvPolynomial.X
          (variableIndex (r := r + 1) i.castSucc j.castSucc)) =
      (MvPolynomial.X (variableIndex (r := r) i j) : PolynomialSpace r n) := by
  simp only [axialTransverseRetraction, MvPolynomial.aeval_eq_bind₁, variableIndex,
    MvPolynomial.bind₁_X_right, axialTransverseCoordinate, Equiv.symm_apply_apply,
    Fin.lastCases_castSucc]

@[simp] theorem axialTransverseRetraction_X_lastCoordinate
    {r n : ℕ} (i : Fin (r + 2)) :
    axialTransverseRetraction
        (MvPolynomial.X
          (variableIndex (r := r + 1) i (Fin.last n))) =
      (0 : PolynomialSpace r n) := by
  induction i using Fin.lastCases with
  | last =>
      simp only [axialTransverseRetraction, MvPolynomial.aeval_eq_bind₁, variableIndex,
        MvPolynomial.bind₁_X_right, axialTransverseCoordinate, Equiv.symm_apply_apply,
        Fin.lastCases_last]
  | cast i =>
      simp only [axialTransverseRetraction, MvPolynomial.aeval_eq_bind₁, variableIndex,
        MvPolynomial.bind₁_X_right, axialTransverseCoordinate, Equiv.symm_apply_apply,
        Fin.lastCases_last, Fin.lastCases_castSucc]

@[simp] theorem axialTransverseRetraction_X_lastRow
    {r n : ℕ} (j : Fin (n + 1)) :
    axialTransverseRetraction
        (MvPolynomial.X
          (variableIndex (r := r + 1) (Fin.last (r + 1)) j)) =
      (0 : PolynomialSpace r n) := by
  simp only [axialTransverseRetraction, MvPolynomial.aeval_eq_bind₁, variableIndex,
    MvPolynomial.bind₁_X_right, axialTransverseCoordinate, Equiv.symm_apply_apply,
    Fin.lastCases_last]

@[simp] theorem axialTransverseRetraction_transversePolynomial
    {r n : ℕ} (p : PolynomialSpace r n) :
    axialTransverseRetraction
      (transversePolynomial (r := r) n p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
      let z := (finProdFinEquiv (m := r + 1) (n := n)).symm a
      have ha : variableIndex z.1 z.2 = a :=
        (finProdFinEquiv (m := r + 1) (n := n)).apply_symm_apply a
      rw [map_mul, map_mul, hp]
      rw [← ha, transversePolynomial_X,
        axialTransverseRetraction_X_castSucc]

@[simp] theorem axialTransverseRetraction_terminalZeroSelectedBranch
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) mu) :
    axialTransverseRetraction
      ((terminalZeroSelectedBranchIsometry mu p :
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu)) :
          PolynomialSpace (r + 1) (n + 1)) =
      (p : PolynomialSpace r n) := by
  change axialTransverseRetraction
    (transversePolynomial n (p : PolynomialSpace r n)) = _
  exact axialTransverseRetraction_transversePolynomial
    (p : PolynomialSpace r n)

end ArbitraryRankAxialTransverseRetraction

end

section


open scoped BigOperators

namespace ArbitraryRankAxialRetractionGramImage

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialTransverseRetraction

theorem axialTransverseRetraction_rowPairingPolynomial_castSucc
    {r n : ℕ} (i j : Fin (r + 1)) :
    axialTransverseRetraction
      (rowPairingPolynomial (r := r + 1) (n := n + 1)
        i.castSucc j.castSucc) =
      rowPairingPolynomial (r := r) (n := n) i j := by
  rw [rowPairingPolynomial, map_sum, Fin.sum_univ_castSucc]
  simp only [map_mul, axialTransverseRetraction_X_castSucc,
    axialTransverseRetraction_X_lastCoordinate, zero_mul, add_zero]
  rfl

theorem axialTransverseRetraction_rowPairingPolynomial_last_left
    {r n : ℕ} (j : Fin (r + 2)) :
    axialTransverseRetraction
      (rowPairingPolynomial (r := r + 1) (n := n + 1)
        (Fin.last (r + 1)) j) = (0 : PolynomialSpace r n) := by
  rw [rowPairingPolynomial, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [map_mul, axialTransverseRetraction_X_lastRow, zero_mul]

theorem axialTransverseRetraction_rowPairingPolynomial_last_right
    {r n : ℕ} (i : Fin (r + 2)) :
    axialTransverseRetraction
      (rowPairingPolynomial (r := r + 1) (n := n + 1)
        i (Fin.last (r + 1))) = (0 : PolynomialSpace r n) := by
  rw [rowPairingPolynomial, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [map_mul, axialTransverseRetraction_X_lastRow, mul_zero]

theorem axialTransverseRetraction_rowPairingPolynomial_mem
    {r n : ℕ} (i j : Fin (r + 2)) :
    axialTransverseRetraction
      (rowPairingPolynomial (r := r + 1) (n := n + 1) i j) ∈
        youngGramRadialIdeal r n := by
  induction i using Fin.lastCases with
  | last =>
      rw [axialTransverseRetraction_rowPairingPolynomial_last_left]
      exact (youngGramRadialIdeal r n).zero_mem
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [axialTransverseRetraction_rowPairingPolynomial_last_right]
          exact (youngGramRadialIdeal r n).zero_mem
      | cast j =>
          rw [axialTransverseRetraction_rowPairingPolynomial_castSucc]
          exact rowPairingPolynomial_mem_youngGramRadialIdeal i j

theorem map_axialTransverseRetraction_youngGramRadialIdeal_le
    {r n : ℕ} :
    Ideal.map axialTransverseRetraction
      (youngGramRadialIdeal (r + 1) (n + 1)) ≤
        youngGramRadialIdeal r n := by
  rw [Ideal.map_le_iff_le_comap, youngGramRadialIdeal,
    Ideal.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact axialTransverseRetraction_rowPairingPolynomial_mem i j

end ArbitraryRankAxialRetractionGramImage

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankAxialRetractionLowerIdeal

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialTransverseRetraction
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialRetractionGramImage
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal

theorem map_axialTransverseRetraction_lowerAxisIdeal_eq_bot
    {r n : ℕ} (row : Fin (r + 2)) :
    Ideal.map (axialTransverseRetraction (r := r) (n := n))
        (lowerAxisIdeal (Fin.last n) row) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Ideal.map_le_iff_le_comap, lowerAxisIdeal, Ideal.span_le]
  rintro p ⟨i, _, rfl⟩
  change axialTransverseRetraction
    (MvPolynomial.X
      (variableIndex (r := r + 1) i (Fin.last n))) = 0
  exact axialTransverseRetraction_X_lastCoordinate i

theorem map_axialTransverseRetraction_lowerAxisGramIdeal_le
    {r n : ℕ} (row : Fin (r + 2)) :
    Ideal.map (axialTransverseRetraction (r := r) (n := n))
        (lowerAxisGramIdeal (Fin.last n) row) ≤
      youngGramRadialIdeal r n := by
  rw [lowerAxisGramIdeal, Ideal.map_sup,
    map_axialTransverseRetraction_lowerAxisIdeal_eq_bot row,
    sup_bot_eq]
  exact map_axialTransverseRetraction_youngGramRadialIdeal_le

theorem axialTransverseRetraction_mem_lowerAxisGramIdeal
    {r n : ℕ} (row : Fin (r + 2))
    {p : PolynomialSpace (r + 1) (n + 1)}
    (hp : p ∈ lowerAxisGramIdeal (Fin.last n) row) :
    axialTransverseRetraction p ∈ youngGramRadialIdeal r n := by
  exact map_axialTransverseRetraction_lowerAxisGramIdeal_le row
    (Ideal.mem_map_of_mem axialTransverseRetraction hp)

end ArbitraryRankAxialRetractionLowerIdeal

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankAxialTransverseSeedNonvanishing

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialTransverseRetraction
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialRetractionLowerIdeal
open MetricCodes.Spherical.HigherYoungArbitraryRowAxialFiltrationIdeal
open MetricCodes.Spherical.HigherYoungIteratedAxialProjectionSemigroup
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem terminalZeroSelectedBranch_not_mem_lowerAxisGramIdeal
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2))
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    ((terminalZeroSelectedBranchIsometry mu p :
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu)) :
        PolynomialSpace (r + 1) (n + 1)) ∉
      lowerAxisGramIdeal (Fin.last n) row := by
  intro hmem
  have hsource :
      (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n := by
    have hret := axialTransverseRetraction_mem_lowerAxisGramIdeal
      row hmem
    rwa [axialTransverseRetraction_terminalZeroSelectedBranch] at hret
  exact hp (harmonicYoung_eq_zero_of_mem_youngGramRadialIdeal
    mu p hsource)

end ArbitraryRankAxialTransverseSeedNonvanishing

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankInterlacingTriangularCoefficient

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinTriangularNormalForm
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAxialTransverseSeedNonvanishing
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherYoungArbitraryRankAxialAssociatedGraded
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem interlacingRowSchedule_pairwise_le
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) :
    (interlacingRowSchedule lam mu).Pairwise (· ≤ ·) := by
  unfold interlacingRowSchedule
  apply List.pairwise_flatMap.mpr
  constructor
  · intro row _
    exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · apply (List.sortedLT_finRange (r + 2)).pairwise.imp
    intro i j hij x hx y hy
    have hx' : x = i := (List.mem_replicate.mp hx).2
    have hy' : y = j := (List.mem_replicate.mp hy).2
    simpa only [hx', hy', ge_iff_le] using le_of_lt hij

theorem reverseInterlacingRowSchedule_pairwise_ge
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) :
    (reverseInterlacingRowSchedule lam mu).Pairwise (· ≥ ·) := by
  unfold reverseInterlacingRowSchedule
  apply List.pairwise_reverse.mpr
  exact interlacingRowSchedule_pairwise_le lam mu

theorem reverseInterlacingRowSchedule_prefix_count_le
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (pref suffix : List (Fin (r + 2)))
    (hdecomp : pref ++ suffix = reverseInterlacingRowSchedule lam mu)
    (row : Fin (r + 2)) :
    pref.count row ≤ interlacingGap lam mu row := by
  have hcount := congrArg (List.count row) hdecomp
  rw [List.count_append,
    reverseInterlacingRowSchedule_count] at hcount
  omega

theorem reverseInterlacingRowSchedule_prefix_leadingScalar_pos
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (h : Interlaces lam mu)
    (pref suffix : List (Fin (r + 2)))
    (row : Fin (r + 2))
    (hdecomp : pref ++ row :: suffix =
      reverseInterlacingRowSchedule lam mu) :
    0 < arbitraryRowLeadingScalar
      (arbitraryRowPathWeight (appendZeroWeight mu) pref) row := by
  rw [arbitraryRowPathWeight_eq_foldl]
  apply foldl_arbitraryRowLeadingScalar_pos_of_count_lt_gap h pref
  · intro i
    exact reverseInterlacingRowSchedule_prefix_count_le
      lam mu pref (row :: suffix) hdecomp i
  · have hcount := congrArg (List.count row) hdecomp
    rw [List.count_append, List.count_cons_self,
      reverseInterlacingRowSchedule_count] at hcount
    omega

theorem reverseInterlacingRowSchedule_positiveLeading
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (h : Interlaces lam mu) :
    positiveLeadingAxialSchedule (appendZeroWeight mu)
      (reverseInterlacingRowSchedule lam mu) := by
  have haux : ∀ (pref suffix : List (Fin (r + 2))),
      pref ++ suffix = reverseInterlacingRowSchedule lam mu →
        positiveLeadingAxialSchedule
          (arbitraryRowPathWeight (appendZeroWeight mu) pref) suffix := by
    intro pref suffix
    induction suffix generalizing pref with
    | nil =>
        intro _
        trivial
    | cons row tail ih =>
        intro hdecomp
        constructor
        · exact reverseInterlacingRowSchedule_prefix_leadingScalar_pos
            h pref tail row hdecomp
        · have hupdate :
              arbitraryRowPathWeight (appendZeroWeight mu)
                  (pref ++ [row]) =
                raiseWeight
                  (arbitraryRowPathWeight (appendZeroWeight mu) pref) row := by
              rw [arbitraryRowPathWeight_eq_foldl,
                arbitraryRowPathWeight_eq_foldl, List.foldl_append]
              simp only [List.foldl_cons, List.foldl_nil]
          rw [← hupdate]
          apply ih (pref ++ [row])
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hdecomp
  simpa only [arbitraryRowPathWeight] using haux [] (reverseInterlacingRowSchedule lam mu) rfl

theorem reverseInterlacingPolynomialSeed_not_mem_youngGramRadialIdeal
    {r n : ℕ} (hn : 2 * (r + 1) < n)
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    reverseInterlacingPolynomialSeed lam mu p ∉
      youngGramRadialIdeal (r + 1) (n + 1) := by
  change
    iteratedArbitraryRowAxialRaise
      (appendZeroWeight mu) (Fin.last n)
      (reverseInterlacingRowSchedule lam mu)
      ((terminalZeroSelectedBranchIsometry mu p :
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu)) :
          PolynomialSpace (r + 1) (n + 1)) ∉
      youngGramRadialIdeal (r + 1) (n + 1)
  apply iteratedArbitraryRowAxialRaise_not_mem_youngGramRadialIdeal_of_descending
    (appendZeroWeight mu) (Fin.last n)
    (reverseInterlacingRowSchedule lam mu) (Fin.last (r + 1))
  · exact reverseInterlacingRowSchedule_pairwise_ge lam mu
  · intro row _
    exact Fin.le_last row
  · exact reverseInterlacingRowSchedule_positiveLeading h
  · intro row q
    exact lowerAxisGramIdeal_axis_mul_mem_iff hn row q
  · exact terminalZeroSelectedBranch_not_mem_lowerAxisGramIdeal
      mu (Fin.last (r + 1)) p hp

end ArbitraryRankInterlacingTriangularCoefficient

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankHarmonicBranch

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungBranchingFibres

theorem young_pderiv_eq_zero_of_isHomogeneous_zero
    {r n : ℕ} (x : Fin ((r + 1) * n))
    (p : PolynomialSpace r n)
    (hp : p.IsHomogeneous 0) :
    MvPolynomial.pderiv x p = 0 := by
  have hdegree : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous
      (Fin ((r + 1) * n))).mpr hp
  have hconstant : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  rw [hconstant, MvPolynomial.pderiv_C]

theorem traceOperator_eq_zero_of_isHomogeneous_degree_lt_two
    {r n d : ℕ} (hd : d < 2)
    (p : PolynomialSpace r n) (hp : p.IsHomogeneous d)
    (i j : Fin (r + 1)) :
    traceOperator r n i j p = 0 := by
  rw [traceOperator_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hfirst :
      (MvPolynomial.pderiv (variableIndex j k) p).IsHomogeneous 0 := by
    simpa only [show d - 1 = 0 by omega] using hp.pderiv
  exact young_pderiv_eq_zero_of_isHomogeneous_zero
    (variableIndex i k) _ hfirst

theorem homogeneous_mem_youngGramRadialIdeal_eq_zero_of_degree_lt_two
    {r n d : ℕ} (hd : d < 2)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) d)
    (hp : (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n) :
    p = 0 := by
  apply Subtype.ext
  apply (SpherePacking.Fischer.polynomialInner_self_eq_zero
    ((r + 1) * n) (p : PolynomialSpace r n)).mp
  exact polynomialInner_youngGramRadialIdeal_eq_zero_of_traceFree
    (p : PolynomialSpace r n) (p : PolynomialSpace r n)
    (fun i j =>
      traceOperator_eq_zero_of_isHomogeneous_degree_lt_two
        hd (p : PolynomialSpace r n) p.property i j)
    hp

theorem simultaneousHarmonicProjection_eq_zero_iff_gramIdeal_all_degree
    {r n d : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) d) :
    simultaneousHarmonicProjection r n d p = 0 ↔
      (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n := by
  by_cases hd : 2 ≤ d
  · exact simultaneousHarmonicProjection_eq_zero_iff_gramIdeal hd p
  · have hsmall : d < 2 := by omega
    have htrace : p ∈ homogeneousTraceFreeSubmodule r n d := by
      rw [mem_homogeneousTraceFreeSubmodule]
      exact fun i j =>
        traceOperator_eq_zero_of_isHomogeneous_degree_lt_two
          hsmall (p : PolynomialSpace r n) p.property i j
    let q : homogeneousTraceFreeSubmodule r n d := ⟨p, htrace⟩
    have hfix : simultaneousHarmonicProjection r n d p = q :=
      simultaneousHarmonicProjection_traceFree q
    constructor
    · intro hzero
      have hq : q = 0 := hfix.symm.trans hzero
      have hpzero : p = 0 := by
        calc
          p = q.val := rfl
          _ = (0 : homogeneousTraceFreeSubmodule r n d).val :=
            congrArg Subtype.val hq
          _ = 0 := rfl
      simp only [hpzero, ZeroMemClass.coe_zero, zero_mem]
    · intro hgram
      have hpzero :=
        homogeneous_mem_youngGramRadialIdeal_eq_zero_of_degree_lt_two
          hsmall p hgram
      simp only [hpzero, map_zero]

theorem youngHarmonicLift_eq_zero_iff_gramIdeal_all_degree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : homogeneousYoungHighestWeightSubmodule (n := n) lam) :
    youngHarmonicLift lam p = 0 ↔
      ((p.val : SpherePacking.Fischer.Homogeneous
        ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n) ∈
        youngGramRadialIdeal r n := by
  rw [← simultaneousHarmonicProjection_eq_zero_iff_gramIdeal_all_degree
    p.val]
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun q : HarmonicYoungSpace (n := n) lam =>
        (q : PolynomialSpace r n)) h
  · intro h
    apply Subtype.ext
    exact congrArg
      (fun q : homogeneousTraceFreeSubmodule r n (∑ i, lam i) =>
        (q.val : PolynomialSpace r n)) h

theorem harmonicBranchOfHighestWeightSeed_injective_iff_gramIdeal_all_degree
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (seed : E →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n) lam) :
    Function.Injective (harmonicBranchOfHighestWeightSeed lam seed) ↔
      ∀ p : E,
        ((((seed p).val : SpherePacking.Fischer.Homogeneous
          ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n) ∈
          youngGramRadialIdeal r n) → p = 0 := by
  constructor
  · intro hinjective p hp
    apply hinjective
    rw [map_zero]
    exact (youngHarmonicLift_eq_zero_iff_gramIdeal_all_degree
      lam (seed p)).mpr hp
  · intro hkernel p q hpq
    have hzero :
        harmonicBranchOfHighestWeightSeed lam seed (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hradial :
        ((((seed (p - q)).val : SpherePacking.Fischer.Homogeneous
          ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n) ∈
          youngGramRadialIdeal r n) :=
      (youngHarmonicLift_eq_zero_iff_gramIdeal_all_degree
        lam (seed (p - q))).mp hzero
    exact sub_eq_zero.mp (hkernel (p - q) hradial)

end ArbitraryRankHarmonicBranch

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankGelfandTsetlinHarmonicIsometry

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingHighestWeightSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingTriangularCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherRepresentationGraph

private def reverseInterlacingHighestWeightSeed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n + 1) lam where
  toFun p := by
    refine ⟨⟨reverseInterlacingPolynomialSeed lam mu p,
      reverseInterlacingPolynomialSeed_isHomogeneous lam mu h p⟩, ?_⟩
    apply (mem_homogeneousYoungHighestWeightSubmodule lam _).mpr
    exact ⟨reverseInterlacingPolynomialSeed_rowEuler lam mu h p,
      reverseInterlacingPolynomialSeed_polarization lam mu h p⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (reverseInterlacingPolynomialSeed lam mu) p q
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (reverseInterlacingPolynomialSeed lam mu) c p

/-- The reverse interlacing harmonic branch used in the spherical-code argument. -/
def reverseInterlacingHarmonicBranch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
  harmonicBranchOfHighestWeightSeed lam
    (reverseInterlacingHighestWeightSeed lam mu h)

theorem reverseInterlacingHarmonicBranch_injective_iff_gramIdeal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    Function.Injective (reverseInterlacingHarmonicBranch (n := n) lam mu h) ↔
      ∀ p : HarmonicYoungSpace (n := n) mu,
        reverseInterlacingPolynomialSeed lam mu p ∈
          youngGramRadialIdeal (r + 1) (n + 1) → p = 0 := by
  exact harmonicBranchOfHighestWeightSeed_injective_iff_gramIdeal_all_degree
    lam (reverseInterlacingHighestWeightSeed lam mu h)

theorem reverseInterlacingHarmonicBranch_injective_of_not_mem
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hnonzero : ∀ (p : HarmonicYoungSpace (n := n) mu),
      p ≠ 0 → reverseInterlacingPolynomialSeed lam mu p ∉
        youngGramRadialIdeal (r + 1) (n + 1)) :
    Function.Injective (reverseInterlacingHarmonicBranch (n := n) lam mu h) := by
  apply (reverseInterlacingHarmonicBranch_injective_iff_gramIdeal
    lam mu h).mpr
  intro p hp
  by_contra hne
  exact hnonzero p hne hp

theorem reverseInterlacingHarmonicBranch_injective
    {r n : ℕ} (hn : 2 * (r + 1) < n)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    Function.Injective (reverseInterlacingHarmonicBranch (n := n) lam mu h) := by
  apply reverseInterlacingHarmonicBranch_injective_of_not_mem lam mu h
  intro p hp
  exact reverseInterlacingPolynomialSeed_not_mem_youngGramRadialIdeal
    hn h p hp

end ArbitraryRankGelfandTsetlinHarmonicIsometry

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankGelfandTsetlinFibreNormalization

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherRepresentationGraph
open SpherePacking.HarmonicCoordinateOperators

private def normalizedGelfandTsetlinFibre
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪reverseInterlacingHarmonicBranch lam mu h p,
        reverseInterlacingHarmonicBranch lam mu h q⟫_ℝ =
        c * ⟪p, q⟫_ℝ) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
  normalizedChannelIsometry
    (reverseInterlacingHarmonicBranch lam mu h) c hc hgram

@[simp] theorem normalizedGelfandTsetlinFibre_apply
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪reverseInterlacingHarmonicBranch lam mu h p,
        reverseInterlacingHarmonicBranch lam mu h q⟫_ℝ =
        c * ⟪p, q⟫_ℝ)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGelfandTsetlinFibre lam mu h c hc hgram p =
      (Real.sqrt c)⁻¹ • reverseInterlacingHarmonicBranch lam mu h p := rfl

theorem normalizedGelfandTsetlinFibre_phase_pos
    {c : ℝ} (hc : 0 < c) :
    0 < (Real.sqrt c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hc)

theorem normalizedGelfandTsetlinFibre_channel_apply
    {r n : ℕ} (source target : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hsource : Interlaces source mu) (htarget : Interlaces target mu)
    (sourceGram targetGram : ℝ)
    (hsourceGram : 0 < sourceGram) (htargetGram : 0 < targetGram)
    (hsourceInner : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪reverseInterlacingHarmonicBranch source mu hsource p,
        reverseInterlacingHarmonicBranch source mu hsource q⟫_ℝ =
        sourceGram * ⟪p, q⟫_ℝ)
    (htargetInner : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪reverseInterlacingHarmonicBranch target mu htarget p,
        reverseInterlacingHarmonicBranch target mu htarget q⟫_ℝ =
        targetGram * ⟪p, q⟫_ℝ)
    (channel : HarmonicYoungSpace (n := n + 1) source →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1) target)
    (coefficient : ℝ)
    (haxis : ∀ p : HarmonicYoungSpace (n := n) mu,
      channel (reverseInterlacingHarmonicBranch source mu hsource p) =
        coefficient • reverseInterlacingHarmonicBranch target mu htarget p)
    (p : HarmonicYoungSpace (n := n) mu) :
    channel (normalizedGelfandTsetlinFibre
      source mu hsource sourceGram hsourceGram hsourceInner p) =
      (coefficient * Real.sqrt targetGram / Real.sqrt sourceGram) •
        normalizedGelfandTsetlinFibre
          target mu htarget targetGram htargetGram htargetInner p := by
  rw [normalizedGelfandTsetlinFibre_apply,
    normalizedGelfandTsetlinFibre_apply, map_smul,
    haxis, smul_smul, smul_smul]
  congr 1
  have hs : Real.sqrt sourceGram ≠ 0 :=
    (Real.sqrt_pos.mpr hsourceGram).ne'
  have ht : Real.sqrt targetGram ≠ 0 :=
    (Real.sqrt_pos.mpr htargetGram).ne'
  field_simp

end AllRankGelfandTsetlinFibreNormalization

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungMixedGapAxisProbability

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel



end HigherYoungMixedGapAxisProbability

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace MixedSignature

/-- The ambient coordinate derivation used in the spherical-code argument. -/
def ambientCoordinateDerivation {r n : ℕ} (a b : Fin n) :
    Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n) :=
  ∑ i : Fin (r + 1),
    (MvPolynomial.X (variableIndex i a) : PolynomialSpace r n) •
      (MvPolynomial.pderiv (variableIndex i b) :
        Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))

@[simp] theorem ambientCoordinateDerivation_apply {r n : ℕ}
    (a b : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r) a b p =
      ∑ i : Fin (r + 1),
        MvPolynomial.X (variableIndex i a) *
          MvPolynomial.pderiv (variableIndex i b) p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ i : Fin (r + 1),
        (MvPolynomial.X (variableIndex i a) : PolynomialSpace r n) •
          (MvPolynomial.pderiv (variableIndex i b) :
            Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n)))) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem ambientCoordinateDerivation_X {r n : ℕ}
    (a b c : Fin n) (i : Fin (r + 1)) :
    ambientCoordinateDerivation (r := r) a b
      (MvPolynomial.X (variableIndex i c)) =
        if b = c then MvPolynomial.X (variableIndex i a) else 0 := by
  classical
  rw [ambientCoordinateDerivation_apply]
  by_cases h : b = c
  · subst c
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
      and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · have h' : c ≠ b := Ne.symm h
    simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, h', and_false,
      not_false_eq_true, Pi.single_eq_of_ne, mul_zero, Finset.sum_const_zero, h, ↓reduceIte]

/-- The ambient rotation used in the spherical-code argument. -/
def ambientRotation {r n : ℕ} (a b : Fin n) :
    Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n) :=
  ambientCoordinateDerivation (r := r) a b -
    ambientCoordinateDerivation (r := r) b a

@[simp] theorem ambientRotation_apply {r n : ℕ}
    (a b : Fin n) (p : PolynomialSpace r n) :
    ambientRotation (r := r) a b p =
      ambientCoordinateDerivation (r := r) a b p -
        ambientCoordinateDerivation (r := r) b a p := rfl

private def rowPolarizationDerivation {r n : ℕ} (i j : Fin (r + 1)) :
    Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n) :=
  ∑ a : Fin n,
    (MvPolynomial.X (variableIndex i a) : PolynomialSpace r n) •
      (MvPolynomial.pderiv (variableIndex j a) :
        Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))

@[simp] theorem rowPolarizationDerivation_apply {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowPolarizationDerivation i j p = polarization r n i j p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ a : Fin n,
        (MvPolynomial.X (variableIndex i a) : PolynomialSpace r n) •
          (MvPolynomial.pderiv (variableIndex j a) :
            Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n)))) p = _
  rw [map_sum, Finset.sum_apply, polarization_apply]
  rfl

theorem rowPolarizationDerivation_X {r n : ℕ}
    (i j k : Fin (r + 1)) (a : Fin n) :
    rowPolarizationDerivation i j
      (MvPolynomial.X (variableIndex k a)) =
        if j = k then MvPolynomial.X (variableIndex i a) else 0 := by
  rw [rowPolarizationDerivation_apply]
  exact polarization_X_euler i j k a

private def derivationCommutator {r n : ℕ}
    (D₁ D₂ : Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n)) :
    Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n) :=
  Derivation.mk'
    (D₁.toLinearMap.comp D₂.toLinearMap -
      D₂.toLinearMap.comp D₁.toLinearMap)
    fun p q => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        Derivation.coeFn_coe, map_add, Derivation.leibniz, smul_eq_mul]
      ring

private instance derivationBracket {r n : ℕ} :
    Bracket
      (Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))
      (Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n)) :=
  ⟨derivationCommutator⟩

@[simp] private theorem derivationCommutator_apply {r n : ℕ}
    (D₁ D₂ : Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))
    (p : PolynomialSpace r n) :
    derivationCommutator D₁ D₂ p = D₁ (D₂ p) - D₂ (D₁ p) := rfl

@[simp] private theorem derivationBracket_apply {r n : ℕ}
    (D₁ D₂ : Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))
    (p : PolynomialSpace r n) :
    ⁅D₁, D₂⁆ p = D₁ (D₂ p) - D₂ (D₁ p) := rfl

theorem ambientCoordinateDerivation_rowPolarization_commutator {r n : ℕ}
    (a b : Fin n) (i j : Fin (r + 1)) :
    ⁅ambientCoordinateDerivation (r := r) a b,
        rowPolarizationDerivation (n := n) i j⁆ = 0 := by
  classical
  apply MvPolynomial.derivation_ext
  have hcoordinate (k : Fin (r + 1)) (c : Fin n) :
      ⁅ambientCoordinateDerivation (r := r) a b,
          rowPolarizationDerivation (n := n) i j⁆
            (MvPolynomial.X (variableIndex k c)) =
        (0 : Derivation ℝ (PolynomialSpace r n) (PolynomialSpace r n))
          (MvPolynomial.X (variableIndex k c)) := by
    simp only [derivationBracket_apply,
      rowPolarizationDerivation_X, ambientCoordinateDerivation_X,
      Derivation.zero_apply]
    split_ifs <;>
      simp_all only [rowPolarizationDerivation_X,
        ambientCoordinateDerivation_X, map_zero, sub_self,
        ite_true, ite_false]
  intro x
  let k := ((finProdFinEquiv (m := r + 1) (n := n)).symm x).1
  let c := ((finProdFinEquiv (m := r + 1) (n := n)).symm x).2
  have hx : variableIndex k c = x := by
    exact (finProdFinEquiv (m := r + 1) (n := n)).apply_symm_apply x
  simpa only [hx] using hcoordinate k c

theorem ambientCoordinateDerivation_polarization_comm {r n : ℕ}
    (a b : Fin n) (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r) a b
        (polarization r n i j p) =
      polarization r n i j
        (ambientCoordinateDerivation (r := r) a b p) := by
  have h := congrArg (fun D : Derivation ℝ (PolynomialSpace r n)
      (PolynomialSpace r n) => D p)
    (ambientCoordinateDerivation_rowPolarization_commutator a b i j)
  have hcomm :
      ambientCoordinateDerivation (r := r) a b
          (rowPolarizationDerivation (n := n) i j p) =
        rowPolarizationDerivation (n := n) i j
          (ambientCoordinateDerivation (r := r) a b p) := by
    apply sub_eq_zero.mp
    simpa only [derivationBracket_apply,
      Derivation.zero_apply] using h
  simpa only [rowPolarizationDerivation_apply] using hcomm

theorem ambientRotation_polarization_comm {r n : ℕ}
    (a b : Fin n) (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    ambientRotation (r := r) a b (polarization r n i j p) =
      polarization r n i j (ambientRotation (r := r) a b p) := by
  simp only [ambientRotation_apply, map_sub,
    ambientCoordinateDerivation_polarization_comm]

theorem ambientRotation_rowEuler_comm {r n : ℕ}
    (a b : Fin n) (i : Fin (r + 1)) (p : PolynomialSpace r n) :
    ambientRotation (r := r) a b (rowEuler r n i p) =
      rowEuler r n i (ambientRotation (r := r) a b p) := by
  simpa only [← polarization_self, polarization_apply, map_sum, Derivation.leibniz,
    ambientRotation_apply,
    ambientCoordinateDerivation_apply, smul_eq_mul, MvPolynomial.pderiv_X, map_sub] using
    ambientRotation_polarization_comm a b i i p

theorem traceOperator_ambientCoordinateDerivation {r n : ℕ}
    (i j : Fin (r + 1)) (a b : Fin n) (p : PolynomialSpace r n) :
    traceOperator r n i j
        (ambientCoordinateDerivation (r := r) a b p) =
      ambientCoordinateDerivation (r := r) a b
          (traceOperator r n i j p) +
        MvPolynomial.pderiv (variableIndex j a)
          (MvPolynomial.pderiv (variableIndex i b) p) +
        MvPolynomial.pderiv (variableIndex i a)
          (MvPolynomial.pderiv (variableIndex j b) p) := by
  classical
  rw [ambientCoordinateDerivation_apply, map_sum]
  simp_rw
    [MetricCodes.Spherical.HigherYoungProjectedRaiseInjectivity.traceOperator_X_mul_coordinate,
    traceOperator_pderiv_comm]
  rw [ambientCoordinateDerivation_apply]
  simp only [traceOperator_apply, map_sum, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

theorem ambientRotation_traceOperator_comm {r n : ℕ}
    (a b : Fin n) (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator r n i j (ambientRotation (r := r) a b p) =
      ambientRotation (r := r) a b (traceOperator r n i j p) := by
  rw [ambientRotation_apply, map_sub,
    traceOperator_ambientCoordinateDerivation,
    traceOperator_ambientCoordinateDerivation,
    ambientRotation_apply]
  have hfirst := SpherePacking.mvPolynomial_pderiv_commute
    (variableIndex j a) (variableIndex i b) p
  have hsecond := SpherePacking.mvPolynomial_pderiv_commute
    (variableIndex i a) (variableIndex j b) p
  rw [hfirst, hsecond]
  abel

theorem ambientRotation_mem_harmonicYoungSubmodule {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (a b : Fin n)
    {p : PolynomialSpace r n} (hp : p ∈ harmonicYoungSubmodule lam) :
    ambientRotation (r := r) a b p ∈ harmonicYoungSubmodule lam := by
  have hp' := (mem_harmonicYoungSubmodule lam p).mp hp
  have hweight : ∀ i : Fin (r + 1),
      rowEuler r n i (ambientRotation (r := r) a b p) =
        (lam i : ℝ) • ambientRotation (r := r) a b p := by
    intro i
    rw [← ambientRotation_rowEuler_comm, hp'.2.1 i,
      Derivation.map_smul]
  have hmulti : ambientRotation (r := r) a b p ∈
      youngMultihomogeneousSubmodule n lam :=
    (mem_youngMultihomogeneousSubmodule_iff_rowEuler lam _).mpr hweight
  apply (mem_harmonicYoungSubmodule lam _).mpr
  refine ⟨youngMultihomogeneous_isHomogeneous lam ⟨_, hmulti⟩,
    hweight, ?_, ?_⟩
  · intro i j
    rw [ambientRotation_traceOperator_comm, hp'.2.2.1 i j, map_zero]
  · intro i j hij
    rw [← ambientRotation_polarization_comm, hp'.2.2.2 i j hij,
      map_zero]

/-- The young ambient rotation used in the spherical-code argument. -/
def youngAmbientRotation {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam where
  toFun p := ⟨ambientRotation (r := r) a b p,
    ambientRotation_mem_harmonicYoungSubmodule lam a b p.property⟩
  map_add' p q := by
    apply Subtype.ext
    exact Derivation.map_add (ambientRotation (r := r) a b)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    exact Derivation.map_smul (ambientRotation (r := r) a b) c
      (p : PolynomialSpace r n)

@[simp] theorem youngAmbientRotation_apply_coe {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (a b : Fin n)
    (p : HarmonicYoungSpace (n := n) lam) :
    ((youngAmbientRotation lam a b p : HarmonicYoungSpace lam) :
      PolynomialSpace r n) = ambientRotation (r := r) a b p := rfl

theorem ambientCoordinateDerivation_polynomialInner {r n : ℕ}
    (a b : Fin n) (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (ambientCoordinateDerivation (r := r) a b p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (ambientCoordinateDerivation (r := r) b a q) := by
  classical
  rw [ambientCoordinateDerivation_apply,
    ambientCoordinateDerivation_apply,
    SpherePacking.Fischer.polynomialInner_sum_left,
    SpherePacking.Fischer.polynomialInner_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  calc
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.X (variableIndex i a) *
          MvPolynomial.pderiv (variableIndex i b) p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i b) p)
        (MvPolynomial.pderiv (variableIndex i a) q) :=
      SpherePacking.Fischer.polynomialInner_X_mul ((r + 1) * n)
        (variableIndex i a)
          (MvPolynomial.pderiv (variableIndex i b) p) q
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i a) q)
        (MvPolynomial.pderiv (variableIndex i b) p) :=
      SpherePacking.Fischer.polynomialInner_comm ((r + 1) * n) _ _
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.X (variableIndex i b) *
          MvPolynomial.pderiv (variableIndex i a) q) p :=
      (SpherePacking.Fischer.polynomialInner_X_mul ((r + 1) * n)
        (variableIndex i b)
          (MvPolynomial.pderiv (variableIndex i a) q) p).symm
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (MvPolynomial.X (variableIndex i b) *
          MvPolynomial.pderiv (variableIndex i a) q) :=
      SpherePacking.Fischer.polynomialInner_comm ((r + 1) * n) _ _

theorem youngAmbientRotation_inner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (a b : Fin n)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngAmbientRotation lam a b p, q⟫_ℝ =
      -⟪p, youngAmbientRotation lam a b q⟫_ℝ := by
  rw [young_inner_eq_polynomialInner,
    young_inner_eq_polynomialInner,
    youngAmbientRotation_apply_coe,
    youngAmbientRotation_apply_coe,
    ambientRotation_apply, ambientRotation_apply,
    SpherePacking.fischer_polynomialInner_sub_left]
  rw [ambientCoordinateDerivation_polynomialInner,
    ambientCoordinateDerivation_polynomialInner]
  have hright :
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (p : PolynomialSpace r n)
          (ambientCoordinateDerivation (r := r) a b q -
            ambientCoordinateDerivation (r := r) b a q) =
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (p : PolynomialSpace r n)
          (ambientCoordinateDerivation (r := r) a b q) -
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (p : PolynomialSpace r n)
          (ambientCoordinateDerivation (r := r) b a q) := by
    rw [SpherePacking.Fischer.polynomialInner_comm _
      (p : PolynomialSpace r n),
      SpherePacking.fischer_polynomialInner_sub_left]
    rw [SpherePacking.Fischer.polynomialInner_comm _
      (ambientCoordinateDerivation (r := r) a b q),
      SpherePacking.Fischer.polynomialInner_comm _
      (ambientCoordinateDerivation (r := r) b a q)]
  rw [hright]
  ring

theorem youngAmbientRotation_adjoint {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (youngAmbientRotation lam a b).adjoint =
      -(youngAmbientRotation lam a b) := by
  apply LinearMap.ext
  intro p
  apply ext_inner_right ℝ
  intro q
  calc
    ⟪(youngAmbientRotation lam a b).adjoint p, q⟫_ℝ =
        ⟪p, youngAmbientRotation lam a b q⟫_ℝ :=
      LinearMap.adjoint_inner_left (youngAmbientRotation lam a b) q p
    _ = -⟪youngAmbientRotation lam a b p, q⟫_ℝ := by
      linarith [youngAmbientRotation_inner lam a b p q]
    _ = ⟪-(youngAmbientRotation lam a b) p, q⟫_ℝ := by
      exact (inner_neg_left (youngAmbientRotation lam a b p) q).symm

end MixedSignature

end

section


open scoped BigOperators InnerProductSpace TensorProduct

theorem youngClebschLower_adjoint_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (v : SpherePacking.Euclidean n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (youngClebschLower mu lam hdeg row).adjoint
        (v ⊗ₜ[ℝ] q) =
      projectedCoordinateRaise lam mu hdeg row v q := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : (∑ j : Fin n, v j • b j) = v := by
    simpa [b] using b.sum_repr v
  calc
    (youngClebschLower mu lam hdeg row).adjoint (v ⊗ₜ[ℝ] q) =
        (youngClebschLower mu lam hdeg row).adjoint
          ((∑ j : Fin n, v j • b j) ⊗ₜ[ℝ] q) := by rw [hv]
    _ = ∑ j : Fin n,
        v j • (youngClebschLower mu lam hdeg row).adjoint
          (b j ⊗ₜ[ℝ] q) := by
      rw [TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← TensorProduct.smul_tmul', map_smul]
    _ = ∑ j : Fin n,
        v j • projectedCoordinateRaise lam mu hdeg row (b j) q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [youngClebschLower_adjoint_basis_tmul]
    _ = projectedCoordinateRaiseAxis lam mu hdeg row q
          (∑ j : Fin n, v j • b j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      rfl
    _ = projectedCoordinateRaise lam mu hdeg row v q := by rw [hv]; rfl

namespace ClebschRotation

open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

/-- The euclidean ambient rotation used in the spherical-code argument. -/
def euclideanAmbientRotation {n : ℕ} (a b : Fin n) :
    SpherePacking.Euclidean n →ₗ[ℝ] SpherePacking.Euclidean n where
  toFun v :=
    v b • EuclideanSpace.basisFun (Fin n) ℝ a -
      v a • EuclideanSpace.basisFun (Fin n) ℝ b
  map_add' v w := by
    simp only [PiLp.add_apply, EuclideanSpace.basisFun_apply, add_smul]
    module
  map_smul' c v := by
    simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.basisFun_apply, mul_smul,
      Real.ringHom_apply]
    module

@[simp] theorem euclideanAmbientRotation_apply {n : ℕ}
    (a b : Fin n) (v : SpherePacking.Euclidean n) :
    euclideanAmbientRotation a b v =
      v b • EuclideanSpace.basisFun (Fin n) ℝ a -
        v a • EuclideanSpace.basisFun (Fin n) ℝ b := rfl

theorem euclideanAmbientRotation_inner {n : ℕ}
    (a b : Fin n) (v w : SpherePacking.Euclidean n) :
    ⟪euclideanAmbientRotation a b v, w⟫_ℝ =
      -⟪v, euclideanAmbientRotation a b w⟫_ℝ := by
  simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, inner_sub_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left, Real.ringHom_apply, one_mul,
    inner_sub_right, real_inner_smul_right, EuclideanSpace.inner_single_right, neg_sub]
  ring

theorem euclideanAmbientRotation_adjoint {n : ℕ}
    (a b : Fin n) :
    (euclideanAmbientRotation a b).adjoint =
      -(euclideanAmbientRotation a b) := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  calc
    ⟪(euclideanAmbientRotation a b).adjoint v, w⟫_ℝ =
        ⟪v, euclideanAmbientRotation a b w⟫_ℝ :=
      LinearMap.adjoint_inner_left (euclideanAmbientRotation a b) w v
    _ = -⟪euclideanAmbientRotation a b v, w⟫_ℝ := by
      linarith [euclideanAmbientRotation_inner a b v w]
    _ = ⟪-(euclideanAmbientRotation a b) v, w⟫_ℝ := by
      exact (inner_neg_left (euclideanAmbientRotation a b v) w).symm

theorem ambientRotation_polynomialInner {r n : ℕ}
    (a b : Fin n) (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (ambientRotation (r := r) a b p) q =
      -SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (ambientRotation (r := r) a b q) := by
  rw [ambientRotation_apply, ambientRotation_apply,
    SpherePacking.fischer_polynomialInner_sub_left]
  rw [ambientCoordinateDerivation_polynomialInner,
    ambientCoordinateDerivation_polynomialInner,
    MetricCodes.Spherical.AssociatedOverlap.polynomialInner_sub_right]
  ring

theorem ambientRotation_rowAxisPolynomial {r n : ℕ}
    (a b : Fin n) (row : Fin (r + 1))
    (v : SpherePacking.Euclidean n) :
    ambientRotation (r := r) a b (rowAxisPolynomial row v) =
      rowAxisPolynomial row (euclideanAmbientRotation a b v) := by
  classical
  have hterm (c d k : Fin n) :
      ambientCoordinateDerivation (r := r) c d
          (MvPolynomial.C (v k) *
            MvPolynomial.X (variableIndex row k)) =
        MvPolynomial.C (v k) *
          (if d = k then MvPolynomial.X (variableIndex row c) else 0) := by
    rw [Derivation.leibniz, ambientCoordinateDerivation_X]
    simp only [smul_eq_mul, mul_ite, mul_zero, MvPolynomial.derivation_C, add_zero]
  have haxis (k : Fin n) :
      rowAxisPolynomial row (EuclideanSpace.basisFun (Fin n) ℝ k) =
        MvPolynomial.X (variableIndex row k) := by
    simp only [EuclideanSpace.basisFun_apply, rowAxisPolynomial_eq_sum, PiLp.single_apply,
      MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  have hsub (x y : SpherePacking.Euclidean n) :
      rowAxisPolynomial row (x - y) =
        rowAxisPolynomial row x - rowAxisPolynomial row y := by
    simp only [rowAxisPolynomial_eq_sum, PiLp.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [ambientRotation_apply, rowAxisPolynomial_eq_sum, map_sum, map_sum]
  simp_rw [hterm]
  simp only [mul_ite, mul_zero, ]
  rw [euclideanAmbientRotation_apply, hsub,
    rowAxisPolynomial_smul, rowAxisPolynomial_smul,
    haxis, haxis]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]

/-- The tensor ambient rotation used in the spherical-code argument. -/
def tensorAmbientRotation {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (a b : Fin n) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) mu) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) :=
  TensorProduct.map (euclideanAmbientRotation a b) LinearMap.id +
    TensorProduct.map LinearMap.id (youngAmbientRotation mu a b)

@[simp] theorem tensorAmbientRotation_tmul {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (a b : Fin n)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) mu) :
    tensorAmbientRotation mu a b (v ⊗ₜ[ℝ] p) =
      (euclideanAmbientRotation a b v) ⊗ₜ[ℝ] p +
        v ⊗ₜ[ℝ] (youngAmbientRotation mu a b p) := by
  simp only [tensorAmbientRotation, LinearMap.add_apply, TensorProduct.map_tmul,
    euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, LinearMap.id_coe, id_eq]

theorem tensorAmbientRotation_adjoint {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (a b : Fin n) :
    (tensorAmbientRotation mu a b).adjoint =
      -(tensorAmbientRotation mu a b) := by
  simp only [tensorAmbientRotation, map_add,
    TensorProduct.adjoint_map, LinearMap.adjoint_id,
    euclideanAmbientRotation_adjoint, youngAmbientRotation_adjoint]
  change
    (-(euclideanAmbientRotation a b)).rTensor
        (HarmonicYoungSpace (n := n) mu) +
      (-(youngAmbientRotation mu a b)).lTensor
        (SpherePacking.Euclidean n) =
      -((euclideanAmbientRotation a b).rTensor
          (HarmonicYoungSpace (n := n) mu) +
        (youngAmbientRotation mu a b).lTensor
          (SpherePacking.Euclidean n))
  rw [LinearMap.rTensor_neg, LinearMap.lTensor_neg]
  module

theorem projectedCoordinateRaise_rotation {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (a b : Fin n)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    youngAmbientRotation mu a b
        (projectedCoordinateRaise mu lam hdeg row v p) =
      projectedCoordinateRaise mu lam hdeg row
          (euclideanAmbientRotation a b v) p +
        projectedCoordinateRaise mu lam hdeg row v
          (youngAmbientRotation lam a b p) := by
  apply ext_inner_right ℝ
  intro q
  calc
    ⟪youngAmbientRotation mu a b
        (projectedCoordinateRaise mu lam hdeg row v p), q⟫_ℝ =
      -⟪projectedCoordinateRaise mu lam hdeg row v p,
        youngAmbientRotation mu a b q⟫_ℝ :=
      youngAmbientRotation_inner mu a b _ q
    _ = -SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (rowAxisPolynomial row v * (p : PolynomialSpace r n))
        (ambientRotation (r := r) a b (q : PolynomialSpace r n)) := by
      unfold projectedCoordinateRaise
      change
        -⟪youngHomogeneousProjection mu
            (rowAxisHomogeneous mu lam hdeg row v p),
          youngAmbientRotation mu a b q⟫_ℝ = _
      rw [youngHomogeneousProjection_inner]
      rfl
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (ambientRotation (r := r) a b
          (rowAxisPolynomial row v * (p : PolynomialSpace r n)))
        (q : PolynomialSpace r n) := by
      rw [ambientRotation_polynomialInner]
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (rowAxisPolynomial row (euclideanAmbientRotation a b v) *
            (p : PolynomialSpace r n) +
          rowAxisPolynomial row v *
            (youngAmbientRotation lam a b p : PolynomialSpace r n))
        (q : PolynomialSpace r n) := by
      congr 1
      rw [Derivation.leibniz, ambientRotation_rowAxisPolynomial]
      simp only [ambientRotation_apply, ambientCoordinateDerivation_apply, smul_eq_mul,
        euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply,
        youngAmbientRotation_apply_coe]
      ring
    _ = ⟪projectedCoordinateRaise mu lam hdeg row
          (euclideanAmbientRotation a b v) p +
        projectedCoordinateRaise mu lam hdeg row v
          (youngAmbientRotation lam a b p), q⟫_ℝ := by
      calc
        _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
              (rowAxisPolynomial row (euclideanAmbientRotation a b v) *
                (p : PolynomialSpace r n))
              (q : PolynomialSpace r n) +
            SpherePacking.Fischer.polynomialInner ((r + 1) * n)
              (rowAxisPolynomial row v *
                (youngAmbientRotation lam a b p : PolynomialSpace r n))
              (q : PolynomialSpace r n) :=
          SpherePacking.Fischer.polynomialInner_add_left _ _ _ _
        _ = ⟪projectedCoordinateRaise mu lam hdeg row
                (euclideanAmbientRotation a b v) p, q⟫_ℝ +
              ⟪projectedCoordinateRaise mu lam hdeg row v
                (youngAmbientRotation lam a b p), q⟫_ℝ := by
          congr 1
          · exact (youngHomogeneousProjection_inner mu
              (rowAxisHomogeneous mu lam hdeg row
                (euclideanAmbientRotation a b v) p) q).symm
          · exact (youngHomogeneousProjection_inner mu
              (rowAxisHomogeneous mu lam hdeg row v
                (youngAmbientRotation lam a b p)) q).symm
        _ = _ := (inner_add_left _ _ _).symm

theorem projectedCoordinateLower_rotation {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (a b : Fin n)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    youngAmbientRotation mu a b
        (projectedCoordinateLower mu lam hdeg row v p) =
      projectedCoordinateLower mu lam hdeg row
          (euclideanAmbientRotation a b v) p +
        projectedCoordinateLower mu lam hdeg row v
          (youngAmbientRotation lam a b p) := by
  have hpair (w : SpherePacking.Euclidean n)
      (x : HarmonicYoungSpace (n := n) lam)
      (z : HarmonicYoungSpace (n := n) mu) :
      ⟪projectedCoordinateLower mu lam hdeg row w x, z⟫_ℝ =
        ⟪x, projectedCoordinateRaise lam mu hdeg row w z⟫_ℝ := by
    calc
      ⟪projectedCoordinateLower mu lam hdeg row w x, z⟫_ℝ =
        ⟪z, projectedCoordinateLower mu lam hdeg row w x⟫_ℝ :=
        real_inner_comm _ _
      _ = ⟪projectedCoordinateRaise lam mu hdeg row w z, x⟫_ℝ :=
        (projectedCoordinateRaise_inner lam mu hdeg row w z x).symm
      _ = ⟪x, projectedCoordinateRaise lam mu hdeg row w z⟫_ℝ :=
        real_inner_comm _ _
  apply ext_inner_right ℝ
  intro q
  calc
    ⟪youngAmbientRotation mu a b
        (projectedCoordinateLower mu lam hdeg row v p), q⟫_ℝ =
      -⟪projectedCoordinateLower mu lam hdeg row v p,
        youngAmbientRotation mu a b q⟫_ℝ :=
      youngAmbientRotation_inner mu a b _ q
    _ = -⟪p, projectedCoordinateRaise lam mu hdeg row v
        (youngAmbientRotation mu a b q)⟫_ℝ := by
      rw [hpair]
    _ = ⟪youngAmbientRotation lam a b p,
          projectedCoordinateRaise lam mu hdeg row v q⟫_ℝ +
        ⟪p, projectedCoordinateRaise lam mu hdeg row
          (euclideanAmbientRotation a b v) q⟫_ℝ := by
      have hrotation :
          ⟪p, youngAmbientRotation lam a b
            (projectedCoordinateRaise lam mu hdeg row v q)⟫_ℝ =
            ⟪p, projectedCoordinateRaise lam mu hdeg row
              (euclideanAmbientRotation a b v) q⟫_ℝ +
            ⟪p, projectedCoordinateRaise lam mu hdeg row v
              (youngAmbientRotation mu a b q)⟫_ℝ := by
        calc
          _ = ⟪p,
              projectedCoordinateRaise lam mu hdeg row
                (euclideanAmbientRotation a b v) q +
              projectedCoordinateRaise lam mu hdeg row v
                (youngAmbientRotation mu a b q)⟫_ℝ := by
            rw [projectedCoordinateRaise_rotation]
          _ = _ := inner_add_right _ _ _
      have hskew := youngAmbientRotation_inner lam a b p
        (projectedCoordinateRaise lam mu hdeg row v q)
      linarith
    _ = ⟪projectedCoordinateLower mu lam hdeg row
          (euclideanAmbientRotation a b v) p +
        projectedCoordinateLower mu lam hdeg row v
          (youngAmbientRotation lam a b p), q⟫_ℝ := by
      calc
        _ = ⟪projectedCoordinateLower mu lam hdeg row v
              (youngAmbientRotation lam a b p), q⟫_ℝ +
            ⟪projectedCoordinateLower mu lam hdeg row
              (euclideanAmbientRotation a b v) p, q⟫_ℝ := by
          rw [hpair, hpair]
        _ = _ := by
          calc
            _ = ⟪projectedCoordinateLower mu lam hdeg row
                  (euclideanAmbientRotation a b v) p, q⟫_ℝ +
                ⟪projectedCoordinateLower mu lam hdeg row v
                  (youngAmbientRotation lam a b p), q⟫_ℝ := by
              ring
            _ = _ := (inner_add_left _ _ _).symm

theorem channel_rotation_intertwine_of_adjoint {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (T : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (a b : Fin n)
    (hT : ∀ (v : SpherePacking.Euclidean n)
        (q : HarmonicYoungSpace (n := n) mu),
      youngAmbientRotation lam a b (T.adjoint (v ⊗ₜ[ℝ] q)) =
        T.adjoint (tensorAmbientRotation mu a b (v ⊗ₜ[ℝ] q))) :
    T.comp (youngAmbientRotation lam a b) =
      (tensorAmbientRotation mu a b).comp T := by
  apply LinearMap.ext
  intro p
  apply TensorProduct.ext_iff_inner_right.mpr
  intro v q
  change
    ⟪T (youngAmbientRotation lam a b p), v ⊗ₜ[ℝ] q⟫_ℝ =
      ⟪tensorAmbientRotation mu a b (T p), v ⊗ₜ[ℝ] q⟫_ℝ
  calc
    ⟪T (youngAmbientRotation lam a b p), v ⊗ₜ[ℝ] q⟫_ℝ =
      ⟪youngAmbientRotation lam a b p,
        T.adjoint (v ⊗ₜ[ℝ] q)⟫_ℝ :=
      (LinearMap.adjoint_inner_right T
        (youngAmbientRotation lam a b p) (v ⊗ₜ[ℝ] q)).symm
    _ = -⟪p, youngAmbientRotation lam a b
      (T.adjoint (v ⊗ₜ[ℝ] q))⟫_ℝ :=
      youngAmbientRotation_inner lam a b p _
    _ = -⟪p, T.adjoint
      (tensorAmbientRotation mu a b (v ⊗ₜ[ℝ] q))⟫_ℝ := by
      rw [hT]
    _ = -⟪T p, tensorAmbientRotation mu a b
      (v ⊗ₜ[ℝ] q)⟫_ℝ := by
      exact congrArg Neg.neg
        (LinearMap.adjoint_inner_right T p
          (tensorAmbientRotation mu a b (v ⊗ₜ[ℝ] q)))
    _ = ⟪T p,
      (tensorAmbientRotation mu a b).adjoint
        (v ⊗ₜ[ℝ] q)⟫_ℝ := by
      rw [tensorAmbientRotation_adjoint]
      exact (inner_neg_right (T p)
        (tensorAmbientRotation mu a b (v ⊗ₜ[ℝ] q))).symm
    _ = ⟪tensorAmbientRotation mu a b (T p), v ⊗ₜ[ℝ] q⟫_ℝ :=
      LinearMap.adjoint_inner_right (tensorAmbientRotation mu a b)
        (T p) (v ⊗ₜ[ℝ] q)

theorem youngClebschRaise_rotation_intertwine {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (a b : Fin n) :
    (youngClebschRaise mu lam hdeg row).comp
        (youngAmbientRotation lam a b) =
      (tensorAmbientRotation mu a b).comp
        (youngClebschRaise mu lam hdeg row) := by
  apply channel_rotation_intertwine_of_adjoint mu lam _ a b
  intro v q
  rw [youngClebschRaise_adjoint_tmul,
    tensorAmbientRotation_tmul, map_add,
    youngClebschRaise_adjoint_tmul,
    youngClebschRaise_adjoint_tmul]
  exact projectedCoordinateLower_rotation lam mu hdeg row a b v q

theorem youngClebschLower_rotation_intertwine {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (a b : Fin n) :
    (youngClebschLower mu lam hdeg row).comp
        (youngAmbientRotation lam a b) =
      (tensorAmbientRotation mu a b).comp
        (youngClebschLower mu lam hdeg row) := by
  apply channel_rotation_intertwine_of_adjoint mu lam _ a b
  intro v q
  rw [youngClebschLower_adjoint_tmul,
    tensorAmbientRotation_tmul, map_add,
    youngClebschLower_adjoint_tmul,
    youngClebschLower_adjoint_tmul]
  exact projectedCoordinateRaise_rotation lam mu hdeg row a b v q

end ClebschRotation

namespace TwoRowAxisChannelCoherence

open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankClebschBranchCoherence
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres

private def phaseNegatedChannel
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗᵢ[ℝ] F) : E →ₗᵢ[ℝ] F :=
  A.comp (LinearIsometryEquiv.neg ℝ).toLinearIsometry

@[simp] theorem phaseNegatedChannel_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗᵢ[ℝ] F) (x : E) :
    phaseNegatedChannel A x = -A x := by
  change A (-x) = -A x
  exact A.map_neg x

@[simp] theorem phaseNegatedChannel_toLinearMap
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗᵢ[ℝ] F) :
    (phaseNegatedChannel A).toLinearMap = (-1 : ℝ) • A.toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearIsometry.coe_toLinearMap, phaseNegatedChannel_apply, neg_smul, one_smul,
    LinearMap.neg_apply]

theorem phaseNegatedChannel_adjoint_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗᵢ[ℝ] F) (y : F) :
    (phaseNegatedChannel A).adjoint y = -A.adjoint y := by
  apply ext_inner_left ℝ
  intro x
  calc
    ⟪x, (phaseNegatedChannel A).adjoint y⟫_ℝ =
        ⟪phaseNegatedChannel A x, y⟫_ℝ :=
      LinearMap.adjoint_inner_right
        (phaseNegatedChannel A).toLinearMap x y
    _ = -⟪A x, y⟫_ℝ := by simp only [phaseNegatedChannel_apply, inner_neg_left]
    _ = -⟪x, A.adjoint y⟫_ℝ := by
      rw [LinearMap.adjoint_inner_right A.toLinearMap]
      rfl
    _ = ⟪x, -A.adjoint y⟫_ℝ := by simp only [inner_neg_right]

end TwoRowAxisChannelCoherence

end

namespace MixedSignature

section


open scoped BigOperators InnerProductSpace

/-- The young ambient casimir used in the spherical-code argument. -/
def youngAmbientCasimir {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam :=
  (2 : ℝ)⁻¹ •
    ∑ a : Fin n, ∑ b : Fin n,
      -((youngAmbientRotation lam a b).comp
        (youngAmbientRotation lam a b))

private def ambientCasimirPolynomial {r n : ℕ} (p : PolynomialSpace r n) :
    PolynomialSpace r n :=
  (2 : ℝ)⁻¹ •
    ∑ a : Fin n, ∑ b : Fin n,
      -(ambientRotation (r := r) a b
        (ambientRotation (r := r) a b p))

@[simp] theorem youngAmbientCasimir_apply_coe {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) :
    ((youngAmbientCasimir lam p : HarmonicYoungSpace lam) :
      PolynomialSpace r n) = ambientCasimirPolynomial
        (p : PolynomialSpace r n) := by
  simp only [youngAmbientCasimir, ambientCasimirPolynomial,
    LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.neg_apply, LinearMap.comp_apply,
    Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_neg,
    youngAmbientRotation_apply_coe]

theorem ambientCasimirPolynomial_eq_coordinateDerivations {r n : ℕ}
    (p : PolynomialSpace r n) :
    ambientCasimirPolynomial p =
      (∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) a b
          (ambientCoordinateDerivation (r := r) b a p)) -
      (∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) a b
          (ambientCoordinateDerivation (r := r) a b p)) := by
  classical
  have hsame :
      (∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) b a
          (ambientCoordinateDerivation (r := r) b a p)) =
      ∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) a b
          (ambientCoordinateDerivation (r := r) a b p) := by
    rw [Finset.sum_comm]
  have hcross :
      (∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) b a
          (ambientCoordinateDerivation (r := r) a b p)) =
      ∑ a : Fin n, ∑ b : Fin n,
        ambientCoordinateDerivation (r := r) a b
          (ambientCoordinateDerivation (r := r) b a p) := by
    rw [Finset.sum_comm]
  unfold ambientCasimirPolynomial
  simp only [ambientRotation_apply, Derivation.map_sub, neg_sub]
  simp_rw [Finset.sum_sub_distrib]
  rw [hsame, hcross]
  module

theorem ambientCoordinateDerivation_comp_apply_diagonal
    {r n : ℕ} (a b c d : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r) a b
        (ambientCoordinateDerivation (r := r) c d p) =
      (if b = c then ambientCoordinateDerivation (r := r) a d p else 0) +
        ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j c) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j d) p) := by
  classical
  rw [ambientCoordinateDerivation_apply c d, map_sum]
  simp_rw [Derivation.leibniz, ambientCoordinateDerivation_X,
    ambientCoordinateDerivation_apply]
  by_cases h : b = c
  · subst c
    simp only [ite_true, smul_eq_mul, Finset.sum_add_distrib]
    have hdelta :
        (∑ j : Fin (r + 1),
          MvPolynomial.pderiv (variableIndex j d) p *
            MvPolynomial.X (variableIndex j a)) =
          ∑ i : Fin (r + 1),
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i d) p := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsecond :
        (∑ j : Fin (r + 1),
          MvPolynomial.X (variableIndex j b) *
            ∑ i : Fin (r + 1),
              MvPolynomial.X (variableIndex i a) *
                MvPolynomial.pderiv (variableIndex i b)
                  (MvPolynomial.pderiv (variableIndex j d) p)) =
        ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j b) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j d) p) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdelta, hsecond]
    abel
  · simp only [h, ite_false, smul_eq_mul, mul_zero, add_zero,
      zero_add]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem ambientCoordinateDerivation_sum_same {r n : ℕ}
    (p : PolynomialSpace r n) :
    (∑ a : Fin n, ∑ b : Fin n,
      ambientCoordinateDerivation (r := r) a b
        (ambientCoordinateDerivation (r := r) a b p)) =
      (∑ i : Fin (r + 1), rowEuler r n i p) +
        ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          rowPairingPolynomial (n := n) i j *
            traceOperator r n i j p := by
  classical
  simp_rw [ambientCoordinateDerivation_comp_apply_diagonal]
  simp_rw [Finset.sum_add_distrib]
  have heuler :
      (∑ a : Fin n, ∑ b : Fin n,
        if b = a then ambientCoordinateDerivation (r := r) a b p
        else 0) =
        ∑ i : Fin (r + 1), rowEuler r n i p := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ambientCoordinateDerivation_apply, rowEuler_apply]
    rw [Finset.sum_comm]
  rw [heuler]
  congr 1
  calc
    (∑ a : Fin n, ∑ b : Fin n,
      ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        MvPolynomial.X (variableIndex i a) *
          MvPolynomial.X (variableIndex j a) *
            MvPolynomial.pderiv (variableIndex i b)
              (MvPolynomial.pderiv (variableIndex j b) p)) =
      ∑ a : Fin n, ∑ i : Fin (r + 1),
        ∑ b : Fin n, ∑ j : Fin (r + 1),
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j b) p) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ a : Fin n,
        ∑ b : Fin n, ∑ j : Fin (r + 1),
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j b) p) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ a : Fin n,
        ∑ j : Fin (r + 1), ∑ b : Fin n,
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j b) p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        ∑ a : Fin n, ∑ b : Fin n,
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.X (variableIndex j a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.pderiv (variableIndex j b) p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        rowPairingPolynomial (n := n) i j *
          traceOperator r n i j p := by
      simp only [rowPairingPolynomial, traceOperator_apply,
        Finset.sum_mul, Finset.mul_sum, mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

end

section


open scoped BigOperators InnerProductSpace

theorem polarization_cross_square_expand {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n i j (polarization r n j i p) =
      rowEuler r n i p +
        ∑ a : Fin n,
          MvPolynomial.X (variableIndex i a) *
            polarization r n j i
              (MvPolynomial.pderiv (variableIndex j a) p) := by
  rw [polarization_apply]
  simp_rw [pderiv_polarization_harmonicLift]
  simp only [ite_true, mul_add, Finset.sum_add_distrib]
  rw [← rowEuler_apply]

theorem ambientCoordinateCrossPair {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    (∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.X (variableIndex i a) *
        MvPolynomial.pderiv (variableIndex i b)
          (MvPolynomial.X (variableIndex j b) *
            MvPolynomial.pderiv (variableIndex j a) p)) =
      (if i = j then (n : ℝ) • rowEuler r n i p else 0) +
        polarization r n i j (polarization r n j i p) -
          rowEuler r n i p := by
  have hpol := polarization_cross_square_expand i j p
  have hrem :
      (∑ a : Fin n, ∑ b : Fin n,
        MvPolynomial.X (variableIndex i a) *
          (MvPolynomial.X (variableIndex j b) *
            MvPolynomial.pderiv (variableIndex i b)
              (MvPolynomial.pderiv (variableIndex j a) p))) =
        ∑ a : Fin n,
          MvPolynomial.X (variableIndex i a) *
            polarization r n j i
              (MvPolynomial.pderiv (variableIndex j a) p) := by
    simp only [polarization_apply, Finset.mul_sum]
  by_cases hij : i = j
  · subst j
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, ↓reduceIte, one_mul, mul_add,
      Finset.sum_add_distrib]
    have hfirst :
        (∑ a : Fin n, ∑ _b : Fin n,
          MvPolynomial.X (variableIndex i a) *
            MvPolynomial.pderiv (variableIndex i a) p) =
          (n : ℝ) • rowEuler r n i p := by
      rw [rowEuler_apply]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.smul_sum, Nat.cast_smul_eq_nsmul]
    rw [hfirst, hrem, hpol]
    abel
  · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, variableIndex_eq_iff_harmonicLift,
      hij, Ne.symm hij, false_and, ↓reduceIte, zero_mul, zero_add,
      zero_add]
    rw [hrem, hpol]
    abel

theorem ambientCoordinateDerivation_sum_swap_eq_rowPolarizations
    {r n : ℕ} (p : PolynomialSpace r n) :
    (∑ a : Fin n, ∑ b : Fin n,
      ambientCoordinateDerivation (r := r) a b
        (ambientCoordinateDerivation (r := r) b a p)) =
      ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        ((if i = j then (n : ℝ) • rowEuler r n i p else 0) +
          polarization r n i j (polarization r n j i p) -
            rowEuler r n i p) := by
  calc
    (∑ a : Fin n, ∑ b : Fin n,
      ambientCoordinateDerivation (r := r) a b
        (ambientCoordinateDerivation (r := r) b a p)) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.X (variableIndex j b) *
                  MvPolynomial.pderiv (variableIndex j a) p) := by
      simp only [ambientCoordinateDerivation_apply, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a : Fin n, ∑ i : Fin (r + 1),
          ∑ b : Fin n, ∑ j : Fin (r + 1),
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.X (variableIndex j b) *
                  MvPolynomial.pderiv (variableIndex j a) p) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ a : Fin n,
          ∑ b : Fin n, ∑ j : Fin (r + 1),
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.X (variableIndex j b) *
                  MvPolynomial.pderiv (variableIndex j a) p) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ a : Fin n,
          ∑ j : Fin (r + 1), ∑ b : Fin n,
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.X (variableIndex j b) *
                  MvPolynomial.pderiv (variableIndex j a) p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          ∑ a : Fin n, ∑ b : Fin n,
            MvPolynomial.X (variableIndex i a) *
              MvPolynomial.pderiv (variableIndex i b)
                (MvPolynomial.X (variableIndex j b) *
                  MvPolynomial.pderiv (variableIndex j a) p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [ambientCoordinateCrossPair]

theorem ambientCasimirPolynomial_eq_rowHowe {r n : ℕ}
    (p : PolynomialSpace r n) :
    ambientCasimirPolynomial p =
      (((n : ℝ) - (r : ℝ) - 2) •
        (∑ i : Fin (r + 1), rowEuler r n i p)) +
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        polarization r n i j (polarization r n j i p)) -
      ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        rowPairingPolynomial (n := n) i j *
          traceOperator r n i j p := by
  classical
  rw [ambientCasimirPolynomial_eq_coordinateDerivations,
    ambientCoordinateDerivation_sum_swap_eq_rowPolarizations,
    ambientCoordinateDerivation_sum_same]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdiagonal :
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i = j then (n : ℝ) • rowEuler r n i p else 0) =
      (n : ℝ) • (∑ i : Fin (r + 1), rowEuler r n i p) := by
    simp only [rowEuler_apply, Finset.smul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hrepeat :
      (∑ i : Fin (r + 1), ∑ _j : Fin (r + 1),
        rowEuler r n i p) =
      ((r + 1 : ℕ) : ℝ) •
        (∑ i : Fin (r + 1), rowEuler r n i p) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_smul_eq_nsmul]
  rw [hdiagonal, hrepeat]
  push_cast
  module

end

section


open scoped BigOperators InnerProductSpace

private def IsYoungAmbientRotationIntertwiner {r n : ℕ}
    (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu) : Prop :=
  ∀ a b : Fin n,
    A.comp (youngAmbientRotation lam a b) =
      (youngAmbientRotation mu a b).comp A

theorem youngAmbientRotationIntertwiner_square
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu)
    (hA : IsYoungAmbientRotationIntertwiner lam mu A)
    (a b : Fin n) :
    A.comp ((youngAmbientRotation lam a b).comp
      (youngAmbientRotation lam a b)) =
      ((youngAmbientRotation mu a b).comp
        (youngAmbientRotation mu a b)).comp A := by
  calc
    A.comp ((youngAmbientRotation lam a b).comp
        (youngAmbientRotation lam a b)) =
      (A.comp (youngAmbientRotation lam a b)).comp
        (youngAmbientRotation lam a b) := by
          rw [LinearMap.comp_assoc]
    _ = ((youngAmbientRotation mu a b).comp A).comp
        (youngAmbientRotation lam a b) := by rw [hA a b]
    _ = (youngAmbientRotation mu a b).comp
        (A.comp (youngAmbientRotation lam a b)) := by
          rw [LinearMap.comp_assoc]
    _ = (youngAmbientRotation mu a b).comp
        ((youngAmbientRotation mu a b).comp A) := by rw [hA a b]
    _ = ((youngAmbientRotation mu a b).comp
        (youngAmbientRotation mu a b)).comp A := by
          rw [LinearMap.comp_assoc]

theorem linearMap_eq_zero_of_distinct_scalar_intertwining
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] E) (C : F →ₗ[ℝ] F)
    (c d : ℝ) (hcomm : A.comp B = C.comp A)
    (hB : B = c • LinearMap.id)
    (hC : C = d • LinearMap.id)
    (hne : c ≠ d) : A = 0 := by
  ext v
  have h := LinearMap.congr_fun hcomm v
  rw [hB, hC] at h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul] at h
  have hscalar : (c - d) • A v = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hne)

end

end MixedSignature

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace CrossGram

theorem adjoint_intertwines_of_skew
    {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G]
    (A : E →ₗ[ℝ] G)
    (R : E →ₗ[ℝ] E) (S : G →ₗ[ℝ] G)
    (hR : R.adjoint = -R)
    (hS : S.adjoint = -S)
    (hA : A.comp R = S.comp A) :
    A.adjoint.comp S = R.comp A.adjoint := by
  have h := congrArg LinearMap.adjoint hA
  simp only [LinearMap.adjoint_comp, hR, hS] at h
  have h' : -(R.comp A.adjoint) = -(A.adjoint.comp S) := by
    simpa only [neg_inj, LinearMap.neg_comp, LinearMap.comp_neg] using h
  exact neg_injective h'.symm

theorem crossGram_intertwines_of_skew
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G)
    (R : E →ₗ[ℝ] E) (T : F →ₗ[ℝ] F) (S : G →ₗ[ℝ] G)
    (hR : R.adjoint = -R)
    (hS : S.adjoint = -S)
    (hA : A.comp R = S.comp A)
    (hB : B.comp T = S.comp B) :
    (A.adjoint.comp B).comp T = R.comp (A.adjoint.comp B) := by
  calc
    (A.adjoint.comp B).comp T = A.adjoint.comp (B.comp T) := by
      rw [LinearMap.comp_assoc]
    _ = A.adjoint.comp (S.comp B) := by rw [hB]
    _ = (A.adjoint.comp S).comp B := by rw [LinearMap.comp_assoc]
    _ = (R.comp A.adjoint).comp B := by
      rw [adjoint_intertwines_of_skew A R S hR hS hA]
    _ = R.comp (A.adjoint.comp B) := by rw [LinearMap.comp_assoc]

theorem young_crossGram_rotation_intertwine
    {r n : ℕ}
    (lam nu mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (B : HarmonicYoungSpace (n := n) nu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (S : (a b : Fin n) →
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (hS : ∀ a b, (S a b).adjoint = -(S a b))
    (hA : ∀ a b,
      A.comp (MixedSignature.youngAmbientRotation lam a b) =
        (S a b).comp A)
    (hB : ∀ a b,
      B.comp (MixedSignature.youngAmbientRotation nu a b) =
        (S a b).comp B)
    (a b : Fin n) :
    (A.adjoint.comp B).comp
        (MixedSignature.youngAmbientRotation nu a b) =
      (MixedSignature.youngAmbientRotation lam a b).comp
        (A.adjoint.comp B) :=
  crossGram_intertwines_of_skew A B
    (MixedSignature.youngAmbientRotation lam a b)
    (MixedSignature.youngAmbientRotation nu a b)
    (S a b)
    (MixedSignature.youngAmbientRotation_adjoint lam a b)
    (hS a b) (hA a b) (hB a b)

end CrossGram

end

section


open scoped BigOperators InnerProductSpace TensorProduct
open MixedSignature

theorem boundaryYoungRotationIntertwiner_casimir
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu)
    (hA : IsYoungAmbientRotationIntertwiner lam mu A) :
    A.comp (youngAmbientCasimir (n := n) lam) =
      (youngAmbientCasimir (n := n) mu).comp A := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, youngAmbientCasimir,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.neg_apply,
    map_smul, map_sum, map_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact LinearMap.congr_fun
    (youngAmbientRotationIntertwiner_square lam mu A hA a b) p

theorem boundaryYoungRotationIntertwiner_eq_zero_of_distinctCasimir
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu)
    (hA : IsYoungAmbientRotationIntertwiner lam mu A)
    (c d : ℝ)
    (hcasimirLam : youngAmbientCasimir (n := n) lam = c • LinearMap.id)
    (hcasimirMu : youngAmbientCasimir (n := n) mu = d • LinearMap.id)
    (hdistinct : c ≠ d) : A = 0 :=
  linearMap_eq_zero_of_distinct_scalar_intertwining
    A (youngAmbientCasimir (n := n) lam)
    (youngAmbientCasimir (n := n) mu) c d
    (boundaryYoungRotationIntertwiner_casimir lam mu A hA)
    hcasimirLam hcasimirMu hdistinct

theorem boundaryYoungChannel_crossGram_eq_zero_of_distinctCasimir
    {r n : ℕ} (lam nu mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (B : HarmonicYoungSpace (n := n) nu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (S : (a b : Fin n) →
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (hS : ∀ a b, (S a b).adjoint = -(S a b))
    (hA : ∀ a b,
      A.comp (youngAmbientRotation lam a b) = (S a b).comp A)
    (hB : ∀ a b,
      B.comp (youngAmbientRotation nu a b) = (S a b).comp B)
    (c d : ℝ)
    (hcasimirLam : youngAmbientCasimir (n := n) lam = c • LinearMap.id)
    (hcasimirNu : youngAmbientCasimir (n := n) nu = d • LinearMap.id)
    (hdistinct : c ≠ d) :
    A.adjoint.comp B = 0 := by
  apply boundaryYoungRotationIntertwiner_eq_zero_of_distinctCasimir
    nu lam (A.adjoint.comp B) ?_ d c
    hcasimirNu hcasimirLam (Ne.symm hdistinct)
  intro a b
  exact CrossGram.young_crossGram_rotation_intertwine
    lam nu mu A B S hS hA hB a b

theorem boundaryYoungChannel_smul_rotation_intertwine
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (S : (a b : Fin n) →
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (hA : ∀ a b,
      A.comp (youngAmbientRotation lam a b) = (S a b).comp A)
    (c : ℝ) (a b : Fin n) :
    (c • A).comp (youngAmbientRotation lam a b) =
      (S a b).comp (c • A) := by
  rw [LinearMap.smul_comp, LinearMap.comp_smul, hA a b]

theorem boundaryNormalizedYoungClebschRaise_rotation_intertwine
    {r n : ℕ} (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschRaise mu lam hdeg row p,
        youngClebschRaise mu lam hdeg row q⟫_ℝ = c * ⟪p, q⟫_ℝ)
    (a b : Fin n) :
    (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).toLinearMap.comp
        (youngAmbientRotation lam a b) =
      (ClebschRotation.tensorAmbientRotation mu a b).comp
        (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).toLinearMap := by
  rw [normalizedYoungClebschRaise_toLinearMap]
  exact boundaryYoungChannel_smul_rotation_intertwine
    lam mu (youngClebschRaise mu lam hdeg row)
    (ClebschRotation.tensorAmbientRotation mu)
    (ClebschRotation.youngClebschRaise_rotation_intertwine mu lam hdeg row)
    (Real.sqrt c)⁻¹ a b

theorem boundaryNormalizedYoungClebschLower_rotation_intertwine
    {r n : ℕ} (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschLower mu lam hdeg row p,
        youngClebschLower mu lam hdeg row q⟫_ℝ = c * ⟪p, q⟫_ℝ)
    (a b : Fin n) :
    (normalizedYoungClebschLower mu lam hdeg row c hc hgram).toLinearMap.comp
        (youngAmbientRotation lam a b) =
      (ClebschRotation.tensorAmbientRotation mu a b).comp
        (normalizedYoungClebschLower mu lam hdeg row c hc hgram).toLinearMap := by
  rw [normalizedYoungClebschLower_toLinearMap]
  exact boundaryYoungChannel_smul_rotation_intertwine
    lam mu (youngClebschLower mu lam hdeg row)
    (ClebschRotation.tensorAmbientRotation mu)
    (ClebschRotation.youngClebschLower_rotation_intertwine mu lam hdeg row)
    (Real.sqrt c)⁻¹ a b

end

namespace MixedSignature

section


open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching

/-- The all rank casimir eigenvalue used in the spherical-code argument. -/
def allRankCasimirEigenvalue {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℝ :=
  ∑ i : Fin (r + 1),
    (lam i : ℝ) * ((lam i : ℝ) + (n : ℝ) - 2 - 2 * (i.val : ℝ))

theorem polarization_opposite_on_harmonicYoung
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam)
    (i j : Fin (r + 1)) :
    polarization r n i j
        (polarization r n j i (p : PolynomialSpace r n)) =
      (if i = j then (lam i : ℝ) ^ 2
       else if i < j then (lam i : ℝ) - (lam j : ℝ)
       else 0) • (p : PolynomialSpace r n) := by
  have hp := (mem_harmonicYoungSubmodule lam
    (p : PolynomialSpace r n)).mp p.property
  rcases lt_trichotomy i j with hij | hij | hij
  · have hupp : polarization r n i j
        (p : PolynomialSpace r n) = 0 := hp.2.2.2 i j hij
    have hcomm := polarization_polarization_commutator
      i j j i (p : PolynomialSpace r n)
    simp only [ite_true, polarization_self, hupp, map_zero,
      zero_add, hp.2.1] at hcomm
    simp only [hij.ne, hij, ite_false, ite_true]
    rw [sub_smul]
    exact hcomm
  · subst j
    simp only [ite_true, polarization_self, hp.2.1,
      map_smul, smul_smul, pow_two]
  · have hupp : polarization r n j i
        (p : PolynomialSpace r n) = 0 := hp.2.2.2 j i hij
    simp only [hupp, map_zero, hij.ne',
      ↓reduceIte, not_lt_of_gt hij, zero_smul]

theorem sum_upper_row_differences
    {r : ℕ} (f : Fin (r + 1) → ℝ) :
    (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      if i < j then f i - f j else 0) =
      ∑ i : Fin (r + 1),
        ((r : ℝ) - 2 * (i.val : ℝ)) * f i := by
  classical
  have hsplit :
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i < j then f i - f j else 0) =
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i < j then f i else 0) -
      (∑ j : Fin (r + 1), ∑ i : Fin (r + 1),
        if i < j then f j else 0) := by
    calc
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i < j then f i - f j else 0) =
        (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          if i < j then f i else 0) -
        (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
          if i < j then f j else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by
        congr 1
        rw [Finset.sum_comm]
  rw [hsplit, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hgreater :
      (∑ j : Fin (r + 1), if i < j then f i else 0) =
        ((r - i.val : ℕ) : ℝ) * f i := by
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.univ.filter (fun j : Fin (r + 1) => i < j)) =
          Finset.Ioi i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    rw [hfilter, Finset.sum_const, Fin.card_Ioi]
    simp only [add_tsub_cancel_right, nsmul_eq_mul]
  have hless :
      (∑ j : Fin (r + 1), if j < i then f i else 0) =
        (i.val : ℝ) * f i := by
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.univ.filter (fun j : Fin (r + 1) => j < i)) =
          Finset.Iio i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [hfilter, Finset.sum_const, Fin.card_Iio]
    simp only [nsmul_eq_mul]
  rw [hgreater, hless]
  have hi : i.val ≤ r := by omega
  rw [Nat.cast_sub hi]
  ring

theorem polarization_opposite_sum_on_harmonicYoung
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) :
    (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      polarization r n i j
        (polarization r n j i (p : PolynomialSpace r n))) =
      (∑ i : Fin (r + 1),
        ((lam i : ℝ) ^ 2 +
          ((r : ℝ) - 2 * (i.val : ℝ)) * (lam i : ℝ))) •
        (p : PolynomialSpace r n) := by
  simp_rw [polarization_opposite_on_harmonicYoung lam p]
  simp_rw [← Finset.sum_smul]
  congr 1
  have hdiag :
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i = j then (lam i : ℝ) ^ 2
        else if i < j then (lam i : ℝ) - (lam j : ℝ)
        else 0) =
      (∑ i : Fin (r + 1), (lam i : ℝ) ^ 2) +
      (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
        if i < j then (lam i : ℝ) - (lam j : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsplit :
        (∑ j : Fin (r + 1),
          if i = j then (lam i : ℝ) ^ 2
          else if i < j then (lam i : ℝ) - (lam j : ℝ)
          else 0) =
          (∑ j : Fin (r + 1),
            if i = j then (lam i : ℝ) ^ 2 else 0) +
          (∑ j : Fin (r + 1),
            if i < j then (lam i : ℝ) - (lam j : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases heq : i = j
      · simp only [heq, ↓reduceIte, lt_self_iff_false, add_zero]
      · simp only [heq, ↓reduceIte, zero_add]
    rw [hsplit]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hdiag, sum_upper_row_differences]
  rw [← Finset.sum_add_distrib]

theorem youngAmbientCasimir_allRank_eq_smul_id
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    youngAmbientCasimir (n := n) lam =
      allRankCasimirEigenvalue n lam • LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [youngAmbientCasimir_apply_coe,
    LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  rw [ambientCasimirPolynomial_eq_rowHowe,
    polarization_opposite_sum_on_harmonicYoung lam p]
  have hp := (mem_harmonicYoungSubmodule lam
    (p : PolynomialSpace r n)).mp p.property
  simp_rw [hp.2.2.1, mul_zero]
  simp only [Finset.sum_const_zero, sub_zero]
  have heuler :
      (∑ i : Fin (r + 1), rowEuler r n i
        (p : PolynomialSpace r n)) =
        (∑ i : Fin (r + 1), (lam i : ℝ)) •
          (p : PolynomialSpace r n) := by
    simp_rw [hp.2.1, ← Finset.sum_smul]
  rw [heuler, smul_smul, ← add_smul]
  congr 1
  unfold allRankCasimirEigenvalue
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

section


open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherChannel

/-- The adjacent casimir eigenvalue used in the spherical-code argument. -/
def adjacentCasimirEigenvalue {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℝ :=
  ∑ row : Fin (r + 1),
    (lam row : ℝ) *
      ((lam row : ℝ) + (n : ℝ) - 2 - 2 * (row.val : ℝ))

theorem adjacentCasimirEigenvalue_raiseWeight {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    adjacentCasimirEigenvalue n (raiseWeight lam row) =
      adjacentCasimirEigenvalue n lam +
        (2 * (lam row : ℝ) + (n : ℝ) - 1 - 2 * (row.val : ℝ)) := by
  classical
  unfold adjacentCasimirEigenvalue
  rw [← Finset.add_sum_erase Finset.univ
      (fun i : Fin (r + 1) =>
        ((raiseWeight lam row i : ℕ) : ℝ) *
          (((raiseWeight lam row i : ℕ) : ℝ) +
            (n : ℝ) - 2 - 2 * (i.val : ℝ)))
      (Finset.mem_univ row),
    ← Finset.add_sum_erase Finset.univ
      (fun i : Fin (r + 1) =>
        (lam i : ℝ) *
          ((lam i : ℝ) + (n : ℝ) - 2 - 2 * (i.val : ℝ)))
      (Finset.mem_univ row)]
  have hrest :
      (∑ i ∈ Finset.univ.erase row,
        ((raiseWeight lam row i : ℕ) : ℝ) *
          (((raiseWeight lam row i : ℕ) : ℝ) +
            (n : ℝ) - 2 - 2 * (i.val : ℝ))) =
      ∑ i ∈ Finset.univ.erase row,
        (lam i : ℝ) *
          ((lam i : ℝ) + (n : ℝ) - 2 - 2 * (i.val : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ row := (Finset.mem_erase.mp hi).1
    simp only [raiseWeight, ne_eq, hne, not_false_eq_true, Function.update_of_ne]
  rw [hrest]
  simp only [raiseWeight, Function.update_self, Nat.cast_add, Nat.cast_one, Finset.mem_univ,
    Finset.sum_erase_eq_sub, add_sub_cancel]
  ring

/-- The predicate asserting all rank one box neighbor. -/
def IsAllRankOneBoxNeighbor {r : ℕ}
    (target source : Fin (r + 1) → ℕ) : Prop :=
  ∃ row : Fin (r + 1),
    source = raiseWeight target row ∨ target = raiseWeight source row

theorem adjacentCasimirEigenvalue_raiseWeight_lt {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (hdominant : Antitone target)
    (i j : Fin (r + 1)) (hij : i < j) :
    adjacentCasimirEigenvalue n (raiseWeight target j) <
      adjacentCasimirEigenvalue n (raiseWeight target i) := by
  rw [adjacentCasimirEigenvalue_raiseWeight,
    adjacentCasimirEigenvalue_raiseWeight]
  have hrows : (target j : ℝ) ≤ target i := by
    exact_mod_cast hdominant (le_of_lt hij)
  have hindices : (i.val : ℝ) < j.val := by
    exact_mod_cast hij
  linarith

theorem adjacentCasimirEigenvalue_raiseWeight_ne {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (hdominant : Antitone target)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    adjacentCasimirEigenvalue n (raiseWeight target i) ≠
      adjacentCasimirEigenvalue n (raiseWeight target j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ne_of_gt
      (adjacentCasimirEigenvalue_raiseWeight_lt target hdominant i j hlt)
  · exact ne_of_lt
      (adjacentCasimirEigenvalue_raiseWeight_lt target hdominant j i hgt)

theorem raiseWeight_injective_fixed_row {r : ℕ}
    (row : Fin (r + 1)) :
    Function.Injective (fun lam : Fin (r + 1) → ℕ =>
      raiseWeight lam row) := by
  intro lam mu heq
  funext i
  have hi := congrFun heq i
  by_cases h : i = row
  · subst i
    simpa only using Nat.add_right_cancel (show lam row + 1 = mu row + 1 by simpa [raiseWeight]
      using hi)
  · simpa only [raiseWeight, ne_eq, h, not_false_eq_true, Function.update_of_ne] using hi

theorem adjacentCasimirEigenvalue_lowerWeight_lt {r n : ℕ}
    (target source source' : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (i j : Fin (r + 1)) (hij : i < j)
    (hi : target = raiseWeight source i)
    (hj : target = raiseWeight source' j) :
    adjacentCasimirEigenvalue n source <
      adjacentCasimirEigenvalue n source' := by
  have hci := adjacentCasimirEigenvalue_raiseWeight n source i
  have hcj := adjacentCasimirEigenvalue_raiseWeight n source' j
  rw [← hi] at hci
  rw [← hj] at hcj
  have hti : target i = source i + 1 := by
    simpa only [raiseWeight, Function.update_self] using congrFun hi i
  have htj : target j = source' j + 1 := by
    simpa only [raiseWeight, Function.update_self] using congrFun hj j
  have htir : (target i : ℝ) = (source i : ℝ) + 1 := by
    exact_mod_cast hti
  have htjr : (target j : ℝ) = (source' j : ℝ) + 1 := by
    exact_mod_cast htj
  have hrows : (target j : ℝ) ≤ target i := by
    exact_mod_cast hdominant (le_of_lt hij)
  have hindices : (i.val : ℝ) < j.val := by
    exact_mod_cast hij
  linarith

theorem adjacentCasimirEigenvalue_lower_lt_raise {r n : ℕ}
    (hn : 2 * r + 2 ≤ n)
    (target source : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1))
    (hsource : target = raiseWeight source j) :
    adjacentCasimirEigenvalue n source <
      adjacentCasimirEigenvalue n (raiseWeight target i) := by
  have hsourceC := adjacentCasimirEigenvalue_raiseWeight n source j
  rw [← hsource] at hsourceC
  rw [adjacentCasimirEigenvalue_raiseWeight]
  have hnR : (2 * r + 2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (i.val : ℝ) ≤ r := by
    exact_mod_cast (show i.val ≤ r by omega)
  have hjR : (j.val : ℝ) ≤ r := by
    exact_mod_cast (show j.val ≤ r by omega)
  have ht : 0 ≤ (target i : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (source j : ℝ) := Nat.cast_nonneg _
  linarith

theorem adjacentCasimirEigenvalue_ne_of_distinct_oneBox_neighbors
    {r n : ℕ} (hn : 2 * r + 2 ≤ n)
    (target source source' : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (hsource : IsAllRankOneBoxNeighbor target source)
    (hsource' : IsAllRankOneBoxNeighbor target source')
    (hne : source ≠ source') :
    adjacentCasimirEigenvalue n source ≠
      adjacentCasimirEigenvalue n source' := by
  rcases hsource with ⟨i, hi | hi⟩
  · rcases hsource' with ⟨j, hj | hj⟩
    · subst source
      subst source'
      have hij : i ≠ j := by
        intro h
        subst j
        exact hne rfl
      exact adjacentCasimirEigenvalue_raiseWeight_ne target hdominant i j hij
    · subst source
      exact ne_of_gt
        (adjacentCasimirEigenvalue_lower_lt_raise hn target source' i j hj)
  · rcases hsource' with ⟨j, hj | hj⟩
    · subst source'
      exact ne_of_lt
        (adjacentCasimirEigenvalue_lower_lt_raise hn target source j i hi)
    · have hij : i ≠ j := by
        intro h
        subst j
        exact hne (raiseWeight_injective_fixed_row i (hi.symm.trans hj))
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact ne_of_lt
          (adjacentCasimirEigenvalue_lowerWeight_lt
            target source source' hdominant i j hlt hi hj)
      · exact ne_of_gt
          (adjacentCasimirEigenvalue_lowerWeight_lt
            target source' source hdominant j i hgt hj hi)

theorem allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
    {r n : ℕ} (hn : 2 * r + 2 ≤ n)
    (target source source' : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (hsource : IsAllRankOneBoxNeighbor target source)
    (hsource' : IsAllRankOneBoxNeighbor target source')
    (hne : source ≠ source')
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (B : HarmonicYoungSpace (n := n) source' →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation source' a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp B) :
    A.adjoint.comp B = 0 := by
  exact boundaryYoungChannel_crossGram_eq_zero_of_distinctCasimir
    source source' target A B
    (ClebschRotation.tensorAmbientRotation target)
    (ClebschRotation.tensorAmbientRotation_adjoint target)
    hA hB
    (allRankCasimirEigenvalue n source)
    (allRankCasimirEigenvalue n source')
    (youngAmbientCasimir_allRank_eq_smul_id source)
    (youngAmbientCasimir_allRank_eq_smul_id source')
    (by
      change adjacentCasimirEigenvalue n source ≠
        adjacentCasimirEigenvalue n source'
      exact adjacentCasimirEigenvalue_ne_of_distinct_oneBox_neighbors
        hn target source source' hdominant hsource hsource' hne)

end

end MixedSignature

end HigherHarmonicYoung

section


namespace HigherYoungAllRankBoxSignatureNeighbors

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherYoungActualGraphAssembly

theorem boxSignature_injective
    {r m n : ℕ} (a : Fin (r + 1) → ℝ) :
    Function.Injective (boxSignature (m := m) a n) := by
  intro v w hsignature
  apply (Fintype.equivFin
    (RectangularVertices.Vertex r m)).symm.injective
  funext i
  apply Fin.ext
  have hcoordinate := congrFun hsignature i
  change flooredCoordinates a n i +
      (((Fintype.equivFin
        (RectangularVertices.Vertex r m)).symm v) i).val =
    flooredCoordinates a n i +
      (((Fintype.equivFin
        (RectangularVertices.Vertex r m)).symm w) i).val at hcoordinate
  exact Nat.add_left_cancel hcoordinate

theorem boxSignature_ne_of_ne
    {r m n : ℕ} (a : Fin (r + 1) → ℝ)
    {source source' : BoxIndex r m} (hne : source ≠ source') :
    boxSignature (m := m) a n source ≠
      boxSignature (m := m) a n source' := by
  intro heq
  exact hne (boxSignature_injective a heq)

theorem boxProbability_positive_signature_oneBox
    {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (target source : BoxIndex r m)
    (hpositive : 0 < boxProbability (m := m) a b n target source) :
    ∃ row : Fin (r + 1),
      boxSignature (m := m) a n source =
          raiseWeight (boxSignature (m := m) a n target) row ∨
        boxSignature (m := m) a n target =
          raiseWeight (boxSignature (m := m) a n source) row := by
  let v : RectangularVertices.Vertex r m :=
    (Fintype.equivFin (RectangularVertices.Vertex r m)).symm target
  let w : RectangularVertices.Vertex r m :=
    (Fintype.equivFin (RectangularVertices.Vertex r m)).symm source
  have hadj : (HigherHierarchyTrueGridAdjacency.grid r m).Adj v w := by
    by_contra hnot
    have hzero := HigherHierarchyBoxChannels.probability_eq_zero_of_not_adjacent
      a b n v w hnot
    have hpositive' : 0 < HigherHierarchyBoxChannels.probability a b n v w :=
      hpositive
    rw [hzero] at hpositive'
    exact (lt_irrefl 0) hpositive'
  obtain ⟨row, hforward | hreverse⟩ := hadj
  · obtain ⟨hrow, hw⟩ := hforward
    refine ⟨row, Or.inl ?_⟩
    change RectangularVertices.signature a n w =
      raiseWeight (RectangularVertices.signature a n v) row
    rw [hw]
    change RectangularVertices.signature a n
      (RectangularVertices.nextVertex v row hrow) = _
    exact RectangularVertices.signature_nextVertex a n v row hrow
  · obtain ⟨hrow, hv⟩ := hreverse
    refine ⟨row, Or.inr ?_⟩
    change RectangularVertices.signature a n v =
      raiseWeight (RectangularVertices.signature a n w) row
    rw [hv]
    change RectangularVertices.signature a n
      (RectangularVertices.nextVertex w row hrow) = _
    exact RectangularVertices.signature_nextVertex a n w row hrow

theorem boxSignature_antitone_of_finiteInterlacing
    {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex r m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (target : BoxIndex r m) :
    Antitone (boxSignature (m := m) a n target) := by
  exact (hstable
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)).antitone_ambient

end HigherYoungAllRankBoxSignatureNeighbors

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankBoxChannelOrthogonality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankBoxSignatureNeighbors
open MetricCodes.Spherical.HigherYoungMovingFibres

theorem boxChannel_crossGram_eq_zero
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (target source source' : BoxIndex (r + 1) m)
    (h : 0 < boxProbability (m := m) a b n target source)
    (h' : 0 < boxProbability (m := m) a b n target source')
    (hne : source ≠ source')
    (A : YoungVertex (n := n) (boxSignature (m := m) a n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) target))
    (B : YoungVertex (n := n) (boxSignature (m := m) a n) source' →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) target))
    (hA : ∀ i j : Fin n,
      A.comp (youngAmbientRotation
        (boxSignature (m := m) a n source) i j) =
        (ClebschRotation.tensorAmbientRotation
          (boxSignature (m := m) a n target) i j).comp A)
    (hB : ∀ i j : Fin n,
      B.comp (youngAmbientRotation
        (boxSignature (m := m) a n source') i j) =
        (ClebschRotation.tensorAmbientRotation
          (boxSignature (m := m) a n target) i j).comp B) :
    A.adjoint.comp B = 0 := by
  apply allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
    (r := r + 1) (n := n)
    (target := boxSignature (m := m) a n target)
    (source := boxSignature (m := m) a n source)
    (source' := boxSignature (m := m) a n source')
    (A := A) (B := B)
  · have hdimension :=
      (hstable ((Fintype.equivFin
        (RectangularVertices.Vertex (r + 1) m)).symm target)).1
    omega
  · exact boxSignature_antitone_of_finiteInterlacing a b hstable target
  · exact boxProbability_positive_signature_oneBox a b target source h
  · exact boxProbability_positive_signature_oneBox a b target source' h'
  · exact boxSignature_ne_of_ne a hne
  · exact hA
  · exact hB

end HigherYoungAllRankBoxChannelOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankActualBoxInstantiation

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankClebschBranchCoherence
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankBoxChannelOrthogonality
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherHarmonicYoung.TwoRowAxisChannelCoherence

theorem boxSignature_interlaces {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (i : BoxIndex (r + 1) m) :
    Interlaces (boxSignature (m := m) a n i) (Weyl.flooredWeight b n) := by
  intro j
  simpa only [Weyl.flooredWeight, boxSignature, flooredCoordinates] using
    (hstable ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm i)).2 j

theorem boxVertex_eq_nextVertex_of_signature_raise {r m n : ℕ}
    (a : Fin (r + 1) → ℝ)
    (target source : BoxIndex r m) (row : Fin (r + 1))
    (hrow : boxSignature (m := m) a n source =
      raiseWeight (boxSignature (m := m) a n target) row) :
    ∃ hstep :
      (((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
        row).val < m,
      (Fintype.equivFin (RectangularVertices.Vertex r m)).symm source =
        RectangularVertices.nextVertex
          ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
          row hstep := by
  let v : RectangularVertices.Vertex r m :=
    (Fintype.equivFin (RectangularVertices.Vertex r m)).symm target
  let w : RectangularVertices.Vertex r m :=
    (Fintype.equivFin (RectangularVertices.Vertex r m)).symm source
  have hcoord : (w row).val = (v row).val + 1 := by
    have hw := congrFun hrow row
    simp only [raiseWeight, Function.update_self] at hw
    change flooredCoordinates a n row + (w row).val =
      flooredCoordinates a n row + (v row).val + 1 at hw
    omega
  have hstep : (v row).val < m := by
    have hw := (w row).isLt
    omega
  refine ⟨hstep, ?_⟩
  change w = RectangularVertices.nextVertex v row hstep
  funext k
  apply Fin.ext
  by_cases hk : k = row
  · subst k
    simpa only [RectangularVertices.nextVertex, Function.update_self] using hcoord
  · have hw := congrFun hrow k
    change flooredCoordinates a n k + (w k).val =
      (raiseWeight (boxSignature (m := m) a n target) row k) at hw
    have heq : (w k).val = (v k).val := by
      simp only [raiseWeight, Function.update_of_ne hk,
        boxSignature, RectangularVertices.signature] at hw
      exact Nat.add_left_cancel hw
    simpa only [RectangularVertices.nextVertex, ne_eq, hk, not_false_eq_true,
      Function.update_of_ne] using heq

theorem boxProbability_eq_plus_of_signature_raise {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (target source : BoxIndex r m) (row : Fin (r + 1))
    (hrow : boxSignature (m := m) a n source =
      raiseWeight (boxSignature (m := m) a n target) row) :
    boxProbability a b n target source =
      plusProbability n (boxSignature (m := m) a n target)
        (flooredCoordinates b n) row := by
  obtain ⟨hstep, hvertex⟩ :=
    boxVertex_eq_nextVertex_of_signature_raise a target source row hrow
  change HigherHierarchyBoxChannels.probability a b n
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source) = _
  rw [hvertex]
  change HigherHierarchyBoxChannels.probability a b n
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
    (HigherHierarchyBoxSpectral.nextVertex
      ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
      row hstep) = _
  rw [HigherHierarchyBoxChannels.probability_nextVertex]
  rfl

theorem boxProbability_eq_minus_of_signature_raise {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (target source : BoxIndex r m) (row : Fin (r + 1))
    (hrow : boxSignature (m := m) a n target =
      raiseWeight (boxSignature (m := m) a n source) row) :
    boxProbability a b n target source =
      minusProbability n (boxSignature (m := m) a n target)
        (flooredCoordinates b n) row := by
  obtain ⟨hstep, hvertex⟩ :=
    boxVertex_eq_nextVertex_of_signature_raise a source target row hrow
  change HigherHierarchyBoxChannels.probability a b n
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source) = _
  rw [hvertex]
  change HigherHierarchyBoxChannels.probability a b n
    (HigherHierarchyBoxSpectral.nextVertex
      ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source)
      row hstep)
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source) = _
  rw [HigherHierarchyBoxChannels.probability_nextVertex_reverse]
  change minusProbability n
    (raiseWeight (RectangularVertices.signature a n
      ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source)) row)
    (flooredCoordinates b n) row = _
  congr 1
  exact hrow.symm

theorem box_stableRange {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n)) :
    2 * (r + 1) + 4 ≤ n := by
  let v : RectangularVertices.Vertex (r + 1) m := fun _ => 0
  exact (hstable v).1

theorem boxStabilizer_finrank_pos {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n)) :
    0 < Module.finrank ℝ (BoxStabilizer n b) := by
  let v : RectangularVertices.Vertex (r + 1) m := fun _ => 0
  have hinter : Interlaces (RectangularVertices.signature a n v)
      (Weyl.flooredWeight b n) := by
    intro j
    simpa only [Weyl.flooredWeight, flooredCoordinates] using (hstable v).2 j
  apply finrank_selectedStabilizer_pos (Weyl.flooredWeight b n) hinter
  have hn := (hstable v).1
  omega

theorem boxWeylDimensions_of_actualWeyl {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (hweyl : ∀ {k d : ℕ} (lam : Fin (k + 1) → ℕ),
      2 * k + 4 ≤ d → Antitone lam →
        Weyl.dimension d lam =
          (Module.finrank ℝ (HarmonicYoungSpace (n := d) lam) : ℝ)) :
    (Weyl.dimension (n - 1) (Weyl.flooredWeight b n) =
      (Module.finrank ℝ (BoxStabilizer n b) : ℝ)) ∧
    (∀ i : BoxIndex (r + 1) m,
      Weyl.dimension n (boxSignature (m := m) a n i) =
        (Module.finrank ℝ
          (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ)) := by
  let v : RectangularVertices.Vertex (r + 1) m := fun _ => 0
  let i : BoxIndex (r + 1) m :=
    (Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)) v
  have hi := boxSignature_interlaces a b hstable i
  have hn := box_stableRange a b hstable
  constructor
  · apply hweyl (Weyl.flooredWeight b n) (by omega)
    exact interlaces_antitone_stabilizer hi
  · intro j
    apply hweyl (boxSignature (m := m) a n j) hn
    exact (boxSignature_interlaces a b hstable j).antitone_ambient

/-- The box axis used in the spherical-code argument. -/
def boxAxis (n : ℕ) (hn : 0 < n) : SpherePoint n := by
  cases n with
  | zero => omega
  | succ d =>
      refine ⟨EuclideanSpace.single (Fin.last d) (1 : ℝ), ?_⟩
      simp only [PiLp.norm_single, norm_one]

private def phaseCorrectedYoungChannel {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : E →ₗᵢ[ℝ] G) (c : ℝ) : E →ₗᵢ[ℝ] G :=
  if 0 ≤ c then A else phaseNegatedChannel A

theorem phaseCorrectedYoungChannel_adjoint_eq_sqrt {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G]
    (A : E →ₗᵢ[ℝ] G) (c p : ℝ)
    (hp : 0 ≤ p) (hc : c ^ 2 = p)
    (z : G) (v : E) (haxis : A.adjoint z = c • v) :
    (phaseCorrectedYoungChannel A c).adjoint z = Real.sqrt p • v := by
  unfold phaseCorrectedYoungChannel
  split_ifs with h
  · rw [haxis]
    congr 1
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  · rw [phaseNegatedChannel_adjoint_apply, haxis, ← neg_smul]
    congr 1
    have hnegative : c < 0 := lt_of_not_ge h
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]

theorem phaseCorrectedYoungChannel_rotation
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu))
    (c : ℝ)
    (hA : ∀ a b : Fin n,
      A.toLinearMap.comp (youngAmbientRotation lam a b) =
        (ClebschRotation.tensorAmbientRotation mu a b).comp A.toLinearMap)
    (a b : Fin n) :
    (phaseCorrectedYoungChannel A c).toLinearMap.comp
        (youngAmbientRotation lam a b) =
      (ClebschRotation.tensorAmbientRotation mu a b).comp
        (phaseCorrectedYoungChannel A c).toLinearMap := by
  unfold phaseCorrectedYoungChannel
  split_ifs with h
  · exact hA a b
  · rw [phaseNegatedChannel_toLinearMap]
    exact boundaryYoungChannel_smul_rotation_intertwine
      lam mu A.toLinearMap (ClebschRotation.tensorAmbientRotation mu)
      hA (-1 : ℝ) a b

/-- Data encoding the coherent box sector construction. -/
structure CoherentBoxSectorData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source) where
  /-- The channel component. -/
  channel : YoungVertex (n := n) (boxSignature (m := m) a n) source →ₗᵢ[ℝ]
    (SpherePacking.Euclidean n ⊗[ℝ]
      YoungVertex (n := n) (boxSignature (m := m) a n) target)
  rotation : ∀ c d : Fin n,
    channel.toLinearMap.comp
      (youngAmbientRotation (boxSignature (m := m) a n source) c d) =
      (ClebschRotation.tensorAmbientRotation
        (boxSignature (m := m) a n target) c d).comp channel.toLinearMap
  /-- The coefficient component. -/
  coefficient : ℝ
  coefficient_sq : coefficient ^ 2 = boxProbability a b n target source
  axis : ∀ (x : SpherePoint n) (v : BoxStabilizer n b),
    channel.adjoint
      (x.val ⊗ₜ[ℝ]
        movingYoungFibre (boxSignature (m := m) a n target)
          o (fibre target) x v) =
      coefficient • movingYoungFibre (boxSignature (m := m) a n source)
        o (fibre source) x v

theorem coherentBoxSector_phaseCorrected_axis {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (S : CoherentBoxSectorData a b o fibre target source h)
    (x : SpherePoint n) (v : BoxStabilizer n b) :
    (phaseCorrectedYoungChannel S.channel S.coefficient).adjoint
      (x.val ⊗ₜ[ℝ]
        movingYoungFibre (boxSignature (m := m) a n target)
          o (fibre target) x v) =
      Real.sqrt (boxProbability a b n target source) •
        movingYoungFibre (boxSignature (m := m) a n source)
          o (fibre source) x v :=
  phaseCorrectedYoungChannel_adjoint_eq_sqrt S.channel S.coefficient
    (boxProbability a b n target source) h.le S.coefficient_sq _ _
    (S.axis x v)

/-- Data encoding the box lowering projected axis witness construction. -/
structure BoxLoweringProjectedAxisWitness {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hdeg :
      (∑ i, boxSignature (m := m) a n source i) =
        (∑ i, boxSignature (m := m) a n target i) + 1) where
  /-- The gram component. -/
  gram : ℝ
  gram_pos : 0 < gram
  gram_inner : ∀ p q :
      YoungVertex (n := n) (boxSignature (m := m) a n) source,
    ⟪youngClebschLower (boxSignature (m := m) a n target)
        (boxSignature (m := m) a n source) hdeg row p,
      youngClebschLower (boxSignature (m := m) a n target)
        (boxSignature (m := m) a n source) hdeg row q⟫_ℝ =
      gram * ⟪p, q⟫_ℝ
  /-- The coefficient component. -/
  coefficient : ℝ
  coefficient_sq : coefficient ^ 2 =
    gram * boxProbability a b n target source
  projected_axis : ∀ v : BoxStabilizer n b,
    projectedCoordinateRaise (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target) hdeg row o.val
        (fibre target v) =
      coefficient • fibre source v

/-- Data encoding the box raising projected axis witness construction. -/
structure BoxRaisingProjectedAxisWitness {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hdeg :
      (∑ i, boxSignature (m := m) a n target i) =
        (∑ i, boxSignature (m := m) a n source i) + 1) where
  /-- The gram component. -/
  gram : ℝ
  gram_pos : 0 < gram
  gram_inner : ∀ p q :
      YoungVertex (n := n) (boxSignature (m := m) a n) source,
    ⟪youngClebschRaise (boxSignature (m := m) a n target)
        (boxSignature (m := m) a n source) hdeg row p,
      youngClebschRaise (boxSignature (m := m) a n target)
        (boxSignature (m := m) a n source) hdeg row q⟫_ℝ =
      gram * ⟪p, q⟫_ℝ
  /-- The coefficient component. -/
  coefficient : ℝ
  coefficient_sq : coefficient ^ 2 =
    gram * boxProbability a b n target source
  projected_axis : ∀ v : BoxStabilizer n b,
    projectedCoordinateLower (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target) hdeg row o.val
        (fibre target v) =
      coefficient • fibre source v

private def coherentBoxLowerSector {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hdeg :
      (∑ i, boxSignature (m := m) a n source i) =
        (∑ i, boxSignature (m := m) a n target i) + 1)
    (D : BoxLoweringProjectedAxisWitness a b o fibre target source
      h row hdeg) :
    CoherentBoxSectorData a b o fibre target source h where
  channel := normalizedYoungClebschLower
    (boxSignature (m := m) a n target)
    (boxSignature (m := m) a n source)
    hdeg row D.gram D.gram_pos D.gram_inner
  rotation := boundaryNormalizedYoungClebschLower_rotation_intertwine
    (boxSignature (m := m) a n target)
    (boxSignature (m := m) a n source)
    hdeg row D.gram D.gram_pos D.gram_inner
  coefficient := (Real.sqrt D.gram)⁻¹ * D.coefficient
  coefficient_sq := by
    rw [mul_pow, inv_pow, Real.sq_sqrt D.gram_pos.le, D.coefficient_sq]
    field_simp [D.gram_pos.ne']
  axis x v := by
    rw [normalizedYoungClebschLower_adjoint_tmul,
      projectedCoordinateRaise_movingFibre_eq_smul
        (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target)
        hdeg row o (fibre target) (fibre source)
        D.coefficient D.projected_axis x v, smul_smul]

private def coherentBoxRaiseSector {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hdeg :
      (∑ i, boxSignature (m := m) a n target i) =
        (∑ i, boxSignature (m := m) a n source i) + 1)
    (D : BoxRaisingProjectedAxisWitness a b o fibre target source
      h row hdeg) :
    CoherentBoxSectorData a b o fibre target source h where
  channel := normalizedYoungClebschRaise
    (boxSignature (m := m) a n target)
    (boxSignature (m := m) a n source)
    hdeg row D.gram D.gram_pos D.gram_inner
  rotation := boundaryNormalizedYoungClebschRaise_rotation_intertwine
    (boxSignature (m := m) a n target)
    (boxSignature (m := m) a n source)
    hdeg row D.gram D.gram_pos D.gram_inner
  coefficient := (Real.sqrt D.gram)⁻¹ * D.coefficient
  coefficient_sq := by
    rw [mul_pow, inv_pow, Real.sq_sqrt D.gram_pos.le, D.coefficient_sq]
    field_simp [D.gram_pos.ne']
  axis x v := by
    rw [normalizedYoungClebschRaise_adjoint_tmul,
      projectedCoordinateLower_movingFibre_eq_smul
        (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target)
        hdeg row o (fibre target) (fibre source)
        D.coefficient D.projected_axis x v, smul_smul]

/-- Data encoding the box projected axis witness construction. -/
inductive BoxProjectedAxisWitness {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source) where
  | lower (row : Fin (r + 2))
      (hdeg :
        (∑ i, boxSignature (m := m) a n source i) =
          (∑ i, boxSignature (m := m) a n target i) + 1)
      (data : BoxLoweringProjectedAxisWitness a b o fibre
        target source h row hdeg)
  | raise (row : Fin (r + 2))
      (hdeg :
        (∑ i, boxSignature (m := m) a n target i) =
          (∑ i, boxSignature (m := m) a n source i) + 1)
      (data : BoxRaisingProjectedAxisWitness a b o fibre
        target source h row hdeg)

private def coherentBoxSector_of_projectedAxisWitness {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (D : BoxProjectedAxisWitness a b o fibre target source h) :
    CoherentBoxSectorData a b o fibre target source h := by
  cases D with
  | lower row hdeg data =>
      exact coherentBoxLowerSector a b o fibre target source h row hdeg data
  | raise row hdeg data =>
      exact coherentBoxRaiseSector a b o fibre target source h row hdeg data

private theorem coherentBoxSector_of_projectedAxisWitness_axis {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (D : BoxProjectedAxisWitness a b o fibre target source h)
    (x : SpherePoint n) (v : BoxStabilizer n b) :
    (phaseCorrectedYoungChannel
      (coherentBoxSector_of_projectedAxisWitness
        a b o fibre target source h D).channel
      (coherentBoxSector_of_projectedAxisWitness
        a b o fibre target source h D).coefficient).adjoint
      (x.val ⊗ₜ[ℝ]
        movingYoungFibre (boxSignature (m := m) a n target)
          o (fibre target) x v) =
      Real.sqrt (boxProbability a b n target source) •
        movingYoungFibre (boxSignature (m := m) a n source)
          o (fibre source) x v :=
  coherentBoxSector_phaseCorrected_axis a b o fibre target source h
    (coherentBoxSector_of_projectedAxisWitness
      a b o fibre target source h D) x v

private def boxRepresentationData_of_coherentSectors {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (hstabilizerWeyl :
      Weyl.dimension (n - 1) (Weyl.flooredWeight b n) =
        (Module.finrank ℝ (BoxStabilizer n b) : ℝ))
    (hvertexWeyl : ∀ i : BoxIndex (r + 1) m,
      Weyl.dimension n (boxSignature (m := m) a n i) =
        (Module.finrank ℝ
          (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ))
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (sector : (target source : BoxIndex (r + 1) m) →
      (h : 0 < boxProbability a b n target source) →
        CoherentBoxSectorData a b o fibre target source h)
    (sector_axis : ∀ (target source : BoxIndex (r + 1) m)
      (h : 0 < boxProbability a b n target source)
      (x : SpherePoint n) (v : BoxStabilizer n b),
      (phaseCorrectedYoungChannel
        (sector target source h).channel
        (sector target source h).coefficient).adjoint
        (x.val ⊗ₜ[ℝ]
          movingYoungFibre (boxSignature (m := m) a n target)
            o (fibre target) x v) =
        Real.sqrt (boxProbability a b n target source) •
          movingYoungFibre (boxSignature (m := m) a n source)
            o (fibre source) x v) :
    BoxRepresentationData (m := m) (n := n) a b where
  axis := o
  stabilizer_pos := boxStabilizer_finrank_pos a b hstable
  stabilizer_weyl := hstabilizerWeyl
  vertex_weyl := hvertexWeyl
  fibre := fibre
  edge target source h :=
    phaseCorrectedYoungChannel
      (sector target source h).channel
      (sector target source h).coefficient
  edge_orthogonal target source source' h h' hne := by
    apply boxChannel_crossGram_eq_zero a b hstable
      target source source' h h' hne
    · exact phaseCorrectedYoungChannel_rotation
        (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target)
        (sector target source h).channel
        (sector target source h).coefficient
        (sector target source h).rotation
    · exact phaseCorrectedYoungChannel_rotation
        (boxSignature (m := m) a n source')
        (boxSignature (m := m) a n target)
        (sector target source' h').channel
        (sector target source' h').coefficient
        (sector target source' h').rotation
  edge_axis target source h x v := sector_axis target source h x v

/-- The box representation data of projected axis witnesses used in the spherical-code argument. -/
def boxRepresentationDataOfProjectedAxisWitnesses {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (hweyl : ∀ {k d : ℕ} (lam : Fin (k + 1) → ℕ),
      2 * k + 4 ≤ d → Antitone lam →
        Weyl.dimension d lam =
          (Module.finrank ℝ (HarmonicYoungSpace (n := d) lam) : ℝ))
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (witness : (target source : BoxIndex (r + 1) m) →
      (h : 0 < boxProbability a b n target source) →
        BoxProjectedAxisWitness a b o fibre target source h) :
    BoxRepresentationData (m := m) (n := n) a b :=
  boxRepresentationData_of_coherentSectors a b hstable
    (boxWeylDimensions_of_actualWeyl a b hstable hweyl).1
    (boxWeylDimensions_of_actualWeyl a b hstable hweyl).2
    o fibre
    (fun target source h =>
      coherentBoxSector_of_projectedAxisWitness a b o fibre
        target source h (witness target source h))
    (fun target source h x v =>
      coherentBoxSector_of_projectedAxisWitness_axis a b o fibre
        target source h (witness target source h) x v)

end HigherYoungAllRankActualBoxInstantiation

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGelfandTsetlinAdjacentFibrePhase

open SpherePacking.HarmonicCoordinateOperators
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankClebschBranchCoherence
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherHarmonicYoung.TwoRowAxisChannelCoherence

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The adjacent normalized axis coefficient used in the spherical-code argument. -/
def adjacentNormalizedAxisCoefficient
    (sourceGram targetGram coefficient : ℝ) : ℝ :=
  coefficient * Real.sqrt targetGram / Real.sqrt sourceGram

end AllRankGelfandTsetlinAdjacentFibrePhase

end

section


open scoped BigOperators InnerProductSpace

theorem youngHarmonicLift_fischer_inner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : homogeneousYoungHighestWeightSubmodule (n := n) lam)
    (q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngHarmonicLift lam p, q⟫_ℝ =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((p.val : SpherePacking.Fischer.Homogeneous
          ((r + 1) * n) (∑ a, lam a)) : PolynomialSpace r n)
        (q : PolynomialSpace r n) := by
  rw [young_inner_eq_polynomialInner]
  let q' : homogeneousTraceFreeSubmodule r n (∑ a, lam a) :=
    ⟨youngHomogeneousEmbedding lam q,
      (mem_homogeneousTraceFreeSubmodule
        (youngHomogeneousEmbedding lam q)).mpr
        ((mem_harmonicYoungSubmodule lam
          (q : PolynomialSpace r n)).mp q.property).2.2.1⟩
  exact simultaneousHarmonicProjection_polynomialInner p.val q'

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungMixedGapStabilizerRotationIntertwining

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherYoungMixedGapBranching

theorem ambientRotation_addedAxisVariable
    {r n : ℕ} (a b : Fin n) (i : Fin (r + 1)) :
    ambientRotation (r := r) a.castSucc b.castSucc
        (MvPolynomial.X (variableIndex i (Fin.last n))) = 0 := by
  rw [ambientRotation_apply, ambientCoordinateDerivation_X,
    ambientCoordinateDerivation_X]
  simp only [Fin.castSucc_ne_last, ↓reduceIte, sub_self]

end HigherYoungMixedGapStabilizerRotationIntertwining

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungArbitraryRankReverseInterlacingRotationIntertwining

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherYoungMixedGapStabilizerRotationIntertwining
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem ambientCoordinateDerivation_transversePolynomial
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r + 1) a.castSucc b.castSucc
        (transversePolynomial n p) =
      transversePolynomial n
        (ambientCoordinateDerivation (r := r) a b p) := by
  rw [ambientCoordinateDerivation_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_transversePolynomial_castSucc,
    pderiv_transversePolynomial_lastRow, mul_zero, add_zero]
  rw [ambientCoordinateDerivation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, transversePolynomial_X]

theorem ambientRotation_transversePolynomial
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientRotation (r := r + 1) a.castSucc b.castSucc
        (transversePolynomial n p) =
      transversePolynomial n (ambientRotation (r := r) a b p) := by
  rw [ambientRotation_apply, ambientRotation_apply, map_sub,
    ambientCoordinateDerivation_transversePolynomial,
    ambientCoordinateDerivation_transversePolynomial]

theorem ambientRotation_lowerPolarizationPath
    {r n : ℕ} (a b : Fin n) (path : List (Fin (r + 1)))
    (p : PolynomialSpace r n) :
    ambientRotation (r := r) a b
        (lowerPolarizationPath path p) =
      lowerPolarizationPath path
        (ambientRotation (r := r) a b p) := by
  induction path generalizing p with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          change
            ambientRotation (r := r) a b
              (polarization r n j i
                (lowerPolarizationPath (j :: tail) p)) =
              polarization r n j i
                (lowerPolarizationPath (j :: tail)
                  (ambientRotation (r := r) a b p))
          rw [ambientRotation_polarization_comm, ih]

theorem ambientRotation_arbitraryRowAxialRaise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (a b : Fin n)
    (p : PolynomialSpace r (n + 1)) :
    ambientRotation (r := r) a.castSucc b.castSucc
        (arbitraryRowAxialRaise lam row (Fin.last n) p) =
      arbitraryRowAxialRaise lam row (Fin.last n)
        (ambientRotation (r := r) a.castSucc b.castSucc p) := by
  rw [arbitraryRowAxialRaise_apply,
    arbitraryRowAxialRaise_apply, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Derivation.map_smul, Derivation.leibniz,
    ambientRotation_addedAxisVariable,
    ambientRotation_lowerPolarizationPath]
  simp only [ambientRotation_apply, ambientCoordinateDerivation_apply, map_sub, map_sum,
    smul_eq_mul, mul_zero, add_zero, Algebra.smul_def, MvPolynomial.algebraMap_eq]

theorem ambientRotation_iteratedArbitraryRowAxialRaise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (rows : List (Fin (r + 1))) (a b : Fin n)
    (p : PolynomialSpace r (n + 1)) :
    ambientRotation (r := r) a.castSucc b.castSucc
        (iteratedArbitraryRowAxialRaise lam (Fin.last n) rows p) =
      iteratedArbitraryRowAxialRaise lam (Fin.last n) rows
        (ambientRotation (r := r) a.castSucc b.castSucc p) := by
  induction rows generalizing lam p with
  | nil => rfl
  | cons row rows ih =>
      change
        ambientRotation (r := r) a.castSucc b.castSucc
          (iteratedArbitraryRowAxialRaise (raiseWeight lam row)
            (Fin.last n) rows (arbitraryRowAxialRaise lam row
              (Fin.last n) p)) =
          iteratedArbitraryRowAxialRaise (raiseWeight lam row)
            (Fin.last n) rows (arbitraryRowAxialRaise lam row
              (Fin.last n)
                (ambientRotation (r := r) a.castSucc b.castSucc p))
      rw [ih, ambientRotation_arbitraryRowAxialRaise]

theorem reverseInterlacingPolynomialSeed_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (a b : Fin n)
    (p : HarmonicYoungSpace (n := n) mu) :
    ambientRotation (r := r + 1) a.castSucc b.castSucc
        (reverseInterlacingPolynomialSeed lam mu p) =
      reverseInterlacingPolynomialSeed lam mu
        (youngAmbientRotation mu a b p) := by
  change
    ambientRotation (r := r + 1) a.castSucc b.castSucc
      (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
        (Fin.last n) (reverseInterlacingRowSchedule lam mu)
          (transversePolynomial n (p : PolynomialSpace r n))) =
      iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
        (Fin.last n) (reverseInterlacingRowSchedule lam mu)
          (transversePolynomial n
            (ambientRotation (r := r) a b (p : PolynomialSpace r n)))
  rw [ambientRotation_iteratedArbitraryRowAxialRaise,
    ambientRotation_transversePolynomial]

end HigherYoungArbitraryRankReverseInterlacingRotationIntertwining

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungMixedGapLieGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungMixedGapBranching

/-- The predicate asserting rotation invariant. -/
def IsRotationInvariant {V I : Type*} [AddCommGroup V] [Module ℝ V]
    (R : I → V →ₗ[ℝ] V) (W : Submodule ℝ V) : Prop :=
  ∀ (i : I) (v : V), v ∈ W → R i v ∈ W

theorem rotationInvariant_orthogonal {V I : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : I → V →ₗ[ℝ] V)
    (hskew : ∀ (i : I) (v w : V),
      ⟪R i v, w⟫_ℝ = -⟪v, R i w⟫_ℝ)
    (W : Submodule ℝ V) (hW : IsRotationInvariant R W) :
    IsRotationInvariant R Wᗮ := by
  intro i v hv
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hz := (Submodule.mem_orthogonal W v).mp hv
    (R i w) (hW i w hw)
  have h := hskew i w v
  linarith

theorem rotationIntertwiner_eigenspace_invariant
    {V I : Type*}
    [AddCommGroup V] [Module ℝ V]
    (R : I → V →ₗ[ℝ] V)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ i, A.comp (R i) = (R i).comp A)
    (c : ℝ) :
    IsRotationInvariant R (Module.End.eigenspace A c) := by
  intro i v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcommute := LinearMap.congr_fun (hA i) v
  simpa only [LinearMap.coe_comp, Function.comp_apply, hv, map_smul] using hcommute

theorem symmetricRotationIntertwiner_eq_smul_id
    {V I : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (R : I → V →ₗ[ℝ] V)
    (hirred : ∀ W : Submodule ℝ V,
      IsRotationInvariant R W → W = ⊥ ∨ W = ⊤)
    (A : V →ₗ[ℝ] V)
    (hsymmetric : A.IsSymmetric)
    (hA : ∀ i, A.comp (R i) = (R i).comp A) :
    ∃ c : ℝ, A = c • LinearMap.id := by
  cases subsingleton_or_nontrivial V with
  | inl hsubsingleton =>
      let := hsubsingleton
      exact ⟨0, Subsingleton.elim _ _⟩
  | inr hnontrivial =>
      let := hnontrivial
      obtain ⟨c, hc⟩ : ∃ c : ℝ, Module.End.HasEigenvalue A c :=
        ⟨_, hsymmetric.hasEigenvalue_iSup_of_finiteDimensional⟩
      have heigenspace : Module.End.eigenspace A c = ⊤ :=
        (hirred _
          (rotationIntertwiner_eigenspace_invariant R A hA c)).resolve_left hc
      refine ⟨c, ?_⟩
      apply LinearMap.ext
      intro v
      have hv : v ∈ Module.End.eigenspace A c := by
        rw [heigenspace]
        trivial
      change A v = c • v
      exact Module.End.mem_eigenspace_iff.mp hv

/-- The young rotation family used in the spherical-code argument. -/
def youngRotationFamily {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Fin n × Fin n →
      HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
        HarmonicYoungSpace (n := n) lam :=
  fun ab => youngAmbientRotation lam ab.1 ab.2

theorem youngRotationFamily_inner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (ab : Fin n × Fin n)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngRotationFamily lam ab p, q⟫_ℝ =
      -⟪p, youngRotationFamily lam ab q⟫_ℝ :=
  youngAmbientRotation_inner lam ab.1 ab.2 p q

end HigherYoungMixedGapLieGram

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankGelfandTsetlinGramRotationCommutation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherYoungArbitraryRankReverseInterlacingRotationIntertwining
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherRepresentationGraph

private def reverseInterlacingHarmonicBranchGram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu :=
  (reverseInterlacingHarmonicBranch (n := n) lam mu h).adjoint.comp
    (reverseInterlacingHarmonicBranch (n := n) lam mu h)

theorem reverseInterlacingHarmonicBranchGram_rotation_commute
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (a b : Fin n)
    (hbranch :
      (reverseInterlacingHarmonicBranch (n := n) lam mu h).comp
          (youngAmbientRotation mu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp
          (reverseInterlacingHarmonicBranch (n := n) lam mu h)) :
    (reverseInterlacingHarmonicBranchGram lam mu h).comp
        (youngAmbientRotation mu a b) =
      (youngAmbientRotation mu a b).comp
        (reverseInterlacingHarmonicBranchGram lam mu h) := by
  exact crossGram_intertwines_of_skew
    (reverseInterlacingHarmonicBranch (n := n) lam mu h)
    (reverseInterlacingHarmonicBranch (n := n) lam mu h)
    (youngAmbientRotation mu a b)
    (youngAmbientRotation mu a b)
    (youngAmbientRotation lam a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint mu a b)
    (youngAmbientRotation_adjoint lam a.castSucc b.castSucc)
    hbranch hbranch

theorem reverseInterlacingHarmonicBranchGram_isSymmetric
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    (reverseInterlacingHarmonicBranchGram (n := n) lam mu h).IsSymmetric :=
  LinearMap.isSymmetric_adjoint_comp_self
    (reverseInterlacingHarmonicBranch (n := n) lam mu h)

theorem reverseInterlacingHarmonicBranchGram_inner_self
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    ⟪reverseInterlacingHarmonicBranchGram lam mu h p, p⟫_ℝ =
      ⟪reverseInterlacingHarmonicBranch (n := n) lam mu h p,
        reverseInterlacingHarmonicBranch (n := n) lam mu h p⟫_ℝ :=
  LinearMap.adjoint_inner_left
    (reverseInterlacingHarmonicBranch (n := n) lam mu h)
    p (reverseInterlacingHarmonicBranch (n := n) lam mu h p)

theorem reverseInterlacingHarmonicBranchGram_inner_self_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hinjective :
      Function.Injective
        (reverseInterlacingHarmonicBranch (n := n) lam mu h))
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    0 < ⟪reverseInterlacingHarmonicBranchGram lam mu h p, p⟫_ℝ := by
  rw [reverseInterlacingHarmonicBranchGram_inner_self]
  apply real_inner_self_pos.mpr
  intro hzero
  apply hp
  apply hinjective
  simpa only [map_zero] using hzero

theorem reverseInterlacingHarmonicBranchGram_eq_smul_id_of_irreducible
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hirred : ∀ W : Submodule ℝ (HarmonicYoungSpace (n := n) mu),
      IsRotationInvariant (youngRotationFamily mu) W →
        W = ⊥ ∨ W = ⊤)
    (hbranch : ∀ a b : Fin n,
      (reverseInterlacingHarmonicBranch (n := n) lam mu h).comp
          (youngAmbientRotation mu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp
          (reverseInterlacingHarmonicBranch (n := n) lam mu h)) :
    ∃ c : ℝ,
      reverseInterlacingHarmonicBranchGram (n := n) lam mu h =
        c • (LinearMap.id : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
          HarmonicYoungSpace (n := n) mu) := by
  apply symmetricRotationIntertwiner_eq_smul_id
    (youngRotationFamily mu) hirred
    (reverseInterlacingHarmonicBranchGram lam mu h)
    (reverseInterlacingHarmonicBranchGram_isSymmetric lam mu h)
  intro ab
  exact reverseInterlacingHarmonicBranchGram_rotation_commute
    lam mu h ab.1 ab.2 (hbranch ab.1 ab.2)

theorem reverseInterlacingHarmonicBranchGram_scalar_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hinjective :
      Function.Injective
        (reverseInterlacingHarmonicBranch (n := n) lam mu h))
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0)
    (c : ℝ)
    (hc : reverseInterlacingHarmonicBranchGram (n := n) lam mu h =
      c • (LinearMap.id : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
        HarmonicYoungSpace (n := n) mu)) :
    0 < c := by
  have hpositive := reverseInterlacingHarmonicBranchGram_inner_self_pos
    lam mu h hinjective p hp
  rw [hc] at hpositive
  change 0 < ⟪c • p, p⟫_ℝ at hpositive
  have hfactor : ⟪c • p, p⟫_ℝ = c * ⟪p, p⟫_ℝ :=
    real_inner_smul_left p p c
  have hproduct : 0 < c * ⟪p, p⟫_ℝ := by
    exact hfactor ▸ hpositive
  have hself : 0 < ⟪p, p⟫_ℝ := real_inner_self_pos.mpr hp
  nlinarith

end HigherYoungAllRankGelfandTsetlinGramRotationCommutation

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankHarmonicBranchRotationIntertwining

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherYoungArbitraryRankReverseInterlacingRotationIntertwining
open MetricCodes.Spherical.HigherRepresentationGraph

theorem harmonicBranchOfHighestWeightSeed_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (seed : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n + 1) lam)
    (a b : Fin n)
    (hseed : ∀ p : HarmonicYoungSpace (n := n) mu,
      ambientRotation (r := r + 1) a.castSucc b.castSucc
          ((((seed p).val : SpherePacking.Fischer.Homogeneous
            ((r + 2) * (n + 1)) (∑ i, lam i)) :
              PolynomialSpace (r + 1) (n + 1))) =
        ((((seed (youngAmbientRotation mu a b p)).val :
          SpherePacking.Fischer.Homogeneous
            ((r + 2) * (n + 1)) (∑ i, lam i)) :
              PolynomialSpace (r + 1) (n + 1)))) :
    (harmonicBranchOfHighestWeightSeed lam seed).comp
        (youngAmbientRotation mu a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (harmonicBranchOfHighestWeightSeed lam seed) := by
  apply LinearMap.ext
  intro p
  apply ext_inner_right ℝ
  intro q
  change
    ⟪youngHarmonicLift lam (seed (youngAmbientRotation mu a b p)), q⟫_ℝ =
      ⟪youngAmbientRotation lam a.castSucc b.castSucc
        (youngHarmonicLift lam (seed p)), q⟫_ℝ
  calc
    ⟪youngHarmonicLift lam (seed (youngAmbientRotation mu a b p)), q⟫_ℝ =
        SpherePacking.Fischer.polynomialInner ((r + 2) * (n + 1))
          ((((seed (youngAmbientRotation mu a b p)).val :
            SpherePacking.Fischer.Homogeneous
              ((r + 2) * (n + 1)) (∑ i, lam i)) :
                PolynomialSpace (r + 1) (n + 1)))
          (q : PolynomialSpace (r + 1) (n + 1)) :=
      youngHarmonicLift_fischer_inner lam _ q
    _ = SpherePacking.Fischer.polynomialInner ((r + 2) * (n + 1))
          (ambientRotation (r := r + 1) a.castSucc b.castSucc
            ((((seed p).val : SpherePacking.Fischer.Homogeneous
              ((r + 2) * (n + 1)) (∑ i, lam i)) :
                PolynomialSpace (r + 1) (n + 1))))
          (q : PolynomialSpace (r + 1) (n + 1)) := by
      rw [hseed p]
    _ = -SpherePacking.Fischer.polynomialInner ((r + 2) * (n + 1))
          ((((seed p).val : SpherePacking.Fischer.Homogeneous
            ((r + 2) * (n + 1)) (∑ i, lam i)) :
              PolynomialSpace (r + 1) (n + 1)))
          (ambientRotation (r := r + 1) a.castSucc b.castSucc
            (q : PolynomialSpace (r + 1) (n + 1))) :=
      ambientRotation_polynomialInner a.castSucc b.castSucc _ _
    _ = -⟪youngHarmonicLift lam (seed p),
          youngAmbientRotation lam a.castSucc b.castSucc q⟫_ℝ := by
      rw [youngHarmonicLift_fischer_inner]
      rfl
    _ = ⟪youngAmbientRotation lam a.castSucc b.castSucc
          (youngHarmonicLift lam (seed p)), q⟫_ℝ := by
      rw [youngAmbientRotation_inner]

theorem reverseInterlacingHarmonicBranch_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (a b : Fin n) :
    (reverseInterlacingHarmonicBranch (n := n) lam mu h).comp
        (youngAmbientRotation mu a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (reverseInterlacingHarmonicBranch (n := n) lam mu h) := by
  apply harmonicBranchOfHighestWeightSeed_rotation_intertwine
    lam mu (reverseInterlacingHighestWeightSeed lam mu h) a b
  intro p
  change ambientRotation (r := r + 1) a.castSucc b.castSucc
      (reverseInterlacingPolynomialSeed lam mu p) =
    reverseInterlacingPolynomialSeed lam mu
      (youngAmbientRotation mu a b p)
  exact reverseInterlacingPolynomialSeed_rotation_intertwine
    lam mu a b p

end ArbitraryRankHarmonicBranchRotationIntertwining

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGelfandTsetlinCanonicalFibre

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranchRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentFibrePhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankGelfandTsetlinGramRotationCommutation
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungMovingFibres

/-- The positive gelfand tsetlin fischer gram used in the spherical-code argument. -/
def PositiveGelfandTsetlinFischerGram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪reverseInterlacingHarmonicBranch lam mu h p,
        reverseInterlacingHarmonicBranch lam mu h q⟫_ℝ =
        c * ⟪p, q⟫_ℝ

/-- The canonical gelfand tsetlin fischer gram used in the spherical-code argument. -/
def canonicalGelfandTsetlinFischerGram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) : ℝ :=
  Classical.choose hgram

theorem canonicalGelfandTsetlinFischerGram_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    0 < canonicalGelfandTsetlinFischerGram lam mu h hgram :=
  (Classical.choose_spec hgram).1

theorem canonicalGelfandTsetlinFischerGram_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪reverseInterlacingHarmonicBranch lam mu h p,
      reverseInterlacingHarmonicBranch lam mu h q⟫_ℝ =
      canonicalGelfandTsetlinFischerGram lam mu h hgram * ⟪p, q⟫_ℝ :=
  (Classical.choose_spec hgram).2 p q

theorem positiveGelfandTsetlinFischerGram_of_irreducible
    {r n : ℕ} (hn : 2 * (r + 1) < n)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hirred : ∀ W : Submodule ℝ (HarmonicYoungSpace (n := n) mu),
      IsRotationInvariant (youngRotationFamily mu) W →
        W = ⊥ ∨ W = ⊤) :
    PositiveGelfandTsetlinFischerGram (n := n) lam mu h := by
  obtain ⟨c, hc⟩ :=
    reverseInterlacingHarmonicBranchGram_eq_smul_id_of_irreducible
      lam mu h hirred
      (fun a b => reverseInterlacingHarmonicBranch_rotation_intertwine
        lam mu h a b)
  obtain ⟨p, hp⟩ := exists_nonzero_harmonicYoung_of_antitone
    (show 2 * (r + 1) ≤ n by omega) mu
    (interlaces_antitone_stabilizer h)
  have hpositive := reverseInterlacingHarmonicBranchGram_scalar_pos
    lam mu h (reverseInterlacingHarmonicBranch_injective hn lam mu h)
    p hp c hc
  refine ⟨c, hpositive, ?_⟩
  intro q t
  calc
    ⟪reverseInterlacingHarmonicBranch lam mu h q,
      reverseInterlacingHarmonicBranch lam mu h t⟫_ℝ =
        ⟪reverseInterlacingHarmonicBranchGram lam mu h q, t⟫_ℝ := by
          symm
          exact LinearMap.adjoint_inner_left
            (reverseInterlacingHarmonicBranch lam mu h)
            t (reverseInterlacingHarmonicBranch lam mu h q)
    _ = ⟪c • q, t⟫_ℝ := by rw [hc]; rfl
    _ = c * ⟪q, t⟫_ℝ := real_inner_smul_left q t c

/-- The canonical gelfand tsetlin fibre used in the spherical-code argument. -/
def canonicalGelfandTsetlinFibre
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
  normalizedGelfandTsetlinFibre lam mu h
    (canonicalGelfandTsetlinFischerGram lam mu h hgram)
    (canonicalGelfandTsetlinFischerGram_pos lam mu h hgram)
    (canonicalGelfandTsetlinFischerGram_inner lam mu h hgram)

@[simp] theorem canonicalGelfandTsetlinFibre_apply
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinFibre lam mu h hgram p =
      (Real.sqrt (canonicalGelfandTsetlinFischerGram
        lam mu h hgram))⁻¹ •
          reverseInterlacingHarmonicBranch lam mu h p := rfl

theorem canonicalGelfandTsetlinFibre_phase_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    0 < (Real.sqrt
      (canonicalGelfandTsetlinFischerGram lam mu h hgram))⁻¹ :=
  normalizedGelfandTsetlinFibre_phase_pos
    (canonicalGelfandTsetlinFischerGram_pos lam mu h hgram)

theorem canonicalGelfandTsetlinFibre_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap := by
  apply LinearMap.ext
  intro p
  change
    (Real.sqrt (canonicalGelfandTsetlinFischerGram
      lam mu h hgram))⁻¹ •
        reverseInterlacingHarmonicBranch lam mu h
          (youngAmbientRotation mu a b p) =
      youngAmbientRotation lam a.castSucc b.castSucc
        ((Real.sqrt (canonicalGelfandTsetlinFischerGram
          lam mu h hgram))⁻¹ •
            reverseInterlacingHarmonicBranch lam mu h p)
  rw [map_smul]
  congr 1
  exact DFunLike.congr_fun
    (reverseInterlacingHarmonicBranch_rotation_intertwine lam mu h a b) p

theorem canonicalGelfandTsetlinFibre_channel_apply
    {r n : ℕ} (source target : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hsource : Interlaces source mu) (htarget : Interlaces target mu)
    (hsourceGram : PositiveGelfandTsetlinFischerGram
      (n := n) source mu hsource)
    (htargetGram : PositiveGelfandTsetlinFischerGram
      (n := n) target mu htarget)
    (channel : HarmonicYoungSpace (n := n + 1) source →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1) target)
    (coefficient : ℝ)
    (haxis : ∀ p : HarmonicYoungSpace (n := n) mu,
      channel (reverseInterlacingHarmonicBranch source mu hsource p) =
        coefficient • reverseInterlacingHarmonicBranch target mu htarget p)
    (p : HarmonicYoungSpace (n := n) mu) :
    channel (canonicalGelfandTsetlinFibre
      source mu hsource hsourceGram p) =
      adjacentNormalizedAxisCoefficient
        (canonicalGelfandTsetlinFischerGram source mu hsource hsourceGram)
        (canonicalGelfandTsetlinFischerGram target mu htarget htargetGram)
        coefficient •
      canonicalGelfandTsetlinFibre
        target mu htarget htargetGram p := by
  exact normalizedGelfandTsetlinFibre_channel_apply
    source target mu hsource htarget
    (canonicalGelfandTsetlinFischerGram source mu hsource hsourceGram)
    (canonicalGelfandTsetlinFischerGram target mu htarget htargetGram)
    (canonicalGelfandTsetlinFischerGram_pos source mu hsource hsourceGram)
    (canonicalGelfandTsetlinFischerGram_pos target mu htarget htargetGram)
    (canonicalGelfandTsetlinFischerGram_inner source mu hsource hsourceGram)
    (canonicalGelfandTsetlinFischerGram_inner target mu htarget htargetGram)
    channel coefficient haxis p

/-- The canonical box gelfand tsetlin fibre used in the spherical-code argument. -/
def canonicalBoxGelfandTsetlinFibre {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n - 1)
        (boxSignature (m := m) a n i)
        (Weyl.flooredWeight b n)
        (boxSignature_interlaces a b hstable i))
    (i : BoxIndex (r + 1) m) :
    BoxStabilizer n b →ₗᵢ[ℝ]
      YoungVertex (n := n) (boxSignature (m := m) a n) i := by
  cases n with
  | zero =>
      have hn := box_stableRange a b hstable
      omega
  | succ d =>
      exact canonicalGelfandTsetlinFibre
        (boxSignature (m := m) a (d + 1) i)
        (Weyl.flooredWeight b (d + 1))
        (boxSignature_interlaces a b hstable i)
        (hgram i)

end AllRankGelfandTsetlinCanonicalFibre

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankReverseProjectedFibreCoefficient

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
open MetricCodes.Spherical.HigherRepresentationGraph

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projectedCoordinateLower_fibre_inner_of_forward
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (axis : SpherePacking.Euclidean n)
    (lowFibre : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) low)
    (highFibre : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) high)
    (coefficient : ℝ)
    (hforward : ∀ p : E,
      projectedCoordinateRaise high low hdeg row axis (lowFibre p) =
        coefficient • highFibre p)
    (p q : E) :
    ⟪lowFibre p,
      projectedCoordinateLower low high hdeg row axis (highFibre q)⟫_ℝ =
      coefficient * ⟪p, q⟫_ℝ := by
  calc
    _ = ⟪projectedCoordinateRaise high low hdeg row axis
          (lowFibre p), highFibre q⟫_ℝ :=
      (projectedCoordinateRaise_inner high low hdeg row axis
        (lowFibre p) (highFibre q)).symm
    _ = ⟪coefficient • highFibre p, highFibre q⟫_ℝ := by
      rw [hforward]
    _ = coefficient * ⟪highFibre p, highFibre q⟫_ℝ :=
      real_inner_smul_left _ _ coefficient
    _ = _ := by
      congr 1
      exact highFibre.inner_map_map p q

theorem projectedCoordinateLower_fibre_eq_of_forward_of_mem_range
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (axis : SpherePacking.Euclidean n)
    (lowFibre : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) low)
    (highFibre : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) high)
    (coefficient : ℝ)
    (hforward : ∀ p : E,
      projectedCoordinateRaise high low hdeg row axis (lowFibre p) =
        coefficient • highFibre p)
    (hrange : ∀ q : E,
      projectedCoordinateLower low high hdeg row axis (highFibre q) ∈
        LinearMap.range lowFibre.toLinearMap)
    (q : E) :
    projectedCoordinateLower low high hdeg row axis (highFibre q) =
      coefficient • lowFibre q := by
  obtain ⟨w, hw⟩ := hrange q
  calc
    _ = lowFibre w := hw.symm
    _ = coefficient • lowFibre q := by
      rw [← lowFibre.map_smul]
      congr 1
      apply ext_inner_left ℝ
      intro p
      have hp := projectedCoordinateLower_fibre_inner_of_forward
        high low hdeg row axis lowFibre highFibre
        coefficient hforward p q
      rw [← hw] at hp
      change ⟪lowFibre p, lowFibre w⟫_ℝ =
        coefficient * ⟪p, q⟫_ℝ at hp
      calc
        ⟪p, w⟫_ℝ = ⟪lowFibre p, lowFibre w⟫_ℝ :=
          (lowFibre.inner_map_map p w).symm
        _ = coefficient * ⟪p, q⟫_ℝ := hp
        _ = ⟪p, coefficient • q⟫_ℝ :=
          (real_inner_smul_right p q coefficient).symm

end AllRankReverseProjectedFibreCoefficient

end

section


namespace BGGRootComplex

open MetricCodes.Spherical.HigherHarmonicYoung
open scoped BigOperators

theorem polarization_polarization_commutator {r n : ℕ}
    (a b c d : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n a b (polarization r n c d p) =
      polarization r n c d (polarization r n a b p) +
        (if b = c then polarization r n a d p else 0) -
          (if d = a then polarization r n c b p else 0) := by
  classical
  have hcross :
      (∑ k : Fin n,
        MvPolynomial.X (variableIndex a k) *
          polarization r n c d
            (MvPolynomial.pderiv (variableIndex b k) p)) =
        ∑ l : Fin n,
          MvPolynomial.X (variableIndex c l) *
            polarization r n a b
              (MvPolynomial.pderiv (variableIndex d l) p) := by
    simp_rw [polarization_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex b k) (variableIndex d l) p]
    ring
  have hleft :
      polarization r n a b (polarization r n c d p) =
        (if b = c then polarization r n a d p else 0) +
          ∑ k : Fin n,
            MvPolynomial.X (variableIndex a k) *
              polarization r n c d
                (MvPolynomial.pderiv (variableIndex b k) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift, mul_add]
    rw [Finset.sum_add_distrib]
    by_cases hbc : b = c
    · simp only [hbc, ↓reduceIte, polarization_apply]
    · simp only [hbc, ↓reduceIte, mul_zero, Finset.sum_const_zero, polarization_apply, zero_add]
  have hright :
      polarization r n c d (polarization r n a b p) =
        (if d = a then polarization r n c b p else 0) +
          ∑ l : Fin n,
            MvPolynomial.X (variableIndex c l) *
              polarization r n a b
                (MvPolynomial.pderiv (variableIndex d l) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift, mul_add]
    rw [Finset.sum_add_distrib]
    by_cases hda : d = a
    · simp only [hda, ↓reduceIte, polarization_apply]
    · simp only [hda, ↓reduceIte, mul_zero, Finset.sum_const_zero, polarization_apply, zero_add]
  rw [hleft, hright, hcross]
  abel

end BGGRootComplex

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungInternalRowPolarizationDescent

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex

theorem upperPolarization_internalRowDerivative
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a b : Fin (r + 1)) (hab : a < b)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n) :
    polarization r n a b
        (MvPolynomial.pderiv (variableIndex a k)
          (p : PolynomialSpace r n)) =
      -MvPolynomial.pderiv (variableIndex b k)
        (p : PolynomialSpace r n) := by
  have hhighest :=
    ((mem_harmonicYoungSubmodule lam
      (p : PolynomialSpace r n)).mp p.property).2.2.2 a b hab
  have hcomm := pderiv_polarization_harmonicLift
    a a b k (p : PolynomialSpace r n)
  rw [hhighest, map_zero, ite_eq_left rfl] at hcomm
  exact eq_neg_of_add_eq_zero_right hcomm.symm

end HigherYoungInternalRowPolarizationDescent

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungPenultimateRowProjectedLower

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex
open MetricCodes.Spherical.HigherYoungInternalRowPolarizationDescent

/-- The lowered internal young weight used in the spherical-code argument. -/
def loweredInternalYoungWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) :
    Fin (r + 1) → ℕ :=
  Function.update lam a (lam a - 1)

@[simp] theorem loweredInternalYoungWeight_self {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) :
    loweredInternalYoungWeight lam a a = lam a - 1 := by
  simp only [loweredInternalYoungWeight, Function.update_self]

@[simp] theorem loweredInternalYoungWeight_of_ne {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a c : Fin (r + 1))
    (hca : c ≠ a) :
    loweredInternalYoungWeight lam a c = lam c := by
  simp only [loweredInternalYoungWeight, ne_eq, hca, not_false_eq_true, Function.update_of_ne]

theorem loweredInternalYoungWeight_sum_add_one {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1))
    (ha : 0 < lam a) :
    (∑ c : Fin (r + 1), lam c) =
      (∑ c : Fin (r + 1), loweredInternalYoungWeight lam a c) + 1 := by
  classical
  unfold loweredInternalYoungWeight
  rw [Finset.sum_update_of_mem (Finset.mem_univ a),
    Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.add_sum_erase
    (Finset.univ : Finset (Fin (r + 1))) lam
    (Finset.mem_univ a)
  omega

theorem internalRowDerivative_mem_traceFree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n) :
    MvPolynomial.pderiv (variableIndex a k)
        (p : PolynomialSpace r n) ∈ traceFreeSubmodule r n := by
  rw [mem_traceFreeSubmodule]
  intro c d
  rw [traceOperator_pderiv_comm,
    ((mem_harmonicYoungSubmodule lam
      (p : PolynomialSpace r n)).mp p.property).2.2.1 c d,
    map_zero]

end HigherYoungPenultimateRowProjectedLower

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRowDownstreamCorrection

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

private def downstreamShift {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a i : Fin (r + 1)) : ℝ :=
  (lam a : ℝ) - (lam i : ℝ) + (i.val : ℝ) - (a.val : ℝ)

@[simp] theorem downstreamShift_self {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) :
    downstreamShift lam a a = 0 := by
  simp only [downstreamShift, sub_self, zero_add]

theorem downstreamShift_pos {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a i : Fin (r + 1))
    (hai : a < i) (hdom : lam i ≤ lam a) :
    0 < downstreamShift lam a i := by
  have hweight : (lam i : ℝ) ≤ lam a := by exact_mod_cast hdom
  have hrow : (a.val : ℝ) < i.val := by exact_mod_cast hai
  unfold downstreamShift
  linarith

theorem downstreamShift_ne_zero {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a i : Fin (r + 1))
    (hai : a < i) (hdom : lam i ≤ lam a) :
    downstreamShift lam a i ≠ 0 :=
  ne_of_gt (downstreamShift_pos lam a i hai hdom)

private def downstreamCorrectedDerivative
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i : Fin (r + 1)) : PolynomialSpace r n :=
  MvPolynomial.pderiv (variableIndex i k)
      (p : PolynomialSpace r n) +
    ∑ j : Fin (r + 1),
      if _h : i < j then
        (downstreamShift lam a j)⁻¹ •
          polarization r n j i
            (downstreamCorrectedDerivative lam a p k j)
      else 0
termination_by r + 1 - i.val
decreasing_by
  have _hij : i.val < j.val := _h
  have _hjbound : j.val < r + 1 := j.isLt
  omega

theorem downstreamCorrectedDerivative_eq
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i : Fin (r + 1)) :
    downstreamCorrectedDerivative lam a p k i =
      MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n) +
        ∑ j : Fin (r + 1),
          if _h : i < j then
            (downstreamShift lam a j)⁻¹ •
              polarization r n j i
                (downstreamCorrectedDerivative lam a p k j)
          else 0 := by
  rw [downstreamCorrectedDerivative]

end HigherYoungArbitraryRowDownstreamCorrection

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankInternalRowLowerGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungInternalRowPolarizationDescent

private def downstreamRows {r : ℕ}
    (row : Fin (r + 1)) : Finset (Fin (r + 1)) :=
  Finset.univ.filter (fun q => row < q)

@[simp] theorem mem_downstreamRows {r : ℕ}
    (row q : Fin (r + 1)) : q ∈ downstreamRows row ↔ row < q := by
  simp only [downstreamRows, Finset.mem_filter, Finset.mem_univ, true_and]

private def downstreamNumerator {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row q : Fin (r + 1)) : ℝ :=
  ((lam row - lam q : ℕ) : ℝ) +
    ((q.val - row.val - 1 : ℕ) : ℝ)

private def downstreamDenominator {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row q : Fin (r + 1)) : ℝ :=
  ((lam row - lam q : ℕ) : ℝ) +
    ((q.val - row.val : ℕ) : ℝ)

/-- The internal row lower gram scalar used in the spherical-code argument. -/
def internalRowLowerGramScalar {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) : ℝ :=
  ((lam row : ℝ) + ((r - row.val : ℕ) : ℝ)) *
    ∏ q ∈ downstreamRows row,
      downstreamNumerator lam row q / downstreamDenominator lam row q

theorem downstreamDenominator_pos {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row q : Fin (r + 1))
    (hq : row < q) :
    0 < downstreamDenominator lam row q := by
  unfold downstreamDenominator
  have hindex : 0 < q.val - row.val := by
    have hval : row.val < q.val := hq
    omega
  have hreal : 0 < ((q.val - row.val : ℕ) : ℝ) := by
    exact_mod_cast hindex
  positivity

theorem downstreamNumerator_pos {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row q : Fin (r + 1))
    (hq : row < q)
    (hstrict : ∀ j : Fin (r + 1),
      j.val = row.val + 1 → lam j < lam row) :
    0 < downstreamNumerator lam row q := by
  unfold downstreamNumerator
  by_cases hadj : q.val = row.val + 1
  · have hgap : 0 < lam row - lam q :=
      Nat.sub_pos_of_lt (hstrict q hadj)
    have hreal : 0 < ((lam row - lam q : ℕ) : ℝ) := by
      exact_mod_cast hgap
    positivity
  · have hindex : 0 < q.val - row.val - 1 := by
      have hval : row.val < q.val := hq
      omega
    have hreal : 0 < ((q.val - row.val - 1 : ℕ) : ℝ) := by
      exact_mod_cast hindex
    positivity

theorem internalRowLowerGramScalar_pos {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hrow : 0 < lam row)
    (hstrict : ∀ j : Fin (r + 1),
      j.val = row.val + 1 → lam j < lam row) :
    0 < internalRowLowerGramScalar lam row := by
  unfold internalRowLowerGramScalar
  apply mul_pos
  · have hrowR : 0 < (lam row : ℝ) := by exact_mod_cast hrow
    positivity
  · apply Finset.prod_pos
    intro q hq
    have hlt := (mem_downstreamRows row q).mp hq
    exact div_pos (downstreamNumerator_pos lam row q hlt hstrict)
      (downstreamDenominator_pos lam row q hlt)

@[simp] theorem downstreamRows_last {r : ℕ} :
    downstreamRows (Fin.last r) = ∅ := by
  ext q
  simp only [downstreamRows, Finset.mem_filter, Finset.mem_univ, not_lt_of_ge (Fin.le_last q),
    and_false, Finset.notMem_empty]

end ArbitraryRankInternalRowLowerGram

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowProjectedLowerOperator

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

private def upperPolarizationPath {r n : ℕ} :
    List (Fin (r + 1)) →
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
  | [] => LinearMap.id
  | [_] => LinearMap.id
  | i :: j :: rest =>
      (upperPolarizationPath (j :: rest)).comp
        (polarization r n i j)

theorem lowerPolarizationPath_fischer_adjoint
    {r n : ℕ} (path : List (Fin (r + 1)))
    (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (lowerPolarizationPath path p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (upperPolarizationPath path q) := by
  induction path generalizing p q with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          change
            SpherePacking.Fischer.polynomialInner ((r + 1) * n)
                (polarization r n j i
                  (lowerPolarizationPath (j :: tail) p)) q =
              SpherePacking.Fischer.polynomialInner ((r + 1) * n)
                p (upperPolarizationPath (j :: tail)
                  (polarization r n i j q))
          rw [polynomialInner_polarization_harmonicLift]
          exact ih p (polarization r n i j q)

private def arbitraryRowAxialLower {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) (k : Fin n) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ S ∈ (precedingRows row).powerset,
    polarizationPathCoefficient lam row S •
      ((upperPolarizationPath
          ((S.sort (· ≤ ·)) ++ [row])).comp
        (MvPolynomial.pderiv
          (variableIndex (polarizationPathStart row S) k)).toLinearMap)

@[simp] theorem arbitraryRowAxialLower_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) (k : Fin n)
    (q : PolynomialSpace r n) :
    arbitraryRowAxialLower lam row k q =
      ∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          upperPolarizationPath
            ((S.sort (· ≤ ·)) ++ [row])
            (MvPolynomial.pderiv
              (variableIndex (polarizationPathStart row S) k) q) := by
  simp only [arbitraryRowAxialLower, LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_comp,
    Derivation.coeFn_coe, Finset.sum_apply, Pi.smul_apply, Function.comp_apply]

theorem arbitraryRowAxialRaise_fischer_adjoint
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (arbitraryRowAxialRaise lam row k p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (arbitraryRowAxialLower lam row k q) := by
  classical
  rw [arbitraryRowAxialRaise_apply, arbitraryRowAxialLower_apply,
    SpherePacking.Fischer.polynomialInner_sum_left,
    SpherePacking.Fischer.polynomialInner_sum_right]
  apply Finset.sum_congr rfl
  intro S hS
  rw [SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_right,
    SpherePacking.Fischer.polynomialInner_X_mul,
    lowerPolarizationPath_fischer_adjoint]

theorem upperPolarization_pderiv_of_highest
    {r n : ℕ} (i j : Fin (r + 1)) (hij : i < j)
    (k : Fin n) (q : PolynomialSpace r n)
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b q = 0) :
    polarization r n i j
        (MvPolynomial.pderiv (variableIndex i k) q) =
      -MvPolynomial.pderiv (variableIndex j k) q := by
  have hcomm := pderiv_polarization_harmonicLift i i j k q
  rw [hhighest i j hij, map_zero, ite_eq_left rfl] at hcomm
  exact eq_neg_of_add_eq_zero_right hcomm.symm

theorem upperPolarizationPath_pderiv_of_highest
    {r n : ℕ} (row : Fin (r + 1))
    (front : List (Fin (r + 1))) (k : Fin n)
    (q : PolynomialSpace r n)
    (hordered : (front ++ [row]).Pairwise (· < ·))
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b q = 0) :
    upperPolarizationPath (front ++ [row])
        (MvPolynomial.pderiv
          (variableIndex (front.headD row) k) q) =
      ((-1 : ℝ) ^ front.length) •
        MvPolynomial.pderiv (variableIndex row k) q := by
  induction front with
  | nil => simp only [List.nil_append, upperPolarizationPath, List.headD_eq_head?_getD,
             List.head?_nil, Option.getD_none, LinearMap.id_coe, id_eq, List.length_nil, pow_zero,
             one_smul]
  | cons i tail ih =>
      cases tail with
      | nil =>
          have hij : i < row :=
            (List.pairwise_cons.mp hordered).1 row (by simp only [List.append_eq, List.nil_append,
                                                         List.mem_cons, List.not_mem_nil, or_false])
          change
            polarization r n i row
                (MvPolynomial.pderiv (variableIndex i k) q) =
              ((-1 : ℝ) ^ 1) •
                MvPolynomial.pderiv (variableIndex row k) q
          rw [upperPolarization_pderiv_of_highest i row hij k q hhighest]
          simp only [pow_one, neg_smul, one_smul]
      | cons j rest =>
          have hpairs := List.pairwise_cons.mp hordered
          have hij : i < j := hpairs.1 j (by simp only [List.append_eq, List.cons_append,
                                               List.mem_cons, List.mem_append, List.not_mem_nil,
                                               or_false, true_or])
          have hrest :
              upperPolarizationPath ((j :: rest) ++ [row])
                  (MvPolynomial.pderiv (variableIndex j k) q) =
                ((-1 : ℝ) ^ (j :: rest).length) •
                  MvPolynomial.pderiv (variableIndex row k) q := by
            simpa only [List.cons_append, List.length_cons, List.headD_eq_head?_getD,
              List.head?_cons, Option.getD_some] using ih hpairs.2
          change
            upperPolarizationPath ((j :: rest) ++ [row])
              (polarization r n i j
                (MvPolynomial.pderiv (variableIndex i k) q)) =
              ((-1 : ℝ) ^ (j :: rest).length.succ) •
                MvPolynomial.pderiv (variableIndex row k) q
          rw [upperPolarization_pderiv_of_highest i j hij k q hhighest,
            map_neg, hrest]
          simp only [List.length_cons, pow_succ, mul_neg, mul_one, neg_smul, neg_neg,
            Nat.succ_eq_add_one]

theorem polarizationPathStart_eq_sort_headD
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1))) :
    polarizationPathStart row S = (S.sort (· ≤ ·)).headD row := by
  classical
  by_cases hS : S.Nonempty
  · have hlen : 0 < (S.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      exact Finset.card_pos.mpr hS
    have hmin : S.min' hS =
        (S.sort (· ≤ ·))[0]'hlen := Finset.min'_eq_sorted_zero
    cases hsort : S.sort (· ≤ ·) with
    | nil => simp only [hsort, List.length_nil, lt_self_iff_false] at hlen
    | cons a tail =>
        have ha : S.min' hS = a := by
          simpa only [hsort, List.getElem_cons_zero] using hmin
        simp only [polarizationPathStart, hS, ↓reduceDIte, ha, List.headD_eq_head?_getD,
          List.head?_cons, Option.getD_some]
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, polarizationPathStart_empty, Finset.sort_empty, List.headD_eq_head?_getD,
      List.head?_nil, Option.getD_none]

end ArbitraryRowProjectedLowerOperator

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungArbitraryRowDownstreamPathPairing

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowProjectedLowerOperator
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungInternalRowPolarizationDescent

theorem internalDerivative_downstreamPolarization_fischer_inner
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j)
    (p : HarmonicYoungSpace (n := n) lam)
    (v : PolynomialSpace r n) (k : Fin n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n))
        (polarization r n j i v) =
      -SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex j k)
          (p : PolynomialSpace r n)) v := by
  rw [SpherePacking.Fischer.polynomialInner_comm ((r + 1) * n),
    polynomialInner_polarization_harmonicLift,
    upperPolarization_internalRowDerivative lam i j hij p k,
    ← neg_one_smul ℝ,
    SpherePacking.Fischer.polynomialInner_smul_right,
    SpherePacking.Fischer.polynomialInner_comm ((r + 1) * n)]
  ring

theorem downstreamCorrectedDerivative_fischer_cross_recurrence
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) lam) (k : Fin n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n))
        (downstreamCorrectedDerivative lam a q k i) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n))
        (MvPolynomial.pderiv (variableIndex i k)
          (q : PolynomialSpace r n)) -
        ∑ j : Fin (r + 1),
          if _h : i < j then
            (downstreamShift lam a j)⁻¹ *
              SpherePacking.Fischer.polynomialInner ((r + 1) * n)
                (MvPolynomial.pderiv (variableIndex j k)
                  (p : PolynomialSpace r n))
                (downstreamCorrectedDerivative lam a q k j)
          else 0 := by
  rw [downstreamCorrectedDerivative_eq,
    SpherePacking.Fischer.polynomialInner_add_right,
    SpherePacking.Fischer.polynomialInner_sum_right,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [SpherePacking.Fischer.polynomialInner_smul_right,
      internalDerivative_downstreamPolarization_fischer_inner
        lam i j hij p _ k]
    ring
  · simp only [SpherePacking.Fischer.polynomialInner, MvPolynomial.coeff_zero, mul_zero,
      Finsupp.sum_fun_zero, neg_zero]

theorem downstreamCorrectedDerivative_fischer_cross_sum_recurrence
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) lam) :
    (∑ k : Fin n,
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n))
        (downstreamCorrectedDerivative lam a q k i)) =
      (lam i : ℝ) * ⟪p, q⟫_ℝ -
        ∑ j : Fin (r + 1),
          if _h : i < j then
            (downstreamShift lam a j)⁻¹ *
              ∑ k : Fin n,
                SpherePacking.Fischer.polynomialInner ((r + 1) * n)
                  (MvPolynomial.pderiv (variableIndex j k)
                    (p : PolynomialSpace r n))
                  (downstreamCorrectedDerivative lam a q k j)
          else 0 := by
  simp_rw [downstreamCorrectedDerivative_fischer_cross_recurrence
    lam a i p q]
  rw [Finset.sum_sub_distrib,
    rowDerivative_fischer_inner_sum lam i p q]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [Finset.mul_sum]
  · simp only [Finset.sum_const_zero]

end HigherYoungArbitraryRowDownstreamPathPairing

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRowDownstreamMembership

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection

private def loweredRowEigenvalue {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i c : Fin (r + 1)) : ℝ :=
  (lam c : ℝ) - if c = i then 1 else 0

theorem downstreamCorrectedDerivative_mem_traceFree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i : Fin (r + 1)) :
    downstreamCorrectedDerivative lam a p k i ∈
      traceFreeSubmodule r n := by
  induction i using
      (measure (fun j : Fin (r + 1) => r + 1 - j.val)).wf.induction with
  | h i ih =>
    rw [downstreamCorrectedDerivative_eq]
    apply (traceFreeSubmodule r n).add_mem
      (internalRowDerivative_mem_traceFree lam i p k)
    apply Submodule.sum_mem
    intro j _
    split_ifs with hij
    · apply (traceFreeSubmodule r n).smul_mem
      apply polarization_mem_traceFreeSubmodule j i
      apply ih j
      change r + 1 - j.val < r + 1 - i.val
      have hji : i.val < j.val := hij
      have hjbound : j.val < r + 1 := j.isLt
      omega
    · exact (traceFreeSubmodule r n).zero_mem

theorem internalDerivative_rowEuler_shifted
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i c : Fin (r + 1)) :
    rowEuler r n c
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n)) =
      loweredRowEigenvalue lam i c •
        MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n) := by
  have hp := ((mem_harmonicYoungSubmodule lam
    (p : PolynomialSpace r n)).mp p.property).2.1
  by_cases hci : c = i
  · subst c
    rw [rowEuler_pderiv_self, hp i,
      (MvPolynomial.pderiv _).map_smul]
    simp only [loweredRowEigenvalue, ↓reduceIte, sub_smul, one_smul]
  · rw [rowEuler_pderiv_of_ne c i k hci,
      hp c, (MvPolynomial.pderiv _).map_smul]
    simp only [loweredRowEigenvalue, hci, ↓reduceIte, sub_zero]

theorem downstreamPolarization_rowEuler_shifted
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j c : Fin (r + 1)) (hij : i < j)
    (q : PolynomialSpace r n)
    (hq : rowEuler r n c q = loweredRowEigenvalue lam j c • q) :
    rowEuler r n c (polarization r n j i q) =
      loweredRowEigenvalue lam i c • polarization r n j i q := by
  rw [rowEuler_polarization_commutator, hq, map_smul]
  by_cases hci : c = i
  · subst c
    have hijne : i ≠ j := hij.ne
    simp only [loweredRowEigenvalue, hijne, ↓reduceIte, sub_zero, polarization_apply, add_zero,
      sub_smul, one_smul]
  · by_cases hcj : c = j
    · subst c
      have hji : j ≠ i := hij.ne.symm
      simp only [loweredRowEigenvalue, ↓reduceIte, polarization_apply, sub_smul, one_smul,
        sub_add_cancel, hji, sub_zero]
    · simp only [loweredRowEigenvalue, hcj, ↓reduceIte, sub_zero, polarization_apply, add_zero, hci]

theorem downstreamCorrectedDerivative_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i c : Fin (r + 1)) :
    rowEuler r n c (downstreamCorrectedDerivative lam a p k i) =
      loweredRowEigenvalue lam i c •
        downstreamCorrectedDerivative lam a p k i := by
  induction i using
      (measure (fun j : Fin (r + 1) => r + 1 - j.val)).wf.induction with
  | h i ih =>
    rw [downstreamCorrectedDerivative_eq, map_add, map_sum,
      internalDerivative_rowEuler_shifted lam p k i c,
      smul_add, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · rw [map_smul,
        downstreamPolarization_rowEuler_shifted lam i j c hij _
          (ih j (by
            change r + 1 - j.val < r + 1 - i.val
            have hji : i.val < j.val := hij
            have hjbound : j.val < r + 1 := j.isLt
            omega)),
        smul_smul, smul_smul]
      simp only [mul_comm]
    · simp only [map_zero, smul_zero]

theorem downstreamCorrectedDerivative_source_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (c : Fin (r + 1)) :
    rowEuler r n c (downstreamCorrectedDerivative lam a p k a) =
      (loweredInternalYoungWeight lam a c : ℝ) •
        downstreamCorrectedDerivative lam a p k a := by
  rw [downstreamCorrectedDerivative_rowEuler]
  congr 1
  by_cases hca : c = a
  · subst c
    simp only [loweredRowEigenvalue, ↓reduceIte, loweredInternalYoungWeight_self,
      Nat.cast_sub (show 1 ≤ lam a by omega), Nat.cast_one]
  · simp only [loweredRowEigenvalue, hca, ↓reduceIte, sub_zero, ne_eq, not_false_eq_true,
      loweredInternalYoungWeight_of_ne]

end HigherYoungArbitraryRowDownstreamMembership

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRowDownstreamHarmonicMembership

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamMembership

theorem downstreamCorrectedDerivative_source_mem_multihomogeneous
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n) :
    downstreamCorrectedDerivative lam a p k a ∈
      youngMultihomogeneousSubmodule n
        (loweredInternalYoungWeight lam a) := by
  apply (mem_youngMultihomogeneousSubmodule_iff_rowEuler
    (loweredInternalYoungWeight lam a) _).mpr
  exact downstreamCorrectedDerivative_source_rowEuler lam a ha p k

theorem downstreamCorrectedDerivative_source_mem_harmonicYoung_of_simpleRoots
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (hsimple : ∀ j : Fin r,
      polarization r n j.castSucc j.succ
        (downstreamCorrectedDerivative lam a p k a) = 0) :
    downstreamCorrectedDerivative lam a p k a ∈
      harmonicYoungSubmodule (loweredInternalYoungWeight lam a) := by
  apply
    (mem_harmonicYoungSubmodule_iff_multihomogeneous_firstTrace_highestWeight
      (loweredInternalYoungWeight lam a) _).mpr
  refine ⟨downstreamCorrectedDerivative_source_mem_multihomogeneous
    lam a ha p k, ?_, ?_⟩
  · exact (mem_traceFreeSubmodule _).mp
      (downstreamCorrectedDerivative_mem_traceFree lam a p k a) 0 0
  · exact polarization_eq_zero_of_simpleRoots _ hsimple

end HigherYoungArbitraryRowDownstreamHarmonicMembership

namespace HigherHarmonicYoung.ArbitraryRowDownstreamScalarTelescoping

private def downstreamScalarFactor (A B : ℝ) (i : ℕ) : ℝ :=
  (A - B + (i : ℝ)) / (A - B + ((i + 1 : ℕ) : ℝ))

theorem downstreamScalar_backward_step
    (A current next leading tail : ℝ) (i : ℕ)
    (hden : A - next + ((i + 1 : ℕ) : ℝ) ≠ 0) :
    (current - next) +
        (1 - (A - next + ((i + 1 : ℕ) : ℝ))⁻¹) *
          (leading * tail -
            (A - next + ((i + 1 : ℕ) : ℝ))) =
      leading * (tail * downstreamScalarFactor A next i) -
        (A - current + (i : ℝ)) := by
  unfold downstreamScalarFactor
  norm_num [Nat.cast_add, Nat.cast_one] at hden ⊢
  field_simp [hden]
  ring

end HigherHarmonicYoung.ArbitraryRowDownstreamScalarTelescoping

end

section


open scoped BigOperators

namespace HigherYoungDownstreamFiniteIntervalSums

private def strictDownstreamRows {m : ℕ} (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => i < j)

private def strictBetweenRows {m : ℕ} (i d : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => i < j ∧ j < d)

@[simp] theorem mem_strictDownstreamRows {m : ℕ} (i j : Fin m) :
    j ∈ strictDownstreamRows i ↔ i < j := by
  simp only [strictDownstreamRows, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_strictBetweenRows {m : ℕ} (i d j : Fin m) :
    j ∈ strictBetweenRows i d ↔ i < j ∧ j < d := by
  simp only [strictBetweenRows, Finset.mem_filter, Finset.mem_univ, true_and]

theorem strictBetweenRows_eq_Ioo {m : ℕ} (i d : Fin m) :
    strictBetweenRows i d = Finset.Ioo i d := by
  ext j
  simp only [mem_strictBetweenRows, Finset.mem_Ioo]

theorem card_strictBetweenRows {m : ℕ} (i d : Fin m) :
    (strictBetweenRows i d).card = d.val - i.val - 1 := by
  rw [strictBetweenRows_eq_Ioo, Fin.card_Ioo]

theorem strictBetweenRows_eq_empty_of_succ {m : ℕ} (i d : Fin m)
    (hid : d.val = i.val + 1) :
    strictBetweenRows i d = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_strictBetweenRows]
  omega

theorem disjoint_strictBetween_singleton {m : ℕ} (i d : Fin m) :
    Disjoint (strictBetweenRows i d) {d} := by
  rw [Finset.disjoint_left]
  intro j hj hjd
  have hlt := (mem_strictBetweenRows i d j).mp hj
  have heq := Finset.mem_singleton.mp hjd
  subst j
  exact (lt_irrefl d) hlt.2

theorem disjoint_strictBetween_downstream {m : ℕ} (i d : Fin m) :
    Disjoint (strictBetweenRows i d) (strictDownstreamRows d) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact (not_lt_of_gt ((mem_strictBetweenRows i d j).mp hj).2)
    ((mem_strictDownstreamRows d j).mp hj')

theorem disjoint_singleton_downstream {m : ℕ} (d : Fin m) :
    Disjoint ({d} : Finset (Fin m)) (strictDownstreamRows d) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  have heq := Finset.mem_singleton.mp hj
  subst j
  exact (lt_irrefl d) ((mem_strictDownstreamRows d d).mp hj')

theorem disjoint_between_union_singleton_downstream
    {m : ℕ} (i d : Fin m) :
    Disjoint (strictBetweenRows i d ∪ {d}) (strictDownstreamRows d) := by
  exact Finset.disjoint_union_left.mpr
    ⟨disjoint_strictBetween_downstream i d,
      disjoint_singleton_downstream d⟩

theorem strictDownstreamRows_eq_between_union_singleton_union_downstream
    {m : ℕ} (i d : Fin m) (hid : i < d) :
    strictDownstreamRows i =
      (strictBetweenRows i d ∪ {d}) ∪ strictDownstreamRows d := by
  ext j
  simp only [mem_strictDownstreamRows, Finset.mem_union,
    mem_strictBetweenRows, Finset.mem_singleton]
  constructor
  · intro hij
    rcases lt_trichotomy j d with hjd | rfl | hdj
    · exact Or.inl (Or.inl ⟨hij, hjd⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr hdj
  · rintro ((⟨hij, _⟩ | rfl) | hdj)
    · exact hij
    · exact hid
    · exact lt_trans hid hdj

theorem sum_strictDownstreamRows_eq_sum_between_add_add_downstream
    {m : ℕ} {A : Type*} [AddCommMonoid A]
    (i d : Fin m) (hid : i < d) (f : Fin m → A) :
    (∑ j ∈ strictDownstreamRows i, f j) =
      (∑ j ∈ strictBetweenRows i d, f j) + f d +
        ∑ j ∈ strictDownstreamRows d, f j := by
  rw [strictDownstreamRows_eq_between_union_singleton_union_downstream
      i d hid,
    Finset.sum_union (disjoint_between_union_singleton_downstream i d),
    Finset.sum_union (disjoint_strictBetween_singleton i d)]
  simp only [Finset.sum_singleton]

theorem sum_ite_downstream_eq_sum_ite_between_add_add_downstream
    {m : ℕ} {A : Type*} [AddCommMonoid A]
    (i d : Fin m) (hid : i < d) (f : Fin m → A) :
    (∑ j : Fin m, if i < j then f j else 0) =
      (∑ j : Fin m, if i < j ∧ j < d then f j else 0) +
        f d +
        ∑ j : Fin m, if d < j then f j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  exact sum_strictDownstreamRows_eq_sum_between_add_add_downstream
    i d hid f

theorem sum_ite_between_eq_zero_of_succ
    {m : ℕ} {A : Type*} [AddCommMonoid A]
    (i d : Fin m) (hid : d.val = i.val + 1) (f : Fin m → A) :
    (∑ j : Fin m, if i < j ∧ j < d then f j else 0) = 0 := by
  rw [← Finset.sum_filter]
  change (∑ j ∈ strictBetweenRows i d, f j) = 0
  rw [strictBetweenRows_eq_empty_of_succ i d hid]
  simp only [Finset.sum_empty]

end HigherYoungDownstreamFiniteIntervalSums

end

section


open scoped BigOperators

namespace HigherHarmonicYoung.ArbitraryRowDownstreamRecurrenceClosedForm

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamScalarTelescoping
open MetricCodes.Spherical.HigherYoungDownstreamFiniteIntervalSums

theorem downstreamRows_castSucc_eq_insert_succ
    {r : ℕ} (i : Fin r) :
    downstreamRows (i.castSucc : Fin (r + 1)) =
      insert i.succ (downstreamRows i.succ) := by
  ext q
  simp only [mem_downstreamRows, Finset.mem_insert]
  constructor
  · intro h
    by_cases hq : q = i.succ
    · exact Or.inl hq
    · right
      have hv : i.val < q.val := h
      have hne : q.val ≠ i.val + 1 := by
        intro heq
        apply hq
        apply Fin.ext
        simpa only [Fin.val_succ] using heq
      change i.val + 1 < q.val
      omega
  · rintro (rfl | h)
    · exact Fin.castSucc_lt_succ
    · exact lt_trans Fin.castSucc_lt_succ h

theorem downstreamDenominator_eq_downstreamShift
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (a q : Fin (r + 1)) (haq : a < q)
    (hdom : Antitone lam) :
    downstreamDenominator lam a q = downstreamShift lam a q := by
  have hw : lam q ≤ lam a := hdom haq.le
  have hi : a.val ≤ q.val := Nat.le_of_lt haq
  unfold downstreamDenominator downstreamShift
  rw [Nat.cast_sub hw, Nat.cast_sub hi]
  ring

theorem downstreamNumerator_eq_downstreamShift_sub_one
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (a q : Fin (r + 1)) (haq : a < q)
    (hdom : Antitone lam) :
    downstreamNumerator lam a q = downstreamShift lam a q - 1 := by
  have hw : lam q ≤ lam a := hdom haq.le
  have hi : a.val ≤ q.val := Nat.le_of_lt haq
  have hstep : 1 ≤ q.val - a.val := by omega
  unfold downstreamNumerator downstreamShift
  rw [Nat.cast_sub hw, Nat.cast_sub hstep, Nat.cast_sub hi]
  norm_num
  ring

theorem downstreamRecurrence_eq_internalRowLowerGramScalar_mul
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (hdom : Antitone lam)
    (F : Fin (r + 1) → ℝ) (I : ℝ)
    (hrec : ∀ i : Fin (r + 1),
      F i = (lam i : ℝ) * I -
        ∑ j : Fin (r + 1),
          if i < j then
            (downstreamShift lam a j)⁻¹ * F j
          else 0) :
    F a = internalRowLowerGramScalar lam a * I := by
  let K : ℝ := (lam a : ℝ) + ((r - a.val : ℕ) : ℝ)
  let factor : Fin (r + 1) → ℝ := fun q =>
    (downstreamShift lam a q - 1) / downstreamShift lam a q
  have hclosed : ∀ i : Fin (r + 1), a ≤ i →
      F i =
        (K * (∏ q ∈ downstreamRows i, factor q) -
          downstreamShift lam a i) * I := by
    intro i
    induction i using Fin.reverseInduction with
    | last =>
        intro hai
        rw [downstreamRows_last]
        simp only [Finset.prod_empty, mul_one]
        have hzero :
            (∑ j : Fin (r + 1),
              if Fin.last r < j then
                (downstreamShift lam a j)⁻¹ * F j
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp only [not_lt_of_ge (Fin.le_last j), ↓reduceIte]
        rw [hrec (Fin.last r), hzero, sub_zero]
        dsimp [K, downstreamShift]
        rw [Nat.cast_sub (show a.val ≤ r by omega)]
        ring
    | cast i ih =>
        intro hai
        have hnext : a ≤ i.succ :=
          le_trans hai (Fin.castSucc_le_succ i)
        have hne : downstreamShift lam a i.succ ≠ 0 :=
          downstreamShift_ne_zero lam a i.succ
            (lt_of_le_of_lt hai Fin.castSucc_lt_succ)
            (hdom (le_trans hai (Fin.castSucc_le_succ i)))
        have hsplit :=
          sum_ite_downstream_eq_sum_ite_between_add_add_downstream
            i.castSucc i.succ Fin.castSucc_lt_succ
            (fun j : Fin (r + 1) =>
              (downstreamShift lam a j)⁻¹ * F j)
        rw [sum_ite_between_eq_zero_of_succ
          i.castSucc i.succ (by simp only [Fin.val_succ, Fin.val_castSucc]) _] at hsplit
        simp only [zero_add] at hsplit
        have hadj :
            F i.castSucc =
              ((lam i.castSucc : ℝ) - (lam i.succ : ℝ)) * I +
                (1 - (downstreamShift lam a i.succ)⁻¹) * F i.succ := by
          rw [hrec i.castSucc, hsplit, hrec i.succ]
          ring
        rw [hadj, ih hnext,
          downstreamRows_castSucc_eq_insert_succ]
        have hnot : i.succ ∉ downstreamRows i.succ := by simp only [mem_downstreamRows,
                                                           lt_self_iff_false, not_false_eq_true]
        rw [Finset.prod_insert hnot]
        have hshift :
            downstreamShift lam a i.succ =
              ((lam a : ℝ) - (a.val : ℝ)) -
                (lam i.succ : ℝ) + ((i.val + 1 : ℕ) : ℝ) := by
          unfold downstreamShift
          simp only [Fin.val_succ]
          push_cast
          ring
        have hshiftCurrent :
            downstreamShift lam a i.castSucc =
              ((lam a : ℝ) - (a.val : ℝ)) -
                (lam i.castSucc : ℝ) + (i.val : ℝ) := by
          unfold downstreamShift
          simp only [Fin.val_castSucc]
          ring
        have hfactor :
            factor i.succ =
              downstreamScalarFactor
                ((lam a : ℝ) - (a.val : ℝ))
                (lam i.succ : ℝ) i.val := by
          dsimp [factor, downstreamScalarFactor]
          rw [hshift]
          push_cast
          field_simp [hne]
          ring
        rw [hshiftCurrent, hfactor]
        have hstep := downstreamScalar_backward_step
          ((lam a : ℝ) - (a.val : ℝ))
          (lam i.castSucc : ℝ) (lam i.succ : ℝ)
          K (∏ q ∈ downstreamRows i.succ, factor q)
          i.val (by rw [← hshift]; exact hne)
        rw [← hshift] at hstep
        linear_combination I * hstep
  rw [hclosed a le_rfl, downstreamShift_self, sub_zero]
  unfold internalRowLowerGramScalar
  change (K * (∏ q ∈ downstreamRows a, factor q)) * I =
    (((lam a : ℝ) + ((r - a.val : ℕ) : ℝ)) *
      ∏ q ∈ downstreamRows a,
        downstreamNumerator lam a q / downstreamDenominator lam a q) * I
  dsimp [K]
  congr 2
  apply Finset.prod_congr rfl
  intro q hq
  have haq := (mem_downstreamRows a q).mp hq
  dsimp [factor]
  rw [downstreamNumerator_eq_downstreamShift_sub_one
      lam a q haq hdom,
    downstreamDenominator_eq_downstreamShift lam a q haq hdom]

end HigherHarmonicYoung.ArbitraryRowDownstreamRecurrenceClosedForm

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungArbitraryRowDownstreamGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamPathPairing
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamHarmonicMembership
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamRecurrenceClosedForm
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

theorem projectedCoordinateLower_basis_eq_downstreamCorrectedDerivative
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (hmem : downstreamCorrectedDerivative lam a p k a ∈
      harmonicYoungSubmodule mu) :
    projectedCoordinateLower mu lam hdeg a
        (EuclideanSpace.basisFun (Fin n) ℝ k) p =
      ⟨downstreamCorrectedDerivative lam a p k a, hmem⟩ := by
  apply ext_inner_right ℝ
  intro q
  change
    ⟪youngHomogeneousProjection mu
        (rowDirectionalHomogeneous mu lam hdeg a
          (EuclideanSpace.basisFun (Fin n) ℝ k) p), q⟫_ℝ =
      ⟪(⟨downstreamCorrectedDerivative lam a p k a, hmem⟩ :
        HarmonicYoungSpace (n := n) mu), q⟫_ℝ
  rw [youngHomogeneousProjection_inner,
    young_inner_eq_polynomialInner]
  have hsource :
      ((rowDirectionalHomogeneous mu lam hdeg a
          (EuclideanSpace.basisFun (Fin n) ℝ k) p :
            SpherePacking.Fischer.Homogeneous ((r + 1) * n)
              (∑ i, mu i)) : PolynomialSpace r n) =
        MvPolynomial.pderiv (variableIndex a k)
          (p : PolynomialSpace r n) := by
    change
      rowDirectionalDerivative r n a
          (EuclideanSpace.basisFun (Fin n) ℝ k)
          (p : PolynomialSpace r n) = _
    rw [EuclideanSpace.basisFun_apply, rowDirectionalDerivative_single]
  rw [hsource]
  change
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex a k)
          (p : PolynomialSpace r n))
        (q : PolynomialSpace r n) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (downstreamCorrectedDerivative lam a p k a)
        (q : PolynomialSpace r n)
  rw [downstreamCorrectedDerivative_eq,
    SpherePacking.Fischer.polynomialInner_add_left,
    SpherePacking.Fischer.polynomialInner_sum_left]
  symm
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with haj
  · rw [SpherePacking.Fischer.polynomialInner_smul_left,
      polynomialInner_polarization_harmonicLift]
    have hhighest :=
      ((mem_harmonicYoungSubmodule mu
        (q : PolynomialSpace r n)).mp q.property).2.2.2 a j haj
    rw [hhighest]
    simp only [SpherePacking.Fischer.polynomialInner, MvPolynomial.coeff_zero, mul_zero,
      Finsupp.sum_fun_zero]
  · simp only [SpherePacking.Fischer.polynomialInner, AddMonoidAlgebra.coeff_zero,
      Finsupp.sum_zero_index]

theorem youngClebschLower_downstream_inner_eq_cross_sum
    {r n : ℕ} (lam mu : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (hmem : ∀ (p : HarmonicYoungSpace (n := n) lam) (k : Fin n),
      downstreamCorrectedDerivative lam a p k a ∈
        harmonicYoungSubmodule mu)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngClebschLower mu lam hdeg a p,
      youngClebschLower mu lam hdeg a q⟫_ℝ =
      ∑ k : Fin n,
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (MvPolynomial.pderiv (variableIndex a k)
            (p : PolynomialSpace r n))
          (downstreamCorrectedDerivative lam a q k a) := by
  rw [youngClebschLower_inner]
  apply Finset.sum_congr rfl
  intro k _
  rw [projectedCoordinateLower_basis_eq_downstreamCorrectedDerivative
    lam mu a hdeg q k (hmem q k)]
  change
    ⟪youngHomogeneousProjection mu
        (rowDirectionalHomogeneous mu lam hdeg a
          (EuclideanSpace.basisFun (Fin n) ℝ k) p),
      (⟨downstreamCorrectedDerivative lam a q k a,
        hmem q k⟩ : HarmonicYoungSpace (n := n) mu)⟫_ℝ = _
  rw [youngHomogeneousProjection_inner]
  congr 1
  change
    rowDirectionalDerivative r n a
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (p : PolynomialSpace r n) =
      MvPolynomial.pderiv (variableIndex a k)
        (p : PolynomialSpace r n)
  rw [EuclideanSpace.basisFun_apply, rowDirectionalDerivative_single]

theorem youngClebschLower_arbitrary_inner_eq_cross_sum_of_simpleRoots
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (hsimple : ∀ (p : HarmonicYoungSpace (n := n) lam)
      (k : Fin n) (j : Fin r),
      polarization r n j.castSucc j.succ
        (downstreamCorrectedDerivative lam a p k a) = 0)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a p,
      youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a q⟫_ℝ =
      ∑ k : Fin n,
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (MvPolynomial.pderiv (variableIndex a k)
            (p : PolynomialSpace r n))
          (downstreamCorrectedDerivative lam a q k a) := by
  exact youngClebschLower_downstream_inner_eq_cross_sum
    lam (loweredInternalYoungWeight lam a) a
    (loweredInternalYoungWeight_sum_add_one lam a ha)
    (fun p k =>
      downstreamCorrectedDerivative_source_mem_harmonicYoung_of_simpleRoots
        lam a ha p k (hsimple p k)) p q

private def downstreamFischerCrossSum
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) lam)
    (i : Fin (r + 1)) : ℝ :=
  ∑ k : Fin n,
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      (MvPolynomial.pderiv (variableIndex i k)
        (p : PolynomialSpace r n))
      (downstreamCorrectedDerivative lam a q k i)

theorem downstreamFischerCrossSum_eq_internalRowLowerGramScalar
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (hdom : Antitone lam)
    (p q : HarmonicYoungSpace (n := n) lam) :
    downstreamFischerCrossSum lam a p q a =
      internalRowLowerGramScalar lam a * ⟪p, q⟫_ℝ := by
  apply downstreamRecurrence_eq_internalRowLowerGramScalar_mul
    lam a hdom (downstreamFischerCrossSum lam a p q) ⟪p, q⟫_ℝ
  intro i
  exact downstreamCorrectedDerivative_fischer_cross_sum_recurrence
    lam a i p q

theorem youngClebschLower_arbitrary_inner_of_simpleRoots
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (hdom : Antitone lam)
    (hsimple : ∀ (p : HarmonicYoungSpace (n := n) lam)
      (k : Fin n) (j : Fin r),
      polarization r n j.castSucc j.succ
        (downstreamCorrectedDerivative lam a p k a) = 0)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a p,
      youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a q⟫_ℝ =
      internalRowLowerGramScalar lam a * ⟪p, q⟫_ℝ := by
  rw [youngClebschLower_arbitrary_inner_eq_cross_sum_of_simpleRoots
    lam a ha hsimple p q]
  exact downstreamFischerCrossSum_eq_internalRowLowerGramScalar
    lam a hdom p q

end HigherYoungArbitraryRowDownstreamGram

end

section


open scoped BigOperators

namespace HigherYoungDownstreamSimpleRootInvariant

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamMembership
open MetricCodes.Spherical.HigherYoungDownstreamFiniteIntervalSums

theorem downstreamShift_succ_sub_castSucc {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) (c : Fin r) :
    downstreamShift lam a c.succ -
        downstreamShift lam a c.castSucc =
      (lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1 := by
  simp only [downstreamShift, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one]
  ring

theorem adjacentRowEuler_sub_on_downstream
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (c : Fin r)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n) :
    rowEuler r n c.castSucc
          (downstreamCorrectedDerivative lam a p k c.succ) -
        rowEuler r n c.succ
          (downstreamCorrectedDerivative lam a p k c.succ) =
      ((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1) •
        downstreamCorrectedDerivative lam a p k c.succ := by
  rw [downstreamCorrectedDerivative_rowEuler,
    downstreamCorrectedDerivative_rowEuler]
  have hne : c.castSucc ≠ c.succ := ne_of_lt Fin.castSucc_lt_succ
  simp only [loweredRowEigenvalue, hne, ite_false, ite_true]
  module

theorem simpleRoot_internalDerivative
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (c : Fin r) (i : Fin (r + 1)) :
    polarization r n c.castSucc c.succ
        (MvPolynomial.pderiv (variableIndex i k)
          (p : PolynomialSpace r n)) =
      if c.castSucc = i then
        -MvPolynomial.pderiv (variableIndex c.succ k)
          (p : PolynomialSpace r n)
      else 0 := by
  have hp := ((mem_harmonicYoungSubmodule lam
    (p : PolynomialSpace r n)).mp p.property).2.2.2
  have hhighest :
      polarization r n c.castSucc c.succ
        (p : PolynomialSpace r n) = 0 :=
    hp c.castSucc c.succ Fin.castSucc_lt_succ
  have hcomm := pderiv_polarization_harmonicLift
    i c.castSucc c.succ k (p : PolynomialSpace r n)
  rw [hhighest, map_zero] at hcomm
  by_cases hci : c.castSucc = i
  · subst i
    simp only [ite_true] at hcomm ⊢
    exact eq_neg_of_add_eq_zero_right hcomm.symm
  · have hic : i ≠ c.castSucc := Ne.symm hci
    simp only [ite_eq_right hic, zero_add] at hcomm
    simp only [ite_eq_right hci]
    exact hcomm.symm

theorem simpleRoot_downstreamPolarization_of_left
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i : Fin (r + 1)) (c : Fin r)
    (hic : i < c.castSucc)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (j : Fin (r + 1))
    (hjroot :
      polarization r n c.castSucc c.succ
          (downstreamCorrectedDerivative lam a p k j) =
        if c.castSucc = j then
          -(downstreamShift lam a j /
              downstreamShift lam a c.succ) •
            downstreamCorrectedDerivative lam a p k c.succ
        else 0) :
    polarization r n c.castSucc c.succ
        (polarization r n j i
          (downstreamCorrectedDerivative lam a p k j)) =
      if j = c.castSucc then
        -(downstreamShift lam a c.castSucc /
          downstreamShift lam a c.succ) •
          polarization r n c.castSucc i
            (downstreamCorrectedDerivative lam a p k c.succ)
      else if j = c.succ then
        polarization r n c.castSucc i
          (downstreamCorrectedDerivative lam a p k c.succ)
      else 0 := by
  rw [polarization_polarization_commutator, hjroot]
  have hic' : i ≠ c.castSucc := ne_of_lt hic
  simp only [ite_eq_right hic', sub_zero]
  by_cases hjc : j = c.castSucc
  · subst j
    have hdc : c.succ ≠ c.castSucc :=
      (ne_of_lt Fin.castSucc_lt_succ).symm
    simp only [ite_true, ite_eq_right hdc, add_zero, map_smul]
  · by_cases hjd : j = c.succ
    · subst j
      have hcd : c.castSucc ≠ c.succ :=
        ne_of_lt Fin.castSucc_lt_succ
      have hdc : c.succ ≠ c.castSucc := hcd.symm
      simp only [ite_eq_right hcd, ite_eq_right hdc, ite_true, map_zero, zero_add]
    · have hcj : c.castSucc ≠ j := Ne.symm hjc
      have hdj : c.succ ≠ j := Ne.symm hjd
      simp only [ite_eq_right hjc, ite_eq_right hjd, ite_eq_right hcj, ite_eq_right hdj,
        map_zero, zero_add]

theorem simpleRoot_downstreamPolarization_of_right
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i : Fin (r + 1)) (c : Fin r)
    (hci : c.castSucc < i)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (j : Fin (r + 1)) (hij : i < j)
    (hjroot :
      polarization r n c.castSucc c.succ
          (downstreamCorrectedDerivative lam a p k j) = 0) :
    polarization r n c.castSucc c.succ
        (polarization r n j i
          (downstreamCorrectedDerivative lam a p k j)) = 0 := by
  rw [polarization_polarization_commutator, hjroot, map_zero]
  have hid : i ≠ c.castSucc := ne_of_gt hci
  have hdj : c.succ ≠ j := by
    intro heq
    subst j
    have hval : c.castSucc.val < i.val := hci
    have hival : i.val < c.succ.val := hij
    simp only [Fin.val_castSucc, Fin.val_succ] at hval hival
    omega
  simp only [hdj, ↓reduceIte, add_zero, hid, sub_self]

end HigherYoungDownstreamSimpleRootInvariant

end

section


open scoped BigOperators

namespace HigherYoungDownstreamAdjacentCancellationAlgebra

theorem neg_add_inv_sub_smul_eq_neg_div_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y : ℝ) (hy : y ≠ 0) (v : V) :
    -v + y⁻¹ • ((y - x) • v) = -(x / y) • v := by
  rw [smul_smul, ← neg_one_smul ℝ v, ← add_smul]
  congr 1
  field_simp [hy]
  ring

end HigherYoungDownstreamAdjacentCancellationAlgebra

namespace HigherYoungDownstreamAdjacentSumHelpers

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungInternalRowPolarizationDescent
open MetricCodes.Spherical.HigherYoungDownstreamFiniteIntervalSums

theorem sum_downstream_two_root_terms_eq_zero
    {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (δ : Fin m → ℝ) (i c d : Fin m)
    (hic : i < c) (hcd : c < d) (hc : δ c ≠ 0)
    (U : V) :
    (∑ j : Fin m,
      if i < j then
        (δ j)⁻¹ •
          (if j = c then -(δ c / δ d) • U
           else if j = d then U else 0)
      else 0) = 0 := by
  classical
  have hid : i < d := lt_trans hic hcd
  have hpoint : ∀ j : Fin m,
      (if i < j then
        (δ j)⁻¹ •
          (if j = c then -(δ c / δ d) • U
           else if j = d then U else 0)
      else 0) =
        if j = c then (δ c)⁻¹ • (-(δ c / δ d) • U)
        else if j = d then (δ d)⁻¹ • U else 0 := by
    intro j
    by_cases hjc : j = c
    · subst j
      simp only [hic, ↓reduceIte, neg_smul, smul_neg]
    · by_cases hjd : j = d
      · subst j
        simp only [hid, ↓reduceIte, hcd.ne.symm]
      · simp only [hjc, ↓reduceIte, hjd, smul_zero, ite_self]
  simp_rw [hpoint]
  rw [smul_smul]
  have hscalar : (δ c)⁻¹ * (-(δ c / δ d)) = -(δ d)⁻¹ := by
    rw [div_eq_mul_inv]
    field_simp [hc]
  rw [hscalar, neg_smul]
  calc
    (∑ x : Fin m,
      if x = c then -((δ d)⁻¹ • U)
      else if x = d then (δ d)⁻¹ • U else 0) =
        (∑ x : Fin m,
          if x = c then -((δ d)⁻¹ • U) else 0) +
        (∑ x : Fin m,
          if x = d then (δ d)⁻¹ • U else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxc : x = c
          · subst x
            simp only [↓reduceIte, hcd.ne, add_zero]
          · by_cases hxd : x = d
            · subst x
              simp only [hcd.ne.symm, ↓reduceIte, zero_add]
            · simp only [hxc, ↓reduceIte, hxd, add_zero]
    _ = 0 := by
      rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      exact neg_add_cancel _

theorem sum_downstream_adjacent_root_eq_selected_sub_tail
    {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (δ : Fin m → ℝ) (c d : Fin m)
    (hcd : c < d) (hsucc : d.val = c.val + 1)
    (g : ℝ) (T : V) (P : Fin m → V) :
    (∑ j : Fin m,
      if c < j then
        (δ j)⁻¹ •
          (if j = d then g • T else -P j)
      else 0) =
      (δ d)⁻¹ • (g • T) -
        ∑ j : Fin m,
          if d < j then (δ j)⁻¹ • P j else 0 := by
  rw [sum_ite_downstream_eq_sum_ite_between_add_add_downstream
    c d hcd (fun j => (δ j)⁻¹ •
      (if j = d then g • T else -P j)),
    sum_ite_between_eq_zero_of_succ c d hsucc
      (fun j => (δ j)⁻¹ •
        (if j = d then g • T else -P j))]
  simp only [zero_add, ite_true]
  have htail :
      (∑ j : Fin m,
        if d < j then
          (δ j)⁻¹ • (if j = d then g • T else -P j)
        else 0) =
        -(∑ j : Fin m,
          if d < j then (δ j)⁻¹ • P j else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hdj : d < j
    · have hjd : j ≠ d := ne_of_gt hdj
      simp only [hdj, ↓reduceIte, hjd, smul_neg]
    · simp only [hdj, ↓reduceIte, neg_zero]
  rw [htail, sub_eq_add_neg]

end HigherYoungDownstreamAdjacentSumHelpers

end

section


open scoped BigOperators

namespace HigherYoungDownstreamSimpleRootInvariant

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamMembership
open MetricCodes.Spherical.HigherYoungDownstreamAdjacentCancellationAlgebra
open MetricCodes.Spherical.HigherYoungDownstreamAdjacentSumHelpers
open MetricCodes.Spherical.HigherYoungDownstreamFiniteIntervalSums

theorem simpleRoot_downstreamPolarization_of_self
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (c : Fin r)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (j : Fin (r + 1)) (hcj : c.castSucc < j)
    (hjroot :
      polarization r n c.castSucc c.succ
          (downstreamCorrectedDerivative lam a p k j) = 0) :
    polarization r n c.castSucc c.succ
        (polarization r n j c.castSucc
          (downstreamCorrectedDerivative lam a p k j)) =
      if j = c.succ then
        ((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1) •
          downstreamCorrectedDerivative lam a p k c.succ
      else
        -polarization r n j c.succ
          (downstreamCorrectedDerivative lam a p k j) := by
  rw [polarization_polarization_commutator, hjroot, map_zero]
  simp only [zero_add, ite_true]
  by_cases hjd : j = c.succ
  · subst j
    simp only [ite_true, polarization_self]
    exact adjacentRowEuler_sub_on_downstream lam a c p k
  · have hdj : c.succ ≠ j := Ne.symm hjd
    simp only [hdj, ↓reduceIte, polarization_apply, zero_sub, hjd]

theorem downstreamCorrectedDerivative_simpleRoot
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (hdom : Antitone lam)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i : Fin (r + 1)) (hai : a ≤ i) (c : Fin r) :
    polarization r n c.castSucc c.succ
        (downstreamCorrectedDerivative lam a p k i) =
      if c.castSucc = i then
        -(downstreamShift lam a i /
            downstreamShift lam a c.succ) •
          downstreamCorrectedDerivative lam a p k c.succ
      else 0 := by
  classical
  induction i using
      (measure (fun j : Fin (r + 1) => r + 1 - j.val)).wf.induction with
  | h i ih =>
    have hrec (j : Fin (r + 1)) (hij : i < j) :
        polarization r n c.castSucc c.succ
            (downstreamCorrectedDerivative lam a p k j) =
          if c.castSucc = j then
            -(downstreamShift lam a j /
                downstreamShift lam a c.succ) •
              downstreamCorrectedDerivative lam a p k c.succ
          else 0 := by
      apply ih j
      · change r + 1 - j.val < r + 1 - i.val
        have hij' : i.val < j.val := hij
        have hjbound : j.val < r + 1 := j.isLt
        omega
      · exact hai.trans hij.le
    rw [downstreamCorrectedDerivative_eq, map_add, map_sum,
      simpleRoot_internalDerivative lam p k c i]
    rcases lt_trichotomy i c.castSucc with hic | hic | hci
    · have hci' : c.castSucc ≠ i := ne_of_gt hic
      simp only [ite_eq_right hci', zero_add]
      have hdc : downstreamShift lam a c.castSucc ≠ 0 :=
        downstreamShift_ne_zero lam a c.castSucc
          (lt_of_le_of_lt hai hic) (hdom (le_trans hai hic.le))
      calc
        (∑ j : Fin (r + 1),
          polarization r n c.castSucc c.succ
            (if i < j then
              (downstreamShift lam a j)⁻¹ •
                polarization r n j i
                  (downstreamCorrectedDerivative lam a p k j)
            else 0)) =
            ∑ j : Fin (r + 1),
              if i < j then
                (downstreamShift lam a j)⁻¹ •
                  (if j = c.castSucc then
                    -(downstreamShift lam a c.castSucc /
                        downstreamShift lam a c.succ) •
                      polarization r n c.castSucc i
                        (downstreamCorrectedDerivative lam a p k c.succ)
                   else if j = c.succ then
                    polarization r n c.castSucc i
                      (downstreamCorrectedDerivative lam a p k c.succ)
                   else 0)
              else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : i < j
              · simp only [ite_eq_left hij, map_smul]
                rw [simpleRoot_downstreamPolarization_of_left
                  lam a i c hic p k j (hrec j hij)]
              · simp only [hij, ↓reduceIte, map_zero, ]
        _ = 0 :=
          sum_downstream_two_root_terms_eq_zero
            (downstreamShift lam a) i c.castSucc c.succ
            hic Fin.castSucc_lt_succ hdc
            (polarization r n c.castSucc i
              (downstreamCorrectedDerivative lam a p k c.succ))
    · subst i
      simp only [ite_true]
      have had : a < c.succ := lt_of_le_of_lt hai Fin.castSucc_lt_succ
      have hd : downstreamShift lam a c.succ ≠ 0 :=
        downstreamShift_ne_zero lam a c.succ had (hdom had.le)
      have hdiag :
          ((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1) =
            downstreamShift lam a c.succ -
              downstreamShift lam a c.castSucc :=
        (downstreamShift_succ_sub_castSucc lam a c).symm
      have hsum :
          (∑ j : Fin (r + 1),
            polarization r n c.castSucc c.succ
              (if c.castSucc < j then
                (downstreamShift lam a j)⁻¹ •
                  polarization r n j c.castSucc
                    (downstreamCorrectedDerivative lam a p k j)
              else 0)) =
            (downstreamShift lam a c.succ)⁻¹ •
              (((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1) •
                downstreamCorrectedDerivative lam a p k c.succ) -
              ∑ j : Fin (r + 1),
                if c.succ < j then
                  (downstreamShift lam a j)⁻¹ •
                    polarization r n j c.succ
                      (downstreamCorrectedDerivative lam a p k j)
                else 0 := by
        calc
          (∑ j : Fin (r + 1),
            polarization r n c.castSucc c.succ
              (if c.castSucc < j then
                (downstreamShift lam a j)⁻¹ •
                  polarization r n j c.castSucc
                    (downstreamCorrectedDerivative lam a p k j)
              else 0)) =
            ∑ j : Fin (r + 1),
              if c.castSucc < j then
                (downstreamShift lam a j)⁻¹ •
                  (if j = c.succ then
                    ((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1) •
                      downstreamCorrectedDerivative lam a p k c.succ
                   else
                    -polarization r n j c.succ
                      (downstreamCorrectedDerivative lam a p k j))
              else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : c.castSucc < j
              · simp only [ite_eq_left hij, map_smul]
                have hroot := hrec j hij
                have hcj : c.castSucc ≠ j := ne_of_lt hij
                rw [ite_eq_right hcj] at hroot
                rw [simpleRoot_downstreamPolarization_of_self
                  lam a c p k j hij hroot]
              · simp only [hij, ↓reduceIte, map_zero, ]
          _ = _ :=
            sum_downstream_adjacent_root_eq_selected_sub_tail
              (downstreamShift lam a) c.castSucc c.succ
              Fin.castSucc_lt_succ (by simp only [Fin.val_succ, Fin.val_castSucc])
              ((lam c.castSucc : ℝ) - (lam c.succ : ℝ) + 1)
              (downstreamCorrectedDerivative lam a p k c.succ)
              (fun j => polarization r n j c.succ
                (downstreamCorrectedDerivative lam a p k j))
      simp only [dite_eq_ite] at hsum ⊢
      rw [hsum, hdiag]
      have htail := downstreamCorrectedDerivative_eq lam a p k c.succ
      have hreshape :
          -(MvPolynomial.pderiv (variableIndex c.succ k)
              (p : PolynomialSpace r n)) -
            (∑ j : Fin (r + 1),
              if c.succ < j then
                (downstreamShift lam a j)⁻¹ •
                  polarization r n j c.succ
                    (downstreamCorrectedDerivative lam a p k j)
              else 0) =
            -downstreamCorrectedDerivative lam a p k c.succ := by
        rw [htail]
        abel
      have hreorder :
          -MvPolynomial.pderiv (variableIndex c.succ k)
                (p : PolynomialSpace r n) +
              ((downstreamShift lam a c.succ)⁻¹ •
                  ((downstreamShift lam a c.succ -
                    downstreamShift lam a c.castSucc) •
                    downstreamCorrectedDerivative lam a p k c.succ) -
                ∑ j : Fin (r + 1),
                  if c.succ < j then
                    (downstreamShift lam a j)⁻¹ •
                      polarization r n j c.succ
                        (downstreamCorrectedDerivative lam a p k j)
                  else 0) =
            -downstreamCorrectedDerivative lam a p k c.succ +
              (downstreamShift lam a c.succ)⁻¹ •
                ((downstreamShift lam a c.succ -
                    downstreamShift lam a c.castSucc) •
                  downstreamCorrectedDerivative lam a p k c.succ) := by
        rw [← hreshape]
        abel
      rw [hreorder]
      exact neg_add_inv_sub_smul_eq_neg_div_smul
        (downstreamShift lam a c.castSucc)
        (downstreamShift lam a c.succ) hd
        (downstreamCorrectedDerivative lam a p k c.succ)
    · have hci' : c.castSucc ≠ i := ne_of_lt hci
      simp only [ite_eq_right hci', zero_add]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hij : i < j
      · have hroot := hrec j hij
        have hcj : c.castSucc ≠ j := ne_of_lt (lt_trans hci hij)
        rw [ite_eq_right hcj] at hroot
        rw [dite_eq_left hij, map_smul,
          simpleRoot_downstreamPolarization_of_right
            lam a i c hci p k j hij hroot, smul_zero]
      · simp only [hij, ↓reduceDIte, map_zero, ]

theorem downstreamCorrectedDerivative_source_simpleRoot_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (hdom : Antitone lam)
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n) (c : Fin r) :
    polarization r n c.castSucc c.succ
      (downstreamCorrectedDerivative lam a p k a) = 0 := by
  rw [downstreamCorrectedDerivative_simpleRoot lam a hdom p k a (le_refl a) c]
  by_cases hca : c.castSucc = a
  · rw [ite_eq_left hca]
    simp only [downstreamShift_self, zero_div, neg_zero, zero_smul]
  · simp only [hca, ↓reduceIte]

end HigherYoungDownstreamSimpleRootInvariant

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamHarmonicMembership
open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamGram
open MetricCodes.Spherical.HigherYoungDownstreamSimpleRootInvariant
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

theorem youngClebschLower_arbitrary_inner
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (hdom : Antitone lam)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a p,
      youngClebschLower (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a q⟫_ℝ =
      internalRowLowerGramScalar lam a * ⟪p, q⟫_ℝ := by
  apply youngClebschLower_arbitrary_inner_of_simpleRoots
    lam a ha hdom
  intro v k j
  exact downstreamCorrectedDerivative_source_simpleRoot_eq_zero
    lam a hdom v k j

theorem youngClebschLower_arbitrary_adjoint_comp_self
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1)) (ha : 0 < lam a)
    (hdom : Antitone lam) :
    (youngClebschLower (n := n)
      (loweredInternalYoungWeight lam a) lam
      (loweredInternalYoungWeight_sum_add_one lam a ha) a).adjoint.comp
      (youngClebschLower (n := n)
        (loweredInternalYoungWeight lam a) lam
        (loweredInternalYoungWeight_sum_add_one lam a ha) a) =
      internalRowLowerGramScalar lam a • LinearMap.id := by
  exact SpherePacking.HarmonicCoordinateOperators.adjoint_comp_self_of_inner
    (youngClebschLower (n := n)
      (loweredInternalYoungWeight lam a) lam
      (loweredInternalYoungWeight_sum_add_one lam a ha) a)
    (internalRowLowerGramScalar lam a)
    (youngClebschLower_arbitrary_inner lam a ha hdom)

end HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungArbitraryRowLoweringProjectedAxisWitness

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

@[simp] theorem loweredInternalYoungWeight_raiseWeight
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    loweredInternalYoungWeight (raiseWeight lam row) row = lam := by
  funext j
  by_cases hj : j = row
  · subst j
    simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right]
  · simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right,
      ne_eq, hj, not_false_eq_true, Function.update_of_ne]

theorem youngClebschLower_inner_of_raisedSignature
    {r n : ℕ} (source target : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hrow : target = loweredInternalYoungWeight source row)
    (hpositive : 0 < source row)
    (hdom : Antitone source)
    (hdeg : (∑ i, source i) = (∑ i, target i) + 1)
    (p q : HarmonicYoungSpace (n := n) source) :
    ⟪youngClebschLower target source hdeg row p,
      youngClebschLower target source hdeg row q⟫_ℝ =
      internalRowLowerGramScalar source row * ⟪p, q⟫_ℝ := by
  subst target
  exact youngClebschLower_arbitrary_inner source row hpositive hdom p q

theorem raiseWeight_strictly_removable
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (row : Fin (r + 1))
    (j : Fin (r + 1)) (hj : j.val = row.val + 1) :
    raiseWeight lam row j < raiseWeight lam row row := by
  have hne : j ≠ row := by
    intro heq
    subst j
    omega
  have hle : lam j ≤ lam row := by
    apply hdom
    change row.val ≤ j.val
    omega
  simpa only [raiseWeight, ne_eq, hne, not_false_eq_true, Function.update_of_ne,
    Function.update_self, Order.lt_add_one_iff, ge_iff_le,
    Nat.succ_eq_add_one] using Nat.lt_succ_of_le hle

/-- Data encoding the genuine lowering fibre axis construction. -/
structure GenuineLoweringFibreAxisData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (row : Fin (r + 2))
    (hdeg : (∑ i, boxSignature (m := m) a n source i) =
      (∑ i, boxSignature (m := m) a n target i) + 1) where
  /-- The coefficient component. -/
  coefficient : ℝ
  coefficient_sq : coefficient ^ 2 =
    internalRowLowerGramScalar (boxSignature (m := m) a n source) row *
      plusProbability n (boxSignature (m := m) a n target)
        (Weyl.flooredWeight b n) row
  projected_axis : ∀ v : BoxStabilizer n b,
    projectedCoordinateRaise (boxSignature (m := m) a n source)
        (boxSignature (m := m) a n target) hdeg row o.val
        (fibre target v) =
      coefficient • fibre source v

private def boxLoweringProjectedAxisWitness_of_actualGT
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a n source =
      raiseWeight (boxSignature (m := m) a n target) row)
    (D : GenuineLoweringFibreAxisData a b o fibre target source row
      (by
        rw [hrow]
        exact sum_raiseWeight _ row)) :
    BoxLoweringProjectedAxisWitness a b o fibre target source h row
      (by
        rw [hrow]
        exact sum_raiseWeight _ row) := by
  let low := boxSignature (m := m) a n target
  let high := boxSignature (m := m) a n source
  have hhighdom : Antitone high :=
    (boxSignature_interlaces a b hstable source).antitone_ambient
  have hlowdom : Antitone low :=
    (boxSignature_interlaces a b hstable target).antitone_ambient
  have hpositive : 0 < high row := by
    dsimp [high]
    rw [hrow]
    simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  have hstrict : ∀ j : Fin (r + 2),
      j.val = row.val + 1 → high j < high row := by
    intro j hj
    dsimp [high]
    rw [hrow]
    exact raiseWeight_strictly_removable low hlowdom row j hj
  have hlowered : low = loweredInternalYoungWeight high row := by
    dsimp [low, high]
    rw [hrow, loweredInternalYoungWeight_raiseWeight]
  refine {
    gram := internalRowLowerGramScalar high row
    gram_pos := internalRowLowerGramScalar_pos high row hpositive hstrict
    gram_inner := ?_
    coefficient := D.coefficient
    coefficient_sq := ?_
    projected_axis := D.projected_axis
  }
  · intro p q
    exact youngClebschLower_inner_of_raisedSignature high low row
      hlowered hpositive hhighdom _ p q
  · rw [boxProbability_eq_plus_of_signature_raise a b target source row hrow]
    exact D.coefficient_sq

end HigherYoungArbitraryRowLoweringProjectedAxisWitness

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungArbitraryRowRaisingProjectedAxisWitness

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres

private def arbitraryRowBoxRaisingProjectedAxisWitness_of_minusProbability
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a n target =
      raiseWeight (boxSignature (m := m) a n source) row)
    (hdeg : (∑ i, boxSignature (m := m) a n target i) =
      (∑ i, boxSignature (m := m) a n source i) + 1)
    (gram : ℝ) (hgram_pos : 0 < gram)
    (hgram : ∀ p q :
      YoungVertex (n := n) (boxSignature (m := m) a n) source,
      ⟪youngClebschRaise (boxSignature (m := m) a n target)
          (boxSignature (m := m) a n source) hdeg row p,
        youngClebschRaise (boxSignature (m := m) a n target)
          (boxSignature (m := m) a n source) hdeg row q⟫_ℝ =
        gram * ⟪p, q⟫_ℝ)
    (coefficient : ℝ)
    (hcoefficient : coefficient ^ 2 =
      gram * minusProbability n
        (boxSignature (m := m) a n target)
        (flooredCoordinates b n) row)
    (haxis : ∀ v : BoxStabilizer n b,
      projectedCoordinateLower
          (boxSignature (m := m) a n source)
          (boxSignature (m := m) a n target)
          hdeg row o.val (fibre target v) =
        coefficient • fibre source v) :
    BoxRaisingProjectedAxisWitness a b o fibre
      target source h row hdeg where
  gram := gram
  gram_pos := hgram_pos
  gram_inner := hgram
  coefficient := coefficient
  coefficient_sq := by
    rw [boxProbability_eq_minus_of_signature_raise
      a b target source row hrow]
    exact hcoefficient
  projected_axis := haxis

end HigherYoungArbitraryRowRaisingProjectedAxisWitness

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankGTFibreReverseProbability

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherYoungArbitraryRowRaisingProjectedAxisWitness

theorem reverseCoefficient_sq_of_forward_sq_and_weylRatio
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (h : FiniteInterlacing n low mu)
    (hraise : FiniteInterlacing n (raiseWeight low row) mu)
    (lowerGram raisingGram coefficient : ℝ)
    (hforward : coefficient ^ 2 =
      lowerGram * plusProbability n low mu row)
    (hgramRatio : raisingGram =
      lowerGram * weylEdgeRatio n low row) :
    coefficient ^ 2 = raisingGram *
      minusProbability n (raiseWeight low row) mu row := by
  rw [hforward, hgramRatio,
    plusProbability_eq_weylEdgeRatio_mul_minus row h hraise]
  ring

private def boxRaisingProjectedAxisWitness_of_forwardGT_and_reverseRange
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source)
    (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a n target =
      raiseWeight (boxSignature (m := m) a n source) row)
    (hdeg : (∑ i, boxSignature (m := m) a n target i) =
      (∑ i, boxSignature (m := m) a n source i) + 1)
    (coefficient : ℝ)
    (hforward : coefficient ^ 2 =
      internalRowLowerGramScalar (boxSignature (m := m) a n target) row *
        plusProbability n (boxSignature (m := m) a n source)
          (flooredCoordinates b n) row)
    (raisingGram : ℝ) (hraisingGram : 0 < raisingGram)
    (hraisingInner : ∀ p q :
      YoungVertex (n := n) (boxSignature (m := m) a n) source,
      ⟪youngClebschRaise (boxSignature (m := m) a n target)
          (boxSignature (m := m) a n source) hdeg row p,
        youngClebschRaise (boxSignature (m := m) a n target)
          (boxSignature (m := m) a n source) hdeg row q⟫_ℝ =
        raisingGram * ⟪p, q⟫_ℝ)
    (hgramRatio : raisingGram =
      internalRowLowerGramScalar (boxSignature (m := m) a n target) row *
        weylEdgeRatio n (boxSignature (m := m) a n source) row)
    (hreverse : ∀ v : BoxStabilizer n b,
      projectedCoordinateLower
          (boxSignature (m := m) a n source)
          (boxSignature (m := m) a n target)
          hdeg row o.val (fibre target v) =
        coefficient • fibre source v) :
    BoxRaisingProjectedAxisWitness a b o fibre target source h row hdeg := by
  let low := boxSignature (m := m) a n source
  let high := boxSignature (m := m) a n target
  let mu := flooredCoordinates b n
  have hlow : FiniteInterlacing n low mu :=
    hstable ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm source)
  have hhigh : FiniteInterlacing n high mu :=
    hstable ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm target)
  have hforward' : coefficient ^ 2 =
      internalRowLowerGramScalar high row * plusProbability n low mu row := by
    exact hforward
  have hreverseSquare : coefficient ^ 2 =
      raisingGram * minusProbability n high mu row := by
    have hsig : high = raiseWeight low row := hrow
    rw [hsig] at hhigh ⊢
    apply reverseCoefficient_sq_of_forward_sq_and_weylRatio
      low mu row hlow hhigh
      (internalRowLowerGramScalar (raiseWeight low row) row)
      raisingGram coefficient
    · simpa only [hsig] using hforward'
    · simpa only [hrow] using hgramRatio
  exact arbitraryRowBoxRaisingProjectedAxisWitness_of_minusProbability
    a b o fibre target source h row hrow hdeg raisingGram
    hraisingGram hraisingInner coefficient hreverseSquare hreverse

end HigherYoungAllRankGTFibreReverseProbability

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankCanonicalBoxProjectedAxisWitness

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankReverseProjectedFibreCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankBoxSignatureNeighbors
open MetricCodes.Spherical.HigherYoungAllRankGTFibreReverseProbability
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungMovingFibres

/-- Data encoding the canonical box edge axis construction. -/
structure CanonicalBoxEdgeAxisData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a n high =
      raiseWeight (boxSignature (m := m) a n low) row) where
  /-- The forward component. -/
  forward : GenuineLoweringFibreAxisData a b o fibre low high row
    (by rw [hrow]; exact sum_raiseWeight _ row)
  /-- The raising gram component. -/
  raisingGram : ℝ
  raisingGram_pos : 0 < raisingGram
  raisingGram_inner : ∀ p q :
      YoungVertex (n := n) (boxSignature (m := m) a n) low,
    ⟪youngClebschRaise (boxSignature (m := m) a n high)
        (boxSignature (m := m) a n low)
        (by rw [hrow]; exact sum_raiseWeight _ row) row p,
      youngClebschRaise (boxSignature (m := m) a n high)
        (boxSignature (m := m) a n low)
        (by rw [hrow]; exact sum_raiseWeight _ row) row q⟫_ℝ =
      raisingGram * ⟪p, q⟫_ℝ
  raisingGram_ratio : raisingGram =
    internalRowLowerGramScalar (boxSignature (m := m) a n high) row *
      weylEdgeRatio n (boxSignature (m := m) a n low) row
  reverse_range : ∀ v : BoxStabilizer n b,
    projectedCoordinateLower
        (boxSignature (m := m) a n low)
        (boxSignature (m := m) a n high)
        (by rw [hrow]; exact sum_raiseWeight _ row)
        row o.val (fibre high v) ∈
      LinearMap.range (fibre low).toLinearMap

theorem canonicalBoxReverseProjectedAxis_of_edgeData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (o : SpherePoint n)
    (fibre : (i : BoxIndex (r + 1) m) →
      BoxStabilizer n b →ₗᵢ[ℝ]
        YoungVertex (n := n) (boxSignature (m := m) a n) i)
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a n high =
      raiseWeight (boxSignature (m := m) a n low) row)
    (D : CanonicalBoxEdgeAxisData a b o fibre low high row hrow)
    (v : BoxStabilizer n b) :
    projectedCoordinateLower
        (boxSignature (m := m) a n low)
        (boxSignature (m := m) a n high)
        (by rw [hrow]; exact sum_raiseWeight _ row)
        row o.val (fibre high v) =
      D.forward.coefficient • fibre low v := by
  exact projectedCoordinateLower_fibre_eq_of_forward_of_mem_range
    (boxSignature (m := m) a n high)
    (boxSignature (m := m) a n low)
    (by rw [hrow]; exact sum_raiseWeight _ row)
    row o.val (fibre low) (fibre high)
    D.forward.coefficient D.forward.projected_axis D.reverse_range v

/-- The canonical box projected axis witness used in the spherical-code argument. -/
def canonicalBoxProjectedAxisWitness {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n - 1)
        (boxSignature (m := m) a n i)
        (Weyl.flooredWeight b n)
        (boxSignature_interlaces a b hstable i))
    (o : SpherePoint n)
    (haxis : ∀ (low high : BoxIndex (r + 1) m)
      (row : Fin (r + 2))
      (hrow : boxSignature (m := m) a n high =
        raiseWeight (boxSignature (m := m) a n low) row),
      CanonicalBoxEdgeAxisData a b o
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
        low high row hrow)
    (target source : BoxIndex (r + 1) m)
    (h : 0 < boxProbability a b n target source) :
    BoxProjectedAxisWitness a b o
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      target source h := by
  classical
  let row := Classical.choose
    (boxProbability_positive_signature_oneBox a b target source h)
  have hcases := Classical.choose_spec
    (boxProbability_positive_signature_oneBox a b target source h)
  by_cases hrow : boxSignature (m := m) a n source =
      raiseWeight (boxSignature (m := m) a n target) row
  · let D := haxis target source row hrow
    exact BoxProjectedAxisWitness.lower row
      (by rw [hrow]; exact sum_raiseWeight _ row)
      (boxLoweringProjectedAxisWitness_of_actualGT
        a b hstable o
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
        target source h row hrow D.forward)
  · have hrow' : boxSignature (m := m) a n target =
        raiseWeight (boxSignature (m := m) a n source) row :=
      hcases.resolve_left hrow
    let D := haxis source target row hrow'
    refine BoxProjectedAxisWitness.raise row
      (by rw [hrow']; exact sum_raiseWeight _ row) ?_
    refine boxRaisingProjectedAxisWitness_of_forwardGT_and_reverseRange
      a b hstable o
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      target source h row hrow'
      (by rw [hrow']; exact sum_raiseWeight _ row)
      D.forward.coefficient ?_ D.raisingGram ?_ ?_ ?_ ?_
    · change D.forward.coefficient ^ 2 =
        internalRowLowerGramScalar
          (boxSignature (m := m) a n target) row *
          plusProbability n (boxSignature (m := m) a n source)
            (Weyl.flooredWeight b n) row
      exact D.forward.coefficient_sq
    · exact D.raisingGram_pos
    · exact D.raisingGram_inner
    · exact D.raisingGram_ratio
    · exact canonicalBoxReverseProjectedAxis_of_edgeData
        a b o
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
        source target row hrow' D

end AllRankCanonicalBoxProjectedAxisWitness

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowTransverseYoungBranch

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

private def FixedAxisInitialSimpleRootCancellation
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n) : Prop :=
  ∀ (p : homogeneousYoungHighestWeightSubmodule (n := n) lam)
    (a : Fin r), a.castSucc < row →
      polarization r n a.castSucc a.succ
        (arbitraryRowAxialRaise lam row k
          (((p.val : SpherePacking.Fischer.Homogeneous
            ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n))) = 0

private def arbitraryRowHighestWeightRaiseOfSimpleRoots
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (hsimple : FixedAxisInitialSimpleRootCancellation lam row k) :
    homogeneousYoungHighestWeightSubmodule (n := n) lam →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n)
        (raiseWeight lam row) where
  toFun p := by
    have hp := (mem_homogeneousYoungHighestWeightSubmodule lam p.val).mp
      p.property
    refine ⟨⟨arbitraryRowAxialRaise lam row k
      (((p.val : SpherePacking.Fischer.Homogeneous
        ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n)), ?_⟩, ?_⟩
    · rw [sum_raiseWeight]
      exact arbitraryRowAxialRaise_isHomogeneous lam row k _ p.val.property
    · apply (mem_homogeneousYoungHighestWeightSubmodule
        (raiseWeight lam row) _).mpr
      exact ⟨arbitraryRowAxialRaise_rowEuler lam row k _ hp.1,
        arbitraryRowAxialRaise_polarization_of_initial_simpleRoots
          lam row k _ hp.2 (hsimple p)⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (arbitraryRowAxialRaise lam row k) _ _
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (arbitraryRowAxialRaise lam row k) c _

end ArbitraryRowTransverseYoungBranch

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowUnconditionalBranch

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSimpleRootPathCancellation
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowTransverseYoungBranch
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem fixedAxisInitialSimpleRootCancellation_of_antitone
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n) :
    FixedAxisInitialSimpleRootCancellation lam row k := by
  intro p a ha
  have hp := (mem_homogeneousYoungHighestWeightSubmodule lam p.val).mp
    p.property
  apply arbitraryRowAxialRaise_polarization lam hdom row k
    (((p.val : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n))
    hp.1 hp.2
  change a.val < a.val + 1
  omega

private def arbitraryRowHighestWeightRaise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n) :
    homogeneousYoungHighestWeightSubmodule (n := n) lam →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n)
        (raiseWeight lam row) :=
  arbitraryRowHighestWeightRaiseOfSimpleRoots lam row k
    (fixedAxisInitialSimpleRootCancellation_of_antitone lam hdom row k)

end ArbitraryRowUnconditionalBranch

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowAxialAdjointGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowProjectedLowerOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowTransverseYoungBranch

/-- The arbitrary row axial lower scalar used in the spherical-code argument. -/
def arbitraryRowAxialLowerScalar {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) : ℝ :=
  ∏ i ∈ precedingRows row, (shiftedRowGap lam row i + 1)

theorem sortedPrecedingPath_pairwise
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows row) :
    ((S.sort (· ≤ ·)) ++ [row]).Pairwise (· < ·) := by
  have hle := Finset.pairwise_sort S (· ≤ ·)
  have hne := List.nodup_iff_pairwise_ne.mp
    (Finset.sort_nodup S (· ≤ ·))
  have hstrict : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    (hle.and hne).imp fun h => lt_of_le_of_ne h.1 h.2
  apply List.pairwise_append.mpr
  refine ⟨hstrict, by simp only [List.pairwise_cons, List.not_mem_nil, IsEmpty.forall_iff,
                        implies_true, List.Pairwise.nil, and_self], ?_⟩
  intro i hi j hj
  have hj' : j = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
  subst j
  exact (mem_precedingRows i row).mp
    (hsub ((Finset.mem_sort (· ≤ ·)).mp hi))

theorem arbitraryRowAxialLower_summand_of_highest
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) (hS : S ⊆ precedingRows row)
    (q : PolynomialSpace r n)
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b q = 0) :
    polarizationPathCoefficient lam row S •
        upperPolarizationPath
          ((S.sort (· ≤ ·)) ++ [row])
          (MvPolynomial.pderiv
            (variableIndex (polarizationPathStart row S) k) q) =
      (∏ i ∈ precedingRows row \ S, shiftedRowGap lam row i) •
        MvPolynomial.pderiv (variableIndex row k) q := by
  rw [polarizationPathStart_eq_sort_headD,
    upperPolarizationPath_pderiv_of_highest row
      (S.sort (· ≤ ·)) k q
      (sortedPrecedingPath_pairwise row S hS) hhighest,
    smul_smul, Finset.length_sort]
  unfold polarizationPathCoefficient
  have hsign : ((-1 : ℝ) ^ S.card) * ((-1 : ℝ) ^ S.card) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, mul_comm
    (∏ i ∈ precedingRows row \ S, shiftedRowGap lam row i)
    ((-1 : ℝ) ^ S.card), ← mul_assoc, hsign, one_mul]

theorem arbitraryRowAxialLower_of_highest
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (q : PolynomialSpace r n)
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b q = 0) :
    arbitraryRowAxialLower lam row k q =
      arbitraryRowAxialLowerScalar lam row •
        MvPolynomial.pderiv (variableIndex row k) q := by
  classical
  rw [arbitraryRowAxialLower_apply]
  calc
    (∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          upperPolarizationPath ((S.sort (· ≤ ·)) ++ [row])
            (MvPolynomial.pderiv
              (variableIndex (polarizationPathStart row S) k) q)) =
        ∑ S ∈ (precedingRows row).powerset,
          (∏ i ∈ precedingRows row \ S, shiftedRowGap lam row i) •
            MvPolynomial.pderiv (variableIndex row k) q := by
      apply Finset.sum_congr rfl
      intro S hS
      exact arbitraryRowAxialLower_summand_of_highest
        lam row k S (Finset.mem_powerset.mp hS) q hhighest
    _ = (∑ S ∈ (precedingRows row).powerset,
          ∏ i ∈ precedingRows row \ S, shiftedRowGap lam row i) •
            MvPolynomial.pderiv (variableIndex row k) q := by
      rw [Finset.sum_smul]
    _ = arbitraryRowAxialLowerScalar lam row •
            MvPolynomial.pderiv (variableIndex row k) q := by
      congr 1
      unfold arbitraryRowAxialLowerScalar
      simpa only [add_comm, Finset.prod_const_one, one_mul] using
        (Finset.prod_add (fun _ : Fin (r + 1) => (1 : ℝ)) (shiftedRowGap lam row) (precedingRows
          row)).symm

end ArbitraryRowAxialAdjointGram

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankRawForwardAxisRange

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherYoungIteratedAxialProjectionSemigroup
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph

theorem simultaneousHarmonicProjection_residual_mem_gram_all_degree
    {r n d : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) d) :
    ((p : PolynomialSpace r n) -
      ((simultaneousHarmonicProjection r n d p).val :
        PolynomialSpace r n)) ∈ youngGramRadialIdeal r n := by
  by_cases hd : 2 ≤ d
  · exact simultaneousHarmonicProjection_residual_mem_gram_of_two_le hd p
  · have hsmall : d < 2 := by omega
    have htrace : p ∈ homogeneousTraceFreeSubmodule r n d := by
      rw [mem_homogeneousTraceFreeSubmodule]
      exact fun i j =>
        traceOperator_eq_zero_of_isHomogeneous_degree_lt_two
          hsmall (p : PolynomialSpace r n) p.property i j
    let q : homogeneousTraceFreeSubmodule r n d := ⟨p, htrace⟩
    have hfix : simultaneousHarmonicProjection r n d p = q :=
      simultaneousHarmonicProjection_traceFree q
    rw [hfix]
    change (p : PolynomialSpace r n) - (p : PolynomialSpace r n) ∈ _
    simp only [sub_self, zero_mem]

theorem youngHarmonicLift_residual_mem_gram_all_degree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : homogeneousYoungHighestWeightSubmodule (n := n) lam) :
    (((p.val : SpherePacking.Fischer.Homogeneous
          ((r + 1) * n) (∑ i, lam i)) : PolynomialSpace r n) -
      ((youngHarmonicLift lam p : HarmonicYoungSpace (n := n) lam) :
        PolynomialSpace r n)) ∈ youngGramRadialIdeal r n :=
  simultaneousHarmonicProjection_residual_mem_gram_all_degree p.val

theorem reverseInterlacingPolynomialSeed_sub_harmonicBranch_mem_gram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    reverseInterlacingPolynomialSeed lam mu p -
      (reverseInterlacingHarmonicBranch (n := n) lam mu h p :
        PolynomialSpace (r + 1) (n + 1)) ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  exact youngHarmonicLift_residual_mem_gram_all_degree lam
    (reverseInterlacingHighestWeightSeed lam mu h p)

theorem arbitraryRowAxialRaise_harmonicBranch_sub_rawSeed_mem_gram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 2)) (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise lam row (Fin.last n)
        (reverseInterlacingHarmonicBranch (n := n) lam mu h p :
          PolynomialSpace (r + 1) (n + 1)) -
      arbitraryRowAxialRaise lam row (Fin.last n)
        (reverseInterlacingPolynomialSeed lam mu p) ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  apply arbitraryRowAxialRaise_sub_mem_youngGramRadialIdeal
    lam row (Fin.last n)
  simpa only [neg_sub] using
    (youngGramRadialIdeal (r + 1) (n + 1)).neg_mem
      (reverseInterlacingPolynomialSeed_sub_harmonicBranch_mem_gram
        lam mu h p)

theorem arbitraryRowAxialRaise_harmonicBranch_sub_adjacent_mem_gram_of_pathExchange
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (row : Fin (r + 2)) (coefficient : ℝ)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        coefficient • reverseInterlacingPolynomialSeed high mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise low row (Fin.last n)
        (reverseInterlacingHarmonicBranch (n := n) low mu hlow p :
          PolynomialSpace (r + 1) (n + 1)) -
      coefficient •
        (reverseInterlacingHarmonicBranch (n := n) high mu hhigh p :
          PolynomialSpace (r + 1) (n + 1)) ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  have hsource := arbitraryRowAxialRaise_harmonicBranch_sub_rawSeed_mem_gram
    low mu hlow row p
  have htarget :
      coefficient •
        (reverseInterlacingPolynomialSeed high mu p -
          (reverseInterlacingHarmonicBranch (n := n) high mu hhigh p :
            PolynomialSpace (r + 1) (n + 1))) ∈
        youngGramRadialIdeal (r + 1) (n + 1) := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact (youngGramRadialIdeal (r + 1) (n + 1)).mul_mem_left _
      (reverseInterlacingPolynomialSeed_sub_harmonicBranch_mem_gram
        high mu hhigh p)
  have hsum := (youngGramRadialIdeal (r + 1) (n + 1)).add_mem
    ((youngGramRadialIdeal (r + 1) (n + 1)).add_mem hsource (hexchange p))
    htarget
  convert hsum using 1 ; module

end AllRankRawForwardAxisRange

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowBaseAxisChannel

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowProjectedLowerOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherYoungProjectedRaiseInjectivity

theorem arbitraryRowAxialLowerScalar_pos
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    0 < arbitraryRowAxialLowerScalar lam row := by
  unfold arbitraryRowAxialLowerScalar
  apply Finset.prod_pos
  intro i _
  unfold shiftedRowGap
  positivity

theorem arbitraryRowAxialRaise_fischer_inner_eq_lowerScalar_mul_coordinate
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p q : PolynomialSpace r n)
    (hhighest : ∀ a b : Fin (r + 1), a < b →
      polarization r n a b q = 0) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      (arbitraryRowAxialRaise lam row k p) q =
      arbitraryRowAxialLowerScalar lam row *
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (MvPolynomial.X (variableIndex row k) * p) q := by
  rw [arbitraryRowAxialRaise_fischer_adjoint lam row k p q,
    arbitraryRowAxialLower_of_highest lam row k q hhighest,
    SpherePacking.Fischer.polynomialInner_smul_right,
    SpherePacking.Fischer.polynomialInner_X_mul]

end ArbitraryRowBaseAxisChannel

namespace AllRankRawProjectedRaiseMickelsson

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch

/-- The arbitrary row same axis harmonic raise used in the spherical-code argument. -/
def arbitraryRowSameAxisHarmonicRaise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) (raiseWeight lam row) :=
  (youngHarmonicLift (raiseWeight lam row)).comp
    ((arbitraryRowHighestWeightRaise lam hdom row k).comp
      (harmonicYoungHighestWeightEmbedding lam))

theorem arbitraryRowSameAxisHarmonicRaise_inner
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) lam)
    (q : HarmonicYoungSpace (n := n) (raiseWeight lam row)) :
    ⟪arbitraryRowSameAxisHarmonicRaise lam hdom row k p, q⟫_ℝ =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (arbitraryRowAxialRaise lam row k
          (p : PolynomialSpace r n))
        (q : PolynomialSpace r n) := by
  change
    ⟪youngHarmonicLift (raiseWeight lam row)
      (arbitraryRowHighestWeightRaise lam hdom row k
        (harmonicYoungHighestWeightEmbedding lam p)), q⟫_ℝ = _
  exact youngHarmonicLift_fischer_inner (raiseWeight lam row)
    (arbitraryRowHighestWeightRaise lam hdom row k
      (harmonicYoungHighestWeightEmbedding lam p)) q

theorem projectedCoordinateRaise_eq_arbitraryRowSameAxisHarmonicRaise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateRaise (raiseWeight lam row) lam
        (sum_raiseWeight lam row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k) p =
      (arbitraryRowAxialLowerScalar lam row)⁻¹ •
        arbitraryRowSameAxisHarmonicRaise lam hdom row k p := by
  apply ext_inner_right ℝ
  intro q
  have hq := (mem_harmonicYoungSubmodule (raiseWeight lam row)
    (q : PolynomialSpace r n)).mp q.property
  have hpair :=
    arbitraryRowAxialRaise_fischer_inner_eq_lowerScalar_mul_coordinate
      lam row k (p : PolynomialSpace r n)
        (q : PolynomialSpace r n) hq.2.2.2
  have hscalar : arbitraryRowAxialLowerScalar lam row ≠ 0 :=
    (arbitraryRowAxialLowerScalar_pos lam row).ne'
  have hraise := arbitraryRowSameAxisHarmonicRaise_inner
    lam hdom row k p q
  rw [young_inner_eq_polynomialInner] at hraise
  change
    ⟪youngHomogeneousProjection (raiseWeight lam row)
      (rowAxisHomogeneous (raiseWeight lam row) lam
        (sum_raiseWeight lam row) row
          (EuclideanSpace.basisFun (Fin n) ℝ k) p), q⟫_ℝ =
      ⟪(arbitraryRowAxialLowerScalar lam row)⁻¹ •
        arbitraryRowSameAxisHarmonicRaise lam hdom row k p, q⟫_ℝ
  rw [youngHomogeneousProjection_inner, young_inner_eq_polynomialInner]
  change
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      (rowAxisPolynomial row (EuclideanSpace.basisFun (Fin n) ℝ k) *
        (p : PolynomialSpace r n))
      (q : PolynomialSpace r n) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((arbitraryRowAxialLowerScalar lam row)⁻¹ •
          ((arbitraryRowSameAxisHarmonicRaise lam hdom row k p :
            HarmonicYoungSpace (n := n) (raiseWeight lam row)) :
              PolynomialSpace r n))
        (q : PolynomialSpace r n)
  rw [SpherePacking.Fischer.polynomialInner_smul_left, hraise]
  have haxis : rowAxisPolynomial row
      (EuclideanSpace.basisFun (Fin n) ℝ k) =
        MvPolynomial.X (variableIndex row k) := by
    simp only [EuclideanSpace.basisFun_apply, rowAxisPolynomial_eq_sum, PiLp.single_apply,
      MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  rw [haxis, hpair, ← mul_assoc, inv_mul_cancel₀ hscalar, one_mul]

end AllRankRawProjectedRaiseMickelsson

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankCanonicalForwardAxisRange

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherYoungIteratedAxialProjectionSemigroup
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph

theorem arbitraryRowSameAxisHarmonicRaise_sub_raw_mem_gram
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) lam) :
    ((arbitraryRowSameAxisHarmonicRaise lam hdom row k p :
        HarmonicYoungSpace (n := n) (raiseWeight lam row)) :
          PolynomialSpace r n) -
      arbitraryRowAxialRaise lam row k (p : PolynomialSpace r n) ∈
      youngGramRadialIdeal r n := by
  have h := youngHarmonicLift_residual_mem_gram_all_degree
    (raiseWeight lam row)
    (arbitraryRowHighestWeightRaise lam hdom row k
      (harmonicYoungHighestWeightEmbedding lam p))
  change
    arbitraryRowAxialRaise lam row k (p : PolynomialSpace r n) -
      ((arbitraryRowSameAxisHarmonicRaise lam hdom row k p :
        HarmonicYoungSpace (n := n) (raiseWeight lam row)) :
          PolynomialSpace r n) ∈ youngGramRadialIdeal r n at h
  simpa only [neg_sub] using (youngGramRadialIdeal r n).neg_mem h

theorem arbitraryRowSameAxisHarmonicRaise_reverseBranch_eq_of_pathExchange
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (coefficient : ℝ)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        coefficient •
          reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
        (reverseInterlacingHarmonicBranch (n := n) low mu hlow p) =
      coefficient • reverseInterlacingHarmonicBranch
        (n := n) (raiseWeight low row) mu hhigh p := by
  let source : HarmonicYoungSpace (n := n + 1) low :=
    reverseInterlacingHarmonicBranch (n := n) low mu hlow p
  let target : HarmonicYoungSpace (n := n + 1)
      (raiseWeight low row) :=
    reverseInterlacingHarmonicBranch (n := n)
      (raiseWeight low row) mu hhigh p
  let raised : HarmonicYoungSpace (n := n + 1)
      (raiseWeight low row) :=
    arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n) source
  have hraw :=
    arbitraryRowAxialRaise_harmonicBranch_sub_adjacent_mem_gram_of_pathExchange
      low (raiseWeight low row) mu hlow hhigh row coefficient hexchange p
  have hproject := arbitraryRowSameAxisHarmonicRaise_sub_raw_mem_gram
    low hdom row (Fin.last n) source
  have hdiff : ((raised - coefficient • target :
      HarmonicYoungSpace (n := n + 1) (raiseWeight low row)) :
        PolynomialSpace (r + 1) (n + 1)) ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
    change
      ((raised : PolynomialSpace (r + 1) (n + 1)) -
        coefficient • (target : PolynomialSpace (r + 1) (n + 1))) ∈ _
    convert (youngGramRadialIdeal (r + 1) (n + 1)).add_mem
      hproject hraw using 1 ; module
  exact sub_eq_zero.mp
    (harmonicYoung_eq_zero_of_mem_youngGramRadialIdeal
      (raiseWeight low row) (raised - coefficient • target) hdiff)

theorem projectedCoordinateRaise_reverseInterlacingHarmonicBranch_eq_of_pathExchange
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (coefficient : ℝ)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        coefficient •
          reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch (n := n) low mu hlow p) =
      ((arbitraryRowAxialLowerScalar low row)⁻¹ * coefficient) •
        reverseInterlacingHarmonicBranch
          (n := n) (raiseWeight low row) mu hhigh p := by
  rw [projectedCoordinateRaise_eq_arbitraryRowSameAxisHarmonicRaise
    low hdom row (Fin.last n),
    arbitraryRowSameAxisHarmonicRaise_reverseBranch_eq_of_pathExchange
      low mu row hlow hhigh hdom coefficient hexchange p,
    smul_smul]

theorem projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (coefficient : ℝ)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        coefficient •
          reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch (n := n) low mu hlow p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch
          (n := n) (raiseWeight low row) mu hhigh) := by
  refine ⟨((arbitraryRowAxialLowerScalar low row)⁻¹ * coefficient) • p, ?_⟩
  rw [map_smul]
  exact (projectedCoordinateRaise_reverseInterlacingHarmonicBranch_eq_of_pathExchange
    low mu row hlow hhigh hdom coefficient hexchange p).symm

end AllRankCanonicalForwardAxisRange

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankCanonicalFibreAxisTransfer

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
open MetricCodes.Spherical.HigherRepresentationGraph

theorem canonicalFibreAxisCoefficient_sq
    (raw sourceGram targetGram : ℝ)
    (hsource : 0 < sourceGram) (htarget : 0 < targetGram) :
    (raw * Real.sqrt targetGram / Real.sqrt sourceGram) ^ 2 =
      raw ^ 2 * targetGram / sourceGram := by
  have hs : Real.sqrt sourceGram ≠ 0 :=
    (Real.sqrt_pos.mpr hsource).ne'
  rw [div_pow, mul_pow, Real.sq_sqrt htarget.le,
    Real.sq_sqrt hsource.le]

end AllRankCanonicalFibreAxisTransfer

end

end HigherHarmonicYoung

section


namespace HigherYoungArbitraryRankAdjacentInterlacingSchedule

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingTriangularCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem interlacingGap_raiseWeight
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row i : Fin (r + 2)) :
    interlacingGap (raiseWeight low row) mu i =
      interlacingGap low mu i + if i = row then 1 else 0 := by
  classical
  by_cases hi : i = row
  · subst i
    have hbase := appendZeroWeight_le_of_interlaces hlow row
    simp only [interlacingGap, raiseWeight, Function.update_self,
      ite_true]
    omega
  · have hri : row ≠ i := Ne.symm hi
    simp only [interlacingGap, raiseWeight, ne_eq, hi, not_false_eq_true, Function.update_of_ne,
      ↓reduceIte, add_zero]

theorem reverseInterlacingRowSchedule_raiseWeight_count
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row i : Fin (r + 2)) :
    (reverseInterlacingRowSchedule (raiseWeight low row) mu).count i =
      (reverseInterlacingRowSchedule low mu).count i +
        if i = row then 1 else 0 := by
  rw [reverseInterlacingRowSchedule_count,
    reverseInterlacingRowSchedule_count,
    interlacingGap_raiseWeight hlow row i]

theorem reverseInterlacingRowSchedule_raiseWeight_perm
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2)) :
    (reverseInterlacingRowSchedule (raiseWeight low row) mu).Perm
      (reverseInterlacingRowSchedule low mu ++ [row]) := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  rw [reverseInterlacingRowSchedule_raiseWeight_count hlow row i,
    List.count_append]
  by_cases hi : i = row
  · subst i
    simp only [↓reduceIte, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_self, List.mem_cons, or_false, List.count_eq_one_of_mem]
  · simp only [hi, ↓reduceIte, add_zero, not_false_eq_true,
      ne_eq, Ne.symm hi, List.count_cons_of_ne, List.count_nil]

/-- The adjacent reverse prefix used in the spherical-code argument. -/
def adjacentReversePrefix {r : ℕ}
    (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) : List (Fin (r + 2)) :=
  (reverseInterlacingRowSchedule low mu).filter
    (fun i => decide (row ≤ i))

/-- The adjacent reverse suffix used in the spherical-code argument. -/
def adjacentReverseSuffix {r : ℕ}
    (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) : List (Fin (r + 2)) :=
  (reverseInterlacingRowSchedule low mu).filter
    (fun i => decide (i < row))

theorem le_of_mem_adjacentReversePrefix {r : ℕ}
    (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row i : Fin (r + 2))
    (hi : i ∈ adjacentReversePrefix low mu row) : row ≤ i := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hi).2

theorem lt_of_mem_adjacentReverseSuffix {r : ℕ}
    (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row i : Fin (r + 2))
    (hi : i ∈ adjacentReverseSuffix low mu row) : i < row := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hi).2

theorem reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
    {r : ℕ} (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) :
    reverseInterlacingRowSchedule low mu =
      adjacentReversePrefix low mu row ++
        adjacentReverseSuffix low mu row := by
  classical
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  have hperm : (pref ++ suff).Perm
      (reverseInterlacingRowSchedule low mu) := by
    apply List.perm_iff_count.mpr
    intro i
    rw [List.count_append]
    by_cases hi : row ≤ i
    · have hprefix : pref.count i =
          (reverseInterlacingRowSchedule low mu).count i := by
        exact List.count_filter (by simpa only [decide_eq_true_eq] using hi)
      have hsuffix : suff.count i = 0 := by
        apply List.count_eq_zero.mpr
        intro hmem
        have hlt := lt_of_mem_adjacentReverseSuffix
          low mu row i hmem
        exact (not_lt_of_ge hi) hlt
      rw [hprefix, hsuffix, Nat.add_zero]
    · have hlt : i < row := lt_of_not_ge hi
      have hprefix : pref.count i = 0 := by
        apply List.count_eq_zero.mpr
        intro hmem
        exact hi (le_of_mem_adjacentReversePrefix
          low mu row i hmem)
      have hsuffix : suff.count i =
          (reverseInterlacingRowSchedule low mu).count i := by
        exact List.count_filter (by simpa only [decide_eq_true_eq] using hlt)
      rw [hprefix, hsuffix, Nat.zero_add]
  have hsorted := reverseInterlacingRowSchedule_pairwise_ge low mu
  have hprefix_sorted : pref.Pairwise (· ≥ ·) :=
    hsorted.filter (fun i => decide (row ≤ i))
  have hsuffix_sorted : suff.Pairwise (· ≥ ·) :=
    hsorted.filter (fun i => decide (i < row))
  have hsplit_sorted : (pref ++ suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hprefix_sorted, hsuffix_sorted, ?_⟩
    intro a ha b hb
    exact (le_of_lt (lt_of_mem_adjacentReverseSuffix
      low mu row b hb)).trans
        (le_of_mem_adjacentReversePrefix low mu row a ha)
  exact hperm.symm.eq_of_sortedGE
    (List.sortedGE_iff_pairwise.mpr hsorted)
    (List.sortedGE_iff_pairwise.mpr hsplit_sorted)

theorem reverseInterlacingRowSchedule_raiseWeight_eq_prefix_cons_suffix
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2)) :
    reverseInterlacingRowSchedule (raiseWeight low row) mu =
      adjacentReversePrefix low mu row ++ row ::
        adjacentReverseSuffix low mu row := by
  classical
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  have hlowSchedule : reverseInterlacingRowSchedule low mu = pref ++ suff :=
    reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
      low mu row
  have hperm :
      (reverseInterlacingRowSchedule (raiseWeight low row) mu).Perm
        (pref ++ row :: suff) := by
    have hfirst := reverseInterlacingRowSchedule_raiseWeight_perm hlow row
    rw [hlowSchedule] at hfirst
    have hswap : (pref ++ suff ++ [row]).Perm (pref ++ row :: suff) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (List.perm_append_comm (l₁ := suff) (l₂ := [row])).append_left pref
    exact hfirst.trans hswap
  have hsortedLow := reverseInterlacingRowSchedule_pairwise_ge low mu
  have hprefix_sorted : pref.Pairwise (· ≥ ·) :=
    hsortedLow.filter (fun i => decide (row ≤ i))
  have hsuffix_sorted : suff.Pairwise (· ≥ ·) :=
    hsortedLow.filter (fun i => decide (i < row))
  have hcons_sorted : (row :: suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, hsuffix_sorted⟩
    intro i hi
    exact le_of_lt (lt_of_mem_adjacentReverseSuffix low mu row i hi)
  have htarget_sorted : (pref ++ row :: suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hprefix_sorted, hcons_sorted, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with hrow | hb
    · subst b
      exact le_of_mem_adjacentReversePrefix low mu row a ha
    · exact (le_of_lt (lt_of_mem_adjacentReverseSuffix
        low mu row b hb)).trans
          (le_of_mem_adjacentReversePrefix low mu row a ha)
  exact hperm.eq_of_sortedGE
    (List.sortedGE_iff_pairwise.mpr
      (reverseInterlacingRowSchedule_pairwise_ge (raiseWeight low row) mu))
    (List.sortedGE_iff_pairwise.mpr htarget_sorted)

theorem arbitraryRowPathWeight_append {r : ℕ}
    (lam : Fin (r + 2) → ℕ)
    (pref suff : List (Fin (r + 2))) :
    arbitraryRowPathWeight lam (pref ++ suff) =
      arbitraryRowPathWeight (arbitraryRowPathWeight lam pref) suff := by
  simp only [arbitraryRowPathWeight_eq_foldl, List.foldl_append]

theorem arbitraryRowPathWeight_adjacentReversePrefix_append_suffix
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2)) :
    arbitraryRowPathWeight (appendZeroWeight mu)
        (adjacentReversePrefix low mu row ++
          adjacentReverseSuffix low mu row) = low := by
  rw [← reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix]
  exact arbitraryRowPathWeight_reverseInterlacingRowSchedule hlow

end HigherYoungArbitraryRankAdjacentInterlacingSchedule

end

end Spherical

end MetricCodes

end MetricCodesNoncomputable
