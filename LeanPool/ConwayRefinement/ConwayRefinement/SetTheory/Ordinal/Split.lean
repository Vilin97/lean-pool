/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorTermCount
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# The parts of an ordinal at or above, and below, an exponent

For a natural ordinal `a` and an exponent `β`, write the Cantor normal form of `a` with repeated
terms [LM24, §2.2] as `a = ω^{e_1} + ⋯ + ω^{e_r}` with `e_1 ≥ ⋯ ≥ e_r`, and let `a_{≥β}` be the sum
of the terms with `e_i ≥ β` and `a_{<β}` the sum of those with `e_i < β` — the *part of `a` at or
above `β`* (Lean `partGE β a`) and the *part of `a` below `β`* (`partLT β a`). Then
`a = a_{≥β} + a_{<β} = a_{≥β} ⊕ a_{<β}`, `a_{<β} < ω^β`, `a_{≥β}` is a multiple of `ω^β`, and both
parts are additive for the natural sum `⊕`, the Cantor normal form of a natural sum being the merge
of the two normal forms. This is the bookkeeping used when a grading by ordinals is split at an
exponent.
-/

universe u

open Ordinal

public noncomputable section

namespace NatOrdinal

open scoped Classical in
/-- The part `a_{≥β}` of `a` at or above `β`: the sum of the terms `ω^e` of the Cantor normal form
of `a` with `e ≥ β`. -/
def partGE (β a : NatOrdinal.{u}) : NatOrdinal.{u} :=
  ((a.val.additivePrincipalTerms.filter fun t ↦ (ω^ β).val ≤ t).map NatOrdinal.of).sum

open scoped Classical in
/-- The part `a_{<β}` of `a` below `β`: the sum of the terms `ω^e` of the Cantor normal form of `a`
with `e < β`. -/
def partLT (β a : NatOrdinal.{u}) : NatOrdinal.{u} :=
  ((a.val.additivePrincipalTerms.filter fun t ↦ t < (ω^ β).val).map NatOrdinal.of).sum

/-- A natural ordinal is the natural sum of its Cantor terms. -/
theorem sum_map_of_additivePrincipalTerms (a : NatOrdinal.{u}) :
    (a.val.additivePrincipalTerms.map NatOrdinal.of).sum = a := by
  rw [← natOrdinal_of_sum_eq_sum_map_of_sorted
    (fun t ht ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms ht)
    (additivePrincipalTerms_sortedGE _), additivePrincipalTerms_sum, NatOrdinal.of_val]

/-- Splitting a list sum along a predicate. -/
theorem sum_map_filter_add_sum_map_filter_not {l : List Ordinal.{u}} (p : Ordinal.{u} → Prop)
    [DecidablePred p] :
    ((l.filter p).map NatOrdinal.of).sum + ((l.filter fun t ↦ ¬ p t).map NatOrdinal.of).sum =
      (l.map NatOrdinal.of).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · rw [List.filter_cons_of_pos (by simpa using ha), List.filter_cons_of_neg (by simpa using ha),
        List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_assoc, ih]
    · rw [List.filter_cons_of_neg (by simpa using ha), List.filter_cons_of_pos (by simpa using ha),
        List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_left_comm, ih]

/-- `a = a_{≥β} + a_{<β}`. -/
theorem partGE_add_partLT (β a : NatOrdinal.{u}) :
    partGE β a + partLT β a = a := by
  classical
  rw [partGE, partLT]
  have h := sum_map_filter_add_sum_map_filter_not (l := a.val.additivePrincipalTerms)
    fun t ↦ (ω^ β).val ≤ t
  simp only [not_le] at h
  rw [h, sum_map_of_additivePrincipalTerms]

/-- The sum of the `of` of a list of ordinals is invariant under permutation. -/
theorem sum_map_of_perm {l l' : List Ordinal.{u}} (h : l.Perm l') :
    (l.map NatOrdinal.of).sum = (l'.map NatOrdinal.of).sum :=
  (h.map NatOrdinal.of).sum_eq

/-- The part at or above `β` is additive for the natural sum. -/
theorem partGE_add (β a b : NatOrdinal.{u}) :
    partGE β (a + b) = partGE β a + partGE β b := by
  classical
  rw [partGE, partGE, partGE, ← List.sum_append, ← List.map_append,
    ← List.filter_append]
  exact sum_map_of_perm ((additivePrincipalTerms_add_perm a b).filter _)

/-- The part below `β` is additive for the natural sum. -/
theorem partLT_add (β a b : NatOrdinal.{u}) :
    partLT β (a + b) = partLT β a + partLT β b := by
  classical
  rw [partLT, partLT, partLT, ← List.sum_append, ← List.map_append,
    ← List.filter_append]
  exact sum_map_of_perm ((additivePrincipalTerms_add_perm a b).filter _)

/-- A natural sum of finitely many ordinals below `ω^β` is below `ω^β`. -/
theorem sum_map_of_lt_wpow {l : List Ordinal.{u}} {β : NatOrdinal.{u}}
    (h : ∀ t ∈ l, t < (ω^ β).val) : (l.map NatOrdinal.of).sum < ω^ β := by
  induction l with
  | nil => simp [NatOrdinal.wpow_pos]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    refine add_lt_of_isAdditivelyPrincipal ?_ ?_ (ih fun t ht ↦ h t (List.mem_cons_of_mem a ht))
    · rw [NatOrdinal.val_wpow]
      exact isAdditivelyPrincipal_omega0_opow _
    · rw [← NatOrdinal.of_val (ω^ β)]
      exact NatOrdinal.of.lt_iff_lt.mpr (h a (List.mem_cons_self ..))

/-- The part of `a` below `β` is below `ω^β`. -/
theorem partLT_lt (β a : NatOrdinal.{u}) : partLT β a < ω^ β := by
  classical
  rw [partLT]
  exact sum_map_of_lt_wpow fun t ht ↦ of_decide_eq_true (List.mem_filter.mp ht).2

@[simp]
theorem partGE_zero (β : NatOrdinal.{u}) : partGE β 0 = 0 := by
  classical
  simp [partGE]

@[simp]
theorem partLT_zero (β : NatOrdinal.{u}) : partLT β 0 = 0 := by
  classical
  simp [partLT]

/-- Taking the part at or above `β`, as an endomorphism of the natural-sum monoid. -/
def partGEAddMonoidHom (β : NatOrdinal.{u}) : NatOrdinal.{u} →+ NatOrdinal.{u} where
  toFun := partGE β
  map_zero' := partGE_zero β
  map_add' := partGE_add β

/-- Taking the part below `β`, as an endomorphism of the natural-sum monoid. -/
def partLTAddMonoidHom (β : NatOrdinal.{u}) : NatOrdinal.{u} →+ NatOrdinal.{u} where
  toFun := partLT β
  map_zero' := partLT_zero β
  map_add' := partLT_add β

@[simp]
theorem partGEAddMonoidHom_apply (β a : NatOrdinal.{u}) : partGEAddMonoidHom β a = partGE β a :=
  (rfl)

@[simp]
theorem partLTAddMonoidHom_apply (β a : NatOrdinal.{u}) : partLTAddMonoidHom β a = partLT β a :=
  (rfl)

theorem partGE_nsmul (β : NatOrdinal.{u}) (n : ℕ) (a : NatOrdinal.{u}) :
    partGE β (n • a) = n • partGE β a := by
  simpa using (partGEAddMonoidHom β).map_nsmul n a

theorem partLT_nsmul (β : NatOrdinal.{u}) (n : ℕ) (a : NatOrdinal.{u}) :
    partLT β (n • a) = n • partLT β a := by
  simpa using (partLTAddMonoidHom β).map_nsmul n a

theorem partGE_sum {ι : Type*} (β : NatOrdinal.{u}) (s : Finset ι) (f : ι → NatOrdinal.{u}) :
    partGE β (∑ i ∈ s, f i) = ∑ i ∈ s, partGE β (f i) := by
  rw [← partGEAddMonoidHom_apply β (∑ i ∈ s, f i), map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ partGEAddMonoidHom_apply β (f i)

theorem partLT_sum {ι : Type*} (β : NatOrdinal.{u}) (s : Finset ι) (f : ι → NatOrdinal.{u}) :
    partLT β (∑ i ∈ s, f i) = ∑ i ∈ s, partLT β (f i) := by
  rw [← partLTAddMonoidHom_apply β (∑ i ∈ s, f i), map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ partLTAddMonoidHom_apply β (f i)

/-- Every Cantor term of `a` is at most `a`. -/
theorem of_le_of_mem_additivePrincipalTerms {a : NatOrdinal.{u}} {t : Ordinal.{u}}
    (ht : t ∈ a.val.additivePrincipalTerms) : NatOrdinal.of t ≤ a := by
  have h := sum_map_of_additivePrincipalTerms a
  rw [← h]
  exact List.single_le_sum (fun _ _ ↦ zero_le) _ (List.mem_map_of_mem ht)

/-- An ordinal below `ω^β` has part `0` at or above `β`. -/
theorem partGE_eq_zero_of_lt {β a : NatOrdinal.{u}} (ha : a < ω^ β) : partGE β a = 0 := by
  classical
  rw [partGE, List.filter_eq_nil_iff.mpr, List.map_nil, List.sum_nil]
  intro t ht
  rw [decide_eq_true_eq, not_le]
  have h := (of_le_of_mem_additivePrincipalTerms ht).trans_lt ha
  rw [← NatOrdinal.of_val (ω^ β)] at h
  exact NatOrdinal.of.lt_iff_lt.mp h

/-- An ordinal below `ω^β` is its own part below `β`. -/
theorem partLT_eq_self_of_lt {β a : NatOrdinal.{u}} (ha : a < ω^ β) : partLT β a = a := by
  have h := partGE_add_partLT β a
  rwa [partGE_eq_zero_of_lt ha, zero_add] at h

/-! ### The part at or above `β` is a multiple of `ω^β`; the two parts add as an ordinal sum -/

/-- The part of `a` at or above `β` is a multiple of `ω^β`: all its terms are at least `ω^β`. -/
theorem exists_val_partGE_eq_mul (β a : NatOrdinal.{u}) :
    ∃ q : Ordinal.{u}, (partGE β a).val = (ω^ β).val * q := by
  classical
  rw [partGE]
  have hsorted : (a.val.additivePrincipalTerms.filter fun t ↦ (ω^ β).val ≤ t).SortedGE :=
    List.sortedGE_iff_pairwise.mpr
      ((List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE _)).sublist
        List.filter_sublist)
  have hprincipal : ∀ t ∈ a.val.additivePrincipalTerms.filter fun t ↦ (ω^ β).val ≤ t,
      IsAdditivelyPrincipal t := fun t ht ↦
    isAdditivelyPrincipal_of_mem_additivePrincipalTerms (List.mem_of_mem_filter ht)
  rw [← natOrdinal_of_sum_eq_sum_map_of_sorted hprincipal hsorted, NatOrdinal.val_of]
  -- every term is a power `ω^e` with `e ≥ β`
  have hterm : ∀ t ∈ a.val.additivePrincipalTerms.filter fun t ↦ (ω^ β).val ≤ t,
      ∃ q, t = (ω^ β).val * q := fun t ht ↦ by
    have hle : (ω^ β).val ≤ t := of_decide_eq_true (List.mem_filter.mp ht).2
    obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp (hprincipal t ht)
    rw [NatOrdinal.val_wpow] at hle ⊢
    have hβe : β.val ≤ e := (opow_le_opow_iff_right one_lt_omega0).mp hle
    exact ⟨ω ^ (e - β.val), by rw [← opow_add, Ordinal.add_sub_cancel_of_le hβe]⟩
  have hmul : ∀ l : List Ordinal.{u}, (∀ t ∈ l, ∃ q, t = (ω^ β).val * q) →
      ∃ q, l.sum = (ω^ β).val * q := by
    intro l hl
    induction l with
    | nil => exact ⟨0, by simp⟩
    | cons t l ih =>
      obtain ⟨q₁, hq₁⟩ := hl t (List.mem_cons_self ..)
      obtain ⟨q₂, hq₂⟩ := ih fun t' ht' ↦ hl t' (List.mem_cons_of_mem t ht')
      exact ⟨q₁ + q₂, by rw [List.sum_cons, hq₁, hq₂, mul_add]⟩
  exact hmul _ hterm

/-- Two multiples of `w` are at least `w` apart. -/
theorem add_le_of_dvd_of_lt {w u v : Ordinal.{u}} (hu : ∃ q, u = w * q) (hv : ∃ q, v = w * q)
    (huv : u < v) : u + w ≤ v := by
  obtain ⟨qu, rfl⟩ := hu
  obtain ⟨qv, rfl⟩ := hv
  have hw : 0 < w := by
    rcases eq_or_ne w 0 with rfl | h
    · simp at huv
    · exact pos_iff_ne_zero.mpr h
  have hq : qu < qv := by
    by_contra hle
    rw [not_lt] at hle
    exact absurd huv (not_lt.mpr (mul_le_mul_right hle w))
  calc w * qu + w = w * Order.succ qu := (Ordinal.mul_succ w qu).symm
    _ ≤ w * qv := mul_le_mul_right (Order.succ_le_of_lt hq) w

/-- The natural sum of an ordinal all of whose Cantor terms are at least `w` and an ordinal all of
whose Cantor terms are below `w` is their ordinal sum. -/
theorem of_add_of_eq_add_of_forall_lt {u t : Ordinal.{u}} {w : Ordinal.{u}}
    (hu : ∀ s ∈ u.additivePrincipalTerms, w ≤ s) (ht : ∀ s ∈ t.additivePrincipalTerms, s < w) :
    NatOrdinal.of u + NatOrdinal.of t = NatOrdinal.of (u + t) := by
  have hsorted : (u.additivePrincipalTerms ++ t.additivePrincipalTerms).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE u),
      List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE t), fun s hs s' hs' ↦ ?_⟩
    exact ((ht s' hs').trans_le (hu s hs)).le
  have hprincipal : ∀ s ∈ u.additivePrincipalTerms ++ t.additivePrincipalTerms,
      IsAdditivelyPrincipal s := fun s hs ↦ by
    rcases List.mem_append.mp hs with h | h
    · exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms h
    · exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms h
  have h := natOrdinal_of_sum_eq_sum_map_of_sorted hprincipal hsorted
  have hu' := sum_map_of_additivePrincipalTerms (NatOrdinal.of u)
  have ht' := sum_map_of_additivePrincipalTerms (NatOrdinal.of t)
  rw [NatOrdinal.val_of] at hu' ht'
  rw [List.sum_append, additivePrincipalTerms_sum, additivePrincipalTerms_sum, List.map_append,
    List.sum_append, hu', ht'] at h
  exact h.symm

/-- The terms of the Cantor normal form of `a_{≥β}` are at least `ω^β`. -/
theorem wpow_le_of_mem_additivePrincipalTerms_partGE {β a : NatOrdinal.{u}} {s : Ordinal.{u}}
    (hs : s ∈ (partGE β a).val.additivePrincipalTerms) : (ω^ β).val ≤ s := by
  classical
  have hmem := mem_of_mem_additivePrincipalTerms_natSum
    (L := a.val.additivePrincipalTerms.filter fun t ↦ (ω^ β).val ≤ t)
    (fun t ht ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms (List.mem_of_mem_filter ht))
    (by rwa [partGE] at hs)
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- The terms of the Cantor normal form of `a_{<β}` are below `ω^β`. -/
theorem lt_wpow_of_mem_additivePrincipalTerms_partLT {β a : NatOrdinal.{u}} {s : Ordinal.{u}}
    (hs : s ∈ (partLT β a).val.additivePrincipalTerms) : s < (ω^ β).val := by
  classical
  have hmem := mem_of_mem_additivePrincipalTerms_natSum
    (L := a.val.additivePrincipalTerms.filter fun t ↦ t < (ω^ β).val)
    (fun t ht ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms (List.mem_of_mem_filter ht))
    (by rwa [partLT] at hs)
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- `a = a_{≥β} + a_{<β}` as an ordinal sum. -/
theorem val_eq_val_partGE_add_val_partLT (β a : NatOrdinal.{u}) :
    a.val = (partGE β a).val + (partLT β a).val := by
  have h := of_add_of_eq_add_of_forall_lt (w := (ω^ β).val)
    (fun s hs ↦ wpow_le_of_mem_additivePrincipalTerms_partGE (β := β) (a := a) hs)
    (fun s hs ↦ lt_wpow_of_mem_additivePrincipalTerms_partLT (β := β) (a := a) hs)
  rw [NatOrdinal.of_val, NatOrdinal.of_val, partGE_add_partLT] at h
  have := congrArg NatOrdinal.val h
  rwa [NatOrdinal.val_of] at this

/-- The part at or above `β` is monotone. -/
theorem partGE_mono {β a b : NatOrdinal.{u}} (hab : a ≤ b) :
    partGE β a ≤ partGE β b := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := add_le_of_dvd_of_lt (exists_val_partGE_eq_mul β b)
    (exists_val_partGE_eq_mul β a) (NatOrdinal.val.lt_iff_lt.mpr hlt)
  have h2 : b.val < a.val := by
    calc b.val = (partGE β b).val + (partLT β b).val :=
          val_eq_val_partGE_add_val_partLT β b
      _ < (partGE β b).val + (ω^ β).val :=
          (add_lt_add_iff_left _).mpr (NatOrdinal.val.lt_iff_lt.mpr (partLT_lt β b))
      _ ≤ (partGE β a).val := h1
      _ ≤ a.val := by
          rw [val_eq_val_partGE_add_val_partLT β a]
          exact le_self_add
  exact absurd (NatOrdinal.val.lt_iff_lt.mp h2) (not_lt.mpr hab)

/-- Ordinals with the same part at or above `β` are ordered by their parts below `β`. -/
theorem partLT_lt_of_lt_of_partGE_eq {β a b : NatOrdinal.{u}} (hab : a < b)
    (hGE : partGE β a = partGE β b) : partLT β a < partLT β b := by
  have h := NatOrdinal.val.lt_iff_lt.mpr hab
  rw [val_eq_val_partGE_add_val_partLT β a, val_eq_val_partGE_add_val_partLT β b,
    hGE, add_lt_add_iff_left] at h
  exact NatOrdinal.val.lt_iff_lt.mp h

/-- A smaller part at or above `β` forces a smaller ordinal. -/
theorem lt_of_partGE_lt {β a b : NatOrdinal.{u}} (h : partGE β a < partGE β b) :
    a < b :=
  lt_of_not_ge fun hba ↦ absurd (partGE_mono (β := β) hba) (not_le.mpr h)

end NatOrdinal

end
