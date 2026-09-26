/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorTermCount
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

/-!
# Deleting the least Cantor term

The least additive-principal term of a natural ordinal, its deletion, and the properties of
that deletion: it splits a nonzero grade as `removeLeastTerm a + leastTerm a = a`, it drops
`cantorTermCount` by exactly one, and it agrees with `NatOrdinal.removeNat _ 1` exactly on the
grades carrying a finite part.
-/

open Ordinal

universe u

public noncomputable section

namespace NatOrdinal

/-- The final additive-principal term of the ordinal, or zero when the ordinal is zero. -/
def leastTerm (a : NatOrdinal.{u}) : NatOrdinal.{u} :=
  NatOrdinal.of (a.val.additivePrincipalTerms.getLastD 0)

/-- The ordinal obtained by removing the final additive-principal term from its Cantor
decomposition. -/
def removeLeastTerm (a : NatOrdinal.{u}) : NatOrdinal.{u} :=
  NatOrdinal.of a.val.additivePrincipalTerms.dropLast.sum

@[simp]
theorem val_removeLeastTerm (a : NatOrdinal.{u}) :
    (removeLeastTerm a).val = a.val.additivePrincipalTerms.dropLast.sum := by
  rw [removeLeastTerm, NatOrdinal.val_of]

@[simp]
theorem leastTerm_zero : leastTerm (0 : NatOrdinal.{u}) = 0 := by
  rw [leastTerm, show (0 : NatOrdinal.{u}).val = 0 from rfl,
    Ordinal.additivePrincipalTerms_zero]
  rfl

@[simp]
theorem removeLeastTerm_zero : removeLeastTerm (0 : NatOrdinal.{u}) = 0 := by
  rw [removeLeastTerm, show (0 : NatOrdinal.{u}).val = 0 from rfl,
    Ordinal.additivePrincipalTerms_zero]
  rfl

theorem additivePrincipalTerms_ne_nil {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    a.val.additivePrincipalTerms ≠ [] := by
  intro hnil
  apply ha
  apply NatOrdinal.val.injective
  have hsum := Ordinal.additivePrincipalTerms_sum a.val
  rw [hnil] at hsum
  simpa using hsum.symm

theorem val_leastTerm {a : NatOrdinal.{u}} (hne : a.val.additivePrincipalTerms ≠ []) :
    (leastTerm a).val = a.val.additivePrincipalTerms.getLast hne := by
  rw [leastTerm, NatOrdinal.val_of, List.getLastD_eq_getLast?,
    List.getLast?_eq_some_getLast hne]
  rfl

theorem isAdditivelyPrincipal_leastTerm {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    IsAdditivelyPrincipal (leastTerm a).val := by
  rw [val_leastTerm (additivePrincipalTerms_ne_nil ha)]
  exact Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms
    (List.getLast_mem _)

theorem removeLeastTerm_add_leastTerm (a : NatOrdinal.{u}) :
    removeLeastTerm a + leastTerm a = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hne : a.val.additivePrincipalTerms ≠ [] := additivePrincipalTerms_ne_nil ha
  set l := a.val.additivePrincipalTerms with hl
  have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
  have hprincipal : ∀ x ∈ l, IsAdditivelyPrincipal x := fun _ hx ↦
    Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms hx
  have hsorted : l.SortedGE := Ordinal.additivePrincipalTerms_sortedGE a.val
  have hdropPrincipal : ∀ x ∈ l.dropLast, IsAdditivelyPrincipal x := fun _ hx ↦
    hprincipal _ (List.dropLast_subset _ hx)
  have hdropSorted : l.dropLast.SortedGE := by
    rw [List.sortedGE_iff_pairwise] at hsorted ⊢
    exact hsorted.sublist (List.dropLast_sublist _)
  apply NatOrdinal.val.injective
  have hmain : NatOrdinal.of l.sum = removeLeastTerm a + leastTerm a := by
    rw [Ordinal.natOrdinal_of_sum_eq_sum_map_of_sorted hprincipal hsorted]
    conv_lhs => rw [← hsplit]
    rw [List.map_append, List.sum_append]
    congr 1
    · rw [removeLeastTerm, ← hl,
        Ordinal.natOrdinal_of_sum_eq_sum_map_of_sorted hdropPrincipal hdropSorted]
    · show (List.map (⇑NatOrdinal.of) [l.getLast hne]).sum = leastTerm a
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      apply NatOrdinal.val.injective
      rw [NatOrdinal.val_of, val_leastTerm hne]
  rw [← hmain, NatOrdinal.val_of, hl]
  exact Ordinal.additivePrincipalTerms_sum a.val

theorem cantorTermCount_leastTerm {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    cantorTermCount (leastTerm a) = 1 := by
  have hself : leastTerm a = NatOrdinal.of (leastTerm a).val := rfl
  rw [hself, cantorTermCount_of,
    Ordinal.additivePrincipalTerms_of_isAdditivelyPrincipal
      (isAdditivelyPrincipal_leastTerm ha)]
  rfl

theorem cantorTermCount_removeLeastTerm {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    cantorTermCount (removeLeastTerm a) + 1 = cantorTermCount a := by
  conv_rhs => rw [← removeLeastTerm_add_leastTerm a]
  rw [cantorTermCount_add, cantorTermCount_leastTerm ha]

theorem cantorTermCount_removeLeastTerm_lt {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    cantorTermCount (removeLeastTerm a) < cantorTermCount a := by
  rw [← cantorTermCount_removeLeastTerm ha]
  omega

theorem removeLeastTerm_eq_zero_iff {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    removeLeastTerm a = 0 ↔ cantorTermCount a = 1 := by
  constructor
  · intro hzero
    have hcount := cantorTermCount_removeLeastTerm ha
    rw [hzero, cantorTermCount_zero] at hcount
    omega
  · intro hone
    have hcount := cantorTermCount_removeLeastTerm ha
    rw [hone] at hcount
    exact cantorTermCount_eq_zero.mp (by omega)

theorem cantorTermCount_eq_one_iff {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    cantorTermCount a = 1 ↔ Ordinal.IsAdditivelyPrincipal a.val := by
  constructor
  · intro hone
    have hne := additivePrincipalTerms_ne_nil ha
    have hlen : a.val.additivePrincipalTerms.length = 1 := by
      have hself : a = NatOrdinal.of a.val := rfl
      rw [hself, cantorTermCount_of] at hone
      exact hone
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    have hsum := Ordinal.additivePrincipalTerms_sum a.val
    rw [hx, List.sum_cons, List.sum_nil, add_zero] at hsum
    rw [← hsum]
    exact Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms
      (by rw [hx]; simp)
  · intro hprin
    have hself : a = NatOrdinal.of a.val := rfl
    rw [hself, cantorTermCount_of,
      Ordinal.additivePrincipalTerms_of_isAdditivelyPrincipal hprin]
    rfl

/-! ### The least term of a sum -/

private theorem getLast_le_of_mem :
    ∀ (l : List Ordinal.{u}), l.SortedGE → ∀ (hne : l ≠ []) (y : Ordinal.{u}),
      y ∈ l → l.getLast hne ≤ y := by
  intro l
  induction l with
  | nil => intro _ hne; exact absurd rfl hne
  | cons c t ih =>
      intro hs hne y hy
      cases t with
      | nil =>
          rw [List.mem_singleton] at hy
          subst hy
          simp
      | cons d u =>
          have hcons : (d :: u) ≠ [] := by simp
          rw [List.getLast_cons hcons]
          have hpair := List.sortedGE_iff_pairwise.mp hs
          have hst : (d :: u).SortedGE :=
            List.sortedGE_iff_pairwise.mpr hpair.tail
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact List.rel_of_pairwise_cons hpair (List.getLast_mem hcons)
          · exact ih hst hcons y hy'

theorem val_leastTerm_mem {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    (leastTerm a).val ∈ a.val.additivePrincipalTerms := by
  rw [val_leastTerm (additivePrincipalTerms_ne_nil ha)]
  exact List.getLast_mem _

theorem val_leastTerm_le_of_mem {a : NatOrdinal.{u}} (ha : a ≠ 0)
    {y : Ordinal.{u}} (hy : y ∈ a.val.additivePrincipalTerms) :
    (leastTerm a).val ≤ y := by
  rw [val_leastTerm (additivePrincipalTerms_ne_nil ha)]
  exact getLast_le_of_mem _ (Ordinal.additivePrincipalTerms_sortedGE a.val) _ y hy

theorem leastTerm_add {a b : NatOrdinal.{u}} (ha : a ≠ 0) (hb : b ≠ 0) :
    leastTerm (a + b) = min (leastTerm a) (leastTerm b) := by
  have hab : a + b ≠ 0 := by
    intro hzero
    apply ha
    have := cantorTermCount_add a b
    rw [hzero, cantorTermCount_zero] at this
    exact cantorTermCount_eq_zero.mp (by omega)
  have hperm := additivePrincipalTerms_add_perm a b
  have hmemA : (leastTerm a).val ∈ (a + b).val.additivePrincipalTerms := by
    rw [hperm.mem_iff, List.mem_append]
    exact Or.inl (val_leastTerm_mem ha)
  have hmemB : (leastTerm b).val ∈ (a + b).val.additivePrincipalTerms := by
    rw [hperm.mem_iff, List.mem_append]
    exact Or.inr (val_leastTerm_mem hb)
  have hle : (leastTerm (a + b)).val ≤ min (leastTerm a).val (leastTerm b).val :=
    le_min (val_leastTerm_le_of_mem hab hmemA) (val_leastTerm_le_of_mem hab hmemB)
  have hge : min (leastTerm a).val (leastTerm b).val ≤ (leastTerm (a + b)).val := by
    have hmem := val_leastTerm_mem hab
    rw [hperm.mem_iff, List.mem_append] at hmem
    rcases hmem with h | h
    · exact (min_le_left _ _).trans (val_leastTerm_le_of_mem ha h)
    · exact (min_le_right _ _).trans (val_leastTerm_le_of_mem hb h)
  apply NatOrdinal.val.injective
  rcases le_total (leastTerm a) (leastTerm b) with hab' | hab'
  · rw [min_eq_left hab']
    exact le_antisymm (hle.trans (min_le_left _ _))
      ((le_min (le_refl _) hab').trans hge)
  · rw [min_eq_right hab']
    exact le_antisymm (hle.trans (min_le_right _ _))
      ((le_min hab' (le_refl _)).trans hge)

theorem removeLeastTerm_add_of_leastTerm_le {a b : NatOrdinal.{u}}
    (ha : a ≠ 0) (hb : b ≠ 0) (hle : leastTerm a ≤ leastTerm b) :
    removeLeastTerm (a + b) = removeLeastTerm a + b := by
  have hab : a + b ≠ 0 := by
    intro hzero
    apply ha
    have hcount := cantorTermCount_add a b
    rw [hzero, cantorTermCount_zero] at hcount
    exact cantorTermCount_eq_zero.mp (by omega)
  have hmin : leastTerm (a + b) = leastTerm a := by
    rw [leastTerm_add ha hb, min_eq_left hle]
  apply _root_.add_right_cancel (b := leastTerm a)
  calc removeLeastTerm (a + b) + leastTerm a
      = removeLeastTerm (a + b) + leastTerm (a + b) := by rw [hmin]
    _ = a + b := removeLeastTerm_add_leastTerm (a + b)
    _ = (removeLeastTerm a + leastTerm a) + b := by
        rw [removeLeastTerm_add_leastTerm a]
    _ = removeLeastTerm a + b + leastTerm a := by ac_rfl

theorem nsmul_ne_zero_of_ne_zero {a : NatOrdinal.{u}} (ha : a ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) : r • a ≠ 0 := by
  intro hzero
  apply ha
  have hcount : r * cantorTermCount a = 0 := by
    rw [← cantorTermCount_nsmul, hzero, cantorTermCount_zero]
  refine cantorTermCount_eq_zero.mp ?_
  rcases Nat.mul_eq_zero.mp hcount with h | h
  · omega
  · exact h

theorem leastTerm_nsmul {a : NatOrdinal.{u}} (ha : a ≠ 0) {r : ℕ} (hr : 1 ≤ r) :
    leastTerm (r • a) = leastTerm a := by
  induction r with
  | zero => omega
  | succ r ih =>
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · simp
      · rw [succ_nsmul, leastTerm_add (nsmul_ne_zero_of_ne_zero ha hrpos) ha,
          ih hrpos, min_self]

theorem removeLeastTerm_nsmul {a : NatOrdinal.{u}} (ha : a ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) :
    removeLeastTerm a + (r - 1) • a = removeLeastTerm (r • a) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hsimp : s + 1 - 1 = s := by omega
  rw [hsimp]
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · simp
  · have hs : s • a ≠ 0 := nsmul_ne_zero_of_ne_zero ha hspos
    have hle : leastTerm a ≤ leastTerm (s • a) := by
      rw [leastTerm_nsmul ha hspos]
    rw [succ_nsmul, add_comm (s • a) a,
      ← removeLeastTerm_add_of_leastTerm_le ha hs hle]

theorem removeLeastTerm_add_of_leastTerm_ge {a b : NatOrdinal.{u}}
    (ha : a ≠ 0) (hb : b ≠ 0) (hle : leastTerm b ≤ leastTerm a) :
    removeLeastTerm (a + b) = a + removeLeastTerm b := by
  rw [add_comm a b, removeLeastTerm_add_of_leastTerm_le hb ha hle, add_comm]

theorem leastTerm_eq_self_of_isAdditivelyPrincipal {a : NatOrdinal.{u}} (ha : a ≠ 0)
    (hprin : Ordinal.IsAdditivelyPrincipal a.val) : leastTerm a = a := by
  have hzero : removeLeastTerm a = 0 :=
    (removeLeastTerm_eq_zero_iff ha).mpr
      ((cantorTermCount_eq_one_iff ha).mpr hprin)
  have hsplit := removeLeastTerm_add_leastTerm a
  rwa [hzero, zero_add] at hsplit

/-! ### Deletion on a sum with a repeated summand

The grade `k • alpha + beta` has least Cantor term `min (leastTerm alpha) (leastTerm beta)`, by
`leastTerm_add` and `leastTerm_nsmul`, so deletion falls on whichever side attains the minimum.
The two lemmas below name the two outcomes, and the third says the second outcome can repeat only
finitely often. -/

theorem removeLeastTerm_nsmul_add_of_le {alpha beta : NatOrdinal.{u}}
    (ha : alpha ≠ 0) (hb : beta ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (hle : leastTerm alpha ≤ leastTerm beta) :
    removeLeastTerm (k • alpha + beta) =
      (removeLeastTerm alpha + (k - 1) • alpha) + beta := by
  have hk0 : k • alpha ≠ 0 := nsmul_ne_zero_of_ne_zero ha hk
  have hle' : leastTerm (k • alpha) ≤ leastTerm beta := by
    rwa [leastTerm_nsmul ha hk]
  rw [removeLeastTerm_add_of_leastTerm_le hk0 hb hle', removeLeastTerm_nsmul ha hk]

theorem removeLeastTerm_nsmul_add_of_ge {alpha beta : NatOrdinal.{u}}
    (ha : alpha ≠ 0) (hb : beta ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (hle : leastTerm beta ≤ leastTerm alpha) :
    removeLeastTerm (k • alpha + beta) = k • alpha + removeLeastTerm beta := by
  have hk0 : k • alpha ≠ 0 := nsmul_ne_zero_of_ne_zero ha hk
  have hle' : leastTerm beta ≤ leastTerm (k • alpha) := by
    rwa [leastTerm_nsmul ha hk]
  exact removeLeastTerm_add_of_leastTerm_ge hk0 hb hle'

theorem exists_iterate_removeLeastTerm (alpha : NatOrdinal.{u}) (beta : NatOrdinal.{u}) :
    ∃ j : ℕ, removeLeastTerm^[j] beta = 0 ∨
      leastTerm alpha ≤ leastTerm (removeLeastTerm^[j] beta) := by
  generalize hn : cantorTermCount beta = n
  induction n using Nat.strong_induction_on generalizing beta with
  | _ n ih =>
    rcases eq_or_ne beta 0 with rfl | hb
    · exact ⟨0, Or.inl rfl⟩
    rcases le_or_gt (leastTerm alpha) (leastTerm beta) with hle | hgt
    · exact ⟨0, Or.inr hle⟩
    · have hlt : cantorTermCount (removeLeastTerm beta) < n := by
        rw [← hn]
        exact cantorTermCount_removeLeastTerm_lt hb
      obtain ⟨j, hj⟩ := ih _ hlt (removeLeastTerm beta) rfl
      refine ⟨j + 1, ?_⟩
      rwa [Function.iterate_succ_apply]

theorem removeLeastTerm_add_one_eq_self_iff {a : NatOrdinal.{u}} :
    removeLeastTerm a + 1 = a ↔ leastTerm a = 1 := by
  constructor
  · intro h
    conv_rhs at h => rw [← removeLeastTerm_add_leastTerm a]
    exact (_root_.add_right_injective _ h).symm
  · intro h
    rw [← h, removeLeastTerm_add_leastTerm]

theorem add_ne_of_isAdditivelyPrincipal {a i j : NatOrdinal.{u}}
    (ha : Ordinal.IsAdditivelyPrincipal a.val) (hi : i ≠ 0) (hj : j ≠ 0) :
    i + j ≠ a := by
  intro hij
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero] at hij
    exact hi (le_antisymm (hij ▸ le_add_right) zero_le)
  have hcount : cantorTermCount a = 1 := (cantorTermCount_eq_one_iff ha0).mpr ha
  rw [← hij, cantorTermCount_add] at hcount
  have hi1 : cantorTermCount i ≠ 0 := fun h ↦ hi (cantorTermCount_eq_zero.mp h)
  have hj1 : cantorTermCount j ≠ 0 := fun h ↦ hj (cantorTermCount_eq_zero.mp h)
  omega

theorem leastTerm_ne_zero {a : NatOrdinal.{u}} (ha : a ≠ 0) : leastTerm a ≠ 0 := by
  intro hzero
  have hcount := cantorTermCount_leastTerm ha
  rw [hzero, cantorTermCount_zero] at hcount
  omega

theorem one_le_leastTerm {a : NatOrdinal.{u}} (ha : a ≠ 0) : 1 ≤ leastTerm a :=
  Order.one_le_iff_ne_zero.mpr (leastTerm_ne_zero ha)

@[simp]
theorem leastTerm_one : leastTerm (1 : NatOrdinal.{u}) = 1 :=
  leastTerm_eq_self_of_isAdditivelyPrincipal one_ne_zero
    (Ordinal.isAdditivelyPrincipal_iff.mpr ⟨0, by simp⟩)

@[simp]
theorem removeLeastTerm_one : removeLeastTerm (1 : NatOrdinal.{u}) = 0 := by
  have h := removeLeastTerm_add_leastTerm (1 : NatOrdinal.{u})
  rw [leastTerm_one] at h
  simpa using h

theorem removeLeastTerm_add_one {a : NatOrdinal.{u}} :
    removeLeastTerm (a + 1) = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [removeLeastTerm_add_of_leastTerm_ge ha one_ne_zero
      (by rw [leastTerm_one]; exact one_le_leastTerm ha), removeLeastTerm_one, add_zero]

/-- Deletion is not strictly monotone below a grade whose least Cantor term exceeds `1`: the
grade `removeLeastTerm a + 1` is strictly below `a`, yet deletion sends it to `removeLeastTerm a`
rather than below it. -/
theorem exists_lt_removeLeastTerm_not_lt {a : NatOrdinal.{u}} (ha : 1 < leastTerm a) :
    ∃ b : NatOrdinal.{u}, b ≠ 0 ∧ b < a ∧ removeLeastTerm a ≤ removeLeastTerm b := by
  refine ⟨removeLeastTerm a + 1, ?_, ?_, ?_⟩
  · intro hzero
    have : (1 : NatOrdinal.{u}) ≤ removeLeastTerm a + 1 := le_add_left
    rw [hzero] at this
    exact absurd (le_antisymm this zero_le) one_ne_zero
  · conv_rhs => rw [← removeLeastTerm_add_leastTerm a]
    exact add_lt_add_of_le_of_lt le_rfl ha
  · rw [removeLeastTerm_add_one]

/-! ### Agreement with the finite-part operation -/

theorem additivePrincipalTerms_eq_append_one {a : NatOrdinal.{u}}
    (ha : 0 < a.constantCoeff) :
    (a.removeNat 1).val.additivePrincipalTerms ++ [1] = a.val.additivePrincipalTerms := by
  set terms := (a.removeNat 1).val.additivePrincipalTerms with hterms
  have hpred : (a.removeNat 1).val + (1 : Ordinal) = a.val := by
    have h := congrArg NatOrdinal.val (removeNat_add_natCast (n := 1) ha)
    calc
      (a.removeNat 1).val + (1 : Ordinal) =
          (a.removeNat 1).val + ((1 : ℕ) : Ordinal) := by rw [Nat.cast_one]
      _ = (a.removeNat 1 + ((1 : ℕ) : NatOrdinal)).val :=
        (NatOrdinal.val_add_natCast (a.removeNat 1) 1).symm
      _ = a.val := h
  have hsum : (terms ++ [1]).sum = a.val := by
    rw [List.sum_append, List.sum_singleton, hterms,
      Ordinal.additivePrincipalTerms_sum]
    exact hpred
  have hprincipal : ∀ x ∈ terms ++ [1], IsAdditivelyPrincipal x := by
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms hx
    · simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 0
  have hsorted : (terms ++ [1]).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp (Ordinal.additivePrincipalTerms_sortedGE _),
      by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact Order.one_le_iff_ne_zero.mpr
      (Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms hx).ne_zero
  exact Ordinal.additivePrincipalTerms_unique hsum hprincipal hsorted

theorem leastTerm_eq_one_of_constantCoeff_pos {a : NatOrdinal.{u}}
    (ha : 0 < a.constantCoeff) : leastTerm a = 1 := by
  apply NatOrdinal.val.injective
  rw [leastTerm, NatOrdinal.val_of, ← additivePrincipalTerms_eq_append_one ha]
  simp

theorem removeLeastTerm_eq_removeNat_one {a : NatOrdinal.{u}}
    (ha : 0 < a.constantCoeff) : removeLeastTerm a = a.removeNat 1 := by
  apply NatOrdinal.val.injective
  rw [removeLeastTerm, NatOrdinal.val_of, ← additivePrincipalTerms_eq_append_one ha,
    List.dropLast_concat]
  exact Ordinal.additivePrincipalTerms_sum _

end NatOrdinal

end
