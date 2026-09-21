/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
public import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Positive additive principal ordinals

LM24, Definition 3.3.1 calls an ordinal additively principal when it is of the form
`Ordinal.omega0 ^ e`. In particular, LM24 excludes zero. Mathlib's more general predicate
`Ordinal.IsPrincipal (· + ·)` includes zero, so `Ordinal.IsAdditivelyPrincipal` records the
source convention explicitly and the bridge theorem retains the necessary nonzero condition.

The purported second equivalence printed in Definition 3.3.1 is false for ordinary ordinal
addition: `1 + ω = ω`. The correct closure condition is Mathlib's
`Ordinal.IsPrincipal (· + ·)`, together with nonzeroness.

The list `Ordinal.additivePrincipalTerms o` is the uncompressed Cantor normal form of `o`: each
finite coefficient is represented by repeated powers of `ω`. Thus repeated equal terms are
retained, as required by LM24's weak normal forms.

The Cantor terms also settle when ordinary and Hessenberg multiplication by a power of `ω` agree.
The Hessenberg product `ω ^ x ⊙ ω ^ w` equals the ordinary product `ω ^ x * ω ^ w` exactly
when `w` is at most every Cantor term of `x`; the weaker `ω ^ w ≤ ω ^ x` does not suffice, as
`x = ω + 1`, `w = ω` gives `ω ^ (ω * 2)` against `ω ^ (ω * 2 + 1)`. Berarducci, Lemma 8.2 uses
this conversion silently, and its hypothesis on principal values supplies the term condition.

Mathlib supplies `Ordinal.IsPrincipal`, its exact power-of-`ω` characterization, ordinal logarithm,
and compressed Cantor normal form. The uncompressed list is defined by repeatedly removing the
largest power of `ω`, which preserves repeated terms.
-/

universe u

open scoped NatOrdinal

public noncomputable section

namespace Ordinal

/-- An LM24 additive principal ordinal: a positive ordinal of the form `ω ^ e`. -/
def IsAdditivelyPrincipal (o : Ordinal) : Prop :=
  ∃ e : Ordinal, o = omega0 ^ e

/-- Characterization of LM24 additive principal ordinals by powers of `ω`. -/
theorem isAdditivelyPrincipal_iff {o : Ordinal} :
    IsAdditivelyPrincipal o ↔ ∃ e : Ordinal, o = omega0 ^ e :=
  (Iff.rfl)

/-- The difference between LM24's positive convention and Mathlib's additive-principal predicate. -/
theorem isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add {o : Ordinal} :
    IsAdditivelyPrincipal o ↔ o ≠ 0 ∧ IsPrincipal (· + ·) o := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨opow_ne_zero _ omega0_ne_zero, isPrincipal_add_omega0_opow e⟩
  · rintro ⟨ho, hp⟩
    rw [isPrincipal_add_iff_zero_or_omega0_opow] at hp
    rcases hp with hzero | ⟨e, he⟩
    · exact (ho hzero).elim
    · exact ⟨e, he.symm⟩

/-- Every power of `ω` is additive principal in the LM24 convention. -/
theorem isAdditivelyPrincipal_omega0_opow (e : Ordinal) :
    IsAdditivelyPrincipal (omega0 ^ e) :=
  ⟨e, rfl⟩

/-- An LM24 additive principal ordinal is nonzero. -/
theorem IsAdditivelyPrincipal.ne_zero {o : Ordinal} (ho : IsAdditivelyPrincipal o) : o ≠ 0 :=
  (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp ho).1

/-- Every proper initial segment of `ρ * (α + 1)` leaves a remainder of at least `ρ` when `ρ` is
additive principal. This is the principal-part computation used in Berarducci, Lemma 6.8. -/
theorem IsAdditivelyPrincipal.le_of_add_eq_mul_succ {o a b c : Ordinal}
    (ho : IsAdditivelyPrincipal o) (hb : b < o * (a + 1)) (h : b + c = o * (a + 1)) :
    o ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hprincipal :=
    (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp ho).2
  rcases le_or_gt (o * a) b with hge | hlt2
  · set d := b - o * a with hd
    have hbd : o * a + d = b := Ordinal.add_sub_cancel_of_le hge
    rw [mul_add_one] at hb
    have hdlt : d < o := by
      rw [← hbd] at hb
      exact lt_of_add_lt_add_left hb
    have hsum : o * a + (d + c) < o * a + o :=
      (add_lt_add_iff_left _).mpr (hprincipal hdlt hlt)
    rw [← add_assoc, hbd, h, mul_add_one] at hsum
    exact lt_irrefl _ hsum
  · have h1 : b + c ≤ o * a + c := by gcongr
    have h2 : o * a + c < o * a + o := (add_lt_add_iff_left _).mpr hlt
    rw [h, mul_add_one] at h1
    exact lt_irrefl _ (h1.trans_lt h2)

/-- A positive additive-principal ordinal strictly above one is at least `ω`. -/
theorem IsAdditivelyPrincipal.omega0_le_of_one_lt {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) (hone : 1 < o) : omega0 ≤ o := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  rw [one_lt_opow] at hone
  simpa [opow_one] using
    opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr hone.2)

/-- An additive-principal ordinal strictly greater than one is a nonzero limit ordinal. -/
theorem IsAdditivelyPrincipal.isSuccLimit_of_one_lt {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) (hone : 1 < o) : Order.IsSuccLimit o := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  rw [one_lt_opow] at hone
  exact isSuccLimit_opow_left isSuccLimit_omega0 hone.2

/-- The finite list of additive principal terms in the uncompressed Cantor normal form of `o`. -/
noncomputable def additivePrincipalTerms (o : Ordinal) : List Ordinal :=
  if o = 0 then []
  else omega0 ^ log omega0 o :: additivePrincipalTerms (o - omega0 ^ log omega0 o)
termination_by o
decreasing_by exact sub_omega0_opow_log_lt (by assumption)

@[simp]
theorem additivePrincipalTerms_zero : additivePrincipalTerms 0 = [] := by
  rw [additivePrincipalTerms]
  simp

theorem additivePrincipalTerms_of_ne_zero {o : Ordinal} (ho : o ≠ 0) :
    additivePrincipalTerms o =
      omega0 ^ log omega0 o :: additivePrincipalTerms (o - omega0 ^ log omega0 o) := by
  rw [additivePrincipalTerms]
  simp only [if_neg ho]

/-- A finite ordinary sum of ordinals below a positive additive-principal ordinal remains below
that ordinal. -/
theorem IsAdditivelyPrincipal.list_sum_lt {o : Ordinal} (ho : IsAdditivelyPrincipal o)
    {l : List Ordinal} (hl : ∀ a ∈ l, a < o) : l.sum < o := by
  have hp := (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp ho).2
  induction l with
  | nil => simpa using (ho.ne_zero.bot_lt)
  | cons a l ih =>
      rw [List.sum_cons]
      apply hp (hl a (by simp))
      exact ih fun b hb ↦ hl b (by simp [hb])

/-- The ordinary ordinal sum of the uncompressed Cantor terms is the original ordinal. -/
theorem additivePrincipalTerms_sum (o : Ordinal) : o.additivePrincipalTerms.sum = o := by
  induction o using additivePrincipalTerms.induct with
  | case1 => simp
  | case2 o ho ih =>
      rw [additivePrincipalTerms_of_ne_zero ho, List.sum_cons, ih]
      exact Ordinal.add_sub_cancel_of_le (opow_log_le_self omega0 ho)

/-- Every term in the uncompressed Cantor normal form is LM24 additive principal. -/
theorem isAdditivelyPrincipal_of_mem_additivePrincipalTerms {o a : Ordinal}
    (ha : a ∈ o.additivePrincipalTerms) : IsAdditivelyPrincipal a := by
  induction o using additivePrincipalTerms.induct with
  | case1 => simp at ha
  | case2 o ho ih =>
      rw [additivePrincipalTerms_of_ne_zero ho] at ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact isAdditivelyPrincipal_omega0_opow _
      · exact ih ha

/-- The uncompressed Cantor terms occur in nonincreasing order. -/
theorem additivePrincipalTerms_sortedGE (o : Ordinal) :
    o.additivePrincipalTerms.SortedGE := by
  induction o using additivePrincipalTerms.induct with
  | case1 => simp [List.sortedGE_iff_pairwise]
  | case2 o ho ih =>
      rw [additivePrincipalTerms_of_ne_zero ho]
      rw [List.sortedGE_iff_pairwise] at ih ⊢
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro a ha
      obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
      apply opow_le_opow_right omega0_pos
      apply le_log_of_opow_le one_lt_omega0
      calc
        omega0 ^ e ≤ (o - omega0 ^ log omega0 o).additivePrincipalTerms.sum :=
          List.le_sum_of_mem ha
        _ = o - omega0 ^ log omega0 o := additivePrincipalTerms_sum _
        _ ≤ o := sub_le_self _ _

/-- A sorted ordinary sum of positive powers of `ω` agrees with the corresponding Hessenberg
sum in `NatOrdinal`. -/
theorem natOrdinal_of_sum_eq_sum_map_of_sorted {l : List Ordinal}
    (hprincipal : ∀ a ∈ l, IsAdditivelyPrincipal a)
    (hsorted : l.SortedGE) :
    NatOrdinal.of l.sum = (l.map NatOrdinal.of).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have haPrincipal := hprincipal a (by simp)
      obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp haPrincipal
      have hpairwise := List.sortedGE_iff_pairwise.mp hsorted
      have htailSorted : l.SortedGE :=
        List.sortedGE_iff_pairwise.mpr (List.pairwise_cons.mp hpairwise).2
      have htailPrincipal : ∀ b ∈ l, IsAdditivelyPrincipal b :=
        fun b hb ↦ hprincipal b (by simp [hb])
      have htailBound : l.sum < omega0 ^ (e + 1) := by
        apply (isAdditivelyPrincipal_omega0_opow _).list_sum_lt
        intro b hb
        have hble : b ≤ omega0 ^ e := (List.pairwise_cons.mp hpairwise).1 b hb
        exact hble.trans_lt <|
          (opow_lt_opow_iff_right one_lt_omega0).mpr (Order.lt_succ e)
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        ← ih htailPrincipal htailSorted, NatOrdinal.of_omega0_opow]
      symm
      apply NatOrdinal.wpow_add_of_lt
      rw [NatOrdinal.wpow_def, NatOrdinal.val_add_one, NatOrdinal.val_of]
      exact NatOrdinal.of.lt_iff_lt.mpr htailBound

/-- The uncompressed Cantor terms are the unique nonincreasing finite list of positive additive
principal ordinals whose ordinary ordinal sum is `o`. -/
theorem additivePrincipalTerms_unique {o : Ordinal} {l : List Ordinal}
    (hsum : l.sum = o) (hprincipal : ∀ a ∈ l, IsAdditivelyPrincipal a)
    (hsorted : l.SortedGE) : l = o.additivePrincipalTerms := by
  have canonicalSum := additivePrincipalTerms_sum o
  have canonicalPrincipal : ∀ a ∈ o.additivePrincipalTerms, IsAdditivelyPrincipal a :=
    fun _ ha ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
  have canonicalSorted := additivePrincipalTerms_sortedGE o
  suffices hunique : ∀ {l m : List Ordinal}, l.sum = m.sum →
      (∀ a ∈ l, IsAdditivelyPrincipal a) → l.SortedGE →
      (∀ a ∈ m, IsAdditivelyPrincipal a) → m.SortedGE → l = m by
    exact hunique (hsum.trans canonicalSum.symm) hprincipal hsorted canonicalPrincipal
      canonicalSorted
  intro l
  induction l with
  | nil =>
      intro m hsum _ _ hmPrincipal _
      cases m with
      | nil => rfl
      | cons b bs =>
          have hbpos : 0 < b := (hmPrincipal b (by simp)).ne_zero.bot_lt
          have hble : b ≤ (b :: bs).sum := List.le_sum_of_mem (by simp)
          rw [← hsum] at hble
          have : b ≤ 0 := by simpa only [List.sum_nil] using hble
          exact (not_lt_of_ge this hbpos).elim
  | cons a as ih =>
      intro m hsum hlPrincipal hlSorted hmPrincipal hmSorted
      cases m with
      | nil =>
          have hapos : 0 < a := (hlPrincipal a (by simp)).ne_zero.bot_lt
          have hale : a ≤ (a :: as).sum := List.le_sum_of_mem (by simp)
          rw [hsum] at hale
          have : a ≤ 0 := by simpa only [List.sum_nil] using hale
          exact (not_lt_of_ge this hapos).elim
      | cons b bs =>
          have hlPairwise : (a :: as).Pairwise (· ≥ ·) :=
            List.sortedGE_iff_pairwise.mp hlSorted
          have hmPairwise : (b :: bs).Pairwise (· ≥ ·) :=
            List.sortedGE_iff_pairwise.mp hmSorted
          have hal : ∀ x ∈ as, x ≤ a := (List.pairwise_cons.mp hlPairwise).1
          have hbl : ∀ x ∈ bs, x ≤ b := (List.pairwise_cons.mp hmPairwise).1
          have hab : a = b := by
            apply le_antisymm
            · apply le_of_not_gt
              intro hba
              have hlt : (b :: bs).sum < a :=
                (hlPrincipal a (by simp)).list_sum_lt (by
                  intro x hx
                  simp only [List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact hba
                  · exact (hbl x hx).trans_lt hba)
              have hale : a ≤ (a :: as).sum := List.le_sum_of_mem (by simp)
              exact (not_lt_of_ge (hale.trans_eq hsum)) hlt
            · apply le_of_not_gt
              intro hab
              have hlt : (a :: as).sum < b :=
                (hmPrincipal b (by simp)).list_sum_lt (by
                  intro x hx
                  simp only [List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact hab
                  · exact (hal x hx).trans_lt hab)
              have hble : b ≤ (b :: bs).sum := List.le_sum_of_mem (by simp)
              exact (not_lt_of_ge (hble.trans_eq hsum.symm)) hlt
          subst b
          congr 1
          apply ih
          · have htail : a + as.sum = a + bs.sum := by
              simpa only [List.sum_cons] using hsum
            exact add_left_cancel htail
          · exact fun x hx ↦ hlPrincipal x (by simp [hx])
          · exact List.sortedGE_iff_pairwise.mpr (List.pairwise_cons.mp hlPairwise).2
          · exact fun x hx ↦ hmPrincipal x (by simp [hx])
          · exact List.sortedGE_iff_pairwise.mpr (List.pairwise_cons.mp hmPairwise).2

/-- If every uncompressed Cantor term of `u` is at least the additive-principal ordinal `w`, then
appending `w` does not reorder the terms, so the ordinary and Hessenberg sums agree. -/
theorem natOrdinal_of_add_eq_add_of_forall_le {u w : Ordinal}
    (hw : IsAdditivelyPrincipal w)
    (hle : ∀ a ∈ u.additivePrincipalTerms, w ≤ a) :
    NatOrdinal.of (u + w) = NatOrdinal.of u + NatOrdinal.of w := by
  set l := u.additivePrincipalTerms with hldef
  have hlprincipal : ∀ a ∈ l, IsAdditivelyPrincipal a := fun a ha ↦
    isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
  have hlsorted : l.SortedGE := additivePrincipalTerms_sortedGE u
  have hallprincipal : ∀ a ∈ l ++ [w], IsAdditivelyPrincipal a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hlprincipal a ha
    · rw [List.mem_singleton] at ha
      exact ha ▸ hw
  have hsorted : (l ++ [w]).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp hlsorted, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    exact hb ▸ hle a ha
  have hsum : (l ++ [w]).sum = u + w := by
    rw [List.sum_append, List.sum_singleton, hldef, additivePrincipalTerms_sum]
  have h1 := natOrdinal_of_sum_eq_sum_map_of_sorted hallprincipal hsorted
  have h2 := natOrdinal_of_sum_eq_sum_map_of_sorted hlprincipal hlsorted
  rw [hsum] at h1
  rw [h1, List.map_append, List.sum_append, ← h2, hldef, additivePrincipalTerms_sum]
  simp


/-- The uncompressed Cantor terms of a Hessenberg sum of additive-principal ordinals are exactly
the summands. -/
theorem mem_of_mem_additivePrincipalTerms_natSum {L : List Ordinal}
    (hL : ∀ a ∈ L, IsAdditivelyPrincipal a) {a : Ordinal}
    (ha : a ∈ (((L.map NatOrdinal.of).sum).val).additivePrincipalTerms) : a ∈ L := by
  classical
  set L' := L.mergeSort (fun x y ↦ decide (y ≤ x)) with hL'def
  have hperm : L'.Perm L := List.mergeSort_perm L _
  have hsorted : L'.SortedGE := List.sortedGE_mergeSort
  have hL'principal : ∀ x ∈ L', IsAdditivelyPrincipal x :=
    fun x hx ↦ hL x (hperm.mem_iff.mp hx)
  have hmapsum : (L'.map NatOrdinal.of).sum = (L.map NatOrdinal.of).sum :=
    (hperm.map NatOrdinal.of).sum_eq
  have hsum : NatOrdinal.of L'.sum = (L.map NatOrdinal.of).sum := by
    rw [natOrdinal_of_sum_eq_sum_map_of_sorted hL'principal hsorted, hmapsum]
  have hval : L'.sum = ((L.map NatOrdinal.of).sum).val := by
    rw [← hsum, NatOrdinal.val_of]
  have huniq := additivePrincipalTerms_unique (o := L'.sum) rfl hL'principal hsorted
  rw [hval] at huniq
  exact hperm.mem_iff.mp (huniq ▸ ha)


/-- Hessenberg and ordinary multiplication by `ω ^ w` agree on a power of `ω` whose exponent is a
Hessenberg sum of additive-principal ordinals all at least `w`. The hypothesis cannot be weakened
to `ω ^ w ≤ ω ^ x`: for `x = ω + 1` and `w = ω` the two products are `ω ^ (ω * 2)` and
`ω ^ (ω * 2 + 1)`. -/
theorem natOrdinal_of_mul_wpow_eq_mul {w : Ordinal} {M : List Ordinal}
    (hw : IsAdditivelyPrincipal w)
    (hM : ∀ u ∈ M, IsAdditivelyPrincipal u ∧ w ≤ u) :
    NatOrdinal.of (omega0 ^ ((M.map NatOrdinal.of).sum).val * omega0 ^ w) =
      NatOrdinal.of (omega0 ^ ((M.map NatOrdinal.of).sum).val) *
        NatOrdinal.of (omega0 ^ w) := by
  set x := ((M.map NatOrdinal.of).sum).val with hxdef
  have hterms : ∀ a ∈ x.additivePrincipalTerms, w ≤ a := by
    intro a ha
    exact (hM a (mem_of_mem_additivePrincipalTerms_natSum (fun u hu ↦ (hM u hu).1) ha)).2
  rw [← opow_add, NatOrdinal.of_omega0_opow, NatOrdinal.of_omega0_opow,
    NatOrdinal.of_omega0_opow, natOrdinal_of_add_eq_add_of_forall_le hw hterms,
    NatOrdinal.wpow_add]

theorem IsAdditivelyPrincipal.opow_log_self {o : Ordinal} (ho : IsAdditivelyPrincipal o) :
    omega0 ^ log omega0 o = o := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  rw [log_opow one_lt_omega0]

theorem natOrdinal_of_eq_wpow_log {o : Ordinal} (ho : IsAdditivelyPrincipal o) :
    NatOrdinal.of o = ω^ (NatOrdinal.of (log omega0 o)) := by
  conv_lhs => rw [← ho.opow_log_self]
  rw [NatOrdinal.of_omega0_opow]

theorem natOrdinal_of_log_eq_sum_terms (o : Ordinal) :
    NatOrdinal.of (log omega0 o) =
      (((log omega0 o).additivePrincipalTerms).map NatOrdinal.of).sum := by
  conv_lhs => rw [← additivePrincipalTerms_sum (log omega0 o)]
  exact natOrdinal_of_sum_eq_sum_map_of_sorted
    (fun _ ha ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha)
    (additivePrincipalTerms_sortedGE _)

/-- The uncompressed Cantor terms of the logarithm of a Hessenberg product come from the two
factors. -/
theorem mem_additivePrincipalTerms_log_natMul {o₁ o₂ : Ordinal}
    (h₁ : IsAdditivelyPrincipal o₁) (h₂ : IsAdditivelyPrincipal o₂) {t : Ordinal}
    (ht : t ∈
      (log omega0 ((NatOrdinal.of o₁ * NatOrdinal.of o₂).val)).additivePrincipalTerms) :
    t ∈ (log omega0 o₁).additivePrincipalTerms ∨
      t ∈ (log omega0 o₂).additivePrincipalTerms := by
  have hprod : NatOrdinal.of o₁ * NatOrdinal.of o₂ =
      ω^ (NatOrdinal.of (log omega0 o₁) + NatOrdinal.of (log omega0 o₂)) := by
    rw [NatOrdinal.wpow_add, ← natOrdinal_of_eq_wpow_log h₁, ← natOrdinal_of_eq_wpow_log h₂]
  have hlog : log omega0 ((NatOrdinal.of o₁ * NatOrdinal.of o₂).val) =
      (NatOrdinal.of (log omega0 o₁) + NatOrdinal.of (log omega0 o₂)).val := by
    rw [hprod, NatOrdinal.val_wpow, log_opow one_lt_omega0]
  set M := (log omega0 o₁).additivePrincipalTerms ++ (log omega0 o₂).additivePrincipalTerms
    with hMdef
  have hM : ∀ u ∈ M, IsAdditivelyPrincipal u := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu <;>
      exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms hu
  have hsum : (M.map NatOrdinal.of).sum =
      NatOrdinal.of (log omega0 o₁) + NatOrdinal.of (log omega0 o₂) := by
    rw [hMdef, List.map_append, List.sum_append, ← natOrdinal_of_log_eq_sum_terms,
      ← natOrdinal_of_log_eq_sum_terms]
  rw [hlog, ← hsum] at ht
  exact List.mem_append.mp (mem_of_mem_additivePrincipalTerms_natSum hM ht)


theorem additivePrincipalTerms_of_isAdditivelyPrincipal {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) : o.additivePrincipalTerms = [o] := by
  rw [additivePrincipalTerms_of_ne_zero ho.ne_zero, ho.opow_log_self, Ordinal.sub_self,
    additivePrincipalTerms_zero]

/-- Ordinary and Hessenberg multiplication by `ω ^ w` agree on an additive-principal ordinal each
of whose canonical multiplicative factors is at least `ω ^ w`. -/
theorem natOrdinal_of_mul_wpow_eq_mul_of_log_terms {w o : Ordinal}
    (hw : IsAdditivelyPrincipal w) (ho : IsAdditivelyPrincipal o)
    (hterms : ∀ t ∈ (log omega0 o).additivePrincipalTerms, w ≤ t) :
    NatOrdinal.of (o * omega0 ^ w) = NatOrdinal.of o * NatOrdinal.of (omega0 ^ w) := by
  have h1 : o * omega0 ^ w = omega0 ^ (log omega0 o + w) := by
    rw [opow_add, ho.opow_log_self]
  rw [h1, NatOrdinal.of_omega0_opow, natOrdinal_of_add_eq_add_of_forall_le hw hterms,
    NatOrdinal.wpow_add, ← natOrdinal_of_eq_wpow_log ho, ← NatOrdinal.of_omega0_opow]

end Ordinal
