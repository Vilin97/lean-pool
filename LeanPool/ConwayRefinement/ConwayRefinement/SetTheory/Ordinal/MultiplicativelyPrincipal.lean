/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal

import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Tactic.NormNum

/-!
# Multiplicatively principal ordinal factors

Berarducci, Definition 3.6 calls a positive ordinal multiplicatively principal when the ordinals
strictly below it are closed under ordinary ordinal multiplication. Under that exact definition,
the finite ordinal `2` is multiplicatively principal. Thus Berarducci, Fact 3.8 omits the case `2`
when it lists only `1` and ordinals of the form `ω ^ (ω ^ e)`. This module records the exact
classification, including `2`, and separately names the infinite multiplicatively principal
ordinals used as factors in Definition 6.4.

For a positive additive-principal ordinal above one, its exponent has a nonempty uncompressed
Cantor normal form. Exponentiating those Cantor terms by `ω` gives the unique nonincreasing list
of multiplicatively principal factors greater than one. The ordinary ordinal product of the list
is the original ordinal. The corresponding Hessenberg product in `NatOrdinal` has the same value,
as asserted in Berarducci, Remark 6.5.

The subtype `Ordinal.AdditivePrincipalAboveOne` is the exact domain of Berarducci's principal and
residual factor operations. Consequently neither operation uses an arbitrary value outside its
mathematical domain. The residual factor is the product of all but the final factor, so it is one
when the factor list is a singleton.

Mathlib supplies the ordinary principal-ordinal classification and ordinal logarithm.
CombinatorialGames supplies Hessenberg arithmetic on `NatOrdinal`. Neither dependency supplies the
finite factor list or the principal and residual projections.
-/

universe u

open scoped NatOrdinal

public noncomputable section

namespace Ordinal

/-- Berarducci's positive convention for multiplicatively principal ordinals. -/
def IsMultiplicativelyPrincipal (o : Ordinal) : Prop :=
  0 < o ∧ IsPrincipal (· * ·) o

/-- The exact relationship with Mathlib's convention, which also includes zero. -/
theorem isMultiplicativelyPrincipal_iff_pos_and_isPrincipal_mul {o : Ordinal} :
    IsMultiplicativelyPrincipal o ↔ 0 < o ∧ IsPrincipal (· * ·) o :=
  Iff.rfl

/-- One is multiplicatively principal in Berarducci's convention. -/
theorem isMultiplicativelyPrincipal_one :
    IsMultiplicativelyPrincipal 1 :=
  ⟨zero_lt_one, isPrincipal_mul_one⟩

/-- Two is multiplicatively principal under the predicate printed in Berarducci, Definition 3.6. -/
theorem isMultiplicativelyPrincipal_two :
    IsMultiplicativelyPrincipal 2 :=
  ⟨by norm_num, isPrincipal_mul_two⟩

/-- Every ordinal of the infinite shape in Berarducci, Fact 3.8 is multiplicatively principal. -/
theorem isMultiplicativelyPrincipal_omega0_opow_opow (e : Ordinal) :
    IsMultiplicativelyPrincipal (omega0 ^ omega0 ^ e) :=
  ⟨opow_pos _ omega0_pos, isPrincipal_mul_omega0_opow_opow e⟩

/-- Corrected classification of Berarducci's multiplicatively principal ordinals. The additional
case `2` is forced by the printed predicate. -/
theorem isMultiplicativelyPrincipal_iff_one_or_two_or_omega0_opow_opow
    {o : Ordinal} :
    IsMultiplicativelyPrincipal o ↔
      o = 1 ∨ o = 2 ∨ ∃ e : Ordinal, o = omega0 ^ omega0 ^ e := by
  rw [IsMultiplicativelyPrincipal, isPrincipal_mul_iff_le_two_or_omega0_opow_opow]
  constructor
  · rintro ⟨ho, hsmall | ⟨e, he⟩⟩
    · obtain rfl | rfl | rfl := Order.le_two_iff.mp hsmall
      · exact (lt_irrefl 0 ho).elim
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨e, he.symm⟩)
  · rintro (rfl | rfl | ⟨e, rfl⟩)
    · exact ⟨zero_lt_one, Or.inl (by norm_num)⟩
    · exact ⟨by norm_num, Or.inl le_rfl⟩
    · exact ⟨opow_pos _ omega0_pos, Or.inr ⟨e, rfl⟩⟩

/-- An infinite multiplicatively principal ordinal, namely an ordinal of the form
`ω ^ (ω ^ e)`. These are the factors occurring in Berarducci, Definition 6.4. -/
def IsInfiniteMultiplicativelyPrincipal (o : Ordinal) : Prop :=
  ∃ e : Ordinal, o = omega0 ^ omega0 ^ e

/-- Characterization of infinite multiplicatively principal ordinals by their defining shape. -/
theorem isInfiniteMultiplicativelyPrincipal_iff {o : Ordinal} :
    IsInfiniteMultiplicativelyPrincipal o ↔ ∃ e : Ordinal, o = omega0 ^ omega0 ^ e :=
  (Iff.rfl)

/-- Every ordinal of the defining infinite shape is infinite multiplicatively principal. -/
theorem isInfiniteMultiplicativelyPrincipal_omega0_opow_opow (e : Ordinal) :
    IsInfiniteMultiplicativelyPrincipal (omega0 ^ omega0 ^ e) :=
  ⟨e, rfl⟩

/-- Every infinite multiplicatively principal ordinal is a nonzero limit ordinal. -/
theorem IsInfiniteMultiplicativelyPrincipal.isSuccLimit {o : Ordinal}
    (ho : IsInfiniteMultiplicativelyPrincipal o) :
    Order.IsSuccLimit o := by
  obtain ⟨e, rfl⟩ := ho
  exact isSuccLimit_opow_left isSuccLimit_omega0 (opow_ne_zero e omega0_ne_zero)

/-- Every infinite multiplicatively principal ordinal is additively principal. -/
theorem IsInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal {o : Ordinal}
    (ho : IsInfiniteMultiplicativelyPrincipal o) :
    IsAdditivelyPrincipal o := by
  obtain ⟨e, rfl⟩ := ho
  exact isAdditivelyPrincipal_omega0_opow (omega0 ^ e)

/-- Infinite multiplicative principality is multiplicative principality together with exclusion
of the exceptional values one and two. -/
theorem isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal
    {o : Ordinal} :
    IsInfiniteMultiplicativelyPrincipal o ↔
      2 < o ∧ IsMultiplicativelyPrincipal o := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨?_, isMultiplicativelyPrincipal_omega0_opow_opow e⟩
    apply (natCast_lt_omega0 2).trans_le
    simpa [opow_one] using
      (opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr <|
        opow_ne_zero e omega0_ne_zero))
  · rintro ⟨htwo, hp⟩
    rcases isMultiplicativelyPrincipal_iff_one_or_two_or_omega0_opow_opow.mp hp with
      rfl | rfl | ⟨e, he⟩
    · exact (not_lt_of_ge (by norm_num) htwo).elim
    · exact (lt_irrefl 2 htwo).elim
    · exact ⟨e, he⟩

/-- The multiplicatively principal factors obtained from the uncompressed Cantor normal form of
the exponent of `o`. -/
noncomputable def multiplicativePrincipalFactors (o : Ordinal) : List Ordinal :=
  (additivePrincipalTerms (log omega0 o)).map (omega0 ^ ·)

private theorem prod_map_omega0_opow (l : List Ordinal) :
    (l.map (omega0 ^ ·)).prod = omega0 ^ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, opow_add]

/-- The ordinary product of the canonical factors of an additive-principal ordinal is the
original ordinal. -/
theorem multiplicativePrincipalFactors_prod {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) :
    o.multiplicativePrincipalFactors.prod = o := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  rw [multiplicativePrincipalFactors, log_opow one_lt_omega0,
    prod_map_omega0_opow, additivePrincipalTerms_sum]

/-- An additive-principal ordinal above one has at least one canonical multiplicative factor. -/
theorem multiplicativePrincipalFactors_ne_nil {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) (hone : 1 < o) :
    o.multiplicativePrincipalFactors ≠ [] := by
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp ho
  have he : e ≠ 0 := by
    intro he
    subst e
    simp at hone
  rw [multiplicativePrincipalFactors, log_opow one_lt_omega0]
  intro hnil
  have hterms : additivePrincipalTerms e = [] := List.map_eq_nil_iff.mp hnil
  have hsum := additivePrincipalTerms_sum e
  rw [hterms] at hsum
  exact he hsum.symm

/-- The canonical multiplicative factors occur in nonincreasing order. -/
theorem multiplicativePrincipalFactors_sortedGE (o : Ordinal) :
    o.multiplicativePrincipalFactors.SortedGE := by
  rw [multiplicativePrincipalFactors, List.sortedGE_iff_pairwise, List.pairwise_map]
  have hsorted := additivePrincipalTerms_sortedGE (log omega0 o)
  rw [List.sortedGE_iff_pairwise] at hsorted
  exact hsorted.imp fun hab ↦ opow_le_opow_right omega0_pos hab

/-- Every canonical factor is an infinite multiplicatively principal ordinal. -/
theorem isInfiniteMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors
    {o f : Ordinal} (hf : f ∈ o.multiplicativePrincipalFactors) :
    IsInfiniteMultiplicativelyPrincipal f := by
  rw [multiplicativePrincipalFactors, List.mem_map] at hf
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨a, rfl⟩ :=
    isAdditivelyPrincipal_iff.mp
      (isAdditivelyPrincipal_of_mem_additivePrincipalTerms he)
  exact ⟨a, rfl⟩

/-- Every canonical factor is multiplicatively principal under the exact source predicate. -/
theorem isMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors
    {o f : Ordinal} (hf : f ∈ o.multiplicativePrincipalFactors) :
    IsMultiplicativelyPrincipal f :=
  (isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
    (isInfiniteMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors hf)).2

/-- Every canonical factor is strictly greater than one. -/
theorem one_lt_of_mem_multiplicativePrincipalFactors
    {o f : Ordinal} (hf : f ∈ o.multiplicativePrincipalFactors) :
    1 < f :=
  (show (1 : Ordinal) < 2 by norm_num).trans <|
    (isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
      (isInfiniteMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors hf)).1

private theorem multiplicativePrincipalFactors_unique_of_infinite
    {o : Ordinal} {l : List Ordinal}
    (hsum : l.prod = o)
    (hprincipal : ∀ f ∈ l, IsInfiniteMultiplicativelyPrincipal f)
    (hsorted : l.SortedGE) :
    l = o.multiplicativePrincipalFactors := by
  let exponents := l.map (log omega0)
  have hprincipalExponents : ∀ e ∈ exponents, IsAdditivelyPrincipal e := by
    intro e he
    change e ∈ l.map (log omega0) at he
    rw [List.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    obtain ⟨a, rfl⟩ := hprincipal f hf
    rw [log_opow one_lt_omega0]
    exact isAdditivelyPrincipal_omega0_opow a
  have hsortedExponents : exponents.SortedGE := by
    change (l.map (log omega0)).SortedGE
    rw [List.sortedGE_iff_pairwise, List.pairwise_map]
    have hpairwise := List.sortedGE_iff_pairwise.mp hsorted
    exact hpairwise.imp fun hab ↦ log_mono_right omega0 hab
  have hprod : l.prod = omega0 ^ exponents.sum := by
    have hreconstruct : l = l.map (fun f ↦ omega0 ^ log omega0 f) := by
      have hmap : l.map id = l.map (fun f ↦ omega0 ^ log omega0 f) := by
        apply List.map_congr_left
        intro f hf
        obtain ⟨a, rfl⟩ := hprincipal f hf
        simp [log_opow one_lt_omega0]
      simpa using hmap
    calc
      l.prod = (l.map fun f ↦ omega0 ^ log omega0 f).prod :=
        congrArg List.prod hreconstruct
      _ = omega0 ^ (l.map (log omega0)).sum := by
        simpa [Function.comp_def] using
          prod_map_omega0_opow (l.map (log omega0))
      _ = omega0 ^ exponents.sum := rfl
  have hoPrincipal : IsAdditivelyPrincipal o :=
    isAdditivelyPrincipal_iff.mpr ⟨exponents.sum, hsum.symm.trans hprod⟩
  obtain ⟨e, rfl⟩ := isAdditivelyPrincipal_iff.mp hoPrincipal
  have hexponents : exponents = additivePrincipalTerms e := by
    apply additivePrincipalTerms_unique
    · apply (opow_right_inj one_lt_omega0).mp
      calc
        omega0 ^ exponents.sum = l.prod := hprod.symm
        _ = omega0 ^ e := hsum
    · exact hprincipalExponents
    · exact hsortedExponents
  rw [multiplicativePrincipalFactors, log_opow one_lt_omega0, ← hexponents]
  change l = (l.map (log omega0)).map (omega0 ^ ·)
  rw [List.map_map]
  have hmap : l.map id = l.map ((omega0 ^ ·) ∘ log omega0) := by
    apply List.map_congr_left
    intro f hf
    obtain ⟨a, rfl⟩ := hprincipal f hf
    simp [Function.comp_apply, log_opow one_lt_omega0]
  simpa using hmap

/-- The canonical factor list is the unique nonincreasing list of source-multiplicatively-principal
ordinals greater than one with the prescribed additive-principal product. -/
theorem multiplicativePrincipalFactors_unique {o : Ordinal} {l : List Ordinal}
    (ho : IsAdditivelyPrincipal o)
    (hsum : l.prod = o)
    (hprincipal : ∀ f ∈ l, IsMultiplicativelyPrincipal f)
    (hone : ∀ f ∈ l, 1 < f)
    (hsorted : l.SortedGE) :
    l = o.multiplicativePrincipalFactors := by
  have hnoTwo : (2 : Ordinal) ∉ l := by
    intro htwo
    have hne : l ≠ [] := List.ne_nil_of_mem htwo
    let last := l.getLast hne
    have hlastMem : last ∈ l := List.getLast_mem hne
    have hpairwise := List.sortedGE_iff_pairwise.mp hsorted
    have hlastLe : last ≤ 2 := hpairwise.rel_getLast htwo
    have htwoLe : (2 : Ordinal) ≤ last := by
      simpa [one_add_one_eq_two] using
        (Order.add_one_le_iff.mpr (hone last hlastMem))
    have hlast : last = 2 := le_antisymm hlastLe htwoLe
    let front := l.dropLast
    have hfrontPos : 0 < front.prod := by
      have hprodPos : ∀ (m : List Ordinal),
          (∀ f ∈ m, 0 < f) → 0 < m.prod := by
        intro m hm
        induction m with
        | nil => exact zero_lt_one
        | cons f m ih =>
            rw [List.prod_cons]
            exact mul_pos (hm f (by simp))
              (ih fun g hg ↦ hm g (by simp [hg]))
      apply hprodPos
      intro f hf
      exact zero_lt_one.trans (hone f (List.mem_of_mem_dropLast hf))
    have hsplit : front.prod * last = l.prod := by
      calc
        front.prod * last = (front ++ [last]).prod := by simp
        _ = l.prod := by
          congr 1
          exact List.dropLast_append_getLast hne
    have hfrontMulTwo : front.prod * 2 = o := by
      rw [← hlast, hsplit, hsum]
    have hfrontLt : front.prod < o := by
      rw [← hfrontMulTwo]
      simpa using mul_lt_mul_of_pos_left (show (1 : Ordinal) < 2 by norm_num)
        hfrontPos
    have hclosed :=
      (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp ho).2 hfrontLt hfrontLt
    change front.prod + front.prod < o at hclosed
    rw [← Ordinal.mul_two, hfrontMulTwo] at hclosed
    exact lt_irrefl o hclosed
  apply multiplicativePrincipalFactors_unique_of_infinite hsum
  · intro f hf
    rcases isMultiplicativelyPrincipal_iff_one_or_two_or_omega0_opow_opow.mp
      (hprincipal f hf) with rfl | rfl | ⟨e, he⟩
    · exact (lt_irrefl 1 (hone 1 hf)).elim
    · exact (hnoTwo hf).elim
    · exact ⟨e, he⟩
  · exact hsorted

/-- An infinite multiplicatively principal ordinal has itself as its sole canonical factor. -/
theorem multiplicativePrincipalFactors_eq_singleton
    {o : Ordinal} (ho : IsInfiniteMultiplicativelyPrincipal o) :
    o.multiplicativePrincipalFactors = [o] := by
  symm
  apply multiplicativePrincipalFactors_unique_of_infinite (o := o)
  · simp
  · intro f hf
    rw [List.mem_singleton] at hf
    subst f
    exact ho
  · simp [List.sortedGE_iff_pairwise]

private theorem naturalProd_map_omega0_opow (l : List Ordinal) :
    (l.map (fun e ↦ NatOrdinal.of (omega0 ^ e))).prod =
      ω^ (l.map NatOrdinal.of).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons,
        NatOrdinal.of_omega0_opow, NatOrdinal.wpow_add]

private theorem naturalProd_factors_eq_of_ordinaryProd {l : List Ordinal}
    (hprincipal : ∀ a ∈ l, IsAdditivelyPrincipal a)
    (hsorted : l.SortedGE) :
    (l.map (fun e ↦ NatOrdinal.of (omega0 ^ e))).prod =
      NatOrdinal.of (l.map (omega0 ^ ·)).prod := by
  rw [naturalProd_map_omega0_opow, prod_map_omega0_opow,
    NatOrdinal.of_omega0_opow,
    natOrdinal_of_sum_eq_sum_map_of_sorted hprincipal hsorted]

private theorem multiplicativePrincipalFactors_naturalProd_eq_of_prod (o : Ordinal) :
    (o.multiplicativePrincipalFactors.map NatOrdinal.of).prod =
      NatOrdinal.of o.multiplicativePrincipalFactors.prod := by
  rw [multiplicativePrincipalFactors, List.map_map]
  apply naturalProd_factors_eq_of_ordinaryProd
  · exact fun _ ha ↦ isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
  · exact additivePrincipalTerms_sortedGE _

/-- The Hessenberg product of the canonical factors agrees with their ordinary product and equals
the original additive-principal ordinal. This is the product agreement used in Berarducci,
Remark 6.5. -/
theorem multiplicativePrincipalFactors_naturalProd {o : Ordinal}
    (ho : IsAdditivelyPrincipal o) :
    (o.multiplicativePrincipalFactors.map NatOrdinal.of).prod = NatOrdinal.of o := by
  rw [multiplicativePrincipalFactors_naturalProd_eq_of_prod,
    multiplicativePrincipalFactors_prod ho]

/-- The exact domain on which Berarducci's principal and residual factors are defined. -/
abbrev AdditivePrincipalAboveOne :=
  {o : Ordinal // IsAdditivelyPrincipal o ∧ 1 < o}

namespace AdditivePrincipalAboveOne

private theorem sortedGE_dropLast {l : List Ordinal} (hl : l.SortedGE) :
    l.dropLast.SortedGE := by
  rw [List.sortedGE_iff_pairwise] at hl ⊢
  induction l with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          rw [List.dropLast_cons_of_ne_nil (by simp), List.pairwise_cons]
          exact ⟨fun c hc ↦ (List.pairwise_cons.mp hl).1 c
              (List.mem_of_mem_dropLast hc),
            ih (List.pairwise_cons.mp hl).2⟩

/-- The final, hence least, factor in the canonical multiplicative factor list. -/
noncomputable def principalFactor (o : AdditivePrincipalAboveOne) : Ordinal :=
  o.1.multiplicativePrincipalFactors.getLast
    (multiplicativePrincipalFactors_ne_nil o.2.1 o.2.2)

/-- The ordinary product of all canonical multiplicative factors except the final one. -/
noncomputable def residualFactor (o : AdditivePrincipalAboveOne) : Ordinal :=
  o.1.multiplicativePrincipalFactors.dropLast.prod

/-- The principal factor is the final element of the nonempty canonical factor list. -/
theorem principalFactor_eq_getLast (o : AdditivePrincipalAboveOne) :
    o.principalFactor = o.1.multiplicativePrincipalFactors.getLast
      (multiplicativePrincipalFactors_ne_nil o.2.1 o.2.2) :=
  (rfl)

/-- The residual factor is the ordinary product of the canonical factor list without its final
element. -/
theorem residualFactor_eq_dropLast_prod (o : AdditivePrincipalAboveOne) :
    o.residualFactor = o.1.multiplicativePrincipalFactors.dropLast.prod :=
  (rfl)

/-- The ordinary product of the residual and principal factors recovers the original ordinal. -/
theorem residualFactor_mul_principalFactor (o : AdditivePrincipalAboveOne) :
    o.residualFactor * o.principalFactor = o.1 := by
  let hne := multiplicativePrincipalFactors_ne_nil o.2.1 o.2.2
  calc
    o.residualFactor * o.principalFactor =
        (o.1.multiplicativePrincipalFactors.dropLast ++
          [o.1.multiplicativePrincipalFactors.getLast hne]).prod := by
      simp [residualFactor, principalFactor]
    _ = o.1.multiplicativePrincipalFactors.prod := by
      rw [List.dropLast_append_getLast hne]
    _ = o.1 := multiplicativePrincipalFactors_prod o.2.1

/-- The principal factor belongs to the canonical factor list. -/
theorem principalFactor_mem_factors (o : AdditivePrincipalAboveOne) :
    o.principalFactor ∈ o.1.multiplicativePrincipalFactors := by
  rw [principalFactor]
  exact List.getLast_mem _

/-- The principal factor is an infinite multiplicatively principal ordinal. -/
theorem principalFactor_isInfiniteMultiplicativelyPrincipal
    (o : AdditivePrincipalAboveOne) :
    IsInfiniteMultiplicativelyPrincipal o.principalFactor :=
  isInfiniteMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors
    o.principalFactor_mem_factors

/-- The principal factor is multiplicatively principal under Berarducci's exact predicate. -/
theorem principalFactor_isMultiplicativelyPrincipal (o : AdditivePrincipalAboveOne) :
    IsMultiplicativelyPrincipal o.principalFactor :=
  isMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors
    o.principalFactor_mem_factors

/-- The principal factor is strictly greater than one. -/
theorem one_lt_principalFactor (o : AdditivePrincipalAboveOne) :
    1 < o.principalFactor :=
  one_lt_of_mem_multiplicativePrincipalFactors o.principalFactor_mem_factors

/-- The residual factor is positive additive principal; in particular, it may equal one. -/
theorem residualFactor_isAdditivelyPrincipal (o : AdditivePrincipalAboveOne) :
    IsAdditivelyPrincipal o.residualFactor := by
  apply isAdditivelyPrincipal_iff.mpr
  refine ⟨(additivePrincipalTerms (log omega0 o.1)).dropLast.sum, ?_⟩
  have hdrop :
      ((additivePrincipalTerms (log omega0 o.1)).map (omega0 ^ ·)).dropLast =
        (additivePrincipalTerms (log omega0 o.1)).dropLast.map (omega0 ^ ·) := by
    induction additivePrincipalTerms (log omega0 o.1) with
    | nil => rfl
    | cons a l ih => cases l <;> simp_all
  rw [residualFactor, multiplicativePrincipalFactors, hdrop, prod_map_omega0_opow]

/-- If the original ordinal is already infinite multiplicatively principal, its principal factor
is the ordinal itself. -/
theorem principalFactor_eq_self_of_isInfiniteMultiplicativelyPrincipal
    (o : AdditivePrincipalAboveOne)
    (ho : IsInfiniteMultiplicativelyPrincipal o.1) :
    o.principalFactor = o.1 := by
  rw [principalFactor]
  let hne := multiplicativePrincipalFactors_ne_nil o.2.1 o.2.2
  calc
    o.1.multiplicativePrincipalFactors.getLast hne =
        [o.1].getLast (by simp) :=
      List.getLast_congr _ _ (multiplicativePrincipalFactors_eq_singleton ho)
    _ = o.1 := rfl

/-- If the original ordinal is already infinite multiplicatively principal, its residual factor
is one, as stipulated in Berarducci, Definition 6.4. -/
theorem residualFactor_eq_one_of_isInfiniteMultiplicativelyPrincipal
    (o : AdditivePrincipalAboveOne)
    (ho : IsInfiniteMultiplicativelyPrincipal o.1) :
    o.residualFactor = 1 := by
  rw [residualFactor, multiplicativePrincipalFactors_eq_singleton ho]
  rfl

private theorem naturalProd_dropLastFactors_eq_residualFactor
    (o : AdditivePrincipalAboveOne) :
    (o.1.multiplicativePrincipalFactors.dropLast.map NatOrdinal.of).prod =
      NatOrdinal.of o.residualFactor := by
  let terms := additivePrincipalTerms (log omega0 o.1)
  have hdrop :
      (terms.map (omega0 ^ ·)).dropLast = terms.dropLast.map (omega0 ^ ·) := by
    induction terms with
    | nil => rfl
    | cons a l ih => cases l <;> simp_all
  rw [residualFactor, multiplicativePrincipalFactors, show
    additivePrincipalTerms (log omega0 o.1) = terms from rfl, hdrop, List.map_map]
  apply naturalProd_factors_eq_of_ordinaryProd
  · intro a ha
    exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms
      (List.mem_of_mem_dropLast ha)
  · exact sortedGE_dropLast (additivePrincipalTerms_sortedGE _)

/-- The Hessenberg product of the residual and principal factors also recovers the original
ordinal. -/
theorem naturalResidual_mul_naturalPrincipal (o : AdditivePrincipalAboveOne) :
    NatOrdinal.of o.residualFactor * NatOrdinal.of o.principalFactor =
      NatOrdinal.of o.1 := by
  let factors := o.1.multiplicativePrincipalFactors
  let hne := multiplicativePrincipalFactors_ne_nil o.2.1 o.2.2
  calc
    NatOrdinal.of o.residualFactor * NatOrdinal.of o.principalFactor =
        (factors.dropLast.map NatOrdinal.of).prod *
          NatOrdinal.of (factors.getLast hne) := by
      rw [naturalProd_dropLastFactors_eq_residualFactor, principalFactor]
    _ = (factors.dropLast.map NatOrdinal.of ++
          [NatOrdinal.of (factors.getLast hne)]).prod := by simp
    _ = (factors.map NatOrdinal.of).prod := by
      have hmap : factors.dropLast.map NatOrdinal.of ++
          [NatOrdinal.of (factors.getLast hne)] = factors.map NatOrdinal.of := by
        rw [← List.map_singleton, ← List.map_append,
          List.dropLast_append_getLast hne]
      rw [hmap]
    _ = NatOrdinal.of factors.prod :=
      multiplicativePrincipalFactors_naturalProd_eq_of_prod o.1
    _ = NatOrdinal.of o.1 := by rw [multiplicativePrincipalFactors_prod o.2.1]

/-- The principal factor is the least canonical factor. -/
theorem principalFactor_le_of_mem_factors (o : AdditivePrincipalAboveOne)
    {f : Ordinal} (hf : f ∈ o.1.multiplicativePrincipalFactors) :
    o.principalFactor ≤ f := by
  rw [principalFactor]
  have hpairwise := List.sortedGE_iff_pairwise.mp
    (multiplicativePrincipalFactors_sortedGE o.1)
  exact hpairwise.rel_getLast hf

/-- The canonical multiplicative factors are the powers of `ω` at the Cantor terms of the
logarithm. -/
theorem multiplicativePrincipalFactors_eq (o : AdditivePrincipalAboveOne) :
    o.1.multiplicativePrincipalFactors =
      (log omega0 o.1).additivePrincipalTerms.map (omega0 ^ ·) :=
  (rfl)

theorem log_principalFactor_le_of_mem_terms (o : AdditivePrincipalAboveOne)
    {t : Ordinal} (ht : t ∈ (log omega0 o.1).additivePrincipalTerms) :
    log omega0 o.principalFactor ≤ t := by
  have hmem : omega0 ^ t ∈ o.1.multiplicativePrincipalFactors := by
    rw [multiplicativePrincipalFactors_eq]
    exact List.mem_map_of_mem ht
  have hle := o.principalFactor_le_of_mem_factors hmem
  have hprin : IsAdditivelyPrincipal o.principalFactor :=
    o.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal
  rw [← hprin.opow_log_self] at hle
  exact (opow_le_opow_iff_right one_lt_omega0).mp hle

theorem log_principalFactor_mem_terms (o : AdditivePrincipalAboveOne) :
    log omega0 o.principalFactor ∈ (log omega0 o.1).additivePrincipalTerms := by
  have hmem := o.principalFactor_mem_factors
  rw [multiplicativePrincipalFactors_eq, List.mem_map] at hmem
  obtain ⟨t, ht, hteq⟩ := hmem
  rw [← hteq, log_opow one_lt_omega0]
  exact ht

theorem mem_terms_of_mem_terms_log_residualFactor (o : AdditivePrincipalAboveOne)
    {t : Ordinal} (ht : t ∈ (log omega0 o.residualFactor).additivePrincipalTerms) :
    t ∈ (log omega0 o.1).additivePrincipalTerms := by
  set L := (log omega0 o.1).additivePrincipalTerms with hLdef
  have hdrop : (L.map (omega0 ^ ·)).dropLast = L.dropLast.map (omega0 ^ ·) := by
    induction L with
    | nil => rfl
    | cons a l ih => cases l <;> simp_all
  have hres : o.residualFactor = omega0 ^ L.dropLast.sum := by
    rw [residualFactor_eq_dropLast_prod, multiplicativePrincipalFactors_eq, ← hLdef, hdrop,
      prod_map_omega0_opow]
  have hlog : log omega0 o.residualFactor = L.dropLast.sum := by
    rw [hres, log_opow one_lt_omega0]
  have hsub : L.dropLast.Sublist L := List.dropLast_sublist L
  have hsorted : L.dropLast.SortedGE :=
    List.sortedGE_iff_pairwise.mpr
      ((List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE _)).sublist hsub)
  have hprin : ∀ a ∈ L.dropLast, IsAdditivelyPrincipal a := fun a ha ↦
    isAdditivelyPrincipal_of_mem_additivePrincipalTerms (hsub.mem ha)
  have huniq := additivePrincipalTerms_unique (o := L.dropLast.sum) rfl hprin hsorted
  rw [hlog, ← huniq] at ht
  exact hsub.mem ht

/-- Berarducci, Remark 6.7: the principal factor of the residual factor is at least the principal
factor itself. -/
theorem principalFactor_le_principalFactor_of_eq_residualFactor
    (o r : AdditivePrincipalAboveOne) (hr : r.1 = o.residualFactor) :
    o.principalFactor ≤ r.principalFactor := by
  have hmem := r.principalFactor_mem_factors
  rw [multiplicativePrincipalFactors_eq] at hmem
  obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hmem
  rw [hr] at ht
  have htO : t ∈ (log omega0 o.1).additivePrincipalTerms :=
    o.mem_terms_of_mem_terms_log_residualFactor ht
  have hle := o.log_principalFactor_le_of_mem_terms htO
  have hprin : IsAdditivelyPrincipal o.principalFactor :=
    o.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal
  calc o.principalFactor = omega0 ^ log omega0 o.principalFactor := hprin.opow_log_self.symm
    _ ≤ omega0 ^ t := opow_le_opow_right omega0_pos hle
    _ = r.principalFactor := hteq

end AdditivePrincipalAboveOne

end Ordinal
