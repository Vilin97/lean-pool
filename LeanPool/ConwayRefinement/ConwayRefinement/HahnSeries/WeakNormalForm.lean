/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal

/-!
# Weak normal forms of Hahn series

This module formalizes LM24, Definitions 3.3.1 and 3.3.2, Proposition 3.3.4, and Corollary
3.3.5. A weakly principal Hahn series has positive additive-principal support order type. A weak
normal form is a finite lower-to-upper decomposition into weakly principal blocks whose support
order types are nonincreasing. The definition uses pairwise support separation; the
`isWeakNormalForm_iff_isChain` theorem proves that this is exactly the adjacent chain printed in
LM24 because every weakly principal block is nonzero.

The order-type condition is deliberately nonstrict. Repeated equal powers of `ω` represent finite
coefficients in Cantor normal form and must produce distinct consecutive blocks. The zero series
has the empty weak normal form.

The existence and uniqueness theorem is generalized from field coefficients and LM24's fixed
support-cardinality bound to additive-monoid coefficients and unrestricted Hahn series. Every
constructed block has support contained in the original support, so the construction restricts to
the source's bounded-support regime.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u} [LinearOrder G] [AddMonoid R]

/-- A weakly principal Hahn series has positive additive-principal support order type. -/
def IsWeaklyPrincipal (x : R⟦G⟧) : Prop :=
  x.supportOrderType.IsAdditivelyPrincipal

/-- Characterization of weakly principal Hahn series by their support order type. -/
theorem isWeaklyPrincipal_iff {x : R⟦G⟧} :
    IsWeaklyPrincipal x ↔ x.supportOrderType.IsAdditivelyPrincipal :=
  (Iff.rfl)

/-- A weakly principal Hahn series is nonzero. -/
theorem IsWeaklyPrincipal.ne_zero {x : R⟦G⟧} (hx : IsWeaklyPrincipal x) : x ≠ 0 := by
  intro hzero
  subst x
  exact (Ordinal.IsAdditivelyPrincipal.ne_zero (isWeaklyPrincipal_iff.mp hx))
    supportOrderType_zero

/-- The four clauses defining an LM24 weak normal form. -/
def IsWeakNormalForm (x : R⟦G⟧) (blocks : List R⟦G⟧) : Prop :=
  blocks.sum = x ∧
    (∀ b ∈ blocks, IsWeaklyPrincipal b) ∧
    (blocks.map supportOrderType).SortedGE ∧
    blocks.Pairwise SupportBelow

/-- Characterization of an LM24 weak normal form by its sum, blocks, order types, and supports. -/
theorem isWeakNormalForm_iff {x : R⟦G⟧} {blocks : List R⟦G⟧} :
    IsWeakNormalForm x blocks ↔
      blocks.sum = x ∧
        (∀ b ∈ blocks, IsWeaklyPrincipal b) ∧
        (blocks.map supportOrderType).SortedGE ∧
        blocks.Pairwise SupportBelow :=
  (Iff.rfl)

/-- Source-form characterization using the adjacent support chain printed in LM24, Definition
3.3.2. Nonzeroness of weakly principal blocks makes this equivalent to pairwise separation. -/
theorem isWeakNormalForm_iff_isChain {x : R⟦G⟧} {blocks : List R⟦G⟧} :
    IsWeakNormalForm x blocks ↔
      blocks.sum = x ∧
        (∀ b ∈ blocks, IsWeaklyPrincipal b) ∧
        (blocks.map supportOrderType).SortedGE ∧
        blocks.IsChain SupportBelow := by
  rw [isWeakNormalForm_iff]
  constructor
  · rintro ⟨hsum, hprincipal, hsorted, hpair⟩
    exact ⟨hsum, hprincipal, hsorted, hpair.isChain⟩
  · rintro ⟨hsum, hprincipal, hsorted, hchain⟩
    refine ⟨hsum, hprincipal, hsorted, ?_⟩
    apply pairwise_supportBelow_of_isChain
    · exact fun b hb ↦ (hprincipal b hb).ne_zero
    · exact hchain

private theorem exists_orderType_blocks (x : R⟦G⟧) (types : List Ordinal)
    (htype : x.supportOrderType = types.sum) :
    ∃ blocks : List R⟦G⟧,
      blocks.sum = x ∧
        blocks.map supportOrderType = types ∧
        blocks.Pairwise SupportBelow := by
  induction types generalizing x with
  | nil =>
      have hx : x = 0 := supportOrderType_eq_zero.mp (by simpa using htype)
      subst x
      exact ⟨[], by simp⟩
  | cons a types ih =>
      have hsplit : x.supportOrderType = a + types.sum := by
        simpa only [List.sum_cons] using htype
      obtain ⟨y, z, hyz, hya, hztypes, hx⟩ :=
        (supportOrderType_eq_add_iff x a types.sum).mp hsplit
      obtain ⟨blocks, hsum, htypes, hpair⟩ := ih z hztypes
      refine ⟨y :: blocks, ?_, ?_, ?_⟩
      · rw [List.sum_cons, hsum]
        exact hx.symm
      · simp only [List.map_cons, hya, htypes]
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair⟩
        intro b hb
        rw [supportBelow_iff]
        intro i hi j hj
        have hbsub : b.support ⊆ z.support := by
          have hsubset := support_subset_list_sum_of_mem hpair hb
          rwa [hsum] at hsubset
        exact hyz.lt hi (hbsub hj)

/-- Every Hahn series has a weak normal form. This is the existence part of LM24, Proposition
3.3.4. -/
theorem exists_isWeakNormalForm (x : R⟦G⟧) :
    ∃ blocks : List R⟦G⟧, IsWeakNormalForm x blocks := by
  obtain ⟨blocks, hsum, htypes, hpair⟩ := exists_orderType_blocks x
    x.supportOrderType.additivePrincipalTerms
    (Ordinal.additivePrincipalTerms_sum x.supportOrderType).symm
  refine ⟨blocks, isWeakNormalForm_iff.mpr ⟨hsum, ?_, ?_, hpair⟩⟩
  · intro b hb
    rw [isWeaklyPrincipal_iff]
    apply Ordinal.isAdditivelyPrincipal_of_mem_additivePrincipalTerms
    rw [← htypes]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  · rw [htypes]
    exact Ordinal.additivePrincipalTerms_sortedGE _

/-- The support order types of a weak normal form are the uncompressed Cantor terms of the whole
support order type. -/
theorem IsWeakNormalForm.supportOrderTypes_eq_additivePrincipalTerms
    {x : R⟦G⟧} {blocks : List R⟦G⟧} (h : IsWeakNormalForm x blocks) :
    blocks.map supportOrderType = x.supportOrderType.additivePrincipalTerms := by
  obtain ⟨hsum, hprincipal, hsorted, hpair⟩ := isWeakNormalForm_iff.mp h
  apply Ordinal.additivePrincipalTerms_unique
  · calc
      (blocks.map supportOrderType).sum = blocks.sum.supportOrderType :=
        (supportOrderType_list_sum hpair).symm
      _ = x.supportOrderType := congrArg supportOrderType hsum
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isWeaklyPrincipal_iff.mp (hprincipal b hb)
  · exact hsorted

private theorem eq_of_pairwise_sum_and_orderTypes {xs ys : List R⟦G⟧}
    (hxpair : xs.Pairwise SupportBelow) (hypair : ys.Pairwise SupportBelow)
    (hsum : xs.sum = ys.sum) (htypes : xs.map supportOrderType = ys.map supportOrderType) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using htypes
  | cons x xs ih =>
      cases ys with
      | nil => simp at htypes
      | cons y ys =>
          rw [List.pairwise_cons] at hxpair hypair
          simp only [List.map_cons, List.cons.injEq] at htypes
          have hxbelow : SupportBelow x xs.sum := supportBelow_list_sum hxpair.1
          have hybelow : SupportBelow y ys.sum := supportBelow_list_sum hypair.1
          have hdecomp := add_decomposition_unique hxbelow hybelow htypes.1 (by
            simpa only [List.sum_cons] using hsum)
          rw [hdecomp.1]
          congr 1
          exact ih hxpair.2 hypair.2 hdecomp.2 htypes.2

/-- Two weak normal forms of the same series are equal. This is the uniqueness part of LM24,
Proposition 3.3.4. -/
theorem IsWeakNormalForm.unique {x : R⟦G⟧} {blocks other : List R⟦G⟧}
    (hblocks : IsWeakNormalForm x blocks) (hother : IsWeakNormalForm x other) :
    blocks = other := by
  obtain ⟨hsum, _, _, hpair⟩ := isWeakNormalForm_iff.mp hblocks
  obtain ⟨hotherSum, _, _, hotherPair⟩ := isWeakNormalForm_iff.mp hother
  apply eq_of_pairwise_sum_and_orderTypes hpair hotherPair
  · exact hsum.trans hotherSum.symm
  · exact hblocks.supportOrderTypes_eq_additivePrincipalTerms.trans
      hother.supportOrderTypes_eq_additivePrincipalTerms.symm

/-- Every Hahn series has exactly one weak normal form. This is LM24, Proposition 3.3.4. -/
theorem existsUnique_isWeakNormalForm (x : R⟦G⟧) :
    ∃! blocks : List R⟦G⟧, IsWeakNormalForm x blocks := by
  obtain ⟨blocks, hblocks⟩ := exists_isWeakNormalForm x
  exact ⟨blocks, hblocks, fun other hother ↦ (hblocks.unique hother).symm⟩

/-- Every nonzero Hahn series has a nonzero weakly principal weak upper truncation. This is LM24,
Corollary 3.3.5, generalized from ordered-group exponents to a linearly ordered type with zero. -/
theorem exists_nonzero_isWeaklyPrincipal_truncGE [Zero G] {x : R⟦G⟧} (hx : x ≠ 0) :
    ∃ c : G, truncGE c x ≠ 0 ∧ IsWeaklyPrincipal (truncGE c x) := by
  obtain ⟨blocks, hblocks⟩ := exists_isWeakNormalForm x
  obtain ⟨hsum, hprincipal, _, hpair⟩ := isWeakNormalForm_iff.mp hblocks
  have hblocksne : blocks ≠ [] := by
    intro hzero
    rw [hzero] at hsum
    exact hx (by simpa using hsum.symm)
  let last := blocks.getLast hblocksne
  have hlastMem : last ∈ blocks := List.getLast_mem hblocksne
  have hlastPrincipal : IsWeaklyPrincipal last := hprincipal last hlastMem
  have hlastNe : last ≠ 0 := hlastPrincipal.ne_zero
  have hlastOrderMem : last.order ∈ last.support :=
    (mem_support last last.order).mpr (coeff_order_eq_zero.not.mpr hlastNe)
  have hprefixBelow : SupportBelow blocks.dropLast.sum last := by
    apply list_sum_supportBelow
    intro b hb
    exact hpair.rel_dropLast_getLast hb
  have hprefixTrunc : truncGE last.order blocks.dropLast.sum = 0 := by
    rw [← support_eq_empty_iff, support_truncGE]
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hi
    exact fun hle ↦ (not_lt_of_ge hle) (hprefixBelow.lt hi hlastOrderMem)
  have hlastTrunc : truncGE last.order last = last := by
    ext i
    by_cases hi : last.coeff i = 0
    · simp [hi]
    · simp [order_le_of_coeff_ne_zero hi]
  have hxsplit : blocks.dropLast.sum + last = x := by
    calc
      blocks.dropLast.sum + last = (blocks.dropLast ++ [last]).sum := by simp
      _ = blocks.sum := congrArg List.sum (List.dropLast_append_getLast hblocksne)
      _ = x := hsum
  refine ⟨last.order, ?_, ?_⟩
  · rw [← hxsplit, truncGE_add, hprefixTrunc, hlastTrunc, zero_add]
    exact hlastNe
  · rw [← hxsplit, truncGE_add, hprefixTrunc, hlastTrunc, zero_add]
    exact hlastPrincipal

end HahnSeries
