/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.WeakNormalForm
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorTermCount

import Mathlib.Data.Sum.Order

/-!
# API checks for LM24 weak normal forms

The ordinal certificates separate LM24's positive additive-principal convention from Mathlib's
convention, which includes zero, and refute the false indecomposability clause printed in LM24,
Definition 3.3.1, using `1 + ω = ω`.

The main Hahn-series fixture has coefficient one at every point of the lexicographic sum
`ℕ ⊕ₗ ℕ`. Its lower and upper components both have support order type `ω`, yet form two
strictly support-separated blocks. Hence its weak normal form has equal consecutive block order
types. This distinguishes LM24, Definition 3.3.2 from the nearby incorrect definition requiring
strict decrease, and it verifies that the uncompressed Cantor-term list retains repeated terms.
The exact terminal truncation also exercises LM24, Corollary 3.3.5 on a nonconstant,
infinite-support series.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- Zero distinguishes LM24's positive additive-principal convention from Mathlib's convention. -/
theorem zero_separates_LM24_from_mathlib_principal :
    ¬Ordinal.IsAdditivelyPrincipal 0 ∧ Ordinal.IsPrincipal (· + ·) 0 := by
  constructor
  · intro h
    exact h.ne_zero rfl
  · exact Ordinal.isPrincipal_zero

/-- The additive-principal ordinal `ω` refutes the false printed indecomposability clause because
`1 + ω = ω` although neither summand is zero. -/
theorem omega_refutes_printed_indecomposability :
    Ordinal.IsAdditivelyPrincipal Ordinal.omega0 ∧
      ¬(∀ b c : Ordinal, Ordinal.omega0 = b + c → b = 0 ∨ c = 0) := by
  constructor
  · simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 1
  · intro h
    rcases h 1 Ordinal.omega0 (by simp) with h | h
    · norm_num at h
    · exact Ordinal.omega0_ne_zero h

/-- The empty block list is the weak normal form of the zero series. -/
theorem zero_weakNormalForm :
    HahnSeries.IsWeakNormalForm (0 : ℚ⟦ℤ⟧) [] := by
  rw [HahnSeries.isWeakNormalForm_iff]
  simp [List.sortedGE_iff_pairwise]

private instance : WellFoundedLT (ℕ ⊕ₗ ℕ) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := ℕ)).symm.toRelEmbedding.isWellFounded

/-- The coefficient-one Hahn series on the lexicographic sum of two copies of `ℕ`. -/
def twoOmegaSeries : ℚ⟦ℕ ⊕ₗ ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using Set.IsPWO.of_linearOrder (Set.univ : Set (ℕ ⊕ₗ ℕ))

/-- The first `ℕ`-indexed component of `twoOmegaSeries`. -/
def twoOmegaLower : ℚ⟦ℕ ⊕ₗ ℕ⟧ :=
  HahnSeries.filter (fun x ↦ x.isLeft) twoOmegaSeries

/-- The second `ℕ`-indexed component of `twoOmegaSeries`. -/
def twoOmegaUpper : ℚ⟦ℕ ⊕ₗ ℕ⟧ :=
  HahnSeries.filter (fun x ↦ x.isRight) twoOmegaSeries

private theorem twoOmegaLower_support : twoOmegaLower.support = Set.range Sum.inlₗ := by
  rw [twoOmegaLower, HahnSeries.support_filter]
  ext x
  rcases x with x | x
  · constructor
    · intro _
      exact ⟨x, rfl⟩
    · intro _
      simp [twoOmegaSeries]
  · constructor
    · intro h
      simp at h
    · rintro ⟨y, h⟩
      exact ((Sum.Lex.inl_lt_inr y x).ne h).elim

private theorem twoOmegaUpper_support : twoOmegaUpper.support = Set.range Sum.inrₗ := by
  rw [twoOmegaUpper, HahnSeries.support_filter]
  ext x
  rcases x with x | x
  · constructor
    · intro h
      simp at h
    · rintro ⟨y, h⟩
      exact ((Sum.Lex.inl_lt_inr x y).ne h.symm).elim
  · constructor
    · intro _
      exact ⟨x, rfl⟩
    · intro _
      simp [twoOmegaSeries]

private theorem twoOmegaLower_supportOrderType :
    twoOmegaLower.supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : twoOmegaLower.support ≃o ℕ :=
    (OrderIso.setCongr twoOmegaLower.support (Set.range Sum.inlₗ)
      twoOmegaLower_support).trans
        (OrderEmbedding.ofStrictMono Sum.inlₗ Sum.Lex.inl_strictMono).orderIso.symm
  exact twoOmegaLower.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_nat_lt

private theorem twoOmegaUpper_supportOrderType :
    twoOmegaUpper.supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : twoOmegaUpper.support ≃o ℕ :=
    (OrderIso.setCongr twoOmegaUpper.support (Set.range Sum.inrₗ)
      twoOmegaUpper_support).trans
        (OrderEmbedding.ofStrictMono Sum.inrₗ Sum.Lex.inr_strictMono).orderIso.symm
  exact twoOmegaUpper.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_nat_lt

private theorem twoOmega_supportBelow :
    HahnSeries.SupportBelow twoOmegaLower twoOmegaUpper := by
  rw [HahnSeries.supportBelow_iff, twoOmegaLower_support, twoOmegaUpper_support]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact Sum.Lex.inl_lt_inr i j

private theorem twoOmegaLower_add_upper :
    twoOmegaLower + twoOmegaUpper = twoOmegaSeries := by
  ext x
  rcases x with x | x <;> simp [twoOmegaLower, twoOmegaUpper, twoOmegaSeries]

private theorem twoOmegaLower_isWeaklyPrincipal :
    HahnSeries.IsWeaklyPrincipal twoOmegaLower := by
  rw [HahnSeries.isWeaklyPrincipal_iff, twoOmegaLower_supportOrderType]
  simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 1

private theorem twoOmegaUpper_isWeaklyPrincipal :
    HahnSeries.IsWeaklyPrincipal twoOmegaUpper := by
  rw [HahnSeries.isWeaklyPrincipal_iff, twoOmegaUpper_supportOrderType]
  simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 1

/-- The two equal-order-type components form an LM24 weak normal form. -/
theorem twoOmega_weakNormalForm :
    HahnSeries.IsWeakNormalForm twoOmegaSeries [twoOmegaLower, twoOmegaUpper] := by
  rw [HahnSeries.isWeakNormalForm_iff_isChain]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using twoOmegaLower_add_upper
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact twoOmegaLower_isWeaklyPrincipal
    · exact twoOmegaUpper_isWeaklyPrincipal
  · simp [twoOmegaLower_supportOrderType, twoOmegaUpper_supportOrderType,
      List.sortedGE_iff_pairwise]
  · exact List.isChain_pair.mpr twoOmega_supportBelow

/-- The support order type of the two-block fixture is the ordinary ordinal sum `ω + ω`. -/
theorem twoOmegaSeries_supportOrderType :
    twoOmegaSeries.supportOrderType = Ordinal.omega0 + Ordinal.omega0 := by
  apply (HahnSeries.supportOrderType_eq_add_iff _ _ _).mpr
  exact ⟨twoOmegaLower, twoOmegaUpper, twoOmega_supportBelow,
    twoOmegaLower_supportOrderType, twoOmegaUpper_supportOrderType,
    twoOmegaLower_add_upper.symm⟩

/-- Equal consecutive block order types are permitted by LM24's nonincreasing condition. -/
theorem twoOmega_weakNormalForm_has_equal_block_orderTypes :
    HahnSeries.IsWeakNormalForm twoOmegaSeries [twoOmegaLower, twoOmegaUpper] ∧
      twoOmegaLower.supportOrderType = twoOmegaUpper.supportOrderType := by
  exact ⟨twoOmega_weakNormalForm,
    twoOmegaLower_supportOrderType.trans twoOmegaUpper_supportOrderType.symm⟩

/-- The uncompressed Cantor-term list retains the two repeated `ω` terms. -/
theorem twoOmega_repeated_additivePrincipalTerms :
    twoOmegaSeries.supportOrderType.additivePrincipalTerms =
      [Ordinal.omega0, Ordinal.omega0] := by
  have h := twoOmega_weakNormalForm.supportOrderTypes_eq_additivePrincipalTerms
  simpa only [List.map_cons, List.map_nil, twoOmegaLower_supportOrderType,
    twoOmegaUpper_supportOrderType] using h.symm

/-- Counting the uncompressed Cantor terms retains both repeated copies of `ω`. -/
theorem twoOmega_cantorTermCount :
    NatOrdinal.cantorTermCount
      (NatOrdinal.of twoOmegaSeries.supportOrderType) = 2 := by
  rw [NatOrdinal.cantorTermCount_of, twoOmega_repeated_additivePrincipalTerms]
  rfl

/-- The public uniqueness theorem identifies any weak normal form of the fixture. -/
theorem twoOmega_weakNormalForm_unique (blocks : List ℚ⟦ℕ ⊕ₗ ℕ⟧)
    (hblocks : HahnSeries.IsWeakNormalForm twoOmegaSeries blocks) :
    blocks = [twoOmegaLower, twoOmegaUpper] :=
  hblocks.unique twoOmega_weakNormalForm

/-- At the first exponent of the upper block, weak upper truncation returns exactly that block. -/
theorem twoOmega_terminal_truncation :
    HahnSeries.truncGE (Sum.inrₗ 0) twoOmegaSeries = twoOmegaUpper := by
  ext x
  induction x using Lex.rec with
  | h x =>
      rcases x with x | x
      · rw [HahnSeries.coeff_truncGE_of_lt (Sum.Lex.inl_lt_inr x 0)]
        rw [twoOmegaUpper, HahnSeries.coeff_filter]
        rfl
      · have hle : (Sum.inrₗ 0 : ℕ ⊕ₗ ℕ) ≤ Sum.inrₗ x :=
          Sum.Lex.inr_le_inr_iff.mpr (Nat.zero_le x)
        rw [HahnSeries.coeff_truncGE_of_le hle]
        rw [twoOmegaUpper, HahnSeries.coeff_filter]
        rfl

/-- The explicit terminal truncation is nonzero and weakly principal, as in LM24, Corollary
3.3.5. -/
theorem twoOmega_terminal_truncation_certificate :
    HahnSeries.truncGE (Sum.inrₗ 0) twoOmegaSeries ≠ 0 ∧
      HahnSeries.IsWeaklyPrincipal
        (HahnSeries.truncGE (Sum.inrₗ 0) twoOmegaSeries) := by
  rw [twoOmega_terminal_truncation]
  exact ⟨twoOmegaUpper_isWeaklyPrincipal.ne_zero, twoOmegaUpper_isWeaklyPrincipal⟩

end Tests
