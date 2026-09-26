/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.OfValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Comparison with Mathlib's valuation integers

For a group-valued Mathlib valuation, read as a max-additive degree by `MaxAddDegree.ofValuation`,
the nonpositive subring is Mathlib's `Valuation.integer`, and the strictly negative ideal is the
pullback of `Valuation.ltIdeal w 1`. These bridges make Mathlib's valuation-ring API available
without imposing a group structure on the monoid-valued construction used in LM24, Section 4.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
  [LinearOrder M] [IsOrderedAddMonoid M]

/-- In the group-valued case, the nonpositive subring is Mathlib's valuation integer subring. -/
theorem nonpositiveSubring_ofValuation_eq_integer (w : Valuation R (WithZero (Multiplicative M))) :
    (ofValuation w).nonpositiveSubring = w.integer := by
  ext x
  rw [mem_nonpositiveSubring_iff, Valuation.mem_integer_iff, ofValuation_apply]
  change Multiplicative.toAdd (WithZero.toMulBot (w x)) ≤ 0 ↔ w x ≤ 1
  rfl

/-- The canonical equivalence from the LM24 nonpositive subring to Mathlib's valuation integers. -/
def nonpositiveEquivInteger (w : Valuation R (WithZero (Multiplicative M))) :
    (ofValuation w).nonpositiveSubring ≃+* w.integer where
  toFun x := ⟨x, by
    rw [← nonpositiveSubring_ofValuation_eq_integer]
    exact x.2⟩
  invFun x := ⟨x, by
    rw [nonpositiveSubring_ofValuation_eq_integer]
    exact x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_nonpositiveEquivInteger (w : Valuation R (WithZero (Multiplicative M)))
    (x : (ofValuation w).nonpositiveSubring) :
    (nonpositiveEquivInteger w x : R) = x :=
  by simp [nonpositiveEquivInteger]

/-- The LM24 negative ideal is the pullback of Mathlib's strict ideal below `1`. -/
theorem negativeIdeal_ofValuation_eq_comap_ltIdeal
    (w : Valuation R (WithZero (Multiplicative M))) :
    (ofValuation w).negativeIdeal =
      (w.ltIdeal 1).comap (nonpositiveEquivInteger w).toRingHom := by
  ext x
  rw [mem_negativeIdeal_iff, Ideal.mem_comap]
  rw [Valuation.mem_ltIdeal_iff]
  have hcoe :
      (((nonpositiveEquivInteger w).toRingHom x : w.integer) : R) = x :=
    coe_nonpositiveEquivInteger w x
  rw [hcoe, ofValuation_apply]
  change Multiplicative.toAdd (WithZero.toMulBot (w (x : R))) < 0 ↔
    w (x : R) < 1
  rfl

end MaxAddDegree
