/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Order.Minimal

/-!
# Least-representative degree on a quotient ring

Let a commutative ring carry a separated max-additive degree whose value index is well ordered.
The degree of a nonzero class modulo an ideal is defined to be the least degree among all its
representatives, while the zero class has bottom degree. This realizes the quotient-degree
construction for filtered quotient rings.

The resulting quotient degree is separated and satisfies the ultrametric addition inequality and
the submultiplicative product inequality. Equality for products is a later associated-graded
consequence and is deliberately not asserted here.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [LinearOrder M]

/-- The grades attained by representatives of a quotient class. -/
def representativeGrades (ν : MaxAddDegree R M) (I : Ideal R) (q : R ⧸ I) : Set M :=
  {m | ∃ x : R, Ideal.Quotient.mk I x = q ∧ ν x = m}

/-- Membership in the set of grades attained by representatives of a quotient class. -/
theorem mem_representativeGrades_iff (ν : MaxAddDegree R M) (I : Ideal R)
    (q : R ⧸ I) (m : M) :
    m ∈ ν.representativeGrades I q ↔
      ∃ x : R, Ideal.Quotient.mk I x = q ∧ ν x = m :=
  Iff.rfl

theorem representativeGrades_nonempty (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) {q : R ⧸ I} (hq : q ≠ 0) :
    (ν.representativeGrades I q).Nonempty := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hx : x ≠ 0 := by
    intro hx
    apply hq
    simp [hx]
  have hνx : ν x ≠ ⊥ := ν.map_ne_bot_of_ne_zero hν hx
  refine ⟨(ν x).unbot hνx, x, rfl, ?_⟩
  exact (WithBot.coe_unbot (ν x) hνx).symm

variable [WellFoundedLT M]

/-- The least degree of a representative of a quotient class, with bottom assigned to zero. -/
def quotientValue (ν : MaxAddDegree R M) (I : Ideal R) (hν : ν.IsSeparated)
    (q : R ⧸ I) : WithBot M := by
  classical
  exact if hq : q = 0 then ⊥
    else (wellFounded_lt.min (ν.representativeGrades I q)
      (ν.representativeGrades_nonempty I hν hq) : M)

@[simp]
theorem quotientValue_zero (ν : MaxAddDegree R M) (I : Ideal R) (hν : ν.IsSeparated) :
    ν.quotientValue I hν 0 = ⊥ := by
  simp [quotientValue]

theorem quotientValue_eq_coe_min (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) {q : R ⧸ I} (hq : q ≠ 0) :
    ν.quotientValue I hν q =
      (wellFounded_lt.min (ν.representativeGrades I q)
        (ν.representativeGrades_nonempty I hν hq) : M) := by
  simp [quotientValue, hq]

@[simp]
theorem quotientValue_eq_bot_iff (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (q : R ⧸ I) :
    ν.quotientValue I hν q = ⊥ ↔ q = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [ν.quotientValue_eq_coe_min I hν hq]
    simp [hq]

/-- Every nonzero quotient class has a representative whose degree is its quotient degree. -/
theorem exists_representative_quotientValue_eq (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) {q : R ⧸ I} (hq : q ≠ 0) :
    ∃ x : R, Ideal.Quotient.mk I x = q ∧ ν x = ν.quotientValue I hν q := by
  have hmem := wellFounded_lt.min_mem (ν.representativeGrades I q)
    (ν.representativeGrades_nonempty I hν hq)
  obtain ⟨x, hxq, hxν⟩ := hmem
  refine ⟨x, hxq, ?_⟩
  rw [ν.quotientValue_eq_coe_min I hν hq]
  exact hxν

/-- The quotient degree is at most the degree of every representative. -/
theorem quotientValue_mk_le (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (x : R) :
    ν.quotientValue I hν (Ideal.Quotient.mk I x) ≤ ν x := by
  by_cases hq : Ideal.Quotient.mk I x = 0
  · rw [hq, ν.quotientValue_zero]
    exact bot_le
  · have hx : x ≠ 0 := by
      intro hx
      apply hq
      simp [hx]
    have hνx : ν x ≠ ⊥ := by
      intro hbot
      exact hx (((isSeparated_iff ν).mp hν x).mp hbot)
    have hmem : (ν x).unbot hνx ∈
        ν.representativeGrades I (Ideal.Quotient.mk I x) := by
      refine ⟨x, rfl, ?_⟩
      exact (WithBot.coe_unbot (ν x) hνx).symm
    rw [ν.quotientValue_eq_coe_min I hν hq, ← WithBot.coe_unbot (ν x) hνx,
      WithBot.coe_le_coe]
    exact wellFounded_lt.min_le hmem

/-- The unit of the quotient has degree at most zero. -/
theorem quotientValue_one_le_zero (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) :
    ν.quotientValue I hν 1 ≤ 0 := by
  calc
    ν.quotientValue I hν 1 =
        ν.quotientValue I hν (Ideal.Quotient.mk I 1) := by rw [map_one]
    _ ≤ ν 1 := ν.quotientValue_mk_le I hν 1
    _ ≤ 0 := ν.map_one_le_zero

@[simp]
theorem quotientValue_neg (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (q : R ⧸ I) :
    ν.quotientValue I hν (-q) = ν.quotientValue I hν q := by
  by_cases hq : q = 0
  · simp [hq]
  · obtain ⟨x, hxq, hxν⟩ := ν.exists_representative_quotientValue_eq I hν hq
    have hle : ν.quotientValue I hν (-q) ≤ ν.quotientValue I hν q := by
      rw [← hxν, ← map_neg, ← hxq]
      exact ν.quotientValue_mk_le I hν (-x)
    have hnq : -q ≠ 0 := neg_ne_zero.mpr hq
    obtain ⟨y, hyq, hyν⟩ := ν.exists_representative_quotientValue_eq I hν hnq
    have hge : ν.quotientValue I hν q ≤ ν.quotientValue I hν (-q) := by
      rw [← hyν, ← map_neg, ← neg_neg q, ← hyq]
      exact ν.quotientValue_mk_le I hν (-y)
    exact le_antisymm hle hge

theorem quotientValue_add_le_max (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (q r : R ⧸ I) :
    ν.quotientValue I hν (q + r) ≤
      max (ν.quotientValue I hν q) (ν.quotientValue I hν r) := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨x, hxq, hxν⟩ := ν.exists_representative_quotientValue_eq I hν hq
  obtain ⟨y, hyr, hyν⟩ := ν.exists_representative_quotientValue_eq I hν hr
  calc
    ν.quotientValue I hν (q + r) =
        ν.quotientValue I hν (Ideal.Quotient.mk I (x + y)) := by rw [map_add, hxq, hyr]
    _ ≤ ν (x + y) := ν.quotientValue_mk_le I hν (x + y)
    _ ≤ max (ν x) (ν y) := ν.map_add_le_max x y
    _ = max (ν.quotientValue I hν q) (ν.quotientValue I hν r) := by rw [hxν, hyν]

theorem quotientValue_mul_le_add (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (q r : R ⧸ I) :
    ν.quotientValue I hν (q * r) ≤
      ν.quotientValue I hν q + ν.quotientValue I hν r := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨x, hxq, hxν⟩ := ν.exists_representative_quotientValue_eq I hν hq
  obtain ⟨y, hyr, hyν⟩ := ν.exists_representative_quotientValue_eq I hν hr
  calc
    ν.quotientValue I hν (q * r) =
        ν.quotientValue I hν (Ideal.Quotient.mk I (x * y)) := by rw [_root_.map_mul, hxq, hyr]
    _ ≤ ν (x * y) := ν.quotientValue_mk_le I hν (x * y)
    _ ≤ ν x + ν y := ν.map_mul_le_add x y
    _ = ν.quotientValue I hν q + ν.quotientValue I hν r := by rw [hxν, hyν]

/-- The quotient degree obtained by minimizing the degree among all representatives. -/
def quotient (ν : MaxAddDegree R M) (I : Ideal R) (hν : ν.IsSeparated) :
    MaxAddDegree (R ⧸ I) M where
  toFun := ν.quotientValue I hν
  map_zero' := ν.quotientValue_zero I hν
  map_one_le_zero' := ν.quotientValue_one_le_zero I hν
  map_neg' := ν.quotientValue_neg I hν
  map_add_le_max' := ν.quotientValue_add_le_max I hν
  map_mul_le_add' := ν.quotientValue_mul_le_add I hν

@[simp]
theorem quotient_apply (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) (q : R ⧸ I) :
    ν.quotient I hν q = ν.quotientValue I hν q := (rfl)

/-- The least-representative degree on a quotient ring is separated. -/
theorem quotient_isSeparated (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) :
    (ν.quotient I hν).IsSeparated := by
  rw [isSeparated_iff]
  intro q
  rw [ν.quotient_apply I hν]
  exact ν.quotientValue_eq_bot_iff I hν q

/-- If the least-representative quotient degree is multiplicative, then the quotient is a
domain. -/
theorem quotient_isDomain (ν : MaxAddDegree R M) (I : Ideal R)
    (hν : ν.IsSeparated) [Nontrivial (R ⧸ I)] [(ν.quotient I hν).IsMultiplicative] :
    IsDomain (R ⧸ I) :=
  (ν.quotient I hν).isDomain (ν.quotient_isSeparated I hν)

end MaxAddDegree
