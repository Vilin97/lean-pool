/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorTermCount

/-!
# Cantor term count of Hahn-series degree

LM24, Proposition 5.6.1 bounds the number of infinite-support irreducible factors by the
number of terms in the Cantor normal form of the degree. `HahnSeries.degreeCantorTermCount`
is that number, with value zero at the bottom degree of the zero series.

Under exact degree multiplicativity, this count is additive on products of nonzero series.
This is the numerical identity used by the factorisation induction.
-/

open scoped HahnSeries NatOrdinal

universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u} [LinearOrder G]

/-- The number of terms in the uncompressed Cantor normal form of a Hahn-series degree,
with value zero at degree `⊥`. -/
def degreeCantorTermCount [Zero R] (x : R⟦G⟧) : ℕ :=
  NatOrdinal.cantorTermCount (x.degree.unbotD 0)

/-- Evaluation of the term count at a specified nonbottom degree. -/
theorem degreeCantorTermCount_eq_of_degree [Zero R] {x : R⟦G⟧}
    {a : NatOrdinal} (hx : x.degree = a) :
    degreeCantorTermCount x = NatOrdinal.cantorTermCount a := by
  rw [degreeCantorTermCount, hx, WithBot.unbotD_coe]

/-- Hahn series with equal degree have equal Cantor term counts. -/
theorem degreeCantorTermCount_congr [Zero R] {x y : R⟦G⟧}
    (hxy : x.degree = y.degree) :
    degreeCantorTermCount x = degreeCantorTermCount y := by
  rw [degreeCantorTermCount, degreeCantorTermCount, hxy]

@[simp]
theorem degreeCantorTermCount_zero [Zero R] :
    degreeCantorTermCount (0 : R⟦G⟧) = 0 := by
  rw [degreeCantorTermCount, degree_zero, WithBot.unbotD_bot,
    NatOrdinal.cantorTermCount_zero]

/-- Positive Hahn-series degree has at least one Cantor term. -/
theorem degreeCantorTermCount_pos_of_degree_pos [Zero R] {x : R⟦G⟧}
    (hx : 0 < x.degree) :
    0 < degreeCantorTermCount x := by
  have hxNe : x ≠ 0 := by
    intro hzero
    subst x
    simp at hx
  have hxDegree : x.degree ≠ ⊥ := degree_eq_bot.not.mpr hxNe
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hxDegree
  rw [degreeCantorTermCount, ← ha, WithBot.unbotD_coe]
  apply NatOrdinal.cantorTermCount_pos
  intro hzero
  subst a
  have hdegreeZero : (0 : WithBot NatOrdinal) = x.degree := by
    simpa using ha
  rw [← hdegreeZero] at hx
  exact (lt_irrefl 0 hx).elim

/-- The Cantor term count of degree is additive on nonzero products when degree is
multiplicative. -/
theorem degreeCantorTermCount_mul
    [Semiring R] [AddCommMonoid G] [IsOrderedCancelAddMonoid G]
    {x y : R⟦G⟧} (hdegree : (x * y).degree = x.degree + y.degree)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    degreeCantorTermCount (x * y) =
      degreeCantorTermCount x + degreeCantorTermCount y := by
  have hxDegree : x.degree ≠ ⊥ := degree_eq_bot.not.mpr hx
  have hyDegree : y.degree ≠ ⊥ := degree_eq_bot.not.mpr hy
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hxDegree
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hyDegree
  rw [degreeCantorTermCount, degreeCantorTermCount,
    degreeCantorTermCount, hdegree, ← ha, ← hb, ← WithBot.coe_add,
    WithBot.unbotD_coe, NatOrdinal.cantorTermCount_add]
  simp only [WithBot.unbotD_coe]

end HahnSeries
