/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionRemainder
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Critical points of nonpositive real Hahn series

For a nonzero series `b`, Berarducci defines its critical point as the least nonpositive exponent
where the ordinal value of a translated truncation is maximal. `IsCriticalPoint b x` states this
characterization directly; existence is the separate content of Berarducci, Lemma 10.1.

The main result here is Berarducci, Lemma 10.4: at critical points `x` and `y`, the translated
truncation of `b * c` at `x + y` has value equal to the Hessenberg product of the two critical
values. The proof isolates the `(x, y)` term in the finite germ-convolution formula. Minimality
makes every other term strictly smaller, so it cannot cancel the distinguished term.

## References

* A. Berarducci, *Factorization in generalized power series*, Trans. Amer. Math. Soc. 352
  (2000), 553–577, cited as [Ber00].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- `x` is the critical point of `b` when `b` is nonzero, `x ≤ 0`, the value of the translated
truncation at `x` is maximal, and `x` is the least point attaining that value. -/
def IsCriticalPoint (b : Series K) (x : ℝ) : Prop :=
  b ≠ 0 ∧ x ≤ 0 ∧
    (∀ y : ℝ, y ≤ 0 →
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) ≤
        ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x)) ∧
    ∀ y : ℝ, y ≤ 0 →
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) =
        ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) → x ≤ y

/-- Characterization of the critical-point predicate. -/
theorem isCriticalPoint_iff {b : Series K} {x : ℝ} :
    IsCriticalPoint b x ↔
      b ≠ 0 ∧ x ≤ 0 ∧
        (∀ y : ℝ, y ≤ 0 →
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) ≤
            ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x)) ∧
        ∀ y : ℝ, y ≤ 0 →
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) =
            ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) → x ≤ y :=
  (Iff.rfl)

/-- Eliminate the critical-point predicate through the module boundary. -/
theorem IsCriticalPoint.elim {b : Series K} {x : ℝ} (hx : IsCriticalPoint b x) :
    b ≠ 0 ∧ x ≤ 0 ∧
      (∀ y : ℝ, y ≤ 0 →
        ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) ≤
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x)) ∧
      ∀ y : ℝ, y ≤ 0 →
        ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) =
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) → x ≤ y :=
  hx

/-- A series with a critical point is nonzero. -/
theorem IsCriticalPoint.ne_zero {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) : b ≠ 0 :=
  hx.elim.1

/-- A critical point is nonpositive. -/
theorem IsCriticalPoint.nonpositive {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) : x ≤ 0 :=
  hx.elim.2.1

/-- The translated-truncation value at a critical point is maximal. -/
theorem IsCriticalPoint.value_le {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) (y : ℝ) (hy : y ≤ 0) :
    ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) ≤
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) :=
  hx.elim.2.2.1 y hy

/-- A critical point is the least nonpositive point attaining the maximal value. -/
theorem IsCriticalPoint.le_of_value_eq {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) (y : ℝ) (hy : y ≤ 0)
    (hvalue : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) =
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x)) : x ≤ y :=
  hx.elim.2.2.2 y hy hvalue

/-- Berarducci's ordinal value is multiplicative on the germ quotient once its multiplicativity
on series is known. -/
theorem germOrdinalValue_mul [CharZero K] (q p : Germ K) :
    germOrdinalValue (q * p) = germOrdinalValue q * germOrdinalValue p := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective p
  have hb' : toGerm b = q := (toGerm_apply b).trans hb
  have hc' : toGerm c = p := (toGerm_apply c).trans hc
  rw [← hb', ← hc', ← map_mul]
  simp only [toGerm_apply, germOrdinalValue_mk, ordinalValue_mul]

/-- Adding a germ of strictly smaller value does not change the larger value. -/
theorem germOrdinalValue_add_eq_left_of_lt {q p : Germ K}
    (h : germOrdinalValue p < germOrdinalValue q) :
    germOrdinalValue (q + p) = germOrdinalValue q := by
  apply le_antisymm
  · simpa [max_eq_left h.le] using germOrdinalValue_add_le_max q p
  · have hle := germOrdinalValue_add_le_max (q + p) (-p)
    rw [add_neg_cancel_right, germOrdinalValue_neg] at hle
    by_contra hnot
    exact (not_lt_of_ge hle) (max_lt (lt_of_not_ge hnot) h)

/-- At an exponent in the support, the translated truncation has positive ordinal value. -/
theorem ordinalValue_translatedTruncation_pos_of_mem_support
    {b : K⟦ℝ⟧} {x : ℝ} (hx : x ∈ b.support) :
    0 < ordinalValue (translatedTruncation b x) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hmem := ordinalValue_eq_zero_iff.mp hzero
  have hcoeff := constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
  rw [HahnSeries.Nonpositive.constantCoeff_apply, coeff_translatedTruncation] at hcoeff
  simp only [le_refl, ite_true, add_zero] at hcoeff
  exact (HahnSeries.mem_support _ _).mp hx hcoeff

/-- The maximal translated-truncation value at a critical point is positive. -/
theorem IsCriticalPoint.value_pos {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) :
    0 < ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) := by
  have hsupport : (b : K⟦ℝ⟧).support.Nonempty :=
    HahnSeries.support_nonempty_iff.mpr (by simpa using hx.ne_zero)
  obtain ⟨y, hy⟩ := hsupport
  have hy0 := HahnSeries.Nonpositive.support_subset b hy
  exact (ordinalValue_translatedTruncation_pos_of_mem_support hy).trans_le
    (hx.value_le y hy0)

/-- A critical point lies in the closure of the series support. -/
theorem IsCriticalPoint.mem_closure_support {b : Series K} {x : ℝ}
    (hx : IsCriticalPoint b x) : x ∈ closure (b : K⟦ℝ⟧).support := by
  by_contra hmem
  have hJ := translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hmem
  rw [← ordinalValue_eq_zero_iff] at hJ
  exact hx.value_pos.ne' hJ

/-- Berarducci, Lemma 10.4: the value of a product truncated at the sum of the factors' critical
points is the Hessenberg product of their critical values. -/
theorem criticalPoint_product_value [CharZero K]
    {b c : Series K} {x y : ℝ}
    (hx : IsCriticalPoint b x) (hy : IsCriticalPoint c y) :
    ordinalValue (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) (x + y)) =
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) *
        ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) := by
  classical
  let gamma := x + y
  let s := convolutionIndex (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) gamma
  let f : ℝ → Germ K := fun beta ↦
    germAt (b : K⟦ℝ⟧) beta * germAt (c : K⟦ℝ⟧) (gamma - beta)
  let X := ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) *
    ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y)
  have hxs : x ∈ s := by
    rw [mem_convolutionIndex]
    refine ⟨hx.mem_closure_support, ?_⟩
    simpa [gamma] using hy.mem_closure_support
  have hXpos : 0 < X := mul_pos hx.value_pos hy.value_pos
  have hfx : germOrdinalValue (f x) = X := by
    dsimp only [f]
    rw [germOrdinalValue_mul]
    simp only [germAt_apply, toGerm_apply, germOrdinalValue_mk]
    congr 1
    simp [gamma]
  have hterm : ∀ beta ∈ s.erase x, germOrdinalValue (f beta) < X := by
    intro beta hbeta
    have hbetaS := (Finset.mem_erase.mp hbeta).2
    have hbetaNe := (Finset.mem_erase.mp hbeta).1
    obtain ⟨hbetaClosure, hdeltaClosure⟩ := mem_convolutionIndex.mp hbetaS
    have hclosureB : closure (b : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
      closure_minimal (HahnSeries.Nonpositive.support_subset b) isClosed_Iic
    have hclosureC : closure (c : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
      closure_minimal (HahnSeries.Nonpositive.support_subset c) isClosed_Iic
    have hbeta0 : beta ≤ 0 := hclosureB hbetaClosure
    have hdelta0 : gamma - beta ≤ 0 := hclosureC hdeltaClosure
    have hbLe := hx.value_le beta hbeta0
    have hcLe := hy.value_le (gamma - beta) hdelta0
    dsimp only [f]
    rw [germOrdinalValue_mul]
    simp only [germAt_apply, toGerm_apply, germOrdinalValue_mk]
    change ordinalValue (translatedTruncation (b : K⟦ℝ⟧) beta) *
        ordinalValue (translatedTruncation (c : K⟦ℝ⟧) (gamma - beta)) < X
    dsimp only [X]
    rcases hbLe.eq_or_lt with hbEq | hbLt
    · have hxbeta : x ≤ beta := hx.le_of_value_eq beta hbeta0 hbEq
      have hdeltaLt : gamma - beta < y := by
        dsimp [gamma]
        rcases hxbeta.eq_or_lt with h | h
        · exact (hbetaNe h.symm).elim
        · linarith
      have hcLt : ordinalValue (translatedTruncation (c : K⟦ℝ⟧) (gamma - beta)) <
          ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) := by
        exact lt_of_le_of_ne hcLe fun heq ↦
          (not_le_of_gt hdeltaLt) (hy.le_of_value_eq (gamma - beta) hdelta0 heq)
      rw [hbEq]
      exact mul_lt_mul_of_pos_left hcLt hx.value_pos
    · exact (mul_le_mul_right hcLe _).trans_lt
        (mul_lt_mul_of_pos_right hbLt hy.value_pos)
  have hrest : germOrdinalValue (∑ beta ∈ s.erase x, f beta) < X :=
    germOrdinalValue_sum_lt hXpos hterm
  have hsum : germOrdinalValue (∑ beta ∈ s, f beta) = X := by
    rw [← s.add_sum_erase f hxs]
    rw [germOrdinalValue_add_eq_left_of_lt]
    · exact hfx
    · rwa [hfx]
  have hconv := germAt_mul (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) gamma
  change ordinalValue (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) gamma) = X
  calc
    _ = germOrdinalValue (germAt (((b * c : Series K) : K⟦ℝ⟧)) gamma) := by
      rw [germAt_apply, toGerm_apply, germOrdinalValue_mk]
    _ = germOrdinalValue
        (germAt ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)) gamma) := by rfl
    _ = X := by rw [hconv]; exact hsum

end Berarducci
