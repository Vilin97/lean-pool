/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ComplexityDecrease
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
public import Mathlib.RingTheory.Ideal.Prime

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Berarducci's induction on complexity

Berarducci, Lemma 9.6: the ordinal value of a product of series of value above one is the
Hessenberg product of their values. The induction is on the complexity of the formal expression,
which decreases by Lemma 9.5 at each step.

Splitting the expression at its selected factor gives `b₀ ^ k` times the product `c` of the
others. The value of `c` comes from the induction hypothesis, since dropping the selected factor
lowers the complexity; that value supplies Lemma 8.2 with `v_J^p(b₀) ≤ v_J^p(c)`, because the
principal value of a product is bounded below by those of its factors. The eventual hypothesis
of Lemma 8.2 is the induction hypothesis at the reduced expression. When the truncation has value
one it is dropped from the expression, which is harmless because a factor of value one does not
change a value; when there is no other factor at all, `c` would be `1` and the pure-power form of
Lemma 8.2 is used instead.
-/

universe v

public noncomputable section

open HahnSeries Ordinal Filter Topology

namespace Berarducci

variable {K : Type v} [Field K]

namespace FormalExpression

/-- The Hessenberg product of the ordinal values of the factors. -/
def valueProd (w : FormalExpression K) : NatOrdinal := (w.map fun x ↦ ordinalValue x.1).prod

theorem valueProd_zero : valueProd (0 : FormalExpression K) = 1 := (rfl)

theorem valueProd_add (w w' : FormalExpression K) :
    valueProd (w + w') = valueProd w * valueProd w' := by
  rw [valueProd, valueProd, valueProd, Multiset.map_add, Multiset.prod_add]

theorem valueProd_replicate (n : ℕ) (x : SeriesWithOrdinalValueAboveOne K) :
    valueProd (Multiset.replicate n x) = ordinalValue x.1 ^ n := by
  rw [valueProd, Multiset.map_replicate, Multiset.prod_replicate]

theorem eval_add (w w' : FormalExpression K) : eval (w + w') = eval w * eval w' := by
  rw [eval_eq, eval_eq, eval_eq, Multiset.map_add, Multiset.prod_add]

theorem eval_replicate (n : ℕ) (x : SeriesWithOrdinalValueAboveOne K) :
    eval (Multiset.replicate n x) = x.1 ^ n := by
  rw [eval_eq, Multiset.map_replicate, Multiset.prod_replicate]

theorem one_le_valueProd (w : FormalExpression K) : 1 ≤ valueProd w := by
  induction w using Multiset.induction with
  | empty => rw [valueProd_zero]
  | cons a s ih =>
    rw [valueProd, Multiset.map_cons, Multiset.prod_cons, ← valueProd]
    calc (1 : NatOrdinal) = 1 * 1 := (one_mul 1).symm
      _ ≤ ordinalValue a.1 * valueProd s := mul_le_mul' a.2.le ih

theorem one_lt_valueProd {w : FormalExpression K} (hw : w ≠ 0) : 1 < valueProd w := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hw
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [valueProd, Multiset.map_cons, Multiset.prod_cons, ← valueProd]
  calc (1 : NatOrdinal) < ordinalValue a.1 := a.2
    _ = ordinalValue a.1 * 1 := (mul_one _).symm
    _ ≤ ordinalValue a.1 * valueProd s := mul_le_mul' le_rfl (one_le_valueProd s)

open Classical in
/-- Splitting an expression at its selected factor. -/
theorem replicate_selectedExponent_add_unselected (w : FormalExpression K) (hw : w ≠ 0) :
    Multiset.replicate (selectedExponent w hw) (selected w hw) + unselected w hw = w := by
  refine Multiset.ext.mpr fun y ↦ ?_
  rw [Multiset.count_add, unselected_eq, Multiset.count_replicate, Multiset.count_filter]
  by_cases hy : y = selected w hw
  · subst hy
    rw [if_pos rfl, if_neg (fun h ↦ h rfl), add_zero, selectedExponent_eq_count]
  · rw [if_neg (Ne.symm hy), if_pos hy, zero_add]

end FormalExpression

open FormalExpression

/-- Berarducci, Lemma 9.6: the value of a product is the Hessenberg product of the values. -/
theorem ordinalValue_eval [CharZero K] (w : FormalExpression K) :
    ordinalValue (eval w) = valueProd w := by
  suffices h : ∀ p : Multiset Ordinal × ℕ, ∀ (w : FormalExpression K) (hw : w ≠ 0),
      complexity w hw = p → ordinalValue (eval w) = valueProd w by
    rcases eq_or_ne w 0 with rfl | hw
    · rw [eval_zero, valueProd_zero, ordinalValue_one]
    · exact h _ w hw rfl
  refine fun p ↦ wellFounded_complexityLT.induction
    (C := fun q ↦ ∀ (w : FormalExpression K) (hw : w ≠ 0), complexity w hw = q →
      ordinalValue (eval w) = valueProd w) p ?_
  clear p
  intro p ih w hw hp
  classical
  have IH : ∀ w' : FormalExpression K,
      (∀ hw' : w' ≠ 0, ComplexityLT (complexity w' hw') (complexity w hw)) →
      ordinalValue (eval w') = valueProd w' := by
    intro w' hlt
    rcases eq_or_ne w' 0 with rfl | hw'
    · rw [eval_zero, valueProd_zero, ordinalValue_one]
    · exact ih (complexity w' hw') (hp ▸ hlt hw') w' hw' rfl
  set x := selected w hw with hx
  set r := unselected w hw with hrdef
  obtain ⟨m, hm⟩ : ∃ m, selectedExponent w hw = m + 1 :=
    ⟨selectedExponent w hw - 1, by have := one_le_selectedExponent w hw; omega⟩
  have hdecomp : w = Multiset.replicate (m + 1) x + r := by
    rw [hrdef, hx, ← hm, replicate_selectedExponent_add_unselected]
  have heval : eval w = x.1 ^ (m + 1) * eval r := by
    conv_lhs => rw [hdecomp]
    rw [eval_add, eval_replicate]
  have hvp : valueProd w = ordinalValue x.1 ^ (m + 1) * valueProd r := by
    conv_lhs => rw [hdecomp]
    rw [valueProd_add, valueProd_replicate]
  have hr : ordinalValue (eval r) = valueProd r :=
    IH r fun hr0 ↦ complexityLT_unselected hw hr0
  -- the induction hypothesis at the reduced expression, for any admissible truncation factors
  have hIHred : ∀ t : FormalExpression K, (∀ u ∈ t, ordinalValue u.1 < ordinalValue x.1) →
      (∀ u ∈ t, x.principalValue ≤ u.principalValue) →
      ordinalValue (eval t * x.1 ^ m * (eval r * eval r))
        = valueProd t * ordinalValue x.1 ^ m * (valueProd r * valueProd r) := by
    intro t ht htp
    have hred := IH (reduced w hw t) fun hne ↦ complexityLT_reduced w hw t ht htp hne
    rw [reduced_eq, hm, Nat.add_sub_cancel] at hred
    simpa only [eval_add, eval_replicate, valueProd_add, valueProd_replicate] using hred
  -- the eventual hypothesis of Lemma 8.2
  have hkey : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet x →
      ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ * x.1 ^ m * (eval r * eval r))
        = ordinalValue x.1 ^ m * ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ)
            * valueProd r * valueProd r := by
    obtain ⟨η, hη, hlt⟩ := exists_ordinalValue_translatedTruncation_lt x
    rw [eventually_nhdsLT_iff_exists]
    refine ⟨η, hη, fun γ hlow hhigh hγ ↦ ?_⟩
    have hgv : ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ) < ordinalValue x.1 := hlt γ hlow
        hhigh
    by_cases hg1 : 1 < ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ)
    · have h := hIHred {⟨translatedTruncation (x.1 : K⟦ℝ⟧) γ, hg1⟩}
        (fun u hu ↦ by rw [Multiset.mem_singleton.mp hu]; exact hgv)
        (fun u hu ↦ by
          rw [Multiset.mem_singleton.mp hu]
          exact principalValue_le_of_mem_residualPointSet x _ hγ rfl)
      rw [eval_eq, valueProd, Multiset.map_singleton, Multiset.map_singleton,
        Multiset.prod_singleton, Multiset.prod_singleton] at h
      rw [h]
      ring
    · have hone : ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ) = 1 := by
        have hne : ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ) ≠ 0 := by
          rw [(mem_residualPointSet_iff.mp hγ).2]
          exact x.residualValue_ne_zero
        rcases eq_or_lt_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hne)) with h | h
        · exact h.symm
        · exact absurd h hg1
      have h := hIHred 0 (by simp) (by simp)
      rw [eval_zero, valueProd_zero, one_mul, one_mul] at h
      rw [mul_assoc, ordinalValue_mul_of_ordinalValue_eq_one hone, h, hone]
      ring
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- no other factor: the pure-power form of Lemma 8.2
    rw [heval, hvp, hr0, eval_zero, valueProd_zero, mul_one, mul_one]
    refine ordinalValue_pow_eq_of_eventually x m (hkey.mono fun γ hγ hmem ↦ ?_)
    have h := hγ hmem
    simp only [hr0, eval_zero, valueProd_zero, mul_one] at h
    exact h
  · -- at least one other factor: the general form
    have hc1 : 1 < ordinalValue (eval r) := hr ▸ one_lt_valueProd hr0
    set c : SeriesWithOrdinalValueAboveOne K := ⟨eval r, hc1⟩ with hcdef
    have hce : c.1 = eval r := rfl
    have hp' : x.principalValue ≤ c.principalValue :=
      principalValue_le_of_forall_mem x c r
        (fun y hy ↦ (isSelected_selected w hw).min_principalValue y (mem_unselected.mp hy).1)
        (by rw [hce]; exact hr)
    have hev : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet x →
        ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ * x.1 ^ m * c.1 ^ 2)
          = ordinalValue x.1 ^ m * ordinalValue (translatedTruncation (x.1 : K⟦ℝ⟧) γ)
              * ordinalValue c.1 * ordinalValue c.1 := by
      refine hkey.mono fun γ hγ hmem ↦ ?_
      rw [hce, sq, hr]
      exact hγ hmem
    have h82 := ordinalValue_pow_mul_eq_of_eventually x c hp' m hev
    rw [hce] at h82
    rw [heval, hvp, h82, hr]

/-- Berarducci, Theorem 9.7: the ordinal value is multiplicative for the Hessenberg product.
Factors in `J` make both sides zero and factors of value one are deleted from both sides, which
reduces the statement to Lemma 9.6 on a two-factor expression. -/
@[blueprint "fact:ordinal-value-multiplicativity"
  (phase := "Ordinal value and degree")
  (title := "Multiplicative property of the ordinal value (Ber00, Theorem 9.7)")
  (statement := /--
    Let $K$ be a field of characteristic zero. For all
    $b,c\in K((\mathbb R^{\le 0}))$,
    \[
      v_J(bc)=v_J(b)\odot v_J(c).
    \]
  -/)
  (proof := /--
  The cases $v_J(b)=0$, $v_J(c)=0$, $v_J(b)=1$, and $v_J(c)=1$ follow from
  the ideal $J$ and multiplication by a series of ordinal value one.  In the
  remaining case, \ref{fact:ordinal-value-support-tail} bounds every sufficiently high
  proper translated truncation below the value of its factor. Together with
  \ref{lem:convolution-formula}, this supplies
  Berarducci's well-founded induction on finite products of factors of ordinal
  value greater than one. Applying the resulting identity to $b,c$ gives the
  formula.
  -/)]
theorem ordinalValue_mul [CharZero K] (b c : Series K) :
    ordinalValue (b * c) = ordinalValue b * ordinalValue c := by
  rcases eq_or_ne (ordinalValue b) 0 with hb0 | hb0
  · rw [hb0, zero_mul, ordinalValue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ (ordinalValue_eq_zero_iff.mp hb0)
  rcases eq_or_ne (ordinalValue c) 0 with hc0 | hc0
  · rw [hc0, mul_zero, ordinalValue_eq_zero_iff]
    exact Ideal.mul_mem_left _ _ (ordinalValue_eq_zero_iff.mp hc0)
  rcases eq_or_lt_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hb0)) with hb1 | hb1
  · rw [← hb1, one_mul, ordinalValue_mul_of_ordinalValue_eq_one hb1.symm]
  rcases eq_or_lt_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hc0)) with hc1 | hc1
  · rw [← hc1, mul_one, mul_comm b c, ordinalValue_mul_of_ordinalValue_eq_one hc1.symm]
  have h := ordinalValue_eval ({⟨b, hb1⟩, ⟨c, hc1⟩} : FormalExpression K)
  rw [eval_eq, valueProd] at h
  simpa using h

/-- Berarducci, Corollary 9.8: the ideal of infinitesimal series is prime. -/
theorem negativeMonomialIdeal_isPrime [CharZero K] :
    (HahnSeries.Nonpositive.negativeMonomialIdeal K).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨HahnSeries.Nonpositive.negativeMonomialIdeal_ne_top, ?_⟩
  intro b c hbc
  have hzero : ordinalValue b * ordinalValue c = 0 := by
    rw [← ordinalValue_mul, ordinalValue_eq_zero_iff]
    exact hbc
  by_cases hb : ordinalValue b = 0
  · exact Or.inl (ordinalValue_eq_zero_iff.mp hb)
  · right
    apply ordinalValue_eq_zero_iff.mp
    by_contra hc
    have hpos : 0 < ordinalValue b * ordinalValue c :=
      mul_pos (pos_iff_ne_zero.mpr hb) (pos_iff_ne_zero.mpr hc)
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos

/-- Berarducci ordinal-value multiplicativity, imported as LM24, Fact 2.7.1(2). -/
theorem ordinalValueMultiplicative [CharZero K] : OrdinalValueMultiplicative K :=
  OrdinalValueMultiplicative.of_forall ordinalValue_mul

end Berarducci
