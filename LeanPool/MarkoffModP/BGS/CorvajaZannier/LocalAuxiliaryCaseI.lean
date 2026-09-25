/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalAuxiliaryWronskian
public import Mathlib.Algebra.Order.Group.Int.Sum
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Corvaja--Zannier local case (i)

This file formalizes the column elimination and the sharp local Wronskian
estimate in case (i) of Corvaja--Zannier's Proposition 2.  Repeated negative
Laurent orders are eliminated by an explicitly constructed product of
transvections.  Consequently the column matrix has determinant one; the
finite-dimensional elimination is not assumed as a hypothesis.

The second part isolates the exact source inequalities.  Pairwise-distinct
negative column orders give the first triangular-number gain, and distinct
derivative orders give the second.  Under the source's cardinal inequalities
this sharpens the ordinary Wronskian order to
`rhoOrder * (epsilon + 1)`, and hence to `rhoOrder * q` when
`epsilon + 1 ≤ q`.

Source provenance: published pages 1935--1936; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 640--685.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators

open HahnSeries LaurentSeries

variable {K : Type*} [Field K]

/-- The depth of the negative part of a Laurent series. -/
def laurentPoleDepth (f : LaurentSeries K) : ℕ := Int.toNat (-f.order)

/-- A terminating measure for repeated leading-term cancellation. -/
def laurentPoleWeight {k : ℕ} (f : Fin k → LaurentSeries K) : ℕ :=
  ∑ i, laurentPoleDepth (f i)

/-- All negative orders in a finite family are pairwise distinct. -/
def NegativeOrdersPairwiseDistinct {ι : Type*}
    (f : ι → LaurentSeries K) : Prop :=
  ∀ ⦃i j : ι⦄, (f i).order < 0 → (f j).order < 0 →
    (f i).order = (f j).order → i = j

/-- Cancel the leading term of `x` using a series `y` of the same order. -/
def cancelLaurentLeadingTerm (x y : LaurentSeries K) : LaurentSeries K :=
  x - (x.leadingCoeff / y.leadingCoeff) • y

@[simp]
theorem laurentPoleDepth_pos_iff (f : LaurentSeries K) :
    0 < laurentPoleDepth f ↔ f.order < 0 := by
  simp [laurentPoleDepth]

@[simp]
theorem laurentPoleDepth_eq_zero_iff (f : LaurentSeries K) :
    laurentPoleDepth f = 0 ↔ 0 ≤ f.order := by
  simp [laurentPoleDepth, Int.toNat_eq_zero]

/-- Cancellation of equal leading terms strictly raises Laurent order. -/
theorem order_lt_orderTop_cancelLaurentLeadingTerm
    (x y : LaurentSeries K) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : x.order = y.order) :
    (x.order : WithTop ℤ) < (cancelLaurentLeadingTerm x y).orderTop := by
  have hycoeff : y.coeff y.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.2 hy
  have hxcoeff : x.coeff x.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.2 hx
  have hylc : y.leadingCoeff ≠ 0 := by
    simpa [HahnSeries.leadingCoeff_eq] using hycoeff
  have hc : x.leadingCoeff / y.leadingCoeff ≠ 0 := div_ne_zero
    (by simpa [HahnSeries.leadingCoeff_eq] using hxcoeff) hylc
  have hscaled : (x.leadingCoeff / y.leadingCoeff) • y ≠ 0 := smul_ne_zero hc hy
  have hscaledOrder :
      ((x.leadingCoeff / y.leadingCoeff) • y).order = y.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      simp only [HahnSeries.coeff_smul]
      exact mul_ne_zero hc hycoeff
    · exact HahnSeries.le_order_smul _ _ hscaled
  have hscaledTop :
      ((x.leadingCoeff / y.leadingCoeff) • y).orderTop =
        (x.order : WithTop ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hscaled, hscaledOrder, ← horder]
  have hlc :
      ((x.leadingCoeff / y.leadingCoeff) • y).leadingCoeff = x.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, hscaledOrder, HahnSeries.coeff_smul]
    rw [HahnSeries.leadingCoeff_eq]
    simp only [smul_eq_mul]
    rw [← HahnSeries.leadingCoeff_eq (x := y)]
    exact div_mul_cancel₀ _ hylc
  have hxtop : x.orderTop = (x.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hx).symm
  unfold cancelLaurentLeadingTerm
  exact HahnSeries.le_orderTop_of_leadingCoeff_eq hxtop hscaledTop hlc.symm

/-- Leading-term cancellation strictly decreases pole depth. -/
theorem laurentPoleDepth_cancelLaurentLeadingTerm_lt
    (x y : LaurentSeries K) (hxneg : x.order < 0)
    (hyneg : y.order < 0) (horder : x.order = y.order) :
    laurentPoleDepth (cancelLaurentLeadingTerm x y) < laurentPoleDepth x := by
  have hx : x ≠ 0 := by
    intro h
    simp [h] at hxneg
  have hy : y ≠ 0 := by
    intro h
    simp [h] at hyneg
  have hraise := order_lt_orderTop_cancelLaurentLeadingTerm x y hx hy horder
  by_cases hz : cancelLaurentLeadingTerm x y = 0
  · simp [laurentPoleDepth, hz]
    omega
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hraise
    simp only [WithTop.coe_lt_coe] at hraise
    simp [laurentPoleDepth]
    omega

private theorem indexedColumnCombination_transvection_same {k : ℕ}
    (f : Fin k → LaurentSeries K) (i j : Fin k) (c : K) :
    indexedLaurentSeriesColumnCombination f (Matrix.transvection j i c) i =
      f i + c • f j := by
  classical
  simp [indexedLaurentSeriesColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, add_smul, Finset.sum_add_distrib]

private theorem indexedColumnCombination_transvection_ne {k : ℕ}
    (f : Fin k → LaurentSeries K) (i j b : Fin k) (c : K) (hb : b ≠ i) :
    indexedLaurentSeriesColumnCombination f (Matrix.transvection j i c) b =
      f b := by
  classical
  have hib : i ≠ b := Ne.symm hb
  simp [indexedLaurentSeriesColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, hib]

private theorem laurentPoleWeight_transvection_lt {k : ℕ}
    (f : Fin k → LaurentSeries K) (i j : Fin k)
    (hi : (f i).order < 0) (hj : (f j).order < 0)
    (horder : (f i).order = (f j).order) :
    laurentPoleWeight
        (indexedLaurentSeriesColumnCombination f
          (Matrix.transvection j i (-(f i).leadingCoeff / (f j).leadingCoeff))) <
      laurentPoleWeight f := by
  let c : K := -(f i).leadingCoeff / (f j).leadingCoeff
  let g := indexedLaurentSeriesColumnCombination f (Matrix.transvection j i c)
  have hgi : g i = cancelLaurentLeadingTerm (f i) (f j) := by
    change indexedLaurentSeriesColumnCombination f (Matrix.transvection j i c) i = _
    rw [indexedColumnCombination_transvection_same]
    simp only [c, cancelLaurentLeadingTerm, neg_div, neg_smul, sub_eq_add_neg]
  have hstrict : laurentPoleDepth (g i) < laurentPoleDepth (f i) := by
    rw [hgi]
    exact laurentPoleDepth_cancelLaurentLeadingTerm_lt (f i) (f j) hi hj horder
  unfold laurentPoleWeight
  apply Finset.sum_lt_sum
  · intro b _
    by_cases hb : b = i
    · subst b
      exact hstrict.le
    · rw [indexedColumnCombination_transvection_ne f i j b c hb]
  · exact ⟨i, Finset.mem_univ _, hstrict⟩

/-- Successive constant column combinations compose by matrix multiplication. -/
theorem indexedLaurentSeriesColumnCombination_mul {k : ℕ}
    (f : Fin k → LaurentSeries K) (A B : Matrix (Fin k) (Fin k) K) :
    indexedLaurentSeriesColumnCombination
        (indexedLaurentSeriesColumnCombination f A) B =
      indexedLaurentSeriesColumnCombination f (A * B) := by
  classical
  funext b
  simp only [indexedLaurentSeriesColumnCombination, Matrix.mul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (B j b) (A i j)]

private theorem indexedLaurentSeriesColumnCombination_one {k : ℕ}
    (f : Fin k → LaurentSeries K) :
    indexedLaurentSeriesColumnCombination f 1 = f := by
  classical
  funext i
  simp [indexedLaurentSeriesColumnCombination, Matrix.one_apply]

/-- Explicit finite-dimensional elimination of repeated negative orders.
The resulting matrix is a product of transvections and therefore has
determinant one. -/
theorem exists_det_one_columnMatrix_negativeOrdersPairwiseDistinct
    {k : ℕ} (a : ℤ) (ha : a ≤ 0)
    (f : Fin k → LaurentSeries K) (hf : ∀ i, a ≤ (f i).order) :
    ∃ A : Matrix (Fin k) (Fin k) K,
      A.det = 1 ∧
      NegativeOrdersPairwiseDistinct
        (indexedLaurentSeriesColumnCombination f A) ∧
      ∀ i, a ≤ (indexedLaurentSeriesColumnCombination f A i).order := by
  induction hN : laurentPoleWeight f using Nat.strong_induction_on generalizing f with
  | h N ih =>
      by_cases hdistinct : NegativeOrdersPairwiseDistinct f
      · refine ⟨1, Matrix.det_one, ?_, ?_⟩
        · simpa [indexedLaurentSeriesColumnCombination_one]
        · simpa [indexedLaurentSeriesColumnCombination_one] using hf
      · have hdup : ∃ i j : Fin k,
            (f i).order < 0 ∧ (f j).order < 0 ∧
            (f i).order = (f j).order ∧ i ≠ j := by
          simp only [NegativeOrdersPairwiseDistinct] at hdistinct
          push Not at hdistinct
          obtain ⟨i, j, hi, hj, ho, hij⟩ := hdistinct
          exact ⟨i, j, hi, hj, ho, hij⟩
        obtain ⟨i, j, hi, hj, horder, hij⟩ := hdup
        let c : K := -(f i).leadingCoeff / (f j).leadingCoeff
        let T : Matrix (Fin k) (Fin k) K := Matrix.transvection j i c
        let g := indexedLaurentSeriesColumnCombination f T
        have hweight : laurentPoleWeight g < N := by
          rw [← hN]
          exact laurentPoleWeight_transvection_lt f i j hi hj horder
        have hgi : g i = cancelLaurentLeadingTerm (f i) (f j) := by
          change indexedLaurentSeriesColumnCombination f
            (Matrix.transvection j i c) i = _
          rw [indexedColumnCombination_transvection_same]
          simp only [c, cancelLaurentLeadingTerm, neg_div, neg_smul, sub_eq_add_neg]
        have hg : ∀ b, a ≤ (g b).order := by
          intro b
          by_cases hb : b = i
          · subst b
            rw [hgi]
            have hfi : f i ≠ 0 := by
              intro hz
              simp [hz] at hi
            have hfj : f j ≠ 0 := by
              intro hz
              simp [hz] at hj
            have hraise :=
              order_lt_orderTop_cancelLaurentLeadingTerm (f i) (f j) hfi hfj horder
            by_cases hz : cancelLaurentLeadingTerm (f i) (f j) = 0
            · simpa [hz] using ha
            · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hraise
              simp only [WithTop.coe_lt_coe] at hraise
              exact (hf i).trans hraise.le
          · change a ≤ (indexedLaurentSeriesColumnCombination f
                (Matrix.transvection j i c) b).order
            rw [indexedColumnCombination_transvection_ne f i j b c hb]
            exact hf b
        obtain ⟨B, hBdet, hBdistinct, hBlower⟩ := ih _ hweight g hg rfl
        refine ⟨T * B, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, hBdet, mul_one]
          exact Matrix.det_transvection_of_ne j i (Ne.symm hij) c
        · rw [← indexedLaurentSeriesColumnCombination_mul]
          exact hBdistinct
        · rw [← indexedLaurentSeriesColumnCombination_mul]
          exact hBlower

/-- Sharp lower sum bound for distinct integers bounded below. -/
theorem sum_range_add_le_sum_of_injOn {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℤ) (a : ℤ)
    (hinj : Set.InjOn w (s : Set ι)) (hlower : ∀ i ∈ s, a ≤ w i) :
    (∑ n ∈ Finset.range s.card, (a + n : ℤ)) ≤ ∑ i ∈ s, w i := by
  have hcard : (s.image w).card = s.card := Finset.card_image_iff.mpr hinj
  have hbound := Finset.sum_range_le_sum
    (s := s.image w) (c := a) (by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hlower i hi)
  rw [hcard] at hbound
  simpa [Finset.sum_image hinj] using hbound

/-- Sharp upper sum bound for distinct natural numbers bounded above. -/
theorem sum_le_sum_range_sub_of_injOn {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℕ) (epsilon : ℕ)
    (hinj : Set.InjOn e (s : Set ι)) (hupper : ∀ i ∈ s, e i ≤ epsilon) :
    (∑ i ∈ s, (e i : ℤ)) ≤
      ∑ n ∈ Finset.range s.card, ((epsilon : ℤ) - n) := by
  let w : ι → ℤ := fun i => e i
  have hinjw : Set.InjOn w (s : Set ι) := by
    intro i hi j hj hij
    exact hinj hi hj (by simpa [w] using hij)
  have hcard : (s.image w).card = s.card := Finset.card_image_iff.mpr hinjw
  have hbound := Finset.sum_le_sum_range
    (s := s.image w) (c := (epsilon : ℤ)) (by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      change (e i : ℤ) ≤ (epsilon : ℤ)
      exact_mod_cast hupper i hi)
  rw [hcard] at hbound
  simpa [w, Finset.sum_image hinjw] using hbound

private theorem caseI_addVal_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → LaurentSeries K) :
    HahnSeries.addVal ℤ K (∏ i ∈ s, g i) =
      ∑ i ∈ s, HahnSeries.addVal ℤ K (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, AddValuation.map_mul]

private theorem caseI_coe_sum_int_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

/-- The determinant bound in which only pole columns pay a derivative-order
cost; regular columns contribute a nonnegative order. -/
theorem orderTop_indexedWronskian_det_lower_bound_of_poles
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (epsilonOrder : ι → ℕ) (g : ι → LaurentSeries K) (poles : Finset ι)
    (E : ℤ)
    (hregular : ∀ i ∉ poles, 0 ≤ (g i).order)
    (hselected : ∀ σ : Equiv.Perm ι,
      (∑ i ∈ poles, (epsilonOrder (σ i) : ℤ)) ≤ E) :
    ((((∑ i ∈ poles, (g i).order) - E : ℤ)) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian epsilonOrder g).det.orderTop := by
  rw [Matrix.det_apply]
  change ((((∑ i ∈ poles, (g i).order) - E : ℤ)) : WithTop ℤ) ≤
    HahnSeries.addVal ℤ K
      (∑ σ, Equiv.Perm.sign σ •
        ∏ i, indexedLaurentSeriesWronskian epsilonOrder g (σ i) i)
  apply AddValuation.map_le_sum
  intro σ _
  calc
    ((((∑ i ∈ poles, (g i).order) - E : ℤ)) : WithTop ℤ) ≤
        (((∑ i ∈ poles,
          ((g i).order - (epsilonOrder (σ i) : ℤ)) : ℤ)) : WithTop ℤ) := by
      rw [Finset.sum_sub_distrib]
      exact_mod_cast sub_le_sub_left (hselected σ) _
    _ = ∑ i, if i ∈ poles then
          (((g i).order - (epsilonOrder (σ i) : ℤ) : ℤ) : WithTop ℤ)
        else 0 := by
      rw [Finset.sum_ite_mem_eq]
      exact caseI_coe_sum_int_finset poles
        (fun i => (g i).order - (epsilonOrder (σ i) : ℤ))
    _ ≤ ∑ i,
        ((((LaurentSeries.derivative K)^[epsilonOrder (σ i)]) (g i)).orderTop) := by
      gcongr with i
      by_cases hi : i ∈ poles
      · simp only [hi, ite_true]
        exact order_sub_le_orderTop_derivative_iterate (epsilonOrder (σ i)) (g i)
      · simp only [hi, ite_false]
        exact orderTop_derivative_iterate_nonnegative_of_order_nonnegative
          (epsilonOrder (σ i)) (g i) (hregular i hi)
    _ = (∏ i,
        indexedLaurentSeriesWronskian epsilonOrder g (σ i) i).orderTop := by
      rw [← HahnSeries.addVal_apply, caseI_addVal_prod]
      simp only [HahnSeries.addVal_apply]
      rfl
    _ ≤ (Equiv.Perm.sign σ •
        ∏ i, indexedLaurentSeriesWronskian epsilonOrder g (σ i) i).orderTop := by
      exact orderTop_le_orderTop_smul _ _

private theorem sum_range_int_mul_two (r : ℕ) :
    (∑ n ∈ Finset.range r, (n : ℤ)) * 2 =
      (r : ℤ) * (r - 1 : ℕ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (Finset.sum_range_id_mul_two r)
  push_cast at h
  exact h

private theorem int_natCast_mul_pred (r : ℕ) :
    (r : ℤ) * (r - 1 : ℕ) = (r : ℤ) * ((r : ℤ) - 1) := by
  cases r <;> simp

/-- The exact intermediate bound in source case (i). -/
theorem orderTop_indexedWronskian_det_caseI_epsilon_plus_one_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (epsilonOrder : ι → ℕ) (g : ι → LaurentSeries K)
    (rhoOrder : ℤ) (epsilon : ℕ)
    (hgdistinct : NegativeOrdersPairwiseDistinct g)
    (hglower : ∀ i, rhoOrder ≤ (g i).order)
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hcardRho : rhoOrder ≤
      -((Finset.univ.filter fun i => (g i).order < 0).card : ℤ))
    (hcardEpsilon :
      (Finset.univ.filter fun i => (g i).order < 0).card ≤ epsilon + 1) :
    ((rhoOrder * (epsilon + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian epsilonOrder g).det.orderTop := by
  let poles : Finset ι := Finset.univ.filter fun i => (g i).order < 0
  let E : ℤ := ∑ n ∈ Finset.range poles.card, ((epsilon : ℤ) - n)
  have horderInj : Set.InjOn (fun i => (g i).order) (poles : Set ι) := by
    intro i hi j hj hij
    apply hgdistinct
    · simpa [poles] using hi
    · simpa [poles] using hj
    · exact hij
  have hpoleLower :
      (∑ n ∈ Finset.range poles.card, (rhoOrder + n : ℤ)) ≤
        ∑ i ∈ poles, (g i).order :=
    sum_range_add_le_sum_of_injOn poles (fun i => (g i).order) rhoOrder
      horderInj (fun i _ => hglower i)
  have hselected : ∀ σ : Equiv.Perm ι,
      (∑ i ∈ poles, (epsilonOrder (σ i) : ℤ)) ≤ E := by
    intro σ
    apply sum_le_sum_range_sub_of_injOn poles (fun i => epsilonOrder (σ i)) epsilon
    · intro i hi j hj hij
      exact σ.injective (hepsilonInjective hij)
    · intro i _
      exact hepsilonMax (σ i)
  have hregular : ∀ i ∉ poles, 0 ≤ (g i).order := by
    intro i hi
    simp only [poles, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  have hW := orderTop_indexedWronskian_det_lower_bound_of_poles
    epsilonOrder g poles E hregular hselected
  apply le_trans ?_ hW
  norm_cast
  have hcardRho' : rhoOrder ≤ -(poles.card : ℤ) := by
    simpa [poles] using hcardRho
  have hcardEpsilon' : poles.card ≤ epsilon + 1 := by
    simpa [poles] using hcardEpsilon
  let S : ℤ := ∑ n ∈ Finset.range poles.card, (n : ℤ)
  have htri : S * 2 = (poles.card : ℤ) * (poles.card - 1 : ℕ) := by
    exact sum_range_int_mul_two poles.card
  have htri' : S * 2 = (poles.card : ℤ) * ((poles.card : ℤ) - 1) :=
    htri.trans (int_natCast_mul_pred poles.card)
  have hpoleRange :
      (∑ n ∈ Finset.range poles.card, (rhoOrder + n : ℤ)) =
        (poles.card : ℤ) * rhoOrder + S := by
    rw [Finset.sum_add_distrib]
    simp [S, mul_comm]
  have hcostRange : E =
      (poles.card : ℤ) * epsilon - S := by
    change (∑ n ∈ Finset.range poles.card, ((epsilon : ℤ) - n)) = _
    rw [Finset.sum_sub_distrib]
    simp [S, mul_comm]
  have hgapEpsilon :
      0 ≤ (epsilon + 1 : ℤ) - (poles.card : ℤ) := by
    have hcast : (poles.card : ℤ) ≤ (epsilon + 1 : ℕ) := by
      exact_mod_cast hcardEpsilon'
    omega
  have hgapRho : 0 ≤ -rhoOrder - (poles.card : ℤ) := by omega
  have hgapProduct :
      0 ≤ ((epsilon + 1 : ℤ) - (poles.card : ℤ)) *
        (-rhoOrder - (poles.card : ℤ)) :=
    mul_nonneg hgapEpsilon hgapRho
  calc
    rhoOrder * (epsilon + 1 : ℕ) ≤
        (∑ n ∈ Finset.range poles.card, (rhoOrder + n : ℤ)) - E := by
      rw [hpoleRange, hcostRange]
      push_cast
      nlinarith
    _ ≤ (∑ i ∈ poles, (g i).order) - E := sub_le_sub_right hpoleLower E

/-- Source case (i), in the final `q * rhoOrder` form. -/
theorem orderTop_indexedWronskian_det_caseI_q_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (epsilonOrder : ι → ℕ) (g : ι → LaurentSeries K)
    (rhoOrder : ℤ) (epsilon q : ℕ)
    (hgdistinct : NegativeOrdersPairwiseDistinct g)
    (hglower : ∀ i, rhoOrder ≤ (g i).order)
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hcardRho : rhoOrder ≤
      -((Finset.univ.filter fun i => (g i).order < 0).card : ℤ))
    (hcardEpsilon :
      (Finset.univ.filter fun i => (g i).order < 0).card ≤ epsilon + 1)
    (hrho : rhoOrder ≤ 0) (hepsilonQ : epsilon + 1 ≤ q) :
    (((q : ℤ) * rhoOrder : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian epsilonOrder g).det.orderTop := by
  apply le_trans ?_
    (orderTop_indexedWronskian_det_caseI_epsilon_plus_one_lower_bound
      epsilonOrder g rhoOrder epsilon hgdistinct hglower hepsilonInjective
      hepsilonMax hcardRho hcardEpsilon)
  norm_cast
  have hepsilonQ' : (epsilon + 1 : ℤ) ≤ q := by exact_mod_cast hepsilonQ
  calc
    (q : ℤ) * rhoOrder ≤ (epsilon + 1 : ℤ) * rhoOrder :=
      mul_le_mul_of_nonpos_right hepsilonQ' hrho
    _ = rhoOrder * (epsilon + 1 : ℕ) := by push_cast; ring

/-- Pairwise-distinct negative integers bounded below by a nonpositive integer
are no more numerous than its pole depth. -/
theorem card_negativeOrders_le_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → LaurentSeries K) (a : ℤ) (ha : a ≤ 0)
    (hgdistinct : NegativeOrdersPairwiseDistinct g)
    (hglower : ∀ i, a ≤ (g i).order) :
    a ≤ -((Finset.univ.filter fun i => (g i).order < 0).card : ℤ) := by
  let poles : Finset ι := Finset.univ.filter fun i => (g i).order < 0
  let w : ι → ℤ := fun i => (g i).order
  have hinj : Set.InjOn w (poles : Set ι) := by
    intro i hi j hj hij
    apply hgdistinct
    · simpa [poles] using hi
    · simpa [poles] using hj
    · exact hij
  have hsubset : poles.image w ⊆ Finset.Ico a 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_Ico]
    exact ⟨hglower i, by simpa [poles] using hi⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_iff.mpr hinj, Int.card_Ico] at hcard
  have hcard' : poles.card ≤ Int.toNat (-a) := by simpa using hcard
  have hcast : (poles.card : ℤ) ≤ Int.toNat (-a) := by
    exact_mod_cast hcard'
  have htoNat : (Int.toNat (-a) : ℤ) = -a := by
    rw [Int.toNat_of_nonneg]
    omega
  rw [htoNat] at hcast
  simpa [poles] using (show a ≤ -(poles.card : ℤ) by omega)

/-- Complete local case (i) for an arbitrary `Fin k` family.  The theorem
constructs the determinant-one elimination matrix, preserves the original
Wronskian determinant, and proves the final `q * a` order bound. -/
theorem exists_caseI_columnMatrix_and_q_wronskian_bound
    {k : ℕ} (epsilonOrder : Fin k → ℕ)
    (f : Fin k → LaurentSeries K) (a : ℤ) (epsilon q : ℕ)
    (ha : a ≤ 0) (hf : ∀ i, a ≤ (f i).order)
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) K,
      A.det = 1 ∧
      (indexedLaurentSeriesWronskian epsilonOrder
        (indexedLaurentSeriesColumnCombination f A)).det =
          (indexedLaurentSeriesWronskian epsilonOrder f).det ∧
      (((q : ℤ) * a : ℤ) : WithTop ℤ) ≤
        (indexedLaurentSeriesWronskian epsilonOrder f).det.orderTop := by
  obtain ⟨A, hAdet, hdistinct, hlower⟩ :=
    exists_det_one_columnMatrix_negativeOrdersPairwiseDistinct a ha f hf
  let g := indexedLaurentSeriesColumnCombination f A
  have hdet :
      (indexedLaurentSeriesWronskian epsilonOrder g).det =
        (indexedLaurentSeriesWronskian epsilonOrder f).det := by
    exact indexedLaurentSeriesWronskian_det_columnCombination_of_det_eq_one
      epsilonOrder f A hAdet
  have hcardRho :
      a ≤ -((Finset.univ.filter fun i => (g i).order < 0).card : ℤ) :=
    card_negativeOrders_le_neg g a ha hdistinct hlower
  have hcardEpsilon :
      (Finset.univ.filter fun i => (g i).order < 0).card ≤ epsilon + 1 := by
    calc
      (Finset.univ.filter fun i => (g i).order < 0).card ≤
          (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
      _ = k := Fintype.card_fin k
      _ ≤ epsilon + 1 := hk
  have hbound := orderTop_indexedWronskian_det_caseI_q_lower_bound
    epsilonOrder g a epsilon q hdistinct hlower hepsilonInjective hepsilonMax
      hcardRho hcardEpsilon ha hepsilonQ
  refine ⟨A, hAdet, hdet, ?_⟩
  rw [← hdet]
  exact hbound

/-- Extend a first-block column operation by the identity on the grid columns
of the source auxiliary family. -/
def caseIColumnMatrix (h k : ℕ) (A : Matrix (Fin k) (Fin k) K) :
    Matrix (Sum (Fin k) (Fin (k + 1) × Fin h))
      (Sum (Fin k) (Fin (k + 1) × Fin h)) K :=
  Matrix.fromBlocks A 0 0 1

theorem caseIColumnMatrix_det (h k : ℕ) (A : Matrix (Fin k) (Fin k) K) :
    (caseIColumnMatrix (K := K) h k A).det = A.det := by
  rw [caseIColumnMatrix, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem indexedColumnCombination_caseIColumnMatrix_inl
    (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → LaurentSeries K)
    (A : Matrix (Fin k) (Fin k) K) (i : Fin k) :
    indexedLaurentSeriesColumnCombination f (caseIColumnMatrix h k A) (Sum.inl i) =
      indexedLaurentSeriesColumnCombination (fun j => f (Sum.inl j)) A i := by
  classical
  rw [indexedLaurentSeriesColumnCombination, Fintype.sum_sum_type]
  simp [caseIColumnMatrix, indexedLaurentSeriesColumnCombination]

theorem indexedColumnCombination_caseIColumnMatrix_inr
    (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → LaurentSeries K)
    (A : Matrix (Fin k) (Fin k) K) (rs : Fin (k + 1) × Fin h) :
    indexedLaurentSeriesColumnCombination f (caseIColumnMatrix h k A) (Sum.inr rs) =
      f (Sum.inr rs) := by
  classical
  rw [indexedLaurentSeriesColumnCombination, Fintype.sum_sum_type]
  simp [caseIColumnMatrix, Matrix.one_apply]

/-- The full auxiliary family after a case-(i) operation on its first block. -/
def caseITransformedLocalAuxiliaryFamily
    (u v rho : LaurentSeries K) (h k : ℕ) (A : Matrix (Fin k) (Fin k) K) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → LaurentSeries K :=
  indexedLaurentSeriesColumnCombination (localAuxiliaryFamily u v rho h k)
    (caseIColumnMatrix h k A)

@[simp]
theorem caseITransformedLocalAuxiliaryFamily_inl
    (u v rho : LaurentSeries K) (h k : ℕ)
    (A : Matrix (Fin k) (Fin k) K) (i : Fin k) :
    caseITransformedLocalAuxiliaryFamily u v rho h k A (Sum.inl i) =
      indexedLaurentSeriesColumnCombination
        (fun j => localAuxiliaryFamily u v rho h k (Sum.inl j)) A i :=
  indexedColumnCombination_caseIColumnMatrix_inl h k
    (localAuxiliaryFamily u v rho h k) A i

@[simp]
theorem caseITransformedLocalAuxiliaryFamily_inr
    (u v rho : LaurentSeries K) (h k : ℕ)
    (A : Matrix (Fin k) (Fin k) K) (rs : Fin (k + 1) × Fin h) :
    caseITransformedLocalAuxiliaryFamily u v rho h k A (Sum.inr rs) =
      localAuxiliaryFamily u v rho h k (Sum.inr rs) :=
  indexedColumnCombination_caseIColumnMatrix_inr h k
    (localAuxiliaryFamily u v rho h k) A rs

/-- The exact source-facing case-(i) result for `localAuxiliaryFamily`.
Only the first `k` columns can have poles; the constructed block matrix
eliminates their repeated negative orders and fixes every grid column. -/
theorem exists_localAuxiliaryFamily_caseI_columnMatrix
    (u v rho : LaurentSeries K) (h k : ℕ)
    (hu : u ≠ 0) (hrhoNe : rho ≠ 0)
    (huOrder : u.order = 0) (hrhoOrder : rho.order ≤ 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      0 ≤ (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order) :
    ∃ A : Matrix (Fin k) (Fin k) K,
      A.det = 1 ∧
      NegativeOrdersPairwiseDistinct
        (caseITransformedLocalAuxiliaryFamily u v rho h k A) ∧
      (∀ i, rho.order ≤
        (caseITransformedLocalAuxiliaryFamily u v rho h k A i).order) ∧
      (∀ rs, caseITransformedLocalAuxiliaryFamily u v rho h k A (Sum.inr rs) =
        localAuxiliaryFamily u v rho h k (Sum.inr rs)) := by
  let first : Fin k → LaurentSeries K :=
    fun i => localAuxiliaryFamily u v rho h k (Sum.inl i)
  have hfirstOrder : ∀ i, (first i).order = rho.order := by
    intro i
    simp only [first, localAuxiliaryFamily]
    rw [HahnSeries.order_mul (pow_ne_zero _ hu) hrhoNe, HahnSeries.order_pow,
      huOrder]
    simp
  have hfirstLower : ∀ i, rho.order ≤ (first i).order := by
    intro i
    rw [hfirstOrder i]
  obtain ⟨A, hAdet, hdistinct, hlower⟩ :=
    exists_det_one_columnMatrix_negativeOrdersPairwiseDistinct
      rho.order hrhoOrder first hfirstLower
  refine ⟨A, hAdet, ?_, ?_, ?_⟩
  · intro x y hx hy hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            apply congrArg Sum.inl
            apply hdistinct
            · simpa [first] using hx
            · simpa [first] using hy
            · simpa [first] using hxy
        | inr rs =>
            rw [caseITransformedLocalAuxiliaryFamily_inr] at hy
            exact (not_lt_of_ge (hgridRegular rs)) hy |>.elim
    | inr rs =>
        rw [caseITransformedLocalAuxiliaryFamily_inr] at hx
        exact (not_lt_of_ge (hgridRegular rs)) hx |>.elim
  · intro i
    cases i with
    | inl j =>
        simpa [first] using hlower j
    | inr rs =>
        rw [caseITransformedLocalAuxiliaryFamily_inr]
        exact hrhoOrder.trans (hgridRegular rs)
  · intro rs
    exact caseITransformedLocalAuxiliaryFamily_inr u v rho h k A rs

/-- Full source case (i) for the exact Sum-indexed auxiliary family: the
first-block elimination preserves the original Wronskian determinant and
gives the `q * order rho` lower bound. -/
theorem exists_localAuxiliaryFamily_caseI_q_wronskian_bound
    (u v rho : LaurentSeries K) (h k : ℕ)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (epsilon q : ℕ)
    (hu : u ≠ 0) (hrhoNe : rho ≠ 0)
    (huOrder : u.order = 0) (hrhoOrder : rho.order ≤ 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      0 ≤ (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order)
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) K,
      A.det = 1 ∧
      (indexedLaurentSeriesWronskian epsilonOrder
        (caseITransformedLocalAuxiliaryFamily u v rho h k A)).det =
          (indexedLaurentSeriesWronskian epsilonOrder
            (localAuxiliaryFamily u v rho h k)).det ∧
      (((q : ℤ) * rho.order : ℤ) : WithTop ℤ) ≤
        (indexedLaurentSeriesWronskian epsilonOrder
          (localAuxiliaryFamily u v rho h k)).det.orderTop := by
  obtain ⟨A, hAdet, hdistinct, hlower, hgrid⟩ :=
    exists_localAuxiliaryFamily_caseI_columnMatrix
      u v rho h k hu hrhoNe huOrder hrhoOrder hgridRegular
  let f := localAuxiliaryFamily u v rho h k
  let B := caseIColumnMatrix h k A
  let g := caseITransformedLocalAuxiliaryFamily u v rho h k A
  have hBdet : B.det = 1 := by
    rw [caseIColumnMatrix_det, hAdet]
  have hdet :
      (indexedLaurentSeriesWronskian epsilonOrder g).det =
        (indexedLaurentSeriesWronskian epsilonOrder f).det := by
    exact indexedLaurentSeriesWronskian_det_columnCombination_of_det_eq_one
      epsilonOrder f B hBdet
  have hcardRho :
      rho.order ≤ -((Finset.univ.filter fun i => (g i).order < 0).card : ℤ) :=
    card_negativeOrders_le_neg g rho.order hrhoOrder hdistinct hlower
  let firstPoles : Finset (Fin k) := Finset.univ.filter fun i =>
    (g (Sum.inl i)).order < 0
  have hpoles :
      (Finset.univ.filter fun i => (g i).order < 0) =
        firstPoles.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    cases x with
    | inl i => simp [firstPoles]
    | inr rs =>
        have hregg : 0 ≤ (g (Sum.inr rs)).order := by
          change 0 ≤ (caseITransformedLocalAuxiliaryFamily u v rho h k A
            (Sum.inr rs)).order
          rw [hgrid rs]
          simpa [localAuxiliaryFamily] using hgridRegular rs
        have hrs : ¬(g (Sum.inr rs)).order < 0 :=
          not_lt_of_ge hregg
        simp [firstPoles, hrs]
  have hcardEpsilon :
      (Finset.univ.filter fun i => (g i).order < 0).card ≤ epsilon + 1 := by
    rw [hpoles, Finset.card_map]
    exact (Finset.card_filter_le _ _).trans (by simpa using hk)
  have hbound := orderTop_indexedWronskian_det_caseI_q_lower_bound
    epsilonOrder g rho.order epsilon q hdistinct hlower hepsilonInjective
      hepsilonMax hcardRho hcardEpsilon hrhoOrder hepsilonQ
  refine ⟨A, hAdet, ?_, ?_⟩
  · exact hdet
  · rw [← hdet]
    exact hbound

/-- The same case-(i) endpoint for the source `auxiliaryFamily`, obtained by
specializing `rho = (1-u)/(1-v)`. -/
theorem exists_auxiliaryFamily_caseI_q_wronskian_bound
    (u v : LaurentSeries K) (h k : ℕ)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (epsilon q : ℕ)
    (hu : u ≠ 0) (hrhoNe : (1 - u) / (1 - v) ≠ 0)
    (huOrder : u.order = 0) (hrhoOrder : ((1 - u) / (1 - v)).order ≤ 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      0 ≤ (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order)
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) K,
      A.det = 1 ∧
      (indexedLaurentSeriesWronskian epsilonOrder
        (indexedLaurentSeriesColumnCombination (auxiliaryFamily u v h k)
          (caseIColumnMatrix h k A))).det =
          (indexedLaurentSeriesWronskian epsilonOrder
            (auxiliaryFamily u v h k)).det ∧
      (((q : ℤ) * ((1 - u) / (1 - v)).order : ℤ) : WithTop ℤ) ≤
        (indexedLaurentSeriesWronskian epsilonOrder
          (auxiliaryFamily u v h k)).det.orderTop := by
  simpa only [caseITransformedLocalAuxiliaryFamily,
    localAuxiliaryFamily_div_eq_auxiliaryFamily] using
    (exists_localAuxiliaryFamily_caseI_q_wronskian_bound
      u v ((1 - u) / (1 - v)) h k epsilonOrder epsilon q hu hrhoNe
      huOrder hrhoOrder hgridRegular hepsilonInjective hepsilonMax hk hepsilonQ)

end

end BGS.CorvajaZannier
