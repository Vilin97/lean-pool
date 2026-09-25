/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindAuxiliaryWronskian
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLeadingTermCancellation
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalAuxiliaryCaseI
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Corvaja--Zannier case (i) at a Dedekind DVR place

This file transports the repeated-leading-term cancellation argument of
Corvaja--Zannier's local case (i) from Laurent series to the fraction field of
a discrete valuation ring.  Constants are assumed to surject onto the residue
field.  This is precisely the input needed to cancel equal-order leading
terms; no coefficient field or completion is chosen.

The Wronskian estimate only assumes that the derivation preserves the DVR.
In particular, a column of nonnegative order and every one of its iterated
derivatives remain regular.  Combining this with determinant-one elimination
gives the source bound `q * ord(rho)` for the full auxiliary family.

Source provenance: published pages 1935--1936; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 640--685.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators
open IsDedekindDomain Multiplicative WithZero

variable {C R L : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [IsDiscreteValuationRing R] [Field L] [Algebra C R] [Algebra R L]
  [Algebra C L] [IsScalarTower C R L] [IsFractionRing R L]

/-- The depth of the pole of `x` at `v`; zero has pole depth zero. -/
def dedekindPoleDepth (v : HeightOneSpectrum R) (x : L) : ℕ :=
  by
    classical
    exact if x = 0 then 0 else Int.toNat (-finitePlaceOrder v x)

/-- A terminating measure for repeated leading-term cancellation. -/
def dedekindPoleWeight {k : ℕ} (v : HeightOneSpectrum R) (f : Fin k → L) : ℕ :=
  ∑ i, dedekindPoleDepth v (f i)

omit [IsDiscreteValuationRing R] in
@[simp]
theorem dedekindPoleDepth_zero (v : HeightOneSpectrum R) :
    dedekindPoleDepth (L := L) v 0 = 0 := by
  simp [dedekindPoleDepth]

/-- All negative finite-place orders in a family are pairwise distinct. -/
def NegativeFinitePlaceOrdersPairwiseDistinct {ι : Type*}
    (v : HeightOneSpectrum R) (f : ι → L) : Prop :=
  ∀ ⦃i j : ι⦄, finitePlaceOrderTop v (f i) < 0 →
    finitePlaceOrderTop v (f j) < 0 →
    finitePlaceOrderTop v (f i) = finitePlaceOrderTop v (f j) → i = j

omit [IsDiscreteValuationRing R] in
@[simp]
theorem dedekindPoleDepth_pos_iff (v : HeightOneSpectrum R) (x : L) :
    0 < dedekindPoleDepth v x ↔ finitePlaceOrderTop v x < 0 := by
  by_cases hx : x = 0
  · subst x
    simp [dedekindPoleDepth]
  · rw [finitePlaceOrderTop_eq_coe v x hx]
    simp [dedekindPoleDepth, hx]

omit [IsDiscreteValuationRing R] in
@[simp]
theorem dedekindPoleDepth_eq_zero_iff (v : HeightOneSpectrum R) (x : L) :
    dedekindPoleDepth v x = 0 ↔ 0 ≤ finitePlaceOrderTop v x := by
  by_cases hx : x = 0
  · subst x
    simp [dedekindPoleDepth]
  · rw [finitePlaceOrderTop_eq_coe v x hx]
    simp [dedekindPoleDepth, hx, Int.toNat_eq_zero]

/-- Equal negative orders have a constant cancellation which strictly lowers
the pole-depth measure. -/
theorem exists_constant_dedekindPoleDepth_sub_mul_lt
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (x y : L)
    (hxneg : finitePlaceOrderTop v x < 0)
    (hyneg : finitePlaceOrderTop v y < 0)
    (horder : finitePlaceOrderTop v x = finitePlaceOrderTop v y) :
    ∃ c : C,
      dedekindPoleDepth v (x - algebraMap C L c * y) <
        dedekindPoleDepth v x ∧
      finitePlaceOrderTop v x <
        finitePlaceOrderTop v (x - algebraMap C L c * y) := by
  have hx : x ≠ 0 := by
    intro h
    subst x
    simp at hxneg
  have hy : y ≠ 0 := by
    intro h
    subst y
    simp at hyneg
  have horder' : finitePlaceOrder v x = finitePlaceOrder v y := by
    rw [finitePlaceOrderTop_eq_coe v x hx,
      finitePlaceOrderTop_eq_coe v y hy] at horder
    exact_mod_cast horder
  obtain ⟨c, hz | hlt⟩ :=
    exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt
      v hresidue x y hx hy horder'
  · refine ⟨c, ?_, ?_⟩
    · rw [hz]
      have hxdepth : 0 < dedekindPoleDepth v x :=
        (dedekindPoleDepth_pos_iff v x).2 hxneg
      simpa only [dedekindPoleDepth_zero] using hxdepth
    · rw [hz, finitePlaceOrderTop_eq_coe v x hx]
      simp
  · by_cases hz : x - algebraMap C L c * y = 0
    · refine ⟨c, ?_, ?_⟩
      · rw [hz]
        have hxdepth : 0 < dedekindPoleDepth v x :=
          (dedekindPoleDepth_pos_iff v x).2 hxneg
        simpa only [dedekindPoleDepth_zero] using hxdepth
      · rw [hz, finitePlaceOrderTop_eq_coe v x hx]
        simp
    · refine ⟨c, ?_, ?_⟩
      · simp only [dedekindPoleDepth, hx, hz, ite_false]
        have hxorderneg : finitePlaceOrder v x < 0 := by
          rw [finitePlaceOrderTop_eq_coe v x hx] at hxneg
          exact_mod_cast hxneg
        omega
      · rw [finitePlaceOrderTop_eq_coe v x hx,
          finitePlaceOrderTop_eq_coe v _ hz]
        exact_mod_cast hlt

private theorem indexedDedekindLocalColumnCombination_transvection_same
    {k : ℕ} (f : Fin k → L) (i j : Fin k) (c : C) :
    indexedDedekindLocalColumnCombination f (Matrix.transvection j i c) i =
      f i + c • f j := by
  classical
  simp [indexedDedekindLocalColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, add_smul, Finset.sum_add_distrib]

private theorem indexedDedekindLocalColumnCombination_transvection_ne
    {k : ℕ} (f : Fin k → L) (i j b : Fin k) (c : C) (hb : b ≠ i) :
    indexedDedekindLocalColumnCombination f (Matrix.transvection j i c) b =
      f b := by
  classical
  have hib : i ≠ b := Ne.symm hb
  simp [indexedDedekindLocalColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, hib]

private theorem exists_dedekindPoleWeight_transvection_lt
    {k : ℕ} (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (f : Fin k → L) (i j : Fin k)
    (hi : finitePlaceOrderTop v (f i) < 0)
    (hj : finitePlaceOrderTop v (f j) < 0)
    (horder : finitePlaceOrderTop v (f i) = finitePlaceOrderTop v (f j)) :
    ∃ c : C,
      dedekindPoleWeight v
          (indexedDedekindLocalColumnCombination f
            (Matrix.transvection j i (-c))) <
        dedekindPoleWeight v f ∧
      finitePlaceOrderTop v (f i) <
        finitePlaceOrderTop v (f i - algebraMap C L c * f j) := by
  obtain ⟨c, hstrict, hraise⟩ :=
    exists_constant_dedekindPoleDepth_sub_mul_lt
      v hresidue (f i) (f j) hi hj horder
  refine ⟨c, ?_, hraise⟩
  unfold dedekindPoleWeight
  apply Finset.sum_lt_sum
  · intro b _
    by_cases hb : b = i
    · subst b
      rw [indexedDedekindLocalColumnCombination_transvection_same]
      simpa only [Algebra.smul_def, map_neg, sub_eq_add_neg, neg_mul] using hstrict.le
    · rw [indexedDedekindLocalColumnCombination_transvection_ne f i j b (-c) hb]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [indexedDedekindLocalColumnCombination_transvection_same]
    simpa only [Algebra.smul_def, map_neg, sub_eq_add_neg, neg_mul] using hstrict

/-- Successive constant column combinations compose by matrix
multiplication. -/
theorem indexedDedekindLocalColumnCombination_mul {k : ℕ}
    (f : Fin k → L) (A B : Matrix (Fin k) (Fin k) C) :
    indexedDedekindLocalColumnCombination
        (indexedDedekindLocalColumnCombination f A) B =
      indexedDedekindLocalColumnCombination f (A * B) := by
  classical
  funext b
  simp only [indexedDedekindLocalColumnCombination, Matrix.mul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (B j b) (A i j)]

private theorem indexedDedekindLocalColumnCombination_one {k : ℕ}
    (f : Fin k → L) :
    indexedDedekindLocalColumnCombination f
      (1 : Matrix (Fin k) (Fin k) C) = f := by
  classical
  funext i
  simp [indexedDedekindLocalColumnCombination, Matrix.one_apply]

/-- Repeated equal negative orders can be eliminated by a determinant-one
constant matrix, while preserving a common lower order bound. -/
theorem exists_det_one_dedekindColumnMatrix_negativeOrdersPairwiseDistinct
    {k : ℕ} (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (a : ℤ) (f : Fin k → L)
    (hf : ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (f i)) :
    ∃ A : Matrix (Fin k) (Fin k) C,
      A.det = 1 ∧
      NegativeFinitePlaceOrdersPairwiseDistinct v
        (indexedDedekindLocalColumnCombination f A) ∧
      ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v
        (indexedDedekindLocalColumnCombination f A i) := by
  induction hN : dedekindPoleWeight v f using Nat.strong_induction_on
      generalizing f with
  | h N ih =>
      by_cases hdistinct : NegativeFinitePlaceOrdersPairwiseDistinct v f
      · refine ⟨(1 : Matrix (Fin k) (Fin k) C), Matrix.det_one, ?_, ?_⟩
        · simpa [indexedDedekindLocalColumnCombination_one]
        · simpa [indexedDedekindLocalColumnCombination_one] using hf
      · have hdup : ∃ i j : Fin k,
            finitePlaceOrderTop v (f i) < 0 ∧
            finitePlaceOrderTop v (f j) < 0 ∧
            finitePlaceOrderTop v (f i) = finitePlaceOrderTop v (f j) ∧
            i ≠ j := by
          simp only [NegativeFinitePlaceOrdersPairwiseDistinct] at hdistinct
          push Not at hdistinct
          obtain ⟨i, j, hi, hj, ho, hij⟩ := hdistinct
          exact ⟨i, j, hi, hj, ho, hij⟩
        obtain ⟨i, j, hi, hj, horder, hij⟩ := hdup
        obtain ⟨c, hweight', hraise⟩ :=
          exists_dedekindPoleWeight_transvection_lt
            v hresidue f i j hi hj horder
        let T : Matrix (Fin k) (Fin k) C := Matrix.transvection j i (-c)
        let g := indexedDedekindLocalColumnCombination f T
        have hweight : dedekindPoleWeight v g < N := by
          rw [← hN]
          exact hweight'
        have hgi : g i = f i - algebraMap C L c * f j := by
          change indexedDedekindLocalColumnCombination f
            (Matrix.transvection j i (-c)) i = _
          rw [indexedDedekindLocalColumnCombination_transvection_same]
          simp only [Algebra.smul_def, map_neg, neg_mul, sub_eq_add_neg]
        have hg : ∀ b, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (g b) := by
          intro b
          by_cases hb : b = i
          · subst b
            rw [hgi]
            exact (hf i).trans hraise.le
          · change (a : WithTop ℤ) ≤ finitePlaceOrderTop v
                (indexedDedekindLocalColumnCombination f
                  (Matrix.transvection j i (-c)) b)
            rw [indexedDedekindLocalColumnCombination_transvection_ne f i j b (-c) hb]
            exact hf b
        obtain ⟨B, hBdet, hBdistinct, hBlower⟩ := ih _ hweight g hg rfl
        refine ⟨T * B, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, hBdet, mul_one]
          exact Matrix.det_transvection_of_ne j i (Ne.symm hij) (-c)
        · rw [← indexedDedekindLocalColumnCombination_mul]
          exact hBdistinct
        · rw [← indexedDedekindLocalColumnCombination_mul]
          exact hBlower

omit [Algebra C R] [IsScalarTower C R L] in
/-- A DVR-preserving derivation and all of its iterates preserve the
nonnegative-order part of the fraction field. -/
theorem finitePlaceOrderTop_derivation_iterate_nonnegative_of_nonnegative
    (v : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (m : ℕ) (x : L) (hx : (0 : WithTop ℤ) ≤ finitePlaceOrderTop v x) :
    (0 : WithTop ℤ) ≤
      finitePlaceOrderTop v (((D : L → L)^[m]) x) := by
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : v.asIdeal = Ideal.span {π} := by
    calc
      v.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal v.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨n, u, hxu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hx0
  have hxrepr :
      x = algebraMap R L (u : R) * (algebraMap R L π) ^ n := by
    simpa [Units.smul_def, Algebra.smul_def] using hxu
  have hxOrder : finitePlaceOrder v x = n := by
    rw [hxrepr]
    exact finitePlaceOrder_unit_mul_uniformizer_zpow
      v π hπ hπIdeal u n
  have hn : 0 ≤ n := by
    rw [finitePlaceOrderTop_eq_coe v x hx0, hxOrder] at hx
    exact_mod_cast hx
  let x0 : R := (u : R) * π ^ n.toNat
  have hxMap : x = algebraMap R L x0 := by
    rw [hxrepr]
    change algebraMap R L (u : R) * (algebraMap R L π) ^ n =
      algebraMap R L ((u : R) * π ^ n.toNat)
    rw [map_mul, map_pow]
    congr 1
    calc
      (algebraMap R L π) ^ n =
          (algebraMap R L π) ^ (n.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hn]
      _ = (algebraMap R L π) ^ n.toNat := zpow_natCast _ _
  have hiter : ∀ r : ℕ, ∃ s : R,
      ((D : L → L)^[r]) x = algebraMap R L s := by
    intro r
    induction r with
    | zero => exact ⟨x0, by simpa using hxMap⟩
    | succ r ih =>
        rw [Function.iterate_succ_apply']
        obtain ⟨s, hs⟩ := ih
        rw [hs]
        exact hDIntegral s
  obtain ⟨s, hs⟩ := hiter m
  rw [hs]
  exact finitePlaceOrderTop_algebraMap_nonnegative (L := L) v s

private theorem dedekindCaseI_coe_sum_int_finset
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

omit [Algebra C R] [IsScalarTower C R L] in
/-- In a DVR-preserving Wronskian, only the pole columns pay a derivative
order cost. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_poles
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (epsilonOrder : ι → ℕ) (g : ι → L) (poles : Finset ι)
    (E : ℤ)
    (hpole : ∀ i ∈ poles, finitePlaceOrderTop v (g i) < 0)
    (hregular : ∀ i ∉ poles, (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (g i))
    (hselected : ∀ σ : Equiv.Perm ι,
      (∑ i ∈ poles, (epsilonOrder (σ i) : ℤ)) ≤ E) :
    (((∑ i ∈ poles, finitePlaceOrder v (g i)) - E : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v
        (indexedDedekindLocalWronskian D epsilonOrder g).det := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : v.asIdeal = Ideal.span {π} := by
    calc
      v.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal v.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [Matrix.det_apply']
  apply le_finitePlaceOrderTop_finset_sum_of_forall
  intro σ _
  let term : L :=
    ((Equiv.Perm.sign σ : ℤ) : L) *
      ∏ i, indexedDedekindLocalWronskian D epsilonOrder g (σ i) i
  change
    (((∑ i ∈ poles, finitePlaceOrder v (g i)) - E : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v term
  calc
    (((∑ i ∈ poles, finitePlaceOrder v (g i)) - E : ℤ) : WithTop ℤ) ≤
        (((∑ i ∈ poles,
          (finitePlaceOrder v (g i) - (epsilonOrder (σ i) : ℤ)) : ℤ)) :
            WithTop ℤ) := by
      rw [Finset.sum_sub_distrib]
      exact_mod_cast sub_le_sub_left (hselected σ) _
    _ = ∑ i, if i ∈ poles then
          (((finitePlaceOrder v (g i) -
            (epsilonOrder (σ i) : ℤ) : ℤ)) : WithTop ℤ)
        else 0 := by
      rw [Finset.sum_ite_mem_eq]
      exact dedekindCaseI_coe_sum_int_finset poles
        (fun i => finitePlaceOrder v (g i) - (epsilonOrder (σ i) : ℤ))
    _ ≤ ∑ i, finitePlaceOrderTop v
        (((D : L → L)^[epsilonOrder (σ i)]) (g i)) := by
      gcongr with i
      by_cases hi : i ∈ poles
      · simp only [hi, ite_true]
        have hgi : g i ≠ 0 := by
          intro hz
          have hneg := hpole i hi
          rw [hz] at hneg
          simp at hneg
        have hbound :=
          finitePlaceOrderTop_derivation_iterate_ge_sub_nat_of_preserves
            v π hπ hπIdeal D hDIntegral (epsilonOrder (σ i)) (g i)
        rw [finitePlaceOrderTop_eq_coe v (g i) hgi] at hbound
        simpa only [← WithTop.coe_add, sub_eq_add_neg] using hbound
      · simp only [hi, ite_false]
        exact finitePlaceOrderTop_derivation_iterate_nonnegative_of_nonnegative
          v D hDIntegral (epsilonOrder (σ i)) (g i) (hregular i hi)
    _ = finitePlaceOrderTop v
        (∏ i, indexedDedekindLocalWronskian D epsilonOrder g (σ i) i) := by
      rw [finitePlaceOrderTop_finset_prod]
      rfl
    _ ≤ finitePlaceOrderTop v term := by
      exact finitePlaceOrderTop_le_intCast_mul v
        (Equiv.Perm.sign σ : ℤ)
        (∏ i, indexedDedekindLocalWronskian D epsilonOrder g (σ i) i)

private theorem dedekindCaseI_sum_range_int_mul_two (r : ℕ) :
    (∑ n ∈ Finset.range r, (n : ℤ)) * 2 =
      (r : ℤ) * (r - 1 : ℕ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (Finset.sum_range_id_mul_two r)
  push_cast at h
  exact h

private theorem dedekindCaseI_int_natCast_mul_pred (r : ℕ) :
    (r : ℤ) * (r - 1 : ℕ) = (r : ℤ) * ((r : ℤ) - 1) := by
  cases r <;> simp

omit [Algebra C R] [IsScalarTower C R L] in
/-- The exact intermediate case-(i) estimate at a Dedekind DVR place. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_caseI_epsilon_plus_one_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (epsilonOrder : ι → ℕ) (g : ι → L)
    (rhoOrder : ℤ) (epsilon : ℕ)
    (hgdistinct : NegativeFinitePlaceOrdersPairwiseDistinct v g)
    (hglower : ∀ i, (rhoOrder : WithTop ℤ) ≤ finitePlaceOrderTop v (g i))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hcardRho : rhoOrder ≤
      -((Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card : ℤ))
    (hcardEpsilon :
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card ≤
        epsilon + 1) :
    ((rhoOrder * (epsilon + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v
        (indexedDedekindLocalWronskian D epsilonOrder g).det := by
  let poles : Finset ι :=
    Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0
  let E : ℤ := ∑ n ∈ Finset.range poles.card, ((epsilon : ℤ) - n)
  have hpole : ∀ i ∈ poles, finitePlaceOrderTop v (g i) < 0 := by
    intro i hi
    simpa [poles] using hi
  have hpoleNe : ∀ i ∈ poles, g i ≠ 0 := by
    intro i hi hz
    have hneg := hpole i hi
    rw [hz] at hneg
    simp at hneg
  have horderInj :
      Set.InjOn (fun i => finitePlaceOrder v (g i)) (poles : Set ι) := by
    intro i hi j hj hij
    apply hgdistinct (hpole i hi) (hpole j hj)
    rw [finitePlaceOrderTop_eq_coe v (g i) (hpoleNe i hi),
      finitePlaceOrderTop_eq_coe v (g j) (hpoleNe j hj)]
    exact_mod_cast hij
  have hpoleLower :
      (∑ n ∈ Finset.range poles.card, (rhoOrder + n : ℤ)) ≤
        ∑ i ∈ poles, finitePlaceOrder v (g i) :=
    sum_range_add_le_sum_of_injOn poles
      (fun i => finitePlaceOrder v (g i)) rhoOrder horderInj (by
        intro i hi
        have h := hglower i
        rw [finitePlaceOrderTop_eq_coe v (g i) (hpoleNe i hi)] at h
        exact_mod_cast h)
  have hselected : ∀ σ : Equiv.Perm ι,
      (∑ i ∈ poles, (epsilonOrder (σ i) : ℤ)) ≤ E := by
    intro σ
    apply sum_le_sum_range_sub_of_injOn poles
      (fun i => epsilonOrder (σ i)) epsilon
    · intro i hi j hj hij
      exact σ.injective (hepsilonInjective hij)
    · intro i _
      exact hepsilonMax (σ i)
  have hregular : ∀ i ∉ poles,
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (g i) := by
    intro i hi
    simp only [poles, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact le_of_not_gt hi
  have hW :=
    finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_poles
      v D hDIntegral epsilonOrder g poles E hpole hregular hselected
  apply le_trans ?_ hW
  norm_cast
  have hcardRho' : rhoOrder ≤ -(poles.card : ℤ) := by
    simpa [poles] using hcardRho
  have hcardEpsilon' : poles.card ≤ epsilon + 1 := by
    simpa [poles] using hcardEpsilon
  let S : ℤ := ∑ n ∈ Finset.range poles.card, (n : ℤ)
  have htri : S * 2 = (poles.card : ℤ) * (poles.card - 1 : ℕ) := by
    exact dedekindCaseI_sum_range_int_mul_two poles.card
  have htri' : S * 2 =
      (poles.card : ℤ) * ((poles.card : ℤ) - 1) :=
    htri.trans (dedekindCaseI_int_natCast_mul_pred poles.card)
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
    _ ≤ (∑ i ∈ poles, finitePlaceOrder v (g i)) - E :=
      sub_le_sub_right hpoleLower E

omit [Algebra C R] [IsScalarTower C R L] in
/-- Source case (i), in the final `q * rhoOrder` form, at a Dedekind DVR
place. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_caseI_q_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (epsilonOrder : ι → ℕ) (g : ι → L)
    (rhoOrder : ℤ) (epsilon q : ℕ)
    (hgdistinct : NegativeFinitePlaceOrdersPairwiseDistinct v g)
    (hglower : ∀ i, (rhoOrder : WithTop ℤ) ≤ finitePlaceOrderTop v (g i))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hcardRho : rhoOrder ≤
      -((Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card : ℤ))
    (hcardEpsilon :
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card ≤
        epsilon + 1)
    (hrho : rhoOrder ≤ 0) (hepsilonQ : epsilon + 1 ≤ q) :
    (((q : ℤ) * rhoOrder : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v
        (indexedDedekindLocalWronskian D epsilonOrder g).det := by
  apply le_trans ?_
    (finitePlaceOrderTop_indexedDedekindLocalWronskian_caseI_epsilon_plus_one_lower_bound
      v D hDIntegral epsilonOrder g rhoOrder epsilon hgdistinct hglower
      hepsilonInjective hepsilonMax hcardRho hcardEpsilon)
  norm_cast
  have hepsilonQ' : (epsilon + 1 : ℤ) ≤ q := by
    exact_mod_cast hepsilonQ
  calc
    (q : ℤ) * rhoOrder ≤ (epsilon + 1 : ℤ) * rhoOrder :=
      mul_le_mul_of_nonpos_right hepsilonQ' hrho
    _ = rhoOrder * (epsilon + 1 : ℕ) := by push_cast; ring

omit [IsDiscreteValuationRing R] in
/-- Pairwise-distinct negative finite-place orders bounded below by a
nonpositive integer are no more numerous than its pole depth. -/
theorem card_negativeFinitePlaceOrders_le_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (g : ι → L) (a : ℤ) (ha : a ≤ 0)
    (hgdistinct : NegativeFinitePlaceOrdersPairwiseDistinct v g)
    (hglower : ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (g i)) :
    a ≤ -((Finset.univ.filter fun i =>
      finitePlaceOrderTop v (g i) < 0).card : ℤ) := by
  let poles : Finset ι :=
    Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0
  have hpole : ∀ i ∈ poles, finitePlaceOrderTop v (g i) < 0 := by
    intro i hi
    simpa [poles] using hi
  have hpoleNe : ∀ i ∈ poles, g i ≠ 0 := by
    intro i hi hz
    have hneg := hpole i hi
    rw [hz] at hneg
    simp at hneg
  let w : ι → ℤ := fun i => finitePlaceOrder v (g i)
  have hinj : Set.InjOn w (poles : Set ι) := by
    intro i hi j hj hij
    apply hgdistinct (hpole i hi) (hpole j hj)
    rw [finitePlaceOrderTop_eq_coe v (g i) (hpoleNe i hi),
      finitePlaceOrderTop_eq_coe v (g j) (hpoleNe j hj)]
    exact_mod_cast hij
  have hsubset : poles.image w ⊆ Finset.Ico a 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_Ico]
    constructor
    · have h := hglower i
      rw [finitePlaceOrderTop_eq_coe v (g i) (hpoleNe i hi)] at h
      exact_mod_cast h
    · have h := hpole i hi
      rw [finitePlaceOrderTop_eq_coe v (g i) (hpoleNe i hi)] at h
      exact_mod_cast h
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

/-- Complete local case (i) for an arbitrary `Fin k` fraction-field family. -/
theorem exists_dedekindCaseI_columnMatrix_and_q_wronskian_bound
    {k : ℕ} (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (epsilonOrder : Fin k → ℕ) (f : Fin k → L)
    (a : ℤ) (epsilon q : ℕ)
    (ha : a ≤ 0)
    (hf : ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (f i))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) C,
      A.det = 1 ∧
      (indexedDedekindLocalWronskian D epsilonOrder
        (indexedDedekindLocalColumnCombination f A)).det =
          (indexedDedekindLocalWronskian D epsilonOrder f).det ∧
      (((q : ℤ) * a : ℤ) : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D epsilonOrder f).det := by
  obtain ⟨A, hAdet, hdistinct, hlower⟩ :=
    exists_det_one_dedekindColumnMatrix_negativeOrdersPairwiseDistinct
      v hresidue a f hf
  let g := indexedDedekindLocalColumnCombination f A
  have hdet :
      (indexedDedekindLocalWronskian D epsilonOrder g).det =
        (indexedDedekindLocalWronskian D epsilonOrder f).det := by
    exact indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
      D epsilonOrder f A hAdet
  have hcardRho :
      a ≤ -((Finset.univ.filter fun i =>
        finitePlaceOrderTop v (g i) < 0).card : ℤ) :=
    card_negativeFinitePlaceOrders_le_neg v g a ha hdistinct hlower
  have hcardEpsilon :
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card ≤
        epsilon + 1 := by
    calc
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card ≤
          (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
      _ = k := Fintype.card_fin k
      _ ≤ epsilon + 1 := hk
  have hbound :=
    finitePlaceOrderTop_indexedDedekindLocalWronskian_caseI_q_lower_bound
      v D hDIntegral epsilonOrder g a epsilon q hdistinct hlower
      hepsilonInjective hepsilonMax hcardRho hcardEpsilon ha hepsilonQ
  refine ⟨A, hAdet, hdet, ?_⟩
  rw [← hdet]
  exact hbound

/-- Extend a first-block operation by the identity on the grid columns. -/
def dedekindCaseIColumnMatrix (h k : ℕ)
    (A : Matrix (Fin k) (Fin k) C) :
    Matrix (Sum (Fin k) (Fin (k + 1) × Fin h))
      (Sum (Fin k) (Fin (k + 1) × Fin h)) C :=
  Matrix.fromBlocks A 0 0 1

theorem dedekindCaseIColumnMatrix_det (h k : ℕ)
    (A : Matrix (Fin k) (Fin k) C) :
    (dedekindCaseIColumnMatrix h k A).det = A.det := by
  rw [dedekindCaseIColumnMatrix, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem indexedDedekindLocalColumnCombination_dedekindCaseIColumnMatrix_inl
    (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → L)
    (A : Matrix (Fin k) (Fin k) C) (i : Fin k) :
    indexedDedekindLocalColumnCombination f
        (dedekindCaseIColumnMatrix h k A) (Sum.inl i) =
      indexedDedekindLocalColumnCombination (fun j => f (Sum.inl j)) A i := by
  classical
  rw [indexedDedekindLocalColumnCombination, Fintype.sum_sum_type]
  simp [dedekindCaseIColumnMatrix, indexedDedekindLocalColumnCombination]

theorem indexedDedekindLocalColumnCombination_dedekindCaseIColumnMatrix_inr
    (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → L)
    (A : Matrix (Fin k) (Fin k) C) (rs : Fin (k + 1) × Fin h) :
    indexedDedekindLocalColumnCombination f
        (dedekindCaseIColumnMatrix h k A) (Sum.inr rs) =
      f (Sum.inr rs) := by
  classical
  rw [indexedDedekindLocalColumnCombination, Fintype.sum_sum_type]
  simp [dedekindCaseIColumnMatrix, Matrix.one_apply]

/-- The full Dedekind-local auxiliary family after eliminating repeated
orders in its first block. -/
def dedekindCaseITransformedLocalAuxiliaryFamily
    (u w rho : L) (h k : ℕ) (A : Matrix (Fin k) (Fin k) C) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → L :=
  indexedDedekindLocalColumnCombination
    (dedekindLocalAuxiliaryFamily u w rho h k)
    (dedekindCaseIColumnMatrix h k A)

@[simp]
theorem dedekindCaseITransformedLocalAuxiliaryFamily_inl
    (u w rho : L) (h k : ℕ) (A : Matrix (Fin k) (Fin k) C) (i : Fin k) :
    dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A (Sum.inl i) =
      indexedDedekindLocalColumnCombination
        (fun j => dedekindLocalAuxiliaryFamily u w rho h k (Sum.inl j)) A i :=
  indexedDedekindLocalColumnCombination_dedekindCaseIColumnMatrix_inl
    h k (dedekindLocalAuxiliaryFamily u w rho h k) A i

@[simp]
theorem dedekindCaseITransformedLocalAuxiliaryFamily_inr
    (u w rho : L) (h k : ℕ) (A : Matrix (Fin k) (Fin k) C)
    (rs : Fin (k + 1) × Fin h) :
    dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A (Sum.inr rs) =
      dedekindLocalAuxiliaryFamily u w rho h k (Sum.inr rs) :=
  indexedDedekindLocalColumnCombination_dedekindCaseIColumnMatrix_inr
    h k (dedekindLocalAuxiliaryFamily u w rho h k) A rs

/-- Source-facing case-(i) elimination for the full auxiliary family.  The
ratio block starts at the common negative order of `rho`, while the grid
columns are assumed regular. -/
theorem exists_dedekindLocalAuxiliaryFamily_caseI_columnMatrix
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (u w rho : L) (h k : ℕ)
    (hrhoNe : rho ≠ 0)
    (huOrder : finitePlaceOrderTop v u = 0)
    (hrhoOrder : finitePlaceOrder v rho < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v
        (u ^ (rs.1 : ℕ) * w ^ (rs.2 : ℕ))) :
    ∃ A : Matrix (Fin k) (Fin k) C,
      A.det = 1 ∧
      NegativeFinitePlaceOrdersPairwiseDistinct v
        (dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A) ∧
      (∀ i, (finitePlaceOrder v rho : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A i)) ∧
      (∀ rs, dedekindCaseITransformedLocalAuxiliaryFamily
          u w rho h k A (Sum.inr rs) =
        dedekindLocalAuxiliaryFamily u w rho h k (Sum.inr rs)) := by
  let first : Fin k → L :=
    fun i => dedekindLocalAuxiliaryFamily u w rho h k (Sum.inl i)
  have hfirstOrder : ∀ i,
      finitePlaceOrderTop v (first i) =
        (finitePlaceOrder v rho : WithTop ℤ) := by
    intro i
    simp only [first, dedekindLocalAuxiliaryFamily]
    rw [finitePlaceOrderTop_mul, finitePlaceOrderTop_pow, huOrder,
      finitePlaceOrderTop_eq_coe v rho hrhoNe]
    simp
  have hfirstLower : ∀ i, (finitePlaceOrder v rho : WithTop ℤ) ≤
      finitePlaceOrderTop v (first i) := by
    intro i
    rw [hfirstOrder i]
  obtain ⟨A, hAdet, hdistinct, hlower⟩ :=
    exists_det_one_dedekindColumnMatrix_negativeOrdersPairwiseDistinct
      v hresidue (finitePlaceOrder v rho) first hfirstLower
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
            rw [dedekindCaseITransformedLocalAuxiliaryFamily_inr] at hy
            exact (not_lt_of_ge (hgridRegular rs)) hy |>.elim
    | inr rs =>
        rw [dedekindCaseITransformedLocalAuxiliaryFamily_inr] at hx
        exact (not_lt_of_ge (hgridRegular rs)) hx |>.elim
  · intro i
    cases i with
    | inl j => simpa [first] using hlower j
    | inr rs =>
        rw [dedekindCaseITransformedLocalAuxiliaryFamily_inr]
        exact (show (finitePlaceOrder v rho : WithTop ℤ) ≤ 0 by
          exact_mod_cast hrhoOrder.le) |>.trans (hgridRegular rs)
  · intro rs
    exact dedekindCaseITransformedLocalAuxiliaryFamily_inr
      u w rho h k A rs

/-- Full Dedekind-DVR case (i): determinant-one repeated cancellation on the
first block preserves the original Wronskian and proves the exact
`q * ord(rho)` lower bound. -/
theorem exists_dedekindLocalAuxiliaryFamily_caseI_q_wronskian_bound
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (u w rho : L) (h k : ℕ)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (epsilon q : ℕ)
    (hrhoNe : rho ≠ 0)
    (huOrder : finitePlaceOrderTop v u = 0)
    (hrhoOrder : finitePlaceOrder v rho < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v
        (u ^ (rs.1 : ℕ) * w ^ (rs.2 : ℕ)))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) C,
      A.det = 1 ∧
      (indexedDedekindLocalWronskian D epsilonOrder
        (dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A)).det =
          (indexedDedekindLocalWronskian D epsilonOrder
            (dedekindLocalAuxiliaryFamily u w rho h k)).det ∧
      (((q : ℤ) * finitePlaceOrder v rho : ℤ) : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D epsilonOrder
            (dedekindLocalAuxiliaryFamily u w rho h k)).det := by
  obtain ⟨A, hAdet, hdistinct, hlower, hgrid⟩ :=
    exists_dedekindLocalAuxiliaryFamily_caseI_columnMatrix
      v hresidue u w rho h k hrhoNe huOrder hrhoOrder hgridRegular
  let f := dedekindLocalAuxiliaryFamily u w rho h k
  let B := dedekindCaseIColumnMatrix h k A
  let g := dedekindCaseITransformedLocalAuxiliaryFamily u w rho h k A
  have hBdet : B.det = 1 := by
    rw [dedekindCaseIColumnMatrix_det, hAdet]
  have hdet :
      (indexedDedekindLocalWronskian D epsilonOrder g).det =
        (indexedDedekindLocalWronskian D epsilonOrder f).det := by
    exact indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
      D epsilonOrder f B hBdet
  have hcardRho :
      finitePlaceOrder v rho ≤ -((Finset.univ.filter fun i =>
        finitePlaceOrderTop v (g i) < 0).card : ℤ) :=
    card_negativeFinitePlaceOrders_le_neg v g (finitePlaceOrder v rho)
      hrhoOrder.le hdistinct hlower
  let firstPoles : Finset (Fin k) := Finset.univ.filter fun i =>
    finitePlaceOrderTop v (g (Sum.inl i)) < 0
  have hpoles :
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0) =
        firstPoles.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    cases x with
    | inl i => simp [firstPoles]
    | inr rs =>
        have hregg : (0 : WithTop ℤ) ≤
            finitePlaceOrderTop v (g (Sum.inr rs)) := by
          change (0 : WithTop ℤ) ≤ finitePlaceOrderTop v
            (dedekindCaseITransformedLocalAuxiliaryFamily
              u w rho h k A (Sum.inr rs))
          rw [hgrid rs]
          simpa [dedekindLocalAuxiliaryFamily] using hgridRegular rs
        have hrs : ¬ finitePlaceOrderTop v (g (Sum.inr rs)) < 0 :=
          not_lt_of_ge hregg
        simp [firstPoles, hrs]
  have hcardEpsilon :
      (Finset.univ.filter fun i => finitePlaceOrderTop v (g i) < 0).card ≤
        epsilon + 1 := by
    rw [hpoles, Finset.card_map]
    exact (Finset.card_filter_le _ _).trans (by simpa using hk)
  have hbound :=
    finitePlaceOrderTop_indexedDedekindLocalWronskian_caseI_q_lower_bound
      v D hDIntegral epsilonOrder g (finitePlaceOrder v rho) epsilon q
      hdistinct hlower hepsilonInjective hepsilonMax hcardRho hcardEpsilon
      hrhoOrder.le hepsilonQ
  refine ⟨A, hAdet, hdet, ?_⟩
  rw [← hdet]
  exact hbound

/-- The same endpoint for the source `auxiliaryFamily`, specialized to
`rho = (1-u)/(1-w)`. -/
theorem exists_dedekindAuxiliaryFamily_caseI_q_wronskian_bound
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (u w : L) (h k : ℕ)
    (epsilonOrder : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (epsilon q : ℕ)
    (hrhoNe : (1 - u) / (1 - w) ≠ 0)
    (huOrder : finitePlaceOrderTop v u = 0)
    (hrhoOrder : finitePlaceOrder v ((1 - u) / (1 - w)) < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v
        (u ^ (rs.1 : ℕ) * w ^ (rs.2 : ℕ)))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) C,
      A.det = 1 ∧
      (indexedDedekindLocalWronskian D epsilonOrder
        (indexedDedekindLocalColumnCombination (auxiliaryFamily u w h k)
          (dedekindCaseIColumnMatrix h k A))).det =
          (indexedDedekindLocalWronskian D epsilonOrder
            (auxiliaryFamily u w h k)).det ∧
      (((q : ℤ) * finitePlaceOrder v ((1 - u) / (1 - w)) : ℤ) :
          WithTop ℤ) ≤
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D epsilonOrder
            (auxiliaryFamily u w h k)).det := by
  simpa only [dedekindCaseITransformedLocalAuxiliaryFamily,
    dedekindLocalAuxiliaryFamily_div_eq_auxiliaryFamily] using
    (exists_dedekindLocalAuxiliaryFamily_caseI_q_wronskian_bound
      v hresidue D hDIntegral u w ((1 - u) / (1 - w)) h k epsilonOrder
      epsilon q hrhoNe huOrder hrhoOrder hgridRegular hepsilonInjective
      hepsilonMax hk hepsilonQ)

end

end BGS.CorvajaZannier
