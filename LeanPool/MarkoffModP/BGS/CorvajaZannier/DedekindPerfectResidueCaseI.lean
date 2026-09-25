/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindAuxiliaryCaseI
public import Mathlib.FieldTheory.Perfect

/-!
# Corvaja--Zannier case (i) over a perfect residue field

The usual leading-coefficient cancellation in local case (i) does not require
the global constant field to surject onto the residue field.  In
characteristic `p`, it is enough that the residue field is perfect.  Given the
ratio of two unit leading coefficients, choose its `p`-th root in the residue
field, lift that root to the DVR, and use the `p`-th power of the lift.  This
coefficient is regular and belongs to the Frobenius subfield of the fraction
field, hence is killed by the separating derivation.

This file packages that argument and then repeats the determinant-one
elimination from `DedekindAuxiliaryCaseI` with coefficients in the Frobenius
subfield.  No algebra structure from the whole Frobenius subfield to the DVR
is asserted: such a structure would be false at a nontrivial place.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators
open IsDedekindDomain Multiplicative WithZero

variable {R L : Type*} [CommRing R] [IsDedekindDomain R]
  [IsDiscreteValuationRing R] [Field L] [Algebra R L]
  [IsFractionRing R L]
  {p : ℕ} [Fact p.Prime] [CharP R p] [CharP L p]

omit [IsDiscreteValuationRing R] [IsFractionRing R L] in
/-- Over a perfect residue field, the ratio of two unit leading coefficients
can be cancelled by a regular element whose image in the fraction field is a
`p`-th power.

The extra witness `b : R` records regularity of the coefficient; its image in
`L` is the coefficient represented by `c : L^p`. -/
theorem exists_frobeniusSubfield_regular_unit_sub_mul_mem_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (u w : Rˣ) :
    ∃ (c : frobeniusSubfield L p) (b : R),
      algebraMap (frobeniusSubfield L p) L c = algebraMap R L b ∧
      (u : R) - b * (w : R) ∈ v.asIdeal := by
  let κ := v.asIdeal.ResidueField
  let : CharP κ p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R κ) p
      (Fact.out : p.Prime).ne_zero
  let : ExpChar κ p := inferInstance
  let ratio : κ := algebraMap R κ (((u * w⁻¹ : Rˣ) : R))
  obtain ⟨z, hz⟩ := surjective_frobenius κ p ratio
  obtain ⟨a, ha⟩ := v.asIdeal.algebraMap_residueField_surjective z
  let b : R := a ^ p
  have hbMap : algebraMap R κ b = ratio := by
    rw [show algebraMap R κ b = (algebraMap R κ a) ^ p by
      simp [b]]
    rw [ha]
    simpa [frobenius_def] using hz
  have hbCancel : (u : R) - b * (w : R) ∈ v.asIdeal := by
    rw [← Ideal.algebraMap_residueField_eq_zero]
    rw [map_sub, map_mul, hbMap]
    dsimp [ratio]
    rw [← map_mul]
    simp
    change algebraMap R κ (u : R) - algebraMap R κ (u : R) = 0
    exact sub_self _
  have hbFrob : algebraMap R L b ∈ frobeniusSubfield L p := by
    refine ⟨algebraMap R L a, ?_⟩
    simp [frobenius_def, b]
  let c : frobeniusSubfield L p := ⟨algebraMap R L b, hbFrob⟩
  refine ⟨c, b, ?_, hbCancel⟩
  rfl

/-- Equal-order nonzero functions admit a strict leading-term cancellation
with a coefficient in the Frobenius subfield whenever the residue field is
perfect. -/
theorem exists_frobeniusSubfield_finitePlaceOrder_sub_mul_eq_zero_or_lt_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : finitePlaceOrder v x = finitePlaceOrder v y) :
    ∃ c : frobeniusSubfield L p,
      x - algebraMap (frobeniusSubfield L p) L c * y = 0 ∨
        finitePlaceOrder v x < finitePlaceOrder v
          (x - algebraMap (frobeniusSubfield L p) L c * y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : v.asIdeal = Ideal.span {π} := by
    calc
      v.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal v.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨nx, ux, hxrepr⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hx
  obtain ⟨ny, uy, hyrepr⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hy
  have hxrepr' :
      x = algebraMap R L (ux : R) * (algebraMap R L π) ^ nx := by
    simpa [Units.smul_def, Algebra.smul_def] using hxrepr
  have hyrepr' :
      y = algebraMap R L (uy : R) * (algebraMap R L π) ^ ny := by
    simpa [Units.smul_def, Algebra.smul_def] using hyrepr
  have hxOrder : finitePlaceOrder v x = nx := by
    rw [hxrepr']
    exact finitePlaceOrder_unit_mul_uniformizer_zpow
      v π hπ hπIdeal ux nx
  have hyOrder : finitePlaceOrder v y = ny := by
    rw [hyrepr']
    exact finitePlaceOrder_unit_mul_uniformizer_zpow
      v π hπ hπIdeal uy ny
  have hnxny : nx = ny := by omega
  rw [← hnxny] at hyrepr'
  obtain ⟨c, b, hc, hb⟩ :=
    exists_frobeniusSubfield_regular_unit_sub_mul_mem_of_perfect_residue
      (L := L) (p := p) v ux uy
  let a : R := (ux : R) - b * (uy : R)
  have haMem : a ∈ v.asIdeal := by simpa [a] using hb
  have hfactor :
      x - algebraMap (frobeniusSubfield L p) L c * y =
        algebraMap R L a * (algebraMap R L π) ^ nx := by
    rw [hxrepr', hyrepr', hc]
    simp only [a, map_sub, map_mul]
    ring
  by_cases ha : a = 0
  · refine ⟨c, Or.inl ?_⟩
    rw [hfactor, ha, map_zero, zero_mul]
  · refine ⟨c, Or.inr ?_⟩
    have haMap : algebraMap R L a ≠ 0 := by
      intro hzero
      apply ha
      exact IsFractionRing.injective R L (by simpa using hzero)
    have hπMap : algebraMap R L π ≠ 0 := by
      simpa using hπ.ne_zero
    have hprod := finitePrincipalDivisor_mul (R := R)
      (algebraMap R L a) ((algebraMap R L π) ^ nx)
      haMap (zpow_ne_zero nx hπMap)
    have hprodOrder := congrArg (fun D ↦ D v) hprod
    simp only [finitePrincipalDivisor_apply, Finsupp.add_apply] at hprodOrder
    rw [finitePlaceOrder_uniformizer_zpow v π hπ hπIdeal nx] at hprodOrder
    have haOrder : (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L a) :=
      one_le_finitePlaceOrder_algebraMap_of_mem v a haMem ha
    rw [hxOrder, hfactor, hprodOrder]
    omega

/-- Equal negative orders have a Frobenius-subfield cancellation which
strictly lowers the pole-depth measure. -/
theorem exists_frobeniusSubfield_dedekindPoleDepth_sub_mul_lt_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (x y : L)
    (hxneg : finitePlaceOrderTop v x < 0)
    (hyneg : finitePlaceOrderTop v y < 0)
    (horder : finitePlaceOrderTop v x = finitePlaceOrderTop v y) :
    ∃ c : frobeniusSubfield L p,
      dedekindPoleDepth v
          (x - algebraMap (frobeniusSubfield L p) L c * y) <
        dedekindPoleDepth v x ∧
      finitePlaceOrderTop v x < finitePlaceOrderTop v
        (x - algebraMap (frobeniusSubfield L p) L c * y) := by
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
    exists_frobeniusSubfield_finitePlaceOrder_sub_mul_eq_zero_or_lt_of_perfect_residue
      (p := p) v x y hx hy horder'
  · refine ⟨c, ?_, ?_⟩
    · rw [hz]
      have hxdepth : 0 < dedekindPoleDepth v x :=
        (dedekindPoleDepth_pos_iff v x).2 hxneg
      simpa only [dedekindPoleDepth_zero] using hxdepth
    · rw [hz, finitePlaceOrderTop_eq_coe v x hx]
      simp
  · by_cases hz :
        x - algebraMap (frobeniusSubfield L p) L c * y = 0
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

private theorem
    indexedDedekindLocalColumnCombination_frobenius_transvection_same
    {k : ℕ} (f : Fin k → L) (i j : Fin k)
    (c : frobeniusSubfield L p) :
    indexedDedekindLocalColumnCombination f (Matrix.transvection j i c) i =
      f i + c • f j := by
  classical
  simp [indexedDedekindLocalColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, add_smul, Finset.sum_add_distrib]

private theorem
    indexedDedekindLocalColumnCombination_frobenius_transvection_ne
    {k : ℕ} (f : Fin k → L) (i j b : Fin k)
    (c : frobeniusSubfield L p) (hb : b ≠ i) :
    indexedDedekindLocalColumnCombination f (Matrix.transvection j i c) b =
      f b := by
  classical
  have hib : i ≠ b := Ne.symm hb
  simp [indexedDedekindLocalColumnCombination, Matrix.transvection,
    Matrix.single, Matrix.one_apply, hib]

private theorem indexedDedekindLocalColumnCombination_frobenius_one
    {k : ℕ} (f : Fin k → L) :
    indexedDedekindLocalColumnCombination f
      (1 : Matrix (Fin k) (Fin k) (frobeniusSubfield L p)) = f := by
  classical
  funext i
  simp [indexedDedekindLocalColumnCombination, Matrix.one_apply]

private theorem
    exists_frobeniusSubfield_dedekindPoleWeight_transvection_lt_of_perfect_residue
    {k : ℕ} (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (f : Fin k → L) (i j : Fin k)
    (hi : finitePlaceOrderTop v (f i) < 0)
    (hj : finitePlaceOrderTop v (f j) < 0)
    (horder : finitePlaceOrderTop v (f i) = finitePlaceOrderTop v (f j)) :
    ∃ c : frobeniusSubfield L p,
      dedekindPoleWeight v
          (indexedDedekindLocalColumnCombination f
            (Matrix.transvection j i (-c))) <
        dedekindPoleWeight v f ∧
      finitePlaceOrderTop v (f i) < finitePlaceOrderTop v
        (f i - algebraMap (frobeniusSubfield L p) L c * f j) := by
  obtain ⟨c, hstrict, hraise⟩ :=
    exists_frobeniusSubfield_dedekindPoleDepth_sub_mul_lt_of_perfect_residue
      (p := p) v (f i) (f j) hi hj horder
  refine ⟨c, ?_, hraise⟩
  unfold dedekindPoleWeight
  apply Finset.sum_lt_sum
  · intro b _
    by_cases hb : b = i
    · subst b
      rw [indexedDedekindLocalColumnCombination_frobenius_transvection_same]
      simpa only [Algebra.smul_def, map_neg, sub_eq_add_neg, neg_mul] using
        hstrict.le
    · rw [indexedDedekindLocalColumnCombination_frobenius_transvection_ne
        f i j b (-c) hb]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [indexedDedekindLocalColumnCombination_frobenius_transvection_same]
    simpa only [Algebra.smul_def, map_neg, sub_eq_add_neg, neg_mul] using
      hstrict

/-- Repeated equal negative orders can be eliminated over the Frobenius
subfield by a determinant-one matrix when the residue field is perfect.

Unlike the constant-field version, this theorem does not require an algebra
map from the coefficient field to the DVR. -/
theorem
  exists_det_one_frobeniusSubfield_columnMatrix_negativeOrdersPairwiseDistinct_of_perfect_residue
    {k : ℕ} (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (a : ℤ) (f : Fin k → L)
    (hf : ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (f i)) :
    ∃ A : Matrix (Fin k) (Fin k) (frobeniusSubfield L p),
      A.det = 1 ∧
      NegativeFinitePlaceOrdersPairwiseDistinct v
        (indexedDedekindLocalColumnCombination f A) ∧
      ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v
        (indexedDedekindLocalColumnCombination f A i) := by
  induction hN : dedekindPoleWeight v f using Nat.strong_induction_on
      generalizing f with
  | h N ih =>
      by_cases hdistinct : NegativeFinitePlaceOrdersPairwiseDistinct v f
      · refine ⟨(1 : Matrix (Fin k) (Fin k) (frobeniusSubfield L p)),
          Matrix.det_one, ?_, ?_⟩
        · simpa [indexedDedekindLocalColumnCombination_frobenius_one]
        · simpa [indexedDedekindLocalColumnCombination_frobenius_one] using hf
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
          exists_frobeniusSubfield_dedekindPoleWeight_transvection_lt_of_perfect_residue
            (p := p) v f i j hi hj horder
        let T : Matrix (Fin k) (Fin k) (frobeniusSubfield L p) :=
          Matrix.transvection j i (-c)
        let g := indexedDedekindLocalColumnCombination f T
        have hweight : dedekindPoleWeight v g < N := by
          rw [← hN]
          exact hweight'
        have hgi :
            g i = f i - algebraMap (frobeniusSubfield L p) L c * f j := by
          change indexedDedekindLocalColumnCombination f
            (Matrix.transvection j i (-c)) i = _
          rw [indexedDedekindLocalColumnCombination_frobenius_transvection_same]
          simp only [Algebra.smul_def, map_neg, neg_mul, sub_eq_add_neg]
        have hg : ∀ b, (a : WithTop ℤ) ≤
            finitePlaceOrderTop v (g b) := by
          intro b
          by_cases hb : b = i
          · subst b
            rw [hgi]
            exact (hf i).trans hraise.le
          · change (a : WithTop ℤ) ≤ finitePlaceOrderTop v
                (indexedDedekindLocalColumnCombination f
                  (Matrix.transvection j i (-c)) b)
            rw [indexedDedekindLocalColumnCombination_frobenius_transvection_ne
              f i j b (-c) hb]
            exact hf b
        obtain ⟨B, hBdet, hBdistinct, hBlower⟩ := ih _ hweight g hg rfl
        refine ⟨T * B, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, hBdet, mul_one]
          exact Matrix.det_transvection_of_ne j i (Ne.symm hij) (-c)
        · rw [← indexedDedekindLocalColumnCombination_mul]
          exact hBdistinct
        · rw [← indexedDedekindLocalColumnCombination_mul]
          exact hBlower

/-- Complete local case (i) for a `Fin k` family, with coefficients in the
Frobenius subfield and no residue-surjectivity assumption. -/
theorem exists_frobeniusSubfield_dedekindCaseI_columnMatrix_and_q_wronskian_bound_of_perfect_residue
    {k : ℕ} (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (epsilonOrder : Fin k → ℕ) (f : Fin k → L)
    (a : ℤ) (epsilon q : ℕ)
    (ha : a ≤ 0)
    (hf : ∀ i, (a : WithTop ℤ) ≤ finitePlaceOrderTop v (f i))
    (hepsilonInjective : Function.Injective epsilonOrder)
    (hepsilonMax : ∀ i, epsilonOrder i ≤ epsilon)
    (hk : k ≤ epsilon + 1) (hepsilonQ : epsilon + 1 ≤ q) :
    ∃ A : Matrix (Fin k) (Fin k) (frobeniusSubfield L p),
      A.det = 1 ∧
      (indexedDedekindLocalWronskian D epsilonOrder
        (indexedDedekindLocalColumnCombination f A)).det =
          (indexedDedekindLocalWronskian D epsilonOrder f).det ∧
      (((q : ℤ) * a : ℤ) : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D epsilonOrder f).det := by
  obtain ⟨A, hAdet, hdistinct, hlower⟩ :=
    exists_det_one_frobeniusSubfield_columnMatrix_negativeOrdersPairwiseDistinct_of_perfect_residue
      (p := p) v a f hf
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

/-- Source-facing case-(i) elimination for the full auxiliary family over the
Frobenius subfield.  Perfectness of the residue field replaces surjectivity
from a global constant field. -/
theorem exists_frobeniusSubfield_dedekindLocalAuxiliaryFamily_caseI_columnMatrix_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (u w rho : L) (h k : ℕ)
    (hrhoNe : rho ≠ 0)
    (huOrder : finitePlaceOrderTop v u = 0)
    (hrhoOrder : finitePlaceOrder v rho < 0)
    (hgridRegular : ∀ rs : Fin (k + 1) × Fin h,
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v
        (u ^ (rs.1 : ℕ) * w ^ (rs.2 : ℕ))) :
    ∃ A : Matrix (Fin k) (Fin k) (frobeniusSubfield L p),
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
    exists_det_one_frobeniusSubfield_columnMatrix_negativeOrdersPairwiseDistinct_of_perfect_residue
      (p := p) v (finitePlaceOrder v rho) first hfirstLower
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

/-- Full Dedekind-DVR case (i) over the Frobenius subfield: perfect residue
fields supply every leading-term cancellation, the determinant-one column
operation preserves the Wronskian, and the exact `q * ord(rho)` lower bound
follows. -/
theorem
  exists_frobeniusSubfield_dedekindLocalAuxiliaryFamily_caseI_q_wronskian_bound_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (D : Derivation (frobeniusSubfield L p) L L)
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
    ∃ A : Matrix (Fin k) (Fin k) (frobeniusSubfield L p),
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
    exists_frobeniusSubfield_dedekindLocalAuxiliaryFamily_caseI_columnMatrix_of_perfect_residue
      (p := p) v u w rho h k hrhoNe huOrder hrhoOrder hgridRegular
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

/-- Source `auxiliaryFamily` endpoint, specialized to
`rho = (1-u)/(1-w)`, over a perfect residue field. -/
theorem exists_frobeniusSubfield_dedekindAuxiliaryFamily_caseI_q_wronskian_bound_of_perfect_residue
    (v : HeightOneSpectrum R)
    [PerfectField v.asIdeal.ResidueField]
    (D : Derivation (frobeniusSubfield L p) L L)
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
    ∃ A : Matrix (Fin k) (Fin k) (frobeniusSubfield L p),
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
    exists_frobeniusSubfield_dedekindLocalAuxiliaryFamily_caseI_q_wronskian_bound_of_perfect_residue
      (p := p) v D hDIntegral u w ((1 - u) / (1 - w)) h k epsilonOrder
      epsilon q hrhoNe huOrder hrhoOrder hgridRegular hepsilonInjective
      hepsilonMax hk hepsilonQ

end

end BGS.CorvajaZannier
