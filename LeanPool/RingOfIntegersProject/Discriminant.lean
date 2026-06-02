/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.List.NodupEquivFin
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IsAdjoinRoot

import LeanPool.RingOfIntegersProject.Resultant

/-!
Discriminants of polynomials and their relation to resultants and power bases.
-/

variable {R K : Type*} [CommRing R] [Field K]
variable {m n : ℕ}

open BigOperators

namespace Polynomial

namespace Multiset

/--
We can pick an order for the elements of a multiset and write its product as a `Fin`-indexed
  product.
-/
@[to_additive]
lemma prod_eq_prod_fin {M : Type*} [CommMonoid M] (s : Multiset M) :
    ∃ t : Fin (Multiset.card s) → M, s.prod = ∏ i, t i :=
  s.induction ⟨![], by simp⟩ (fun a s ⟨t, ih⟩ =>
    ⟨fun i => Fin.cons (α := fun _ => M) a t ⟨i, by simpa using i.prop⟩,
     by
      convert (Fin.prod_cons a t).symm
      · simp [ih]
      · simp
      · simp⟩)

/--
We can pick an order for the elements of a multiset and write its product as a `Fin`-indexed
  product.
-/
@[to_additive]
lemma prod_map_eq_prod_fin {α M : Type*} [CommMonoid M] (s : Multiset α) (f : α → M) :
    ∃ t : Fin (Multiset.card s) → α, (s.map f).prod = ∏ i, f (t i) :=
  s.induction ⟨![], by simp⟩ (fun a s ⟨t, ih⟩ =>
    ⟨fun i => Fin.cons (α := fun _ => α) a t ⟨i, by simpa using i.prop⟩,
     calc
      (Multiset.map f (a ::ₘ s)).prod
      _ = ∏ i : Fin (Multiset.card s + 1), f (Fin.cons (α := fun _ => α) a t i) := by
        simp [Fin.prod_univ_succ, ih]
      _ = ∏ i : Fin (Multiset.card (a ::ₘ s)), f _ := Fintype.prod_equiv
        (Fin.castOrderIso (by simp)).toEquiv _ _ (by
          intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · simp only [Fin.cons_succ, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.val_cast,
              Fin.val_succ, ← Fin.succ_mk, Fin.is_lt])⟩)

lemma prod_toList_map {α M : Type*} [CommMonoid M] (s : Multiset α) (f : α → M) :
    (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_toList]
  apply List.Perm.prod_eq (Multiset.coe_eq_coe.mp _)
  rw [Multiset.coe_toList, ← Multiset.map_coe, Multiset.coe_toList]

end Multiset

namespace List

lemma prod_get {α M : Type*} [CommMonoid M] (s : List α) (f : α → M) :
    ∏ i, f (s.get i) = (s.map f).prod := by
  induction s
  · simp
  · simp [Fin.prod_univ_succ]

end List

theorem resultant_eq_of_splits [Infinite K] (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits) :
    roiResultant f g =
      leadingCoeff f ^ g.natDegree * leadingCoeff g ^ f.natDegree *
        (f.roots.map (fun ai => (g.roots.map fun bj => (ai - bj)).prod)).prod := by
    conv_lhs =>
      rw [Splits.eq_prod_roots hf, Splits.eq_prod_roots hg]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [resultant_eq_prod_roots]
    congr <;> simp [splits_iff_card_roots.mp hf, splits_iff_card_roots.mp hg]
    · simpa
    · simpa

lemma hom_eval {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (x : R) :
    f (eval x p) = eval₂ f (f x) p := by
  rw [eval, hom_eval₂, RingHom.comp_id]

lemma prod_X_sub_C_resultant {ι : Type*} (s : Finset ι) (t : ι → K) (g : K[X]) :
    roiResultant (∏ i ∈ s, (X - C (t i))) g =
      ∏ i ∈ s, eval (t i) g := by
  by_cases hg0 : g = 0
  · simp [hg0, resultant_zero']
  have : (g.map (algebraMap K (AlgebraicClosure K))).Splits :=
    IsAlgClosed.splits (k := AlgebraicClosure K) _
  apply RingHom.injective (algebraMap K (AlgebraicClosure K))
  simp only [    ← resultant_map (RingHom.injective (algebraMap K (AlgebraicClosure K))),
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_prod, hom_eval,
    ← Polynomial.eval_map]
  rw [Splits.eq_prod_roots this,
      Finset.prod_eq_multiset_prod, ← one_mul (s.val.map _).prod, ← map_one C,
      resultant_multiset_eq_prod_roots]
  · simp only [Finset.card_val, one_mul,
      one_pow, Finset.prod_map_val, eval_mul, eval_C, Finset.prod_mul_distrib,
      Finset.prod_const, eval_multiset_prod, Multiset.map_map,
      Function.comp_apply, eval_sub, eval_X]
  · exact one_ne_zero
  · exact leadingCoeff_ne_zero.mpr (map_ne_zero hg0)

lemma resultant_prod_X_sub_C {ι : Type*} (f : K[X]) (s : Finset ι) (u : ι → K) :
    roiResultant f (∏ i ∈ s, (X - C (u i))) =
      (-1) ^ (f.natDegree * s.card) * ∏ i ∈ s, eval (u i) f := by
  rw [resultant_swap, prod_X_sub_C_resultant, natDegree_prod_X_sub_C]

namespace Fin

/-- Imported declaration. -/
def last' (n : ℕ) [NeZero n] : Fin n := Fin.rev 0

@[simp] lemma val_last' (n : ℕ) [NeZero n] : (Fin.last' n : ℕ) = n - 1 := rfl

lemma val_eq_card_sub_one_iff {n : ℕ} [NeZero n] {i : Fin n} :
    (i : ℕ) = n - 1 ↔ i = Fin.last' n := by
  rw [Fin.ext_iff, Fin.val_last']

lemma castAdd_eq_last' {m n : ℕ} [NeZero (n + m)] [NeZero n] {i : Fin n} :
    Fin.castAdd m i = Fin.last' (n + m) ↔ m = 0 ∧ i = Fin.last' n := by
  constructor
  · intro h
    rw [Fin.ext_iff, Fin.val_castAdd, Fin.val_last'] at h
    have : m = 0 := Nat.le_zero.mp <| by
      obtain ⟨i, hi⟩ := i
      rw [Fin.val_mk, add_comm, add_tsub_assoc_of_le (show 1 ≤ n from bot_lt_of_lt hi)] at h
      rw [h, ← Nat.le_sub_one_iff_lt (NeZero.pos _)] at hi
      simpa using hi
    simpa [Fin.ext_iff, this] using h
  · rintro ⟨rfl, rfl⟩
    ext
    simp

lemma natAdd_eq_last' {m n : ℕ} [NeZero (n + m)] [NeZero m] {i : Fin m} :
    Fin.natAdd n i = Fin.last' (n + m) ↔ i = Fin.last' m := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_natAdd, Fin.val_last', Fin.val_last',
      add_tsub_assoc_of_le (show 1 ≤ m from bot_lt_of_lt i.2), add_left_cancel_iff]

end Fin

lemma sylvesterMatrix_last' (f g : R[X]) [NeZero f.natDegree] [NeZero (f.natDegree + g.natDegree)]
    (i : Fin _) :
    sylvesterMatrix f g (Fin.last' _) i =
      if (i : ℕ) = (f.natDegree - 1) then g.leadingCoeff
      else if (i : ℕ) = (f.natDegree + g.natDegree - 1) then f.leadingCoeff
      else 0 := by
  by_cases hg0 : g.natDegree = 0
  · simp only [hg0, add_zero]
    obtain ⟨x, rfl⟩ := natDegree_eq_zero.mp hg0
    simp only [sylvesterMatrix_C, Matrix.diagonal_apply, eq_comm]
    split_ifs with h h1 h1
    · simp
    · simp [← Fin.val_eq_card_sub_one_iff, h] at h1
    · simp [← Fin.val_eq_card_sub_one_iff, h] at h1
    · simp
  simp only [sylvesterMatrix, sylvesterMatrixAux, sylvesterMatrixVec, Matrix.transpose_apply,
    Matrix.of_apply,
    Fin.val_eq_card_sub_one_iff]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have : NeZero f.natDegree := NeZero.of_pos (bot_lt_of_lt i.2)
    simp only [sylvesterVec_def, Fin.val_cast, tsub_le_iff_right, toVec_mk, dite_eq_ite,
      Fin.addCases_left, Fin.val_last', Fin.val_castAdd, ← coeff_natDegree]
    rw [if_pos (Nat.le_sub_one_of_lt (Nat.lt_add_right _ i.2)),
      if_neg (mt Fin.castAdd_eq_last'.mp (not_and_of_not_left _ hg0))]
    by_cases hi : ↑i = f.natDegree - 1
    · rw [if_pos hi, hi, if_pos, tsub_tsub_eq_add_tsub_of_le, tsub_add_cancel_of_le,
      add_tsub_cancel_left]
      · exact NeZero.pos (f.natDegree + g.natDegree)
      · exact NeZero.pos f.natDegree
      · rw [add_assoc, tsub_add_cancel_of_le (NeZero.pos f.natDegree), add_comm]
    · rw [if_neg hi, if_neg]
      · rw [add_comm, not_le, add_assoc]
        omega
  · simp only [sylvesterVec_def, Fin.val_cast, tsub_le_iff_right, toVec_mk, dite_eq_ite,
      Fin.addCases_right, Fin.val_last', Fin.val_natAdd, ← coeff_natDegree]
    rw [if_pos (Nat.le_sub_one_of_lt (Nat.lt_add_left _ i.2)),
      if_neg (show f.natDegree + ↑i ≠ f.natDegree - 1 from ?_)]
    · have : NeZero g.natDegree := ⟨hg0⟩
      by_cases hi : (i : ℕ) = g.natDegree - 1
      · rw [if_pos, if_pos, hi, add_tsub_assoc_of_le (NeZero.pos g.natDegree),
        add_tsub_cancel_right]
        · rw [Fin.natAdd_eq_last', ← Fin.val_eq_card_sub_one_iff, hi]
        · rw [hi, ← add_tsub_assoc_of_le (NeZero.pos g.natDegree),
          tsub_add_cancel_of_le (NeZero.pos (f.natDegree + g.natDegree))]
      · rw [if_neg, if_neg]
        · rwa [Fin.natAdd_eq_last', ← Fin.val_eq_card_sub_one_iff]
        · rw [add_assoc, not_le]
          omega
    · exact ((Nat.sub_one_lt (NeZero.ne _)).trans_le (Nat.le_add_right _ _)).ne'

/--
The discriminant of a polynomial `f` is defined as the roiResultant of `f` and its
derivative `f'`, up to a scaling factor.
We implement the scaling factor in the definition of the "modified" Sylvester matrix.
-/
noncomputable def modifiedSylvesterMatrix (f : R[X]) :
    Matrix (Fin (f.natDegree + (derivative f).natDegree)) (Fin (f.natDegree +
      (derivative f).natDegree)) R :=
  if h : 0 < f.natDegree
  then have h' : 0 < f.natDegree + (derivative f).natDegree := Nat.add_pos_left h (derivative
    f).natDegree
       (sylvesterMatrix f (derivative f)).updateRow (@Fin.last' _ (NeZero.of_pos h'))
          -- We will prove that this is equivalent to scalar multiplying the row by `(leadingCoeff
          -- f)⁻¹`
          (fun i => if (i : ℕ) = (f.natDegree - 1) then f.natDegree else
            if (i : ℕ) = (f.natDegree + f.derivative.natDegree - 1) then 1 else 0)
  else -- f and Q are constant polynomials so this is actually just an empty matrix
    sylvesterMatrix f (derivative f)

@[simp] theorem natDegree_derivative [NoZeroSMulDivisors ℕ R] (p : Polynomial R) :
    (Polynomial.derivative p).natDegree = p.natDegree - 1 := by
  by_cases hp0 : 0 < p.natDegree
  · refine le_antisymm (natDegree_derivative_le p) (le_natDegree_of_ne_zero ?_)
    rw [coeff_derivative, tsub_add_cancel_of_le hp0]
    norm_cast
    rw [tsub_add_cancel_of_le hp0, coeff_natDegree, mul_comm, ← nsmul_eq_mul]
    apply smul_ne_zero hp0.ne' (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp0))
  · obtain ⟨x, rfl⟩ := natDegree_eq_zero.mp (not_bot_lt_iff.mp hp0)
    simp

@[simp] lemma leadingCoeff_derivative [NoZeroSMulDivisors ℕ R] (f : R[X]) :
    leadingCoeff (derivative f) = f.natDegree * leadingCoeff f := by
  by_cases hp0 : 0 < f.natDegree
  · rw [leadingCoeff, coeff_derivative, natDegree_derivative, tsub_add_cancel_of_le hp0]
    norm_cast
    rw [tsub_add_cancel_of_le hp0, coeff_natDegree, mul_comm]
  · obtain ⟨x, rfl⟩ := natDegree_eq_zero.mp (not_bot_lt_iff.mp hp0)
    simp

lemma updateRow_smul_modifiedSylvesterMatrix [NoZeroSMulDivisors ℕ R] (f : R[X])
    [NeZero (f.natDegree + (derivative f).natDegree)] :
    (modifiedSylvesterMatrix f).updateRow (Fin.last' _) (f.leadingCoeff • modifiedSylvesterMatrix f
      (Fin.last' _)) =
      sylvesterMatrix (R := R) f (derivative f) := by
  have h : 0 < f.natDegree + (derivative f).natDegree := Nat.pos_of_neZero (f.natDegree +
    (derivative f).natDegree)
  have h : 0 < f.natDegree := by
    rw [pos_iff_ne_zero] at h ⊢
    contrapose! h
    rw [h, zero_add, natDegree_derivative, h, Nat.zero_sub]
  have : NeZero f.natDegree := NeZero.of_pos h
  simp only [modifiedSylvesterMatrix, dif_pos h]
  ext i j
  by_cases hi : i = Fin.last' _
  · simp only [natDegree_derivative, Matrix.updateRow_self, hi, Pi.smul_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, sylvesterMatrix_last', leadingCoeff_derivative]
    split_ifs
    · simp [mul_comm]
    · simp
    · simp
  · simp [hi]

/--
The discriminant of a polynomial `f` is defined as the roiResultant of `f` and its
derivative `f'`, up to a scaling factor.
-/
noncomputable def discriminant (f : R[X]) : R :=
  (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * Matrix.det (modifiedSylvesterMatrix f)

lemma discriminant_C (x : R) : discriminant (C x) = 1 := by
  rw [discriminant, modifiedSylvesterMatrix, dif_neg]
  · simp [C_sylvesterMatrix]
  · simp

lemma discriminant_one : discriminant (1 : R[X]) = 1 := by
  rw [← map_one C, discriminant_C]

lemma discriminant_zero : discriminant (0 : R[X]) = 1 := by
  rw [← map_zero C, discriminant_C]

@[simp] lemma discriminant_of_natDegree_eq_zero (f : R[X]) (hf0 : natDegree f = 0) :
    discriminant f = 1 := by
  obtain ⟨x, rfl⟩ := natDegree_eq_zero.mp hf0
  rw [discriminant_C]

variable [NoZeroSMulDivisors ℕ R]

lemma discriminant_def (f : R[X]) (hf : natDegree f ≠ 0) :
    f.leadingCoeff * discriminant f = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      roiResultant f (derivative f) := by
  have hf : 0 < natDegree f := Nat.pos_of_ne_zero hf
  have : NeZero (f.natDegree + (derivative f).natDegree) := NeZero.of_pos (by simp [hf])
  rw [roiResultant, ← updateRow_smul_modifiedSylvesterMatrix, Matrix.det_updateRow_smul,
      Matrix.updateRow_eq_self, discriminant, mul_left_comm]

lemma resultant_derivative_self (f : R[X]) (hf : natDegree f ≠ 0) :
    roiResultant f (derivative f) = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff *
      discriminant f := by
  rw [mul_assoc, discriminant_def _ hf, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_pow_two,
    one_pow, one_mul]

namespace Monic

lemma discriminant_def (f : R[X]) (hf : Monic f) :
    discriminant f =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * roiResultant f (derivative f) := by
  by_cases hf0 : natDegree f = 0
  · simp [hf.natDegree_eq_zero.mp hf0]
  · conv_lhs => rw [← one_mul f.discriminant, ← hf.leadingCoeff, Polynomial.discriminant_def _ hf0]

end Monic

@[simp] lemma discriminant_X_add_C [Nontrivial R] (b : R) : discriminant (X + C b) = 1 := by
  simp [(monic_X_add_C _).discriminant_def]

namespace Fin

@[simp] lemma val_unique {n : ℕ} [Unique (Fin n)] (i : Fin n) : (i : ℕ) = 0 := by
  have : NeZero n := NeZero.of_pos (bot_lt_of_lt i.2)
  rw [Subsingleton.elim i 0, Fin.val_zero]

end Fin

omit [NoZeroSMulDivisors ℕ R] in
@[simp] lemma discriminant_C_mul_X_add_C (a b : R) (ha : a ≠ 0) : discriminant (C a * X + C b) =
  1 := by
  have : Unique (Fin ((C a * X + C b).natDegree + (derivative (C a * X + C b)).natDegree)) := by
    simpa [ha] using inferInstanceAs (Unique (Fin 1))
  simp [discriminant, modifiedSylvesterMatrix, ha, Unique.eq_default]

@[simp]
theorem natDegree_derivative_eq {R : Type*} [Semiring R] [NoZeroSMulDivisors ℕ R]
    [IsAddTorsionFree R]
    (p : Polynomial R) : (derivative p).natDegree = p.natDegree - 1 := by
  obtain (hp | hp) := Nat.eq_zero_or_pos p.natDegree
  · rw [eq_C_of_natDegree_eq_zero hp, derivative_C, natDegree_zero, natDegree_C, Nat.zero_sub]
  exact natDegree_eq_of_degree_eq_some (degree_derivative_eq p hp)

@[simp] lemma discriminant_C_mul [CharZero R] [NoZeroDivisors R] (x : R) (hx0 : x ≠ 0)
    (p : R[X]) :
    discriminant (C x * p) = x ^ (2 * (p.natDegree - 1)) * discriminant p := by
  by_cases hp0 : natDegree p = 0
  · rw [eq_C_of_natDegree_eq_zero hp0, ← map_mul C, discriminant_C, natDegree_C, Nat.zero_sub,
        mul_zero, pow_zero, one_mul, discriminant_C]
  by_cases hp1 : natDegree p = 1
  · obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hp1
    rw [mul_add, ← mul_assoc, ← map_mul C, ← map_mul C]
    simp [-map_mul, mul_ne_zero hx0 ha, ha]
  have hcp0 : C x * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hx0) (ne_zero_of_natDegree_gt
    (Nat.pos_of_ne_zero hp0))
  have : (p.natDegree + (p.natDegree - 1)) = 1 + 2 * (p.natDegree - 1) := by omega
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr hcp0))
  rw [discriminant_def, derivative_mul, derivative_C, zero_mul, zero_add, C_mul_resultant,
      resultant_C_mul _ _ _ hp0, resultant_derivative_self, ← mul_assoc (x ^ _), ← pow_add,
      mul_left_comm (x ^ _), ← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, natDegree_C_mul hx0,
      ← two_mul, pow_mul, neg_one_pow_two, one_pow, one_mul, natDegree_C_mul hx0,
      natDegree_derivative_eq, add_comm, leadingCoeff_mul, leadingCoeff_C, this, pow_add, pow_one,
      mul_assoc, mul_assoc, mul_assoc, mul_left_comm _ p.leadingCoeff, ← mul_assoc]
  · assumption
  · rw [natDegree_C_mul hx0, natDegree_derivative_eq, ne_eq, Nat.sub_eq_zero_iff_le, not_le]
    exact lt_of_le_of_ne (Nat.pos_of_ne_zero hp0) (Ne.symm hp1)
  · rwa [natDegree_C_mul hx0]

omit [NoZeroSMulDivisors ℕ R] in
-- TODO: rename me to `derivative_prod` and `derivative_prod` to `derivative_multisetProd`.
theorem derivative_prod' {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → R[X]} :
    derivative (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ i ∈ s.erase i, f i) * derivative (f i) :=
  derivative_prod

omit [NoZeroSMulDivisors ℕ R] in
lemma derivative_prod_X_sub_C {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → R) :
    derivative (∏ i ∈ s, (X - C (t i))) =
      ∑ i ∈ s, ∏ j ∈ s.erase i, (X - C (t j)) := by
  rw [derivative_prod']
  exact Finset.sum_congr rfl (by simp)

omit [NoZeroSMulDivisors ℕ R] in
lemma natDegree_add_eq_of_leadingCoeff_add_ne_zero {p q : R[X]}
    (hcoeff : leadingCoeff p + leadingCoeff q ≠ 0) :
    natDegree (p + q) = max (natDegree p) (natDegree q) := by
  apply le_antisymm (natDegree_add_le _ _)
  obtain (lt | eq | gt) := lt_trichotomy (natDegree p) (natDegree q)
  · rw [natDegree_add_eq_right_of_natDegree_lt lt, max_eq_right_of_lt lt]
  · rw [eq, max_self]
    refine le_of_not_gt (mt ?_ hcoeff)
    intro lt
    rw [leadingCoeff, leadingCoeff, eq, ← coeff_add]
    exact coeff_eq_zero_of_natDegree_lt lt
  · rw [natDegree_add_eq_left_of_natDegree_lt gt, max_eq_left_of_lt gt]

omit [NoZeroSMulDivisors ℕ R] in
lemma natDegree_sum_eq {ι : Type*} {s : Finset ι} {p : ι → R[X]}
    (h0 : s.Nonempty)
    (hdeg : ∀ i ∈ s, natDegree (p i) = n) (hcoeff : ∑ i ∈ s, leadingCoeff (p i) ≠ 0) :
    natDegree (∑ i ∈ s, p i) = n := by
  classical
  induction s using Finset.cons_induction
  case empty =>
    contradiction
  case cons a s h ih =>
    obtain (rfl | hs0) := s.eq_empty_or_nonempty
    · simp [hdeg]
    rw [Finset.sum_cons] at hcoeff ⊢
    obtain ⟨hdega, hdegs⟩ : (p a).natDegree = n ∧ ∀ i ∈ s, (p i).natDegree = n := by
      simpa using hdeg
    by_cases hsum0 : ∑ b ∈ s, p b = 0
    · rwa [hsum0, add_zero]
    by_cases hcoeff' : ∑ i ∈ s, (p i).leadingCoeff = 0
    · rw [natDegree_add_eq_left_of_natDegree_lt (lt_of_le_of_ne _ _), hdega]
      · refine (natDegree_sum_le _ _).trans ?_
        rw [Finset.fold_congr (g := fun _ => n), Finset.fold_const]
        · simp [hs0.ne_empty, hdega]
        · simp
        · intro i hi
          exact hdegs _ hi
      · rw [hdega]
        intro h
        have := (Finset.sum_congr rfl (fun i hi => by rw [← coeff_natDegree,
          hdegs _ hi])).trans hcoeff'
        rw [← finsetSum_coeff, ← h, coeff_natDegree, leadingCoeff_eq_zero] at this
        contradiction
    have : (∑ i ∈ s, p i).natDegree = n := ih hs0 hdegs hcoeff'
    rw [natDegree_add_eq_of_leadingCoeff_add_ne_zero, hdega, this, max_self]
    · simp only [← coeff_natDegree, hdega, this, finsetSum_coeff] at hcoeff ⊢
      rwa [Finset.sum_congr rfl (fun i hi => by rw [hdegs _ hi])] at hcoeff

lemma discriminant_prod_X_sub_C [CharZero K] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → K) :
    discriminant (∏ i ∈ s, (X - C (t i))) =
      (-1) ^ (s.card * (s.card - 1) / 2) * ∏ i ∈ s, ∏ j ∈ s.erase i, (t i - t j) := by
  rw [Monic.discriminant_def, natDegree_prod_X_sub_C, derivative_prod_X_sub_C,
    prod_X_sub_C_resultant]
  · congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.sum_eq_single _
        (fun j _ hji => Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) (sub_self _))
        (fun h => (h hi).elim)
  · exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

@[simp]
theorem discriminant_map' [CharZero R] {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (φ : R →+* S)
    (hφ : Function.Injective φ) (f : R[X]) :
    discriminant (f.map φ) = φ (discriminant f) := by
  by_cases hf0 : f.natDegree = 0
  · simp [hf0, natDegree_map_eq_of_injective hφ]
  have hf0' : f ≠ 0 := by contrapose! hf0; simp [hf0]
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff hφ).mpr hf0')))
  rw [discriminant_def, derivative_map, resultant_map, leadingCoeff_map_of_injective hφ, ← map_mul,
      discriminant_def, natDegree_map_eq_of_injective hφ, map_mul, map_pow, map_neg, map_one]
  · assumption
  · assumption
  · rwa [natDegree_map_eq_of_injective hφ]

@[simp]
theorem discriminant_map [CharZero K] {L : Type*} [Field L] [CharZero L] (φ : K →+* L) (f : K[X]) :
    discriminant (f.map φ) = φ (discriminant f) := by
  by_cases hf0 : f.natDegree = 0
  · simp [hf0]
  have hf0' : f ≠ 0 := by contrapose! hf0; simp [hf0]
  apply mul_left_cancel₀ ((leadingCoeff_ne_zero.mpr (map_ne_zero hf0')))
  rw [discriminant_def, derivative_map, resultant_map, leadingCoeff_map, ← map_mul,
    discriminant_def,
      natDegree_map, map_mul, map_pow, map_neg, map_one]
  · assumption
  · apply RingHom.injective
  · rwa [natDegree_map]

namespace Splits

theorem eq_fin_prod_roots {L : Type*} [Field L] {φ : K →+* L} {f : K[X]}
    (h : Splits (f.map φ)) :
    f.map φ = C (φ f.leadingCoeff) * ∏ i : Fin (Multiset.card (roots (f.map φ))),
      (X - C ((roots (f.map φ)).toList.get (i.cast (Multiset.length_toList _).symm))) := by
  conv_lhs => rw [Splits.eq_prod_roots h]
  congr 1
  · rw [leadingCoeff_map]
  · rw [← Fintype.prod_equiv (finCongr (Multiset.length_toList _)) _ _ (fun _ => rfl)]
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
    refine Eq.trans ?_ (List.finset_prod_get (map φ f).roots.toList (fun x => X - C x)).symm
    exact (Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))

end Splits

namespace Finset

lemma Iio_union_Ioi {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] [DecidableEq α] (a : α) :
    (Finset.Iio a) ∪ (Finset.Ioi a) = Finset.univ.erase a :=
  Finset.ext (fun _ =>
    ⟨fun h => Finset.mem_erase.mpr ⟨(Finset.mem_union.mp h).casesOn
        (fun h => (Finset.mem_Iio.mp h).ne) (fun h => (Finset.mem_Ioi.mp h).ne'),
          Finset.mem_univ _⟩,
      fun h => Finset.mem_union.mpr ((lt_or_gt_of_ne (Finset.mem_erase.mp h).1).imp
        Finset.mem_Iio.mpr Finset.mem_Ioi.mpr)⟩)

end Finset

namespace Fintype

lemma card_subtype_congr {α : Type*} {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    [Fintype (Subtype p)] [Fintype (Subtype q)] :
    Fintype.card (Subtype p) = Fintype.card (Subtype q) :=
  Fintype.card_congr ((Equiv.refl _).subtypeEquiv e)

end Fintype

namespace Subtype

-- TODO: promote me to instance?
/-- Imported declaration. -/
@[reducible]
noncomputable def fintypeOr {α : Type*} {p q : α → Prop} [Fintype (Subtype p)]
    [Fintype (Subtype q)] :
    Fintype { x // p x ∨ q x } := by
  classical
  exact Fintype.ofSurjective
    (Sum.elim (fun (x : Subtype p) => ⟨x.1, Or.inl x.2⟩) (fun (x : Subtype q) => ⟨x.1, Or.inr x.2⟩))
    (fun x => x.2.casesOn (fun hx => ⟨Sum.inl ⟨x, hx⟩, rfl⟩) (fun hx => ⟨Sum.inr ⟨x, hx⟩, rfl⟩))

end Subtype

namespace Multiset

theorem card_subtype_mem {α : Type*} [DecidableEq α] (s : Multiset α) :
    Fintype.card { x // x ∈ s } = Multiset.card s.dedup := by
  classical
  induction s using Multiset.induction
  case empty =>
    have : IsEmpty { x // x ∈ (0 : Multiset α) } := ⟨fun x => by simpa using x.2⟩
    simp
  case cons a s ih =>
    by_cases h : a ∈ s
    · rw [Fintype.card_subtype_congr (q := (· ∈ s)), ih, Multiset.dedup_cons_of_mem h]
      · simp [h]
    · have : Fintype { x // x = a ∨ x ∈ s } := Subtype.fintypeOr
      rw [Fintype.card_subtype_congr (q := fun x => x = a ∨ x ∈ s),
          Fintype.card_subtype_or_disjoint, Fintype.card_subtype_eq, ih,
          Multiset.dedup_cons_of_notMem h, Multiset.card_cons, add_comm]
      · rintro p hpeq hpmem x hx
        obtain rfl := hpeq _ hx
        exact h (hpmem _ hx)
      · exact fun _ => Multiset.mem_cons

end Multiset

instance {K : Type*} [Field K] : IsIntegrallyClosed K :=
  (isIntegrallyClosed_iff K).mpr (fun {x} _ => ⟨x, rfl⟩)

namespace Finset

omit [NoZeroSMulDivisors ℕ R] in
lemma prod_univ_prod_Iio {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] (f : α → R) :
    ∏ i : α, ∏ j ∈ Finset.Iio i, (f i - f j) =
      ∏ i : α, ∏ j ∈ Finset.Ioi i, (f j - f i) :=
  by
    classical
    exact Finset.prod_comm' (by simp)

end Finset

namespace List

/-- Imported declaration. -/
@[simps!]
def equivFin {α : Type*} [DecidableEq α] {s : List α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin s.length :=
  (List.Nodup.getEquiv s hs).symm

end List

namespace Multiset

@[simp] lemma nodup_toList {α : Type*} {s : Multiset α} :
    s.toList.Nodup ↔ s.Nodup := by
  rw [← Multiset.coe_toList s, Multiset.coe_nodup, Multiset.coe_toList]

/-- Imported declaration. -/
@[simps!]
noncomputable def equivFin {α : Type*} {s : Multiset α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin (Multiset.card s) := by
  classical
  exact ((Equiv.refl _).subtypeEquiv (by simp)).trans
    ((List.equivFin (Multiset.nodup_toList.mpr hs)).trans
    (finCongr (by simp)))

end Multiset

namespace Fin

lemma sum_card_sub_one_sub_self {n : ℕ} :
    ∑ i : Fin n, (n - 1 - (i : ℕ)) = n * (n - 1) / 2 := by
  obtain (⟨⟩ | n) := n
  · simp
  · simp only [← Finset.sum_range, add_tsub_cancel_right, Finset.sum_flip (f := fun x => x),
      Finset.sum_range_id]

end Fin

namespace Algebra

theorem discr_of_isAdjoinRootMonic {K : Type*} [Field K] [Algebra ℚ K] {T : ℚ[X]}
    (f : IsAdjoinRootMonic K T) (hT : Irreducible T) :
    Algebra.discr ℚ (f.powerBasis).basis = Polynomial.discriminant T := by
  classical
  have hT0 : T ≠ 0 := f.monic.ne_zero
  have : FiniteDimensional ℚ K := Module.Finite.of_basis f.powerBasis.basis
  apply RingHom.injective (algebraMap ℚ (AlgebraicClosure ℚ))
  let _ : Fintype (K →ₐ[ℚ] AlgebraicClosure ℚ) := PowerBasis.AlgHom.fintype f.powerBasis
  have nd_aroots' : (aroots (minpoly ℚ f.root) (AlgebraicClosure ℚ)).Nodup :=
    (nodup_aroots_iff_of_splits (minpoly.ne_zero f.isIntegral_root)
      (IsAlgClosed.splits (k := AlgebraicClosure ℚ) _)).mpr
    (minpoly.irreducible f.isIntegral_root).separable
  have card_roots : Multiset.card (map (algebraMap ℚ (AlgebraicClosure ℚ)) T).roots =
    T.natDegree := by
    have hT0_map : map (algebraMap ℚ (AlgebraicClosure ℚ)) T ≠ 0 := map_ne_zero hT0
    have hsplit : (map (algebraMap ℚ (AlgebraicClosure ℚ)) T).Splits :=
      IsAlgClosed.splits (k := AlgebraicClosure ℚ) _
    rw [← natDegree_eq_of_degree_eq_some (hsplit.degree_eq_card_roots hT0_map), natDegree_map]
  have card_aroots : Multiset.card (aroots T (AlgebraicClosure ℚ)) = natDegree T := by
    rw [aroots, card_roots]
  let e : Fin f.powerBasis.dim ≃ (K →ₐ[ℚ] AlgebraicClosure ℚ) := by
    refine (finCongr ?_).trans ((Multiset.equivFin nd_aroots').symm.trans (PowerBasis.liftEquiv'
      f.powerBasis).symm)
    rw [f.minpoly_eq hT, card_aroots, f.powerBasis_dim]
  have e_apply : ∀ i, e i f.root =
      (T.aroots (AlgebraicClosure ℚ)).toList.get (Fin.cast (by simp [card_aroots]) i) := by
    intro i
    rw [← f.powerBasis_gen]
    simp only [e, Equiv.trans_apply, finCongr_apply]
    let y := (Multiset.equivFin nd_aroots').symm
      (Fin.cast (by rw [f.powerBasis_dim, f.minpoly_eq hT, card_aroots]) i)
    change ((PowerBasis.liftEquiv' f.powerBasis).symm y) f.powerBasis.gen = _
    rw [← PowerBasis.liftEquiv'_apply_coe f.powerBasis
      ((PowerBasis.liftEquiv' f.powerBasis).symm y)]
    simp only [Equiv.apply_symm_apply]
    simp [y, f.minpoly_eq hT]
  rw [Algebra.discr_powerBasis_eq_prod _ _ _ e]
  · conv_rhs => rw [← discriminant_map,
      Splits.eq_fin_prod_roots (IsAlgClosed.splits (k := AlgebraicClosure ℚ) _)]
    rw [f.monic.leadingCoeff, map_one, map_one, one_mul, discriminant_prod_X_sub_C,
        ← Fintype.prod_equiv (finCongr card_roots.symm) _ _ (fun _ => rfl)]
    conv_rhs => rw [Finset.prod_congr rfl (fun i _ => by
      rw [← Finset.prod_equiv (s := Finset.univ.erase i)
            (finCongr card_roots.symm)
            (by simp [-finCongr_apply])
            (fun _ _ => rfl),
          ← Finset.Iio_union_Ioi, Finset.prod_union]
      · exact (Finset.disjoint_Ioi_Iio _).symm)]
    simp only [IsAdjoinRootMonic.powerBasis_gen, pow_two, Finset.prod_mul_distrib,
      finCongr_apply, Fin.cast_cast]
    rw [mul_left_comm]
    congr 1
    · rw [Finset.prod_univ_prod_Iio]
      refine Fintype.prod_congr _ _ (fun i => Finset.prod_congr rfl (fun j _ => ?_))
      erw [e_apply, e_apply]
      rfl
    · refine Eq.trans (Fintype.prod_congr _ _ (fun i => Finset.prod_congr rfl (fun j _ => by
        erw [e_apply, e_apply, ← neg_sub, ← neg_one_mul]))) ?_
      simp only [Finset.prod_mul_distrib, Finset.prod_const]
      change ((∏ x : Fin T.natDegree, (-1 : AlgebraicClosure ℚ) ^ (Finset.Ioi x).card) * _) = _
      rw [show (∏ x : Fin T.natDegree, (-1 : AlgebraicClosure ℚ) ^ (Finset.Ioi x).card) =
          (-1) ^ (∑ x : Fin T.natDegree, (Finset.Ioi x).card) by
        exact Finset.prod_pow_eq_pow_sum Finset.univ
          (fun x : Fin T.natDegree => (Finset.Ioi x).card) (-1 : AlgebraicClosure ℚ)]
      simp [aroots_def, Fin.card_Ioi, Fin.sum_card_sub_one_sub_self, card_roots]
      rfl

end Algebra

end Polynomial
