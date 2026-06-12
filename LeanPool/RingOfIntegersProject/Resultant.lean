/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Vieta

import Mathlib.Tactic.Qify

import LeanPool.RingOfIntegersProject.DegreeLT
import LeanPool.RingOfIntegersProject.Homogeneous
import LeanPool.RingOfIntegersProject.PolynomialsAsLists
import LeanPool.RingOfIntegersProject.SylvesterMatrix

/-!
Resultants, Sylvester matrices, and polynomial identities used by the ring-of-integers certificates.
-/

variable {R : Type*}

open Module BigOperators Polynomial Matrix

section general

variable {m n : ℕ}

variable [CommRing R]

/-- R[X]_n is notation for the submodule of polynomials of degree strictly less than n. -/
local notation:9000 R "[x]_" n =>  Polynomial.degreeLT R n

section Preliminaries

@[simp] lemma Fin.last_ne_castSucc {n : ℕ} (i : Fin n) : Fin.last n ≠ i.castSucc := by
  simpa [Fin.ext_iff] using i.2.ne'

lemma Fin.sum_mul_sub_lt_of_apply_zero_lt [NeZero m] {b : Fin m → ℕ}
    (hb : ∑ i, b i = n) (hb0 : b 0 < n) :
    ∑ i, b i * (m - i) < n * m := by
  cases m
  · have := NeZero.out (n := 0)
    contradiction
  rw [Fin.sum_univ_succ] at hb ⊢
  simp only [← hb, val_zero, tsub_zero, add_mul, add_lt_add_iff_left, val_succ, Nat.reduceSubDiff,
      Finset.sum_mul]
  obtain ⟨i, hi⟩ : ∃ i, b (Fin.succ i) ≠ 0 := by
    contrapose! hb
    simpa [hb] using hb0.ne
  exact Finset.sum_lt_sum
    (fun i _ => mul_le_mul_right ((Nat.sub_le _ _).trans (Nat.le_succ _)) _)
    ⟨i, Finset.mem_univ _, (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hi)).mpr
      (Nat.lt_succ_iff.mpr (Nat.sub_le _ _))⟩

lemma lt_of_sum_eq_of_ne {n : ℕ}
    {b : ι → ℕ} {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hs : ∑ i ∈ s, b i = n) (hib : b i ≠ Finsupp.single j n i) (h0 : ∀ i ∈ s, 0 ≤ b i) :
    b j < n := by
  classical
  by_cases hij : i = j
  · rw [hij, Finsupp.single_eq_same] at hib
    exact lt_of_le_of_ne ((Finset.single_le_sum h0 hj).trans_eq hs) hib
  · rw [← hs, ← Finset.add_sum_erase _ _ hj]
    exact lt_add_of_pos_right _ (Finset.sum_pos' (fun i hi => h0 i (Finset.mem_erase.mp hi).2)
      ⟨i, Finset.mem_erase.mpr ⟨hij, hi⟩, lt_of_le_of_ne (h0 _ hi)
        (by
          intro hbi
          apply hib
          simpa [Finsupp.single_eq_of_ne hij] using hbi.symm)⟩)

@[simp] lemma Sum.elim_fin_addCases (f : Fin m → σ) (g : Fin n → σ) (i : Fin (m + n)) :
    Sum.elim f g (Fin.addCases Sum.inl Sum.inr i) = Fin.addCases f g i :=
  Fin.addCases (fun i => by simp) (fun i => by simp) i

lemma Finset.sum_range_cast_mul_two {n : ℕ} :
    (∑ i ∈ Finset.range n, (i : R)) * 2 = n * (n - 1) := by
  cases n
  · simp
  · rw [← Nat.cast_sum, ← Nat.cast_ofNat (n := 2), ← Nat.cast_mul, Finset.sum_range_id_mul_two]
    simp

@[simp] lemma Fin.cast_rfl : Fin.cast (rfl : m = m) = id := rfl

@[simp] lemma finCongr_trans_finCongr {m n o} (h₁ : m = n) (h₂ : n = o) :
  (finCongr h₁).trans (finCongr h₂) = finCongr (h₁.trans h₂) := rfl

lemma Fin.natAdd_zero_right [NeZero m] [NeZero (n + m)] :
    Fin.natAdd n (0 : Fin m) = ⟨n, lt_add_of_pos_right _ (NeZero.pos _)⟩ := rfl

lemma Matrix.det_submatrix {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    (e f : m ≃ n) (M : Matrix n n R) :
    (M.submatrix e f).det = Equiv.Perm.sign (e.symm.trans f) * M.det := by
  rw [← det_permute', ← det_submatrix_equiv_self e, submatrix_submatrix]
  congr
  ext i
  simp

@[simp]
lemma LinearMap.det_toMatrix_eq {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (c : Basis ι R N) :
    det (toMatrix b c f) = LinearMap.det (f ∘ₗ (c.equiv b (Equiv.refl _)).toLinearMap) := by
  rw [← LinearMap.det_toMatrix c, toMatrix_comp _ b, toMatrix_basis_equiv, mul_one]

lemma LinearMap.det_eq_zero_iff_bot_lt_ker {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M]
    (f : M →ₗ[K] M) : LinearMap.det f = 0 ↔ ⊥ < ker f := by
  refine ⟨LinearMap.bot_lt_ker_of_det_eq_zero, fun hf => ?_⟩
  rw [bot_lt_iff_ne_bot, ne_eq, ← isUnit_iff_ker_eq_bot] at hf
  contrapose! hf
  rw [← isUnit_iff_ne_zero, ← LinearMap.det_toMatrix (Module.Free.chooseBasis K M)] at hf
  let e := LinearEquiv.ofIsUnitDet hf
  refine ⟨⟨e, e.symm, ?_, ?_⟩, ?_⟩
  · ext x
    exact e.apply_symm_apply x
  · ext x
    exact e.symm_apply_apply x
  · exact LinearEquiv.coe_ofIsUnitDet hf

lemma LinearMap.det_eq_zero_iff_range_lt_top {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M]
    (f : M →ₗ[K] M) : LinearMap.det f = 0 ↔ range f < ⊤ := by
  rw [LinearMap.det_eq_zero_iff_bot_lt_ker, lt_top_iff_ne_top, ne_eq, ← isUnit_iff_range_eq_top,
      bot_lt_iff_ne_bot, ne_eq, ← isUnit_iff_ker_eq_bot]

lemma Polynomial.IsRoot.X_sub_C_dvd {P : R[X]} {x : R} (hP : IsRoot P x) :
    X - C x ∣ P := by simpa [hP.eq_zero] using X_sub_C_dvd_sub_C_eval (a := x) (p := P)

lemma degreeLT_X_pow_mem (R : Type*) [Semiring R] {n : ℕ} (i : Fin n) :
    (X ^ (i : ℕ) : R[X]) ∈ Polynomial.degreeLT R n := by
  rw [Polynomial.mem_degreeLT]
  exact (degree_X_pow_le i).trans_lt (Nat.cast_lt.mpr i.is_lt)

lemma mul_left_mem_degreeLT' {R : Type*} [Semiring R] {m n : ℕ} (P Q : R[X])
    (hP : P.degree ≤ n) (hQ : Q ∈ Polynomial.degreeLT R m) :
    P * Q ∈ Polynomial.degreeLT R (m + n) := by
  by_cases hP0 : P = 0
  · simp [hP0]
  rw [Polynomial.mem_degreeLT] at hQ ⊢
  refine (degree_mul_le P Q).trans_lt ?_
  simpa [add_comm] using
    WithBot.add_lt_add_of_le_of_lt (degree_ne_bot.mpr hP0) hP hQ

lemma mul_left_mem_degreeLT {R : Type*} [Semiring R] {m n : ℕ} (P Q : R[X])
    (hP : P.degree ≤ m) (hQ : Q ∈ Polynomial.degreeLT R n) :
    P * Q ∈ Polynomial.degreeLT R (m + n) := by
  by_cases hP0 : P = 0
  · simp [hP0]
  rw [Polynomial.mem_degreeLT] at hQ ⊢
  refine (degree_mul_le P Q).trans_lt ?_
  exact WithBot.add_lt_add_of_le_of_lt (degree_ne_bot.mpr hP0) hP hQ

@[simp] lemma finAddFlip_zero_zero : finAddFlip (m := 0) (n := 0) = Equiv.refl _ := by
  ext i
  apply finZeroElim i

lemma coe_finRotate_pow (i) :
    ((finRotate m ^ n) i : ℕ) = (i + n) % m := by
  cases m
  · apply finZeroElim i
  induction n generalizing i
  case zero =>
    simp [Nat.mod_eq_of_lt i.2]
  case succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, coe_finRotate]
    split_ifs with h
    · subst h
      simp [add_left_comm _ n]
    · simp [add_comm, add_left_comm]

lemma coe_finAddFlip (i : Fin (m + n)) :
    (finAddFlip i : ℕ) = if (i : ℕ) < m then i + n else i - m := by
  cases i using Fin.addCases
  · simp [add_comm]
  · simp

lemma finRotate_pow :
    (finRotate _) ^ m = ((finCongr (add_comm m n)).trans finAddFlip) := by
  ext i
  simp only [coe_finRotate_pow, Equiv.trans_apply, finCongr_apply, coe_finAddFlip, Fin.val_cast]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by rw [add_comm]; exact Nat.add_lt_add_left h _)
  · rw [Nat.mod_eq_sub_mod, ← Nat.sub_sub, Nat.add_sub_cancel, Nat.mod_eq_of_lt]
    · exact tsub_lt_of_lt i.prop
    · rw [add_comm]
      exact Nat.add_le_add_left (le_of_not_gt h) _

lemma sign_finAddFlip :
    Equiv.Perm.sign ((finCongr (add_comm m n)).trans finAddFlip) = (-1) ^ (n * m) := by
  rw [← finRotate_pow, map_pow]
  cases n
  case zero =>
    cases m
    case zero =>
      simp
    case succ m =>
      rw [sign_finRotate, ← pow_mul, zero_mul]
      exact (Nat.even_mul_succ_self m).neg_one_pow
  case succ n =>
    dsimp only [Nat.add_succ, Nat.add_zero]
    rw [sign_finRotate, Nat.succ_eq_add_one, ← pow_mul]
    obtain (hm | hm) := Nat.even_or_odd m
    · exact Eq.trans (hm.mul_left (m + n)).neg_one_pow
        (hm.mul_left (n + 1)).neg_one_pow.symm
    obtain (hn | hn) := Nat.even_or_odd n
    · exact Eq.trans ((hm.add_even hn).mul hm).neg_one_pow
        (((hn.add_odd odd_one).mul hm).neg_one_pow).symm
    · exact Eq.trans ((hm.add_odd hn).mul_right m).neg_one_pow
        (((hn.add_odd odd_one).mul_right m).neg_one_pow).symm

lemma intUnitsNegOnePow_cast (k : ℕ) :
    ((↑(((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : R)) = (-1 : R) ^ k := by
  obtain hk | hk := Nat.even_or_odd k
  · rw [hk.neg_one_pow]
    have hk' : ((-1 : ℤˣ) ^ k) = 1 := hk.neg_one_pow
    rw [hk']
    simp
  · rw [hk.neg_one_pow]
    have hk' : ((-1 : ℤˣ) ^ k) = -1 := hk.neg_one_pow
    rw [hk']
    simp

@[simp] lemma finCongr_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) :
    (finCongr hab).trans (finCongr hbc) = finCongr (hab.trans hbc) := rfl

section prod_X_sub_C

variable [Nontrivial R]
@[simp] lemma Polynomial.leadingCoeff_prod_X_sub_C {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))).leadingCoeff = 1 :=
  (leadingCoeff_prod' _ _ (by simp)).trans (by simp)

@[simp] lemma Polynomial.leadingCoeff_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i ∈ s, (X - C (t i))).leadingCoeff = x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [leadingCoeff_mul', leadingCoeff_prod'] <;>
    simp [hx0]

lemma Polynomial.natDegree_prod_X_sub_C {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))).natDegree = s.card :=
  (natDegree_prod' _ _ (by simp)).trans (by simp)

@[simp] lemma Polynomial.natDegree_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → R) (s : Finset σ) {x : R} (hx0 : x ≠ 0) :
    (C x * ∏ i ∈ s, (X - C (t i))).natDegree = s.card := by
  rw [natDegree_mul', natDegree_prod'] <;>
    simp [hx0]

@[simp] lemma Polynomial.natDegree_C_mul_prod_X_sub_C_le
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i ∈ s, (X - C (t i))).natDegree ≤ s.card := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (natDegree_C_mul_prod_X_sub_C _ _ hx0).le

@[simp] lemma Polynomial.prod_X_sub_C_ne_zero {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))) ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simp)

@[simp] lemma Polynomial.C_mul_prod_X_sub_C_ne_zero
    {σ : Type*} (t : σ → R) (s : Finset σ) {x : R} (hx0 : x ≠ 0) :
    (C x * ∏ i ∈ s, (X - C (t i))) ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simpa)

@[simp] lemma Polynomial.coeff_prod_X_sub_C_card {σ : Type*} (t : σ → R) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))).coeff s.card = 1 := by
  simpa only [leadingCoeff, natDegree_prod_X_sub_C] using leadingCoeff_prod_X_sub_C t s

lemma Polynomial.coeff_C_mul_prod_X_sub_C_card
    {σ : Type*} (t : σ → R) (s : Finset σ) (x : R) :
    (C x * ∏ i ∈ s, (X - C (t i))).coeff s.card = x := by
  simp

variable {K : Type*} [Field K]

lemma Polynomial.splits_prod_X_sub_C
    {σ : Type*} (t : σ → K) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))).Splits :=
  Splits.prod fun _ _ => Splits.X_sub_C _

lemma Polynomial.splits_C_mul_prod_X_sub_C
    {σ : Type*} (t : σ → K) (s : Finset σ) (x : K) :
    (C x * ∏ i ∈ s, (X - C (t i))).Splits :=
  (splits_prod_X_sub_C t s).C_mul x

@[simp] lemma Polynomial.roots_prod_X_sub_C'
    {σ : Type*} (t : σ → K) (s : Finset σ) :
    (∏ i ∈ s, (X - C (t i))).roots = s.val.map t := by
  simp only [roots_prod _ _ (Monic.ne_zero (monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))),
    roots_X_sub_C, Multiset.bind_singleton]

lemma Polynomial.roots_C_mul_prod_X_sub_C'
    {σ : Type*} (t : σ → K) (s : Finset σ) {x : K} (hx0 : x ≠ 0) :
    (C x * ∏ i ∈ s, (X - C (t i))).roots = s.val.map t := by
  rw [roots_C_mul _ hx0, roots_prod_X_sub_C']

omit [Nontrivial R]
lemma Polynomial.isRoot_X_sub_C {x y : R} :
    IsRoot (X - C x) y ↔ x = y := by
  simp [sub_eq_zero, eq_comm]

lemma Polynomial.isRoot_prod_X_sub_C [IsDomain R]
    {σ : Type*} {t : σ → R} {s : Finset σ} {x : R} :
    IsRoot (∏ i ∈ s, (X - C (t i))) x ↔ ∃ i ∈ s, x = t i := by
  simp only [isRoot_prod, isRoot_X_sub_C, eq_comm]

lemma Polynomial.isRoot_C_mul_prod_X_sub_C [IsDomain R]
    {σ : Type*} {t : σ → K} {s : Finset σ} {x y : K} :
    IsRoot (C x * ∏ i ∈ s, (X - C (t i))) y ↔ x = 0 ∨ ∃ i ∈ s, y = t i := by
  rw [IsRoot, eval_mul, mul_eq_zero, eval_C, ← IsRoot, isRoot_prod_X_sub_C]

lemma coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) (t : ι → K) j :
    (∏ i ∈ s, (X - C (t i))).coeff j =
      if j ≤ s.card
      then (-1) ^ (s.card - j) * ∑ t_1 ∈ Finset.powersetCard (s.card - j) s, t_1.prod t
      else 0 := by
  split_ifs with hj
  · convert coeff_eq_esymm_roots_of_splits (splits_prod_X_sub_C t _)
        (hj.trans_eq (natDegree_prod_X_sub_C t _).symm)
    · simp
    · simp [Finset.esymm_map_val]
  · exact coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_prod_X_sub_C, ← not_le])

lemma Polynomial.eval_prod_X_sub_C {ι κ : Type*} [Fintype κ]
    (t : ι → K) (u : κ → K) (i : ι) :
    (∏ j, (X - C (u j))).eval (t i) = ∏ j, (t i - u j) := by
  simp only [eval_prod, eval_sub, eval_X, eval_C]

lemma Polynomial.prod_eval_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) :
    ∏ i, (∏ j, (X - C (u j))).eval (t i) = ∏ i, ∏ j, (t i - u j) :=
  Finset.prod_congr rfl (fun i _ => (by simp only [eval_prod, eval_sub, eval_X, eval_C]))

lemma MvPolynomial.eval_prod_prod_X_sub_C {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → K) (u : κ → K) :
    MvPolynomial.eval t (∏ i, (∏ j, (X i - C (u j)))) = ∏ i, ∏ j, (t i - u j) := by
  rw [eval_prod, Fintype.prod_congr]
  · intro i
    simp only [eval_prod, eval_sub, eval_X, eval_C]

end prod_X_sub_C

section eval_of_infinite

lemma MvPolynomial.X_sub_X_dvd_of_rename_eq_zero [IsDomain R]
    {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ R)
    {i j : σ} (h : rename (Function.update id i j) P = 0) :
    X i - X j ∣ P := by
  by_cases hij : i = j
  · subst i
    have hupdate : Function.update id j j = id := by
      funext x
      by_cases hx : x = j <;> simp [Function.update, hx]
    rw [hupdate, rename_id] at h
    rw [show P = 0 by simpa using h]
    exact dvd_zero _
  -- This is a bit of annoying work because we don't have division with remainder
  -- for MvPolynomials yet.
  let τ : Type _ := { x : σ // x ≠ i }
  have hτ : ∀ x : τ, (x : σ) ≠ i := fun x => x.2
  let e : σ ≃ Option τ :=
  { toFun := fun k => if h : k = i then none else some ⟨k, h⟩,
    invFun := fun o => Option.elim o i Subtype.val,
    left_inv := fun k => by by_cases h : k = i <;> simp [h]
    right_inv := fun o => by cases o <;> simp [hτ] }
  have ei : e i = none := dif_pos rfl
  have e_ne_i : ∀ {a} (h : a ≠ i), e a = some ⟨a, h⟩ := fun h => dif_neg h
  have ej : e j = some ⟨j, Ne.symm hij⟩ := e_ne_i _
  rw [← map_dvd_iff ((MvPolynomial.renameEquiv R e).trans (MvPolynomial.optionEquivLeft R τ))]
  simp only [map_sub, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, ei,
    ej, ne_eq, optionEquivLeft_X_some, optionEquivLeft_X_none]
  apply dvd_iff_isRoot.mpr (rename_injective _ Subtype.val_injective _)
  -- Found this rewrite by exploration; there's no useful explanation I can offer for why it works.
  rw [map_zero, ← h, optionEquivLeft_apply, aeval_def, MvPolynomial.polynomial_eval_eval₂,
      eval₂_rename, ← aeval_X_left_apply (rename _ P), aeval_def, algebraMap_eq, eval₂_rename]
  refine (eval₂_comp_left _ _ _ _).trans ?_
  congr
  · ext x
    simp
  · ext a
    by_cases hai : a = i
    · simp [hai, ei]
    simp [e_ne_i, hai]

lemma MvPolynomial.X_sub_X_dvd_of_eval_eq_zero [IsDomain R] [Infinite R]
    {σ : Type*} (P : MvPolynomial σ R)
    {i j : σ} (h : ∀ f, f i = f j → eval f P = 0) :
    X i - X j ∣ P := by
  classical
  apply MvPolynomial.X_sub_X_dvd_of_rename_eq_zero
  apply MvPolynomial.zero_of_eval_zero
  intro f
  specialize h (Function.update f i (f j)) ?_
  · by_cases hij : j = i
    · subst hij
      simp
    rw [Function.update_self, Function.update_of_ne hij]
  rwa [eval_rename, Function.comp_update, Function.comp_id]

end eval_of_infinite

section MvPolynomial

lemma MvPolynomial.intCast_eq_C (a : ℤ) : (a : MvPolynomial σ R) = C (a : R) := rfl

lemma MvPolynomial.coeff_eq_zero_of_dvd_of_support {m : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hqp : q ∣ p) (hqm : ∀ m' ≤ m, m' ∉ support q) :
    coeff m p = 0 := by
  classical
  obtain ⟨p', rfl⟩ := hqp
  rw [coeff_mul, Finset.sum_eq_zero]
  · simp only [Finset.mem_antidiagonal, Prod.forall]
    intro m' _ h
    rw [notMem_support_iff.mp (hqm m' _), zero_mul]
    · rw [← h, Finsupp.le_def]
      intro
      exact Nat.le.intro rfl

lemma MvPolynomial.coeff_eq_zero_of_X_dvd {m : σ →₀ ℕ} {p : MvPolynomial σ R}
    (j : σ) (hjp : X j ∣ p) (hjm : m j = 0) :
    coeff m p = 0 := by
  classical
  obtain ⟨q, rfl⟩ := hjp
  rw [coeff_X_mul', if_neg]
  · simpa

lemma MvPolynomial.eval_snoc (t : ι → R) (v : Fin m →
  MvPolynomial ι R) (x : MvPolynomial ι R) (i) :
    eval t (Fin.snoc (α := fun _ => MvPolynomial ι R) v x i) =
    Fin.snoc (α := fun _ => R) (fun i => eval t (v i)) (eval t x) i := by
  simp [Fin.snoc]
  split_ifs
  · rfl
  · rfl

variable [Nontrivial R]
lemma MvPolynomial.isUnit_C [NoZeroDivisors R] {x : R} :
    IsUnit (C (σ := σ) x) ↔ IsUnit x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  constructor
  · rintro ⟨⟨a, b, ha, hb⟩, rfl⟩
    obtain ⟨c, rfl⟩ := totalDegree_eq_zero_iff_exists_C.mp (show totalDegree b = 0 from
      le_antisymm (by rw [← totalDegree_C_mul_eq hx0, ha, totalDegree_one]) (Nat.zero_le _))
    exact ⟨⟨x, c, C_injective _ _ <| by simpa using ha, C_injective _ _ <| by simpa using hb⟩, rfl⟩
  · rintro ⟨⟨a, b, ha, hb⟩, h⟩
    exact ⟨⟨C a, C b, by simpa using congr_arg C ha, by simpa using congr_arg C hb⟩,
      by simpa using h⟩

lemma MulEquiv.map_irreducible_iff {R S : Type*} [Semiring R] [Semiring S] (f : R ≃* S) {x : R} :
    Irreducible (f x) ↔ Irreducible x := by
  simp only [irreducible_iff]

lemma map_irreducible_iff {F R S : Type*} [Semiring R] [Semiring S] [EquivLike F R S]
    [RingEquivClass F R S] (f : F) {x : R} :
    Irreducible (f x) ↔ Irreducible x := (f : R ≃* S).map_irreducible_iff

omit [Nontrivial R]

lemma MvPolynomial.irreducible_X_sub_X [IsDomain R] {σ : Type*} {i j : σ} (hij : i ≠ j) :
    Irreducible (X i - X j : MvPolynomial σ R) := by
  classical
  let e : MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
    .trans (renameEquiv _ (Equiv.optionSubtypeNe _).symm) (optionEquivLeft _ _)
  convert (map_irreducible_iff e).mp _
  simpa [e, hij.symm] using irreducible_X_sub_C _

lemma MvPolynomial.isRelPrime_X_sub_X_of_ne_left [IsDomain R] {σ : Type*}
    {i i' j j' : σ} (hi : i ≠ i') (hij : i ≠ j) (hi'j' : i' ≠ j') (hij' : i ≠ j') :
    IsRelPrime (X i - X j : MvPolynomial σ R) (X i' - X j') := by
  classical
  refine (MvPolynomial.irreducible_X_sub_X hij).isRelPrime_iff_not_dvd.mpr (mt (fun h => ?_) hi)
  obtain ⟨c, hc⟩ := ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).exists_C_mul_eq_of_dvd
    ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)) h
  have := congr_arg (coeff (Finsupp.single i 1)) hc
  simp only [coeff_C_mul, coeff_sub, coeff_X', ↓reduceIte, Finsupp.single_eq_single_iff, hij.symm,
    and_true, one_ne_zero, and_self, or_self, sub_zero, mul_one, hi.symm, hij'.symm,
    sub_self] at this
  rw [eq_comm, this, map_zero, zero_mul, sub_eq_zero, X_injective.eq_iff] at hc
  contradiction

lemma MvPolynomial.isRelPrime_X_sub_X_of_ne_right [IsDomain R] {σ : Type*}
    {i i' j j' : σ} (hij : i ≠ j) (hi'j' : i' ≠ j') (hi'j : i' ≠ j) (hj : j ≠ j') :
    IsRelPrime (X i - X j : MvPolynomial σ R) (X i' - X j') := by
  rw [← IsRelPrime.neg_left_iff, ← IsRelPrime.neg_right_iff, neg_sub, neg_sub]
  exact isRelPrime_X_sub_X_of_ne_left hj hij.symm hi'j'.symm hi'j.symm

theorem MvPolynomial.eval_esymm_eq_multiset_esymm {σ : Type*} [Fintype σ] (f : σ → R) (n : ℕ) :
    eval f (esymm σ R n) = (Finset.univ.val.map f).esymm n :=
  aeval_esymm_eq_multiset_esymm _ _ _ _

end MvPolynomial

end Preliminaries

/- We define the roiResultant as the determinant of the Sylvester matrix. -/
/-- Imported declaration. -/
def Polynomial.roiResultant (P Q : Polynomial R) := det (Polynomial.sylvesterMatrix P Q)

lemma Polynomial.roiResultant_eq_det_sylvesterMatrix {P Q : Polynomial R}
    (h₁ : P.natDegree = m) (h₂ : Q.natDegree = n) :
    P.roiResultant Q = det (sylvesterMatrixAux m n P Q) := by
  subst h₁ h₂
  rw [roiResultant, sylvesterMatrix]

/-- If `P.degree ≤ n` and `Q.degree ≤ m`, and `(a, b) ∈ R[X]_m × R[X]_n`, then `P * a + Q * b`
is in `R[X]_(m + n)`. -/
lemma sylvester_map_mem_aux {n m : ℕ} {P Q : Polynomial R}
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (a : R[x]_m) (b : R[x]_n) :
    P * a.val + Q * b.val ∈ R[x]_(m + n) := by
  apply add_mem
  · exact mul_left_mem_degreeLT' _ _ hP a.prop
  · exact mul_left_mem_degreeLT _ _ hQ b.prop

/-- We define the linear map R[X]_m × R[X]_n → R[X]_{m + n}
    with (a, b) ↦ P * a + Q * b. -/
@[simps]
noncomputable def sylvesterMap {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) :
    ((R[x]_m) × (R[x]_n)) →ₗ[R] (R[x]_(m + n)) where
  toFun := fun (a, b) ↦ ⟨P * a.val + Q * b.val, sylvester_map_mem_aux hP hQ a b⟩
  map_add' x y := by
    ext
    push_cast
    congr 1
    ring
  map_smul' r a := by
    ext
    simp

@[simp] lemma sylvesterMap_C_mul {n m : ℕ} (a : R) (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (hQ' : (C a * Q).degree ≤ m := by simp [hQ]) :
    sylvesterMap P (C a * Q) hP hQ' =
      (sylvesterMap P Q hP hQ) ∘ₗ (LinearMap.prod (LinearMap.fst _ _ _) (a • LinearMap.snd _ _ _))
        := by
  ext ⟨x, y⟩
  · simp [sylvesterMap]
  · simp [sylvesterMap, mul_assoc]

variable [Nontrivial R]
omit [Nontrivial R] in
@[simp] lemma sylvesterMap_X_pow_zero {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin m) :
    sylvesterMap P Q hP hQ (Polynomial.degreeLT.basis R m i, 0) =
      ⟨P * X ^ (i : ℕ), mul_left_mem_degreeLT' _ _ hP (degreeLT_X_pow_mem R i)⟩ := by
  simp [sylvesterMap, Polynomial.degreeLT.basis_val]

omit [Nontrivial R] in
@[simp] lemma sylvesterMap_zero_X_pow {n m : ℕ} (P Q : Polynomial R)
    (hP : P.degree ≤ n) (hQ : Q.degree ≤ m) (i : Fin n) :
    sylvesterMap P Q hP hQ (0, Polynomial.degreeLT.basis R n i) =
      ⟨Q * X ^ (i : ℕ), mul_left_mem_degreeLT _ _ hQ (degreeLT_X_pow_mem R i)⟩ := by
  simp [sylvesterMap, Polynomial.degreeLT.basis_val]

omit [Nontrivial R] in
/-- The Sylvester matrix is equal to the Sylvester map as a matrix in basis
(1, .., X^(m-1); 1, ..., X^(n-1)) and (1, ..., X^(m+n-1)).
-/
lemma sylvesterMap_toMatrix (P Q : Polynomial R) :
    LinearMap.toMatrix
      (Polynomial.degreeLT.basisProd R P.natDegree Q.natDegree)
      (Polynomial.degreeLT.basis R (P.natDegree + Q.natDegree))
      (sylvesterMap Q P degree_le_natDegree degree_le_natDegree) =
     Polynomial.sylvesterMatrix P Q := by
  ext i j
  rw [sylvesterMatrix, LinearMap.toMatrix_apply, sylvesterMatrixAux, sylvesterMatrixVec,
      transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, Polynomial.degreeLT.basisProd_castAdd, sylvesterMap_X_pow_zero,
        degreeLT.basis_repr, Subtype.coe_mk, coeff_mul_X_pow']
    split_ifs with h₁
    · by_cases h₂ : (i : ℕ) - j ≤ Q.natDegree
      · rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂, toVec_mk, Fin.val_cast]
      · rw [not_le] at h₂
        rw [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂, coeff_eq_zero_of_natDegree_lt]
        assumption
    · rw [sylvesterVec_of_lt]
      simpa using h₁
  · rw [Fin.addCases_right, Polynomial.degreeLT.basisProd_natAdd, sylvesterMap_zero_X_pow,
        degreeLT.basis_repr, Subtype.coe_mk, coeff_mul_X_pow']
    split_ifs with h₁
    · by_cases h₂ : (i : ℕ) - j ≤ P.natDegree
      · rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂, toVec_mk]
      · rw [not_le] at h₂
        rw [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂, coeff_eq_zero_of_natDegree_lt]
        assumption
    · rw [sylvesterVec_of_lt]
      simpa using h₁

omit [Nontrivial R] in
lemma resultant_eq_det_sylvesterMap (P Q : Polynomial R) :
    P.roiResultant Q =
      LinearMap.det ((sylvesterMap Q P degree_le_natDegree degree_le_natDegree) ∘ₗ
        (Polynomial.degreeLT.addLinearEquiv R P.natDegree Q.natDegree).toLinearMap) := by
  rw [roiResultant, ← sylvesterMap_toMatrix, degreeLT.addLinearEquiv,
      LinearMap.det_toMatrix_eq]

variable {K : Type*} [Field K]

lemma resultant_eq_zero_iff {P Q : K[X]} :
    P.roiResultant Q = 0 ↔
      ∃ a : K[x]_Q.natDegree, ∃ b : K[x]_P.natDegree, (a ≠ 0 ∨ b ≠ 0) ∧ P * a + Q * b = 0 := by
  simp only [resultant_eq_det_sylvesterMap, LinearMap.det_eq_zero_iff_bot_lt_ker,
      SetLike.lt_iff_le_and_exists, bot_le, LinearMap.mem_ker, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Submodule.mem_bot,
      true_and, ne_eq]
  constructor
  · rintro ⟨ab, hfab, hab0⟩
    have hab0 := mt (degreeLT.addLinearEquiv K P.natDegree Q.natDegree).map_eq_zero_iff.mp hab0
    set ab := degreeLT.addLinearEquiv K P.natDegree Q.natDegree ab with ab_eq
    obtain ⟨a, b⟩ := ab
    refine ⟨b, a, ?_, ?_⟩
    · simpa [-not_and, not_and_or, or_comm] using hab0
    · simpa [sylvesterMap, add_comm] using hfab
  · rintro ⟨a, b, hab0, hfab⟩
    refine ⟨(degreeLT.addLinearEquiv K P.natDegree Q.natDegree).symm (b, a), ?_, ?_⟩
    · simpa [sylvesterMap, add_comm] using hfab
    · simpa [-not_and, not_and_or, or_comm] using hab0

lemma resultant_ne_zero_iff {P Q : K[X]} :
    P.roiResultant Q ≠ 0 ↔
      ∀ a : K[x]_Q.natDegree, ∀ b : K[x]_P.natDegree, P * a + Q * b = 0 → a = 0 ∧ b = 0 := by
  simpa [-Subtype.exists, -not_and, not_and']
    using not_iff_not.mpr (resultant_eq_zero_iff (P := P) (Q := Q))

omit [Nontrivial R]
@[simp] lemma resultant_C (P : Polynomial R) (x : R) :
    P.roiResultant (C x) = x ^ P.natDegree := by
  rw [roiResultant, sylvesterMatrix_C, det_diagonal, Fin.prod_const, natDegree_C, add_zero]

@[simp] lemma C_resultant (Q : Polynomial R) (x : R) :
    (C x).roiResultant Q = x ^ Q.natDegree := by
  rw [roiResultant, C_sylvesterMatrix, det_diagonal, Fin.prod_const, natDegree_C, zero_add]

@[simp] lemma resultant_zero' (P : Polynomial R) :
    P.roiResultant 0 = 0 ^ P.natDegree := by
  rw [← map_zero C, resultant_C]

@[simp] lemma zero_resultant' (Q : Polynomial R) :
    roiResultant 0 Q = 0 ^ Q.natDegree := by
  rw [← map_zero C, C_resultant]

lemma resultant_zero (P : Polynomial R) (hP : P.natDegree ≠ 0) :
    P.roiResultant 0 = 0 := by
  rw [← map_zero C, resultant_C, zero_pow hP]

lemma zero_resultant (Q : Polynomial R) (hQ : Q.natDegree ≠ 0) :
    roiResultant 0 Q = 0 := by
  rw [← map_zero C, C_resultant, zero_pow hQ]

lemma zero_resultant_zero :
    (0 : R[X]).roiResultant 0 = 1 := by
  rw [← map_zero C, resultant_C, natDegree_C, pow_zero]

@[simp] lemma resultant_one (P : Polynomial R) :
    P.roiResultant 1 = 1 := by
  rw [← C.map_one, resultant_C, one_pow]

@[simp] lemma one_resultant (Q : Polynomial R) :
    roiResultant 1 Q = 1 := by
  rw [← C.map_one, C_resultant, one_pow]

section Nontrivial

variable [Nontrivial R]

@[simp] lemma X_add_C_resultant_X_add_C (x y : R) :
    (X + C x).roiResultant (X + C y) = y - x := by
  rw [roiResultant_eq_det_sylvesterMatrix (natDegree_X_add_C _) (natDegree_X_add_C _),
      sylvesterMatrixAux, toVec_X_add_C, toVec_X_add_C, sylvesterMatrixVec_one]
  simp

/-- Note the condition `hPQ`: if `P` and `Q` are both constant polynomials,
their roiResultant is equal to `1` but we would have to write `1 = P * 0 + Q * 0` because of the
degree restrictions. -/
lemma resultant_eq_comb (P Q : K[X]) (hPQ : 0 < P.natDegree + Q.natDegree) :
    ∃ a : K[x]_Q.natDegree, ∃ b : K[x]_P.natDegree,
      P * a + Q * b = C (Polynomial.roiResultant P Q) := by
  by_cases h0 : P.roiResultant Q = 0
  · obtain ⟨a, b, _hab0, hpq⟩ := resultant_eq_zero_iff.mp h0
    exact ⟨a, b, by simp [h0, hpq]⟩
  have : Function.Surjective (sylvesterMap Q P degree_le_natDegree degree_le_natDegree) := by
    apply Function.Surjective.of_comp
    rwa [resultant_eq_det_sylvesterMap, LinearMap.det_eq_zero_iff_range_lt_top, lt_top_iff_ne_top,
      ne_eq, not_not, LinearMap.range_eq_top, LinearMap.coe_comp] at h0
  obtain ⟨⟨a, b⟩, hab⟩ := this ⟨C (P.roiResultant Q),
          mem_degreeLT.mpr (by rw [degree_C h0]; exact_mod_cast hPQ)⟩
  refine ⟨b, a, ?_⟩
  simpa [Subtype.ext_iff, add_comm] using hab

end Nontrivial

lemma resultant_swap (P Q : Polynomial R) :
    P.roiResultant Q = (-1) ^ (P.natDegree * Q.natDegree) * Q.roiResultant P := by
  rw [roiResultant, sylvesterMatrix, sylvesterMatrixAux, roiResultant, sylvesterMatrix,
      sylvesterMatrixAux, sylvesterMatrixVec_swap, reindex_apply, det_submatrix]
  simp only [finCongr_symm, finAddFlip_symm, sign_finAddFlip]
  rw [intUnitsNegOnePow_cast (R := R)]

lemma C_mul_resultant [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≠ 0) :
    (C a * P).roiResultant Q = a ^ Q.natDegree * P.roiResultant Q := by
  by_cases ha : a = 0
  · rw [ha, map_zero, zero_mul, zero_resultant _ hQ, zero_pow hQ, zero_mul]
  · rw [roiResultant, sylvesterMatrix, sylvesterMatrixAux, toVec_C_mul, sylvesterMatrixVec_smul,
        det_mul_row, roiResultant, sylvesterMatrix]
    congr 1
    · simp only [Fin.prod_univ_add, Fin.addCases_left, Finset.prod_const_one, one_mul,
          Fin.addCases_right, Fin.prod_const]
    · have : P.natDegree = (C a * P).natDegree := by rw [natDegree_C_mul ha]
      rw [sylvesterMatrixAux, this]

lemma C_mul_resultant' [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hQ : Q.natDegree ≠ 0) (h : Q.natDegree = n) :
    (C a * P).roiResultant Q = a ^ n * P.roiResultant Q := by
  rw [C_mul_resultant, h]
  · assumption

lemma resultant_C_mul [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hP : P.natDegree ≠ 0) :
    P.roiResultant (C a * Q) = a ^ P.natDegree * P.roiResultant Q := by
  by_cases ha : a = 0
  · simp [ha, hP]
  rw [resultant_swap, C_mul_resultant _ _ _ hP, resultant_swap P Q, natDegree_C_mul ha,
      mul_left_comm]

lemma resultant_C_mul' [NoZeroDivisors R] (a : R) (P Q : Polynomial R)
    (hP : P.natDegree ≠ 0) (h : m = P.natDegree) :
    P.roiResultant (C a * Q) = a ^ m * P.roiResultant Q := by
  rw [resultant_C_mul, h]
  · assumption

theorem resultant_map {S : Type*} [CommRing S] {φ : R →+* S} (hφ : Function.Injective φ)
    (f g : R[X]) :
    roiResultant (f.map φ) (g.map φ) = φ (roiResultant f g) := by
  by_cases hf0 : f = 0 <;> by_cases hg0 : g = 0
  · simp [hf0, hg0]
  · rw [hf0, Polynomial.map_zero, ← map_zero C, C_resultant, natDegree_map_eq_of_injective,
        ← map_zero C, C_resultant, map_pow, map_zero]
    · assumption
  · rw [hg0, Polynomial.map_zero, ← map_zero C, resultant_C, natDegree_map_eq_of_injective,
        ← map_zero C, resultant_C, map_pow, map_zero]
    · assumption
  rw [roiResultant_eq_det_sylvesterMatrix
        (natDegree_map_eq_of_injective hφ _)
        (natDegree_map_eq_of_injective hφ _),
      roiResultant, sylvesterMatrixAux, toVec_map, toVec_map,
      sylvesterMatrixVec_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      sylvesterMatrix, sylvesterMatrixAux]

lemma resultant_eq_zero_of_root_aux {P Q : K[X]} {x : K} (hP0 : P ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) :
    P.roiResultant Q = 0 := by
  obtain ⟨a, rfl⟩ := hP.X_sub_C_dvd
  obtain ⟨b, rfl⟩ := hQ.X_sub_C_dvd
  have ha : a ≠ 0 := right_ne_zero_of_mul hP0
  by_cases hb : b = 0
  · rw [hb, mul_zero, resultant_zero]
    · rw [natDegree_mul (monic_X_sub_C _).ne_zero ha, natDegree_X_sub_C,
          add_comm]
      exact Nat.succ_ne_zero a.natDegree
  refine resultant_eq_zero_iff.mpr
    ⟨⟨b, mem_degreeLT.mpr (degree_le_natDegree.trans_lt ?_)⟩,
     ⟨-a, mem_degreeLT.mpr (degree_le_natDegree.trans_lt ?_)⟩,
     by simp [hb], ?_⟩
  · rw [natDegree_mul (monic_X_sub_C _).ne_zero hb, natDegree_X_sub_C, add_comm, Nat.cast_lt]
    · exact Nat.lt_succ_self _
  · rw [natDegree_mul (monic_X_sub_C _).ne_zero ha, natDegree_X_sub_C, natDegree_neg, add_comm,
        Nat.cast_lt]
    · exact Nat.lt_succ_self _
  · simp [mul_right_comm]

lemma resultant_eq_zero_of_root [IsDomain R] {P Q : R[X]} {x : R} (hP0 : P ≠ 0)
    (hP : IsRoot P x) (hQ : IsRoot Q x) :
    P.roiResultant Q = 0 := by
  have := IsFractionRing.injective R (FractionRing R)
  apply this
  rw [← resultant_map this, resultant_eq_zero_of_root_aux, map_zero]
  · exact mt (Polynomial.map_eq_zero_iff this).mp hP0
  · exact hP.map
  · exact hQ.map

section AsPolynomial

/-! Interpret the roiResultant as a multivariate polynomial in the coefficients and in the roots. -/

/-- The determinant as a multivariate polynomial in the matrix entries. -/
noncomputable def MvPolynomial.det {ι : Type*} [DecidableEq ι] [Fintype ι] :
    MvPolynomial (ι × ι) R :=
  ∑ σ : Equiv.Perm ι, C (Equiv.Perm.sign σ : R) * ∏ (i : ι), X (σ i, i)

lemma MvPolynomial.eval_det {ι : Type*} [DecidableEq ι] [Fintype ι] (M : Matrix ι ι R) :
    MvPolynomial.eval (fun ij => M ij.1 ij.2) MvPolynomial.det = M.det := by
  simp [MvPolynomial.det, Matrix.det_apply, Units.smul_def]

@[simp]
lemma MvPolynomial.eval_det' {ι : Type*} [DecidableEq ι] [Fintype ι] (M : ι × ι → R) :
    MvPolynomial.eval M MvPolynomial.det = (Matrix.of fun i j => M (i, j)).det := by
  simp [MvPolynomial.det, Matrix.det_apply, Units.smul_def]

@[simp]
lemma MvPolynomial.aeval_det {S ι : Type*} [CommRing S] [Algebra R S] [DecidableEq ι] [Fintype ι]
    (M : ι × ι → S) :
    MvPolynomial.aeval M (MvPolynomial.det (R := R)) = (Matrix.of fun i j => M (i, j)).det := by
  simp [MvPolynomial.det, Matrix.det_apply, Units.smul_def]

variable {σ : Type*}

/-- We can express each coefficient of a polynomial in terms of its roots. -/
noncomputable def coeffOfRoots {ι : Type*} [Fintype ι] (i : Fin (Fintype.card ι)) :
    MvPolynomial ι R :=
  (-1) ^ (Fintype.card ι - ↑i) * MvPolynomial.esymm _ _ (Fintype.card ι - i)

/-- We can express each coefficient of a polynomial in terms of its roots. -/
lemma MvPolynomial.map_coeffOfRoots {ι S : Type*} [Fintype ι] [CommRing S] (f : R →+* S)
    (i : Fin (Fintype.card ι)) :
    map f (coeffOfRoots (R := R) i) = coeffOfRoots i := by
  rw [coeffOfRoots, _root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one,
      map_esymm, coeffOfRoots]

lemma MvPolynomial.isHomogeneous_coeffOfRoots {ι : Type*} [Fintype ι] (i : Fin (Fintype.card ι)) :
    IsHomogeneous (coeffOfRoots (R := R) i) (Fintype.card ι - i) := by
  simpa [coeffOfRoots] using
    (isHomogeneous_C _ ((-1 : R) ^ (Fintype.card ι - i))).mul isHomogeneous_esymm

lemma MvPolynomial.isWeightedHomogeneous_coeffOfRoots {ι : Type*} [Fintype ι]
    (i : Fin (Fintype.card ι)) :
    IsWeightedHomogeneous (fun _ => 1) (coeffOfRoots (R := R) i) (Fintype.card ι - i) := by
  exact isHomogeneous_coeffOfRoots i

lemma MvPolynomial.eval_coeffOfRoots [IsDomain R] {ι : Type*} [Fintype ι] (t : ι → R)
    (i : Fin (Fintype.card ι)) :
    MvPolynomial.eval t (coeffOfRoots i) = Polynomial.coeff (∏ i,
      (Polynomial.X - Polynomial.C (t i))) i := by
  apply (IsFractionRing.injective _ (FractionRing R))
  simp only [← Polynomial.coeff_map (algebraMap R _), Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
  conv_lhs => rw [← eval₂_id, eval₂_comp_left, RingHom.comp_id, ← eval_map]
  conv_rhs =>
    rw [← one_mul (∏ _, _), ← _root_.map_one Polynomial.C,
        coeff_eq_esymm_roots_of_splits (splits_C_mul_prod_X_sub_C (fun i => algebraMap R
          (FractionRing R) (t i)) _ _)]
    · rfl
    · exact i.prop.le.trans_eq (natDegree_C_mul_prod_X_sub_C _ _ one_ne_zero).symm
  rw [map_coeffOfRoots, coeffOfRoots, eval_mul, eval_esymm_eq_multiset_esymm]
  simp

lemma ofVec_coeffOfRoots_one [IsDomain R] {ι : Type*} [Fintype ι] (t : ι → R) :
    ofVec (Fin.snoc (fun i => MvPolynomial.eval t (coeffOfRoots i)) 1) = ∏ i, (X - C (t i)) := by
  ext i
  rw [coeff_ofVec]
  split_ifs with hi
  · conv_rhs => rw [← Fin.val_mk hi]
    cases hi
    case pos.refl =>
      exact (Fin.snoc_last _ _).trans (coeff_prod_X_sub_C_card t Finset.univ).symm
    case pos.step h =>
      exact (Fin.snoc_castSucc _ _ ⟨i, h⟩).trans (MvPolynomial.eval_coeffOfRoots t ⟨i, h⟩)
  · exact (coeff_eq_zero_of_natDegree_lt ((natDegree_prod_X_sub_C t _).trans_lt (lt_of_not_ge (mt
    Nat.lt_succ_iff.mpr hi)))).symm

lemma ofVec_coeffOfRoots_smul [IsDomain R] {ι : Type*} [Fintype ι] (x : R) (t : ι → R) :
    ofVec (Fin.snoc (fun i => MvPolynomial.eval t (x • coeffOfRoots i)) x) = C x * ∏ i,
      (X - C (t i)) := by
  ext i
  rw [coeff_ofVec]
  split_ifs with hi
  · conv_rhs => rw [← Fin.val_mk hi]
    cases hi
    case pos.refl =>
      exact (Fin.snoc_last _ _).trans (coeff_C_mul_prod_X_sub_C_card t Finset.univ x).symm
    case pos.step h =>
      refine (Fin.snoc_castSucc _ _ ⟨i, h⟩).trans ?_
      simp only [MvPolynomial.smul_eval, coeff_C_mul, mul_eq_mul_left_iff]
      rw [(MvPolynomial.eval_coeffOfRoots t ⟨i, h⟩)]
      exact Or.inl rfl
  · exact (coeff_eq_zero_of_natDegree_lt ((natDegree_C_mul_prod_X_sub_C_le t _ _).trans_lt
            (lt_of_not_ge (mt Nat.lt_succ_iff.mpr hi)))).symm

lemma MvPolynomial.eval_prod_prod_X_sub_C' {ι κ : Type*} [Fintype κ]
    (t : ι → K) (u : κ → K) (i : ι) :
    ∏ x : κ, (t i - u x) = (MvPolynomial.eval (MvPolynomial.eval u ∘ (Fin.snoc coeffOfRoots 1)))
      (∑ j : Fin (_ + 1), MvPolynomial.C (t i ^ (j : ℕ)) * MvPolynomial.X j) := by
  simp only [map_pow, map_sum, _root_.map_mul, eval_C, eval_X, Function.comp_apply]
  rw [← Polynomial.eval_prod_X_sub_C, Polynomial.eval_eq_sum_range, natDegree_prod_X_sub_C,
    Finset.card_univ, Finset.sum_range, Fintype.sum_congr _ _ (fun j => ?_)]
  rw [mul_comm]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.val_last, Fin.snoc_last, ← Finset.card_univ, coeff_prod_X_sub_C_card, _root_.map_one]
  · simp [eval_coeffOfRoots]


/-- The roiResultant as a multivariate polynomial in the coefficients of two polynomials.

Note that this only equals the actual roiResultant if the leading coefficients are nonzero.
-/
noncomputable def resultantPolynomialCoeff :
    MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) R :=
  MvPolynomial.bind₁
    (fun ij => sylvesterMatrixVec (fun i => MvPolynomial.X (Sum.inr i)) (fun i => MvPolynomial.X
      (Sum.inl i)) ij.1 ij.2)
    MvPolynomial.det

@[simp] lemma MvPolynomial.aeval_sylvesterVec {ι S : Type*} [CommRing S] [Algebra R S]
    (v : Fin (n + 1) → MvPolynomial ι R) (t : ι → S) (i : Fin m) (j) :
    MvPolynomial.aeval t (sylvesterVec v i j) =
      sylvesterVec (fun i => aeval t (v i)) i j := by
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp [sylvesterVec_of_lt _ _ _ h]
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) n
    case inl h₂ =>
      simp [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
    case inr h₂ =>
      simp [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]

@[simp] lemma MvPolynomial.aeval_sylvesterMatrixVec {ι S : Type*} [CommRing S] [Algebra R S]
    (v : Fin (m + 1) → MvPolynomial ι R) (w : Fin (n + 1) → MvPolynomial ι R)
    (t : ι → S) (i j) :
    MvPolynomial.aeval t (sylvesterMatrixVec v w i j) =
      sylvesterMatrixVec (fun i => aeval t (v i)) (fun j => aeval t (w j)) i j := by
  unfold sylvesterMatrixVec
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp
  · simp

@[simp] lemma MvPolynomial.eval_sylvesterMatrixVec {ι : Type*}
    (v : Fin (m + 1) → MvPolynomial ι R) (w : Fin (n + 1) → MvPolynomial ι R)
    (t : ι → R) (i j) :
    MvPolynomial.eval t (sylvesterMatrixVec v w i j) =
      sylvesterMatrixVec (fun i => eval t (v i)) (fun j => eval t (w j)) i j :=
  aeval_sylvesterMatrixVec v w t i j

@[simp] lemma MvPolynomial.eval_resultantPolynomialCoeff
    (tu : (Fin (m + 1) ⊕ Fin (n + 1)) → R)
    (hl : tu (Sum.inl (Fin.last m)) ≠ 0) (hr : tu (Sum.inr (Fin.last n)) ≠ 0) :
    MvPolynomial.eval tu resultantPolynomialCoeff =
    (ofVec (fun i => tu (Sum.inl i))).roiResultant (ofVec (fun i => tu (Sum.inr i))) := by
  rw [resultantPolynomialCoeff, eval_bind₁, eval_det',
    roiResultant_eq_det_sylvesterMatrix (natDegree_ofVec hl) (natDegree_ofVec hr),
    sylvesterMatrixAux]
  congr 1
  ext i j
  rw [toVec_ofVec', toVec_ofVec', of_apply, eval_sylvesterMatrixVec]
  congr <;>
  · ext
    apply eval_X

lemma resultant_eq_eval_resultantPolynomialCoeff (f g : R[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    roiResultant f g = MvPolynomial.eval
      (Sum.elim (f.toVec (f.natDegree + 1)) (g.toVec (g.natDegree + 1)))
      resultantPolynomialCoeff := by
  rw [MvPolynomial.eval_resultantPolynomialCoeff]
  · simp
  · simp [hf0]
  · simp [hg0]

lemma sylvesterMatrixVec_row_zero {m n : ℕ} (f : Fin (m + 1 + 1) → R) (g : Fin (n + 1 + 1) → R)
    (j : Fin (n.succ + m.succ)) :
    sylvesterMatrixVec f g (0 : Fin (n.succ + m).succ) j =
      if (j : ℕ) = 0 then f 0 else if (j : ℕ) = n + 1 then g 0 else 0 := by
  rw [sylvesterMatrixVec]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Nat.succ_eq_add_one, transpose_apply, of_apply, Fin.addCases_left, Fin.cast_zero,
      Fin.val_castAdd]
    split_ifs with h
    · have : j = 0 := by ext; exact h
      simp only [this, sylvesterVec_zero]
      exact Fin.pad_of_lt _ _ _ _
    · have := j.2.ne
      contradiction
    · rw [sylvesterVec_of_lt]
      exact Nat.pos_of_ne_zero h
  · simp only [Nat.succ_eq_add_one, transpose_apply, of_apply, Fin.addCases_right,
    Fin.val_natAdd, add_eq_zero, one_ne_zero, and_false, false_and, add_eq_left, ↓reduceIte]
    split_ifs with h
    · have : j = 0 := by ext; exact h
      simp only [this, sylvesterVec_zero]
      exact Fin.pad_of_lt _ _ _ _
    · rw [sylvesterVec_of_lt]
      exact Nat.pos_of_ne_zero h

/-- The roiResultant is weighted homogeneous. -/
theorem det_sylvesterMatrixVec_pow_mul (c : R)
    (f : Fin (m + 1) → R) (g : Fin (n + 1) → R) :
    (of fun i j ↦
          sylvesterMatrixVec (fun i ↦ c ^ (n - ↑i) * g i) (fun j ↦ c ^ (m - ↑j) * f j) i j).det =
      c ^ (m * n) * (of fun i j ↦ sylvesterMatrixVec (fun i ↦ g i) (fun j ↦ f j) i j).det := by
  rw [det_apply, det_apply, Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun σ => ?_)
  rw [mul_smul_comm, Fin.prod_univ_add, Fin.prod_univ_add]
  -- For some reason the subtraction operator gets unfolded, tell `simp` to refold it.
  have : ∀ R (i j : Fin R), (i.sub j) = i - j := fun _ _ _ => rfl
  -- Generalize to sequences of natural numbers so we don't have such a mess of fin casts.
  let f' : ℕ → R := fun i => if h : i < m + 1 then f ⟨i, h⟩ else 0
  have f_apply : ∀ i, f i = f' i := fun i => by
    dsimp [f']
    rw [if_pos i.is_lt]
  let g' : ℕ → R := fun i => if h : i < n + 1 then g ⟨i, h⟩ else 0
  have g_apply : ∀ i, g i = g' i := fun i => by
    dsimp [g']
    rw [if_pos i.is_lt]
  simp only [sylvesterMatrixVec, sylvesterVec_def, f_apply, g_apply,
    Fin.val_cast, tsub_le_iff_right, dite_eq_ite, transpose_apply, of_apply,
    Fin.addCases_left, Fin.addCases_right, smul_left_cancel_iff]
  -- If the `if` conditions are ever false, both sides are `0` and we are done.
  by_cases hil : ∀ i, i ≤ (σ (Fin.castAdd n i) : ℕ)
  swap
  · obtain ⟨i, hi⟩ := not_forall.mp hil
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Finset.prod_eq_zero (Finset.mem_univ i), zero_mul,
      zero_mul, mul_zero]
      <;> simp [hi]
  by_cases hir : ∀ i, ↑(σ (Fin.castAdd n i)) ≤ n + ↑i
  swap
  · obtain ⟨i, hi⟩ := not_forall.mp hir
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Finset.prod_eq_zero (Finset.mem_univ i), zero_mul,
      zero_mul, mul_zero]
      <;> simp [hi]
  by_cases hjl : ∀ j, j ≤ (σ (Fin.natAdd m j) : ℕ)
  swap
  · obtain ⟨j, hj⟩ := not_forall.mp hjl
    rw [Finset.prod_eq_zero (Finset.mem_univ j), Finset.prod_eq_zero (Finset.mem_univ j), mul_zero,
      mul_zero, mul_zero]
      <;> simp [hj]
  by_cases hjr : ∀ j, ↑(σ (Fin.natAdd m j)) ≤ m + ↑j
  swap
  · obtain ⟨j, hj⟩ := not_forall.mp hjr
    rw [Finset.prod_eq_zero (Finset.mem_univ j), Finset.prod_eq_zero (Finset.mem_univ j), mul_zero,
      mul_zero, mul_zero]
      <;> simp [hj]
  -- So consider the case where the conditions are always true, and pull the powers of `c` outside.
  simp only [← mul_ite_zero, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [mul_assoc, mul_left_comm _ (c ^ _), ← mul_assoc, ← pow_add]
  -- Then both sides become a power of `c` times the same thing, with the exponent equal to the sum
  -- of all the exponents in each term.
  congr 2
  -- Because we can assume the `if` conditions are always true, we have real subtraction.
  zify
  rw [Fintype.sum_congr _ (fun i => (n : ℤ) - ((σ (Fin.castAdd n i)) - i)) (fun _ => ?_),
      Fintype.sum_congr _ (fun j => (m : ℤ) - ((σ (Fin.natAdd m j)) - j)) (fun _ => ?_)]
  swap
  · rw [Nat.cast_sub (Nat.sub_le_of_le_add (hjr _)), Nat.cast_sub (hjl _)]
  swap
  · rw [Nat.cast_sub (Nat.sub_le_of_le_add (hir _)), Nat.cast_sub (hil _)]
  -- And all the sums come down to `∑ 0 ≤ i < k, i` with different `k`.
  -- But because `1/2 * (k - 1) * k` is more annoying to work with than `(k - 1) * k`,
  -- we'll multiply all terms by 2.
  apply mul_right_cancel₀ two_ne_zero
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_mul]
  rw [← Finset.sum_range, Finset.sum_range_cast_mul_two,
      ← Finset.sum_range, Finset.sum_range_cast_mul_two,
      add_left_comm (Finset.sum _ _ * _), add_left_comm (Finset.sum _ _ * _), ← add_mul,
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← neg_add, neg_mul,
      ← Fin.sum_univ_add (f := fun i => ((σ i : ℕ) : ℤ)),
      Fintype.sum_equiv σ _ (fun i => ((i : ℕ) : ℤ)) (fun _ => rfl),
      ← Finset.sum_range, Finset.sum_range_cast_mul_two,
      Nat.cast_add]
  ring

/-- The roiResultant as a polynomial in the coefficients is weighted homogeneous with weights
`n - i` for the `i`th coefficient. -/
lemma MvPolynomial.isWeightedHomogeneous_coeffDegree_resultantPolynomialCoeff [Infinite R]
    [IsDomain R] :
    IsWeightedHomogeneous
      (Sum.elim
        (fun (i : Fin (m + 1)) => m - (i : ℕ))
        (fun (j : Fin (n + 1)) => n - (j : ℕ)))
      (resultantPolynomialCoeff (R := R)) (m * n) :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    -- Note that we can't quite reuse the theorem about the roiResultant function being homogeneous,
    -- since we also need to care about the case where the leading coefficient is zero.
    calc
    _ = (of fun (i : Fin _) (j : Fin _) => sylvesterMatrixVec (fun i ↦ c ^ (n - i) *
      f (Sum.inr i)) (fun j => c ^ (m - j) * f (Sum.inl j)) i j).det := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [-sylvesterMatrixVec_smul, -smul_sylvesterMatrixVec]
    _ = c ^ (m * n) * (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl
      j)) i j).det :=
      det_sylvesterMatrixVec_pow_mul c (fun i => f (Sum.inl i)) (fun i => f (Sum.inr i))
    _ = _ := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialCoeff [Infinite R] [IsDomain R] :
    IsWeightedHomogeneous (Sum.elim (fun (_ : Fin (m + 1)) => (m + 1)) (fun (_ : Fin (n +
      1)) => (n + 1)))
      (resultantPolynomialCoeff (R := R)) (n * (m + 1) + m * (n + 1)) :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    -- Note that we can't quite reuse the theorem about the roiResultant function being homogeneous,
    -- since we also need to care about the case where the leading coefficient is zero.
    calc
    _ = (of fun i j ↦ sylvesterMatrixVec (c ^ (n + 1) • fun i ↦ f (Sum.inr i)) (c ^ (m +
      1) • fun j ↦ f (Sum.inl j)) i j).det := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [-sylvesterMatrixVec_smul, -smul_sylvesterMatrixVec]
      rfl
    _ = c ^ ((m + 1) * n) * (c ^ ((n + 1) * m) *
      (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl j)) i j).det) :=
        by
      rw [sylvesterMatrixVec_smul, smul_sylvesterMatrixVec]
      simp only [of_apply]
      convert det_mul_row _ _ using 2
      · simp [Fin.prod_univ_add, pow_mul]
      · convert (det_mul_row (Fin.addCases (fun _ => c ^ (n + 1)) (fun _ => 1)) _).symm using 2
        · simp [Fin.prod_univ_add, pow_mul]
    _ = _ := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [mul_assoc, pow_add, mul_comm, mul_left_comm]

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialCoeff_left [Infinite R] [IsDomain R] :
    IsWeightedHomogeneous (Sum.elim (fun (_ : Fin (m + 1)) => 1) (fun (_ : Fin (n + 1)) => 0))
      (resultantPolynomialCoeff (R := R)) n :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    calc
    _ = (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (c • fun j ↦ f (Sum.inl j)) i
      j).det := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [-sylvesterMatrixVec_smul, -smul_sylvesterMatrixVec]
      rfl
    _ = c ^ n * (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl j)) i
      j).det := by
      rw [sylvesterMatrixVec_smul]
      simp only [of_apply]
      convert det_mul_row _ _ using 2
      · simp [Fin.prod_univ_add]
    _ = _ := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialCoeff_right [Infinite R] [IsDomain R] :
    IsWeightedHomogeneous (Sum.elim (fun (_ : Fin (m + 1)) => 0) (fun (_ : Fin (n + 1)) => 1))
      (resultantPolynomialCoeff (R := R)) m :=
  isWeightedHomogeneous_iff_eval_smul_eq_pow_smul.mpr fun c f => by
    calc
    _ = (of fun i j ↦ sylvesterMatrixVec (c • fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl j)) i
      j).det := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp [-sylvesterMatrixVec_smul, -smul_sylvesterMatrixVec]
      rfl
    _ = c ^ m * (of fun i j ↦ sylvesterMatrixVec (fun i ↦ f (Sum.inr i)) (fun j ↦ f (Sum.inl j)) i
      j).det := by
      rw [smul_sylvesterMatrixVec]
      simp only [of_apply]
      convert det_mul_row _ _ using 2
      · simp [Fin.prod_univ_add]
    _ = _ := by
      rw [resultantPolynomialCoeff, eval_bind₁, eval_det']
      simp

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The roiResultant as a multivariate polynomial in the roots of two monic polynomials. -/
noncomputable def resultantPolynomialRoots : MvPolynomial (ι ⊕ κ) R :=
  MvPolynomial.bind₁ (Sum.elim
      (Fin.snoc (fun i => MvPolynomial.rename Sum.inl (coeffOfRoots i)) 1)
      (Fin.snoc (fun i => MvPolynomial.rename Sum.inr (coeffOfRoots i)) 1))
    resultantPolynomialCoeff

@[simp] lemma MvPolynomial.eval_resultantPolynomialRoots [IsDomain R] (tu : ι ⊕ κ → R) :
    MvPolynomial.eval tu resultantPolynomialRoots =
    (∏ i, (Polynomial.X - Polynomial.C (tu (Sum.inl i)))).roiResultant
      (∏ i, (Polynomial.X - Polynomial.C (tu (Sum.inr i)))) := by
  simp [resultantPolynomialRoots, eval_bind₁, eval_resultantPolynomialCoeff, eval_rename,
    Function.comp, ofVec_coeffOfRoots_one, MvPolynomial.eval_snoc]

lemma resultantPolynomialRoots_of_isEmpty_left [IsEmpty ι] [Infinite R] [IsDomain R] :
    resultantPolynomialRoots (R := R) (ι := ι) (κ := κ) = MvPolynomial.C 1 :=
  MvPolynomial.eq_of_eval_eq _ _ fun x => by simp

lemma resultantPolynomialRoots_of_isEmpty_right [IsEmpty κ] [Infinite R] [IsDomain R] :
    resultantPolynomialRoots (R := R) (ι := ι) (κ := κ) = MvPolynomial.C 1 :=
  MvPolynomial.eq_of_eval_eq _ _ fun x => by simp

theorem prod_root_differences_dvd_resultantPolynomialRoots [Infinite R] [IsDomain R]
    [UniqueFactorizationMonoid R] :
    ∏ (i : ι), ∏ (j : κ), (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr j)) ∣
      (resultantPolynomialRoots (R := R)) :=
  by
    classical
    exact Finset.prod_dvd_of_isRelPrime
      (fun i _ j _ hij => IsRelPrime.prod_left fun i' _ => IsRelPrime.prod_right fun j' _ =>
        MvPolynomial.isRelPrime_X_sub_X_of_ne_left
          (Sum.inl_injective.ne hij)
          Sum.inl_ne_inr
          Sum.inl_ne_inr
          Sum.inl_ne_inr)
      (fun i _ => Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij =>
        MvPolynomial.isRelPrime_X_sub_X_of_ne_right
          Sum.inl_ne_inr
          Sum.inl_ne_inr
          Sum.inl_ne_inr
          (Sum.inr_injective.ne hij))
        (fun j _ => MvPolynomial.X_sub_X_dvd_of_eval_eq_zero _ (fun tu hij => by
          rw [MvPolynomial.eval_resultantPolynomialRoots, resultant_eq_zero_of_root]
          · exact prod_X_sub_C_ne_zero _ _
          · exact isRoot_prod_X_sub_C.mpr ⟨i, Finset.mem_univ _, rfl⟩
          · exact isRoot_prod_X_sub_C.mpr ⟨j, Finset.mem_univ _, hij⟩)))

omit [Fintype ι] [Fintype κ] in
lemma Finset.prod_prod_sub_swap (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    ∏ i ∈ s, ∏ j ∈ t, (f i - g j) = (-1) ^ (s.card * t.card) * ∏ j ∈ t, ∏ i ∈ s, (g j - f i) := by
  rw [prod_comm, pow_mul, ← prod_const, ← prod_mul_distrib, prod_congr rfl (fun j _ => ?_)]
  rw [← prod_const, ← prod_mul_distrib, prod_congr rfl (fun i _ => ?_)]
  rw [neg_one_mul, neg_sub]

lemma MvPolynomial.isWeightedHomogeneous_prod_root_differences :
    IsWeightedHomogeneous (R := R) (fun (_ : ι ⊕ κ) => 1)
      (∏ i, ∏ j, (X (Sum.inl i) - X (Sum.inr j)))
      (Fintype.card ι * Fintype.card κ) := by
  convert IsWeightedHomogeneous.prod Finset.univ (fun i => ∏ j,
    (X (Sum.inl i) - X (Sum.inr j))) (fun _ => Fintype.card κ) _
  · simp
  intro i _
  convert IsWeightedHomogeneous.prod Finset.univ (fun j => X (Sum.inl i) - X (Sum.inr j)) (fun _ =>
    1) _
  · simp
  intro j _
  exact (isWeightedHomogeneous_X _ _ _).sub (isWeightedHomogeneous_X _ _ _)

lemma MvPolynomial.isWeightedHomogeneous_resultantPolynomialRoots [IsDomain R] [Infinite R] :
    IsWeightedHomogeneous (fun (_ : ι ⊕ κ) => 1)
      (resultantPolynomialRoots (R := R)) (Fintype.card ι * Fintype.card κ) := by
  rw [← mul_one (Fintype.card ι * Fintype.card κ)]
  apply IsWeightedHomogeneous.bind₁ isWeightedHomogeneous_coeffDegree_resultantPolynomialCoeff
  · rintro (i | i)
      <;> simp only [Sum.elim_inl, Sum.elim_inr]
      <;> refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [MvPolynomial.C_1] using isWeightedHomogeneous_C _ (1 : R)
    · simpa using (isWeightedHomogeneous_coeffOfRoots (R := R) i).rename (f := Sum.inl) (w₂ := fun
      _ => 1) (fun _ => rfl)
    · simpa [MvPolynomial.C_1] using isWeightedHomogeneous_C _ (1 : R)
    · simpa using (isWeightedHomogeneous_coeffOfRoots (R := R) i).rename (f := Sum.inr) (w₂ := fun
      _ => 1) (fun _ => rfl)

/-- The coefficient of `Π i, Π j, (X i - X j)` that corresponds to taking everything on the left. -/
lemma coeff_inl_prod_X_inl_sub_X_inr :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ => Fintype.card κ) 0))
      (∏ i : ι, ∏ j : κ, (MvPolynomial.X (R := R) (Sum.inl i) - MvPolynomial.X (Sum.inr j))) =
        1 := by
  classical
  simp only [sub_eq_add_neg, Finset.prod_add, Finset.powerset_univ, Finset.prod_const,
    Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib, MvPolynomial.coeff_sum]
  -- We only need to look at those terms where we get `X (Sum.inl _)`.
  rw [Fintype.sum_eq_single (fun _ => Finset.univ)]
  -- And that term is exactly the product of the `X`es we want the coefficients of.
  · convert MvPolynomial.coeff_monomial
      (Finsupp.equivFunOnFinite.symm (Sum.elim (α := ι) (β := κ) (fun _ => Fintype.card κ) 0))
      (Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ => Fintype.card κ) 0))
      (1 : R)
    · simp [MvPolynomial.monic_monomial_eq]
    · rw [if_pos rfl]
  · intro x hx
    rw [MvPolynomial.coeff_mul, Finset.sum_eq_zero]
    · simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b h
      by_cases hb0 : b = 0
      · convert zero_mul _
        convert MvPolynomial.coeff_monomial a (Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (x
          i).card) 0)) (1 : R)
        · simp [MvPolynomial.monic_monomial_eq]
        · rw [if_neg]
          rintro rfl
          apply hx
          ext i : 1
          exact Finset.eq_univ_of_card _ (by simpa [hb0] using DFunLike.congr_fun h (Sum.inl i))
      · rw [DFunLike.ext_iff, not_forall] at hb0
        simp only [Finsupp.coe_zero, Pi.zero_apply, Sum.exists] at hb0
        obtain (⟨i, hi⟩ | ⟨j, hj⟩) := hb0
        swap
        · have := DFunLike.congr_fun h (Sum.inr j)
          simp [hj] at this
        convert mul_zero _
        simp only [← neg_one_mul (MvPolynomial.X (R := R) _), Finset.prod_mul_distrib,
          Finset.prod_const, Finset.prod_pow_eq_pow_sum, ← _root_.map_one MvPolynomial.C, ← map_neg,
          ← map_pow, ← map_prod, MvPolynomial.coeff_C_mul, neg_one_pow_mul_eq_zero_iff]
        rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun j => i ∉
          x j))]
        · simp only [Finset.prod_const]
          convert MvPolynomial.coeff_monomial b (Finsupp.equivFunOnFinite.symm (Sum.elim 0 (fun i =>
            (Finset.filter (fun j ↦ i ∉ x j) Finset.univ).card))) (1 : R)
          · simp [MvPolynomial.monic_monomial_eq]
          · rw [if_neg]
            rintro rfl
            simp at hi
        · simp

lemma prod_sylvesterMatrixVec_finAddFlip (f : Fin (n + 1) → R) (g : Fin (m + 1) → R) :
    ∏ x : Fin (m + n), sylvesterMatrixVec f g (Fin.cast (add_comm _ _) (finAddFlip x)) x =
    f (Fin.last _) ^ m * g 0 ^ n := by
  rw [Fin.prod_univ_add, Fintype.prod_congr, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.prod_congr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro i
    simp [finAddFlip, sylvesterMatrixVec, finSumFinEquiv, sylvesterVec_def]
  · intro i
    simp [finAddFlip, sylvesterMatrixVec, finSumFinEquiv, sylvesterVec_def, add_comm]
    rfl

/-- The coefficient of the roiResultant corresponding to `a₀ ^ n * bₙ ^ m`. -/
lemma MvPolynomial.coeff_zero_lead_resultantPolynomialCoeff :
    MvPolynomial.coeff (Finsupp.single (Sum.inl 0) n + Finsupp.single (Sum.inr (Fin.last _)) m)
      (resultantPolynomialCoeff (m := m) (n := n) (R := R)) = (-1) ^ (m * n) := by
  rw [resultantPolynomialCoeff, ← aeval_eq_bind₁, aeval_det, det_apply, MvPolynomial.coeff_sum]
  simp only [Units.smul_def, zsmul_eq_mul, intCast_eq_C, of_apply, coeff_C_mul]
  rw [Fintype.sum_eq_single ((finCongr (add_comm m n)).trans finAddFlip).symm]
  · simp only [Equiv.Perm.sign_symm, sign_finAddFlip, mul_comm, Equiv.symm_trans_apply,
      finCongr_symm, finAddFlip_symm, finCongr_apply]
    rw [prod_sylvesterMatrixVec_finAddFlip,
        coeff_X_pow_mul, coeff_X_pow, if_pos rfl, mul_one]
    rw [intUnitsNegOnePow_cast (R := R)]
  · intro σ hσ
    obtain ⟨i, hi⟩ := not_forall.mp (mt DFunLike.ext_iff.mpr hσ)
    cases i using Fin.addCases
    case left i =>
      simp only [Equiv.symm_trans_apply, finCongr_symm, finAddFlip_symm, finAddFlip_apply_castAdd,
        finCongr_apply, Fin.cast_natAdd] at hi
      by_cases h : ↑(σ (Fin.castAdd n i)) ≤ n + ↑i
      · by_cases h' : (i : ℕ) ≤ ↑(σ (Fin.castAdd n i))
        · rw [coeff_eq_zero_of_X_dvd (Sum.inr ⟨↑(σ (Fin.castAdd n i)) - ↑i,
            Nat.lt_succ_iff.mpr (tsub_le_iff_right.mpr h)⟩), mul_zero]
          · refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (Fin.castAdd n i)))
            simp [sylvesterMatrixVec, sylvesterVec_def, h, h']
          · simp only [Finsupp.coe_add, Pi.add_apply, ne_eq, not_false_eq_true,
              Finsupp.single_eq_of_ne, Finsupp.single_apply, Sum.inr.injEq, Fin.ext_iff,
              Fin.val_last, zero_add, ite_eq_right_iff, reduceCtorEq]
            obtain (hlt | heq) := h.lt_or_eq
            · intro hn
              have := (Nat.sub_lt_right_of_lt_add h' hlt).ne'
              contradiction
            · have : σ (Fin.castAdd n i) = i.addNat n := by
                ext
                simpa [h, add_comm]
              contradiction
        · rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.castAdd n i)), coeff_zero, mul_zero]
          simp [sylvesterMatrixVec, sylvesterVec_def, h']
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.castAdd n i)), coeff_zero, mul_zero]
        · simp [sylvesterMatrixVec, sylvesterVec_def, h]
    case right i =>
      simp only [Equiv.symm_trans_apply, finCongr_symm, finAddFlip_symm, finAddFlip_apply_natAdd,
        finCongr_apply,
        Fin.cast_castAdd, Fin.ext_iff, Fin.val_castLE] at hi
      by_cases h : ↑(σ (Fin.natAdd m i)) ≤ m + ↑i
      · by_cases h' : (i : ℕ) ≤ ↑(σ (Fin.natAdd m i))
        · rw [coeff_eq_zero_of_X_dvd (Sum.inl ⟨↑(σ (Fin.natAdd m i)) - ↑i,
            Nat.lt_succ_iff.mpr (tsub_le_iff_right.mpr h)⟩), mul_zero]
          · refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (Fin.natAdd m i)))
            simp [sylvesterMatrixVec, sylvesterVec_def, h, h']
          · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Sum.inl.injEq,
              Fin.ext_iff, Fin.val_zero, add_zero,
              ite_eq_right_iff, if_false, reduceCtorEq]
            rw [eq_comm, tsub_eq_zero_iff_le]
            intro h''
            exact (hi (le_antisymm h'' h')).elim
        · rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd m i)), coeff_zero, mul_zero]
          simp [sylvesterMatrixVec, sylvesterVec_def, h']
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd m i)), coeff_zero, mul_zero]
        · simp [sylvesterMatrixVec, sylvesterVec_def, h]

@[simp] lemma MvPolynomial.coeffOfRoots_zero [NeZero (Fintype.card ι)] :
    coeffOfRoots (ι := ι) (R := R) 0 = monomial (Finsupp.equivFunOnFinite.symm 1) ((-1) ^
      Fintype.card ι) := by
  rw [coeffOfRoots, esymm_eq_sum_monomial, Fin.val_zero, Nat.sub_zero, ← Finset.card_univ,
      Finset.powersetCard_self (Finset.univ), Finset.sum_singleton, ← _root_.map_one C, ← map_neg,
      ← map_pow, C_mul_monomial, mul_one, monomial_eq_monomial_iff]
  refine Or.inl ⟨?_, rfl⟩
  ext i
  simp [Finsupp.finsetSum_apply]

lemma MvPolynomial.coeff_inl_resultantPolynomialRoots [Nonempty ι] [Nonempty κ] [Infinite R]
    [IsDomain R] :
    MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm (Sum.elim (α := ι) (β := κ) (fun _ ↦ Fintype.card κ) 0))
        (resultantPolynomialRoots (R := R)) =
      1 := by
  have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  classical
  rw [resultantPolynomialRoots, ← aeval_eq_bind₁, aeval_def, eval₂_eq, coeff_sum]
  simp only [algebraMap_eq, coeff_C_mul]
  rw [Finset.sum_eq_single (Finsupp.single (Sum.inl 0) _ + Finsupp.single (Sum.inr (Fin.last _)) _)]
  · have hdisj : Disjoint (fun₀ | Sum.inl (0 : Fin (Fintype.card ι + 1)) => Fintype.card κ).support
                  (fun₀ | Sum.inr (Fin.last (Fintype.card κ)) => Fintype.card ι).support := by
      simp [Finsupp.support_single]
    rw [coeff_zero_lead_resultantPolynomialCoeff, Finsupp.support_add_eq hdisj,
        Finset.prod_union hdisj, Finsupp.support_single _ Fintype.card_ne_zero,
        Finsupp.support_single _ Fintype.card_ne_zero]
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.prod_singleton, Sum.elim_inl,
      Fin.snoc_apply_zero,
      coeffOfRoots_zero, rename_monomial, Finsupp.single_eq_same, ne_eq,
      not_false_eq_true, Finsupp.single_eq_of_ne, add_zero, monomial_pow, Sum.elim_inr,
        Fin.snoc_last, zero_add, one_pow,
      mul_one, coeff_monomial, mul_ite, mul_zero, reduceCtorEq]
    rw [if_pos, ← pow_mul, ← mul_pow, neg_mul_neg, one_mul, one_pow]
    · ext (i | j)
      · simp [Finsupp.mapDomain_apply Sum.inl_injective]
      · simp [Finsupp.mapDomain_notin_range]
  · intro b hb b_ne
    refine mul_eq_zero.mpr (Or.inr ?_)
    have : ∀ i ∈ b.support, Sum.elim (Fin.snoc (fun i ↦ (rename Sum.inl) (coeffOfRoots i)) 1)
              (Fin.snoc (fun i ↦ (rename Sum.inr) (coeffOfRoots i)) 1) i ∣
            (∏ i ∈ b.support,
              Sum.elim (Fin.snoc (fun i ↦ (rename Sum.inl) (coeffOfRoots i)) 1)
                  (Fin.snoc (fun i ↦ (rename Sum.inr) (coeffOfRoots (R := R) i)) 1) i ^
                b i) := fun i hbi =>
        (dvd_pow dvd_rfl (Finsupp.mem_support_iff.mp hbi)).trans (Finset.dvd_prod_of_mem _ hbi)
    -- The inequality `b_ne` can be in the `inl` part or the `inr` part.
    -- We first show that the `inr` part has to be the same.
    -- For the non-leading coefficients we get a root of `g` in every term...
    by_cases h₁ : ∃ i, b (Sum.inr (Fin.castSucc i)) ≠ 0
    · obtain ⟨i, hbi⟩ := h₁
      rw [coeff_eq_zero_of_dvd_of_support (this _ (Finsupp.mem_support_iff.mpr hbi))]
      intro m hm
      rw [Sum.elim_inr, Fin.snoc_castSucc, notMem_support_iff, coeffOfRoots, _root_.map_mul,
        ← C.map_one, ← C.map_neg (1 : R), ← C_pow, rename_C, coeff_C_mul]
      simp only [esymm_eq_sum_monomial, map_sum, coeff_sum, mul_eq_zero, pow_eq_zero_iff',
        neg_eq_zero, one_ne_zero, ne_eq, false_and, false_or]
      rw [Finset.sum_eq_zero]
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, rename_monomial,
        Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, coeff_monomial, DFunLike.ext_iff,
        Finsupp.finsetSum_apply, Sum.forall,         ite_eq_right_iff, one_ne_zero, imp_false,
          not_and, not_forall]
      intro s hs _
      obtain ⟨x, hxs⟩ : Finset.Nonempty s := Finset.card_ne_zero.mp (hs ▸ Nat.sub_ne_zero_of_lt i.2)
      use x
      simp only [Finsupp.le_def, Finsupp.coe_equivFunOnFinite_symm, Sum.forall,
        Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, nonpos_iff_eq_zero] at hm
      simp only [hm.2, Finset.sum_eq_zero_iff, not_forall]
      use x, hxs
      simp
    -- So we can simplify away the `inr` bit of the product over `b`.
    simp only [ne_eq, not_exists, Decidable.not_not] at h₁
    rw [Finset.prod_subset (Finset.subset_univ _), Fintype.prod_sum_type,
        Fintype.prod_eq_single (Fin.last (Fintype.card κ)), Sum.elim_inr, Fin.snoc_last,
        one_pow, mul_one]
    swap
    · intro x hx
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hx
      simp [h₁]
    swap
    · simp only [Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, Decidable.not_not, true_implies]
      intro i hi
      simp [hi]
    -- And by homogeneity, we can't only change the leading coefficient.
    by_cases h₂ : b (Sum.inr (Fin.last _)) = Fintype.card ι
    swap
    · have := isWeightedHomogeneous_resultantPolynomialCoeff_right (mem_support_iff.mp hb)
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_subset (Finset.subset_univ _)] at this
      · simp only [smul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, mul_zero, Finset.sum_const_zero,
          Sum.elim_inr, mul_one, Fin.sum_univ_castSucc, h₁, zero_add] at this
        contradiction
      · simp
    -- So we must have a difference in the coefficients of `f`.
    obtain ⟨i, hib⟩ : ∃ i, b (Sum.inl i) ≠ (fun₀ | 0 => Fintype.card κ) i := by
      contrapose! b_ne
      ext i
      obtain (i | i) := i
      · simp [b_ne, Finsupp.single_apply_left (Sum.inl_injective)]
      · cases i using Fin.lastCases
        case _ =>
          simpa using h₂
        case _ i =>
          simpa using h₁ i
    simp only [Sum.elim_inl]
    -- But again by homogeneity we can compute the number of times a term occurs in the product.
    have : ∑ i, b (Sum.inl i) = Fintype.card κ := by
      have := isWeightedHomogeneous_resultantPolynomialCoeff_left (mem_support_iff.mp hb)
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_subset (Finset.subset_univ _)] at this
      · simpa only [smul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, mul_zero,
          Finset.sum_const_zero, Sum.elim_inr, mul_one, add_zero] using this
      · simp
    -- And it turns out the upper bound is only achieved when `b = Finsupp.single 0 (Fintype.card
    -- κ)`.
    apply coeff_eq_zero_of_totalDegree_lt
    rw [Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
    · refine (totalDegree_finsetProd _ _).trans_lt ?_
      refine (Finset.sum_le_sum (fun _ _ => totalDegree_pow _ _)).trans_lt ?_
      rw [Fin.sum_univ_castSucc]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Sum.elim_inl, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, Sum.elim_inr, Pi.zero_apply, mul_zero, add_zero,
        Fin.snoc_castSucc, Fin.snoc_last, totalDegree_one]
      refine (Finset.sum_le_sum
        (fun _ _ => mul_le_mul_right (totalDegree_rename_le _ _) _)).trans_lt ?_
      refine (Finset.sum_le_sum (fun _ _ => mul_le_mul_right (isHomogeneous_coeffOfRoots
        _).totalDegree_le _)).trans_lt ?_
      rw [mul_comm]
      -- Because either we have some weight in the leading coefficient.
      by_cases h₃ : b (Sum.inl (Fin.last _)) ≠ 0
      · simp only [← this, Fin.sum_univ_castSucc, add_mul, Finset.sum_mul]
        exact lt_add_of_le_of_pos
          (Finset.sum_le_sum (fun _ _ => mul_le_mul_right (Nat.sub_le _ _) _))
          (mul_pos (Nat.pos_of_ne_zero h₃) (NeZero.pos _))
      simp only [ne_eq, Decidable.not_not] at h₃
      -- Or we have some weight away from the constant coefficient.
      apply Fin.sum_mul_sub_lt_of_apply_zero_lt
      · simpa [h₃, Fin.sum_univ_castSucc] using this
      · cases i using Fin.lastCases
        case _ =>
          rw [Finsupp.single_eq_of_ne] at hib
          · contradiction
          · simp [Fin.ext_iff]
        case _ i =>
          exact lt_of_sum_eq_of_ne (b := b ∘ Sum.inl) (Finset.mem_univ _) (Finset.mem_univ _) this
            hib (fun _ _ => Nat.zero_le _)
    · simp
  · simp only [mem_support_iff, ne_eq, Decidable.not_not, Finsupp.coe_add, Pi.add_apply,
      mul_eq_zero]
    intro h
    simp [h]

open MvPolynomial in
/-- If P = ∏ (X - t i) and Q = ∏ (X - u i), then
  Res_(n, m) (P, Q) = ∏ (-1)^(n*m) * (t i - u j) -/
lemma resultant_eq_prod_roots_aux [IsDomain R]
    [UniqueFactorizationMonoid R]
    [Infinite R] : -- TODO: we don't need this hypothesis if we work over `ℤ`
    ∀ (t : ι → R) (u : κ → R),
        Polynomial.roiResultant (∏ i,
          (Polynomial.X - Polynomial.C (t i))) (∏ i, (Polynomial.X - Polynomial.C (u i))) =
      ∏ i, ∏ j, (t i - u j) := by
  classical
  intro t u
  suffices MvPolynomial.eval (Sum.elim t u) resultantPolynomialRoots =
      MvPolynomial.eval (Sum.elim t u) (∏ i : ι, ∏ j : κ, (X (Sum.inl i) - X (Sum.inr j))) by
    simpa [eval_resultantPolynomialRoots] using this
  obtain ⟨c, hc⟩ := MvPolynomial.IsWeightedHomogeneous.exists_C_mul_eq_of_dvd
    (R := R) (nonTorsionWeight_of (fun _ => one_ne_zero))
      isWeightedHomogeneous_prod_root_differences
      isWeightedHomogeneous_resultantPolynomialRoots
    (prod_root_differences_dvd_resultantPolynomialRoots (ι := ι) (κ := κ))
  suffices c = 1 by
    rw [← hc, this, _root_.map_one, one_mul]
  -- We show the constant is as desired by inspecting the coefficients.
  cases isEmpty_or_nonempty ι
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      resultantPolynomialRoots_of_isEmpty_left, _root_.map_one] at hc
    simpa using MvPolynomial.C_injective _ _ hc
  cases isEmpty_or_nonempty κ
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_const_one, mul_one,
      resultantPolynomialRoots_of_isEmpty_right, _root_.map_one] at hc
    simpa using MvPolynomial.C_injective _ _ hc
  · -- Consider the term that consists of the product of the roots, i.e. the constant coefficient.
    have := congr_arg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ =>
      Fintype.card κ) 0))) hc
    rw [MvPolynomial.coeff_C_mul, coeff_inl_prod_X_inl_sub_X_inr, mul_one] at this
    rw [this, MvPolynomial.coeff_inl_resultantPolynomialRoots]

/-- If P = a_n ∏ (X - t i) and Q = b_n ∏ (X - u i, then
  Res_(n, m) (P, Q) = ∏ (-1)^(n*m) * (a_n)^m * (b_m)^n (t i - u j) -/
lemma resultant_eq_prod_roots [Infinite K] -- TODO: should work over `ℤ`
    (t : Fin m → K) (u : Fin n → K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Polynomial.roiResultant (C x * ∏ i, (X - C (t i))) (C y * ∏ i, (X - C (u i))) =
      x ^ n * y ^ m * ∏ i, ∏ j, (t i - u j) := by
  by_cases hm : m = 0
  · subst hm
    simp [natDegree_C_mul hy]
  by_cases hn : n = 0
  · subst hn
    simp [natDegree_C_mul hx]
  rw [C_mul_resultant, resultant_C_mul,
      resultant_eq_prod_roots_aux,
      natDegree_C_mul, natDegree_prod_X_sub_C, Finset.card_univ, Fintype.card_fin,
      natDegree_prod_X_sub_C, Finset.card_univ, Fintype.card_fin]
  · ring
  · assumption
  · simpa
  · simpa [natDegree_C_mul hy]

omit [Fintype ι] [Fintype κ]
lemma Multiset.toList_cons (a : ι) (s : Multiset ι) :
    (a ::ₘ s).toList.Perm (a :: s.toList) := by
  rw [← coe_eq_coe, coe_toList, ← cons_coe, coe_toList]

lemma Multiset.toList_map (f : ι → κ) (s : Multiset ι) :
    (s.map f).toList.Perm (s.toList.map f) := by
  rw [← coe_eq_coe, coe_toList, ← map_coe, coe_toList]

lemma Finset.toList_map (f : ι ↪ κ) (s : Finset ι) :
    (s.map f).toList.Perm (s.toList.map f) :=
  Multiset.toList_map _ _

lemma List.get_univ_toList_perm_self (a : List ι) :
    (Finset.univ.toList.map a.get).Perm a := by
  induction a
  case nil =>
    simp
  case cons a as ih =>
    simp only [length_cons, Fin.univ_succ]
    refine ((Finset.toList_cons _).map _).trans ?_
    rw [map_cons, get_cons_zero, perm_cons]
    refine ((Finset.toList_map _ _).map _).trans ?_
    rw [← List.comp_map]
    exact ih

lemma List.finset_prod_get (a : List ι) (f : ι → R) :
    ∏ i : Fin a.length, f (a.get i) = (a.map f).prod := by
  refine (Finset.prod_map_toList Finset.univ (f ∘ a.get)).symm.trans (List.Perm.prod_eq ?_)
  rw [List.comp_map]
  exact (List.get_univ_toList_perm_self _).map _

lemma resultant_list_eq_prod_roots {ι κ : Type*} (a : List ι) (b : List κ) [Infinite K]
    (t : ι → K) (u : κ → K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Polynomial.roiResultant
        (C x * (a.map (fun i => X - C (t i))).prod)
        (C y * (b.map (fun i => (X - C (u i)))).prod) =
      x ^ b.length * y ^ a.length *
        (a.map (fun i => (b.map (fun j => t i - u j)).prod)).prod := by
  convert resultant_eq_prod_roots (t ∘ a.get) (u ∘ b.get) x y hx hy
  · exact (List.finset_prod_get a _).symm
  · exact (List.finset_prod_get b _).symm
  · rw [← List.finset_prod_get a]
    refine Fintype.prod_congr _ _ (fun i => ?_)
    exact (List.finset_prod_get b _).symm

lemma resultant_multiset_eq_prod_roots {ι κ : Type*} (a : Multiset ι) (b : Multiset κ) [Infinite K]
    (t : ι → K) (u : κ → K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Polynomial.roiResultant
        (C x * (a.map (fun i => X - C (t i))).prod)
        (C y * (b.map (fun i => (X - C (u i)))).prod) =
      x ^ Multiset.card b * y ^ Multiset.card a *
        (a.map (fun i => (b.map (fun j => t i - u j)).prod)).prod := by
  convert resultant_list_eq_prod_roots a.toList b.toList t u x y hx hy
  · exact (Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))
  · exact (Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))
  · simp
  · simp
  · rw [(Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))]
    congr
    ext i
    exact (Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))

end AsPolynomial

end general
