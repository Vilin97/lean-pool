/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import LeanPool.RingOfIntegersProject.PolynomialAsVec
import LeanPool.RingOfIntegersProject.Resultant

variable {R : Type*} [CommRing R]

/-- A polynomial function in `ι` arguments is one that can be given as evaluating a MvPolynomial. -/
def IsPolynomial {ι R : Type*} [CommSemiring R] (f : (ι → R) → R) : Prop :=
  ∃ p : MvPolynomial ι R, ∀ x, f x = MvPolynomial.eval x p

lemma IsPolynomial.const {ι : Type*} (x : R) :
    IsPolynomial (fun (_ : ι → R) => x) :=
  ⟨MvPolynomial.C x, fun _ => (MvPolynomial.eval_C _).symm⟩

lemma IsPolynomial.apply_const {ι : Type*} (i : ι) :
    IsPolynomial (fun (x : ι → R) => x i) :=
  ⟨MvPolynomial.X i, fun _ => (MvPolynomial.eval_X _).symm⟩

lemma IsPolynomial.comp {ι κ : Type*} {f : (ι → R) → R} (s : ι → κ):
    IsPolynomial f → IsPolynomial (fun x => f (x ∘ s)) := by
  rintro ⟨f, f_eq⟩
  exact ⟨MvPolynomial.rename s f, by simp [f_eq, MvPolynomial.eval_rename]⟩

lemma IsPolynomial.add {ι : Type*} {f g : (ι → R) → R} :
    IsPolynomial f → IsPolynomial g → IsPolynomial (fun (x : ι → R) => f x + g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f + g, by simp [f_eq, g_eq]⟩

@[to_additive existing]
lemma IsPolynomial.mul {ι : Type*} {f g : (ι → R) → R} :
    IsPolynomial f → IsPolynomial g → IsPolynomial (fun (x : ι → R) => f x * g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f * g, by simp [f_eq, g_eq]⟩

lemma IsPolynomial.sum {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsPolynomial (f i)) (s : Finset m) :
    IsPolynomial (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.sum_empty]
    apply IsPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

@[to_additive existing]
lemma IsPolynomial.prod {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsPolynomial (f i)) (s : Finset m) :
    IsPolynomial (fun x => ∏ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    apply IsPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

lemma isPolynomial_ofVec (i : ℕ) :
    IsPolynomial (fun (v : Fin m → R) => (Polynomial.ofVec v).coeff i) := by
  simp only [Polynomial.coeff_ofVec]
  split_ifs with hi
  · simpa using IsPolynomial.apply_const (R := R) (⟨i, hi⟩ : Fin m)
  · exact IsPolynomial.const 0

lemma isPolynomial_ofVec_snoc {x : R} (i : ℕ) :
    IsPolynomial (fun (v : Fin m → R) => (Polynomial.ofVec (Fin.snoc v x)).coeff i) := by
  simp only [Polynomial.coeff_ofVec, Fin.snoc]
  split_ifs with hi_succ hi
  · simpa using IsPolynomial.apply_const (R := R) (⟨i, hi⟩ : Fin m)
  · have hi_eq : i = m := le_antisymm (Nat.lt_succ_iff.mp hi_succ) (le_of_not_gt hi)
    subst hi_eq
    exact IsPolynomial.const x
  · exact IsPolynomial.const 0

lemma IsPolynomial.det {m ι : Type*} [DecidableEq m] [Fintype m]
    (f : m → m → (ι → R) → R) (h : ∀ i j, IsPolynomial (f i j)) :
    IsPolynomial (fun x => Matrix.det (Matrix.of (fun i j => f i j x))) := by
  simp only [det_apply, of_apply, Units.smul_def, zsmul_eq_mul]
  apply IsPolynomial.sum
  intro σ
  exact (IsPolynomial.const (Equiv.Perm.sign σ : R)).mul (.prod _ (fun _ => h _ _) _)

/-- A symmetric polynomial function in `ι` arguments is one that can be given as evaluating a
symmetric MvPolynomial. -/
def IsSymmPolynomial {ι R : Type*} [CommSemiring R] (f : (ι → R) → R) : Prop :=
  ∃ p : MvPolynomial ι R, ∀ x, f x = MvPolynomial.eval x p ∧ p.IsSymmetric

lemma IsSymmPolynomial.toIsPolynomial {ι R : Type*} [CommSemiring R] {f : (ι → R) → R} :
    IsSymmPolynomial f → IsPolynomial f := by
  rintro ⟨P, hP⟩
  exact ⟨P, fun x => (hP x).1⟩

lemma IsSymmPolynomial.const {ι : Type*} (x : R) :
    IsSymmPolynomial (fun (_ : ι → R) => x) :=
  ⟨MvPolynomial.C x, fun _ => ⟨(MvPolynomial.eval_C _).symm, MvPolynomial.IsSymmetric.C _⟩⟩

lemma IsSymmPolynomial.eval_esymm {ι : Type*} [Fintype ι] :
    IsSymmPolynomial (fun (x : ι → R) => MvPolynomial.eval x (MvPolynomial.esymm _ _ n)) :=
  ⟨MvPolynomial.esymm _ _ n, fun _ => ⟨rfl, MvPolynomial.esymm_isSymmetric _ _ _⟩⟩

lemma IsSymmPolynomial.esymm {ι : Type*} [Fintype ι] :
    ∀ i, IsSymmPolynomial (fun (x : ι → R) => (Multiset.map x Finset.univ.val).esymm i) := by
  intro i
  refine ⟨MvPolynomial.esymm _ _ i, fun _ => ⟨?_, MvPolynomial.esymm_isSymmetric _ _ _⟩⟩
  rw [← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe,
      MvPolynomial.aeval_esymm_eq_multiset_esymm]

lemma IsSymmPolynomial.add {ι : Type*} {f g : (ι → R) → R} :
    IsSymmPolynomial f → IsSymmPolynomial g → IsSymmPolynomial (fun (x : ι → R) => f x + g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f + g, fun i => ⟨by simp [f_eq, g_eq], MvPolynomial.IsSymmetric.add (f_eq i).2 (g_eq i).2⟩⟩

@[to_additive existing]
lemma IsSymmPolynomial.mul {ι : Type*} {f g : (ι → R) → R} :
    IsSymmPolynomial f → IsSymmPolynomial g → IsSymmPolynomial (fun (x : ι → R) => f x * g x) := by
  rintro ⟨f, f_eq⟩ ⟨g, g_eq⟩
  exact ⟨f * g, fun i => ⟨by simp [f_eq, g_eq], MvPolynomial.IsSymmetric.mul (f_eq i).2 (g_eq i).2⟩⟩

lemma IsSymmPolynomial.sum {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsSymmPolynomial (f i)) (s : Finset m) :
    IsSymmPolynomial (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.sum_empty]
    apply IsSymmPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

@[to_additive existing]
lemma IsSymmPolynomial.prod {m ι : Type*}
    (f : m → (ι → R) → R) (h : ∀ i, IsSymmPolynomial (f i)) (s : Finset m) :
    IsSymmPolynomial (fun x => ∏ i in s, f i x) := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    apply IsSymmPolynomial.const
  case insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

lemma IsSymmPolynomial.det {m ι : Type*} [DecidableEq m] [Fintype m]
    (f : m → m → (ι → R) → R) (h : ∀ i j, IsSymmPolynomial (f i j)) :
    IsSymmPolynomial (fun x => Matrix.det (Matrix.of (fun i j => f i j x))) := by
  simp only [det_apply, of_apply, Units.smul_def, zsmul_eq_mul]
  apply IsSymmPolynomial.sum
  intro σ
  exact (IsSymmPolynomial.const (Equiv.Perm.sign σ : R)).mul (.prod _ (fun _ => h _ _) _)

/-- If the coefficients of `f` is given by polynomial functions, so is its Sylvester matrix. -/
theorem IsPolynomial.sylvesterVec {ι : Type*} {m n : ℕ} {f : (ι → R) → (Fin (m + 1) → R)}
    (hf : ∀ i, IsPolynomial (fun x => (f x) i)) :
    ∀ i (j : Fin (m + n)), IsPolynomial (fun x => sylvesterVec (f x) i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp only [sylvesterVec_of_lt _ _ _ h]
    apply IsPolynomial.const
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) m
    case inl h₂ =>
      simp only [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      simp only [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]
      apply IsPolynomial.const

/-- If the coefficients of `f` is given by polynomial functions, so is its Sylvester matrix. -/
theorem IsSymmPolynomial.sylvesterVec {ι : Type*} {m n : ℕ} {f : (ι → R) → (Fin (m + 1) → R)}
    (hf : ∀ i, IsSymmPolynomial (fun x => (f x) i)) :
    ∀ i (j : Fin (m + n)), IsSymmPolynomial (fun x => sylvesterVec (f x) i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    simp only [sylvesterVec_of_lt _ _ _ h]
    apply IsSymmPolynomial.const
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) m
    case inl h₂ =>
      simp only [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      simp only [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]
      apply IsSymmPolynomial.const

/-- If the coefficients of `f` and `g` are given by polynomial functions, so is their resultant.

Note that we have to be a bit tricky here: a priori the degree of `f x` and `g x` can change
as a function of `x`, so suddenly we could get a completely different Sylvester matrix.
Thus we need to assume the degree remains constant in terms of `x`.
-/
theorem IsSymmPolynomial.resultant {ι : Type*} {m n : ℕ} {f g : (ι → R) → R[X]}
    (hdegf : ∀ x, (f x).natDegree = m) (hdegg : ∀ x, (g x).natDegree = n)
    (hf : ∀ i, IsSymmPolynomial (fun x => coeff (f x) i)) (hg : ∀ i, IsSymmPolynomial (fun x => coeff (g x) i)) :
    IsSymmPolynomial (fun x => (f x).resultant (g x)) := by
  conv =>
    congr
    · ext x
      rw [Polynomial.resultant_eq_det_sylvesterMatrix (hdegf x) (hdegg x),
          sylvesterMatrixAux, sylvesterMatrixVec]
      · skip
  simp only [det_transpose]
  refine IsSymmPolynomial.det _ (fun i j => Fin.addCases (fun i => ?_) (fun i => ?_) i)
  · simp only [Fin.addCases_left]
    apply IsSymmPolynomial.sylvesterVec
    intro i
    apply hg
  · simp only [Fin.addCases_right]
    apply IsSymmPolynomial.sylvesterVec
    intro i
    apply hf

/-- The coefficients of a polynomial are a symmetric polynomial function in its roots. -/
lemma Polynomial.coeff_isSymmPolynomial_roots {ι : Type*} [Fintype ι] (x : K) :
    ∀ i, IsSymmPolynomial (fun t => (C x * ∏ i : ι, (X - C (t i))).coeff i) := by
  intro i
  by_cases hx0 : x = 0
  · simpa [hx0] using IsSymmPolynomial.const 0

  cases le_or_gt i (Fintype.card ι)
  case neg.inr h =>
    conv =>
      congr
      ext t
      rw [coeff_eq_zero_of_natDegree_lt ((natDegree_C_mul_prod_X_sub_C _ _ hx0).trans_lt h)]
    apply IsSymmPolynomial.const
  case neg.inl h =>
    conv =>
      congr
      ext t
      rw [coeff_eq_esymm_roots_of_splits (splits_C_mul_prod_X_sub_C t _ x)
            (h.trans_eq (natDegree_C_mul_prod_X_sub_C t _ hx0).symm)]
    refine IsSymmPolynomial.mul (.mul ?_ ?_) ?_
    · simp only [leadingCoeff_C_mul_prod_X_sub_C]
      apply IsSymmPolynomial.const
    · simp only [natDegree_C_mul_prod_X_sub_C _ _ hx0]
      apply IsSymmPolynomial.const
    · simp_rw [roots_C_mul_prod_X_sub_C' _ _ hx0, natDegree_C_mul_prod_X_sub_C _ _ hx0]
      apply IsSymmPolynomial.esymm

/-- The resultant of a polynomial is a symmetric polynomial function in its roots. -/
lemma Polynomial.resultant_isSymmPolynomial_left {ι : Type*} [Fintype ι]
    (Q : K[X]) (x : K) :
    IsSymmPolynomial (fun t => (C x * ∏ i : ι, (X - C (t i))).resultant Q) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, zero_mul]
    by_cases hQ0 : Q.natDegree = 0
    · obtain ⟨y, rfl⟩ := natDegree_eq_zero.mp hQ0
      simp_rw [resultant_C, natDegree_zero, pow_zero]
      apply IsSymmPolynomial.const
    simp_rw [zero_resultant _ hQ0]
    apply IsSymmPolynomial.const
  refine IsSymmPolynomial.resultant (m := Fintype.card ι) ?_ (fun _ => rfl)
      (Polynomial.coeff_isSymmPolynomial_roots x)
      (fun i => IsSymmPolynomial.const _)
  · intro tu
    simp [hx0]

/-- The resultant of a polynomial is a symmetric polynomial function in its roots. -/
lemma Polynomial.resultant_isSymmPolynomial_right {ι : Type*} [Fintype ι]
    (P : K[X]) (x : K) :
    IsSymmPolynomial (fun t => P.resultant (C x * ∏ i : ι, (X - C (t i)))) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, zero_mul]
    by_cases hP0 : P.natDegree = 0
    · obtain ⟨y, rfl⟩ := natDegree_eq_zero.mp hP0
      simp_rw [C_resultant, natDegree_zero, pow_zero]
      apply IsSymmPolynomial.const
    simp_rw [resultant_zero _ hP0]
    apply IsSymmPolynomial.const
  simp_rw [resultant_swap P]
  refine .mul ?_ (Polynomial.resultant_isSymmPolynomial_left _ _)
  convert IsSymmPolynomial.const (ι := ι) ((-1) ^ (P.natDegree * Fintype.card ι) : K)
  · simp [hx0]

/-- If the coefficients of `P` and `Q` are given by polynomial functions, so is their resultant.

Note that we have to be a bit tricky here: a priori the degree of `P x` and `Q x` can change
as a function of `x`, so suddenly we could get a completely different Sylvester matrix.
Thus we need to assume the degree remains constant in terms of `x`.
-/
theorem IsPolynomial.resultant {ι κ : Type*} {m n : ℕ} {P : (ι → R) → R[X]} {Q : (κ → R) → R[X]}
    (hdegP : ∀ x, (P x).natDegree = m) (hdegQ : ∀ x, (Q x).natDegree = n)
    (hf : ∀ i, IsPolynomial (fun x => coeff (P x) i)) (hg : ∀ i, IsPolynomial (fun x => coeff (Q x) i)) :
    IsPolynomial (fun (xy : ι ⊕ κ → R) => (P (xy ∘ Sum.inl)).resultant (Q (xy ∘ Sum.inr))) := by
  conv =>
    congr
    · ext xy
      rw [resultant_eq_det_sylvesterMatrix (hdegP _) (hdegQ _),
          sylvesterMatrixAux, sylvesterMatrixVec]
      · skip
  simp only [det_transpose]
  refine IsPolynomial.det _ (fun i j => Fin.addCases (fun i => ?_) (fun i => ?_) i)
  · simp only [Fin.addCases_left]
    exact IsPolynomial.sylvesterVec (fun i => IsPolynomial.comp _ (hg _)) _ _
  · simp only [Fin.addCases_right]
    exact IsPolynomial.sylvesterVec (fun i => IsPolynomial.comp _ (hf _)) _ _

/-- The resultant of two polynomials is a polynomial function in their roots. -/
lemma Polynomial.resultant_isPolynomial_roots {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : K) :
    IsPolynomial (fun tu =>
      (C x * ∏ i : ι, (X - C (tu (Sum.inl i)))).resultant
      (C y * ∏ i : κ, (X - C (tu (Sum.inr i))))) := by
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · simpa [hx0, hy0] using IsPolynomial.const 1
    · obtain (hκ | hκ) := isEmpty_or_nonempty κ
      · simpa [hx0, hκ] using IsPolynomial.const 1
      convert IsPolynomial.const (0 : K)
      rw [hx0, map_zero, zero_mul, zero_resultant]
      · rw [natDegree_C_mul_prod_X_sub_C _ _ hy0]
        exact Fintype.card_pos.ne'
  by_cases hy0 : y = 0
  · obtain (hι | hι) := isEmpty_or_nonempty ι
    · simpa [hy0, hι] using IsPolynomial.const 1
    convert IsPolynomial.const (0 : K)
    rw [hy0, map_zero, zero_mul, resultant_zero]
    · rw [natDegree_C_mul_prod_X_sub_C _ _ hx0]
      exact Fintype.card_pos.ne'
  exact IsPolynomial.resultant
    (P := fun t => C x * ∏ i : ι, (X - C (t i)))
    (Q := fun u => C y * ∏ i : κ, (X - C (u i)))
    (fun _ => natDegree_C_mul_prod_X_sub_C _ _ hx0)
    (fun _ => natDegree_C_mul_prod_X_sub_C _ _ hy0)
    (fun i => (Polynomial.coeff_isSymmPolynomial_roots _ i).toIsPolynomial)
    (fun i => (Polynomial.coeff_isSymmPolynomial_roots _ i).toIsPolynomial)
