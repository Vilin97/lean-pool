/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Basic

variable {σ R : Type*} [CommRing R]

section Preliminaries

-- TODO: generalize!
@[simp] lemma Finset.sup_add_const {s : Finset σ} (hs : s.Nonempty) (f : σ → ℕ) (a : ℕ) :
    s.sup (fun i => f i + a) = s.sup f + a := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp at hs
  case insert x s hxs ih =>
    obtain (rfl | hs) := s.eq_empty_or_nonempty
    · simp
    rw [Finset.sup_insert, ih hs, max_add_add_right (f x) (s.sup f) a, Finset.sup_insert]

lemma Nat.sub_self_div_two (h : Even n) : n - n / 2 = n / 2 := by
  refine (Nat.div_eq_of_eq_mul_right two_pos ?_).symm
  rw [Nat.mul_sub, Nat.mul_div_cancel' h.two_dvd, two_mul, Nat.add_sub_cancel]

lemma Finset.disjoint_iff_not_mem_of_mem {α : Type*} {s t : Finset α} :
    Disjoint s t ↔ ∀ {x}, x ∈ s → ¬ x ∈ t :=
  ⟨fun h x hs ht => not_mem_empty _ (h (x := {x})
    (singleton_subset_iff.mpr hs)
    (singleton_subset_iff.mpr ht)
    (mem_singleton_self _)),
   fun h _ hs ht _ hx => (h (hs hx) (ht hx)).elim⟩

lemma Finset.disjoint_iff_not_mem_or_not_mem {α : Type*} {s t : Finset α} :
    Disjoint s t ↔ ∀ {x}, x ∉ s ∨ x ∉ t :=
  Finset.disjoint_iff_not_mem_of_mem.trans (forall_congr' (fun _ => imp_iff_or_not.trans or_comm))

/-- Taking a product over `s : Finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`. -/
@[to_additive "Taking a sum over `s : Finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`."]
theorem Finset.mul_prod_erase' {α β : Type*} [DecidableEq α] [CommMonoid β] (s : Finset α) (f : α → β)
    {a : α} (h : a ∉ s → f a = 1) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · exact Finset.mul_prod_erase _ _ ha
  · rw [h ha, one_mul, Finset.prod_erase _ (h ha)]

lemma Finsupp.add_single_injective {σ : Type*} {j : σ} {f : (σ →₀ ℕ) → ℕ}
    {a b : σ →₀ ℕ} (hf : (∀ i ≠ j, a i = b i) → ∃ (v : ℕ), b j * v + f a = a j * v + f b)
    (h : a + Finsupp.single j (f a) = b + Finsupp.single j (f b)) :
    a = b := by
  ext i
  have eq_of_ne : ∀ i ≠ j, a i = b i := by
    intro i hij
    simpa [hij.symm] using (DFunLike.congr_fun h i)
  by_cases hij : j = i
  swap
  · exact eq_of_ne _ (Ne.symm hij)
  subst hij
  obtain ⟨v, hv⟩ := hf eq_of_ne
  refine mul_left_cancel₀ v.succ_ne_zero ?_
  have := DFunLike.congr_fun h j
  simp only [smul_eq_mul, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Finsupp.sum] at this
  rw [Nat.succ_mul, Nat.succ_mul, ← add_left_cancel_iff (a := f a), ← add_assoc, ← add_assoc,
      add_comm (f a), add_comm (f a), mul_comm v, mul_comm v, hv, add_assoc, add_assoc,
      add_comm (f a), add_comm (f b), this]

section Weight

@[simp] lemma Finsupp.weight_const {σ : Type*} {w : ℕ} (x : σ →₀ ℕ) :
    Finsupp.weight (fun _ => w) x = Finsupp.degree x * w := by
  simp only [weight_apply, Finsupp.sum, smul_eq_mul, Finset.sum_const, degree,
    Finset.sum_mul]

@[simp] lemma Finsupp.weight_add {σ : Type*} {w : σ → ℕ} (d e : σ →₀ ℕ) :
    weight w (d + e) = weight w d + weight w e := by
  classical
  simp only [weight_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_add,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib, add_mul]
    rfl
  all_goals
  · intro i _ hi
    simp only [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma Finsupp.degree_add {σ : Type*} (d e : σ →₀ ℕ) :
    degree (d + e) = degree d + degree e := by
  classical
  unfold degree
  rw [Finset.sum_subset support_add,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [add_apply, Finset.sum_add_distrib]
    rfl
  all_goals
  · intro i _ hi
    exact not_mem_support_iff.mp hi

@[simp] lemma Finsupp.weight_sub {σ : Type*} {w : σ → ℕ} (d e : σ →₀ ℕ) (h : e ≤ d) :
    weight w (d - e) = weight w d - weight w e := by
  classical
  simp only [weight_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_tsub,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.tsub_apply, Nat.sub_mul]
    apply Nat.eq_sub_of_add_eq
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro x _
    rw [Nat.sub_add_cancel (Nat.mul_le_mul_right _ (h x))]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]
  · intro i _ hi
    rw [Finsupp.tsub_apply, Nat.sub_mul, Finsupp.not_mem_support_iff.mp hi, zero_mul, Nat.zero_sub]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma Finsupp.degree_sub {σ : Type*} (d e : σ →₀ ℕ) (h : e ≤ d) :
    degree (d - e) = degree d - degree e := by
  classical
  unfold degree
  rw [Finset.sum_subset Finsupp.support_tsub,
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_left (s₁ := d.support)),
      Finset.sum_subset (Finset.subset_union_right (s₂ := e.support))]
  · simp only [Finsupp.tsub_apply]
    apply Nat.eq_sub_of_add_eq
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro x _
    rw [Nat.sub_add_cancel (h x)]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi
  · intro i _ hi
    rw [Finsupp.tsub_apply, Finsupp.not_mem_support_iff.mp hi, Nat.zero_sub]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi

@[simp] lemma Finsupp.weight_single {σ : Type*} {w : σ → ℕ} (i : σ) (n : ℕ) :
    weight w (Finsupp.single i n) = n * w i := by
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_subset Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]
  · intro i _ hi
    rw [Finsupp.not_mem_support_iff.mp hi, zero_mul]

@[simp] lemma Finsupp.degree_single {σ : Type*} (i : σ) (n : ℕ) :
    degree (Finsupp.single i n) = n := by
  unfold degree
  rw [Finset.sum_subset Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]
  · intro i _ hi
    exact Finsupp.not_mem_support_iff.mp hi

@[simp] lemma Finsupp.weight_mapDomain {σ τ : Type*} {w : τ → ℕ} (f : σ → τ) (d : σ →₀ ℕ) :
    weight w (Finsupp.mapDomain f d) = weight (fun i => w (f i)) d := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Function.comp_apply]
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · simp [add_mul]

@[simp] lemma Finsupp.degree_mapDomain {σ τ : Type*} (f : σ → τ) (d : σ →₀ ℕ) :
    degree (Finsupp.mapDomain f d) = degree d :=
  Finsupp.sum_mapDomain_index (h := fun _ x => x) (fun _ => rfl) (fun _ _ _ => rfl)

end Weight

section MvPolynomial

open Polynomial

theorem Polynomial.zero_of_eval_zero' [IsDomain R] {σ : Type*} (f : σ → R)
    (hf : (Set.range f).Infinite)
    (p : R[X]) (h : ∀ x, p.eval (f x) = 0) : p = 0 := by
  classical
  by_contra hp
  have : Infinite (Set.range f) := hf.to_subtype
  refine @Fintype.false (Set.range f) _ ?_
  exact ⟨(p.roots.toFinset).subtype _, fun ⟨x, hx⟩ => by
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    exact Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _)))⟩

/-- If an `MvPolynomial` evaluates to zero everywhere on an infinite domain, it is zero. -/
lemma MvPolynomial.zero_of_eval_zero_aux [IsDomain R] [Infinite R]
    (p : MvPolynomial (Fin n) R) (h : ∀ x, MvPolynomial.eval x p = 0) : p = 0 := by
  induction n
  case zero =>
    rw [MvPolynomial.eq_C_of_isEmpty p] at h ⊢
    simp only [algHom_C, algebraMap_eq, eval_C, forall_const] at h
    simp [h]
  case succ n ih =>
    apply (MvPolynomial.finSuccEquiv R n).injective
    rw [map_zero]
    apply zero_of_eval_zero' MvPolynomial.C (Set.infinite_range_of_injective (C_injective _ _))
    refine fun x => ih _ (fun xs => ?_)
    rw [← h (Fin.cons x xs), MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map,
        ← Polynomial.eval₂_hom, MvPolynomial.eval_C]

/-- If an `MvPolynomial` is zero on all points of an infinite domain, they are equal. -/
lemma MvPolynomial.zero_of_eval_zero {σ : Type*} [IsDomain R] [Infinite R]
    (p : MvPolynomial σ R) (h : ∀ x, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨n, f, hf, q, rfl⟩ := MvPolynomial.exists_fin_rename p
  by_cases hn : n = 0
  · subst hn
    rw [MvPolynomial.eq_C_of_isEmpty q] at h ⊢
    simp only [algHom_C, algebraMap_eq, eval_C, forall_const] at h
    simp [h]
  have : NeZero n := ⟨hn⟩
  rw [MvPolynomial.zero_of_eval_zero_aux q (?_), map_zero]
  intro x
  specialize h (x ∘ f.invFun)
  simp [eval_rename] at h
  convert h
  ext
  rw [Function.comp_apply, Function.comp_apply, Function.leftInverse_invFun hf]

/-- If two `MvPolynomial`s evaluate the same all points of an infinite domain, they are equal. -/
lemma MvPolynomial.eq_of_eval_eq {σ : Type*} [IsDomain R] [Infinite R]
    (p q : MvPolynomial σ R) (h : ∀ x, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q :=
  sub_eq_zero.mp (zero_of_eval_zero _ (fun i => by rw [eval_sub, h, sub_eq_zero]))

lemma MvPolynomial.aeval_X_pow_mul_monomial {σ : Type*} {w : σ → ℕ} (i : σ) (x : σ →₀ ℕ) (a : R) :
    aeval (fun j => X i ^ w j * X j) (monomial x a) =
      monomial (x + .single i (Finsupp.weight w x)) a := by
  simp only [aeval_monomial, algebraMap_eq, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      prod_X_pow_eq_monomial, monomial_add_single, Finset.prod_pow_eq_pow_sum,
      ← pow_mul, fun i => mul_comm (w i) (x i)]
  rw [mul_left_comm, C_mul_monomial, mul_one, mul_comm]
  rfl

lemma MvPolynomial.aeval_X_mul_monomial {σ : Type*} (i : σ) (x : σ →₀ ℕ) (a : R) :
    aeval (fun j => X i * X j) (monomial x a) = monomial (x + .single i (Finsupp.degree x)) a := by
  simp only [aeval_monomial, algebraMap_eq, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      prod_X_pow_eq_monomial, monomial_add_single, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rw [mul_left_comm, C_mul_monomial, mul_one, mul_comm]

theorem MvPolynomial.coeff_aeval_X_pow_mul {σ : Type*} {w : σ → ℕ} {j : σ} (p : MvPolynomial σ R)
    (d : σ →₀ ℕ):
    coeff (d + Finsupp.single j (Finsupp.weight w d)) (MvPolynomial.aeval (fun i => X j ^ w i * X i) p) =
      coeff d p := by
  classical
  induction p using induction_on'''
  case h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d]
    split_ifs with hd
    · subst hd
      simp
    · rw [coeff_C, if_neg]
      contrapose! hd
      ext i
      symm
      simpa using (Nat.add_eq_zero.mp (DFunLike.congr_fun hd i).symm).1
  case h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, coeff_add, ih]
    congr 1
    rw [aeval_X_pow_mul_monomial, coeff_monomial d]
    split_ifs with hd
    · subst hd
      rw [coeff_monomial, if_pos rfl]
    · rw [coeff_monomial, if_neg]
      contrapose! hd
      apply Finsupp.add_single_injective _ hd
      intro eq_of_ne
      use w j
      simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
      rw [← Finset.add_sum_erase' (s := a.support) (a := j),
          ← Finset.add_sum_erase' (s := d.support) (a := j)]
      · rw [add_left_comm, add_left_cancel_iff, add_left_cancel_iff, Finset.sum_congr]
        · ext i
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, eq_of_ne _ hij]
        · intro i hi
          rw [eq_of_ne _ (Finset.mem_erase.mp hi).1]
      · intro h
        rw [Finsupp.not_mem_support_iff.mp h, zero_mul]
      · intro h
        rw [Finsupp.not_mem_support_iff.mp h, zero_mul]

theorem MvPolynomial.coeff_aeval_X_mul {σ : Type*} {j : σ} (p : MvPolynomial σ R) (d : σ →₀ ℕ):
    coeff (d + Finsupp.single j (Finsupp.degree d)) (MvPolynomial.aeval (fun i => X j * X i) p) =
      coeff d p := by
  classical
  induction p using induction_on'''
  case h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d]
    split_ifs with hd
    · subst hd
      simp
    · rw [coeff_C, if_neg]
      contrapose! hd
      ext i
      symm
      simpa using (Nat.add_eq_zero.mp (DFunLike.congr_fun hd i).symm).1
  case h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, coeff_add, ih]
    congr 1
    rw [aeval_X_mul_monomial, coeff_monomial d]
    split_ifs with hd
    · subst hd
      rw [coeff_monomial, if_pos rfl]
    · rw [coeff_monomial, if_neg]
      contrapose! hd
      ext i
      symm
      have eq_of_ne : ∀ i ≠ j, d i = a i := by
        intro i hij
        simpa [hij.symm] using (DFunLike.congr_fun hd i).symm
      by_cases hij : j = i
      swap
      · exact eq_of_ne _ (Ne.symm hij)
      subst hij
      by_cases hdeg : Finsupp.degree d = Finsupp.degree a
      · rw [hdeg] at hd
        simpa using (DFunLike.congr_fun hd j).symm
      · have := (DFunLike.congr_fun hd j).symm
        have erase_eq : d.support.erase j = a.support.erase j := by
          ext i
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, eq_of_ne _ hij]
        simp only [Finsupp.degree, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
        rw [← Finset.add_sum_erase' (f := d) (a := j), ← Finset.add_sum_erase' (f := a) (a := j),
            Finset.sum_congr erase_eq (fun i hi => eq_of_ne i ?_)]
          at this
        · simpa [← add_assoc, ← two_mul] using this
        · exact (Finset.mem_erase.mp hi).1
        · intro h
          exact Finsupp.not_mem_support_iff.mp h
        · intro h
          exact Finsupp.not_mem_support_iff.mp h

lemma MvPolynomial.coeff_zero_mul {σ : Type*} {p q : MvPolynomial σ R} :
    coeff 0 (p * q) = coeff 0 p * coeff 0 q := by
  classical
  rw [coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]

lemma MvPolynomial.X_mul_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : MvPolynomial.X i * p = MvPolynomial.X i * q) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i 1 + d)) h
  simpa [coeff_X_mul, coeff_X_mul] using this

lemma MvPolynomial.mul_X_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : p * MvPolynomial.X i = q * MvPolynomial.X i) : p = q := by
  ext d
  have := congr_arg (coeff (d + Finsupp.single i 1)) h
  rwa [coeff_mul_X, coeff_mul_X] at this

lemma MvPolynomial.coeff_mul_X_pow {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff (m + Finsupp.single i n) (p * MvPolynomial.X i ^ n) =
      MvPolynomial.coeff m p := by
  simp [X_pow_eq_monomial, coeff_mul_monomial']

lemma MvPolynomial.coeff_X_pow_mul {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff (m + Finsupp.single i n) (MvPolynomial.X i ^ n * p) =
      MvPolynomial.coeff m p := by
  simp [X_pow_eq_monomial, coeff_monomial_mul']

lemma MvPolynomial.coeff_X_pow_mul' {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff m (MvPolynomial.X i ^ n * p) =
      if n ≤ m i then MvPolynomial.coeff (m - Finsupp.single i n) p else 0 := by
  simp [X_pow_eq_monomial, coeff_monomial_mul']

lemma MvPolynomial.coeff_mul_X_pow' {σ : Type*} {p : MvPolynomial σ R} {i : σ} {m : σ →₀ ℕ} :
    MvPolynomial.coeff m (p * MvPolynomial.X i ^ n) =
      if n ≤ m i then MvPolynomial.coeff (m - Finsupp.single i n) p else 0 := by
  simp [X_pow_eq_monomial, coeff_mul_monomial']

lemma MvPolynomial.X_mul_pow_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : MvPolynomial.X i ^ n * p = MvPolynomial.X i ^ n * q) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i n + d)) h
  simpa [coeff_X_pow_mul', coeff_X_pow_mul'] using this

lemma MvPolynomial.mul_X_pow_cancel {σ : Type*} {p q : MvPolynomial σ R} {i : σ}
    (h : p * MvPolynomial.X i ^ n = q * MvPolynomial.X i ^ n) : p = q := by
  ext d
  have := congr_arg (coeff (Finsupp.single i n + d)) h
  simpa [coeff_mul_X_pow', coeff_mul_X_pow'] using this

lemma MvPolynomial.X_mul_eq_C_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ} {a : R} :
    MvPolynomial.X i * p = MvPolynomial.C a ↔ a = 0 ∧ p = 0 := by
  classical
  by_cases hp : p = 0
  · rw [hp, eq_comm, mul_zero, map_eq_zero_iff _ (C_injective _ _)]
    simp
  simp only [hp, and_false, iff_false]
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hp
  intro hxi
  have := congr_arg (coeff (Finsupp.single i 1 + d)) hxi
  rw [coeff_X_mul, coeff_C, if_neg (Ne.symm (Finsupp.ne_iff.mpr ⟨i, by simp⟩))] at this
  contradiction

lemma MvPolynomial.mul_X_eq_C_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ} {a : R} :
    p * MvPolynomial.X i = MvPolynomial.C a ↔ a = 0 ∧ p = 0 := by
  rw [mul_comm, X_mul_eq_C_iff]

theorem MvPolynomial.coeff_aeval_X_pow_mul' {σ : Type*} {w : σ → ℕ} {j : σ} (p : MvPolynomial σ R)
    (d : σ →₀ ℕ):
    coeff d (MvPolynomial.aeval (fun i => X j ^ w i * X i) p) =
      if (w j + 1) ∣ Finsupp.weight w d ∧ Finsupp.weight w d / (w j + 1) ≤ d j
      then coeff (d - Finsupp.single j (Finsupp.weight w d / (w j + 1))) p
      else 0 := by
  classical
  split_ifs with hdeg
  · obtain ⟨⟨d', hdeg⟩, hdiv⟩ := hdeg
    rw [hdeg, Nat.mul_div_cancel_left _ (Nat.succ_pos _)] at hdiv ⊢
    rw [← coeff_aeval_X_pow_mul (j := j) p]
    congr
    ext i
    by_cases hij : i = j
    · subst hij
      rw [Finsupp.weight_sub _ _ (Finsupp.single_le_iff.mpr hdiv), Finsupp.weight_single, hdeg,
          mul_comm, ← Nat.mul_sub, Nat.add_sub_cancel_left, mul_one, Finsupp.add_apply,
          Finsupp.tsub_apply, Nat.sub_add_cancel]
      · simpa
    · simp [Ne.symm hij]
  induction p using induction_on'''
  case neg.h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d, if_neg]
    · rintro rfl
      simp at hdeg
  case neg.h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, ih, add_zero, aeval_X_pow_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    refine hdeg ⟨?_, ?_⟩
    · use Finsupp.weight w a
      simp [add_mul, add_comm, mul_comm]
    · rw [map_add, Finsupp.weight_single, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
          add_comm, ← Nat.mul_succ, Nat.mul_div_cancel]
      · exact Nat.le_add_left _ _
      · exact Nat.succ_pos _

theorem MvPolynomial.coeff_aeval_X_mul' {σ : Type*} {j : σ} (p : MvPolynomial σ R) (d : σ →₀ ℕ):
    coeff d (MvPolynomial.aeval (fun i => X j * X i) p) =
      if Even (Finsupp.degree d) ∧ Finsupp.degree d / 2 ≤ d j
      then coeff (d - Finsupp.single j (Finsupp.degree d / 2)) p
      else 0 := by
  classical
  split_ifs with hdeg
  · rw [← coeff_aeval_X_mul (j := j) p]
    congr
    ext i
    by_cases hij : i = j
    · subst hij
      simp [Finsupp.degree_sub _ _ (Finsupp.single_le_iff.mpr hdeg.2), Nat.sub_self_div_two hdeg.1,
          Nat.sub_add_cancel hdeg.2]
    · simp [Ne.symm hij]
  induction p using induction_on'''
  case neg.h_C a =>
    rw [aeval_C, algebraMap_eq, coeff_C d, if_neg]
    · rintro rfl
      simp at hdeg
  case neg.h_add_weak a b p _ _ ih =>
    simp only at *
    rw [map_add, coeff_add, ih, add_zero, aeval_X_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    simp [← two_mul] at hdeg

theorem MvPolynomial.aeval_X_mul_injective {σ : Type*} {j : σ} :
    Function.Injective (MvPolynomial.aeval (R := R) (S₁ := MvPolynomial σ R)
      (fun i => X j * X i)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [MvPolynomial.eq_zero_iff] at hp ⊢
  intro d
  simpa [MvPolynomial.coeff_aeval_X_mul, -MvPolynomial.aeval_eq_bind₁]
    using hp (d + Finsupp.single j (Finsupp.degree d))

theorem MvPolynomial.disjoint_support_rename {σ τ : Type*} {p q : MvPolynomial σ R} (f : σ → τ)
    (hf : f.Injective) (h : Disjoint p.support q.support) :
    Disjoint (MvPolynomial.rename f p).support (MvPolynomial.rename f q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not] at *
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hp
  obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hq
  rw [Finsupp.mapDomain_injective hf u'_eq] at hu'
  exact hu' (h hu)

theorem MvPolynomial.disjoint_support_monomial_mul {σ : Type*} {p q : MvPolynomial σ R}
    (a : σ →₀ ℕ) (b : R) (h : Disjoint p.support q.support) :
    Disjoint (MvPolynomial.monomial a b * p).support (MvPolynomial.monomial a b * q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_monomial_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq ((h (right_ne_zero_of_mul hp)) ▸ mul_zero b)
  · contradiction

theorem MvPolynomial.disjoint_support_X_pow_mul {σ : Type*} {p q : MvPolynomial σ R}
    (j : σ) (n : ℕ) (h : Disjoint p.support q.support) :
    Disjoint (X j ^ n * p).support (X j ^ n * q).support := by
  simpa only [X_pow_eq_monomial] using disjoint_support_monomial_mul (Finsupp.single j n) 1 h

theorem MvPolynomial.disjoint_support_aeval_X_pow_mul {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R} (j : σ) (h : Disjoint p.support q.support) :
    Disjoint
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j ^ w i * MvPolynomial.X i) p).support
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j ^ w i * MvPolynomial.X i) q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_aeval_X_pow_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq (h hp)
  · contradiction

theorem MvPolynomial.disjoint_support_aeval_X_mul {σ : Type*} {p q : MvPolynomial σ R} (j : σ)
    (h : Disjoint p.support q.support) :
    Disjoint
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j * MvPolynomial.X i) p).support
      (MvPolynomial.aeval (S₁ := MvPolynomial σ R) (fun i => MvPolynomial.X j * MvPolynomial.X i) q).support := by
  rw [Finset.disjoint_iff_not_mem_of_mem] at h ⊢
  intro i hp hq
  simp only [mem_support_iff, ne_eq, not_not, coeff_aeval_X_mul'] at *
  split_ifs at hp hq with hdeg
  · exact hq (h hp)
  · contradiction

theorem MvPolynomial.coeff_zero_or_zero_of_disjoint_support {σ : Type*} {p q : MvPolynomial σ R}
    (x : σ →₀ ℕ) (h : Disjoint p.support q.support) :
    MvPolynomial.coeff x p = 0 ∨ MvPolynomial.coeff x q = 0 := by
  simp only [Finset.disjoint_iff_not_mem_or_not_mem, not_mem_support_iff] at h
  cases @h x
  case inl h => simp [h]
  case inr h => simp [h]

theorem MvPolynomial.eval_bind₁ {σ τ : Type*} (f : τ → R) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval f (bind₁ g φ) = eval (fun i => eval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

end MvPolynomial

section Degree

lemma MvPolynomial.totalDegree_C_mul (x : R) (p : MvPolynomial σ R) :
    totalDegree (C x * p) ≤ totalDegree p := by
  simpa [smul_eq_C_mul] using totalDegree_smul_le x p

@[simp] lemma MvPolynomial.totalDegree_X_mul (i : σ) (p : MvPolynomial σ R) (hp0 : p ≠ 0) :
    totalDegree (X i * p) = totalDegree p + 1 := by
  classical
  rw [totalDegree, totalDegree, support_X_mul, Finset.sup_map, ← Finset.sup_add_const,
      Finset.sup_congr rfl]
  · intro a _
    rw [Function.comp_apply, addLeftEmbedding_apply,
        Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
    simp [add_comm]
  · simp [hp0]

@[simp] lemma MvPolynomial.support_C_mul [NoZeroDivisors R] {x : R} (hx : x ≠ 0) (p : MvPolynomial σ R) :
    support (C x * p) = support p := by
  ext i
  simp [hx]

lemma MvPolynomial.totalDegree_C_mul_eq [NoZeroDivisors R] {x : R} (hx : x ≠ 0)
    (p : MvPolynomial σ R) :
    totalDegree (C x * p) = totalDegree p := by
  rw [totalDegree, support_C_mul hx, totalDegree]

/-- The total degree is zero exactly for the constant polynomials. -/
lemma MvPolynomial.weightedTotalDegree_eq_zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    {w : σ → ℕ} (hw : NonTorsionWeight w) :
    weightedTotalDegree w P = 0 ↔ ∃ x, P = C x := by
  simp only [weightedTotalDegree_eq_zero_iff hw, mem_support_iff]
  constructor
  · rintro hdeg
    use constantCoeff P
    ext x
    by_cases hx : x = 0
    · simp [hx, constantCoeff_eq]
    · classical
      rw [coeff_C, if_neg (Ne.symm hx)]
      contrapose! hx
      ext
      exact hdeg _ hx _
  · rintro ⟨x, rfl⟩ m hm i
    classical
    simp only [coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp] at hm
    simp [← hm.1]

/-- The total degree is zero exactly for the constant polynomials. -/
lemma MvPolynomial.totalDegree_eq_zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R} :
    totalDegree P = 0 ↔ ∃ x, P = C x := by
  constructor
  · rintro hdeg
    use constantCoeff P
    ext x
    by_cases hx : x = 0
    · simp [hx, constantCoeff_eq]
    · classical
      rw [coeff_C, if_neg (Ne.symm hx), coeff_eq_zero_of_totalDegree_lt]
      · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hx
        rw [hdeg]
        refine Finset.sum_pos' (fun _ _ => zero_le _)
          ⟨i, Finsupp.mem_support_iff.mpr hi, Nat.pos_of_ne_zero hi⟩
  · rintro ⟨x, rfl⟩
    exact totalDegree_C _

end Degree

end Preliminaries

theorem MvPolynomial.isHomogeneous_of_add_left {σ : Type*} {p q : MvPolynomial σ R}
    (hq : IsHomogeneous q n) (hpq : IsHomogeneous (p + q) n) :
    IsHomogeneous p n := by
  simpa using hpq.sub hq

theorem MvPolynomial.isHomogeneous_of_add_right {σ : Type*} {p q : MvPolynomial σ R}
    (hp : IsHomogeneous p n) (hpq : IsHomogeneous (p + q) n) :
    IsHomogeneous q n := by
  simpa using hpq.sub hp

theorem MvPolynomial.IsWeightedHomogeneous.neg {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p n) :
    IsWeightedHomogeneous w (-p) n := by
  simpa using hp.mul (isWeightedHomogeneous_C _ (-1))

theorem MvPolynomial.IsWeightedHomogeneous.sub {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R}
    (hp : IsWeightedHomogeneous w p n) (hq : IsWeightedHomogeneous w q n) :
    IsWeightedHomogeneous w (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add hq.neg

theorem MvPolynomial.isWeightedHomogeneous_left_of_add_of_disjoint {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R}
    (hpq : IsWeightedHomogeneous w (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsWeightedHomogeneous w p n := by
  intro d hd
  apply hpq
  suffices coeff d q = 0 by rwa [coeff_add, this, add_zero]
  exact not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp hsupp
    (mem_support_iff.mpr hd))

theorem MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint {σ : Type*} {w : σ → ℕ}
    {p q : MvPolynomial σ R}
    (hpq : IsWeightedHomogeneous w (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsWeightedHomogeneous w q n :=
  isWeightedHomogeneous_left_of_add_of_disjoint (by rwa [add_comm]) (by rwa [disjoint_comm])

theorem MvPolynomial.isHomogeneous_left_of_add_of_disjoint {σ : Type*} {p q : MvPolynomial σ R}
    (hpq : IsHomogeneous (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsHomogeneous p n := by
  intro d hd
  apply hpq
  suffices coeff d q = 0 by rwa [coeff_add, this, add_zero]
  exact not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp hsupp
    (mem_support_iff.mpr hd))

theorem MvPolynomial.isHomogeneous_right_of_add_of_disjoint {σ : Type*} {p q : MvPolynomial σ R}
    (hpq : IsHomogeneous (p + q) n) (hsupp : Disjoint (support p) (support q)) :
    IsHomogeneous q n :=
  isHomogeneous_left_of_add_of_disjoint (by rwa [add_comm]) (by rwa [disjoint_comm])

lemma MvPolynomial.isWeightedHomogeneous_zero_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R}
    (hw : NonTorsionWeight w) :
    IsWeightedHomogeneous w p 0 ↔ ∃ a, p = C a := by
  constructor
  · intro h
    use constantCoeff p
    ext i
    by_cases hi : i = 0
    · simp [hi, constantCoeff]
    · classical
      rw [IsWeightedHomogeneous.coeff_eq_zero h, coeff_C, if_neg (Ne.symm hi)]
      · contrapose! hi
        ext j
        rw [weightedDegree_eq_zero_iff hw] at hi
        apply hi
  · rintro ⟨a, rfl⟩
    exact isWeightedHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_zero_iff {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p 0 ↔ ∃ a, p = C a := by
  constructor
  · intro h
    use constantCoeff p
    ext i
    by_cases hi : i = 0
    · simp [hi, constantCoeff]
    · classical
      rw [IsHomogeneous.coeff_eq_zero h, coeff_C, if_neg (Ne.symm hi)]
      · contrapose! hi
        ext j
        rw [Finsupp.degree_eq_weight_one, weightedDegree_eq_zero_iff] at hi
        apply hi
        · refine nonTorsionWeight_of (fun _ => one_ne_zero)
  · rintro ⟨a, rfl⟩
    exact isHomogeneous_C _ _

lemma MvPolynomial.isWeightedHomogeneous_C_iff {σ : Type*} {a : R} {w : σ → ℕ} :
    IsWeightedHomogeneous w (C (σ := σ) a) n ↔ a = 0 ∨ n = 0 := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right ((map_ne_zero_iff _ (C_injective _ _)).mpr ha) (isWeightedHomogeneous_C _ _)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · exact isWeightedHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_C_iff {σ : Type*} {a : R} :
    IsHomogeneous (C (σ := σ) a) n ↔ a = 0 ∨ n = 0 := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right (isHomogeneous_C _ _) ((map_ne_zero_iff _ (C_injective _ _)).mpr ha)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_C _ _

lemma MvPolynomial.isHomogeneous_monomial_iff {σ : Type*} {x : σ →₀ ℕ} {a : R} :
    IsHomogeneous (monomial x a) n ↔ a = 0 ∨ n = Finsupp.degree x := by
  constructor
  · rw [or_iff_not_imp_left]
    intro h ha
    exact h.inj_right (isHomogeneous_monomial _ rfl) (mt monomial_eq_zero.mp ha)
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ rfl

lemma MvPolynomial.isWeightedHomogeneous_mul_X_pow_iff {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} {i : σ} {e : ℕ} (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (p * X i ^ e) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + e * w i := by
  constructor
  · intro hp
    have hn0 : e * w i ≤ n := by
      rw [IsWeightedHomogeneous] at hp
      obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
      rw [← hp (coeff_mul_X_pow.trans_ne hd), Finsupp.weight_add, Finsupp.weight_single]
      exact le_of_add_le_right le_rfl
    refine ⟨n - e * w i, ?_, (Nat.sub_add_cancel hn0).symm⟩
    simp only [IsWeightedHomogeneous, Finsupp.degree_eq_weight_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i e + d) ?_
    · rw [← this, Finsupp.weight_add, Finsupp.weight_single, Nat.add_sub_cancel_left]
    · rwa [add_comm, coeff_mul_X_pow]
  · rintro ⟨m, hp, rfl⟩
    rw [X_pow_eq_monomial]
    exact hp.mul (isWeightedHomogeneous_monomial _ _ _ (by simp))

lemma MvPolynomial.isWeightedHomogeneous_X_pow_mul_iff {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} {i : σ} {e : ℕ} (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (X i ^ e * p) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + e *  w i := by
  rw [mul_comm, isWeightedHomogeneous_mul_X_pow_iff]
  · assumption

lemma MvPolynomial.isWeightedHomogeneous_mul_X_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (p * X i) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + w i := by
  constructor
  · intro hp
    have hn0 : w i ≤ n := by
      rw [IsWeightedHomogeneous] at hp
      obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
      specialize hp ((coeff_mul_X _ _ _).trans_ne hd)
      refine le_of_add_le_right (a := Finsupp.weight w d) (Eq.le ?_)
      rwa [Finsupp.weight_add, Finsupp.weight_single, one_mul] at hp
    refine ⟨n - w i, ?_, (Nat.sub_add_cancel hn0).symm⟩
    rw [← Nat.sub_add_cancel hn0] at hp
    set m := n.pred
    simp only [IsWeightedHomogeneous, Finsupp.degree_eq_weight_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i 1 + d) ?_
    simpa [add_comm] using this
    · rwa [add_comm, coeff_mul_X]
  · rintro ⟨m, hp, rfl⟩
    exact hp.mul (isWeightedHomogeneous_X _ _ _)

lemma MvPolynomial.isWeightedHomogeneous_X_mul_iff {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w (X i * p) n ↔ ∃ m, IsWeightedHomogeneous w p m ∧ n = m + w i := by
  rw [mul_comm, isWeightedHomogeneous_mul_X_iff]
  · assumption

lemma MvPolynomial.isHomogeneous_mul_X_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsHomogeneous (p * X i) n ↔ ∃ m, IsHomogeneous p m ∧ n = m + 1 := by
  constructor
  · intro hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := isHomogeneous_zero_iff.mp hp
      exact hp0 (mul_X_eq_C_iff.mp ha).2
    refine ⟨n.pred, ?_, (Nat.succ_pred_eq_of_ne_zero hn0).symm⟩
    rw [← Nat.succ_pred_eq_of_ne_zero hn0] at hp
    set m := n.pred
    simp only [IsHomogeneous, IsWeightedHomogeneous, Finsupp.degree_eq_weight_one, coeff_mul_X] at hp ⊢
    intro d hd
    have := @hp (Finsupp.single i 1 + d) ?_
    simpa [add_comm 1] using this
    · rwa [add_comm, coeff_mul_X]
  · rintro ⟨m, hp, rfl⟩
    exact hp.mul (isHomogeneous_X _ _)

lemma MvPolynomial.isHomogeneous_X_mul_iff {σ : Type*} {p : MvPolynomial σ R} {i : σ}
    (hp0 : p ≠ 0) :
    IsHomogeneous (X i * p) n ↔ ∃ m, IsHomogeneous p m ∧ n = m + 1 := by
  rw [mul_comm, isHomogeneous_mul_X_iff]
  · assumption

/-- A weighted homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul' {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ MvPolynomial.aeval (fun i => X none ^ (Option.elim i 0 w) * X i) (rename some p) =
      X none ^ n * rename some p := by
  classical
  induction p using MvPolynomial.induction_on'' generalizing n
  case h_C a =>
    rw [isWeightedHomogeneous_C_iff]
    constructor
    · rintro (rfl | rfl)
      · simp
      · simp
    · rw [algHom_C, algebraMap_eq, aeval_C, algebraMap_eq, or_iff_not_imp_right]
      intro h hn
      have h := congr_arg (coeff (Finsupp.single none n)) h.symm
      rwa [coeff_C, mul_comm, coeff_C_mul, coeff_X_pow, if_pos rfl, if_neg, mul_one] at h
      · rwa [eq_comm, Finsupp.single_eq_zero]
  case h_add_weak x a p hx ha ih_r ih_l =>
    -- simp? [rename_monomial, aeval_monomial] at *
    simp only at *
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    have disj : Disjoint ((monomial x) a).support (support p) := by simpa [support_monomial, ha]
    constructor
    · intro h
      have ih_l' := ih_l.mp (MvPolynomial.isWeightedHomogeneous_left_of_add_of_disjoint h disj)
      have ih_r' := ih_r.mp (MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint h disj)
      simp only [map_add, ih_l', ih_r', mul_add]
    · intro h
      rw [map_add, map_add, mul_add] at h
      have disj_lhs := disjoint_support_aeval_X_pow_mul (w := fun i => Option.elim i 0 w) none
        (disjoint_support_rename _ (Option.some_injective _) disj)
      have disj_rhs := disjoint_support_X_pow_mul none n
        (disjoint_support_rename _ (Option.some_injective _) disj)

      have h_l : ∀ (d : Option σ →₀ ℕ),
          coeff d ((aeval fun i ↦ X none ^ (Option.elim i 0 w) * X i) (rename some (monomial x a))) =
          coeff d (X none ^ n * rename some (monomial x a)) := by
        intro d
        obtain (hdl | hdl) := coeff_zero_or_zero_of_disjoint_support d disj_lhs <;>
            obtain (hdr | hdr) := coeff_zero_or_zero_of_disjoint_support d disj_rhs
        · rw [hdl, hdr]
        · have h := MvPolynomial.ext_iff.mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdl, ← h]
          simp only [coeff_aeval_X_pow_mul', coeff_X_pow_mul', Option.elim_none, zero_add,
            Nat.div_one, one_dvd, true_and] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hdeg hn
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (Ne.symm hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ (h.symm.trans_ne (Ne.symm hp))
            have : Finsupp.weight _ d = d none := le_antisymm hdeg <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu')))
          · rw [h]
          · rfl
          · rfl
        -- TODO: this next block is almost the same as the previous one.
        · have h := MvPolynomial.ext_iff.mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdr, h]
          simp only [coeff_aeval_X_pow_mul', coeff_X_pow_mul', Option.elim_none, zero_add,
            Nat.div_one, one_dvd, true_and] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hn hdeg
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (h.trans_ne hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hp
            have : Finsupp.weight _ d = d none := le_antisymm hdeg <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu' (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu)))
          · rw [h]
          · rfl
          · rfl
        · simpa [hdl, hdr, -aeval_eq_bind₁] using MvPolynomial.ext_iff.mp h d
      refine IsWeightedHomogeneous.add
          (ih_l.mpr (MvPolynomial.ext_iff.mpr h_l))
          (ih_r.mpr (MvPolynomial.ext_iff.mpr fun d => ?_))
      have h := MvPolynomial.ext_iff.mp h d
      rw [coeff_add, h_l] at h
      exact add_left_cancel h
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0, -aeval_eq_bind₁] using isWeightedHomogeneous_zero _ _ _
    rw [isWeightedHomogeneous_mul_X_iff]
    constructor
    · rintro ⟨m, hp, rfl⟩
      simp [ih.mp hp, -aeval_eq_bind₁]
      ring
    · intro hp
      have hn0 : w i ≤ n := by
        obtain ⟨d, hd⟩ := ne_zero_iff.mp hp0
        have := (congr_arg (coeff _) hp)
          |>.trans coeff_X_pow_mul
          |>.trans (coeff_rename_mapDomain _ (Option.some_injective _) _ _)
          |>.trans (coeff_mul_X d _ _)
        rw [coeff_aeval_X_pow_mul'] at this
        split_ifs at this with hdeg
        · simp only [Option.elim_none, zero_add, map_add, Finsupp.weight_mapDomain,
              Option.elim_some, Finsupp.weight_single, one_mul, mul_zero, add_zero, isUnit_one,
              IsUnit.dvd, Nat.div_one, Finsupp.coe_add, Pi.add_apply, Set.mem_range, exists_false,
              not_false_eq_true, Finsupp.mapDomain_notin_range, Finsupp.single_eq_same, true_and,
              reduceCtorEq]
            at hdeg
          exact (le_add_left le_rfl).trans hdeg
        · exact (hd this.symm).elim
      refine ⟨n - w i, ih.mpr ?_, (Nat.sub_add_cancel hn0).symm⟩
      rw [← Nat.sub_add_cancel hn0] at hp
      apply mul_X_pow_cancel (i := none) (n := w i)
      apply mul_X_cancel (i := some i)
      simp only [_root_.map_mul, rename_X, aeval_X, Nat.succ_eq_add_one, Option.elim_some] at hp
      rw [pow_add, mul_assoc, mul_left_comm (X none ^ _), ← mul_assoc] at hp
      rw [hp]
      ring
    · assumption

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul' {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ MvPolynomial.aeval (fun i => X none * X i) (rename some p) =
      X none ^ n * rename some p := by
  classical
  induction p using MvPolynomial.induction_on'' generalizing n
  case h_C a =>
    rw [isHomogeneous_C_iff]
    constructor
    · rintro (rfl | rfl)
      · simp
      · simp
    · rw [algHom_C, algebraMap_eq, aeval_C, algebraMap_eq, or_iff_not_imp_right]
      intro h hn
      have h := congr_arg (coeff (Finsupp.single none n)) h.symm
      rwa [coeff_C, mul_comm, coeff_C_mul, coeff_X_pow, if_pos rfl, if_neg, mul_one] at h
      · rwa [eq_comm, Finsupp.single_eq_zero]
  case h_add_weak x a p hx ha ih_r ih_l =>
    simp only at *
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    have disj : Disjoint ((monomial x) a).support (support p) := by simpa [support_monomial, ha]
    constructor
    · intro h
      have ih_l' := ih_l.mp (MvPolynomial.isHomogeneous_left_of_add_of_disjoint h disj)
      have ih_r' := ih_r.mp (MvPolynomial.isHomogeneous_right_of_add_of_disjoint h disj)
      simp only [map_add, ih_l', ih_r', mul_add]
    · intro h
      rw [map_add, map_add, mul_add] at h
      have disj_lhs := disjoint_support_aeval_X_mul none
        (disjoint_support_rename _ (Option.some_injective _) disj)
      have disj_rhs := disjoint_support_X_pow_mul none n
        (disjoint_support_rename _ (Option.some_injective _) disj)

      have h_l : ∀ (d : Option σ →₀ ℕ),
          coeff d ((aeval fun i ↦ X none * X i) (rename some (monomial x a))) =
          coeff d (X none ^ n * rename some (monomial x a)) := by
        intro d
        obtain (hdl | hdl) := coeff_zero_or_zero_of_disjoint_support d disj_lhs <;>
            obtain (hdr | hdr) := coeff_zero_or_zero_of_disjoint_support d disj_rhs
        · rw [hdl, hdr]
        · have h := MvPolynomial.ext_iff.mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdl, ← h]
          simp only [coeff_aeval_X_mul', coeff_X_pow_mul'] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hdeg hn
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (Ne.symm hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ (h.symm.trans_ne (Ne.symm hp))
            have : Finsupp.degree d / 2 = d none := le_antisymm hdeg.2 <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu')))
          · rw [h]
          · rfl
          · rfl
        -- TODO: this next block is almost the same as the previous one.
        · have h := MvPolynomial.ext_iff.mp h d
          rw [coeff_add, hdl, coeff_add, hdr, zero_add, add_zero] at h
          rw [hdr, h]
          simp only [coeff_aeval_X_mul', coeff_X_pow_mul'] at h hdl hdr ⊢
          split_ifs at h hdl hdr ⊢ with hn hdeg
          · by_contra hp
            obtain ⟨u, u_eq, hu⟩ := coeff_rename_ne_zero _ _ _ (h.trans_ne hp)
            obtain ⟨u', u'_eq, hu'⟩ := coeff_rename_ne_zero _ _ _ hp
            have : Finsupp.degree d / 2 = d none := le_antisymm hdeg.2 <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                  using DFunLike.congr_fun u_eq.symm none
            rw [this] at u_eq
            have : n = d none := le_antisymm hn <| by
              simpa [Finsupp.mapDomain_notin_range, Nat.sub_eq_zero_iff_le]
                using DFunLike.congr_fun u'_eq.symm none
            rw [this, ← u_eq] at u'_eq
            rw [Finsupp.mapDomain_injective (Option.some_injective _) u'_eq] at hu'
            exact hu' (not_mem_support_iff.mp (Finset.disjoint_iff_not_mem_of_mem.mp disj
                  (mem_support_iff.mpr hu)))
          · rw [h]
          · rfl
          · rfl
        · simpa [hdl, hdr, -aeval_eq_bind₁] using MvPolynomial.ext_iff.mp h d
      refine IsHomogeneous.add
          (ih_l.mpr (MvPolynomial.ext_iff.mpr h_l))
          (ih_r.mpr (MvPolynomial.ext_iff.mpr fun d => ?_))
      have h := MvPolynomial.ext_iff.mp h d
      rw [coeff_add, h_l] at h
      exact add_left_cancel h
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0, -aeval_eq_bind₁] using isHomogeneous_zero _ _ _
    rw [isHomogeneous_mul_X_iff]
    constructor
    · rintro ⟨m, hp, rfl⟩
      simp [ih.mp hp, -aeval_eq_bind₁]
      ring
    · intro hp
      have hn0 : n ≠ 0 := by
        rintro rfl
        apply hp0
        apply rename_injective _ (Option.some_injective _)
        apply aeval_X_mul_injective
        rw [MvPolynomial.ext_iff] at hp ⊢
        intro d
        rw [map_zero, map_zero, coeff_zero]
        specialize hp (d + Finsupp.single none 1 + Finsupp.single (some i) 1)
        rw [_root_.map_mul, _root_.map_mul, rename_X, aeval_X, ← mul_assoc, coeff_mul_X,
            coeff_mul_X, pow_zero, one_mul, coeff_mul_X] at hp
        rw [hp, ← not_mem_support_iff, support_rename_of_injective (Option.some_injective _),
            Finset.mem_image, not_exists]
        simp only [not_and]
        intro x _ h
        have := DFunLike.congr_fun h none
        rw [Finsupp.mapDomain_notin_range] at this
        simp at this
        · rintro ⟨x, ⟨⟩⟩
      refine ⟨n.pred, ih.mpr ?_, (Nat.succ_pred_eq_of_ne_zero hn0).symm⟩
      rw [← Nat.succ_pred_eq_of_ne_zero hn0] at hp
      set m := n.pred
      apply mul_X_cancel (i := none)
      apply mul_X_cancel (i := some i)
      simp only [_root_.map_mul, rename_X, aeval_X, Nat.succ_eq_add_one] at hp
      rwa [pow_succ, mul_assoc, mul_left_comm (X none), ← mul_assoc, ← mul_assoc, ← mul_assoc]
        at hp
    · assumption

/-- A weighted homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul {σ : Type*} {w : σ → ℕ}
    {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ MvPolynomial.aeval (fun i => X none ^ w i * X (some i)) p =
      X none ^ n * rename some p := by
  rw [isWeightedHomogeneous_iff_comp_smul_eq_pow_smul', aeval_rename]
  rfl

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ MvPolynomial.aeval (fun i => X none * X (some i)) p =
      X none ^ n * rename some p := by
  rw [isHomogeneous_iff_comp_smul_eq_pow_smul', aeval_rename]
  rfl

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isWeightedHomogeneous_iff_eval_smul_eq_pow_smul [Infinite R] [IsDomain R]
    {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p n ↔ ∀ x (f : σ → R),
      MvPolynomial.eval (fun i => x ^ w i * f i) p = x ^ n * eval f p := by
  refine isWeightedHomogeneous_iff_comp_smul_eq_pow_smul.trans ⟨fun h x f => ?_, fun h => ?_⟩
  · have h := congr_arg (eval (fun i => Option.elim i x f)) h
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, Option.elim_none, Option.elim_some,
        coe_eval₂Hom, map_pow, eval_rename] at h
    rw [← eval₂_id]
    convert h
    ext y
    simp
  · apply MvPolynomial.eq_of_eval_eq
    intro x
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, coe_eval₂Hom, map_pow, eval_rename]
    convert (eval₂_id _).trans (h (x none) (x ∘ some))
    ext
    simp

/-- A homogeneous polynomial is one where scaling the variables is equivalent to scaling the
whole polynomial by a power of the scale. -/
theorem MvPolynomial.isHomogeneous_iff_eval_smul_eq_pow_smul [Infinite R] [IsDomain R]
    {σ : Type*} {p : MvPolynomial σ R} :
    IsHomogeneous p n ↔ ∀ x f, MvPolynomial.eval (x • f) p = x ^ n * eval f p := by
  refine isHomogeneous_iff_comp_smul_eq_pow_smul.trans ⟨fun h x f => ?_, fun h => ?_⟩
  · have h := congr_arg (eval (fun i => Option.elim i x f)) h
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, Option.elim_none, Option.elim_some,
        coe_eval₂Hom, map_pow, eval_rename] at h
    rw [← eval₂_id]
    convert h
    ext y
    simp
  · apply MvPolynomial.eq_of_eval_eq
    intro x
    simp only [map_aeval, algebraMap_eq, _root_.map_mul, eval_X, coe_eval₂Hom, map_pow, eval_rename]
    convert (eval₂_id _).trans (h (x none) (x ∘ some))
    ext
    simp

theorem MvPolynomial.IsHomogeneous.of_mul_left [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    (hq : IsHomogeneous q n) (hpq : IsHomogeneous (p * q) (m + n)) (hq0 : q ≠ 0) :
    IsHomogeneous p m := by
  rw [MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hq] at hpq
  exact mul_right_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hq0)) hpq

theorem MvPolynomial.IsWeightedHomogeneous.of_mul_right [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    {w : σ → ℕ}
    (hp : IsWeightedHomogeneous w p m) (hpq : IsWeightedHomogeneous w (p * q) (m + n)) (hp0 : p ≠ 0) :
    IsWeightedHomogeneous w q n := by
  rw [MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hp] at hpq
  exact mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hp0)) hpq

theorem MvPolynomial.IsHomogeneous.of_mul_right [IsDomain R] {σ : Type*} {p q : MvPolynomial σ R}
    (hp : IsHomogeneous p m) (hpq : IsHomogeneous (p * q) (m + n)) (hp0 : p ≠ 0) :
    IsHomogeneous q n := by
  rw [MvPolynomial.isHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hp] at hpq
  exact mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hp0)) hpq

theorem MvPolynomial.isHomogeneous_esymm {σ : Type*} [Fintype σ] {n : ℕ} :
    IsHomogeneous (MvPolynomial.esymm σ R n) n :=
  IsHomogeneous.sum _ _ _ (fun i hi => by
    simpa [(Finset.mem_powersetCard.mp hi).2]
      using IsHomogeneous.prod (R := R) i X 1 (fun t _ => isHomogeneous_X _ _))

/-- A homogeneous polynomial has degree zero if and only if it's constant. -/
lemma MvPolynomial.IsWeightedHomogeneous.zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    {w : σ → ℕ} (hw : NonTorsionWeight w)
    (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) : n = 0 ↔ ∃ x, P = C x := by
  refine Iff.trans ?_ (weightedTotalDegree_eq_zero_iff_exists_C hw)
  constructor
  · rintro rfl
    rwa [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]
  · intro h
    exact IsWeightedHomogeneous.inj_right hP0 hP (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero.mpr h)

/-- A homogeneous polynomial has degree zero if and only if it's constant. -/
lemma MvPolynomial.IsHomogeneous.zero_iff_exists_C {σ : Type*} {P : MvPolynomial σ R}
    (hP : IsHomogeneous P n) (hP0 : P ≠ 0) : n = 0 ↔ ∃ x, P = C x := by
  refine Iff.trans ?_ totalDegree_eq_zero_iff_exists_C
  constructor
  · rintro rfl
    rwa [totalDegree_zero_iff_isHomogeneous]
  · intro h
    exact IsHomogeneous.inj_right hP ((totalDegree_zero_iff_isHomogeneous _).mp h) hP0

/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsWeightedHomogeneous.exists_C_mul_eq_of_dvd [IsDomain R] {σ : Type*}
    {w : σ → ℕ} (hw : NonTorsionWeight w)
    {P Q : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w n) (hQ : Q.IsWeightedHomogeneous w n)
    (hdvd : P ∣ Q) :
    ∃ c, C c * P = Q := by
  obtain ⟨R, rfl⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    ((IsWeightedHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hw hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsHomogeneous.exists_C_mul_eq_of_dvd [IsDomain R] {σ : Type*}
    {P Q : MvPolynomial σ R} (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n) (hdvd : P ∣ Q) :
    ∃ c, C c * P = Q := by
  obtain ⟨R, rfl⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    ((IsHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

lemma MvPolynomial.IsWeightedHomogeneous.bind₁ {σ τ : Type*} {w₁ : σ → ℕ} {w₂ : τ → ℕ}
    {P : MvPolynomial σ R} {Q : σ → MvPolynomial τ R}
    (hP : P.IsWeightedHomogeneous w₁ m) (hQ : ∀ i, (Q i).IsWeightedHomogeneous w₂ (w₁ i * n)) :
    (bind₁ Q P).IsWeightedHomogeneous w₂ (m * n) := by
  induction P using MvPolynomial.induction_on'' generalizing m
  case h_C a =>
    obtain (rfl | rfl) := isWeightedHomogeneous_C_iff.mp hP
    · simpa using isWeightedHomogeneous_zero _ _ _
    · simpa using isWeightedHomogeneous_C _ a
  case h_add_weak a b f ha hb ih_r ih_l =>
    simp only at *
    rw [map_add]
    have : Disjoint ((monomial a) b).support (support f) := by
      classical
      simpa [support_monomial, hb] using ha
    exact (ih_l (isWeightedHomogeneous_left_of_add_of_disjoint hP this)).add
      (ih_r (MvPolynomial.isWeightedHomogeneous_right_of_add_of_disjoint hP this))
  case h_X p i ih =>
    by_cases hp0 : p = 0
    · simpa [hp0] using isWeightedHomogeneous_zero _ _ _
    obtain ⟨m, hp, rfl⟩ := (isWeightedHomogeneous_mul_X_iff hp0).mp hP
    rw [_root_.map_mul, bind₁_X_right, add_mul]
    exact (ih hp).mul (hQ _)

theorem MvPolynomial.IsWeightedHomogeneous.rename {σ τ : Type*}
    {f : σ → τ} {w₁ : σ → ℕ} {w₂ : τ → ℕ} {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w₁ p n)
    (hw : ∀ i, w₂ (f i) = w₁ i) :
    IsWeightedHomogeneous w₂ (rename f p) n := by
  rw [← p.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  apply IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ isWeightedHomogeneous_monomial _ _ _ _
  intro d hd
  simp [hw, h (mem_support_iff.mp hd)]

variable {ι κ : Type*}

lemma MvPolynomial.isHomogeneous_prod_sum_coeff {s : Finset κ} (u : κ → R) :
    (∏ j in s, (∑ i : Fin (m + 1), C (u j ^ (i : ℕ)) * X i)).IsHomogeneous (Finset.card s) := by
  rw [Finset.card_eq_sum_ones]
  exact IsHomogeneous.prod _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ =>
    (isHomogeneous_C _ _).mul (isHomogeneous_X _ _)

lemma MvPolynomial.isHomogeneous_C_mul_prod_sum_coeff {s : Finset κ} (u : κ → R) :
    (C ((-1) ^ (m * n)) * ∏ j in s, (∑ i : Fin (m + 1), C (u j ^ (i : ℕ)) * X i)).IsHomogeneous
      (Finset.card s) :=
  (isHomogeneous_prod_sum_coeff _).C_mul _
