/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Basis.Defs

open Module BigOperators

/-- Imported declaration. -/
structure TimesTable (ι : Type _) (R : Type _) (S : Type _) [Semiring R] [AddCommMonoid S] [Mul S]
    [Module R S] : Type _ where
  /-- Imported declaration. -/
  basis : Basis ι R S
  /-- Imported declaration. -/
  table : ι → ι → ι → R
  basis_mul_basis : ∀ i j k, basis.repr (basis i * basis j) k = table i j k

section add_monoid

variable {ι R S : Type _} [Semiring R] [AddCommMonoid S] [Module R S] [Mul S]

/-- Imported declaration. -/
noncomputable def TimesTable.coord (t : TimesTable ι R S) (x : S) (i : ι) : R :=
t.basis.repr x i

@[simp] lemma TimesTable.basis_repr_eq (t : TimesTable ι R S) (x : S) (i : ι) :
  t.basis.repr x i = t.coord x i := rfl

@[simp] lemma TimesTable.coord_basis [DecidableEq ι] (t : TimesTable ι R S) (i : ι) :
  t.coord (t.basis i) = Pi.single i 1 :=
by ext; rw [← t.basis_repr_eq, t.basis.repr_self i, Finsupp.single_eq_pi_single]

lemma TimesTable.ext (t : TimesTable ι R S) {x y : S} (h : ∀ i, t.coord x i = t.coord y i) :
  x = y :=
t.basis.ext_elem h

end add_monoid

section Semiring
variable {ι R S : Type _} [Fintype ι] [CommSemiring R] [NonUnitalNonAssocSemiring S] [Module R S]
    [IsScalarTower R S S] [SMulCommClass R S S]

lemma TimesTable.unfold_mul' (t : TimesTable ι R S) :
  ∀ x y k, t.basis.repr (x * y) k =
    ∑ i : ι, ∑ j : ι, t.basis.repr x i * t.basis.repr y j * t.table i j k := by
  intros x y k
  conv_lhs => rw [← t.basis.sum_repr x, ← t.basis.sum_repr y]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc, map_smul, mul_smul_comm,
    map_smul, smul_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.coe_smul, ← t.basis_mul_basis]
  rfl

lemma TimesTable.unfold_mul (t : TimesTable ι R S) :
  ∀ x y k, t.coord (x * y) k = ∑ i : ι, ∑ j : ι, t.coord x i * t.coord y j * t.table i j k :=
t.unfold_mul'

omit [Fintype ι] [IsScalarTower R S S] [SMulCommClass R S S] in
@[simp] lemma TimesTable.mul_def (t : TimesTable ι R S) (i j k : ι) :
    t.coord (t.basis i * t.basis j) k = t.table i j k := by
  exact t.basis_mul_basis i j k

/-
@[simp] lemma linear_equiv.map_bit0 {R M N : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M ≃ₗ[R] N) (x : M) : f (bit0 x) = bit0 (f x) :=
by { unfold bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
@[simp] lemma linear_equiv.map_bit1 {R M N : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [One M]
  (f : M ≃ₗ[R] N) (x : M) : f (bit1 x) = bit0 (f x) + f 1 :=
by { unfold bit1 bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
-/

end Semiring

namespace TimesTable

section AddCommMonoid

variable {R S ι : Type _} [CommSemiring R] [AddCommMonoid S] [Module R S]
variable [Mul S]

protected lemma coord_zero (t : TimesTable ι R S) (k : ι) :
  t.coord 0 k = 0 :=
by rw [← t.basis_repr_eq, _root_.map_zero, Finsupp.zero_apply]

/-
protected lemma coord_bit0 (t : TimesTable ι R S) (k : ι) {e₁ : S} {e₁' e' : R}
  (e₁_eq : t.coord e₁ k = e₁') (e_eq : e₁' + e₁' = e') :
  t.coord (bit0 e₁) k = e' :=
by rw [bit0, ← t.basis_repr_eq, _root_.map_add, finsupp.add_apply, t.basis_repr_eq, e₁_eq, e_eq]

protected lemma coord_bit1 [One S] (t : TimesTable ι R S) (k : ι) {e₁ : S} {e₁' e₁2 e' o : R}
  (e₁_eq : t.coord e₁ k = e₁') (one_eq : t.coord 1 k = o) (e2_eq : e₁' + e₁' = e₁2)
  (e_eq : e₁2 + o = e') :
  t.coord (bit1 e₁) k = e' :=
by simp only [← t.basis_repr_eq, bit1, bit0, _root_.map_add, finsupp.add_apply, t.basis_repr_eq,
  e₁_eq, e2_eq, one_eq, e_eq]
-/

protected lemma coord_add (t : TimesTable ι R S) (k : ι) (e₁ e₂ : S) :
  t.coord (e₁ + e₂) k =  t.coord e₁ k + t.coord e₂ k :=
by rw [← t.basis_repr_eq, _root_.map_add, Finsupp.add_apply, t.basis_repr_eq, t.basis_repr_eq]

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable {ι R S : Type _} [Fintype ι] [CommSemiring R] [NonUnitalNonAssocSemiring S] [Module R S]
    [IsScalarTower R S S] [SMulCommClass R S S]

protected lemma coord_mul (t : TimesTable ι R S) (k : ι) (e₁ e₂ : S) (e' : R)
  (eq : ∑ i : ι, ∑ j : ι, t.coord e₁ i * t.coord e₂ j * t.table i j k = e') :
  t.coord (e₁ * e₂) k = e' :=
by rw [TimesTable.unfold_mul t, eq]

protected lemma coord_repr_table
  {r₁i r₂j tijk e₁' e₂' t' e₁e₂ e' : R} (e₁_eq : r₁i = e₁') (e₂_eq : r₂j = e₂')
  (t_eq : tijk = t') (e₁e₂_eq : e₁' * e₂' = e₁e₂) (eq : e₁e₂ * t' = e') :
  r₁i * r₂j * tijk = e' :=
by rw [e₁_eq, e₂_eq, t_eq, e₁e₂_eq, eq]

end NonUnitalNonAssocSemiring

section Semiring

variable {ι R S : Type _} [CommSemiring R] [Semiring S] [Module R S]

protected lemma eval_pow_zero (t : TimesTable ι R S) (k : ι) (e₁ : S) {e' : R}
  (e_eq : t.coord 1 k = e') :
  t.coord (e₁ ^ 0) k = e' :=
by rw [pow_zero, e_eq]

protected lemma eval_pow_one (t : TimesTable ι R S) (k : ι) {e₁ : S} {e' : R}
  (e_eq : t.coord e₁ k = e') :
  t.coord (e₁ ^ 1) k = e' :=
by rw [pow_one, e_eq]

/-
protected lemma eval_pow_bit0 (t : TimesTable ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.coord (e₁ ^ n * e₁ ^ n) k = e') :
  t.coord (e₁ ^ (bit0 n)) k = e' :=
by rw [pow_bit0, e_eq]

protected lemma eval_pow_bit1 (t : TimesTable ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.coord (e₁ ^ n * e₁ ^ n * e₁) k = e') :
  t.coord (e₁ ^ (bit1 n)) k = e' :=
by rw [pow_bit1, e_eq]
-/

end Semiring

section AddCommGroup

variable {R S ι : Type _} [CommRing R] [AddCommGroup S] [Mul S] [Module R S]

protected lemma coord_sub (t : TimesTable ι R S) (k : ι) (e₁ e₂ : S) :
  t.coord (e₁ - e₂) k =  t.coord e₁ k - t.coord e₂ k :=
by rw [← t.basis_repr_eq, map_sub t.basis.repr, Finsupp.sub_apply, t.basis_repr_eq, t.basis_repr_eq]

protected lemma coord_neg (t : TimesTable ι R S) (k : ι) (e : S) :
  t.coord (-e) k = - t.coord e k :=
by rw [← t.basis_repr_eq, map_neg t.basis.repr, Finsupp.neg_apply, t.basis_repr_eq]

end AddCommGroup

open BigOperators Polynomial

-- TODO: could generalize to infinite ι
/-- Imported declaration. -/
@[reducible]
noncomputable def has_mul_of_table {ι R S : Type _} [Fintype ι] [Semiring R]
    [AddCommMonoid S] [Module R S] (b : Basis ι R S) (table : ι → ι → ι → R) :
    Mul S :=
{ mul := fun x y =>
    b.equivFun.symm (fun k => ∑ i, ∑ j, b.repr x i * b.repr y j * table i j k) }

lemma mul_def' {ι R S : Type _} [Fintype ι] [Semiring R]
    [hS : AddCommMonoid S] [Module R S] (b : Basis ι R S) (table : ι → ι → ι → R)
    (x y : S) (k : ι) :
    b.repr (by { letI := has_mul_of_table b table; exact x * y }) k =
      ∑ i, ∑ j, b.repr x i * b.repr y j * table i j k :=
show b.repr (b.equivFun.symm (fun k => ∑ i, ∑ j, b.repr x i * b.repr y j * table i j k)) k =
  ∑ i, ∑ j, b.repr x i * b.repr y j * table i j k
by simp only [← b.equivFun_apply, b.equivFun.apply_symm_apply]

lemma mul_def_of_table {ι R S : Type _} [Fintype ι] [Semiring R]
    [hS : AddCommMonoid S] [Module R S] (b : Basis ι R S) (table : ι → ι → ι → R)
    (i j k : ι) :
    b.repr (by { letI := has_mul_of_table b table; exact b i * b j }) k = table i j k := by
  classical
  rw [mul_def', Fintype.sum_eq_single i, Fintype.sum_eq_single j]
  · simp
  · intros k hk
    simp [Finsupp.single_eq_of_ne hk]
  · intros k hk
    simp [Finsupp.single_eq_of_ne hk]

-- TODO: could generalize to infinite ι
-- See note [reducible non-instances]
/-- Imported declaration. -/
@[reducible]
noncomputable def non_unital_non_assoc_semiring_of_table {ι R S : Type _} [Fintype ι] [Semiring R]
  [hS : AddCommMonoid S] [Module R S] (b : Basis ι R S) (table : ι → ι → ι → R) :
    NonUnitalNonAssocSemiring S :=
{ hS with
  zero := 0,
  add := (·+·),
  mul := (has_mul_of_table b table).mul,
  zero_mul := fun x => b.ext_elem (fun k => by
    rw [mul_def']
    simp only [map_zero b.repr, Finsupp.zero_apply, zero_mul, Finset.sum_const_zero]),
  mul_zero := fun x => b.ext_elem (fun k => by
    rw [mul_def']
    simp only [map_zero b.repr, Finsupp.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]),
  left_distrib := fun x y z => b.ext_elem (fun k => by
    rw [mul_def']
    simp only [map_add b.repr, Finsupp.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
      mul_def']),
  right_distrib := fun x y z => b.ext_elem (fun k => by
    rw [mul_def']
    simp only [map_add b.repr, Finsupp.add_apply, add_mul, Finset.sum_add_distrib, mul_def']) }

end TimesTable

open Polynomial

theorem PowerBasis.repr_gen_pow {R S : Type _} [CommRing R] [Ring S] [Algebra R S]
    (pb : PowerBasis R S) (n : ℕ) (hn : n < pb.dim) :
    pb.basis.repr (pb.gen ^ n) = Finsupp.single ⟨n, hn⟩ 1 := by
  rw [← pb.basis.repr_self, pb.coe_basis]

theorem PowerBasis.repr_aeval_gen_of_natDegree_lt {R S : Type _} [CommRing R] [Ring S] [Algebra R S]
    (pb : PowerBasis R S) (f : R[X]) (hf : f.natDegree < pb.dim) (k) :
    pb.basis.repr (aeval (R := R) pb.gen f) k = f.coeff (k : ℕ) := by
  simp only [aeval_eq_sum_range, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.smul_apply,
      Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (k : ℕ)]
  · rw [pb.repr_gen_pow _ k.isLt, Finsupp.single_eq_same, mul_one]
  · intro i hi hik
    have hi' : i < f.natDegree + 1 := by
      simpa [Finset.mem_range] using hi
    have hip : i < pb.dim := (Nat.le_of_lt_succ hi').trans_lt hf
    rw [pb.repr_gen_pow _ hip, Finsupp.single_eq_of_ne, mul_zero]
    exact fun h => hik (congrArg Fin.val h).symm
  · intro hk
    have hklt : f.natDegree < (k : ℕ) := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hk)
    rw [coeff_eq_zero_of_natDegree_lt hklt, zero_mul]

@[simp]
theorem PowerBasis.repr_aeval_gen {R S : Type _} [CommRing R] [Ring S] [Algebra R S]
    (pb : PowerBasis R S) (f : R[X]) (k) :
    pb.basis.repr (aeval (R := R) pb.gen f) k = (f %ₘ minpoly R pb.gen).coeff (k : ℕ) := by
  conv_lhs => rw [← modByMonic_add_div f (minpoly R pb.gen)]
  simp only [map_add, map_mul, minpoly.aeval, zero_mul, add_zero]
  by_cases h : f %ₘ minpoly R pb.gen = 0
  · rw [h, map_zero, map_zero, Finsupp.zero_apply, coeff_zero]
  have : Nontrivial R := Polynomial.nontrivial_iff.mp ⟨_, _, h⟩
  apply PowerBasis.repr_aeval_gen_of_natDegree_lt
  rw [natDegree_lt_iff_degree_lt h, ← pb.degree_minpoly]
  exact degree_modByMonic_lt _ (minpoly.monic pb.isIntegral_gen)

/-- A power basis determines a times table. -/
noncomputable def PowerBasis.timesTable {R S : Type _} [CommRing R] [Ring S] [Algebra R S]
    (pb : PowerBasis R S) : TimesTable (Fin pb.dim) R S :=
{ basis := pb.basis,
  table := fun i j k =>
    (X^(↑i + ↑j : ℕ) %ₘ minpoly R pb.gen).coeff (k : ℕ),
  basis_mul_basis := by
    intros i j k
    calc
        pb.basis.repr (pb.basis i * pb.basis j) k =
        pb.basis.repr (aeval (R := R) pb.gen (X^(i + j : ℕ))) k :=
      by simp only [PowerBasis.coe_basis, aeval_X, map_mul, map_pow, pow_add]
    _ = (X ^ (↑i + ↑j) %ₘ minpoly R pb.gen).coeff (k : ℕ) :=
      by simp only [pb.repr_aeval_gen] }
