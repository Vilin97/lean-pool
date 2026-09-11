/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
/-!
# Common zeros on products of projective planes

Scratch development, independent of `Submission/Spec.lean`.
The multihomogeneity convention is coefficientwise, so the zero polynomial
is homogeneous of every multidegree.  No projective intersection theorem is
assumed as an axiom.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace KoetheMultiProjective

variable {k : Type*} {N : ℕ}

/-- The polynomial variables, grouped into triples. -/
abbrev Vars (N : ℕ) := Fin N × Fin 3

/-- The degree of an exponent vector in one block. -/
def blockDegree (d : Vars N →₀ ℕ) (b : Fin N) : ℕ :=
  ∑ j : Fin 3, d (b, j)

@[simp] theorem blockDegree_zero (b : Fin N) : blockDegree 0 b = 0 := by
  simp [blockDegree]

@[simp] theorem blockDegree_add (d e : Vars N →₀ ℕ) (b : Fin N) :
    blockDegree (d + e) b = blockDegree d b + blockDegree e b := by
  simp [blockDegree, Finset.sum_add_distrib]

/-- All block degrees of an exponent vector are equal. -/
def Balanced (d : Vars N →₀ ℕ) : Prop :=
  ∀ b c : Fin N, blockDegree d b = blockDegree d c

instance (d : Vars N →₀ ℕ) : Decidable (Balanced d) :=
  inferInstanceAs (Decidable (∀ b c : Fin N, blockDegree d b = blockDegree d c))

@[simp] theorem balanced_zero : Balanced (0 : Vars N →₀ ℕ) := by
  intro b c
  simp

theorem Balanced.add {d e : Vars N →₀ ℕ} (hd : Balanced d) (he : Balanced e) :
    Balanced (d + e) := by
  intro b c
  simp only [blockDegree_add, hd b c, he b c]

theorem Balanced.add_iff_right {d e : Vars N →₀ ℕ} (hd : Balanced d) :
    Balanced (d + e) ↔ Balanced e := by
  constructor
  · intro h b c
    have := h b c
    simpa only [blockDegree_add, hd b c, Nat.add_left_cancel_iff] using this
  · exact hd.add

/-- Coefficientwise multihomogeneity with a specified degree in each block. -/
def IsMultiHomogeneous [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : Fin N → ℕ) : Prop :=
  ∀ d, coeff d f ≠ 0 → ∀ b, blockDegree d b = r b

/-- Every nonzero monomial has the same degree `r` in every block. -/
def IsMultiHomogeneousOfDegree [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : ℕ) : Prop :=
  IsMultiHomogeneous f (fun _ => r)

/-- Polynomials all of whose monomials have balanced block degrees.
Different monomials may have different common degrees. -/
def HasBalancedSupport [CommSemiring k] (f : MvPolynomial (Vars N) k) : Prop :=
  ∀ d, coeff d f ≠ 0 → Balanced d

theorem IsMultiHomogeneousOfDegree.hasBalancedSupport [CommSemiring k]
    {f : MvPolynomial (Vars N) k} {r : ℕ} (hf : IsMultiHomogeneousOfDegree f r) :
    HasBalancedSupport f := by
  intro d hd b c
  exact (hf d hd b).trans (hf d hd c).symm

section MultihomogeneityAPI

variable [CommSemiring k]

@[simp] theorem isMultiHomogeneous_zero (r : Fin N → ℕ) :
    IsMultiHomogeneous (0 : MvPolynomial (Vars N) k) r := by
  intro d hd
  simp at hd

@[simp] theorem isMultiHomogeneousOfDegree_zero (r : ℕ) :
    IsMultiHomogeneousOfDegree (0 : MvPolynomial (Vars N) k) r :=
  isMultiHomogeneous_zero _

theorem isMultiHomogeneous_monomial {d : Vars N →₀ ℕ} {r : Fin N → ℕ}
    (hd : ∀ b, blockDegree d b = r b) (a : k) :
    IsMultiHomogeneous (monomial d a) r := by
  classical
  intro e he
  by_cases h : d = e
  · subst e
    exact hd
  · simp [coeff_monomial, h] at he

theorem IsMultiHomogeneous.add {p q : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q r) :
    IsMultiHomogeneous (p + q) r := by
  intro d hd
  by_cases h : coeff d p = 0
  · apply hq d
    simpa [coeff_add, h] using hd
  · exact hp d h

theorem IsMultiHomogeneous.smul {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (a : k) : IsMultiHomogeneous (a • p) r := by
  intro d hd
  apply hp d
  exact right_ne_zero_of_mul (by simpa only [coeff_smul, smul_eq_mul] using hd)

theorem IsMultiHomogeneous.mul {p q : MvPolynomial (Vars N) k} {r s : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q s) :
    IsMultiHomogeneous (p * q) (r + s) := by
  classical
  intro d hd b
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hef, blockDegree_add,
    hp e (left_ne_zero_of_mul h) b, hq f (right_ne_zero_of_mul h) b]
  rfl

theorem IsMultiHomogeneous.pow {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (n : ℕ) :
    IsMultiHomogeneous (p ^ n) (fun b => n * r b) := by
  induction n with
  | zero =>
    have h := isMultiHomogeneous_monomial (fun b : Fin N => blockDegree_zero b) (1 : k)
    rw [monomial_zero', C_1] at h
    simpa only [pow_zero, Nat.zero_mul] using h
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hp using 1
    funext b
    simp [Nat.add_mul]

theorem IsMultiHomogeneousOfDegree.add {p q : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q r) :
    IsMultiHomogeneousOfDegree (p + q) r := IsMultiHomogeneous.add hp hq

theorem IsMultiHomogeneousOfDegree.mul {p q : MvPolynomial (Vars N) k} {r s : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q s) :
    IsMultiHomogeneousOfDegree (p * q) (r + s) := IsMultiHomogeneous.mul hp hq

theorem IsMultiHomogeneousOfDegree.pow {p : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (n : ℕ) :
    IsMultiHomogeneousOfDegree (p ^ n) (n * r) := IsMultiHomogeneous.pow hp n

end MultihomogeneityAPI

section BalancedAlgebra

variable [CommSemiring k]

theorem hasBalancedSupport_monomial {d : Vars N →₀ ℕ} (hd : Balanced d) (a : k) :
    HasBalancedSupport (monomial d a) := by
  classical
  intro e he
  by_cases h : d = e
  · simpa [← h] using hd
  · simp [coeff_monomial, h] at he

theorem hasBalancedSupport_add {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p + q) := by
  intro d hd
  by_cases h : coeff d p = 0
  · apply hq d
    simpa [coeff_add, h] using hd
  · exact hp d h

theorem hasBalancedSupport_mul {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p * q) := by
  classical
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have he : coeff e p ≠ 0 := left_ne_zero_of_mul h
  have hf : coeff f q ≠ 0 := right_ne_zero_of_mul h
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hef]
  exact (hp e he).add (hq f hf)

/-- The diagonal (balanced-degree) monomial subalgebra. -/
def balancedAlgebra (k : Type*) [CommSemiring k] (N : ℕ) :
    Subalgebra k (MvPolynomial (Vars N) k) where
  carrier := {p | HasBalancedSupport p}
  zero_mem' := by intro d hd; simp at hd
  one_mem' := hasBalancedSupport_monomial balanced_zero 1
  add_mem' := hasBalancedSupport_add
  mul_mem' := hasBalancedSupport_mul
  algebraMap_mem' a := hasBalancedSupport_monomial balanced_zero a

@[simp] theorem mem_balancedAlgebra {p : MvPolynomial (Vars N) k} :
    p ∈ balancedAlgebra k N ↔ HasBalancedSupport p := Iff.rfl

/-- Exponent vector of a degree-one Segre coordinate. -/
def segreExponent (j : Fin N → Fin 3) : Vars N →₀ ℕ :=
  ∑ b : Fin N, Finsupp.single (b, j b) 1

@[simp] theorem segreExponent_apply (j : Fin N → Fin 3) (b : Fin N) (c : Fin 3) :
    segreExponent j (b, c) = if j b = c then 1 else 0 := by
  classical
  simp only [segreExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single b]
  · simp [Finsupp.single_apply, Prod.mk.injEq]
  · intro a _ ha
    simp [Prod.mk.injEq, ha]
  · simp

@[simp] theorem blockDegree_segreExponent (j : Fin N → Fin 3) (b : Fin N) :
    blockDegree (segreExponent j) b = 1 := by
  classical
  simp [blockDegree]

theorem balanced_segreExponent (j : Fin N → Fin 3) : Balanced (segreExponent j) := by
  intro b c
  simp

/-- A degree-one Segre coordinate, as a polynomial in the original triples. -/
def segreMonomial (j : Fin N → Fin 3) : MvPolynomial (Vars N) k :=
  ∏ b : Fin N, X (b, j b)

theorem segreMonomial_eq_monomial (j : Fin N → Fin 3) :
    segreMonomial (k := k) j = monomial (segreExponent j) 1 := by
  classical
  simp [segreMonomial, segreExponent, monomial_sum_one, X]

theorem isMultiHomogeneousOfDegree_segreMonomial (j : Fin N → Fin 3) :
    IsMultiHomogeneousOfDegree (segreMonomial (k := k) j) 1 := by
  rw [segreMonomial_eq_monomial]
  exact isMultiHomogeneous_monomial (blockDegree_segreExponent j) 1

theorem segreMonomial_mem (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ∈ balancedAlgebra k N := by
  rw [segreMonomial_eq_monomial]
  exact hasBalancedSupport_monomial (balanced_segreExponent j) 1

theorem exponent_eq_zero_of_blockDegree_zero {d : Vars N →₀ ℕ}
    (hd : ∀ b, blockDegree d b = 0) : d = 0 := by
  classical
  ext ⟨b, j⟩
  have h : d (b, j) ≤ blockDegree d b :=
    Finset.single_le_sum (f := fun j : Fin 3 => d (b, j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa [hd b] using h

theorem exists_segreExponent_le {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r + 1) :
    ∃ j : Fin N → Fin 3, segreExponent j ≤ d := by
  classical
  have hpos : ∀ b, ∃ j : Fin 3, 0 < d (b, j) := by
    intro b
    by_contra! h
    have hzero : blockDegree d b = 0 := by
      simp [blockDegree, Nat.eq_zero_of_le_zero (h _)]
    have := hd b
    omega
  choose j hj using hpos
  refine ⟨j, ?_⟩
  intro ⟨b, c⟩
  simp only [segreExponent_apply]
  split_ifs with h
  · subst c
    exact hj b
  · exact Nat.zero_le _

/-- A balanced monomial factors into degree-one Segre monomials.
This is the finite-generation step, proved by induction on the common degree. -/
theorem monomial_mem_adjoin_segre {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r) (a : k) :
    monomial d a ∈ Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) := by
  classical
  induction r generalizing d with
  | zero =>
    have : d = 0 := exponent_eq_zero_of_blockDegree_zero hd
    subst d
    exact Subalgebra.algebraMap_mem _ a
  | succ r ih =>
    obtain ⟨j, hj⟩ := exists_segreExponent_le hd
    have hde : segreExponent j + (d - segreExponent j) = d := add_tsub_cancel_of_le hj
    have hrem : ∀ b, blockDegree (d - segreExponent j) b = r := by
      intro b
      have h := congrArg (fun e => blockDegree e b) hde
      simp only [blockDegree_add, blockDegree_segreExponent, hd b] at h
      omega
    have hm : monomial d a = segreMonomial j * monomial (d - segreExponent j) a := by
      rw [segreMonomial_eq_monomial, monomial_mul, one_mul, hde]
    rw [hm]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨j, rfl⟩) (ih hrem)

/-- The balanced subalgebra is generated by the finitely many Segre coordinates. -/
theorem adjoin_segre_eq_balancedAlgebra [NeZero N] :
    Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) = balancedAlgebra k N := by
  classical
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact segreMonomial_mem j
  · intro p hp
    rw [p.as_sum]
    apply Subalgebra.sum_mem
    intro d hd
    apply monomial_mem_adjoin_segre (r := blockDegree d 0)
    intro b
    exact hp d (mem_support_iff.mp hd) b 0

end BalancedAlgebra

instance balancedAlgebra_isNoetherianRing [CommRing k] [IsNoetherianRing k] [NeZero N] :
    IsNoetherianRing (balancedAlgebra k N) := by
  apply isNoetherianRing_of_fg
  exact Subalgebra.fg_def.mpr ⟨Set.range segreMonomial, Set.finite_range _,
    adjoin_segre_eq_balancedAlgebra⟩

section Retraction

variable [CommSemiring k]

/-- Keep just the monomials whose block degrees are all equal. -/
def balancedPart : MvPolynomial (Vars N) k →ₗ[k] MvPolynomial (Vars N) k where
  toFun p := (AddMonoidAlgebra.coeffLinearEquiv k).symm
    (Finsupp.filter Balanced (AddMonoidAlgebra.coeffLinearEquiv k p))
  map_add' _ _ := by simp [Finsupp.filter_add]
  map_smul' _ _ := by simp [Finsupp.filter_smul]

@[simp] theorem coeff_balancedPart (p : MvPolynomial (Vars N) k) (d : Vars N →₀ ℕ) :
    coeff d (balancedPart p) = if Balanced d then coeff d p else 0 := by
  simp [balancedPart, MvPolynomial.coeff, Finsupp.filter_apply]

theorem balancedPart_mem (p : MvPolynomial (Vars N) k) :
    balancedPart p ∈ balancedAlgebra k N := by
  classical
  intro d hd
  by_contra h
  simp [h] at hd

@[simp] theorem balancedPart_of_mem {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) : balancedPart p = p := by
  classical
  ext d
  rw [coeff_balancedPart]
  by_cases h : Balanced d
  · simp [h]
  · have hc : coeff d p = 0 := by
      by_contra hc
      exact h (hp d hc)
    simp [h, hc]

@[simp] theorem balancedPart_monomial (d : Vars N →₀ ℕ) (a : k) :
    balancedPart (monomial d a) = if Balanced d then monomial d a else 0 := by
  classical
  ext e
  rw [coeff_balancedPart]
  rcases eq_or_ne d e with rfl | hde
  · split_ifs <;> simp [coeff_monomial]
  · simp [coeff_monomial, hde, apply_ite (coeff e)]

theorem balancedPart_monomial_mul {d : Vars N →₀ ℕ} (hd : Balanced d)
    (a : k) (q : MvPolynomial (Vars N) k) :
    balancedPart (monomial d a * q) = monomial d a * balancedPart q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [monomial_mul, balancedPart_monomial, balancedPart_monomial]
    simp only [hd.add_iff_right]
    split_ifs <;> simp [monomial_mul]
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]

/-- The balanced-monomial projection is linear over the whole balanced subalgebra,
not merely over the coefficient field. -/
theorem balancedPart_mul {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) (q : MvPolynomial (Vars N) k) :
    balancedPart (p * q) = p * balancedPart q := by
  classical
  calc
    balancedPart (p * q) =
        balancedPart ((∑ d ∈ p.support, monomial d (coeff d p)) * q) := by
      congr 2
      exact p.as_sum
    _ = ∑ d ∈ p.support, balancedPart (monomial d (coeff d p) * q) := by
      simp only [Finset.sum_mul, map_sum]
    _ = ∑ d ∈ p.support, monomial d (coeff d p) * balancedPart q := by
      apply Finset.sum_congr rfl
      intro d hd
      exact balancedPart_monomial_mul (hp d (mem_support_iff.mp hd)) _ _
    _ = p * balancedPart q := by rw [← Finset.sum_mul, ← p.as_sum]

/-- The same projection with codomain restricted to the balanced algebra. -/
def balancedRetract : MvPolynomial (Vars N) k →ₗ[k] balancedAlgebra k N :=
  balancedPart.codRestrict (balancedAlgebra k N).toSubmodule balancedPart_mem

@[simp] theorem coe_balancedRetract (p : MvPolynomial (Vars N) k) :
    (balancedRetract p : MvPolynomial (Vars N) k) = balancedPart p := rfl

@[simp] theorem balancedRetract_coe (p : balancedAlgebra k N) :
    balancedRetract (p : MvPolynomial (Vars N) k) = p := by
  apply Subtype.ext
  exact balancedPart_of_mem p.property

@[simp] theorem balancedRetract_mul (p : balancedAlgebra k N)
    (q : MvPolynomial (Vars N) k) :
    balancedRetract ((p : MvPolynomial (Vars N) k) * q) = p * balancedRetract q := by
  apply Subtype.ext
  exact balancedPart_mul p.property q

/-- Extending an ideal generated by balanced polynomials to the ambient polynomial
ring and contracting it back introduces no new balanced elements. -/
theorem mem_span_range_coe_iff {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k))) ↔
      p ∈ Ideal.span (Set.range f) := by
  classical
  cases nonempty_fintype ι
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg balancedRetract ha
    have hsum : (∑ i, balancedRetract (a i) * f i) = p := by
      simpa only [smul_eq_mul, map_sum, mul_comm, balancedRetract_mul,
        balancedRetract_coe] using h
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg (balancedAlgebra k N).val ha
    simp only [smul_eq_mul, map_sum, map_mul] at h
    change ∑ i, (a i : MvPolynomial (Vars N) k) * (f i : MvPolynomial (Vars N) k) =
      (p : MvPolynomial (Vars N) k) at h
    rw [← h]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))

theorem mem_radical_span_range_coe_iff {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        (Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k)))).radical ↔
      p ∈ (Ideal.span (Set.range f)).radical := by
  simp only [Ideal.mem_radical_iff, ← Subalgebra.coe_pow, mem_span_range_coe_iff]

end Retraction

section Height

variable [Field k]

/-- A Segre coordinate as an element of the balanced subalgebra. -/
def segre (j : Fin N → Fin 3) : balancedAlgebra k N :=
  ⟨segreMonomial j, segreMonomial_mem j⟩

@[simp] theorem coe_segre (j : Fin N → Fin 3) :
    (segre (k := k) j : MvPolynomial (Vars N) k) = segreMonomial j := rfl

theorem segreMonomial_ne_zero (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => X_ne_zero _)

@[simp] theorem constantCoeff_segreMonomial [NeZero N] (j : Fin N → Fin 3) :
    constantCoeff (segreMonomial (k := k) j) = 0 := by
  classical
  simp [segreMonomial, NeZero.ne N]

/-- Set a specified finite set of ambient variables to zero. -/
def killVars (s : Finset (Vars N)) :
    MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k := by
  classical
  exact aeval (fun v => if v ∈ s then 0 else X v)

@[simp] theorem killVars_X (s : Finset (Vars N)) (v : Vars N) :
    killVars (k := k) s (X v) = if v ∈ s then 0 else X v := by
  classical
  simp [killVars]

theorem killVars_comp_of_subset {s t : Finset (Vars N)} (hst : s ⊆ t) :
    (killVars (k := k) t).comp (killVars s) = killVars t := by
  classical
  ext v
  by_cases h : v ∈ s
  · simp [h, hst h]
  · simp [h]

theorem zero_aeval_comp_killVars (s : Finset (Vars N)) :
    (aeval (R := k) (fun _ : Vars N => (0 : k))).comp (killVars (k := k) s) =
      aeval (R := k) (fun _ : Vars N => (0 : k)) := by
  classical
  ext v
  by_cases h : v ∈ s <;> simp [h]

/-- Contract a prime variable ideal to the balanced subalgebra. -/
def killedIdeal (s : Finset (Vars N)) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((killVars s).comp (balancedAlgebra k N).val).toRingHom)

@[simp] theorem mem_killedIdeal (s : Finset (Vars N)) (p : balancedAlgebra k N) :
    p ∈ killedIdeal s ↔ killVars s (p : MvPolynomial (Vars N) k) = 0 := Iff.rfl

instance killedIdeal_isPrime (s : Finset (Vars N)) :
    (killedIdeal (k := k) s).IsPrime := RingHom.ker_isPrime _

/-- The vertex of the affine Segre cone: the augmentation ideal. -/
def vertexIdeal (k : Type*) [Field k] (N : ℕ) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((aeval (fun _ : Vars N => (0 : k))).comp
    (balancedAlgebra k N).val).toRingHom)

@[simp] theorem mem_vertexIdeal (p : balancedAlgebra k N) :
    p ∈ vertexIdeal k N ↔ constantCoeff (p : MvPolynomial (Vars N) k) = 0 := by
  change aeval (fun _ : Vars N => (0 : k)) (p : MvPolynomial (Vars N) k) = 0 ↔ _
  simp

instance vertexIdeal_isPrime : (vertexIdeal k N).IsPrime := RingHom.ker_isPrime _

theorem killedIdeal_mono {s t : Finset (Vars N)} (hst : s ⊆ t) :
    killedIdeal (k := k) s ≤ killedIdeal t := by
  intro p hp
  rw [mem_killedIdeal] at hp ⊢
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k =>
    φ (p : MvPolynomial (Vars N) k)) (killVars_comp_of_subset hst)
  simpa [hp] using h.symm

theorem killedIdeal_le_vertexIdeal (s : Finset (Vars N)) :
    killedIdeal (k := k) s ≤ vertexIdeal k N := by
  intro p hp
  rw [mem_killedIdeal] at hp
  rw [mem_vertexIdeal]
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] k =>
    φ (p : MvPolynomial (Vars N) k)) (zero_aeval_comp_killVars s)
  simpa [hp] using h.symm

theorem killVars_segreMonomial_of_disjoint (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (hj : ∀ b, (b, j b) ∉ s) :
    killVars (k := k) s (segreMonomial j) = segreMonomial j := by
  classical
  simp [segreMonomial, hj]

theorem killVars_segreMonomial_of_mem (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (b : Fin N) (hb : (b, j b) ∈ s) :
    killVars (k := k) s (segreMonomial j) = 0 := by
  classical
  simp only [segreMonomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

/-- Choose the newly killed variable in its block and the protected coordinate `2`
in every other block. -/
def separatingChoice (v : Vars N) (b : Fin N) : Fin 3 :=
  if b = v.1 then v.2 else 2

theorem separatingChoice_avoids {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    ∀ b, (b, separatingChoice v b) ∉ s := by
  intro b
  by_cases h : b = v.1
  · subst b
    simpa [separatingChoice] using hv
  · simpa [separatingChoice, h] using hprotect b

/-- Each additional killed coordinate strictly increases the contracted prime ideal. -/
theorem killedIdeal_lt_insert {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    killedIdeal (k := k) s < killedIdeal (insert v s) := by
  classical
  refine lt_of_le_of_ne (killedIdeal_mono (Finset.subset_insert _ _)) ?_
  intro heq
  have hmem : segre (k := k) (separatingChoice v) ∈ killedIdeal (insert v s) := by
    rw [mem_killedIdeal, coe_segre]
    apply killVars_segreMonomial_of_mem _ _ v.1
    simp [separatingChoice]
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ (separatingChoice_avoids hprotect hv)] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The final strict step kills the remaining positive-degree balanced monomials. -/
theorem killedIdeal_lt_vertexIdeal [NeZero N] {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    killedIdeal (k := k) s < vertexIdeal k N := by
  refine lt_of_le_of_ne (killedIdeal_le_vertexIdeal s) ?_
  intro heq
  have hmem : segre (k := k) (fun _ : Fin N => 2) ∈ vertexIdeal k N := by
    simp
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ hprotect] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The height of a contracted variable ideal is at least the number of killed
coordinates, as long as one coordinate in every block remains protected. -/
theorem card_le_height_killedIdeal (s : Finset (Vars N))
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    (s.card : ℕ∞) ≤ (killedIdeal (k := k) s).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
      intro b hb
      exact hprotect b (Finset.mem_insert_of_mem hb)
    have hlt : (killedIdeal (k := k) s).height + 1 ≤ (killedIdeal (k := k) (insert v s)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime (killedIdeal_lt_insert (k := k) hs hv)
    calc
      ((insert v s).card : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hv]
      _ ≤ (killedIdeal (k := k) s).height + 1 := add_le_add (ih hs) le_rfl
      _ ≤ (killedIdeal (k := k) (insert v s)).height := hlt

/-- The Segre cone vertex has height at least `2*N + 1`.
The proof constructs all `2*N + 1` strict prime-ideal steps explicitly. -/
theorem vertexIdeal_height_lower_bound [NeZero N] :
    (2 * N + 1 : ℕ∞) ≤ (vertexIdeal k N).height := by
  classical
  let s : Finset (Vars N) := Finset.univ ×ˢ ({0, 1} : Finset (Fin 3))
  have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
    intro b
    simp [s]
  have hcard : s.card = 2 * N := by
    simp [s, Finset.card_product, Nat.mul_comm]
  have hlt : (killedIdeal (k := k) s).height + 1 ≤ (vertexIdeal k N).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (killedIdeal_lt_vertexIdeal (k := k) hs)
  calc
    (2 * N + 1 : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hcard]
    _ ≤ (killedIdeal (k := k) s).height + 1 :=
      add_le_add (card_le_height_killedIdeal s hs) le_rfl
    _ ≤ (vertexIdeal k N).height := hlt

end Height

section CommonZeros

variable [Field k]

theorem IsMultiHomogeneousOfDegree.constantCoeff_eq_zero [NeZero N]
    {f : MvPolynomial (Vars N) k} {r : ℕ}
    (hf : IsMultiHomogeneousOfDegree f r) (hr : 0 < r) : constantCoeff f = 0 := by
  change coeff 0 f = 0
  by_contra h
  have hdeg := hf 0 h (0 : Fin N)
  simp only [blockDegree_zero] at hdeg
  omega

/-- On an assignment with one zero block, any balanced polynomial evaluates
to its constant coefficient. -/
theorem eval_eq_constantCoeff_of_block_zero [NeZero N]
    {p : MvPolynomial (Vars N) k} (hp : p ∈ balancedAlgebra k N)
    {x : Vars N → k} {b : Fin N} (hx : ∀ j, x (b, j) = 0) :
    eval x p = constantCoeff p := by
  classical
  rw [← adjoin_segre_eq_balancedAlgebra] at hp
  refine Algebra.adjoin_induction (p := fun p _ => eval x p = constantCoeff p)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨j, rfl⟩
    rw [constantCoeff_segreMonomial]
    simp only [segreMonomial, map_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (hx (j b))
  · intro a
    simp
  · intro p q _ _ hp hq
    simp only [map_add, hp, hq]
  · intro p q _ _ hp hq
    simp only [map_mul, hp, hq]

variable [IsAlgClosed k] [NeZero N]

/-- If balanced polynomials with zero constant term have no common zero with all
blocks nonzero, their ideal in the balanced subalgebra has radical the vertex.
This is the affine Nullstellensatz plus the explicitly proved retraction. -/
theorem radical_span_eq_vertex_of_no_common_zero {ι : Type*} [Finite ι]
    (f : ι → balancedAlgebra k N) (hf : ∀ i, f i ∈ vertexIdeal k N)
    (hno : ¬ ∃ x : Vars N → k, (∀ b, ∃ j, x (b, j) ≠ 0) ∧
      ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0) :
    (Ideal.span (Set.range f)).radical = vertexIdeal k N := by
  classical
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (vertexIdeal_isPrime (k := k) (N := N))).mpr
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hf i
  · intro p hp
    apply (mem_radical_span_range_coe_iff f p).mp
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hfx : ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0 := by
      intro i
      exact hx _ (Ideal.mem_span_range_self (x := i))
    have hbad : ∃ b, ∀ j, x (b, j) = 0 := by
      by_contra! hgood
      exact hno ⟨x, hgood, hfx⟩
    obtain ⟨b, hb⟩ := hbad
    change eval x (p : MvPolynomial (Vars N) k) = 0
    rw [eval_eq_constantCoeff_of_block_zero p.property hb]
    exact (mem_vertexIdeal p).mp hp

/-- A slightly stronger algebraic theorem: the polynomials may be sums of balanced
monomials of different degrees, provided all constant coefficients vanish. -/
theorem exists_common_zero_balanced {q : ℕ} (hq : q ≤ 2 * N)
    (f : Fin q → balancedAlgebra k N) (hf : ∀ i, f i ∈ vertexIdeal k N) :
    ∃ x : Vars N → k, (∀ b, ∃ j, x (b, j) ≠ 0) ∧
      ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0 := by
  classical
  by_contra hno
  have hrad := radical_span_eq_vertex_of_no_common_zero f hf hno
  have hmin : vertexIdeal k N ∈ (Ideal.span (Set.range f)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hupper := Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_range f) hmin
  have hcard : (Set.range f).ncard ≤ q := by
    simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
      (Set.ncard_image_le (s := Set.univ) (f := f) Set.finite_univ)
  have hbound : (2 * N + 1 : ℕ∞) ≤ q :=
    (vertexIdeal_height_lower_bound (k := k) (N := N)).trans
      (hupper.trans (by exact_mod_cast hcard))
  have hnat : 2 * N + 1 ≤ q := by exact_mod_cast hbound
  omega

end CommonZeros

/-- **Multiprojective common-zero theorem.** Over an algebraically closed field,
at most `2*N` polynomials of common positive degree in every one of `N` blocks
of three variables have a common zero with no zero block.

The proof is entirely affine commutative algebra: finite generation of the balanced
monomial algebra, a linear retraction, the Nullstellensatz, an explicit chain of
prime ideals, and Krull's height theorem. -/
theorem exists_common_zero [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i, IsMultiHomogeneousOfDegree (f i) r) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ∀ i : Fin q, eval x (f i) = 0 := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let fs : Fin q → balancedAlgebra k N :=
    fun i => ⟨f i, (hf i).hasBalancedSupport⟩
  have hfs : ∀ i, fs i ∈ vertexIdeal k N := by
    intro i
    rw [mem_vertexIdeal]
    exact (hf i).constantCoeff_eq_zero hr
  obtain ⟨x, hx, hfx⟩ := exists_common_zero_balanced hq fs hfs
  refine ⟨x, ?_, hfx⟩
  intro b hb
  obtain ⟨j, hj⟩ := hx b
  exact hj (congrFun hb j)

/-- An entry point with the multihomogeneity hypothesis fully expanded in terms
of coefficients and blockwise sums of exponents. -/
theorem exists_common_zero_of_coeff [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i d, coeff d (f i) ≠ 0 → ∀ b : Fin N, ∑ j : Fin 3, d (b, j) = r) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ∀ i : Fin q, eval x (f i) = 0 :=
  exists_common_zero f hN hr hq hf

/-- The same result with the assignment written as a family of nonzero vectors. -/
theorem exists_common_zero_vectors [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i, IsMultiHomogeneousOfDegree (f i) r) :
    ∃ x : Fin N → Fin 3 → k, (∀ b, x b ≠ 0) ∧
      ∀ i, eval (fun v => x v.1 v.2) (f i) = 0 := by
  obtain ⟨x, hx, hfx⟩ := exists_common_zero f hN hr hq hf
  exact ⟨fun b j => x (b, j), hx, hfx⟩

end KoetheMultiProjective

end
