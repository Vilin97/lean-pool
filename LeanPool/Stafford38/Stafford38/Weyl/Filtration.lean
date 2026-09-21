/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.PBW

/-!
# Weighted PBW truncations

The ordered PBW basis gives intrinsic finite-degree subspaces of the presented
Weyl algebra.  This file constructs the truncations for an arbitrary weight on
the named generators, proves their coefficient characterization, monotonicity,
exhaustiveness, and basis-monomial membership, and specializes them to the
Bernstein and order weights.  Exact normal ordering then proves multiplicative
closure.  Leading symbols and the associated graded algebra remain downstream.
-/

namespace Stafford38.WeylFiltration

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Weighted degree of a commutative phase-space monomial. -/
def monomialWeight {n : ℕ} (w : PhaseVar n → ℕ)
    (m : PhaseVar n →₀ ℕ) : ℕ :=
  m.sum fun i e => e * w i

/-- Extend an old exponent vector by exponents for the newest coordinate and
momentum. -/
def extendPhaseExponent (n a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    PhaseVar (n + 1) →₀ ℕ :=
  Finsupp.single (.inr (0 : Fin (n + 1))) p +
    Finsupp.single (.inl (0 : Fin (n + 1))) a +
    Finsupp.mapDomain oldIndex m

theorem monomialWeight_mono {n : ℕ} {w₁ w₂ : PhaseVar n → ℕ}
    (h : ∀ i, w₁ i ≤ w₂ i) (m : PhaseVar n →₀ ℕ) :
    monomialWeight w₁ m ≤ monomialWeight w₂ m := by
  apply Finsupp.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (h i)

/-- Symbols supported on monomials of weighted degree at most `N`. -/
def symbolWeightPiece {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    Submodule k (SymbolRing k n) where
  carrier := {f | ∀ m, f.coeff m ≠ 0 → monomialWeight w m ≤ N}
  zero_mem' m hm := by simp at hm
  add_mem' {f g} hf hg m hm := by
    by_cases hfm : f.coeff m = 0
    · apply hg m
      simpa [MvPolynomial.coeff_add, hfm] using hm
    · exact hf m hfm
  smul_mem' c f hf m hm := by
    apply hf m
    intro hfm
    apply hm
    simp [MvPolynomial.coeff_smul, hfm]

@[simp] theorem mem_symbolWeightPiece {n : ℕ} (w : PhaseVar n → ℕ)
    (N : ℕ) (f : SymbolRing k n) :
    f ∈ symbolWeightPiece k w N ↔
      ∀ m, f.coeff m ≠ 0 → monomialWeight w m ≤ N :=
  Iff.rfl

theorem symbolWeightPiece_mono {n : ℕ} (w : PhaseVar n → ℕ)
    {N M : ℕ} (hNM : N ≤ M) :
    symbolWeightPiece k w N ≤ symbolWeightPiece k w M := by
  intro f hf m hm
  exact (hf m hm).trans hNM

theorem symbolWeightPiece_antitone_weight {n : ℕ}
    {w₁ w₂ : PhaseVar n → ℕ} (h : ∀ i, w₁ i ≤ w₂ i) (N : ℕ) :
    symbolWeightPiece k w₂ N ≤ symbolWeightPiece k w₁ N := by
  intro f hf m hm
  exact (monomialWeight_mono h m).trans (hf m hm)

@[simp] theorem monomial_mem_symbolWeightPiece_iff {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) (m : PhaseVar n →₀ ℕ) :
    MvPolynomial.monomial m (1 : k) ∈ symbolWeightPiece k w N ↔
      monomialWeight w m ≤ N := by
  constructor
  · intro h
    apply h m
    simp [MvPolynomial.coeff_monomial]
  · intro hm q hq
    simp only [MvPolynomial.coeff_monomial] at hq
    split at hq
    · next h => simpa [h] using hm
    · contradiction

/-- The sum of the weights of all supported monomials is a simple exhaustive
bound.  It is not intended to be the minimal weighted degree. -/
def symbolSupportWeightBound {n : ℕ} (w : PhaseVar n → ℕ)
    (f : SymbolRing k n) : ℕ :=
  f.support.sum (monomialWeight w)

theorem mem_symbolWeightPiece_supportBound {n : ℕ}
    (w : PhaseVar n → ℕ) (f : SymbolRing k n) :
    f ∈ symbolWeightPiece k w (symbolSupportWeightBound k w f) := by
  intro m hm
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  exact MvPolynomial.mem_support_iff.mpr hm

/-- Pull a weighted symbol truncation back through checked Weyl normal-form
coordinates. -/
def presentedWeightPiece {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    Submodule k (PresentedWeyl k n) :=
  (symbolWeightPiece k w N).comap
    (presentedNormalFormLinearEquiv k n).toLinearMap

@[simp] theorem mem_presentedWeightPiece {n : ℕ} (w : PhaseVar n → ℕ)
    (N : ℕ) (a : PresentedWeyl k n) :
    a ∈ presentedWeightPiece k w N ↔
      ∀ m, (presentedNormalFormLinearEquiv k n a).coeff m ≠ 0 →
        monomialWeight w m ≤ N :=
  Iff.rfl

theorem presentedWeightPiece_mono {n : ℕ} (w : PhaseVar n → ℕ)
    {N M : ℕ} (hNM : N ≤ M) :
    presentedWeightPiece k w N ≤ presentedWeightPiece k w M :=
  Submodule.comap_mono (symbolWeightPiece_mono k w hNM)

theorem presentedWeightPiece_antitone_weight {n : ℕ}
    {w₁ w₂ : PhaseVar n → ℕ} (h : ∀ i, w₁ i ≤ w₂ i) (N : ℕ) :
    presentedWeightPiece k w₂ N ≤ presentedWeightPiece k w₁ N :=
  Submodule.comap_mono (symbolWeightPiece_antitone_weight k h N)

theorem presentedNormalFormLinearEquiv_basis {n : ℕ}
    (m : PhaseVar n →₀ ℕ) :
    presentedNormalFormLinearEquiv k n (presentedPBWBasis k n m) =
      MvPolynomial.monomial m 1 := by
  rw [presentedPBWBasis, presentedNormalFormBasis_apply,
    LinearEquiv.apply_symm_apply]

theorem presentedPBWBasis_mem_weightPiece_iff {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) (m : PhaseVar n →₀ ℕ) :
    presentedPBWBasis k n m ∈ presentedWeightPiece k w N ↔
      monomialWeight w m ≤ N := by
  rw [mem_presentedWeightPiece,
    presentedNormalFormLinearEquiv_basis]
  exact monomial_mem_symbolWeightPiece_iff k w N m

/-- The ordered PBW basis vectors whose weights are bounded by `N`. -/
def presentedWeightBasisSet {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    Set (PresentedWeyl k n) :=
  {a | ∃ m : PhaseVar n →₀ ℕ,
    monomialWeight w m ≤ N ∧ a = presentedPBWBasis k n m}

/-- The coefficient-support definition of a weighted truncation agrees with
the span of exactly the bounded ordered PBW basis vectors. -/
theorem presentedWeightPiece_eq_span {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    presentedWeightPiece k w N =
      Submodule.span k (presentedWeightBasisSet k w N) := by
  apply le_antisymm
  · intro a ha
    let f := presentedNormalFormLinearEquiv k n a
    have hreconstruct :
        a = ∑ m ∈ f.support,
          f.coeff m • presentedPBWBasis k n m := by
      apply (presentedNormalFormLinearEquiv k n).injective
      simp only [map_sum, map_smul,
        presentedNormalFormLinearEquiv_basis]
      change f = _
      calc
        f = ∑ m ∈ f.support,
            MvPolynomial.monomial m (f.coeff m) :=
          MvPolynomial.as_sum f
        _ = _ := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [MvPolynomial.smul_monomial]
          simp
    rw [hreconstruct]
    apply Submodule.sum_mem
    intro m hm
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨m, ha m (MvPolynomial.mem_support_iff.mp hm), rfl⟩
  · apply Submodule.span_le.mpr
    intro a ha
    obtain ⟨m, hm, rfl⟩ := ha
    exact (presentedPBWBasis_mem_weightPiece_iff k w N m).mpr hm

/-- Normal form of a bounded old basis vector followed by the newest pair. -/
theorem presentedCoefficientOrdered_basis_normal (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p (presentedPBWBasis k n m)) =
      MvPolynomial.monomial (extendPhaseExponent n a p m) 1 := by
  rw [presentedNormalFormLinearEquiv_previous_ordered,
    presentedNormalFormLinearEquiv_basis,
    MvPolynomial.rename_monomial,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
  simp [extendPhaseExponent]

/-- Appending a fixed newest-pair monomial is scalar-linear in the old
coefficient. -/
def presentedCoefficientOrderedLinear (n a p : ℕ) :
    PresentedWeyl k n →ₗ[k] PresentedWeyl k (n + 1) where
  toFun z := presentedCoefficientOrdered k n a p z
  map_add' z w := by
    simp [presentedCoefficientOrdered, map_add, add_mul]
  map_smul' c z := by
    simp [presentedCoefficientOrdered, map_smul, Algebra.smul_mul_assoc]

theorem exists_mem_presentedWeightPiece {n : ℕ} (w : PhaseVar n → ℕ)
    (a : PresentedWeyl k n) :
    ∃ N, a ∈ presentedWeightPiece k w N := by
  let f := presentedNormalFormLinearEquiv k n a
  exact ⟨symbolSupportWeightBound k w f,
    mem_symbolWeightPiece_supportBound k w f⟩

/-- Every named generator has Bernstein weight one. -/
def bernsteinWeight {n : ℕ} (_ : PhaseVar n) : ℕ := 1

/-- Coordinates have order weight zero and momenta have order weight one. -/
def orderWeight {n : ℕ} : PhaseVar n → ℕ := fibreWeight

theorem monomialWeight_extend_bernstein (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    monomialWeight (@bernsteinWeight n) m + a + p =
      monomialWeight (@bernsteinWeight (n + 1))
        (extendPhaseExponent n a p m) := by
  simp only [extendPhaseExponent, monomialWeight]
  rw [Finsupp.sum_add_index, Finsupp.sum_add_index,
    Finsupp.sum_single_index, Finsupp.sum_single_index,
    Finsupp.sum_mapDomain_index]
  · simp [bernsteinWeight, add_comm, add_left_comm, add_assoc]
  all_goals simp [bernsteinWeight, add_mul]

theorem monomialWeight_extend_order (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    monomialWeight (@orderWeight n) m + p =
      monomialWeight (@orderWeight (n + 1))
        (extendPhaseExponent n a p m) := by
  simp only [extendPhaseExponent, monomialWeight]
  rw [Finsupp.sum_add_index, Finsupp.sum_add_index,
    Finsupp.sum_single_index, Finsupp.sum_single_index,
    Finsupp.sum_mapDomain_index]
  · simp only [orderWeight, fibreWeight, Nat.mul_one, Nat.mul_zero, add_zero]
    rw [add_comm]
    congr 1
    apply Finsupp.sum_congr
    intro i hi
    cases i <;> simp [orderWeight, fibreWeight, oldIndex]
  all_goals simp [orderWeight, fibreWeight, oldIndex, add_mul]

theorem phaseExponent_succ_eq_extend (n : ℕ)
    (a p : Fin (n + 1) → ℕ) :
    phaseExponent a p =
      extendPhaseExponent n (a 0) (p 0)
        (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) :=
  phaseExponent_succ n a p

theorem monomialWeight_phaseExponent_succ_bernstein
    (n : ℕ) (a p : Fin (n + 1) → ℕ) :
    monomialWeight (@bernsteinWeight (n + 1)) (phaseExponent a p) =
      monomialWeight (@bernsteinWeight n)
          (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) +
        a 0 + p 0 := by
  rw [phaseExponent_succ_eq_extend,
    ← monomialWeight_extend_bernstein]

theorem monomialWeight_phaseExponent_succ_order
    (n : ℕ) (a p : Fin (n + 1) → ℕ) :
    monomialWeight (@orderWeight (n + 1)) (phaseExponent a p) =
      monomialWeight (@orderWeight n)
          (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) + p 0 := by
  rw [phaseExponent_succ_eq_extend,
    ← monomialWeight_extend_order]

/-- Bernstein truncation of the presented Weyl algebra. -/
def bernsteinPiece (n N : ℕ) : Submodule k (PresentedWeyl k n) :=
  presentedWeightPiece k bernsteinWeight N

/-- Differential-order truncation of the presented Weyl algebra. -/
abbrev orderPiece (n N : ℕ) : Submodule k (PresentedWeyl k n) :=
  presentedWeightPiece k (@orderWeight n) N

/-- Appending a normal-ordered newest pair increases Bernstein degree by at
most the sum of the two new exponents. -/
theorem presentedCoefficientOrdered_mem_bernsteinPiece
    (n N a p : ℕ) (z : PresentedWeyl k n)
    (hz : z ∈ bernsteinPiece k n N) :
    presentedCoefficientOrdered k n a p z ∈
      bernsteinPiece k (n + 1) (N + a + p) := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      rw [bernsteinPiece, mem_presentedWeightPiece,
        presentedCoefficientOrdered_basis_normal]
      intro q hq
      simp only [MvPolynomial.coeff_monomial] at hq
      split at hq
      · next h =>
          subst q
          rw [← monomialWeight_extend_bernstein]
          omega
      · contradiction
  | zero =>
      change presentedCoefficientOrderedLinear k n a p 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      change presentedCoefficientOrderedLinear k n a p (x + y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      change presentedCoefficientOrderedLinear k n a p (c • x) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c ih

/-- Appending a normal-ordered newest pair increases differential order by at
most the new momentum exponent; coordinate powers have order zero. -/
theorem presentedCoefficientOrdered_mem_orderPiece
    (n N a p : ℕ) (z : PresentedWeyl k n)
    (hz : z ∈ orderPiece k n N) :
    presentedCoefficientOrdered k n a p z ∈
      orderPiece k (n + 1) (N + p) := by
  rw [orderPiece, presentedWeightPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      rw [orderPiece, mem_presentedWeightPiece,
        presentedCoefficientOrdered_basis_normal]
      intro q hq
      simp only [MvPolynomial.coeff_monomial] at hq
      split at hq
      · next h =>
          subst q
          rw [← monomialWeight_extend_order]
          omega
      · contradiction
  | zero =>
      change presentedCoefficientOrderedLinear k n a p 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      change presentedCoefficientOrderedLinear k n a p (x + y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      change presentedCoefficientOrderedLinear k n a p (c • x) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c ih

/-- Products of ordered PBW monomials satisfy the Bernstein degree bound. -/
theorem presentedOrderedMonomial_mul_mem_bernsteinPiece :
    ∀ (n : ℕ) (a p c q : Fin n → ℕ),
      presentedOrderedMonomial k n a p * presentedOrderedMonomial k n c q ∈
        bernsteinPiece k n
          (monomialWeight (@bernsteinWeight n) (phaseExponent a p) +
            monomialWeight (@bernsteinWeight n) (phaseExponent c q)) := by
  intro n
  induction n with
  | zero =>
      intro a p c q
      have hap : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      have hcq : phaseExponent c q = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hap, hcq]
      simp only [monomialWeight, Finsupp.sum_zero_index, zero_add]
      simp only [presentedOrderedMonomial, one_mul]
      change (1 : PresentedWeyl k 0) ∈ bernsteinPiece k 0 0
      rw [bernsteinPiece, mem_presentedWeightPiece]
      intro m hm
      have hone :
          presentedNormalFormLinearEquiv k 0 (1 : PresentedWeyl k 0) = 1 :=
        presentedNormalFormLinearEquiv_one k 0
      rw [hone] at hm
      have hm0 : m = 0 := by
        symm
        simpa [MvPolynomial.coeff_one] using hm
      subst m
      simp [monomialWeight]
  | succ n ih =>
      intro a p c q
      change
        presentedCoefficientOrdered k n (a 0) (p 0)
              (presentedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ)) *
            presentedCoefficientOrdered k n (c 0) (q 0)
              (presentedOrderedMonomial k n
                (fun i => c i.succ) (fun i => q i.succ)) ∈ _
      rw [presentedCoefficientOrdered_mul]
      apply Submodule.sum_mem
      intro i hi
      have hib : i ≤ p 0 := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hic : i ≤ c 0
      · simp only [if_pos hic]
        apply Submodule.smul_mem
        have hterm := presentedCoefficientOrdered_mem_bernsteinPiece k
          n
          (monomialWeight (@bernsteinWeight n)
              (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) +
            monomialWeight (@bernsteinWeight n)
              (phaseExponent (fun i => c i.succ) (fun i => q i.succ)))
          (a 0 + c 0 - i) (p 0 + q 0 - i)
          (presentedOrderedMonomial k n
              (fun i => a i.succ) (fun i => p i.succ) *
            presentedOrderedMonomial k n
              (fun i => c i.succ) (fun i => q i.succ))
          (ih (fun i => a i.succ) (fun i => p i.succ)
            (fun i => c i.succ) (fun i => q i.succ))
        apply presentedWeightPiece_mono k bernsteinWeight _ hterm
        rw [monomialWeight_phaseExponent_succ_bernstein,
          monomialWeight_phaseExponent_succ_bernstein]
        omega
      · simp [hic]

/-- Products of ordered PBW monomials satisfy the differential-order bound. -/
theorem presentedOrderedMonomial_mul_mem_orderPiece :
    ∀ (n : ℕ) (a p c q : Fin n → ℕ),
      presentedOrderedMonomial k n a p * presentedOrderedMonomial k n c q ∈
        orderPiece k n
          (monomialWeight (@orderWeight n) (phaseExponent a p) +
            monomialWeight (@orderWeight n) (phaseExponent c q)) := by
  intro n
  induction n with
  | zero =>
      intro a p c q
      have hap : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      have hcq : phaseExponent c q = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hap, hcq]
      simp only [monomialWeight, Finsupp.sum_zero_index, zero_add]
      simp only [presentedOrderedMonomial, one_mul]
      change (1 : PresentedWeyl k 0) ∈ orderPiece k 0 0
      rw [orderPiece, mem_presentedWeightPiece]
      intro m hm
      have hone :
          presentedNormalFormLinearEquiv k 0 (1 : PresentedWeyl k 0) = 1 :=
        presentedNormalFormLinearEquiv_one k 0
      rw [hone] at hm
      have hm0 : m = 0 := by
        symm
        simpa [MvPolynomial.coeff_one] using hm
      subst m
      simp [monomialWeight]
  | succ n ih =>
      intro a p c q
      change
        presentedCoefficientOrdered k n (a 0) (p 0)
              (presentedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ)) *
            presentedCoefficientOrdered k n (c 0) (q 0)
              (presentedOrderedMonomial k n
                (fun i => c i.succ) (fun i => q i.succ)) ∈ _
      rw [presentedCoefficientOrdered_mul]
      apply Submodule.sum_mem
      intro i hi
      have hib : i ≤ p 0 := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hic : i ≤ c 0
      · simp only [if_pos hic]
        apply Submodule.smul_mem
        have hterm := presentedCoefficientOrdered_mem_orderPiece k
          n
          (monomialWeight (@orderWeight n)
              (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) +
            monomialWeight (@orderWeight n)
              (phaseExponent (fun i => c i.succ) (fun i => q i.succ)))
          (a 0 + c 0 - i) (p 0 + q 0 - i)
          (presentedOrderedMonomial k n
              (fun i => a i.succ) (fun i => p i.succ) *
            presentedOrderedMonomial k n
              (fun i => c i.succ) (fun i => q i.succ))
          (ih (fun i => a i.succ) (fun i => p i.succ)
            (fun i => c i.succ) (fun i => q i.succ))
        apply presentedWeightPiece_mono k orderWeight _ hterm
        rw [monomialWeight_phaseExponent_succ_order,
          monomialWeight_phaseExponent_succ_order]
        omega
      · simp [hic]

/-- The Bernstein PBW truncations are multiplicatively filtered. -/
theorem mul_mem_bernsteinPiece {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ bernsteinPiece k n N) (hy : y ∈ bernsteinPiece k n M) :
    x * y ∈ bernsteinPiece k n (N + M) := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at hx hy
  apply Submodule.span_induction₂
      (p := fun x y _ _ => x * y ∈ bernsteinPiece k n (N + M))
      (ha := hx) (hb := hy)
  · intro x y hx hy
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hy
    rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
    have hprod := presentedOrderedMonomial_mul_mem_bernsteinPiece k n
      (fun i => m (.inl i)) (fun i => m (.inr i))
      (fun i => r (.inl i)) (fun i => r (.inr i))
    rw [phaseExponent_split, phaseExponent_split] at hprod
    exact presentedWeightPiece_mono k bernsteinWeight
      (Nat.add_le_add hm hr) hprod
  · intro y hy
    rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x hx
    rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x y z hx hy hz hxy hyz
    rw [add_mul]
    exact Submodule.add_mem _ hxy hyz
  · intro x y z hx hy hz hxy hxz
    rw [mul_add]
    exact Submodule.add_mem _ hxy hxz
  · intro c x y hx hy hxy
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem _ c hxy
  · intro c x y hx hy hxy
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hxy

/-- The differential-order PBW truncations are multiplicatively filtered. -/
theorem mul_mem_orderPiece {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ orderPiece k n N) (hy : y ∈ orderPiece k n M) :
    x * y ∈ orderPiece k n (N + M) := by
  rw [orderPiece, presentedWeightPiece_eq_span] at hx hy
  apply Submodule.span_induction₂
      (p := fun x y _ _ => x * y ∈ orderPiece k n (N + M))
      (ha := hx) (hb := hy)
  · intro x y hx hy
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hy
    rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
    have hprod := presentedOrderedMonomial_mul_mem_orderPiece k n
      (fun i => m (.inl i)) (fun i => m (.inr i))
      (fun i => r (.inl i)) (fun i => r (.inr i))
    rw [phaseExponent_split, phaseExponent_split] at hprod
    exact presentedWeightPiece_mono k orderWeight
      (Nat.add_le_add hm hr) hprod
  · intro y hy
    rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x hx
    rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x y z hx hy hz hxy hyz
    rw [add_mul]
    exact Submodule.add_mem _ hxy hyz
  · intro x y z hx hy hz hxy hxz
    rw [mul_add]
    exact Submodule.add_mem _ hxy hxz
  · intro c x y hx hy hxy
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem _ c hxy
  · intro c x y hx hy hxy
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hxy

-- Compile-time API contracts: the filtration bounds are exactly additive.
example {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ bernsteinPiece k n N) (hy : y ∈ bernsteinPiece k n M) :
    x * y ∈ bernsteinPiece k n (N + M) :=
  mul_mem_bernsteinPiece k hx hy

example {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ orderPiece k n N) (hy : y ∈ orderPiece k n M) :
    x * y ∈ orderPiece k n (N + M) :=
  mul_mem_orderPiece k hx hy

theorem bernsteinPiece_le_orderPiece (n N : ℕ) :
    bernsteinPiece k n N ≤ orderPiece k n N := by
  apply presentedWeightPiece_antitone_weight k
  intro i
  cases i <;> simp [orderWeight, fibreWeight, bernsteinWeight]

theorem exists_mem_bernsteinPiece {n : ℕ} (a : PresentedWeyl k n) :
    ∃ N, a ∈ bernsteinPiece k n N :=
  exists_mem_presentedWeightPiece k bernsteinWeight a

theorem exists_mem_orderPiece {n : ℕ} (a : PresentedWeyl k n) :
    ∃ N, a ∈ orderPiece k n N :=
  exists_mem_presentedWeightPiece k orderWeight a


end

end Stafford38.WeylFiltration
