/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.AssociatedGraded


/-!
# Filtered commutators and subprincipal symbols

This file develops the two-element commutator calculus for the differential-
order filtration.  The first theorem is the exact filtration drop for arbitrary
filtered elements; it includes the degree-zero case rather than hiding natural-
number truncation behind a positivity hypothesis.
-/

@[expose] public section

namespace Stafford38.WeylFilteredCommutator

open Stafford38.Characteristic
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Commutators lower differential order by one.  With natural-number
filtration indices, the `r = s = 0` case says that two order-zero operators
commute and hence their commutator belongs to `F₀`. -/
theorem commutator_mem_orderPiece_pred
    {n r s : ℕ} {a b : PresentedWeyl k n}
    (ha : a ∈ orderPiece k n r) (hb : b ∈ orderPiece k n s) :
    Stafford.commutator a b ∈ orderPiece k n (r + s - 1) := by
  have hab : a * b ∈ orderPiece k n (r + s) :=
    mul_mem_orderPiece k ha hb
  have hba : b * a ∈ orderPiece k n (s + r) :=
    mul_mem_orderPiece k hb ha
  have hba' : b * a ∈ orderPiece k n (r + s) := by
    simpa [Nat.add_comm] using hba
  have hcomm : Stafford.commutator a b ∈ orderPiece k n (r + s) := by
    exact Submodule.sub_mem _ hab hba'
  have hmulba :
      presentedPrincipalComponent k (@orderWeight n) (r + s) (b * a) =
        presentedPrincipalComponent k (@orderWeight n) s b *
          presentedPrincipalComponent k (@orderWeight n) r a := by
    simpa [Nat.add_comm] using
      (presentedPrincipalComponent_mul_order k hb ha)
  have htop :
      presentedPrincipalComponent k (@orderWeight n) (r + s)
          (Stafford.commutator a b) = 0 := by
    change presentedPrincipalComponent k (@orderWeight n) (r + s)
        (a * b - b * a) = 0
    rw [map_sub,
      presentedPrincipalComponent_mul_order k ha hb,
      hmulba]
    exact sub_eq_zero.mpr (mul_comm _ _)
  have hlower :=
    (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
      k (@orderWeight n) _ hcomm).mp htop
  cases hsum : r + s with
  | zero =>
      have hr : r = 0 := by omega
      have hs : s = 0 := by omega
      subst r
      subst s
      simpa using hcomm
  | succ t =>
      change a * b - b * a ∈ presentedWeightPiece k orderWeight t
      simpa [presentedStrictLowerPiece, hsum] using hlower

/-- Differential operators of order zero are multiplication operators and
therefore commute. -/
theorem commutator_eq_zero_of_mem_orderPiece_zero
    {n : ℕ} {a b : PresentedWeyl k n}
    (ha : a ∈ orderPiece k n 0) (hb : b ∈ orderPiece k n 0) :
    Stafford.commutator a b = 0 := by
  have hab : a * b ∈ orderPiece k n 0 := by
    simpa using (mul_mem_orderPiece k ha hb)
  have hba : b * a ∈ orderPiece k n 0 := by
    simpa using (mul_mem_orderPiece k hb ha)
  have hcomm : Stafford.commutator a b ∈ orderPiece k n 0 :=
    Submodule.sub_mem _ hab hba
  have htop :
      presentedPrincipalComponent k (@orderWeight n) 0
          (Stafford.commutator a b) = 0 := by
    change presentedPrincipalComponent k (@orderWeight n) 0
        (a * b - b * a) = 0
    rw [map_sub,
      presentedPrincipalComponent_mul_order k ha hb,
      presentedPrincipalComponent_mul_order k hb ha]
    exact sub_eq_zero.mpr (mul_comm _ _)
  have hlower := (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
    k (@orderWeight n) _ hcomm).mp htop
  simpa [presentedStrictLowerPiece] using hlower

@[simp]
theorem poissonBracket_zero_left {n : ℕ}
    (f : SymbolRing k n) : poissonBracket 0 f = 0 := by
  simp [poissonBracket]

@[simp]
theorem poissonBracket_zero_right {n : ℕ}
    (f : SymbolRing k n) : poissonBracket f 0 = 0 := by
  simp [poissonBracket]

theorem poissonBracket_add_left {n : ℕ}
    (f g h : SymbolRing k n) :
    poissonBracket (f + g) h = poissonBracket f h + poissonBracket g h := by
  simp only [poissonBracket, map_add, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem poissonBracket_add_right {n : ℕ}
    (f g h : SymbolRing k n) :
    poissonBracket f (g + h) = poissonBracket f g + poissonBracket f h := by
  simp only [poissonBracket, map_add, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem poissonBracket_smul_left {n : ℕ}
    (c : k) (f g : SymbolRing k n) :
    poissonBracket (c • f) g = c • poissonBracket f g := by
  simp only [poissonBracket, Algebra.smul_def, MvPolynomial.pderiv_mul,
    MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C, zero_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem poissonBracket_smul_right {n : ℕ}
    (c : k) (f g : SymbolRing k n) :
    poissonBracket f (c • g) = c • poissonBracket f g := by
  simp only [poissonBracket, Algebra.smul_def, MvPolynomial.pderiv_mul,
    MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C, zero_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The one-contraction part of normal-ordered multiplication.  It
differentiates the left monomial in momentum and the right monomial in the
matching coordinate. -/
def pbwFirstContraction {n : ℕ}
    (m q : PhaseVar n →₀ ℕ) : SymbolRing k n :=
  ∑ i : Fin n,
    MvPolynomial.pderiv (.inr i) (MvPolynomial.monomial m 1) *
      MvPolynomial.pderiv (.inl i) (MvPolynomial.monomial q 1)

/-- Antisymmetrizing the first normal-ordering contraction is exactly the
negative Poisson bracket for the convention `[x,p] = -1`. -/
theorem pbwFirstContraction_sub_swap_eq_neg_poisson {n : ℕ}
    (m q : PhaseVar n →₀ ℕ) :
    pbwFirstContraction k m q - pbwFirstContraction k q m =
      -poissonBracket (MvPolynomial.monomial m 1)
        (MvPolynomial.monomial q 1) := by
  rw [pbwFirstContraction, pbwFirstContraction, poissonBracket,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem momentumExponent_eq_zero_of_orderWeight_eq_zero {n : ℕ}
    (m : PhaseVar n →₀ ℕ)
    (hm : monomialWeight (@orderWeight n) m = 0) (i : Fin n) :
    m (.inr i) = 0 := by
  by_contra hne
  have himem : (.inr i : PhaseVar n) ∈ m.support :=
    Finsupp.mem_support_iff.mpr hne
  have hle :
      m (.inr i) * orderWeight (.inr i) ≤
        ∑ j ∈ m.support, m j * orderWeight j :=
    Finset.single_le_sum
      (f := fun j => m j * orderWeight j)
      (fun j _ => Nat.zero_le _) himem
  have hle' : m (.inr i) ≤ monomialWeight (@orderWeight n) m := by
    simpa [monomialWeight, Finsupp.sum, orderWeight, fibreWeight] using hle
  omega

theorem pbwFirstContraction_eq_zero_of_orderWeight_eq_zero {n : ℕ}
    (m q : PhaseVar n →₀ ℕ)
    (hm : monomialWeight (@orderWeight n) m = 0) :
    pbwFirstContraction k m q = 0 := by
  rw [pbwFirstContraction]
  apply Finset.sum_eq_zero
  intro i hi
  rw [MvPolynomial.pderiv_monomial,
    momentumExponent_eq_zero_of_orderWeight_eq_zero m hm i]
  simp

/-- A one-sided first-contraction formula for PBW products implies the exact
PBW commutator formula.  Unlike a commutator restatement, the premise is the
specific local normal-ordering coefficient that the recursive PBW product API
must expose. -/
theorem pbw_commutator_formula_of_firstContraction
    {n : ℕ}
    (hProduct : ∀ m q : PhaseVar n →₀ ℕ,
      0 < monomialWeight (@orderWeight n) m +
          monomialWeight (@orderWeight n) q →
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) m +
            monomialWeight (@orderWeight n) q - 1)
          (presentedPBWBasis k n m * presentedPBWBasis k n q) =
        pbwFirstContraction k m q) :
    ∀ m q : PhaseVar n →₀ ℕ,
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) m +
            monomialWeight (@orderWeight n) q - 1)
          (Stafford.commutator
            (presentedPBWBasis k n m) (presentedPBWBasis k n q)) =
        -poissonBracket (MvPolynomial.monomial m 1)
          (MvPolynomial.monomial q 1) := by
  intro m q
  let R := monomialWeight (@orderWeight n) m
  let S := monomialWeight (@orderWeight n) q
  by_cases hpos : 0 < R + S
  · change presentedPrincipalComponent k (@orderWeight n) (R + S - 1)
      (presentedPBWBasis k n m * presentedPBWBasis k n q -
        presentedPBWBasis k n q * presentedPBWBasis k n m) = _
    rw [map_sub, hProduct m q hpos]
    have hpos' : 0 < S + R := by omega
    rw [show R + S - 1 = S + R - 1 by omega, hProduct q m hpos']
    exact pbwFirstContraction_sub_swap_eq_neg_poisson k m q
  · have hzero : R + S = 0 := by omega
    have hR : R = 0 := by omega
    have hS : S = 0 := by omega
    have hmPiece : presentedPBWBasis k n m ∈ orderPiece k n 0 := by
      exact (presentedPBWBasis_mem_weightPiece_iff k orderWeight 0 m).mpr
        (by simpa [R] using hR.le)
    have hqPiece : presentedPBWBasis k n q ∈ orderPiece k n 0 := by
      exact (presentedPBWBasis_mem_weightPiece_iff k orderWeight 0 q).mpr
        (by simpa [S] using hS.le)
    rw [commutator_eq_zero_of_mem_orderPiece_zero k hmPiece hqPiece, map_zero]
    rw [← pbwFirstContraction_sub_swap_eq_neg_poisson k m q,
      pbwFirstContraction_eq_zero_of_orderWeight_eq_zero k m q hR,
      pbwFirstContraction_eq_zero_of_orderWeight_eq_zero k q m hS,
      sub_zero]

/-- Bilinear PBW extension principle for the subprincipal commutator formula.
The hypothesis concerns every pair of actual PBW basis vectors at their exact
orders.  The conclusion handles arbitrary finite PBW sums at arbitrary declared
filtration bounds, including vanishing leading components. -/
theorem principalComponent_commutator_eq_neg_poisson_of_PBW
    {n r s : ℕ} {a b : PresentedWeyl k n}
    (hPBW : ∀ m q : PhaseVar n →₀ ℕ,
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) m +
            monomialWeight (@orderWeight n) q - 1)
          (Stafford.commutator
            (presentedPBWBasis k n m) (presentedPBWBasis k n q)) =
        -poissonBracket (MvPolynomial.monomial m 1)
          (MvPolynomial.monomial q 1))
    (ha : a ∈ orderPiece k n r) (hb : b ∈ orderPiece k n s) :
    presentedPrincipalComponent k (@orderWeight n) (r + s - 1)
        (Stafford.commutator a b) =
      -poissonBracket
        (presentedPrincipalComponent k (@orderWeight n) r a)
        (presentedPrincipalComponent k (@orderWeight n) s b) := by
  rw [orderPiece, presentedWeightPiece_eq_span] at ha hb
  apply Submodule.span_induction₂
      (p := fun a b _ _ =>
        presentedPrincipalComponent k (@orderWeight n) (r + s - 1)
            (Stafford.commutator a b) =
          -poissonBracket
            (presentedPrincipalComponent k (@orderWeight n) r a)
            (presentedPrincipalComponent k (@orderWeight n) s b))
      (ha := ha) (hb := hb)
  · intro x y hx hy
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    let R := monomialWeight (@orderWeight n) m
    let S := monomialWeight (@orderWeight n) q
    have hmPiece : presentedPBWBasis k n m ∈ orderPiece k n R := by
      exact (presentedPBWBasis_mem_weightPiece_iff k orderWeight R m).mpr le_rfl
    have hqPiece : presentedPBWBasis k n q ∈ orderPiece k n S := by
      exact (presentedPBWBasis_mem_weightPiece_iff k orderWeight S q).mpr le_rfl
    by_cases hR : R = r
    · by_cases hS : S = s
      · subst r
        subst s
        rw [presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp only [R, S]
        exact hPBW m q
      · have hSlt : S < s := lt_of_le_of_ne hq hS
        rw [presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp only [R, S, hR, ite_eq_left, hS, ite_false,
          poissonBracket_zero_right, neg_zero]
        by_cases hzero : R + S = 0
        · have hR0 : R = 0 := by omega
          have hS0 : S = 0 := by omega
          rw [commutator_eq_zero_of_mem_orderPiece_zero k
            (by simpa [hR0] using hmPiece) (by simpa [hS0] using hqPiece),
            map_zero]
        · have hmem := commutator_mem_orderPiece_pred k hmPiece hqPiece
          apply presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            (@orderWeight n) _ hmem
          omega
    · have hRlt : R < r := lt_of_le_of_ne hm hR
      rw [presentedPrincipalComponent_basis,
        presentedPrincipalComponent_basis]
      simp only [R,  hR, ite_false, poissonBracket_zero_left, neg_zero]
      by_cases hzero : R + S = 0
      · have hR0 : R = 0 := by omega
        have hS0 : S = 0 := by omega
        rw [commutator_eq_zero_of_mem_orderPiece_zero k
          (by simpa [hR0] using hmPiece) (by simpa [hS0] using hqPiece),
          map_zero]
      · have hmem := commutator_mem_orderPiece_pred k hmPiece hqPiece
        apply presentedPrincipalComponent_eq_zero_of_mem_of_lt k
          (@orderWeight n) _ hmem
        omega
  · intro y hy
    simp [Stafford.commutator]
  · intro x hx
    simp [Stafford.commutator]
  · intro x y z hx hy hz hxy hyz
    rw [show Stafford.commutator (x + y) z =
        Stafford.commutator x z + Stafford.commutator y z by
      change (x + y) * z - z * (x + y) =
        (x * z - z * x) + (y * z - z * y)
      noncomm_ring,
      map_add, hxy, hyz, map_add, poissonBracket_add_left]
    abel
  · intro x y z hx hy hz hxy hxz
    rw [show Stafford.commutator x (y + z) =
        Stafford.commutator x y + Stafford.commutator x z by
      change x * (y + z) - (y + z) * x =
        (x * y - y * x) + (x * z - z * x)
      noncomm_ring,
      map_add, hxy, hxz, map_add, poissonBracket_add_right]
    abel
  · intro c x y hx hy hxy
    rw [show Stafford.commutator (c • x) y =
        c • Stafford.commutator x y by
      change (c • x) * y - y * (c • x) = c • (x * y - y * x)
      simp only [Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_sub],
      map_smul, hxy, map_smul, poissonBracket_smul_left, smul_neg]
  · intro c x y hx hy hxy
    rw [show Stafford.commutator x (c • y) =
        c • Stafford.commutator x y by
      change x * (c • y) - (c • y) * x = c • (x * y - y * x)
      simp only [Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, smul_sub],
      map_smul, hxy, map_smul, poissonBracket_smul_right, smul_neg]

/-- Full arbitrary-sum consequence of the one-sided PBW first-contraction
formula.  This packages both nontrivial bridges: antisymmetrization produces
the sign-correct Poisson bracket, and PBW bilinearity handles arbitrary
declared filtration bounds. -/
theorem principalComponent_commutator_eq_neg_poisson_of_firstContraction
    {n r s : ℕ} {a b : PresentedWeyl k n}
    (hProduct : ∀ m q : PhaseVar n →₀ ℕ,
      0 < monomialWeight (@orderWeight n) m +
          monomialWeight (@orderWeight n) q →
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) m +
            monomialWeight (@orderWeight n) q - 1)
          (presentedPBWBasis k n m * presentedPBWBasis k n q) =
        pbwFirstContraction k m q)
    (ha : a ∈ orderPiece k n r) (hb : b ∈ orderPiece k n s) :
    presentedPrincipalComponent k (@orderWeight n) (r + s - 1)
        (Stafford.commutator a b) =
      -poissonBracket
        (presentedPrincipalComponent k (@orderWeight n) r a)
        (presentedPrincipalComponent k (@orderWeight n) s b) :=
  principalComponent_commutator_eq_neg_poisson_of_PBW k
    (pbw_commutator_formula_of_firstContraction k hProduct) ha hb


end

end Stafford38.WeylFilteredCommutator
