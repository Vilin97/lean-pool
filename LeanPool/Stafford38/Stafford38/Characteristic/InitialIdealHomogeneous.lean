/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientGraded


/-!
# Homogeneous pieces of the order initial ideal

The generators of `orderInitialIdeal` are weighted homogeneous and are exact
symbol relations.  This file proves that taking the degree-`N` homogeneous
component of any element of their ideal span again gives an exact degree-`N`
relation.  The proof uses the finite direct-sum decomposition of each
polynomial multiplier and the homogeneous relation closure proved in
`FilteredQuotientGraded`.
-/

@[expose] public section

namespace Stafford38.CharacteristicInitialIdealHomogeneous

open Stafford38.Characteristic
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylLeadingSymbol

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The submodule of symbols homogeneous of the given momentum order. -/
abbrev OrderHomogeneous (N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N

/-- The decomposition of the symbol ring by homogeneous momentum order. -/
abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The grading of the symbol algebra by momentum order. -/
local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- Only finitely many order-homogeneous components of a symbol are nonzero. -/
theorem orderHomogeneousComponent_support_finite (P : SymbolRing k n) :
    (Function.support fun N =>
      MvPolynomial.weightedHomogeneousComponent (@orderWeight n) N P).Finite :=
  MvPolynomial.weightedHomogeneousComponent_finsupp P

/-- Reconstruction from the finite family of order-homogeneous components. -/
theorem finsum_orderHomogeneousComponent (P : SymbolRing k n) :
    (∑ᶠ N, MvPolynomial.weightedHomogeneousComponent
      (@orderWeight n) N P) = P :=
  MvPolynomial.sum_weightedHomogeneousComponent (@orderWeight n) P

/-- Multiplying a symbol whose every homogeneous component is an exact
relation preserves that property. -/
private theorem decompose_mul_mem_orderSymbolRelation
    (I : RightIdeal (PresentedWeyl k n)) (a x : SymbolRing k n)
    (hx : ∀ M, DirectSum.decompose (orderDecomposition (n := n) k) x M ∈
      orderSymbolRelation k I M) (N : ℕ) :
    DirectSum.decompose (orderDecomposition (n := n) k) (a * x) N ∈
      orderSymbolRelation k I N := by
  classical
  let : ∀ (M : ℕ) (Q : OrderHomogeneous (n := n) k M),
      Decidable (Q ≠ 0) :=
    fun _ Q => Classical.propDecidable (Q ≠ 0)
  have hxsum :
      (∑ M ∈ (DirectSum.decompose
          (orderDecomposition (n := n) k) x).support,
        (DirectSum.decompose (orderDecomposition (n := n) k) x M :
          SymbolRing k n)) = x :=
    DirectSum.sum_support_decompose (orderDecomposition (n := n) k) x
  rw [← hxsum, Finset.mul_sum,
    DirectSum.decompose_sum]
  rw [DFinsupp.finsetSum_apply]
  apply Submodule.sum_mem
  intro M hM
  by_cases hMN : M ≤ N
  · have hmul := homogeneousRightMul_mem_orderSymbolRelation k I
      (DirectSum.decompose (orderDecomposition k) a (N - M))
      (DirectSum.decompose (orderDecomposition (n := n) k) x M) (hx M)
    have hsum : M + (N - M) = N := Nat.add_sub_of_le hMN
    rw [← hsum]
    have hMN' : M ≤ M + (N - M) := Nat.le_add_right M (N - M)
    have heq :
        DirectSum.decompose (orderDecomposition (n := n) k)
            (a * (DirectSum.decompose (orderDecomposition (n := n) k) x M :
              SymbolRing k n)) (M + (N - M)) =
          homogeneousRightMul k
            (DirectSum.decompose (orderDecomposition (n := n) k) a (N - M))
            (DirectSum.decompose (orderDecomposition (n := n) k) x M) := by
      apply Subtype.ext
      rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
        (orderDecomposition k)
        (DirectSum.decompose (orderDecomposition (n := n) k) x M).property hMN']
      simp only [coe_homogeneousRightMul]
      rw [Nat.add_sub_cancel_left]
      exact mul_comm
        (DirectSum.decompose (orderDecomposition (n := n) k) a (N - M) :
          SymbolRing k n)
        (DirectSum.decompose (orderDecomposition (n := n) k) x M :
          SymbolRing k n)
    rw [heq]
    exact hmul
  · have heq :
        DirectSum.decompose (orderDecomposition (n := n) k)
            (a * (DirectSum.decompose (orderDecomposition (n := n) k) x M :
              SymbolRing k n)) N = 0 := by
      apply Subtype.ext
      exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le
        (orderDecomposition k)
        (DirectSum.decompose (orderDecomposition (n := n) k) x M).property hMN
    rw [heq]
    exact Submodule.zero_mem _

/-- Every homogeneous component of the ideal generated by order-principal
symbols is an exact symbol relation in that degree. -/
private theorem all_decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n)
    (hP : P ∈ orderInitialIdeal k I) :
    ∀ N, DirectSum.decompose (orderDecomposition (n := n) k) P N ∈
      orderSymbolRelation k I N := by
  classical
  change P ∈ Ideal.span (orderInitialGeneratorSet k I) at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
      intro N
      obtain ⟨M, z, hzM, hzI, rfl⟩ := hP
      let Q : OrderHomogeneous k M :=
        principalComponentOnPiece k (@orderWeight n) M ⟨z, hzM⟩
      have hQ : Q ∈ orderSymbolRelation k I M :=
        principalComponent_mem_orderSymbolRelation k I M z hzM hzI
      by_cases hNM : N = M
      · subst N
        change DirectSum.decompose (orderDecomposition (n := n) k)
          (Q : SymbolRing k n) M ∈ orderSymbolRelation k I M
        simpa only [DirectSum.decompose_coe, DirectSum.of_eq_same] using hQ
      · have hzero :
            (DirectSum.decompose (orderDecomposition k)
              (presentedPrincipalComponent k orderWeight M z) N :
                SymbolRing k n) = 0 := by
          change DirectSum.decompose (orderDecomposition k)
            (Q : SymbolRing k n) N = (0 : SymbolRing k n)
          exact DirectSum.decompose_of_mem_ne (orderDecomposition k) Q.property
            (fun h => hNM h.symm)
        have hzero' : DirectSum.decompose (orderDecomposition k)
            (presentedPrincipalComponent k orderWeight M z) N = 0 :=
          Subtype.ext hzero
        rw [hzero']
        exact Submodule.zero_mem _
  | zero =>
      intro N
      rw [DirectSum.decompose_zero]
      exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
      intro N
      simpa only [DirectSum.decompose_add, DirectSum.add_apply] using
        (Submodule.add_mem (orderSymbolRelation k I N) (hP N) (hQ N))
  | smul a P _ hP =>
      intro N
      change DirectSum.decompose (orderDecomposition k) (a * P) N ∈
        orderSymbolRelation k I N
      exact decompose_mul_mem_orderSymbolRelation k I a P hP N

/-- Every homogeneous component of the ideal generated by order-principal
symbols is an exact symbol relation in that degree. -/
theorem decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n)
    (hP : P ∈ orderInitialIdeal k I) (N : ℕ) :
    DirectSum.decompose (orderDecomposition (n := n) k) P N ∈
      orderSymbolRelation k I N :=
  all_decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal k I P hP N

/-- Reverse homogeneous-piece inclusion: a degree-`N` homogeneous element of
the order initial ideal is an exact relation in degree `N`. -/
theorem mem_orderSymbolRelation_of_coe_mem_orderInitialIdeal
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (P : OrderHomogeneous k N)
    (hP : (P : SymbolRing k n) ∈ orderInitialIdeal k I) :
    P ∈ orderSymbolRelation k I N := by
  have hcomponent :=
    decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal k I P hP N
  simpa [DirectSum.decompose_coe] using hcomponent

/-- Exact homogeneous relations are precisely the homogeneous pieces of the
order initial ideal. -/
theorem mem_orderSymbolRelation_iff_coe_mem_orderInitialIdeal
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (P : OrderHomogeneous k N) :
    P ∈ orderSymbolRelation k I N ↔
      (P : SymbolRing k n) ∈ orderInitialIdeal k I :=
  ⟨coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k I N P,
    mem_orderSymbolRelation_of_coe_mem_orderInitialIdeal k I N P⟩


end

end Stafford38.CharacteristicInitialIdealHomogeneous
