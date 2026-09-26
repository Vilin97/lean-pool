/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalUnitCoordinatePreimage


/-!
# A strict unit preimage from degree-zero initial-ideal generation

If the canonical order initial ideal and the distinguished coordinate symbol
generate the unit ideal, the degree-zero homogeneous part of that identity is
an exact order-symbol relation.  An exact filtered representative of that
relation differs from `y * x - 1` by the strict lower order piece in degree
zero, which is zero.  This produces the literal order-zero coordinate
predecessor required by `StrictUnitCoordinatePreimage`.

No noncharacteristic or characteristic-variety theorem is used here.
-/

@[expose] public section

namespace Stafford38.CanonicalUnitPreimageFromInitialTop

open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.CanonicalUnitCoordinatePreimage
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylEulerResidue

noncomputable section


universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

/-- The canonical right ideal defining the distinguished coordinate quotient. -/
abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

private abbrev OrderHomogeneous (n N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N

private abbrev orderDecomposition (n : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The weighted graded-algebra structure on the order-symbol decomposition. -/
private local instance orderGradedAlgebraInstance (n : ℕ) :
    GradedAlgebra (orderDecomposition k n) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

private theorem unit_relation_of_sup_span_eq_top
    {R : Type*} [CommRing R] (I : Ideal R) (X : R)
    (htop : I ⊔ Ideal.span {X} = ⊤) : ∃ a : R, a * X - 1 ∈ I := by
  have hone : (1 : R) ∈ I ⊔ Ideal.span {X} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp hone
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨a, ?_⟩
  have hrelation : a * X - 1 = -j := by rw [← hjs, ha]; ring
  rw [hrelation]
  exact I.neg_mem hj

omit [Algebra ℚ k] in
/-- The converse needed by the terminal cancellation route: unit generation
in the order initial ideal yields an actual order-zero coordinate predecessor
of the unit in the canonical right quotient. -/
theorem strictUnitCoordinatePreimage_of_orderInitialIdeal_sup_coordinate_eq_top
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (htop :
      orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
        Ideal.span {MvPolynomial.X (.inl (0 : Fin (n + 1)))} = ⊤) :
    StrictUnitCoordinatePreimage k n N d := by
  classical
  let I := CanonicalIdeal k n N d
  let x := presentedCoordinate k n
  let X : OrderHomogeneous k (n + 1) 0 :=
    principalComponentOnPiece k (@orderWeight (n + 1)) 0
      ⟨x, presentedCoordinate_mem_orderPiece_zero k n⟩
  have hX : (X : SymbolRing k (n + 1)) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) := by
    exact coe_coordinate_order_symbol k n
  obtain ⟨a, hrelationInitial⟩ := unit_relation_of_sup_span_eq_top
    (orderInitialIdeal k I) (X : SymbolRing k (n + 1)) (by simpa only [hX] using htop)
  let s := a * (X : SymbolRing k (n + 1))
  have hsEq : s = a * (X : SymbolRing k (n + 1)) := rfl
  let A₀ : OrderHomogeneous k (n + 1) 0 :=
    DirectSum.decompose (orderDecomposition k (n + 1)) a 0
  let oneH : OrderHomogeneous k (n + 1) 0 :=
    ⟨1, MvPolynomial.isWeightedHomogeneous_one k orderWeight⟩
  have hprod :
      (A₀ : SymbolRing k (n + 1)) * (X : SymbolRing k (n + 1)) ∈
        MvPolynomial.weightedHomogeneousSubmodule k
          (@orderWeight (n + 1)) 0 := by
    simpa using A₀.property.mul X.property
  have hdiffHom :
      (A₀ : SymbolRing k (n + 1)) * (X : SymbolRing k (n + 1)) - 1 ∈
        MvPolynomial.weightedHomogeneousSubmodule k
          (@orderWeight (n + 1)) 0 :=
    (MvPolynomial.weightedHomogeneousSubmodule k
      (@orderWeight (n + 1)) 0).sub_mem hprod oneH.property
  have hcomponent :
      DirectSum.decompose (orderDecomposition k (n + 1)) (s - 1) 0 =
        ⟨(A₀ : SymbolRing k (n + 1)) * (X : SymbolRing k (n + 1)) - 1,
          hdiffHom⟩ := by
    apply Subtype.ext
    rw [DirectSum.decompose_sub, hsEq]
    have hmul := DirectSum.coe_decompose_mul_of_right_mem_of_le
      (orderDecomposition k (n + 1)) X.property (Nat.zero_le 0)
      (a := a) (n := 0)
    change ((DirectSum.decompose (orderDecomposition k (n + 1))
        (a * (X : SymbolRing k (n + 1))) 0 :
          OrderHomogeneous k (n + 1) 0) : SymbolRing k (n + 1)) -
        ((DirectSum.decompose (orderDecomposition k (n + 1))
          (1 : SymbolRing k (n + 1)) 0 :
            OrderHomogeneous k (n + 1) 0) : SymbolRing k (n + 1)) = _
    rw [hmul]
    have honeDecomp :
        DirectSum.decompose (orderDecomposition k (n + 1))
            (1 : SymbolRing k (n + 1)) 0 = oneH := by
      change DirectSum.decompose (orderDecomposition k (n + 1))
          (oneH : SymbolRing k (n + 1)) 0 = oneH
      simp only [DirectSum.decompose_coe, DirectSum.of_eq_same]
    rw [honeDecomp]
  have hcomponentRelation :
      DirectSum.decompose (orderDecomposition k (n + 1)) (s - 1) 0 ∈
        orderSymbolRelation k I 0 :=
    decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
      k I (s - 1) hrelationInitial 0
  rw [hcomponent] at hcomponentRelation
  obtain ⟨yPiece, hySymbol⟩ :=
    principalComponentOnPiece_surjective k (@orderWeight (n + 1)) A₀
  let y : PresentedWeyl k (n + 1) := yPiece
  have hy : y ∈ orderPiece k (n + 1) 0 := yPiece.property
  have hx : x ∈ orderPiece k (n + 1) 0 :=
    presentedCoordinate_mem_orderPiece_zero k n
  have hyxOne : y * x - 1 ∈ orderPiece k (n + 1) 0 :=
    (orderPiece k (n + 1) 0).sub_mem
      (mul_mem_orderPiece k hy hx)
      (orderPieceOne (n := n + 1) k).property
  let relationH : OrderHomogeneous k (n + 1) 0 :=
    ⟨(A₀ : SymbolRing k (n + 1)) * (X : SymbolRing k (n + 1)) - 1,
      hdiffHom⟩
  have hrelationH : relationH ∈ orderSymbolRelation k I 0 := by
    exact hcomponentRelation
  obtain ⟨z, hz, hzI, hzSymbol⟩ :=
    (mem_orderSymbolRelation_iff k I 0 relationH).mp hrelationH
  have hpcEq :
      principalComponentOnPiece k (@orderWeight (n + 1)) 0
          ⟨y * x - 1, hyxOne⟩ =
        principalComponentOnPiece k (@orderWeight (n + 1)) 0 ⟨z, hz⟩ := by
    rw [← hzSymbol]
    apply Subtype.ext
    change presentedPrincipalComponent k orderWeight 0 (y * x - 1) =
      (relationH : SymbolRing k (n + 1))
    rw [map_sub, presentedPrincipalComponent_mul_order k hy hx]
    have honePC : presentedPrincipalComponent k orderWeight 0
        (1 : PresentedWeyl k (n + 1)) = 1 := by
      change presentedPrincipalComponent k orderWeight 0
          ((orderPieceOne (n := n + 1) k : orderPiece k (n + 1) 0) :
            PresentedWeyl k (n + 1)) = 1
      exact presentedPrincipalComponent_orderPieceOne (n := n + 1) k
    rw [honePC]
    change presentedPrincipalComponent k orderWeight 0 y *
        presentedPrincipalComponent k orderWeight 0 x - 1 = _
    rw [show presentedPrincipalComponent k orderWeight 0 y =
        (A₀ : SymbolRing k (n + 1)) by
      exact congrArg Subtype.val hySymbol]
    change (A₀ : SymbolRing k (n + 1)) *
        presentedPrincipalComponent k orderWeight 0 x - 1 = _
    rw [show presentedPrincipalComponent k orderWeight 0 x =
        (X : SymbolRing k (n + 1)) by rfl]
  have heq : y * x - 1 = z := by
    have hdiffPiece : y * x - 1 - z ∈ orderPiece k (n + 1) 0 :=
      (orderPiece k (n + 1) 0).sub_mem hyxOne hz
    have hzero : presentedPrincipalComponent k orderWeight 0
        (y * x - 1 - z) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg
        (fun q : OrderHomogeneous k (n + 1) 0 =>
          (q : SymbolRing k (n + 1))) hpcEq)
    have hlower := (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
      k (@orderWeight (n + 1)) (y * x - 1 - z) hdiffPiece).mp hzero
    change y * x - 1 - z ∈ (⊥ : Submodule k (PresentedWeyl k (n + 1))) at hlower
    rw [Submodule.mem_bot] at hlower
    exact sub_eq_zero.mp hlower
  refine ⟨y, hy, ?_⟩
  apply (Submodule.Quotient.eq I).2
  change y * x - 1 ∈ I
  rw [heq]
  exact hzI


end

end Stafford38.CanonicalUnitPreimageFromInitialTop
