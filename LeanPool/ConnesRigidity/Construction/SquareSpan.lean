/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete coefficient proof for the Zhou square-span boundary. Paper: §2.
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Polynomial.Basis
import LeanPool.ConnesRigidity.Construction.PaperActions

/-!
The square span component of the Connes rigidity formalization.
-/

namespace Connes
namespace Construction
namespace PaperKernel

noncomputable section

/-- Ordered basis indices for the polynomial module. Paper: §2. -/
abbrev OrderedBasisIndex := Lex (Fin 3 × Nat)

/-- Ordered basis indices for the tensor square. Paper: §2. -/
abbrev OrderedTensorIndex := Lex (OrderedBasisIndex × OrderedBasisIndex)

/-- The ordered monomial basis of the polynomial module. Paper: §2. -/
noncomputable def orderedBasis : Module.Basis OrderedBasisIndex k A :=
  (Pi.basis (fun _ => Polynomial.basisMonomials k)).reindex
    ((Equiv.sigmaEquivProd (Fin 3) Nat).trans toLex)

/-- The ordered tensor basis used for coefficient involution. Paper: §2. -/
noncomputable def orderedTensorBasis :
    Module.Basis OrderedTensorIndex k TensorAA :=
  (orderedBasis.tensorProduct orderedBasis).reindex toLex

/-- The index involution induced by tensor flip. Paper: §2. -/
def swapIndex (p : OrderedTensorIndex) : OrderedTensorIndex :=
  toLex (ofLex p).swap

/-- The flip involution on ordered tensor indices is self-inverse. Paper: §2. -/
theorem swapIndex_involutive (p : OrderedTensorIndex) :
    swapIndex (swapIndex p) = p := by
  simp [swapIndex]

/-- Coordinate extraction in the ordered tensor basis. Paper: §2. -/
def coeffMap (i j : OrderedBasisIndex) : TensorAA →ₗ[k] k :=
  (Finsupp.lapply (toLex (i, j))).comp (orderedTensorBasis.repr :
    TensorAA →ₗ[k] (OrderedTensorIndex →₀ k))

/-- Flip exchanges the two ordered tensor coordinates. Paper: §2. -/
theorem coeffMap_flip (x : TensorAA) (i j : OrderedBasisIndex) :
    coeffMap i j (TensorProduct.comm k A A x) = coeffMap j i x := by
  let f : TensorAA →ₗ[k] k :=
    (coeffMap i j).comp (TensorProduct.comm k A A).toLinearMap
  let g : TensorAA →ₗ[k] k := coeffMap j i
  have hfg : f = g := by
    apply orderedTensorBasis.ext
    intro p
    let ij := ofLex p
    have hp : p = toLex ij := (toLex.apply_symm_apply p).symm
    rw [hp]
    rcases ij with ⟨i', j'⟩
    simp [f, g, coeffMap, orderedTensorBasis,
      Module.Basis.tensorProduct_apply, Finsupp.lapply]
    ring
  exact congrArg (fun h : TensorAA →ₗ[k] k => h x) hfg

/-- Flip exchanges ordered tensor-basis coefficients. Paper: §2. -/
theorem coeff_flip (x : TensorAA) (p : OrderedTensorIndex) :
    orderedTensorBasis.repr (TensorProduct.comm k A A x) p =
      orderedTensorBasis.repr x (swapIndex p) := by
  let ij := ofLex p
  have hp : p = toLex ij := (toLex.apply_symm_apply p).symm
  rw [hp]
  rcases ij with ⟨i, j⟩
  simpa [coeffMap, swapIndex, orderedTensorBasis] using
    coeffMap_flip x i j

/-- Off-diagonal basis pairs lie in the square span. Paper: §2. -/
theorem pair_mem_squareSpan (i j : OrderedBasisIndex) :
    orderedBasis i ⊗ₜ[k] orderedBasis j +
        orderedBasis j ⊗ₜ[k] orderedBasis i ∈ squareSpan := by
  have hsum :
      (orderedBasis i + orderedBasis j) ⊗ₜ[k]
          (orderedBasis i + orderedBasis j) ∈ squareSpan :=
    Submodule.subset_span ⟨orderedBasis i + orderedBasis j, rfl⟩
  have hi : orderedBasis i ⊗ₜ[k] orderedBasis i ∈ squareSpan :=
    Submodule.subset_span ⟨orderedBasis i, rfl⟩
  have hj : orderedBasis j ⊗ₜ[k] orderedBasis j ∈ squareSpan :=
    Submodule.subset_span ⟨orderedBasis j, rfl⟩
  have A_add_self (x : A) : x + x = 0 := by
    ext n m
    exact CharTwo.add_self_eq_zero ((x n).coeff m)
  have tensor_add_self (x : TensorAA) : x + x = 0 := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro x y
      rw [← TensorProduct.add_tmul, A_add_self]
      simp
    · intro x y hx hy
      simp only [add_add_add_comm, hx, hy, add_zero]
  have heq :
      orderedBasis i ⊗ₜ[k] orderedBasis j +
          orderedBasis j ⊗ₜ[k] orderedBasis i =
        (orderedBasis i + orderedBasis j) ⊗ₜ[k]
            (orderedBasis i + orderedBasis j) +
          orderedBasis i ⊗ₜ[k] orderedBasis i +
          orderedBasis j ⊗ₜ[k] orderedBasis j := by
    calc
      _ = (orderedBasis i ⊗ₜ[k] orderedBasis j +
          orderedBasis j ⊗ₜ[k] orderedBasis i) +
          (orderedBasis i ⊗ₜ[k] orderedBasis i +
            orderedBasis i ⊗ₜ[k] orderedBasis i) +
          (orderedBasis j ⊗ₜ[k] orderedBasis j +
            orderedBasis j ⊗ₜ[k] orderedBasis j) := by
        rw [tensor_add_self, tensor_add_self]
        simp
      _ = _ := by
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
        abel
  rw [heq]
  exact squareSpan.add_mem (squareSpan.add_mem hsum hi) hj

/-- The expansion of a tensor in the ordered tensor basis. Paper: §2. -/
theorem basis_expansion (x : TensorAA) :
    x = ∑ p ∈ (orderedTensorBasis.repr x).support,
      (orderedTensorBasis.repr x p) • orderedTensorBasis p := by
  symm
  calc
    _ = (Finsupp.linearCombination k (⇑orderedTensorBasis))
        (orderedTensorBasis.repr x) := by
      rw [Finsupp.linearCombination_apply]
      rfl
    _ = orderedTensorBasis.repr.symm (orderedTensorBasis.repr x) := by
      symm
      exact orderedTensorBasis.repr_symm_apply (orderedTensorBasis.repr x)
    _ = x := LinearEquiv.symm_apply_apply orderedTensorBasis.repr x

/-- The diagonal predicate on ordered tensor indices. Paper: §2. -/
def diagonalIndex (p : OrderedTensorIndex) : Prop :=
  (ofLex p).1 = (ofLex p).2

/-- The off-diagonal predicate on ordered tensor indices. Paper: §2. -/
def offDiagonalIndex (p : OrderedTensorIndex) : Prop :=
  (ofLex p).1 ≠ (ofLex p).2

/-- Swapping preserves the off-diagonal predicate. Paper: §2. -/
theorem swapIndex_offDiagonal {p : OrderedTensorIndex}
    (hp : offDiagonalIndex p) : offDiagonalIndex (swapIndex p) := by
  simpa [offDiagonalIndex, swapIndex] using (Ne.symm hp)

/-- An off-diagonal index is not fixed by swapping. Paper: §2. -/
theorem swapIndex_ne_self_of_offDiagonal {p : OrderedTensorIndex}
    (hp : offDiagonalIndex p) : swapIndex p ≠ p := by
  intro h
  have hpair : (ofLex p).swap = ofLex p := by
    have h' := congrArg ofLex h
    simpa [swapIndex] using h'
  have hcoord := congrArg Prod.fst hpair
  exact hp hcoord.symm

/-- Fixed tensors have swap-symmetric ordered coefficients. Paper: §2. -/
theorem repr_swap_eq (c : C) (p : OrderedTensorIndex) :
    orderedTensorBasis.repr (c : TensorAA) (swapIndex p) =
      orderedTensorBasis.repr (c : TensorAA) p := by
  have h := coeff_flip (c : TensorAA) p
  have hc : TensorProduct.comm k A A (c : TensorAA) = (c : TensorAA) := c.property
  rw [hc] at h
  exact h.symm

/-- A diagonal tensor-basis vector lies in the square span. Paper: §2. -/
theorem basis_mem_squareSpan_of_diagonal {p : OrderedTensorIndex}
    (hp : diagonalIndex p) : orderedTensorBasis p ∈ squareSpan := by
  let ij := ofLex p
  have hpi : p = toLex ij := (toLex.apply_symm_apply p).symm
  rw [hpi]
  rw [hpi] at hp
  rcases ij with ⟨i, j⟩
  dsimp [diagonalIndex] at hp
  have hij : i = j := hp
  subst j
  have hgen : orderedBasis i ⊗ₜ[k] orderedBasis i ∈ squareSpan :=
    Submodule.subset_span ⟨orderedBasis i, rfl⟩
  simpa [orderedTensorBasis, Module.Basis.tensorProduct_apply] using hgen

/-- Coefficient-symmetric basis pairs lie in the square span. Paper: §2. -/
theorem coeff_pair_mem_squareSpan (c : C) (p : OrderedTensorIndex) :
    (orderedTensorBasis.repr (c : TensorAA) p) • orderedTensorBasis p +
        (orderedTensorBasis.repr (c : TensorAA) (swapIndex p)) •
          orderedTensorBasis (swapIndex p) ∈ squareSpan := by
  let ij := ofLex p
  have hpi : p = toLex ij := (toLex.apply_symm_apply p).symm
  rw [hpi]
  rcases ij with ⟨i, j⟩
  have hcoeff := repr_swap_eq c (toLex (i, j))
  rw [← hcoeff]
  rw [← smul_add]
  apply squareSpan.smul_mem
  simpa [orderedTensorBasis, swapIndex,
    Module.Basis.tensorProduct_apply] using pair_mem_squareSpan i j

/-- Flip symmetry preserves the finite coefficient support. Paper: §2. -/
theorem repr_support_swap_mem (c : C) {p : OrderedTensorIndex}
    (hp : p ∈ (orderedTensorBasis.repr (c : TensorAA)).support) :
    swapIndex p ∈ (orderedTensorBasis.repr (c : TensorAA)).support := by
  rw [Finsupp.mem_support_iff] at hp ⊢
  intro hzero
  apply hp
  rw [← repr_swap_eq c p, hzero]

/-- The Zhou fixed tensor module is spanned by square tensors. Paper: §2. -/
theorem concreteSquareSpanData : SquareSpanData where
  squares_span c := by
    classical
    let r := orderedTensorBasis.repr (c : TensorAA)
    let q : TensorAA →ₗ[k] (TensorAA ⧸ squareSpan) := Submodule.mkQ squareSpan
    let f : OrderedTensorIndex → (TensorAA ⧸ squareSpan) :=
      fun p => q (r p • orderedTensorBasis p)
    let diagonalSupport := r.support.filter diagonalIndex
    let offDiagonalSupport := r.support.filter (fun p => ¬ diagonalIndex p)
    have hpair (p : OrderedTensorIndex) : f p + f (swapIndex p) = 0 := by
      change q (r p • orderedTensorBasis p) +
        q (r (swapIndex p) • orderedTensorBasis (swapIndex p)) = 0
      rw [← q.map_add]
      exact (Submodule.Quotient.mk_eq_zero squareSpan).2
        (coeff_pair_mem_squareSpan c p)
    have hdiagonal : ∑ p ∈ diagonalSupport, f p = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero squareSpan).2
      change r p • orderedTensorBasis p ∈ squareSpan
      exact squareSpan.smul_mem (r p)
        (basis_mem_squareSpan_of_diagonal (Finset.mem_filter.mp hp).2)
    have hoffDiagonal : ∑ p ∈ offDiagonalSupport, f p = 0 := by
      apply Finset.sum_involution (fun p _ => swapIndex p)
      · intro p hp
        exact hpair p
      · intro p hp _
        exact swapIndex_ne_self_of_offDiagonal (by
          simpa [offDiagonalIndex, diagonalIndex] using
            (Finset.mem_filter.mp hp).2)
      · intro p hp
        apply Finset.mem_filter.mpr
        refine ⟨repr_support_swap_mem c (Finset.mem_filter.mp hp).1, ?_⟩
        simpa [offDiagonalIndex, diagonalIndex] using
          swapIndex_offDiagonal (by
            simpa [offDiagonalIndex, diagonalIndex] using
              (Finset.mem_filter.mp hp).2)
      · intro p hp
        exact swapIndex_involutive p
    have hsplit :
        ∑ p ∈ r.support, f p =
          ∑ p ∈ diagonalSupport, f p + ∑ p ∈ offDiagonalSupport, f p := by
      symm
      simpa [diagonalSupport, offDiagonalSupport] using
        (Finset.sum_filter_add_sum_filter_not r.support diagonalIndex f)
    have hexpand : q (c : TensorAA) = ∑ p ∈ r.support, f p := by
      calc
        q (c : TensorAA) = q (∑ p ∈ (orderedTensorBasis.repr (c : TensorAA)).support,
            (orderedTensorBasis.repr (c : TensorAA) p) • orderedTensorBasis p) :=
          congrArg q (basis_expansion (c : TensorAA))
        _ = ∑ p ∈ r.support, f p := by
          simp only [map_sum]
          rfl
    apply (Submodule.Quotient.mk_eq_zero squareSpan).mp
    calc
      q (c : TensorAA) = ∑ p ∈ r.support, f p := hexpand
      _ = ∑ p ∈ diagonalSupport, f p + ∑ p ∈ offDiagonalSupport, f p := hsplit
      _ = 0 := by rw [hdiagonal, hoffDiagonal, zero_add]

end
end PaperKernel
end Construction
end Connes
