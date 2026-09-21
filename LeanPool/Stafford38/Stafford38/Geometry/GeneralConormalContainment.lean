/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalClosure

/-!
# Generic equation-conormal containment

This is the support-independent form of the affine conormal argument.
Fibre-degree homogeneity supplies its zero-section input through the actual
Mathlib graded-ideal API.
-/

namespace Stafford38.Geometry.GeneralConormalContainment

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.WeylFiltration

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (k := k) (n := n)) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

private def basePart (g : SymbolRing k n) : MvPolynomial (Fin n) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)
    (Sum.elim MvPolynomial.X (fun _ => 0)) g

private theorem baseLift_basePart_eq_zeroComponent (g : SymbolRing k n) :
    baseLift (basePart g) =
      (DirectSum.decompose (orderDecomposition (k := k) (n := n)) g 0 :
        SymbolRing k n) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
      have hC : MvPolynomial.C a ∈ orderDecomposition (k := k) (n := n) 0 :=
        MvPolynomial.isWeightedHomogeneous_C (@orderWeight n) a
      let C0 : orderDecomposition (k := k) (n := n) 0 := ⟨MvPolynomial.C a, hC⟩
      have hd := congrArg (fun z => z 0)
        (DirectSum.decompose_coe (orderDecomposition (k := k) (n := n)) C0)
      have hd' : (DirectSum.decompose (orderDecomposition (k := k) (n := n))
          (MvPolynomial.C a) 0 : SymbolRing k n) = MvPolynomial.C a := by
        simpa [C0] using congrArg Subtype.val hd
      rw [hd']
      simp [basePart]
  | add P Q hP hQ =>
      rw [DirectSum.decompose_add]
      change baseLift (basePart (P + Q)) =
        (DirectSum.decompose (orderDecomposition (k := k) (n := n)) P 0 :
          SymbolRing k n) +
        (DirectSum.decompose (orderDecomposition (k := k) (n := n)) Q 0 :
          SymbolRing k n)
      rw [← hP, ← hQ]
      simp [basePart]
  | mul_X P i hP =>
      rcases i with i | i
      · have hX : MvPolynomial.X (Sum.inl i : PhaseVar n) ∈
            orderDecomposition (k := k) (n := n) 0 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) _
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
          (orderDecomposition (k := k) (n := n)) hX (Nat.zero_le 0)]
        rw [← hP]
        simp [basePart, baseLift]
      · have hX : MvPolynomial.X (Sum.inr i : PhaseVar n) ∈
            orderDecomposition (k := k) (n := n) 1 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) _
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le
          (orderDecomposition (k := k) (n := n)) hX (by omega)]
        simp [basePart]

private theorem eval_basePart (y : Fin n → k) (g : SymbolRing k n) :
    MvPolynomial.eval y (basePart g) =
      MvPolynomial.eval (zeroSectionPoint y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [basePart]
  | add P Q hP hQ =>
      simp only [basePart] at hP hQ
      simp only [basePart, map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rcases i with i | i
      · simp only [basePart, map_mul, MvPolynomial.eval₂Hom_X', Sum.elim_inl,
          MvPolynomial.eval_X]
        simp only [basePart] at hP
        rw [hP]
        simp [zeroSectionPoint]
      · simp [basePart, zeroSectionPoint]

theorem zeroSection_commonZero_of_isHomogeneous
    (J : Ideal (SymbolRing k n))
    (hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := n)))
    (y : Fin n → k)
    (hy : ∀ f ∈ J.comap baseLift, MvPolynomial.eval y f = 0) :
    ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0 := by
  intro g hg
  let f := basePart g
  have hf : baseLift f ∈ J := by
    rw [baseLift_basePart_eq_zeroComponent]
    exact (hhom.mem_iff.mp hg 0)
  have hzero := hy f hf
  rw [eval_basePart] at hzero
  exact hzero

/-- The equation-defined conormal over `V(J.comap baseLift)` is contained in
`V(J)`, provided the zero section over every base zero is a common zero of
`J`.  This is the exact generic bridge; no characteristic-support predicate
or radicality assumption is used here. -/
theorem equationConormalLocus_subset_zeroLocus
    [CharZero k]
    (J : Ideal (SymbolRing k n))
    (hJ : IsBaseRelativePoisson J)
    (hzero : ∀ y : Fin n → k,
      (∀ f ∈ J.comap baseLift, MvPolynomial.eval y f = 0) →
        ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0) :
    equationConormalLocus (J.comap baseLift) ⊆
      MvPolynomial.zeroLocus k J := by
  intro q hq
  let y : Fin n → k := fun i => q (Sum.inl i)
  let ξ : Fin n → k := fun i => q (Sum.inr i)
  have hy : ∀ f ∈ J.comap baseLift, MvPolynomial.eval y f = 0 := by
    intro f hf
    exact hq.1 f hf
  have hs := affineConormal_coordinatePoint_isCommonZero J hJ y
    (hzero y hy) (J.comap baseLift)
    (fun f => f.2) ξ hq.2
  have hsplit : Sum.elim y ξ = q := by
    funext i
    rcases i with i | i <;> rfl
  rw [← hsplit]
  exact hs

theorem equationConormalClosure_subset_zeroLocus
    [CharZero k]
    (J : Ideal (SymbolRing k n))
    (hJ : IsBaseRelativePoisson J)
    (hzero : ∀ y : Fin n → k,
      (∀ f ∈ J.comap baseLift, MvPolynomial.eval y f = 0) →
        ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0) :
    equationConormalClosure (J.comap baseLift) ⊆
      MvPolynomial.zeroLocus k J := by
  exact zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    (equationConormalLocus (J.comap baseLift)) J
    (equationConormalLocus_subset_zeroLocus J hJ hzero)

/-- Fibre-homogeneity supplies the zero-section input required by the generic
conormal argument. -/
theorem equationConormalClosure_subset_zeroLocus_of_isHomogeneous
    [CharZero k]
    (J : Ideal (SymbolRing k n))
    (hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := n)))
    (hJ : IsBaseRelativePoisson J) :
    equationConormalClosure (J.comap baseLift) ⊆
      MvPolynomial.zeroLocus k J := by
  apply equationConormalClosure_subset_zeroLocus J hJ
  intro y hy
  exact zeroSection_commonZero_of_isHomogeneous J hhom y hy


end

end Stafford38.Geometry.GeneralConormalContainment
