/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.HomogeneousChart
public import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalClosure


/-!
# The pure-momentum axis obstruction

The normalized canonical order symbol is homogeneous of ordinary total degree:
it is order-homogeneous and its proved fibre-only property removes every
weight-zero coordinate exponent.  Its value at the distinguished pure-momentum
axis is therefore its normalized pure coefficient, namely one.

Consequently that axis cannot belong to any checked affine zero locus contained
in the principal-symbol hypersurface.  Applying the existing conditional
equation-conormal-closure containment gives the corresponding contradiction.
This file proves no conormal-axis producer and no Gabber theorem.
-/

@[expose] public section

namespace Stafford38.Geometry.ConormalAxisContradiction

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylEulerResidue
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable {k : Type*} [Field k] {n N : ℕ}

/-- An order-homogeneous fibre-only symbol is homogeneous for ordinary total
degree. -/
theorem isHomogeneous_of_orderHomogeneous_of_isFibreOnly
    {P : SymbolRing k n}
    (horder : P.IsWeightedHomogeneous (@orderWeight n) N)
    (hfibre : IsFibreOnly k P) :
    P.IsHomogeneous N := by
  intro m hm
  have horder' := horder hm
  rw [Finsupp.weight_apply] at horder'
  rw [← horder']
  apply Finsupp.sum_congr
  intro i hi
  rcases i with i | i
  · simp [orderWeight, fibreWeight, hfibre m hm i]
  · simp [orderWeight, fibreWeight]

/-- The canonical order principal symbol is homogeneous of ordinary total
degree `N`. -/
theorem canonical_orderPrincipalComponent_isHomogeneous
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedPrincipalComponent k orderWeight N d).IsHomogeneous N := by
  apply isHomogeneous_of_orderHomogeneous_of_isFibreOnly
  · simpa [presentedPrincipalComponent] using
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := @orderWeight (n + 1)) (n := N)
        (presentedNormalFormLinearEquiv k (n + 1) d))
  · exact canonical_orderPrincipalComponent_isFibreOnly k n N hd

/-- A homogeneous polynomial with pure-axis coefficient one does not vanish at
that axis. -/
theorem eval_axis_eq_one_of_pureCoefficient_one
    (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N)
    (hpure : P.coeff (Finsupp.single t N) = 1) :
    MvPolynomial.eval (axisPoint k t) P = 1 := by
  classical
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (Finsupp.single t N)]
  · rw [hpure, one_mul]
    by_cases hN : N = 0
    · subst N
      simp
    · rw [Finsupp.support_single t hN]
      simp [axisPoint]
  · intro m hm hne
    have hmcoeff : P.coeff m ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    have hexists : ∃ i ∈ m.support, i ≠ t := by
      by_contra hnot
      have hsubset : m.support ⊆ {t} := by
        intro i hi
        simp only [Finset.mem_singleton]
        by_contra hit
        exact hnot ⟨i, hi, hit⟩
      have hmform : m = Finsupp.single t (m t) :=
        Finsupp.support_subset_singleton.mp hsubset
      have hdegree : m.degree = N := by
        rw [Finsupp.degree_eq_weight_one]
        exact hP hmcoeff
      rw [hmform, Finsupp.degree_single] at hdegree
      apply hne
      rw [hmform, hdegree]
    rcases hexists with ⟨i, hi, hit⟩
    rw [Finset.prod_eq_zero hi, mul_zero]
    rw [axisPoint, ite_eq_right hit, zero_pow]
    exact Finsupp.mem_support_iff.mp hi
  · intro hnot
    exact (hnot (MvPolynomial.mem_support_iff.mpr (hpure.trans_ne one_ne_zero))).elim

/-- Direct set-level obstruction: if a checked affine locus lies in `V(P)`,
axis membership contradicts homogeneity and pure coefficient one. -/
theorem false_of_axis_mem_of_subset_principal_zeroLocus
    (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N)
    (hpure : P.coeff (Finsupp.single t N) = 1)
    {S : Set (PhaseVar n → k)}
    (hS : S ⊆ MvPolynomial.zeroLocus k (Ideal.span ({P} : Set (SymbolRing k n))))
    (haxis : axisPoint k t ∈ S) : False := by
  have hzero := (MvPolynomial.mem_zeroLocus_iff.mp (hS haxis)) P
    (Ideal.subset_span (Set.mem_singleton P))
  rw [MvPolynomial.aeval_eq_eval,
    eval_axis_eq_one_of_pureCoefficient_one t hP hpure] at hzero
  exact one_ne_zero hzero

/-- The normalized canonical order symbol evaluates to one at the
distinguished pure-momentum axis. -/
theorem canonical_orderPrincipalComponent_eval_pureMomentumAxis
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    MvPolynomial.eval
        (axisPoint k (.inr (0 : Fin (n + 1))))
        (presentedPrincipalComponent k orderWeight N d) = 1 := by
  exact eval_axis_eq_one_of_pureCoefficient_one
    (.inr (0 : Fin (n + 1)))
    (canonical_orderPrincipalComponent_isHomogeneous n N hd)
    (canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd)

/-- Any checked affine locus contained in the canonical principal-symbol
hypersurface excludes the distinguished pure-momentum axis. -/
theorem canonical_pureMomentumAxis_not_mem_of_subset_principal_zeroLocus
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {S : Set (PhaseVar (n + 1) → k)}
    (hS : S ⊆ MvPolynomial.zeroLocus k
      (Ideal.span
        ({presentedPrincipalComponent k orderWeight N d} :
          Set (SymbolRing k (n + 1))))) :
    axisPoint k (.inr (0 : Fin (n + 1))) ∉ S := by
  intro haxis
  exact false_of_axis_mem_of_subset_principal_zeroLocus
    (.inr (0 : Fin (n + 1)))
    (canonical_orderPrincipalComponent_isHomogeneous n N hd)
    (canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd)
    hS haxis

/-- The reduced canonical order-support zero locus is contained in the
canonical principal-symbol hypersurface. -/
theorem canonical_reducedOrderSupport_zeroLocus_subset_principal_zeroLocus
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    MvPolynomial.zeroLocus k
        (reducedOrderSupportIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)) ⊆
      MvPolynomial.zeroLocus k
        (Ideal.span
          ({presentedPrincipalComponent k orderWeight N d} :
            Set (SymbolRing k (n + 1)))) := by
  apply MvPolynomial.zeroLocus_anti_mono
  apply Ideal.span_le.mpr
  intro P hP
  rw [Set.mem_singleton_iff.mp hP]
  exact orderInitialIdeal_le_reducedOrderSupportIdeal k _
    (canonical_orderPrincipalComponent_mem_initialIdeal k n N hd)

/-- Exact equation-conormal connector.  Under the already isolated
base-relative Poisson hypothesis, membership of the distinguished axis in the
equation-conormal closure is impossible. -/
theorem false_of_canonical_pureMomentumAxis_mem_equationConormalClosure
    [CharZero k]
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (hJ : IsBaseRelativePoisson
      (reducedOrderSupportIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))
    (haxis : axisPoint k (.inr (0 : Fin (n + 1))) ∈
      equationConormalClosure
        (reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N))) : False := by
  apply false_of_axis_mem_of_subset_principal_zeroLocus
    (.inr (0 : Fin (n + 1)))
    (canonical_orderPrincipalComponent_isHomogeneous n N hd)
    (canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd)
    (S := equationConormalClosure
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))
  · exact (equationConormalClosure_subset_reducedOrderSupport
      (canonicalRightIdeal (presentedCoordinate k n) d N) hJ).trans
        (canonical_reducedOrderSupport_zeroLocus_subset_principal_zeroLocus
          n N hd)
  · exact haxis


end

end Stafford38.Geometry.ConormalAxisContradiction
