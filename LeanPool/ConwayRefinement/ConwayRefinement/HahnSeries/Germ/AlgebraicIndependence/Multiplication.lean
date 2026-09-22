/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Additive
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.CantorBendixsonAddition
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive

/-!
# Upper bounds on Cantor–Bendixson values of Hahn products

In an ordered uniform exponent group that is Cauchy complete, every derivative point of a product
support lifts to a pair in the closed factor supports with a sufficient natural sum of ranks. For
nonpositive supports the only pair summing to zero is `(0, 0)`, giving submultiplicativity of the
value.
This is an upper bound only; coefficient cancellation is not excluded.
-/

public noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]

section Semiring

variable [NonUnitalNonAssocSemiring R]

/-- The closed support of a product is contained in the sum of the closed supports. -/
theorem closedSupport_mul_subset_add (b d : HahnSeries G R) :
    ((b * d).closedSupport : Set G) ⊆ (b.closedSupport : Set G) + (d.closedSupport : Set G) := by
  rw [coe_closedSupport, coe_closedSupport, coe_closedSupport,
    ← b.isPWO_support.closure_add_eq d.isPWO_support]
  exact closure_mono support_mul_subset

/-- A product derivative point lifts to closed-support summands whose ranks bound its stage. -/
theorem exists_cantorBendixsonRank_add_ge_of_mem_mul_derivative (b d : HahnSeries G R)
    (o : Ordinal.{u}) {z : G} (hz : z ∈ ((b * d).closedSupport.cantorBendixson o : Set G)) :
    ∃ x ∈ b.closedSupport, ∃ y ∈ d.closedSupport, x + y = z ∧
      o ≤ (NatOrdinal.of (b.cantorBendixsonRank x) +
        NatOrdinal.of (d.cantorBendixsonRank y)).val := by
  let s : Closeds G := ⟨(b.closedSupport : Set G) + (d.closedSupport : Set G),
    b.closedSupport_isPWO.isClosed_add d.closedSupport_isPWO
      b.closedSupport.isClosed d.closedSupport.isClosed⟩
  have hsub : (b * d).closedSupport ≤ s := b.closedSupport_mul_subset_add d
  have hm : z ∈ (s.cantorBendixson o : Set G) :=
    Closeds.cantorBendixson_mono hsub o hz
  simpa only [cantorBendixsonRank_eq, Set.mem_ofPred_eq] using
    b.closedSupport.cantorBendixson_add_subset d.closedSupport
      b.closedSupport_isPWO d.closedSupport_isPWO o hm

/-- For nonpositive supports, the product rank at zero is bounded by the natural sum. -/
theorem cantorBendixsonRank_mul_le (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0)
    (h : 0 ∈ closure (b * d).support) :
    0 ∈ closure b.support ∧ 0 ∈ closure d.support ∧
      (b * d).cantorBendixsonRank 0 ≤
        (NatOrdinal.of (b.cantorBendixsonRank 0) +
          NatOrdinal.of (d.cantorBendixsonRank 0)).val := by
  have hm := ((b * d).mem_support_derivative_iff 0 ((b * d).cantorBendixsonRank 0)).mpr ⟨h, le_rfl⟩
  obtain ⟨x, hx, y, hy, hxy, hr⟩ := b.exists_cantorBendixsonRank_add_ge_of_mem_mul_derivative d _ hm
  have hx0 : x ≤ 0 := closure_minimal hb isClosed_Iic ((b.mem_closedSupport x).mp hx)
  have hy0 : y ≤ 0 := closure_minimal hd isClosed_Iic ((d.mem_closedSupport y).mp hy)
  have hxge : 0 ≤ x := by simpa only [hxy, add_zero] using add_le_add_right hy0 x
  have hxe : x = 0 := hx0.antisymm hxge
  subst x
  have hye : y = 0 := by simpa only [zero_add] using hxy
  subst y
  exact ⟨(b.mem_closedSupport 0).mp hx, (d.mem_closedSupport 0).mp hy, hr⟩

/-- The value of a product with nonpositive supports is bounded by the natural product. -/
@[blueprint "lem:cantor-bendixson-value-product-upper-bound"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Product upper bound for the Cantor--Bendixson value")
  (statement := /--
    Let $R$ be a semiring, not necessarily unital or associative, and let $G$
    be a nontrivial ordered abelian group equipped with a compatible additive
    uniformity and its order topology.  Assume that $G$ is Cauchy complete.  If
    $b,d\in R((G^{\le0}))$, then
    \[
      V_{\mathrm{CB}}(bd)
      \le V_{\mathrm{CB}}(b)\odot V_{\mathrm{CB}}(d),
    \]
    where $\odot$ is Hessenberg's natural product.
  -/)
  (proof := /--
    By \ref{def:cantor-bendixson-value}, the assertion is trivial if $0$ is
    outside the closed support of $bd$; otherwise its value is $\omega$ to
    the rank there.  The closed support of $bd$ is contained in the sum of
    the closed supports of $b$ and $d$.  By
    \ref{lem:cantor-bendixson-derivative-of-sum}, a point of rank $\alpha$ in
    this sum lifts to $x$ and $y$ whose ranks have natural sum at least
    $\alpha$.  Nonpositivity and $x+y=0$ force $x=y=0$.  Exponentiating the
    resulting rank inequality by $\omega$ turns natural sum into natural
    product and gives the bound.
  -/)]
theorem cantorBendixsonValue_mul_le (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0) :
    NatOrdinal.of (b * d).cantorBendixsonValue ≤
      NatOrdinal.of b.cantorBendixsonValue * NatOrdinal.of d.cantorBendixsonValue := by
  by_cases hm : 0 ∈ closure (b * d).support
  · obtain ⟨hb0, hd0, hr⟩ := b.cantorBendixsonRank_mul_le d hb hd hm
    rw [(b * d).cantorBendixsonValue_of_mem hm, b.cantorBendixsonValue_of_mem hb0,
      d.cantorBendixsonValue_of_mem hd0, NatOrdinal.of_omega0_opow,
      NatOrdinal.of_omega0_opow, NatOrdinal.of_omega0_opow, ← NatOrdinal.wpow_add]
    exact NatOrdinal.wpow_le_wpow.mpr hr
  · rw [(b * d).cantorBendixsonValue_of_notMem hm]
    exact zero_le

end Semiring

section Ring

variable [Ring R]

/-- A nonnegative integer power is bounded by the natural power of the original value. -/
theorem cantorBendixsonValue_pow_le (b : HahnSeries G R) (hb : b.support ⊆ Iic 0) (m : ℕ) :
    NatOrdinal.of (b ^ m).cantorBendixsonValue ≤
      NatOrdinal.of b.cantorBendixsonValue ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    have hf : (1 : HahnSeries G R).support.Finite :=
      (finite_singleton _).subset support_single_subset
    by_cases hc : (1 : HahnSeries G R).coeff 0 = 0
    · rw [cantorBendixsonValue_of_finite_of_coeff_eq_zero _ hf hc]
      exact zero_le
    · rw [cantorBendixsonValue_of_finite_of_coeff_ne_zero _ hf hc]
      exact le_rfl
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact (cantorBendixsonValue_mul_le _ _
      ((nonpositiveSubring G R).pow_mem hb m) hb).trans (mul_le_mul_left ih _)


omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] in
/-- Multiplication by a nonzero ordinary scalar preserves the value. -/
theorem cantorBendixsonValue_single_zero_mul [NoZeroDivisors R]
    (b : HahnSeries G R) {a : R} (ha : a ≠ 0) :
    (single 0 a * b).cantorBendixsonValue = b.cantorBendixsonValue := by
  apply cantorBendixsonValue_congr_support
  ext x
  simp only [mem_support, coeff_single_zero_mul, mul_ne_zero_iff]
  exact ⟨And.right, fun hx ↦ ⟨ha, hx⟩⟩

/-- A nonpositive factor of value zero makes the product value zero. -/
theorem cantorBendixsonValue_mul_eq_zero_of_left (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0)
    (hz : b.cantorBendixsonValue = 0) : (b * d).cantorBendixsonValue = 0 := by
  have h := b.cantorBendixsonValue_mul_le d hb hd
  rw [hz, NatOrdinal.of_zero, zero_mul] at h
  exact le_antisymm h zero_le

/-- A nonpositive factor of value one preserves the other factor's value. -/
theorem cantorBendixsonValue_mul_of_left_eq_one [NoZeroDivisors R] (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0)
    (hone : b.cantorBendixsonValue = 1) :
    (b * d).cantorBendixsonValue = d.cantorBendixsonValue := by
  obtain ⟨hcoeff, hz⟩ := (b.cantorBendixsonValue_eq_one_iff).mp hone
  have he : (b - single 0 (b.coeff 0)).support ⊆ Iic (0 : G) := by
    intro x hx
    rcases support_sub_subset _ _ hx with hx | hx
    · exact hb hx
    · exact (support_single_subset hx : x = 0) ▸ le_rfl
  have herr := (b - single 0 (b.coeff 0)).cantorBendixsonValue_mul_eq_zero_of_left d he hd hz
  rw [sub_mul] at herr
  exact (cantorBendixsonValue_eq_of_sub_value_eq_zero _ _ herr).trans
    (d.cantorBendixsonValue_single_zero_mul hcoeff)

end Ring

end HahnSeries
