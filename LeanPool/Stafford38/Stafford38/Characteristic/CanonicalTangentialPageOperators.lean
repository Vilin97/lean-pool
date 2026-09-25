/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalFilteredGradedBridge
public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalActions
public import LeanPool.Stafford38.Stafford38.Weyl.FilteredCommutator


/-!
# Tangential filtered operators on the canonical quotient

Right multiplication by every tangential Weyl generator gives an actual
filtered operator on the canonical quotient.  The distinguished coordinate
commutes with these operators, so they induce operators on every page.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalTangentialPageOperators

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylPBW
open Stafford38.WeylQuotientTransport
open Stafford38.WeylFilteredCommutator

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CI (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

private abbrev K (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  canonicalFilteredTwoTerm k n N d

/-- A filtered page operator on the canonical two-term complex for the Weyl element. -/
abbrev PageOperator (n N : ℕ) (d : PresentedWeyl k (n + 1)) (e : ℤ) :=
  (K k n N d).PageOperator e

omit [Algebra ℚ k] in
private theorem oldGenerator_mem_orderPiece
    (n : ℕ) (i : Fin n ⊕ Fin n) :
    oldGenerator k n i ∈ orderPiece k (n + 1)
      (match i with | .inl _ => 0 | .inr _ => 1) := by
  cases i with
  | inl i =>
      rw [oldGenerator, orderPiece, mem_presentedWeightPiece,
        presentedNormalFormLinearEquiv_generator]
      intro m hm
      simp only [MvPolynomial.coeff_X] at hm
      split at hm
      · subst m
        simp [oldIndex, monomialWeight, orderWeight, fibreWeight]
      · contradiction
  | inr i =>
      rw [oldGenerator, orderPiece, mem_presentedWeightPiece,
        presentedNormalFormLinearEquiv_generator]
      intro m hm
      simp only [MvPolynomial.coeff_X] at hm
      split at hm
      · subst m
        simp [oldIndex, monomialWeight, orderWeight, fibreWeight]
      · contradiction

omit [Algebra ℚ k] in
private theorem rightMul_commute
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (a : PresentedWeyl k (n + 1))
    (ha : a * presentedCoordinate k n = presentedCoordinate k n * a) :
    (rightMulLinearMap k (CI k n N d) (presentedCoordinate k n)).comp
        (rightMulLinearMap k (CI k n N d) a) =
      (rightMulLinearMap k (CI k n N d) a).comp
        (rightMulLinearMap k (CI k n N d) (presentedCoordinate k n)) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (CI k n N d)) q
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    rightMulLinearMap_mk, rightMulLinearMap_mk, rightMulLinearMap_mk,
    rightMulLinearMap_mk]
  apply congrArg Submodule.Quotient.mk
  simp only [mul_assoc]
  rw [ha]

omit [Algebra ℚ k] in
private theorem rightMul_shift
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    {e : ℕ}
    (a : PresentedWeyl k (n + 1)) (ha : a ∈ orderPiece k (n + 1) e)
    {p : ℤ} {q : FilteredRightQuotient k (CI k n N d)}
    (hp : p ≤ 0) (hq : q ∈
      canonicalOrderFiltration k (CI k n N d) p) :
    rightMulLinearMap k (CI k n N d) a q ∈
      canonicalOrderFiltration k (CI k n N d) (p - (e : ℤ)) := by
  rw [canonicalOrderFiltration_eq_of_nonpos k _ hp] at hq
  have htarget : p - (e : ℤ) ≤ 0 := by omega
  rw [canonicalOrderFiltration_eq_of_nonpos k _ htarget]
  have hidx : (-(p - (e : ℤ))).toNat = (-p).toNat + e := by omega
  rw [hidx]
  rcases Submodule.mem_map.mp hq with ⟨z, hz, rfl⟩
  change rightMulLinearMap k (CI k n N d) a
    (Submodule.Quotient.mk z) ∈ _
  rw [rightMulLinearMap_mk]
  apply Submodule.mem_map.mpr
  refine ⟨z * a, ?_, rfl⟩
  exact mul_mem_orderPiece k hz ha

/-- Right multiplication by a symbol of bounded order, packaged as a filtered page operator. -/
def tangentialPageOperator
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (a : PresentedWeyl k (n + 1)) (e : ℕ)
    (ha : a ∈ orderPiece k (n + 1) e)
    (hax : a * presentedCoordinate k n = presentedCoordinate k n * a) :
    PageOperator k n N d (e : ℤ) where
  g := rightMulLinearMap k (CI k n N d) a
  commute := rightMul_commute k n N d a hax
  shift := by
    intro p q hq
    by_cases hp : p ≤ 0
    · exact rightMul_shift k n N d (a := a) ha hp hq
    · change q ∈ canonicalOrderFiltration k (CI k n N d) p at hq
      rw [canonicalOrderFiltration_eq_bot_of_pos k _ (lt_of_not_ge hp)] at hq
      subst q
      rw [map_zero]
      exact Submodule.zero_mem _

/-- The degree-zero page operator induced by a tangential position generator. -/
def tangentialCoordinatePageOperator
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (i : Fin n) :
    PageOperator k n N d 0 := by
  apply tangentialPageOperator k n N d
    (oldGenerator k n (.inl i)) 0
  · simpa using oldGenerator_mem_orderPiece k n (.inl i)
  · exact (presentedCoordinate_commutes_oldGenerator k n (.inl i)).symm

/-- The degree-one page operator induced by a tangential momentum generator. -/
def tangentialMomentumPageOperator
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (i : Fin n) :
    PageOperator k n N d 1 := by
  apply tangentialPageOperator k n N d
    (oldGenerator k n (.inr i)) 1
  · simpa using oldGenerator_mem_orderPiece k n (.inr i)
  · exact (presentedCoordinate_commutes_oldGenerator k n (.inr i)).symm


/-- The order degree of a tangential generator: zero for positions and one for momenta. -/
def tangentialDegree : (Fin n ⊕ Fin n) → ℕ
  | .inl _ => 0
  | .inr _ => 1

omit [Algebra ℚ k] in
private theorem rightMul_zero (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (z : CanonicalQuotient k n N d) :
    rightMulLinearMap k (CI k n N d) 0 z = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (CI k n N d)) z
  rw [rightMulLinearMap_mk, mul_zero]
  simp

omit [Algebra ℚ k] in
private theorem rightMul_commutator_apply
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (a b : PresentedWeyl k (n + 1)) (q : CanonicalQuotient k n N d) :
    rightMulLinearMap k (CI k n N d) a
        (rightMulLinearMap k (CI k n N d) b q) -
      rightMulLinearMap k (CI k n N d) b
        (rightMulLinearMap k (CI k n N d) a q) =
      rightMulLinearMap k (CI k n N d) (b * a - a * b) q := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (CI k n N d)) q
  change Submodule.Quotient.mk (z * b * a) -
      Submodule.Quotient.mk (z * a * b) =
    Submodule.Quotient.mk (z * (b * a - a * b))
  rw [mul_sub]
  rw [← Submodule.Quotient.mk_sub]
  congr 1
  noncomm_ring

omit [Algebra ℚ k] in
private theorem rightMul_lower_of_orderPiece
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    {e : ℕ} (a : PresentedWeyl k (n + 1))
    (ha : a ∈ orderPiece k (n + 1) e) {p : ℤ}
    {z : CanonicalQuotient k n N d}
    (hz : z ∈ (K k n N d).G p) :
    rightMulLinearMap k (CI k n N d) a z ∈
      (K k n N d).G (p - (e : ℤ)) := by
  change z ∈ canonicalOrderFiltration k (CI k n N d) p at hz
  change rightMulLinearMap k (CI k n N d) a z ∈
    canonicalOrderFiltration k (CI k n N d) (p - (e : ℤ))
  by_cases hp : p ≤ 0
  · exact rightMul_shift k n N d (a := a) ha hp hz
  · rw [canonicalOrderFiltration_eq_bot_of_pos k _ (lt_of_not_ge hp)] at hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    rw [map_zero]
    exact Submodule.zero_mem _

omit [Algebra ℚ k] in
theorem tangential_commutator_lower
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (i j : Fin n ⊕ Fin n) (p : ℤ)
    (z : CanonicalQuotient k n N d)
    (hz : z ∈ (K k n N d).G p) :
    (rightMulLinearMap k (CI k n N d) (oldGenerator k n i))
        (rightMulLinearMap k (CI k n N d) (oldGenerator k n j) z) -
      (rightMulLinearMap k (CI k n N d) (oldGenerator k n j))
        (rightMulLinearMap k (CI k n N d) (oldGenerator k n i) z) ∈
      (K k n N d).G
        (p - (tangentialDegree i + tangentialDegree j : ℤ) + 1) := by
  rcases i with i | i <;> rcases j with j | j
  · have hxi := oldGenerator_mem_orderPiece k n (.inl i)
    have hxj := oldGenerator_mem_orderPiece k n (.inl j)
    have hc := commutator_mem_orderPiece_pred k hxi hxj
    have hzero : oldGenerator k n (.inl j) * oldGenerator k n (.inl i) -
        oldGenerator k n (.inl i) * oldGenerator k n (.inl j) = 0 := by
      calc
        _ = -(Stafford.commutator (oldGenerator k n (.inl i))
          (oldGenerator k n (.inl j))) := by simp [Stafford.commutator]
        _ = 0 := by rw [oldGenerator_commutator]; simp [Matrix.J]
    rw [rightMul_commutator_apply, hzero]
    have hr : rightMulLinearMap k (CI k n N d)
        (0 : PresentedWeyl k (n + 1)) z = 0 := rightMul_zero k n N d z
    rw [hr]
    exact Submodule.zero_mem _
  · have hxi := oldGenerator_mem_orderPiece k n (.inl i)
    have hxj := oldGenerator_mem_orderPiece k n (.inr j)
    have hc := commutator_mem_orderPiece_pred k hxi hxj
    have hc' : oldGenerator k n (.inr j) * oldGenerator k n (.inl i) -
        oldGenerator k n (.inl i) * oldGenerator k n (.inr j) ∈
        orderPiece k (n + 1) 0 := by
      simpa [Stafford.commutator] using (show
        -(Stafford.commutator (oldGenerator k n (.inl i))
          (oldGenerator k n (.inr j))) ∈ orderPiece k (n + 1) 0 from
        (orderPiece k (n + 1) 0).neg_mem hc)
    rw [rightMul_commutator_apply]
    simpa [tangentialDegree] using
      (rightMul_lower_of_orderPiece k n N d _ hc' hz)
  · have hxi := oldGenerator_mem_orderPiece k n (.inr i)
    have hxj := oldGenerator_mem_orderPiece k n (.inl j)
    have hc := commutator_mem_orderPiece_pred k hxi hxj
    have hc' : oldGenerator k n (.inl j) * oldGenerator k n (.inr i) -
        oldGenerator k n (.inr i) * oldGenerator k n (.inl j) ∈
        orderPiece k (n + 1) 0 := by
      simpa [Stafford.commutator] using (show
        -(Stafford.commutator (oldGenerator k n (.inr i))
          (oldGenerator k n (.inl j))) ∈ orderPiece k (n + 1) 0 from
        (orderPiece k (n + 1) 0).neg_mem hc)
    rw [rightMul_commutator_apply]
    simpa [tangentialDegree] using
      (rightMul_lower_of_orderPiece k n N d _ hc' hz)
  · have hxi := oldGenerator_mem_orderPiece k n (.inr i)
    have hxj := oldGenerator_mem_orderPiece k n (.inr j)
    have hc := commutator_mem_orderPiece_pred k hxi hxj
    rw [rightMul_commutator_apply]
    have hc' := (orderPiece k (n + 1) 1).neg_mem hc
    have hc'' : oldGenerator k n (.inr j) * oldGenerator k n (.inr i) -
        oldGenerator k n (.inr i) * oldGenerator k n (.inr j) ∈
        orderPiece k (n + 1) 1 := by
      convert hc' using 1
      simp [Stafford.commutator]
    convert (rightMul_lower_of_orderPiece k n N d _ hc'' hz) using 1
    norm_num [tangentialDegree]
    ring

end
end Stafford38.Characteristic.CanonicalTangentialPageOperators
