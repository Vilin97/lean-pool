/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermPages
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalAxisAvoidanceConsumer
import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule

/-!
# The canonical filtered two-term complex

This is the concrete filtered complex used for the canonical Weyl quotient.
The filtration is the actual order filtration on the quotient, extended by
zero in negative order.  No associated-graded identification is assumed here.
-/

namespace Stafford38.Characteristic.CanonicalFilteredTwoTerm

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylQuotientTransport
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CanonicalIdeal (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

/-- The filtered quotient by the canonical right ideal determined by `d` and its monic degree. -/
abbrev CanonicalQuotient (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  FilteredRightQuotient k (CanonicalIdeal k n N d)

/-- Right multiplication by an element, descended to the quotient by a right ideal. -/
def rightMulLinearMap (I : RightIdeal (PresentedWeyl k (n + 1)))
    (a : PresentedWeyl k (n + 1)) :
    FilteredRightQuotient k I →ₗ[k] FilteredRightQuotient k I :=
  Submodule.mapQ (rightIdealKSubmodule k I) (rightIdealKSubmodule k I)
    (LinearMap.mulRight k a) (by
      intro z hz
      exact I.smul_mem (MulOpposite.op a) hz)

omit [Algebra ℚ k] in
@[simp]
theorem rightMulLinearMap_mk
    (I : RightIdeal (PresentedWeyl k (n + 1)))
    (a z : PresentedWeyl k (n + 1)) :
    rightMulLinearMap k I a (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (z * a) := by
  change Submodule.Quotient.mk (LinearMap.mulRight k a z) = _
  rfl

/-- The decreasing integer filtration obtained from quotient order pieces in nonpositive
degrees. -/
def canonicalOrderFiltration
    (I : RightIdeal (PresentedWeyl k (n + 1))) (p : ℤ) :
    Submodule k (FilteredRightQuotient k I) :=
  if _hp : p ≤ 0 then quotientOrderPiece k I (-p).toNat else ⊥

omit [Algebra ℚ k] in
theorem canonicalOrderFiltration_eq_of_nonpos
    (I : RightIdeal (PresentedWeyl k (n + 1))) {p : ℤ} (hp : p ≤ 0) :
    canonicalOrderFiltration k I p = quotientOrderPiece k I (-p).toNat := by
  simp [canonicalOrderFiltration, hp]

omit [Algebra ℚ k] in
theorem canonicalOrderFiltration_eq_bot_of_pos
    (I : RightIdeal (PresentedWeyl k (n + 1))) {p : ℤ} (hp : 0 < p) :
    canonicalOrderFiltration k I p = ⊥ := by
  simp [canonicalOrderFiltration, not_le.mpr hp]

omit [Algebra ℚ k] in
theorem canonicalOrderFiltration_antitone
    (I : RightIdeal (PresentedWeyl k (n + 1))) :
    Antitone (canonicalOrderFiltration k I) := by
  intro p q hpq
  by_cases hq : q ≤ 0
  · have hp : p ≤ 0 := le_trans hpq hq
    rw [canonicalOrderFiltration_eq_of_nonpos k I hp,
      canonicalOrderFiltration_eq_of_nonpos k I hq]
    apply Submodule.map_mono
    exact presentedWeightPiece_mono k orderWeight (by omega)
  · rw [canonicalOrderFiltration_eq_bot_of_pos k I (lt_of_not_ge hq)]
    exact bot_le

omit [Algebra ℚ k] in
theorem canonicalOrderFiltration_exhaustive
    (I : RightIdeal (PresentedWeyl k (n + 1))) :
    ∀ q : FilteredRightQuotient k I, ∃ p : ℤ,
      q ∈ canonicalOrderFiltration k I p := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k I) q
  obtain ⟨m, hm⟩ := exists_mem_orderPiece k z
  refine ⟨-(m : ℤ), ?_⟩
  rw [canonicalOrderFiltration_eq_of_nonpos k I (by omega)]
  have hidx : (- - (m : ℤ)).toNat = m := by omega
  rw [hidx]
  change (rightIdealKSubmodule k I).mkQ z ∈ quotientOrderPiece k I m
  exact Submodule.mem_map.mpr ⟨z, hm, rfl⟩

omit [Algebra ℚ k] in
private theorem quotientOrderPiece_mul_coordinate_mem
    (I : RightIdeal (PresentedWeyl k (n + 1)))
    {m : ℕ} {q : FilteredRightQuotient k I}
    (hq : q ∈ quotientOrderPiece k I m)
    (hx : presentedCoordinate k n ∈ orderPiece k (n + 1) 0) :
    rightMulLinearMap k I (presentedCoordinate k n) q ∈
      quotientOrderPiece k I m := by
  rcases (Submodule.mem_map.mp hq) with ⟨z, hz, rfl⟩
  change rightMulLinearMap k I (presentedCoordinate k n)
    (Submodule.Quotient.mk z) ∈ quotientOrderPiece k I m
  rw [rightMulLinearMap_mk]
  apply Submodule.mem_map.mpr
  refine ⟨z * presentedCoordinate k n, mul_mem_orderPiece k hz hx, ?_⟩
  rfl

/-- The filtered two-term construction on the canonical quotient, with differential given by
right multiplication by the distinguished coordinate. -/
def canonicalFilteredTwoTerm (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :
    FilteredTwoTerm k (CanonicalQuotient k n N d) where
  G := canonicalOrderFiltration k (CanonicalIdeal k n N d)
  antitone := canonicalOrderFiltration_antitone k _
  f := rightMulLinearMap k (CanonicalIdeal k n N d) (presentedCoordinate k n)
  map_le := by
    intro p
    by_cases hp : p ≤ 0
    · rw [canonicalOrderFiltration_eq_of_nonpos k _ hp]
      apply Submodule.map_le_iff_le_comap.mpr
      intro z hz
      exact quotientOrderPiece_mul_coordinate_mem k _ hz
        (presentedCoordinate_mem_orderPiece_zero k n)
    · rw [canonicalOrderFiltration_eq_bot_of_pos k _ (lt_of_not_ge hp)]
      simp

theorem canonicalFilteredTwoTerm_f_surjective
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (canonicalFilteredTwoTerm k n N d).f := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (CanonicalIdeal k n N d)) q
  obtain ⟨y, hy⟩ :=
    presentedCanonicalRightQuotient_rightMul_coordinate_surjective
      (k := k) n N hd (qmk (CanonicalIdeal k n N d) z)
  obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective
    (rightIdealKSubmodule k (CanonicalIdeal k n N d)) y
  rw [← hy'] at hy
  refine ⟨Submodule.Quotient.mk y', ?_⟩
  change rightMulLinearMap k (CanonicalIdeal k n N d)
      (presentedCoordinate k n) (Submodule.Quotient.mk y') =
    Submodule.Quotient.mk z
  rw [rightMulLinearMap_mk]
  exact hy


end
end Stafford38.Characteristic.CanonicalFilteredTwoTerm
