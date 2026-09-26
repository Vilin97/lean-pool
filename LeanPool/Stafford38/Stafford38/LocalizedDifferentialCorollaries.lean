/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.LocalizedDifferentialClearing
public import LeanPool.Stafford38.Stafford38.LeftDenominatorTransport
public import LeanPool.Stafford38.Stafford38.FoundationClosure


/-!
Two-generator corollaries for localized polynomial differential-operator rings.
-/

@[expose] public section

namespace Stafford38.LocalizedDifferentialCorollaries

open Stafford
open Stafford38.DifferentialOperators
open Stafford38.LocalizedWeylAction
open Stafford38.LocalizedDifferentialClearing
open Stafford38.LocalizationCorollaries
open Stafford38.WeylIteratedEquivalence

noncomputable section
universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable (S : Submonoid (MvPolynomial (Fin n) k))
variable (B : Type u) [CommRing B]
variable [Algebra (MvPolynomial (Fin n) k) B] [Algebra k B]
variable [IsScalarTower k (MvPolynomial (Fin n) k) B]
variable [IsLocalization S B]

/-- The polynomial coefficient algebra in `n` variables. -/
abbrev A := MvPolynomial (Fin n) k
/-- The differential-operator algebra of the localized coefficient ring. -/
abbrev D := DifferentialOperators.algebra (k := k) (R := B)

/-- Multiplication by a coefficient, bundled as a differential operator of order zero. -/
def multiplicationD (b : B) : D (k := k) B :=
  ⟨multiplication (k := k) b,
    ⟨0, (mem_order_zero_iff_eq_multiplication _).2 (by
      ext x
      simp [multiplication_apply])⟩⟩

omit [CharZero k] in
private theorem multiplicationD_mul (b c : B) :
    multiplicationD (k := k) (B := B) b * multiplicationD (k := k) (B := B) c =
      multiplicationD (k := k) (B := B) (b * c) := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply, mul_assoc]

omit [CharZero k] in
private theorem multiplicationD_one : multiplicationD (k := k) (B := B) (1 : B) =
    (1 : D (k := k) B) := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply]

omit [CharZero k] in
private theorem multiplicationD_isUnit {b : B} (hb : IsUnit b) :
    IsUnit (multiplicationD (k := k) (B := B) b) := by
  rcases hb with ⟨u, hu⟩
  refine ⟨⟨multiplicationD (k := k) (B := B) b,
      multiplicationD (k := k) (B := B) u.inv, ?_, ?_⟩, rfl⟩
  · have h : b * u.inv = 1 := by rw [← hu]; exact u.val_inv
    rw [multiplicationD_mul, h, multiplicationD_one]
  · have h : u.inv * b = 1 := by rw [← hu]; exact u.inv_val
    rw [multiplicationD_mul, h, multiplicationD_one]

include S in
theorem s38_localized_differential
    (hS : S38 (PresentedWeyl k n)) : S38 (D (k := k) B) := by
  apply s38_of_leftUnitClearing hS
  · intro q hq
    obtain ⟨s, a, ha⟩ := localized_differential_left_denominator_clearing S B q
    let b : B := algebraMap (A (k := k) (n := n)) B (s : A)
    have hb : IsUnit b := IsLocalization.map_units B s
    refine ⟨a, multiplicationD (k := k) (B := B) b,
      multiplicationD_isUnit (k := k) (B := B) hb, ?_⟩
    apply Subtype.ext
    change multiplication (k := k) b * (q : Module.End k B) = weylEnd S B a
    exact ha

theorem s38_principal_localized_differential
    (f : A (k := k) (n := n))
    (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsLocalization (Submonoid.powers f) B]
    (hS : S38 (PresentedWeyl k n)) :
    S38 (D (k := k) B) := by
  exact s38_localized_differential (Submonoid.powers f) B hS

theorem s38_unconditional_localized_differential
    (S : Submonoid (A (k := k) (n := n)))
    (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsLocalization S B] :
    S38 (D (k := k) B) := by
  apply s38_localized_differential S B
  intro d hd
  exact Stafford38.universalStatement (k := k) n d hd

theorem s38_fraction_ring_differential
    (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsFractionRing (A (k := k) (n := n)) B] :
    S38 (D (k := k) B) := by
  apply s38_localized_differential
    (nonZeroDivisors (A (k := k) (n := n))) B
  intro d hd
  exact Stafford38.universalStatement (k := k) n d hd

/-- The product of all coordinate variables, whose inversion gives the Laurent localization. -/
def allCoordinateProduct : A (k := k) (n := n) :=
  Finset.univ.prod (fun i : Fin n => MvPolynomial.X i)

theorem s38_laurent_differential
    (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsLocalization (Submonoid.powers
      (allCoordinateProduct (k := k) (n := n))) B] :
    S38 (D (k := k) B) := by
  apply s38_localized_differential
    (Submonoid.powers (allCoordinateProduct (k := k) (n := n))) B
  intro d hd
  exact Stafford38.universalStatement (k := k) n d hd


theorem s38_principal_open_differential
    (f : A (k := k) (n := n))
    (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsLocalization (Submonoid.powers f) B] :
    S38 (D (k := k) B) :=
  s38_unconditional_localized_differential (Submonoid.powers f) B

theorem s38_partial_laurent_differential
    (J : Finset (Fin n)) (B : Type u) [CommRing B]
    [Algebra (A (k := k) (n := n)) B] [Algebra k B]
    [IsScalarTower k (A (k := k) (n := n)) B]
    [IsLocalization (Submonoid.powers
      (J.prod (fun i => (MvPolynomial.X i : A (k := k) (n := n))))) B] :
    S38 (D (k := k) B) :=
  s38_unconditional_localized_differential
    (Submonoid.powers (J.prod (fun i =>
      (MvPolynomial.X i : A (k := k) (n := n))))) B


end
end Stafford38.LocalizedDifferentialCorollaries
