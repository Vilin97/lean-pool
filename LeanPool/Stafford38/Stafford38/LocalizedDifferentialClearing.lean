/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.LocalizedWeylAction
public import LeanPool.Stafford38.Stafford38.CoordinateDifferentialGeneration
public import LeanPool.Stafford38.Stafford38.LocalizedPolynomialCommutant


/-!
Clearing coefficient denominators in localized polynomial differential operators.
-/

@[expose] public section

namespace Stafford38.LocalizedDifferentialClearing

open Stafford
open Stafford38.DifferentialOperators
open Stafford38.LocalizedPolynomialDerivations
open Stafford38.LocalizedWeylAction
open Stafford38.LocalizedPolynomialCommutant
open Stafford38.CoordinateDifferentialGeneration
open Stafford38.WeylIteratedEquivalence

noncomputable section
universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable (S : Submonoid (MvPolynomial (Fin n) k))
variable (B : Type u) [CommRing B]
variable [Algebra (MvPolynomial (Fin n) k) B] [Algebra k B]
variable [IsScalarTower k (MvPolynomial (Fin n) k) B]
variable [IsLocalization S B]

/-- The polynomial coefficient algebra in the selected finite set of variables. -/
abbrev A := MvPolynomial (Fin n) k
/-- The algebra of differential operators on the localized coefficient algebra. -/
abbrev D := DifferentialOperators.algebra (k := k) (R := B)

/-- The endomorphism induced by a presented Weyl element on the localization. -/
def weylEnd (a : PresentedWeyl k n) : Module.End k B :=
  (localizedWeylAction S B a : Module.End k B)

/-- The localized coefficient-module span of the Weyl action endomorphisms. -/
def actionSpan : Submodule B (Module.End k B) :=
  Submodule.span B (Set.range (weylEnd S B))

omit [CharZero k] in
private theorem actionSpan_mem (a : PresentedWeyl k n) :
    weylEnd S B a ∈ actionSpan S B :=
  Submodule.subset_span ⟨a, rfl⟩

omit [CharZero k] in
private theorem actionSpan_smul_eq_multiplication (b : B) :
    b • weylEnd S B 1 = multiplication (k := k) b := by
  ext x
  simp [weylEnd, multiplication_apply]

omit [CharZero k] in
private theorem actionSpan_mul_right_generator
    (i : Fin n) (a : PresentedWeyl k n) :
    weylEnd S B a * (localizedPderiv S B i).toLinearMap ∈ actionSpan S B := by
  change (localizedWeylAction S B a : Module.End k B) *
      (differentialGenerator S B (.inr i) : Module.End k B) ∈ actionSpan S B
  rw [← localizedWeylAction_generator S B (.inr i)]
  have hm := congrArg (fun q : D (k := k) B =>
      (q : Module.End k B))
    ((localizedWeylAction S B).map_mul a
      (freeWeylGenerator (Matrix.J (Fin n) k) (.inr i)))
  have hm' : weylEnd S B
        (a * freeWeylGenerator (Matrix.J (Fin n) k) (.inr i)) =
      weylEnd S B a * weylEnd S B
        (freeWeylGenerator (Matrix.J (Fin n) k) (.inr i)) := by
    simp [weylEnd]
  change weylEnd S B a * weylEnd S B
      (freeWeylGenerator (Matrix.J (Fin n) k) (.inr i)) ∈ actionSpan S B
  rw [← hm']
  exact actionSpan_mem S B _

omit [CharZero k] in
private theorem actionSpan_right_stable
    (i : Fin n) {Q : Module.End k B} (hQ : Q ∈ actionSpan S B) :
    Q * (localizedPderiv S B i).toLinearMap ∈ actionSpan S B := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hQ
  · rintro Q ⟨a, rfl⟩
    exact actionSpan_mul_right_generator S B i a
  · simp
  · intro x y hx hy hxr hyr
    rw [add_mul]
    exact (actionSpan S B).add_mem hxr hyr
  · intro c x hx hxr
    rw [smul_mul_assoc]
    exact (actionSpan S B).smul_mem c hxr

theorem actual_differential_mem_actionSpan
    (P : Module.End k B)
    (hP : P ∈ D (k := k) B) : P ∈ actionSpan S B := by
  refine mem_submodule_of_coordinates
    (fun i : Fin n => algebraMap (A (k := k) (n := n)) B (MvPolynomial.X i))
    (fun i => localizedPderiv S B i)
    (H := (actionSpan S B).restrictScalars k)
    ?_ ?_ ?_ ?_ P hP
  · intro i j
    exact localizedPderiv_apply_algebraMap_X S B i j
  · intro Q hQ
    apply eq_multiplication_of_commute_coordinate B S Q
    intro i b
    have hi := LinearMap.congr_fun (hQ i) b
    exact sub_eq_zero.mp (by simpa [commutator_apply] using hi)
  · intro b
    rw [← actionSpan_smul_eq_multiplication S B b]
    exact (actionSpan S B).smul_mem b (actionSpan_mem S B 1)
  · intro i Q hQ
    exact actionSpan_right_stable S B i hQ

theorem localized_differential_mem_actionSpan
    (P : D (k := k) B) :
    (P : Module.End k B) ∈ actionSpan S B :=
  actual_differential_mem_actionSpan S B P (P.property)

omit [CharZero k] in
private theorem multiplication_algebraMap_in_action
    (f : A (k := k) (n := n)) :
    ∃ a : PresentedWeyl k n,
      weylEnd S B a = multiplication (algebraMap (A (k := k) (n := n)) B f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
      refine ⟨algebraMap k (PresentedWeyl k n) c, ?_⟩
      have hc : algebraMap (A (k := k) (n := n)) B (MvPolynomial.C c) =
          algebraMap k B c := by
        calc
          _ = algebraMap (A (k := k) (n := n)) B
              (algebraMap k (A (k := k) (n := n)) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k B c := by
            exact (IsScalarTower.algebraMap_apply k
              (A (k := k) (n := n)) B c).symm
      ext b
      simp [weylEnd, multiplication_apply, Algebra.smul_def, hc]
  | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      have hadd : weylEnd S B (a + b) = weylEnd S B a + weylEnd S B b := by
        simp [weylEnd]
      rw [hadd, ha, hb]
      ext z
      simp [multiplication_apply]
      ring
  | mul_X f i hf =>
      obtain ⟨a, ha⟩ := hf
      let Xweyl := freeWeylGenerator (Matrix.J (Fin n) k) (.inl i)
      refine ⟨Xweyl * a, ?_⟩
      have hX : weylEnd S B Xweyl =
          multiplication (algebraMap (A (k := k) (n := n)) B
            (MvPolynomial.X i)) := by
        ext z
        simp [Xweyl, weylEnd, differentialGenerator, coordinateEnd,
          multiplication_apply]
      have hmul := congrArg (fun q : D (k := k) B => (q : Module.End k B))
        ((localizedWeylAction S B).map_mul Xweyl a)
      rw [show weylEnd S B (Xweyl * a) = weylEnd S B Xweyl * weylEnd S B a by
        simp [weylEnd]]
      rw [hX, ha]
      ext z
      simp [multiplication_apply, Module.End.mul_apply, map_mul, mul_assoc]
      ring

/-- A common denominator on the left clears every intrinsic differential
operator on a localization of a polynomial ring. -/
theorem actual_differential_left_denominator_clearing
    (P : Module.End k B) (hP : P ∈ D (k := k) B) :
    ∃ s : S, ∃ a : PresentedWeyl k n,
      multiplication (algebraMap (A (k := k) (n := n)) B (s : A)) * P =
        weylEnd S B a := by
  have hspan := actual_differential_mem_actionSpan S B P hP
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · rintro Q ⟨a, rfl⟩
    refine ⟨1, a, ?_⟩
    ext z
    simp [multiplication_apply, Module.End.mul_apply]
  · refine ⟨1, 0, ?_⟩
    ext z
    simp [ weylEnd]
  · intro Q T hQ hT hcQ hcT
    obtain ⟨s, a, ha⟩ := hcQ
    obtain ⟨t, b, hb⟩ := hcT
    obtain ⟨pt, hpt⟩ := multiplication_algebraMap_in_action S B (t : A)
    obtain ⟨ps, hps⟩ := multiplication_algebraMap_in_action S B (s : A)
    refine ⟨s * t, pt * a + ps * b, ?_⟩
    have hact_mul (c d : PresentedWeyl k n) :
        weylEnd S B (c * d) = weylEnd S B c * weylEnd S B d := by
      have h := congrArg (fun q : D (k := k) B => (q : Module.End k B))
        ((localizedWeylAction S B).map_mul c d)
      simp [weylEnd]
    have hact_add (c d : PresentedWeyl k n) :
        weylEnd S B (c + d) = weylEnd S B c + weylEnd S B d := by
      simp [weylEnd]
    rw [hact_add, hact_mul, hact_mul, hpt, hps, ← ha, ← hb]
    ext z
    simp [multiplication_apply, Module.End.mul_apply, map_mul]
    ring
  · intro c Q hQ hcQ
    obtain ⟨s, a, ha⟩ := hcQ
    obtain ⟨⟨r, u⟩, hu⟩ := IsLocalization.surj S c
    obtain ⟨pr, hpr⟩ := multiplication_algebraMap_in_action S B r
    refine ⟨u * s, pr * a, ?_⟩
    have hact_mul : weylEnd S B (pr * a) =
        weylEnd S B pr * weylEnd S B a := by
      have h := congrArg (fun q : D (k := k) B => (q : Module.End k B))
        ((localizedWeylAction S B).map_mul pr a)
      simp [weylEnd]
    rw [hact_mul, hpr, ← ha]
    ext z
    simp only [Module.End.mul_apply, multiplication_apply, LinearMap.smul_apply,
      Algebra.smul_def, Submonoid.coe_mul, map_mul]
    change algebraMap (MvPolynomial (Fin n) k) B (u : MvPolynomial (Fin n) k) *
        algebraMap (MvPolynomial (Fin n) k) B (s : MvPolynomial (Fin n) k) *
          (c * Q z) =
      algebraMap (MvPolynomial (Fin n) k) B r *
        (algebraMap (MvPolynomial (Fin n) k) B
          (s : MvPolynomial (Fin n) k) * Q z)
    rw [← hu]
    ring

theorem localized_differential_left_denominator_clearing
    (P : D (k := k) B) :
    ∃ s : S, ∃ a : PresentedWeyl k n,
      multiplication (algebraMap (A (k := k) (n := n)) B (s : A)) *
          (P : Module.End k B) = weylEnd S B a :=
  actual_differential_left_denominator_clearing S B P P.property

end
end Stafford38.LocalizedDifferentialClearing
