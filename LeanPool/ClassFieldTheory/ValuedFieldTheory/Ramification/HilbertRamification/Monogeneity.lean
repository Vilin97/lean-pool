/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.HenselLemma
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Polynomial
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
/-!
# Monogeneity over a noncomplete discretely valued field

This file proves the algebraic, noncomplete form of the monogeneity argument
used in the monogenic integral-generator theorem.  The proof uses the finite integral
closure supplied by unique extension, a primitive residue element, the
representative adjustment , and Nakayama's lemma.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
namespace Higher

open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A local injection of DVRs maps the source maximal ideal to the power of
the target maximal ideal indexed by its ramification index. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx_dvf :
    Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
        base.maximalIdeal =
      target.maximalIdeal ^
        Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal := by
  let i := algebraMap base.valuationSubring target.valuationSubring
  let p := base.maximalIdeal
  let P := target.maximalIdeal
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply (algebraMap K L).injective
    exact congrArg Subtype.val hab
  have hp0 : p ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field base.valuationSubring
  have hmap0 : Ideal.map i p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hi).not.mpr hp0
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, hm⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hpi
  have hmapPow : Ideal.map i p = P ^ m := by
    rw [hm, show P = IsLocalRing.maximalIdeal target.valuationSubring from rfl,
      hpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map i p ≤ P ^ (m + 1) := by
    rw [hmapPow]
    exact not_le_of_gt
      (Ideal.pow_succ_lt_pow
        (IsDiscreteValuationRing.not_a_field target.valuationSubring) m)
  have he : Ideal.ramificationIdx' p P = m :=
    Ideal.ramificationIdx'_spec (by rw [hmapPow]) hnot
  change Ideal.map i p = P ^ Ideal.ramificationIdx' p P
  rw [he]
  exact hmapPow

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Module finiteness of the valuation-ring extension implies finiteness of
the residue-field extension, without completeness. -/
theorem residueField_finiteDimensional_of_moduleFinite_dvf
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional base.residueField target.residueField := by
  refine FiniteDimensional.of_finrank_pos
    (K := base.residueField) (V := target.residueField) ?_
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_liesOver_of_hasExtension
      (L := L) base.valuation target.valuation
  change 0 < Module.finrank
    (base.valuationSubring ⧸ base.maximalIdeal)
    (target.valuationSubring ⧸ target.maximalIdeal)
  have h := target.maximalIdeal.inertiaDeg_pos base.valuationSubring
  rw [Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
  exact h

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Lift a residue polynomial coefficientwise to the base valuation ring. -/
theorem exists_base_polynomial_lift_residue_eq_dvf
    (fbar : base.residueField[X]) :
    ∃ P : base.valuationSubring[X], P.map base.residueMap = fbar :=
  Polynomial.map_surjective base.residueMap base.residue_surjective fbar

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Reduction after extension of coefficients agrees with extension after
reduction. -/
theorem base_polynomial_lift_target_reduction_eq_dvf
    {P : base.valuationSubring[X]} {fbar : base.residueField[X]}
    (hP : P.map base.residueMap = fbar) :
    (P.map (algebraMap base.valuationSubring target.valuationSubring)).map
        target.residueMap =
      fbar.map (algebraMap base.residueField target.residueField) := by
  rw [← hP]
  ext k
  rw [algebraMap_eq_map_algebraMap]
  simp only [Polynomial.coeff_map]
  exact
    (IsLocalRing.ResidueField.map_residue
      (algebraMap base.valuationSubring target.valuationSubring)
      (P.coeff k)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A reduced polynomial root is an actual value in the maximal ideal. -/
theorem polynomial_eval_mem_maximalIdeal_of_reduced_eval_eq_zero_dvf
    {P : Polynomial target.valuationSubring} {a : target.valuationSubring}
    (hroot : (P.map target.residueMap).eval (target.residueMap a) = 0) :
    P.eval a ∈ target.maximalIdeal := by
  rw [← target.residue_eq_zero_iff]
  calc
    target.residueMap (P.eval a) =
        (P.map target.residueMap).eval (target.residueMap a) := by
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap) (p := P) a).symm
    _ = 0 := hroot

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A nonzero reduced derivative lifts to a unit derivative. -/
theorem polynomial_derivative_eval_isUnit_of_reduced_ne_zero_dvf
    {P : Polynomial target.valuationSubring} {a : target.valuationSubring}
    (hsimple :
      ((P.map target.residueMap).derivative).eval
        (target.residueMap a) ≠ 0) :
    IsUnit (P.derivative.eval a) := by
  apply (target.residue_ne_zero_iff_isUnit (P.derivative.eval a)).1
  calc
    target.residueMap (P.derivative.eval a) =
        (P.derivative.map target.residueMap).eval
          (target.residueMap a) := by
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap) (p := P.derivative) a).symm
    _ = ((P.map target.residueMap).derivative).eval
          (target.residueMap a) := by
      rw [Polynomial.derivative_map]
    _ ≠ 0 := hsimple

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If a polynomial value is already in the square of the maximal ideal and
the derivative is a unit, adding a uniformizer to the argument makes the
polynomial value a uniformizer. -/
theorem polynomial_eval_add_uniformizer_isUniformizer_dvf
    {P : Polynomial target.valuationSubring}
    {a pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hdeep : P.eval a ∈ target.maximalIdeal ^ 2)
    (hderiv : IsUnit (P.derivative.eval a)) :
    target.valuation.IsUniformizer
      ((P.eval (a + pi) : target.valuationSubring) : L) := by
  let q : Polynomial target.valuationSubring :=
    P /ₘ (Polynomial.X - Polynomial.C a)
  have hdecomp :
      P = Polynomial.C (P.eval a) +
        (Polynomial.X - Polynomial.C a) * q := by
    dsimp [q]
    calc
      P = P %ₘ (Polynomial.X - Polynomial.C a) +
          (Polynomial.X - Polynomial.C a) *
            (P /ₘ (Polynomial.X - Polynomial.C a)) :=
        (Polynomial.modByMonic_add_div P
          (Polynomial.X - Polynomial.C a)).symm
      _ = Polynomial.C (P.eval a) +
          (Polynomial.X - Polynomial.C a) *
            (P /ₘ (Polynomial.X - Polynomial.C a)) := by
        rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
  have hEval :
      P.eval (a + pi) = P.eval a + pi * q.eval (a + pi) := by
    rw [hdecomp]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub]
  have hqEval : q.eval a = P.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval
        (p := P) a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hpiMem : pi ∈ target.maximalIdeal :=
    target.uniformizer_mem_maximalIdeal hpi
  have hPMem : P.eval (a + pi) ∈ target.maximalIdeal := by
    have haMem : P.eval a ∈ target.maximalIdeal := by
      simpa using
        Ideal.pow_le_pow_right (show 1 ≤ 2 by norm_num) hdeep
    rw [hEval]
    exact Ideal.add_mem _ haMem
      (Ideal.mul_mem_right (q.eval (a + pi)) target.maximalIdeal hpiMem)
  have hqdiff :
      q.eval (a + pi) - q.eval a ∈ target.maximalIdeal := by
    have harg : (a + pi) - a ∈ target.maximalIdeal := by
      simpa using hpiMem
    simpa using
      polynomial_eval₂_sub_mem_of_sub_mem
        (f := RingHom.id target.valuationSubring)
        (I := target.maximalIdeal)
        (x := a + pi) (y := a) harg q
  have hpiqdiff :
      pi * (q.eval (a + pi) - q.eval a) ∈ target.maximalIdeal ^ 2 := by
    simpa [pow_two] using
      (Ideal.mul_mem_mul hpiMem hqdiff :
        pi * (q.eval (a + pi) - q.eval a) ∈
          target.maximalIdeal * target.maximalIdeal)
  have herr :
      P.eval (a + pi) - pi * q.eval a ∈ target.maximalIdeal ^ 2 := by
    have hre :
        P.eval (a + pi) - pi * q.eval a =
          P.eval a + pi * (q.eval (a + pi) - q.eval a) := by
      rw [hEval]
      ring
    rw [hre]
    exact Ideal.add_mem _ hdeep hpiqdiff
  have hnot : P.eval (a + pi) ∉ target.maximalIdeal ^ 2 := by
    intro hsquare
    have hmain : pi * q.eval a ∈ target.maximalIdeal ^ 2 := by
      have hsub := Ideal.sub_mem _ hsquare herr
      convert hsub using 1
      ring
    exact target.uniformizer_mul_unit_not_mem_maximalIdeal_sq
      hpi hqUnit hmain
  exact target.isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
    hPMem hnot

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Representative adjustment from the proof of the monogenic integral-generator theorem. -/
theorem exists_residue_eq_polynomial_eval_isUniformizer_dvf
    {P : Polynomial target.valuationSubring}
    {a pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hP : P.eval a ∈ target.maximalIdeal)
    (hderiv : IsUnit (P.derivative.eval a)) :
    ∃ y : target.valuationSubring,
      target.residueMap y = target.residueMap a ∧
        target.valuation.IsUniformizer ((P.eval y : target.valuationSubring) : L) := by
  by_cases hdeep : P.eval a ∈ target.maximalIdeal ^ 2
  · refine ⟨a + pi, ?_, ?_⟩
    · rw [residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := target.valuationSubring)]
      simpa using target.uniformizer_mem_maximalIdeal hpi
    · exact polynomial_eval_add_uniformizer_isUniformizer_dvf
        (target := target) hpi hdeep hderiv
  · exact
      ⟨a, rfl,
        target.isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
          hP hdeep⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Reducing a base-polynomial evaluation agrees with evaluating the reduced
polynomial at the reduced argument. -/
theorem base_polynomial_aeval_residue_eq_dvf
    (P : base.valuationSubring[X]) (a : target.valuationSubring) :
    target.residueMap (Polynomial.aeval a P) =
      ((P.map base.residueMap).map
        (algebraMap base.residueField target.residueField)).eval
          (target.residueMap a) := by
  calc
    target.residueMap (Polynomial.aeval a P) =
        ((P.map
          (algebraMap base.valuationSubring target.valuationSubring)).map
            target.residueMap).eval (target.residueMap a) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap)
          (p := P.map
            (algebraMap base.valuationSubring target.valuationSubring))
          a).symm
    _ =
        ((P.map base.residueMap).map
          (algebraMap base.residueField target.residueField)).eval
            (target.residueMap a) := by
      rw [base_polynomial_lift_target_reduction_eq_dvf
        (base := base) (target := target)
        (P := P) (fbar := P.map base.residueMap) rfl]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every residue class is represented in the algebra generated by a lift of
a primitive residue element. -/
theorem exists_mem_adjoin_residue_eq_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (zbar : target.residueField) :
    ∃ z : target.valuationSubring,
      z ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        target.residueMap z = zbar := by
  have htop :
      Algebra.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : Subalgebra base.residueField target.residueField) :=
    Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (target.residueMap a)) hprim
  have hz :
      zbar ∈ Algebra.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) := by
    simp [htop]
  rcases Algebra.adjoin_mem_exists_aeval
      base.residueField (target.residueMap a) hz with
    ⟨fbar, hfbar⟩
  rcases exists_base_polynomial_lift_residue_eq_dvf
      (base := base) fbar with
    ⟨P, hP⟩
  refine ⟨Polynomial.aeval a P, ?_, ?_⟩
  · exact
      Polynomial.aeval_mem_adjoin_singleton
        (R := base.valuationSubring) (p := P) a
  · rw [base_polynomial_aeval_residue_eq_dvf
      (base := base) (target := target) P a, hP]
    simpa [Polynomial.aeval_def] using hfbar

omit [FiniteDimensional K L] [IsGalois K L] in
/-- First-order approximation by the algebra generated by a primitive residue
lift. -/
theorem exists_mem_adjoin_sub_mem_maximalIdeal_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (z : target.valuationSubring) :
    ∃ y : target.valuationSubring,
      y ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        z - y ∈ target.maximalIdeal := by
  rcases exists_mem_adjoin_residue_eq_dvf
      (base := base) (target := target) hprim
      (target.residueMap z) with
    ⟨y, hy, hyres⟩
  refine ⟨y, hy, ?_⟩
  rw [← target.residue_eq_zero_iff, map_sub, hyres, sub_self]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Approximation to arbitrary maximal-ideal order, using the fact that the
lifted minimal polynomial evaluates to a target uniformizer. -/
theorem exists_mem_adjoin_sub_mem_maximalIdeal_pow_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {P : base.valuationSubring[X]} {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (hpi :
      target.valuation.IsUniformizer
        (Polynomial.aeval a P : L))
    (n : ℕ) (z : target.valuationSubring) :
    ∃ y : target.valuationSubring,
      y ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        z - y ∈ target.maximalIdeal ^ n := by
  let pi : target.valuationSubring := Polynomial.aeval a P
  let A : Subalgebra base.valuationSubring target.valuationSubring :=
    Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring)
  have hpiA : pi ∈ A := by
    exact
      Polynomial.aeval_mem_adjoin_singleton
        (R := base.valuationSubring) (p := P) a
  induction n generalizing z with
  | zero =>
      refine ⟨0, A.zero_mem, ?_⟩
      simp
  | succ n ih =>
      rcases ih z with ⟨y, hyA, hdiff⟩
      have hdiv : pi ^ n ∣ z - y := by
        exact
          (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
            (pi := pi) (x := z - y) hpi n).1
            (by simpa [pi] using hdiff)
      rcases hdiv with ⟨b, hb⟩
      rcases exists_mem_adjoin_sub_mem_maximalIdeal_dvf
          (base := base) (target := target) (a := a) hprim b with
        ⟨c, hcA, hbc⟩
      refine ⟨y + pi ^ n * c, ?_, ?_⟩
      · exact A.add_mem hyA (A.mul_mem (A.pow_mem hpiA n) hcA)
      · have hpiPow : pi ^ n ∈ target.maximalIdeal ^ n := by
          exact
            (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
              (pi := pi) (x := pi ^ n) hpi n).2
              ⟨1, by rw [mul_one]⟩
        have hmul :
            pi ^ n * (b - c) ∈
              target.maximalIdeal ^ n * target.maximalIdeal :=
          Ideal.mul_mem_mul hpiPow hbc
        have hre : z - (y + pi ^ n * c) = pi ^ n * (b - c) := by
          calc
            z - (y + pi ^ n * c) = (z - y) - pi ^ n * c := by ring
            _ = pi ^ n * b - pi ^ n * c := by rw [hb]
            _ = pi ^ n * (b - c) := by ring
        rw [hre]
        simpa [pow_succ] using hmul

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A primitive residue lift can be adjusted so that its lifted minimal
polynomial value is a target uniformizer. -/
theorem exists_primitive_residue_lift_polynomial_uniformizer_dvf
    [FiniteDimensional base.residueField target.residueField]
    [Algebra.IsSeparable base.residueField target.residueField] :
    ∃ P : base.valuationSubring[X], ∃ a : target.valuationSubring,
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField) ∧
      target.valuation.IsUniformizer (Polynomial.aeval a P : L) ∧
      IsUnit
        ((P.map
          (algebraMap base.valuationSubring target.valuationSubring)).derivative.eval a) := by
  rcases Field.exists_primitive_element
      base.residueField target.residueField with
    ⟨xbar, hprim⟩
  have hsep : IsSeparable base.residueField xbar :=
    Algebra.IsSeparable.isSeparable base.residueField xbar
  let fbar : base.residueField[X] := minpoly base.residueField xbar
  rcases exists_base_polynomial_lift_residue_eq_dvf
      (base := base) fbar with
    ⟨P, hP⟩
  rcases target.residue_surjective xbar with ⟨a0, ha0⟩
  rcases target.exists_uniformizer with ⟨pi, hpi⟩
  let Q : target.valuationSubring[X] :=
    P.map (algebraMap base.valuationSubring target.valuationSubring)
  have hred :
      Q.map target.residueMap =
        fbar.map (algebraMap base.residueField target.residueField) := by
    exact base_polynomial_lift_target_reduction_eq_dvf
      (base := base) (target := target) hP
  have hrootbar :
      (fbar.map
        (algebraMap base.residueField target.residueField)).eval xbar = 0 := by
    dsimp [fbar]
    rw [Polynomial.eval_map_algebraMap]
    exact minpoly.aeval base.residueField xbar
  have hsimplebar :
      ((fbar.map
        (algebraMap base.residueField target.residueField)).derivative).eval
          xbar ≠ 0 := by
    dsimp [fbar]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero
      (minpoly.aeval base.residueField xbar)
  have hroot :
      (Q.map target.residueMap).eval (target.residueMap a0) = 0 := by
    rw [hred, ha0]
    exact hrootbar
  have hsimple :
      ((Q.map target.residueMap).derivative).eval
          (target.residueMap a0) ≠ 0 := by
    rw [hred, ha0]
    exact hsimplebar
  have hQmem : Q.eval a0 ∈ target.maximalIdeal :=
    polynomial_eval_mem_maximalIdeal_of_reduced_eval_eq_zero_dvf
      (target := target) hroot
  have hQderiv : IsUnit (Q.derivative.eval a0) :=
    polynomial_derivative_eval_isUnit_of_reduced_ne_zero_dvf
      (target := target) hsimple
  rcases exists_residue_eq_polynomial_eval_isUniformizer_dvf
      (target := target) (P := Q) (a := a0) (pi := pi)
      hpi hQmem hQderiv with
    ⟨a, hares, hauniform⟩
  have hsimpleA :
      ((Q.map target.residueMap).derivative).eval
          (target.residueMap a) ≠ 0 := by
    rw [hares]
    exact hsimple
  have hderivA : IsUnit (Q.derivative.eval a) :=
    polynomial_derivative_eval_isUnit_of_reduced_ne_zero_dvf
      (target := target) hsimpleA
  refine ⟨P, a, ?_, ?_, ?_⟩
  · rw [hares, ha0]
    exact hprim
  · have heval : Q.eval a = Polynomial.aeval a P := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [← heval]
    exact hauniform
  · exact hderivA

/-- The full noncomplete generator data used by the monogenic integral-generator theorem and the
first ramification-quotient homomorphism: a primitive residue lift, a lifted polynomial whose
value is a
uniformizer, its unit derivative, and generation of the entire target
valuation ring. -/
theorem exists_valuationSubring_generator_data_of_uniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    [Algebra.IsSeparable base.residueField target.residueField] :
    ∃ P : base.valuationSubring[X], ∃ a : target.valuationSubring,
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField) ∧
      target.valuation.IsUniformizer (Polynomial.aeval a P : L) ∧
      IsUnit
        ((P.map
          (algebraMap base.valuationSubring target.valuationSubring)).derivative.eval a) ∧
      Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) =
        (⊤ : Subalgebra base.valuationSubring target.valuationSubring) := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    target_valuationSubring_moduleFinite_of_uniqueExtension
      (base := base) (target := target) huniq
  let : FiniteDimensional base.residueField target.residueField :=
    residueField_finiteDimensional_of_moduleFinite_dvf
      (base := base) (target := target)
  rcases exists_primitive_residue_lift_polynomial_uniformizer_dvf
      (base := base) (target := target) with
    ⟨P, a, hprim, hpi, hderiv⟩
  let A : Subalgebra base.valuationSubring target.valuationSubring :=
    Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring)
  let e : ℕ :=
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal
  have hmap :
      Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
          base.maximalIdeal =
        target.maximalIdeal ^ e := by
    exact map_maximalIdeal_eq_pow_ramificationIdx_dvf
      (base := base) (target := target)
  have htop :
      (⊤ : Submodule base.valuationSubring target.valuationSubring) ≤
        A.toSubmodule ⊔
          base.maximalIdeal •
            (⊤ : Submodule base.valuationSubring target.valuationSubring) := by
    intro z _hz
    rcases exists_mem_adjoin_sub_mem_maximalIdeal_pow_dvf
        (base := base) (target := target) (P := P) (a := a)
        hprim hpi e z with
      ⟨y, hyA, hdiff⟩
    have hySub : y ∈ A.toSubmodule := by
      simpa [A] using hyA
    have hdiffMap :
        z - y ∈
          Ideal.map
            (algebraMap base.valuationSubring target.valuationSubring)
            base.maximalIdeal := by
      rw [hmap]
      exact hdiff
    have hdiffSmul :
        z - y ∈
          base.maximalIdeal •
            (⊤ : Submodule base.valuationSubring target.valuationSubring) := by
      simpa [Ideal.smul_top_eq_map] using hdiffMap
    have hsum :
        y + (z - y) ∈
          A.toSubmodule ⊔
            base.maximalIdeal •
              (⊤ : Submodule base.valuationSubring target.valuationSubring) :=
      Submodule.add_mem_sup hySub hdiffSmul
    have hsumEq : y + (z - y) = z := by ring
    rw [hsumEq] at hsum
    exact hsum
  have hjac :
      base.maximalIdeal ≤
        Ideal.jacobson (⊥ : Ideal base.valuationSubring) := by
    simpa using
      (IsLocalRing.maximalIdeal_le_jacobson
        (⊥ : Ideal base.valuationSubring))
  have hle :
      (⊤ : Submodule base.valuationSubring target.valuationSubring) ≤
        A.toSubmodule :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := base.maximalIdeal) (N := A.toSubmodule)
      (N' := (⊤ : Submodule base.valuationSubring target.valuationSubring))
      Module.Finite.fg_top hjac htop
  have hA : A.toSubmodule = ⊤ := le_antisymm le_top hle
  exact ⟨P, a, hprim, hpi, hderiv, Algebra.toSubmodule_eq_top.mp hA⟩

/-- A noncomplete monogeneity theorem for integral valuation rings. -/
theorem exists_valuationSubring_adjoin_eq_top_of_uniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    [Algebra.IsSeparable base.residueField target.residueField] :
    ∃ a : target.valuationSubring,
      Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) =
        (⊤ : Subalgebra base.valuationSubring target.valuationSubring) := by
  rcases exists_valuationSubring_generator_data_of_uniqueExtension
      (base := base) (target := target) huniq with
    ⟨_P, a, _hprim, _hpi, _hderiv, ha⟩
  exact ⟨a, ha⟩

end Higher
end RamificationTheory.HilbertRamification
