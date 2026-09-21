/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Hensel Lemma -/
namespace ValuationTheory

/-!
# Factorization-shaped Hensel consequences

Mathlib exposes the simple-root form of Hensel's lemma.  The statements below
turn it into a linear-factor lifting API for a simple residual linear factor.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- The cofactor obtained by dividing by `X - C a` evaluates to the derivative
value at `a`.  This is the polynomial identity behind the simple-root
decomposition over the residual algebra. -/
theorem divByMonic_X_sub_C_eval_eq_derivative_eval
    {S : Type*} [CommRing S] (p : Polynomial S) (a : S) :
    (p /ₘ (Polynomial.X - Polynomial.C a)).eval a =
      p.derivative.eval a := by
  have h :=
    Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      p a
  have heval := congrArg (fun q : Polynomial S => q.eval a) h
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub] using
    heval

namespace HenselianDVF

open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} [Field K]

/-- A linear factor is coprime to any polynomial whose value at the root is a
unit.  This is the elementary Bezout step used in factorization-form Hensel
arguments. -/
theorem isCoprime_X_sub_C_of_isUnit_eval
    {R : Type u} [CommRing R] (q : Polynomial R) (a : R)
    (hq : IsUnit (q.eval a)) :
    IsCoprime (Polynomial.X - Polynomial.C a) q := by
  rcases Polynomial.X_sub_C_dvd_sub_C_eval (p := q) (a := a) with ⟨r, hr⟩
  refine ⟨-Polynomial.C hq.unit⁻¹.val * r, Polynomial.C hq.unit⁻¹.val, ?_⟩
  have hq_eq :
      q = (Polynomial.X - Polynomial.C a) * r + Polynomial.C (q.eval a) := by
    rw [← sub_eq_iff_eq_add]
    exact hr
  have hq_sub :
      q - (Polynomial.X - Polynomial.C a) * r = Polynomial.C (q.eval a) := by
    rw [← hr]
    ring
  calc
    -Polynomial.C ↑hq.unit⁻¹ * r * (Polynomial.X - Polynomial.C a) +
        Polynomial.C ↑hq.unit⁻¹ * q =
      Polynomial.C ↑hq.unit⁻¹ * (q - (Polynomial.X - Polynomial.C a) * r) := by
        ring
    _ = Polynomial.C ↑hq.unit⁻¹ * Polynomial.C (q.eval a) := by
        rw [hq_sub]
    _ = 1 := by
        rw [← Polynomial.C_mul]
        exact congrArg Polynomial.C hq.val_inv_mul

/-- If `f = (X - a) * q` and the derivative of `f` at `a` is a unit, then
the linear factor and the quotient are coprime.

This is the coprime-factor algebra bridge needed after a Hensel lift proves
that the lifted root remains simple. -/
theorem linearFactor_isCoprime_quotient_of_derivative_isUnit
    {R : Type u} [CommRing R] (f q : Polynomial R) (a : R)
    (hfactor : f = (Polynomial.X - Polynomial.C a) * q)
    (hderiv : IsUnit (f.derivative.eval a)) :
    IsCoprime (Polynomial.X - Polynomial.C a) q := by
  have hq_eval : f.derivative.eval a = q.eval a := by
    rw [hfactor, Polynomial.derivative_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.derivative_X_sub_C, Polynomial.eval_one,
      one_mul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, add_zero]
  exact isCoprime_X_sub_C_of_isUnit_eval q a (hq_eval ▸ hderiv)

variable (F : HenselianDVF.{u, v} K)

/-- A simple root in a fixed residue class is unique.

This is the uniqueness half used by residue-lift constructions: if two actual
roots have the same residue and one of them has unit derivative, then they are
equal. -/
theorem eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
    {f : Polynomial F.valuationSubring} {a b : F.valuationSubring}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : F.residueMap b = F.residueMap a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : Polynomial F.valuationSubring :=
    f /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor :
      (Polynomial.X - Polynomial.C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hq_eval :
      q.eval a = f.derivative.eval a := by
    simpa [q] using
      divByMonic_X_sub_C_eval_eq_derivative_eval (p := f) a
  have hq_unit_a : IsUnit (q.eval a) := by
    simpa [hq_eval] using hderiv
  have hq_residue :
      F.residueMap (q.eval b) = F.residueMap (q.eval a) := by
    calc
      F.residueMap (q.eval b) =
          (q.map F.residueMap).eval (F.residueMap b) := by
        exact (Polynomial.eval_map_apply (f := F.residueMap) (p := q) b).symm
      _ = (q.map F.residueMap).eval (F.residueMap a) := by
        rw [hres]
      _ = F.residueMap (q.eval a) := by
        exact Polynomial.eval_map_apply (f := F.residueMap) (p := q) a
  have hq_residue_ne : F.residueMap (q.eval b) ≠ 0 := by
    rw [hq_residue]
    exact (F.toDVF.residue_ne_zero_iff_isUnit (q.eval a)).2 hq_unit_a
  have hq_ne : q.eval b ≠ 0 := by
    intro hzero
    exact hq_residue_ne (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hb_eval :
        ((Polynomial.X - Polynomial.C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hb_eval
  have hsub : b - a = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hq_ne
  exact sub_eq_zero.mp hsub

/-- Hensel's lemma gives a linear factor lifting from a simple approximate root. -/
theorem exists_linear_factor_lift
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_lift_root_simple f hf a0 hroot hsimple with
    ⟨a, ha_root, ha_congruent⟩
  rcases (Polynomial.dvd_iff_isRoot.mpr ha_root) with ⟨q, hq⟩
  exact ⟨a, q, ha_root, ha_congruent, hq⟩

/-- The lifted linear factor is monic. -/
theorem exists_monic_linear_factor_lift
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        (Polynomial.X - Polynomial.C a).Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_linear_factor_lift f hf a0 hroot hsimple with
    ⟨a, q, ha_root, ha_congruent, hfactor⟩
  exact ⟨a, q, ha_root, ha_congruent, Polynomial.monic_X_sub_C a, hfactor⟩

/-- Hensel's lemma gives a monic linear factor whose quotient is also monic. -/
theorem exists_monic_linear_factor_lift_with_monic_quotient
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_monic_linear_factor_lift f hf a0 hroot hsimple with
    ⟨a, q, ha_root, ha_congruent, hlinear, hfactor⟩
  have hq : q.Monic := hlinear.of_mul_monic_left (hfactor ▸ hf)
  exact ⟨a, q, ha_root, ha_congruent, hlinear, hq, hfactor⟩

/-- Residue-field form of the lifted monic linear factor theorem.  Starting
from an actual simple root of the reduced polynomial over the residue field,
Hensel's lemma gives a root with the prescribed residue class, a monic lifted
linear factor, and a monic quotient. -/
theorem exists_monic_linear_factor_lift_of_residue_root
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : (f.derivative.map F.residueMap).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  obtain ⟨a0, ha0⟩ := F.toDVF.residue_surjective aBar
  have hroot_residue : F.residueMap (f.eval a0) = 0 := by
    have heval :
        (f.map F.residueMap).eval (F.residueMap a0) =
          F.residueMap (f.eval a0) := by
      exact Polynomial.eval_map_apply (f := F.residueMap) (p := f) a0
    rw [← heval, ha0]
    exact hroot
  have hroot_mem : f.eval a0 ∈ F.maximalIdeal := by
    simpa [HenselianDVF.residueMap, DVF.residueMap]
      using (IsLocalRing.residue_eq_zero_iff (f.eval a0)).1 hroot_residue
  have hderivative_residue :
      F.residueMap (f.derivative.eval a0) ≠ 0 := by
    have heval :
        (f.derivative.map F.residueMap).eval (F.residueMap a0) =
          F.residueMap (f.derivative.eval a0) := by
      exact Polynomial.eval_map_apply (f := F.residueMap)
        (p := f.derivative) a0
    rw [← heval, ha0]
    exact hsimple
  have hsimple_unit :
      IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0)) := by
    change IsUnit (F.residueMap (f.derivative.eval a0))
    exact isUnit_iff_ne_zero.mpr hderivative_residue
  rcases F.exists_monic_linear_factor_lift_with_monic_quotient
      f hf a0 hroot_mem hsimple_unit with
    ⟨a, q, ha_root, ha_congruent, hlinear, hq, hfactor⟩
  have ha_residue : F.residueMap a = aBar := by
    rw [← ha0]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) a a0).2 ha_congruent
  exact ⟨a, q, ha_root, ha_residue, hlinear, hq, hfactor⟩

/-- Natural reduced-polynomial form of the lifted monic linear factor theorem.
The simplicity condition is stated using the derivative of the reduced
polynomial itself. -/
theorem exists_monic_linear_factor_lift_of_reduced_simple_root
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : ((f.map F.residueMap).derivative).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  exact F.exists_monic_linear_factor_lift_of_residue_root
    f hf aBar hroot (by simpa [Polynomial.derivative_map] using hsimple)

/-- Reduced-factorization compatibility for the lifted monic linear factor.
The lifted factorization reduces to the original reduced linear factor
`X - aBar`.  This is the linear-factor compatibility input needed for the
later full factorization-form Hensel theorem. -/
theorem exists_monic_linear_factor_lift_of_reduced_simple_root_with_reduction
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : ((f.map F.residueMap).derivative).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q ∧
            (q.map F.residueMap).Monic ∧
              f.map F.residueMap =
                (Polynomial.X - Polynomial.C aBar) * q.map F.residueMap := by
  rcases F.exists_monic_linear_factor_lift_of_reduced_simple_root
      f hf aBar hroot hsimple with
    ⟨a, q, ha_root, ha_residue, hlinear, hq, hfactor⟩
  refine ⟨a, q, ha_root, ha_residue, hlinear, hq, hfactor,
    hq.map F.residueMap, ?_⟩
  calc
    f.map F.residueMap =
        (((Polynomial.X - Polynomial.C a) * q).map F.residueMap) := by
      rw [hfactor]
    _ = (Polynomial.X - Polynomial.C (F.residueMap a)) *
        q.map F.residueMap := by
      simp [Polynomial.map_mul, Polynomial.map_sub]
    _ = (Polynomial.X - Polynomial.C aBar) * q.map F.residueMap := by
      rw [ha_residue]

/-- A Hensel lift of a simple reduced root has a unit derivative at the lifted
root, so the lifted linear factor is coprime to the lifted quotient.

This is the first construction-level bridge from simple-root Hensel to the
coprime factorization form: the coprimeness is proved from the actual lifted
factorization and the nonzero reduced derivative, not assumed as extra data. -/
theorem exists_monic_linear_factor_lift_of_reduced_simple_root_with_coprime_quotient
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : ((f.map F.residueMap).derivative).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          IsUnit (f.derivative.eval a) ∧
            IsCoprime (Polynomial.X - Polynomial.C a) q ∧
              f = (Polynomial.X - Polynomial.C a) * q ∧
                (q.map F.residueMap).Monic ∧
                  f.map F.residueMap =
                    (Polynomial.X - Polynomial.C aBar) * q.map F.residueMap := by
  rcases F.exists_monic_linear_factor_lift_of_reduced_simple_root_with_reduction
      f hf aBar hroot hsimple with
    ⟨a, q, ha_root, ha_residue, hlinear, hq, hfactor, hqbar, hred⟩
  have hderiv_residue :
      F.residueMap (f.derivative.eval a) =
        ((f.map F.residueMap).derivative).eval aBar := by
    calc
      F.residueMap (f.derivative.eval a) =
          (f.derivative.map F.residueMap).eval (F.residueMap a) := by
        exact (Polynomial.eval_map_apply (f := F.residueMap)
          (p := f.derivative) a).symm
      _ = (f.derivative.map F.residueMap).eval aBar := by
        rw [ha_residue]
      _ = ((f.map F.residueMap).derivative).eval aBar := by
        rw [Polynomial.derivative_map]
  have hderiv_ne : F.residueMap (f.derivative.eval a) ≠ 0 := by
    rw [hderiv_residue]
    exact hsimple
  have hderiv_unit : IsUnit (f.derivative.eval a) :=
    (F.toDVF.residue_ne_zero_iff_isUnit (f.derivative.eval a)).1 hderiv_ne
  have hcoprime :
      IsCoprime (Polynomial.X - Polynomial.C a) q :=
    linearFactor_isCoprime_quotient_of_derivative_isUnit f q a hfactor hderiv_unit
  exact ⟨a, q, ha_root, ha_residue, hlinear, hq, hderiv_unit,
    hcoprime, hfactor, hqbar, hred⟩

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
