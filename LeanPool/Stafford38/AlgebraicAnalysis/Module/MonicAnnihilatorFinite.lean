/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finiteness from a monic annihilator

A finite polynomial-ring module annihilated by a monic polynomial is finite
over the coefficient ring. This is the algebraic finiteness step for the
normal covariable; no characteristic-support assertion is assumed.
-/

namespace AlgebraicAnalysis.MonicAnnihilatorFinite

open Polynomial

theorem finite_of_monic_annihilator {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Module R[X] E]
    [IsScalarTower R R[X] E] [Module.Finite R[X] E]
    (g : R[X]) (hg : g.Monic) (hkill : ∀ z : E, g • z = 0) :
    Module.Finite R E := by
  have ht : Module.IsTorsionBySet R[X] E (Ideal.span {g}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact hkill
  let := ht.module
  let : IsScalarTower R[X] (R[X] ⧸ Ideal.span {g}) E :=
    ht.isScalarTower
  let : IsScalarTower R (R[X] ⧸ Ideal.span {g}) E :=
    ht.isScalarTower
  let : Module.Finite (R[X] ⧸ Ideal.span {g}) E :=
    Module.Finite.of_restrictScalars_finite R[X] (R[X] ⧸ Ideal.span {g}) E
  let := hg.finite_quotient
  exact Module.Finite.trans (R[X] ⧸ Ideal.span {g}) E

/-- A finite module killed by the polynomial variable is finite over the
coefficient ring. -/
theorem finite_of_variable_annihilates {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Module R[X] E]
    [IsScalarTower R R[X] E] [Module.Finite R[X] E]
    (hkill : ∀ z : E, (X : R[X]) • z = 0) : Module.Finite R E :=
  finite_of_monic_annihilator X monic_X hkill

/-- Both terms of the principal Koszul homology are finite over the
coefficient ring, although the ambient module need not be. -/
theorem finite_kernel_and_cokernel_variable {R E : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup E] [Module R E] [Module R[X] E]
    [IsScalarTower R R[X] E] [Module.Finite R[X] E] :
    Module.Finite R (LinearMap.ker (LinearMap.lsmul R[X] E X)) ∧
      Module.Finite R (E ⧸ LinearMap.range (LinearMap.lsmul R[X] E X)) := by
  let f : Module.End R[X] E := LinearMap.lsmul R[X] E X
  constructor
  · apply finite_of_variable_annihilates
    intro z
    apply Subtype.ext
    exact LinearMap.mem_ker.mp z.property
  · apply finite_of_variable_annihilates
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩

end AlgebraicAnalysis.MonicAnnihilatorFinite
