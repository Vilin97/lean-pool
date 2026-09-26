/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Algebra.Module.ZMod

/-!
# Finite-field characters as linear functionals

Restricting a character to scalar multiples of a vector and using the
one-dimensional character equivalence recovers its finite-field linear
functional.  This gives the exact normalization needed for geometric sums.
-/

@[expose] public section

namespace EGZ.Expansion

variable {p d : ℕ} [NeZero p]

/-- The scalar additive character obtained by restricting a vector-space character to
multiples of `a`. -/
noncomputable def scalarCharacter (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d) :
    AddChar (ZMod p) ℂ :=
  χ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod p) (FpCoord p d) a).toAddMonoidHom

omit [NeZero p] in
@[simp] theorem scalarCharacter_apply (χ : AddChar (FpCoord p d) ℂ)
    (a : FpCoord p d) (z : ZMod p) : scalarCharacter χ a z = χ (z • a) := rfl

/-- The additive finite-field logarithm of a complex additive character. -/
noncomputable def characterLog (χ : AddChar (FpCoord p d) ℂ) :
    FpCoord p d →+ ZMod p where
  toFun a := AddChar.zmodAddEquiv.symm (scalarCharacter χ a)
  map_zero' := by
    apply AddChar.zmodAddEquiv.injective
    simp only [AddEquiv.apply_symm_apply, map_zero]
    ext z
    simp
  map_add' a b := by
    apply AddChar.zmodAddEquiv.injective
    simp only [map_add, AddEquiv.apply_symm_apply]
    ext z
    simp [smul_add, AddChar.map_add_eq_mul]

/-- The finite-field linear functional corresponding to a complex additive character. -/
noncomputable def characterLinear (χ : AddChar (FpCoord p d) ℂ) :
    FpCoord p d →ₗ[ZMod p] ZMod p := (characterLog χ).toZModLinearMap p

theorem characterLinear_spec (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d) :
    AddChar.zmodAddEquiv (characterLinear χ a) = scalarCharacter χ a :=
  AddEquiv.apply_symm_apply _ _

theorem characterLinear_eval (χ : AddChar (FpCoord p d) ℂ) (a : FpCoord p d)
    (n : ℕ) : (AddChar.zmodAddEquiv (characterLinear χ a)) (n : ZMod p) = χ (n • a) := by
  rw [characterLinear_spec, scalarCharacter_apply]
  congr 1
  ext i
  simp [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]

theorem characterLinear_ne_zero {χ : AddChar (FpCoord p d) ℂ} (hχ : χ ≠ 0) :
    characterLinear χ ≠ 0 := by
  intro hz
  apply hχ
  ext a
  have hh := characterLinear_eval χ a 1
  rw [hz, LinearMap.zero_apply, map_zero] at hh
  simpa using hh.symm

end EGZ.Expansion
