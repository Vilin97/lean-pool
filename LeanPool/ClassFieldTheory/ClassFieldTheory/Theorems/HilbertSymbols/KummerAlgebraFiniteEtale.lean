/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraFiniteFree
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.Away.Basic
/-!
# Finite étaleness of a Kummer algebra

The quotient by `X ^ n - a` is finite étale when the exponent is invertible in
the base field.  This includes reducible polynomials: the algebra need not be
a field.
-/

namespace ClassFieldTheory

open Polynomial

universe u

/-- The canonical Kummer algebra is finite étale when its exponent is a unit
in the base field. -/
theorem kummerAlgebra_finiteEtale
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K)) :
    Module.Finite K (KummerAlgebra K n a) ∧
      Algebra.Etale K (KummerAlgebra K n a) := by
  have hFinite : Module.Finite K (KummerAlgebra K n a) :=
    (kummerAlgebra_finiteFree K n a).1
  have hFormal : Algebra.FormallyEtale K (KummerAlgebra K n a) := by
    let f : K[X] := X ^ (n : ℕ) - C (a : K)
    change Algebra.FormallyEtale K (AdjoinRoot f)
    have hf : f.Monic :=
      Polynomial.monic_X_pow_sub_C (a : K) (Nat.ne_of_gt n.pos)
    have hrootPow : (AdjoinRoot.root f) ^ (n : ℕ) =
        AdjoinRoot.of f (a : K) := by
      change (AdjoinRoot.root (X ^ (n : ℕ) - C (a : K))) ^ (n : ℕ) =
        AdjoinRoot.of (X ^ (n : ℕ) - C (a : K)) (a : K)
      rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub,
        eval₂_C, eval₂_pow, eval₂_X]
    have hrootUnit : IsUnit (AdjoinRoot.root f) := by
      refine (isUnit_pow_iff n.ne_zero).mp ?_
      rw [hrootPow]
      exact a.isUnit.map (AdjoinRoot.of f)
    have hDerivativeFormula :
        aeval (AdjoinRoot.root f) f.derivative =
          algebraMap K (AdjoinRoot f) (n : K) *
            AdjoinRoot.root f ^ ((n : ℕ) - 1) := by
      dsimp [f]
      simp [Polynomial.derivative_X_pow]
    have hDerivative : IsUnit (aeval (AdjoinRoot.root f) f.derivative) := by
      rw [hDerivativeFormula]
      exact (hn.map (algebraMap K (AdjoinRoot f))).mul
        (hrootUnit.pow ((n : ℕ) - 1))
    have hmk : IsUnit (AdjoinRoot.mk f f.derivative) := by
      simpa only [AdjoinRoot.aeval_eq] using hDerivative
    let P : StandardEtalePair K :=
      { f := f
        monic_f := hf
        g := f.derivative
        cond := ⟨1, 0, 1, by
          simp only [mul_one, mul_zero, add_zero, pow_one]⟩ }
    have hP : IsUnit (AdjoinRoot.mk P.f P.g) := by
      change IsUnit (AdjoinRoot.mk f f.derivative)
      exact hmk
    let eUnit :
        AdjoinRoot P.f ≃ₐ[AdjoinRoot P.f]
          Localization.Away (AdjoinRoot.mk P.f P.g) :=
      IsLocalization.atUnit
        (AdjoinRoot P.f)
        (Localization.Away (AdjoinRoot.mk P.f P.g))
        (AdjoinRoot.mk P.f P.g) hP
    let e : P.Ring ≃ₐ[K] AdjoinRoot P.f :=
      P.equivAwayAdjoinRoot.trans (eUnit.symm.restrictScalars K)
    change Algebra.FormallyEtale K (AdjoinRoot P.f)
    exact Algebra.FormallyEtale.of_equiv e
  have hPresentation : Algebra.FinitePresentation K (KummerAlgebra K n a) := by
    change Algebra.FinitePresentation K
      (AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)))
    infer_instance
  exact ⟨hFinite, ⟨hFormal, hPresentation⟩⟩

end ClassFieldTheory
