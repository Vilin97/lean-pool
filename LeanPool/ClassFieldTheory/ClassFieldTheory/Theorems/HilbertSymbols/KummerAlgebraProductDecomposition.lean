/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraFiniteEtale
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Field
/-!
# Product decomposition of a Kummer algebra

When the exponent is invertible, the possibly reducible algebra
`K[X] / (X ^ n - a)` is a finite product of finite separable simple field
extensions. This applies in particular when `a = 1`.
-/

namespace ClassFieldTheory

universe u

/-- A Kummer algebra with invertible exponent is a finite product of simple
finite separable field extensions. In each factor, the image of the canonical
root generates the field and has `n`-th power `a`. -/
theorem kummerAlgebra_exists_algEquiv_pi_simpleFields
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K)) :
    ∃ (I : Type u) (_ : Finite I) (E : I → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (e : KummerAlgebra K n a ≃ₐ[K] ∀ i, E i),
      ∀ i, Module.Finite K (E i) ∧ Algebra.IsSeparable K (E i) ∧
        ∃ β : E i,
          β = (e (AdjoinRoot.root
            (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)))) i ∧
          β ^ (n : ℕ) = algebraMap K (E i) (a : K) ∧
          IntermediateField.adjoin K {β} = ⊤ := by
  let : Algebra.Etale K (KummerAlgebra K n a) :=
    (kummerAlgebra_finiteEtale K n a hn).2
  obtain ⟨I, hI, E, hField, hAlgebra, e, hFactors⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (KummerAlgebra K n a)).mp inferInstance
  let : Finite I := hI
  let (i : I) : Field (E i) := hField i
  let (i : I) : Algebra K (E i) := hAlgebra i
  refine ⟨I, hI, E, hField, hAlgebra, e, ?_⟩
  intro i
  have hFinite : Module.Finite K (E i) := (hFactors i).1
  have hSeparable : Algebra.IsSeparable K (E i) := (hFactors i).2
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let A := KummerAlgebra K n a
  let φ : A →ₐ[K] E i := (Pi.evalAlgHom K E i).comp e.toAlgHom
  have hSurj : Function.Surjective φ :=
    (Function.surjective_eval i).comp e.surjective
  let β : E i := φ (AdjoinRoot.root p)
  have hPow : (AdjoinRoot.root p) ^ (n : ℕ) =
      algebraMap K A (a : K) := by
    change (AdjoinRoot.root
      (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))) ^ (n : ℕ) =
        AdjoinRoot.of (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)) (a : K)
    rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hβPow : β ^ (n : ℕ) = algebraMap K (E i) (a : K) := by
    calc
      β ^ (n : ℕ) = φ ((AdjoinRoot.root p) ^ (n : ℕ)) := by
        rw [map_pow]
      _ = φ (algebraMap K A (a : K)) := by rw [hPow]
      _ = algebraMap K (E i) (a : K) := φ.commutes (a : K)
  have hAlgGen : Algebra.adjoin K ({β} : Set (E i)) = ⊤ := by
    change Algebra.adjoin K ({φ (AdjoinRoot.root p)} : Set (E i)) = ⊤
    calc
      Algebra.adjoin K ({φ (AdjoinRoot.root p)} : Set (E i)) =
          (Algebra.adjoin K ({AdjoinRoot.root p} : Set A)).map φ :=
        (φ.map_adjoin_singleton (AdjoinRoot.root p)).symm
      _ = (⊤ : Subalgebra K A).map φ := by
        rw [AdjoinRoot.adjoinRoot_eq_top]
      _ = φ.range := Algebra.map_top φ
      _ = ⊤ := (AlgHom.range_eq_top φ).mpr hSurj
  exact ⟨hFinite, hSeparable, β, rfl, hβPow,
    IntermediateField.adjoin_eq_top_of_algebra K {β} hAlgGen⟩

end ClassFieldTheory
