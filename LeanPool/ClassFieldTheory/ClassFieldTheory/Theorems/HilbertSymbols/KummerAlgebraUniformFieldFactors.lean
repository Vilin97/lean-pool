/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraProductDecomposition
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.SplittingField.Construction
/-!
# Uniform field factors of a Kummer algebra

If the base field contains the `n`-th roots of unity, every field factor of
`K[X] / (X ^ n - a)` is a splitting field of the same polynomial. Thus all
factors in the finite product decomposition are isomorphic over the base.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

open Polynomial

universe u

private theorem isSplittingField_of_root_generated
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (a : Kˣ)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (β : L)
    (hpow : β ^ (n : ℕ) = algebraMap K L (a : K))
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    Polynomial.IsSplittingField K L
      (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)) := by
  apply isSplittingField_iff_intermediateField.mpr
  constructor
  · obtain ⟨ζ, hζ⟩ := hmu
    have hprimitive : IsPrimitiveRoot ζ (n : ℕ) :=
      (mem_primitiveRoots n.pos).mp hζ
    rw [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hprimitive.map_of_injective (algebraMap K L).injective) hpow
  · have hroot : β ∈
        (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)).rootSet L := by
      rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero n.pos (a : K)),
        aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, hpow, sub_self]
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact IntermediateField.subset_adjoin K _ hroot

/-- When `K` contains the `n`-th roots of unity, the root-generated field
factors of its Kummer algebra are pairwise isomorphic over `K`. -/
theorem kummerAlgebra_exists_algEquiv_pi_isomorphicFields
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ (I : Type u) (_ : Finite I) (E : I → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (e : KummerAlgebra K n a ≃ₐ[K] ∀ i, E i),
      (∀ i, Module.Finite K (E i) ∧ Algebra.IsSeparable K (E i) ∧
        ∃ β : E i,
          β = (e (AdjoinRoot.root
            (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)))) i ∧
          β ^ (n : ℕ) = algebraMap K (E i) (a : K) ∧
          IntermediateField.adjoin K {β} = ⊤) ∧
      ∀ i j, Nonempty (E i ≃ₐ[K] E j) := by
  obtain ⟨I, hI, E, hField, hAlgebra, e, hFactors⟩ :=
    kummerAlgebra_exists_algEquiv_pi_simpleFields K n a hn
  let : Finite I := hI
  let (i : I) : Field (E i) := hField i
  let (i : I) : Algebra K (E i) := hAlgebra i
  refine ⟨I, hI, E, hField, hAlgebra, e, hFactors, ?_⟩
  intro i j
  obtain ⟨_, _, βi, _, hPowi, hGeni⟩ := hFactors i
  obtain ⟨_, _, βj, _, hPowj, hGenj⟩ := hFactors j
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  have hSplitsi : Polynomial.IsSplittingField K (E i) p :=
    isSplittingField_of_root_generated K (E i) n a hmu βi hPowi hGeni
  have hSplitsj : Polynomial.IsSplittingField K (E j) p :=
    isSplittingField_of_root_generated K (E j) n a hmu βj hPowj hGenj
  let ei : E i ≃ₐ[K] p.SplittingField := by
    letI := hSplitsi
    exact Polynomial.IsSplittingField.algEquiv (E i) p
  let ej : E j ≃ₐ[K] p.SplittingField := by
    letI := hSplitsj
    exact Polynomial.IsSplittingField.algEquiv (E j) p
  exact ⟨ei.trans ej.symm⟩

end ClassFieldTheory
