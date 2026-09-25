/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraProductDecomposition
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace
/-!
# Norm across the finite product of Kummer field factors

The algebra norm of a possibly reducible Kummer algebra is the product of
the norms of its finite separable field factors. The factors may have
different degrees; no factorwise norm-image assertion is made.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u

/-- For an invertible exponent, the canonical Kummer algebra has a finite
separable field-product decomposition whose algebra norm is the product of
the norms of its coordinates. -/
theorem kummerAlgebra_exists_normProductDecomposition
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K)) :
    ∃ (I : Type u) (_ : Fintype I) (E : I → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (e : KummerAlgebra K n a ≃ₐ[K] ∀ i, E i),
      (∀ i, Module.Finite K (E i) ∧ Algebra.IsSeparable K (E i)) ∧
      ∀ z : KummerAlgebra K n a,
        Algebra.norm K z = ∏ i, Algebra.norm K (e z i) := by
  classical
  obtain ⟨I, hI, E, hField, hAlgebra, e, hFactors⟩ :=
    kummerAlgebra_exists_algEquiv_pi_simpleFields K n a hn
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (E i) := hField i
  let (i : I) : Algebra K (E i) := hAlgebra i
  let (i : I) : Module.Finite K (E i) := (hFactors i).1
  refine ⟨I, Fintype.ofFinite I, E, hField, hAlgebra, e, ?_, ?_⟩
  · intro i
    exact ⟨(hFactors i).1, (hFactors i).2.1⟩
  · intro z
    calc
      Algebra.norm K z = Algebra.norm K (e z) :=
        (Algebra.norm_eq_of_algEquiv e z).symm
      _ = ∏ i, Algebra.norm K (e z i) :=
        ValuationTheory.Completion.algebra_norm_pi_apply E (e z)

end ClassFieldTheory
