/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Definitions
/-!
# The maximal unramified subextension

Let `L/K` be an algebraic valued extension.  Its maximal unramified
subextension is the compositum, inside `L`, of all unramified subextensions.
Since the finite unramified-extension definition defines an arbitrary unramified extension as a
  union of
finite unramified subextensions, this compositum is the supremum of the finite
unramified intermediate fields.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

section MaximalUnramifiedSubextension

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The finite unramified intermediate fields occurring in the finite unramified-extension
definition. -/
def finiteUnramifiedSubextensions
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    Set (IntermediateField K L) :=
  {E | FiniteUnramifiedSubextension v w hExt E}

@[simp]
theorem mem_finiteUnramifiedSubextensions_iff
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L} :
    E ∈ finiteUnramifiedSubextensions v w hExt ↔
      FiniteUnramifiedSubextension v w hExt E :=
  Iff.rfl

/-- The maximal unramified
subextension `T/K` of `L/K`.

The supremum is the field compositum.  Indexing by finite unramified
subextensions is literal the finite unramified-extension definition: every arbitrary unramified
subextension is their union. -/
def maximalUnramifiedSubextension
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    IntermediateField K L :=
  sSup (finiteUnramifiedSubextensions v w hExt)

/-- Every finite unramified subextension is contained in `T`. -/
theorem finiteUnramifiedSubextension_le_maximal
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L}
    (hE : FiniteUnramifiedSubextension v w hExt E) :
    E ≤ maximalUnramifiedSubextension v w hExt := by
  apply le_sSup
  exact hE

/-- `T` is the least intermediate field containing every finite unramified
subextension. -/
theorem maximalUnramifiedSubextension_le
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {M : IntermediateField K L}
    (hM : ∀ E : IntermediateField K L,
      FiniteUnramifiedSubextension v w hExt E → E ≤ M) :
    maximalUnramifiedSubextension v w hExt ≤ M := by
  apply sSup_le
  intro E hE
  exact hM E hE

/-- The least-upper-bound characterization of the maximal-unramified-subextension definition. -/
theorem maximalUnramifiedSubextension_le_iff
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {M : IntermediateField K L} :
    maximalUnramifiedSubextension v w hExt ≤ M ↔
      ∀ E : IntermediateField K L,
        FiniteUnramifiedSubextension v w hExt E → E ≤ M := by
  constructor
  · intro h E hE
    exact (finiteUnramifiedSubextension_le_maximal v w hExt hE).trans h
  · exact maximalUnramifiedSubextension_le v w hExt

end MaximalUnramifiedSubextension

end Valuations
end AlgebraicNumberTheory

end
