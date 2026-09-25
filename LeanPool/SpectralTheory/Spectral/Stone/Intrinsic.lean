/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.Stone.Theorem


/-!
# Intrinsic statement of Stone's generator relation

This file packages Stone's generator relation intrinsically, by the exact
punctured-neighborhood difference-quotient domain and limit, without exposing
the library's choice-based construction of the generator. It states Stone's
theorem in both directions: every strongly continuous unitary group has a
self-adjoint generator, and every self-adjoint operator generates such a
group.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- `U` has infinitesimal generator `A`: its domain is exactly the vectors
whose Stone difference quotient converges, and the limit is `A`. -/
def StrongContUnitary.Generates (U : StrongContUnitary E)
    (A : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ A.domain ↔
    ∃ y, Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) ∧
  ∀ x : A.domain, Filter.Tendsto
    (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
    (nhdsWithin 0 {0}ᶜ) (nhds (A x))

private theorem StrongContUnitary.generates_generator
    (U : StrongContUnitary E) : U.Generates U.generator :=
  ⟨U.mem_generator_domain_iff, U.tendsto_generator⟩

/-- Stone's theorem in both directions: strongly continuous one-parameter
unitary groups have self-adjoint generators, and every self-adjoint operator
generates such a group. -/
theorem stone_theorem_intrinsic :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by
  constructor
  · intro U
    exact ⟨U.generator, U.generator_isSelfAdjoint, U.generates_generator⟩
  · intro A hA
    let U := selfAdjointGeneratesUnitaryGroup A hA
    refine ⟨U, ?_⟩
    rw [← selfAdjoint_generates_unitary_group_generator A hA]
    exact U.generates_generator
