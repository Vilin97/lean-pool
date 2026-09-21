/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary

/-!
# Strongly continuous unitary groups and their generators

This file defines strongly continuous one-parameter unitary groups and the
infinitesimal-generator relation between such a group and a partial operator,
via the Stone difference quotient.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A strongly continuous one-parameter unitary group. -/
structure StrongContUnitary (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  toFun : ℝ → (E →L[ℂ] E)
  isUnitary : ∀ t, toFun t ∈ unitary (E →L[ℂ] E)
  zero : toFun 0 = 1
  add : ∀ s t, toFun (s + t) = toFun s * toFun t
  stronglyContinuous : ∀ x, Continuous (fun t => toFun t x)

namespace StrongContUnitary

private noncomputable def differenceQuotient (U : StrongContUnitary E) (x : E) (t : ℝ) : E :=
  (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x)

private theorem differenceQuotient_zero (U : StrongContUnitary E) :
    differenceQuotient U (0 : E) = 0 := by
  funext t
  simp only [differenceQuotient, map_zero, sub_self, smul_zero, Pi.zero_apply]

private theorem differenceQuotient_add (U : StrongContUnitary E) (x y : E) :
    differenceQuotient U (x + y) =
      differenceQuotient U x + differenceQuotient U y := by
  funext t
  simp only [differenceQuotient, map_add, add_sub_add_comm, smul_add, Pi.add_apply]

private theorem differenceQuotient_smul (U : StrongContUnitary E) (c : ℂ) (x : E) :
    differenceQuotient U (c • x) = c • differenceQuotient U x := by
  funext t
  simp only [differenceQuotient, map_smul, ← smul_sub, smul_smul, Pi.smul_apply, mul_comm]

private def generatorDomain (U : StrongContUnitary E) : Submodule ℂ E where
  carrier := {x | ∃ y, Filter.Tendsto (differenceQuotient U x)
    (nhdsWithin 0 {0}ᶜ) (nhds y)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [differenceQuotient_zero]
    exact tendsto_const_nhds
  add_mem' {x y} hx hy := by
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    refine ⟨x' + y', ?_⟩
    rw [differenceQuotient_add]
    exact hx.add hy
  smul_mem' c x hx := by
    obtain ⟨x', hx⟩ := hx
    refine ⟨c • x', ?_⟩
    rw [differenceQuotient_smul]
    exact hx.const_smul c

private theorem mem_generatorDomain_iff (U : StrongContUnitary E) (x : E) :
    x ∈ generatorDomain U ↔
      ∃ y, Filter.Tendsto (differenceQuotient U x)
        (nhdsWithin 0 {0}ᶜ) (nhds y) :=
  Iff.rfl

private noncomputable def generatorLimit (U : StrongContUnitary E)
    (x : generatorDomain U) : E :=
  Classical.choose ((mem_generatorDomain_iff U x).mp x.property)

private theorem generatorLimit_spec (U : StrongContUnitary E)
    (x : generatorDomain U) :
    Filter.Tendsto (differenceQuotient U x)
      (nhdsWithin 0 {0}ᶜ) (nhds (generatorLimit U x)) :=
  Classical.choose_spec ((mem_generatorDomain_iff U x).mp x.property)

/-- The infinitesimal generator of a strongly continuous unitary group.

Its domain consists of the vectors for which `(U(t)x - x) / (i * t)`
converges as nonzero real `t` tends to zero. -/
noncomputable def generator
    (U : StrongContUnitary E) : E →ₗ.[ℂ] E :=
  { domain := generatorDomain U
    toFun :=
      { toFun := generatorLimit U
        map_add' := fun x y ↦ by
          apply tendsto_nhds_unique (generatorLimit_spec U (x + y))
          change Filter.Tendsto
            (differenceQuotient U ((x : E) + (y : E)))
            (nhdsWithin 0 {0}ᶜ)
            (nhds (generatorLimit U x + generatorLimit U y))
          rw [differenceQuotient_add]
          exact (generatorLimit_spec U x).add (generatorLimit_spec U y)
        map_smul' := fun c x ↦ by
          apply tendsto_nhds_unique (generatorLimit_spec U (c • x))
          change Filter.Tendsto
            (differenceQuotient U (c • (x : E)))
            (nhdsWithin 0 {0}ᶜ)
            (nhds (c • generatorLimit U x))
          rw [differenceQuotient_smul]
          exact (generatorLimit_spec U x).const_smul c } }

/-- Membership in the generator domain is convergence of the Stone difference quotient. -/
theorem mem_generator_domain_iff (U : StrongContUnitary E) (x : E) :
    x ∈ U.generator.domain ↔
      ∃ y, Filter.Tendsto
        (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
        (nhdsWithin 0 {0}ᶜ) (nhds y) :=
  Iff.rfl

/-- On its domain, the Stone difference quotient converges to the generator. -/
theorem tendsto_generator (U : StrongContUnitary E) (x : U.generator.domain) :
    Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
      (nhdsWithin 0 {0}ᶜ) (nhds (U.generator x)) :=
  generatorLimit_spec U x

end StrongContUnitary
