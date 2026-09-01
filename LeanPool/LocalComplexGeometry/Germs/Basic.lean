/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Germs
import Mathlib.Topology.Germ
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Holomorphic function germs at the origin

This file defines the local analytic ring as the subring of Mathlib's
neighbourhood-function germs which have an analytic representative.  It uses
the same `Filter.Germ` model and `AnalyticAt` predicate as the pinned WPT
project.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- The complex vector space `ℂⁿ`. -/
abbrev ComplexEuclidean (n : ℕ) := Fin n → ℂ

/-- The ambient ring of all function germs at the origin of `ℂⁿ`. -/
abbrev FunctionGerm (n : ℕ) :=
  Filter.Germ (𝓝 (0 : ComplexEuclidean n)) ℂ

/-- Function germs which have a representative analytic at the origin. -/
def holomorphicGermSubring (n : ℕ) : Subring (FunctionGerm n) where
  carrier := {φ | ∃ f : ComplexEuclidean n → ℂ,
    AnalyticAt ℂ f 0 ∧ (f : FunctionGerm n) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, by simp⟩
  mul_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, by simp⟩
  neg_mem' := by
    rintro φ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, by simp⟩

/-- The commutative ring `𝒪_{ℂⁿ,0}` of holomorphic germs at the origin. -/
abbrev HolomorphicGerm (n : ℕ) := holomorphicGermSubring n

/-- Pass from an analytic representative to its holomorphic germ. -/
def HolomorphicGerm.ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) : HolomorphicGerm n :=
  ⟨(f : FunctionGerm n), ⟨f, hf, rfl⟩⟩

@[simp]
theorem HolomorphicGerm.coe_ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ((HolomorphicGerm.ofFunction f hf : HolomorphicGerm n) : FunctionGerm n) = f :=
  rfl

/-- Every holomorphic germ has an analytic representative. -/
theorem HolomorphicGerm.exists_rep {n : ℕ} (φ : HolomorphicGerm n) :
    ∃ f : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ f 0 ∧ (f : FunctionGerm n) = φ :=
  φ.property

/-- Evaluation at the origin, as a ring homomorphism. -/
def evalAtOriginHom (n : ℕ) : HolomorphicGerm n →+* ℂ :=
  (Filter.Germ.valueRingHom : FunctionGerm n →+* ℂ).comp
    (holomorphicGermSubring n).subtype

/-- Evaluation of a holomorphic germ at the origin. -/
abbrev evalAtOrigin {n : ℕ} (φ : HolomorphicGerm n) : ℂ :=
  evalAtOriginHom n φ

@[simp]
theorem evalAtOrigin_ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    evalAtOrigin (HolomorphicGerm.ofFunction f hf) = f 0 :=
  rfl

instance holomorphicGerm_nontrivial (n : ℕ) : Nontrivial (HolomorphicGerm n) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact (zero_ne_one : (0 : ℂ) ≠ 1)
    (by simpa using congrArg (evalAtOriginHom n) h)

/-- A holomorphic germ is a unit exactly when its value at the origin is nonzero. -/
theorem holomorphicGerm_isUnit_iff {n : ℕ} (φ : HolomorphicGerm n) :
    IsUnit φ ↔ evalAtOrigin φ ≠ 0 := by
  constructor
  · intro hφ
    exact isUnit_iff_ne_zero.mp (hφ.map (evalAtOriginHom n))
  · intro hφ0
    obtain ⟨f, hf, hrep⟩ := φ.property
    have hf0 : f 0 ≠ 0 := by
      change Filter.Germ.value (φ : FunctionGerm n) ≠ 0 at hφ0
      rw [← hrep] at hφ0
      simpa using hφ0
    let ψ : HolomorphicGerm n :=
      ⟨((f⁻¹ : ComplexEuclidean n → ℂ) : FunctionGerm n),
        ⟨(f⁻¹ : ComplexEuclidean n → ℂ), hf.inv hf0, rfl⟩⟩
    have hne : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean n), f x ≠ 0 :=
      hf.continuousAt.eventually_ne hf0
    have hmul : φ * ψ = 1 := by
      apply Subtype.ext
      change (φ : FunctionGerm n) *
        ((f⁻¹ : ComplexEuclidean n → ℂ) : FunctionGerm n) = 1
      rw [← hrep, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hne] with x hx
      exact mul_inv_cancel₀ hx
    have hmul' : ψ * φ = 1 := by
      rw [mul_comm, hmul]
    exact ⟨⟨φ, ψ, hmul, hmul'⟩, rfl⟩

/-- The holomorphic germ ring is local. -/
theorem holomorphicGerm_isLocalRing (n : ℕ) : IsLocalRing (HolomorphicGerm n) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro φ
  by_cases hφ : evalAtOrigin φ = 0
  · right
    apply (holomorphicGerm_isUnit_iff (1 - φ)).2
    simp [hφ]
  · exact Or.inl ((holomorphicGerm_isUnit_iff φ).2 hφ)

instance holomorphicGerm_instIsLocalRing (n : ℕ) : IsLocalRing (HolomorphicGerm n) :=
  holomorphicGerm_isLocalRing n

/-- The maximal ideal consists exactly of germs vanishing at the origin. -/
theorem holomorphicGerm_maximalIdeal (n : ℕ) :
    IsLocalRing.maximalIdeal (HolomorphicGerm n) =
      Ideal.comap (evalAtOriginHom n) ⊥ := by
  ext φ
  rw [IsLocalRing.mem_maximalIdeal]
  simp only [mem_nonunits_iff, Ideal.mem_comap, Ideal.mem_bot]
  simpa only [not_ne_iff] using not_congr (holomorphicGerm_isUnit_iff φ)

end

end LocalComplexGeometry
