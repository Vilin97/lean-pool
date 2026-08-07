/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MeromorphicTrace.OrderMultiplicity
import LeanPool.JacobianDiffgeo.MappingDegree
import LeanPool.JacobianDiffgeo.ProjectiveLine.Sphere

/-!
# `homeoSphere_of_exists_simple_pole` (proper-map-degree, file 3 of 3)

Unit: proper-map-degree (`docs/design/proper-map-degree.md` §3.3). The meromorphic-function
version of degree-1 ⇒ homeomorphism: a single simple pole (no other poles) forces the induced
`ℙ¹`-valued map `RS.MTrace.toP1 f` to have degree exactly `1`, hence `X ≃ₜ ℙ¹ ≃ₜ S²`. This is
genus-zero-headline's forward-headline finisher: the caller (riemann-roch's genus-0
single-simple-pole existence result) supplies `φ` and the pole location `Q`, nothing else.
`φ ≠ 0`/nonconstancy of `φ` are *derived*, not required — `φ.ord Q = -1` alone already rules out
both. This file has zero dependency on `MeromorphicTrace/ArgumentPrinciple.lean`
(unlike `DivisorDegreeZero.lean`): the nonconstancy witness here is the explicit pole location `Q`
itself, cheaper than the general codiscrete-nonconstancy argument.

Main declaration: `RS.homeoSphere_of_exists_simple_pole`.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The meromorphic-function version of degree-1 ⇒ homeomorphism**: a single simple pole (no
other poles) forces the induced `ℙ¹`-valued map to have degree exactly `1`, hence `X` is
homeomorphic to `ℙ¹`, hence to `S²`. Consumed by `genus-zero-headline`'s forward direction. -/
theorem homeoSphere_of_exists_simple_pole (φ : ℳ X) (Q : X) (hpole : φ.ord Q = -1)
    (hreg : ∀ x, x ≠ Q → 0 ≤ φ.ord x) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  obtain ⟨f, hf, rfl⟩ := MeroGermOn.exists_rep φ
  have hpole' : RS.ordAtX f Q = -1 := by
    rwa [MeroGermOn.ord_mk isOpen_univ (mem_univ Q)] at hpole
  have hreg' : ∀ x, x ≠ Q → 0 ≤ RS.ordAtX f x := by
    intro x hx
    have := hreg x hx
    rwa [MeroGermOn.ord_mk isOpen_univ (mem_univ x)] at this
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (MTrace.toP1 f) := MTrace.toP1_contMDiff hf
  have hpoleneg : RS.ordAtX f Q < 0 := by rw [hpole']; decide
  have hFQ : MTrace.toP1 f Q = (∞ : OnePoint ℂ) := MTrace.toP1_eq_infty_iff.2 hpoleneg
  -- Nonconstancy: `Q` maps to `∞` but some other point (perfectness gives one) does not.
  have hne : ¬ ∃ c, ∀ x, MTrace.toP1 f x = c := by
    rintro ⟨c, hc⟩
    obtain ⟨x₀, hx₀⟩ := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := Q) (s := ({Q}ᶜ : Set X)))
    have h1 : MTrace.toP1 f x₀ = c := hc x₀
    have h2 : MTrace.toP1 f Q = c := hc Q
    rw [hFQ] at h2
    have h3 : MTrace.toP1 f x₀ ≠ (∞ : OnePoint ℂ) := by
      intro hcontra
      exact (not_lt.2 (hreg' x₀ hx₀)) (MTrace.toP1_eq_infty_iff.1 hcontra)
    exact h3 (h1.trans h2.symm)
  -- The fiber over `∞` is exactly `{Q}`.
  have hfibereq : MTrace.toP1 f ⁻¹' {(∞ : OnePoint ℂ)} = ({Q} : Set X) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxQ
      have hxlt : RS.ordAtX f x < 0 := MTrace.toP1_eq_infty_iff.1 hx
      exact absurd (hreg' x hxQ) (not_le.2 hxlt)
    · rintro rfl
      exact hFQ
  -- `multiplicity F Q = 1` (the order of the simple pole, made positive).
  have hmultQ : RS.multiplicity (MTrace.toP1 f) Q = 1 := by
    have hkey : (RS.multiplicity (MTrace.toP1 f) Q : ℤ) = -(RS.ordAtX f Q).untop₀ :=
      MTrace.multiplicity_toP1_of_ordAtX_neg hf hpoleneg
    rw [hpole'] at hkey
    have : (RS.multiplicity (MTrace.toP1 f) Q : ℤ) = 1 := by rw [hkey]; decide
    exact_mod_cast this
  -- `degree F = 1`.
  have hdeg1 : RS.degree (MTrace.toP1 f) = 1 := by
    rw [← RS.fiberMultSum_eq_degree hF hne (∞ : OnePoint ℂ), RS.fiberMultSum_def, hfibereq,
      finsum_mem_singleton]
    exact hmultQ
  exact ⟨(RS.homeomorphOfDegreeEqOne hF hne hdeg1).trans RS.P1.homeoSphere⟩

end RS
