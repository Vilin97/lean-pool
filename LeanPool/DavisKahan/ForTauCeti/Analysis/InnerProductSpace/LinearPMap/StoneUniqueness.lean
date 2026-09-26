/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Stone

/-!
# Stone's theorem, the uniqueness half

`genToGroup hA` builds the unitary group of a self-adjoint `A`.  This module
proves that its generator is `A` again.

## Why only one inclusion has to be proved

`generator (genToGroup hA)` is self-adjoint by
`OneParameterUnitaryGroup.isSelfAdjoint_generator` (Stone's forward direction),
and `eq_of_le_of_isSelfAdjoint` says a self-adjoint operator has no proper
self-adjoint extension.  So `A ≤ generator (genToGroup hA)` already gives
equality, and the reverse inclusion — which would need a description of the
generator's domain — is never required.

## The route

The Yosida file stops at the *Lipschitz* bound
`‖expLimit hA τ ψ - ψ‖ ≤ |τ| ‖A ψ‖`; what is wanted is the derivative at
`τ = 0`.  The step from one to the other is the integral identity

`expLimit hA t ψ - ψ = ∫₀ᵗ i · expLimit hA s (A ψ) ds`  for `ψ ∈ dom A`,

after which the difference quotient is the *average* of
`s ↦ expLimit hA s (A ψ)` over `[0, t]`, and that tends to the value at `0`
because the integrand is continuous.

The identity itself is ordinary calculus for the bounded Yosida approximants
(`hasDerivAt_expTime`), and passes to the limit under the integral sign: the
integrand converges pointwise in `s` and is dominated by a constant, since a
convergent sequence of vectors is bounded.

Two other routes were tried and rejected, recorded here so they are not
retried.  The mean-value inequality applied to `s ↦ exp(isAₙ)ψ - ψ - isAₙψ`
has the right shape but needs `exp(isAₙ)φ → expLimit hA s φ` *uniformly* on
compact `s`-intervals, which is a separate equicontinuity argument.  A
second-order Duhamel estimate brings in `‖Aₙ² ψ‖`, which blows up with `n`.

## Provenance

* **Original repository:** none — **authored in place** in the AIQ DKPS
  formalization (`https://github.com/AIQ-Kitware/aiq-dkps-formalization`),
  commit `c9c8502c`, for staging into Tau Ceti.
* **Original module:** none; written directly at this path.
* **Original authors / copyright / licence:** Copyright (c) 2026 Kitware, Inc.;
  `Authors: Jon Crall, Claude Opus 5`; Apache 2.0 (this repository's `LICENSE`).
  No third-party code is incorporated, so no donor notice is carried.
* **Extraction class:** *authored in place*, for upstreaming to Tau Ceti.
* **Relation to existing libraries:** the uniqueness half of Stone's theorem for
  a self-adjoint `LinearPMap`. Neither Mathlib nor the retired Spectra snapshot
  carries it. Only one inclusion is proved: the generator of `genToGroup hA` is
  self-adjoint by the forward direction, and a self-adjoint operator admits no
  proper self-adjoint extension, so `A ≤ generator (genToGroup hA)` already
  gives equality — the reverse inclusion, which would need a description of the
  generator's domain, is never required.
* **Semantic differences from a donor:** not applicable.
-/

@[expose] public section

open scoped InnerProductSpace
open Filter Topology Complex MeasureTheory intervalIntegral

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-! ### The bounded case: an exact integral identity -/

/-- `s ↦ exp(s • B) ψ` is continuous. -/
@[simp]
theorem continuous_expTime_apply (B : H →L[ℂ] H) (ψ : H) :
    Continuous fun s : ℝ => expTime B s ψ := by
  have hdiff : Differentiable ℝ fun s : ℝ => expTime B s ψ := fun s =>
    (hasDerivAt_expTime_apply B ψ s).differentiableAt
  exact hdiff.continuous

/-- **The exact integral identity for a bounded generator.** -/
@[simp]
theorem integral_expTime_apply (B : H →L[ℂ] H) (ψ : H) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, expTime B s (B ψ)) = expTime B t ψ - ψ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => expTime B s ψ) (expTime B s (B ψ)) s :=
    fun s _ => hasDerivAt_expTime_apply B ψ s
  have hint : IntervalIntegrable (fun s : ℝ => expTime B s (B ψ)) volume 0 t :=
    (continuous_expTime_apply B (B ψ)).intervalIntegrable 0 t
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-! ### Passing the identity to the limit -/

/-- The identity, for the Yosida approximants. -/
theorem integral_expApprox (hA : IsSelfAdjoint A) (n : ℕ+) (ψ : H) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (I : ℂ) • expApprox hA n s (yosidaApproximantSym hA n ψ))
      = expApprox hA n t ψ - ψ := by
  have h := integral_expTime_apply ((I : ℂ) • yosidaApproximantSym hA n) ψ t
  simp only [smul_apply, map_smul, ← expApprox_eq_expTime] at h
  exact h

/-- `s ↦ expApprox hA n s w` is continuous. -/
@[simp]
theorem continuous_expApprox_apply (hA : IsSelfAdjoint A) (n : ℕ+) (w : H) :
    Continuous fun s : ℝ => expApprox hA n s w := by
  simp only [expApprox_eq_expTime]
  exact continuous_expTime_apply _ w

/-- **The integral identity for the limit flow.**  The approximants converge
pointwise in `s` and are bounded by a constant, because a convergent sequence of
vectors is bounded and each `expApprox` is unitary. -/
theorem integral_expLimit (hA : IsSelfAdjoint A) {ψ : H} (hψ : ψ ∈ A.domain) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩)) = expLimit hA t ψ - ψ := by
  have hconv := tendsto_yosidaApproxSym_of_mem_domain hA ψ hψ
  -- a uniform bound on the approximant images
  have hnorm : Tendsto (fun n : ℕ+ => ‖yosidaApproximantSym hA n ψ‖) atTop (𝓝 ‖A ⟨ψ, hψ⟩‖) :=
    hconv.norm
  set C : ℝ := ‖A ⟨ψ, hψ⟩‖ + 1 with hCdef
  have hCle : ∀ᶠ n : ℕ+ in atTop, ‖yosidaApproximantSym hA n ψ‖ ≤ C :=
    hnorm.eventually_le_const (by rw [hCdef]; linarith)
  -- the integrands converge pointwise
  have hlim : ∀ s : ℝ, Tendsto
      (fun n : ℕ+ => (I : ℂ) • expApprox hA n s (yosidaApproximantSym hA n ψ)) atTop
      (𝓝 ((I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩))) := by
    intro s
    refine Filter.Tendsto.const_smul ?_ (I : ℂ)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsplit : ∀ n : ℕ+,
        ‖expApprox hA n s (yosidaApproximantSym hA n ψ) - expLimit hA s (A ⟨ψ, hψ⟩)‖
          ≤ ‖yosidaApproximantSym hA n ψ - A ⟨ψ, hψ⟩‖
            + ‖expApprox hA n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := by
      intro n
      calc ‖expApprox hA n s (yosidaApproximantSym hA n ψ) - expLimit hA s (A ⟨ψ, hψ⟩)‖
          = ‖expApprox hA n s (yosidaApproximantSym hA n ψ - A ⟨ψ, hψ⟩)
              + (expApprox hA n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩))‖ := by
            rw [map_sub]; congr 1; abel
        _ ≤ ‖expApprox hA n s (yosidaApproximantSym hA n ψ - A ⟨ψ, hψ⟩)‖
              + ‖expApprox hA n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := norm_add_le _ _
        _ = ‖yosidaApproximantSym hA n ψ - A ⟨ψ, hψ⟩‖
              + ‖expApprox hA n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := by
            rw [norm_expApprox]
    refine squeeze_zero (fun n => norm_nonneg _) hsplit ?_
    have h1 : Tendsto (fun n : ℕ+ => ‖yosidaApproximantSym hA n ψ - A ⟨ψ, hψ⟩‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hconv
    have h2 : Tendsto
        (fun n : ℕ+ => ‖expApprox hA n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_expLimitFun hA s (A ⟨ψ, hψ⟩))
    simpa using h1.add h2
  -- dominated convergence
  have hint : Tendsto
      (fun n : ℕ+ => ∫ s in (0 : ℝ)..t, (I : ℂ) • expApprox hA n s (yosidaApproximantSym hA n ψ))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun n =>
        (((continuous_expApprox_apply hA n (yosidaApproximantSym hA n ψ)).const_smul
          (I : ℂ)).aestronglyMeasurable)
    · filter_upwards [hCle] with n hn
      refine Eventually.of_forall fun s _ => ?_
      rw [norm_smul, Complex.norm_I, one_mul, norm_expApprox]
      exact hn
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s _ => hlim s
  -- and the right-hand sides converge too
  have hrhs : Tendsto (fun n : ℕ+ => expApprox hA n t ψ - ψ) atTop
      (𝓝 (expLimit hA t ψ - ψ)) :=
    (tendsto_expLimitFun hA t ψ).sub tendsto_const_nhds
  refine tendsto_nhds_unique hint ?_
  refine hrhs.congr fun n => ?_
  exact (integral_expApprox hA n ψ t).symm

/-- The difference quotient of the limit flow converges to `A ψ` on the domain:
the integral identity turns it into the *average* of a continuous integrand. -/
theorem tendsto_genDiffQuot_genToGroup (hA : IsSelfAdjoint A) {ψ : H} (hψ : ψ ∈ A.domain) :
    Tendsto (TauCeti.OneParameterUnitaryGroup.genDiffQuot (genToGroup hA) ψ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (A ⟨ψ, hψ⟩)) := by
  set g : ℝ → H := fun s => (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩) with hg
  have hgcont : Continuous g := (continuous_expLimit hA (A ⟨ψ, hψ⟩)).const_smul (I : ℂ)
  have hg0 : g 0 = (I : ℂ) • A ⟨ψ, hψ⟩ := by rw [hg]; simp
  have hderiv : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, g s) ((I : ℂ) • A ⟨ψ, hψ⟩) 0 := by
    have h := (hgcont.integral_hasStrictDerivAt 0 0).hasDerivAt
    rwa [hg0] at h
  have hderiv' : HasDerivAt (fun u : ℝ => expLimit hA u ψ - ψ) ((I : ℂ) • A ⟨ψ, hψ⟩) 0 := by
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards with u
    exact (integral_expLimit hA hψ u).symm
  rw [hasDerivAt_iff_tendsto_slope] at hderiv'
  have hres := hderiv'.const_smul (-(I : ℂ))
  have hval : (-(I : ℂ)) • ((I : ℂ) • A ⟨ψ, hψ⟩) = A ⟨ψ, hψ⟩ := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [hval] at hres
  refine hres.congr fun t => ?_
  have hf0 : expLimit hA 0 ψ - ψ = 0 := by rw [expLimit_zero]; simp
  simp only [slope_def_module, hf0, sub_zero,
    TauCeti.OneParameterUnitaryGroup.genDiffQuot_apply]
  have hcast : (t⁻¹ : ℝ) • ((expLimit hA t) ψ - ψ)
      = (((t : ℂ))⁻¹) • ((expLimit hA t) ψ - ψ) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (t⁻¹ : ℝ) ((expLimit hA t) ψ - ψ)]
    norm_cast
  rw [hcast, smul_smul, mul_inv, Complex.inv_I]
  rfl

/-! ### The derivative at zero, and the identification -/

/-- **Stone's theorem, uniqueness half.**  The generator of the unitary group of
a self-adjoint operator is that operator again. -/
theorem generator_genToGroup (hA : IsSelfAdjoint A) :
    TauCeti.OneParameterUnitaryGroup.generator (genToGroup hA) = A := by
  refine (eq_of_le_of_isSelfAdjoint hA
    (TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator (genToGroup hA)) ?_).symm
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · -- the domain inclusion, which is the same limit computation
    refine ⟨A ⟨ψ, hψ⟩, ?_⟩
    exact tendsto_genDiffQuot_genToGroup hA hψ
  · rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ hEq
    simp only at hEq
    subst hEq
    exact (tendsto_nhds_unique
      (TauCeti.OneParameterUnitaryGroup.generator_tendsto (genToGroup hA) ⟨ψ, hψ'⟩)
      (tendsto_genDiffQuot_genToGroup hA hψ)).symm

end LinearPMap
end TauCeti
