/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.Normed.Module.Connected

/-!
Vendored from Mathlib's `Analysis/Complex/CanonicalDecomposition.lean` at `v4.33.0-rc1`
(`ECanonicalDecomp` and `MeromorphicOn.exists_ecanonicalDecomp` postdate the `v4.32.0-rc1`
revision of that file, which this repository builds against). Delete this file at the next
Mathlib bump: these declarations upstream verbatim, and keeping the copy would collide.
-/

@[expose] public section

namespace Complex

open ComplexConjugate Filter Function MeromorphicOn Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}
  {f g : ℂ → E}

/--
In a `T1Space`, every set is codiscrete within a subsingleton set. Vendored from Mathlib
`Topology/DiscreteSubset.lean` at `v4.33.0-rc1`; delete with this file at the next bump.
-/
@[simp] theorem _root_.Set.Subsingleton.mem_codiscreteWithin
    {X : Type*} [TopologicalSpace X] [T1Space X] {s t : Set X}
    (h : Set.Subsingleton t) :
    s ∈ codiscreteWithin t := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop

/--
A finite product of functions is nonzero at a point where every factor is nonzero. Vendored
from Mathlib `Algebra/BigOperators/Finprod.lean` at `v4.33.0-rc1`; delete with this file at
the next bump.
-/
theorem _root_.finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀]
    [Nontrivial M₀] [NoZeroDivisors M₀] {n : N₀} {f : ι → N₀ → M₀} (h : ∀ i, f i n ≠ 0) :
    (∏ᶠ i, f i) n ≠ 0 := by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

/--
Given a canonical decomposition `CanonicalDecomp f g R`, the function associated with the divisor of
`g` equals the function associated with the divisor of `f`, seen as a meromorphic function on the
sphere.
-/
theorem CanonicalDecomp.divisor_eq_divisor {x : ℂ} (D : CanonicalDecomp f g R) (hR : 0 < R) :
    divisor g (closedBall (0 : ℂ) R) x = divisor f (sphere 0 R) x := by
  rcases lt_trichotomy ‖x‖ R with h|h|h
  · -- The case where `x` is contained in `ball 0 R`. There, the divisor of `g` vanishes because `g`
    -- does not have zeros or poles. The divisor of `f` vanishes because `x` is not contained in the
    -- sphere.
    have : x ∉ sphere (0 : ℂ) R := by aesop
    have := (D.meromorphicNFOn (mem_closedBall_zero_iff.mpr h.le)).meromorphicOrderAt_eq_zero_iff.2
      (D.ne_zero x (by aesop))
    rw [divisor_apply D.meromorphicNFOn.meromorphicOn (mem_closedBall_zero_iff.mpr h.le)]
    simp_all
  · -- The case where `x` is contained in `sphere 0 R`. There, the orders of `f` and `g` agree
    -- because the canonical factors are analytic and do not vanish.
    have η₁ : AnalyticAt ℂ (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x := by
      refine analyticAt_finprod fun a ↦ ?_
      by_cases ha : a ∈ ball 0 R
      · exact (analyticOnNhd_canonicalFactor _ _ _ (by aesop)).zpow
          (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all only [mem_ball, dist_zero_right, not_lt,
          locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
        exact analyticAt_const
    have η₀ : f =ᶠ[𝓝[≠] x] (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) • g := by
      refine MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := closedBall 0 R) (D.meromorphicOn x (by aesop))
        (η₁.meromorphicAt.smul (D.meromorphicNFOn.meromorphicOn x (by aesop))) (by aesop) ?_
        D.eventuallyEq
      rw [← closure_ball 0 hR.ne']
      exact isOpen_ball.perfect_closure.2
    have : meromorphicOrderAt (∏ᶠ u, canonicalFactor R u ^ (-(divisor f (ball 0 R)) u)) x = 0 := by
      refine η₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (finprod_apply_ne_zero fun a ↦ ?_)
      by_cases ha : a ∈ ball 0 R
      · exact zpow_ne_zero _ (canonicalFactor_ne_zero ha (by aesop) (by aesop))
      · simp_all
    rw [divisor_apply (D.meromorphicOn.mono_set sphere_subset_closedBall) (by aesop),
      divisor_apply D.meromorphicNFOn.meromorphicOn (by aesop), meromorphicOrderAt_congr η₀,
      meromorphicOrderAt_smul η₁.meromorphicAt (D.meromorphicNFOn (by aesop)).meromorphicAt]
    simp_all
  · -- Trivial case: `x` is outside `closedBall 0 R`, so both divisors evaluate to zero.
    have : x ∉ sphere (0 : ℂ) R := by aesop
    simp_all


/--
Given functions `f`, `g` and a real number `R`, the following convenience structure packs the
information relevant in the extended canonical decomposition.
-/
structure ECanonicalDecomp (f g : ℂ → E) (R : ℝ) where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)
  /-- A proof that `g` is analytic in a neighborhood of `closedBall 0 R`. -/
  analyticOnNhd : AnalyticOnNhd ℂ g (closedBall 0 R)
  /-- A proof that `g` does not vanish on the closed ball. -/
  ne_zero : ∀ u ∈ (closedBall 0 R), g u ≠ 0
  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g`, canonical
  factors prescribed by the divisor of `f`, and a factorized rational function with poles and zeros
  only on the boundary of the ball.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u))
    * (∏ᶠ v, (· - v) ^ (divisor f (sphere 0 R)) v)) • g

/--
**Extended canonical decomposition:** A meromorphic function on a closed disk is equal, up to
modification over a discrete set, to a product of a non-vanishing analytic function, canonical
factors and meromorphic functions of the form `(x - const) ^ n` where `const` is on the
circumference of the disk.
-/
theorem _root_.MeromorphicOn.exists_ecanonicalDecomp (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ h, ECanonicalDecomp f h R := by
  rcases gt_trichotomy 0 R with hR | hR | hR
  · use fun _ ↦ f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd := by simp_all
      ne_zero := by simp_all
      eventuallyEq := by
        simp_all only [closedBall_of_neg]
        filter_upwards [Filter.self_mem_codiscreteWithin ∅] with a ha
        tauto
    }
  · use fun _ ↦ meromorphicTrailingCoeffAt f 0
    exact {
      meromorphicOn := by simp_all
      analyticOnNhd _ _ := by fun_prop
      ne_zero := by
        simp only [hR.symm, closedBall_zero, mem_singleton_iff, ne_eq, forall_eq]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁f 0 _) _
        <;> simp_all
      eventuallyEq := by
        simp only [hR.symm, closedBall_zero]
        apply subsingleton_singleton.mem_codiscreteWithin
    }
  obtain ⟨g, D⟩ := h₁f.exists_canonicalDecomp h₂f
  have h₄g : ∀ (u : closedBall (0 : ℂ) R), meromorphicOrderAt g u ≠ ⊤ := by
    rw [← D.meromorphicNFOn.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)]
    have s₁ : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
    use ⟨0, s₁⟩
    simp [(D.meromorphicNFOn s₁).meromorphicOrderAt_eq_zero_iff.2 (D.ne_zero 0 (by simp [hR]))]
  obtain ⟨h, h₁h, h₂h, h₃h⟩ := D.meromorphicNFOn.meromorphicOn.extract_zeros_poles h₄g <|
    (divisor g (closedBall 0 R)).finiteSupport <| isCompact_closedBall 0 R
  use h
  exact {
    meromorphicOn := h₁f
    analyticOnNhd := h₁h
    ne_zero := (h₂h ⟨·, ·⟩)
    eventuallyEq := by
      filter_upwards [D.eventuallyEq, h₃h] with a h₁a h₂a
      simp_rw [← D.divisor_eq_divisor hR]
      simp_all [← smul_assoc]
    }

end Complex
