/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FiniteProductWeakForm

/-!
# Weak limit passage on fixed Fourier tests

A fixed real Fourier test is embedded in every sufficiently large cutoff. The finite product-space
identities therefore pass to the synchronized weak product limits without changing their tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem ProductWeakLimitPassage.scalarProductTestLp_congr {η : ℝ → ℝ} {ψ χ : ScalarTorusL2}
    (hη : MemLp η ⊤ GalerkinTimeMeasure) (hψ : ψ = χ) :
    scalarProductTestLp η ψ hη = scalarProductTestLp η χ hη := by
  subst χ
  rfl

theorem ProductWeakLimitPassage.gradientProductTestLp_congr {η : ℝ → ℝ} {g h : SpatialGradientL2}
    (hη : MemLp η ⊤ GalerkinTimeMeasure) (hg : g = h) :
    gradientProductTestLp η g hη = gradientProductTestLp η h hη := by
  subst h
  rfl

private theorem FrozenDriftProblem.weightedDriftProductTestLp_lift
    (P : FrozenDriftProblem) {M N : ℕ} (hMN : M ≤ N)
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (d : Coefficients (RealFourierDimension M)) :
    P.weightedDriftProductTestLp η N (realFourierCoefficientsLift hMN d) hη =
      P.weightedDriftProductTestLp η M d hη := by
  change (P.weightedDriftProductTest_memLp hη N
      (realFourierCoefficientsLift hMN d)).toLp
        (P.weightedDriftProductTestFunction η N (realFourierCoefficientsLift hMN d)) =
    (P.weightedDriftProductTest_memLp hη M d).toLp
      (P.weightedDriftProductTestFunction η M d)
  apply Lp.ext
  filter_upwards [
    (P.weightedDriftProductTest_memLp hη N (realFourierCoefficientsLift hMN d)).coeFn_toLp,
    (P.weightedDriftProductTest_memLp hη M d).coeFn_toLp] with p hN hM
  simp only [FrozenDriftProblem.weightedDriftProductTestFunction,
    SpatialVector, PiLp] at hN hM ⊢
  rw [hN, hM]
  simp [scalarExpansion_lift hMN d]

theorem ProductWeakLimitPassage.strictMono_nat_id_le {σ : ℕ → ℕ} (hσ : StrictMono σ) (n : ℕ) : n ≤
    σ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hσ (Nat.lt_succ_self n)))

/-- The synchronized weak product limits satisfy the weak equation against every separated smooth
time test and fixed finite real Fourier test. -/
theorem FrozenDriftProblem.synchronized_limit_fourier_test_weak_identity
    (P : FrozenDriftProblem) (M : ℕ)
    (d : Coefficients (RealFourierDimension M))
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hη₁ : η 1 = 0)
    (hηMem : MemLp η ⊤ GalerkinTimeMeasure)
    (hηDerivMem : MemLp (deriv η) ⊤ GalerkinTimeMeasure)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v))) :
    -inner ℝ Uprod
        (scalarProductTestLp (deriv η) (realFourierScalarMap M d) hηDerivMem) +
      inner ℝ Gprod (P.weightedDriftProductTestLp η M d hηMem) +
      P.κ * inner ℝ Gprod
        (gradientProductTestLp η (realFourierGradientMap M d) hηMem) =
      η 0 * inner ℝ P.initialTorusL2 (realFourierScalarMap M d) := by
  let ψ := scalarProductTestLp (deriv η) (realFourierScalarMap M d) hηDerivMem
  let btest := P.weightedDriftProductTestLp η M d hηMem
  let gtest := gradientProductTestLp η (realFourierGradientMap M d) hηMem
  let lhsSeq : ℕ → ℝ := fun n =>
    -inner ℝ (P.scalarProductLp (σ n)) ψ +
      inner ℝ (P.gradientProductLp (σ n)) btest +
      P.κ * inner ℝ (P.gradientProductLp (σ n)) gtest
  let rhs : ℝ := η 0 * inner ℝ P.initialTorusL2 (realFourierScalarMap M d)
  have hlarge : ∀ᶠ n : ℕ in atTop, M ≤ σ n := by
    filter_upwards [eventually_atTop.2 ⟨M, fun n hn =>
      le_trans hn (ProductWeakLimitPassage.strictMono_nat_id_le hσ n)⟩] with n hn
    exact hn
  have hfiniteEventually : ∀ᶠ n : ℕ in atTop, lhsSeq n = rhs := by
    filter_upwards [hlarge] with n hn
    let dN := realFourierCoefficientsLift hn d
    have hscalarMap : realFourierScalarMap (σ n) dN = realFourierScalarMap M d :=
      realFourierScalarMap_lift hn d
    have hgradientMap : realFourierGradientMap (σ n) dN = realFourierGradientMap M d :=
      realFourierGradientMap_lift hn d
    have hscalarTest := ProductWeakLimitPassage.scalarProductTestLp_congr hηDerivMem hscalarMap
    have hdriftTest := P.weightedDriftProductTestLp_lift hn η hηMem d
    have hgradientTest := ProductWeakLimitPassage.gradientProductTestLp_congr hηMem hgradientMap
    have hidentity := P.finite_product_fourier_test_weak_identity
      (σ n) dN η hη hη₁ hηMem hηDerivMem
    rw [hscalarTest, hdriftTest, hgradientTest, hscalarMap] at hidentity
    change lhsSeq n = rhs
    exact hidentity
  have hlimit : Tendsto lhsSeq atTop
      (𝓝 (-inner ℝ Uprod ψ + inner ℝ Gprod btest + P.κ * inner ℝ Gprod gtest)) := by
    have hs := hUweak ψ
    have hb := hGweak btest
    have hg := hGweak gtest
    have hsneg : Tendsto (fun n => -inner ℝ (P.scalarProductLp (σ n)) ψ) atTop
        (𝓝 (-inner ℝ Uprod ψ)) :=
      (continuous_neg.continuousAt (x := inner ℝ Uprod ψ)).tendsto.comp hs
    convert (hsneg.add hb).add (tendsto_const_nhds.mul hg) using 1
  have hconstant : Tendsto lhsSeq atTop (𝓝 rhs) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => rhs) atTop (𝓝 rhs)).congr'
    filter_upwards [hfiniteEventually] with n hn
    exact hn.symm
  have hEq := tendsto_nhds_unique hlimit hconstant
  simpa [ψ, btest, gtest, rhs] using hEq

end AVenhance.Infra.Parabolic.FourierGalerkin

end
