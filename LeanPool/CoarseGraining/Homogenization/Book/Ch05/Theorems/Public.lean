/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyEndpoint
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyOptimized

/-! # Public -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Public Chapter 5 minimal-scale theorem

This file is the public landing zone for the quenched minimal-scale theorem.
The proof-internal Section 5.7 development exposes separate finite-`sigma` and
uniform-endpoint statements; the public theorem below packages them as the two
branches of the manuscript theorem.
-/

noncomputable section

/-- Public Chapter 5.7 quenched minimal-scale theorem.

The first component is the finite-`sigma` statement, with a single algebraic
exponent selected before `sigma` and stochastic exponent
`finiteQuenchedTailExponent d sigma t`.  The second component is the
`Gamma_infty` endpoint, with stochastic exponent `d` and the same public
condition `t ≤ 1`.  In both branches the minimal-scale constant is selected
before the probability law.  The Section 5.7 parameter bundle contains only
`sUpper` and `sLower`; the finite moment exponent needed by older Chapter 5 APIs
is chosen internally. -/
theorem homogenization_quenched_minimal_scale
    {d : ℕ} [NeZero d]
    (params : Section57.GammaCoarseGrainedEllipticityParams d) :
    (∃ α : ℝ, 0 < α ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∀ {t : ℝ}, max params.sUpper params.sLower < t → t ≤ 1 →
          ∃ Cscale : ℝ, 0 < Cscale ∧
            ∀ {P : Ch04.RestrictionCoeffLaw d}
              (hP : Ch04.RestrictionLawCarrier P)
              (hStruct : Ch04.RestrictionStructuralLaw P)
              (hΓ : Section57.GammaSigmaCoarseGrainedEllipticityNoXi
                P hP hStruct),
              hΓ.sigma = σ → hΓ.params = params →
              let η : ℝ := Section57.finiteQuenchedTailExponent d σ t
              ∃ X : RegCoeffField d → ℝ,
                IsBigO P (gammaSigma η) X
                  (Real.exp
                    (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
                (∀ aω, 1 ≤ X aω) ∧
                  ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                    ∀ᵐ aω ∂P,
                      ∀ {m n : ℕ},
                        X aω ≤ (3 : ℝ) ^ m →
                        n < m →
                        (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                            Section57.localizedLimitNormalizedJMax
                              hP hStruct m n e aω ≤
                          ((3 : ℝ) ^ m / X aω) ^ (-α)) ∧
    (∃ α : ℝ, 0 < α ∧
      ∀ {t : ℝ},
        max params.sUpper params.sLower < t →
        t ≤ 1 →
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : Section57.GammaInfinityCoarseGrainedEllipticityNoXi
              P hP hStruct),
            hInf.params = params →
            let η : ℝ := ((d : ℕ) : ℝ)
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
                  ∀ᵐ aω ∂P,
                    ∀ {m n : ℕ},
                      X aω ≤ (3 : ℝ) ^ m →
                      n < m →
                      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                          Section57.localizedLimitNormalizedJMax
                            hP hStruct m n e aω ≤
                        ((3 : ℝ) ^ m / X aω) ^ (-α)) := by
  constructor
  · obtain ⟨α, hα, _hαmax, hfinite⟩ :=
      Section57.exists_quenchedLocalizedEstimate_interpolated_expLogSq_uniformAnnealedExponent
        (d := d) params.toQuantitativeParams
    refine ⟨α, hα, ?_⟩
    intro σ hσ t ht ht_one
    obtain ⟨Cscale, hCscale, hscale⟩ := hfinite hσ ht ht_one
    refine ⟨Cscale, hCscale, ?_⟩
    intro P hP hStruct hΓ hσ_eq hparams
    let hΓold : Section57.GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
      hΓ.withInternalXi
    have hσ_old : hΓold.sigma = σ := by
      simpa [hΓold] using hσ_eq
    have hparams_old : hΓold.params = params.toQuantitativeParams := by
      dsimp [hΓold, Section57.GammaSigmaCoarseGrainedEllipticityNoXi.withInternalXi]
      rw [hparams]
    obtain ⟨X, hX, hX_one, hmain⟩ :=
      hscale hP hStruct hΓold hσ_old hparams_old
    exact ⟨X, by simpa [hΓold] using hX, hX_one, hmain⟩
  · obtain ⟨α, hα, _hαmax, hendpoint⟩ :=
      Section57.exists_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
        (d := d) params.toQuantitativeParams
    refine ⟨α, hα, ?_⟩
    intro t ht ht_one
    have ht_dim : t ≤ (d : ℝ) / 2 := by
      have hd : (2 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast params.two_le_dim
      have hone_le_dim_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by
        nlinarith
      exact ht_one.trans hone_le_dim_half
    obtain ⟨Cscale, hCscale, hscale⟩ := hendpoint ht ht_dim
    refine ⟨Cscale, hCscale, ?_⟩
    intro P hP hStruct hInf hparams
    let hInfOld : Section57.GammaInfinityCoarseGrainedEllipticity P hP hStruct :=
      hInf.withInternalXi
    have hparams_old : hInfOld.params = params.toQuantitativeParams := by
      dsimp [hInfOld, Section57.GammaInfinityCoarseGrainedEllipticityNoXi.withInternalXi]
      rw [hparams]
    obtain ⟨X, hX, hX_one, hmain⟩ :=
      hscale hP hStruct hInfOld hparams_old
    exact ⟨X, by simpa [hInfOld] using hX, hX_one, hmain⟩

/-- Public Chapter 5.7 quenched homogenization comparison theorem.

This is the public Ch3-facing consequence of the minimal-scale theorem,
stated in the manuscript's simplified two-parameter form: `t` is the
stochastic integrability dial and `s` is both the negative Besov comparison
exponent and the force regularity exponent, subject to `s₁ ∨ s₂ < t` and
`4t < s < 1`.  The coarse-graining exponent `r = t + s / 4`, the discount
exponent `τ = 2t`, and the localization depth `j` of the compressed
two-exponent RHS are all chosen inside the proof; the depth is optimized so
that the RHS collapses to a single constant times `(3^m / X)^(-α)` times the
two natural data norms.  The finite branch has stochastic exponent
`finiteQuenchedTailExponent d sigma t` (the interpolated min collapses by
monotonicity in the discount); the uniform endpoint has exponent `d`.  The
exponent `α` is selected before `sigma` and is already the relabeled
post-optimization exponent. -/
theorem homogenization_quenched_homogenization_comparison
    {d : ℕ} [NeZero d]
    (params : Section57.GammaCoarseGrainedEllipticityParams d) :
    (∃ α : ℝ, 0 < α ∧
      ∀ {σ t s : ℝ}, 0 < σ →
        max params.sUpper params.sLower < t →
        4 * t < s →
        s < 1 →
        ∃ C Cscale : ℝ, 0 < C ∧ 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : Section57.GammaSigmaCoarseGrainedEllipticityNoXi
              P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma (Section57.finiteQuenchedTailExponent d σ t)) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m : ℕ} {g : Vec d → Vec d}
                    (w : Section57.assemblyComparisonDatum
                      hP hStruct hΓ.withInternalXi aω ha m g),
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity
                      (Section57.assemblyOriginCube d m) s g →
                    Ch03.homogenizationComparisonNegativeBesovLHS
                        (Section57.assemblyOriginCube d m)
                        (Section57.assemblyCoeffFamily aω ha)
                        (Section57.assemblyConstantCoeffMatrix
                          hP hStruct hΓ.withInternalXi)
                        s w.u w.v ≤
                      Section57.assemblyHomogenizationComparisonRHS
                        hP hStruct hΓ.withInternalXi
                        C α s X aω ha m g w) ∧
    (∃ α : ℝ, 0 < α ∧
      ∀ {t s : ℝ},
        max params.sUpper params.sLower < t →
        4 * t < s →
        s < 1 →
        ∃ C Cscale : ℝ, 0 < C ∧ 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : Section57.GammaInfinityCoarseGrainedEllipticityNoXi
              P hP hStruct),
            hInf.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma ((d : ℕ) : ℝ)) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m : ℕ} {g : Vec d → Vec d}
                    (w : Section57.assemblyComparisonDatumOfScalar
                      (Section57.barSigmaLimit hP hStruct)
                      (hInf.withInternalXi.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      aω ha m g),
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity
                      (Section57.assemblyOriginCube d m) s g →
                    Ch03.homogenizationComparisonNegativeBesovLHS
                        (Section57.assemblyOriginCube d m)
                        (Section57.assemblyCoeffFamily aω ha)
                        (Section57.assemblyConstantCoeffMatrixOfScalar
                          (Section57.barSigmaLimit hP hStruct)
                          (hInf.withInternalXi.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos)
                        s w.u w.v ≤
                      Section57.assemblyHomogenizationComparisonRHSOfScalar
                        (Section57.barSigmaLimit hP hStruct)
                        (hInf.withInternalXi.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                        C α s X aω ha m g w) := by
  constructor
  · obtain ⟨Ccg, α₀, hCcg, hα₀, hα₀max, hfinite⟩ :=
      Section57.exists_homogenizationComparison_compressedTwoExponentRHS_interpolated_expLogSq
        (d := d) params.toQuantitativeParams
    refine ⟨α₀ / 8, by positivity, ?_⟩
    intro σ t s hσ ht hts hs_one
    have hα₀max' : α₀ < max params.sUpper params.sLower := by
      simpa using hα₀max
    have hα₀t : α₀ < t := hα₀max'.trans ht
    have ht0 : 0 < t := by
      exact (lt_of_lt_of_le params.sUpper_pos (le_max_left _ _)).trans ht
    have hs_pos : 0 < s := by linarith
    let r : ℝ := t + s / 4
    have hτr : 2 * t < r := by dsimp [r]; linarith
    have hrs : r < s / 2 := by dsimp [r]; linarith
    have hrrs : 3 / 2 * r ≤ s := by dsimp [r]; linarith
    have hr_pos : 0 < r := by linarith
    have hr_le_s : r ≤ s := by linarith
    have hτ2 : max params.sUpper params.sLower < 2 * t / 2 := by linarith
    have hατ : α₀ < 2 * t / 2 := by linarith
    have hτ_one : 2 * t ≤ 1 := by linarith
    obtain ⟨Cclean, hCclean, hclean⟩ :=
      Section57.exists_compressedTwoExponentRHS_le_homogenizationComparisonRHS
        d hCcg hα₀ (by linarith : (0 : ℝ) < 2 * t) hτr hs_pos hr_pos hrs
        hs_one hrrs
    obtain ⟨Cscale, hCscale, hlaw⟩ :=
      hfinite hσ hτ2 hατ hτ_one hs_pos hr_pos hrs hs_one hτr hr_le_s
    refine ⟨Cclean, Cscale, hCclean, hCscale, ?_⟩
    intro P hP hStruct hΓ hσ_eq hparams
    let hΓold : Section57.GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
      hΓ.withInternalXi
    have hσ_old : hΓold.sigma = σ := by
      simpa [hΓold] using hσ_eq
    have hparams_old : hΓold.params = params.toQuantitativeParams := by
      dsimp [hΓold, Section57.GammaSigmaCoarseGrainedEllipticityNoXi.withInternalXi]
      rw [hparams]
    obtain ⟨X, hX, hX_one, hmain⟩ :=
      hlaw hP hStruct hΓold hσ_old hparams_old
    have hηeq :
        min (Section57.finiteQuenchedTailExponent d σ (2 * t))
            (Section57.finiteQuenchedTailExponent d σ (2 * t / 2)) =
          Section57.finiteQuenchedTailExponent d σ t := by
      rw [show (2 * t / 2 : ℝ) = t by ring]
      exact min_eq_right
        (Section57.finiteQuenchedTailExponent_le_of_le hσ ht0
          (by linarith : t ≤ 2 * t))
    refine ⟨X, ?_, hX_one, ?_⟩
    · rw [← hηeq]
      simpa [hΓold] using hX
    · filter_upwards [hmain] with aω haω
      intro ha m g w hXm hg
      have hstep :=
        haω ha (m := m)
          (j := Section57.assemblyOptimizedDepth α₀ r X aω m) (g := g) w hXm hg
      have hcompress :=
        hclean (σ0 := Section57.barSigmaLimit hP hStruct)
          hΓold.barSigmaLimit_pos X aω ha m g w (hX_one aω) hXm hg
      refine hstep.trans ?_
      simpa [Section57.assemblyCompressedTwoExponentRHS,
        Section57.assemblyHomogenizationComparisonRHS, hΓold] using hcompress
  · obtain ⟨Ccg, α₀, hCcg, hα₀, hα₀max, hendpoint⟩ :=
      Section57.exists_homogenizationComparison_compressedTwoExponentRHS_uniformEndpoint_expLogSq
        (d := d) params.toQuantitativeParams
    refine ⟨α₀ / 8, by positivity, ?_⟩
    intro t s ht hts hs_one
    have hα₀max' : α₀ < max params.sUpper params.sLower := by
      simpa using hα₀max
    have hα₀t : α₀ < t := hα₀max'.trans ht
    have ht0 : 0 < t := by
      exact (lt_of_lt_of_le params.sUpper_pos (le_max_left _ _)).trans ht
    have hs_pos : 0 < s := by linarith
    let r : ℝ := t + s / 4
    have hτr : 2 * t < r := by dsimp [r]; linarith
    have hrs : r < s / 2 := by dsimp [r]; linarith
    have hrrs : 3 / 2 * r ≤ s := by dsimp [r]; linarith
    have hr_pos : 0 < r := by linarith
    have hr_le_s : r ≤ s := by linarith
    have hτ2 : max params.sUpper params.sLower < 2 * t / 2 := by linarith
    have hατ : α₀ < 2 * t / 2 := by linarith
    have hτ_one : 2 * t ≤ 1 := by linarith
    obtain ⟨Cclean, hCclean, hclean⟩ :=
      Section57.exists_compressedTwoExponentRHS_le_homogenizationComparisonRHS
        d hCcg hα₀ (by linarith : (0 : ℝ) < 2 * t) hτr hs_pos hr_pos hrs
        hs_one hrrs
    obtain ⟨Cscale, hCscale, hlaw⟩ :=
      hendpoint hτ2 hατ hτ_one hs_pos hr_pos hrs hs_one hτr hr_le_s
    refine ⟨Cclean, Cscale, hCclean, hCscale, ?_⟩
    intro P hP hStruct hInf hparams
    let hInfOld : Section57.GammaInfinityCoarseGrainedEllipticity P hP hStruct :=
      hInf.withInternalXi
    have hparams_old : hInfOld.params = params.toQuantitativeParams := by
      dsimp [hInfOld, Section57.GammaInfinityCoarseGrainedEllipticityNoXi.withInternalXi]
      rw [hparams]
    obtain ⟨X, hX, hX_one, hmain⟩ :=
      hlaw hP hStruct hInfOld hparams_old
    refine ⟨X, by simpa [hInfOld] using hX, hX_one, ?_⟩
    filter_upwards [hmain] with aω haω
    intro ha m g w hXm hg
    have hstep :=
      haω ha (m := m)
        (j := Section57.assemblyOptimizedDepth α₀ r X aω m) (g := g) w hXm hg
    have hcompress :=
      hclean (σ0 := Section57.barSigmaLimit hP hStruct)
        (hInfOld.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
        X aω ha m g w (hX_one aω) hXm hg
    refine hstep.trans ?_
    simpa [hInfOld] using hcompress

end

end Ch05
end Book
end Homogenization
