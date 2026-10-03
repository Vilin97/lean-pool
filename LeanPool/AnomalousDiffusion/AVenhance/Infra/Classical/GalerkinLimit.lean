/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinCauchy
public import Mathlib.Topology.MetricSpace.Cauchy

/-! Uniform Cauchy convergence of the scalar torus Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Filter Topology Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

/-- The explicit cutoff error supplied by the nested-path energy estimate. -/
def classicalGalerkinScalarPathError
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ)
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (E_F E_T : ℝ) (M : ℕ) : ℝ :=
  let scale : ℝ := (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹
  let δ : ℝ := Real.sqrt (scale * AVenhance.gradNormSq (AVenhance.spaceGrad θ₀))
  let ε : ℝ := Real.sqrt (scale * E_F) + Real.sqrt (scale * E_T)
  Real.sqrt ((δ ^ 2 + ε ^ 2) * Real.exp
    (positiveCutoffDriftConstant (AVenhance.streamVel φ)
      (classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀).drift_bounded ^ 2 / κ + 1))

/-- The explicit nested-path error tends to zero as the lower cutoff grows. -/
theorem classicalGalerkinScalarPathError_tendsto_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ)
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (E_F E_T : ℝ) :
    Tendsto (fun M => classicalGalerkinScalarPathError φ hφ κ hκ θ₀ hθ₀
      E_F E_T M) atTop (𝓝 0) := by
  let scale : ℕ → ℝ := fun M => (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹
  let δ : ℕ → ℝ := fun M =>
    Real.sqrt (scale M * AVenhance.gradNormSq (AVenhance.spaceGrad θ₀))
  let ε : ℕ → ℝ := fun M => Real.sqrt (scale M * E_F) + Real.sqrt (scale M * E_T)
  let H : ℝ := positiveCutoffDriftConstant (AVenhance.streamVel φ)
    (classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀).drift_bounded
  have hrealShift : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hrealShift' : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using hrealShift
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have hden : Tendsto (fun M : ℕ => 4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)
      atTop atTop := by
    simpa using (hpow.comp hrealShift').const_mul_atTop
      (show 0 < 4 * Real.pi ^ 2 by positivity)
  have hscale : Tendsto scale atTop (𝓝 0) := by
    change Tendsto (fun M => (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹)
      atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp hden
  have hroot (C : ℝ) : Tendsto (fun M => Real.sqrt (scale M * C)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun M => scale M * C) atTop (𝓝 0) := by
      simpa using hscale.mul_const C
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hmul
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using hroot (AVenhance.gradNormSq (AVenhance.spaceGrad θ₀))
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hroot E_F).add (hroot E_T)
  have hδsq : Tendsto (fun M => δ M ^ 2) atTop (𝓝 0) := by
    simpa [pow_two] using hδ.mul hδ
  have hεsq : Tendsto (fun M => ε M ^ 2) atTop (𝓝 0) := by
    simpa [pow_two] using hε.mul hε
  have hsum : Tendsto (fun M => δ M ^ 2 + ε M ^ 2) atTop (𝓝 0) := by
    simpa using hδsq.add hεsq
  have hinside : Tendsto (fun M => (δ M ^ 2 + ε M ^ 2) *
      Real.exp (H ^ 2 / κ + 1)) atTop (𝓝 0) := by
    simpa using hsum.mul_const (Real.exp (H ^ 2 / κ + 1))
  have houter := (Real.continuous_sqrt.tendsto 0).comp hinside
  have houter' : Tendsto
      (fun M => Real.sqrt ((δ M ^ 2 + ε M ^ 2) * Real.exp (H ^ 2 / κ + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using houter
  simpa [classicalGalerkinScalarPathError, scale, δ, ε, H] using houter'

/-- The smooth Galerkin scalar paths are Cauchy uniformly in time in torus `L²`. -/
theorem classicalGalerkinScalarPath_cauchy
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    CauchySeq (fun N => classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N) := by
  obtain ⟨E_F, -, hFenergy⟩ := classicalForcing_gradient_energy_uniform_bound F hF hFper
  obtain ⟨E_T, -, hTenergy⟩ := classicalGalerkinTransport_gradient_energy_uniform_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  let U := fun N => classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N
  let err := fun M => classicalGalerkinScalarPathError φ hφ κ hκ θ₀ hθ₀
    E_F E_T M
  have herr := classicalGalerkinScalarPathError_tendsto_zero
    φ hφ κ hκ θ₀ hθ₀ E_F E_T
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hnear : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
  obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1 (herr.eventually hnear))
  refine ⟨M₀, ?_⟩
  intro m hm n hn
  let K := min m n
  have hK : M₀ ≤ K := (Nat.le_min).2 ⟨hm, hn⟩
  have hsmall : err K < ε := hM₀ K hK
  have hnonneg : 0 ≤ err K := by
    dsimp [err, classicalGalerkinScalarPathError]
    positivity
  have hdist : dist (U m) (U n) ≤ err K := by
    rw [ContinuousMap.dist_le hnonneg]
    intro t
    rw [dist_eq_norm]
    rcases le_total m n with hmn | hnm
    · have hpath := classicalGalerkinScalarPath_nested_difference_norm_le
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per E_F E_T hFenergy hTenergy
        m n hmn (t : ℝ) t.property
      simpa [U, err, K, min_eq_left hmn, norm_sub_rev,
        classicalGalerkinScalarPathError] using hpath
    · have hpath := classicalGalerkinScalarPath_nested_difference_norm_le
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per E_F E_T hFenergy hTenergy
        n m hnm (t : ℝ) t.property
      simpa [U, err, K, min_eq_right hnm,
        classicalGalerkinScalarPathError] using hpath
  exact hdist.trans_lt hsmall

end AVenhance.Infra.Classical

end
