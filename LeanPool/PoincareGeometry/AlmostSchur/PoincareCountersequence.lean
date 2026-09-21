/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyAlgebra
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Normalized countersequences to the intrinsic Poincaré inequality

Failure of a uniform inequality supplies witnesses with arbitrarily large
L²-to-energy ratio. Scaling by the reciprocal L² norm gives unit L² norm
and square-root energy bounded by `1 / (n + 1)`. No compactness or connectedness
is needed in this normalization step.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]

local instance poincareCountersequenceContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance poincareCountersequenceFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Negating Poincaré produces actual unit-L², mean-zero C¹ functions with
square-root energy at most `1 / (n + 1)`. The L² witnesses are constructed. -/
theorem exists_poincare_countersequence
    (hfail : ¬ ∃ C : ℝ, 0 < C ∧ ∀ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      (∫ x, f x ∂riemannianVolume (I := I)) = 0 →
      lpNorm f 2 (riemannianVolume (I := I)) ≤
        C * Real.sqrt (dirichletForm (I := I) f f)) :
    ∃ f : ℕ → M → ℝ, ∃ hfLp : ∀ n, MemLp (f n) 2 (riemannianVolume (I := I)),
      (∀ n, ContMDiff I 𝓘(ℝ, ℝ) 1 (f n)) ∧
      (∀ n, (∫ x, f n x ∂riemannianVolume (I := I)) = 0) ∧
      (∀ n, ‖(hfLp n).toLp (f n)‖ = 1) ∧
      (∀ n, Real.sqrt (dirichletForm (I := I) (f n) (f n)) ≤ 1 / ((n : ℝ) + 1)) := by
  classical
  have hw (n : ℕ) : ∃ g : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) 1 g ∧
      (∫ x, g x ∂riemannianVolume (I := I)) = 0 ∧
      ((n : ℝ) + 1) * Real.sqrt (dirichletForm (I := I) g g) <
        lpNorm g 2 (riemannianVolume (I := I)) := by
    by_contra hn
    push Not at hn
    exact hfail ⟨(n : ℝ) + 1, by positivity, fun g hg hm => hn g hg hm⟩
  choose g hg hm hratio using hw
  let L (n : ℕ) := lpNorm (g n) 2 (riemannianVolume (I := I))
  have hL (n : ℕ) : 0 < L n :=
    lt_of_le_of_lt (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (hratio n)
  let f (n : ℕ) (x : M) := (L n)⁻¹ * g n x
  have hf (n : ℕ) : ContMDiff I 𝓘(ℝ, ℝ) 1 (f n) :=
    contMDiff_const.mul (hg n)
  have hfLp (n : ℕ) : MemLp (f n) 2 (riemannianVolume (I := I)) :=
    (hf n).continuous.memLp_of_hasCompactSupport isClosed_closure.isCompact
  refine ⟨f, hfLp, hf, ?_, ?_, ?_⟩
  · intro n
    change (∫ x, (L n)⁻¹ * g n x ∂riemannianVolume (I := I)) = 0
    rw [integral_const_mul, hm n, mul_zero]
  · intro n
    rw [Lp.norm_toLp, toReal_eLpNorm]
    change lpNorm ((L n)⁻¹ • g n) 2 (riemannianVolume (I := I)) = 1
    rw [lpNorm_const_smul]
    change |(L n)⁻¹| * L n = 1
    rw [abs_of_pos (inv_pos.mpr (hL n)), inv_mul_cancel₀ (hL n).ne']
  · intro n
    change Real.sqrt (dirichletForm (I := I)
      (fun x => (L n)⁻¹ * g n x) (fun x => (L n)⁻¹ * g n x)) ≤ _
    rw [sqrt_dirichletForm_const_mul_self _ _ (hg n),
      abs_of_pos (inv_pos.mpr (hL n))]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    apply (le_div_iff₀ hn).2
    have hr : ((n : ℝ) + 1) * Real.sqrt (dirichletForm (I := I) (g n) (g n)) ≤ L n :=
      (hratio n).le
    have hh := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (hL n).le)
    rw [inv_mul_cancel₀ (hL n).ne'] at hh
    nlinarith

end AlmostSchur
