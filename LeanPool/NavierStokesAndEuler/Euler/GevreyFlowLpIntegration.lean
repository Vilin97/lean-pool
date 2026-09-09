/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyJetCompositionLp
public import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral

@[expose] public section

/-! The all-order L² step for a volume-preserving flow.  The spatial base
may be a periodic cylinder.  The output is the actual time integral of
the finite Taylor composition; identifying it with the displacement jet
uses the already constructed flow's differentiated integral equation. -/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Interval

namespace EulerGevreyFlowLpIntegration

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform positive inner-jet bounds and the outer L² bounds imply an
L² bound for the actual integrated composition at every finite order. -/
theorem integrated_composition_bound
    (T : ℝ) (hT : 0 ≤ T) (μ : Measure X) [SFinite μ]
    (φ : ℝ → X → X) (hφ : ∀ t ∈ Icc 0 T, MeasurePreserving (φ t) μ μ)
    (P : ℝ → X → FormalMultilinearSeries ℝ E E)
    (Q : ℝ → X → FormalMultilinearSeries ℝ E F) (n : ℕ)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × X => (Q p.1 (φ p.1 p.2)).taylorComp (P p.1 p.2) n)
      ((volume.restrict (Icc 0 T)).prod μ))
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hQLp : ∀ t ∈ Icc 0 T, ∀ j ≤ n, MemLp (fun x => Q t x j) 2 μ)
    (hQ : ∀ t ∈ Icc 0 T, ∀ j ≤ n,
      (eLpNorm (fun x => Q t x j) 2 μ).toReal ≤ A*S^j*(j.factorial : ℝ)^2)
    (hP : ∀ t ∈ Icc 0 T, ∀ j, 0 < j → j ≤ n → ∀ x,
      ‖P t x j‖ ≤ B*R^j*(j.factorial : ℝ)^2) :
    MemLp (fun x => ∫ t in 0..T, (Q t (φ t x)).taylorComp (P t x) n) 2 μ ∧
      (eLpNorm (fun x => ∫ t in 0..T, (Q t (φ t x)).taylorComp (P t x) n) 2 μ).toReal ≤
        T*A*(R*(B*S+2))^n*(n.factorial : ℝ)^2 := by
  let C := A*(R*(B*S+2))^n*(n.factorial : ℝ)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      MemLp (fun x => (Q t (φ t x)).taylorComp (P t x) n) 2 μ ∧
        (eLpNorm (fun x => (Q t (φ t x)).taylorComp (P t x) n) 2 μ).toReal ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hm.prodMk_left] with t ht hmt
    exact EulerGevreyJetCompositionLp.composition_memLp_and_bound μ (φ t) (hφ t ht)
      (P t) (Q t) n hmt A B R S hA hB hR hS (hQLp t ht) (hQ t ht) (hP t ht)
  obtain ⟨hLp,hNorm⟩ := EulerLpParameterIntegral.intervalIntegral_memLp_and_bound
    T hT μ (fun p : ℝ × X => (Q p.1 (φ p.1 p.2)).taylorComp (P p.1 p.2) n) hm C hC hbound
  refine ⟨hLp,hNorm.trans_eq ?_⟩
  dsimp [C]
  ring

end EulerGevreyFlowLpIntegration
