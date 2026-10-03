/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.KeystoneStatements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyReal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyDissipation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyClosure
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Nonempty
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.ExistsIsStreamSeq

/-! # Main theorem from the three statements

`anomalous_dissipation_of_keystones` derives the main theorem (`t.anomalous.diffusion`) from the
    literal
statements of the estimates step-down estimate, classical well-posedness and stream-function
    estimates.  Everything else (choice of `β`,
ingredients, stream sequence, Hölder / `∃ b` packaging, later-start cascade, `H¹` reduction) is
    proved.
The statement files themselves are never imported. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- The pointwise limit of periodic streams is periodic. -/
theorem AnomalousDissipation.limit_periodic {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) (t : ℝ) :
    IsZ2Periodic (φ t) := by
  intro n x
  refine tendsto_nhds_unique (htend t (x + latticeShift n)) ?_
  have h := htend t x
  refine h.congr fun M => ?_
  have := (hΦ M).2 0 n t x
  simpa using this.symm

/-- The pointwise limit of admissible streams is jointly measurable. -/
theorem AnomalousDissipation.limit_aestronglyMeasurable {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (μ : Measure (ℝ × Vec 2)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2) μ := by
  have hm : Measurable (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    measurable_of_tendsto_metrizable (f := fun M (p : ℝ × Vec 2) => Φ M p.1 p.2)
      (fun M => (hΦ M).1.continuous.measurable)
      (tendsto_pi_nhds.2 fun p => htend p.1 p.2)
  exact hm.aestronglyMeasurable

/-- Numerical choice of the exponent `β`. -/
theorem AnomalousDissipation.exists_beta (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ β : ℝ, 6 / 5 ≤ β ∧ α < β - 1 ∧ β < 4 / 3 ∧ 1 < β := by
  have h1 := le_max_left (6 / 5 : ℝ) (1 + α)
  have h2 := le_max_right (6 / 5 : ℝ) (1 + α)
  have h3 : max (6 / 5 : ℝ) (1 + α) < 4 / 3 := max_lt (by norm_num) (by linarith)
  refine ⟨(max (6 / 5) (1 + α) + 4 / 3) / 2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Main theorem from the three estimates.**  The main theorem follows from the literal
    statements of step-down estimate, classical well-posedness and
Stream-function estimates; everything else is proved. -/
theorem anomalous_dissipation_of_keystones
    (hA8 : ∀ β C₀ : ℝ, IndyStepDownStatement β C₀)
    (hA1c : ClassicalWellposedStatement)
    (hA3b : ∀ β : ℝ, LimitFieldRegularStatement β) :
    AnomalousDissipationStatement := by
  intro α hα₀ hα₁
  obtain ⟨β, hβ65, hαβ, hβ43, hβ1⟩ := AnomalousDissipation.exists_beta α hα₀ hα₁
  obtain ⟨C₀, -, hnon⟩ := Ingredients.nonempty β hβ1 hβ43
  obtain ⟨Λ₀, hrel⟩ := RelativeError.anomalous_dissipation_of_relative β C₀ hβ65 (hA8 β C₀)
  obtain ⟨I, hIΛ, hz, hx, hh⟩ := hnon (max (2 ^ 7) ⌈Λ₀⌉₊) (le_max_left _ _)
  have hΛ : Λ₀ ≤ (I.Λ : ℝ) := by
    rw [hIΛ]
    exact (Nat.le_ceil Λ₀).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨Φ, hΦ⟩ := exists_isStreamSeq I
  have hadm : ∀ M, IsAdmissibleStream (Φ M) := streamSeq_isAdmissible hΦ
  obtain ⟨C, hC1, hlim⟩ := hA3b β
  obtain ⟨φ, htend, htail, hdiff, -, hhol⟩ := hlim I Φ hΦ
  obtain ⟨hHolder, hdiv⟩ := hhol α hα₀ hαβ
  have hsolv : ∀ j : ℕ, RelativeError.ClassicalSolvable (streamVel (Φ j)) := by
    intro j ν hν g hg hgp F hF hFp
    exact (hA1c (Φ j) (hadm j) ν hν F hF hFp g hg hgp).imp fun θ hθ => hθ.1
  have hcont := hHolder.2.1
  have hbp := hHolder.1
  have hbb := hHolder.2.2.1
  obtain ⟨ϱ, hϱ, hmain⟩ := hrel I hz hx hh hΛ Φ hΦ hsolv C hC1 φ
    (AnomalousDissipation.limit_aestronglyMeasurable hadm htend _)
    (fun t _ => AnomalousDissipation.limit_periodic hadm htend t)
    (fun t _ => hdiff t)
    (fun M _ t _ x => htail M t x)
    (hcont.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ))
    hbb hbp hdiv
  exact ⟨streamVel φ, hHolder, hdiv, ϱ, hϱ, hmain⟩

end AVenhance.Infra.Section5.Integration
