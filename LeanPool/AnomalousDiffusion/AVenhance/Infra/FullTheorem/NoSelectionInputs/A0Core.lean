/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.KeystoneStatements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyReal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyDissipation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyClosure
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IndyStepDown
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.ExistsIsStreamSeq

/-! # `A0CoreContract`: the main theorem at ingredient level

The content of the main theorem, for the given stream sequence and limit field
(the limit field from the regularity estimates agrees with the given one by uniqueness of limits).
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance AVenhance.Infra.Section5

/-- The pointwise limit of periodic streams is periodic. -/
theorem limit_periodic {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
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
theorem limit_aestronglyMeasurable {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (μ : Measure (ℝ × Vec 2)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2) μ := by
  have hm : Measurable (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    measurable_of_tendsto_metrizable (f := fun M (p : ℝ × Vec 2) => Φ M p.1 p.2)
      (fun M => (hΦ M).1.continuous.measurable)
      (tendsto_pi_nhds.2 fun p => htend p.1 p.2)
  exact hm.aestronglyMeasurable

theorem a0Core (β C₀ : ℝ) (hβ : 6 / 5 ≤ β) : A0CoreContract β C₀ := by
  obtain ⟨Λ₀, hrel⟩ := RelativeError.anomalous_dissipation_of_relative β C₀ hβ
    (AVenhance.indystepdown β C₀)
  refine ⟨Λ₀, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  have hadm : ∀ M, IsAdmissibleStream (Φ M) := streamSeq_isAdmissible hΦ
  obtain ⟨C, hC1, hlim⟩ := AVenhance.limit_field_regular β
  obtain ⟨φ', htend', htail, hdiff, -, hhol⟩ := hlim I Φ hΦ
  have hφφ : φ' = φ := by
    funext t x
    exact tendsto_nhds_unique (htend' t x) (htend t x)
  subst hφφ
  have hβ1 : 1 < β := I.one_lt_beta
  have hα0 : 0 < (β - 1) / 2 := by linarith
  have hα1 : (β - 1) / 2 < β - 1 := by linarith
  obtain ⟨hHolder, hdiv⟩ := hhol _ hα0 hα1
  have hsolv : ∀ j : ℕ, RelativeError.ClassicalSolvable (streamVel (Φ j)) := by
    intro j ν hν g hg hgp F hF hFp
    exact (AVenhance.classical_wellposed (Φ j) (hadm j) ν hν F hF hFp g hg hgp).imp
      fun θ hθ => hθ.1
  exact hrel I hz hx hh hΛ Φ hΦ hsolv C hC1 φ'
    (limit_aestronglyMeasurable hadm htend _)
    (fun t _ => limit_periodic hadm htend t)
    (fun t _ => hdiff t)
    (fun M _ t _ x => htail M t x)
    (hHolder.2.1.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ))
    hHolder.2.2.1 hHolder.1 hdiv

end AVenhance.Infra.FullTheorem.NoSelectionInputs
