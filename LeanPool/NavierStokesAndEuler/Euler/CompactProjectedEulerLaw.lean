/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CompactSolenoidalDensity
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.CompactProjectedPairing
import LeanPool.NavierStokesAndEuler.Euler.ProjectedEulerPairing

/-!
# The Comparator solution satisfies the weak projected Euler equation

The test family is the dense family of compact smooth solenoidal fields.
Only pointwise identification of the supplied smooth `L²` fields with the
Comparator velocity is assumed; no time regularity of those fields is used.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

private theorem inner_smoothField_eq_integral
    (g : L2) (φ : Space → Space) (hg : (g : Space → Space) =ᵐ[volume] φ)
    (A : SmoothL2Field Space) :
    inner ℝ g A.toLp = ∫ x, inner ℝ (φ x) (A.field x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg, A.toLp_ae] with x hgx hAx
  rw [hgx, hAx]

/-- An arbitrary compact smooth solenoidal representative has the clamped
weak projected derivative used by the Sobolev time-upgrade theorem. -/
theorem comparator_compact_rep_pairing_hasDerivAt
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ} (hT : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ s, (A s).field = (v · s))
    (g : solenoidalSpace) (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφdiv : ∀ x, EulerSmoothLimit.divergence φ x = 0)
    (hg : ((g : L2) : Space → Space) =ᵐ[volume] φ)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => inner ℝ (g : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t := by
  have hd := comparator_clamped_compact_pairing_hasDerivAt h hT A hA
    (g : L2) φ hφ hφc hφdiv hg t ht
  have hR : -(∫ x, inner ℝ (φ x) (fderiv ℝ (v · t) x (v x t))) =
      inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp := by
    rw [EulerCompactProjectedPairing.inner_projectedRhs _ g.property,
      inner_smoothField_eq_integral _ φ hg]
    simp only [advectionField_field, hA]
  rwa [hR] at hd

/-- The exact weak projected derivative on the dense compact solenoidal
test family. This is derived from the Comparator Euler equation itself. -/
theorem comparator_projected_pairing_hasDerivAt
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ} (hT : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ s, (A s).field = (v · s))
    (g : solenoidalSpace) (hg : g ∈ compactSolenoidalTests)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => inner ℝ (g : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t := by
  obtain ⟨φ, hφ, hφc, hφdiv, hgrep⟩ := compactSolenoidalTests_representation g hg
  exact comparator_compact_rep_pairing_hasDerivAt h hT A hA g φ
    hφ hφc hφdiv hgrep t ht

end Euler.ComparatorBridge
