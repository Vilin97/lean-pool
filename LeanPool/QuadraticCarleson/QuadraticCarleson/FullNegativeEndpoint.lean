/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.NegativeEndpoint

/-!
# The full negative endpoint by pointwise domination

The full modulation set contains `2^ℤ`. Thus the full quadratic Carleson
supremum pointwise dominates the lacunary one, and failure of every
sub-`L log₂ L` modular estimate transfers immediately. No continuity or
density argument in the modulation parameter is involved.

We state the modular predicate directly for a function-valued operator. This
is slightly stronger than first bundling measurability: even the bare global
outer-measure inequality is impossible. Whenever the operator is measurable,
this predicate is definitionally the paper's `HasPhiModularEstimate`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson


/-- The full real-modulation supremum of the canonical symmetric-truncation
`limsup` on the paper's `L0Infinity` test domain. -/
noncomputable def quadraticCarlesonL0 (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ modulation : ℝ, quadraticHilbertL0Limsup modulation f x

/-- The elementary inclusion `2^ℤ ⊆ ℝ`, expressed as the pointwise
operator inequality used in the paper. -/
theorem lacunaryQuadraticCarlesonL0_le_quadraticCarlesonL0
    (f : L0Infinity) (x : ℝ) :
    lacunaryQuadraticCarlesonL0 f x ≤ quadraticCarlesonL0 f x := by
  apply iSup_le
  intro n
  exact le_iSup
    (fun modulation : ℝ ↦ quadraticHilbertL0Limsup modulation f x)
    (dyadicModulation n)

/-- Strict level set of an arbitrary extended-nonnegative operator function. -/
def functionOperatorLevelSet
    (T : L0Infinity → ℝ → ℝ≥0∞) (f : L0Infinity) (α : ℝ) : Set ℝ :=
  {x | ENNReal.ofReal α < T f x}

/-- The paper's modular inequality, stated without a redundant measurability
field on the operator. Its failure therefore also covers every measurable
realization of the same pointwise supremum. -/
def HasFunctionPhiModularEstimate
    (Phi : YoungFunction) (T : L0Infinity → ℝ → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
    volume (functionOperatorLevelSet T f α) ≤
      ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖ / α))

theorem hasFunctionPhiModularEstimate_iff
    (Phi : YoungFunction) (T : NonnegativeOperator) :
    HasFunctionPhiModularEstimate Phi T ↔ HasPhiModularEstimate Phi T := by
  rfl

/-- The full real-modulation operator has no modular estimate below
`L log₂ L`, solely because it pointwise dominates the lacunary operator. -/
theorem fullNegativeEndpoint_not_hasPhiModularEstimate
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi quadraticCarlesonL0 := by
  intro hfull
  apply negativeEndpoint_not_hasPhiModularEstimate Phi hPhi
  rw [← hasFunctionPhiModularEstimate_iff]
  obtain ⟨C, hC, hbound⟩ := hfull
  refine ⟨C, hC, fun f α hα ↦ ?_⟩
  apply (measure_mono ?_).trans (hbound f α hα)
  intro x hx
  exact hx.trans_le (lacunaryQuadraticCarlesonL0_le_quadraticCarlesonL0 f x)

/-- The paper's normalized witnesses for the lacunary operator are also
witnesses for the full real-modulation supremum. -/
theorem fullNegativeEndpoint_exists_paper_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa *
          volume (functionOperatorLevelSet quadraticCarlesonL0 f 1) := by
  obtain ⟨f, hf⟩ :=
    negativeEndpoint_exists_paper_modular_witness Phi hPhi hkappa
  refine ⟨f, hf.trans_le ?_⟩
  gcongr
  intro x hx
  exact hx.trans_le (lacunaryQuadraticCarlesonL0_le_quadraticCarlesonL0 f x)

end QuadraticCarleson
