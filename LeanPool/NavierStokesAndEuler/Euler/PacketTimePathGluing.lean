/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeIntervalGlue
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Gluing matching continuous paths is one fixed linear contraction. -/

@[expose] public section


noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerTimeIntervalGlue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance compactInterval (a b : ℝ) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Pair: an abbreviation for `C(Icc (0 : ℝ) τ,E) × C(Icc τ S,E)`. -/
abbrev Pair (S τ : ℝ) (E : Type*) [TopologicalSpace E] :=
  C(Icc (0 : ℝ) τ,E) × C(Icc τ S,E)

/-- Mismatch as an element of `Pair S τ E →L[ℝ] E`. -/
def mismatch (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Pair S τ E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ ⟨τ,hτ0,le_rfl⟩).comp
      (ContinuousLinearMap.fst ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E)) -
    (ContinuousMap.evalCLM ℝ ⟨τ,le_rfl,hτS⟩).comp
      (ContinuousLinearMap.snd ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E))

/-- Matching: an abbreviation for `(mismatch (E := E) S τ hτ0 hτS).ker`. -/
abbrev Matching (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Submodule ℝ (Pair S τ E) :=
  (mismatch (E := E) S τ hτ0 hτS).ker

theorem matching_values (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) :
    u.val.1 ⟨τ,hτ0,le_rfl⟩=u.val.2 ⟨τ,le_rfl,hτS⟩ := by
  have h : mismatch S τ hτ0 hτS u.val=0 := u.property
  exact sub_eq_zero.mp h

/-- Glue path as an element of `C(Icc (0 : ℝ) S,E)`. -/
def gluePath (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) : C(Icc (0 : ℝ) S,E) :=
  ⟨fun t => glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
      (fun r => u.val.2 (projIcc τ S hτS r)) t,
    (glue_continuous τ _ _ (by
      simpa only [Function.comp_def, projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
        projIcc_of_mem hτS ⟨le_rfl,hτS⟩] using matching_values S τ hτ0 hτS u)
      (u.val.1.continuous.comp continuous_projIcc)
      (u.val.2.continuous.comp continuous_projIcc)).comp continuous_subtype_val⟩

theorem gluePath_norm_le (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) : ‖gluePath S τ hτ0 hτS u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  change ‖glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t‖ ≤ ‖u‖
  by_cases ht : (t : ℝ) ≤ τ
  · rw [glue_left τ _ _ t ht]
    exact (u.val.1.norm_coe_le_norm _).trans (norm_fst_le u.val)
  · simp only [glue, ht, ite_false]
    exact (u.val.2.norm_coe_le_norm _).trans (norm_snd_le u.val)

/-- Glue operator as an element of `Matching (E := E) S τ hτ0 hτS →L[ℝ] C(Icc (0 : ℝ) S,E)`. -/
def glueOperator (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Matching (E := E) S τ hτ0 hτS →L[ℝ] C(Icc (0 : ℝ) S,E) :=
  ({ toFun := gluePath S τ hτ0 hτS
     map_add' := by
       intro u v
       ext t
       by_cases ht : (t : ℝ) ≤ τ <;> simp [gluePath, glue, ht]
     map_smul' := by
       intro c u
       ext t
       by_cases ht : (t : ℝ) ≤ τ <;> simp [gluePath, glue, ht] } :
      Matching (E := E) S τ hτ0 hτS →ₗ[ℝ] C(Icc (0 : ℝ) S,E)).mkContinuous
    1 (fun u => by
      change ‖gluePath S τ hτ0 hτS u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using gluePath_norm_le S τ hτ0 hτS u)

theorem glueOperator_norm_le_one (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    ‖glueOperator (E := E) S τ hτ0 hτS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖gluePath S τ hτ0 hτS u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using gluePath_norm_le S τ hτ0 hτS u

end EulerPacketTimePathGluing
