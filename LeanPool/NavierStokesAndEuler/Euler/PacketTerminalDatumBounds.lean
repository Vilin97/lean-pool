/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalDatum
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCompactBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
Actual mixed L² and fixed-Hq bounds for χ₁(y) fδ(θ) ξT.  All constants
are explicit: the only support factor is the fixed L² mass of the cutoff
support cylinder.  The one-time conversion from tensor jets to words
precedes the fixed-radius linear solves.
-/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerSpatialCutoffs EulerPeriodicProfile EulerGevreyCutoff
  EulerCylinderCompact EulerLpCylinderTranslation EulerGevrey EulerGevreyFunctions
  EulerParameterWordGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

/-- Jet radius, given by `64 + 40 * (δ^2)⁻¹`. -/
def jetRadius (δ : ℝ) : ℝ := 64 + 40 * (δ^2)⁻¹

/-- Scalar jet cost, given by `3 * (9 / rawBump 0)^3 * (100 * (δ^2)⁻¹)`. -/
def scalarJetCost (δ : ℝ) : ℝ := 3 * (9 / rawBump 0)^3 * (100 * (δ^2)⁻¹)

theorem jetRadius_nonneg (δ : ℝ) : 0 ≤ jetRadius δ := by
  unfold jetRadius
  positivity

theorem scalarJetCost_nonneg (δ : ℝ) : 0 ≤ scalarJetCost δ := by
  have := rawBump_pos_zero
  unfold scalarJetCost
  positivity

private theorem cutoffLift_bound (y : Space) (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => innerCutoff (y+b.1)) a‖ ≤
      (9 / rawBump 0)^3 * majorant 64 0 n := by
  let L : LiftTangent →L[ℝ] Space := ContinuousLinearMap.fst ℝ Space ℝ
  have hf : ContDiff ℝ ∞ (fun z : Space => innerCutoff (y+z)) :=
    innerCutoff_contDiff.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n ((fun z : Space => innerCutoff (y+z)) ∘ L) a‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf a (by simp)]
  rw [iteratedFDeriv_comp_add_left]
  have hn := (iteratedFDeriv ℝ n (fun z : Space => innerCutoff (y+z)) (L
      a)).norm_compContinuousLinearMap_le
    (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,iteratedFDeriv_comp_add_left] at hn
  have hp : ‖L‖^n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) (norm_fst_le ℝ Space ℝ) n
  exact hn.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans
    (by simpa only [mul_one] using innerCutoff_gevrey n (y+L a)))

theorem scalarField_jet_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (x : LiftDomain period) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (localFieldLift period (scalarField δ) x) a‖ ≤
      scalarJetCost δ * majorant (jetRadius δ) 0 n := by
  rcases x with ⟨y,θ⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective θ
  rw [← hs,local_scalarField]
  have hc : 0 ≤ (9 / rawBump 0)^3 := by have := rawBump_pos_zero; positivity
  have hp : 0 ≤ 100*(δ^2)⁻¹ := by positivity
  have hR₁ : (64 : ℝ) ≤ jetRadius δ := le_add_of_nonneg_right (by positivity)
  have hR₂ : 40*(δ^2)⁻¹ ≤ jetRadius δ := by unfold jetRadius; linarith
  have hb₁ (k : ℕ) (b : LiftTangent) :=
    (cutoffLift_bound y k b).trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono 64 (jetRadius δ) (by norm_num) hR₁ 0 k) hc)
  have hb₂ (k : ℕ) (b : LiftTangent) :
      ‖iteratedFDeriv ℝ k (fun z : LiftTangent => profile δ (s+z.2)) b‖ ≤
        (100*(δ^2)⁻¹) * majorant (jetRadius δ) 0 k := by
    have hh := affine_composition_bound (profile δ) (profile_contDiff δ hδ)
      (ContinuousLinearMap.snd ℝ Space ℝ) s (40*(δ^2)⁻¹) (100*(δ^2)⁻¹) 1
      (by positivity) hp (by norm_num) (norm_snd_le ℝ Space ℝ)
      (profile_gevrey δ hδ hδ1) k b
    simp only [mul_one,add_comm _ s] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono _ (jetRadius δ) (by positivity) hR₂ 0 k) hp)
  exact product_bound _ _
    (innerCutoff_contDiff.comp (contDiff_const.add contDiff_fst))
    ((profile_contDiff δ hδ).comp (contDiff_const.add contDiff_snd))
    (jetRadius δ) ((9/rawBump 0)^3) (100*(δ^2)⁻¹)
    (jetRadius_nonneg δ) hc hp hb₁ hb₂ n a

theorem field_jet_bound {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
    (n : ℕ) (x : LiftDomain period) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (localFieldLift period (field δ ξ) x) a‖ ≤
      (scalarJetCost δ * ‖ξ‖) * majorant (jetRadius δ) 0 n := by
  let L : ℝ →L[ℝ] U := toSpanSingleton ℝ ξ
  have hn := L.norm_iteratedFDeriv_comp_left
    ((scalarField_smooth δ hδ x).contDiffAt (x := a)) (n := n) (by simp)
  change ‖iteratedFDeriv ℝ n (L ∘ localFieldLift period (scalarField δ) x) a‖ ≤ _
  exact hn.trans ((mul_le_mul_of_nonneg_left (scalarField_jet_bound δ hδ hδ1 n x a)
    (norm_nonneg L)).trans_eq (by simp only [L,norm_toSpanSingleton]; ring))

/-- Terminal mass, given by `supportMass period supportSet supportSet_compact`. -/
def terminalMass : ℝ := supportMass period supportSet supportSet_compact

theorem terminalMass_nonneg : 0 ≤ terminalMass := norm_nonneg _

theorem terminal_jet_bound {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U) (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate period b (terminal δ hδ ξ)) a‖ ≤
      (scalarJetCost δ * ‖ξ‖ * terminalMass) * majorant (jetRadius δ) 0 n :=
  (compactField δ hδ ξ).translation_gevrey supportSet supportSet_compact (field_support δ ξ)
    (jetRadius δ) (scalarJetCost δ * ‖ξ‖) (fun k x => field_jet_bound δ hδ hδ1 ξ k x 0) n a

/-- Word radius, given by `sobolevCoefficientRadius ι (jetRadius δ)`. -/
def wordRadius (ι : Type*) [Fintype ι] (δ : ℝ) : ℝ :=
  sobolevCoefficientRadius ι (jetRadius δ)

/-- Word cost, given by `sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ *
terminalMass)`. -/
def wordCost (ι : Type*) [Fintype ι] (q : ℕ) (δ : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * terminalMass)

theorem terminal_block_bound {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => translate period b (terminal δ hδ ξ)) n a ≤
      sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * ‖ξ‖ * terminalMass) *
        majorant (wordRadius ι δ) 0 n :=
  (compactField δ hδ ξ).translation_block_bound directions hd q supportSet supportSet_compact
    (field_support δ ξ) (jetRadius δ) (scalarJetCost δ * ‖ξ‖)
    (jetRadius_nonneg δ) (mul_nonneg (scalarJetCost_nonneg δ) (norm_nonneg ξ))
    (fun k x => field_jet_bound δ hδ hδ1 ξ k x 0) n a

end EulerPacketTerminalDatum
