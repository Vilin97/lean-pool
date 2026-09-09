/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourcePiola
public import LeanPool.NavierStokesAndEuler.Euler.PacketJetAssembly

@[expose] public section

/-! The actual finite joined packet, including its terminal corrector, satisfies the lifted
  constraint. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerFiniteGrades
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

def joinedPacketPullbackField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame z
      (fieldSum (N+1) κ (assembledVelocity N (joinedSourceProfiles P M D τ hτ hτT B primary)) z))
        := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let term := fun i : ℕ =>
    (joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).add
      ((joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).smul (κ^(i+1)))
  let total := Field.finsetSum (range N) _ term
  refine total.congr ?_
  intro t x θ
  have ha0 : a 0 = 0 := profiles_zero _ _
  have hu0 : (a 0).high+(a 0).mean = (0 : VectorField) := by rw [ha0]; simp
  have hc0 : (a 0).corrector = (0 : VectorField) := by rw [ha0]; rfl
  have he := fieldSum_assemble_from_one N κ (fun i => (a i).high+(a i).mean)
    (fun i => (a i).corrector) hu0 hc0 (t,(x,θ))
  change (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
    (fieldSum (N+1) κ (assemble N (fun i => (a i).high+(a i).mean)
      (fun i => (a i).corrector)) (t,(x,θ))) = _
  rw [he,map_sum,Finset.sum_apply]
  apply sum_congr rfl
  intro i _
  change (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
      (κ^(i+1) • ((a (i+1)).high (t,(x,θ))+(a (i+1)).mean (t,(x,θ))) +
        κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) =
    (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
      (κ^(i+1) • (a (i+1)).high (t,(x,θ)) + κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) +
      κ^(i+1) • (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ)) ((a (i+1)).mean
        (t,(x,θ)))
  simp only [map_add,map_smul,smul_add]
  abel

theorem joinedPacketPullbackField_path (N : ℕ) (κ : ℝ) :
    (joinedPacketPullbackField P M D hT τ hτ hτT B primary hprimary N κ).path =
      ∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path) := rfl

theorem joinedPacketPullbackField_mem
    (hmean : primary.mean = 0)
    (hc : primary.corrector = D.curlCorrector P primary.high)
    (hm : ∀ (t : Icc (0 : ℝ) M.T) x, (∫ θ in (0 : ℝ)..P, primary.high (t,(x,θ))) = 0)
    (ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (D.normalField (t,(x,θ))) (primary.high (t,(x,θ))) = 0)
    (A : SourceCoefficientAgreement M D) (N : ℕ) (κ : ℝ) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (joinedPacketPullbackField P M D hT τ hτ hτT B primary hprimary N κ).path t ∈
      divergenceFreeSpace P κ D.m₀ := by
  rw [joinedPacketPullbackField_path]
  have he : (∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path)) t =
      ∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path t +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path t) :=
    map_sum (ContinuousMap.evalCLM ℝ t) _ (range N)
  rw [he]
  apply (divergenceFreeSpace P κ D.m₀).sum_mem
  intro i _
  apply (divergenceFreeSpace P κ D.m₀).add_mem
  · exact joinedPairField_mem P M D hT τ hτ hτT B primary hprimary hc hm ht κ (i+1) (by omega) t Ξ
    hΞ hF hdet
  · exact (divergenceFreeSpace P κ D.m₀).smul_mem (κ^(i+1))
      (joinedMeanPullbackField_mem P M D hT τ hτ hτT B primary hprimary hmean A κ D.m₀ (i+1) t)

end EulerPacketCylinderField
