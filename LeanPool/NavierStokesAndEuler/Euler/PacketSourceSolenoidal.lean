/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePiola
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanSolenoidal
public import LeanPool.NavierStokesAndEuler.Euler.PacketJetAssembly

@[expose] public section

/-!
# The actual finite source packet satisfies the lifted L² constraint

The terminal corrector is retained in the finite assembly. Each genuine Piola
pair and every inverse-frame mean belongs to the same closed constraint space.
-/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerFiniteGrades
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

def sourcePacketPullbackField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => (sourceOperators P M D I).inverseFrame z
      (fieldSum (N+1) κ (assembledVelocity N (sourceProfiles P M D I Iprimary)) z)) := by
  let a := sourceProfiles P M D I Iprimary
  let term := fun i : ℕ =>
    (sourcePairField P M D hT I Iprimary κ (i+1)).add
      ((sourceMeanPullbackField P M D hT I Iprimary (i+1)).smul (κ^(i+1)))
  let total := Field.finsetSum (range N) _ term
  refine total.congr ?_
  intro t x θ
  have ha0 : a 0 = 0 := profiles_zero _ _
  have hu0 : (a 0).high+(a 0).mean = (0 : VectorField) := by rw [ha0]; simp
  have hc0 : (a 0).corrector = (0 : VectorField) := by rw [ha0]; rfl
  have he := fieldSum_assemble_from_one N κ (fun i => (a i).high+(a i).mean)
    (fun i => (a i).corrector) hu0 hc0 (t,(x,θ))
  change (sourceOperators P M D I).inverseFrame (t,(x,θ))
    (fieldSum (N+1) κ (assemble N (fun i => (a i).high+(a i).mean)
      (fun i => (a i).corrector)) (t,(x,θ))) = _
  rw [he,map_sum,Finset.sum_apply]
  apply sum_congr rfl
  intro i _
  change (sourceOperators P M D I).inverseFrame (t,(x,θ))
      (κ^(i+1) • ((a (i+1)).high (t,(x,θ))+(a (i+1)).mean (t,(x,θ))) +
        κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) =
    (sourceOperators P M D I).inverseFrame (t,(x,θ))
      (κ^(i+1) • (a (i+1)).high (t,(x,θ)) + κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) +
      κ^(i+1) • (sourceOperators P M D I).inverseFrame (t,(x,θ)) ((a (i+1)).mean (t,(x,θ)))
  simp only [map_add,map_smul,smul_add]
  abel

theorem sourcePacketPullbackField_path (N : ℕ) (κ : ℝ) :
    (sourcePacketPullbackField P M D hT I Iprimary N κ).path =
      ∑ i ∈ range N, ((sourcePairField P M D hT I Iprimary κ (i+1)).path +
        κ^(i+1) • (sourceMeanPullbackField P M D hT I Iprimary (i+1)).path) := rfl

theorem sourcePacketPullbackField_mem (A : SourceCoefficientAgreement M D)
    (N : ℕ) (κ : ℝ) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (sourcePacketPullbackField P M D hT I Iprimary N κ).path t ∈ divergenceFreeSpace P κ D.m₀ := by
  rw [sourcePacketPullbackField_path]
  have he : (∑ i ∈ range N, ((sourcePairField P M D hT I Iprimary κ (i+1)).path +
        κ^(i+1) • (sourceMeanPullbackField P M D hT I Iprimary (i+1)).path)) t =
      ∑ i ∈ range N, ((sourcePairField P M D hT I Iprimary κ (i+1)).path t +
        κ^(i+1) • (sourceMeanPullbackField P M D hT I Iprimary (i+1)).path t) :=
    map_sum (ContinuousMap.evalCLM ℝ t) _ (range N)
  rw [he]
  apply (divergenceFreeSpace P κ D.m₀).sum_mem
  intro i _
  apply (divergenceFreeSpace P κ D.m₀).add_mem
  · exact sourcePairField_mem P M D hT I Iprimary κ (i+1) (by omega) t Ξ hΞ hF hdet
  · exact (divergenceFreeSpace P κ D.m₀).smul_mem (κ^(i+1))
      (sourceMeanPullbackField_mem P M D hT I Iprimary A κ D.m₀ (i+1) t)

end EulerPacketCylinderField
