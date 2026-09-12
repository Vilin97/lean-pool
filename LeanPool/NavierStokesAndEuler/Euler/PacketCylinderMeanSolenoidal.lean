/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.CylinderClassicalSolenoidal
import LeanPool.NavierStokesAndEuler.Euler.MeanCylinderSolenoidal
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract

/-! The actual inverse-frame mean profiles satisfy the closed lifted divergence constraint. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSmoothOrbit EulerCylinderClassicalSolenoidal EulerMeanCylinderSolenoidal
  EulerPacketPointJets EulerPacketProfileRecursion EulerVectorCalculus
open scoped ContDiff

theorem Field.mem_divergenceFree_of_angleIndependent {P T : ℝ} [Fact (0 < P)]
    {raw : VectorField} (G : Field P T raw) (κ : ℝ) (m : Space)
    (t : Icc (0 : ℝ) T)
    (ha : ∀ x θ, raw (t, (x, θ)) = raw (t, (x, 0)))
    (hd : ∀ x, divergence (fun y : Space => raw (t,(y,0))) x = 0) :
    G.path t ∈ divergenceFreeSpace P κ m := by
  let f : Space → Space := fun y => raw (t,(y,0))
  have hf : ContDiff ℝ ∞ f := (G.raw_smooth t).comp (contDiff_id.prodMk contDiff_const)
  have hr : (G.path t : LiftDomain P → Space) =ᵐ[liftMeasure P] fun z => f z.1 := by
    filter_upwards [pointField_ae P G.path G.orbit t] with z hz
    obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
    have he := (G.raw_eq t z.1 θ).symm.trans (ha z.1 θ)
    rw [hθ] at he
    exact hz.trans he
  apply mem_of_classical P κ m (G.path t) (fun z : LiftDomain P => f z.1) hr
  · intro z
    exact hf.comp (contDiff_const.add contDiff_fst)
  · exact lift_classical_divergence P κ m f hf hd

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

/-- Source mean pullback field, given by `(sourceCoefficientData P M D I hT).inverse.multiply
(sourceProfileWitness P M D hT I Iprimary p).mean`. -/
def sourceMeanPullbackField (p : ℕ) :
    Field P M.T (fun z => (sourceOperators P M D I).inverseFrame z
      ((sourceProfiles P M D I Iprimary p).mean z)) :=
  (sourceCoefficientData P M D I hT).inverse.multiply
    (sourceProfileWitness P M D hT I Iprimary p).mean

include hT in
theorem sourceMeanPullback_divergence (A : SourceCoefficientAgreement M D)
    (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) :
    divergence (fun y : Space => (sourceOperators P M D I).inverseFrame (t,(y,0))
      ((sourceProfiles P M D I Iprimary p).mean (t,(y,0)))) x = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change divergence (fun y : Space => (sourceOperators P M D I).inverseFrame (t,(y,0)) 0) x = 0
    simp [divergence]
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    simp [divergence]
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceMeanForcing P M D hT I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      EulerPacketProfileRecursion.step (sourceOperators P M D I) p (sourceProfiles P M D I
          Iprimary) :=
    profiles_step _ _ p hp
  have hf : (fun y : Space => (sourceOperators P M D I).inverseFrame (t,(y,0))
      ((sourceProfiles P M D I Iprimary p).mean (t,(y,0)))) =
      fun y => M.inverseFrame (t,(y,0))
        ((EulerMeanPacketProvider.meanSolve M
          (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(y,0)))
              := by
    funext y
    rw [sourceInverse_eq_mean P M D I A t y 0,he]
    rfl
  rw [hf]
  exact EulerMeanPacketProvider.meanSolve_divergence M _ h t x 0

theorem sourceMeanPullbackField_mem (A : SourceCoefficientAgreement M D) (κ : ℝ) (m : Space)
    (p : ℕ) (t : Icc (0 : ℝ) M.T) :
    (sourceMeanPullbackField P M D hT I Iprimary p).path t ∈ divergenceFreeSpace P κ m := by
  apply Field.mem_divergenceFree_of_angleIndependent _ κ m t
  · intro x θ
    change D.FInv.field (D.clamp t) x ((sourceProfiles P M D I Iprimary p).mean (t,(x,θ))) =
      D.FInv.field (D.clamp t) x ((sourceProfiles P M D I Iprimary p).mean (t,(x,0)))
    rw [(sourceProfileWitness P M D hT I Iprimary p).mean_angle t x θ]
  · exact sourceMeanPullback_divergence P M D hT I Iprimary A p t

end EulerPacketCylinderField
