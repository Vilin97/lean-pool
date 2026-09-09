/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketAngularPressureStepBound
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceConstraints
import LeanPool.NavierStokesAndEuler.Euler.PacketMeanPressureStepBound
import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGrade

/-! The actual initialized recursion has both mean and angular pressure
budgets at every grade. All bounds are derived from the source solvers. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic

/-- Pressure budget data, collecting `mean`, `angular`, `mean_bound`, `angular_bound`. -/
structure PressureBudget (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T) (m : Space)
    (a : Profile) (S : Scales (Icc (0 : ℝ) T)) (R : ℝ) (p : ℕ) where
  /-- Mean field of `PressureBudget`, of type `Field P T (pressureGradient a.meanPressure)`. -/
  mean : Field P T (pressureGradient a.meanPressure)
  /-- Angular of `PressureBudget`, of type `Field P T (fun z => (pressureJet a.highPressure z).2
  angleDirection • m)`. -/
  angular : Field P T (fun z => (pressureJet a.highPressure z).2 angleDirection • m)
  mean_bound : (mean.normalized hT (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p)
  angular_bound : (angular.normalized hT (S.high p) (S.high_pos p)).WordBound 6 R 1 (highShift p)

end EulerPacketCylinderField

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketPointJets EulerPacketShiftArithmetic
  EulerTransversePacketPrimary

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPressureBudget_exists (p : ℕ) :
    Nonempty (PressureBudget period M.T M.T_pos.le D.m₀
      (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α p) S L.R p) := by
  let a := initializedProfiles M D τ hτ hτT B δ hδ ξ hs α
  let primary := joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
  have ha0 : a 0=0 := profiles_zero _ _
  have hb0 : pressureGradient (a 0).meanPressure=0 := by
    rw [ha0]
    funext z
    simp [pressureGradient,pressureJet_zero]
  have hb1 : pressureGradient (a 1).meanPressure=0 := by
    have he : (a 1).meanPressure=0 := by
      simp only [a,initializedProfiles,joinedSourceProfiles,profiles_one]
      rfl
    rw [he]
    funext z
    simp [pressureGradient,pressureJet_zero]
  by_cases hp0 : p=0
  · subst p
    have han : (fun z => (pressureJet (a 0).highPressure z).2 angleDirection • D.m₀)=0 := by
      rw [ha0]
      funext z
      simp [pressureJet_zero]
    let Q := (Field.zero period M.T).congr (fun _ _ _ => congrFun hb0 _)
    let A : Field period M.T (fun z => (pressureJet (a 0).highPressure z).2 angleDirection • D.m₀)
        :=
      (Field.zero period M.T).congr (fun _ _ _ => congrFun han _)
    refine ⟨⟨Q,A,?_,?_⟩⟩
    · exact (Field.wordBound_normalized_of_zero Q (fun _ _ _ => congrFun hb0 _)
        M.T_pos.le (S.mean 0) (S.mean_pos 0) 6 L.R (meanShift 0)).mono_amplitude
          (zero_le_one.trans L.radius_bounds.1) zero_le_one
    · exact (Field.wordBound_normalized_of_zero A (fun _ _ _ => congrFun han _)
        M.T_pos.le (S.high 0) (S.high_pos 0) 6 L.R (highShift 0)).mono_amplitude
          (zero_le_one.trans L.radius_bounds.1) zero_le_one
  by_cases hp1 : p=1
  · subst p
    let Q := (Field.zero period M.T).congr (fun _ _ _ => congrFun hb1 _)
    have hs1 : S.high 1=S.growth := ContinuousMap.ext (fun t => S.high_one t)
    have ht : timeProfileChange (α • L.fullProfile) hTime.symm=S.high 1 := by
      rw [← hgrowth,timeProfileChange_roundtrip,hs1]
    have hb := H.angular_grade_bound NB _ WP (initialData D δ hδ (α • ξ) hs) α hα
      (scaled_initialData_bound (L := L) δ hδ hδ1 ξ hs α hα hR)
    have hb' := hb.normalized_changeTime D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) hTime.symm M.T_pos.le
      (S.high 1) (S.high_pos 1) ht
    have he : (a 1).highPressure=scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs) := by
      simp only [a,initializedProfiles,joinedSourceProfiles,profiles_one]
      rfl
    let A : Field period M.T (fun z => (pressureJet (a 1).highPressure z).2 angleDirection • D.m₀)
        :=
      ((angularField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).changeTime hTime.symm).congr
        (fun _ _ _ => by rw [he])
    refine ⟨⟨Q,A,?_,hb'.of_path_eq _ rfl⟩⟩
    exact (Field.wordBound_normalized_of_zero Q (fun _ _ _ => congrFun hb1 _)
      M.T_pos.le (S.mean 1) (S.mean_pos 1) 6 L.R (meanShift 1)).mono_amplitude
        (zero_le_one.trans L.radius_bounds.1) zero_le_one
  have hp : 2 ≤ p := by omega
  let O := joinedSourceOperators period M D τ hτ hτT B
  let C := joinedSourceCoefficientData period M D τ hτ hτT B hTime
  let G : ∀ i, i < p → ProfileRegularity period M.T M.T_pos.le D.support (a i) :=
    fun i _ => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have he : a p=step O p a := profiles_step O primary p hp
  have hc₀ : (a 0).corrector=0 := by rw [ha0]; rfl
  have hB₁ : (a 1).mean=0 := by
    simp only [a,initializedProfiles,joinedSourceProfiles,profiles_one]
    rfl
  have hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ)))=0 := by
    intro i _ t x θ
    by_cases hi : i=0
    · subst i
      rw [ha0]
      exact inner_zero_right _
    · exact joinedSource_high_tangent_all period M D hTime τ hτ hτT B primary
        (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
        (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
        i (by omega) t x θ
  obtain ⟨Q,hQ⟩ := ProfileBudget.meanPressure_step_exists M LM WM C BC rfl hRc hcost
    S hp G hG hc₀ hB₁ hA
  obtain ⟨A,hAb⟩ := ProfileBudget.angularPressure_step_exists M D hTime τ hτ hτT B L NB W LM WM
    C BC rfl rfl hRc hcost S hp G hG hc₀ hB₁ hA
    (α*meanScale S.H0 p) (S.gradeFactor_pos α hα p)
    (S.high_timeProfile_eq hTime L.fullProfile α hgrowth p)
  let Q' : Field period M.T (pressureGradient (a p).meanPressure) :=
    Q.congr (fun _ _ _ => by rw [he])
  let A' : Field period M.T (fun z => (pressureJet (a p).highPressure z).2 angleDirection • D.m₀) :=
    A.congr (fun _ _ _ => by rw [he])
  exact ⟨⟨Q',A',hQ.of_path_eq _ rfl,hAb.of_path_eq _ rfl⟩⟩

end EulerPacketTerminalDatum
