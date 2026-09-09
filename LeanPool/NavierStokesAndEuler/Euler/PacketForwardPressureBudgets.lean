/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardScalarPressureGrade
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardStepBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPressureBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles

@[expose] public section

/-! The angular derivative of the actual recursive high pressure retains
the unit grade budget. This is derived from the same source solve used by
the velocity recursion. -/

noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem forwardAngularPressure_step_exists
    {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
    (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
    (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
    (W : EulerTransversePacketForward.Budget.GradeGuards (P := P) L N 1)
    (LM : EulerMeanPacketProvider.Budget M 6 L.R)
    (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
    {O : Operators} (C : CoefficientData P M.T O) (BC : CoefficientBudget C)
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
    (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D
      (EulerTransversePacketProvider.InitialData.zero P D))
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
    (S : Scales (Icc (0 : ℝ) M.T))
    {p : ℕ} {a : ℕ → Profile} (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i))
    (hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i)
    (hc₀ : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ))) = 0)
    (c : ℝ) (hc : 0 < c)
    (hprofile : timeProfileChange (S.high p) hTime = c • L.g) :
    ∃ Q : Field P M.T (fun z => (pressureJet (step O p a).highPressure z).2 angleDirection • D.m₀),
      (Q.normalized M.T_pos.le (S.high p) (S.high_pos p)).WordBound 6 L.R 1 (highShift p) := by
  let F := ProfileRegularity.prefixFields G
  let V := G (p-1) (by omega)
  have hV := hG (p-1) (by omega) (by omega)
  have BF : PrefixBound F M.T_pos.le S L.R := {
    high := fun i hi hi1 => (hG i hi hi1).high
    mean := fun i hi hi2 => (hG i hi (by omega)).mean
    corrector := fun i hi hi1 => (hG i hi hi1).corrector
  }
  have hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)) := fun i hi => (G i hi).mean_angle
  let MF := F.meanForce C (by omega) M.T_pos V.correctorDerivative V.corrector_time V.pressure
  have hMF : (MF.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 L.R 1 (meanForceShift p) :=
    BF.meanForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure L.radius_one hRc hcost hc₀ hB₁ hA hB
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (meanForce O p a)) :=
    ⟨F.meanForcing M C (by omega) V.correctorDerivative V.corrector_time V.pressure⟩
  let GM := Classical.choice hm
  have hMeanSolve : O.meanSolve (meanForce O p a) = (GM.vector,GM.scalar) := by
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
  let newMean : Field P M.T (meanResult O p a).1 := (GM.vectorCylinderField P).congr
    (fun t x θ => by change (O.meanSolve (meanForce O p a)).1 _ = _; rw [hMeanSolve])
  have hNew : (newMean.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 L.R 1 (meanShift p) := (LM.grade_bounds WM S GM MF p hp hMF).1.of_path_eq _ rfl
  let HF := F.highForce C hp M.T_pos V.correctorDerivative V.corrector_time V.pressure newMean
  have hHF : (HF.normalized M.T_pos.le (S.high p) (S.high_pos p)).WordBound
      6 L.R 1 (highForceShift p) :=
    BF.highForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure L.radius_one hRc hcost hc₀ hB₁ hA hB newMean hNew
  let hh : Nonempty (EulerTransversePacketProvider.Forcing P D (highForce O p a)) :=
    ⟨F.highForcing M D hTime C hp V.correctorDerivative V.corrector_time V.pressure hmean
      (ProfileRegularity.prefixLocality G) V.pressure_zero⟩
  let GH := Classical.choice hh
  let hg := smul_profile_pos L.g L.positive c hc
  have hHFD : ((HF.changeTime hTime).normalized D.T_pos.le (c • L.g) hg).WordBound
      6 L.R 1 (highForceShift p) :=
    hHF.normalized_changeTime M.T_pos.le (S.high p) (S.high_pos p) hTime D.T_pos.le
      (c • L.g) hg hprofile
  have hj := (L.forced_scalar_and_angular_grade_bound N W GH (HF.changeTime hTime) c hc p hp hHFD).2
  have hback : timeProfileChange (c • L.g) hTime.symm = S.high p := by
    rw [← hprofile,timeProfileChange_roundtrip]
  have hbound := hj.normalized_changeTime D.T_pos.le (c • L.g) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hHighSolve : O.highSolve (highForce O p a) =
      (GH.vector (EulerTransversePacketProvider.InitialData.zero P D),GH.scalar
        (EulerTransversePacketProvider.InitialData.zero P D)) := by
    rw [hhigh]
    exact EulerTransversePacketProvider.highSolve_of_admissible D
      (EulerTransversePacketProvider.InitialData.zero P D) _ hh
  have hscalar : (step O p a).highPressure = GH.scalar
    (EulerTransversePacketProvider.InitialData.zero P D) :=
    congrArg Prod.snd hHighSolve
  let Q : Field P M.T (fun z => (pressureJet (step O p a).highPressure z).2 angleDirection • D.m₀)
    :=
    ((EulerTransversePacketForward.angularField GH (EulerTransversePacketProvider.InitialData.zero
      P D)).changeTime hTime.symm).congr
      (fun _ _ _ => by rw [hscalar])
  exact ⟨Q,hbound.of_path_eq _ rfl⟩

end EulerPacketCylinderField.ProfileBudget

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketPointJets EulerPacketShiftArithmetic
  EulerPacketForwardPrimary EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderSobolev EulerGevrey

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.g)

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem forwardInitializedPressureBudget_exists (p : ℕ) :
    Nonempty (PressureBudget period M.T M.T_pos.le D.m₀
      (forwardInitializedProfiles M D δ hδ ξ hs α p) S L.R p) := by
  let a := forwardInitializedProfiles M D δ hδ ξ hs α
  let primary := homogeneousPrimary D (initialData D δ hδ (α • ξ) hs)
    (sourceOperators period M D (InitialData.zero period D))
  have ha0 : a 0=0 := profiles_zero _ _
  have hb0 : pressureGradient (a 0).meanPressure=0 := by
    rw [ha0]
    funext z
    simp [pressureGradient,pressureJet_zero]
  have hb1 : pressureGradient (a 1).meanPressure=0 := by
    have he : (a 1).meanPressure=0 := by
      simp only [a,forwardInitializedProfiles,sourceProfiles,profiles_one]
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
          (zero_le_one.trans L.radius_one) zero_le_one
    · exact (Field.wordBound_normalized_of_zero A (fun _ _ _ => congrFun han _)
        M.T_pos.le (S.high 0) (S.high_pos 0) 6 L.R (highShift 0)).mono_amplitude
          (zero_le_one.trans L.radius_one) zero_le_one
  by_cases hp1 : p=1
  · subst p
    let Q := (Field.zero period M.T).congr (fun _ _ _ => congrFun hb1 _)
    have hs1 : S.high 1=S.growth := ContinuousMap.ext (fun t => S.high_one t)
    have ht : timeProfileChange (α • L.g) hTime.symm=S.high 1 := by
      rw [← hgrowth,timeProfileChange_roundtrip,hs1]
    have hYb : ∀ n, block standardDirection 6
        (fun a => translate period a ((initialData D δ hδ (α • ξ) hs).value : CylinderL2 period U))
          n 0 ≤
          (α*(wordCost (Fin 4) 6 δ*‖ξ‖))*majorant L.R 0 n := by
      intro n
      have hh := initialData_common_radius D δ hδ (α • ξ) hs standardDirection
        (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) 6 hδ1 L.R hR n
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hα,mul_assoc,mul_left_comm,mul_comm] using
        hh
    have hb := (L.primary_scalar_and_angular_grade_bound NB _ WP
      (initialData D δ hδ (α • ξ) hs) α hα hYb).2
    have hb' := hb.normalized_changeTime D.T_pos.le (α • L.g)
      (smul_profile_pos L.g L.positive α hα) hTime.symm M.T_pos.le
      (S.high 1) (S.high_pos 1) ht
    have he : (a 1).highPressure=scalar D (initialData D δ hδ (α • ξ) hs) := by
      simp only [a,forwardInitializedProfiles,sourceProfiles,profiles_one]
      rfl
    let A : Field period M.T (fun z => (pressureJet (a 1).highPressure z).2 angleDirection • D.m₀)
      :=
      ((EulerTransversePacketForward.angularField (forcing D) (initialData D δ hδ (α • ξ)
        hs)).changeTime hTime.symm).congr
        (fun _ _ _ => by rw [he])
    refine ⟨⟨Q,A,?_,hb'.of_path_eq _ rfl⟩⟩
    exact (Field.wordBound_normalized_of_zero Q (fun _ _ _ => congrFun hb1 _)
      M.T_pos.le (S.mean 1) (S.mean_pos 1) 6 L.R (meanShift 1)).mono_amplitude
        (zero_le_one.trans L.radius_one) zero_le_one
  have hp : 2 ≤ p := by omega
  let O := sourceOperators period M D (InitialData.zero period D)
  let C := sourceCoefficientData period M D (InitialData.zero period D) hTime
  let G : ∀ i, i < p → ProfileRegularity period M.T M.T_pos.le D.support (a i) :=
    fun i _ => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i
  have hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have he : a p=step O p a := profiles_step O primary p hp
  have hc₀ : (a 0).corrector=0 := by rw [ha0]; rfl
  have hB₁ : (a 1).mean=0 := by
    simp only [a,forwardInitializedProfiles,sourceProfiles,profiles_one]
    rfl
  have hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ)))=0 :=
    fun i _ t x θ => source_high_tangent period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t x θ
  obtain ⟨Q,hQ⟩ := ProfileBudget.meanPressure_step_exists M LM WM C BC rfl hRc hcost
    S hp G hG hc₀ hB₁ hA
  obtain ⟨A,hAb⟩ := ProfileBudget.forwardAngularPressure_step_exists M D hTime L NB W LM WM
    C BC rfl rfl hRc hcost S hp G hG hc₀ hB₁ hA
    (α*meanScale S.H0 p) (S.gradeFactor_pos α hα p)
    (S.high_timeProfile_eq hTime L.g α hgrowth p)
  let Q' : Field period M.T (pressureGradient (a p).meanPressure) :=
    Q.congr (fun _ _ _ => by rw [he])
  let A' : Field period M.T (fun z => (pressureJet (a p).highPressure z).2 angleDirection • D.m₀) :=
    A.congr (fun _ _ _ => by rw [he])
  exact ⟨⟨Q',A',hQ.of_path_eq _ rfl,hAb.of_path_eq _ rfl⟩⟩

end EulerPacketTerminalDatum
