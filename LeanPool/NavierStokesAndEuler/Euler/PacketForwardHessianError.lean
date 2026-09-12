/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPressureBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimary
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketForcingBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGrade
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardGradeBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity

/-! The actual finite pressure Hessian is its primary normal tensor plus
a uniform inverse-frequency error. No derivative or remainder estimate
is assumed for a solved field. -/

section

/-! Scalar pressure and angular pressure-gradient grade bounds for the actual
zero-history solve. Forced grades have zero initial data; the primary keeps
the literal compact initial-data amplitude. All bounds retain the same radius. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketForward

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSobolev
  EulerPacketShiftArithmetic EulerCylinderScalarPrimitive
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField}

/-- Scalar field, given by `scalarEmbeddingField (G.scalar I) (G.pressurePath I)
(G.pressurePath_orbit I) (G.scalar_eq_pointField I)`. -/
def scalarField (G : Forcing P D raw) (I : InitialData P D) :
    Field P D.T (fun z => scalarEmbed (G.scalar I z)) :=
  scalarEmbeddingField (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I)

/-- Angular field, constructed using `EulerPacketPressure.angularGradientField`. -/
def angularField (G : Forcing P D raw) (I : InitialData P D) :
    Field P D.T (fun z => (EulerPacketPointJets.pressureJet (G.scalar I) z).2
      EulerPacketPointJets.angleDirection • D.m₀) :=
  EulerPacketPressure.angularGradientField P (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I) D.m₀

namespace Budget

variable (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)

theorem scalar_grade_bound_pred (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d + 3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c * C) * majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c * C) * majorant L.R d n) :
    ((scalarField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (e-1) := by
  have hb : ((scalarField G I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.pressureAmplitude (P := P) N*C)*c) (d+1) := by
    apply scalarEmbeddingField_normalized_bound _ _ _ _ D.T_pos.le L.g L.positive
    intro n
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      L.pressure_bound N G I (c*C) (mul_nonneg hc.le W.data_nonneg) d hforce hinitial n
  have hnonneg := mul_nonneg (L.pressureAmplitude_nonneg (P := P) N) W.data_nonneg
  have hcost : L.pressureAmplitude (P := P) N*C ≤ L.R := by
    linarith [W.pressureGradient]
  exact (hb.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
    L.radius_one hnonneg hcost (by omega)

theorem angular_grade_bound (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d + 3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c * C) * majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c * C) * majorant L.R d n) :
    ((angularField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e := by
  have hh := angularGradientField_normalized_bound _ _ _ _ D.T_pos.le
    (c • L.g) (smul_profile_pos L.g L.positive c hc)
    D.m₀ D.m₀_unit.le (zero_le_one.trans L.radius_one) zero_le_one
    (L.scalar_grade_bound_pred N C W G I c hc d e hroom hforce hinitial)
  simpa only [angularField,Field.WordBound,Field.normalized_path,
    show e-1+1=e by omega] using hh

theorem scalar_grade_bound (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d + 3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c * C) * majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c * C) * majorant L.R d n) :
    ((scalarField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e :=
  (L.scalar_grade_bound_pred N C W G I c hc d e hroom hforce hinitial).mono_shift
    L.radius_one zero_le_one (Nat.sub_le _ _)

theorem forced_scalar_and_angular_grade_bound
    (W : GradeGuards (P := P) L N 1)
    (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
    (p : ℕ) (hp : 2 ≤ p)
    (hforce : (F.normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highForceShift p)) :
    ((scalarField G (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((angularField G (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R (c*1) (highForceShift p) :=
    (hforce.unscale_profile D.T_pos.le L.g L.positive c hc).transfer _
  have hi (n : ℕ) : block standardDirection 6
      (fun a => translate P a ((InitialData.zero P D).value : CylinderL2 P U)) n 0 ≤
        (c*1)*majorant L.R (highForceShift p) n := by
    simpa only [InitialData.zero,Submodule.coe_zero,map_zero,block_zero_function,mul_one] using
      mul_nonneg hc.le (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (highForceShift p) n)
  have hroom : highForceShift p+3 ≤ highShift p := by
    simp only [highForceShift,highShift]
    omega
  exact ⟨L.scalar_grade_bound N 1 W G (InitialData.zero P D) c hc _ _ hroom hf hi,
    L.angular_grade_bound N 1 W G (InitialData.zero P D) c hc _ _ hroom hf hi⟩

theorem primary_scalar_and_angular_grade_bound
    (C : ℝ) (W : GradeGuards (P := P) L N C) (Y : InitialData P D)
    (α : ℝ) (hα : 0 < α)
    (hYb : ∀ n, block standardDirection 6
      (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α * C) * majorant L.R 0 n) :
    ((scalarField (EulerPacketForwardPrimary.forcing D) Y).normalized D.T_pos.le (α • L.g)
      (smul_profile_pos L.g L.positive α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((angularField (EulerPacketForwardPrimary.forcing D) Y).normalized D.T_pos.le (α • L.g)
      (smul_profile_pos L.g L.positive α hα)).WordBound 6 L.R 1 (highShift 1) := by
  let G := EulerPacketForwardPrimary.forcing (P := P) D
  have hf (n : ℕ) : block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (α*C)*majorant L.R 0 n := by
    have hh : HistoryData.forcingPath G = 0 := by
      unfold HistoryData.forcingPath
      rw [EulerPacketForwardPrimary.forcing_path_zero,map_zero]
    simpa only [hh,map_zero,block_zero_function] using
      mul_nonneg (mul_nonneg hα.le W.data_nonneg)
        (majorant_nonneg L.R (zero_le_one.trans L.radius_one) 0 n)
  have hroom : 0+3 ≤ highShift 1 := by norm_num [highShift]
  exact ⟨L.scalar_grade_bound N C W G Y α hα 0 _ hroom hf hYb,
    L.angular_grade_bound N C W G Y α hα 0 _ hroom hf hYb⟩

end Budget

end EulerTransversePacketForward

end
end

end

section

/-! The angular derivative of the actual recursive high pressure retains
the unit grade budget. This is derived from the same source solve used by
the velocity recursion. -/

@[expose] public section

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
      inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)
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
  (D : Data U) (hTime : M.T = D.T)
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
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

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

end
end

end

section

/-! The actual forward finite pressure has its actual leading angular force
and a uniformly small covector remainder. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerPacketForwardPrimary
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedProfiles_one_highPressure :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).highPressure =
      scalar D (initialData D δ hδ (α • ξ) hs) := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

theorem forwardInitializedProfiles_one_meanPressure :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).meanPressure = 0 := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

/-- Forward initialized angular pressure, defined pointwise by `(pressureJet (scalar D
(initialData D δ hδ (α • ξ) hs)) z).2 angleDirection`. -/
def forwardInitializedAngularPressure : ScalarField := fun z =>
  (pressureJet (scalar D (initialData D δ hδ (α • ξ) hs)) z).2 angleDirection

/-- Forward initialized covector remainder, given by `covectorRemainder (N := N) (a :=
forwardInitializedProfiles M D δ hδ ξ hs α) D.m₀ κ`. -/
def forwardInitializedCovectorRemainder (N : ℕ) (κ : ℝ) : VectorField :=
  covectorRemainder (N := N) (a := forwardInitializedProfiles M D δ hδ ξ hs α) D.m₀ κ

include hTime in
theorem forwardInitializedPressure_gradient_decomposition (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x =
      fastForce (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z))
        k D.m₀ Y (fun y => D.FInv.field t (Y y)) x +
      (D.FInv.field t (Y x)).adjoint
        (forwardInitializedCovectorRemainder M D δ hδ ξ hs α N k⁻¹
          (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))) := by
  let tm : Icc (0 : ℝ) M.T := ⟨t.val,by simpa only [hTime] using t.property⟩
  let a := forwardInitializedProfiles M D δ hδ ξ hs α
  have hm (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).meanPressure (t,z)) :=
    source_meanPressure_smooth period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t
  have hh (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).highPressure (t,z)) :=
    source_highPressure_smooth period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t
  have ha (i : ℕ) : (pressureJet (a i).meanPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))).2 angleDirection=0 :=
    source_meanPressure_angle period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t _ _
  have hp : DifferentiableAt ℝ
      (fun z => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹ (t,z))
      (graphMap k D.m₀ (Y x)) :=
    ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).smooth tm).differentiable
      (by simp) _
  rw [gradient_physical_covector k D.m₀ _ t Y _ x hY hp]
  have he := covector_finite N k⁻¹ (inv_ne_zero hk) D.m₀ a
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))
    (fun i _ => (hm i).differentiable (by simp) _) (fun i _ => (hh i).differentiable (by simp) _)
    (fun i _ => ha i)
  rw [inv_inv] at he
  change covector k D.m₀ (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) = _ at he
  rw [he]
  have h1 : (a 1).highPressure=scalar D (initialData D δ hδ (α • ξ) hs) :=
    forwardInitializedProfiles_one_highPressure M D δ hδ ξ hs α
  have hv : fieldSum (N+1) k⁻¹ (covectorGrades N D.m₀ a) (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) =
      k⁻¹ • angularPressure D.m₀ (a 1).highPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) +
      forwardInitializedCovectorRemainder M D δ hδ ξ hs α N k⁻¹
        (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) := by
    dsimp only [forwardInitializedCovectorRemainder,covectorRemainder,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [hv,map_add,map_smul]
  simp only [fastForce,transportedNormal,graphMap_apply,angularPressure,
    forwardInitializedAngularPressure,map_smul,h1]

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

/-- Forward initialized pressure budget, constructed using `Classical.choice`. -/
def forwardInitializedPressureBudget (p : ℕ) :=
  Classical.choice (forwardInitializedPressureBudget_exists M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth p)

/-- Forward initialized angular pressure field as an element of `Field period D.T (fun z =>
forwardInitializedAngularPressure D δ hδ ξ hs α z • D.m₀)`. -/
def forwardInitializedAngularPressureField :
    Field period D.T (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α z • D.m₀) :=
  (((forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1).angular).changeTime hTime).congr
      (fun _ _ _ => by rw [forwardInitializedProfiles_one_highPressure]; rfl)

theorem forwardInitializedAngularPressure_bound :
    (forwardInitializedAngularPressureField M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  let K := forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1
  have hb := K.angular_bound.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_one) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_one) S.H0_pos.le
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [forwardInitializedProfiles_one_highPressure]; rfl)

/-- Forward initialized covector remainder field as an element of `Field period D.T
(forwardInitializedCovectorRemainder M D δ hδ ξ hs α N κ)`. -/
def forwardInitializedCovectorRemainderField (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) :
    Field period D.T (forwardInitializedCovectorRemainder M D δ hδ ξ hs α N κ) :=
  (covectorRemainderField M.T_pos D.m₀
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (forwardInitializedProfiles_zero M D δ hδ ξ hs α) hN
    (forwardInitializedProfiles_one_meanPressure M D δ hδ ξ hs α) κ).changeTime hTime

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth
theorem forwardInitializedCovectorRemainder_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (forwardInitializedCovectorRemainderField M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹).WordBound
      6 (4*L.R) ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) 0 := by
  exact (covectorRemainder_bound M.T_pos D.m₀
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (fun i _ hi => forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi)
    L.radius_one (forwardInitializedProfiles_zero M D δ hδ ξ hs α) hN
    (forwardInitializedProfiles_one_meanPressure M D δ hδ ξ hs α) BC k hk hbase).changeTime hTime

end EulerPacketTerminalDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerPacketForwardPrimary EulerPeriodicProfile
  EulerPacketInverseFlowGevrey EulerPacketPhysicalGevrey EulerGevrey
  EulerLiftedGradientSpace EulerCylinderSobolevSpace
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Forward initialized pressure hessian cost, constructed using `fastHessianCost`. -/
def forwardInitializedPressureHessianCost {D : Data U} {q : ℕ} {R₀ : ℝ}
    (NB : EulerTransversePacketJoin.NormalBudget D q R₀) (R H0 Rc C : ℝ) : ℝ :=
  fastHessianCost (P := period) NB (4*R) (fixedVelocityGradeCost R H0 1) +
    9*C*physicalFixedCost D Rc C (4*R) 1*sobolevEmbeddingConstant period 3 *
      (fixedVelocityGradeCost R H0 2+2)

variable (M : EulerMeanPacketProvider.Data) (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedAngularPressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z)) := by
  have hq := pressure_smooth D (initialData D δ hδ (α • ξ) hs) t
  simp only [forwardInitializedAngularPressure,pressureJet_angle]
  change ContDiff ℝ ∞ (angularDerivative (fun y =>
    scalar D (initialData D δ hδ (α • ξ) hs) (t,y)))
  exact angularDerivative_contDiff hq

theorem forwardInitializedAngularPressure_second (t : Icc (0 : ℝ) D.T) (z : LiftTangent) :
    angularDerivative (fun w => forwardInitializedAngularPressure D δ hδ ξ hs α (t,w)) z =
      EulerPacketForwardShear.pressureCoefficient D ξ α t z.1 * deriv (profile δ) z.2 := by
  have hq := pressure_smooth D (initialData D δ hδ (α • ξ) hs) t
  simp only [forwardInitializedAngularPressure,pressureJet_angle]
  change angularDerivative (angularDerivative (fun w =>
    scalar D (initialData D δ hδ (α • ξ) hs) (t,w))) z = _
  rw [angularSecond_eq_deriv hq]
  exact EulerPacketForwardShear.scalar_second_deriv D δ hδ ξ hs α t z.1 z.2

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem forwardInitializedPressure_hessian_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ)))) x -
      (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
      rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤
        forwardInitializedPressureHessianCost NB L.R S.H0 L.Rc L.C₀/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_one
  let AF := forwardInitializedAngularPressureField M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  let RF := forwardInitializedCovectorRemainderField M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹
  let a : LiftTangent → ℝ := fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z)
  let J : Space → Space →L[ℝ] Space := fun y => D.FInv.field t (Y t y)
  have hYd := continuousInverse_differentiable D X Y hX hXY hY
  have hYder := continuousInverse_hasFDerivAt D X Y hX hXY hY
  have hJ : DifferentiableAt ℝ J x :=
    ((D.FInv.smooth t).differentiable (by simp) (Y t x)).comp x (hYd t x)
  have ha : ContDiff ℝ ∞ a := forwardInitializedAngularPressure_smooth D δ hδ ξ hs α t
  have hf := fastForce_hasFDerivAt a k hk0.ne' D.m₀ (Y t) J x (hYder t x) hJ
    (ha.differentiable (by simp) _)
  have hsecond : angularDerivative a (graphMap k D.m₀ (Y t x)) =
      EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ) :=
    forwardInitializedAngularPressure_second D δ hδ ξ hs α t _
  have hn : transportedNormal D.m₀ J x = D.normal.field t (Y t x) := rfl
  rw [hsecond,hn] at hf
  have hRF := forwardInitializedCovectorRemainder_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hAF := forwardInitializedAngularPressure_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  have hfast := fastHessianRemainder_bound NB
    (forwardInitializedAngularPressure D δ hδ ξ hs α) AF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 1) (by positivity)
    (fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1) hAF k hk0 t (Y t) x (hYder t x)
    (ha.differentiable (by simp) _)
  have htail := physicalCovector_error_bound D RF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 2+2) (by positivity)
    (by have h := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 2; linarith)
    k (by linarith) hRF L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg hdet L.frame_bound
    X Y hX hYd hXY t x
  have htaild : DifferentiableAt ℝ (physicalCovector D RF k Y t) x := by
    have hI := (adjoint.differentiableAt.comp x hJ)
    have hR := (RF.raw_graph_contDiff t k D.m₀).differentiable (by simp) (Y t x)
    have hRg := hR.comp x (hYd t x)
    exact hI.clm_apply hRg
  have he : gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
      (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) =
      fastForce a k D.m₀ (Y t) J + physicalCovector D RF k Y t := by
    funext y
    exact forwardInitializedPressure_gradient_decomposition M D hTime δ hδ ξ hs α
      N k hk0.ne' t (Y t) y (hYder t y)
  calc
    _ = ‖fastHessianRemainder a k D.m₀ (Y t) J x +
        fderiv ℝ (physicalCovector D RF k Y t) x‖ := by
      rw [he,fderiv_add hf.differentiableAt htaild,hf.fderiv]
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hfast htail).trans_eq (by
      unfold forwardInitializedPressureHessianCost
      ring))

end EulerPacketTerminalDatum
