/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGradient
import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMapBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanStep
import LeanPool.NavierStokesAndEuler.Euler.PacketForcingBounds

/-! Related estimates used together by the same construction modules. -/

section

/-! Retain the actual scalar angular pressure in the quantitative grade
bounds. Its norm-one embedding supplies genuine vector-valued Sobolev
evaluation, without changing the radius or the time profile. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerCylinderScalarPrimitive
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (raw : ScalarField)
  (p : C(Icc (0 : ℝ) T, CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (he : ∀ (t : Icc (0 : ℝ) T) x θ,
    raw (t, (x, θ)) = scalarPointField P p hp t (x, (θ : AddCircle P)))

theorem scalarEmbeddingField_normalized_bound (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun a => pathTranslate P a (normalize g hg p)) n 0 ≤ A * majorant R d n) :
    ((scalarEmbeddingField raw p hp he).normalized hT g hg).WordBound q R A d := by
  have hc : normalize g hg (pathMap P scalarEmbed p) =
      pathMap P scalarEmbed (normalize g hg p) := by
    apply ContinuousMap.ext
    intro t
    exact ((map P scalarEmbed).map_smul _ _).symm
  intro n
  change block standardDirection q
    (fun a => pathTranslate P a (normalize g hg (pathMap P scalarEmbed p))) n 0 ≤ _
  rw [hc]
  have hh := pathMap_block_bound P standardDirection q scalarEmbed (normalize g hg p)
    (scalarWeightedOrbit p hp (reciprocal g hg)) n 0
  simpa only [scalarEmbed_norm,one_mul] using hh.trans
    (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg scalarEmbed))

theorem angularGradientField_normalized_bound (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (m : Space) (hm : ‖m‖ ≤ 1) {q d : ℕ} {R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ((scalarEmbeddingField raw p hp he).normalized hT g hg).WordBound q R A d) :
    ((EulerPacketPressure.angularGradientField P raw p hp he m).normalized hT g hg).WordBound
      q R A (d+1) := by
  let L := (toSpanSingleton ℝ m).comp scalarProject
  have hL : ‖L‖ ≤ 1 := by
    exact (opNorm_comp_le _ _).trans (by
        simpa only [norm_toSpanSingleton,scalarProject_norm,mul_one])
  have hh := (hb.normalized_derivative hT 0).map L
  have hh' := hh.mono_amplitude hR (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hA)
  apply hh'.of_path_eq
  apply ContinuousMap.ext
  intro t
  exact ((map P L).map_smul _ _).symm

end EulerPacketCylinderField

namespace EulerTransversePacketJoin

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransversePacketProvider
  EulerPacketCylinderField EulerCylinderScalarPrimitive EulerLpCylinderTranslation
  EulerPacketProfileRecursion EulerParameterWordGevrey EulerGevrey
  EulerPacketShiftArithmetic
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {raw : VectorField}

/-- Scalar field, constructed using `scalarEmbeddingField`. -/
def scalarField (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (G : Forcing P D raw) :
    Field P D.T (fun z => scalarEmbed (scalar τ hτ hτT B G z)) :=
  scalarEmbeddingField (scalar τ hτ hτT B G) (pressurePath τ hτ hτT B G)
    (pressurePath_orbit τ hτ hτT B G) (scalar_eq_pointField τ hτ hτT B G)

theorem Budget.scalar_grade_bound_pred (L : Budget D τ hτ hτT B (Fin 4) 6)
    (N : NormalBudget D 6 L.R) (W : Budget.GradeGuards (P := P) L N)
    (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
    (p : ℕ) (hp : 2 ≤ p)
    (hforce : (F.normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highForceShift p)) :
    ((scalarField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highShift p-1) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
      6 L.R c (highForceShift p) := by
    have hh := hforce.unscale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc
    have hh' : (F.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
        6 L.R c (highForceShift p) := by simpa only [mul_one] using hh
    exact hh'.transfer _
  have hb : ((scalarField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.pressureAmplitude (P := P) N*c) (highForceShift p+3) :=
    scalarEmbeddingField_normalized_bound _ _ _ _ D.T_pos.le L.fullProfile L.fullProfile_pos
      6 L.R _ _ (L.pressure_bound N G c hc.le (highForceShift p) hf)
  have hcost : L.pressureAmplitude (P := P) N ≤ L.R := by
    have hn := L.pressureAmplitude_nonneg (P := P) N
    linarith [W.pressureGradient]
  exact (hb.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
    L.radius_bounds.1 (L.pressureAmplitude_nonneg N) hcost (by
      simp only [highForceShift,highShift]
      omega)

/-- Angular field, constructed using `EulerPacketPressure.angularGradientField`. -/
def angularField (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (G : Forcing P D raw) :
    Field P D.T (fun z => (EulerPacketPointJets.pressureJet (scalar τ hτ hτT B G) z).2
      EulerPacketPointJets.angleDirection • D.m₀) :=
  EulerPacketPressure.angularGradientField P (scalar τ hτ hτT B G) (pressurePath τ hτ hτT B G)
    (pressurePath_orbit τ hτ hτT B G) (scalar_eq_pointField τ hτ hτT B G) D.m₀

theorem Budget.angular_grade_bound (L : Budget D τ hτ hτT B (Fin 4) 6)
    (N : NormalBudget D 6 L.R) (W : Budget.GradeGuards (P := P) L N)
    (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
    (p : ℕ) (hp : 2 ≤ p)
    (hforce : (F.normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highForceShift p)) :
    ((angularField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highShift p) := by
  have hh := angularGradientField_normalized_bound _ _ _ _ D.T_pos.le
    (c • L.fullProfile) (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)
    D.m₀ D.m₀_unit.le (zero_le_one.trans L.radius_bounds.1) zero_le_one
    (L.scalar_grade_bound_pred N W G F c hc p hp hforce)
  simpa only [angularField,Field.WordBound,Field.normalized_path,
    show highShift p-1+1=highShift p by unfold highShift; omega] using hh

theorem Budget.scalar_grade_bound (L : Budget D τ hτ hτT B (Fin 4) 6)
    (N : NormalBudget D 6 L.R) (W : Budget.GradeGuards (P := P) L N)
    (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
    (p : ℕ) (hp : 2 ≤ p)
    (hforce : (F.normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highForceShift p)) :
    ((scalarField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound
      6 L.R 1 (highShift p) :=
  (L.scalar_grade_bound_pred N W G F c hc p hp hforce).mono_shift
    L.radius_bounds.1 zero_le_one (Nat.sub_le _ _)

end EulerTransversePacketJoin

namespace EulerTransversePacketPrimary

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransversePacketProvider
  EulerPacketCylinderField EulerCylinderScalarPrimitive EulerLpCylinderTranslation
  EulerPacketProfileRecursion EulerParameterWordGevrey EulerGevrey
  EulerPacketShiftArithmetic EulerCylinderSobolev
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}

/-- Scalar field, constructed using `scalarEmbeddingField`. -/
def scalarField (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D) :
    Field P D.T (fun z => scalarEmbed (scalar τ hτ hτT B Y z)) :=
  scalarEmbeddingField (scalar τ hτ hτT B Y) (pressurePath τ hτ hτT B Y)
    (pressurePath_orbit τ hτ hτT B Y) (scalar_eq_pointField τ hτ hτT B Y)

theorem Budget.scalar_grade_bound_pred
    {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
    (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)
    (W : Budget.GradeGuards (P := P) H N C)
    (Y : InitialData P D) (α : ℝ) (hα : 0 < α)
    (hYb : ∀ n, block standardDirection 6
      (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α * C) * majorant L.R 0 n) :
    ((scalarField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1-1) :=
          by
  have hb : ((scalarField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.pressureAmplitude (P := P) N*C)*α) 3 := by
    apply scalarEmbeddingField_normalized_bound _ _ _ _ D.T_pos.le L.fullProfile L.fullProfile_pos
    intro n
    simpa only [Nat.zero_add,mul_assoc,mul_left_comm,mul_comm] using
      H.pressure_bound N Y (α*C) (mul_nonneg hα.le W.terminal_nonneg) 0 hYb n
  have hnonneg := mul_nonneg (H.pressureAmplitude_nonneg (P := P) N) W.terminal_nonneg
  have hcost : H.pressureAmplitude (P := P) N*C ≤ L.R := by
    linarith [W.pressureGradient]
  exact (hb.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
    L.radius_bounds.1 hnonneg hcost (by norm_num [highShift])

/-- Angular field, constructed using `EulerPacketPressure.angularGradientField`. -/
def angularField (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D) :
    Field P D.T (fun z => (EulerPacketPointJets.pressureJet (scalar τ hτ hτT B Y) z).2
      EulerPacketPointJets.angleDirection • D.m₀) :=
  EulerPacketPressure.angularGradientField P (scalar τ hτ hτT B Y) (pressurePath τ hτ hτT B Y)
    (pressurePath_orbit τ hτ hτT B Y) (scalar_eq_pointField τ hτ hτT B Y) D.m₀

theorem Budget.angular_grade_bound
    {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
    (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)
    (W : Budget.GradeGuards (P := P) H N C)
    (Y : InitialData P D) (α : ℝ) (hα : 0 < α)
    (hYb : ∀ n, block standardDirection 6
      (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α * C) * majorant L.R 0 n) :
    ((angularField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) := by
  have hh := angularGradientField_normalized_bound _ _ _ _ D.T_pos.le
    (α • L.fullProfile) (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)
    D.m₀ D.m₀_unit.le (zero_le_one.trans L.radius_bounds.1) zero_le_one
    (H.scalar_grade_bound_pred N C W Y α hα hYb)
  exact hh

theorem Budget.scalar_grade_bound
    {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
    (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)
    (W : Budget.GradeGuards (P := P) H N C)
    (Y : InitialData P D) (α : ℝ) (hα : 0 < α)
    (hYb : ∀ n, block standardDirection 6
      (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α * C) * majorant L.R 0 n) :
    ((scalarField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) :=
  (H.scalar_grade_bound_pred N C W Y α hα hYb).mono_shift
    L.radius_bounds.1 zero_le_one (Nat.sub_le _ _)

end EulerTransversePacketPrimary

end
end

end

section

/-! The actual recursive mean pressure retains the same grade estimate
as the mean velocity. This estimate was already proved by the source
solver but is not a field of the velocity-oriented ProfileBudget. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {R : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  {O : Operators} (C : CoefficientData P M.T O) (BC : CoefficientBudget C)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) (hcost : BC.termCost ≤ R)
  (S : Scales (Icc (0 : ℝ) M.T)) {support : Set Space}
  {p : ℕ} {a : ℕ → Profile} (hp : 2 ≤ p)
  (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le support (a i))
  (hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hc₀ : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
  (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
    inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)

include WM BC hmean hRc hcost hp hG hc₀ hB₁ hA in
theorem meanPressure_step_exists :
    ∃ Q : Field P M.T (pressureGradient (step O p a).meanPressure),
      (Q.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p) := by
  let F := ProfileRegularity.prefixFields G
  let V := G (p-1) (by omega)
  have hV := hG (p-1) (by omega) (by omega)
  have BF : PrefixBound F M.T_pos.le S R := {
    high := fun i hi hi1 => (hG i hi hi1).high
    mean := fun i hi hi2 => (hG i hi (by omega)).mean
    corrector := fun i hi hi1 => (hG i hi hi1).corrector
  }
  have hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      (a i).mean (t,(x,θ))=(a i).mean (t,(x,0)) := fun i hi => (G i hi).mean_angle
  let MF := F.meanForce C (by omega) M.T_pos V.correctorDerivative V.corrector_time V.pressure
  have hMF : (MF.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanForceShift p) :=
    BF.meanForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure LM.radius_bounds.1 hRc hcost hc₀ hB₁ hA hB
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (meanForce O p a)) :=
    ⟨F.meanForcing M C (by omega) V.correctorDerivative V.corrector_time V.pressure⟩
  let GM := Classical.choice hm
  have hsolve : O.meanSolve (meanForce O p a)=(GM.vector,GM.scalar) := by
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
  have hscalar : (step O p a).meanPressure=GM.scalar := congrArg Prod.snd hsolve
  let Q : Field P M.T (pressureGradient (step O p a).meanPressure) :=
    (GM.pressureGradientCylinderField P).congr
      (fun t x θ => congrFun (congrArg pressureGradient hscalar) (t,(x,θ)))
  refine ⟨Q,?_⟩
  exact (LM.grade_bounds WM S GM MF p hp hMF).2.2.of_path_eq _ rfl

include WM BC hmean hRc hcost hp hG hc₀ hB₁ hA in
theorem meanPressure_step_bound (Q : Field P M.T (pressureGradient (step O p a).meanPressure)) :
    (Q.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p) := by
  obtain ⟨Q₀,hQ₀⟩ := meanPressure_step_exists M LM WM C BC hmean hRc hcost S hp G hG hc₀ hB₁ hA
  exact hQ₀.normalized_of_raw_eq Q M.T_pos.le (S.mean p) (S.mean_pos p) (fun _ _ _ => rfl)

end EulerPacketCylinderField.ProfileBudget

end
end

end
