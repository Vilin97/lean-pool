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
