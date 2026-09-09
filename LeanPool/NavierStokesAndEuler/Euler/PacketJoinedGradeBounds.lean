/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedFullBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderProfileChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer

@[expose] public section

/-! A single source budget closes every forced transverse grade.  The actual
profile is retained, its positive scalar factor cancels exactly, and one
spare derivative shift pays the fixed operator constants. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerPacketProfileRecursion

theorem smul_profile_pos {K : Type*} [TopologicalSpace K]
    (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) (c : ℝ) (hc : 0 < c) (t : K) :
    0 < (c • g) t := mul_pos hc (hg t)

namespace Field

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (c : ℝ) (hc : 0 < c) {q d : ℕ} {R A : ℝ}

theorem WordBound.unscale_profile
    (hG : (G.normalized hT (c • g) (smul_profile_pos g hg c hc)).WordBound q R A d) :
    (G.normalized hT g hg).WordBound q R (c*A) d :=
  hG.changeProfile hT g hg c hc.le (fun _ => le_rfl)

theorem WordBound.scale_profile
    (hG : (G.normalized hT g hg).WordBound q R (A*c) d) :
    (G.normalized hT (c • g) (smul_profile_pos g hg c hc)).WordBound q R A d := by
  have hh := hG.changeProfile hT (c • g) (smul_profile_pos g hg c hc) c⁻¹
    (inv_nonneg.mpr hc.le) (fun t => by
      change g t ≤ c⁻¹*(c*g t)
      rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul])
  have he : c⁻¹*(A*c) = A := by field_simp
  simpa only [he] using hh

end Field
end EulerPacketCylinderField

namespace EulerTransversePacketJoin.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey EulerSourceNormalResidualBounds
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  (L : Budget D τ hτ hτT B (Fin 4) 6) (N : NormalBudget D 6 L.R)

theorem pressureAmplitude_nonneg : 0 ≤ L.pressureAmplitude (P := P) N := by
  have hRi := N.Ri_nonneg
  have hC := N.C_nonneg
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) N.C
    (by positivity) hC
  unfold pressureAmplitude pressureCost
  positivity

theorem correctorAmplitude_nonneg : 0 ≤ L.correctorAmplitude (P := P) N := by
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity

theorem correctorTimeAmplitude_nonneg : 0 ≤ L.correctorTimeAmplitude (P := P) N := by
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity

/-- These four numerical guards depend only on the source data and the fixed
external radius.  They are chosen before the forcing, its amplitude or grade. -/
structure GradeGuards : Prop where
  common : L.commonCost ≤ L.R
  corrector : L.correctorAmplitude (P := P) N ≤ L.R
  correctorTime : L.correctorTimeAmplitude (P := P) N ≤ L.R
  pressureGradient : 3*L.pressureAmplitude (P := P) N ≤ L.R

private theorem grade_shift_room (p : ℕ) (hp : 2 ≤ p) :
    highForceShift p+3+1 ≤ highShift p ∧ highForceShift p+4+1 ≤ highShift p := by
  simp only [highForceShift,highShift]
  omega

variable (W : GradeGuards (P := P) L N) {raw : VectorField}
  (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
  (p : ℕ) (hp : 2 ≤ p)
  (hforce : (F.normalized D.T_pos.le (c • L.fullProfile)
    (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highForceShift p))

include N W hp hforce

/-- Actual A, A_t, curl corrector, its time derivative, and the literal scalar
pressure gradient satisfy the unit grade budget with the same time profile. -/
theorem grade_bounds :
    ((vectorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((correctorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
      6 L.R c (highForceShift p) := by
    have hh := hforce.unscale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc
    have hh' : (F.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
        6 L.R c (highForceShift p) := by simpa only [mul_one] using hh
    exact hh'.transfer _
  have hv : ((vectorField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.commonCost*c) (highForceShift p+3) :=
    L.velocity_common_bound G c hc.le (highForceShift p) hf
  have ht : ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.commonCost*c) (highForceShift p+3) :=
    L.derivative_common_bound G c hc.le (highForceShift p) hf
  have hC : ((correctorField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.correctorAmplitude (P := P) N*c) (highForceShift p+4) :=
    L.corrector_bound N G c hc.le (highForceShift p) hf
  have hCt : ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.correctorTimeAmplitude (P := P) N*c) (highForceShift
        p+4) :=
    L.corrector_time_bound N G c hc.le (highForceShift p) hf
  have hπ : ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((3*L.pressureAmplitude (P := P) N)*c) (highForceShift
        p+4) :=
    L.pressure_gradient_bound N G c hc.le (highForceShift p) hf
  have hroom := grade_shift_room p hp
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 L.commonCost_nonneg W.common hroom.1
  · exact (ht.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 L.commonCost_nonneg W.common hroom.1
  · exact (hC.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (L.correctorAmplitude_nonneg N) W.corrector hroom.2
  · exact (hCt.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (L.correctorTimeAmplitude_nonneg N) W.correctorTime hroom.2
  · exact (hπ.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (by norm_num) (L.pressureAmplitude_nonneg N))
        W.pressureGradient hroom.2

theorem vector_grade_bound :
    ((vectorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).1

theorem derivative_grade_bound :
    ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.1

theorem corrector_grade_bound :
    ((correctorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.1

theorem corrector_derivative_grade_bound :
    ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.2.1

theorem pressure_gradient_grade_bound :
    ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.2.2

end EulerTransversePacketJoin.Budget
