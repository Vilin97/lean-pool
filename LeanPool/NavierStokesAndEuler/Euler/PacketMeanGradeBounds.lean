/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketShiftArithmetic
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption

/-! The actual mean solver closes a grade at its constant source profile.
Only fixed source costs are absorbed into the radius; the grade amplitude
cancels without any loss. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)
  (hT : 0 ≤ T) (c : ℝ) (hc : 0 < c)

theorem normalized_const_path :
    (G.normalized hT (ContinuousMap.const (Icc (0 : ℝ) T) c) (fun _ => hc)).path =
      (G.smul c⁻¹).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  rfl

variable {G} {q d : ℕ} {R A : ℝ}

theorem WordBound.normalize_const (hG : G.WordBound q R (A * c) d) :
    (G.normalized hT (ContinuousMap.const (Icc (0 : ℝ) T) c) (fun _ => hc)).WordBound q R A d := by
  have hh := hG.smul c⁻¹
  have he : |c⁻¹| * (A*c) = A := by
    rw [abs_of_pos (inv_pos.mpr hc)]
    field_simp
  rw [he] at hh
  exact hh.of_path_eq _ (G.normalized_const_path hT c hc)

theorem WordBound.of_normalized_const
    (hG : (G.normalized hT (ContinuousMap.const (Icc (0 : ℝ) T) c) (fun _ => hc)).WordBound q R A
        d) :
    G.WordBound q R (c*A) d := by
  have hh := hG.smul c
  rw [abs_of_pos hc] at hh
  apply hh.of_path_eq G
  apply path_eq_of_raw_eq
  intro t x θ
  change c • (c⁻¹ • raw (t,(x,θ))) = raw (t,(x,θ))
  rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul]

end EulerPacketCylinderField.Field

namespace EulerMeanPacketProvider.Budget

open Set EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerPacketCylinderField
  EulerPacketTimeProfile

variable {P : ℝ} [Fact (0 < P)] {D : Data} {R : ℝ} (L : Budget D 6 R)

/-- The mean source costs are fixed before selecting any grade or its profile. -/
structure GradeGuards : Prop where
  velocity : L.velocityCost ≤ R
  derivative : L.derivativeCost ≤ R
  pressureGradient : L.pressureGradientCost ≤ R

variable (W : GradeGuards L) (S : Scales (Icc (0 : ℝ) D.T))
  {raw : VectorField} (G : Forcing D raw) (F : Field P D.T raw)
  (p : ℕ) (hp : 2 ≤ p)
  (hforce : (F.normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
    6 R 1 (meanForceShift p))

include W hp hforce

/-- The three actual mean outputs satisfy the unit budget at b_p=H₀^(2p−2)
and the same external radius. -/
theorem grade_bounds :
    ((G.vectorCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) ∧
    ((G.vectorDerivativeCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) ∧
    ((G.pressureGradientCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) := by
  have hc : 0 < S.H0^(2*p-2) := pow_pos S.H0_pos _
  have hf : F.WordBound 6 R (1*S.H0^(2*p-2)) (meanForceShift p) := by
    have hh := hforce.of_normalized_const D.T_pos.le (S.H0^(2*p-2)) hc
    simpa only [mul_one,one_mul] using hh
  obtain ⟨hv,ht,hπ⟩ := L.grade_profile_bounds P G F p (meanForceShift p) 1 S.H0
    zero_le_one S.H0_pos.le hf
  simp only [one_mul] at hv ht hπ
  have hroom : meanForceShift p+3+1 ≤ meanShift p := by
    dsimp only [meanForceShift,meanShift]
    omega
  refine ⟨?_,?_,?_⟩
  · exact (hv.normalize_const D.T_pos.le (S.H0^(2*p-2)) hc).absorb_amplitude_to
      L.radius_bounds.1 L.costs_nonneg.1 W.velocity hroom
  · exact (ht.normalize_const D.T_pos.le (S.H0^(2*p-2)) hc).absorb_amplitude_to
      L.radius_bounds.1 L.costs_nonneg.2.1 W.derivative hroom
  · exact (hπ.normalize_const D.T_pos.le (S.H0^(2*p-2)) hc).absorb_amplitude_to
      L.radius_bounds.1 L.costs_nonneg.2.2.2 W.pressureGradient hroom

theorem vector_grade_bound :
    ((G.vectorCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) := (L.grade_bounds W S G F p hp hforce).1

theorem derivative_grade_bound :
    ((G.vectorDerivativeCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) := (L.grade_bounds W S G F p hp hforce).2.1

theorem pressure_gradient_grade_bound :
    ((G.pressureGradientCylinderField P).normalized D.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanShift p) := (L.grade_bounds W S G F p hp hforce).2.2

end EulerMeanPacketProvider.Budget
