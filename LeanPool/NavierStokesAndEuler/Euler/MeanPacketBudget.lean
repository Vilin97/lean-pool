/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCylinderWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketPathEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketPressureForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds

@[expose] public section

/-!
Source-only budgets for the actual mean solver on the cylinder.  The radius
and inverse guards are fixed before the forcing amplitude, shift, or grade.
The output fields are the genuine velocity, time derivative, and gradient
of the normalized scalar pressure constructed by the source solver.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set Real ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanTimeContinuousTranslation EulerParameterWordGevrey EulerGevrey
  EulerMeanStrongContinuousGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

/-- All quantitative inputs concern the source coefficients and their inverse.
The fixed normalized forcing factor only accounts for time-L² inclusion. -/
structure Budget (D : Data) (q : ℕ) (R : ℝ) extends SobolevData D (Fin 4) q R where
  forcing_one : 1 ≤ Cf
  forcing_time : sqrt D.T ≤ Cf

def Data.frameCoefficient (D : Data) : MatrixCoefficient D.T
    (fun z => D.F.field (D.clamp z.1) z.2.1) where
  path := D.F.field
  orbit := D.F.translation_contDiff
  raw_eq t x θ := by rw [Data.clamp_coe]

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)
  (P : ℝ) [Fact (0 < P)]

def pressureForceCylinderField : EulerPacketCylinderField.Field P D.T G.pressureForce :=
  G.pressureForceForcing.toCylinderField P

/-- This witness represents the literal spatial gradient encoded by the
packet pressure jet, not merely the projected physical pressure force. -/
def pressureGradientCylinderField : EulerPacketCylinderField.Field P D.T (pressureGradient
  G.scalar) :=
  (D.frameCoefficient.adjoint.multiply (G.pressureForceCylinderField P)).congr (by
    intro t x θ
    change pressureGradient G.scalar (t,(x,θ)) =
      (D.F.field (D.clamp t) x).adjoint (G.pressureForce (t,(x,θ)))
    rw [Data.clamp_coe]
    change (toDual ℝ Space).symm ((pressureJet G.scalar (t,(x,θ))).2.comp spatialInjection) = _
    rw [pressureJet_spatial_derivative G.scalar t x θ
      ((G.scalar_spatial_smooth t).differentiable (by simp) (x,θ))]
    exact G.scalarGradient_eq t x θ)

theorem restore_cylinder_word_bound {q d : ℕ} {R A C : ℝ}
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      ((P⁻¹*sqrt P)*A)*(C*majorant R d n)) :
    (G.toCylinderField P).WordBound q R (A*C) d := by
  have hh := G.toCylinderField_word_bound P (A := ((P⁻¹*sqrt P)*A)*C) (fun n a =>
    (hb n a).trans_eq (by ring))
  have hC : sqrt P*(((P⁻¹*sqrt P)*A)*C) = A*C := by
    calc
      _ = (sqrt P*(P⁻¹*sqrt P))*(A*C) := by ring
      _ = _ := by rw [embedding_mean_norm_product, one_mul]
  simpa only [hC] using hh

end Forcing

namespace Budget

variable {D : Data} {q : ℕ} {R : ℝ} (B : Budget D q R)

def velocityCost : ℝ := B.toSobolevData.velocityAmplitude
def derivativeCost : ℝ := B.toSobolevData.derivativeAmplitude
def pressureForceCost : ℝ := B.toSobolevData.pressureAmplitude
def pressureGradientCost : ℝ := 3*sobolevCoefficientAmplitude (Fin 4) q B.Rc
  B.CF*B.pressureForceCost

theorem coefficient_radius_nonneg : 0 ≤ B.Rc :=
  (by norm_num : (0:ℝ) ≤ 1024).trans B.radius_lower

theorem radius_bounds : 1 ≤ R ∧ sobolevCoefficientRadius (Fin 4) B.Rc ≤ R := by
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 4) B.Rc B.coefficient_radius_nonneg
  have hm := B.inverse_cost_lower
  have h := B.radius_budget
  constructor <;> nlinarith only [hr, hm, h]

theorem costs_nonneg : 0 ≤ B.velocityCost ∧ 0 ≤ B.derivativeCost ∧
    0 ≤ B.pressureForceCost ∧ 0 ≤ B.pressureGradientCost := by
  have hF := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q B.Rc B.CF
    B.coefficient_radius_nonneg B.CF_nonneg
  have hF₁ := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q B.Rc B.CF₁
    B.coefficient_radius_nonneg B.CF₁_nonneg
  have hT := coordinateTraceCost_nonneg D.T D.T_pos.le
  have hf := B.Cf_nonneg
  unfold velocityCost derivativeCost pressureGradientCost pressureForceCost
    SobolevData.velocityAmplitude SobolevData.derivativeAmplitude SobolevData.pressureAmplitude
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem frameCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.frameCoefficient.path) a‖ ≤
      B.CF*majorant B.Rc 0 n :=
  D.F.norm_iteratedFDeriv_translation_le n (B.CF*majorant B.Rc 0 n)
    (mul_nonneg B.CF_nonneg (majorant_nonneg B.Rc B.coefficient_radius_nonneg 0 n))
    (B.frame_bound n) a

/-- Same-radius bounds on the three actual physical output paths. The
period factors from averaging and constant extension cancel exactly. -/
theorem physical_word_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hG : (G.toCylinderField P).WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureForceCylinderField P).WordBound q R (A*B.pressureForceCost) (d+3) := by
  have hA' : 0 ≤ (P⁻¹*sqrt P)*A := by
    have hp := (Fact.out : 0 < P)
    positivity
  obtain ⟨hv, hd, hp⟩ := B.toSobolevData.path_envelope_bounds B.forcing_one B.forcing_time
    spatialDirection spatialDirection_norm G d ((P⁻¹*sqrt P)*A) hA'
    (G.ordinary_word_bound P hG)
  exact ⟨G.vectorForcing.restore_cylinder_word_bound P hv,
    G.vectorDerivativeForcing.restore_cylinder_word_bound P hd,
    G.pressureForceForcing.restore_cylinder_word_bound P hp⟩

/-- The mean solver consumes at most three shifts, with a linear forcing
amplitude and the identical radius. The third output is d(bar q). -/
theorem word_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hG : (G.toCylinderField P).WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) := by
  obtain ⟨hv, hd, hp⟩ := B.physical_word_bounds P G d A hA hG
  have hprod := hp.multiply D.frameCoefficient.adjoint B.Rc B.CF
    B.coefficient_radius_nonneg B.CF_nonneg (mul_nonneg hA B.costs_nonneg.2.2.1) B.radius_bounds.2
    (D.frameCoefficient.adjoint_bound B.Rc B.CF B.frameCoefficient_bound)
  refine ⟨hv, hd, ?_⟩
  change (D.frameCoefficient.adjoint.multiply (G.pressureForceCylinderField P)).WordBound q R
    (A*B.pressureGradientCost) (d+3)
  convert! hprod using 1
  unfold pressureGradientCost
  ring

/-- Any actual cylinder witness of the input raw forcing can supply the
bound; the provider's canonical choice is immaterial. -/
theorem word_bounds_of_field (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (d : ℕ) (A : ℝ) (hA : 0 ≤ A) (hF : F.WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) :=
  B.word_bounds P G d A hA (hF.transfer (G.toCylinderField P))

/-- A common three-shift budget also covers the velocity, and is therefore
within the source allowance of ten shifts. -/
theorem three_shift_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (d : ℕ) (A : ℝ) (hA : 0 ≤ A) (hF : F.WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+3) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) := by
  obtain ⟨hv, hd, hp⟩ := B.word_bounds_of_field P G F d A hA hF
  exact ⟨hv.mono_shift B.radius_bounds.1 (mul_nonneg hA B.costs_nonneg.1) (by omega), hd, hp⟩

/-- The mean profile H₀^(2p−2) is a constant scalar envelope. The same
fixed source budget applies at every grade and every derivative shift. -/
theorem grade_profile_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (p d : ℕ) (A H₀ : ℝ) (hA : 0 ≤ A) (hH₀ : 0 ≤ H₀)
    (hF : F.WordBound q R (A*H₀^(2*p-2)) d) :
    (G.vectorCylinderField P).WordBound q R ((A*B.velocityCost)*H₀^(2*p-2)) (d+3) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R ((A*B.derivativeCost)*H₀^(2*p-2)) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R ((A*B.pressureGradientCost)*H₀^(2*p-2)) (d+3)
      := by
  have hh := B.three_shift_bounds P G F d (A*H₀^(2*p-2)) (mul_nonneg hA (pow_nonneg hH₀ _)) hF
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

end Budget
end EulerMeanPacketProvider
