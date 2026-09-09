/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLp
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLpAlgebra
import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLpMap
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerJetLp
import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldJetLp

/-! One fixed coefficient radius controls both the true cover sup norms
and the actual cylinder L² norms of the corrected lifted velocity. -/

@[expose] public section


noncomputable section


namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerSobolevGevreyOperators
  EulerCylinderJetLp EulerCylinderCoverDescent
open scoped ContDiff BoundedContinuousFunction

/-- Lifted input constant, given by `1 + sobolevEmbeddingConstant P 3`. -/
def liftedInputConstant (P : ℝ) [Fact (0 < P)] : ℝ := 1 + sobolevEmbeddingConstant P 3

/-- Lifted input radius, given by `1 + ‖coordinateEquiv.symm.toContinuousLinearMap‖ * (R +
ρ⁻¹)`. -/
def liftedInputRadius (R ρ : ℝ) : ℝ :=
  1 + ‖coordinateEquiv.symm.toContinuousLinearMap‖ * (R + ρ⁻¹)

theorem liftedInputConstant_one_le (P : ℝ) [Fact (0 < P)] : 1 ≤ liftedInputConstant P := by
  have h := sobolevEmbeddingConstant_nonneg P 3
  dsimp [liftedInputConstant]
  linarith

theorem liftedInputConstant_embedding_le (P : ℝ) [Fact (0 < P)] :
    sobolevEmbeddingConstant P 3 ≤ liftedInputConstant P := by
  dsimp [liftedInputConstant]
  linarith

theorem liftedInputRadius_pos (R ρ : ℝ) (hR : 0 ≤ R) (hρ : 0 < ρ) :
    0 < liftedInputRadius R ρ := by
  dsimp [liftedInputRadius]
  positivity

theorem liftedInputRadius_packet (R ρ : ℝ) (_hR : 0 ≤ R) (hρ : 0 < ρ) :
    ‖coordinateEquiv.symm.toContinuousLinearMap‖ * R ≤ liftedInputRadius R ρ := by
  have h := mul_nonneg (norm_nonneg coordinateEquiv.symm.toContinuousLinearMap) (inv_nonneg.mpr
      hρ.le)
  dsimp [liftedInputRadius]
  nlinarith

theorem liftedInputRadius_error (R ρ : ℝ) (hR : 0 ≤ R) :
    ‖coordinateEquiv.symm.toContinuousLinearMap‖ * ρ⁻¹ ≤ liftedInputRadius R ρ := by
  have h := mul_nonneg (norm_nonneg coordinateEquiv.symm.toContinuousLinearMap) hR
  dsimp [liftedInputRadius]
  nlinarith

private theorem jet_envelope_mono {C D R S : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hCD : C ≤ D) (hRS : R ≤ S) (n : ℕ) :
    C*R^n*(n.factorial : ℝ)^2 ≤ D*S^n*(n.factorial : ℝ)^2 := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hCD (pow_le_pow_left₀ hR hRS n) (pow_nonneg hR n) hD)
    (sq_nonneg _)

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw : VectorField}

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds1 (n : ℕ) : NormedAddCommGroup (LiftTangent
    [×n]→L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to
shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds3 (n : ℕ) : NormedAddCommGroup (LiftTangent
    [×n]→L[ℝ] LiftTangent) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds4 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds5 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] Space))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds6 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds7 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds8 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] LiftTangent))
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent →ᵇ (LiftTangent
[×n]→L[ℝ] Space))` instance to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds9 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent →ᵇ (LiftTangent
[×n]→L[ℝ] LiftTangent))` instance to shorten typeclass synthesis. -/
local instance instPacketLiftedCoefficientBounds10 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent)) := inferInstance

private theorem pointField_map (G : Field P T raw) (L : Space →L[ℝ] Space)
    (t : Icc (0 : ℝ) T) :
    (G.map L).toFieldTower.pointField t = fun q => L (G.toFieldTower.pointField t q) := by
  funext q
  have h : (G.map L).toFieldTower.pointField t (coveringMap P (sectionPoint P q)) =
      L (G.toFieldTower.pointField t (coveringMap P (sectionPoint P q))) := by
    change (G.map L).toFieldTower.pointField t
        ((sectionPoint P q).1,((sectionPoint P q).2 : AddCircle P)) =
      L (G.toFieldTower.pointField t ((sectionPoint P q).1,((sectionPoint P q).2 : AddCircle P)))
    rw [(G.map L).toFieldTower_pointField_raw, G.toFieldTower_pointField_raw]
  simpa only [coveringMap_sectionPoint] using h

theorem Budget.liftedPacketCoefficient_jetSeries (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (n : ℕ) (t : Icc (0 : ℝ) T) :
    (fun q => jetSeries P ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) q
        n) =
      tensor P (fun q => transportDirection A.κ A.direction
        ((B.correctedFieldTower P).pointField t q)) n := by
  have he : ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) =
      fun x => transportDirection A.κ A.direction ((B.correctedFieldTower P).pointField t
          (coveringMap P x)) :=
    funext (B.liftedPacketCoefficient_eq_corrected P G hG t)
  rw [he]
  rfl

theorem Budget.liftedPacketCoefficient_memLp (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P ((B.liftedPacketCoefficient P G).field t : LiftTangent →
        LiftTangent) q n)
      2 (liftMeasure P) := by
  rw [B.liftedPacketCoefficient_jetSeries P G hG]
  exact tensor_map_memLp P (transportLinear A.κ A.direction) _
    ((B.correctedFieldTower P).pointField_smooth t) n ((B.correctedFieldTower P).coverTensor_memLp
        n t)

theorem Budget.liftedPacketCoefficient_jet_bound (G : Field P T raw)
    (k R ρ C0 Cn Ce : ℝ) (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hC0 : 0 ≤ C0) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce)
    (hG : G.WordBound 6 R C0 0)
    (hN : (G.map (normalComponentMap A.direction)).WordBound 6 R (Cn / k) 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T),
      weightedNorm P 6 n ρ ((B.fieldTower P).realization (n + 6) t) ≤ Ce) (n : ℕ) :
    ‖(B.liftedPacketCoefficient P G).jet n‖ ≤
      (liftedInputConstant P*((C0+Cn)/k+2*Ce)) * (liftedInputRadius R ρ)^n * (n.factorial : ℝ)^2 :=
          by
  have hK : 0 ≤ liftedInputConstant P := (zero_le_one.trans (liftedInputConstant_one_le P))
  have hk0 : 0 < k := by linarith
  have hA' (j : ℕ) : ‖G.toSmoothTimeField.jet j‖ ≤
      (liftedInputConstant P*C0)*(liftedInputRadius R ρ)^j*(j.factorial : ℝ)^2 :=
    (hG.toSmoothTimeField_jet_bound (by norm_num) hR hC0 j).trans
      (jet_envelope_mono (mul_nonneg hK hC0)
        (mul_nonneg (norm_nonneg _) hR)
        (mul_le_mul_of_nonneg_right (liftedInputConstant_embedding_le P) hC0)
        (liftedInputRadius_packet R ρ hR hρ) j)
  have hN' (j : ℕ) : ‖(G.toSmoothTimeField.map (normalComponentMap A.direction)).jet j‖ ≤
      ((liftedInputConstant P*Cn)/k)*(liftedInputRadius R ρ)^j*(j.factorial : ℝ)^2 := by
    rw [← G.toSmoothTimeField_map_jet]
    have hn := (hN.toSmoothTimeField_jet_bound (by norm_num) hR (div_nonneg hCn hk0.le) j).trans
      (jet_envelope_mono (mul_nonneg hK (div_nonneg hCn hk0.le))
        (mul_nonneg (norm_nonneg _) hR)
        (mul_le_mul_of_nonneg_right (liftedInputConstant_embedding_le P) (div_nonneg hCn hk0.le))
        (liftedInputRadius_packet R ρ hR hρ) j)
    simpa only [mul_div_assoc] using hn
  have hE' (j : ℕ) : ‖(B.correctionCoefficient P).jet j‖ ≤
      (liftedInputConstant P*Ce)*(liftedInputRadius R ρ)^j*(j.factorial : ℝ)^2 :=
    ((B.fieldTower P).toSmoothTimeField_jet_weighted j ρ Ce hρ hCe (hE j)).trans
      (jet_envelope_mono (mul_nonneg hK hCe)
        (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le))
        (mul_le_mul_of_nonneg_right (liftedInputConstant_embedding_le P) hCe)
        (liftedInputRadius_error R ρ hR) j)
  have h := lift_add_inverse_scale_bound G.toSmoothTimeField (B.correctionCoefficient P)
    k hk A.direction hm (liftedInputRadius R ρ) (liftedInputConstant P*C0)
    (liftedInputConstant P*Cn) (liftedInputConstant P*Ce)
    (liftedInputRadius_pos R ρ hR hρ).le (mul_nonneg hK hCe) hA' hN' hE' n
  change ‖(lift (G.toSmoothTimeField.add (B.correctionCoefficient P)) A.κ A.direction).jet n‖ ≤ _
  rw [hκ]
  apply h.trans_eq
  ring

theorem Budget.liftedPacketCoefficient_L2_bound (G : Field P T raw)
    (hGfield : A.approximation = G.toFieldTower)
    (k R ρ C0 Cn Ce : ℝ) (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hC0 : 0 ≤ C0) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce)
    (hG : G.WordBound 6 R C0 0)
    (hN : (G.map (normalComponentMap A.direction)).WordBound 6 R (Cn / k) 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T),
      weightedNorm P 6 n ρ ((B.fieldTower P).realization (n + 6) t) ≤ Ce)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    (eLpNorm (fun q => jetSeries P
      ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure
          P)).toReal ≤
      (liftedInputConstant P*((C0+Cn)/k+2*Ce)) * (liftedInputRadius R ρ)^n * (n.factorial : ℝ)^2 :=
          by
  have hk0 : 0 < k := by linarith
  have hA' := (hG.coverTensor_bound n t).trans
    (jet_envelope_mono hC0 (mul_nonneg (norm_nonneg _) hR) le_rfl
      (liftedInputRadius_packet R ρ hR hρ) n)
  have hN' := (hN.coverTensor_bound n t).trans
    (jet_envelope_mono (div_nonneg hCn hk0.le) (mul_nonneg (norm_nonneg _) hR) le_rfl
      (liftedInputRadius_packet R ρ hR hρ) n)
  rw [pointField_map P G (normalComponentMap A.direction) t] at hN'
  have hE' := ((B.fieldTower P).coverTensor_weighted n ρ Ce hρ t (hE n t)).trans
    (jet_envelope_mono hCe (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le)) le_rfl
      (liftedInputRadius_error R ρ hR) n)
  rw [B.liftedPacketCoefficient_jetSeries P G hGfield,
    B.correctedFieldTower_eq P, FieldTower.add_pointField, hGfield]
  have h := tensor_transport_add_norm_le P A.κ A.direction
    (G.toFieldTower.pointField t) ((B.fieldTower P).pointField t)
    (G.toFieldTower.pointField_smooth t) ((B.fieldTower P).pointField_smooth t) n
    (G.toFieldTower.coverTensor_memLp n t) ((B.fieldTower P).coverTensor_memLp n t)
  have hb := h.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hA' (abs_nonneg A.κ)) hN')
    (mul_le_mul_of_nonneg_left hE' (add_nonneg (abs_nonneg A.κ) (norm_nonneg A.direction))))
  have hki : |A.κ| ≤ 1 := by
    rw [hκ, abs_of_pos (inv_pos.mpr hk0)]
    exact inv_le_one_of_one_le₀ hk
  have hcoef : |A.κ| * C0+Cn/k+(|A.κ| + ‖A.direction‖)*Ce ≤ (C0+Cn)/k+2*Ce := by
    have he := mul_le_mul_of_nonneg_right (add_le_add hki hm) hCe
    calc
      _ ≤ |A.κ| * C0+Cn/k+(1+1)*Ce := add_le_add le_rfl he
      _ = _ := by rw [hκ, abs_of_pos (inv_pos.mpr hk0)]; ring
  have hcoef' : |A.κ| * C0+Cn/k+(|A.κ| + ‖A.direction‖)*Ce ≤
      liftedInputConstant P*((C0+Cn)/k+2*Ce) :=
    hcoef.trans (by
      have hn : 0 ≤ (C0+Cn)/k+2*Ce := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (liftedInputConstant_one_le P) hn)
  apply hb.trans
  calc
    _ = (|A.κ| * C0+Cn/k+(|A.κ| + ‖A.direction‖)*Ce) *
        (liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef' (pow_nonneg (liftedInputRadius_pos R ρ hR hρ).le n))
      (sq_nonneg _)

end EulerAllOrderDriftCorrection
