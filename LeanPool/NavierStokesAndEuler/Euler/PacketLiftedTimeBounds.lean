/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficientBounds

@[expose] public section

/-! The actual lifted time coefficient has simultaneous sup and cylinder
L² bounds from the genuine approximation and correction time derivatives. -/

noncomputable section


namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerSobolevGevreyOperators
  EulerCylinderJetLp EulerCylinderCoverDescent
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw_t : VectorField}

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] LiftTangent) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))
  := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) :=
  inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ]
  LiftTangent)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))
  := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent)) := inferInstance

private theorem time_envelope_mono {C D R S : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hCD : C ≤ D) (hRS : R ≤ S) (n : ℕ) :
    C*R^n*(n.factorial : ℝ)^2 ≤ D*S^n*(n.factorial : ℝ)^2 :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul hCD (pow_le_pow_left₀ hR hRS n) (pow_nonneg hR n) hD) (sq_nonneg _)

theorem Budget.liftedPacketDerivativeCoefficient_periodic (H : Field P T raw_t)
    (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketDerivativeCoefficient P H).field t (x.1,(c : ℝ)+x.2) =
      (B.liftedPacketDerivativeCoefficient P H).field t x := by
  have hc : coveringMap P (x.1,(c : ℝ)+x.2) = coveringMap P x :=
    EulerCylinderMeasureDescent.coveringMap_deck P c x
  change transportDirection A.κ A.direction
    (EulerCylinderSmoothOrbit.pointField P H.path H.orbit t (coveringMap P (x.1,(c : ℝ)+x.2)) +
      (B.timeDerivativeTower P).pointField t (coveringMap P (x.1,(c : ℝ)+x.2))) = _
  rw [hc]
  rfl

theorem Budget.liftedPacketDerivativeCoefficient_jetSeries (H : Field P T raw_t)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    (fun q => jetSeries P ((B.liftedPacketDerivativeCoefficient P H).field t : LiftTangent →
      LiftTangent) q n) =
      tensor P (fun q => transportDirection A.κ A.direction
        (H.toFieldTower.pointField t q + (B.timeDerivativeTower P).pointField t q)) n := by
  have he : ((B.liftedPacketDerivativeCoefficient P H).field t : LiftTangent → LiftTangent) =
      fun x => transportDirection A.κ A.direction
        (H.toFieldTower.pointField t (coveringMap P x) +
          (B.timeDerivativeTower P).pointField t (coveringMap P x)) := by
    funext x
    change transportDirection A.κ A.direction
      (H.toSmoothTimeField.field t x + (B.timeDerivativeTower P).pointField t (coveringMap P x)) = _
    rw [H.toSmoothTimeField_apply]
    change transportDirection A.κ A.direction
      (raw_t (t,x) + (B.timeDerivativeTower P).pointField t (coveringMap P x)) =
      transportDirection A.κ A.direction
        (H.toFieldTower.pointField t (x.1,(x.2 : AddCircle P)) +
          (B.timeDerivativeTower P).pointField t (coveringMap P x))
    rw [H.toFieldTower_pointField_raw]
  rw [he]
  rfl

theorem Budget.liftedPacketDerivativeCoefficient_memLp (H : Field P T raw_t)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P
      ((B.liftedPacketDerivativeCoefficient P H).field t : LiftTangent → LiftTangent) q n)
      2 (liftMeasure P) := by
  rw [B.liftedPacketDerivativeCoefficient_jetSeries P H]
  exact tensor_map_memLp P (transportLinear A.κ A.direction)
    (fun q => H.toFieldTower.pointField t q + (B.timeDerivativeTower P).pointField t q)
    (fun q => (H.toFieldTower.pointField_smooth t q).add ((B.timeDerivativeTower
      P).pointField_smooth t q)) n
    (tensor_add_memLp P _ _ (H.toFieldTower.pointField_smooth t)
      ((B.timeDerivativeTower P).pointField_smooth t) n
      (H.toFieldTower.coverTensor_memLp n t) ((B.timeDerivativeTower P).coverTensor_memLp n t))

theorem Budget.liftedPacketDerivativeCoefficient_jet_bound (H : Field P T raw_t)
    (R ρ Ch Ce : ℝ) (hκ : |A.κ| ≤ 1) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hCh : 0 ≤ Ch) (hCe : 0 ≤ Ce)
    (hH : H.WordBound 6 R Ch 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T),
      weightedNorm P 6 n ρ ((B.timeDerivativeTower P).realization (n+6) t) ≤ Ce) (n : ℕ) :
    ‖(B.liftedPacketDerivativeCoefficient P H).jet n‖ ≤
      (2*liftedInputConstant P*(Ch+Ce)) * (liftedInputRadius R ρ)^n * (n.factorial : ℝ)^2 := by
  have hK : 0 ≤ liftedInputConstant P := zero_le_one.trans (liftedInputConstant_one_le P)
  have hh := (hH.toSmoothTimeField_jet_bound (by norm_num) hR hCh n).trans
    (time_envelope_mono (mul_nonneg hK hCh) (mul_nonneg (norm_nonneg _) hR)
      (mul_le_mul_of_nonneg_right (liftedInputConstant_embedding_le P) hCh)
      (liftedInputRadius_packet R ρ hR hρ) n)
  have he : ‖(B.correctionDerivativeCoefficient P).jet n‖ ≤
      (liftedInputConstant P*Ce)*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2 :=
    ((B.timeDerivativeTower P).toSmoothTimeField_jet_weighted n ρ Ce hρ hCe (hE n)).trans
      (time_envelope_mono (mul_nonneg hK hCe) (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le))
        (mul_le_mul_of_nonneg_right (liftedInputConstant_embedding_le P) hCe)
        (liftedInputRadius_error R ρ hR) n)
  have hsum := (H.toSmoothTimeField.add_jet_norm_le (B.correctionDerivativeCoefficient P) n).trans
    (add_le_add hh he)
  have hfull := lift_jet_norm_le_full
    (H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)) A.κ A.direction n
  change ‖(lift (H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)) A.κ
    A.direction).jet n‖ ≤ _
  apply hfull.trans
  calc
    _ ≤ 2*‖(H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)).jet n‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ 2*((liftedInputConstant P*Ch)*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2 +
        (liftedInputConstant P*Ce)*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

theorem Budget.liftedPacketDerivativeCoefficient_L2_bound (H : Field P T raw_t)
    (R ρ Ch Ce : ℝ) (hκ : |A.κ| ≤ 1) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hCh : 0 ≤ Ch) (hCe : 0 ≤ Ce)
    (hH : H.WordBound 6 R Ch 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T),
      weightedNorm P 6 n ρ ((B.timeDerivativeTower P).realization (n+6) t) ≤ Ce)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    (eLpNorm (fun q => jetSeries P
      ((B.liftedPacketDerivativeCoefficient P H).field t : LiftTangent → LiftTangent) q n)
      2 (liftMeasure P)).toReal ≤
      (2*liftedInputConstant P*(Ch+Ce)) * (liftedInputRadius R ρ)^n * (n.factorial : ℝ)^2 := by
  have hh := (hH.coverTensor_bound n t).trans
    (time_envelope_mono hCh (mul_nonneg (norm_nonneg _) hR) le_rfl (liftedInputRadius_packet R ρ hR
      hρ) n)
  have he := ((B.timeDerivativeTower P).coverTensor_weighted n ρ Ce hρ t (hE n t)).trans
    (time_envelope_mono hCe (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le)) le_rfl
      (liftedInputRadius_error R ρ hR) n)
  let f := H.toFieldTower.pointField t
  let g := (B.timeDerivativeTower P).pointField t
  have hf := H.toFieldTower.pointField_smooth t
  have hg := (B.timeDerivativeTower P).pointField_smooth t
  have hF := H.toFieldTower.coverTensor_memLp n t
  have hG := (B.timeDerivativeTower P).coverTensor_memLp n t
  have hs := (tensor_add_norm_le P f g hf hg n hF hG).trans (add_le_add hh he)
  have hb := tensor_transport_norm_le_full P A.κ A.direction (fun q => f q+g q)
    (fun q => (hf q).add (hg q)) n (tensor_add_memLp P f g hf hg n hF hG)
  rw [B.liftedPacketDerivativeCoefficient_jetSeries P H]
  apply hb.trans
  calc
    _ ≤ 2*(eLpNorm (tensor P (fun q => f q+g q) n) 2 (liftMeasure P)).toReal :=
      mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
    _ ≤ 2*(Ch*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2 +
        Ce*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (2*(Ch+Ce))*(liftedInputRadius R ρ)^n*(n.factorial : ℝ)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (by nlinarith [liftedInputConstant_one_le P] : 2*(Ch+Ce) ≤ 2*liftedInputConstant P*(Ch+Ce))
        (pow_nonneg (liftedInputRadius_pos R ρ hR hρ).le n)) (sq_nonneg _)

end EulerAllOrderDriftCorrection
