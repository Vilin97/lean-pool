/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldJetLp
import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLpMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderMeasureDescent
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerJetLp
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCorrectionPotential
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftCorrection
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftGraph
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPointwiseGevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalPressureGevrey
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionOutputPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedHessianError
public import LeanPool.NavierStokesAndEuler.Euler.PacketRadiusCostPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGlobalShear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! Related estimates used together by the same construction modules. -/

section

/-! A fixed actual correction and the derived approximation bounds
construct physical graph-flow data. No new solution or inverse is an input. -/

section

/-! The actual lifted time coefficient has simultaneous sup and cylinder
L² bounds from the genuine approximation and correction time derivatives. -/

@[expose] public section

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

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedTimeBounds1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedTimeBounds2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to
shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds3 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    LiftTangent) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to shorten
typeclass synthesis. -/
local instance instPacketLiftedTimeBounds4 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds5 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] Space))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds6 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds7 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds8 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] LiftTangent))
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent →ᵇ (LiftTangent
[×n]→L[ℝ] Space))` instance to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds9 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent →ᵇ (LiftTangent
[×n]→L[ℝ] LiftTangent))` instance to shorten typeclass synthesis. -/
local instance instPacketLiftedTimeBounds10 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
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
      weightedNorm P 6 n ρ ((B.timeDerivativeTower P).realization (n + 6) t) ≤ Ce) (n : ℕ) :
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
      weightedNorm P 6 n ρ ((B.timeDerivativeTower P).realization (n + 6) t) ≤ Ce)
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerSobolevGevreyOperators
  EulerPhysicalGraphFlowBounds EulerCylinderCoverDescent
open scoped ContDiff

/-- Physical input radius, given by `max (liftedInputRadius R ρ) (liftedInputRadius Rt ρ)`. -/
def physicalInputRadius (R Rt ρ : ℝ) : ℝ :=
  max (liftedInputRadius R ρ) (liftedInputRadius Rt ρ)

/-- Physical input size, given by `liftedInputConstant P*((C0+Cn)/k+2*Ev)`. -/
def physicalInputSize (P k C0 Cn Ev : ℝ) [Fact (0 < P)] : ℝ :=
  liftedInputConstant P*((C0+Cn)/k+2*Ev)

theorem envelope_radius_mono {C R S : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRS : R ≤ S) (n : ℕ) :
    C*R^n*(n.factorial : ℝ)^2 ≤ C*S^n*(n.factorial : ℝ)^2 :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRS n) hC) (sq_nonneg _)

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : EulerAllOrderCorrectionData.Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}

/-- Physical flow data as an element of `EulerPhysicalGraphFlowBounds.Data P T`. -/
def Budget.physicalFlowData (G : Field P T raw) (H : Field P T raw_t)
    (hGfield : A.approximation = G.toFieldTower) (htime : TimeDerivative hT.le G H)
    (k R Rt ρ C0 Cn Ch Ev Et : ℝ)
    (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hRt : 0 ≤ Rt) (hρ : 0 < ρ)
    (hC0 : 0 ≤ C0) (hCn : 0 ≤ Cn) (hCh : 0 ≤ Ch) (hEv : 0 ≤ Ev) (hEt : 0 ≤ Et)
    (hG : G.WordBound 6 R C0 0)
    (hN : (G.map (normalComponentMap A.direction)).WordBound 6 R (Cn / k) 0)
    (hH : H.WordBound 6 Rt Ch 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T), weightedNorm P 6 n ρ
      ((B.fieldTower P).realization (n + 6) t) ≤ Ev)
    (hEtower : ∀ n (t : Icc (0 : ℝ) T), weightedNorm P 6 n ρ
      ((B.timeDerivativeTower P).realization (n + 6) t) ≤ Et)
    (hsmall : physicalInputSize P k C0 Cn Ev * physicalInputRadius R Rt ρ * T ≤ 1 / 8) :
    EulerPhysicalGraphFlowBounds.Data P T := by
  have hrv := (liftedInputRadius_pos R ρ hR hρ)
  have hrt := (liftedInputRadius_pos Rt ρ hRt hρ)
  have hK : 0 ≤ liftedInputConstant P := zero_le_one.trans (liftedInputConstant_one_le P)
  have hamp : 0 ≤ physicalInputSize P k C0 Cn Ev := by
    dsimp [physicalInputSize]
    positivity
  have hamp1 : 0 ≤ 2*liftedInputConstant P*(Ch+Et) := by positivity
  have hκ1 : |A.κ| ≤ 1 := by
    rw [hκ,abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
    exact inv_le_one_of_one_le₀ hk
  refine {
    time_nonneg := hT.le
    A := B.liftedPacketCoefficient P G
    A₁ := B.liftedPacketDerivativeCoefficient P H
    time_derivative := B.liftedPacketCoefficient_timeDerivative P G H htime
    periodic := B.liftedPacketCoefficient_periodic P G
    periodic_time := B.liftedPacketDerivativeCoefficient_periodic P H
    divergence := B.liftedPacketCoefficient_trace P G hGfield
    B := physicalInputSize P k C0 Cn Ev
    R := physicalInputRadius R Rt ρ
    C := physicalInputSize P k C0 Cn Ev
    S := physicalInputRadius R Rt ρ
    C₁ := 2*liftedInputConstant P*(Ch+Et)
    S₁ := physicalInputRadius R Rt ρ
    B_nonneg := hamp
    R_pos := hrv.trans_le (le_max_left _ _)
    C_nonneg := hamp
    S_nonneg := hrv.le.trans (le_max_left _ _)
    C₁_nonneg := hamp1
    S₁_nonneg := hrv.le.trans (le_max_left _ _)
    small := hsmall
    sup_bound := ?_
    integrable := fun t n => B.liftedPacketCoefficient_memLp P G hGfield n t
    lp_bound := ?_
    integrable_time := fun t n => B.liftedPacketDerivativeCoefficient_memLp P H n t
    lp_bound_time := ?_ }
  · intro n
    exact (B.liftedPacketCoefficient_jet_bound P G k R ρ C0 Cn Ev hk hκ hm
      hR hρ hC0 hCn hEv hG hN hE n).trans
      (envelope_radius_mono hamp hrv.le (le_max_left _ _) n)
  · intro t n
    exact (B.liftedPacketCoefficient_L2_bound P G hGfield k R ρ C0 Cn Ev hk hκ hm
      hR hρ hC0 hCn hEv hG hN hE n t).trans
      (envelope_radius_mono hamp hrv.le (le_max_left _ _) n)
  · intro t n
    exact (B.liftedPacketDerivativeCoefficient_L2_bound P H Rt ρ Ch Et hκ1 hm
      hRt hρ hCh hEt hH hEtower n t).trans
      (envelope_radius_mono hamp1 hrt.le (le_max_right _ _) n)

end EulerAllOrderDriftCorrection

end
end

end

section

/-! Actual weighted correction and pressure norms bound the physical
velocity gradient and the Hessian of the constructed scalar potential
for that same correction. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerSmoothLimit EulerAllOrderCorrectionData EulerLiftedGradientSpace
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevGevreyOperators
  EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey EulerGraphPressurePotential
  EulerCylinderPhysicalTensor EulerGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

/-- Weighted physical gradient cost, given by `((1+9*CF)*physicalFixedCost D R CF ρ⁻¹
1)*(sobolevEmbeddingConstant P 3*Cw)`. -/
def weightedPhysicalGradientCost (R CF ρ Cw : ℝ) : ℝ :=
  ((1+9*CF)*physicalFixedCost D R CF ρ⁻¹ 1)*(sobolevEmbeddingConstant P 3*Cw)

theorem weightedPhysicalGradientCost_nonneg (R CF ρ Cw : ℝ)
    (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hρ : 0 < ρ) (hCw : 0 ≤ Cw) :
    0 ≤ weightedPhysicalGradientCost D P R CF ρ Cw := by
  have h := physicalFixedCost_nonneg D R CF ρ⁻¹ 1 hR hCF (inv_nonneg.mpr hρ.le)
  have hs := sobolevEmbeddingConstant_nonneg P 3
  unfold weightedPhysicalGradientCost
  positivity

variable {A : Data P D.T} (Q : Budget P D.T_pos A)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
  (R CF : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF)
  (hFb : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ CF * majorant R 0 n)

include hX hXY hY hdet hR hCF hFb in
theorem Budget.physical_gradient_hessian_of_weighted (k ρ Cw d : ℝ)
    (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : A.direction = D.m₀)
    (hρ : 0 < ρ) (hCw : 0 ≤ Cw) (hd : 0 ≤ d)
    (he : ∀ n (t : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
      ((Q.fieldTower P).realization (n + 6) t) ≤ Cw * d)
    (hp : ∀ n (t : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
      ((Q.pressureTower P).realization (n + 6) t) ≤ Cw * d)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y t y)
      (Q.pointField P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤
        weightedPhysicalGradientCost D P R CF ρ Cw*k*d ∧
    ‖fderiv ℝ (gradient (Q.physicalPotential D P k Y t)) x‖ ≤
        weightedPhysicalGradientCost D P R CF ρ Cw*k*d := by
  let Cpt := sobolevEmbeddingConstant P 3*Cw
  have hCpt : 0 ≤ Cpt := mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) hCw
  have hword (F : FieldTower P D.T)
      (hF : ∀ n (s : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
        (F.realization (n+6) s) ≤ Cw*d) (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (F.pointField s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    have h := F.pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega) le_rfl
      ρ (Cw*d) hρ s (hF n s) y
    simpa only [Cpt,mul_assoc] using h
  have heword (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (Q.pointField P s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    simpa only [Q.correctionTower_pointField P s] using hword (Q.fieldTower P) he n s y
  have hpword (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (Q.pointPressure P s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    simpa only [Q.pressureTower_pointField P s] using hword (Q.pressureTower P) hp n s y
  have hYd := continuousInverse_differentiable D X Y hX hXY hY
  have hk0 : 0 < k := by linarith
  have hki : |k⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hk0)]
    exact inv_le_one_of_one_le₀ hk
  have hv := physicalReconstruction_power_bound D P k⁻¹ k (Q.pointField P)
    (Q.pointField_smooth P) R CF (Cpt*d) ρ⁻¹ hR hCF (mul_nonneg hCpt hd)
    (inv_nonneg.mpr hρ.le) hFb heword X Y hX hYd hXY hdet hk hki 1 t x
  have hpr := physicalPressureForce_power_bound D P k⁻¹ k (Q.pointPressure P)
    (Q.pointPressure_smooth P) R CF (Cpt*d) ρ⁻¹ hR hCF (mul_nonneg hCpt hd)
    (inv_nonneg.mpr hρ.le) hdet hFb hpword X Y hX hYd hXY hk hki 1 t x
  let H := (1+9*CF)*physicalFixedCost D R CF ρ⁻¹ 1
  have hc := physicalFixedCost_nonneg D R CF ρ⁻¹ 1 hR hCF (inv_nonneg.mpr hρ.le)
  have hcv : physicalFixedCost D R CF ρ⁻¹ 1 ≤ H := by dsimp [H]; nlinarith
  have hcp : 9*CF*physicalFixedCost D R CF ρ⁻¹ 1 ≤ H := by dsimp [H]; nlinarith
  have absorb (v c : ℝ) (hvc : v ≤ c*(Cpt*d)*k) (hcH : c ≤ H) :
      v ≤ weightedPhysicalGradientCost D P R CF ρ Cw*k*d := by
    apply hvc.trans
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcH (mul_nonneg hCpt hd)) hk0.le).trans_eq
    dsimp [weightedPhysicalGradientCost,H,Cpt]
    ring
  constructor
  · apply absorb _ _ _ hcv
    change ‖iteratedFDeriv ℝ 1 (fun y => k⁻¹ • D.F.field t (Y t y)
      (Q.pointField P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤ _ at hv
    simpa only [norm_iteratedFDeriv_one,pow_one] using hv
  · have hscale : k*A.κ=1 := by rw [hκ]; exact mul_inv_cancel₀ hk0.ne'
    rw [Q.physicalPotential_hessian_norm D P X Y hX hXY hY k hscale t x,hκ,hm]
    apply absorb _ _ _ hcp
    change ‖iteratedFDeriv ℝ 1 (fun y => k⁻¹ • (D.FInv.field t (Y t y)).adjoint
      (Q.pointPressure P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤ _ at hpr
    simpa only [pow_one] using hpr

end EulerAllOrderDriftCorrection

end
end

end

section

/-! Fixed polynomial envelopes for the physical remainder, correction
error and lifted-flow input costs. All spatial derivative orders here are
fixed (H6 and one physical derivative). -/

section

/-! The actual finite and exact packets have the source shear at every
physical point. The slow primary derivative and finite tail contribute
only a fixed source constant divided by the frequency. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderSobolevSpace EulerCylinderCoordinates
  EulerPacketPrimaryShear EulerPacketPrimaryFactorization EulerTransversePacketPrimary
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPeriodicProfile EulerGevrey
open scoped ContDiff

/-- Initialized global shear cost as an element of `ℝ`. -/
def initializedGlobalShearCost (R H0 C : ℝ) : ℝ :=
  ‖coordinateEquiv.symm.toContinuousLinearMap‖*
      (sobolevEmbeddingConstant period 3*fixedVelocityGradeCost R H0 1*(4*R))*C +
    |initializedRemainderDerivativeCost R H0| *C

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

theorem initializedPrimary_global_bound :
    (vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  have hG := initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1 le_rfl
  have hb := hG.high.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_bounds.1) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_bounds.1) S.H0_pos.le
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [initializedProfiles_one_high])

theorem initializedVelocity_global_gradient_error (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  have hc0 := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1
  have hinv : ‖D.FInv.field t (Y x)‖ ≤ NB.C := by
    simpa [majorant] using NB.inverse_bound 0 t (Y x)
  have hprimary := scaled_terminal_global_gradient_bound τ hτ hτT B δ hδ ξ hs α k hk0
    (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) NB.C (by positivity) hc0 NB.C_nonneg
    (initializedPrimary_global_bound M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth) t Y x hY hinv
  have htail := initializedPrimaryRemainder_physical_fderiv_inv M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY.differentiableAt
  rw [hY.fderiv] at htail
  have htail' : ‖fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x‖ ≤ |initializedRemainderDerivativeCost L.R S.H0| *NB.C/k := by
    apply htail.trans
    calc
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*‖D.FInv.field t (Y x)‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hk0.le) (norm_nonneg
            _)
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*NB.C :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hp := (((vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).smul k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hpd : DifferentiableAt ℝ (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def,Pi.smul_apply] using hp.comp x hY.differentiableAt
  have hr := ((initializedPrimaryRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α N hN
      k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hrd : DifferentiableAt ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N
      k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def] using hr.comp x hY.differentiableAt
  have he : (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) =
      (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) +
      (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) := by
    funext y
    dsimp only [initializedPrimaryRemainder,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [he,fderiv_add hpd hrd]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans ((add_le_add hprimary htail').trans_eq (by
    unfold initializedGlobalShearCost
    ring))

theorem initializedExactPhysicalVelocity_global_gradient_error
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k +
        ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
          (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x‖ := by
  rw [initializedExactPhysicalVelocity_fderiv M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q t Y x hY.differentiableAt]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans (add_le_add
    (initializedVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY) le_rfl)

end EulerPacketTerminalDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalCost

open EulerSmoothLimit EulerPacketTerminalDatum EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketCorrectionOutput EulerPacketFiveCost EulerCylinderSobolevSpace
  EulerCylinderCoordinates EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey
  EulerAllOrderDriftCorrection EulerPacketGraphHessian EulerPolynomialCost
  EulerParameterWordGevrey

/-- Coordinate cost, given by `‖coordinateEquiv.symm.toContinuousLinearMap‖`. -/
def coordinateCost : ℝ := ‖coordinateEquiv.symm.toContinuousLinearMap‖

/-- Physical envelope, given by `3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))`. -/
def physicalEnvelope (X S : ℝ) : ℝ :=
  3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))

/-- Shear envelope as an element of `ℝ`. -/
def shearEnvelope (X : ℝ) : ℝ :=
  coordinateCost*(sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*(4*X))*X +
    (8*coordinateCost*sobolevEmbeddingConstant period 3*X*(fixedVelocityGradeCost X X 2+2))*X

/-- Hessian envelope, constructed using `sobolevEmbeddingConstant`. -/
def hessianEnvelope (X : ℝ) : ℝ :=
  sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*X^2*(X+coordinateCost*(4*X)) +
    9*X*physicalEnvelope X (4*X)*sobolevEmbeddingConstant period 3*(fixedVelocityGradeCost X X 2+2)

/-- Time envelope, given by `6*EulerPacketRadiusPolynomial.normalEnvelope X *
(fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)`. -/
def timeEnvelope (X : ℝ) : ℝ :=
  6*EulerPacketRadiusPolynomial.normalEnvelope X *
    (fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)

/-- Radius envelope, given by `1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)`. -/
def radiusEnvelope (X : ℝ) : ℝ := 1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)

/-- Velocity input envelope, given by `liftedInputConstant period*(velocity X X X+normal X X
X)`. -/
def velocityInputEnvelope (X : ℝ) : ℝ := liftedInputConstant period*(velocity X X X+normal X X X)
/-- Error input envelope, given by `2*liftedInputConstant period*outputEnvelope period X`. -/
def errorInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*outputEnvelope period X
/-- Time input envelope, given by `2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
period X)`. -/
def timeInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
    period X)
/-- Weighted error envelope, given by `(1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope
X)*sobolevEmbeddingConstant period 3 * outputEnvelope period X`. -/
def weightedErrorEnvelope (X : ℝ) : ℝ :=
  (1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope X)*sobolevEmbeddingConstant period 3 *
    outputEnvelope period X

/-- Extra envelope as an element of `ℝ`. -/
def extraEnvelope (X : ℝ) : ℝ :=
  1+outputEnvelope period X+radiusEnvelope X+velocityInputEnvelope X+errorInputEnvelope X +
    timeInputEnvelope X+weightedErrorEnvelope X+shearEnvelope X+hessianEnvelope X

/-- Extra polynomial as an element of `Polynomial ℝ`. -/
def extraPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let c := Polynomial.C coordinateCost
  let e := Polynomial.C (sobolevEmbeddingConstant period 3)
  let l := Polynomial.C (liftedInputConstant period)
  let o := outputPolynomial period
  let i := 1+8*X+4*X^2+X
  let a1 := gradePolynomial 1
  let a2 := gradePolynomial 2
  let v := velocityPolynomial
  let n := X*(a2+2)
  let nb := coefficientPolynomial 6 (5*X+1) (1+X+6*X^2+729*X^6)
  let ti := 6*nb*(a1+a2+1)
  let pp := fun S : Polynomial ℝ => 3*X*((1+18*X^2*X)*(9*X^2*(X+c*2*S)+2))
  let sh := c*(e*a1*(4*X))*X+(8*c*e*X*(a2+2))*X
  let he := e*a1*X^2*(X+c*(4*X))+9*X*pp (4*X)*e*(a2+2)
  1+o+(1+c*(4*X+4*i))+l*(v+n)+2*l*o+2*l*(ti+o)+(1+9*X)*pp (4*i)*e*o+sh+he

theorem extraPolynomial_eval (X : ℝ) : extraPolynomial.eval X=extraEnvelope X := by
  unfold extraPolynomial extraEnvelope radiusEnvelope velocityInputEnvelope errorInputEnvelope
    timeInputEnvelope weightedErrorEnvelope shearEnvelope hessianEnvelope physicalEnvelope
    timeEnvelope EulerPacketRadiusPolynomial.normalEnvelope EulerPacketRadiusPolynomial.coeff
    inverseRadiusEnvelope normal
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    outputPolynomial_eval,gradePolynomial_eval,velocityPolynomial_eval,coefficientPolynomial_eval]

/-- Extra constant, given by `coefficientCost extraPolynomial`. -/
def extraConstant : ℝ := coefficientCost extraPolynomial
/-- Extra power, given by `extraPolynomial.natDegree`. -/
def extraPower : ℕ := extraPolynomial.natDegree

theorem extraConstant_pos : 0 < extraConstant := coefficientCost_pos _

theorem extraEnvelope_power (X : ℝ) (hX : 1 ≤ X) : extraEnvelope X ≤ extraConstant*X^extraPower :=
    by
  rw [← extraPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound extraPolynomial X hX)

theorem physicalEnvelope_nonneg (X S : ℝ) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    0 ≤ physicalEnvelope X S := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  unfold physicalEnvelope
  positivity

theorem extra_components (X : ℝ) (hX : 0 ≤ X) :
    outputEnvelope period X ≤ extraEnvelope X ∧ radiusEnvelope X ≤ extraEnvelope X ∧
    velocityInputEnvelope X ≤ extraEnvelope X ∧ errorInputEnvelope X ≤ extraEnvelope X ∧
    timeInputEnvelope X ≤ extraEnvelope X ∧ weightedErrorEnvelope X ≤ extraEnvelope X ∧
    shearEnvelope X ≤ extraEnvelope X ∧ hessianEnvelope X ≤ extraEnvelope X := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hl := zero_le_one.trans (liftedInputConstant_one_le period)
  have ho := zero_le_one.trans (output_components period X hX).1
  have hi : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have hr : 0 ≤ radiusEnvelope X := by unfold radiusEnvelope; positivity
  have hv := velocity_nonneg X X X hX hX
  have hn := normal_nonneg X X X hX hX
  have hvi : 0 ≤ velocityInputEnvelope X := by unfold velocityInputEnvelope; positivity
  have hei : 0 ≤ errorInputEnvelope X := by unfold errorInputEnvelope; positivity
  have ha1 := fixedVelocityGradeCost_nonneg X X hX 1
  have ha2 := fixedVelocityGradeCost_nonneg X X hX 2
  have hb := EulerPacketRadiusPolynomial.normalEnvelope_nonneg X hX
  have ht : 0 ≤ timeEnvelope X := by unfold timeEnvelope; positivity
  have hti : 0 ≤ timeInputEnvelope X := by unfold timeInputEnvelope; positivity
  have hpp1 := physicalEnvelope_nonneg X (4*X) hX (by positivity)
  have hpp2 := physicalEnvelope_nonneg X (4*inverseRadiusEnvelope X) hX (by positivity)
  have hw : 0 ≤ weightedErrorEnvelope X := by unfold weightedErrorEnvelope; positivity
  have hsh : 0 ≤ shearEnvelope X := by unfold shearEnvelope; positivity
  have hhe : 0 ≤ hessianEnvelope X := by unfold hessianEnvelope; positivity
  unfold extraEnvelope
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem gradeCost_mono (R H X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRX : R ≤ X) (hHX : H ≤ X) (n : ℕ) :
    fixedVelocityGradeCost R H n ≤ fixedVelocityGradeCost X X n := by
  have hX := hR.trans hRX
  unfold fixedVelocityGradeCost
  gcongr

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

theorem physicalFixedCost_one_le (R C S X Y : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hRX : R ≤ X) (hCX : C ≤ X) (hSY : S ≤ Y) :
    physicalFixedCost D R C S 1 ≤ physicalEnvelope X Y := by
  have hX := hR.trans hRX
  have hY := hS.trans hSY
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  simp only [physicalFixedCost,physicalRadiusCost,sourceInverseRadius,physicalEnvelope,
    coordinateCost,D.m₀_unit,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,mul_one]
  norm_num only
  gcongr

theorem shearCost_le (R H C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) :
    initializedGlobalShearCost R H C ≤ shearEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hrem : 0 ≤ initializedRemainderDerivativeCost R H := by
    unfold initializedRemainderDerivativeCost
    positivity
  unfold initializedGlobalShearCost shearEnvelope
  rw [abs_of_nonneg hrem]
  unfold initializedRemainderDerivativeCost coordinateCost
  gcongr

theorem hessianCost_le {q : ℕ} {R₀ : ℝ}
    (N : EulerTransversePacketJoin.NormalBudget D q R₀)
    (R H Rc C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hRcX : Rc ≤ X) (hCX : C ≤ X)
    (hNR : N.Rc ≤ X) (hNC : N.C ≤ X) :
    initializedPressureHessianCost N R H Rc C ≤ hessianEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hpp := physicalFixedCost_one_le D Rc C (4*R) X (4*X) hRc hC (by positivity)
    hRcX hCX (by gcongr)
  have hp0 := physicalFixedCost_nonneg D Rc C (4*R) 1 hRc hC (by positivity)
  have hpX := hp0.trans hpp
  have hNC0 := N.C_nonneg
  have hNR0 := N.Rc_nonneg
  unfold initializedPressureHessianCost fastHessianCost hessianEnvelope coordinateCost
  gcongr

end EulerPacketPhysicalCost

end
end

end
