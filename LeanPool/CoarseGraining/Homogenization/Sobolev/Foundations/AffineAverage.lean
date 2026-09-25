/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Affine Average -/

@[expose] public section

namespace Homogenization

namespace CorrectionFieldData

theorem integral_pairing_affine_eq_volume_mul_vecDot
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    (X : CorrectionFieldData U) (p q : Vec d) :
    ∫ x in U, vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume U).toReal * vecDot p q := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  exact
    X.integral_pairing_affine_eq_volume_mul_vecDot_of_integral_eq_zero p q
      (IsPotentialZeroTraceOn.integral_eq_zero X.isPotentialZeroTrace)
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
        X.isSolenoidalZeroNormalTrace)

theorem integral_potential_affine_eq_volume_smul
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (X : CorrectionFieldData U) (p : Vec d) :
    (fun i => ∫ x in U, (p + X.potential x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume U).toReal • p := by
  have hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0 :=
    IsPotentialZeroTraceOn.integral_eq_zero X.isPotentialZeroTrace
  ext i
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => p i) U := by
    simp [MeasureTheory.IntegrableOn]
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => X.potential x i) U :=
    integrableOn_coord_of_memVectorL2 (U := U) X.potential_memL2 i
  calc
    ∫ x in U, (p + X.potential x) i ∂MeasureTheory.volume =
        ∫ x in U, p i + X.potential x i ∂MeasureTheory.volume := by
          simp
    _ =
        ∫ x in U, (p i) ∂MeasureTheory.volume +
          ∫ x in U, X.potential x i ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hconstInt hpotInt]
    _ = ∫ x in U, (p i) ∂MeasureTheory.volume + 0 := by
      rw [show ∫ x in U, X.potential x i ∂MeasureTheory.volume = 0 by
        simpa using congrFun hpotZero i]
    _ = ∫ x in U, (p i) ∂MeasureTheory.volume := by
      simp
    _ = (MeasureTheory.volume U).toReal * p i := by
      rw [MeasureTheory.integral_const, smul_eq_mul]
      have hμ₁ :
          (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
        exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
      have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
      rw [hμ₁, hμ₂]

theorem integral_flux_affine_eq_volume_smul
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    (X : CorrectionFieldData U) (q : Vec d) :
    (fun i => ∫ x in U, (q + X.flux x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume U).toReal • q := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0 :=
    IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
      X.isSolenoidalZeroNormalTrace
  ext i
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => q i) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => X.flux x i) U :=
    integrableOn_coord_of_memVectorL2 (U := U) X.flux_memL2 i
  calc
    ∫ x in U, (q + X.flux x) i ∂MeasureTheory.volume =
        ∫ x in U, q i + X.flux x i ∂MeasureTheory.volume := by
          simp
    _ =
        ∫ x in U, (q i) ∂MeasureTheory.volume +
          ∫ x in U, X.flux x i ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hconstInt hfluxInt]
    _ = ∫ x in U, (q i) ∂MeasureTheory.volume + 0 := by
      rw [show ∫ x in U, X.flux x i ∂MeasureTheory.volume = 0 by
        simpa using congrFun hfluxZero i]
    _ = ∫ x in U, (q i) ∂MeasureTheory.volume := by
      simp
    _ = (MeasureTheory.volume U).toReal * q i := by
      rw [MeasureTheory.integral_const, smul_eq_mul]
      have hμ₁ :
          (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
        exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
      have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
      rw [hμ₁, hμ₂]

theorem average_potential_affine
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (X : CorrectionFieldData U) (p : Vec d) :
    (fun i => integralAverage U (fun x => (p + X.potential x) i)) = p := by
  have hint := X.integral_potential_affine_eq_volume_smul p
  ext i
  unfold integralAverage
  rw [show ∫ x in U, (p + X.potential x) i ∂MeasureTheory.volume =
      ((MeasureTheory.volume U).toReal • p) i by simpa using congrFun hint i]
  have hcancel :
      (MeasureTheory.volume U).toReal⁻¹ * ((MeasureTheory.volume U).toReal * p i) = p i := by
    field_simp [hvol]
  simpa using hcancel

theorem average_flux_affine
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (X : CorrectionFieldData U) (q : Vec d) :
    (fun i => integralAverage U (fun x => (q + X.flux x) i)) = q := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hint := X.integral_flux_affine_eq_volume_smul hU q
  ext i
  unfold integralAverage
  rw [show ∫ x in U, (q + X.flux x) i ∂MeasureTheory.volume =
      ((MeasureTheory.volume U).toReal • q) i by simpa using congrFun hint i]
  have hcancel :
      (MeasureTheory.volume U).toReal⁻¹ * ((MeasureTheory.volume U).toReal * q i) = q i := by
    field_simp [hvol]
  simpa using hcancel

theorem average_state_affine
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (X : CorrectionFieldData U) (P : BlockVec d) :
    ((fun i => integralAverage U (fun x => (P.1 + X.potential x) i)),
      (fun i => integralAverage U (fun x => (P.2 + X.flux x) i))) = P := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  apply Prod.ext
  · exact X.average_potential_affine hvol P.1
  · exact X.average_flux_affine hU hvol P.2

end CorrectionFieldData

end Homogenization
