/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeBridge

/-! # Potential Solenoidal L2Origin Cube Bridge -/

@[expose] public section

namespace Homogenization

noncomputable section

namespace CorrectionFieldData

theorem volume_cubeSet_originCube_lt_top_l2 {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (cubeSet (originCube d n)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hzero : (MeasureTheory.volume (cubeSet (originCube d n))).toReal = 0 := by
    simp [htop]
  rw [volume_cubeSet_toReal] at hzero
  exact (ne_of_gt (cubeVolume_pos (originCube d n))) hzero

theorem volume_openCubeSet_originCube_lt_top_l2 {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (openCubeSet (originCube d n)) < ⊤ := by
  exact lt_of_le_of_lt
    (MeasureTheory.measure_mono (openCubeSet_subset_cubeSet (originCube d n)))
    (volume_cubeSet_originCube_lt_top_l2 (d := d) n)

instance instIsFiniteMeasureVolumeMeasureOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ} :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_originCube_lt_top_l2 (d := d) n⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)
  infer_instance

instance instIsFiniteMeasureVolumeMeasureOnCubeSetOriginCube {d : ℕ} {n : ℤ} :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet (originCube d n))) := by
  let U : Set (Vec d) := cubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_cubeSet_originCube_lt_top_l2 (d := d) n⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)
  infer_instance

/--
On an open centered cube, the affine pairing attached to a zero-trace /
zero-normal-trace `L²` correction is integrable.
-/
theorem integrableOn_pairing_affine_openCubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (openCubeSet (originCube d n))) (p q : Vec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (p + X.potential x) (q + X.flux x))
      (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hsum :
      MeasureTheory.IntegrableOn
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum123.integrable.add hpairInt.integrable
  have hEq :
      (fun x => vecDot (p + X.potential x) (q + X.flux x)) =
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) := by
    funext x
    simp [vecDot_add_left, vecDot_add_right, add_assoc]
    ring
  rw [hEq]
  exact hsum

/--
On an open centered cube, the affine perturbation of a zero-trace / zero-normal-trace
`L²` correction has pairing integral equal to the cube volume times the constant pairing.
-/
theorem integral_pairing_affine_openCubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (openCubeSet (originCube d n))) (p q : Vec d) :
    ∫ x in openCubeSet (originCube d n),
        vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal * vecDot p q := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  have : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_originCube_lt_top_l2 (d := d) n⟩
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := inferInstance
  have hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (f := X.potential) X.isPotentialZeroTrace)
  have hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (g := X.flux) X.isSolenoidalZeroNormalTrace)
  rcases X.isPotentialZeroTrace with ⟨u, hu⟩
  have hpairZero :
      ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume = 0 := by
    simpa [U, hu, vecDot_comm] using X.isSolenoidalZeroNormalTrace u.toH1Function
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hfluxTerm :
      ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume = 0 :=
    integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) p X.flux_memL2 hfluxZero
  have hpotTerm :
      ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume = 0 := by
    rw [show (fun x => vecDot (X.potential x) q) = fun x => vecDot q (X.potential x) by
      funext x
      exact vecDot_comm _ _]
    exact integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) q X.potential_memL2 hpotZero
  calc
    ∫ x in U, vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
        ∫ x in U,
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
          congr 1
          funext x
          simp [vecDot_add_left, vecDot_add_right, add_assoc]
          ring
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum123 hpairInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume := by
            rw [hpairZero, add_zero]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum12 hpotInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [hpotTerm, add_zero]
    _ =
        ∫ x in U, (vecDot p q) ∂MeasureTheory.volume +
          ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hconstInt hfluxInt]
    _ = (MeasureTheory.volume U).toReal * vecDot p q := by
      rw [hfluxTerm, add_zero]
      rw [MeasureTheory.integral_const, smul_eq_mul]
      have hμ₁ :
          (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
        exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
      have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
      rw [hμ₁, hμ₂]

/--
On an open centered cube, the affine potential field `p + correction` has
componentwise integral equal to the cube volume times `p`.
-/
theorem integral_potential_affine_openCubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (openCubeSet (originCube d n))) (p : Vec d) :
    (fun i => ∫ x in openCubeSet (originCube d n), (p + X.potential x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal • p := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  have hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (f := X.potential) X.isPotentialZeroTrace)
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

/--
On an open centered cube, the affine flux field `q + correction` has
componentwise integral equal to the cube volume times `q`.
-/
theorem integral_flux_affine_openCubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (openCubeSet (originCube d n))) (q : Vec d) :
    (fun i => ∫ x in openCubeSet (originCube d n), (q + X.flux x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal • q := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  have hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (g := X.flux) X.isSolenoidalZeroNormalTrace)
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

/--
On the half-open centered cube, the affine pairing attached to a zero-trace /
zero-normal-trace `L²` correction is integrable.
-/
theorem integrableOn_pairing_affine_cubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (cubeSet (originCube d n))) (p q : Vec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (p + X.potential x) (q + X.flux x))
      (cubeSet (originCube d n)) := by
  let U : Set (Vec d) := cubeSet (originCube d n)
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hsum :
      MeasureTheory.IntegrableOn
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum123.integrable.add hpairInt.integrable
  have hEq :
      (fun x => vecDot (p + X.potential x) (q + X.flux x)) =
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) := by
    funext x
    simp [vecDot_add_left, vecDot_add_right, add_assoc]
    ring
  rw [hEq]
  exact hsum

/--
On the half-open centered cube, the affine perturbation of a zero-trace / zero-normal-trace
`L²` correction has pairing integral equal to the cube volume times the constant pairing.
-/
theorem integral_pairing_affine_cubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (cubeSet (originCube d n))) (p q : Vec d) :
    ∫ x in cubeSet (originCube d n),
        vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal * vecDot p q := by
  let U : Set (Vec d) := cubeSet (originCube d n)
  have : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_cubeSet_originCube_lt_top_l2 (d := d) n⟩
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := inferInstance
  have hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (f := X.potential) X.isPotentialZeroTrace)
  have hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (g := X.flux) X.isSolenoidalZeroNormalTrace)
  rcases X.isPotentialZeroTrace with ⟨u, hu⟩
  have hpairZero :
      ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume = 0 := by
    simpa [U, hu, vecDot_comm] using X.isSolenoidalZeroNormalTrace u.toH1Function
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hfluxTerm :
      ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume = 0 :=
    integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) p X.flux_memL2 hfluxZero
  have hpotTerm :
      ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume = 0 := by
    rw [show (fun x => vecDot (X.potential x) q) = fun x => vecDot q (X.potential x) by
      funext x
      exact vecDot_comm _ _]
    exact integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) q X.potential_memL2 hpotZero
  calc
    ∫ x in U, vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
        ∫ x in U,
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
          congr 1
          funext x
          simp [vecDot_add_left, vecDot_add_right, add_assoc]
          ring
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum123 hpairInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume := by
            rw [hpairZero, add_zero]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum12 hpotInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [hpotTerm, add_zero]
    _ =
        ∫ x in U, (vecDot p q) ∂MeasureTheory.volume +
          ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hconstInt hfluxInt]
    _ = (MeasureTheory.volume U).toReal * vecDot p q := by
      rw [hfluxTerm, add_zero]
      rw [MeasureTheory.integral_const, smul_eq_mul]
      have hμ₁ :
          (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
        exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
      have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
      rw [hμ₁, hμ₂]

/--
On the half-open centered cube, the affine potential field `p + correction` has
componentwise integral equal to the cube volume times `p`.
-/
theorem integral_potential_affine_cubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (cubeSet (originCube d n))) (p : Vec d) :
    (fun i => ∫ x in cubeSet (originCube d n), (p + X.potential x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal • p := by
  let U : Set (Vec d) := cubeSet (originCube d n)
  have hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (f := X.potential) X.isPotentialZeroTrace)
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

/--
On the half-open centered cube, the affine flux field `q + correction` has
componentwise integral equal to the cube volume times `q`.
-/
theorem integral_flux_affine_cubeSet_originCube {d : ℕ} [NeZero d] {n : ℤ}
    (X : CorrectionFieldData (cubeSet (originCube d n))) (q : Vec d) :
    (fun i => ∫ x in cubeSet (originCube d n), (q + X.flux x) i ∂MeasureTheory.volume) =
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal • q := by
  let U : Set (Vec d) := cubeSet (originCube d n)
  have hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0 := by
    simpa [U] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (g := X.flux) X.isSolenoidalZeroNormalTrace)
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

end CorrectionFieldData

end

end Homogenization
