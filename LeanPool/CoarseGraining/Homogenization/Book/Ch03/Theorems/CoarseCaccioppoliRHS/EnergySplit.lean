/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Setup

/-! # Energy Split -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Coarse Caccioppoli with RHS Energy Split

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: split forced boundary Caccioppoli energy into the homogeneous part,
zero-trace corrector part, and cross terms using the public coefficient
representative.

Downstream target: `CoarseCaccioppoliRHS/Prefactors.lean` and
`CoarseCaccioppoliRHS/FinalBounds.lean`.  This file should contain energy
identities and inequalities only.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- On subsets of the open cube, public localized energy can be evaluated using
the pointwise deterministic coefficient representative. -/
theorem localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet Q)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue V (a.coeffOn Q) u =
      volumeAverage V
        (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
  have hcoeffV :
      publicCoeffField Q a =ᵐ[volumeMeasureOn V] (a.coeffOn Q).toCoeffField :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hV
      (publicCoeffField_ae_eq_openCubeSet Q a)
  have henergy_ae :
      coefficientEnergyDensity (publicCoeffField Q a) u.grad
        =ᵐ[volumeMeasureOn V]
      coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad :=
    hcoeffV.mono fun y hy => by
      simp [coefficientEnergyDensity, hy]
  rw [localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity]
  exact (volumeAverage_eq_of_ae_eq henergy_ae).symm

/-- Coefficient-energy triangle inequality for a decomposition `F = G + H`
over an arbitrary measurable set. -/
theorem volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
    {d : ℕ} {V : Set (Vec d)} {A : CoeffField d} {lam Lam : ℝ}
    {F G H : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam V A)
    (hF : MemVectorL2 V F)
    (hG : MemVectorL2 V G)
    (hH : MemVectorL2 V H)
    (hFGH : F =ᵐ[volumeMeasureOn V] fun y => G y + H y) :
    volumeAverage V (coefficientEnergyDensity A F) ≤
      2 * volumeAverage V (coefficientEnergyDensity A G) +
        2 * volumeAverage V (coefficientEnergyDensity A H) := by
  let Hneg : Vec d → Vec d := (-1 : ℝ) • H
  have hHneg : MemVectorL2 V Hneg := by
    dsimp [Hneg]
    exact hH.const_smul (-1)
  have hF_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A F) V :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hF
  have hG_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A G) V :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hG
  have hHneg_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A Hneg) V :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hHneg
  have hmem :
      ∀ᵐ y ∂volumeMeasureOn V, y ∈ V :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
      (Filter.Eventually.of_forall fun _ hy => hy)
  have hpoint :
      ∀ᵐ y ∂volumeMeasureOn V,
        coefficientEnergyDensity A F y ≤
          2 * (coefficientEnergyDensity A G y +
            coefficientEnergyDensity A Hneg y) := by
    filter_upwards [hmem, hFGH] with y hy hsum
    have hleft :
        coefficientEnergyDensity A F y =
          coefficientEnergyDensity A (fun z => G z - Hneg z) y := by
      have hvec : F y = G y - Hneg y := by
        rw [hsum]
        simp [Hneg]
      unfold coefficientEnergyDensity
      rw [hvec]
    exact hleft.trans_le
      (coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
        hEll G Hneg y hy)
  have havg_raw :
      volumeAverage V (coefficientEnergyDensity A F) ≤
        volumeAverage V
          (fun y => 2 * (coefficientEnergyDensity A G y +
            coefficientEnergyDensity A Hneg y)) := by
    unfold volumeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    exact
      MeasureTheory.integral_mono_ae hF_int
        ((hG_int.add hHneg_int).const_mul (2 : ℝ)) hpoint
  have hsplit :
      volumeAverage V
          (fun y => 2 * (coefficientEnergyDensity A G y +
            coefficientEnergyDensity A Hneg y)) =
        2 * volumeAverage V (coefficientEnergyDensity A G) +
          2 * volumeAverage V (coefficientEnergyDensity A Hneg) := by
    unfold volumeAverage
    have hfun :
        (fun y => 2 * (coefficientEnergyDensity A G y +
            coefficientEnergyDensity A Hneg y)) =
          fun y => 2 * coefficientEnergyDensity A G y +
            2 * coefficientEnergyDensity A Hneg y := by
      funext y
      ring
    rw [hfun, MeasureTheory.integral_add (hG_int.const_mul (2 : ℝ))
      (hHneg_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  have hneg_avg :
      volumeAverage V (coefficientEnergyDensity A Hneg) =
        volumeAverage V (coefficientEnergyDensity A H) := by
    apply volumeAverage_eq_of_ae_eq
    exact Filter.Eventually.of_forall fun y => by
      unfold coefficientEnergyDensity
      simp [Hneg, matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
  calc
    volumeAverage V (coefficientEnergyDensity A F)
        ≤
      volumeAverage V
        (fun y => 2 * (coefficientEnergyDensity A G y +
          coefficientEnergyDensity A Hneg y)) := havg_raw
    _ =
      2 * volumeAverage V (coefficientEnergyDensity A G) +
        2 * volumeAverage V (coefficientEnergyDensity A Hneg) := hsplit
    _ =
      2 * volumeAverage V (coefficientEnergyDensity A G) +
        2 * volumeAverage V (coefficientEnergyDensity A H) := by
        rw [hneg_avg]

/-- A core average is controlled by the parent cube average with the
dimension-only volume ratio `18^d`. -/
theorem normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_cubeAverage
    {d : ℕ} (Q : TriadicCube d) {x : Vec d} {energy : Vec d → ℝ}
    (hx : x ∈ openCubeSet Q)
    (henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    normalizedSetAverage (caccioppoliCoreSet Q x) energy ≤
      (18 : ℝ) ^ d * cubeAverage Q energy := by
  have hcore_sub_cube_ae :
      caccioppoliCoreSet Q x ≤ᵐ[MeasureTheory.volume] cubeSet Q :=
    Filter.Eventually.of_forall fun y hy =>
      caccioppoliCoreSet_subset_cubeSet Q x hy
  have hnonneg_ae :
      0 ≤ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] energy := by
    change ∀ᵐ y ∂MeasureTheory.volume.restrict (cubeSet Q), 0 ≤ energy y
    rw [MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)]
    exact Filter.Eventually.of_forall henergy_nonneg
  have hraw :
      ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume ≤
        ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume :=
    MeasureTheory.setIntegral_mono_set henergy_int hnonneg_ae hcore_sub_cube_ae
  have hratio := caccioppoliCoreSet_volumeRatio_le_eighteen_pow Q hx
  have hcube_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  unfold normalizedSetAverage volumeAverage
  calc
    (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
        ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume ≤
      (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
        ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume := by
        exact mul_le_mul_of_nonneg_left hraw
          (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ =
      ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
          cubeVolume Q) *
        (cubeVolume Q)⁻¹ *
          ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume := by
        calc
          (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
              ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume =
            (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
              (1 * ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume) := by
              ring
          _ =
            (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
              ((cubeVolume Q * (cubeVolume Q)⁻¹) *
                ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume) := by
              rw [mul_inv_cancel₀ hvol_ne]
          _ =
            ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
                cubeVolume Q) *
              (cubeVolume Q)⁻¹ *
                ∫ y in cubeSet Q, energy y ∂MeasureTheory.volume := by
              ring
    _ =
      ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
          cubeVolume Q) *
        (cubeAverage Q energy) := by
        simp [cubeAverage]
        ring
    _ ≤
      (18 : ℝ) ^ d * cubeAverage Q energy :=
        mul_le_mul_of_nonneg_right hratio hcube_nonneg

/-- The zero-trace corrector's localized core energy is controlled by its
parent cube coefficient energy with only the geometric `18^d` loss. -/
theorem boundaryForcedCaccioppoliCorrector_coreEnergy_le_eighteen_pow_mul_parentEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hx : x ∈ openCubeSet Q) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function ≤
      (18 : ℝ) ^ d *
        cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun y => ρ.toH10.toH1Function.grad y)) := by
  let energy : Vec d → ℝ :=
    coefficientEnergyDensity (publicCoeffField Q a)
      (fun y => ρ.toH10.toH1Function.grad y)
  have hcore_open : caccioppoliCoreSet Q x ⊆ openCubeSet Q := fun y hy => hy.1
  have henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y :=
    coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      (fun y => ρ.toH10.toH1Function.grad y)
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      ρ.toH10.toH1Function.grad_memVectorL2
  have hcore :
      normalizedSetAverage (caccioppoliCoreSet Q x) energy ≤
        (18 : ℝ) ^ d * cubeAverage Q energy :=
    normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_cubeAverage
      Q hx henergy_nonneg henergy_int
  have henergy_core :
      localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function =
        normalizedSetAverage (caccioppoliCoreSet Q x) energy := by
    simpa [energy, normalizedSetAverage] using
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := Q) (a := a) hcore_open
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function
  simpa [energy, henergy_core] using hcore

/-- The public zero-Dirichlet RHS is nonnegative under the force regularity
hypothesis. -/
theorem zeroDirichletEnergyWithRHSRHS_nonneg
    {d : ℕ} [NeZero d] {C : ℝ} (hC_nonneg : 0 ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d}
    (ht : 0 < t) (hg : ForceBesovRegularity Q (2 * t) g) :
    0 ≤ zeroDirichletEnergyWithRHSRHS C Q a t g := by
  unfold zeroDirichletEnergyWithRHSRHS poincareLowerEllipticityFactor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hC_nonneg (Real.rpow_nonneg ht.le _))
      (Real.rpow_nonneg
        (Ch02.lambdaSq_finite_nonneg Q a ht
          (by norm_num : (1 : ℝ) ≤ 2)) _))
    (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (Q := Q) (s := 2 * t) (g := g) hg)

/-- Squared form of the zero-trace corrector energy estimate, tuned to the
`t`-notation used by the boundary Caccioppoli RHS theorem. -/
theorem zeroTraceDirichletCorrectorData_parentEnergy_le_zeroDirichletEnergyWithRHSRHS_sq_publicCoeffField
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hg : ForceBesovRegularity Q (2 * t) g) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
      (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g) ^ 2 := by
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  let Z : ℝ := zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  have hZ_nonneg : 0 ≤ Z := by
    dsimp [Z]
    exact zeroDirichletEnergyWithRHSRHS_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le d) hC_nonneg) ht hg
  have hs : 0 < 2 * t := by nlinarith
  have hs_lt : 2 * t < 1 := by nlinarith
  have hs_half : 2 * t / 2 = t := by ring
  have hsqrt_le :
      Real.sqrt E ≤ Z := by
    dsimp [E, Z]
    simpa [hs_half] using
      zeroTraceDirichletCorrectorData_energyNorm_le_zeroDirichletEnergyWithRHSRHS_half_publicCoeffField
        (C := C) hC_nonneg hC_zero
        (Q := Q) (a := a) (s := 2 * t) (g := g) ρ hs hs_lt hg
  have hsquare : (Real.sqrt E) ^ 2 ≤ Z ^ 2 := by
    nlinarith [hsqrt_le, Real.sqrt_nonneg E, hZ_nonneg,
      sq_nonneg (Z - Real.sqrt E)]
  calc
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => ρ.toH10.toH1Function.grad x))
        = E := rfl
    _ = (Real.sqrt E) ^ 2 := (Real.sq_sqrt hE_nonneg).symm
    _ ≤ Z ^ 2 := hsquare
    _ = (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g) ^ 2 := rfl

/-- The localized corrector core is controlled directly by the square of the
public zero-Dirichlet RHS, with only the geometric `18^d` loss. -/
theorem boundaryForcedCaccioppoliCorrector_coreEnergy_le_eighteen_pow_mul_zeroDirichletEnergyWithRHSRHS_sq
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {x : Vec d} {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hx : x ∈ openCubeSet Q)
    (hg : ForceBesovRegularity Q (2 * t) g) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function ≤
      (18 : ℝ) ^ d *
        (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g) ^ 2 := by
  have hcore :=
    boundaryForcedCaccioppoliCorrector_coreEnergy_le_eighteen_pow_mul_parentEnergy
      (Q := Q) (a := a) (x := x) (g := g) ρ hx
  have hparent :=
    zeroTraceDirichletCorrectorData_parentEnergy_le_zeroDirichletEnergyWithRHSRHS_sq_publicCoeffField
      (C := C) hC_nonneg hC_zero
      (Q := Q) (a := a) (t := t) (g := g) ρ ht ht_lt hg
  have hgeom_nonneg : 0 ≤ (18 : ℝ) ^ d := by positivity
  exact hcore.trans (mul_le_mul_of_nonneg_left hparent hgeom_nonneg)

/-- Localized core-energy split for the manuscript decomposition `u = w + ρ`.
-/
theorem boundaryForcedCaccioppoliCoreEnergy_le_two_mul_remainder_add_corrector
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    boundaryForcedCaccioppoliCoreEnergy u ≤
      2 * boundaryCaccioppoliCoreEnergy
        (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) +
      2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
        (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ).toH1Function := by
  let V : Set (Vec d) := caccioppoliCoreSet Q x
  let wDatum : BoundaryCaccioppoliDatum Q a x :=
    boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem
  let ρOpen : H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ
  have hV_open : V ⊆ openCubeSet Q := fun y hy => hy.1
  have hV_cube : V ⊆ cubeSet Q :=
    (fun y hy => openCubeSet_subset_cubeSet Q (hV_open hy))
  have hmono_open :
      volumeMeasureOn V ≤ volumeMeasureOn (openCubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hV_open
  have hmono_cube :
      volumeMeasureOn V ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hV_cube
  have hu_mem : MemVectorL2 V u.toH1.grad := by
    exact u.toH1.grad_memVectorL2.mono_measure hmono_open
  have hw_mem : MemVectorL2 V wDatum.toH1.grad := by
    exact wDatum.toH1.grad_memVectorL2.mono_measure hmono_open
  have hρ_mem : MemVectorL2 V ρOpen.toH1Function.grad := by
    simpa [ρOpen] using
      ρ.toH10.toH1Function.grad_memVectorL2.mono_measure hmono_cube
  have hsplit :
      u.toH1.grad =ᵐ[volumeMeasureOn V]
        fun y => wDatum.toH1.grad y + ρOpen.toH1Function.grad y := by
    exact Filter.Eventually.of_forall fun y => by
      simp only [wDatum, ρOpen, boundaryForcedCaccioppoliRemainderDatum_toH1,
        boundaryForcedCaccioppoliRemainderOpenH1_grad,
        boundaryForcedCaccioppoliCorrectorOpenH10_grad]
      abel
  have htriangle :
      volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad) ≤
        2 * volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) wDatum.toH1.grad) +
        2 * volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) ρOpen.toH1Function.grad) :=
    volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
      (V := V) (A := publicCoeffField Q a)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      ((publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
        (measurableSet_caccioppoliCoreSet Q x) hV_cube)
      hu_mem hw_mem hρ_mem hsplit
  have henergy_u :
      boundaryForcedCaccioppoliCoreEnergy u =
        volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad) := by
    simpa [boundaryForcedCaccioppoliCoreEnergy, V] using
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := Q) (a := a) hV_open u.toH1
  have henergy_w :
      boundaryCaccioppoliCoreEnergy wDatum =
        volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) wDatum.toH1.grad) := by
    simpa [boundaryCaccioppoliCoreEnergy, V, wDatum] using
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := Q) (a := a) hV_open wDatum.toH1
  have henergy_ρ :
      localizedCoeffEnergyValue V (a.coeffOn Q) ρOpen.toH1Function =
        volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) ρOpen.toH1Function.grad) := by
    simpa [V, ρOpen] using
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := Q) (a := a) hV_open ρOpen.toH1Function
  calc
    boundaryForcedCaccioppoliCoreEnergy u
        =
      volumeAverage V
        (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad) := henergy_u
    _ ≤
      2 * volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) wDatum.toH1.grad) +
        2 * volumeAverage V
          (coefficientEnergyDensity (publicCoeffField Q a) ρOpen.toH1Function.grad) :=
        htriangle
    _ =
      2 * boundaryCaccioppoliCoreEnergy wDatum +
        2 * localizedCoeffEnergyValue V (a.coeffOn Q) ρOpen.toH1Function := by
        rw [henergy_w, henergy_ρ]

/-- Parent `L²` split for the manuscript decomposition `w = u - ρ`. -/
theorem boundaryForcedCaccioppoliRemainder_parentL2_le_two_mul_forced_add_corrector
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    boundaryCaccioppoliParentL2Sq
        (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
      2 * boundaryForcedCaccioppoliParentL2Sq u +
      2 * normalizedL2SqOnSet (openCubeSet Q)
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function.toFun := by
  let U : Set (Vec d) := openCubeSet Q
  let wDatum : BoundaryCaccioppoliDatum Q a x :=
    boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem
  let ρOpen : H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ
  have hw_int :
      MeasureTheory.IntegrableOn (fun y => wDatum.toH1.toFun y ^ 2) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, U, wDatum,
      Ch02.cubeDomain_coe, Real.norm_eq_abs, sq_abs] using
      wDatum.toH1.memL2.integrable_sq
  have hu_int :
      MeasureTheory.IntegrableOn (fun y => u.toH1.toFun y ^ 2) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, U,
      Ch02.cubeDomain_coe, Real.norm_eq_abs, sq_abs] using
      u.toH1.memL2.integrable_sq
  have hρ_int :
      MeasureTheory.IntegrableOn (fun y => ρOpen.toH1Function.toFun y ^ 2) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, U, ρOpen,
      Ch02.cubeDomain_coe, Real.norm_eq_abs, sq_abs] using
      ρOpen.toH1Function.memL2.integrable_sq
  have hpoint :
      ∀ᵐ y ∂volumeMeasureOn U,
        wDatum.toH1.toFun y ^ 2 ≤
          2 * u.toH1.toFun y ^ 2 + 2 * ρOpen.toH1Function.toFun y ^ 2 := by
    exact Filter.Eventually.of_forall fun y => by
      have hsq :
          (u.toH1.toFun y - ρOpen.toH1Function.toFun y) ^ 2 ≤
            2 * u.toH1.toFun y ^ 2 + 2 * ρOpen.toH1Function.toFun y ^ 2 := by
        nlinarith [sq_nonneg (u.toH1.toFun y + ρOpen.toH1Function.toFun y)]
      simpa only [wDatum, ρOpen, boundaryForcedCaccioppoliRemainderDatum_toH1,
        boundaryForcedCaccioppoliRemainderOpenH1_toFun,
        boundaryForcedCaccioppoliCorrectorOpenH10_toFun] using hsq
  have havg_raw :
      volumeAverage U (fun y => wDatum.toH1.toFun y ^ 2) ≤
        volumeAverage U
          (fun y => 2 * u.toH1.toFun y ^ 2 +
            2 * ρOpen.toH1Function.toFun y ^ 2) := by
    unfold volumeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    exact
      MeasureTheory.integral_mono_ae hw_int
        ((hu_int.const_mul (2 : ℝ)).add (hρ_int.const_mul (2 : ℝ))) hpoint
  have hsplit :
      volumeAverage U
          (fun y => 2 * u.toH1.toFun y ^ 2 +
            2 * ρOpen.toH1Function.toFun y ^ 2) =
        2 * volumeAverage U (fun y => u.toH1.toFun y ^ 2) +
          2 * volumeAverage U (fun y => ρOpen.toH1Function.toFun y ^ 2) := by
    unfold volumeAverage
    rw [MeasureTheory.integral_add (hu_int.const_mul (2 : ℝ))
      (hρ_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  calc
    boundaryCaccioppoliParentL2Sq wDatum
        =
      volumeAverage U (fun y => wDatum.toH1.toFun y ^ 2) := by
        rfl
    _ ≤
      volumeAverage U
        (fun y => 2 * u.toH1.toFun y ^ 2 +
          2 * ρOpen.toH1Function.toFun y ^ 2) := havg_raw
    _ =
      2 * volumeAverage U (fun y => u.toH1.toFun y ^ 2) +
        2 * volumeAverage U (fun y => ρOpen.toH1Function.toFun y ^ 2) := hsplit
    _ =
      2 * boundaryForcedCaccioppoliParentL2Sq u +
        2 * normalizedL2SqOnSet U ρOpen.toH1Function.toFun := by
        rfl

/-- Apply the proved homogeneous boundary Caccioppoli theorem to the harmonic
remainder produced from a forced datum. -/
theorem boundaryForcedCaccioppoliRemainder_coreEnergy_le_homogeneousRHS
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hx : x ∈ openCubeSet Q) :
    ∃ C : ℝ, 0 < C ∧
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) := by
  rcases (coarseCaccioppoliTheory d).exists_constant with
    ⟨C, hC_pos, hboundary, _hinterior⟩
  exact
    ⟨C, hC_pos,
      hboundary
        (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem)
        hs ht hst hx⟩


end

end Ch03
end Book
end Homogenization
