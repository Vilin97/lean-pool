/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Measurability
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CubeMinimizer
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.QuadraticStability.Integral
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# Per-phase stability of the corridor observable

Statement of `p.phase.comparison`'s stability estimate `e.phase.comparison.stability`
in the discrete-grid setting.  With `U := cubeSet (originCube d m)`,
`S := corridorSet ℓ σ`, and `Z` the minimizer for `(a, P)`
(`exists_cubeBlockMinimizer`, which supplies `Mu U P a = blockEnergyAverage U a Z`):

* `F := P·𝐀(U; a)P = 2·Mu U P a`, and `2·Mu U P a = (vol U)⁻¹ ∫_U Z·(blockCoeffField a)Z`
  (`coarseBlockMatrix_quadratic_eq_energyIntegral`); the sharp constant is
  `24Θ = (vol U)⁻¹·6·(4Θ)`.  We state the (weaker, still true) `48Θ`, valid
  because the corridor energy integrand is `≥ 0`
  (`blockMatrixOfCoeff_quadratic_nonneg`).
* B′3 `abs_setIntegral_energy_sub_le` with `B := blockCoeffField a`,
  `Bt := blockCoeffField (corridorField ℓ σ a)`, `S := corridorSet ℓ σ ∩ U`,
  minimizers `Z` (for `a`), `Zσ` (for `corridorField ℓ σ a`, elliptic via
  `corridorField_isEllipticMatrix`).

The core B′3 assembly is packaged as `abs_phaseObservable_sub_le_of_minimizer`
(taking the minimizer `Z` for `a` as input); `abs_phaseObservable_sub_le`
(M2) is the existential wrapper.  The `Z`-as-input form is what the grid-averaging
step M3 needs, since a single `a`-minimizer serves every phase `σ`.
-/

open Homogenization
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## Field-level ellipticity transport through the corridor -/

/-- The corridor self-map preserves everywhere-`(1, Θ)`-ellipticity on `U`: the
pointwise ellipticity is `corridorField_isEllipticMatrix`, and the entrywise
measurability of the `U`-truncated modified field is the corridor-gated
piecewise of the constant `(1 : Mat d)` and the original truncated field. -/
theorem isEllipticFieldOn_corridorField {Θ : ℝ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (hΘ : 1 ≤ Θ) {ℓ : ℝ} {σ : Vec d} {a : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ U a) :
    IsEllipticFieldOn 1 Θ U (corridorField ℓ σ a) := by
  classical
  refine ⟨?_, fun x hx => corridorField_isEllipticMatrix hΘ (hEll.2 x hx)⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have hcomp : Measurable (fun x => if x ∈ U then a x i j else 0) := by
    have := (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i)) j
    simpa using this
  have hind : Measurable (fun x : Vec d => if x ∈ U then (1 : Mat d) i j else 0) :=
    Measurable.ite hU measurable_const measurable_const
  have heq : (fun x => if x ∈ U then corridorField ℓ σ a x i j else 0)
      = fun x => if x ∈ corridorSet ℓ σ then (if x ∈ U then (1 : Mat d) i j else 0)
                                          else (if x ∈ U then a x i j else 0) := by
    funext x
    by_cases hxS : x ∈ corridorSet ℓ σ
    · rw [if_pos hxS, corridorField_apply_of_mem hxS]
    · rw [if_neg hxS, corridorField_apply_of_not_mem hxS]
  rw [heq]
  exact Measurable.ite (measurableSet_corridorSet ℓ σ) hind hcomp

/-! ## The `Mu`-quadratic as a normalized energy integral -/

/-- `P·𝐀(U; a)P = (vol U)⁻¹ ∫_U Z·(blockCoeffField a)Z` for any minimizer `Z`
of `(a, P)` on the half-open triadic cube.  This is `Mu = ½ P·𝐀 P` combined with
`Mu = blockEnergyAverage`, the `½` cancelling the density's `½`. -/
theorem coarseBlockMatrix_quadratic_eq_energyIntegral [NeZero d] {Θ : ℝ} {m : ℤ}
    {a : CoeffField d} (P : BlockVec d)
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a)
    {Z : BlockState d}
    (hZeng : Mu (cubeSet (originCube d m)) P a
      = blockEnergyAverage (cubeSet (originCube d m)) a Z) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P)
      = (volume (cubeSet (originCube d m))).toReal⁻¹ *
          ∫ x in cubeSet (originCube d m),
            blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) := by
  set U := cubeSet (originCube d m) with hUdef
  have h1 : Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
    mu_eq_half_coarseBlockMatrix_cube hEll P
  have hg : (∫ x in U, blockEnergyDensity a Z x)
      = (1 / 2 : ℝ) *
          ∫ x in U, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) := by
    rw [show (∫ x in U, blockEnergyDensity a Z x)
          = ∫ x in U, (1 / 2 : ℝ) *
              blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) from rfl]
    exact integral_const_mul _ _
  have e1 : blockEnergyAverage U a Z
      = (volume U).toReal⁻¹ * ((1 / 2 : ℝ) *
          ∫ x in U, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x))) := by
    unfold blockEnergyAverage volumeAverage; rw [hg]
  have e2 : (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P)
      = (1 / 2 : ℝ) * ((volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x))) := by
    rw [← h1, hZeng, e1]; ring
  exact mul_left_cancel₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) e2

/-! ## M2 core: the B′3 assembly with the minimizer as input -/

/-- **M2 core.**  Given the minimizer `Z` for `(a, P)` (its admissibility,
response-space membership and energy-realizing identity), the corridor-phase
comparison bound holds with the corridor energy of that specific `Z`.  This is
the B′3 assembly; `abs_phaseObservable_sub_le` obtains `Z` and calls this. -/
theorem abs_phaseObservable_sub_le_of_minimizer [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {a : CoeffField d} (P : BlockVec d)
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a)
    {Z : BlockState d}
    (hZadm : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZresp : BlockResponseSpace a (cubeSet (originCube d m)) Z)
    (hZeng : Mu (cubeSet (originCube d m)) P a
      = blockEnergyAverage (cubeSet (originCube d m)) a Z) :
    |blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a)) P) -
        blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P)| ≤
      48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
        ∫ x in corridorSet ℓ σ ∩ cubeSet (originCube d m),
          blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) := by
  classical
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    rw [hUdef]; infer_instance
  have hΘpos : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  set aσ := corridorField ℓ σ a with haσdef
  have hEllσ : IsEllipticFieldOn 1 Θ U aσ := isEllipticFieldOn_corridorField hU hΘ hEll
  obtain ⟨Zσ, hZσadm, hZσeng, hZσresp⟩ := exists_cubeBlockMinimizer hEllσ P
  -- energy-integral forms of both `Mu`-quadratics
  have hFa : blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P)
      = (volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEll hZeng
  have hFσ : blockVecDot P (blockMatVecMul (coarseBlockMatrix U aσ) P)
      = (volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (Zσ.eval x) (blockMatVecMul (blockCoeffField aσ x) (Zσ.eval x)) :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEllσ hZσeng
  -- B′3 data
  set S : Set (Vec d) := corridorSet ℓ σ ∩ U with hSdef
  have hS : MeasurableSet S := (measurableSet_corridorSet ℓ σ).inter hU
  have hSU : S ⊆ U := Set.inter_subset_right
  have hK : (1 : ℝ) ≤ 4 * Θ := by linarith
  have hZbl : MemBlockL2 U Z.eval := hZadm.memBlockL2_eval
  have hZσbl : MemBlockL2 U Zσ.eval := hZσadm.memBlockL2_eval
  set W : BlockState d :=
    { potential := fun x => Zσ.potential x - Z.potential x
      flux := fun x => Zσ.flux x - Z.flux x } with hWdef
  have hWeval : ∀ x, W.eval x = Zσ.eval x - Z.eval x := fun x => rfl
  have hWbl : MemBlockL2 U W.eval := hZσbl.sub hZbl
  have hae : ∀ᵐ x ∂(volume.restrict U),
      IsSymmetricBlockMat (blockCoeffField a x) ∧ IsSymmetricBlockMat (blockCoeffField aσ x) ∧
      (∀ V : BlockVec d, 0 ≤ blockVecDot V (blockMatVecMul (blockCoeffField a x) V)) ∧
      (∀ V : BlockVec d, 0 ≤ blockVecDot V (blockMatVecMul (blockCoeffField aσ x) V)) ∧
      BlockMatLoewnerLE (blockCoeffField aσ x) ((4 * Θ) • blockCoeffField a x) ∧
      BlockMatLoewnerLE (blockCoeffField a x) ((4 * Θ) • blockCoeffField aσ x) := by
    refine (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have hAx : IsEllipticMatrix 1 Θ (a x) := hEll.2 x hx
    have hAσx : IsEllipticMatrix 1 Θ (aσ x) := corridorField_isEllipticMatrix hΘ hAx
    exact ⟨isSymmetricBlockMat_blockMatrixOfCoeff (a x),
      isSymmetricBlockMat_blockMatrixOfCoeff (aσ x),
      fun V => blockMatrixOfCoeff_quadratic_nonneg hAx V,
      fun V => blockMatrixOfCoeff_quadratic_nonneg hAσx V,
      blockMatrixOfCoeff_blockMatLoewnerLE_smul_of_isThetaElliptic hAx hAσx,
      blockMatrixOfCoeff_blockMatLoewnerLE_smul_of_isThetaElliptic hAσx hAx⟩
  have hagree : ∀ᵐ x ∂(volume.restrict (U \ S)),
      blockCoeffField a x = blockCoeffField aσ x := by
    refine (ae_restrict_iff' (hU.diff hS)).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have hxnc : x ∉ corridorSet ℓ σ := fun hc => hx.2 ⟨hc, hx.1⟩
    have haσx : aσ x = a x := by rw [haσdef]; exact corridorField_apply_of_not_mem hxnc
    unfold blockCoeffField; rw [haσx]
  have hIntBZZ : IntegrableOn
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x))) U := by
    simpa [blockPairingIntegrand] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (X := Z) (Y := Z) hZbl hZbl hEll
  have hIntBtZZ : IntegrableOn
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField aσ x) (Z.eval x))) U := by
    simpa [blockPairingIntegrand] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (X := Z) (Y := Z) hZbl hZbl hEllσ
  have hIntBtYY : IntegrableOn
      (fun x => blockVecDot (Zσ.eval x - Z.eval x)
        (blockMatVecMul (blockCoeffField aσ x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := W) (Y := W) hWbl hWbl hEllσ
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hIntBtZY : IntegrableOn
      (fun x => blockVecDot (Z.eval x)
        (blockMatVecMul (blockCoeffField aσ x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := Z) (Y := W) hZbl hWbl hEllσ
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hIntBZY : IntegrableOn
      (fun x => blockVecDot (Z.eval x)
        (blockMatVecMul (blockCoeffField a x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := Z) (Y := W) hZbl hWbl hEll
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hEulerB : ∫ x in U,
      blockVecDot (Zσ.eval x - Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) = 0 :=
    cubeBlockMinimizer_euler_orthogonality_sub hZresp hZσadm hZadm
  have hEulerBt : ∫ x in U,
      blockVecDot (Zσ.eval x - Z.eval x) (blockMatVecMul (blockCoeffField aσ x) (Zσ.eval x)) = 0 :=
    cubeBlockMinimizer_euler_orthogonality_sub hZσresp hZσadm hZadm
  have hB3 := abs_setIntegral_energy_sub_le (U := U) (S := S)
    (B := blockCoeffField a) (Bt := blockCoeffField aσ)
    (Z := Z.eval) (Zt := Zσ.eval) (K := 4 * Θ)
    hU hS hSU hK hae hagree
    hIntBZZ hIntBtZZ hIntBtYY hIntBtZY hIntBZY hEulerB hEulerBt
  rw [hFσ, hFa]
  have hc0 : (0 : ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hES0 : (0 : ℝ) ≤ ∫ x in S,
      blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) :=
    setIntegral_nonneg hS
      (fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x (hSU hx)) (Z.eval x))
  set c := (volume U).toReal⁻¹ with hcdef
  set Iσ := ∫ x in U,
    blockVecDot (Zσ.eval x) (blockMatVecMul (blockCoeffField aσ x) (Zσ.eval x)) with hIσdef
  set I := ∫ x in U,
    blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) with hIdef
  set ES := ∫ x in S,
    blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) with hESdef
  have hprod : (0 : ℝ) ≤ c * Θ * ES := mul_nonneg (mul_nonneg hc0 hΘpos.le) hES0
  calc |c * Iσ - c * I|
      = c * |Iσ - I| := by rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    _ ≤ c * (6 * (4 * Θ) * ES) := mul_le_mul_of_nonneg_left hB3 hc0
    _ ≤ 48 * Θ * c * ES := by nlinarith [hprod]

/-- **M2 (per-phase stability).**  For a fixed grid phase `σ` and a coefficient
`a` that is `(1, Θ)`-elliptic on `U := cubeSet (originCube d m)`, the coarse
observable moves by at most a normalized corridor energy of the minimizer
`Z` for `(a, P)`. -/
theorem abs_phaseObservable_sub_le [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {a : CoeffField d} (P : BlockVec d)
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) :
    ∃ Z : BlockState d,
      IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
        BlockResponseSpace a (cubeSet (originCube d m)) Z ∧
        |blockVecDot P
              (blockMatVecMul
                (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a)) P) -
            blockVecDot P
              (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P)| ≤
          48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
            ∫ x in corridorSet ℓ σ ∩ cubeSet (originCube d m),
              blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) := by
  obtain ⟨Z, hZadm, hZeng, hZresp⟩ := exists_cubeBlockMinimizer hEll P
  exact ⟨Z, hZadm, hZresp,
    abs_phaseObservable_sub_le_of_minimizer hΘ P hEll hZadm hZresp hZeng⟩

end Homogenization
