/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Stability
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Recombination

/-!
# One-core resampling stability

The deterministic sensitivity estimate `e.fixed.phase.sensitivity` behind the
Efron–Stein step of Proposition 4.3.  Resampling the coefficient field on a
single core `coreBox ℓ σ k` moves the fixed-phase observable
`F_σ(b) = P · 𝐀(U; b_σ) P` by at most a normalized energy over that core:

`|F_σ(b) − F_σ(b')| ≤ 48 Θ (vol U)⁻¹ ∫_{coreBox ℓ σ k ∩ U} Z · 𝐀_σ(b) Z`,

where `Z` is a minimizer for `corridorField ℓ σ b` and `b, b'` are two fields,
`(1, Θ)`-elliptic on `U`, agreeing off the core.

The proof is exactly the B′3 assembly of
`abs_phaseObservable_sub_le_of_minimizer`, with the corridor
comparison replaced by the resampling comparison: instead of comparing `a` with
`corridorField ℓ σ a` (agreeing off `corridorSet`), we compare
`corridorField ℓ σ b` with `corridorField ℓ σ b'` (agreeing off `coreBox ℓ σ k`).
We factor out the corridor-independent core as the general lemma
`abs_coarseObservable_sub_le_of_minimizer`.
-/

open Homogenization
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## Measurability of a core box -/

/-- Each core box is measurable (a finite product of closed intervals). -/
theorem measurableSet_coreBox (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    MeasurableSet (coreBox ℓ σ k) := by
  rw [coreBox]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Icc)

/-! ## The general two-field coarse-stability lemma (B′3 core) -/

/-- **General coarse stability.**  For two fields `c, c'` that are `(1, Θ)`-elliptic
on `U := cubeSet (originCube d m)` and agree on `U ∖ S`, the coarse observable
moves by at most `48 Θ (vol U)⁻¹` times the `S`-energy of any minimizer `Z`
for `c`.  This is the corridor-independent heart of
`abs_phaseObservable_sub_le_of_minimizer`. -/
theorem abs_coarseObservable_sub_le_of_minimizer [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {S : Set (Vec d)} (P : BlockVec d) {c c' : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) c)
    (hEll' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) c')
    (hS : MeasurableSet S) (hSU : S ⊆ cubeSet (originCube d m))
    (hagreeOff : Set.EqOn c c' (cubeSet (originCube d m) \ S))
    {Z : BlockState d}
    (hZadm : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZresp : BlockResponseSpace c (cubeSet (originCube d m)) Z)
    (hZeng : Mu (cubeSet (originCube d m)) P c
      = blockEnergyAverage (cubeSet (originCube d m)) c Z) :
    |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) c') P) -
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) c) P)| ≤
      48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
        ∫ x in S, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) := by
  classical
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by rw [hUdef]; infer_instance
  have hΘpos : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  obtain ⟨Zσ, hZσadm, hZσeng, hZσresp⟩ := exists_cubeBlockMinimizer hEll' P
  -- energy-integral forms of both `Mu`-quadratics
  have hFc : blockVecDot P (blockMatVecMul (coarseBlockMatrix U c) P)
      = (volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEll hZeng
  have hFc' : blockVecDot P (blockMatVecMul (coarseBlockMatrix U c') P)
      = (volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (Zσ.eval x) (blockMatVecMul (blockCoeffField c' x) (Zσ.eval x)) :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEll' hZσeng
  have hK : (1 : ℝ) ≤ 4 * Θ := by linarith
  have hZbl : MemBlockL2 U Z.eval := hZadm.memBlockL2_eval
  have hZσbl : MemBlockL2 U Zσ.eval := hZσadm.memBlockL2_eval
  set W : BlockState d :=
    { potential := fun x => Zσ.potential x - Z.potential x
      flux := fun x => Zσ.flux x - Z.flux x } with hWdef
  have hWeval : ∀ x, W.eval x = Zσ.eval x - Z.eval x := fun x => rfl
  have hWbl : MemBlockL2 U W.eval := hZσbl.sub hZbl
  have hae : ∀ᵐ x ∂(volume.restrict U),
      IsSymmetricBlockMat (blockCoeffField c x) ∧ IsSymmetricBlockMat (blockCoeffField c' x) ∧
      (∀ V : BlockVec d, 0 ≤ blockVecDot V (blockMatVecMul (blockCoeffField c x) V)) ∧
      (∀ V : BlockVec d, 0 ≤ blockVecDot V (blockMatVecMul (blockCoeffField c' x) V)) ∧
      BlockMatLoewnerLE (blockCoeffField c' x) ((4 * Θ) • blockCoeffField c x) ∧
      BlockMatLoewnerLE (blockCoeffField c x) ((4 * Θ) • blockCoeffField c' x) := by
    refine (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have hAx : IsEllipticMatrix 1 Θ (c x) := hEll.2 x hx
    have hAσx : IsEllipticMatrix 1 Θ (c' x) := hEll'.2 x hx
    exact ⟨isSymmetricBlockMat_blockMatrixOfCoeff (c x),
      isSymmetricBlockMat_blockMatrixOfCoeff (c' x),
      fun V => blockMatrixOfCoeff_quadratic_nonneg hAx V,
      fun V => blockMatrixOfCoeff_quadratic_nonneg hAσx V,
      blockMatrixOfCoeff_blockMatLoewnerLE_smul_of_isThetaElliptic hAx hAσx,
      blockMatrixOfCoeff_blockMatLoewnerLE_smul_of_isThetaElliptic hAσx hAx⟩
  have hagree : ∀ᵐ x ∂(volume.restrict (U \ S)),
      blockCoeffField c x = blockCoeffField c' x := by
    refine (ae_restrict_iff' (hU.diff hS)).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have hcc' : c x = c' x := hagreeOff hx
    unfold blockCoeffField; rw [hcc']
  have hIntBZZ : IntegrableOn
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x))) U := by
    simpa [blockPairingIntegrand] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (X := Z) (Y := Z) hZbl hZbl hEll
  have hIntBtZZ : IntegrableOn
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c' x) (Z.eval x))) U := by
    simpa [blockPairingIntegrand] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (X := Z) (Y := Z) hZbl hZbl hEll'
  have hIntBtYY : IntegrableOn
      (fun x => blockVecDot (Zσ.eval x - Z.eval x)
        (blockMatVecMul (blockCoeffField c' x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := W) (Y := W) hWbl hWbl hEll'
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hIntBtZY : IntegrableOn
      (fun x => blockVecDot (Z.eval x)
        (blockMatVecMul (blockCoeffField c' x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := Z) (Y := W) hZbl hWbl hEll'
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hIntBZY : IntegrableOn
      (fun x => blockVecDot (Z.eval x)
        (blockMatVecMul (blockCoeffField c x) (Zσ.eval x - Z.eval x))) U := by
    have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := Z) (Y := W) hZbl hWbl hEll
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [blockPairingIntegrand, hWeval]
  have hEulerB : ∫ x in U,
      blockVecDot (Zσ.eval x - Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) = 0 :=
    cubeBlockMinimizer_euler_orthogonality_sub hZresp hZσadm hZadm
  have hEulerBt : ∫ x in U,
      blockVecDot (Zσ.eval x - Z.eval x) (blockMatVecMul (blockCoeffField c' x) (Zσ.eval x)) = 0 :=
    cubeBlockMinimizer_euler_orthogonality_sub hZσresp hZσadm hZadm
  have hB3 := abs_setIntegral_energy_sub_le (U := U) (S := S)
    (B := blockCoeffField c) (Bt := blockCoeffField c')
    (Z := Z.eval) (Zt := Zσ.eval) (K := 4 * Θ)
    hU hS hSU hK hae hagree
    hIntBZZ hIntBtZZ hIntBtYY hIntBtZY hIntBZY hEulerB hEulerBt
  rw [hFc', hFc]
  have hc0 : (0 : ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hES0 : (0 : ℝ) ≤ ∫ x in S,
      blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) :=
    setIntegral_nonneg hS
      (fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x (hSU hx)) (Z.eval x))
  set cst := (volume U).toReal⁻¹ with hcstdef
  set Iσ := ∫ x in U,
    blockVecDot (Zσ.eval x) (blockMatVecMul (blockCoeffField c' x) (Zσ.eval x)) with hIσdef
  set I := ∫ x in U,
    blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) with hIdef
  set ES := ∫ x in S,
    blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) with hESdef
  have hprod : (0 : ℝ) ≤ cst * Θ * ES := mul_nonneg (mul_nonneg hc0 hΘpos.le) hES0
  calc |cst * Iσ - cst * I|
      = cst * |Iσ - I| := by rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    _ ≤ cst * (6 * (4 * Θ) * ES) := mul_le_mul_of_nonneg_left hB3 hc0
    _ ≤ 48 * Θ * cst * ES := by nlinarith [hprod]

/-! ## The one-core resampling specialization -/

/-- **Part 3 (one-core resampling stability), minimizer form.**  For a fixed grid
phase `σ` and two fields `b, b'` that are `(1, Θ)`-elliptic on
`U := cubeSet (originCube d m)` and agree off the core `coreBox ℓ σ k`, the
fixed-phase observable moves by at most a normalized core-energy of the
minimizer `Z` for `corridorField ℓ σ b`. -/
theorem abs_phaseObservable_resample_sub_le_of_minimizer [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} (P : BlockVec d)
    {b b' : CoeffField d}
    (hEllb : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b)
    (hEllb' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b')
    (hbb' : Set.EqOn b b' (coreBox ℓ σ k)ᶜ)
    {Z : BlockState d}
    (hZadm : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZresp : BlockResponseSpace (corridorField ℓ σ b) (cubeSet (originCube d m)) Z)
    (hZeng : Mu (cubeSet (originCube d m)) P (corridorField ℓ σ b)
      = blockEnergyAverage (cubeSet (originCube d m)) (corridorField ℓ σ b) Z) :
    |blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b')) P) -
        blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b)) P)| ≤
      48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
        ∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
          blockVecDot (Z.eval x)
            (blockMatVecMul (blockCoeffField (corridorField ℓ σ b) x) (Z.eval x)) := by
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  -- the two corridor-modified fields are elliptic on `U`
  have hEllc : IsEllipticFieldOn 1 Θ U (corridorField ℓ σ b) :=
    isEllipticFieldOn_corridorField hU hΘ hEllb
  have hEllc' : IsEllipticFieldOn 1 Θ U (corridorField ℓ σ b') :=
    isEllipticFieldOn_corridorField hU hΘ hEllb'
  set S : Set (Vec d) := coreBox ℓ σ k ∩ U with hSdef
  have hS : MeasurableSet S := (measurableSet_coreBox ℓ σ k).inter hU
  have hSU : S ⊆ U := Set.inter_subset_right
  -- corridor fields agree on `U ∖ S = U ∖ coreBox k`
  have hagreeOff : Set.EqOn (corridorField ℓ σ b) (corridorField ℓ σ b') (U \ S) := by
    intro x hx
    have hxnc : x ∉ coreBox ℓ σ k := by
      intro hc; exact hx.2 ⟨hc, hx.1⟩
    by_cases hxS : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hxS, corridorField_apply_of_mem hxS]
    · rw [corridorField_apply_of_not_mem hxS, corridorField_apply_of_not_mem hxS]
      exact hbb' hxnc
  exact abs_coarseObservable_sub_le_of_minimizer hΘ P hEllc hEllc' hS hSU hagreeOff
    hZadm hZresp hZeng

/-- **Part 3 (one-core resampling stability).**  Existential-minimizer wrapper. -/
theorem abs_phaseObservable_resample_sub_le [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} (P : BlockVec d)
    {b b' : CoeffField d}
    (hEllb : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b)
    (hEllb' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b')
    (hbb' : Set.EqOn b b' (coreBox ℓ σ k)ᶜ) :
    ∃ Z : BlockState d,
      IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
        BlockResponseSpace (corridorField ℓ σ b) (cubeSet (originCube d m)) Z ∧
        |blockVecDot P
              (blockMatVecMul
                (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b')) P) -
            blockVecDot P
              (blockMatVecMul
                (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b)) P)| ≤
          48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
            ∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
              blockVecDot (Z.eval x)
                (blockMatVecMul (blockCoeffField (corridorField ℓ σ b) x) (Z.eval x)) := by
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  have hEllc : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (corridorField ℓ σ b) :=
    isEllipticFieldOn_corridorField hU hΘ hEllb
  obtain ⟨Z, hZadm, hZeng, hZresp⟩ := exists_cubeBlockMinimizer hEllc P
  exact ⟨Z, hZadm, hZresp,
    abs_phaseObservable_resample_sub_le_of_minimizer hΘ P hEllb hEllb' hbb' hZadm hZresp hZeng⟩

end Homogenization
