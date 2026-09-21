/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.IntegrabilityFamily

/-! # Pair States -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Foundations -- pair and pair-half state witnesses

blockResponsePairState and blockResponsePairHalfState definitions plus
their mem_responseSpace / lowerImage_ae_eq / integrability data theorems
under IsEllipticFieldOn.
-/

def blockResponsePairState {d : ℕ} {U : Set (Vec d)} (a : CoeffField d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    BlockState d :=
  { potential := fun x => u.toH1.grad x + v.toH1.grad x
    flux := fun x =>
      matVecMul (a x) (u.toH1.grad x) -
        matVecMul (matTranspose (a x)) (v.toH1.grad x) }

def blockResponsePairHalfState {d : ℕ} {U : Set (Vec d)} (a : CoeffField d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    BlockState d :=
  (1 / 2 : ℝ) • blockResponsePairState a u v

theorem blockResponse_pair_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    BlockResponseSpace a U
      { potential := fun x => u.toH1.grad x + v.toH1.grad x
        flux := fun x =>
          matVecMul (a x) (u.toH1.grad x) -
            matVecMul (matTranspose (a x)) (v.toH1.grad x) } := by
  let X : BlockState d :=
    { potential := fun x => u.toH1.grad x + v.toH1.grad x
      flux := fun x =>
        matVecMul (a x) (u.toH1.grad x) -
          matVecMul (matTranspose (a x)) (v.toH1.grad x) }
  let fluxPlus : Vec d → Vec d :=
    fun x =>
      matVecMul (a x) (u.toH1.grad x) +
        matVecMul (matTranspose (a x)) (v.toH1.grad x)
  let gradDiff : Vec d → Vec d := fun x => u.toH1.grad x - v.toH1.grad x
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have huFluxL2 :
      MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hvFluxAdjL2 :
      MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) (v.toH1.grad x)) := by
    simpa [Homogenization.adjointCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj v.toH1.grad_memVectorL2
  have huWeakInt :
      ∀ φ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (matVecMul (a x) (u.toH1.grad x)) (φ.toH1Function.grad x)) U := by
    intro φ
    exact integrableOn_vecDot_of_memVectorL2 huFluxL2 φ.toH1Function.grad_memVectorL2
  have hvWeakInt :
      ∀ φ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (matVecMul (matTranspose (a x)) (v.toH1.grad x))
            (φ.toH1Function.grad x)) U := by
    intro φ
    exact integrableOn_vecDot_of_memVectorL2 hvFluxAdjL2 φ.toH1Function.grad_memVectorL2
  have hfluxSol :
      IsBlockSolenoidalOn U X := by
    have huSol :
        IsSolenoidalOn U (fun x => matVecMul (a x) (u.toH1.grad x)) := u.isHarmonic.2
    have hvSol :
        IsSolenoidalOn U (fun x => matVecMul (matTranspose (a x)) (v.toH1.grad x)) := by
      simpa [Homogenization.adjointCoeffField] using v.isHarmonic.2
    have hvNegSol :
        IsSolenoidalOn U
          (fun x => -matVecMul (matTranspose (a x)) (v.toH1.grad x)) := by
      simpa [Pi.smul_apply] using! isSolenoidalOn_smul hvSol (-1 : ℝ)
    have hvNegInt :
        ∀ φ : H10Function U,
          MeasureTheory.IntegrableOn
            (fun x => vecDot (-matVecMul (matTranspose (a x)) (v.toH1.grad x))
              (φ.toH1Function.grad x)) U := by
      intro φ
      have hneg :
          MeasureTheory.IntegrableOn
            (fun x =>
              -(vecDot (matVecMul (matTranspose (a x)) (v.toH1.grad x))
                (φ.toH1Function.grad x))) U := by
        exact (hvWeakInt φ).neg
      simpa [vecDot_neg_left] using hneg
    refine isSolenoidalOn_add huSol hvNegSol huWeakInt hvNegInt
  refine ⟨?_, hfluxSol, ?_⟩
  · exact isPotentialOn_add u.toH1.isPotentialOn v.toH1.isPotentialOn
  · intro Y hY
    rcases hY with ⟨hYpot, hYflux⟩
    rcases hYpot with ⟨φ, hφ⟩
    have hYpotL2 : MemVectorL2 U Y.potential := by
      simpa [hφ] using φ.toH1Function.grad_memVectorL2
    have hFluxPlusL2 : MemVectorL2 U fluxPlus := by
      simpa [fluxPlus, Pi.add_apply] using! huFluxL2.add hvFluxAdjL2
    have hTerm1Int :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (fluxPlus x)) U :=
      integrableOn_vecDot_of_memVectorL2 hYpotL2 hFluxPlusL2
    have hFluxPlusSol :
        IsSolenoidalOn U fluxPlus := by
      have huSol :
          IsSolenoidalOn U (fun x => matVecMul (a x) (u.toH1.grad x)) := u.isHarmonic.2
      have hvSol :
          IsSolenoidalOn U (fun x => matVecMul (matTranspose (a x)) (v.toH1.grad x)) := by
        simpa [Homogenization.adjointCoeffField] using v.isHarmonic.2
      exact isSolenoidalOn_add huSol hvSol huWeakInt hvWeakInt
    have hTerm1Zero :
        ∫ x in U, vecDot (Y.potential x) (fluxPlus x) ∂MeasureTheory.volume = 0 := by
      have hzero := hFluxPlusSol φ
      simpa [fluxPlus, hφ, vecDot_comm] using hzero
    have hTerm2Zero :
        ∫ x in U, vecDot (Y.flux x) (gradDiff x) ∂MeasureTheory.volume = 0 := by
      have hzero := hYflux (u.toH1 + (-1 : ℝ) • v.toH1)
      have hgradDiff :
          gradDiff = fun x => (u.toH1 + (-1 : ℝ) • v.toH1).grad x := by
        funext x
        ext i
        change u.toH1.grad x i - v.toH1.grad x i = u.toH1.grad x i + (-1 : ℝ) * v.toH1.grad x i
        ring
      simpa [hgradDiff] using hzero
    have hrewrite :
        ∫ x in U,
            blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
              ∂MeasureTheory.volume =
          ∫ x in U, vecDot (Y.potential x) (fluxPlus x) + vecDot (Y.flux x) (gradDiff x)
              ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with
        x hx
      have himage :=
        blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
          (a := a) hEll hx (u.toH1.grad x) (v.toH1.grad x)
      simpa [X, fluxPlus, gradDiff, BlockState.eval, blockVecDot] using
        congrArg (fun Z => blockVecDot (Y.eval x) Z) himage
    rw [hrewrite]
    by_cases hTerm2Int :
        MeasureTheory.IntegrableOn (fun x => vecDot (Y.flux x) (gradDiff x)) U
    · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hTerm1Zero, hTerm2Zero]
      simp
    · have hSumNotInt :
          ¬MeasureTheory.IntegrableOn
            (fun x => vecDot (Y.potential x) (fluxPlus x) + vecDot (Y.flux x) (gradDiff x)) U := by
        intro hSumInt
        exact hTerm2Int
          ((MeasureTheory.integrable_add_iff_integrable_right'
              (μ := MeasureTheory.volume.restrict U) hTerm1Int).mp hSumInt)
      rw [MeasureTheory.integral_undef hSumNotInt]

theorem blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    BlockResponseSpace a U
      ((1 / 2 : ℝ) •
        { potential := fun x => u.toH1.grad x + v.toH1.grad x
          flux := fun x =>
            matVecMul (a x) (u.toH1.grad x) -
              matVecMul (matTranspose (a x)) (v.toH1.grad x) }) := by
  exact blockResponse_mem_responseSpace_smul
    (blockResponse_pair_mem_responseSpace_of_isEllipticFieldOn (a := a) hEll u v) (1 / 2 : ℝ)

theorem blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    (fun x =>
      (blockMatVecMul (blockCoeffField a x)
        ((blockResponsePairHalfState a u v).eval x)).2)
      =ᵐ[volumeMeasureOn U]
        fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x) := by
  let Y : BlockState d := blockResponsePairState a u v
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with
    x hx
  have himage :
      blockMatVecMul (blockCoeffField a x) (Y.eval x) =
        (matVecMul (a x) (u.toH1.grad x) + matVecMul (matTranspose (a x)) (v.toH1.grad x),
          u.toH1.grad x - v.toH1.grad x) := by
    simpa [Y, blockResponsePairState, BlockState.eval] using
      blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
        (a := a) hEll hx (u.toH1.grad x) (v.toH1.grad x)
  change (blockMatVecMul (blockCoeffField a x) (((1 / 2 : ℝ) • Y).eval x)).2 =
      (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)
  rw [BlockState.eval_smul, blockMatVecMul_smul]
  simpa using congrArg Prod.snd (congrArg ((1 / 2 : ℝ) • ·) himage)

theorem blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    BlockResponseIntegrabilityData U a (blockResponsePairHalfState a u v) := by
  have hGradDiffPot :
      IsPotentialOn U (fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)) := by
    have hGradDiff :
        IsPotentialOn U (fun x => u.toH1.grad x - v.toH1.grad x) := by
      simpa [sub_eq_add_neg, Pi.add_apply, Pi.smul_apply] using!
        isPotentialOn_add u.toH1.isPotentialOn (isPotentialOn_smul v.toH1.isPotentialOn (-1 : ℝ))
    exact isPotentialOn_smul hGradDiff (1 / 2 : ℝ)
  exact
    blockResponseIntegrabilityData_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
      (hX := by
        simpa [blockResponsePairHalfState] using!
          (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn (a := a) hEll u v))
      hGradDiffPot
      (blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn (a := a) hEll u v)
      hEll

end

end Homogenization
