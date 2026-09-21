/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.Common

/-! # Response Space -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Doubled Response Space

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

theorem potentialFieldOn_of_ae_eq {d : ℕ}
    {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hg : Book.Ch01.PotentialFieldOn U g) :
    Book.Ch01.PotentialFieldOn U f := by
  rcases hg with ⟨hgMem, u, hgu⟩
  exact ⟨hgMem.ae_eq hfg.symm, u, hfg.trans hgu⟩

theorem solenoidalFieldOn_of_ae_eq {d : ℕ}
    {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hg : Book.Ch01.SolenoidalFieldOn U g) :
    Book.Ch01.SolenoidalFieldOn U f := by
  refine ⟨hg.1.ae_eq hfg.symm, ?_⟩
  intro φ
  calc
    ∫ x in U, vecDot (f x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hfg] with x hx
        simp [hx]
    _ = 0 := hg.2 φ

theorem isDoubledResponseField_of_sameAE {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {X Y : DoubledField d}
    (hXY : DoubledField.SameAE (U := U) X Y)
    (hY : IsDoubledResponseField U a Y) :
    IsDoubledResponseField U a X := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨potentialFieldOn_of_ae_eq hXY.1 hY.1.1,
        solenoidalFieldOn_of_ae_eq hXY.2 hY.1.2⟩
  · intro T hT
    calc
      ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a T X x ∂MeasureTheory.volume =
        ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a T Y x ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hXY.1, hXY.2] with x hxPot hxFlux
          simp [doubledBlockPairingIntegrand, DoubledField.eval, hxPot, hxFlux]
      _ = 0 := hY.2 T hT

theorem isPotentialOn_congr_ae {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict U] g)
    (hf : IsPotentialOn U f) :
    IsPotentialOn U g := by
  rcases hf with ⟨u, hgrad⟩
  let v : H1Function U :=
    { toFun := u.toFun
      grad := g
      memL2 := u.memL2
      gradMemL2 := by
        intro i
        have hcoord :
            (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i := by
          filter_upwards [hfg] with x hx
          simpa [hgrad] using congrArg (fun y : Vec d => y i) hx
        exact (u.gradMemL2 i).ae_eq hcoord
      hasWeakGradient := by
        intro i ψ hψ_smooth hψ_compact hψ_sub
        have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_compact hψ_sub
        have hcoord :
            (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i := by
          filter_upwards [hfg] with x hx
          simpa [hgrad] using congrArg (fun y : Vec d => y i) hx
        have hright :
            ∫ x in U, g x i * ψ x ∂MeasureTheory.volume =
              ∫ x in U, u.grad x i * ψ x ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hcoord] with x hx
          rw [← hx]
        calc
          ∫ x in U, u.toFun x * (fderiv ℝ ψ x) (basisVec i)
              ∂MeasureTheory.volume =
            -∫ x in U, u.grad x i * ψ x ∂MeasureTheory.volume := hweak
          _ = -∫ x in U, g x i * ψ x ∂MeasureTheory.volume := by rw [hright] }
  exact ⟨v, rfl⟩

theorem potentialFieldOn_of_isPotentialOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialOn U f) :
    Book.Ch01.PotentialFieldOn U f := by
  rcases hf with ⟨u, rfl⟩
  exact Book.Ch01.potentialFieldOn_of_h1 u

theorem isPotentialOn_of_potentialFieldOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : Book.Ch01.PotentialFieldOn U f) :
    IsPotentialOn U f := by
  rcases hf with ⟨_hfMem, u, hu⟩
  exact isPotentialOn_congr_ae hu.symm u.isPotentialOn

theorem isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases hf with ⟨_hfMem, φ, hφ⟩
  exact IsPotentialZeroTraceOn.congr_ae hφ.symm φ.isPotentialZeroTraceOn

theorem solenoidalFieldOn_of_isSolenoidalOn {d : ℕ}
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg_mem : MemVectorL2 U g) (hg : IsSolenoidalOn U g) :
    Book.Ch01.SolenoidalFieldOn U g :=
  ⟨hg_mem, hg⟩

theorem lowerImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {X : BlockState d}
    {lam Lam : ℝ}
    (hPot : MemVectorL2 U X.potential) (hFlux : MemVectorL2 U X.flux)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  have hSkewPot :
      MemVectorL2 U (fun x => matVecMul (skewPart (a x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hPot
  have hShift :
      MemVectorL2 U
        (fun x => X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [sub_eq_add_neg] using! hFlux.sub hSkewPot
  have hInv :
      MemVectorL2 U
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hShift
  have hEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) =
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) := by
    funext x
    simpa [BlockState.eval, blockCoeffField] using
      (blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x) (p := X.potential x) (q := X.flux x))
  simpa [hEq] using hInv

theorem upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {X : BlockState d} (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d}
    (hx : x ∈ U) :
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 + X.flux x =
      matVecMul (a x)
        (X.potential x + (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  let lower : Vec d := (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hlower :
      lower =
        matVecMul ((symmPart (a x))⁻¹)
          (X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hupper :
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 =
        matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x)) lower := by
    rw [hlower]
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_fst
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hrecover :
      X.flux x =
        matVecMul (symmPart (a x)) lower +
          matVecMul (skewPart (a x)) (X.potential x) := by
    simpa [lower] using!
      blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
        (A := a x) (hEll.2 x hx) (p := X.potential x) (q := X.flux x)
  have hsplit : a x = symmPart (a x) + skewPart (a x) := by
    ext i j
    simp [symmPart, skewPart, sub_eq_add_neg]
    ring
  calc
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 + X.flux x =
        (matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x)) lower) +
          (matVecMul (symmPart (a x)) lower +
            matVecMul (skewPart (a x)) (X.potential x)) := by
          rw [hupper, hrecover]
    _ =
        matVecMul (symmPart (a x)) (X.potential x + lower) +
          matVecMul (skewPart (a x)) (X.potential x + lower) := by
          rw [matVecMul_add, matVecMul_add]
          abel
    _ = matVecMul ((symmPart (a x)) + skewPart (a x)) (X.potential x + lower) := by
          rw [add_matVecMul]
    _ = matVecMul (a x) (X.potential x + lower) := by
          rw [← hsplit]

theorem upperImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {X : BlockState d}
    {lam Lam : ℝ}
    (hPot : MemVectorL2 U X.potential) (hFlux : MemVectorL2 U X.flux)
    (hLower :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
  let lower : Vec d → Vec d :=
    fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hPotLower : MemVectorL2 U (fun x => X.potential x + lower x) := by
    simpa [lower, Pi.add_apply] using! hPot.add hLower
  have hA :
      MemVectorL2 U (fun x => matVecMul (a x) (X.potential x + lower x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hPotLower
  have hUpper' :
      MemVectorL2 U (fun x => matVecMul (a x) (X.potential x + lower x) - X.flux x) := by
    simpa [sub_eq_add_neg] using! hA.sub hFlux
  have hEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1)
        =ᵐ[volumeMeasureOn U]
      fun x => matVecMul (a x) (X.potential x + lower x) - X.flux x := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)]
      with x hx
    have hpoint :=
      upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
        (a := a) hEll (X := X) hx
    exact eq_sub_iff_add_eq.mpr (by simpa [lower] using hpoint)
  have hMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1)
        (volumeMeasureOn U) :=
    hUpper'.1.congr hEq.symm
  refine hUpper'.congr_norm hMeas ?_
  filter_upwards [hEq] with x hx
  simpa using congrArg norm hx.symm

theorem blockResponseSpace_of_isDoubledResponseField_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    {X : DoubledField d} (hX : IsDoubledResponseField U a X) :
    BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled X) := by
  let upper : Vec d → Vec d :=
    fun x => (blockMatVecMul (blockCoeffField a.toCoeffField x)
      ((blockStateOfDoubled X).eval x)).1
  let lower : Vec d → Vec d :=
    fun x => (blockMatVecMul (blockCoeffField a.toCoeffField x)
      ((blockStateOfDoubled X).eval x)).2
  have hPotMem : MemVectorL2 (U : Set (Vec d)) X.potential := hX.1.1.1
  have hFluxMem : MemVectorL2 (U : Set (Vec d)) X.flux := hX.1.2.1
  have hLowerL2 : MemVectorL2 (U : Set (Vec d)) lower := by
    simpa [lower, blockStateOfDoubled] using
      lowerImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn
        (a := a.toCoeffField) (X := blockStateOfDoubled X)
        hPotMem hFluxMem hEll
  have hUpperL2 : MemVectorL2 (U : Set (Vec d)) upper := by
    simpa [upper, lower, blockStateOfDoubled] using
      upperImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn
        (a := a.toCoeffField) (X := blockStateOfDoubled X)
        hPotMem hFluxMem hLowerL2 hEll
  have hUpperSol : IsSolenoidalOn (U : Set (Vec d)) upper := by
    intro φ
    let Y : DoubledField d := { potential := φ.toH1Function.grad, flux := 0 }
    have hY : IsDoubledTestField U Y := by
      refine ⟨Book.Ch01.potentialZeroTraceFieldOn_of_h10 φ, ?_⟩
      refine ⟨MeasureTheory.MemLp.zero, ?_⟩
      intro ψ
      simp [Y, vecDot]
    have hzero := hX.2 Y hY
    have hrewrite :
        ∫ x in (U : Set (Vec d)),
            doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume =
          ∫ x in (U : Set (Vec d)), vecDot (φ.toH1Function.grad x) (upper x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [Y, upper, blockStateOfDoubled, doubledBlockPairingIntegrand,
        DoubledField.eval, BlockState.eval, blockMatrixField, blockCoeffField,
        blockMatrixOfCoeff, blockVecDot, vecDot_zero_left]
    calc
      ∫ x in (U : Set (Vec d)), vecDot (upper x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in (U : Set (Vec d)), vecDot (φ.toH1Function.grad x) (upper x)
          ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [vecDot_comm]
      _ = 0 := by
        simpa [hrewrite] using hzero
  have hLowerOrth :
      ∀ {g : Vec d → Vec d}, MemVectorL2 (U : Set (Vec d)) g →
        IsSolenoidalZeroNormalTraceOn (U : Set (Vec d)) g →
          ∫ x in (U : Set (Vec d)), vecDot (g x) (lower x)
            ∂MeasureTheory.volume = 0 := by
    intro g hg hsol
    let Y : DoubledField d := { potential := 0, flux := g }
    have hY : IsDoubledTestField U Y := by
      refine ⟨?_, ⟨hg, hsol⟩⟩
      exact Book.Ch01.potentialZeroTraceFieldOn_of_h10
        (0 : H10Function (U : Set (Vec d)))
    have hzero := hX.2 Y hY
    have hrewrite :
        ∫ x in (U : Set (Vec d)),
            doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume =
          ∫ x in (U : Set (Vec d)), vecDot (g x) (lower x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [Y, lower, blockStateOfDoubled, doubledBlockPairingIntegrand,
        DoubledField.eval, BlockState.eval, blockMatrixField, blockCoeffField,
        blockMatrixOfCoeff, blockVecDot, vecDot_zero_left]
    simpa [hrewrite] using hzero
  have hLowerPot : IsPotentialOn (U : Set (Vec d)) lower :=
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain)
      hLowerL2 hLowerOrth
  refine ⟨isPotentialOn_of_potentialFieldOn hX.1.1, hX.1.2.2, ?_⟩
  intro Y hY
  rcases hY.1 with ⟨φ, hφ⟩
  rcases hLowerPot with ⟨ψ, hψ⟩
  have hYpotL2 : MemVectorL2 (U : Set (Vec d)) Y.potential := by
    simpa [hφ] using φ.toH1Function.grad_memVectorL2
  have hTerm1Int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.potential x) (upper x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hYpotL2 hUpperL2
  have hTerm1Zero :
      ∫ x in (U : Set (Vec d)), vecDot (Y.potential x) (upper x)
        ∂MeasureTheory.volume = 0 := by
    have hzero := hUpperSol φ
    simpa [hφ, vecDot_comm] using hzero
  have hTerm2Zero :
      ∫ x in (U : Set (Vec d)), vecDot (Y.flux x) (lower x)
        ∂MeasureTheory.volume = 0 := by
    have hzero := hY.2 ψ
    simpa [hψ] using hzero
  have hrewrite :
      ∫ x in (U : Set (Vec d)),
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockCoeffField a.toCoeffField x)
              ((blockStateOfDoubled X).eval x)) ∂MeasureTheory.volume =
        ∫ x in (U : Set (Vec d)),
          vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)
            ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [upper, lower, blockStateOfDoubled, BlockState.eval, blockVecDot]
  rw [hrewrite]
  by_cases hTerm2Int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.flux x) (lower x)) (U : Set (Vec d))
  · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hTerm1Zero, hTerm2Zero]
    simp
  · have hSumNotInt :
        ¬MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x))
          (U : Set (Vec d)) := by
      intro hSumInt
      exact hTerm2Int
        ((MeasureTheory.integrable_add_iff_integrable_right'
            (μ := MeasureTheory.volume.restrict (U : Set (Vec d))) hTerm1Int).mp hSumInt)
    rw [MeasureTheory.integral_undef hSumNotInt]

theorem isDoubledResponseField_of_blockResponseSpace {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {X : BlockState d}
    (hX : BlockResponseSpace a.toCoeffField (U : Set (Vec d)) X)
    (hFlux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    IsDoubledResponseField U a (doubledFieldOfBlockState X) := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨potentialFieldOn_of_isPotentialOn hX.1,
        solenoidalFieldOn_of_isSolenoidalOn hFlux hX.2.1⟩
  · intro Y hY
    have hYOld : IsBlockTestOn (U : Set (Vec d)) (blockStateOfDoubled Y) := by
      refine ⟨?_, ?_⟩
      · exact isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hY.1
      · exact hY.2.2
    simpa [doubledFieldOfBlockState, blockStateOfDoubled,
      doubledBlockPairingIntegrand, blockCoeffField]
      using! hX.2.2 (blockStateOfDoubled Y) hYOld

theorem doubledFieldOfSolutions_flux_memL2_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    MemVectorL2 (U : Set (Vec d)) (doubledFieldOfSolutions a v vStar).flux := by
  have hEllAdj :
      IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
        (Homogenization.adjointCoeffField a.toCoeffField) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hv :
      MemVectorL2 (U : Set (Vec d))
        (fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1.grad_memVectorL2
  have hvStar :
      MemVectorL2 (U : Set (Vec d))
        (fun x => matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x)) := by
    simpa [Homogenization.adjointCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj vStar.toH1.grad_memVectorL2
  simpa [doubledFieldOfSolutions, sub_eq_add_neg] using! hv.sub hvStar

theorem doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    IsDoubledResponseField U a (doubledFieldOfSolutions a v vStar) := by
  have hOld :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d))
        (blockResponsePairState a.toCoeffField v vStar) := by
    simpa [Homogenization.adjointCoeffField] using!
      blockResponse_pair_mem_responseSpace_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll v vStar
  have hFlux :=
    doubledFieldOfSolutions_flux_memL2_of_isEllipticFieldOn U a hEll v vStar
  simpa [doubledFieldOfBlockState, doubledFieldOfSolutions, blockResponsePairState,
    Homogenization.adjointCoeffField] using
    isDoubledResponseField_of_blockResponseSpace U a hOld hFlux

theorem response_space_by_solutions_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ X : DoubledField d,
      IsDoubledResponseField U a X ↔
        ∃ v : Solution U a, ∃ vStar : Solution U a.transpose,
          DoubledField.SameAE (U := U) X (doubledFieldOfSolutions a v vStar) := by
  intro X
  constructor
  · intro hX
    have hOld :
        BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled X) :=
      blockResponseSpace_of_isDoubledResponseField_of_isEllipticFieldOn U a hEll hX
    have hLowerL2 :
        MemVectorL2 (U : Set (Vec d))
          (fun x =>
            (blockMatVecMul (blockCoeffField a.toCoeffField x)
              ((blockStateOfDoubled X).eval x)).2) := by
      exact
        lowerImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn
          (a := a.toCoeffField) (X := blockStateOfDoubled X)
          hX.1.1.1 hX.1.2.1 hEll
    rcases
      exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_memVectorL2_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (a := a.toCoeffField) U.isDomain hOld hLowerL2 hEll
        with ⟨u, vStarOld, hhalf⟩
    let vStar : Solution U a.transpose := by
      simpa [Homogenization.adjointCoeffField] using! vStarOld
    refine ⟨solutionSMul U a (1 / 2 : ℝ) u,
      solutionSMul U a.transpose (1 / 2 : ℝ) vStar, ?_⟩
    have hEq :
        doubledFieldOfSolutions a (solutionSMul U a (1 / 2 : ℝ) u)
            (solutionSMul U a.transpose (1 / 2 : ℝ) vStar) =
          doubledFieldOfBlockState
            (blockResponsePairHalfState a.toCoeffField u vStarOld) := by
      simpa [vStar, Homogenization.adjointCoeffField] using
        doubledFieldOfSolutions_solutionSMul_half_eq_pairHalf U a u vStar
    have hSamePair :
        DoubledField.SameAE (U := U) X
          (doubledFieldOfBlockState
            (blockResponsePairHalfState a.toCoeffField u vStarOld)) := by
      constructor
      · filter_upwards [hhalf] with x hx
        exact (congrArg Prod.fst hx).symm
      · filter_upwards [hhalf] with x hx
        exact (congrArg Prod.snd hx).symm
    rw [hEq]
    exact hSamePair
  · rintro ⟨v, vStar, hsame⟩
    exact
      isDoubledResponseField_of_sameAE U a hsame
        (doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn U a hEll v vStar)

theorem book_doubledResponseValue_eq_blockResponseIntegrand {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d) (X : DoubledField d) :
    doubledResponseValue U a P Q X =
      volumeAverage (U : Set (Vec d))
        (blockResponseIntegrand a.toCoeffField P Q (blockStateOfDoubled X)) :=
  rfl

theorem book_doubledResponseValue_ofBlockState_eq_blockResponseIntegrand {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d) (X : BlockState d) :
    doubledResponseValue U a P Q (doubledFieldOfBlockState X) =
      volumeAverage (U : Set (Vec d))
        (blockResponseIntegrand a.toCoeffField P Q X) :=
  rfl

theorem book_doubledResponseValueSet_eq_blockJValueSet_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (P Q : BlockVec d) :
    doubledResponseValueSet U a P Q =
      blockJValueSet (U : Set (Vec d)) P Q a.toCoeffField := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hOld :
        BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled X) :=
      blockResponseSpace_of_isDoubledResponseField_of_isEllipticFieldOn U a hEll hX
    have hInt :
        BlockResponseIntegrabilityData (U : Set (Vec d)) a.toCoeffField
          (blockStateOfDoubled X) :=
      blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
        hOld hX.1.2.1 hEll
    exact ⟨blockStateOfDoubled X, hOld, hInt, rfl⟩
  · rintro ⟨X, hX, hInt, rfl⟩
    exact
      ⟨doubledFieldOfBlockState X,
        isDoubledResponseField_of_blockResponseSpace U a hX hInt.flux_memL2, rfl⟩

theorem book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (P Q : BlockVec d) :
    doubledResponseJ U a P Q =
      BlockJ (U : Set (Vec d)) P Q a.toCoeffField := by
  unfold doubledResponseJ BlockJ
  rw [book_doubledResponseValueSet_eq_blockJValueSet_of_isEllipticFieldOn U a hEll P Q]

end BookCh02

end

end Ch02
end Internal
end Homogenization
