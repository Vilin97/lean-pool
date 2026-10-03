/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPushforward
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenShearOrthogonality

/-! Column divergence of the per-corrector diffusion flux and its inverse-flow
expansion. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

noncomputable section

theorem CorrectorDiffusionDivergence.vecDiv_eq_fderiv
    {V : Vec 2 → Vec 2} {x : Vec 2} {LV : Vec 2 →L[ℝ] Vec 2}
    (hV : HasFDerivAt V LV x) :
    vecDiv V x = ∑ i : Fin 2, (LV (basisVec i)) i := by
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : HasFDerivAt (fun y => V y i)
      ((ContinuousLinearMap.proj i).comp LV) x := by
    exact (ContinuousLinearMap.proj i).hasFDerivAt.comp x hV
  rw [spaceGrad, hcoord.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem CorrectorDiffusionDivergence.vecDiv_add_hasFDerivAt
    {V W : Vec 2 → Vec 2} {x : Vec 2}
    {LV LW : Vec 2 →L[ℝ] Vec 2}
    (hV : HasFDerivAt V LV x) (hW : HasFDerivAt W LW x) :
    vecDiv (fun y => V y + W y) x = vecDiv V x + vecDiv W x := by
  change vecDiv (V + W) x = vecDiv V x + vecDiv W x
  rw [CorrectorDiffusionDivergence.vecDiv_eq_fderiv (hV.add hW),
      CorrectorDiffusionDivergence.vecDiv_eq_fderiv hV,
    CorrectorDiffusionDivergence.vecDiv_eq_fderiv hW]
  simp [Pi.add_apply, Finset.sum_add_distrib]

theorem CorrectorDiffusionDivergence.vecDiv_const_eq_zero (v : Vec 2) (x : Vec 2) :
    vecDiv (fun _ : Vec 2 => v) x = 0 := by
  simp [vecDiv, spaceGrad, fderiv_const_apply]

/-- Shear matrix plus the diffusive corrector gradient, evaluated along the inverse flow. -/
def correctorBaseMatrix
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (I.zetaProd m k t * psi β I.Λ m k
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
    κ • gradMatrix (fun z => I.chiMK κ m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)

/-- Corrector defect caused by the inverse-flow Jacobian's deviation from the identity. -/
def correctorDefectMatrix
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • ((gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y - 1) *
    gradMatrix (fun z => I.chiMK κ m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))

/-- Corrector matrix contribution caused by the transposed flow Jacobian's deviation from
identity. -/
def correctorPushforwardMatrix
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose) *
    correctorBaseMatrix I hΦ m k t κ y

/-- Shear amplitude multiplied by the rotated gradient of one transported corrector component. -/
def correctorShearCrossColumn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (j : Fin 2) (y : Vec 2) : Vec 2 :=
  fun i =>
    (I.zetaProd m k t * psi β I.Λ m k
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) *
      sigmaMat.mulVec (spaceGrad
        (fun z => I.chiTilde hΦ m κ k t z j) y) i

/-- Specified column of the inverse-flow corrector defect matrix. -/
def correctorDefectColumn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (j : Fin 2) (y : Vec 2) : Vec 2 :=
  fun i => correctorDefectMatrix I hΦ m k t κ y i j

/-- Specified column of the corrector pushforward matrix. -/
def correctorPushforwardColumn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (j : Fin 2) (y : Vec 2) : Vec 2 :=
  fun i => correctorPushforwardMatrix I hΦ m k t κ y i j

theorem CorrectorDiffusionDivergence.correctorFlux_column_decomposition
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ)
    (j : Fin 2) :
    (fun y i => correctorFlux I hΦ m κ k t y i j) =
      fun y => (κ • basisVec j +
        frozenCorrectorFlux I κ m k j t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) +
        correctorDefectColumn I hΦ m k t κ j y) +
          correctorShearCrossColumn I hΦ m k t κ j y := by
  funext y i
  have hexpand := frozen_corrector_diffusion_matrix_expansion
    I hΦ m k t y κ
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hexpand
  let M := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  let χ : Vec 2 → Vec 2 := fun z => I.chiMK κ m k t z
  have hχ : DifferentiableAt ℝ χ (M y) := by
    have hχ2 : ContDiff ℝ 2 χ := by
      let E : Vec 2 → ℝ × Vec 2 := fun z => (t, z)
      have hE : ContDiff ℝ 2 E := by fun_prop
      have hχ0 := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k 0).comp hE
      have hχ1 := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k 1).comp hE
      apply contDiff_pi.2
      intro c
      fin_cases c
      · simpa [χ, E, Function.comp_def] using hχ0
      · simpa [χ, E, Function.comp_def] using hχ1
    exact hχ2.differentiable (by norm_num) (M y)
  have hM : DifferentiableAt ℝ M y :=
    (xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) y
  have hchain : gradMatrix (I.chiTilde hΦ m κ k t) y =
      gradMatrix M y * gradMatrix χ (M y) := by
    have hcomp := gradMatrix_comp hχ hM
    have heq : I.chiTilde hΦ m κ k t = fun z => χ (M z) := rfl
    rw [heq]
    exact hcomp
  have hcross :
      ((I.zetaProd m k t * psi β I.Λ m k
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat *
        (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y *
          gradMatrix (fun z => I.chiMK κ m k t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) i j =
      correctorShearCrossColumn I hΦ m k t κ j y i := by
    rw [← hchain]
    simp [correctorShearCrossColumn, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, gradMatrix]
    ring
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] at hentry
  rw [hcross] at hentry
  convert hentry using 1
  simp [correctorDefectColumn, correctorDefectMatrix,
    correctorShearCrossColumn, frozenCorrectorFlux, Ingredients.zetaProd,
    Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, gradMatrix,
    basisVec, Pi.single_apply, Fin.sum_univ_two, Matrix.mulVec,
    dotProduct]

/-- Column divergence of the twisted-corrector diffusion matrix.
The displayed derivative inputs are only local regularity: one derivative of
the pulled base flux and of the two error columns, one derivative of the
inverse-flow cofactor, and the explicit Piola divergence identity. -/
theorem frozen_corrector_diffusion_column_divergence
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (κ : ℝ) (j : Fin 2)
    {LM : Vec 2 →L[ℝ] Vec 2} {LB : Vec 2 →L[ℝ] Vec 2}
    {LD LE : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) LM x)
    (hB : HasFDerivAt (frozenCorrectorFlux I κ m k j t)
      LB (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (hD : HasFDerivAt (correctorDefectColumn I hΦ m k t κ j) LD x)
    (hE : HasFDerivAt (correctorShearCrossColumn I hΦ m k t κ j) LE x)
    (hQ : ∀ i q, HasFDerivAt (fun y => rowCofactor
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i q)
      (LQ i q) x)
    (hPiolaDiv : ∀ q,
      ∑ i : Fin 2, (LQ i q) (basisVec i) = 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    matDiv (correctorFlux I hΦ m κ k t) x j =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
        matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
  let M := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  let B : Vec 2 → Vec 2 := fun y =>
    frozenCorrectorFlux I κ m k j t (M y)
  let D : Vec 2 → Vec 2 := correctorDefectColumn I hΦ m k t κ j
  let E : Vec 2 → Vec 2 := correctorShearCrossColumn I hΦ m k t κ j
  have hBcomp : HasFDerivAt B (LB.comp LM) x := by
    exact hB.comp x hM
  have hconst : HasFDerivAt (fun _ : Vec 2 => κ • basisVec j)
      (0 : Vec 2 →L[ℝ] Vec 2) x := hasFDerivAt_const _ x
  have hsum : HasFDerivAt (fun y =>
      (κ • basisVec j + B y + D y) + E y)
      (((0 : Vec 2 →L[ℝ] Vec 2) + LB.comp LM + LD) + LE) x := by
    exact ((hconst.add hBcomp).add hD).add hE
  have hdecomp : (fun y i => correctorFlux I hΦ m κ k t y i j) =
      fun y => (κ • basisVec j + B y + D y) + E y := by
    simpa [M, B, D, E] using
      (CorrectorDiffusionDivergence.correctorFlux_column_decomposition I hΦ m k t κ j)
  have hpsiSpace : ContDiff ℝ 2 (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ 2
        (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  have hpsiPull : DifferentiableAt ℝ
      (fun y => psi β I.Λ m k (M y)) x := by
    have hM2 : ContDiff ℝ 2 M :=
      xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t
    have hcomp := hpsiSpace.comp hM2
    exact hcomp.differentiable (by norm_num) x
  have hchiTilde : ContDiff ℝ 2
      (fun y => I.chiTilde hΦ m κ k t y j) := by
    have hchiMK : ContDiff ℝ 2
        (fun z => I.chiMK κ m k t z j) := by
      let Etime : Vec 2 → ℝ × Vec 2 := fun z => (t, z)
      have hEtime : ContDiff ℝ 2 Etime := by fun_prop
      have hchi := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k j).comp hEtime
      simpa [Etime, Function.comp_def] using hchi
    have hM2 : ContDiff ℝ 2 M :=
      xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t
    have hcomp := hchiMK.comp hM2
    simpa [Ingredients.chiTilde, M, Function.comp_def] using hcomp
  have horth0 := frozen_shear_orthogonality_component I hΦ m κ k t x j
  let ψpull : Vec 2 → ℝ := fun y => psi β I.Λ m k (M y)
  let q : Vec 2 → ℝ := fun y => I.zetaProd m k t * ψpull y
  have hψpullDiff : DifferentiableAt ℝ ψpull x := by
    simpa [ψpull] using hpsiPull
  have hqDiff : DifferentiableAt ℝ q x :=
    (differentiableAt_const (I.zetaProd m k t)).mul hψpullDiff
  have hqgrad (i : Fin 2) : spaceGrad q x i =
      I.zetaProd m k t * spaceGrad ψpull x i := by
    change fderiv ℝ (fun y => I.zetaProd m k t * ψpull y) x
      (basisVec i) = _
    rw [fderiv_const_mul hψpullDiff (I.zetaProd m k t)]
    simp [spaceGrad, smul_eq_mul]
  have horthPull : vecDot (spaceGrad ψpull x)
      (sigmaMat.mulVec (spaceGrad (fun y =>
        I.chiTilde hΦ m κ k t y j) x)) = 0 := by
    simpa [ψpull] using horth0
  have horth : vecDot (spaceGrad q x)
      (sigmaMat.mulVec (spaceGrad (fun y =>
        I.chiTilde hΦ m κ k t y j) x)) = 0 := by
    calc
      _ = I.zetaProd m k t * vecDot (spaceGrad ψpull x)
          (sigmaMat.mulVec (spaceGrad (fun y =>
            I.chiTilde hΦ m κ k t y j) x)) := by
            simp [vecDot, hqgrad, Fin.sum_univ_two]
            ring
      _ = 0 := by rw [horthPull]; simp
  have hcrossZero := shear_cross_flux_vecDiv_eq_zero
    (ψ := q) (f := fun y => I.chiTilde hΦ m κ k t y j) (x := x)
    hqDiff (hchiTilde.contDiffAt) horth
  have hpush := xFlowInv_corrector_pushforward_flowGrad I hΦ m k t x κ j
    hM hB hQ hPiolaDiv hdiv
  have hcorrect : correctorPushforwardColumn I hΦ m k t κ j = fun y =>
      (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose).mulVec
        (frozenCorrectorFlux I κ m k j t (M y)) := by
    funext y i
    simp [M, correctorPushforwardColumn, correctorPushforwardMatrix,
      correctorBaseMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, frozenCorrectorFlux, gradMatrix, Ingredients.zetaProd,
      Matrix.transpose_apply, Matrix.one_apply]
  have hdivsum : vecDiv (fun y => (κ • basisVec j + B y + D y) + E y) x =
      vecDiv B x + vecDiv D x + vecDiv E x := by
    have hmid := CorrectorDiffusionDivergence.vecDiv_add_hasFDerivAt (hconst.add hBcomp) hD
    have hout := CorrectorDiffusionDivergence.vecDiv_add_hasFDerivAt ((hconst.add hBcomp).add hD) hE
    have hbase := CorrectorDiffusionDivergence.vecDiv_add_hasFDerivAt hconst hBcomp
    have hconstB : (fun _ : Vec 2 => κ • basisVec j) + B =
        fun y => κ • basisVec j + B y := rfl
    rw [hconstB] at hmid
    calc
      vecDiv (fun y => (κ • basisVec j + B y + D y) + E y) x =
          vecDiv (fun y => κ • basisVec j + B y + D y) x + vecDiv E x :=
        hout
      _ = (vecDiv (fun y => κ • basisVec j + B y) x) + vecDiv D x + vecDiv E x := by
        simpa [D] using congrArg (fun v : ℝ => v + vecDiv E x) hmid
      _ = vecDiv B x + vecDiv D x + vecDiv E x := by
        calc
          _ = (vecDiv (fun y => κ • basisVec j) x + vecDiv B x) +
                vecDiv D x + vecDiv E x := by
                  exact congrArg (fun v : ℝ => v + vecDiv D x + vecDiv E x) hbase
          _ = _ := by rw [CorrectorDiffusionDivergence.vecDiv_const_eq_zero]; simp
  have hcol :
      vecDiv (fun y i => correctorFlux I hΦ m κ k t y i j) x =
        vecDiv B x + vecDiv D x + vecDiv E x := by
    rw [hdecomp]
    exact hdivsum
  have hmatD : matDiv (correctorDefectMatrix I hΦ m k t κ) x j =
      vecDiv D x := rfl
  have hmatE : matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j =
      vecDiv (correctorPushforwardColumn I hΦ m k t κ j) x := rfl
  have hEeq : E = fun y => (q y • sigmaMat).mulVec
      (spaceGrad (fun z => I.chiTilde hΦ m κ k t z j) y) := by
    funext y
    change (fun i => (I.zetaProd m k t * psi β I.Λ m k (M y)) *
        sigmaMat.mulVec (spaceGrad (fun z => I.chiTilde hΦ m κ k t z j) y) i) =
      fun i => ((I.zetaProd m k t * psi β I.Λ m k (M y)) • sigmaMat).mulVec
        (spaceGrad (fun z => I.chiTilde hΦ m κ k t z j) y) i
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
    ring
  have hEzero : vecDiv E x = 0 := by
    rw [hEeq]
    exact hcrossZero
  have hcorr : vecDiv (correctorPushforwardColumn I hΦ m k t κ j) x =
      vecDiv (fun y =>
        (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose).mulVec
          (frozenCorrectorFlux I κ m k j t (M y))) x := by
    rw [hcorrect]
  change vecDiv (fun y i => correctorFlux I hΦ m κ k t y i j) x = _
  calc
    _ = vecDiv B x + vecDiv D x + vecDiv E x := hcol
    _ = vecDiv B x + vecDiv D x := by rw [hEzero]; simp
    _ = deriv (fun s => I.chiMK κ m k s (M x) j) t +
      vecDiv (correctorPushforwardColumn I hΦ m k t κ j) x + vecDiv D x := by
        rw [hpush, hcorr]
    _ = deriv (fun s => I.chiMK κ m k s (M x) j) t +
          matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
          matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
        rw [hmatD, hmatE]
        abel

end

end Section5

end Infra

end AVenhance
