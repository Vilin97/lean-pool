/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFluxFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionFlow
public import Mathlib.Analysis.Matrix.Normed

/-! The local derivatives in the corrector diffusion identity follow
from the spatial C² regularity of the flows and correctors. -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance

theorem CorrectorDiffusionRegularity.gradMatrix_contDiff_one_of_contDiff_two_local
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ 2 X) :
    ContDiff ℝ 1 (fun x => gradMatrix X x) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have hi : ContDiff ℝ 1
      (fun x => fderiv ℝ X x (basisVec i)) := hD.clm_apply contDiff_const
  have hij := contDiff_pi.1 hi j
  have heq : (fun x => gradMatrix X x i j) =
      fun x => fderiv ℝ X x (basisVec i) j := by
    funext x
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => X y j) x (basisVec i) = _
    have hdiff : DifferentiableAt ℝ X x := hX.differentiable (by norm_num) x
    rw [fderiv_apply hdiff j]
    simp
  rw [heq]
  exact hij

theorem CorrectorDiffusionRegularity.chiMK_vector_contDiff_two
    {β : ℝ} (I : Ingredients β) (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (fun y => I.chiMK κ m k t y) := by
  apply contDiff_pi.2
  intro j
  let E : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hE : ContDiff ℝ 2 E := by fun_prop
  have h := (Infra.Section3.chiMK_component_contDiff_two
    I (m := m) κ k j).comp hE
  simpa [E, Function.comp_def] using h

theorem CorrectorDiffusionRegularity.psi_contDiff_two
    {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) :
    ContDiff ℝ 2 (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ 2
      (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

theorem CorrectorDiffusionRegularity.matrixMul_contDiff_one_local
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) :
    ContDiff ℝ 1 (fun y => A y * B y) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  change ContDiff ℝ 1 (fun y =>
    ∑ p : Fin 2, A y i p * B y p j)
  apply ContDiff.sum
  intro p hp
  exact (contDiff_pi.1 (contDiff_pi.1 hA i) p).mul
    (contDiff_pi.1 (contDiff_pi.1 hB p) j)

theorem CorrectorDiffusionRegularity.corrector_diffusion_columns_contDiff_one
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (κ : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (frozenCorrectorFlux I κ m k j t) ∧
    ContDiff ℝ 1 (correctorDefectColumn I hΦ m k t κ j) ∧
    ContDiff ℝ 1 (correctorShearCrossColumn I hΦ m k t κ j) := by
  let M : Vec 2 → Vec 2 := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  have hM2 : ContDiff ℝ 2 M :=
    xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t
  have hM1 : ContDiff ℝ 1 M := hM2.of_le (by norm_num)
  have hχ : ContDiff ℝ 2 (fun y => I.chiMK κ m k t y) :=
    CorrectorDiffusionRegularity.chiMK_vector_contDiff_two I κ m k t
  have hχgrad : ContDiff ℝ 1 (fun y => gradMatrix
      (fun z => I.chiMK κ m k t z) y) :=
    CorrectorDiffusionRegularity.gradMatrix_contDiff_one_of_contDiff_two_local hχ
  have hψ2 : ContDiff ℝ 2 (psi β I.Λ m k) := CorrectorDiffusionRegularity.psi_contDiff_two I m k
  have hψM : ContDiff ℝ 1 (fun y => psi β I.Λ m k (M y)) := by
    exact (hψ2.comp hM2).of_le (by norm_num)
  have hflux := frozen_corrector_flux_contDiff_one I κ m k j t
  have hH : ContDiff ℝ 1 (fun y => gradMatrix M y) :=
    CorrectorDiffusionRegularity.gradMatrix_contDiff_one_of_contDiff_two_local hM2
  have hC := hχgrad.comp hM1
  have hHminus : ContDiff ℝ 1 (fun y => gradMatrix M y - 1) :=
    hH.sub contDiff_const
  have hprod := CorrectorDiffusionRegularity.matrixMul_contDiff_one_local hHminus hC
  have hdefMat : ContDiff ℝ 1 (fun y =>
      κ • ((gradMatrix M y - 1) *
        gradMatrix (fun z => I.chiMK κ m k t z) (M y))) := by
    simpa using hprod.const_smul κ
  have hdef : ContDiff ℝ 1 (correctorDefectColumn I hΦ m k t κ j) := by
    apply contDiff_pi.2
    intro i
    have hi := contDiff_pi.1 (contDiff_pi.1 hdefMat i) j
    simpa [correctorDefectColumn, correctorDefectMatrix, M] using hi
  have htilde : ContDiff ℝ 2 (I.chiTilde hΦ m κ k t) := by
    change ContDiff ℝ 2 (fun y => I.chiMK κ m k t (M y))
    exact hχ.comp hM2
  have htildeGrad : ContDiff ℝ 1
      (fun y => gradMatrix (I.chiTilde hΦ m κ k t) y) :=
    CorrectorDiffusionRegularity.gradMatrix_contDiff_one_of_contDiff_two_local htilde
  have hcoef : ContDiff ℝ 1
      (fun y => I.zetaProd m k t * psi β I.Λ m k (M y)) :=
    contDiff_const.mul hψM
  have hcross : ContDiff ℝ 1
      (correctorShearCrossColumn I hΦ m k t κ j) := by
    apply contDiff_pi.2
    intro i
    have hshearGrad : ContDiff ℝ 1 (fun y =>
        ∑ p : Fin 2, sigmaMat i p *
          gradMatrix (I.chiTilde hΦ m κ k t) y p j) := by
      apply ContDiff.sum
      intro p hp
      exact contDiff_const.mul
        (contDiff_pi.1 (contDiff_pi.1 htildeGrad p) j)
    have hmul := hcoef.mul hshearGrad
    change ContDiff ℝ 1 (fun y =>
      I.zetaProd m k t * psi β I.Λ m k (M y) *
        sigmaMat.mulVec
          (spaceGrad (fun z => I.chiTilde hΦ m κ k t z j) y) i)
    have heq : (fun y =>
        I.zetaProd m k t * psi β I.Λ m k (M y) *
          sigmaMat.mulVec
            (spaceGrad (fun z => I.chiTilde hΦ m κ k t z j) y) i) =
        fun y => I.zetaProd m k t * psi β I.Λ m k (M y) *
          (∑ p : Fin 2, sigmaMat i p *
            gradMatrix (I.chiTilde hΦ m κ k t) y p j) := by
      funext y
      simp [Matrix.mulVec, dotProduct, gradMatrix, Fin.sum_univ_two,
        ]
    rw [heq]
    exact hmul
  exact ⟨hflux, hdef, hcross⟩

/-- The full selected diffusion-column expansion with its local regularity
derived from the flow and corrector definitions. -/
theorem diffusionMatrix_selected_corrector_column_divergence_of_smooth
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (x : Vec 2) (κ : ℝ) (j : Fin 2)
    (hk : Odd k) (hxi : I.xiMK m k t ≠ 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    matDiv (fun y => diffusionMatrix I hΦ m κ t y *
      (1 + gradChiTilde I hΦ m κ k t y)) x j =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
        matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
  obtain ⟨hB, hD, hE⟩ :=
    CorrectorDiffusionRegularity.corrector_diffusion_columns_contDiff_one I hΦ m k t κ j
  let M := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  have hB' := (hB.differentiable (by norm_num) (M x)).hasFDerivAt
  have hD' := (hD.differentiable (by norm_num) x).hasFDerivAt
  have hE' := (hE.differentiable (by norm_num) x).hasFDerivAt
  exact diffusionMatrix_selected_corrector_column_divergence
    I hΦ m hm k t x κ j hk hxi hB' hD' hE' hdiv

end AVenhance.Infra.Section5
