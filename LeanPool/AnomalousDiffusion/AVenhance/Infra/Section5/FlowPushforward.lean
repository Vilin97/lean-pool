/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaIdentity

/-! Corrected inverse-flow push-forward decomposition for divergence, followed
by its corrector specialization. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

theorem FlowPushforward.vecDiv_eq_fderiv
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

/-- Adding complementary matrix coefficients splits the divergence exactly.
This is the algebraic step behind the corrected `e.pushforward` formula. -/
theorem vecDiv_matrix_identity_split
    {V : Vec 2 → Vec 2} {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {x : Vec 2} {LV : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hV : HasFDerivAt V LV x)
    (hQ : ∀ i j, HasFDerivAt (fun y => Q y i j) (LQ i j) x) :
    vecDiv V x =
      vecDiv (fun y => (Q y).mulVec (V y)) x +
      vecDiv (fun y => (1 - Q y).mulVec (V y)) x := by
  let LC : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ := fun i j => -LQ i j
  have hC : ∀ i j, HasFDerivAt (fun y => (1 - Q y) i j) (LC i j) x := by
    intro i j
    have hfun : (fun y => (1 - Q y) i j) =
        (fun y => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) -
          (fun y => Q y i j) := by
      funext y
      rfl
    have h := (hasFDerivAt_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j) x).sub
      (hQ i j)
    rw [hfun]
    simpa [LC] using h
  have hdivV := FlowPushforward.vecDiv_eq_fderiv hV
  have hdivQ := vecDiv_matrixMulVec hQ hV
  have hdivC := vecDiv_matrixMulVec hC hV
  have hdiag (i : Fin 2) (D : Fin 2 → Fin 2 → ℝ) :
      ∑ j : Fin 2, (if i = j then 1 else 0) * D i j = D i i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp
  calc
    vecDiv V x = ∑ i : Fin 2, (LV (basisVec i)) i := hdivV
    _ =
      (∑ i : Fin 2, ∑ j : Fin 2,
        ((LQ i j) (basisVec i) * V x j +
          Q x i j * (LV (basisVec i)) j)) +
      (∑ i : Fin 2, ∑ j : Fin 2,
        ((LC i j) (basisVec i) * V x j +
          (1 - Q x) i j * (LV (basisVec i)) j)) := by
        symm
        calc
          (∑ i : Fin 2, ∑ j : Fin 2,
            ((LQ i j) (basisVec i) * V x j +
              Q x i j * (LV (basisVec i)) j)) +
          (∑ i : Fin 2, ∑ j : Fin 2,
            ((LC i j) (basisVec i) * V x j +
              (1 - Q x) i j * (LV (basisVec i)) j)) =
              ∑ i : Fin 2, ∑ j : Fin 2,
                ((if i = j then 1 else 0) * (LV (basisVec i)) j) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j hj
                  simp only [LC, Matrix.sub_apply, neg_apply, Matrix.one_apply]
                  ring
          _ = ∑ i : Fin 2, (LV (basisVec i)) i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hdiag i (fun i j => (LV (basisVec i)) j)
          _ = ∑ i : Fin 2, (LV (basisVec i)) i := rfl
    _ = vecDiv (fun y => (Q y).mulVec (V y)) x +
        vecDiv (fun y => (1 - Q y).mulVec (V y)) x := by
          rw [hdivQ, hdivC]

/-- Corrected push-forward decomposition: the Piola term is the pulled-back
source divergence, and the complementary Jacobian coefficient remains as a
separate divergence. -/
theorem vecDiv_comp_eq_pulledDiv_add_correction
    {M g : Vec 2 → Vec 2} {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {x : Vec 2} {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt M LM x)
    (hg : HasFDerivAt g Lg (M x))
    (hQ : ∀ i j, HasFDerivAt (fun y => Q y i j) (LQ i j) x)
    (hPiola : vecDiv (fun y => (Q y).mulVec (g (M y))) x =
      vecDiv g (M x)) :
    vecDiv (fun y => g (M y)) x = vecDiv g (M x) +
      vecDiv (fun y => (1 - Q y).mulVec (g (M y))) x := by
  have hcomp : HasFDerivAt (fun y => g (M y)) (Lg.comp LM) x := hg.comp x hM
  have hsplit := vecDiv_matrix_identity_split hcomp hQ
  calc
    vecDiv (fun y => g (M y)) x =
        vecDiv (fun y => (Q y).mulVec (g (M y))) x +
          vecDiv (fun y => (1 - Q y).mulVec (g (M y))) x := hsplit
    _ = vecDiv g (M x) +
        vecDiv (fun y => (1 - Q y).mulVec (g (M y))) x := by rw [hPiola]

/-- inverse-flow version with the coordinate Piola premise stated
explicitly. The Jacobian correction has the transposed row-Jacobian orientation
required by the matrix convention. -/
theorem xFlowInv_cofactor_pushforward_split
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    {g : Vec 2 → Vec 2} {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt (I.xFlowInv hΦ m l t) LM x)
    (hg : HasFDerivAt g Lg (I.xFlowInv hΦ m l t x))
    (hQ : ∀ i j, HasFDerivAt
      (fun y => rowCofactor (gradMatrix (I.xFlowInv hΦ m l t) y) i j)
      (LQ i j) x)
    (hPiolaDiv : ∀ j : Fin 2,
      ∑ i : Fin 2, (LQ i j) (basisVec i) = 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    vecDiv (fun y => g (I.xFlowInv hΦ m l t y)) x =
      vecDiv g (I.xFlowInv hΦ m l t x) +
        vecDiv (fun y =>
          (1 - rowCofactor (gradMatrix (I.xFlowInv hΦ m l t) y)).mulVec
            (g (I.xFlowInv hΦ m l t y))) x := by
  apply vecDiv_comp_eq_pulledDiv_add_correction hM hg hQ
  exact xFlowInv_cofactorPiola I hΦ m l t x hM hg hQ hPiolaDiv hdiv

/-- Source corrector push-forward identity with its local corrector equation
substituted. The remaining Piola divergence is explicit as in the flow bridge. -/
theorem xFlowInv_corrector_pushforward
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2) (κ : ℝ)
    (j : Fin 2) {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) LM x)
    (hg : HasFDerivAt (frozenCorrectorFlux I κ m k j t) Lg
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (hQ : ∀ i q, HasFDerivAt (fun y => rowCofactor
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i q)
      (LQ i q) x)
    (hPiolaDiv : ∀ q,
      ∑ i : Fin 2, (LQ i q) (basisVec i) = 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    vecDiv (fun y => frozenCorrectorFlux I κ m k j t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) x =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        vecDiv (fun y =>
          (1 - rowCofactor (gradMatrix
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
            (frozenCorrectorFlux I κ m k j t
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) x := by
  have hsplit := xFlowInv_cofactor_pushforward_split I hΦ m
    (lIdx β I.Λ m k) t x hM hg hQ hPiolaDiv hdiv
  rw [frozenCorrectorFlux_vecDiv] at hsplit
  exact hsplit

/-- Rewrite the cofactor correction in `xFlowInv_corrector_pushforward` using
the corrected transpose of the forward row-Jacobian. -/
theorem xFlowInv_corrector_pushforward_flowGrad
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2) (κ : ℝ)
    (j : Fin 2) {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) LM x)
    (hg : HasFDerivAt (frozenCorrectorFlux I κ m k j t) Lg
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (hQ : ∀ i q, HasFDerivAt (fun y => rowCofactor
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i q)
      (LQ i q) x)
    (hPiolaDiv : ∀ q,
      ∑ i : Fin 2, (LQ i q) (basisVec i) = 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    vecDiv (fun y => frozenCorrectorFlux I κ m k j t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) x =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        vecDiv (fun y =>
          (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose).mulVec
            (frozenCorrectorFlux I κ m k j t
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) x := by
  have hbase := xFlowInv_corrector_pushforward I hΦ m k t x κ j
    hM hg hQ hPiolaDiv hdiv
  have hcoef : ∀ y, rowCofactor
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) =
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose := by
    intro y
    exact xFlowInv_rowCofactor_eq_flowGrad_transpose I hΦ m
      (lIdx β I.Λ m k) t y hdiv
  have hcorrection :
      (fun y => (1 - rowCofactor
        (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
        (frozenCorrectorFlux I κ m k j t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) =
      (fun y => (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose).mulVec
        (frozenCorrectorFlux I κ m k j t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) := by
    funext y
    rw [hcoef y]
  rw [hcorrection] at hbase
  exact hbase

end AVenhance.Infra.Section5
