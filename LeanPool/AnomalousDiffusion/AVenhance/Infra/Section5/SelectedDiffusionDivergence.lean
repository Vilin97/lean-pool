/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SelectedCorrectorDivergence

/-! Divergence expansion for the four selected pieces of the ansatz flux. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- If the pointwise selected-gradient decomposition holds, its divergence is
the sum of the selected corrector flux divergence and the three remaining
flux divergences. Regularity is stated only at the evaluation point. -/
theorem selected_ansatz_diffusion_divergence
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (S : Finset {k : ℤ // Odd k})
    (hxi : ∀ q ∈ S, I.xiMK m q.1 t ≠ 0)
    (hB : ∀ q ∈ S, ∀ i j,
      HasFDerivAt (fun y => correctorFlux I hΦ m κ q.1 t y i j)
        (fderiv ℝ (fun y => correctorFlux I hΦ m κ q.1 t y i j) x) x)
    (hG : ∀ q ∈ S,
      HasFDerivAt (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y)
        (fderiv ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x) x)
    {LM LC LH : Vec 2 →L[ℝ] Vec 2}
    (hM : HasFDerivAt (fun y =>
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y -
          ∑ q ∈ S, I.xiMK m q.1 t •
            G I hΦ m T (lIdx β I.Λ m q.1) t y)) LM x)
    (hC : HasFDerivAt (fun y =>
      ∑ q ∈ S, I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κ t y).mulVec
          (chiGradG I hΦ m κ T q.1 t y)) LC x)
    (hH : HasFDerivAt (fun y =>
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.Hm hΦ m κ T t) y)) LH x)
    (hflux : ∀ y,
      (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (I.ansatz hΦ m κ T t) y) =
        (∑ q ∈ S, I.xiMK m q.1 t •
          (correctorFlux I hΦ m κ q.1 t y).mulVec
            (G I hΦ m T (lIdx β I.Λ m q.1) t y)) +
        (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (T t) y -
            ∑ q ∈ S, I.xiMK m q.1 t •
              G I hΦ m T (lIdx β I.Λ m q.1) t y) +
        (∑ q ∈ S, I.xiMK m q.1 t •
          (diffusionMatrix I hΦ m κ t y).mulVec
            (chiGradG I hΦ m κ T q.1 t y)) +
        (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (I.Hm hΦ m κ T t) y)) :
    vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.ansatz hΦ m κ T t) y)) x =
      (∑ q ∈ S, I.xiMK m q.1 t *
        (vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          frob (correctorFlux I hΦ m κ q.1 t x)
            (gradMatrix (G I hΦ m T (lIdx β I.Λ m q.1) t) x) +
          vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x))) +
      vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y -
          ∑ q ∈ S, I.xiMK m q.1 t •
            G I hΦ m T (lIdx β I.Λ m q.1) t y)) x +
      vecDiv (fun y => ∑ q ∈ S, I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κ t y).mulVec
          (chiGradG I hΦ m κ T q.1 t y)) x +
      vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.Hm hΦ m κ T t) y)) x := by
  classical
  let F : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun q y =>
    (correctorFlux I hΦ m κ q.1 t y).mulVec
      (G I hΦ m T (lIdx β I.Λ m q.1) t y)
  let Selected : Vec 2 → Vec 2 := fun y =>
    ∑ q ∈ S, I.xiMK m q.1 t • F q y
  let Mismatch : Vec 2 → Vec 2 := fun y =>
    (diffusionMatrix I hΦ m κ t y).mulVec
      (spaceGrad (T t) y -
        ∑ q ∈ S, I.xiMK m q.1 t •
          G I hΦ m T (lIdx β I.Λ m q.1) t y)
  let ChiTerm : Vec 2 → Vec 2 := fun y =>
    ∑ q ∈ S, I.xiMK m q.1 t •
      (diffusionMatrix I hΦ m κ t y).mulVec
        (chiGradG I hΦ m κ T q.1 t y)
  let HmTerm : Vec 2 → Vec 2 := fun y =>
    (diffusionMatrix I hΦ m κ t y).mulVec
      (spaceGrad (I.Hm hΦ m κ T t) y)
  let LF : {k : ℤ // Odd k} → Vec 2 →L[ℝ] Vec 2 := fun q =>
    ContinuousLinearMap.pi fun i =>
      ∑ j : Fin 2, (
        (G I hΦ m T (lIdx β I.Λ m q.1) t x j) •
            (fderiv ℝ (fun y => correctorFlux I hΦ m κ q.1 t y i j) x) +
          (correctorFlux I hΦ m κ q.1 t x i j) •
            ((ContinuousLinearMap.proj j).comp
              (fderiv ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x)))
  have hF : ∀ q ∈ S, HasFDerivAt (F q) (LF q) x := by
    intro q hq
    simpa [F, LF] using hasFDerivAt_matrix_mulVec (hB q hq) (hG q hq)
  let LSum : Vec 2 →L[ℝ] Vec 2 := ∑ q ∈ S, I.xiMK m q.1 t • LF q
  have hSum : HasFDerivAt
      (fun y => ∑ q ∈ S, I.xiMK m q.1 t • F q y) LSum x := by
    dsimp [LSum]
    have hfun : (fun y => ∑ q ∈ S, I.xiMK m q.1 t • F q y) =
        ∑ q ∈ S, (fun y => I.xiMK m q.1 t • F q y) := by
      funext y
      simp
    rw [hfun]
    apply HasFDerivAt.sum
    intro q hq
    exact (hF q hq).const_smul (I.xiMK m q.1 t)
  have hleft := selected_corrector_flux_sum_divergence I hΦ m hm κ T t x
    S hxi hB hG
  have hsum1 := vecDiv_add_of_hasFDerivAt hSum hM
  have hsum2 := vecDiv_add_of_hasFDerivAt (hSum.add hM) hC
  have hsum3 := vecDiv_add_of_hasFDerivAt ((hSum.add hM).add hC) hH
  have hsplit : (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
      (spaceGrad (I.ansatz hΦ m κ T t) y)) =
      (fun y => ((Selected y + Mismatch y) + ChiTerm y) + HmTerm y) := by
    funext y
    simpa [F, Selected, Mismatch, ChiTerm, HmTerm] using hflux y
  have hsum3' : vecDiv (fun y => ((Selected y + Mismatch y) +
      ChiTerm y) + HmTerm y) x =
      vecDiv (fun y => (Selected y + Mismatch y) + ChiTerm y) x +
        vecDiv HmTerm x := by
    convert hsum3 using 1
  have hsum2' : vecDiv (fun y => (Selected y + Mismatch y) +
      ChiTerm y) x =
      vecDiv (fun y => Selected y + Mismatch y) x + vecDiv ChiTerm x := by
    convert hsum2 using 1
  have hsum1' : vecDiv (fun y => Selected y + Mismatch y) x =
      vecDiv Selected x + vecDiv Mismatch x := by
    convert hsum1 using 1
  have hleft' : vecDiv Selected x =
      ∑ q ∈ S, I.xiMK m q.1 t *
        (vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          frob (correctorFlux I hΦ m κ q.1 t x)
            (gradMatrix (G I hΦ m T (lIdx β I.Λ m q.1) t) x) +
          vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x)) := by
    simpa [Selected, F] using hleft
  rw [hsplit]
  calc
    _ = (vecDiv Selected x + vecDiv Mismatch x) +
        vecDiv ChiTerm x + vecDiv HmTerm x := by
          calc
            _ = vecDiv (fun y => (Selected y + Mismatch y) +
                ChiTerm y) x + vecDiv HmTerm x := hsum3'
            _ = (vecDiv (fun y => Selected y + Mismatch y) x +
                vecDiv ChiTerm x) + vecDiv HmTerm x := by rw [hsum2']
            _ = _ := by rw [hsum1']
    _ = _ := by rw [hleft']

end AVenhance.Infra.Section5
