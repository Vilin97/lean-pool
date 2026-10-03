/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualCoordinateNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIndependentCoordinateNorms

/-! # Iterates Actual Independent Norms

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual positive-increment estimate with independently chosen coordinate
words, as required by the paper's separate maxima. -/
theorem iterate_actual_independent_coordinate_norms_of_scales {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {Ccoef Cs C C₀ N B r L D Bflow ρ F : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvel : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (hD : 0 ≤ D) (hCs : 0 ≤ Cs) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hρ : 0 < ρ) (hρq : ρ ≤ ρ * F ^ 2)
    (hC₀ : 1 ≤ C₀) (hF : C₀ ≤ F) (hlarge : 32 * C ≤ C₀)
    (hsmall : C₀ * (ρ * F ^ 2) ≤ 1)
    (hQ : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hscale : D * L ^ 2 ≤ Cs * (ρ * F ^ 2))
    (hvelocity : (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹) ≤ Cs * κprev * L ^ 2)
    (hBr : B * r = (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹))
    (hjet : ∀ t x (p : List (Fin 2)), 1 ≤ p.length → ∀ j,
      |iterateSpatialWord p (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
        B * (p.length.factorial : ℝ) * r ^ p.length)
    (hFlowBound : ∀ t x j k, |gradMatrix (streamVel (Φ (m - 1)) t) x j k| ≤ Bflow)
    (hFlowScale : D * Bflow ≤ Cs * κprev * ρ)
    (hcoef : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * (p.length.factorial : ℝ) * r ^ p.length)
    (hrem : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * ρ * (p.length.factorial : ℝ) * r ^ p.length)
    (hbase : iterateCoordinateEnergyProfile θprev κprev N L 0)
    (hmat : 24 * amnrMaterialMajorantConstant Ccoef Cs Cs Cs ≤ C)
    (hfirst : 24 * (iterateFirstMaterialCoefficient Cs Ccoef + 384 * Cs ^ 2 + 32 * Ccoef ^ 2) ≤ C)
    (hu : (24 * (2 * ((2 : ℝ) ^ 19 * a β I.Λ (m - 1)) / L ^ 2)) / κprev ≤ C / F ^ 2)
    (hv : (24 * (16 / κprev * (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) ^ 2 *
      (2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2) ^ 2)) / κprev ≤ C / F ^ 4)
    (hc : (24 * (8 * D * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹))) / κprev ≤ C * ρ) :
    ∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2), v.length = w.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) + Real.sqrt κprev *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement
            T i t)))) ≤
      N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i * iterateAnalyticWeight v.length i L := by
  have hn := iterate_actual_coordinate_norm_of_scales I hΦ hT hθ hm hκm hκ hflow hflowp hA3 hL hg
      hvel hD hCs hC hN hB hr hρ hρq hC₀ hF hlarge hsmall hQ hscale hvelocity hBr hjet hFlowBound
      hFlowScale hcoef hrem hbase hmat hfirst hu hv hc
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hFp : 0 < F := hp.trans_le hF
  have hη := mul_pos hp (mul_pos hρ (sq_pos_of_pos hFp))
  intro i hi0 hi v w hvw s hs hs1
  have he (p : List (Fin 2)) : 0 ≤ l2NormSq (iterateSpatialWord p (iterateIncrement T i s)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hg (p : List (Fin 2)) : 0 ≤ spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T i t))) := by
    apply integral_nonneg
    intro z
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hev := (iterate_norm_sq_components (he v) (hg v) hκ.le (hn i hi0 hi v s hs hs1)).1
  have hgw := (iterate_norm_sq_components (he w) (hg w) hκ.le (hn i hi0 hi w s hs hs1)).2
  rw [← hvw] at hgw
  apply iterate_independent_coordinate_norms (he v) (hg w) hκ.le
    (mul_nonneg (mul_nonneg hN (iterateAmplitude_pos hη i).le)
      (iterateAnalyticWeight_nonneg _ _ hL.le))
  · convert hev using 1
    ring
  · convert hgw using 1
    ring

end AVenhance.Infra.Section4
