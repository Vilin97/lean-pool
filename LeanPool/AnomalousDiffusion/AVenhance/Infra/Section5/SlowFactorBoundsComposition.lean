/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsChoices

/-! Proved composed analytic inputs for all four slow factors. The order-zero
bound is obtained from the same positive-T-jet calculation as every other order. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

theorem slowFactor_sum_smooth {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ (∑ i ∈ s, f i) := by
  convert ContDiff.sum hf using 1
  funext x
  simp only [Finset.sum_apply]

theorem slowFactorH_smooth {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (hT : ContDiff ℝ ∞ T) (i j : Fin 2) :
    ContDiff ℝ ∞ (slowFactorH Q T i j) := slowWord_smooth (slowFactorG_smooth hQ hT j) [i]

theorem slowFactorGradDiv_smooth {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) (hT : ContDiff ℝ ∞ T) (i : Fin 2) :
    ContDiff ℝ ∞ (slowFactorGradDiv B T i) :=
  slowWord_smooth (slowFactor_sum_smooth Finset.univ _
    (fun j _ => slowWord_smooth (slowFactorG_smooth hB hT j) [j])) [i]

theorem slowFactorContractH_smooth {A Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (hT : ContDiff ℝ ∞ T) (a j : Fin 2) :
    ContDiff ℝ ∞ (slowFactorContractH A Q T a j) :=
  slowFactor_sum_smooth Finset.univ _ (fun i _ => (hA i a).mul (slowFactorH_smooth hQ hT i j))

section Composed
variable (X : PeriodicVolumePreservingDiffeomorphism 2)
variable {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
variable (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (hT : ContDiff ℝ ∞ T)
variable {CQ M L CX R : ℝ} (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hL : 0 < L)
variable (hCX : 0 < CX) (hR : 0 < R)
variable (hQb : ∀ i j w x, |amnrSpaceWord w (fun y => Q y i j) x| ≤
  CQ * w.length.factorial * L ^ w.length)
variable (hTb : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) 2
  (volume.restrict (unitCell 2)) ≤ ENNReal.ofReal (M * w.length.factorial * L ^ w.length))
variable (hXb : ∀ n (w : Fin n → Fin 2), 0 < n → ∀ x j,
  |(spatialJet n X.toFun w x) j| ≤ CX * n.factorial * R ^ n)
include hQ hT hCQ hM hL hCX hR hQb hTb hXb

theorem slowFactorChoice1_composed_bounds {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) {CB ξ : ℝ}
    (hCB : 0 ≤ CB) (hξ : |ξ| ≤ 1)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => B y i j) x| ≤
      CB * w.length.factorial * L ^ w.length) (j : Fin 2)
    (hper : IsZPeriodic (slowFactorChoice1 ξ Q B T j)) :
    HasCoordinateAnalyticL2Bounds (fun x => (slowFactorChoice1 ξ Q B T j (X.toFun x) : ℂ))
      (2048 * CQ * CB * M * L ^ 3)
      ((16 * L)⁻¹ / (R * ((16 * L)⁻¹ + 2 * CX))) := by
  have hs : ContDiff ℝ ∞ (slowFactorChoice1 ξ Q B T j) :=
    (slowFactor_sum_smooth Finset.univ _
      (fun i _ => (hQ j i).mul (slowFactorGradDiv_smooth hB hT i))).const_smul ξ
  exact slowFactor_hasCoordinateAnalyticL2Bounds_comp X hs hper (by positivity)
    (by positivity) hCX hR
    (slowFactorChoice1_word_bound hQ hT hCQ hM hL.le _ hQb hTb hB hCB hξ hBb j) hXb

theorem slowFactorChoice3_composed_bounds {Y : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hY : ∀ i j, ContDiff ℝ ∞ (fun x => Y x i j)) {CY ξ : ℝ}
    (hCY : 0 ≤ CY) (hξ : |ξ| ≤ 1)
    (hYb : ∀ i j w x, |amnrSpaceWord w (fun y => Y y i j) x| ≤
      CY * w.length.factorial * L ^ w.length) (a j : Fin 2)
    (hper : IsZPeriodic (slowFactorChoice3 ξ Y Q T a j)) :
    HasCoordinateAnalyticL2Bounds (fun x => (slowFactorChoice3 ξ Y Q T a j (X.toFun x) : ℂ))
      (64 * CY * CQ * M * L ^ 2)
      ((16 * L)⁻¹ / (R * ((16 * L)⁻¹ + 2 * CX))) := by
  have hs := (slowFactorContractH_smooth hY hQ hT a j).const_smul ξ
  exact slowFactor_hasCoordinateAnalyticL2Bounds_comp X hs hper (by positivity)
    (by positivity) hCX hR
    (slowFactorChoice3_word_bound hQ hT hCQ hM hL.le _ hQb hTb hY hCY hξ hYb a j) hXb

end Composed
end AVenhance.Infra.Section5
