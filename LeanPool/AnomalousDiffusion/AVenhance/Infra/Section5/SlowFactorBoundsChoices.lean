/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsJets

/-! Component estimates for the four Appendix C slow factors, including order
zero. The matrix contractions follow the derivative-row convention. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

/-- Slow factor formed by contracting the flow matrix with the gradient-divergence term. -/
def slowFactorChoice1 (ξ : ℝ) (Q B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : Vec 2 → ℝ) (j : Fin 2) : Vec 2 → ℝ :=
  ξ • (∑ i : Fin 2, (fun x => Q x j i) * slowFactorGradDiv B T i)

/-- This is the contraction arising when matDiv differentiates a matrix
product: its i-th derivative pairs with the i-th row of A. -/
def slowFactorContractH (A Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : Vec 2 → ℝ) (a j : Fin 2) : Vec 2 → ℝ :=
  ∑ i : Fin 2, (fun x => A x i a) * slowFactorH Q T i j

/-- Slow factor formed by contracting the Hessian contribution with two matrix fields. -/
def slowFactorChoice2 (ξ κ : ℝ) (A Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : Vec 2 → ℝ) (a j : Fin 2) : Vec 2 → ℝ := ξ • (κ • slowFactorContractH A Q T a j)

/-- The actual corrected push-forward factor uses Y=1-Q.transpose. -/
def slowFactorChoice3 (ξ : ℝ) (Y Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : Vec 2 → ℝ) (a j : Fin 2) : Vec 2 → ℝ := ξ • slowFactorContractH Y Q T a j

section Bounds
variable {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
variable (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (hT : ContDiff ℝ ∞ T)
variable {CQ M L : ℝ} (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hL : 0 ≤ L)
variable (μ : Measure (Vec 2))
variable (hQb : ∀ i j w x, |amnrSpaceWord w (fun y => Q y i j) x| ≤
  CQ * w.length.factorial * L ^ w.length)
variable (hTb : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) 2 μ ≤
  ENNReal.ofReal (M * w.length.factorial * L ^ w.length))

include hQ hT hCQ hM hL hQb hTb

theorem slowFactorContractH_word_bound {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ i j w x, |amnrSpaceWord w (fun y => A y i j) x| ≤
      CA * w.length.factorial * L ^ w.length) (a j : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorContractH A Q T a j)) 2 μ ≤
      ENNReal.ofReal ((64 * CA * CQ * M * L ^ 2) * w.length.factorial * (16 * L) ^ w.length) := by
  have hrate : L ≤ 8 * L := by linarith only [hL]
  have hhprod (i : Fin 2) (v : List (Fin 2)) := slowFactor_word_mul_eLpNorm_le
    (hA i a) (slowWord_smooth (slowFactorG_smooth hQ hT j) [i]) hCA
    (by positivity : 0 ≤ 32 * CQ * M * L ^ 2) (by positivity : 0 ≤ 8 * L)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ
    (fun b x => (hAb i a b x).trans (slowFactor_rate_mono hCA hL hrate _))
    (slowFactorH_word_bound hQ hT hCQ hM hL μ hQb hTb i j) v
  have hh := slowFactor_sum_eLpNorm_le Finset.univ
    (fun i : Fin 2 => (fun x => A x i a) * slowFactorH Q T i j)
    (fun i _ => (hA i a).mul (slowWord_smooth (slowFactorG_smooth hQ hT j) [i]))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ (fun i _ v => hhprod i v) w
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  exact le_of_eq (by ring)

theorem slowFactorChoice1_word_bound {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) {CB ξ : ℝ}
    (hCB : 0 ≤ CB) (hξ : |ξ| ≤ 1)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => B y i j) x| ≤
      CB * w.length.factorial * L ^ w.length) (j : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorChoice1 ξ Q B T j)) 2 μ ≤
      ENNReal.ofReal ((2048 * CQ * CB * M * L ^ 3) * w.length.factorial * (16 * L) ^ w.length) := by
  have hDs (i : Fin 2) : ContDiff ℝ ∞ (slowFactorGradDiv B T i) := by
    apply slowWord_smooth _ [i]
    have hh := ContDiff.sum (s := Finset.univ)
      (fun j _ => slowWord_smooth (slowFactorG_smooth hB hT j) [j])
    convert hh using 1
    funext x
    simp only [slowFactorDiv, Finset.sum_apply]
  have hrate : L ≤ 8 * L := by linarith only [hL]
  have hprod (i : Fin 2) (v : List (Fin 2)) := slowFactor_word_mul_eLpNorm_le
    (hQ j i) (hDs i) hCQ (by positivity : 0 ≤ 1024 * CB * M * L ^ 3)
    (by positivity : 0 ≤ 8 * L) (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ
    (fun b x => (hQb j i b x).trans (slowFactor_rate_mono hCQ hL hrate _))
    (slowFactorGradDiv_word_bound hB hT hCB hM hL μ hBb hTb i) v
  have hs := slowFactor_sum_eLpNorm_le Finset.univ
    (fun i : Fin 2 => (fun x => Q x j i) * slowFactorGradDiv B T i)
    (fun i _ => (hQ j i).mul (hDs i)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ
    (fun i _ v => hprod i v)
  have hh := slowFactor_cutoff_eLpNorm_le hξ 2 μ hs w
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  exact le_of_eq (by ring)

theorem slowFactorChoice3_word_bound {Y : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hY : ∀ i j, ContDiff ℝ ∞ (fun x => Y x i j)) {CY ξ : ℝ}
    (hCY : 0 ≤ CY) (hξ : |ξ| ≤ 1)
    (hYb : ∀ i j w x, |amnrSpaceWord w (fun y => Y y i j) x| ≤
      CY * w.length.factorial * L ^ w.length) (a j : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorChoice3 ξ Y Q T a j)) 2 μ ≤
      ENNReal.ofReal ((64 * CY * CQ * M * L ^ 2) * w.length.factorial * (16 * L) ^ w.length) :=
  slowFactor_cutoff_eLpNorm_le hξ 2 μ
    (slowFactorContractH_word_bound hQ hT hCQ hM hL μ hQb hTb hY hCY hYb a j) w

end Bounds
end AVenhance.Infra.Section5
