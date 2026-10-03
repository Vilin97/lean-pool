/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsAnalytic

/-! Concrete differentiated coefficient-gradient products in the four slow
factors. Matrix rows are derivative coordinates, as in the gradMatrix. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

/-- Component of Q grad T, with the derivative-row matrix convention. -/
def slowFactorG (Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (T : Vec 2 → ℝ)
    (j : Fin 2) : Vec 2 → ℝ := ∑ k : Fin 2, (fun x => Q x j k) * amnrSpaceWord [k] T

/-- The (i,j) entry of grad(Q grad T). -/
def slowFactorH (Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (T : Vec 2 → ℝ)
    (i j : Fin 2) : Vec 2 → ℝ := amnrSpaceWord [i] (slowFactorG Q T j)

/-- Component of the divergence of B grad T. -/
def slowFactorDiv (B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (T : Vec 2 → ℝ) :
    Vec 2 → ℝ := ∑ j : Fin 2, amnrSpaceWord [j] (slowFactorG B T j)

/-- Component of grad div(B grad T), whose T factor always has positive order. -/
def slowFactorGradDiv (B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (T : Vec 2 → ℝ)
    (i : Fin 2) : Vec 2 → ℝ := amnrSpaceWord [i] (slowFactorDiv B T)

/-- Q grad T is analytic in the averaged norm from positive T jets alone. -/
theorem slowFactorG_word_bound {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {T : Vec 2 → ℝ} (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j))
    (hT : ContDiff ℝ ∞ T) {CQ M L : ℝ}
    (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hL : 0 ≤ L) (μ : Measure (Vec 2))
    (hQb : ∀ i j w x, |amnrSpaceWord w (fun y => Q y i j) x| ≤
      CQ * w.length.factorial * L ^ w.length)
    (hTb : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) 2 μ ≤
      ENNReal.ofReal (M * w.length.factorial * L ^ w.length)) (j : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorG Q T j)) 2 μ ≤
      ENNReal.ofReal ((4 * CQ * M * L) * w.length.factorial * (4 * L) ^ w.length) := by
  have hrate : L ≤ 2 * L := by linarith only [hL]
  have hgb (k : Fin 2) (v : List (Fin 2)) :
      eLpNorm (amnrSpaceWord v (amnrSpaceWord [k] T)) 2 μ ≤
      ENNReal.ofReal ((2 * M * L) * v.length.factorial * (2 * L) ^ v.length) := by
    have hh := slowFactor_positive_temperature_shift hM hL 2 μ hTb [k] (by simp) v
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.factorial_one,
      Nat.cast_one, pow_one, mul_one]
    exact le_of_eq (by ring)
  have hprod (k : Fin 2) (v : List (Fin 2)) := slowFactor_word_mul_eLpNorm_le
    (hQ j k) (slowWord_smooth hT [k]) hCQ (by positivity : 0 ≤ 2 * M * L)
    (by positivity : 0 ≤ 2 * L) (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ
    (fun a x => (hQb j k a x).trans (slowFactor_rate_mono hCQ hL hrate _)) (hgb k) v
  have hh := slowFactor_sum_eLpNorm_le Finset.univ
    (fun k : Fin 2 => (fun x => Q x j k) * amnrSpaceWord [k] T)
    (fun k _ => (hQ j k).mul (slowWord_smooth hT [k]))
    (F := CQ * (2 * M * L)) (L := 2 * (2 * L)) (by norm_num) μ
    (fun k _ v => hprod k v) w
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  exact le_of_eq (by ring)

theorem slowFactorG_smooth {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (hT : ContDiff ℝ ∞ T) (j : Fin 2) :
    ContDiff ℝ ∞ (slowFactorG Q T j) := by
  have hh := ContDiff.sum (s := Finset.univ) (fun k _ => (hQ j k).mul (slowWord_smooth hT [k]))
  convert hh using 1
  funext x
  simp only [slowFactorG, Finset.sum_apply, Pi.mul_apply]

/-- Actual all-order Hessian-factor bound, including its order-zero case. -/
theorem slowFactorH_word_bound {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {T : Vec 2 → ℝ} (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j))
    (hT : ContDiff ℝ ∞ T) {CQ M L : ℝ}
    (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hL : 0 ≤ L) (μ : Measure (Vec 2))
    (hQb : ∀ i j w x, |amnrSpaceWord w (fun y => Q y i j) x| ≤
      CQ * w.length.factorial * L ^ w.length)
    (hTb : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) 2 μ ≤
      ENNReal.ofReal (M * w.length.factorial * L ^ w.length)) (i j : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorH Q T i j)) 2 μ ≤
      ENNReal.ofReal ((32 * CQ * M * L ^ 2) * w.length.factorial * (8 * L) ^ w.length) := by
  have hh := slowFactor_word_shift_eLpNorm_le (by positivity : 0 ≤ 4 * CQ * M * L)
    (by positivity : 0 ≤ 4 * L) 2 μ
    (slowFactorG_word_bound hQ hT hCQ hM hL μ hQb hTb j) [i] w
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.factorial_one,
    Nat.cast_one, pow_one, mul_one]
  exact le_of_eq (by ring)

/-- The differentiated divergence needs no zeroth T estimate. -/
theorem slowFactorGradDiv_word_bound {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {T : Vec 2 → ℝ} (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j))
    (hT : ContDiff ℝ ∞ T) {CB M L : ℝ}
    (hCB : 0 ≤ CB) (hM : 0 ≤ M) (hL : 0 ≤ L) (μ : Measure (Vec 2))
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => B y i j) x| ≤
      CB * w.length.factorial * L ^ w.length)
    (hTb : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) 2 μ ≤
      ENNReal.ofReal (M * w.length.factorial * L ^ w.length)) (i : Fin 2) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (slowFactorGradDiv B T i)) 2 μ ≤
      ENNReal.ofReal ((1024 * CB * M * L ^ 3) * w.length.factorial * (8 * L) ^ w.length) := by
  have he : slowFactorGradDiv B T i =
      ∑ j : Fin 2, amnrSpaceWord [i, j] (slowFactorG B T j) := by
    unfold slowFactorGradDiv slowFactorDiv
    rw [slowWord_sum Finset.univ _ (fun j _ => slowWord_smooth (slowFactorG_smooth hB hT j) [j])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← amnrSpaceWord_append]
    rfl
  have hshift (j : Fin 2) (v : List (Fin 2)) :=
    slowFactor_word_shift_eLpNorm_le (by positivity : 0 ≤ 4 * CB * M * L)
      (by positivity : 0 ≤ 4 * L) 2 μ
      (slowFactorG_word_bound hB hT hCB hM hL μ hBb hTb j) [i, j] v
  have hs (j : Fin 2) (v : List (Fin 2)) :
      eLpNorm (amnrSpaceWord v (amnrSpaceWord [i, j] (slowFactorG B T j))) 2 μ ≤
      ENNReal.ofReal ((512 * CB * M * L ^ 3) * v.length.factorial * (8 * L) ^ v.length) := by
    apply (hshift j v).trans
    apply ENNReal.ofReal_le_ofReal
    norm_num only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
      Nat.factorial, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  rw [he]
  have hh := slowFactor_sum_eLpNorm_le Finset.univ
    (fun j : Fin 2 => amnrSpaceWord [i, j] (slowFactorG B T j))
    (fun j _ => slowWord_smooth (slowFactorG_smooth hB hT j) [i, j])
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) μ (fun j _ v => hs j v) w
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  exact le_of_eq (by ring)

end AVenhance.Infra.Section5
