/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientIdentity

/-! Quantitative mixed jets for a two-dimensional matrix product. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Addition commutes with finite smoothness words at every point of an open
set. This upstream version lets coefficient estimates stay below the flux
modules in the import graph. -/
theorem amnrWord_add_contDiffOn {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    Set.EqOn (amnrWord b w (f + g)) (amnrWord b w f + amnrWord b w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons d w ih =>
    have hwN : w.length ≤ N := by simp only [List.length_cons] at hw; omega
    intro z hz
    have hnear := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hwN hy)
    have hf' := (amnrWord_contDiffOn hU hb hf w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    have hg' := (amnrWord_contDiffOn hU hb hg w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    unfold amnrWord amnrOp
    rw [hnear.fderiv_eq, fderiv_add (hf'.differentiableAt (by norm_num))
      (hg'.differentiableAt (by norm_num))]
    rfl

/-- A finite matrix contraction preserves the weighted mixed budget. This
conditional calculus helper accounts for all product-rule terms explicitly. -/
theorem amnr_matrix_product_sub_const_word_bound
    {b : AmnrSpace → Vec 2} {N : ℕ} {K G : Fin 2 → AmnrSpace → ℝ}
    (hb : ContDiff ℝ N b) (hK : ∀ p, ContDiff ℝ N (K p))
    (hG : ∀ p, ContDiff ℝ N (G p))
    {S H A B d : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    (hKb : ∀ p v, v.Sublist w → ∀ z,
      |amnrWord b v (K p) z| ≤ A * amnrWeight S H v)
    (hGb : ∀ p v, v.Sublist w → ∀ z,
      |amnrWord b v (G p) z| ≤ B * amnrWeight S H v) (z : AmnrSpace) :
    |amnrWord b w (fun y => (∑ p : Fin 2, K p y * G p y) - d) z| ≤
      (2 * (2 : ℝ) ^ N * A * B + |d|) * amnrWeight S H w := by
  classical
  let f : AmnrSpace → ℝ := ∑ p : Fin 2, K p * G p
  have hf : ContDiff ℝ N f := by
    change ContDiff ℝ N (fun y => ∑ p : Fin 2, K p y * G p y)
    exact ContDiff.sum (s := Finset.univ) (fun p _ => (hK p).mul (hG p))
  have hlen := (amnrBudget_length_le w).trans hw
  have he : (fun y => (∑ p : Fin 2, K p y * G p y) - d) = f - (fun _ => d) := by
    funext y
    simp only [f, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
  rw [he, amnrWord_sub isOpen_univ hb.contDiffOn hf.contDiffOn contDiffOn_const w hlen (mem_univ z)]
  have hsum := amnrWord_sum isOpen_univ hb.contDiffOn Finset.univ
    (fun p => K p * G p) (fun p _ => ((hK p).mul (hG p)).contDiffOn) w hlen (mem_univ z)
  have hprod (p : Fin 2) : |amnrWord b w (K p * G p) z| ≤
      (2 : ℝ) ^ N * A * B * amnrWeight S H w := by
    have hh := amnrWord_mul_abs_le isOpen_univ hb.contDiffOn (hK p).contDiffOn
      (hG p).contDiffOn hS hH hA hB w hw
      (fun v hv y _ => hKb p v hv y) (fun v hv y _ => hGb p v hv y) (mem_univ z)
    refine hh.trans ?_
    have hp : (2 : ℝ) ^ w.length ≤ (2 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) hlen
    gcongr
    exact amnrWeight_nonneg hS hH w
  have hs : |amnrWord b w f z| ≤ 2 * (2 : ℝ) ^ N * A * B * amnrWeight S H w := by
    rw [hsum]
    change |∑ p : Fin 2, amnrWord b w (K p * G p) z| ≤ _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hh := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin 2))) => hprod p)
    refine hh.trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hd : |amnrWord b w (fun _ => d) z| ≤ |d| * amnrWeight S H w := by
    rw [amnrWord_const]
    by_cases hnil : w = []
    · subst w; simp [amnrWeight]
    · simp only [hnil, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact mul_nonneg (abs_nonneg d) (amnrWeight_nonneg hS hH w)
  exact (abs_sub _ _).trans ((add_le_add hs hd).trans_eq (by ring))

/-- A two-by-two contraction with two indexed factors costs one Leibniz
factor per contracted row. -/
theorem amnr_matrix_double_product_word_bound
    {b : AmnrSpace → Vec 2} {N : ℕ}
    {P H : Fin 2 → Fin 2 → AmnrSpace → ℝ}
    (hb : ContDiff ℝ N b)
    (hP : ∀ i p, ContDiff ℝ N (P i p))
    (hH : ∀ i p, ContDiff ℝ N (H i p))
    {S T A B : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    (hPb : ∀ i p v, v.Sublist w → ∀ z,
      |amnrWord b v (P i p) z| ≤ A * amnrWeight S T v)
    (hHb : ∀ i p v, v.Sublist w → ∀ z,
      |amnrWord b v (H i p) z| ≤ B * amnrWeight S T v)
    (z : AmnrSpace) :
    |amnrWord b w (fun y => ∑ i : Fin 2, ∑ p : Fin 2, P i p y * H i p y) z| ≤
      (4 * (2 : ℝ) ^ N * A * B) * amnrWeight S T w := by
  classical
  have hlen := (amnrBudget_length_le w).trans hw
  let row (i : Fin 2) : AmnrSpace → ℝ := fun y => ∑ p : Fin 2, P i p y * H i p y
  have hrowCont : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ContDiffOn ℝ N (row i) Set.univ := by
    intro i _
    change ContDiffOn ℝ N (fun y => ∑ p : Fin 2, P i p y * H i p y) Set.univ
    apply ContDiffOn.sum
    intro p _
    exact (hP i p).contDiffOn.mul (hH i p).contDiffOn
  have hsum : Set.EqOn (amnrWord b w (fun y => ∑ i : Fin 2, row i y))
      (∑ i : Fin 2, amnrWord b w (row i)) Set.univ :=
    amnrWord_sum isOpen_univ hb.contDiffOn Finset.univ row hrowCont w hlen
  have hrow (i : Fin 2) :
      |amnrWord b w (row i) z| ≤
        (2 * (2 : ℝ) ^ N * A * B) * amnrWeight S T w := by
    have hh := amnr_matrix_product_sub_const_word_bound (d := 0) hb
      (fun p => hP i p) (fun p => hH i p) hS hT hA hB w hw
      (fun p v hv y => hPb i p v hv y)
      (fun p v hv y => hHb i p v hv y) z
    simpa [row] using hh
  have hsumPoint := hsum (mem_univ z)
  rw [hsumPoint]
  calc
    |∑ i : Fin 2, amnrWord b w (row i) z| ≤
        ∑ i : Fin 2, |amnrWord b w (row i) z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 2, (2 * (2 : ℝ) ^ N * A * B) * amnrWeight S T w :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (4 * (2 : ℝ) ^ N * A * B) * amnrWeight S T w := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Subtracting a scalar constant adds its absolute size to a weighted word
bound; every nonempty word annihilates the constant. -/
theorem amnr_word_sub_const_abs_le
    {b : AmnrSpace → Vec 2} {N : ℕ} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ N b) (hf : ContDiff ℝ N f)
    {S T A c : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N) (z : AmnrSpace)
    (hbound : |amnrWord b w f z| ≤ A * amnrWeight S T w) :
    |amnrWord b w (fun y => f y - c) z| ≤
      (A + |c|) * amnrWeight S T w := by
  have hlen := (amnrBudget_length_le w).trans hw
  have hg : ContDiffOn ℝ N (fun _ : AmnrSpace => c) Set.univ := contDiffOn_const
  have heq := amnrWord_sub isOpen_univ hb.contDiffOn hf.contDiffOn hg
    w hlen (mem_univ z)
  change |amnrWord b w (f - fun _ => c) z| ≤ _
  rw [heq]
  have hconst : |amnrWord b w (fun _ => c) z| ≤
      |c| * amnrWeight S T w := by
    rw [amnrWord_const]
    by_cases hnil : w = []
    · subst w
      simp [amnrWeight]
    · simp only [hnil, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact mul_nonneg (abs_nonneg c) (amnrWeight_nonneg hS hT w)
  calc
    |amnrWord b w f z - amnrWord b w (fun _ => c) z| ≤
        |amnrWord b w f z| + |amnrWord b w (fun _ => c) z| := abs_sub _ _
    _ ≤ A * amnrWeight S T w + |c| * amnrWeight S T w :=
      add_le_add hbound hconst
    _ = _ := by ring

end AVenhance.Infra.Section4
