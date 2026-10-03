/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityMaterialSum
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Quantitative finite-jet induction for derived flow-transport coefficients. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Every nonempty actual differential word annihilates a scalar constant. -/
theorem amnrWord_const {b : AmnrSpace → Vec 2} (w : List (Option (Fin 2))) (c : ℝ) :
    amnrWord b w (fun _ => c) = if w = [] then (fun _ => c) else (0 : AmnrSpace → ℝ) := by
  induction w with
  | nil => simp [amnrWord]
  | cons d w ih =>
    simp only [amnrWord, ih, List.cons_ne_nil, ↓reduceIte]
    split_ifs <;> funext z <;> simp [amnrOp]

/-- Addition commutes with actual ordered words when their smooth primitive
functions supply every intermediate derivative. -/
theorem amnrWord_add_global {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (w : List (Option (Fin 2))) :
    amnrWord b w (f + g) = amnrWord b w f + amnrWord b w g := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    simp only [amnrWord]
    rw [ih]
    funext z
    have hdf := contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
        hf.contDiffOn w)
    have hdg := contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
        hg.contDiffOn w)
    unfold amnrOp
    rw [fderiv_add (hdf.differentiable (by simp) z) (hdg.differentiable (by simp) z), add_apply]
    rfl

/-- Every mixed jet of the derived flow-transport coefficient is bounded
from the actual velocity-gradient jets. This generic conditional helper does
not assert the primitive gradient bounds. Each induction level loses two units. -/
theorem amnrFlowMaterialCoefficient_mixed_abs_le_of_gradient_bounds
    {b : AmnrSpace → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {N : ℕ} {S H Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) (hCb : 0 ≤ Cb)
    {z : AmnrSpace}
    (hBb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ N →
      |amnrWord b w (amnrVelocityGradient b i p) z| ≤ Cb * H * amnrWeight S H w)
    (n : ℕ) (w : List (Option (Fin 2))) (hw : IsAmnrMixedWord w)
    (hbudget : amnrBudget w + 2 * n ≤ N) (q p : Fin 2) :
    |amnrWord b w (amnrFlowMaterialCoefficient b n q p) z| ≤
      (1 + (2 : ℝ) ^ (N + 1) * Cb) ^ n * H ^ n * amnrWeight S H w := by
  let D := (2 : ℝ) ^ (N + 1)
  let R := 1 + D * Cb
  have hD : 0 ≤ D := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  change _ ≤ R ^ n * H ^ n * amnrWeight S H w
  induction n generalizing w q p with
  | zero =>
    simp only [amnrFlowMaterialCoefficient, amnrWord_const, pow_zero, one_mul]
    split_ifs with hw0 hqp
    · subst w
      simp [amnrWeight]
    · subst w
      simp [amnrWeight]
    · simp only [Pi.zero_apply, abs_zero]
      exact amnrWeight_nonneg hS hH w
  | succ n ih =>
    have hnext := amnrLevelBudget hbudget
    have hlen : w.length ≤ N := (amnrBudget_length_le w).trans (by omega)
    let B := fun a => amnrVelocityGradient b a q
    let M := fun a => amnrFlowMaterialCoefficient b n a p
    have hB (a : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (B a) :=
      contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn a q)
    have hM (a : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (M a) := amnrFlowMaterialCoefficient_contDiff hb n a p
    have heq : amnrFlowMaterialCoefficient b (n + 1) q p =
        amnrOp b none (M q) + ∑ a : Fin 2, B a * M a := by
      funext y
      simp only [amnrFlowMaterialCoefficient, Finset.sum_apply, Pi.mul_apply, Pi.add_apply]
      rfl
    have hF₁ : ContDiff ℝ (⊤ : ℕ∞) (amnrOp b none (M q)) :=
      contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn (hM q).contDiffOn
          [none])
    have hF₂ : ContDiff ℝ (⊤ : ℕ∞) (∑ a : Fin 2, B a * M a) :=
      by simpa only [Finset.sum_fn, Pi.mul_apply] using
        ContDiff.sum (s := Finset.univ) (fun a _ => (hB a).mul (hM a))
    rw [heq, amnrWord_add_global hb hF₁ hF₂ w]
    change |amnrWord b w (amnrWord b [none] (M q)) z + amnrWord b w (∑ a : Fin 2, B a * M a) z| ≤ _
    rw [← amnrWord_append (b := b) w [none]]
    have hsum := amnrWord_sum (N := N) isOpen_univ (hb.of_le (by simp)).contDiffOn Finset.univ
      (fun a => B a * M a) (fun a _ => ((hB a).mul (hM a)).of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
          by simp) |>.contDiffOn)
      w hlen (Set.mem_univ z)
    rw [hsum]
    have hfirst := ih (w ++ [none]) hw.material hnext.1 q p
    have hweight : amnrWeight S H (w ++ [none]) = amnrWeight S H w * H := by simp [amnrWeight]
    rw [hweight] at hfirst
    have hprod (a : Fin 2) : |amnrWord b w (B a * M a) z| ≤
        (2 : ℝ) ^ w.length * (Cb * H) * (R ^ n * H ^ n) * amnrWeight S H w := by
      apply amnrWord_mul_abs_le_at (N := N) isOpen_univ (hb.of_le (by simp)).contDiffOn
        ((hB a).of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
        ((hM a).of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
        hS hH (mul_nonneg hCb hH) (by positivity) w (by omega) (Set.mem_univ z)
      · intro v hv
        exact hBb a q v (hw.sublist hv) (by have := amnrBudget_sublist hv; omega)
      · intro v hv
        exact ih v (hw.sublist hv) (by have := amnrBudget_sublist hv; omega) a p
    have hsumBound : |∑ a : Fin 2, amnrWord b w (B a * M a) z| ≤
        D * Cb * R ^ n * H ^ (n + 1) * amnrWeight S H w := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 2))) => hprod a)
      simp only [Fin.sum_univ_two] at hh
      have hpow : 2 * (2 : ℝ) ^ w.length ≤ D := by
        rw [mul_comm, ← pow_succ]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hscaled := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ Cb * R ^ n * H ^ (n + 1) * amnrWeight S H w by
          have := amnrWeight_nonneg hS hH w; positivity)
      rw [Fin.sum_univ_two]
      refine hh.trans ?_
      convert hscaled using 1 <;> rw [pow_succ] <;> ring
    refine ((abs_add_le _ _).trans (add_le_add hfirst hsumBound)).trans_eq ?_
    dsimp [R]
    rw [pow_succ, pow_succ]
    ring

end AVenhance.Infra.Section4
