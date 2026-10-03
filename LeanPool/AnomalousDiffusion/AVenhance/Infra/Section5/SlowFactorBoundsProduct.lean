/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.DirectionalProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragedComposition
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Finite scalar products: bounded coefficient jets times averaged positive
T jets. Every differentiation allocation retains its multiplicity. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

/-- Allocations of derivative positions between two scalar factors. -/
def slowWordSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w =>
    (slowWordSplits w).map (fun p => (i :: p.1, p.2)) ++
    (slowWordSplits w).map (fun p => (p.1, i :: p.2))

theorem slowWordSplits_length (w : List (Fin 2)) :
    (slowWordSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [slowWordSplits, ih, pow_succ, Nat.mul_two]

theorem slowWordSplits_sizes (w : List (Fin 2)) (p : List (Fin 2) × List (Fin 2))
    (hp : p ∈ slowWordSplits w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    have he : p = ([], []) := by simpa [slowWordSplits] using hp
    subst p
    rfl
  | cons i w ih =>
    simp only [slowWordSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simp only [List.length_cons] <;> have hh := ih q hq <;> omega

theorem amnrSpaceWord_eq_directionalJet (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    amnrSpaceWord w f = directionalJet (w.map basisVec) f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [amnrSpaceWord, List.map_cons, directionalJet, ih]

theorem slowWordSplits_map_directions (w : List (Fin 2)) :
    directionalSplits (w.map basisVec) =
      (slowWordSplits w).map (fun p => (p.1.map basisVec, p.2.map basisVec)) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [directionalSplits, slowWordSplits, ih, List.map_map, Function.comp_def]

theorem slowWord_smooth {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (amnrSpaceWord w f) := by
  rw [amnrSpaceWord_eq_directionalJet]
  exact directionalJet_contDiff _ _ hf

theorem slowWord_mul_expansion {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List (Fin 2)) :
    amnrSpaceWord w (f * g) =
      ((slowWordSplits w).map (fun p => amnrSpaceWord p.1 f * amnrSpaceWord p.2 g)).sum := by
  rw [amnrSpaceWord_eq_directionalJet]
  have hh := directionalJet_mul (w.map basisVec) f g hf hg
  rw [slowWordSplits_map_directions] at hh
  have hsum (x : Vec 2) (L : List (Vec 2 → ℝ)) : L.sum x = (L.map (fun g => g x)).sum := by
    induction L with
    | nil => rfl
    | cons g L ih =>
      simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using
        (congrArg (fun a => g x + a) ih)
  funext x
  rw [hsum x]
  simpa only [List.map_map, Function.comp_def, ← amnrSpaceWord_eq_directionalJet,
    Pi.mul_apply, Pi.mul_def] using congrFun hh x

/-- L-infinity times Lp, using an actual pointwise bound rather than an
assumed product estimate. -/
theorem slowFactor_mul_eLpNorm_le {f g : Vec 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) (μ : Measure (Vec 2)) :
    eLpNorm (f * g) p μ ≤ ENNReal.ofReal B * eLpNorm g p μ := by
  have hn : ∀ᵐ x ∂μ, ‖(f * g) x‖ ≤ ‖(B • g) x‖ := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
  have hh := eLpNorm_mono_ae (hf.mul hg).aestronglyMeasurable hn (p := p)
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg hB] at hh
  exact hh

theorem slowFactor_listSum_eLpNorm_le (L : List (Vec 2 → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (μ : Measure (Vec 2)) :
    eLpNorm L.sum p μ ≤ (L.map (fun f => eLpNorm f p μ)).sum := by
  induction L with
  | nil => simp
  | cons f L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (eLpNorm_add_le hp).trans (add_le_add le_rfl ih)

/-- The two allocated factorials never exceed the total factorial. -/
theorem slowFactor_split_factorial_le (a b : ℕ) :
    (a.factorial : ℝ) * b.factorial ≤ (a + b).factorial := by
  have hc : 1 ≤ (a + b).choose b := Nat.succ_le_of_lt
    (Nat.choose_pos (Nat.le_add_left b a))
  have hh := Nat.add_choose_mul_factorial_mul_factorial a b
  have hp : a.factorial * b.factorial ≤ (a + b).factorial := by
    calc
      _ ≤ (a + b).choose b * (a.factorial * b.factorial) :=
        Nat.le_mul_of_pos_left _ hc
      _ = _ := by simpa only [Nat.mul_assoc] using hh
  exact_mod_cast hp

/-- A binary product consumes no derivative of T of order zero when its
averaged factor was already a positive T jet. Iteration handles any fixed
finite number of coefficient factors. -/
theorem slowFactor_word_mul_eLpNorm_le {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {F G L : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hL : 0 ≤ L)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (μ : Measure (Vec 2))
    (hfb : ∀ w x, |amnrSpaceWord w f x| ≤ F * w.length.factorial * L ^ w.length)
    (hgb : ∀ w, eLpNorm (amnrSpaceWord w g) p μ ≤
      ENNReal.ofReal (G * w.length.factorial * L ^ w.length)) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (f * g)) p μ ≤
      ENNReal.ofReal (F * G * w.length.factorial * (2 * L) ^ w.length) := by
  rw [slowWord_mul_expansion hf hg]
  apply (slowFactor_listSum_eLpNorm_le _ hp μ).trans
  have hterm (q : List (Fin 2) × List (Fin 2)) (hq : q ∈ slowWordSplits w) :
      eLpNorm (amnrSpaceWord q.1 f * amnrSpaceWord q.2 g) p μ ≤
        ENNReal.ofReal (F * G * w.length.factorial * L ^ w.length) := by
    have hh := (slowFactor_mul_eLpNorm_le (slowWord_smooth hf q.1).continuous
      (slowWord_smooth hg q.2).continuous (by positivity) (hfb q.1) p μ).trans
        (mul_le_mul_right (hgb q.2) _)
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ F * q.1.length.factorial * L ^ q.1.length)] at hh
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs := slowWordSplits_sizes w q hq
    have hfac := slowFactor_split_factorial_le q.1.length q.2.length
    rw [hs] at hfac
    calc
      _ = F * G * ((q.1.length.factorial : ℝ) * q.2.length.factorial) *
          L ^ (q.1.length + q.2.length) := by rw [pow_add]; ring
      _ ≤ F * G * w.length.factorial * L ^ w.length := by
        rw [hs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac (by positivity)) (by positivity)
  have hsum : ((slowWordSplits w).map (fun q =>
      eLpNorm (amnrSpaceWord q.1 f * amnrSpaceWord q.2 g) p μ)).sum ≤
      ((slowWordSplits w).length : ℕ) •
        ENNReal.ofReal (F * G * w.length.factorial * L ^ w.length) := by
    have hh := List.sum_le_sum hterm
    simpa only [List.map_const', List.sum_replicate] using hh
  simp only [List.map_map, Function.comp_def]
  apply hsum.trans_eq
  rw [slowWordSplits_length, nsmul_eq_mul]
  rw [show ((2 ^ w.length : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ w.length) by
    simp]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  ring

end AVenhance.Infra.Section5
