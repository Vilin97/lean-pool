/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FrozenBridge

/-! Memory infrastructure for the AMNR tensors. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A time-only scalar has no spatial derivative; its material derivative
is its ordinary time derivative, regardless of the velocity. -/
theorem amnrOp_timeOnly {b : AmnrSpace → Vec 2} {f : ℝ → ℝ} {z : AmnrSpace}
    (hf : DifferentiableAt ℝ f z.1) (d : Option (Fin 2)) :
    amnrOp b d (fun y => f y.1) z =
      match d with | none => deriv f z.1 | some _ => 0 := by
  have hh := (hf.hasDerivAt.hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := Vec 2))).fderiv
  unfold amnrOp
  change fderiv ℝ (f ∘ Prod.fst) z (amnrDirection b d z) = _
  rw [hh]
  cases d <;> simp [amnrDirection]

/-- Pure material words on the actual memory coefficient reduce to ordinary
time derivatives, retaining its finite approved regularity order. -/
theorem amnrWord_timeOnly_material {b : AmnrSpace → Vec 2} {f : ℝ → ℝ} {N : ℕ}
    (hf : ContDiff ℝ N f) (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    amnrWord b (List.replicate ℓ none) (fun z => f z.1) =
      fun z => iteratedDeriv ℓ f z.1 := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [List.replicate_succ]
    change amnrOp b none (amnrWord b (List.replicate ℓ none) (fun z => f z.1)) = _
    rw [ih (by omega)]
    funext z
    rw [amnrOp_timeOnly (hf.differentiable_iteratedDeriv ℓ (by exact_mod_cast (by omega : ℓ < N))
        z.1)]
    rw [iteratedDeriv_succ]

/-- Spatial letters outside a time-only material word annihilate it. -/
theorem amnrWord_timeOnly_mixed {b : AmnrSpace → Vec 2} {f : ℝ → ℝ} {N : ℕ}
    (hf : ContDiff ℝ N f) (α : List (Fin 2)) (ℓ : ℕ) (h : α.length + ℓ ≤ N) :
    amnrWord b (amnrMixedWord α ℓ) (fun z => f z.1) =
      if α = [] then (fun z : AmnrSpace => iteratedDeriv ℓ f z.1) else (0 : AmnrSpace → ℝ) := by
  induction α with
  | nil => simpa only [amnrMixedWord, List.map_nil, List.nil_append, ite_true] using
      amnrWord_timeOnly_material hf ℓ (by simpa using h)
  | cons i α ih =>
    simp only [List.length_cons] at h
    change amnrOp b (some i) (amnrWord b (amnrMixedWord α ℓ) (fun z => f z.1)) = _
    rw [ih (by omega)]
    by_cases ha : α = []
    · rw [ite_eq_left ha]
      funext z
      rw [amnrOp_timeOnly (hf.differentiable_iteratedDeriv ℓ
        (by exact_mod_cast (by omega : ℓ < N)) z.1)]
      simp
    · rw [ite_eq_right ha]
      funext z
      simp [amnrOp]

/-- All admissible mixed memory derivatives use the proved §3 bound and the
large cutoff rate. Spatial derivatives vanish. The invalid fine-rate
comparison is neither assumed nor used. -/
theorem LMN_mixed_word_abs_le {β C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hcutoff : I.Chat ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (hn : n ≤ AVenhance.Nstar β) {b : AmnrSpace → Vec 2}
    {S : ℝ} (hS : 0 ≤ S) (α : List (Fin 2)) (ℓ : ℕ)
    (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β) (z : AmnrSpace) :
    |amnrWord b (amnrMixedWord α ℓ) (fun y => I.LMN κ m n y.1) z| ≤
      amnrMemoryConstant β C₀ * (AVenhance.epsilon β I.Λ m ^ 2 / κ) *
        S ^ α.length * (AVenhance.tauP β I.Λ m)⁻¹ ^ ℓ := by
  have hℓ : ℓ ≤ AVenhance.Nstar β := by omega
  have hreg : ContDiff ℝ (AVenhance.Nstar β : ℕ) (I.LMN κ m n) :=
    (Infra.Section3.LMN_contDiff I hm hκ n).of_le (by norm_cast)
  rw [amnrWord_timeOnly_mixed hreg α ℓ (by omega)]
  by_cases hα : α = []
  · rw [ite_eq_left hα]
    have hh := Infra.Section3.LMN_derivative_paper_bound I hcutoff hm hκ hn hℓ z.1
    simpa only [hα, List.length_nil, pow_zero, mul_one, amnrMemoryConstant,
      div_eq_mul_inv, inv_pow, mul_assoc] using hh
  · rw [ite_eq_right hα]
    simp only [Pi.zero_apply, abs_zero]
    have hC : 0 ≤ amnrMemoryConstant β C₀ := by unfold amnrMemoryConstant; positivity
    have hτ : 0 < AVenhance.tauP β I.Λ m :=
      AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    positivity

end AVenhance.Infra.Section4
