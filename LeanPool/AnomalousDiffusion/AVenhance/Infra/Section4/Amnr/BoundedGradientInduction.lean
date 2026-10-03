/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityHigherStep

/-! Bounded material induction for derivatives of actual velocity components. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- A scalar's material/spatial jets control its differentiated material jets
using only strictly lower material orders of the actual velocity gradient.
This conditional calculus lemma does not assert the source primitive bounds. -/
theorem amnr_material_gradient_mixed_abs_le_of_bounded_lower_gradient_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hfb : ∀ η r, r ≤ cut → η.length + 2 * r ≤ N →
      |amnrWord b (amnrMixedWord η r) f z| ≤ F * S ^ η.length * H ^ r)
    (hBb : ∀ p i η r, r < cut → η.length + 2 * r + 2 ≤ N →
      |amnrWord b (amnrMixedWord η r) (amnrVelocityGradient b p i) z| ≤
        Cb * H * S ^ η.length * H ^ r)
    (n : ℕ) (hn : n ≤ cut) (α : List (Fin 2)) (j : ℕ)
    (hbudget : α.length + 1 + 2 * (n + j) ≤ N) (htotal : n + j ≤ cut) (i : Fin 2) :
    |amnrWord b (amnrMixedWord α n)
      (amnrOp b (some i) (amnrWord b (List.replicate j none) f)) z| ≤
      (1 + (2 : ℝ) ^ (N + 1) * Cb) ^ n * F * S ^ (α.length + 1) * H ^ (n + j) := by
  let R := 1 + (2 : ℝ) ^ (N + 1) * Cb
  have hR : 1 ≤ R := by
    have hh : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb := by positivity
    dsimp [R]
    linarith only [hh]
  have hbound : ∀ n : ℕ, n ≤ cut → ∀ α : List (Fin 2), ∀ j : ℕ,
      α.length + 1 + 2 * (n + j) ≤ N → n + j ≤ cut → ∀ i : Fin 2,
      |amnrWord b (amnrMixedWord α n)
        (amnrOp b (some i) (amnrWord b (List.replicate j none) f)) z| ≤
        R ^ n * F * S ^ (α.length + 1) * H ^ (n + j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn α j hbudget htotal i
      cases n with
      | zero =>
        have hh := hfb (α ++ [i]) j (by omega) (by
          simp only [List.length_append, List.length_singleton]
          omega)
        simp only [amnrMixedWord, List.replicate_zero, List.append_nil]
        change |amnrWord b (α.map some)
          (amnrWord b [some i] (amnrWord b (List.replicate j none) f)) z| ≤ _
        rw [← amnrWord_append, ← amnrWord_append]
        simp only [amnrMixedWord, List.map_append, List.map_singleton, List.length_append,
          List.length_singleton] at hh
        simpa only [List.append_assoc, pow_zero, one_mul, Nat.zero_add] using hh
      | succ n =>
        let w := amnrMixedWord α n
        let g := amnrWord b (List.replicate j none) f
        have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiffOn_univ.mp
          (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn hf.contDiffOn (List.replicate j
              none))
        have hshift : amnrOp b none g = amnrWord b (List.replicate (j + 1) none) f := by
          simp only [List.replicate_succ, amnrWord, g]
        have hfirst : |amnrWord b (w ++ [some i, none]) g z| ≤
            R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) := by
          rw [amnrWord_append]
          change |amnrWord b w (amnrOp b (some i) (amnrOp b none g)) z| ≤ _
          rw [hshift]
          simpa only [Nat.add_assoc] using ih n (by omega) (by omega) α (j + 1) (by omega) (by
              omega) i
        have hBsub : ∀ p v, v.Sublist w →
            |amnrWord b v (amnrVelocityGradient b p i) z| ≤ (Cb * H) * amnrWeight S H v := by
          intro p v hv
          obtain ⟨η, r, heq, hr, hη⟩ := amnrMixedWord_subword_normalForm hv
          rw [heq, amnrMixedWord_weight]
          have hh := hBb p i η r (by omega) (by omega)
          convert hh using 1
          ring
        have hGsub : ∀ p v, v.Sublist w →
            |amnrWord b v (amnrOp b (some p) g) z| ≤
              (R ^ n * F * S * H ^ j) * amnrWeight S H v := by
          intro p v hv
          obtain ⟨η, r, heq, hr, hη⟩ := amnrMixedWord_subword_normalForm hv
          rw [heq, amnrMixedWord_weight]
          have hh := ih r (by omega) (by omega) η j (by omega) (by omega) p
          have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR hr)
            (show 0 ≤ F * S ^ (η.length + 1) * H ^ (r + j) by positivity)
          refine hh.trans ?_
          calc
            _ = R ^ r * (F * S ^ (η.length + 1) * H ^ (r + j)) := by ring
            _ ≤ R ^ n * (F * S ^ (η.length + 1) * H ^ (r + j)) := hp
            _ = _ := by rw [pow_succ, pow_add]; ring
        have hh := amnr_word_material_spatial_abs_le_of_bounds hb hg w i z hS hH
          (show 0 ≤ Cb * H by positivity)
          (show 0 ≤ R ^ n * F * S * H ^ j by
            have hR0 := hR.trans' (by norm_num : (0 : ℝ) ≤ 1)
            positivity)
          hfirst hBsub hGsub
        have heq : amnrWord b (amnrMixedWord α (n + 1)) (amnrOp b (some i) g) =
            amnrWord b w (amnrOp b none (amnrOp b (some i) g)) := by
          unfold amnrMixedWord
          rw [List.replicate_succ', ← List.append_assoc, amnrWord_append]
          rfl
        rw [heq]
        refine hh.trans ?_
        have hlen : w.length ≤ N := by
          have hh := amnrBudget_length_le w
          have he : amnrBudget w = α.length + 2 * n := amnrMixedWord_budget α n
          omega
        have hp : (2 : ℝ) ^ (w.length + 1) ≤ (2 : ℝ) ^ (N + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hd := mul_le_mul_of_nonneg_right hp
          (show 0 ≤ (Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w by
            have := amnrWeight_nonneg hS hH w
            have := hR.trans' (by norm_num : (0 : ℝ) ≤ 1)
            positivity)
        calc
          _ = R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) +
              (2 : ℝ) ^ (w.length + 1) *
                ((Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w) := by ring
          _ ≤ R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) +
              (2 : ℝ) ^ (N + 1) *
                ((Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w) := add_le_add le_rfl hd
          _ = _ := by
            rw [amnrMixedWord_weight]
            dsimp [R]
            rw [pow_succ, pow_add, pow_add, pow_succ]
            ring
  exact hbound n hn α j hbudget htotal i

end AVenhance.Infra.Section4
