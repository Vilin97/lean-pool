/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesForcingSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsTIterates
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! # recursive construction of the `T` iterates

assumes only that classical solutions exist for the finite drifts with jointly
smooth periodic forcing (`ClassicalSolvable`; `AVenhance.classical_wellposed` is its precise
    form).  Then the actual `T`
iterates `T^{(0)} = θ_{m-1}`, `T^{(i)}` the classical solution of `e.Tm-1.i` are constructed
recursively: each `T^{(i)}` is classical, hence jointly smooth and periodic, so the next forcing
(`TForcing_contDiffOn`, `TForcing_periodic`) is admissible.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped Matrix.Norms.Elementwise ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- Classical solvability of the finite-level transport–diffusion problem with smooth data and
    smooth
periodic forcing (the existence hypothesis of the relative step; `AVenhance.classical_wellposed`
    is its general form). -/
def ClassicalSolvable (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → IsZ2Periodic g →
    ∀ F : ℝ → Vec 2 → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
      (∀ t, 0 ≤ t → IsZ2Periodic (F t)) →
      ∃ u : ℝ → Vec 2 → ℝ, IsClassicalSol b ν F g u

/-- Existence of the `T` iterates from classical solvability of the finite drifts. -/
theorem exists_TIterates {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    (hκprev : 0 < κprev)
    (hsolv : ClassicalSolvable (streamVel (Φ (m - 1))))
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hθ₀p : IsZ2Periodic θ₀)
    {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev) :
    ∃ T : ℕ → ℝ → Vec 2 → ℝ, I.IsTIterates hΦ m κm κprev θ₀ θprev T := by
  have key : ∀ i : ℕ, ∃ T : ℕ → ℝ → Vec 2 → ℝ, T 0 = θprev ∧ ∀ j : ℕ, 1 ≤ j → j ≤ i →
      IsClassicalSol (streamVel (Φ (m - 1))) κprev
        (I.TForcing hΦ m κm κprev (T (j - 1))) θ₀ (T j) := by
    intro i
    induction i with
    | zero => exact ⟨fun _ => θprev, rfl, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ i ih =>
      obtain ⟨T, h0, hT⟩ := ih
      have hgood : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T i p.1 p.2)
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧ ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T i t) := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          rw [h0]
          exact ⟨hθprev.1, hθprev.2.1⟩
        · exact ⟨(hT i hi le_rfl).1, (hT i hi le_rfl).2.1⟩
      obtain ⟨u, hu⟩ := hsolv κprev hκprev θ₀ hθ₀ hθ₀p (I.TForcing hΦ m κm κprev (T i))
        (TForcing_contDiffOn I hΦ hm hκm κprev hgood.1)
        (fun t ht => TForcing_periodic I hΦ hm κm κprev
          ((slice_contDiff_of_contDiffOn hgood.1 ht).of_le (by exact_mod_cast le_top))
          (hgood.2 t ht))
      refine ⟨Function.update T (i + 1) u, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact h0
      · intro j h1 h2
        rcases Nat.lt_or_ge j (i + 1) with hj | hj
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hT j h1 (by omega)
        · have hji : j = i + 1 := by omega
          subst hji
          rw [Function.update_self, Nat.add_sub_cancel, Function.update_of_ne (by omega)]
          exact hu
  obtain ⟨T, h0, hT⟩ := key (Nstar β)
  exact ⟨T, h0, fun i h1 h2 => hT i h1 h2⟩

end AVenhance.Infra.Section5.RelativeError
