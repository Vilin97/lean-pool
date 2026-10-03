/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalHighStream
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedStreamOrders

/-! The complete actual all-order stream contribution under the stream-regularity estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Combine the actual first and high stream jets; the skew principal term
 vanishes. Only strictly lower current scalar orders are inductive inputs. -/
theorem iterate_increment_terminal_stream_flux_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (hm : 2 ≤ m) (hκ : 0 < κprev)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hθp : ∀ t, 0 ≤ t → IsZ2Periodic (θprev t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (i : ℕ) (hi : i ≤ Nstar β) (j : Fin 2) (w : List (Fin 2)) {B L : ℝ} (hL : 0 < L)
    (hg : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (D : ℕ → ℝ)
    (hfirst : ∀ p : List (Fin 2), p.length = w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T i t))) ≤
        B ^ 2 * (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 * D w.length ^ 2)
    (hhigh : ∀ p ∈ (iterateSpatialSplits (j :: w)).filter (fun p => decide (2 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (iterateIncrement T i t))) ≤
        B ^ 2 * (((p.2.length + 2 * i).factorial : ℝ) * L ^ p.2.length) ^ 2 * D p.2.length ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (j :: w)
        (iterateIncrement T i z.1)) z.2)
      (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat) (iterateIncrement T i z.1) (j :: w)
          z.2)| ≤
      κprev / 8 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord (j :: w) (iterateIncrement T i t))) +
      2 * ((2 : ℝ) ^ 19 * a β I.Λ (m - 1)) * B ^ 2 / L ^ 2 *
        (((w.length + 1 + 2 * i).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 * D w.length ^ 2 +
      16 / κprev * (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) ^ 2 * B ^ 2 *
        (2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2) ^ 2 *
        (((w.length + 1 + 2 * i).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (4 : ℝ)) ^ k * D (w.length - 1 - k) ^ 2 := by
  obtain ⟨hφ, _⟩ := hΦ.2 m (by omega)
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ hi
  have ha := AVenhance.Infra.Cutoff.a_pos (m := m - 1) I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hp (t : ℝ) (_ : 0 < t) : IsZ2Periodic (Φ (m - 1) t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have hup (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateIncrement T i t) :=
    iterateIncrement_periodic I hΦ hT hθp hi ht.le
  have h₁ := iterate_truncated_first_stream_flux_analytic_bound (by positivity) hL hφ.1.contDiffOn
      hu hs0 hs1
    hp hup j w i (fun t x k l => iterate_stream_second_jet_bound_of_A3 I hΦ hm hA3 t x l k) hfirst
  have h₂ := iterate_increment_terminal_high_stream_bound_of_A3 I hΦ hT hθ hm hκ hA3
    hs1 i hi (j :: w) hL hg D hhigh
  rw [iterate_truncated_stream_pairing_order_split hφ.1.contDiffOn hu hs1 (j :: w)]
  have ht := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  simp only [List.length_cons, Nat.add_sub_cancel] at ht
  have hs : w.length + 1 - 2 = w.length - 1 := by omega
  simp only [hs] at ht
  linarith only [ht]

end AVenhance.Infra.Section4
