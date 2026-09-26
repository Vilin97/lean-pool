/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FourierEnergy
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterLinear
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterSum

/-!
# Thickness and dilated translation growth

The geometric sum estimate outside a central slab supplies a uniform
spectral gap for short integer multiples of the available translations.
Subadditivity then transfers growth back to an original translation.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.Expansion

/-- The non-strict central-slab thickness condition for real weights. -/
def IsCentrallyThick {p d : ℕ} [NeZero p] (w : FpCoord p d → ℝ)
    (K : ℕ) (δ : ℝ) : Prop := by
  classical
  exact ∀ ξ : FpCoord p d →ₗ[ZMod p] ZMod p, ξ ≠ 0 →
    δ * (∑ v, w v) ≤ ∑ v, if ¬ HasBoundedRepresentative p K (ξ v) then w v else 0

/-- The growth step, separated from the one-dimensional character-sum
estimate so that the combinatorial and analytic arguments remain reusable. -/
theorem exists_boundary_of_dilated_characters {p d K m : ℕ} [NeZero p]
    (w : FpCoord p d → ℝ) (hw : ∀ v, 0 ≤ w v) (hW : 0 < ∑ v, w v)
    (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) (hthick : IsCentrallyThick w K δ)
    (hchar : ∀ r : ZMod p, ¬ HasBoundedRepresentative p K r →
      ‖∑ j : Fin m, (AddChar.zmodAddEquiv r) (j : ZMod p)‖ ≤ (m : ℝ) / 2)
    (Y : Finset (FpCoord p d)) (hhalf : 2 * Y.card ≤ p ^ d) :
    ∃ v, 0 < w v ∧ δ * Y.card ≤ 4 * m * (boundary Y v : ℝ) := by
  classical
  let w' : FpCoord p d × Fin m → ℝ := fun i ↦ w i.1
  let a' : FpCoord p d × Fin m → FpCoord p d := fun i ↦ (i.2 : ℕ) • i.1
  have hmass : (∑ i, w' i) = (m : ℝ) * ∑ v, w v := by
    simp [w', Fintype.sum_prod_type, Finset.sum_const, Finset.mul_sum]
  have hgap (χ : AddChar (FpCoord p d) ℂ) (hχ : χ ≠ 0) :
      (∑ i, w' i * (χ (-a' i)).re) ≤ (1 - δ / 2) * ∑ i, w' i := by
    let ψ := -χ
    let ξ := characterLinear ψ
    have hξ : ξ ≠ 0 := characterLinear_ne_zero (neg_ne_zero.mpr hχ)
    have hout := hthick ξ hξ
    have hpoint (v : FpCoord p d) :
        w v * (∑ j : Fin m, (ψ ((j : ℕ) • v)).re) ≤
          (m : ℝ) * w v - ((m : ℝ) / 2) *
            (if ¬ HasBoundedRepresentative p K (ξ v) then w v else 0) := by
      have hnorm : ‖∑ j : Fin m, ψ ((j : ℕ) • v)‖ ≤ (m : ℝ) := by
        calc
          _ ≤ ∑ j : Fin m, ‖ψ ((j : ℕ) • v)‖ := norm_sum_le _ _
          _ = _ := by simp only [AddChar.norm_apply, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
      by_cases hv : ¬ HasBoundedRepresentative p K (ξ v)
      · have hsmall : ‖∑ j : Fin m, ψ ((j : ℕ) • v)‖ ≤ (m : ℝ) / 2 := by
          simp_rw [← characterLinear_eval]
          exact hchar (ξ v) hv
        have hreal : (∑ j : Fin m, (ψ ((j : ℕ) • v)).re) ≤ (m : ℝ) / 2 := by
          rw [← re_sum]
          exact (Complex.re_le_norm _).trans hsmall
        rw [ite_eq_left hv]
        nlinarith [mul_le_mul_of_nonneg_left hreal (hw v)]
      · have hreal : (∑ j : Fin m, (ψ ((j : ℕ) • v)).re) ≤ (m : ℝ) := by
          rw [← re_sum]
          exact (Complex.re_le_norm _).trans hnorm
        rw [ite_eq_right hv, mul_zero, sub_zero]
        nlinarith [mul_le_mul_of_nonneg_left hreal (hw v)]
    calc
      (∑ i, w' i * (χ (-a' i)).re) =
          ∑ v, w v * ∑ j : Fin m, (ψ ((j : ℕ) • v)).re := by
        simp only [Fintype.sum_prod_type, w', a', Finset.mul_sum]
        rfl
      _ ≤ ∑ v, ((m : ℝ) * w v - ((m : ℝ) / 2) *
          (if ¬ HasBoundedRepresentative p K (ξ v) then w v else 0)) :=
        Finset.sum_le_sum fun v _ ↦ hpoint v
      _ = (m : ℝ) * (∑ v, w v) - ((m : ℝ) / 2) *
          ∑ v, if ¬ HasBoundedRepresentative p K (ξ v) then w v else 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 - δ / 2) * ∑ i, w' i := by
        rw [hmass]
        nlinarith [mul_le_mul_of_nonneg_left hout
          (show (0 : ℝ) ≤ (m : ℝ) / 2 by positivity)]
  obtain ⟨⟨v, j⟩, hv, hgrow⟩ := exists_boundary_of_spectral_gap Y w' a'
    (fun i ↦ hw i.1) (by rw [hmass]; positivity) (by positivity : 0 ≤ δ / 2)
    (by simpa using hhalf) hgap
  refine ⟨v, hv, ?_⟩
  have hbound : boundary Y ((j : ℕ) • v) ≤ m * boundary Y v :=
    (boundary_nsmul_le Y v j).trans (Nat.mul_le_mul_right _ j.isLt.le)
  have hr : (boundary Y ((j : ℕ) • v) : ℝ) ≤ (m : ℝ) * boundary Y v := by
    exact_mod_cast hbound
  change δ / 2 * Y.card ≤ 2 * (boundary Y ((j : ℕ) • v) : ℝ) at hgrow
  nlinarith

/-- Central thickness forces a translation with a proportionate boundary.
The absolute constant `20` suffices; the paper uses the looser `200`. -/
theorem exists_boundary_of_central_thickness {p d K : ℕ} [NeZero p]
    (hK : 0 < K) (hKp : K ≤ p)
    (w : FpCoord p d → ℝ) (hw : ∀ v, 0 ≤ w v) (hW : 0 < ∑ v, w v)
    {δ : ℝ} (hδ : 0 ≤ δ) (hthick : IsCentrallyThick w K δ)
    (Y : Finset (FpCoord p d)) (hhalf : 2 * Y.card ≤ p ^ d) :
    ∃ v, 0 < w v ∧ (K : ℝ) * δ * Y.card ≤ 20 * p * (boundary Y v : ℝ) := by
  classical
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpr : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hKpr : (K : ℝ) ≤ p := by exact_mod_cast hKp
  let m := ⌈4 * (p : ℝ) / K⌉₊
  have hmlo : 4 * (p : ℝ) / K ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    rw [hm0, Nat.cast_zero] at hmlo
    have : (0 : ℝ) < 4 * p / K := by positivity
    linarith
  have hmhi : (m : ℝ) * K ≤ 5 * p := by
    have hh : (m : ℝ) < 4 * p / K + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmul := mul_lt_mul_of_pos_right hh hKr
    rw [add_mul, div_mul_cancel₀ _ hKr.ne', one_mul] at hmul
    linarith
  have hchar (r : ZMod p) (hr : ¬ HasBoundedRepresentative p K r) :
      ‖∑ j : Fin m, (AddChar.zmodAddEquiv r) (j : ZMod p)‖ ≤ (m : ℝ) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ (AddChar.zmodAddEquiv r) (j : ZMod p))]
    apply (character_partial_sum_le hK r hr m).trans
    calc
      2 * (p : ℝ) / K = (4 * p / K) / 2 := by ring
      _ ≤ (m : ℝ) / 2 := by linarith
  obtain ⟨v, hv, hgrow⟩ := exists_boundary_of_dilated_characters w hw hW hm hδ hthick
    hchar Y hhalf
  refine ⟨v, hv, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hgrow hKr.le
  have hmB := mul_le_mul_of_nonneg_right hmhi (show (0 : ℝ) ≤ 4 * boundary Y v by positivity)
  nlinarith

/-- Multiplicative form of the central-thickness growth lemma. -/
theorem exists_translate_growth_of_central_thickness {p d K : ℕ} [NeZero p]
    (hK : 0 < K) (hKp : K ≤ p)
    (w : FpCoord p d → ℝ) (hw : ∀ v, 0 ≤ w v) (hW : 0 < ∑ v, w v)
    {δ : ℝ} (hδ : 0 ≤ δ) (hthick : IsCentrallyThick w K δ)
    (Y : Finset (FpCoord p d)) (hhalf : 2 * Y.card ≤ p ^ d) :
    ∃ v, 0 < w v ∧ (1 + K * δ / (20 * p)) * (Y.card : ℝ) ≤
      (translate Y v ∪ Y).card := by
  obtain ⟨v, hv, hb⟩ := exists_boundary_of_central_thickness hK hKp w hw hW hδ hthick Y hhalf
  refine ⟨v, hv, ?_⟩
  have hp : (0 : ℝ) < 20 * p := by
    have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    positivity
  have hdiv : (K : ℝ) * δ * Y.card / (20 * p) ≤ (boundary Y v : ℝ) :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hu : (boundary Y v : ℝ) + Y.card = (translate Y v ∪ Y).card := by
    exact_mod_cast boundary_add_card Y v
  calc
    (1 + K * δ / (20 * p)) * (Y.card : ℝ) = Y.card + K * δ * Y.card / (20 * p) := by ring
    _ ≤ Y.card + boundary Y v := by linarith
    _ = _ := by linarith

end EGZ.Expansion
