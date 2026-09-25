/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairCollapse

/-! # Bad Scale Tail Exponent -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Tail exponents for the quenched minimal scale

This file isolates the real-variable exponent used in the corrected finite
`sigma` theorem.  The mixed bottom range optimizes a `Gamma_tau` localized
tail against a `Gamma_sigma` crude tail; the resulting exponent is the
interpolated one recorded below.
-/

noncomputable section

/-- The finite-sigma concentration exponent after the Chapter 4 concentration
step. -/
def finiteQuenchedTailTau (σ : ℝ) : ℝ :=
  min σ 2

/-- The corrected finite-sigma exponent for Theorem `t.homogenization.quenched`,
written with an abstract `b = d / 2`. -/
noncomputable def interpolatedQuenchedTailExponent (b σ t : ℝ) : ℝ :=
  let τ : ℝ := finiteQuenchedTailTau σ
  (σ * τ * b * t) / (σ * t + τ * (b - t))

/-- Dimension-specialized version of `interpolatedQuenchedTailExponent`. -/
noncomputable def finiteQuenchedTailExponent (d : ℕ) (σ t : ℝ) : ℝ :=
  interpolatedQuenchedTailExponent ((d : ℝ) / 2) σ t

theorem finiteQuenchedTailTau_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < finiteQuenchedTailTau σ := by
  dsimp [finiteQuenchedTailTau]
  exact lt_min hσ (by norm_num : (0 : ℝ) < 2)

theorem finiteQuenchedTailDen_pos
    {b σ t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) :
    0 < σ * t + finiteQuenchedTailTau σ * (b - t) := by
  dsimp [finiteQuenchedTailTau]
  by_cases hσ2 : σ ≤ 2
  · rw [min_eq_left hσ2]
    nlinarith
  · have h2σ : 2 ≤ σ := le_of_not_ge hσ2
    rw [min_eq_right h2σ]
    nlinarith

theorem interpolatedQuenchedTailExponent_pos
    {b σ t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) :
    0 < interpolatedQuenchedTailExponent b σ t := by
  let τ : ℝ := finiteQuenchedTailTau σ
  have hτ : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ
  have hden : 0 < σ * t + τ * (b - t) := by
    simpa [τ] using finiteQuenchedTailDen_pos hb hσ ht
  dsimp [interpolatedQuenchedTailExponent, τ]
  exact div_pos (by positivity) hden

theorem finiteQuenchedTailExponent_pos
    {d : ℕ} [NeZero d] {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    0 < finiteQuenchedTailExponent d σ t := by
  have hb : 0 < (d : ℝ) / 2 := by
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  exact interpolatedQuenchedTailExponent_pos hb hσ ht

theorem interpolatedQuenchedTailExponent_le_tau_mul_b
    {b σ t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) (htb : t ≤ b) :
    interpolatedQuenchedTailExponent b σ t ≤
      finiteQuenchedTailTau σ * b := by
  let τ : ℝ := finiteQuenchedTailTau σ
  have hτ : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ
  have hden : 0 < σ * t + τ * (b - t) := by
    simpa [τ] using finiteQuenchedTailDen_pos hb hσ ht
  have hbt : 0 ≤ b - t := sub_nonneg.mpr htb
  dsimp [interpolatedQuenchedTailExponent, τ]
  rw [div_le_iff₀ hden]
  ring_nf
  nlinarith [mul_nonneg (mul_nonneg hτ.le hb.le) hbt]

theorem interpolatedQuenchedTailExponent_le_sigma_mul_t
    {b σ t : ℝ} (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) :
    interpolatedQuenchedTailExponent b σ t ≤ σ * t := by
  let τ : ℝ := finiteQuenchedTailTau σ
  have hτ_le_σ : τ ≤ σ := by
    dsimp [τ, finiteQuenchedTailTau]
    exact min_le_left σ 2
  have hden : 0 < σ * t + τ * (b - t) := by
    simpa [τ] using finiteQuenchedTailDen_pos hb hσ ht
  dsimp [interpolatedQuenchedTailExponent, τ]
  rw [div_le_iff₀ hden]
  ring_nf
  nlinarith [
    mul_nonneg (mul_nonneg hσ.le (mul_nonneg ht.le ht.le))
      (sub_nonneg.mpr hτ_le_σ)]

theorem interpolatedQuenchedTailExponent_le_mixed
    {b σ t : ℝ} :
    interpolatedQuenchedTailExponent b σ t ≤
      (σ * finiteQuenchedTailTau σ * b * t) /
        (σ * t + finiteQuenchedTailTau σ * (b - t)) := by
  rfl

/-- The mixed bottom exponent collapse.

In the bottom range, write `j = q - n`.  The localized tail contributes
`tau * (b*q - (b-t)*j)` and the crude tail contributes `sigma*t*j`.  Their
maximum dominates the corrected finite exponent times `q`. -/
theorem interpolatedQuenchedTailExponent_mul_le_max_mixed
    {b σ t q j : ℝ}
    (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) (htb : t ≤ b)
    (hj : 0 ≤ j) (hjq : j ≤ q) :
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := interpolatedQuenchedTailExponent b σ t
    η * q ≤ max (τ * (b * q - (b - t) * j)) (σ * t * j) := by
  intro τ η
  have hq : 0 ≤ q := hj.trans hjq
  have hτ : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ
  have hden : 0 < σ * t + τ * (b - t) := by
    simpa [τ] using finiteQuenchedTailDen_pos hb hσ ht
  have hσt : 0 < σ * t := mul_pos hσ ht
  have hη_le_tau_b : η ≤ τ * b := by
    simpa [η, τ] using
      interpolatedQuenchedTailExponent_le_tau_mul_b
        (b := b) (σ := σ) (t := t) hb hσ ht htb
  have hη_le_mixed :
      η ≤ (σ * τ * b * t) / (σ * t + τ * (b - t)) := by
    simpa [η, τ] using
      interpolatedQuenchedTailExponent_le_mixed
        (b := b) (σ := σ) (t := t)
  have hbt : 0 ≤ b - t := sub_nonneg.mpr htb
  by_cases hright : η * q ≤ σ * t * j
  · exact le_max_of_le_right hright
  · have hj_upper : j ≤ η * q / (σ * t) := by
      have hright' : ¬ η * q ≤ j * (σ * t) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hright
      exact (le_div_iff₀ hσt).2 (le_of_not_ge hright')
    have hηD :
        η * (σ * t + τ * (b - t)) ≤ σ * τ * b * t := by
      exact (le_div_iff₀ hden).1 hη_le_mixed
    have hcoeff :
        η ≤ τ * b - τ * (b - t) * η / (σ * t) := by
      rw [le_sub_iff_add_le]
      have hmul :
          (η + τ * (b - t) * η / (σ * t)) * (σ * t) ≤
            (τ * b) * (σ * t) := by
        field_simp [hσt.ne']
        ring_nf
        nlinarith [hηD]
      exact le_of_mul_le_mul_right hmul hσt
    have hcoeff_q :
        η * q ≤ (τ * b - τ * (b - t) * η / (σ * t)) * q :=
      mul_le_mul_of_nonneg_right hcoeff hq
    have hj_term :
        τ * (b - t) * j ≤ τ * (b - t) * (η * q / (σ * t)) := by
      have hfactor : 0 ≤ τ * (b - t) := mul_nonneg hτ.le hbt
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hj_upper hfactor
    have hleft :
        η * q ≤ τ * (b * q - (b - t) * j) := by
      calc
        η * q
            ≤ (τ * b - τ * (b - t) * η / (σ * t)) * q := hcoeff_q
        _ = τ * b * q - τ * (b - t) * (η * q / (σ * t)) := by
              field_simp [hσt.ne']
        _ ≤ τ * b * q - τ * (b - t) * j := by
              linarith
        _ = τ * (b * q - (b - t) * j) := by ring
    exact le_max_of_le_left hleft

/-- Mixed bottom collapse with the row gain retained.  The row variable `r`
is the distance above the bad scale; since both stochastic mechanisms gain
`(t - alpha) * r`, the maximum retains a positive weighted-kernel gain. -/
theorem interpolatedQuenchedTailExponent_mul_add_row_le_max_mixed
    {b σ t α q j r : ℝ}
    (hb : 0 < b) (hσ : 0 < σ) (ht : 0 < t) (hαt : α < t) (htb : t ≤ b)
    (hj : 0 ≤ j) (hjq : j ≤ q) (hr : 0 ≤ r) :
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := interpolatedQuenchedTailExponent b σ t
    η * q + τ * (t - α) * r ≤
      max
        (τ * (b * q - (b - t) * j + (t - α) * r))
        (σ * (t * j + (t - α) * r)) := by
  intro τ η
  have hbase :
      η * q ≤ max (τ * (b * q - (b - t) * j)) (σ * t * j) := by
    simpa [τ, η] using
      interpolatedQuenchedTailExponent_mul_le_max_mixed
        (b := b) (σ := σ) (t := t) (q := q) (j := j)
        hb hσ ht htb hj hjq
  have hτ_nonneg : 0 ≤ τ := (finiteQuenchedTailTau_pos hσ).le
  have hτ_le_σ : τ ≤ σ := by
    dsimp [τ, finiteQuenchedTailTau]
    exact min_le_left σ 2
  have hgap_nonneg : 0 ≤ t - α := (sub_pos.mpr hαt).le
  have hrow_le :
      τ * (t - α) * r ≤ σ * (t - α) * r := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hτ_le_σ hgap_nonneg) hr
  by_cases hleft :
      σ * t * j ≤ τ * (b * q - (b - t) * j)
  · have hmax_left :
        max (τ * (b * q - (b - t) * j)) (σ * t * j) =
          τ * (b * q - (b - t) * j) := max_eq_left hleft
    calc
      η * q + τ * (t - α) * r
          ≤ τ * (b * q - (b - t) * j) + τ * (t - α) * r := by
            linarith [hbase, hmax_left]
      _ = τ * (b * q - (b - t) * j + (t - α) * r) := by ring
      _ ≤ max
          (τ * (b * q - (b - t) * j + (t - α) * r))
          (σ * (t * j + (t - α) * r)) := le_max_left _ _
  · have hmax_right :
        max (τ * (b * q - (b - t) * j)) (σ * t * j) =
          σ * t * j := max_eq_right (le_of_not_ge hleft)
    calc
      η * q + τ * (t - α) * r
          ≤ σ * t * j + τ * (t - α) * r := by
            linarith [hbase, hmax_right]
      _ ≤ σ * t * j + σ * (t - α) * r := by linarith
      _ = σ * (t * j + (t - α) * r) := by ring
      _ ≤ max
          (τ * (b * q - (b - t) * j + (t - α) * r))
          (σ * (t * j + (t - α) * r)) := le_max_right _ _

/-- Dimension-specialized high-top collapse: the finite bad-scale exponent is
no larger than the localized `tau * d/2` exponent. -/
theorem finiteQuenchedTailExponent_mul_nat_le_tau_mul_b_nat
    {d : ℕ} [NeZero d] {σ t : ℝ} {q : ℕ}
    (hσ : 0 < σ) (ht : 0 < t) (htb : t ≤ (d : ℝ) / 2) :
    finiteQuenchedTailExponent d σ t * (q : ℝ) ≤
      finiteQuenchedTailTau σ * ((d : ℝ) / 2) * (q : ℝ) := by
  have hb : 0 < (d : ℝ) / 2 := by
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  exact mul_le_mul_of_nonneg_right
    (by
      simpa [finiteQuenchedTailExponent] using
        interpolatedQuenchedTailExponent_le_tau_mul_b
          (b := (d : ℝ) / 2) (σ := σ) (t := t) hb hσ ht htb)
    (by positivity)

/-- Dimension-specialized crude-bottom collapse: the finite bad-scale exponent
is no larger than the crude `sigma * t` exponent. -/
theorem finiteQuenchedTailExponent_mul_nat_le_sigma_mul_t_nat
    {d : ℕ} [NeZero d] {σ t : ℝ} {q : ℕ}
    (hσ : 0 < σ) (ht : 0 < t) :
    finiteQuenchedTailExponent d σ t * (q : ℝ) ≤
      σ * t * (q : ℝ) := by
  have hb : 0 < (d : ℝ) / 2 := by
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  exact mul_le_mul_of_nonneg_right
    (by
      simpa [finiteQuenchedTailExponent] using
        interpolatedQuenchedTailExponent_le_sigma_mul_t
          (b := (d : ℝ) / 2) (σ := σ) (t := t) hb hσ ht)
    (by positivity)

/-- Dimension-specialized mixed-bottom collapse in shifted natural indices.
Here `j = q - n` is the distance from the bad scale down to the bottom scale. -/
theorem finiteQuenchedTailExponent_mul_nat_le_max_bottom
    {d q n : ℕ} [NeZero d] {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (htb : t ≤ (d : ℝ) / 2) :
    let b : ℝ := (d : ℝ) / 2
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let j : ℝ := ((q - n : ℕ) : ℝ)
    η * (q : ℝ) ≤ max (τ * (b * (q : ℝ) - (b - t) * j)) (σ * t * j) := by
  intro b τ η j
  have hb : 0 < b := by
    dsimp [b]
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hj_nonneg : 0 ≤ j := by
    dsimp [j]
    positivity
  have hj_le_q : j ≤ (q : ℝ) := by
    dsimp [j]
    exact_mod_cast Nat.sub_le q n
  simpa [finiteQuenchedTailExponent, b, τ, η, j] using
    interpolatedQuenchedTailExponent_mul_le_max_mixed
      (b := b) (σ := σ) (t := t) (q := (q : ℝ)) (j := j)
      hb hσ ht (by simpa [b] using htb) hj_nonneg hj_le_q

/-- Dimension-specialized mixed-bottom collapse with the row gain retained. -/
theorem finiteQuenchedTailExponent_mul_nat_add_row_le_max_bottom
    {d q n r : ℕ} [NeZero d] {σ t α : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (hαt : α < t)
    (htb : t ≤ (d : ℝ) / 2) :
    let b : ℝ := (d : ℝ) / 2
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let j : ℝ := ((q - n : ℕ) : ℝ)
    η * (q : ℝ) + τ * (t - α) * (r : ℝ) ≤
      max
        (τ * (b * (q : ℝ) - (b - t) * j + (t - α) * (r : ℝ)))
        (σ * (t * j + (t - α) * (r : ℝ))) := by
  intro b τ η j
  have hb : 0 < b := by
    dsimp [b]
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hj_nonneg : 0 ≤ j := by
    dsimp [j]
    positivity
  have hj_le_q : j ≤ (q : ℝ) := by
    dsimp [j]
    exact_mod_cast Nat.sub_le q n
  have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
  simpa [finiteQuenchedTailExponent, b, τ, η, j] using
    interpolatedQuenchedTailExponent_mul_add_row_le_max_mixed
      (b := b) (σ := σ) (t := t) (α := α)
      (q := (q : ℝ)) (j := j) (r := (r : ℝ))
      hb hσ ht hαt (by simpa [b] using htb) hj_nonneg hj_le_q hr_nonneg

end

end Section57
end Ch05
end Book
end Homogenization
