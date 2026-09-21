/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentSummation
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry

/-! # Bad Scale Component Rows -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Row estimates for split bad-scale components

The lemmas in this file are deliberately small.  They convert a fixed-pair
tail bound, a deterministic lower bound on the tail parameter, and a
descendant-cardinality estimate into the weighted row estimates needed by the
component summation lemmas.
-/

noncomputable section

private theorem exp_neg_rpow_le_exp_neg_rpow_of_le
    {x y τ : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hτ : 0 < τ) :
    Real.exp (-(y ^ τ)) ≤ Real.exp (-(x ^ τ)) := by
  have hpow : x ^ τ ≤ y ^ τ :=
    Real.rpow_le_rpow hx hxy hτ.le
  exact Real.exp_le_exp.mpr (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- High-bottom row estimate from a fixed-pair no-log bound and deterministic
weight estimates. -/
theorem measureReal_highBottomPairEvent_le_weighted_row_of_badPair_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n r : ℕ}
    {S D A ρ τ lam w : ℝ}
    (hS : 0 ≤ S) (hw : 0 ≤ w) (hD : D ≤ w ^ q * w ^ r)
    (hAρ_nonneg : 0 ≤ A * ρ ^ r)
    (hlam : A * ρ ^ r ≤ lam) (hτ : 0 < τ)
    (hbad :
      μ.real (badPairEvent H t α q m n) ≤
        S * (D * Real.exp (-(lam ^ τ)))) :
    μ.real (highBottomPairEvent H K a t α q m n) ≤
      (S * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
  have hmono :
      μ.real (highBottomPairEvent H K a t α q m n) ≤
        μ.real (badPairEvent H t α q m n) := by
    exact measureReal_mono
      (by
        intro ω hω
        exact hω.2.2)
  have hexp :
      Real.exp (-(lam ^ τ)) ≤
        Real.exp (-((A * ρ ^ r) ^ τ)) :=
    exp_neg_rpow_le_exp_neg_rpow_of_le hAρ_nonneg hlam hτ
  have hDexp :
      D * Real.exp (-(lam ^ τ)) ≤
        (w ^ q * w ^ r) *
          Real.exp (-((A * ρ ^ r) ^ τ)) :=
    mul_le_mul hD hexp (by positivity)
      (mul_nonneg (pow_nonneg hw q) (pow_nonneg hw r))
  have htail :
      S * (D * Real.exp (-(lam ^ τ))) ≤
        (S * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
    calc
      S * (D * Real.exp (-(lam ^ τ)))
          ≤ S *
              ((w ^ q * w ^ r) *
                Real.exp (-((A * ρ ^ r) ^ τ))) :=
            mul_le_mul_of_nonneg_left hDexp hS
      _ = (S * w ^ q) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
            ring
  exact hmono.trans (hbad.trans htail)

/-- Crude-bottom row estimate from a fixed-pair crude bound and deterministic
weight estimates. -/
theorem measureReal_crudeBottomPairEvent_le_weighted_row_of_badPair_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n r : ℕ}
    {S D A ρ σ lam w : ℝ}
    (hS : 0 ≤ S) (hw : 0 ≤ w) (hD : D ≤ w ^ q * w ^ r)
    (hAρ_nonneg : 0 ≤ A * ρ ^ r)
    (hlam : A * ρ ^ r ≤ lam) (hσ : 0 < σ)
    (hbad :
      μ.real (badPairEvent H t α q m n) ≤
        S * (D * Real.exp (-(lam ^ σ)))) :
    μ.real (crudeBottomPairEvent H K a t α q m n) ≤
      (S * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
  have hmono :
      μ.real (crudeBottomPairEvent H K a t α q m n) ≤
        μ.real (badPairEvent H t α q m n) := by
    exact measureReal_mono
      (by
        intro ω hω
        exact hω.2.2)
  have hexp :
      Real.exp (-(lam ^ σ)) ≤
        Real.exp (-((A * ρ ^ r) ^ σ)) :=
    exp_neg_rpow_le_exp_neg_rpow_of_le hAρ_nonneg hlam hσ
  have hDexp :
      D * Real.exp (-(lam ^ σ)) ≤
        (w ^ q * w ^ r) *
          Real.exp (-((A * ρ ^ r) ^ σ)) :=
    mul_le_mul hD hexp (by positivity)
      (mul_nonneg (pow_nonneg hw q) (pow_nonneg hw r))
  have htail :
      S * (D * Real.exp (-(lam ^ σ))) ≤
        (S * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
    calc
      S * (D * Real.exp (-(lam ^ σ)))
          ≤ S *
              ((w ^ q * w ^ r) *
                Real.exp (-((A * ρ ^ r) ^ σ))) :=
            mul_le_mul_of_nonneg_left hDexp hS
      _ = (S * w ^ q) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
            ring
  exact hmono.trans (hbad.trans htail)

/-- Descendant-cardinality weight for bottom rows.  In the range
`n = q - j`, `m = q + r`, the number of descendants is bounded by
`(3^d)^q (3^d)^r`. -/
theorem descendantsAtScale_bottom_row_card_le_weight
    {d : ℕ} {N q r : ℕ} {j : Fin (q + 1)}
    (hnm : q - j.val ≤ q + r) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale
        (originCube d (((N + (q + r) : ℕ) : ℤ)))
        (((N + (q - j.val) : ℕ) : ℤ))
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    (D.card : ℝ) ≤ w ^ q * w ^ r := by
  intro D w
  have hcard :
      D.card = (3 ^ d) ^ ((q + r) - (q - j.val)) := by
    simpa [D] using
      descendantsAtScale_originCube_nat_shift_card
        (d := d) (N := N) (m := q + r) (n := q - j.val) hnm
  have hgap_le : (q + r) - (q - j.val) ≤ q + r := by
    exact Nat.sub_le (q + r) (q - j.val)
  have hpow_le_nat : (3 ^ d) ^ ((q + r) - (q - j.val)) ≤ (3 ^ d) ^ (q + r) :=
    Nat.pow_le_pow_right
      (by exact pow_pos (by norm_num : (0 : ℕ) < 3) d) hgap_le
  dsimp [w]
  rw [hcard]
  have hcast :
      (((3 ^ d) ^ (q + r) : ℕ) : ℝ) =
        (((3 ^ d : ℕ) : ℝ) ^ q) * (((3 ^ d : ℕ) : ℝ) ^ r) := by
    norm_num [pow_add]
  calc
    (((3 ^ d) ^ ((q + r) - (q - j.val)) : ℕ) : ℝ)
        ≤ (((3 ^ d) ^ (q + r) : ℕ) : ℝ) := by
          exact_mod_cast hpow_le_nat
    _ = (((3 ^ d : ℕ) : ℝ) ^ q) * (((3 ^ d : ℕ) : ℝ) ^ r) := hcast

end

end Section57
end Ch05
end Book
end Homogenization
