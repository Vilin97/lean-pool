/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionAlgebra
import LeanPool.Feige.Lemma43ArbitraryBase
import LeanPool.Feige.Lemma43FiniteSigned

/-!
# The local transfer result in the insertion-sequence interface

The analytic transfer statement is phrased in terms of two probability
laws, while the chain-insertion step consumes four numerical sequences along
an old Boolean chain.  This file records the exact, purely algebraic
interface between those two presentations.
-/

open MeasureTheory

namespace Feige
namespace Lemma43

theorem theta_nonneg (ν : Measure ℝ) (c d : ℝ) :
    0 ≤ theta ν c d := by
  unfold theta w u v
  exact div_nonneg ENNReal.toReal_nonneg
    (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- The entries of the insertion sequences at one edge are represented by
the two laws occurring in the local transfer step. -/
def RealizesInsertionEdge
    (upper old width interpolation : ℕ → ℝ) (j : ℕ)
    (νP νM : Measure ℝ) (c d : ℝ) : Prop :=
  upper j = A νP d ∧
  upper (j + 1) = A νM d ∧
  old j = F νP ∧
  old (j + 1) = F νM ∧
  width j = w νP c d ∧
  interpolation j = theta νP c d ∧
  interpolation (j + 1) = theta νM c d

/-- The factorized local transfer identity is exactly the identity required
on one chain-insertion edge. -/
theorem insertionTransfer_eq_of_realizesInsertionEdge
    {upper old width interpolation : ℕ → ℝ} {j : ℕ}
    {νP νM : Measure ℝ} {a c d : ℝ}
    (hreal :
      RealizesInsertionEdge upper old width interpolation j νP νM c d)
    (hid :
      (1 - theta νM c d) * (A νP d - A νM d) -
          (c / (c + d)) * (F νP - F νM) =
        ((a - c) / (c + d)) * w νP c d *
          (theta νP c d - theta νM c d)) :
    insertionTransfer upper old interpolation (c / (c + d)) j =
      ((a - c) / (c + d)) * width j *
        (interpolation j - interpolation (j + 1)) := by
  rcases hreal with
    ⟨hAj, hAs, hFj, hFs, hwj, hθj, hθs⟩
  unfold insertionTransfer insertedUpperMass independentUpperMass
  rw [hAj, hAs, hFj, hFs, hwj, hθj, hθs]
  exact hid

/-- The order and denominator conclusions of the local transfer result pass
verbatim to adjacent entries of the insertion sequences. -/
theorem insertion_order_widths_of_realizesInsertionEdge
    {upper old width interpolation : ℕ → ℝ} {j : ℕ}
    {νP νM : Measure ℝ} {c d : ℝ}
    (hreal :
      RealizesInsertionEdge upper old width interpolation j νP νM c d)
    (horder : theta νM c d ≤ theta νP c d)
    (hwP : 0 < w νP c d) :
    interpolation (j + 1) ≤ interpolation j ∧
      0 < width j := by
  rcases hreal with
    ⟨_hAj, _hAs, _hFj, _hFs, hwj, hθj, hθs⟩
  constructor
  · rw [hθs, hθj]
    exact horder
  · rw [hwj]
    exact hwP

/-- A full `CompleteConclusion` immediately supplies every analytic fact
needed by the insertion algorithm on a realized edge. -/
theorem insertion_conclusions_of_complete
    {upper old width interpolation : ℕ → ℝ} {j : ℕ}
    {f : ℝ → ENNReal} {a b c d : ℝ}
    (hreal :
      RealizesInsertionEdge upper old width interpolation j
        (TransferStein.zPlusLaw (volume.withDensity f) a)
        (TransferStein.zMinusLaw (volume.withDensity f) b) c d)
    (hcomplete : CompleteConclusion f a b c d) :
    insertionTransfer upper old interpolation (c / (c + d)) j =
        ((a - c) / (c + d)) * width j *
          (interpolation j - interpolation (j + 1)) ∧
      interpolation (j + 1) ≤ interpolation j ∧
      0 < width j := by
  rcases hcomplete with ⟨hid, horder, hwP, _hwM⟩
  refine ⟨insertionTransfer_eq_of_realizesInsertionEdge hreal hid, ?_⟩
  exact insertion_order_widths_of_realizesInsertionEdge
    hreal horder hwP

/-- The local transfer result for finite signed-exponential common parts,
now exposed directly in the insertion-sequence interface. -/
theorem finiteSignedExp_insertion_conclusions
    (Fs : List LikelihoodRatio.SignedExpFactor)
    {upper old width interpolation : ℕ → ℝ} {j : ℕ}
    {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hreal :
      RealizesInsertionEdge upper old width interpolation j
        (TransferStein.zPlusLaw
          (volume.withDensity
            (LikelihoodRatio.finiteSignedExpSumDensity Fs)) a)
        (TransferStein.zMinusLaw
          (volume.withDensity
            (LikelihoodRatio.finiteSignedExpSumDensity Fs)) b)
        c d) :
    insertionTransfer upper old interpolation (c / (c + d)) j =
        ((a - c) / (c + d)) * width j *
          (interpolation j - interpolation (j + 1)) ∧
      interpolation (j + 1) ≤ interpolation j ∧
      0 < width j := by
  exact insertion_conclusions_of_complete hreal
    (finiteSignedExp_complete Fs ha hb hc hd)

/-- The terminal edge changes the distinguished exponential from `+E₀` to
`-E₀`.  The factorized transfer identity still holds for its arbitrary
common law; support on the nonpositive half-line makes the negative
endpoint's interpolation parameter zero, which is all the order information
needed there. -/
theorem terminal_insertion_conclusions
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Ioi 0) = 0)
    {upper old width interpolation : ℕ → ℝ} {j : ℕ}
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hreal :
      RealizesInsertionEdge upper old width interpolation j
        (TransferStein.zPlusLaw μ 1)
        (TransferStein.zMinusLaw μ 1) c d) :
    insertionTransfer upper old interpolation (c / (c + d)) j =
        ((1 - c) / (c + d)) * width j *
          (interpolation j - interpolation (j + 1)) ∧
      interpolation (j + 1) ≤ interpolation j ∧
      0 < width j := by
  obtain ⟨hid, hwP, _hwM⟩ :=
    Lemma43ArbitraryBase.identity_and_w_pos μ
      (a := (1 : ℝ)) (b := (1 : ℝ)) one_pos one_pos hc hd
  obtain ⟨_hFminus, hθminus⟩ :=
    Lemma43ArbitraryBase.terminal_zMinus μ hpos
      (b := (1 : ℝ)) (c := c) (d := d) one_pos
  refine
    ⟨insertionTransfer_eq_of_realizesInsertionEdge hreal hid, ?_⟩
  apply insertion_order_widths_of_realizesInsertionEdge hreal
  · rw [hθminus]
    exact theta_nonneg _ _ _
  · exact hwP

end Lemma43
end Feige
