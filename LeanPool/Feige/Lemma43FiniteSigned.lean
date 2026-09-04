/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionCommonDensity
import LeanPool.Feige.Lemma43Complete

/-!
# Local transfer for finite signed-exponential common parts

This module specializes the automatic pushforward-density and
likelihood-ratio results to the exact common laws appearing on genuine
Boolean-lattice insertion edges.
-/

open MeasureTheory

namespace Feige
namespace Lemma43

open TransferStein
open LikelihoodRatio

/-- The complete four-part local-transfer conclusion for the two exponential
shifts of a base density. -/
def CompleteConclusion
    (f : ℝ → ENNReal) (a b c d : ℝ) : Prop :=
  let νP := zPlusLaw (volume.withDensity f) a
  let νM := zMinusLaw (volume.withDensity f) b
  ((1 - theta νM c d) * (A νP d - A νM d) -
        (c / (c + d)) * (F νP - F νM) =
      ((a - c) / (c + d)) * w νP c d *
        (theta νP c d - theta νM c d)) ∧
    theta νM c d ≤ theta νP c d ∧
    0 < w νP c d ∧ 0 < w νM c d

/-- The order half of the local transfer result for a distinguished
exponential plus an arbitrary finite list of signed scaled exponentials. -/
theorem finiteSignedExp_theta_order
    (Fs : List SignedExpFactor)
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    theta
        (zMinusLaw
          (volume.withDensity (finiteSignedExpSumDensity Fs)) b) c d ≤
      theta
        (zPlusLaw
          (volume.withDensity (finiteSignedExpSumDensity Fs)) a) c d :=
  Lemma43Density.theta_order_zPlus_zMinus
    (measurable_finiteSignedExpSumDensity Fs)
    (fourPointLogConcave_finiteSignedExpSumDensity Fs)
    ha hb hc hd

/-- The full local transfer result, with every analytic and probability
hypothesis discharged, for a finite signed-exponential common part. -/
theorem finiteSignedExp_complete
    (Fs : List SignedExpFactor)
    {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    CompleteConclusion (finiteSignedExpSumDensity Fs) a b c d := by
  simpa only [CompleteConclusion] using
    Lemma43Complete.complete_for_density
      (measurable_finiteSignedExpSumDensity Fs)
      (fourPointLogConcave_finiteSignedExpSumDensity Fs)
      ha hb hc hd

/-- Actual insertion-edge specialization: the changed low coordinate is
the positive shift and the changed high coordinate is the negative shift. -/
theorem commonFactors_theta_order
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    theta
        (zMinusLaw
          (volume.withDensity
            (finiteSignedExpSumDensity
              (commonFactors γ β hγ hβ S changed)))
          (β changed)) c d ≤
      theta
        (zPlusLaw
          (volume.withDensity
            (finiteSignedExpSumDensity
              (commonFactors γ β hγ hβ S changed)))
          (γ changed)) c d :=
  finiteSignedExp_theta_order _
    (hγ changed).le (hβ changed).le hc hd

/-- The full automatic local transfer result on every genuine insertion
edge. -/
theorem commonFactors_complete
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    CompleteConclusion
      (finiteSignedExpSumDensity
        (commonFactors γ β hγ hβ S changed))
      (γ changed) (β changed) c d :=
  finiteSignedExp_complete _
    (hγ changed) (hβ changed) hc hd

end Lemma43
end Feige
