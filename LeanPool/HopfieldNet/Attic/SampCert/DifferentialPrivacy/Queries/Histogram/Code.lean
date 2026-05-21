/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector.Basic

/-!
# ``privHistogram`` Implementation

This file implements a logarithmic histogram with noised bins
-/

/--
Function to categorize values of type T into ``num_bins.succ`` distinct bins.
-/
structure Bins (T : Type) (num_bins : ℕ) where
  bin : T -> Fin num_bins


/-!
## Private Histograms
-/

noncomputable section

variable (numBins : ℕ+)

def predBins : ℕ := numBins.natPred

def predBins_lt_numBins : predBins numBins < numBins := by
  rw [predBins]
  cases numBins
  rename_i v Hv
  simp only [PNat.natPred_eq_pred, Nat.pred_eq_sub_one, PNat.mk_coe, tsub_lt_self_iff, zero_lt_one, and_true]
  assumption

/--
A histogram with a fixed binning method and ``i+1`` bins

Counts in the histogram are permitted to be negative.
-/
structure Histogram (T : Type) (num_bins : ℕ+) (B : Bins T num_bins) where
  count : sorry--Mathlib.Vector ℤ num_bins

variable {T : Type}
variable (B : Bins T numBins)

/--
Construct an empty histagram
-/
def emptyHistogram : Histogram T numBins B := sorry
  --Histogram.mk (Mathlib.Vector.replicate numBins 0)

-- Is there any way to get the discrete measure space for free?
-- instance : MeasurableSpace (Histogram T numBins B) where
--   MeasurableSet' _ := True
--   measurableSet_empty := by simp
--   measurableSet_compl := by simp
--   measurableSet_iUnion := by simp

-- There's probably an easier way to do this?
instance : Countable (Histogram T numBins B) where
  exists_injective_nat' := by stop
    have Y : ∃ f : Mathlib.Vector ℤ numBins -> ℕ, Function.Injective f := by exact Countable.exists_injective_nat'
    rcases Y with ⟨ f, Hf ⟩
    exists (fun h => f h.count)
    intro h₁ h₂
    simp
    intro Heq
    cases h₁
    cases h₂
    simp_all
    apply Hf
    apply Heq


instance : Inhabited (Histogram T numBins B) where
  default := emptyHistogram numBins B

-- instance : DiscreteMeasurableSpace (Histogram T numBins B) where
--   forall_measurableSet := by simp

namespace SLang

variable [dps : DPSystem T]

/--
Compute the exact number of elements inside a histogram bin
-/
def exactBinCount (b : Fin numBins) (l : List T) : ℤ :=
  List.length (List.filter (fun v => B.bin v = b) l)

/--
Compute a noised count of the number of list elements inside a particular histogram bin
-/
def privNoisedBinCount (ε₁ ε₂ : ℕ+) (b : Fin numBins) : Mechanism T ℤ :=
  (dps.noise (exactBinCount numBins B b) 1 ε₁ (ε₂ * numBins))

/--
Modify a count inside a Histogram
-/
def setCount (h : Histogram T numBins B) (b : Fin numBins) (v : ℤ) : Histogram T numBins B := sorry
  --{ h with count := h.count.set b v }


def privNoisedHistogramAux (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) : Mechanism T (Histogram T numBins B) :=
  let privNoisedHistogramAux_rec :=
    match n with
    | Nat.zero => privConst (emptyHistogram numBins B)
    | Nat.succ n' => privNoisedHistogramAux ε₁ ε₂ n' (Nat.lt_of_succ_lt Hn)
  privPostProcess
    (privCompose (privNoisedBinCount numBins B ε₁ ε₂ n) privNoisedHistogramAux_rec)
    (fun z => setCount numBins B z.2 n z.1)


/--
Histogram with noise added to each count
-/
def privNoisedHistogram (ε₁ ε₂ : ℕ+) : Mechanism T (Histogram T numBins B) :=
  privNoisedHistogramAux numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins)


/--
Compute the maximum bin above threshold
-/
def exactMaxBinAboveThresholdAux (τ : ℤ) (n : ℕ) (Hn : n < numBins) (h : Histogram T numBins B) : Option (Fin numBins) := sorry
--by
  -- match n with
  -- | Nat.zero => none
  -- | Nat.succ n' =>
  --   let n_fin := (Fin.mk n'.succ Hn)
  --   if (h.count.get n_fin > τ)
  --     then some n_fin
  --     else exactMaxBinAboveThresholdAux τ n' (Nat.lt_of_succ_lt Hn) h

/--
Compute the noisy maximum histogram bin whose value exeeds τ
-/
def privMaxBinAboveThreshold (ε₁ ε₂ : ℕ+) (τ : ℤ) : Mechanism T (Option (Fin numBins)) := sorry
  -- privPostProcess
  --   (privNoisedHistogram numBins B ε₁ ε₂)
  --   (exactMaxBinAboveThresholdAux numBins B τ (predBins numBins) (predBins_lt_numBins numBins))

end SLang
