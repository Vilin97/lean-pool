/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Queries.BoundedMean.Basic
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Queries.Histogram.Basic
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.System
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.System
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Queries.HistogramMean.Properties
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Approximate.DP
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Gaussian.Properties
import Init.Data.UInt.Lemmas

open SLang PMF

def combineConcentrated := @privNoisedBoundedMean_DP gaussian_zCDPSystem
def combinePure := @privNoisedBoundedMean_DP PureDPSystem

/-
##  Example: execute the histogram mean on a list
-/
section histogramMeanExample

def numBins : ℕ+ := 64

/-
Bin the infinite type ℕ with clipping
-/
def bin (n : ℕ) : Fin numBins :=
  { val := min (Nat.log 2 n) (PNat.natPred numBins),
    isLt := by
      apply min_lt_iff.mpr
      right
      exact Nat.lt_of_sub_eq_succ rfl
  }

/-
Return an upper bound on the bin value, clipped to 2^(1 + numBins)
-/
def unbin (n : Fin numBins) : ℕ+ := 2 ^ (1 + n.val)

noncomputable def combineMeanHistogram : Mechanism ℕ (Option ℚ) :=
  privMeanHistogram PureDPSystem numBins { bin } unbin 1 20 2 1 20

end histogramMeanExample

-- The following is unsound and should NOT be part of the code
-- We are using it for now until the Python FFI is richer
@[extern "dirty_io_get"]
opaque DirtyIOGet(x : IO ℤ) : UInt32

lemma UInt32.toNa_of_non_zero {n : UInt32} (h : n ≠ 0) :
  0 < n.toNat := by
  have A : n.toNat ≠ 0 := by
    rw [← UInt32.zero_toNat]
    by_contra
    rename_i h'
    have B := UInt32.toNat.inj h'
    contradiction
  exact Nat.zero_lt_of_ne_zero A

@[export dgs_get]
def DiscreteGaussianSampleGet (num den : UInt32) (mix: UInt32) :
    UInt32 := Id.run do
  if h₁ : num = 0 then
    panic "DiscreteGaussianSampleGet was called with num = 0"
  else if h₂ : den = 0 then
    panic "DiscreteGaussianSampleGet was called with den = 0"
  else
    let z : IO ℤ ← run <| DiscreteGaussianPMF ⟨ num.toNat , UInt32.toNa_of_non_zero h₁ ⟩ ⟨ den.toNat , UInt32.toNa_of_non_zero h₂ ⟩ mix.toNat
    return DirtyIOGet z
