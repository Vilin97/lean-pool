/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Lean.Elab.Tactic.Omega
import LeanPool.OrdvecFormalization.BitmapNull
import LeanPool.OrdvecFormalization.OverlapSufficiency

/-!
# Constant-weight bitmap incidence

This file contains reusable definitions connecting literal constant-weight
bitmap overlap to the feasible ordered overlap support.
-/

open scoped NNReal ENNReal

namespace OrdvecFormalization

/-- FNCH overlap parameters for two `K`-active bitmaps in a `D`-coordinate universe. -/
def bitmapOverlapParams (D K : ℕ) (hK : K ≤ D) : FNCHParams where
  N := D
  k := K
  draws := K
  k_le_N := hK
  draws_le_N := hK

/-- Threshold cuts for the feasible overlap range of two `K`-active bitmaps. -/
abbrev BitmapCut (D K : ℕ) (hK : K ≤ D) :=
  Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2)

/-- The actual overlap threshold represented by a feasible bitmap cut. -/
def bitmapCutThreshold {D K : ℕ} (hK : K ≤ D) (cut : BitmapCut D K hK) : ℕ :=
  (bitmapOverlapParams D K hK).lo + cut.val

/-- The finite type of `K`-active bitmaps in a `D`-coordinate universe. -/
abbrev ConstantWeightBitmap (D K : ℕ) :=
  {d : Finset (BitmapCoord D) // d ∈ constantWeightBitmapSpace D K}

@[simp]
theorem constantWeightBitmap_card {D K : ℕ} (d : ConstantWeightBitmap D K) :
    d.val.card = K :=
  mem_constantWeightBitmapSpace_iff.mp d.property

/-- Uniform finite law over the `K`-active bitmap subtype. -/
noncomputable def constantWeightBitmapUniformLaw (D K : ℕ) (hK : K ≤ D) :
    FiniteLaw (ConstantWeightBitmap D K) where
  mass _ := ((D.choose K : ℝ≥0)⁻¹)
  pos _ := by
    have hchoose : 0 < (D.choose K : ℝ≥0) := by
      exact_mod_cast Nat.choose_pos hK
    exact inv_pos.mpr hchoose
  sum_one := by
    have hcard : Fintype.card (ConstantWeightBitmap D K) = D.choose K := by
      simp [ConstantWeightBitmap]
    have hchoose : (D.choose K : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hK
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ hchoose

/-- The literal overlap tail event on the `K`-active bitmap subtype. -/
def constantWeightBitmapOverlapTailSet (D K t : ℕ) (q : Finset (BitmapCoord D)) :
    Set (ConstantWeightBitmap D K) :=
  {d | t ≤ bitmapOverlap q d.val}

theorem bitmapOverlapParams_lo_le_overlap {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) (hd : d.card = K) :
    (bitmapOverlapParams D K hK).lo ≤ bitmapOverlap q d := by
  have hUnionLe : (q ∪ d).card ≤ D := by
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (q ∪ d : Finset (BitmapCoord D)))
  have hCard : (q ∪ d).card + bitmapOverlap q d = K + K := by
    simpa [bitmapOverlap, hq, hd] using Finset.card_union_add_card_inter q d
  change K + K - D ≤ bitmapOverlap q d
  omega

theorem bitmapOverlap_le_bitmapOverlapParams_hi {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapOverlap q d ≤ (bitmapOverlapParams D K hK).hi := by
  have hOverlap : bitmapOverlap q d ≤ K := by
    rw [bitmapOverlap, ← hq]
    exact Finset.card_le_card Finset.inter_subset_left
  simpa [bitmapOverlapParams, FNCHParams.hi] using hOverlap

/--
Literal bitmap overlap, shifted into the feasible FNCH support for two
`K`-active bitmaps.
-/
def constantWeightBitmapOverlapEvidence {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ConstantWeightBitmap D K → (bitmapOverlapParams D K hK).support :=
  fun d =>
    let p : FNCHParams := bitmapOverlapParams D K hK
    let x := bitmapOverlap q d.val - p.lo
    ⟨x, by
      have hd : d.val.card = K := constantWeightBitmap_card d
      have hlo : p.lo ≤ bitmapOverlap q d.val :=
        bitmapOverlapParams_lo_le_overlap hK hq hd
      have hhi : bitmapOverlap q d.val ≤ p.hi :=
        bitmapOverlap_le_bitmapOverlapParams_hi hK hq
      change bitmapOverlap q d.val - p.lo < p.hi - p.lo + 1
      omega⟩

@[simp]
theorem constantWeightBitmapOverlapEvidence_overlap {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) (d : ConstantWeightBitmap D K) :
    (bitmapOverlapParams D K hK).overlap (constantWeightBitmapOverlapEvidence hK hq d) =
      bitmapOverlap q d.val := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  have hd : d.val.card = K := constantWeightBitmap_card d
  have hlo : p.lo ≤ bitmapOverlap q d.val :=
    bitmapOverlapParams_lo_le_overlap hK hq hd
  simp [constantWeightBitmapOverlapEvidence, FNCHParams.overlap, p, Nat.add_sub_of_le hlo]

/-- Pulled-back actual-overlap quotient thresholds are literal bitmap overlap tails. -/
theorem overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq {D K : ℕ}
    (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2)) :
    overlapQuotientThresholdSet (bitmapOverlapParams D K hK)
        (fun d : ConstantWeightBitmap D K => d) (constantWeightBitmapOverlapEvidence hK hq) cut =
      constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q := by
  ext d
  simp [overlapQuotientThresholdSet, actualOverlapThresholdSet, constantWeightBitmapOverlapTailSet]

end OrdvecFormalization
