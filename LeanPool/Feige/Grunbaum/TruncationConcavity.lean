/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import LeanPool.Feige.Grunbaum.Definitions
import LeanPool.Isoperimetric.BrunnMinkowski
import Mathlib.Analysis.Convex.Function

/-!
# Concavity of truncated-volume roots
-/

open MeasureTheory Set
open scoped Pointwise

namespace Grunbaum

/-- The part of `C` cut out by the sublevel halfspace of `ℓ` at `t`. -/
def trunc {d : ℕ} (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : Set (Euc d) :=
  C ∩ ℓ ⁻¹' Set.Iic t

/-- The dimension-normalized root of a truncation's volume. -/
noncomputable def truncRoot {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  (volume (trunc C ℓ t) ^ ((d : ℝ) + 1)⁻¹).toReal

/-- The dimension-normalized root of the truncation's volume ratio. -/
noncomputable def cdfRoot {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ((volume (trunc C ℓ t) / volume C) ^ ((d : ℝ) + 1)⁻¹).toReal

/-- Thresholds for which the corresponding truncation is nonempty. -/
def truncDomain {d : ℕ} (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) : Set ℝ :=
  {t | (trunc C ℓ t).Nonempty}

lemma isCompact_trunc {d : ℕ} {C : Set (Euc d)} (hC : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    IsCompact (trunc C ℓ t) :=
  hC.inter_right (isClosed_Iic.preimage ℓ.continuous)

lemma volume_trunc_ne_top {d : ℕ} {C : Set (Euc d)} (hC : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    volume (trunc C ℓ t) ≠ ⊤ :=
  (isCompact_trunc hC ℓ t).measure_lt_top.ne

private lemma volume_smul_rpow {d : ℕ} (S : Set (Euc d))
    (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S) ^ ((d : ℝ) + 1)⁻¹ =
      ENNReal.ofReal a * volume S ^ ((d : ℝ) + 1)⁻¹ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) ha]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow ha]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    ENNReal.pow_rpow_inv_natCast (Nat.succ_ne_zero d) (ENNReal.ofReal a)

private lemma weighted_trunc_subset {d : ℕ} {C : Set (Euc d)}
    (hC : Convex ℝ C) (ℓ : Euc d →L[ℝ] ℝ)
    {s t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • trunc C ℓ s + b • trunc C ℓ t ⊆ trunc C ℓ (a * s + b * t) := by
  rintro z ⟨ax, ⟨x, hx, rfl⟩, by_, ⟨y, hy, rfl⟩, rfl⟩
  change x ∈ C ∧ ℓ x ≤ s at hx
  change y ∈ C ∧ ℓ y ≤ t at hy
  refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
  change ℓ (a • x + b • y) ≤ a * s + b * t
  simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
    (mul_le_mul_of_nonneg_left hy.2 hb)

theorem truncRoot_combo {d : ℕ} {C : Set (Euc d)}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ)
    {s t a b : ℝ}
    (hs : (trunc C ℓ s).Nonempty) (ht : (trunc C ℓ t).Nonempty)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * truncRoot C ℓ s + b * truncRoot C ℓ t
      ≤ truncRoot C ℓ (a * s + b * t) := by
  let A := a • trunc C ℓ s
  let B := b • trunc C ℓ t
  have hsc : IsCompact (trunc C ℓ s) := isCompact_trunc hCcomp ℓ s
  have htc : IsCompact (trunc C ℓ t) := isCompact_trunc hCcomp ℓ t
  have hAcomp : IsCompact A := hsc.smul a
  have hBcomp : IsCompact B := htc.smul b
  have hABcomp : IsCompact (A + B) := hAcomp.add hBcomp
  have hbm :
      volume A ^ ((d : ℝ) + 1)⁻¹ + volume B ^ ((d : ℝ) + 1)⁻¹
        ≤ volume (A + B) ^ ((d : ℝ) + 1)⁻¹ :=
    brunn_minkowski_euclideanSpace
      (hs.smul_set (a := a)) hAcomp.measurableSet
      (ht.smul_set (a := b)) hBcomp.measurableSet hABcomp.measurableSet
  have hsubset : A + B ⊆ trunc C ℓ (a * s + b * t) :=
    weighted_trunc_subset hCconv ℓ ha hb hab
  have hmono :
      volume (A + B) ^ ((d : ℝ) + 1)⁻¹
        ≤ volume (trunc C ℓ (a * s + b * t)) ^ ((d : ℝ) + 1)⁻¹ := by
    exact (ENNReal.monotone_rpow_of_nonneg (by positivity)) (measure_mono hsubset)
  have hfin :
      volume (trunc C ℓ (a * s + b * t)) ^ ((d : ℝ) + 1)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg
      (by positivity) (volume_trunc_ne_top hCcomp ℓ (a * s + b * t))
  have hAfin : volume A ^ ((d : ℝ) + 1)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hAcomp.measure_lt_top.ne
  have hBfin : volume B ^ ((d : ℝ) + 1)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hBcomp.measure_lt_top.ne
  have hreal := ENNReal.toReal_mono hfin (hbm.trans hmono)
  rw [ENNReal.toReal_add hAfin hBfin] at hreal
  simp only [truncRoot] at hreal ⊢
  rw [volume_smul_rpow (trunc C ℓ s) a ha,
      volume_smul_rpow (trunc C ℓ t) b hb,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at hreal
  exact hreal

theorem convex_truncDomain {d : ℕ} {C : Set (Euc d)}
    (hCconv : Convex ℝ C) (ℓ : Euc d →L[ℝ] ℝ) :
    Convex ℝ (truncDomain C ℓ) := by
  intro s hs t ht a b ha hb hab
  change (trunc C ℓ s).Nonempty at hs
  change (trunc C ℓ t).Nonempty at ht
  change (trunc C ℓ (a * s + b * t)).Nonempty
  rcases hs with ⟨x, hx⟩
  rcases ht with ⟨y, hy⟩
  exact ⟨a • x + b • y,
    weighted_trunc_subset hCconv ℓ ha hb hab
      (add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy))⟩

theorem concaveOn_truncRoot {d : ℕ} {C : Set (Euc d)}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) :
    ConcaveOn ℝ (truncDomain C ℓ) (truncRoot C ℓ) := by
  refine ⟨convex_truncDomain hCconv ℓ, ?_⟩
  intro s hs t ht a b ha hb hab
  simpa only [smul_eq_mul] using
    truncRoot_combo hCconv hCcomp ℓ hs ht ha hb hab

lemma cdfRoot_eq {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    cdfRoot C ℓ t =
      (volume C ^ ((d : ℝ) + 1)⁻¹).toReal⁻¹ * truncRoot C ℓ t := by
  unfold cdfRoot truncRoot
  rw [ENNReal.div_rpow_of_nonneg _ _ (by positivity), ENNReal.toReal_div]
  simp only [div_eq_mul_inv, mul_comm]

theorem concaveOn_cdfRoot {d : ℕ} {C : Set (Euc d)}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) :
    ConcaveOn ℝ (truncDomain C ℓ) (cdfRoot C ℓ) := by
  have h := ConcaveOn.smul
    (c := (volume C ^ ((d : ℝ) + 1)⁻¹).toReal⁻¹)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (concaveOn_truncRoot hCconv hCcomp ℓ)
  have heq :
      cdfRoot C ℓ =
        fun t => (volume C ^ ((d : ℝ) + 1)⁻¹).toReal⁻¹ • truncRoot C ℓ t := by
    funext t
    rw [cdfRoot_eq]
    simp only [smul_eq_mul]
  rw [heq]
  exact h

end Grunbaum
