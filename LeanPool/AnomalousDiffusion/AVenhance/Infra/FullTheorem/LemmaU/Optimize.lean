/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lemma U: the final cutoff optimisation

Abstract real arithmetic.  Given the low/high Fourier split bound
`X ≤ S² (h (80 κ K² + B²/κ) + 1/(9K²) + B²/(36 κ² K²))` for every integer cutoff `K ≥ 1`, the
choice `K = ⌈h^{-1/4} κ^{-3/4}⌉` gives `√X ≤ 20 (1+B) κ^{-1/2} h^{1/4} S`.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- Core inequality in the variables `u = h^{1/4}`, `v = κ^{1/4}`. -/
theorem optimize_core {u v B S X K : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hv0 : 0 < v)
    (hv1 : v ≤ 1) (hB : 0 ≤ B) (hKx : 1 / (u * v ^ 3) ≤ K) (hK2 : K ≤ 2 / (u * v ^ 3))
    (hX : X ≤ S ^ 2 * (u ^ 4 * (80 * v ^ 4 * K ^ 2 + B ^ 2 / v ^ 4) + 1 / (9 * K ^ 2) +
      B ^ 2 / (36 * (v ^ 4) ^ 2 * K ^ 2))) :
    X ≤ (20 * (1 + B) * u * S / v ^ 2) ^ 2 := by
  have hw : 0 < u * v ^ 3 := by positivity
  have hx0 : 0 < 1 / (u * v ^ 3) := by positivity
  have hK0 : 0 < K := lt_of_lt_of_le hx0 hKx
  -- bounds on K²
  have hKsq_up : K ^ 2 ≤ 4 / (u ^ 2 * v ^ 6) := by
    have h1 : K ^ 2 ≤ (2 / (u * v ^ 3)) ^ 2 := pow_le_pow_left₀ hK0.le hK2 2
    calc K ^ 2 ≤ (2 / (u * v ^ 3)) ^ 2 := h1
      _ = 4 / (u ^ 2 * v ^ 6) := by field_simp; ring
  have hKinv : 1 / K ≤ u * v ^ 3 := by
    rw [div_le_iff₀ hK0]
    have := (div_le_iff₀ hw).mp (by simpa [one_div] using hKx.trans' (le_refl _) : 1 / (u * v ^ 3)
        ≤ K)
    linarith
  have hKinvsq : 1 / K ^ 2 ≤ u ^ 2 * v ^ 6 := by
    have h1 : (1 / K) ^ 2 ≤ (u * v ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hKinv 2
    calc 1 / K ^ 2 = (1 / K) ^ 2 := by rw [one_div_pow]
      _ ≤ (u * v ^ 3) ^ 2 := h1
      _ = u ^ 2 * v ^ 6 := by ring
  have hv2 : 0 < v ^ 2 := by positivity
  have hv4 : 0 < v ^ 4 := by positivity
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hv2le : v ^ 2 ≤ 1 := by nlinarith
  -- pieces
  have p1 : u ^ 4 * (80 * v ^ 4 * K ^ 2) ≤ 320 * (u ^ 2 / v ^ 2) := by
    have : u ^ 4 * (80 * v ^ 4 * K ^ 2) ≤ u ^ 4 * (80 * v ^ 4 * (4 / (u ^ 2 * v ^ 6))) := by
      gcongr
    calc _ ≤ _ := this
      _ = 320 * (u ^ 2 / v ^ 2) := by field_simp; ring
  have p2 : u ^ 4 * (B ^ 2 / v ^ 4) ≤ B ^ 2 * (u ^ 2 / v ^ 4) := by
    have : u ^ 4 * (B ^ 2 / v ^ 4) = (u ^ 4) * (B ^ 2 / v ^ 4) := rfl
    calc u ^ 4 * (B ^ 2 / v ^ 4) = B ^ 2 / v ^ 4 * u ^ 4 := by ring
      _ ≤ B ^ 2 / v ^ 4 * u ^ 2 := by gcongr
      _ = B ^ 2 * (u ^ 2 / v ^ 4) := by ring
  have p3 : 1 / (9 * K ^ 2) ≤ u ^ 2 / v ^ 4 := by
    have : 1 / (9 * K ^ 2) = (1 / 9) * (1 / K ^ 2) := by field_simp
    rw [this]
    have h6 : u ^ 2 * v ^ 6 ≤ u ^ 2 / v ^ 4 := by
      rw [le_div_iff₀ hv4]
      have : v ^ 6 * v ^ 4 ≤ 1 := by
        have : v ^ 6 * v ^ 4 = v ^ 10 := by ring
        rw [this]; exact pow_le_one₀ hv0.le hv1
      calc u ^ 2 * v ^ 6 * v ^ 4 = u ^ 2 * (v ^ 6 * v ^ 4) := by ring
        _ ≤ u ^ 2 * 1 := by gcongr
        _ = u ^ 2 := by ring
    calc (1 / 9) * (1 / K ^ 2) ≤ (1 / 9) * (u ^ 2 * v ^ 6) := by gcongr
      _ ≤ 1 * (u ^ 2 * v ^ 6) := by gcongr; norm_num
      _ ≤ u ^ 2 / v ^ 4 := by linarith
  have p4 : B ^ 2 / (36 * (v ^ 4) ^ 2 * K ^ 2) ≤ B ^ 2 * (u ^ 2 / v ^ 4) := by
    have e1 : B ^ 2 / (36 * (v ^ 4) ^ 2 * K ^ 2) =
        B ^ 2 / (36 * (v ^ 4) ^ 2) * (1 / K ^ 2) := by field_simp
    rw [e1]
    have h1 : B ^ 2 / (36 * (v ^ 4) ^ 2) * (1 / K ^ 2) ≤
        B ^ 2 / (36 * (v ^ 4) ^ 2) * (u ^ 2 * v ^ 6) := by gcongr
    have h2 : B ^ 2 / (36 * (v ^ 4) ^ 2) * (u ^ 2 * v ^ 6) =
        B ^ 2 * (u ^ 2 / v ^ 4) * (v ^ 2 / 36) := by field_simp
    have h3 : B ^ 2 * (u ^ 2 / v ^ 4) * (v ^ 2 / 36) ≤ B ^ 2 * (u ^ 2 / v ^ 4) * 1 := by
      gcongr; linarith
    linarith
  -- combine
  have hsum : u ^ 4 * (80 * v ^ 4 * K ^ 2 + B ^ 2 / v ^ 4) + 1 / (9 * K ^ 2) +
      B ^ 2 / (36 * (v ^ 4) ^ 2 * K ^ 2) ≤
      (320 * v ^ 2 + 1 + 2 * B ^ 2) * (u ^ 2 / v ^ 4) := by
    have e : u ^ 2 / v ^ 2 = v ^ 2 * (u ^ 2 / v ^ 4) := by field_simp
    have : u ^ 4 * (80 * v ^ 4 * K ^ 2 + B ^ 2 / v ^ 4) =
        u ^ 4 * (80 * v ^ 4 * K ^ 2) + u ^ 4 * (B ^ 2 / v ^ 4) := by ring
    rw [this]
    nlinarith [p1, p2, p3, p4, e]
  have hcoef : (320 * v ^ 2 + 1 + 2 * B ^ 2) ≤ 400 * (1 + B) ^ 2 := by nlinarith
  have hpos : 0 ≤ u ^ 2 / v ^ 4 := by positivity
  calc X ≤ S ^ 2 * (u ^ 4 * (80 * v ^ 4 * K ^ 2 + B ^ 2 / v ^ 4) + 1 / (9 * K ^ 2) +
      B ^ 2 / (36 * (v ^ 4) ^ 2 * K ^ 2)) := hX
    _ ≤ S ^ 2 * ((320 * v ^ 2 + 1 + 2 * B ^ 2) * (u ^ 2 / v ^ 4)) := by gcongr
    _ ≤ S ^ 2 * (400 * (1 + B) ^ 2 * (u ^ 2 / v ^ 4)) := by gcongr
    _ = (20 * (1 + B) * u * S / v ^ 2) ^ 2 := by field_simp; ring

/-- The final square-root optimisation of Lemma U. -/
theorem lemmaU_optimize {h κ B S X : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hX : ∀ K : ℕ, 1 ≤ K → X ≤ S ^ 2 *
      (h * (80 * κ * (K : ℝ) ^ 2 + B ^ 2 / κ) + 1 / (9 * (K : ℝ) ^ 2) +
        B ^ 2 / (36 * κ ^ 2 * (K : ℝ) ^ 2))) :
    Real.sqrt X ≤ 20 * (1 + B) / Real.sqrt κ * h ^ ((1 : ℝ) / 4) * S := by
  set u : ℝ := h ^ ((1 : ℝ) / 4) with hu
  set v : ℝ := κ ^ ((1 : ℝ) / 4) with hv
  have hu0 : 0 < u := Real.rpow_pos_of_pos hh _
  have hv0 : 0 < v := Real.rpow_pos_of_pos hκ _
  have hu1 : u ≤ 1 := Real.rpow_le_one hh.le hh1 (by norm_num)
  have hv1 : v ≤ 1 := Real.rpow_le_one hκ.le hκ1 (by norm_num)
  have hu4 : u ^ 4 = h := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
  have hv4 : v ^ 4 = κ := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le]; norm_num
  have hsq : Real.sqrt κ = v ^ 2 := by
    rw [← hv4, show v ^ 4 = (v ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hw : 0 < u * v ^ 3 := by positivity
  set x : ℝ := 1 / (u * v ^ 3) with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef, le_div_iff₀ hw]
    have : v ^ 3 ≤ 1 := pow_le_one₀ hv0.le hv1
    have := mul_le_mul hu1 this (by positivity) zero_le_one
    linarith
  set K : ℕ := ⌈x⌉₊ with hK
  have hKx : x ≤ (K : ℝ) := Nat.le_ceil x
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by linarith) hKx
    exact_mod_cast this
  have hKup : (K : ℝ) ≤ 2 / (u * v ^ 3) := by
    have h1 : (K : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    have : 2 / (u * v ^ 3) = 2 * x := by rw [hxdef]; ring
    rw [this]; linarith
  have key := hX K hK1
  rw [← hu4, ← hv4] at key
  have hcore := optimize_core hu0 hu1 hv0 hv1 hB hKx hKup (by simpa [hxdef] using key)
  rw [hsq]
  have hrhs : 0 ≤ 20 * (1 + B) / v ^ 2 * u * S := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨hrhs, ?_⟩
  calc X ≤ _ := hcore
    _ = _ := by ring
end AVenhance.Infra.FullTheorem.LemmaU

end
