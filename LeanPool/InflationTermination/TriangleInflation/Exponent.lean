/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Fan

/-!
# Rejecting-order exponent for the family `P_ε`

Statements for the finite parts of paper Proposition 5.13 (`prop:family`): the passing
construction below `1 + ½ ε^{-1/3}`, the fan rejection at `⌊τ_-(ε)⌋ + 1`, and
incompatibility. Proofs are deferred.

Scope: the asymptotic `liminf`/`limsup` statement of Proposition 5.13 is not formalized, nor
is the finiteness of `t_min` (which the paper quotes from the asymptotic completeness of the
Navascués–Wolfe hierarchy). Only the explicit finite bounds are stated.
-/

namespace TriangleInflation

open Finset

noncomputable
section

/-- `σ = ½ ε^{2/3}`, so that `P_ε = Q(ε, 1 - σ)` (paper Proposition 5.13). -/
def sigmaEps (ε : ℝ) : ℝ := ε ^ ((2 : ℝ) / 3) / 2

/-- `m = ε + (1-ε)σ`, the common one-variable zero marginal of `P_ε`. -/
def mEps (ε : ℝ) : ℝ := ε + (1 - ε) * sigmaEps ε

/-- `z = ε + (1-ε)σ³`, the all-zero atom of `P_ε`. -/
def zEps (ε : ℝ) : ℝ := ε + (1 - ε) * sigmaEps ε ^ 3

/-- `τ_- = (z + m²/2 - √((z + m²/2)² - 2m³))/m²`, the smaller root of the quadratic
`v_t = t z - m - C(t,2) m²` of paper Proposition 5.13. -/
def tauMinus (ε : ℝ) : ℝ :=
  (zEps ε + mEps ε ^ 2 / 2 - Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3))
    / mEps ε ^ 2

/-! ## Private auxiliaries

The estimates of paper Proposition 5.13 are written in terms of `u = ε^{1/3}`, for which
`σ = u²/2`; splitting them off keeps each elaboration small. -/

/-- The real cube root of `ε`, packaged with the two identities the estimates below use:
`u³ = ε` and `σ = u²/2`. -/
private theorem exists_cube_root {ε : ℝ} (h0 : 0 < ε) :
    ∃ u : ℝ, 0 < u ∧ u ^ 3 = ε ∧ sigmaEps ε = u ^ 2 / 2 := by
  refine ⟨ε ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos h0 _, ?_, ?_⟩
  · rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul h0.le]
    norm_num
  · simp only [sigmaEps]
    rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul h0.le]
    norm_num

/-- `σ > 0` for `ε > 0`. -/
private theorem sigmaEps_pos {ε : ℝ} (h0 : 0 < ε) : 0 < sigmaEps ε := by
  simp only [sigmaEps]
  have := Real.rpow_pos_of_pos h0 ((2 : ℝ) / 3)
  linarith

/-- `σ < 1/2` for `0 < ε < 1`, since `ε^{2/3} < 1`. -/
private theorem sigmaEps_lt_half {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : sigmaEps ε < 1 / 2 := by
  simp only [sigmaEps]
  have := Real.rpow_lt_one h0.le h1 (by norm_num : (0 : ℝ) < (2 : ℝ) / 3)
  linarith

/-- `P_ε` is a probability law for `0 < ε < 1`. -/
private theorem Peps_isLaw {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : IsLaw (Peps ε) := by
  have hσ0 := sigmaEps_pos h0
  have hσ1 := sigmaEps_lt_half h0 h1
  change IsLaw (Q ε (1 - sigmaEps ε))
  exact Q_isLaw h0.le h1.le (by linarith) (by linarith)

/-- A downward parabola is positive strictly between its roots: if `m > 0`, `s ≥ 0` and
`s² = (z + m²/2)² - 2m³`, then `m²x` strictly between `(z + m²/2) ∓ s` makes the fan
quantity `v_x = x z - m - C(x,2) m²` positive. -/
private theorem fan_gap {m z x s : ℝ} (hm : 0 < m)
    (hs2 : s ^ 2 = (z + m ^ 2 / 2) ^ 2 - 2 * m ^ 3)
    (hlow : z + m ^ 2 / 2 - s < m ^ 2 * x)
    (hhigh : m ^ 2 * x < z + m ^ 2 / 2 + s) :
    m + x * (x - 1) / 2 * (m * m) < x * z := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have h1 : 0 < s - (m ^ 2 * x - (z + m ^ 2 / 2)) := by linarith
  have h2 : 0 < s + (m ^ 2 * x - (z + m ^ 2 / 2)) := by linarith
  have key : 0 < s ^ 2 - (m ^ 2 * x - (z + m ^ 2 / 2)) ^ 2 := by nlinarith [mul_pos h1 h2]
  have iden : s ^ 2 - (m ^ 2 * x - (z + m ^ 2 / 2)) ^ 2
      = 2 * m ^ 2 * (x * z - (m + x * (x - 1) / 2 * (m * m))) := by
    rw [hs2]; ring
  rw [iden] at key
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [key, mul_nonneg hm2.le (sub_nonneg.mpr hcon)]

/-- The elementary bounds `m ≤ ¾u²` and `z ≥ u³` of paper Proposition 5.13, for `ε ≤ 1/64`
(equivalently `u ≤ 1/4`). -/
private theorem mz_bounds {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 4 ∧ 0 < mEps ε ∧ mEps ε ≤ 3 / 4 * u ^ 2 ∧ u ^ 3 ≤ zEps ε := by
  obtain ⟨u, hu0, hu3, hσ⟩ := exists_cube_root h0
  have hu4 : u ≤ 1 / 4 := by nlinarith [hu3, h1, hu0, sq_nonneg u, mul_pos hu0 hu0]
  have hu2pos : (0 : ℝ) < u ^ 2 := pow_pos hu0 2
  have hu3pos : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu3le : u ^ 3 ≤ 1 / 64 := by rw [hu3]; exact h1
  have hm : mEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) := by
    simp only [mEps, hσ]; rw [hu3]
  have hzz : zEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) ^ 3 := by
    simp only [zEps, hσ]; rw [hu3]
  refine ⟨u, hu0, hu4, ?_, ?_, ?_⟩
  · rw [hm]
    nlinarith [mul_pos (show (0 : ℝ) < 1 - u ^ 3 by linarith) hu2pos]
  · rw [hm]
    nlinarith [mul_nonneg hu3pos.le hu2pos.le,
      mul_nonneg hu2pos.le (show (0 : ℝ) ≤ 1 / 4 - u by linarith)]
  · rw [hzz]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - u ^ 3 by linarith)
      (show (0 : ℝ) ≤ (u ^ 2 / 2) ^ 3 by positivity)]

/-- The discriminant bound `D = (z + m²/2)² - 2m³ ≥ (5/32)u⁶` of paper Proposition 5.13. -/
private theorem disc_lb {m z u : ℝ} (hu0 : 0 < u) (hm0 : 0 < m) (hmub : m ≤ 3 / 4 * u ^ 2)
    (hzlb : u ^ 3 ≤ z) : 5 / 32 * u ^ 6 ≤ (z + m ^ 2 / 2) ^ 2 - 2 * m ^ 3 := by
  have hu3pos : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hzpos : 0 < z := lt_of_lt_of_le hu3pos hzlb
  have hm3 : m ^ 3 ≤ 27 / 64 * u ^ 6 :=
    calc m ^ 3 ≤ (3 / 4 * u ^ 2) ^ 3 := pow_le_pow_left₀ hm0.le hmub 3
      _ = 27 / 64 * u ^ 6 := by ring
  have hz2 : u ^ 6 ≤ z ^ 2 :=
    calc u ^ 6 = (u ^ 3) ^ 2 := by ring
      _ ≤ z ^ 2 := pow_le_pow_left₀ hu3pos.le hzlb 2
  nlinarith [hz2, hm3, mul_nonneg (sq_nonneg m) hzpos.le, sq_nonneg (m ^ 2)]

/-- The three facts about `√D` that the rejecting order needs: `D ≥ 0`, that `τ_-` is
nonnegative (`√D < z + m²/2`), and that the two roots are more than one apart
(`m² < 2√D`). -/
private theorem Peps_disc {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    0 ≤ (zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3 ∧
      Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) < zEps ε + mEps ε ^ 2 / 2 ∧
      mEps ε ^ 2 < 2 * Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) := by
  obtain ⟨u, hu0, hu4, hm0, hmub, hzlb⟩ := mz_bounds h0 h1
  have hu3pos : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu6nn : (0 : ℝ) ≤ u ^ 6 := by positivity
  have hzpos : 0 < zEps ε := lt_of_lt_of_le hu3pos hzlb
  have hDlb := disc_lb hu0 hm0 hmub hzlb
  have hD0 : 0 ≤ (zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3 := by linarith
  have hcnn : (0 : ℝ) ≤ zEps ε + mEps ε ^ 2 / 2 := by
    have := sq_nonneg (mEps ε); linarith
  refine ⟨hD0, ?_, ?_⟩
  · have hlt : (zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3
        < (zEps ε + mEps ε ^ 2 / 2) ^ 2 := by
      have := pow_pos hm0 3; linarith
    have h := Real.sqrt_lt_sqrt hD0 hlt
    rwa [Real.sqrt_sq hcnn] at h
  · have hslb : 1 / 3 * u ^ 3
        ≤ Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) :=
      (Real.le_sqrt (by linarith) hD0).mpr (by nlinarith [hDlb, hu6nn])
    have hm2ub : mEps ε ^ 2 ≤ 9 / 16 * u ^ 4 :=
      calc mEps ε ^ 2 ≤ (3 / 4 * u ^ 2) ^ 2 := pow_le_pow_left₀ hm0.le hmub 2
        _ = 9 / 16 * u ^ 4 := by ring
    have h9 : 9 / 16 * u ^ 4 ≤ 9 / 64 * u ^ 3 := by
      nlinarith [mul_nonneg hu3pos.le (show (0 : ℝ) ≤ 1 / 4 - u by linarith)]
    linarith

/-! ## The statements of Proposition 5.13 -/

/-- `P_ε` is `Q(ε, 1 - σ)`. -/
theorem Peps_eq (ε : ℝ) : Peps ε = Q ε (1 - sigmaEps ε) := rfl

/-- `m` is the common one-variable zero marginal of `P_ε`. -/
theorem mEps_eq_marg {ε : ℝ} :
    margA (Peps ε) = mEps ε ∧ margB (Peps ε) = mEps ε ∧ margC (Peps ε) = mEps ε := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [margA, margB, margC, Peps, Q, bern, mEps, sigmaEps, Fintype.sum_bool]
      norm_num [-mul_eq_mul_left_iff]
      ring

/-- `z` is the all-zero atom of `P_ε`. -/
theorem zEps_eq_atom {ε : ℝ} : atom000 (Peps ε) = zEps ε := by
  simp only [atom000, Peps, Q, bern, zEps, sigmaEps]
  norm_num [-mul_eq_mul_left_iff]
  ring

/-- Paper Proposition 5.13 (`prop:family`), lower bound, part (a): if `0 < ε < 1/8` and
`t ≤ 1 + ½ ε^{-1/3}` then `P_ε` is feasible at order `t`. This is Theorem 5.1 applied with
`r = 1 - σ`, using `(1-ε)^{t-1} ≥ 1 - (t-1)ε ≥ 1 - σ`. -/
theorem Peps_aiFeasible {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 8) (t : ℕ) (ht : 1 ≤ t)
    (hle : (t : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2) : AIFeasible t (Peps ε) := by
  have hε1 : ε < 1 := by linarith
  have hσ0 := sigmaEps_pos h0
  have hσ1 := sigmaEps_lt_half h0 hε1
  -- `ε^{-1/3} · ε = ε^{2/3}`
  have hpow : ε ^ (-(1 : ℝ) / 3) * ε = ε ^ ((2 : ℝ) / 3) := by
    have h := (Real.rpow_add h0 (-(1 : ℝ) / 3) 1).symm
    rw [Real.rpow_one] at h
    rw [h]
    norm_num
  -- `(t-1) ε ≤ σ`
  have hkey : ((t : ℝ) - 1) * ε ≤ sigmaEps ε := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (t : ℝ) - 1 ≤ ε ^ (-(1 : ℝ) / 3) / 2)
      h0.le
    simp only [sigmaEps]
    calc ((t : ℝ) - 1) * ε ≤ ε ^ (-(1 : ℝ) / 3) / 2 * ε := h
      _ = ε ^ (-(1 : ℝ) / 3) * ε / 2 := by ring
      _ = ε ^ ((2 : ℝ) / 3) / 2 := by rw [hpow]
  -- Bernoulli's inequality
  have hbern : 1 - ((t : ℝ) - 1) * ε ≤ (1 - ε) ^ (t - 1) := by
    have h := one_add_mul_le_pow (a := -ε) (by linarith) (t - 1)
    rw [Nat.cast_sub ht] at h
    push_cast at h
    calc 1 - ((t : ℝ) - 1) * ε = 1 + ((t : ℝ) - 1) * -ε := by ring
      _ ≤ (1 + -ε) ^ (t - 1) := h
      _ = (1 - ε) ^ (t - 1) := by ring_nf
  change AIFeasible t (Q ε (1 - sigmaEps ε))
  exact membership_AI t h0 hε1 (by linarith) (by linarith)

/-- The Navascués–Wolfe form of the same lower bound. -/
theorem Peps_nwFeasible {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 8) (t : ℕ) (ht : 1 ≤ t)
    (hle : (t : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2) : NWFeasible t (Peps ε) :=
  nwFeasible_of_aiFeasible (Peps_aiFeasible h0 h1 t ht hle)

/-- Paper Proposition 5.13 (`prop:family`), upper bound, part (b): if `ε ≤ 1/64` then the
first fan inequality rejects `P_ε` at order `⌊τ_-(ε)⌋ + 1`. -/
theorem Peps_not_nwFeasible {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    ¬ NWFeasible (⌊tauMinus ε⌋₊ + 1) (Peps ε) := by
  intro hfeas
  have hε1 : ε < 1 := by linarith
  obtain ⟨u, hu0, hu4, hm0, hmub, hzlb⟩ := mz_bounds h0 h1
  obtain ⟨hD0, hsub, hgap⟩ := Peps_disc h0 h1
  have hmne : mEps ε ≠ 0 := ne_of_gt hm0
  have hm2pos : (0 : ℝ) < mEps ε ^ 2 := pow_pos hm0 2
  have hs2 : Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) ^ 2
      = (zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3 := Real.sq_sqrt hD0
  have hmul : mEps ε ^ 2 * tauMinus ε
      = zEps ε + mEps ε ^ 2 / 2
        - Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) := by
    simp only [tauMinus]
    field_simp
  have hτ0 : 0 ≤ tauMinus ε := by
    simp only [tauMinus]
    exact div_nonneg (by linarith) hm2pos.le
  -- the rejecting order `T = ⌊τ_-⌋ + 1` lies strictly between the two roots
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ⌊tauMinus ε⌋₊ + 1 = T := ⟨_, rfl⟩
  rw [hT] at hfeas
  have hT1 : 1 ≤ T := by omega
  have hxlow : tauMinus ε < (T : ℝ) := by
    rw [← hT]; push_cast; exact Nat.lt_floor_add_one _
  have hxhigh : (T : ℝ) ≤ tauMinus ε + 1 := by
    rw [← hT]; push_cast; linarith [Nat.floor_le hτ0]
  have hlow : zEps ε + mEps ε ^ 2 / 2
      - Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) < mEps ε ^ 2 * (T : ℝ) := by
    rw [← hmul]
    exact mul_lt_mul_of_pos_left hxlow hm2pos
  have hhigh : mEps ε ^ 2 * (T : ℝ)
      < zEps ε + mEps ε ^ 2 / 2
        + Real.sqrt ((zEps ε + mEps ε ^ 2 / 2) ^ 2 - 2 * mEps ε ^ 3) := by
    have h := mul_le_mul_of_nonneg_left hxhigh hm2pos.le
    rw [mul_add, hmul, mul_one] at h
    linarith
  have hpos := fan_gap hm0 hs2 hlow hhigh
  -- but the first fan inequality at order `T` says the opposite
  have hfan := fan_first T hT1 (Peps_isLaw h0 hε1) hfeas
  obtain ⟨hA, hB, hC⟩ := mEps_eq_marg (ε := ε)
  rw [zEps_eq_atom (ε := ε), hA, hB, hC, Nat.cast_choose_two] at hfan
  linarith

/-- Paper Proposition 5.13 (`prop:family`), part (c): `P_ε` violates the Finner inequality,
since `m³ < ε² ≤ z²` when `ε < 1/8`; hence `P_ε ∉ C_tri`. -/
theorem Peps_not_compatible {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 8) :
    ¬ TriangleCompatible (Peps ε) := by
  intro hc
  have hε1 : ε < 1 := by linarith
  have hfin := finner_of_compatible hc
  obtain ⟨hA, hB, hC⟩ := mEps_eq_marg (ε := ε)
  rw [zEps_eq_atom (ε := ε), hA, hB, hC] at hfin
  obtain ⟨u, hu0, hu3, hσ⟩ := exists_cube_root h0
  have hu2 : u < 1 / 2 := by nlinarith [hu3, h1, hu0, sq_nonneg u, mul_pos hu0 hu0]
  have hu2pos : (0 : ℝ) < u ^ 2 := pow_pos hu0 2
  have hu3pos : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu3le : u ^ 3 ≤ 1 / 8 := by rw [hu3]; linarith
  have hm : mEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) := by
    simp only [mEps, hσ]; rw [hu3]
  have hzz : zEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) ^ 3 := by
    simp only [zEps, hσ]; rw [hu3]
  have hm0 : 0 < mEps ε := by
    rw [hm]
    nlinarith [mul_pos (show (0 : ℝ) < 1 - u ^ 3 by linarith) hu2pos]
  have hmub : mEps ε ≤ u ^ 3 + u ^ 2 / 2 := by
    rw [hm]
    nlinarith [mul_nonneg hu3pos.le hu2pos.le]
  have hlt1 : u ^ 3 + u ^ 2 / 2 < u ^ 2 := by
    nlinarith [mul_pos hu2pos (show (0 : ℝ) < 1 / 2 - u by linarith)]
  have hm3 : mEps ε ^ 3 < u ^ 6 :=
    calc mEps ε ^ 3 ≤ (u ^ 3 + u ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hm0.le hmub 3
      _ < (u ^ 2) ^ 3 := pow_lt_pow_left₀ hlt1 (by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
      _ = u ^ 6 := by ring
  have hzlb : u ^ 3 ≤ zEps ε := by
    rw [hzz]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - u ^ 3 by linarith)
      (show (0 : ℝ) ≤ (u ^ 2 / 2) ^ 3 by positivity)]
  have hz2 : u ^ 6 ≤ zEps ε ^ 2 :=
    calc u ^ 6 = (u ^ 3) ^ 2 := by ring
      _ ≤ zEps ε ^ 2 := pow_le_pow_left₀ hu3pos.le hzlb 2
  nlinarith [hfin, hm3, hz2]

/-- Paper Proposition 5.13 (`prop:family`), the finite sandwich on the first rejecting order
of the Navascués–Wolfe hierarchy. -/
theorem Peps_tminNW_bounds {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    ⌊1 + ε ^ (-(1 : ℝ) / 3) / 2⌋₊ + 1 ≤ tminNW (Peps ε)
      ∧ tminNW (Peps ε) ≤ ⌊tauMinus ε⌋₊ + 1 := by
  have h8 : ε < 1 / 8 := by linarith
  have hfl : (0 : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 := by
    have := Real.rpow_pos_of_pos h0 (-(1 : ℝ) / 3); linarith
  have hmem : (⌊tauMinus ε⌋₊ + 1) ∈ {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t (Peps ε)} :=
    ⟨by omega, Peps_not_nwFeasible h0 h1⟩
  refine ⟨?_, Nat.sInf_le hmem⟩
  have hne : {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t (Peps ε)}.Nonempty := ⟨_, hmem⟩
  have hmem2 : tminNW (Peps ε) ∈ {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t (Peps ε)} := Nat.sInf_mem hne
  obtain ⟨hge1, hnot⟩ := hmem2
  by_contra hcon
  rw [not_le] at hcon
  have hle : ((tminNW (Peps ε) : ℕ) : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 :=
    (Nat.le_floor_iff hfl).mp (Nat.lt_succ_iff.mp hcon)
  exact hnot (Peps_nwFeasible h0 h8 _ hge1 hle)

/-- The same sandwich for the ancestral-independence hierarchy. -/
theorem Peps_tminAI_bounds {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 64) :
    ⌊1 + ε ^ (-(1 : ℝ) / 3) / 2⌋₊ + 1 ≤ tminAI (Peps ε)
      ∧ tminAI (Peps ε) ≤ ⌊tauMinus ε⌋₊ + 1 := by
  have h8 : ε < 1 / 8 := by linarith
  have hfl : (0 : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 := by
    have := Real.rpow_pos_of_pos h0 (-(1 : ℝ) / 3); linarith
  have hmem : (⌊tauMinus ε⌋₊ + 1) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)} :=
    ⟨by omega, fun h => Peps_not_nwFeasible h0 h1 (nwFeasible_of_aiFeasible h)⟩
  refine ⟨?_, Nat.sInf_le hmem⟩
  have hne : {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)}.Nonempty := ⟨_, hmem⟩
  have hmem2 : tminAI (Peps ε) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Peps ε)} := Nat.sInf_mem hne
  obtain ⟨hge1, hnot⟩ := hmem2
  by_contra hcon
  rw [not_le] at hcon
  have hle : ((tminAI (Peps ε) : ℕ) : ℝ) ≤ 1 + ε ^ (-(1 : ℝ) / 3) / 2 :=
    (Nat.le_floor_iff hfl).mp (Nat.lt_succ_iff.mp hcon)
  exact hnot (Peps_aiFeasible h0 h8 _ hge1 hle)

end

end TriangleInflation
