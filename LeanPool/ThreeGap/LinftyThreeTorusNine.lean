/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.SimultaneousDirichlet
import LeanPool.ThreeGap.LinftyFiveDistanceSharpArith

/-!
# The `L∞` three-torus bound `g_∞ ≤ 2^d+1` is **sharp** for `d = 3`: nine distances attained

The repo's `SimDirichlet.nnDist_count_unconditional` proves the sup-norm bound `g_∞ ≤ 2^d + 1` in
all
dimensions (Shutov), i.e. `≤ 9` for `d = 3`. Haynes–Marklof–Ramirez
([arXiv:2010.08842](https://arxiv.org/abs/2010.08842), *Higher dimensional gap theorems for the
maximum metric*, IJNT 17 (2021)) prove this bound is **sharp for `d ≤ 3`**, and give an explicit
`d = 3` example realizing exactly **nine** distinct sup-norm nearest-neighbour distances. This file
formalizes that example, giving `g_∞(3) ≥ 9`; together with the repo's `≤ 9` it shows
`g_∞(3) = 9` — the bound is attained.

## The witness (Haynes–Ramirez, §3)
`L = ℤ³`, `α = (−157/10000, −742/3125, −23/400) = (−785, −11872, −2875)/50000`, `N = 73`. The scaled
sup-norm defects `M_m = max_k |r(a_k m)|` (`a = (−785,−11872,−2875)`, balanced residues mod `50000`)
have eight records in the doubling window `(⌈73/2⌉, 73] = (37, 73]` at `m =
50,51,54,55,67,68,71,72`,
giving the nine distinct distances (over `50000`)
`11500 > 10750 > 9965 > 8912 > 8125 > 7375 > 7296 > 7088 > 7000`, realized at
`q = 24,23,22,19,18,6,5,2,1`.

Same dynamics-free, integer-exact route as `LinftyRecords.sharp_attained` (`d = 2`), extended to
three
coordinates; everything is exact modular arithmetic — no square roots.
-/

namespace ThreeGap.LinftyRecords3

open scoped Real
open ThreeGap.SimApprox ThreeGap.DeltaCost ThreeGap.Chevallier ThreeGap.SimDirichlet
open ThreeGap.LinftyRecords (abs_residue_le)
open ThreeGap.EuclideanRecords (inf_lt_inf)


/-- The `L∞` rational witness `α* = (−785, −11872, −2875)/50000` on `𝕋³` (Haynes–Ramirez). -/
noncomputable def astar : Fin 3 → ℝ := ![-785 / 50000, -11872 / 50000, -2875 / 50000]

/-- **The witness defect is coordinatewise-exact**: `delta α* d = M/50000` with
`M = max(|r₀|,|r₁|,|r₂|)`, the balanced residues of `−785d, −11872d, −2875d` mod `50000`. -/
theorem delta_astar (d n₀ n₁ n₂ r₀ r₁ r₂ M : ℤ)
    (hr0 : -785 * d = r₀ + 50000 * n₀) (hr1 : -11872 * d = r₁ + 50000 * n₁)
    (hr2 : -2875 * d = r₂ + 50000 * n₂)
    (hb0 : 2 * |r₀| ≤ 50000) (hb1 : 2 * |r₁| ≤ 50000) (hb2 : 2 * |r₂| ≤ 50000)
    (hM0 : |r₀| ≤ M) (hM1 : |r₁| ≤ M) (hM2 : |r₂| ≤ M)
    (hMa : M = |r₀| ∨ M = |r₁| ∨ M = |r₂|) :
    delta astar d = (M : ℝ) / 50000 := by
  have hMnn : (0 : ℝ) ≤ (M : ℝ) / 50000 := by
    have h : (0 : ℤ) ≤ M := le_trans (abs_nonneg r₀) hM0
    have : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    positivity
  have normcoord : ∀ z : ℤ, ‖((z : ℝ)) / 50000‖ = ((|z| : ℤ) : ℝ) / 50000 := by
    intro z
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 50000 by norm_num), ← Int.cast_abs]
  have c0 : ∀ p : Fin 3 → ℤ, (rem astar d p) 0 = ((-785 * d - 50000 * p 0 : ℤ) : ℝ) / 50000 := by
    intro p; simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    push_cast; ring
  have c1 : ∀ p : Fin 3 → ℤ, (rem astar d p) 1 = ((-11872 * d - 50000 * p 1 : ℤ) : ℝ) / 50000 := by
    intro p; simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
    push_cast; ring
  have c2 : ∀ p : Fin 3 → ℤ, (rem astar d p) 2 = ((-2875 * d - 50000 * p 2 : ℤ) : ℝ) / 50000 := by
    intro p; simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  refine le_antisymm ?_ ?_
  · refine le_trans (delta_le astar d ![n₀, n₁, n₂]) ?_
    have b0 : ‖(rem astar d ![n₀, n₁, n₂]) 0‖ ≤ (M : ℝ) / 50000 := by
      rw [c0 ![n₀, n₁, n₂]]
      have hz : (-785 * d - 50000 * (![n₀, n₁, n₂] : Fin 3 → ℤ) 0) = r₀ := by
        simp only [Matrix.cons_val_zero]; linarith [hr0]
      rw [hz, normcoord r₀]
      have hle : ((|r₀| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast hM0
      linarith
    have b1 : ‖(rem astar d ![n₀, n₁, n₂]) 1‖ ≤ (M : ℝ) / 50000 := by
      rw [c1 ![n₀, n₁, n₂]]
      have hz : (-11872 * d - 50000 * (![n₀, n₁, n₂] : Fin 3 → ℤ) 1) = r₁ := by
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; linarith [hr1]
      rw [hz, normcoord r₁]
      have hle : ((|r₁| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast hM1
      linarith
    have b2 : ‖(rem astar d ![n₀, n₁, n₂]) 2‖ ≤ (M : ℝ) / 50000 := by
      rw [c2 ![n₀, n₁, n₂]]
      have hz : (-2875 * d - 50000 * (![n₀, n₁, n₂] : Fin 3 → ℤ) 2) = r₂ := by
        simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linarith [hr2]
      rw [hz, normcoord r₂]
      have hle : ((|r₂| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast hM2
      linarith
    rw [pi_norm_le_iff_of_nonneg hMnn]
    intro i; fin_cases i
    · exact b0
    · exact b1
    · exact b2
  · refine le_ciInf (fun p => ?_)
    rcases hMa with hMa | hMa | hMa
    · refine le_trans ?_ (norm_le_pi_norm (rem astar d p) 0)
      rw [c0 p, normcoord, hMa]
      have hnum : ((|r₀| : ℤ) : ℝ) ≤ ((|-785 * d - 50000 * p 0| : ℤ) : ℝ) := by
        exact_mod_cast abs_residue_le 50000 r₀ (-785 * d) (by norm_num) hb0 ⟨n₀, by linarith [hr0]⟩
          (p 0)
      linarith
    · refine le_trans ?_ (norm_le_pi_norm (rem astar d p) 1)
      rw [c1 p, normcoord, hMa]
      have hnum : ((|r₁| : ℤ) : ℝ) ≤ ((|-11872 * d - 50000 * p 1| : ℤ) : ℝ) := by
        exact_mod_cast abs_residue_le 50000 r₁ (-11872 * d) (by norm_num) hb1 ⟨n₁, by linarith
          [hr1]⟩ (p 1)
      linarith
    · refine le_trans ?_ (norm_le_pi_norm (rem astar d p) 2)
      rw [c2 p, normcoord, hMa]
      have hnum : ((|r₂| : ℤ) : ℝ) ≤ ((|-2875 * d - 50000 * p 2| : ℤ) : ℝ) := by
        exact_mod_cast abs_residue_le 50000 r₂ (-2875 * d) (by norm_num) hb2 ⟨n₂, by linarith [hr2]⟩
          (p 2)
      linarith

/-- The witness defects `delta α* m = M_m/50000` for `m = 1,…,72`. -/
theorem dstar1 : delta astar 1 = (11872 : ℝ) / 50000 := by
  rw [delta_astar 1 0 0 0 (-785) (-11872) (-2875) 11872 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar2 : delta astar 2 = (23744 : ℝ) / 50000 := by
  rw [delta_astar 2 0 0 0 (-1570) (-23744) (-5750) 23744 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar3 : delta astar 3 = (14384 : ℝ) / 50000 := by
  rw [delta_astar 3 0 (-1) 0 (-2355) 14384 (-8625) 14384 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar4 : delta astar 4 = (11500 : ℝ) / 50000 := by
  rw [delta_astar 4 0 (-1) 0 (-3140) 2512 (-11500) 11500 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar5 : delta astar 5 = (14375 : ℝ) / 50000 := by
  rw [delta_astar 5 0 (-1) 0 (-3925) (-9360) (-14375) 14375 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar6 : delta astar 6 = (21232 : ℝ) / 50000 := by
  rw [delta_astar 6 0 (-1) 0 (-4710) (-21232) (-17250) 21232 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar7 : delta astar 7 = (20125 : ℝ) / 50000 := by
  rw [delta_astar 7 0 (-2) 0 (-5495) 16896 (-20125) 20125 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar8 : delta astar 8 = (23000 : ℝ) / 50000 := by
  rw [delta_astar 8 0 (-2) 0 (-6280) 5024 (-23000) 23000 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar9 : delta astar 9 = (24125 : ℝ) / 50000 := by
  rw [delta_astar 9 0 (-2) (-1) (-7065) (-6848) 24125 24125 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar10 : delta astar 10 = (21250 : ℝ) / 50000 := by
  rw [delta_astar 10 0 (-2) (-1) (-7850) (-18720) 21250 21250 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar11 : delta astar 11 = (19408 : ℝ) / 50000 := by
  rw [delta_astar 11 0 (-3) (-1) (-8635) 19408 18375 19408 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar12 : delta astar 12 = (15500 : ℝ) / 50000 := by
  rw [delta_astar 12 0 (-3) (-1) (-9420) 7536 15500 15500 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar13 : delta astar 13 = (12625 : ℝ) / 50000 := by
  rw [delta_astar 13 0 (-3) (-1) (-10205) (-4336) 12625 12625 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar14 : delta astar 14 = (16208 : ℝ) / 50000 := by
  rw [delta_astar 14 0 (-3) (-1) (-10990) (-16208) 9750 16208 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar15 : delta astar 15 = (21920 : ℝ) / 50000 := by
  rw [delta_astar 15 0 (-4) (-1) (-11775) 21920 6875 21920 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar16 : delta astar 16 = (12560 : ℝ) / 50000 := by
  rw [delta_astar 16 0 (-4) (-1) (-12560) 10048 4000 12560 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar17 : delta astar 17 = (13345 : ℝ) / 50000 := by
  rw [delta_astar 17 0 (-4) (-1) (-13345) (-1824) 1125 13345 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar18 : delta astar 18 = (14130 : ℝ) / 50000 := by
  rw [delta_astar 18 0 (-4) (-1) (-14130) (-13696) (-1750) 14130 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar19 : delta astar 19 = (24432 : ℝ) / 50000 := by
  rw [delta_astar 19 0 (-5) (-1) (-14915) 24432 (-4625) 24432 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar20 : delta astar 20 = (15700 : ℝ) / 50000 := by
  rw [delta_astar 20 0 (-5) (-1) (-15700) 12560 (-7500) 15700 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar21 : delta astar 21 = (16485 : ℝ) / 50000 := by
  rw [delta_astar 21 0 (-5) (-1) (-16485) 688 (-10375) 16485 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar22 : delta astar 22 = (17270 : ℝ) / 50000 := by
  rw [delta_astar 22 0 (-5) (-1) (-17270) (-11184) (-13250) 17270 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar23 : delta astar 23 = (23056 : ℝ) / 50000 := by
  rw [delta_astar 23 0 (-5) (-1) (-18055) (-23056) (-16125) 23056 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar24 : delta astar 24 = (19000 : ℝ) / 50000 := by
  rw [delta_astar 24 0 (-6) (-1) (-18840) 15072 (-19000) 19000 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar25 : delta astar 25 = (21875 : ℝ) / 50000 := by
  rw [delta_astar 25 0 (-6) (-1) (-19625) 3200 (-21875) 21875 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar26 : delta astar 26 = (24750 : ℝ) / 50000 := by
  rw [delta_astar 26 0 (-6) (-1) (-20410) (-8672) (-24750) 24750 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar27 : delta astar 27 = (22375 : ℝ) / 50000 := by
  rw [delta_astar 27 0 (-6) (-2) (-21195) (-20544) 22375 22375 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar28 : delta astar 28 = (21980 : ℝ) / 50000 := by
  rw [delta_astar 28 0 (-7) (-2) (-21980) 17584 19500 21980 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar29 : delta astar 29 = (22765 : ℝ) / 50000 := by
  rw [delta_astar 29 0 (-7) (-2) (-22765) 5712 16625 22765 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar30 : delta astar 30 = (23550 : ℝ) / 50000 := by
  rw [delta_astar 30 0 (-7) (-2) (-23550) (-6160) 13750 23550 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar31 : delta astar 31 = (24335 : ℝ) / 50000 := by
  rw [delta_astar 31 0 (-7) (-2) (-24335) (-18032) 10875 24335 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar32 : delta astar 32 = (24880 : ℝ) / 50000 := by
  rw [delta_astar 32 (-1) (-8) (-2) 24880 20096 8000 24880 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar33 : delta astar 33 = (24095 : ℝ) / 50000 := by
  rw [delta_astar 33 (-1) (-8) (-2) 24095 8224 5125 24095 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar34 : delta astar 34 = (23310 : ℝ) / 50000 := by
  rw [delta_astar 34 (-1) (-8) (-2) 23310 (-3648) 2250 23310 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar35 : delta astar 35 = (22525 : ℝ) / 50000 := by
  rw [delta_astar 35 (-1) (-8) (-2) 22525 (-15520) (-625) 22525 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar36 : delta astar 36 = (22608 : ℝ) / 50000 := by
  rw [delta_astar 36 (-1) (-9) (-2) 21740 22608 (-3500) 22608 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar37 : delta astar 37 = (20955 : ℝ) / 50000 := by
  rw [delta_astar 37 (-1) (-9) (-2) 20955 10736 (-6375) 20955 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar38 : delta astar 38 = (20170 : ℝ) / 50000 := by
  rw [delta_astar 38 (-1) (-9) (-2) 20170 (-1136) (-9250) 20170 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar39 : delta astar 39 = (19385 : ℝ) / 50000 := by
  rw [delta_astar 39 (-1) (-9) (-2) 19385 (-13008) (-12125) 19385 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar40 : delta astar 40 = (24880 : ℝ) / 50000 := by
  rw [delta_astar 40 (-1) (-9) (-2) 18600 (-24880) (-15000) 24880 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar41 : delta astar 41 = (17875 : ℝ) / 50000 := by
  rw [delta_astar 41 (-1) (-10) (-2) 17815 13248 (-17875) 17875 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar42 : delta astar 42 = (20750 : ℝ) / 50000 := by
  rw [delta_astar 42 (-1) (-10) (-2) 17030 1376 (-20750) 20750 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar43 : delta astar 43 = (23625 : ℝ) / 50000 := by
  rw [delta_astar 43 (-1) (-10) (-2) 16245 (-10496) (-23625) 23625 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar44 : delta astar 44 = (23500 : ℝ) / 50000 := by
  rw [delta_astar 44 (-1) (-10) (-3) 15460 (-22368) 23500 23500 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar45 : delta astar 45 = (20625 : ℝ) / 50000 := by
  rw [delta_astar 45 (-1) (-11) (-3) 14675 15760 20625 20625 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar46 : delta astar 46 = (17750 : ℝ) / 50000 := by
  rw [delta_astar 46 (-1) (-11) (-3) 13890 3888 17750 17750 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar47 : delta astar 47 = (14875 : ℝ) / 50000 := by
  rw [delta_astar 47 (-1) (-11) (-3) 13105 (-7984) 14875 14875 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar48 : delta astar 48 = (19856 : ℝ) / 50000 := by
  rw [delta_astar 48 (-1) (-11) (-3) 12320 (-19856) 12000 19856 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar49 : delta astar 49 = (18272 : ℝ) / 50000 := by
  rw [delta_astar 49 (-1) (-12) (-3) 11535 18272 9125 18272 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar50 : delta astar 50 = (10750 : ℝ) / 50000 := by
  rw [delta_astar 50 (-1) (-12) (-3) 10750 6400 6250 10750 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar51 : delta astar 51 = (9965 : ℝ) / 50000 := by
  rw [delta_astar 51 (-1) (-12) (-3) 9965 (-5472) 3375 9965 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar52 : delta astar 52 = (17344 : ℝ) / 50000 := by
  rw [delta_astar 52 (-1) (-12) (-3) 9180 (-17344) 500 17344 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar53 : delta astar 53 = (20784 : ℝ) / 50000 := by
  rw [delta_astar 53 (-1) (-13) (-3) 8395 20784 (-2375) 20784 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar54 : delta astar 54 = (8912 : ℝ) / 50000 := by
  rw [delta_astar 54 (-1) (-13) (-3) 7610 8912 (-5250) 8912 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar55 : delta astar 55 = (8125 : ℝ) / 50000 := by
  rw [delta_astar 55 (-1) (-13) (-3) 6825 (-2960) (-8125) 8125 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar56 : delta astar 56 = (14832 : ℝ) / 50000 := by
  rw [delta_astar 56 (-1) (-13) (-3) 6040 (-14832) (-11000) 14832 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar57 : delta astar 57 = (23296 : ℝ) / 50000 := by
  rw [delta_astar 57 (-1) (-14) (-3) 5255 23296 (-13875) 23296 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar58 : delta astar 58 = (16750 : ℝ) / 50000 := by
  rw [delta_astar 58 (-1) (-14) (-3) 4470 11424 (-16750) 16750 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar59 : delta astar 59 = (19625 : ℝ) / 50000 := by
  rw [delta_astar 59 (-1) (-14) (-3) 3685 (-448) (-19625) 19625 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar60 : delta astar 60 = (22500 : ℝ) / 50000 := by
  rw [delta_astar 60 (-1) (-14) (-3) 2900 (-12320) (-22500) 22500 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar61 : delta astar 61 = (24625 : ℝ) / 50000 := by
  rw [delta_astar 61 (-1) (-14) (-4) 2115 (-24192) 24625 24625 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar62 : delta astar 62 = (21750 : ℝ) / 50000 := by
  rw [delta_astar 62 (-1) (-15) (-4) 1330 13936 21750 21750 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar63 : delta astar 63 = (18875 : ℝ) / 50000 := by
  rw [delta_astar 63 (-1) (-15) (-4) 545 2064 18875 18875 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ]; norm_num
theorem dstar64 : delta astar 64 = (16000 : ℝ) / 50000 := by
  rw [delta_astar 64 (-1) (-15) (-4) (-240) (-9808) 16000 16000 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar65 : delta astar 65 = (21680 : ℝ) / 50000 := by
  rw [delta_astar 65 (-1) (-15) (-4) (-1025) (-21680) 13125 21680 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar66 : delta astar 66 = (16448 : ℝ) / 50000 := by
  rw [delta_astar 66 (-1) (-16) (-4) (-1810) 16448 10250 16448 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar67 : delta astar 67 = (7375 : ℝ) / 50000 := by
  rw [delta_astar 67 (-1) (-16) (-4) (-2595) 4576 7375 7375 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar68 : delta astar 68 = (7296 : ℝ) / 50000 := by
  rw [delta_astar 68 (-1) (-16) (-4) (-3380) (-7296) 4500 7296 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar69 : delta astar 69 = (19168 : ℝ) / 50000 := by
  rw [delta_astar 69 (-1) (-16) (-4) (-4165) (-19168) 1625 19168 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar70 : delta astar 70 = (18960 : ℝ) / 50000 := by
  rw [delta_astar 70 (-1) (-17) (-4) (-4950) 18960 (-1250) 18960 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar71 : delta astar 71 = (7088 : ℝ) / 50000 := by
  rw [delta_astar 71 (-1) (-17) (-4) (-5735) 7088 (-4125) 7088 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num
theorem dstar72 : delta astar 72 = (7000 : ℝ) / 50000 := by
  rw [delta_astar 72 (-1) (-17) (-4) (-6520) (-4784) (-7000) 7000 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ]; norm_num

/-- **Nine strictly-decreasing sample values force ≥ 9 distinct images.** -/
theorem nine_le_card_image {N : ℕ} (f : ℕ → ℝ) {q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ : ℕ}
    (m₀ : q₀ ∈ Finset.range (N + 1)) (m₁ : q₁ ∈ Finset.range (N + 1))
    (m₂ : q₂ ∈ Finset.range (N + 1)) (m₃ : q₃ ∈ Finset.range (N + 1))
    (m₄ : q₄ ∈ Finset.range (N + 1)) (m₅ : q₅ ∈ Finset.range (N + 1))
    (m₆ : q₆ ∈ Finset.range (N + 1)) (m₇ : q₇ ∈ Finset.range (N + 1))
    (m₈ : q₈ ∈ Finset.range (N + 1))
    (h01 : f q₁ < f q₀) (h12 : f q₂ < f q₁) (h23 : f q₃ < f q₂) (h34 : f q₄ < f q₃)
    (h45 : f q₅ < f q₄) (h56 : f q₆ < f q₅) (h67 : f q₇ < f q₆) (h78 : f q₈ < f q₇) :
    9 ≤ ((Finset.range (N + 1)).image f).card := by
  have a0_2 : f q₂ < f q₀ := lt_trans h12 h01
  have a0_3 : f q₃ < f q₀ := lt_trans h23 a0_2
  have a0_4 : f q₄ < f q₀ := lt_trans h34 a0_3
  have a0_5 : f q₅ < f q₀ := lt_trans h45 a0_4
  have a0_6 : f q₆ < f q₀ := lt_trans h56 a0_5
  have a0_7 : f q₇ < f q₀ := lt_trans h67 a0_6
  have a0_8 : f q₈ < f q₀ := lt_trans h78 a0_7
  have a1_3 : f q₃ < f q₁ := lt_trans h23 h12
  have a1_4 : f q₄ < f q₁ := lt_trans h34 a1_3
  have a1_5 : f q₅ < f q₁ := lt_trans h45 a1_4
  have a1_6 : f q₆ < f q₁ := lt_trans h56 a1_5
  have a1_7 : f q₇ < f q₁ := lt_trans h67 a1_6
  have a1_8 : f q₈ < f q₁ := lt_trans h78 a1_7
  have a2_4 : f q₄ < f q₂ := lt_trans h34 h23
  have a2_5 : f q₅ < f q₂ := lt_trans h45 a2_4
  have a2_6 : f q₆ < f q₂ := lt_trans h56 a2_5
  have a2_7 : f q₇ < f q₂ := lt_trans h67 a2_6
  have a2_8 : f q₈ < f q₂ := lt_trans h78 a2_7
  have a3_5 : f q₅ < f q₃ := lt_trans h45 h34
  have a3_6 : f q₆ < f q₃ := lt_trans h56 a3_5
  have a3_7 : f q₇ < f q₃ := lt_trans h67 a3_6
  have a3_8 : f q₈ < f q₃ := lt_trans h78 a3_7
  have a4_6 : f q₆ < f q₄ := lt_trans h56 h45
  have a4_7 : f q₇ < f q₄ := lt_trans h67 a4_6
  have a4_8 : f q₈ < f q₄ := lt_trans h78 a4_7
  have a5_7 : f q₇ < f q₅ := lt_trans h67 h56
  have a5_8 : f q₈ < f q₅ := lt_trans h78 a5_7
  have a6_8 : f q₈ < f q₆ := lt_trans h78 h67
  have e0 : f q₀ ∉ ({f q₁, f q₂, f q₃, f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h01, ne_of_gt a0_2, ne_of_gt a0_3, ne_of_gt a0_4, ne_of_gt a0_5, ne_of_gt a0_6,
      ne_of_gt a0_7, ne_of_gt a0_8⟩
  have e1 : f q₁ ∉ ({f q₂, f q₃, f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h12, ne_of_gt a1_3, ne_of_gt a1_4, ne_of_gt a1_5, ne_of_gt a1_6, ne_of_gt a1_7,
      ne_of_gt a1_8⟩
  have e2 : f q₂ ∉ ({f q₃, f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h23, ne_of_gt a2_4, ne_of_gt a2_5, ne_of_gt a2_6, ne_of_gt a2_7, ne_of_gt a2_8⟩
  have e3 : f q₃ ∉ ({f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h34, ne_of_gt a3_5, ne_of_gt a3_6, ne_of_gt a3_7, ne_of_gt a3_8⟩
  have e4 : f q₄ ∉ ({f q₅, f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h45, ne_of_gt a4_6, ne_of_gt a4_7, ne_of_gt a4_8⟩
  have e5 : f q₅ ∉ ({f q₆, f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h56, ne_of_gt a5_7, ne_of_gt a5_8⟩
  have e6 : f q₆ ∉ ({f q₇, f q₈} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt h67, ne_of_gt a6_8⟩
  have e7 : f q₇ ∉ ({f q₈} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    exact ne_of_gt h78
  have hcard : (({f q₀, f q₁, f q₂, f q₃, f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ)).card = 9 := by
    rw [Finset.card_insert_of_notMem e0, Finset.card_insert_of_notMem e1,
      Finset.card_insert_of_notMem e2, Finset.card_insert_of_notMem e3,
      Finset.card_insert_of_notMem e4, Finset.card_insert_of_notMem e5,
      Finset.card_insert_of_notMem e6, Finset.card_insert_of_notMem e7, Finset.card_singleton]
  have hsub : ({f q₀, f q₁, f q₂, f q₃, f q₄, f q₅, f q₆, f q₇, f q₈} : Finset ℝ) ⊆ (Finset.range (N
    + 1)).image f := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact
      Finset.mem_image_of_mem f ‹_›
  calc 9 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **`nnDist` as a prefix-minimum of the `L∞` defect** (`d = 3`, `N = 73`). -/
theorem nnDist_eq_inf (α : Fin 3 → ℝ) {q : ℕ} (hq : q ≤ 73)
    (hne : (Finset.Icc 1 (max q (73 - q))).Nonempty) :
    nnDist α 73 q = (Finset.Icc 1 (max q (73 - q))).inf' hne (fun n => delta α (n : ℤ)) := by
  rw [← gapVal_eq_nnDist α (by norm_num) hq, gapVal, dif_pos hne]; rfl

/-- **`card ≥ 9` from the eight record drops** at `m = 50,51,54,55,67,68,71,72`, realized at
`q = 24,23,22,19,18,6,5,2,1` (cutoffs `D = 49,50,51,54,55,67,68,71,72`). -/
theorem card_ge_nine (α : Fin 3 → ℝ)
    (H1 : ∀ n ∈ Finset.Icc (1 : ℕ) 49, delta α 50 < delta α (n : ℤ))
    (H2 : ∀ n ∈ Finset.Icc (1 : ℕ) 50, delta α 51 < delta α (n : ℤ))
    (H3 : ∀ n ∈ Finset.Icc (1 : ℕ) 51, delta α 54 < delta α (n : ℤ))
    (H4 : ∀ n ∈ Finset.Icc (1 : ℕ) 54, delta α 55 < delta α (n : ℤ))
    (H5 : ∀ n ∈ Finset.Icc (1 : ℕ) 55, delta α 67 < delta α (n : ℤ))
    (H6 : ∀ n ∈ Finset.Icc (1 : ℕ) 67, delta α 68 < delta α (n : ℤ))
    (H7 : ∀ n ∈ Finset.Icc (1 : ℕ) 68, delta α 71 < delta α (n : ℤ))
    (H8 : ∀ n ∈ Finset.Icc (1 : ℕ) 71, delta α 72 < delta α (n : ℤ)) :
    9 ≤ ((Finset.range 74).image (nnDist α 73)).card := by
  have ne49 : (Finset.Icc 1 49).Nonempty := ⟨1, by decide⟩
  have ne50 : (Finset.Icc 1 50).Nonempty := ⟨1, by decide⟩
  have ne51 : (Finset.Icc 1 51).Nonempty := ⟨1, by decide⟩
  have ne54 : (Finset.Icc 1 54).Nonempty := ⟨1, by decide⟩
  have ne55 : (Finset.Icc 1 55).Nonempty := ⟨1, by decide⟩
  have ne67 : (Finset.Icc 1 67).Nonempty := ⟨1, by decide⟩
  have ne68 : (Finset.Icc 1 68).Nonempty := ⟨1, by decide⟩
  have ne71 : (Finset.Icc 1 71).Nonempty := ⟨1, by decide⟩
  have ne72 : (Finset.Icc 1 72).Nonempty := ⟨1, by decide⟩
  have v24 : nnDist α 73 24 = (Finset.Icc 1 49).inf' ne49 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne49
  have v23 : nnDist α 73 23 = (Finset.Icc 1 50).inf' ne50 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne50
  have v22 : nnDist α 73 22 = (Finset.Icc 1 51).inf' ne51 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne51
  have v19 : nnDist α 73 19 = (Finset.Icc 1 54).inf' ne54 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne54
  have v18 : nnDist α 73 18 = (Finset.Icc 1 55).inf' ne55 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne55
  have v6 : nnDist α 73 6 = (Finset.Icc 1 67).inf' ne67 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne67
  have v5 : nnDist α 73 5 = (Finset.Icc 1 68).inf' ne68 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne68
  have v2 : nnDist α 73 2 = (Finset.Icc 1 71).inf' ne71 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne71
  have v1 : nnDist α 73 1 = (Finset.Icc 1 72).inf' ne72 (fun n => delta α n) := nnDist_eq_inf α
      (by norm_num) ne72
  refine nine_le_card_image (nnDist α 73)
    (q₀ := 24) (q₁ := 23) (q₂ := 22) (q₃ := 19) (q₄ := 18) (q₅ := 6) (q₆ := 5) (q₇ := 2) (q₈ := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [v23, v24]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 50 (by decide) ne49 ne50 (fun n hn => ?_)
    change delta α (50 : ℤ) < delta α (n : ℤ); exact H1 n hn
  · rw [v22, v23]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 51 (by decide) ne50 ne51 (fun n hn => ?_)
    change delta α (51 : ℤ) < delta α (n : ℤ); exact H2 n hn
  · rw [v19, v22]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 54 (by decide) ne51 ne54 (fun n hn => ?_)
    change delta α (54 : ℤ) < delta α (n : ℤ); exact H3 n hn
  · rw [v18, v19]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 55 (by decide) ne54 ne55 (fun n hn => ?_)
    change delta α (55 : ℤ) < delta α (n : ℤ); exact H4 n hn
  · rw [v6, v18]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 67 (by decide) ne55 ne67 (fun n hn => ?_)
    change delta α (67 : ℤ) < delta α (n : ℤ); exact H5 n hn
  · rw [v5, v6]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 68 (by decide) ne67 ne68 (fun n hn => ?_)
    change delta α (68 : ℤ) < delta α (n : ℤ); exact H6 n hn
  · rw [v2, v5]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 71 (by decide) ne68 ne71 (fun n hn => ?_)
    change delta α (71 : ℤ) < delta α (n : ℤ); exact H7 n hn
  · rw [v1, v2]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 72 (by decide) ne71 ne72 (fun n hn => ?_)
    change delta α (72 : ℤ) < delta α (n : ℤ); exact H8 n hn

/-! ### Rational → irrational upgrade by Lipschitz-openness -/

theorem delta_sub_le (α β : Fin 3 → ℝ) (d : ℤ) :
    delta α d ≤ delta β d + |(d : ℝ)| * ‖α - β‖ := by
  have hC : ∀ p : Fin 3 → ℤ, delta α d ≤ ‖rem β d p‖ + |(d : ℝ)| * ‖α - β‖ := by
    intro p
    have h1 : delta α d ≤ ‖rem α d p‖ := delta_le α d p
    have hdiff : rem α d p - rem β d p = (d : ℝ) • (α - β) := by simp only [rem, smul_sub]; ring
    have he : rem β d p + (d : ℝ) • (α - β) = rem α d p := by rw [← hdiff]; ring
    have h2 : ‖rem α d p‖ ≤ ‖rem β d p‖ + ‖(d : ℝ) • (α - β)‖ := by
      have := norm_add_le (rem β d p) ((d : ℝ) • (α - β)); rwa [he] at this
    rw [norm_smul, Real.norm_eq_abs] at h2
    linarith
  have hkey : delta α d - |(d : ℝ)| * ‖α - β‖ ≤ delta β d := le_ciInf (fun p => by linarith [hC p])
  linarith

/-- The perturbed witness `α* + (s,0,0)`. -/
noncomputable def aprt (s : ℝ) : Fin 3 → ℝ := ![-785 / 50000 + s, -11872 / 50000, -2875 / 50000]

theorem aprt_irrational {s : ℝ} (hs : Irrational s) : Irrational (aprt s 0) := by
  have h : aprt s 0 = ((-785 / 50000 : ℚ) : ℝ) + s := by
    rw [show ((-785 / 50000 : ℚ) : ℝ) = -785 / 50000 by norm_num]; simp [aprt]
  rw [h]; exact hs.ratCast_add _

theorem norm_aprt (s : ℝ) (hs : 0 ≤ s) : ‖aprt s - astar‖ = s := by
  have e0 : (aprt s - astar) 0 = s := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_zero]; ring
  have e1 : (aprt s - astar) 1 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  have e2 : (aprt s - astar) 2 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons];
      ring
  have b0 : ‖(aprt s - astar) 0‖ ≤ s := by rw [Real.norm_eq_abs, e0, abs_of_nonneg hs]
  have b1 : ‖(aprt s - astar) 1‖ ≤ s := by rw [Real.norm_eq_abs, e1, abs_zero]; exact hs
  have b2 : ‖(aprt s - astar) 2‖ ≤ s := by rw [Real.norm_eq_abs, e2, abs_zero]; exact hs
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hs]; intro i; fin_cases i
    · exact b0
    · exact b1
    · exact b2
  · calc s = ‖(aprt s - astar) 0‖ := by rw [e0, Real.norm_eq_abs, abs_of_nonneg hs]
      _ ≤ ‖aprt s - astar‖ := norm_le_pi_norm _ 0

theorem norm_aprt' (s : ℝ) (hs : 0 ≤ s) : ‖astar - aprt s‖ = s := by
  have e0 : (astar - aprt s) 0 = -s := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_zero]; ring
  have e1 : (astar - aprt s) 1 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  have e2 : (astar - aprt s) 2 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons];
      ring
  have b0 : ‖(astar - aprt s) 0‖ ≤ s := by rw [Real.norm_eq_abs, e0, abs_neg, abs_of_nonneg hs]
  have b1 : ‖(astar - aprt s) 1‖ ≤ s := by rw [Real.norm_eq_abs, e1, abs_zero]; exact hs
  have b2 : ‖(astar - aprt s) 2‖ ≤ s := by rw [Real.norm_eq_abs, e2, abs_zero]; exact hs
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hs]; intro i; fin_cases i
    · exact b0
    · exact b1
    · exact b2
  · calc s = ‖(astar - aprt s) 0‖ := by rw [e0, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
      _ ≤ ‖astar - aprt s‖ := norm_le_pi_norm _ 0

theorem transport (s : ℝ) (hs0 : 0 ≤ s) (m n : ℤ) (Mm Mn : ℝ)
    (hm : delta astar m = Mm / 50000) (hn : delta astar n = Mn / 50000)
    (hgap : 50000 * ((|(m : ℝ)| + |(n : ℝ)|) * s) < Mn - Mm) :
    delta (aprt s) m < delta (aprt s) n := by
  have hd1 := delta_sub_le (aprt s) astar m
  have hd2 := delta_sub_le astar (aprt s) n
  rw [norm_aprt s hs0, hm] at hd1
  rw [norm_aprt' s hs0, hn] at hd2
  have hexp : 50000 * ((|(m : ℝ)| + |(n : ℝ)|) * s)
      = 50000 * (|(m : ℝ)| * s) + 50000 * (|(n : ℝ)| * s) := by ring
  rw [hexp] at hgap
  obtain ⟨U, hU⟩ : ∃ U, |(m : ℝ)| * s = U := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, |(n : ℝ)| * s = V := ⟨_, rfl⟩
  rw [hU] at hd1 hgap
  rw [hV] at hd2 hgap
  linarith [hd1, hd2, hgap]

theorem Hpair (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) (m n Mm Mn : ℤ)
    (hm : delta astar m = (Mm : ℝ) / 50000) (hn : delta astar n = (Mn : ℝ) / 50000)
    (hc : |(m : ℝ)| + |(n : ℝ)| ≤ 144) (hgapZ : Mm + 1 ≤ Mn) :
    delta (aprt s) m < delta (aprt s) n := by
  refine transport s hs0 m n (Mm : ℝ) (Mn : ℝ) hm hn ?_
  have h1 : (|(m : ℝ)| + |(n : ℝ)|) * s ≤ 144 * s := mul_le_mul_of_nonneg_right hc hs0
  have h2 : (Mm : ℝ) + 1 ≤ (Mn : ℝ) := by exact_mod_cast hgapZ
  linarith [h1, h2, hsmall]

theorem H1_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 49, delta (aprt s) 50 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 50 1 10750 11872 dstar50 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 2 10750 23744 dstar50 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 3 10750 14384 dstar50 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 4 10750 11500 dstar50 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 5 10750 14375 dstar50 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 6 10750 21232 dstar50 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 7 10750 20125 dstar50 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 8 10750 23000 dstar50 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 9 10750 24125 dstar50 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 10 10750 21250 dstar50 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 11 10750 19408 dstar50 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 12 10750 15500 dstar50 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 13 10750 12625 dstar50 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 14 10750 16208 dstar50 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 15 10750 21920 dstar50 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 16 10750 12560 dstar50 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 17 10750 13345 dstar50 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 18 10750 14130 dstar50 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 19 10750 24432 dstar50 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 20 10750 15700 dstar50 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 21 10750 16485 dstar50 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 22 10750 17270 dstar50 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 23 10750 23056 dstar50 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 24 10750 19000 dstar50 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 25 10750 21875 dstar50 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 26 10750 24750 dstar50 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 27 10750 22375 dstar50 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 28 10750 21980 dstar50 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 29 10750 22765 dstar50 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 30 10750 23550 dstar50 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 31 10750 24335 dstar50 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 32 10750 24880 dstar50 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 33 10750 24095 dstar50 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 34 10750 23310 dstar50 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 35 10750 22525 dstar50 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 36 10750 22608 dstar50 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 37 10750 20955 dstar50 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 38 10750 20170 dstar50 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 39 10750 19385 dstar50 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 40 10750 24880 dstar50 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 41 10750 17875 dstar50 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 42 10750 20750 dstar50 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 43 10750 23625 dstar50 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 44 10750 23500 dstar50 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 45 10750 20625 dstar50 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 46 10750 17750 dstar50 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 47 10750 14875 dstar50 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 48 10750 19856 dstar50 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 50 49 10750 18272 dstar50 dstar49 (by norm_num) (by norm_num)

theorem H2_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 50, delta (aprt s) 51 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 51 1 9965 11872 dstar51 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 2 9965 23744 dstar51 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 3 9965 14384 dstar51 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 4 9965 11500 dstar51 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 5 9965 14375 dstar51 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 6 9965 21232 dstar51 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 7 9965 20125 dstar51 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 8 9965 23000 dstar51 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 9 9965 24125 dstar51 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 10 9965 21250 dstar51 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 11 9965 19408 dstar51 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 12 9965 15500 dstar51 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 13 9965 12625 dstar51 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 14 9965 16208 dstar51 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 15 9965 21920 dstar51 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 16 9965 12560 dstar51 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 17 9965 13345 dstar51 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 18 9965 14130 dstar51 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 19 9965 24432 dstar51 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 20 9965 15700 dstar51 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 21 9965 16485 dstar51 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 22 9965 17270 dstar51 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 23 9965 23056 dstar51 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 24 9965 19000 dstar51 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 25 9965 21875 dstar51 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 26 9965 24750 dstar51 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 27 9965 22375 dstar51 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 28 9965 21980 dstar51 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 29 9965 22765 dstar51 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 30 9965 23550 dstar51 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 31 9965 24335 dstar51 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 32 9965 24880 dstar51 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 33 9965 24095 dstar51 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 34 9965 23310 dstar51 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 35 9965 22525 dstar51 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 36 9965 22608 dstar51 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 37 9965 20955 dstar51 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 38 9965 20170 dstar51 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 39 9965 19385 dstar51 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 40 9965 24880 dstar51 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 41 9965 17875 dstar51 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 42 9965 20750 dstar51 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 43 9965 23625 dstar51 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 44 9965 23500 dstar51 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 45 9965 20625 dstar51 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 46 9965 17750 dstar51 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 47 9965 14875 dstar51 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 48 9965 19856 dstar51 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 49 9965 18272 dstar51 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 51 50 9965 10750 dstar51 dstar50 (by norm_num) (by norm_num)

theorem H3_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 51, delta (aprt s) 54 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 54 1 8912 11872 dstar54 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 2 8912 23744 dstar54 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 3 8912 14384 dstar54 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 4 8912 11500 dstar54 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 5 8912 14375 dstar54 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 6 8912 21232 dstar54 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 7 8912 20125 dstar54 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 8 8912 23000 dstar54 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 9 8912 24125 dstar54 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 10 8912 21250 dstar54 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 11 8912 19408 dstar54 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 12 8912 15500 dstar54 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 13 8912 12625 dstar54 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 14 8912 16208 dstar54 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 15 8912 21920 dstar54 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 16 8912 12560 dstar54 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 17 8912 13345 dstar54 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 18 8912 14130 dstar54 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 19 8912 24432 dstar54 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 20 8912 15700 dstar54 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 21 8912 16485 dstar54 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 22 8912 17270 dstar54 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 23 8912 23056 dstar54 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 24 8912 19000 dstar54 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 25 8912 21875 dstar54 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 26 8912 24750 dstar54 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 27 8912 22375 dstar54 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 28 8912 21980 dstar54 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 29 8912 22765 dstar54 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 30 8912 23550 dstar54 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 31 8912 24335 dstar54 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 32 8912 24880 dstar54 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 33 8912 24095 dstar54 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 34 8912 23310 dstar54 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 35 8912 22525 dstar54 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 36 8912 22608 dstar54 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 37 8912 20955 dstar54 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 38 8912 20170 dstar54 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 39 8912 19385 dstar54 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 40 8912 24880 dstar54 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 41 8912 17875 dstar54 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 42 8912 20750 dstar54 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 43 8912 23625 dstar54 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 44 8912 23500 dstar54 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 45 8912 20625 dstar54 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 46 8912 17750 dstar54 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 47 8912 14875 dstar54 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 48 8912 19856 dstar54 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 49 8912 18272 dstar54 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 50 8912 10750 dstar54 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 54 51 8912 9965 dstar54 dstar51 (by norm_num) (by norm_num)

theorem H4_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 54, delta (aprt s) 55 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 55 1 8125 11872 dstar55 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 2 8125 23744 dstar55 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 3 8125 14384 dstar55 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 4 8125 11500 dstar55 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 5 8125 14375 dstar55 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 6 8125 21232 dstar55 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 7 8125 20125 dstar55 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 8 8125 23000 dstar55 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 9 8125 24125 dstar55 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 10 8125 21250 dstar55 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 11 8125 19408 dstar55 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 12 8125 15500 dstar55 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 13 8125 12625 dstar55 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 14 8125 16208 dstar55 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 15 8125 21920 dstar55 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 16 8125 12560 dstar55 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 17 8125 13345 dstar55 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 18 8125 14130 dstar55 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 19 8125 24432 dstar55 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 20 8125 15700 dstar55 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 21 8125 16485 dstar55 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 22 8125 17270 dstar55 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 23 8125 23056 dstar55 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 24 8125 19000 dstar55 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 25 8125 21875 dstar55 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 26 8125 24750 dstar55 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 27 8125 22375 dstar55 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 28 8125 21980 dstar55 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 29 8125 22765 dstar55 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 30 8125 23550 dstar55 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 31 8125 24335 dstar55 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 32 8125 24880 dstar55 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 33 8125 24095 dstar55 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 34 8125 23310 dstar55 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 35 8125 22525 dstar55 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 36 8125 22608 dstar55 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 37 8125 20955 dstar55 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 38 8125 20170 dstar55 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 39 8125 19385 dstar55 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 40 8125 24880 dstar55 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 41 8125 17875 dstar55 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 42 8125 20750 dstar55 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 43 8125 23625 dstar55 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 44 8125 23500 dstar55 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 45 8125 20625 dstar55 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 46 8125 17750 dstar55 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 47 8125 14875 dstar55 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 48 8125 19856 dstar55 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 49 8125 18272 dstar55 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 50 8125 10750 dstar55 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 51 8125 9965 dstar55 dstar51 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 52 8125 17344 dstar55 dstar52 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 53 8125 20784 dstar55 dstar53 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 55 54 8125 8912 dstar55 dstar54 (by norm_num) (by norm_num)

theorem H5_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 55, delta (aprt s) 67 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 67 1 7375 11872 dstar67 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 2 7375 23744 dstar67 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 3 7375 14384 dstar67 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 4 7375 11500 dstar67 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 5 7375 14375 dstar67 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 6 7375 21232 dstar67 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 7 7375 20125 dstar67 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 8 7375 23000 dstar67 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 9 7375 24125 dstar67 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 10 7375 21250 dstar67 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 11 7375 19408 dstar67 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 12 7375 15500 dstar67 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 13 7375 12625 dstar67 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 14 7375 16208 dstar67 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 15 7375 21920 dstar67 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 16 7375 12560 dstar67 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 17 7375 13345 dstar67 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 18 7375 14130 dstar67 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 19 7375 24432 dstar67 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 20 7375 15700 dstar67 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 21 7375 16485 dstar67 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 22 7375 17270 dstar67 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 23 7375 23056 dstar67 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 24 7375 19000 dstar67 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 25 7375 21875 dstar67 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 26 7375 24750 dstar67 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 27 7375 22375 dstar67 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 28 7375 21980 dstar67 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 29 7375 22765 dstar67 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 30 7375 23550 dstar67 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 31 7375 24335 dstar67 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 32 7375 24880 dstar67 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 33 7375 24095 dstar67 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 34 7375 23310 dstar67 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 35 7375 22525 dstar67 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 36 7375 22608 dstar67 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 37 7375 20955 dstar67 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 38 7375 20170 dstar67 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 39 7375 19385 dstar67 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 40 7375 24880 dstar67 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 41 7375 17875 dstar67 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 42 7375 20750 dstar67 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 43 7375 23625 dstar67 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 44 7375 23500 dstar67 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 45 7375 20625 dstar67 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 46 7375 17750 dstar67 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 47 7375 14875 dstar67 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 48 7375 19856 dstar67 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 49 7375 18272 dstar67 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 50 7375 10750 dstar67 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 51 7375 9965 dstar67 dstar51 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 52 7375 17344 dstar67 dstar52 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 53 7375 20784 dstar67 dstar53 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 54 7375 8912 dstar67 dstar54 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 67 55 7375 8125 dstar67 dstar55 (by norm_num) (by norm_num)

theorem H6_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 67, delta (aprt s) 68 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 68 1 7296 11872 dstar68 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 2 7296 23744 dstar68 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 3 7296 14384 dstar68 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 4 7296 11500 dstar68 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 5 7296 14375 dstar68 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 6 7296 21232 dstar68 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 7 7296 20125 dstar68 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 8 7296 23000 dstar68 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 9 7296 24125 dstar68 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 10 7296 21250 dstar68 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 11 7296 19408 dstar68 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 12 7296 15500 dstar68 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 13 7296 12625 dstar68 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 14 7296 16208 dstar68 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 15 7296 21920 dstar68 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 16 7296 12560 dstar68 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 17 7296 13345 dstar68 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 18 7296 14130 dstar68 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 19 7296 24432 dstar68 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 20 7296 15700 dstar68 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 21 7296 16485 dstar68 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 22 7296 17270 dstar68 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 23 7296 23056 dstar68 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 24 7296 19000 dstar68 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 25 7296 21875 dstar68 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 26 7296 24750 dstar68 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 27 7296 22375 dstar68 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 28 7296 21980 dstar68 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 29 7296 22765 dstar68 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 30 7296 23550 dstar68 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 31 7296 24335 dstar68 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 32 7296 24880 dstar68 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 33 7296 24095 dstar68 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 34 7296 23310 dstar68 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 35 7296 22525 dstar68 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 36 7296 22608 dstar68 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 37 7296 20955 dstar68 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 38 7296 20170 dstar68 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 39 7296 19385 dstar68 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 40 7296 24880 dstar68 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 41 7296 17875 dstar68 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 42 7296 20750 dstar68 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 43 7296 23625 dstar68 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 44 7296 23500 dstar68 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 45 7296 20625 dstar68 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 46 7296 17750 dstar68 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 47 7296 14875 dstar68 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 48 7296 19856 dstar68 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 49 7296 18272 dstar68 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 50 7296 10750 dstar68 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 51 7296 9965 dstar68 dstar51 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 52 7296 17344 dstar68 dstar52 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 53 7296 20784 dstar68 dstar53 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 54 7296 8912 dstar68 dstar54 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 55 7296 8125 dstar68 dstar55 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 56 7296 14832 dstar68 dstar56 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 57 7296 23296 dstar68 dstar57 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 58 7296 16750 dstar68 dstar58 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 59 7296 19625 dstar68 dstar59 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 60 7296 22500 dstar68 dstar60 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 61 7296 24625 dstar68 dstar61 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 62 7296 21750 dstar68 dstar62 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 63 7296 18875 dstar68 dstar63 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 64 7296 16000 dstar68 dstar64 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 65 7296 21680 dstar68 dstar65 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 66 7296 16448 dstar68 dstar66 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 68 67 7296 7375 dstar68 dstar67 (by norm_num) (by norm_num)

theorem H7_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 68, delta (aprt s) 71 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 71 1 7088 11872 dstar71 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 2 7088 23744 dstar71 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 3 7088 14384 dstar71 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 4 7088 11500 dstar71 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 5 7088 14375 dstar71 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 6 7088 21232 dstar71 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 7 7088 20125 dstar71 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 8 7088 23000 dstar71 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 9 7088 24125 dstar71 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 10 7088 21250 dstar71 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 11 7088 19408 dstar71 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 12 7088 15500 dstar71 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 13 7088 12625 dstar71 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 14 7088 16208 dstar71 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 15 7088 21920 dstar71 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 16 7088 12560 dstar71 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 17 7088 13345 dstar71 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 18 7088 14130 dstar71 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 19 7088 24432 dstar71 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 20 7088 15700 dstar71 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 21 7088 16485 dstar71 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 22 7088 17270 dstar71 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 23 7088 23056 dstar71 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 24 7088 19000 dstar71 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 25 7088 21875 dstar71 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 26 7088 24750 dstar71 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 27 7088 22375 dstar71 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 28 7088 21980 dstar71 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 29 7088 22765 dstar71 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 30 7088 23550 dstar71 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 31 7088 24335 dstar71 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 32 7088 24880 dstar71 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 33 7088 24095 dstar71 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 34 7088 23310 dstar71 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 35 7088 22525 dstar71 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 36 7088 22608 dstar71 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 37 7088 20955 dstar71 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 38 7088 20170 dstar71 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 39 7088 19385 dstar71 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 40 7088 24880 dstar71 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 41 7088 17875 dstar71 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 42 7088 20750 dstar71 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 43 7088 23625 dstar71 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 44 7088 23500 dstar71 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 45 7088 20625 dstar71 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 46 7088 17750 dstar71 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 47 7088 14875 dstar71 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 48 7088 19856 dstar71 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 49 7088 18272 dstar71 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 50 7088 10750 dstar71 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 51 7088 9965 dstar71 dstar51 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 52 7088 17344 dstar71 dstar52 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 53 7088 20784 dstar71 dstar53 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 54 7088 8912 dstar71 dstar54 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 55 7088 8125 dstar71 dstar55 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 56 7088 14832 dstar71 dstar56 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 57 7088 23296 dstar71 dstar57 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 58 7088 16750 dstar71 dstar58 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 59 7088 19625 dstar71 dstar59 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 60 7088 22500 dstar71 dstar60 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 61 7088 24625 dstar71 dstar61 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 62 7088 21750 dstar71 dstar62 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 63 7088 18875 dstar71 dstar63 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 64 7088 16000 dstar71 dstar64 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 65 7088 21680 dstar71 dstar65 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 66 7088 16448 dstar71 dstar66 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 67 7088 7375 dstar71 dstar67 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 71 68 7088 7296 dstar71 dstar68 (by norm_num) (by norm_num)

theorem H8_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 7200000 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 71, delta (aprt s) 72 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 72 1 7000 11872 dstar72 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 2 7000 23744 dstar72 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 3 7000 14384 dstar72 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 4 7000 11500 dstar72 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 5 7000 14375 dstar72 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 6 7000 21232 dstar72 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 7 7000 20125 dstar72 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 8 7000 23000 dstar72 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 9 7000 24125 dstar72 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 10 7000 21250 dstar72 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 11 7000 19408 dstar72 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 12 7000 15500 dstar72 dstar12 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 13 7000 12625 dstar72 dstar13 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 14 7000 16208 dstar72 dstar14 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 15 7000 21920 dstar72 dstar15 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 16 7000 12560 dstar72 dstar16 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 17 7000 13345 dstar72 dstar17 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 18 7000 14130 dstar72 dstar18 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 19 7000 24432 dstar72 dstar19 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 20 7000 15700 dstar72 dstar20 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 21 7000 16485 dstar72 dstar21 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 22 7000 17270 dstar72 dstar22 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 23 7000 23056 dstar72 dstar23 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 24 7000 19000 dstar72 dstar24 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 25 7000 21875 dstar72 dstar25 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 26 7000 24750 dstar72 dstar26 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 27 7000 22375 dstar72 dstar27 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 28 7000 21980 dstar72 dstar28 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 29 7000 22765 dstar72 dstar29 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 30 7000 23550 dstar72 dstar30 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 31 7000 24335 dstar72 dstar31 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 32 7000 24880 dstar72 dstar32 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 33 7000 24095 dstar72 dstar33 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 34 7000 23310 dstar72 dstar34 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 35 7000 22525 dstar72 dstar35 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 36 7000 22608 dstar72 dstar36 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 37 7000 20955 dstar72 dstar37 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 38 7000 20170 dstar72 dstar38 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 39 7000 19385 dstar72 dstar39 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 40 7000 24880 dstar72 dstar40 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 41 7000 17875 dstar72 dstar41 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 42 7000 20750 dstar72 dstar42 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 43 7000 23625 dstar72 dstar43 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 44 7000 23500 dstar72 dstar44 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 45 7000 20625 dstar72 dstar45 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 46 7000 17750 dstar72 dstar46 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 47 7000 14875 dstar72 dstar47 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 48 7000 19856 dstar72 dstar48 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 49 7000 18272 dstar72 dstar49 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 50 7000 10750 dstar72 dstar50 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 51 7000 9965 dstar72 dstar51 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 52 7000 17344 dstar72 dstar52 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 53 7000 20784 dstar72 dstar53 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 54 7000 8912 dstar72 dstar54 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 55 7000 8125 dstar72 dstar55 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 56 7000 14832 dstar72 dstar56 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 57 7000 23296 dstar72 dstar57 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 58 7000 16750 dstar72 dstar58 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 59 7000 19625 dstar72 dstar59 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 60 7000 22500 dstar72 dstar60 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 61 7000 24625 dstar72 dstar61 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 62 7000 21750 dstar72 dstar62 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 63 7000 18875 dstar72 dstar63 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 64 7000 16000 dstar72 dstar64 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 65 7000 21680 dstar72 dstar65 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 66 7000 16448 dstar72 dstar66 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 67 7000 7375 dstar72 dstar67 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 68 7000 7296 dstar72 dstar68 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 69 7000 19168 dstar72 dstar69 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 70 7000 18960 dstar72 dstar70 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 72 71 7000 7088 dstar72 dstar71 (by norm_num) (by norm_num)

/-- **The `L∞` three-torus bound `g_∞ ≤ 2^d+1` is sharp for `d = 3`.** There is a Kronecker vector
`α : Fin 3 → ℝ` with an irrational coordinate and `N ≥ 2` whose orbit on `𝕋³` realizes at least nine
distinct sup-norm nearest-neighbour distances; with `SimDirichlet.nnDist_count_unconditional` (`≤
9`)
this gives `g_∞(3) = 9` — the Shutov bound `2^d+1` is attained (Haynes–Ramirez, `d ≤ 3`). The
witness
is `α = (−785/50000 + s, −11872/50000, −2875/50000)` for a small irrational `s`; `card ≥ 9`
transports
from the rational `α*` by the dynamics-free Lipschitz argument. -/
theorem nine_attained : ∃ α : Fin 3 → ℝ, (∃ k, Irrational (α k)) ∧
    ∃ N, 2 ≤ N ∧ 9 ≤ ((Finset.range (N + 1)).image (nnDist α N)).card := by
  obtain ⟨s, hs_irr, hs_pos, hs_lt⟩ :=
    exists_irrational_btwn (show (0 : ℝ) < 1 / 7200000 by norm_num)
  have hsmall : 7200000 * s < 1 := by
    rw [lt_div_iff₀ (by norm_num)] at hs_lt; linarith [hs_lt]
  exact ⟨aprt s, ⟨0, aprt_irrational hs_irr⟩, 73, by norm_num,
    card_ge_nine (aprt s) (H1_aprt s hs_pos.le hsmall) (H2_aprt s hs_pos.le hsmall)
      (H3_aprt s hs_pos.le hsmall) (H4_aprt s hs_pos.le hsmall) (H5_aprt s hs_pos.le hsmall)
      (H6_aprt s hs_pos.le hsmall) (H7_aprt s hs_pos.le hsmall) (H8_aprt s hs_pos.le hsmall)⟩

end ThreeGap.LinftyRecords3
