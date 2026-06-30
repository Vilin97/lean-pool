/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.SimultaneousDirichlet
import LeanPool.ThreeGap.EuclideanFiveDistanceSharpArith

/-!
# Arithmetic sharpness of the `L∞` five-distance theorem `g_∞ ≤ 5` on `𝕋²` (dynamics-free)

`nnDist_count_plane_unconditional` proves the **upper** bound: any Kronecker orbit on `𝕋²` has at
most **five** distinct sup-norm nearest-neighbour distances (the `d = 2` case of Shutov's `2^d +
1`).
This file shows the bound is **sharp** by an explicit, dynamics-free witness, mirroring the
Euclidean
`EuclideanRecords.sharp_attained` but with the `L∞` (sup-norm) defect, which is *integer-exact*:
`delta α* d = max(|r(4d)|, |r(15d)|)/47` for balanced residues mod `47` — **no square roots**.

## The witness
`α* = (4/47, 15/47)`, `N = 13`. The scaled sup-norm defects
`M_d = max(|r(4d)|, |r(15d)|)` for `d = 1,…,13` are

`[15, 17, 12, 16, 20, 23, 19, 21, 11, 9, 23, 8, 7]`,

with record minima at `d = 1, 3, 9, 10, 12, 13` (values `15 > 12 > 11 > 9 > 8 > 7`). The four
records
inside the doubling window `(⌈13/2⌉, 13] = (7, 13]` are `9, 10, 12, 13` — giving the **five**
distinct
distances `12/47 > 11/47 > 9/47 > 8/47 > 7/47`, realized at `q = 6, 4, 3, 1, 0` (cutoffs
`D = 7, 9, 10, 12, 13`).

## Method (cross-field reuse)
The minimax identity `min_p max_k |dα_k − p_k| = max_k min_{p_k}|dα_k − p_k|` (independent
coordinates) makes the sup-norm defect exactly the `max` of two balanced residues — so every
comparison is between *integers*, and the rational→irrational transport gap is *linear* (no
`√`-gap):
`s ∈ (0, 1/1222)` suffices. The combinatorial core
(`five_le_card_image_of_strictAnti_chain`, `inf_lt_inf`) and the integer minimum (`sq_residue_le`)
are reused verbatim from the Euclidean development.
-/

namespace ThreeGap.LinftyRecords

open scoped Real
open ThreeGap.SimApprox ThreeGap.DeltaCost ThreeGap.Chevallier ThreeGap.SimDirichlet
open ThreeGap.EuclideanRecords (sq_residue_le five_le_card_image_of_strictAnti_chain inf_lt_inf)

/-- The `L∞` rational witness `α* = (4/47, 15/47)`. -/
noncomputable def astar : Fin 2 → ℝ := ![4 / 47, 15 / 47]

/-- **Per-coordinate integer minimum (`L∞` crux).** The balanced residue `|r|` lower-bounds
`|a − m·k|` for every `k` — the absolute-value version of `sq_residue_le`. -/
theorem abs_residue_le (m r a : ℤ) (hm : 0 < m) (h2r : 2 * |r| ≤ m) (hcong : m ∣ (a - r)) (k : ℤ) :
    |(r : ℝ)| ≤ |(a : ℝ) - m * k| := by
  have hsq := sq_residue_le m r a hm h2r hcong k
  have hsqR : (r : ℝ) ^ 2 ≤ ((a : ℝ) - m * k) ^ 2 := by exact_mod_cast hsq
  calc |(r : ℝ)| = Real.sqrt ((r : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((a : ℝ) - m * k) ^ 2) := Real.sqrt_le_sqrt hsqR
    _ = |(a : ℝ) - m * k| := Real.sqrt_sq_eq_abs _

/-- **The witness defect is coordinatewise-exact.** With `α* = (4/47, 15/47)`, balanced residues
`4d ≡ r₀`, `15d ≡ r₁ (mod 47)` give `delta α* d = M/47`, where `M = max(|r₀|, |r₁|)` (provided as
`M` with `|r₀| ≤ M`, `|r₁| ≤ M`, `M ∈ {|r₀|, |r₁|}`). Upper bound at the rounding `(n₀, n₁)`; lower
bound coordinatewise via `abs_residue_le` and `norm_le_pi_norm` (the sup norm dominates each
coordinate). -/
theorem delta_astar (d n₀ n₁ r₀ r₁ M : ℤ)
    (hr0 : 4 * d = r₀ + 47 * n₀) (hr1 : 15 * d = r₁ + 47 * n₁)
    (hb0 : 2 * |r₀| ≤ 47) (hb1 : 2 * |r₁| ≤ 47)
    (hM0 : |r₀| ≤ M) (hM1 : |r₁| ≤ M) (hMa : M = |r₀| ∨ M = |r₁|) :
    delta astar d = (M : ℝ) / 47 := by
  have hMnn : (0 : ℝ) ≤ (M : ℝ) / 47 := by
    have h : (0 : ℤ) ≤ M := le_trans (abs_nonneg r₀) hM0
    have : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    positivity
  have normcoord : ∀ z : ℤ, ‖((z : ℝ)) / 47‖ = ((|z| : ℤ) : ℝ) / 47 := by
    intro z
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 47 by norm_num), ← Int.cast_abs]
  have c0 : ∀ p : Fin 2 → ℤ, (rem astar d p) 0 = ((4 * d - 47 * p 0 : ℤ) : ℝ) / 47 := by
    intro p
    simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    push_cast; ring
  have c1 : ∀ p : Fin 2 → ℤ, (rem astar d p) 1 = ((15 * d - 47 * p 1 : ℤ) : ℝ) / 47 := by
    intro p
    simp only [rem, astar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
    push_cast; ring
  refine le_antisymm ?_ ?_
  · -- upper bound: attained at `![n₀, n₁]`
    refine le_trans (delta_le astar d ![n₀, n₁]) ?_
    rw [pi_norm_le_iff_of_nonneg hMnn, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [c0 ![n₀, n₁]]
      have hz : (4 * d - 47 * (![n₀, n₁] : Fin 2 → ℤ) 0) = r₀ := by
        simp only [Matrix.cons_val_zero]; linarith [hr0]
      rw [hz, normcoord r₀]
      have hle : ((|r₀| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast hM0
      linarith
    · rw [c1 ![n₀, n₁]]
      have hz : (15 * d - 47 * (![n₀, n₁] : Fin 2 → ℤ) 1) = r₁ := by
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; linarith [hr1]
      rw [hz, normcoord r₁]
      have hle : ((|r₁| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast hM1
      linarith
  · -- lower bound: `M/47` is below every translate
    refine le_ciInf (fun p => ?_)
    rcases hMa with hMa | hMa
    · refine le_trans ?_ (norm_le_pi_norm (rem astar d p) 0)
      rw [c0 p, normcoord, hMa]
      have hnum : ((|r₀| : ℤ) : ℝ) ≤ ((|4 * d - 47 * p 0| : ℤ) : ℝ) := by
        exact_mod_cast abs_residue_le 47 r₀ (4 * d) (by norm_num) hb0 ⟨n₀, by linarith [hr0]⟩ (p 0)
      linarith
    · refine le_trans ?_ (norm_le_pi_norm (rem astar d p) 1)
      rw [c1 p, normcoord, hMa]
      have hnum : ((|r₁| : ℤ) : ℝ) ≤ ((|15 * d - 47 * p 1| : ℤ) : ℝ) := by
        exact_mod_cast abs_residue_le 47 r₁ (15 * d) (by norm_num) hb1 ⟨n₁, by linarith [hr1]⟩ (p 1)
      linarith

/-- The thirteen witness defects `delta α* d = M_d/47`, `d = 1,…,13`, with
`M_d = [15,17,12,16,20,23,19,21,11,9,23,8,7]` — from `delta_astar` at the balanced residues of
`4d, 15d` mod `47`. -/
theorem dstar1 : delta astar 1 = (15 : ℝ) / 47 := by
  rw [delta_astar 1 0 0 4 15 15 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar2 : delta astar 2 = (17 : ℝ) / 47 := by
  rw [delta_astar 2 0 1 8 (-17) 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar3 : delta astar 3 = (12 : ℝ) / 47 := by
  rw [delta_astar 3 0 1 12 (-2) 12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar4 : delta astar 4 = (16 : ℝ) / 47 := by
  rw [delta_astar 4 0 1 16 13 16 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar5 : delta astar 5 = (20 : ℝ) / 47 := by
  rw [delta_astar 5 0 2 20 (-19) 20 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar6 : delta astar 6 = (23 : ℝ) / 47 := by
  rw [delta_astar 6 1 2 (-23) (-4) 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar7 : delta astar 7 = (19 : ℝ) / 47 := by
  rw [delta_astar 7 1 2 (-19) 11 19 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar8 : delta astar 8 = (21 : ℝ) / 47 := by
  rw [delta_astar 8 1 3 (-15) (-21) 21 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar9 : delta astar 9 = (11 : ℝ) / 47 := by
  rw [delta_astar 9 1 3 (-11) (-6) 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar10 : delta astar 10 = (9 : ℝ) / 47 := by
  rw [delta_astar 10 1 3 (-7) 9 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar11 : delta astar 11 = (23 : ℝ) / 47 := by
  rw [delta_astar 11 1 4 (-3) (-23) 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar12 : delta astar 12 = (8 : ℝ) / 47 := by
  rw [delta_astar 12 1 4 1 (-8) 8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num
theorem dstar13 : delta astar 13 = (7 : ℝ) / 47 := by
  rw [delta_astar 13 1 4 5 7 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; norm_num

/-! ### `nnDist` as a prefix-minimum, and `card ≥ 5` from the four record drops -/

/-- **`nnDist` as a prefix-minimum of the `L∞` defect.** `nnDist α 13 q` is the infimum of
`delta α d` over `d ∈ [1, max(q, 13−q)]` (via the repo's `gapVal_eq_nnDist`). -/
theorem nnDist_eq_inf (α : Fin 2 → ℝ) {q : ℕ} (hq : q ≤ 13)
    (hne : (Finset.Icc 1 (max q (13 - q))).Nonempty) :
    nnDist α 13 q = (Finset.Icc 1 (max q (13 - q))).inf' hne (fun n => delta α (n : ℤ)) := by
  rw [← gapVal_eq_nnDist α (by norm_num) hq, gapVal, dif_pos hne]; rfl

/-- **`card ≥ 5` from the four record drops.** If the defect drops strictly below the whole
preceding
prefix at `d = 9, 10, 12, 13`, then the five `nnDist α 13 q` at `q = 6, 4, 3, 1, 0` are strictly
decreasing, so the image has `≥ 5` elements. -/
theorem card_ge_five (α : Fin 2 → ℝ)
    (H1 : ∀ n ∈ Finset.Icc (1 : ℕ) 7, delta α 9 < delta α (n : ℤ))
    (H2 : ∀ n ∈ Finset.Icc (1 : ℕ) 9, delta α 10 < delta α (n : ℤ))
    (H3 : ∀ n ∈ Finset.Icc (1 : ℕ) 10, delta α 12 < delta α (n : ℤ))
    (H4 : ∀ n ∈ Finset.Icc (1 : ℕ) 12, delta α 13 < delta α (n : ℤ)) :
    5 ≤ ((Finset.range 14).image (nnDist α 13)).card := by
  have ne7 : (Finset.Icc 1 7).Nonempty := ⟨1, by decide⟩
  have ne9 : (Finset.Icc 1 9).Nonempty := ⟨1, by decide⟩
  have ne10 : (Finset.Icc 1 10).Nonempty := ⟨1, by decide⟩
  have ne12 : (Finset.Icc 1 12).Nonempty := ⟨1, by decide⟩
  have ne13 : (Finset.Icc 1 13).Nonempty := ⟨1, by decide⟩
  have v6 : nnDist α 13 6 = (Finset.Icc 1 7).inf' ne7 (fun n => delta α n) :=
    nnDist_eq_inf α (by norm_num) ne7
  have v4 : nnDist α 13 4 = (Finset.Icc 1 9).inf' ne9 (fun n => delta α n) :=
    nnDist_eq_inf α (by norm_num) ne9
  have v3 : nnDist α 13 3 = (Finset.Icc 1 10).inf' ne10 (fun n => delta α n) :=
    nnDist_eq_inf α (by norm_num) ne10
  have v1 : nnDist α 13 1 = (Finset.Icc 1 12).inf' ne12 (fun n => delta α n) :=
    nnDist_eq_inf α (by norm_num) ne12
  have v0 : nnDist α 13 0 = (Finset.Icc 1 13).inf' ne13 (fun n => delta α n) :=
    nnDist_eq_inf α (by norm_num) ne13
  refine five_le_card_image_of_strictAnti_chain (nnDist α 13)
    (q₀ := 6) (q₁ := 4) (q₂ := 3) (q₃ := 1) (q₄ := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_
  · rw [v4, v6]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 9 (by decide) ne7 ne9 (fun n hn => ?_)
    change delta α (9 : ℤ) < delta α (n : ℤ); exact H1 n hn
  · rw [v3, v4]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 10 (by decide) ne9 ne10 (fun n hn => ?_)
    change delta α (10 : ℤ) < delta α (n : ℤ); exact H2 n hn
  · rw [v1, v3]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 12 (by decide) ne10 ne12 (fun n hn => ?_)
    change delta α (12 : ℤ) < delta α (n : ℤ); exact H3 n hn
  · rw [v0, v1]
    refine inf_lt_inf (fun n => delta α (n : ℤ)) 13 (by decide) ne12 ne13 (fun n hn => ?_)
    change delta α (13 : ℤ) < delta α (n : ℤ); exact H4 n hn

/-! ### Rational → irrational upgrade by Lipschitz-openness -/

/-- **`delta · d` is `|d|`-Lipschitz in `α`.** (Both are distances to the lattice; perturbing `α` by
`α − β` moves `d·α` by `d·(α−β)`.) -/
theorem delta_sub_le (α β : Fin 2 → ℝ) (d : ℤ) :
    delta α d ≤ delta β d + |(d : ℝ)| * ‖α - β‖ := by
  have hC : ∀ p : Fin 2 → ℤ, delta α d ≤ ‖rem β d p‖ + |(d : ℝ)| * ‖α - β‖ := by
    intro p
    have h1 : delta α d ≤ ‖rem α d p‖ := delta_le α d p
    have hdiff : rem α d p - rem β d p = (d : ℝ) • (α - β) := by
      simp only [rem, smul_sub]; ring
    have he : rem β d p + (d : ℝ) • (α - β) = rem α d p := by rw [← hdiff]; ring
    have h2 : ‖rem α d p‖ ≤ ‖rem β d p‖ + ‖(d : ℝ) • (α - β)‖ := by
      have := norm_add_le (rem β d p) ((d : ℝ) • (α - β)); rwa [he] at this
    rw [norm_smul, Real.norm_eq_abs] at h2
    linarith
  have hkey : delta α d - |(d : ℝ)| * ‖α - β‖ ≤ delta β d :=
    le_ciInf (fun p => by linarith [hC p])
  linarith

/-- The perturbed witness `α* + (s, 0) = (4/47 + s, 15/47)`. -/
noncomputable def aprt (s : ℝ) : Fin 2 → ℝ := ![4 / 47 + s, 15 / 47]

theorem aprt_irrational {s : ℝ} (hs : Irrational s) : Irrational (aprt s 0) := by
  have h : aprt s 0 = ((4 / 47 : ℚ) : ℝ) + s := by
    rw [show ((4 / 47 : ℚ) : ℝ) = 4 / 47 by norm_num]; simp [aprt]
  rw [h]; exact hs.ratCast_add _

theorem norm_aprt (s : ℝ) (hs : 0 ≤ s) : ‖aprt s - astar‖ = s := by
  have e0 : (aprt s - astar) 0 = s := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_zero]; ring
  have e1 : (aprt s - astar) 1 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_one]; ring
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hs, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs, e0, abs_of_nonneg hs]
    · rw [Real.norm_eq_abs, e1, abs_zero]; exact hs
  · calc s = ‖(aprt s - astar) 0‖ := by rw [e0, Real.norm_eq_abs, abs_of_nonneg hs]
      _ ≤ ‖aprt s - astar‖ := norm_le_pi_norm _ 0

theorem norm_aprt' (s : ℝ) (hs : 0 ≤ s) : ‖astar - aprt s‖ = s := by
  have e0 : (astar - aprt s) 0 = -s := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_zero]; ring
  have e1 : (astar - aprt s) 1 = 0 := by
    simp only [Pi.sub_apply, aprt, astar, Matrix.cons_val_one]; ring
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hs, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs, e0, abs_neg, abs_of_nonneg hs]
    · rw [Real.norm_eq_abs, e1, abs_zero]; exact hs
  · calc s = ‖(astar - aprt s) 0‖ := by rw [e0, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
      _ ≤ ‖astar - aprt s‖ := norm_le_pi_norm _ 0

/-- **Transport a defect inequality from `α*` to the perturbed witness.** -/
theorem transport (s : ℝ) (hs0 : 0 ≤ s) (m n : ℤ) (Mm Mn : ℝ)
    (hm : delta astar m = Mm / 47) (hn : delta astar n = Mn / 47)
    (hgap : 47 * ((|(m : ℝ)| + |(n : ℝ)|) * s) < Mn - Mm) :
    delta (aprt s) m < delta (aprt s) n := by
  have hd1 := delta_sub_le (aprt s) astar m
  have hd2 := delta_sub_le astar (aprt s) n
  rw [norm_aprt s hs0, hm] at hd1
  rw [norm_aprt' s hs0, hn] at hd2
  have hexp : 47 * ((|(m : ℝ)| + |(n : ℝ)|) * s)
      = 47 * (|(m : ℝ)| * s) + 47 * (|(n : ℝ)| * s) := by ring
  rw [hexp] at hgap
  obtain ⟨U, hU⟩ : ∃ U, |(m : ℝ)| * s = U := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, |(n : ℝ)| * s = V := ⟨_, rfl⟩
  rw [hU] at hd1 hgap
  rw [hV] at hd2 hgap
  linarith [hd1, hd2, hgap]

/-- Bundles `transport` for an integer record gap: once `s` is small (`1222·s < 1`), an integer
defect drop `Mm + 1 ≤ Mn` transports from `α*` to `aprt s`. -/
theorem Hpair (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1222 * s < 1) (m n Mm Mn : ℤ)
    (hm : delta astar m = (Mm : ℝ) / 47) (hn : delta astar n = (Mn : ℝ) / 47)
    (hc : |(m : ℝ)| + |(n : ℝ)| ≤ 26) (hgapZ : Mm + 1 ≤ Mn) :
    delta (aprt s) m < delta (aprt s) n := by
  refine transport s hs0 m n (Mm : ℝ) (Mn : ℝ) hm hn ?_
  have h1 : (|(m : ℝ)| + |(n : ℝ)|) * s ≤ 26 * s := mul_le_mul_of_nonneg_right hc hs0
  have h2 : (Mm : ℝ) + 1 ≤ (Mn : ℝ) := by exact_mod_cast hgapZ
  linarith [h1, h2, hsmall]

theorem H1_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1222 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 7, delta (aprt s) 9 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 9 1 11 15 dstar9 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 2 11 17 dstar9 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 3 11 12 dstar9 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 4 11 16 dstar9 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 5 11 20 dstar9 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 6 11 23 dstar9 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 9 7 11 19 dstar9 dstar7 (by norm_num) (by norm_num)

theorem H2_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1222 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 9, delta (aprt s) 10 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 10 1 9 15 dstar10 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 2 9 17 dstar10 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 3 9 12 dstar10 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 4 9 16 dstar10 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 5 9 20 dstar10 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 6 9 23 dstar10 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 7 9 19 dstar10 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 8 9 21 dstar10 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 10 9 9 11 dstar10 dstar9 (by norm_num) (by norm_num)

theorem H3_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1222 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 10, delta (aprt s) 12 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 12 1 8 15 dstar12 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 2 8 17 dstar12 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 3 8 12 dstar12 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 4 8 16 dstar12 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 5 8 20 dstar12 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 6 8 23 dstar12 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 7 8 19 dstar12 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 8 8 21 dstar12 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 9 8 11 dstar12 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 12 10 8 9 dstar12 dstar10 (by norm_num) (by norm_num)

theorem H4_aprt (s : ℝ) (hs0 : 0 ≤ s) (hsmall : 1222 * s < 1) :
    ∀ n ∈ Finset.Icc (1 : ℕ) 12, delta (aprt s) 13 < delta (aprt s) (n : ℤ) := by
  intro n hn; obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · exact Hpair s hs0 hsmall 13 1 7 15 dstar13 dstar1 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 2 7 17 dstar13 dstar2 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 3 7 12 dstar13 dstar3 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 4 7 16 dstar13 dstar4 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 5 7 20 dstar13 dstar5 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 6 7 23 dstar13 dstar6 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 7 7 19 dstar13 dstar7 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 8 7 21 dstar13 dstar8 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 9 7 11 dstar13 dstar9 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 10 7 9 dstar13 dstar10 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 11 7 23 dstar13 dstar11 (by norm_num) (by norm_num)
  · exact Hpair s hs0 hsmall 13 12 7 8 dstar13 dstar12 (by norm_num) (by norm_num)

/-- **Arithmetic sharpness of the `L∞` five-distance theorem `g_∞ ≤ 5` on `𝕋²`.** There is a
Kronecker vector `α` with an irrational coordinate and an `N ≥ 2` for which the orbit `{0, α, …,
Nα}`
on `𝕋²` realizes **exactly five** distinct sup-norm nearest-neighbour distances — so the bound
`nnDist_count_plane_unconditional` is sharp. The witness is `α = (4/47 + s, 15/47)` for a small
irrational `s`: `card ≥ 5` transports from the rational `α*` (Lipschitz), `card ≤ 5` is the
five-distance theorem itself. Entirely elementary — no homogeneous dynamics. -/
theorem sharp_attained : ∃ α : Fin 2 → ℝ, (∃ k, Irrational (α k)) ∧
    ∃ N, 2 ≤ N ∧ ((Finset.range (N + 1)).image (nnDist α N)).card = 5 := by
  obtain ⟨s, hs_irr, hs_pos, hs_lt⟩ :=
    exists_irrational_btwn (show (0 : ℝ) < 1 / 1222 by norm_num)
  have hsmall : 1222 * s < 1 := by
    rw [lt_div_iff₀ (by norm_num)] at hs_lt; linarith [hs_lt]
  refine ⟨aprt s, ⟨0, aprt_irrational hs_irr⟩, 13, by norm_num, le_antisymm ?_ ?_⟩
  · exact nnDist_count_plane_unconditional (aprt s) (k₀ := 0) (aprt_irrational hs_irr) (by norm_num)
  · exact card_ge_five (aprt s) (H1_aprt s hs_pos.le hsmall) (H2_aprt s hs_pos.le hsmall)
      (H3_aprt s hs_pos.le hsmall) (H4_aprt s hs_pos.le hsmall)

end ThreeGap.LinftyRecords
