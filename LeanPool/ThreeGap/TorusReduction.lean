/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.DeltaCost

/-!
# The isometry reduction: `gapVal` *is* the torus nearest-neighbour distance

Chevallier's count (`ChevallierCount`) and the unconditional sup-norm growth (`DeltaCost`) bound the
number of distinct values of the abstract quantity `gapVal (delta α) N q`. This file identifies that
quantity with the **actual geometric nearest-neighbour distance** in the torus `𝕋ᵈ = ℝᵈ/ℤᵈ`, closing
the gap between the combinatorial bound and the genuine higher-dimensional three-distance statement.

The torus distance between two orbit points `iα` and `jα` is, by translation invariance,

  `d_𝕋(iα, jα) = inf_{p ∈ ℤᵈ} ‖(i−j)•α − p‖_∞ = delta α (i − j)`,

so the nearest-neighbour distance of the `q`-th point among `{0, α, …, Nα}` is
`min_{0 ≤ j ≤ N, j ≠ q} delta α (q − j)`. Using the **symmetry** `delta α (−t) = delta α t` and the
offset bookkeeping (`|q − j|` ranges over `[1, max(q, N−q)]`), this equals exactly
`min_{1 ≤ t ≤ max(q, N−q)} delta α t = gapVal (delta α) N q`.

Hence `gapVal = nnDist`, and the bound `gap_count_supNorm_le` becomes a bound on the number of
distinct **actual** nearest-neighbour distances: `g_∞ ≤ 2^d + 1`.

Axiom-clean; elementary.
-/

namespace ThreeGap.DeltaCost

open ThreeGap.SimApprox ThreeGap.Chevallier

variable {d : ℕ}

/-! ## Symmetry of the defect -/

/-- Negating both the denominator and the integer translate negates the remainder vector. -/
theorem rem_neg_neg (α : Fin d → ℝ) (q : ℤ) (p : Fin d → ℤ) :
    rem α (-q) (-p) = - rem α q p := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  push_cast; ring

/-- One inequality of the symmetry `delta α (−q) ≤ delta α q`. -/
theorem delta_neg_le (α : Fin d → ℝ) (q : ℤ) : delta α (-q) ≤ delta α q := by
  unfold delta
  refine le_ciInf (fun p => ?_)
  have h := delta_le α (-q) (-p)
  rwa [rem_neg_neg, norm_neg] at h

/-- **The defect is symmetric:** `delta α (−q) = delta α q`. (The torus distance to the origin is
unchanged by reflection.) -/
theorem delta_neg_eq (α : Fin d → ℝ) (q : ℤ) : delta α (-q) = delta α q :=
  le_antisymm (delta_neg_le α q) (by have := delta_neg_le α (-q); rwa [neg_neg] at this)

/-! ## The torus nearest-neighbour distance -/

/-- **The nearest-neighbour distance** of the `q`-th orbit point `qα` among `{0, α, …, Nα}`, using
the torus distance `d_𝕋(qα, jα) = delta α (q − j)`: the minimum over the other `N` points. -/
noncomputable def nnDist (α : Fin d → ℝ) (N q : ℕ) : ℝ :=
  if h : ((Finset.range (N + 1)).erase q).Nonempty then
    ((Finset.range (N + 1)).erase q).inf' h (fun j => delta α ((q : ℤ) - (j : ℤ))) else 0

/-- **The isometry reduction.** For `q ≤ N` (`N ≥ 2`), the abstract gap value of the defect cost
equals the genuine torus nearest-neighbour distance:

  `gapVal (delta α) N q = nnDist α N q`.

Proof: each side is an infimum; the offset map `j ↦ |q − j|` is a value-preserving correspondence
between `{0,…,N}\{q}` and `[1, max(q, N−q)]` (using `delta α (−t) = delta α t`), so the two infima
agree. -/
theorem gapVal_eq_nnDist (α : Fin d → ℝ) {N : ℕ} (hN : 2 ≤ N) {q : ℕ} (hq : q ≤ N) :
    gapVal (deltaCost α) N q = nnDist α N q := by
  have hIcc : (Finset.Icc 1 (max q (N - q))).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, ?_⟩⟩
    rcases Nat.eq_zero_or_pos q with h | h
    · exact le_trans (by omega : 1 ≤ N - q) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  have hEr : ((Finset.range (N + 1)).erase q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
      Finset.card_range]
    omega
  rw [gapVal, dif_pos hIcc, nnDist, dif_pos hEr]
  apply le_antisymm
  · -- `inf'_Icc (deltaCost) ≤ inf'_erase (delta (q−j))`
    refine Finset.le_inf' _ _ (fun j hj => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hj
    obtain ⟨hjne, hjN⟩ := hj
    rcases lt_or_ge j q with hjq | hjq
    · -- `j < q`: matching offset `t = q − j`
      have htmem : q - j ∈ Finset.Icc 1 (max q (N - q)) :=
        Finset.mem_Icc.mpr ⟨by omega, le_trans (by omega : q - j ≤ q) (le_max_left _ _)⟩
      have hval : deltaCost α (q - j) = delta α ((q : ℤ) - (j : ℤ)) := by
        rw [deltaCost]; congr 1; rw [Nat.cast_sub (by omega : j ≤ q)]
      calc (Finset.Icc 1 (max q (N - q))).inf' hIcc (deltaCost α)
          ≤ deltaCost α (q - j) := Finset.inf'_le _ htmem
        _ = delta α ((q : ℤ) - (j : ℤ)) := hval
    · -- `j ≥ q` (and `j ≠ q`, so `j > q`): matching offset `t = j − q`
      have hjq' : q < j := lt_of_le_of_ne hjq (by omega)
      have htmem : j - q ∈ Finset.Icc 1 (max q (N - q)) :=
        Finset.mem_Icc.mpr ⟨by omega, le_trans (by omega : j - q ≤ N - q) (le_max_right _ _)⟩
      have hval : deltaCost α (j - q) = delta α ((q : ℤ) - (j : ℤ)) := by
        rw [deltaCost]
        rw [Nat.cast_sub (by omega : q ≤ j), show (j : ℤ) - (q : ℤ) = -((q : ℤ) - (j : ℤ)) by ring,
          delta_neg_eq]
      calc (Finset.Icc 1 (max q (N - q))).inf' hIcc (deltaCost α)
          ≤ deltaCost α (j - q) := Finset.inf'_le _ htmem
        _ = delta α ((q : ℤ) - (j : ℤ)) := hval
  · -- `inf'_erase (delta (q−j)) ≤ inf'_Icc (deltaCost)`
    refine Finset.le_inf' _ _ (fun t ht => ?_)
    rw [Finset.mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rcases le_or_gt t q with hcase | hcase
    · -- `t ≤ q`: matching point `j = q − t`
      have hjmem : q - t ∈ (Finset.range (N + 1)).erase q :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      have hval : delta α ((q : ℤ) - ((q - t : ℕ) : ℤ)) = deltaCost α t := by
        rw [deltaCost, Nat.cast_sub hcase]; congr 1; ring
      calc ((Finset.range (N + 1)).erase q).inf' hEr (fun j => delta α ((q : ℤ) - (j : ℤ)))
          ≤ delta α ((q : ℤ) - ((q - t : ℕ) : ℤ)) := Finset.inf'_le _ hjmem
        _ = deltaCost α t := hval
    · -- `t > q`: then `max(q, N−q) = N−q`, so `t ≤ N − q`; matching point `j = q + t`
      have htNq : t ≤ N - q := by
        rcases le_total q (N - q) with hle | hle
        · rwa [max_eq_right hle] at ht2
        · rw [max_eq_left hle] at ht2; omega
      have hjmem : q + t ∈ (Finset.range (N + 1)).erase q :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      have hval : delta α ((q : ℤ) - ((q + t : ℕ) : ℤ)) = deltaCost α t := by
        rw [deltaCost, Nat.cast_add,
          show (q : ℤ) - ((q : ℤ) + (t : ℤ)) = -(t : ℤ) by ring, delta_neg_eq]
      calc ((Finset.range (N + 1)).erase q).inf' hEr (fun j => delta α ((q : ℤ) - (j : ℤ)))
          ≤ delta α ((q : ℤ) - ((q + t : ℕ) : ℤ)) := Finset.inf'_le _ hjmem
        _ = deltaCost α t := hval

/-- **`g_∞ ≤ 2^d + 1` for the actual torus nearest-neighbour distances (combinatorial three-distance
bound in `L^∞`).** For every `N ≥ 2`, the number of distinct nearest-neighbour distances
`{nnDist α N q : 0 ≤ q ≤ N}` of the orbit `{0, α, …, Nα}` on the torus `𝕋ᵈ` is at most `2^d + 1`.
The only hypothesis is `RecordsContinue` (the best approximations of `α` improve without bound — the
appropriate irrationality). The growth geometry is fully discharged (orthant pigeonhole), and the
geometric identification `gapVal = nnDist` is now proven. -/
theorem nnDist_count_le (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α)) {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.range (N + 1)).image (nnDist α N)).card ≤ 2 ^ d + 1 := by
  have hcongr : (Finset.range (N + 1)).image (nnDist α N)
      = (Finset.range (N + 1)).image (gapVal (deltaCost α) N) := by
    refine Finset.image_congr (fun q hq => ?_)
    rw [Finset.mem_coe, Finset.mem_range] at hq
    exact (gapVal_eq_nnDist α hN (by omega)).symm
  rw [hcongr]
  exact gap_count_supNorm_le α hr hN

/-- **The `L^∞` five-distance theorem on `𝕋²`** (the `d = 2` instance of `nnDist_count_le`). For
every `N ≥ 2`, the orbit `{0, α, …, Nα}` on the two-dimensional torus has at most **five** distinct
nearest-neighbour distances in the sup-norm metric. This is the sharp `g_∞ ≤ 5` bound for `d = 2`
(`2² + 1 = 5`), fully discharged modulo `RecordsContinue` (irrationality): the growth geometry is
the
orthant pigeonhole and the geometric identification `gapVal = nnDist` is proven.

NB: this is the **sup-norm** (`L^∞`) five-distance theorem. The *Euclidean* five-distance bound
`g₂ ≤ 5` (Haynes–Marklof) is a distinct statement requiring Romanov's sharper growth constant
`K = 4`; the contact-number route gives only the Euclidean `g₂ ≤ 7`. -/
theorem nnDist_count_le_plane (α : Fin 2 → ℝ) (hr : RecordsContinue (deltaCost α)) {N : ℕ}
    (hN : 2 ≤ N) : ((Finset.range (N + 1)).image (nnDist α N)).card ≤ 5 := by
  have h := nnDist_count_le (d := 2) α hr hN
  norm_num at h
  exact h

end ThreeGap.DeltaCost
