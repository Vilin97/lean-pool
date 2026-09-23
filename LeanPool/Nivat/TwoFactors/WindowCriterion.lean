/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.TwoFactors.BoundaryPeriod
public import LeanPool.Nivat.TwoFactors.StripStates

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# From a normalized window to a directional period

The positive-height case in the proof of Theorem 5.1 (`thm:twofactor`) of
`paper/nivat.tex`. Lemma 5.6 supplies either a transverse period or an agreeing
strip with a boundary disagreement. Lemma 5.7 gives periodic interior rows in
the latter case, and Lemma 5.8 extends a multiple of the horizontal direction
to a global period. The conclusion retains which input direction supplies it.
-/

@[expose] public section

namespace Nivat.TwoFactors

/-- Theorem 5.1 (`thm:twofactor`), after the window of Lemma 5.5 has been
normalized: a nonzero integer multiple of one of the two directions is a
period. Lemmas 5.6–5.8 preserve which direction supplies the period. -/
theorem directional_period_of_short_window (c : Configuration ℚ) (hc : FiniteRange c)
    (C : Finset Lattice) (e H : ℕ) (hH : 0 < H)
    (hC : ∀ z ∈ C, 1 ≤ z.2 ∧ z.2 ≤ H)
    (hblocks : ∀ j : Fin H, ∃ α : ℤ, ∀ s : ℕ, s < e - 1 →
      (α + s, ((j : ℕ) : ℤ) + 1) ∈ C)
    (hcost : complexity c (prefixWindow C e) < complexity c C + e)
    (q : ℕ) (hq : 0 < q) (a M : ℤ) (hM : 0 < M)
    (hmix : difference ((q : ℤ), 0) (difference (a, M) c) = 0) :
    ∃ k : ℤ, k ≠ 0 ∧
      (IsPeriod c (k • ((q : ℤ), 0)) ∨ IsPeriod c (k • (a, M))) := by
  obtain ⟨k, hke, hrule⟩ := boundaryRule_of_small_cost c hc C e hcost
  let W := max H M.toNat
  have hHW : (H : ℤ) ≤ W := by exact_mod_cast (le_max_left H M.toNat)
  have hMW : M ≤ W := by
    have h := le_max_right H M.toNat
    have hcast : (M.toNat : ℤ) = M := Int.toNat_of_nonneg (le_of_lt hM)
    have hh : (M.toNat : ℤ) ≤ W := by exact_mod_cast (show M.toNat ≤ W from h)
    rwa [hcast] at hh
  rcases finite_strip_dichotomy c hc q W hq a M hM hMW hmix with hperiod | hamb
  · obtain ⟨p, hp, hpc⟩ := hperiod
    exact ⟨p, by omega, Or.inr (by simpa only [natCast_zsmul] using hpc)⟩
  · obtain ⟨u, v, hagree, hne, hper, _⟩ := hamb
    have hinner : ∀ i : ℤ, patternAt (shift u c) C (i, 0) =
        patternAt (shift v c) C (i, 0) := by
      intro i
      funext z
      exact hagree (z.1 + (i, 0)) (by simpa using (hC z.1 z.2).1)
        (by simpa using (hC z.1 z.2).2.trans hHW)
    have hedge := every_edge_differs c C k e q hke hq hrule u v hinner hper hne
    have hbudget := innerOrbit_budget c hc C e u v hinner hedge
    let r := (innerOrbit (shift u c) C).ncard
    have hr : 0 < r := (Set.ncard_pos (innerOrbit_finite (hc.shift u) C)).2
      ⟨_, 0, rfl⟩
    have hre : r ≤ e - 1 := by dsimp [r]; omega
    choose α hα using hblocks
    have hblocks' : ∀ j : Fin H, ∀ s : Fin r,
        (α j + (s : ℕ), ((j : ℕ) : ℤ) + 1) ∈ C := by
      intro j s
      exact hα j s (lt_of_lt_of_le s.isLt hre)
    obtain ⟨p, hp, _, hrows⟩ := common_inner_period (shift u c) (hc.shift u) C H r hr
      α hblocks' le_rfl
    have hrows' : ∀ j : ℤ, 1 ≤ j → j ≤ H → RowPeriodic (shift u c) j := by
      intro j hj hjH
      let jj : Fin H := ⟨(j - 1).toNat, by omega⟩
      have heq : ((jj : ℕ) : ℤ) + 1 = j := by
        dsimp [jj]
        omega
      exact ⟨p, hp, by simpa only [heq] using hrows jj⟩
    have hmix' : difference ((q : ℤ), 0) (difference (a, M) (shift u c)) = 0 := by
      funext z
      have hz := congrFun hmix (z + u)
      simpa [difference_apply, shift, add_assoc, add_comm, add_left_comm] using hz
    obtain ⟨L, hL, hLc⟩ := periodic_of_rows_boundaryRule (shift u c) (hc.shift u)
      C k H hH hC (boundaryRule_shift c C k hrule u) q hq a M hM hmix' hrows'
    refine ⟨L, by omega, Or.inl ?_⟩
    simpa [Prod.smul_mk, zsmul_eq_mul, Nat.cast_mul] using
      (isPeriod_shift_iff c _ u).mp hLc

end Nivat.TwoFactors
