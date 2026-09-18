/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Lattice
import LeanPool.Nivat.Core.BoundedDifferences
import LeanPool.Nivat.TwoFactors.WindowNormalization
import LeanPool.Nivat.TwoFactors.WindowCriterion

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
# Two difference operators

Theorem 5.1 (`thm:twofactor`) of `paper/nivat.tex`. A primitive lattice basis
puts the first direction on the horizontal axis. Lemma 5.5 selects and
normalizes a low-cost boundary in the preimage of the original rectangle.
The positive-height argument uses Lemmas 5.6–5.8; a one-row window uses the
factorial common period from Corollary 5.3. Directional periods are transported
back through both coordinate changes. The parallel case uses bounded finite
differences. The final corollary treats sums of two periodic configurations.
-/

namespace Nivat.TwoFactors

/-- The word complexity of any row is bounded by the configuration's horizontal-edge complexity,
which counts translations on all rows. Theorem 5.1 (`thm:twofactor`), one-row case using
Corollary 5.3 (`cor:morse`). -/
theorem wordComplexity_row_le {A : Type*} (c : Configuration A) (hc : FiniteRange c)
    (e : ℕ) (j : ℤ) :
    wordComplexity (fun i : ℤ => c (i, j)) e ≤ complexity c (rowPrefix e) := by
  let extract : (rowPrefix e → A) → (Fin e → A) := fun p r =>
    p ⟨((r : ℕ), 0), (mem_rowPrefix _ e).mpr ⟨r, r.isLt, rfl⟩⟩
  have hsubset : Set.range (word (fun i : ℤ => c (i, j)) e) ⊆
      extract '' patterns c (rowPrefix e) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨patternAt c (rowPrefix e) (i, j), ⟨(i, j), rfl⟩, ?_⟩
    funext r
    simp [extract, patternAt, word, add_comm]
  exact (Set.ncard_le_ncard hsubset ((patterns_finite hc _).image extract)).trans
    (Set.ncard_image_le (patterns_finite hc _))

/-- In the one-row case of Theorem 5.1 (`thm:twofactor`), Corollary 5.3
bounds every row period by the edge length, so its factorial is a period of
all rows simultaneously. -/
theorem isPeriod_factorial_of_lowcomplex_rowPrefix {A : Type*} (c : Configuration A)
    (hc : FiniteRange c) (e : ℕ) (he : 0 < e)
    (hlow : complexity c (rowPrefix e) ≤ e) :
    IsPeriod c ((e.factorial : ℤ), 0) := by
  rintro ⟨i, j⟩
  have hrowfin : (Set.range (fun i : ℤ => c (i, j))).Finite := hc.subset (by
    rintro _ ⟨l, rfl⟩
    exact ⟨(l, j), rfl⟩)
  obtain ⟨p, hp, hpe, hper⟩ := morse_hedlund (fun i : ℤ => c (i, j)) hrowfin e he
    ((wordComplexity_row_le c hc e j).trans hlow)
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hp hpe
  have h := hper.nat_mul k i
  simpa only [Prod.mk_add_mk, add_zero, hk, Nat.cast_mul, mul_comm] using h

/-- Reversing the transverse direction preserves the mixed-difference identity, by commutation
and negation of a period. Theorem 5.1 (`thm:twofactor`). -/
theorem mixed_difference_neg_right {A : Type*} [AddCommGroup A]
    (c : Configuration A) (h t : Lattice) (hmix : difference h (difference t c) = 0) :
    difference h (difference (-t) c) = 0 := by
  rw [difference_comm]
  apply (difference_eq_zero_iff (-t) _).mpr
  apply IsPeriod.neg
  apply (difference_eq_zero_iff t _).mp
  rwa [difference_comm]

/-- Theorem 5.1 for a normalized window, allowing either sign of the
transverse displacement and the one-row case. A nonzero integer period
multiple is retained when the transverse direction is reversed. -/
private theorem directional_period_of_short_window_transverse
    (c : Configuration ℚ) (hc : FiniteRange c)
    (C : Finset Lattice) (e H : ℕ) (he : 0 < e)
    (hC : ∀ z ∈ C, 1 ≤ z.2 ∧ z.2 ≤ H)
    (hblocks : ∀ j : Fin H, ∃ α : ℤ, ∀ s : ℕ, s < e - 1 →
      (α + s, ((j : ℕ) : ℤ) + 1) ∈ C)
    (hcost : complexity c (prefixWindow C e) < complexity c C + e)
    (q : ℕ) (hq : 0 < q) (a M : ℤ) (hM : M ≠ 0)
    (hmix : difference ((q : ℤ), 0) (difference (a, M) c) = 0) :
    ∃ k : ℤ, k ≠ 0 ∧
      (IsPeriod c (k • ((q : ℤ), 0)) ∨ IsPeriod c (k • (a, M))) := by
  by_cases hH : H = 0
  · have hCe : C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have := hC z hz
      omega
    have hlow : complexity c (rowPrefix e) ≤ e := by
      simpa only [hCe, prefixWindow, Finset.empty_union, complexity_empty,
        Nat.lt_add_one_iff, add_comm 1] using hcost
    refine ⟨e.factorial, by exact_mod_cast (Nat.factorial_pos e).ne', Or.inl ?_⟩
    simpa [Prod.smul_mk, nsmul_eq_mul, zsmul_eq_mul, mul_comm] using
      (isPeriod_factorial_of_lowcomplex_rowPrefix c hc e he hlow).nsmul q
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    rcases lt_or_gt_of_ne hM with hneg | hpos
    · have hmix' : difference ((q : ℤ), 0) (difference (-a, -M) c) = 0 := by
        simpa only [Prod.neg_mk] using mixed_difference_neg_right c ((q : ℤ), 0) (a, M) hmix
      obtain ⟨k, hk, hp⟩ := directional_period_of_short_window c hc C e H hHpos
        hC hblocks hcost q hq (-a) (-M) (by omega) hmix'
      rcases hp with hp | hp
      · exact ⟨k, hk, Or.inl hp⟩
      · refine ⟨-k, neg_ne_zero.mpr hk, Or.inr ?_⟩
        simpa only [← Prod.neg_mk, smul_neg, neg_smul] using hp
    · exact directional_period_of_short_window c hc C e H hHpos hC hblocks hcost q hq a M hpos hmix

/-- The normalized-window argument yields a nonzero integer period multiple of the horizontal or
transverse input direction for any low-complexity lattice-convex window. Affine transport
preserves the original window's own pattern count. Theorem 5.1 (`thm:twofactor`). -/
private theorem directional_period_of_latticeConvex_mixed_difference (c : Configuration ℚ)
    (hc : FiniteRange c) (D : Finset Lattice) (hconv : LatticeConvex D)
    (hlow : complexity c D ≤ D.card) (q : ℕ) (hq : 0 < q) (v : Lattice)
    (hv : v.2 ≠ 0) (hmix : difference ((q : ℤ), 0) (difference v c) = 0) :
    ∃ k : ℤ, k ≠ 0 ∧
      (IsPeriod c (k • ((q : ℤ), 0)) ∨ IsPeriod c (k • v)) := by
  obtain ⟨w⟩ := exists_shapeWindow c hc D hconv hlow
  obtain ⟨N⟩ := w.normalize
  have hv' : (N.t.symm v).2 ≠ 0 :=
    transverse_coordinate_ne_zero N.t q (N.horizontal q) (by
      change (q : ℤ) * v.2 ≠ 0 * v.1
      simpa only [zero_mul] using mul_ne_zero (show (q : ℤ) ≠ 0 by omega) hv)
  have hmix' : difference ((q : ℤ), 0) (difference (N.t.symm v) (c ∘ N.s)) = 0 := by
    rw [difference_affine_reindex c N.s N.t N.affine, N.t.apply_symm_apply,
      difference_affine_reindex (difference v c) N.s N.t N.affine, N.horizontal, hmix]
    rfl
  obtain ⟨k, hk, hper⟩ := directional_period_of_short_window_transverse (c ∘ N.s) (hc.precomp N.s)
    N.C N.e N.H N.positive N.interior N.blocks N.cost q hq
    (N.t.symm v).1 (N.t.symm v).2 hv' hmix'
  refine ⟨k, hk, ?_⟩
  rcases hper with hper | hper
  · left
    simpa only [map_zsmul, N.horizontal] using
      (isPeriod_affine_reindex_iff c N.s N.t N.affine _).mp hper
  · right
    simpa only [map_zsmul, N.t.apply_symm_apply] using
      (isPeriod_affine_reindex_iff c N.s N.t N.affine _).mp hper

/-- A nonzero multiple of a nonzero lattice vector is itself nonzero; thus a
period in either input direction gives the periodicity conclusion of
Theorem 5.1 (`thm:twofactor`). -/
private theorem periodic_of_directional_period {A : Type*} (c : Configuration A)
    (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (hp : ∃ k : ℤ, k ≠ 0 ∧ (IsPeriod c (k • h) ∨ IsPeriod c (k • t))) :
    Periodic c := by
  obtain ⟨k, hk, hp⟩ := hp
  rcases hp with hp | hp
  · exact ⟨k • h, smul_ne_zero hk hh, hp⟩
  · exact ⟨k • t, smul_ne_zero hk ht, hp⟩

end Nivat.TwoFactors

namespace Nivat

/-- The directional conclusion of Theorem 5.1 (`thm:twofactor`): for
nonparallel directions, a nonzero integer multiple of one of them is a period.
The complexity bound is on the original axis-aligned rectangle. -/
theorem two_factors_nonparallel (c : Configuration ℚ) (hc : FiniteRange c) (m n : ℕ)
    (_hm : 0 < m) (_hn : 0 < n) (h t : Lattice) (hh : h ≠ 0) (_ht : t ≠ 0)
    (hcomplexity : complexity c (rectangle m n) ≤ m * n)
    (hmix : difference h (difference t c) = 0)
    (hparallel : h.1 * t.2 ≠ h.2 * t.1) :
    ∃ k : ℤ, k ≠ 0 ∧ (IsPeriod c (k • h) ∨ IsPeriod c (k • t)) := by
  -- Express the original rectangle in a primitive basis for the first direction.
  obtain ⟨q, hq, e, he⟩ := exists_lattice_basis_for_nonzero h hh
  let D := (rectangle m n).map e.symm.toEquiv.toEmbedding
  have hD : ∀ z : Lattice, z ∈ D ↔ e z ∈ rectangle m n := by
    intro z
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
      have heu : e z = u := by rw [← huz]; exact e.apply_symm_apply u
      simpa only [heu] using hu
    · intro hz
      exact Finset.mem_map.mpr ⟨e z, hz, e.symm_apply_apply z⟩
  have hconv : TwoFactors.LatticeConvex D :=
    (TwoFactors.latticeConvex_rectangle m n).linear_preimage e (latticeEquivRatLinear e)
      (latticeEquivRatLinear_compatible e) hD
  -- Transport the actual pattern count and mixed difference through that basis.
  have hmap : D.map e.toEquiv.toEmbedding = rectangle m n := by simp [D, Finset.map_map]
  have hlow : complexity (c ∘ e) D ≤ D.card := by
    change complexity (c ∘ e.toEquiv) D ≤ D.card
    rw [complexity_affine_reindex c e.toEquiv e (map_add e), hmap]
    simpa only [D, Finset.card_map, card_rectangle] using hcomplexity
  have hv : (e.symm t).2 ≠ 0 := transverse_coordinate_ne_zero e q he hparallel
  have hmix' : difference ((q : ℤ), 0) (difference (e.symm t) (c ∘ e)) = 0 := by
    change difference ((q : ℤ), 0) (difference (e.symm t) (c ∘ e.toEquiv)) = 0
    rw [difference_affine_reindex c e.toEquiv e (map_add e), e.apply_symm_apply,
      difference_affine_reindex (difference t c) e.toEquiv e (map_add e), he, hmix]
    rfl
  -- Keep the integer multiple while returning to the original coordinates.
  obtain ⟨k, hk, hp⟩ := TwoFactors.directional_period_of_latticeConvex_mixed_difference
    (c ∘ e) (hc.precomp e) D hconv hlow q hq (e.symm t) hv hmix'
  refine ⟨k, hk, ?_⟩
  rcases hp with hp | hp
  · left
    simpa only [map_zsmul, he] using
      (isPeriod_affine_reindex_iff c e.toEquiv e (map_add e) _).mp hp
  · right
    simpa only [map_zsmul, e.apply_symm_apply] using
      (isPeriod_affine_reindex_iff c e.toEquiv e (map_add e) _).mp hp

/-- Theorem 5.1 (`thm:twofactor`). A finite-range rational configuration with
at most `m * n` patterns on the original positive axis-aligned rectangle and
annihilated by the product of two nonzero directional differences has a
nonzero global period. -/
theorem two_factors (c : Configuration ℚ) (hc : FiniteRange c) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (hcomplexity : complexity c (rectangle m n) ≤ m * n)
    (hmix : difference h (difference t c) = 0) : Periodic c := by
  by_cases hparallel : h.1 * t.2 = h.2 * t.1
  · exact periodic_of_parallel_mixed_difference c hc h t hh ht hparallel hmix
  · exact TwoFactors.periodic_of_directional_period c h t hh ht
      (two_factors_nonparallel c hc m n hm hn h t hh ht hcomplexity hmix hparallel)

/-- Difference operators distribute over sums, the algebraic observation after
Theorem 5.1 (`thm:twofactor`) that gives the two-periodic-summand corollary. -/
theorem difference_add {A : Type*} [AddCommGroup A] (h : Lattice)
    (a b : Configuration A) : difference h (a + b) = difference h a + difference h b := by
  funext z
  simp only [difference_apply, Pi.add_apply]
  abel

/-- The consequence of Theorem 5.1 stated in the opening discussion of
Section 5 (`sec:twofactor`): a low-complexity finite-range sum of two periodic
rational configurations is periodic. The individual summands need not have
finite range. -/
theorem two_periodic_summands (c a b : Configuration ℚ) (hc : FiniteRange c)
    (hsum : c = a + b) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (ha : IsPeriod a h) (hb : IsPeriod b t)
    (hlow : complexity c (rectangle m n) ≤ m * n) : Periodic c := by
  apply two_factors c hc m n hm hn h t hh ht hlow
  have haz := (difference_eq_zero_iff h a).mpr ha
  have hbz := (difference_eq_zero_iff t b).mpr hb
  rw [hsum, difference_add, difference_add, difference_comm h t a, haz, hbz]
  funext z
  simp [difference_apply]

end Nivat
