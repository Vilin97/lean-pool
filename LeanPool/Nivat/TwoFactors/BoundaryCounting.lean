/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Patterns
public import LeanPool.Nivat.TwoFactors.PeriodicRows

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
# Boundary cost and unique extension

The counting part of Lemma 5.5 (`lem:boundary-window`) and the fiber count in
Lemma 5.7 (`lem:periodic-interior`) of `paper/nivat.tex`. Restriction is a
surjection on occurring patterns. A small total increase forces a zero increase
at one boundary site, and the total excess of fiber sizes bounds the number of
interior patterns with more than one boundary extension.
-/

public section

namespace Nivat.TwoFactors

/-- The first `k` consecutive sites of the horizontal boundary row. Lemma 5.5
(`lem:boundary-window`), equation `eq:boundary-rule-domain`. -/
def rowPrefix (k : ℕ) : Finset Lattice :=
  (Finset.range k).image (fun i : ℕ => ((i : ℤ), (0 : ℤ)))

/-- Membership in the horizontal boundary prefix means being its `r`th site for some natural
index `r < k`. Lemma 5.5 (`lem:boundary-window`). -/
@[simp] theorem mem_rowPrefix (z : Lattice) (k : ℕ) :
    z ∈ rowPrefix k ↔ ∃ i < k, z = ((i : ℤ), 0) := by
  simp [rowPrefix, eq_comm]

/-- A boundary prefix of length zero is empty, so a zero-memory rule uses only the interior.
Lemma 5.5 (`lem:boundary-window`). -/
@[simp] theorem rowPrefix_zero : rowPrefix 0 = ∅ := by simp [rowPrefix]

/-- Increasing the prefix length retains all previously adjoined boundary sites. Lemma 5.5
(`lem:boundary-window`). -/
theorem rowPrefix_mono : Monotone rowPrefix := by
  intro i j hij
  exact Finset.image_subset_image (Finset.range_mono hij)

/-- The interior together with the first `k` boundary sites, the finite window denoted `D_k` in
the paper. Lemma 5.5 (`lem:boundary-window`), equation `eq:boundary-rule-domain`. -/
@[expose] def prefixWindow (C : Finset Lattice) (k : ℕ) : Finset Lattice := C ∪ rowPrefix k

/-- Before any boundary sites are adjoined, the prefix window is exactly the interior. Lemma 5.5
(`lem:boundary-window`). -/
@[simp] theorem prefixWindow_zero (C : Finset Lattice) : prefixWindow C 0 = C := by
  simp [prefixWindow]

/-- The successive interior-plus-prefix windows are nested, hence their pattern complexities are
nondecreasing. Lemma 5.5 (`lem:boundary-window`). -/
theorem prefixWindow_mono (C : Finset Lattice) : Monotone (prefixWindow C) := by
  intro i j hij
  exact Finset.union_subset_union (by rfl) (rowPrefix_mono hij)

/-- A nondecreasing integer sequence whose total increase over `e` steps is less than `e` has an
adjacent equality. Lemma 5.5 (`lem:boundary-window`). -/
theorem exists_plateau_of_small_increase (p : ℕ → ℕ) (hp : Monotone p)
    (e : ℕ) (hcost : p e < p 0 + e) : ∃ k < e, p (k + 1) = p k := by
  by_contra! hnone
  have hlower : ∀ i ≤ e, p 0 + i ≤ p i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hmono := hp (show i ≤ i + 1 by omega)
      have hne := hnone i (by omega)
      omega
  have := hlower e le_rfl
  omega

/-- A boundary cost smaller than its length yields an index `k < e` where the next site is
uniquely determined by the occurring interior and prefix pattern. Lemma 5.5
(`lem:boundary-window`), equation `eq:boundary-rule`. -/
theorem boundaryRule_of_small_cost {A : Type*} (c : Configuration A)
    (hc : FiniteRange c) (C : Finset Lattice) (e : ℕ)
    (hcost : complexity c (prefixWindow C e) < complexity c C + e) :
    ∃ k < e, BoundaryRule c C k := by
  obtain ⟨k, hk, heq⟩ := exists_plateau_of_small_increase
    (fun k => complexity c (prefixWindow C k))
    (fun i j hij => complexity_mono hc (prefixWindow_mono C hij)) e
    (by simpa using hcost)
  refine ⟨k, hk, ?_⟩
  intro u v hC hmem
  have hsmall : patternAt c (prefixWindow C k) u = patternAt c (prefixWindow C k) v := by
    funext z
    rcases Finset.mem_union.mp z.2 with hz | hz
    · exact hC z.1 hz
    · obtain ⟨i, hi, hiz⟩ := (mem_rowPrefix z.1 k).mp hz
      simpa [patternAt, hiz, add_comm] using hmem ⟨i, hi⟩
  have hlarge := equal_complexity_unique_extension hc
    (prefixWindow_mono C (show k ≤ k + 1 by omega)) heq.symm hsmall
  have hkSite : ((k : ℤ), (0 : ℤ)) ∈ prefixWindow C (k + 1) := by
    apply Finset.mem_union_right
    exact (mem_rowPrefix _ _).mpr ⟨k, by omega, rfl⟩
  simpa [patternAt, add_comm] using congrFun hlarge ⟨_, hkSite⟩

/-- Outputs with at least two distinct preimages are bounded in number by input cardinality
minus output cardinality. The additive statement counts only finite occurring fibers. Lemma
5.7 (`lem:periodic-interior`). -/
theorem ambiguous_output_budget {A B : Type*} (f : A → B) {P : Set A}
    (hP : P.Finite) {Q : Set B}
    (hQ : ∀ b ∈ Q, ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ f x = b ∧ f y = b) :
    Q.ncard + (f '' P).ncard ≤ P.ncard := by
  classical
  by_cases hPn : P.Nonempty
  swap
  · have hPe : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hPn
    have hQe : Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨x, hx, _⟩ := hQ b hb
      simp [hPe] at hx
    simp [hPe, hQe]
  let : Nonempty A := ⟨hPn.choose⟩
  let R := Function.invFunOn f P '' (f '' P)
  have hR : R ⊆ P := Function.invFunOn_image_image_subset f P
  have hRcard : R.ncard = (f '' P).ncard :=
    (Function.invFunOn_injOn_image f P).ncard_image
  have hQsub : Q ⊆ f '' (P \ R) := by
    intro b hb
    obtain ⟨x, hx, y, hy, hne, hfx, hfy⟩ := hQ b hb
    have hrep : ∀ a ∈ R, f a = b → a = Function.invFunOn f P b := by
      rintro a ⟨d, hd, rfl⟩ heq
      rw [Function.invFunOn_eq hd] at heq
      exact congrArg (Function.invFunOn f P) heq
    by_cases hxR : x ∈ R
    · have hyR : y ∉ R := by
        intro hyR
        exact hne ((hrep x hxR hfx).trans (hrep y hyR hfy).symm)
      exact ⟨y, ⟨hy, hyR⟩, hfy⟩
    · exact ⟨x, ⟨hx, hxR⟩, hfx⟩
  have hcard : Q.ncard ≤ (P \ R).ncard :=
    (Set.ncard_le_ncard hQsub (hP.sdiff.image f)).trans (Set.ncard_image_le hP.sdiff)
  have hsum : (P \ R).ncard + (f '' P).ncard = P.ncard := by
    rw [← hRcard]
    exact Set.ncard_sdiff_add_ncard_of_subset hR hP
  exact (Nat.add_le_add_right hcard _).trans_eq hsum

end Nivat.TwoFactors
