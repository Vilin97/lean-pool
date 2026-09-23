/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.TwoFactors.Window
public import LeanPool.Nivat.Core.Reindex

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
# Normalizing the selected boundary

The coordinate normalization in Lemma 5.5 (`lem:boundary-window`) of
`paper/nivat.tex`. Translation places the first edge site at the origin, and
reflection in the normal coordinate places the interior above the edge.
The window and configuration are transported by the same affine bijection;
the pattern inequality and row-block witnesses are preserved explicitly.
-/

@[expose] public section

namespace Nivat.TwoFactors

/-- The additive lattice equivalence that preserves horizontal coordinates and either preserves
or reverses the normal coordinate. Lemma 5.5 (`lem:boundary-window`). -/
def normalSignEquiv (ε : ℤ) (hε : ε = 1 ∨ ε = -1) : Lattice ≃+ Lattice where
  toFun z := (z.1, ε * z.2)
  invFun z := (z.1, ε * z.2)
  left_inv z := by rcases hε with rfl | rfl <;> simp
  right_inv z := by rcases hε with rfl | rfl <;> simp
  map_add' z u := by apply Prod.ext <;> dsimp; ring

/-- The affine lattice bijection sending the normalized edge origin to its selected site and
choosing the normal orientation. Lemma 5.5 (`lem:boundary-window`). -/
def normalAffineEquiv (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (start edge : ℤ) :
    Lattice ≃ Lattice :=
  (normalSignEquiv ε hε).toEquiv.trans (Equiv.addRight (start, edge))

/-- The normalization map translates the horizontal coordinate and translates the signed normal
coordinate. Lemma 5.5 (`lem:boundary-window`). -/
@[simp] theorem normalAffineEquiv_apply (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (start edge : ℤ) (z : Lattice) :
    normalAffineEquiv ε hε start edge z = (z.1 + start, ε * z.2 + edge) := rfl

/-- The linear part of the affine normalization transports a translation vector by the chosen
normal sign. Lemma 5.5 (`lem:boundary-window`). -/
theorem normalAffineEquiv_add (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (start edge : ℤ) (z u : Lattice) :
    normalAffineEquiv ε hε start edge (z + u) =
      normalAffineEquiv ε hε start edge z + normalSignEquiv ε hε u := by
  apply Prod.ext <;> dsimp [normalAffineEquiv, normalSignEquiv] <;> ring

/-- The bottom-edge window data together with the exact affine change of configuration under
which its boundary-cost inequality holds. Lemma 5.5 (`lem:boundary-window`). -/
structure NormalizedWindow {A : Type*} (c : Configuration A) where
  /-- The affine map from normalized sites to the selected window sites. -/
  s : Lattice ≃ Lattice
  /-- The additive linear part transporting period vectors. -/
  t : Lattice ≃+ Lattice
  /-- Translation vectors are transported by the linear part. -/
  affine : ∀ z u : Lattice, s (z + u) = s z + t u
  /-- The horizontal coordinate direction is fixed by normalization. -/
  horizontal : ∀ q : ℤ, t (q, 0) = (q, 0)
  /-- The normalized interior above the bottom edge. -/
  C : Finset Lattice
  /-- The number of sites on the normalized bottom edge. -/
  e : ℕ
  /-- The highest normalized interior row, allowing zero. -/
  H : ℕ
  /-- The bottom edge has positive length. -/
  positive : 0 < e
  /-- All interior sites lie on rows `1` through `H`. -/
  interior : ∀ z ∈ C, 1 ≤ z.2 ∧ z.2 ≤ H
  /-- Each interior row contains `e - 1` consecutive sites. -/
  blocks : ∀ j : Fin H, ∃ l : ℤ, ∀ r : ℕ, r < e - 1 →
    (l + (r : ℤ), ((j : ℕ) : ℤ) + 1) ∈ C
  /-- The transported configuration satisfies the strict boundary-cost inequality. -/
  cost : complexity (c ∘ s) (prefixWindow C e) < complexity (c ∘ s) C + e

/-- Translate the first edge site to the origin and orient the normal coordinate so that the
interior lies above it, preserving the actual pattern inequality and row-block witnesses.
Lemma 5.5 (`lem:boundary-window`). -/
theorem ShapeWindow.normalize {A : Type*} {c : Configuration A} {D₀ : Finset Lattice}
    (w : ShapeWindow c D₀) : Nonempty (NormalizedWindow c) := by
  classical
  obtain ⟨ε, hε, horient⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((ε = 1 ∧ w.edge = w.lo) ∨ (ε = -1 ∧ w.edge = w.hi)) := by
    rcases w.edge_side with hl | hh
    · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, hl⟩⟩
    · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, hh⟩⟩
  let t := normalSignEquiv ε hε
  let s := normalAffineEquiv ε hε w.start w.edge
  let C := w.C.map s.symm.toEmbedding
  let D := w.D.map s.symm.toEmbedding
  let H := (w.hi - w.lo).toNat
  have hH : (H : ℤ) = w.hi - w.lo := Int.toNat_of_nonneg (sub_nonneg.mpr w.ordered)
  have hs (z : Lattice) : s z = (z.1 + w.start, ε * z.2 + w.edge) := rfl
  have hD (z : Lattice) : z ∈ D ↔ s z ∈ w.D := by
    simp only [D, Finset.mem_map_equiv, Equiv.symm_symm]
  have hC (z : Lattice) : z ∈ C ↔ s z ∈ w.C := by
    simp only [C, Finset.mem_map_equiv, Equiv.symm_symm]
  have hnorm : D = prefixWindow C w.e := by
    ext z
    rw [hD, prefixWindow, Finset.mem_union, hC]
    constructor
    · intro hz
      by_cases hedge : (s z).2 = w.edge
      · right
        have hz2 : z.2 = 0 := by
          rw [hs] at hedge
          rcases hε with rfl | rfl <;> dsimp at hedge <;> omega
        have hrow : ((s z).1, w.edge) ∈ w.D := by simpa only [← hedge] using hz
        obtain ⟨r, hr, hxr⟩ := (w.edge_exact _).mp hrow
        have hz1 : z.1 = r := by rw [hs] at hxr; dsimp at hxr; omega
        exact (mem_rowPrefix z w.e).mpr ⟨r, hr, Prod.ext hz1 hz2⟩
      · left
        rw [w.interior_eq]
        exact Finset.mem_filter.mpr ⟨hz, hedge⟩
    · rintro (hz | hz)
      · rw [w.interior_eq] at hz
        exact (Finset.mem_filter.mp hz).1
      · obtain ⟨r, hr, rfl⟩ := (mem_rowPrefix z w.e).mp hz
        rw [hs]
        simp only [mul_zero, zero_add]
        exact (w.edge_exact _).mpr ⟨r, hr, by omega⟩
  have hinterior : ∀ z ∈ C, 1 ≤ z.2 ∧ z.2 ≤ H := by
    intro z hz
    have hzin := (hC z).mp hz
    rw [w.interior_eq] at hzin
    obtain ⟨hzD, hze⟩ := Finset.mem_filter.mp hzin
    obtain ⟨hzlo, hzhi⟩ := w.bounds _ hzD
    rw [hs] at hzlo hzhi hze
    rcases horient with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;>
      dsimp at hzlo hzhi hze <;> constructor <;> omega
  have hblocks : ∀ j : Fin H, ∃ l : ℤ, ∀ r : ℕ, r < w.e - 1 →
      (l + (r : ℤ), ((j : ℕ) : ℤ) + 1) ∈ C := by
    intro j
    let row : ℤ := ε * (((j : ℕ) : ℤ) + 1) + w.edge
    have hlo : w.lo ≤ row := by
      rcases horient with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> dsimp [row] <;> omega
    have hhi : row ≤ w.hi := by
      rcases horient with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> dsimp [row] <;> omega
    have hne : row ≠ w.edge := by
      rcases hε with rfl | rfl <;> dsimp [row] <;> omega
    obtain ⟨l, hl⟩ := w.interior_row_blocks row hlo hhi hne
    refine ⟨l - w.start, ?_⟩
    intro r hr
    rw [hC, hs]
    convert hl r hr using 1; congr 1; dsimp [row]; ring
  have hmapsD : D.map s.toEmbedding = w.D := by simp [D, Finset.map_map]
  have hmapsC : C.map s.toEmbedding = w.C := by simp [C, Finset.map_map]
  have hcost : complexity (c ∘ s) (prefixWindow C w.e) < complexity (c ∘ s) C + w.e := by
    rw [← hnorm, complexity_affine_reindex c s t (normalAffineEquiv_add ε hε w.start w.edge),
      complexity_affine_reindex c s t (normalAffineEquiv_add ε hε w.start w.edge), hmapsD, hmapsC]
    exact w.small_cost
  refine ⟨⟨s, t, normalAffineEquiv_add ε hε w.start w.edge, ?_, C, w.e, H,
    w.positive, hinterior, hblocks, hcost⟩⟩
  intro q
  simp [t, normalSignEquiv]

end Nivat.TwoFactors
