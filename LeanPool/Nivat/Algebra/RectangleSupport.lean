/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.Action
public import LeanPool.Nivat.Core.Patterns
public import Mathlib.Algebra.MonoidAlgebra.Support

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
# Multiples supported in a rectangle

The support equality in Lemma 2.1 (`lem:supported`) is
`support_mul_subset_rectangle_iff`. Coordinate extrema of a nonzero product
add: lexicographic refinement gives an extreme support pair whose sum has a
unique representation and therefore a nonzero coefficient.

The definitions `erosion` and `erodedWindow` express containment of every
translated filter-support point. The equality holds for empty erosion as well
as for positive rectangles. The injective finite multiplier map and the
associated dimension calculation from Lemma 2.1 are constructed in
`Nivat.Descent.ExactDescent`, where they enter Theorem 2.2 (`thm:descent`).
-/

@[expose] public section

namespace Nivat.Algebra

open scoped Pointwise

/-- Auxiliary to Lemma 2.1 (`lem:supported`): lexicographically maximal support points have a unique
sum, so their product coefficient survives cancellation. The coordinate map allows the same
argument for either coordinate and either orientation. -/
private theorem exists_mul_support_extreme (f g : Laurent) (hf : f ≠ 0) (hg : g ≠ 0)
    (e : Lattice →+ Lattice) (he : Function.Injective e) :
    ∃ a ∈ f.coeff.support, ∃ b ∈ g.coeff.support,
      a + b ∈ (f * g).coeff.support ∧
        (∀ z ∈ f.coeff.support, (e z).1 ≤ (e a).1) ∧
        (∀ z ∈ g.coeff.support, (e z).1 ≤ (e b).1) := by
  classical
  have hfS : f.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hf
  have hgS : g.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hg
  obtain ⟨a, ha, hmaxa⟩ := f.coeff.support.exists_max_image (fun z => toLex (e z)) hfS
  obtain ⟨b, hb, hmaxb⟩ := g.coeff.support.exists_max_image (fun z => toLex (e z)) hgS
  have huniq : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro x y hx hy hxy
    have hxle := Prod.Lex.toLex_le_toLex.mp (hmaxa x hx)
    have hyle := Prod.Lex.toLex_le_toLex.mp (hmaxb y hy)
    have hsum : e x + e y = e a + e b := by rw [← map_add, ← map_add, hxy]
    have hs1 := congrArg Prod.fst hsum
    have hs2 := congrArg Prod.snd hsum
    simp only [Prod.fst_add] at hs1
    simp only [Prod.snd_add] at hs2
    constructor
    · apply he
      apply Prod.ext <;> omega
    · apply he
      apply Prod.ext <;> omega
  have hab : a + b ∈ (f * g).coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha) (Finsupp.mem_support_iff.mp hb)
  refine ⟨a, ha, b, hb, hab, ?_, ?_⟩
  · intro z hz
    exact Prod.Lex.monotone_fst _ _ (hmaxa z hz)
  · intro z hz
    exact Prod.Lex.monotone_fst _ _ (hmaxb z hz)

/-- Auxiliary to Lemma 2.1 (`lem:supported`): a coordinate bound on the product support bounds the
coordinate sum of every pair from the factor supports. -/
private theorem support_sum_coord_le (f g : Laurent) (hf : f ≠ 0) (hg : g ≠ 0)
    (e : Lattice →+ Lattice) (he : Function.Injective e) (K : ℤ)
    (hbound : ∀ w ∈ (f * g).coeff.support, (e w).1 ≤ K)
    (u : Lattice) (hu : u ∈ f.coeff.support) (v : Lattice) (hv : v ∈ g.coeff.support) :
    (e (u + v)).1 ≤ K := by
  obtain ⟨a, ha, b, hb, hab, hmaxa, hmaxb⟩ := exists_mul_support_extreme f g hf hg e he
  have h1 := hmaxa u hu
  have h2 := hmaxb v hv
  have h3 := hbound (a + b) hab
  simp only [map_add, Prod.fst_add] at h3 ⊢
  omega

/-- The eroded support window in Section 1.2, equation (`eq:erosion-definition`), and Lemma 2.1
(`lem:supported`): all translates of the filter support contained in the target. -/
def erosion (Φ : Laurent) (R : Finset Lattice) : Set Lattice :=
  {z | ∀ a ∈ Φ.coeff.support, z + a ∈ R}

/-- Auxiliary to Lemma 2.1 (`lem:supported`): erosion by a nonzero filter is finite because any one
support point embeds it into a translate of the finite target window. -/
theorem erosion_finite (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice) :
    (erosion Φ R).Finite := by
  have hS : Φ.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hΦ
  obtain ⟨a, ha⟩ := hS
  apply (R.finite_toSet.image (fun r => r - a)).subset
  intro z hz
  exact ⟨z + a, hz a ha, by simp⟩

/-- The finite-set form of the erosion in Lemma 2.1 (`lem:supported`), including empty erosion. -/
noncomputable def erodedWindow (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice) :
    Finset Lattice := (erosion_finite Φ hΦ R).toFinset

/-- The membership condition for the eroded window of Lemma 2.1 (`lem:supported`). -/
@[simp] theorem mem_erodedWindow (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice)
    (z : Lattice) : z ∈ erodedWindow Φ hΦ R ↔ ∀ a ∈ Φ.coeff.support, z + a ∈ R := by
  simp [erodedWindow, erosion]

/-- The support equality in Lemma 2.1 (`lem:supported`): a multiple is supported in an axis-aligned
rectangle exactly when its multiplier is supported in the erosion. The statement also covers
zero side lengths and empty erosion. -/
theorem support_mul_subset_rectangle_iff (Φ : Laurent) (hΦ : Φ ≠ 0) (g : Laurent)
    (m n : ℕ) : (Φ * g).coeff.support ⊆ rectangle m n ↔
      g.coeff.support ⊆ erodedWindow Φ hΦ (rectangle m n) := by
  classical
  constructor
  · intro hfit z hz
    rw [mem_erodedWindow]
    intro u hu
    have hg : g ≠ 0 := by intro heq; simp [heq] at hz
    have hrect : ∀ w ∈ (Φ * g).coeff.support,
        0 ≤ w.1 ∧ w.1 < m ∧ 0 ≤ w.2 ∧ w.2 < n := by
      intro w hw
      exact (mem_rectangle w m n).mp (hfit hw)
    have hfstHi := support_sum_coord_le Φ g hΦ hg (AddMonoidHom.id Lattice)
      Function.injective_id ((m : ℤ) - 1) (by
        intro w hw
        change w.1 ≤ (m : ℤ) - 1
        have := hrect w hw
        omega) u hu z hz
    have hfstLo := support_sum_coord_le Φ g hΦ hg
      (AddEquiv.neg Lattice).toAddMonoidHom (AddEquiv.neg Lattice).injective 0 (by
        intro w hw
        change -w.1 ≤ 0
        have := hrect w hw
        omega) u hu z hz
    have hsndHi := support_sum_coord_le Φ g hΦ hg
      (AddEquiv.prodComm : Lattice ≃+ Lattice).toAddMonoidHom AddEquiv.prodComm.injective
      ((n : ℤ) - 1) (by
        intro w hw
        change w.2 ≤ (n : ℤ) - 1
        have := hrect w hw
        omega) u hu z hz
    let revSwap : Lattice ≃+ Lattice := AddEquiv.prodComm.trans (AddEquiv.neg Lattice)
    have hsndLo := support_sum_coord_le Φ g hΦ hg
      revSwap.toAddMonoidHom revSwap.injective 0 (by
        intro w hw
        change -w.2 ≤ 0
        have := hrect w hw
        omega) u hu z hz
    change u.1 + z.1 ≤ (m : ℤ) - 1 at hfstHi
    change -(u.1 + z.1) ≤ 0 at hfstLo
    change u.2 + z.2 ≤ (n : ℤ) - 1 at hsndHi
    change -(u.2 + z.2) ≤ 0 at hsndLo
    rw [mem_rectangle]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · intro hfit w hw
    obtain ⟨u, hu, z, hz, rfl⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset Φ g hw)
    have hzfit := (mem_erodedWindow Φ hΦ (rectangle m n) z).mp (hfit hz)
    simpa [add_comm] using hzfit u hu

end Nivat.Algebra
