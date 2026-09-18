/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Patterns

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
# Affine lattice coordinates

Coordinate transport for Lemma 5.5 (`lem:boundary-window`) and Theorem 5.1
(`thm:twofactor`) in `paper/nivat.tex`.

A configuration and its window are transported together. The affine map `s`
acts on sites, while its additive part `t` acts on translation and period vectors.
-/

namespace Nivat

/-- Reindexing lattice sites preserves finite range (Section 1.1). -/
theorem FiniteRange.precomp {A : Type*} {c : Configuration A} (hc : FiniteRange c)
    (f : Lattice → Lattice) : FiniteRange (c ∘ f) := by
  apply hc.subset
  rintro a ⟨z, rfl⟩
  exact ⟨f z, rfl⟩

/-- Transport both a configuration and its window along affine lattice coordinates.
This is the basis-and-origin change in Lemma 5.5 (`lem:boundary-window`);
`s` is the affine bijection and `t` its linear part. -/
theorem complexity_affine_reindex {A : Type*} (c : Configuration A)
    (s : Lattice ≃ Lattice) (t : Lattice ≃+ Lattice)
    (hst : ∀ z u : Lattice, s (z + u) = s z + t u) (D : Finset Lattice) :
    complexity (c ∘ s) D = complexity c (D.map s.toEmbedding) := by
  symm
  apply Set.ncard_congr
    (fun p _ => fun z : D => p ⟨s z, Finset.mem_map.mpr ⟨z, z.2, rfl⟩⟩)
  · rintro p ⟨u, rfl⟩
    refine ⟨t.symm u, ?_⟩
    funext z
    simp [patternAt, hst]
  · intro p q _ _ hpq
    funext z
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp z.2
    have h := congrFun hpq ⟨w, hw⟩
    convert h using 1 <;> congr 1 <;> exact Subtype.ext heq.symm
  · rintro p ⟨u, rfl⟩
    refine ⟨patternAt c (D.map s.toEmbedding) (t u), ⟨t u, rfl⟩, ?_⟩
    funext z
    simp [patternAt, hst]

/-- A period in affine coordinates transports through the linear part.
This is the return to the original lattice in Theorem 5.1 (`thm:twofactor`). -/
theorem isPeriod_affine_reindex_iff {A : Type*} (c : Configuration A)
    (s : Lattice ≃ Lattice) (t : Lattice ≃+ Lattice)
    (hst : ∀ z u : Lattice, s (z + u) = s z + t u) (h : Lattice) :
    IsPeriod (c ∘ s) h ↔ IsPeriod c (t h) := by
  constructor
  · intro hp z
    have hx := hp (s.symm z)
    simpa only [Function.comp_apply, hst, s.apply_symm_apply] using hx
  · intro hp z
    simpa only [Function.comp_apply, hst] using hp (s z)

/-- Difference operators transport with their lattice direction.
This is the mixed-difference coordinate change in Theorem 5.1 (`thm:twofactor`). -/
theorem difference_affine_reindex {A : Type*} [AddCommGroup A] (c : Configuration A)
    (s : Lattice ≃ Lattice) (t : Lattice ≃+ Lattice)
    (hst : ∀ z u : Lattice, s (z + u) = s z + t u) (h : Lattice) :
    difference h (c ∘ s) = difference (t h) c ∘ s := by
  funext z
  simp only [difference_apply, Function.comp_apply, hst]

end Nivat
