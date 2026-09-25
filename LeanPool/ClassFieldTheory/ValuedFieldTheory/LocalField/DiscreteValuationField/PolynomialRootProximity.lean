/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Finset.Max
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
/-!
# A root-proximity estimate over a discrete valuation ring

If a monic polynomial splits over a discrete valuation ring, one of its
roots is at least as close to a given point as the polynomial value, after
accounting for the derivative at that root.  The proof selects a root of
maximal additive valuation and compares the remaining factors by the
ultrametric inequality.

Repeated roots and zero derivative values are allowed; the statement is in
`ℕ∞`, so the estimate also covers infinite additive valuations.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

universe u

namespace Polynomial.Splits

private theorem addVal_multiset_prod_le
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {α : Type*} (s : Multiset α) (f g : α → R)
    (h :
      ∀ z ∈ s,
        IsDiscreteValuationRing.addVal R (f z) ≤
          IsDiscreteValuationRing.addVal R (g z)) :
    IsDiscreteValuationRing.addVal R ((s.map f).prod) ≤
      IsDiscreteValuationRing.addVal R ((s.map g).prod) := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons z s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons,
        IsDiscreteValuationRing.addVal_mul,
        IsDiscreteValuationRing.addVal_mul]
      apply add_le_add
      · exact h z (by simp)
      · apply ih
        intro t ht
        exact h t (by simp [ht])

/-- Let `p` be a nonconstant monic polynomial that splits over a discrete
valuation ring.  For every `x`, some root `y` satisfies

`v(p(x)) ≤ v(x - y) + v(p'(y))`.

Choosing `y` with maximal `v(x-y)` makes every other factor `x-z` no deeper
than `y-z`; multiplying those inequalities gives the result. -/
theorem exists_root_addVal_eval_le_sub_add_derivative
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : R[X]) (hs : p.Splits) (hm : p.Monic)
    (hdeg : p.natDegree ≠ 0) (x : R) :
    ∃ y, y ∈ p.roots ∧
      IsDiscreteValuationRing.addVal R (p.eval x) ≤
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R (p.derivative.eval y) := by
  classical
  have hroots : p.roots ≠ 0 := by
    intro hzero
    apply hdeg
    simpa [hzero] using hs.natDegree_eq_card_roots
  obtain ⟨y, hy, hymax⟩ :=
    Multiset.exists_max_image
      (s := p.roots)
      (fun z => IsDiscreteValuationRing.addVal R (x - z)) hroots
  have hfactor :
      ∀ z ∈ p.roots.erase y,
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (y - z) := by
    intro z hz
    have hzroot : z ∈ p.roots :=
      Multiset.mem_of_mem_erase hz
    have hmax :
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (x - y) :=
      hymax z hzroot
    have hneg :
        IsDiscreteValuationRing.addVal R (y - x) =
          IsDiscreteValuationRing.addVal R (x - y) := by
      have hsub : y - x = -(x - y) := by ring
      rw [hsub, (IsDiscreteValuationRing.addVal R).map_neg]
    have hmax' :
        IsDiscreteValuationRing.addVal R (x - z) ≤
          IsDiscreteValuationRing.addVal R (y - x) := by
      rw [hneg]
      exact hmax
    have hultra :=
      IsDiscreteValuationRing.addVal_add
        (R := R) (a := y - x) (b := x - z)
    have hsum : (y - x) + (x - z) = y - z := by
      ring
    rw [min_eq_right hmax', hsum] at hultra
    exact hultra
  have hprod :
      IsDiscreteValuationRing.addVal R
          (((p.roots.erase y).map (x - ·)).prod) ≤
        IsDiscreteValuationRing.addVal R
          (((p.roots.erase y).map (y - ·)).prod) :=
    addVal_multiset_prod_le (p.roots.erase y)
      (x - ·) (y - ·) hfactor
  have hroot_prod :
      ((p.roots.map (x - ·)).prod) =
        (x - y) * (((p.roots.erase y).map (x - ·)).prod) := by
    calc
      ((p.roots.map (x - ·)).prod) =
          (((y ::ₘ p.roots.erase y).map (x - ·)).prod) :=
        congrArg (fun s : Multiset R => (s.map (x - ·)).prod)
          (Multiset.cons_erase hy).symm
      _ = (x - y) * (((p.roots.erase y).map (x - ·)).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]
  refine ⟨y, hy, ?_⟩
  calc
    IsDiscreteValuationRing.addVal R (p.eval x) =
        IsDiscreteValuationRing.addVal R
          ((p.roots.map (x - ·)).prod) := by
            rw [hs.eval_eq_prod_roots_of_monic hm]
    _ =
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (((p.roots.erase y).map (x - ·)).prod) := by
              rw [hroot_prod, IsDiscreteValuationRing.addVal_mul]
    _ ≤
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (((p.roots.erase y).map (y - ·)).prod) :=
      add_le_add (le_refl _) hprod
    _ =
        IsDiscreteValuationRing.addVal R (x - y) +
          IsDiscreteValuationRing.addVal R
            (p.derivative.eval y) := by
              rw [hs.eval_root_derivative hm hy]

end Polynomial.Splits

end
