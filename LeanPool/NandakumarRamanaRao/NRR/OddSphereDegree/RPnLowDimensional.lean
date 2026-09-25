/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RealProjectiveSpace
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyToChainHomotopy

/-!
# Low-dimensional real projective space: `RP⁰`

This file records the genuine low-dimensional computations available in pinned
Mathlib for `RP⁰`, the base case of the `H^*(RPⁿ; F₂)` ring computation.

`RP⁰` is a single point: `Sphere 0` is the unit sphere in `ℝ¹`, which is the
two-point set `{±e}`, and the antipodal quotient identifies the two points. Hence
`RP⁰` is a `Subsingleton`, therefore `TotallyDisconnectedSpace`, and Mathlib's
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` /
`singularHomologyFunctorZeroOfTotallyDisconnectedSpace` give its singular homology
outright:

```text
Hₙ(RP⁰; ℤ) = 0 (n ≠ 0), H₀(RP⁰; ℤ) ≅ ℤ.
```

These are honest, formalized computations: the only inputs are the point-set fact
`Subsingleton (RP 0)` (proved here from the library's `proj_eq_iff` and the
one-dimensional sphere geometry) and Mathlib's totally-disconnected homology API.

**Scope note.** This is the *homology* base case. The corresponding mod-two
*cohomology* base case `H^k(RP⁰; F₂) = 0 (k≠0)`, `H⁰(RP⁰; F₂) ≅ F₂` requires
dualizing the totally-disconnected chain complex through the library's
`singularCohomologyFunctor` (a contravariant `Hom(-, F₂)` of an exact-at-`n`
complex); pinned Mathlib has no off-the-shelf "dual of an exact complex is exact"
in this packaged form, so that step is the recorded next concrete theorem (see
cohomology computation is introduced.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- Any two points of `Sphere 0` (the unit sphere in `ℝ¹`) are equal or
antipodal: the one-dimensional unit sphere is the two-point set `{±e}`. -/
theorem sphere_zero_eq_or_neg (x y : Sphere 0) : x = y ∨ x = -y := by
  rcases x with ⟨x, hx⟩; rcases y with ⟨y, hy⟩
  simp_all +decide only [Nat.reduceAdd, Subtype.mk.injEq]
  rw [mem_sphere_zero_iff_norm] at hx hy
  norm_num [EuclideanSpace.norm_eq] at hx hy
  simp_all +decide only [Nat.reduceAdd, Finset.univ_unique, Fin.eq_zero, Fin.isValue,
    Finset.sum_const, Finset.card_singleton, one_smul, sq_eq_one_iff, Subtype.ext_iff,
    coe_neg_sphere]
  cases hx <;> cases hy <;> simp_all? +decide
  · exact Or.inl (by ext i; fin_cases i; aesop)
  · exact Or.inr (by ext i; fin_cases i; aesop)
  · exact Or.inr (by ext i; fin_cases i; aesop)
  · exact Or.inl (by ext i; fin_cases i; aesop)

/-- `RP⁰` is a single point: the antipodal quotient of the two-point set
`Sphere 0`. -/
instance : Subsingleton (RP 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := RP.exists_rep a
  obtain ⟨y, rfl⟩ := RP.exists_rep b
  simp +decide only [proj_apply, Quotient.eq']
  exact sphere_zero_eq_or_neg x y

/-- `RP⁰` is nonempty (it is the image of the nonempty `Sphere 0`). -/
instance : Nonempty (RP 0) :=
  ⟨proj 0 ⟨EuclideanSpace.single 0 1, by norm_num [EuclideanSpace.norm_eq]⟩⟩

/-- **Higher singular homology of `RP⁰` vanishes.** For `n ≠ 0`,
`Hₙ(RP⁰; ℤ) = 0`, since `RP⁰` is totally disconnected (a point). -/
theorem rp0_singularHomologyℤ_isZero (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero ((singularHomologyℤ n).obj (TopCat.of (RP 0))) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (RP 0)) hn

end SphereOddDegree
