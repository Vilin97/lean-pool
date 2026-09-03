/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Basis

/-!
# The dimension gap between the first two subspaces

`dim V - dim U ≤ |R₁|`: passing from `U` to `V` adds only the twisted functions at the simple real
points, one per point, so the dimension can grow by at most their number.

This is the bound that turns the source's second-range estimate into a statement about the count of
simple real elements — the quantity the whole proposition is about.
-/

@[expose] public section

namespace ZetaZeros

open Module

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- `finrank (p ⊔ q) ≤ finrank p + finrank q` for finitely-generated submodules of an arbitrary
module. Mathlib's `finrank_sup_add_finrank_inf_eq` needs the *ambient* module finite-dimensional,
which `L²` is not, so the bound is built here from the surjection `p × q → p ⊔ q`. -/
theorem finrank_sup_le {M : Type*} [AddCommGroup M] [Module ℂ M] (p q : Submodule ℂ M)
    [FiniteDimensional ℂ p] [FiniteDimensional ℂ q] :
    finrank ℂ (p ⊔ q : Submodule ℂ M) ≤ finrank ℂ p + finrank ℂ q := by
  classical
  let f : (p × q) →ₗ[ℂ] (p ⊔ q : Submodule ℂ M) :=
    { toFun := fun x => ⟨(x.1 : M) + (x.2 : M),
        Submodule.add_mem_sup x.1.2 x.2.2⟩
      map_add' := by intro x y; ext; simp; abel
      map_smul' := by intro c x; ext; simp [smul_add] }
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp y.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by simpa [f] using hab)⟩
  have := LinearMap.finrank_le_finrank_of_surjective (f := f) hsurj
  simpa [Module.finrank_prod] using this

/-- `V` is `U` together with the span of the twisted functions at the simple real points. -/
private lemma subspaceV_eq_sup (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    subspaceV h Z m
      = Submodule.span ℂ (fzL2 h '' (simpleRealPart Z m : Set ℂ)) ⊔ subspaceU h Z m := by
  rw [subspaceV, subspaceU, ← Submodule.span_union]
  congr 1
  rw [Finset.coe_union, Set.image_union]
  ext x
  simp only [Set.mem_union]
  tauto

/-- **The dimension gap.** Passing from `U` to `V` costs at most one dimension per simple real
point. -/
@[zz_tag "lem_dim_V_minus_U"]
theorem finrank_subspaceV_le (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    finrank ℂ (subspaceV h Z m)
      ≤ finrank ℂ (subspaceU h Z m) + (simpleRealPart Z m).card := by
  classical
  have hsup := subspaceV_eq_sup h Z m
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (fzL2 h '' (simpleRealPart Z m : Set ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have hle : finrank ℂ (subspaceV h Z m)
      ≤ finrank ℂ (Submodule.span ℂ (fzL2 h '' (simpleRealPart Z m : Set ℂ)))
        + finrank ℂ (subspaceU h Z m) := by
    rw [hsup]
    exact finrank_sup_le _ _
  have hcard : finrank ℂ (Submodule.span ℂ (fzL2 h '' (simpleRealPart Z m : Set ℂ)))
      ≤ (simpleRealPart Z m).card := by
    have himg : fzL2 h '' (simpleRealPart Z m : Set ℂ)
        = (((simpleRealPart Z m).image (fzL2 h) : Finset (L2Interval lam)) : Set _) := by
      rw [Finset.coe_image]
    rw [himg]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le
  omega

end ZetaZeros
