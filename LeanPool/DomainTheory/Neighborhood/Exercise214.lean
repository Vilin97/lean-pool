/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Approximable

/-!
# Exercise 2.14 (Scott 1981, PRG-19, §2) — the neighbourhood correspondence `φ` of
an isomorphism

> **EXERCISE 2.14.** Let `f : |𝒟₀| → |𝒟₁|` be an isomorphism between domains. Let
`φ : 𝒟₀ → 𝒟₁` be
> the one-one correspondence between neighbourhoods provided by Theorem 2.7 where
`f(↑X) = ↑φ(X)`
> for all `X ∈ 𝒟₀`. Show that the approximable mapping determined by `f` is just
the relationship
> `φ(X) ⊆ Y`. In addition prove that if `X, X' ∈ 𝒟₀` are consistent, then
> `φ(X ∩ X') = φ(X) ∩ φ(X')`.
> Remark that the isomorphisms between domains correspond exactly to the
isomorphisms between
> neighbourhood systems (in the sense of one-one inclusion preserving
correspondences).

Theorem 2.7 (`exists_principal_eq_apply_principal`) says a domain isomorphism `e :
|𝒟₀| ≃o |𝒟₁|`
carries each finite element `↑X` to a finite element `↑Y`. We extract the witness
`Y` by
`Classical.choose`, getting `φ` with `φ_spec : e(↑X) = ↑φ(X)`:

* `phi e hX`, `phi_mem`, `phi_spec` — the neighbourhood correspondence `φ` of `e`.
* `rel_ofIso_iff` — the approximable mapping of `e` is exactly `φ(X) ⊆ Y`:
  `(ofIso e).rel X Y ↔ 𝒟₁ Y ∧ φ(X) ⊆ Y` (for `X ∈ 𝒟₀`).
* `phi_inter` — **`φ(X ∩ X') = φ(X) ∩ φ(X')`** for *consistent* `X, X'` (i.e. `X ∩
X' ∈ 𝒟₀`).
  The proof goes through the order structure: `↑(X ∩ X')` is the **least upper
  bound** (join) of
  `↑X, ↑X'` in `|𝒟₀|` (note the inclusion order is *reversed*); `e` and `e.symm`
  are monotone, so
  they preserve this join, and the join of two consistent principals `↑A, ↑B` in
  `|𝒟₁|` is
  `↑(A ∩ B)`.

`φ` is `Classical.choose`-based, hence `noncomputable` and classical; the
order-theoretic proofs of
`rel_ofIso_iff`/`phi_inter` are otherwise choice-free (`propext`, `Quot.sound`). -/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.14 — the correspondence `φ`.** For a domain isomorphism `e` and
`X ∈ 𝒟₀`, `φ(X)` is
the neighbourhood with `e(↑X) = ↑φ(X)` provided by Theorem 2.7. -/
noncomputable def phi (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) : Set β :=
  Classical.choose (exists_principal_eq_apply_principal e hX)

/-- `φ(X) ∈ 𝒟₁`. -/
theorem phi_mem (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    V₁.mem (phi e hX) :=
  Classical.choose (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

/-- **Theorem 2.7 defining equation: `e(↑X) = ↑φ(X)`.** -/
theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

/-- **Exercise 2.14 — the approximable mapping of `e` is `φ(X) ⊆ Y`.** For `X ∈
𝒟₀`,
`(ofIso e).rel X Y ↔ Y ∈ 𝒟₁ ∧ φ(X) ⊆ Y`. (Immediate from `phi_spec` and
`mem_principal`.) -/
theorem rel_ofIso_iff (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    (ofIso e).rel X Y ↔ V₁.mem Y ∧ phi e hX ⊆ Y := by
  constructor
  · rintro ⟨_, hmem⟩
    have h : (e (V₀.principal hX)).mem Y := hmem
    rw [phi_spec e hX] at h
    exact h
  · intro h
    refine ⟨hX, ?_⟩
    rw [phi_spec e hX]
    exact h

/-- **Exercise 2.14 — `φ` preserves consistent intersections.** If `X, X'` are
consistent
(`X ∩ X' ∈ 𝒟₀`), then `φ(X ∩ X') = φ(X) ∩ φ(X')`.

`↑(X ∩ X')` is the join of `↑X, ↑X'` in `|𝒟₀|` (the order is inclusion-reversed).
`e`/`e.symm`
preserve this least upper bound, and the join of the consistent principals `↑φ(X),
↑φ(X')` is
`↑(φ(X) ∩ φ(X'))`. -/
theorem phi_inter (e : V₀.Element ≃o V₁.Element) {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hXX' : V₀.mem (X ∩ X')) :
    phi e hXX' = phi e hX ∩ phi e hX' := by
  have hpX_le : V₀.principal hX ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX hXX').mpr Set.inter_subset_left
  have hpX'_le : V₀.principal hX' ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX' hXX').mpr Set.inter_subset_right
  have hleast : ∀ w : V₀.Element, V₀.principal hX ≤ w → V₀.principal hX' ≤ w →
      V₀.principal hXX' ≤ w := by
    intro w hXw hX'w Z hZ
    obtain ⟨hZmem, hsubZ⟩ := hZ
    have hwX : w.mem X := hXw X ⟨hX, subset_rfl⟩
    have hwX' : w.mem X' := hX'w X' ⟨hX', subset_rfl⟩
    exact w.up_mem (w.inter_mem hwX hwX') hZmem hsubZ
  have hqX : e (V₀.principal hX) = V₁.principal (phi_mem e hX) := phi_spec e hX
  have hqX' : e (V₀.principal hX') = V₁.principal (phi_mem e hX') := phi_spec e hX'
  have hqXX' : e (V₀.principal hXX') = V₁.principal (phi_mem e hXX') := phi_spec e hXX'
  have hsub1 : phi e hXX' ⊆ phi e hX := by
    have h : e (V₀.principal hX) ≤ e (V₀.principal hXX') := e.monotone hpX_le
    rw [hqX, hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX) (phi_mem e hXX')).mp h
  have hsub1' : phi e hXX' ⊆ phi e hX' := by
    have h : e (V₀.principal hX') ≤ e (V₀.principal hXX') := e.monotone hpX'_le
    rw [hqX', hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX') (phi_mem e hXX')).mp h
  have hsubInter : phi e hXX' ⊆ phi e hX ∩ phi e hX' := Set.subset_inter hsub1 hsub1'
  have hinter : V₁.mem (phi e hX ∩ phi e hX') :=
    V₁.inter_mem (phi_mem e hX) (phi_mem e hX') (phi_mem e hXX') hsubInter
  have hsub2 : phi e hX ∩ phi e hX' ⊆ phi e hXX' := by
    have hqXleI : e (V₀.principal hX) ≤ V₁.principal hinter := by
      rw [hqX]; exact (V₁.principal_le_iff (phi_mem e hX) hinter).mpr Set.inter_subset_left
    have hqX'leI : e (V₀.principal hX') ≤ V₁.principal hinter := by
      rw [hqX']; exact (V₁.principal_le_iff (phi_mem e hX') hinter).mpr Set.inter_subset_right
    have hpXleI : V₀.principal hX ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqXleI; rwa [e.symm_apply_apply] at h
    have hpX'leI : V₀.principal hX' ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqX'leI; rwa [e.symm_apply_apply] at h
    have hpXX'leI : V₀.principal hXX' ≤ e.symm (V₁.principal hinter) :=
      hleast _ hpXleI hpX'leI
    have h : e (V₀.principal hXX') ≤ V₁.principal hinter := by
      have h := e.monotone hpXX'leI; rwa [e.apply_symm_apply] at h
    rw [hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hXX') hinter).mp h
  exact Set.Subset.antisymm hsubInter hsub2

end Domain.Neighborhood
