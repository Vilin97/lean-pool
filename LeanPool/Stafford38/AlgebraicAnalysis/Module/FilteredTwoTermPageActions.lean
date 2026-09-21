/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPages
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Filtered operators on two-term pages

A filtered operator of degree `d` shifts `G p` into `G (p - d)` and commutes
with the two-term differential.  This file constructs its maps on the concrete
source and target pages, proves compatibility with `drop`, and proves that an
operator is unchanged on pages after adding one that shifts an additional
filtration level.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

/-- A `k`-linear operator of filtration degree `d` commuting with the
two-term differential. -/
structure PageOperator (d : ℤ) where
  /-- The underlying endomorphism of the filtered module. -/
  g : M →ₗ[k] M
  commute : K.f.comp g = g.comp K.f
  shift : ∀ p x, x ∈ K.G p → g x ∈ K.G (p - d)

namespace PageOperator

variable {K} {d : ℤ} (P : K.PageOperator d)

/-- Composition of filtered operators. -/
def comp {e : ℤ} (Q : K.PageOperator e) : K.PageOperator (d + e) where
  g := P.g.comp Q.g
  commute := by
    apply LinearMap.ext
    intro x
    change K.f (P.g (Q.g x)) = P.g (Q.g (K.f x))
    have hp := LinearMap.congr_fun P.commute (Q.g x)
    have hq := LinearMap.congr_fun Q.commute x
    change K.f (P.g (Q.g x)) = P.g (K.f (Q.g x)) at hp
    change K.f (Q.g x) = Q.g (K.f x) at hq
    rw [hp, hq]
  shift := by
    intro p x hx
    have hQ := Q.shift p x hx
    have hP := P.shift (p - e) (Q.g x) hQ
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hP

/-- The reverse-order composition, given the same canonical sum degree. -/
def reverseComp {e : ℤ} (Q : K.PageOperator e) : K.PageOperator (d + e) where
  g := Q.g.comp P.g
  commute := by
    apply LinearMap.ext
    intro x
    change K.f (Q.g (P.g x)) = Q.g (P.g (K.f x))
    have hq := LinearMap.congr_fun Q.commute (P.g x)
    have hp := LinearMap.congr_fun P.commute x
    change K.f (Q.g (P.g x)) = Q.g (K.f (P.g x)) at hq
    change K.f (P.g x) = P.g (K.f x) at hp
    rw [hq, hp]
  shift := by
    intro p x hx
    have hP := P.shift p x hx
    have hQ := Q.shift (p - d) (P.g x) hP
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hQ

private theorem coe_castG {p q : ℤ} (h : p = q) (x : K.G p) :
    ((h ▸ x : K.G q) : M) = (x : M) := by
  subst q
  rfl

theorem commute_apply (x : M) : K.f (P.g x) = P.g (K.f x) := by
  exact LinearMap.congr_fun P.commute x

/-- The restriction of the operator to a source-page cycle numerator. -/
def sourceRestricted (r : ℕ) (p : ℤ) :
    K.cycles r p →ₗ[k] K.cycles r (p - d) :=
  (P.g.comp (K.cycles r p).subtype).codRestrict (K.cycles r (p - d)) (by
    intro x
    refine ⟨P.shift p (x : M) x.property.1, ?_⟩
    change K.f (P.g (x : M)) ∈ K.G (p - d + r)
    rw [P.commute_apply]
    have h := P.shift (p + r) (K.f (x : M)) x.property.2
    have hindex : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
    rwa [hindex] at h)

private theorem sourceRestricted_denominator (r : ℕ) (p : ℤ) :
    (K.G (p + 1)).comap (K.cycles r p).subtype ≤
      ((K.G (p - d + 1)).comap (K.cycles r (p - d)).subtype).comap
        (P.sourceRestricted r p) := by
  intro x hx
  change P.g (x : M) ∈ K.G (p - d + 1)
  have h := P.shift (p + 1) (x : M) hx
  have hindex : p + 1 - d = p - d + 1 := by omega
  rwa [hindex] at h

/-- The operator induced on a source page. -/
def sourceMap (r : ℕ) (p : ℤ) :
    K.SourcePage r p →ₗ[k] K.SourcePage r (p - d) :=
  Submodule.mapQ _ _ (P.sourceRestricted r p)
    (P.sourceRestricted_denominator r p)

@[simp]
theorem sourceMap_mk (r : ℕ) (p : ℤ) (x : K.cycles r p) :
    P.sourceMap r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.sourceRestricted r p x) :=
  Submodule.mapQ_apply _ _ _ _

/-- Transport between equal source-page indices. -/
def sourcePageCast (r : ℕ) {p q : ℤ} (h : p = q) :
    K.SourcePage r p ≃ₗ[k] K.SourcePage r q := by
  subst q
  exact LinearEquiv.refl k _

@[simp]
theorem sourcePageCast_mk (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.cycles r p) :
    sourcePageCast (K := K) r h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h ▸ x) := by
  subst q
  rfl

/-- The restriction of the operator to a target-page filtration piece. -/
def targetRestricted (p : ℤ) : K.G p →ₗ[k] K.G (p - d) :=
  (P.g.comp (K.G p).subtype).codRestrict (K.G (p - d))
    (fun x => P.shift p (x : M) x.property)

private theorem maps_boundaries (r : ℕ) (p : ℤ) {x : M}
    (hx : x ∈ K.boundaries r p) : P.g x ∈ K.boundaries r (p - d) := by
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, e, he, rfl⟩
  rw [map_add]
  apply Submodule.add_mem
  · apply Submodule.mem_sup.mpr
    refine ⟨P.g a, ⟨P.shift p a ha.1, ?_⟩, 0, Submodule.zero_mem _, by simp⟩
    rcases ha.2 with ⟨z, hz, rfl⟩
    refine ⟨P.g z, ?_, ?_⟩
    · have h := P.shift (p - r + 1) z hz
      have hindex : p - (r : ℤ) + 1 - d = p - d - (r : ℤ) + 1 := by omega
      rwa [hindex] at h
    · exact P.commute_apply z
  · apply Submodule.mem_sup.mpr
    have h := P.shift (p + 1) e he
    have hindex : p + 1 - d = p - d + 1 := by omega
    rw [hindex] at h
    exact ⟨0, Submodule.zero_mem _, P.g e, h, by simp⟩

private theorem targetRestricted_denominator (r : ℕ) (p : ℤ) :
    (K.boundaries r p).comap (K.G p).subtype ≤
      ((K.boundaries r (p - d)).comap (K.G (p - d)).subtype).comap
        (P.targetRestricted p) := by
  intro x hx
  exact P.maps_boundaries r p hx

/-- The operator induced on a target page. -/
def targetMap (r : ℕ) (p : ℤ) :
    K.TargetPage r p →ₗ[k] K.TargetPage r (p - d) :=
  Submodule.mapQ _ _ (P.targetRestricted p)
    (P.targetRestricted_denominator r p)

@[simp]
theorem targetMap_mk (r : ℕ) (p : ℤ) (x : K.G p) :
    P.targetMap r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.targetRestricted p x) :=
  Submodule.mapQ_apply _ _ _ _

/-- Transport between target-page indices known to be equal. -/
def targetPageCast (r : ℕ) {p q : ℤ} (h : p = q) :
    K.TargetPage r p ≃ₗ[k] K.TargetPage r q := by
  subst q
  exact LinearEquiv.refl k _

@[simp]
theorem targetPageCast_mk (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.G p) :
    targetPageCast (K := K) r h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h ▸ x) := by
  subst q
  rfl

private def targetRestrictedAtDrop (r : ℕ) (p : ℤ) :
    K.G (p + r) →ₗ[k] K.G (p - d + r) :=
  (P.g.comp (K.G (p + r)).subtype).codRestrict (K.G (p - d + r)) (by
    intro x
    have h := P.shift (p + r) (x : M) x.property
    have hindex : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
    rwa [hindex] at h)

private theorem targetRestrictedAtDrop_denominator (r : ℕ) (p : ℤ) :
    (K.boundaries r (p + r)).comap (K.G (p + r)).subtype ≤
      ((K.boundaries r (p - d + r)).comap (K.G (p - d + r)).subtype).comap
        (P.targetRestrictedAtDrop r p) := by
  intro x hx
  have h := P.maps_boundaries r (p + r) hx
  have hindex : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
  rwa [hindex] at h

/-- The target-page operator at the codomain index of `drop`, reindexed by
the identity `(p+r)-d = (p-d)+r`. -/
def targetMapAtDrop (r : ℕ) (p : ℤ) :
    K.TargetPage r (p + r) →ₗ[k] K.TargetPage r (p - d + r) :=
  Submodule.mapQ _ _ (P.targetRestrictedAtDrop r p)
    (P.targetRestrictedAtDrop_denominator r p)

@[simp]
theorem targetMapAtDrop_mk (r : ℕ) (p : ℤ) (x : K.G (p + r)) :
    P.targetMapAtDrop r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.targetRestrictedAtDrop r p x) :=
  Submodule.mapQ_apply _ _ _ _

/-- `targetMapAtDrop` is the general target-page map followed by the canonical
reindexing isomorphism. -/
theorem targetMapAtDrop_eq_cast_targetMap (r : ℕ) (p : ℤ) :
    P.targetMapAtDrop r p =
      (targetPageCast (K := K) r
        (by omega : p + (r : ℤ) - d = p - d + (r : ℤ))).toLinearMap.comp
          (P.targetMap r (p + r)) := by
  let hindex : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
  change P.targetMapAtDrop r p =
    (targetPageCast (K := K) r hindex).toLinearMap.comp
      (P.targetMap r (p + r))
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on
    ((K.boundaries r (p + r)).comap (K.G (p + r)).subtype) y ?_
  intro x
  rw [P.targetMapAtDrop_mk, LinearMap.comp_apply, P.targetMap_mk]
  change Submodule.Quotient.mk (P.targetRestrictedAtDrop r p x) =
    targetPageCast (K := K) r _
      (Submodule.Quotient.mk (P.targetRestricted (p + r) x))
  rw [targetPageCast_mk]
  congr 1
  apply Subtype.ext
  change P.g (x : M) =
    ((hindex ▸ P.targetRestricted (p + r) x : K.G (p - d + r)) : M)
  rw [coe_castG]
  rfl

/-- The source and reindexed target operator maps commute with the page
differential. -/
theorem targetMapAtDrop_drop (r : ℕ) (p : ℤ) (x : K.SourcePage r p) :
    P.targetMapAtDrop r p (K.drop r p x) =
      K.drop r (p - d) (P.sourceMap r p x) := by
  refine Submodule.Quotient.induction_on
    ((K.G (p + 1)).comap (K.cycles r p).subtype) x ?_
  intro z
  rw [K.drop_mk, P.targetMapAtDrop_mk, P.sourceMap_mk, K.drop_mk]
  change Submodule.Quotient.mk (⟨P.g (K.f (z : M)), _⟩ : K.G (p - d + r)) =
    Submodule.Quotient.mk (⟨K.f (P.g (z : M)), _⟩ : K.G (p - d + r))
  congr 2
  exact (P.commute_apply (z : M)).symm

/-- Compatibility of the general source and target page maps with `drop`,
with the unavoidable target-index transport made explicit. -/
theorem targetMap_drop (r : ℕ) (p : ℤ) (x : K.SourcePage r p) :
    targetPageCast (K := K) r
        (by omega : p + (r : ℤ) - d = p - d + (r : ℤ))
        (P.targetMap r (p + r) (K.drop r p x)) =
      K.drop r (p - d) (P.sourceMap r p x) := by
  let hindex : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
  change ((targetPageCast (K := K) r hindex).toLinearMap.comp
    (P.targetMap r (p + r))) (K.drop r p x) = _
  rw [← P.targetMapAtDrop_eq_cast_targetMap r p]
  exact P.targetMapAtDrop_drop r p x

/-- Two degree-`d` operators have the same symbol when their difference shifts
one additional filtration level. -/
def SameSymbol (Q : K.PageOperator d) : Prop :=
  ∀ p x, x ∈ K.G p → (P.g - Q.g) x ∈ K.G (p - d + 1)

theorem sourceMap_eq_of_sameSymbol {Q : K.PageOperator d}
    (hPQ : P.SameSymbol Q) (r : ℕ) (p : ℤ) :
    P.sourceMap r p = Q.sourceMap r p := by
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on
    ((K.G (p + 1)).comap (K.cycles r p).subtype) y ?_
  intro x
  rw [P.sourceMap_mk, Q.sourceMap_mk]
  apply (Submodule.Quotient.eq _).2
  change P.g (x : M) - Q.g (x : M) ∈ K.G (p - d + 1)
  simpa using hPQ p (x : M) x.property.1

theorem targetMap_eq_of_sameSymbol {Q : K.PageOperator d}
    (hPQ : P.SameSymbol Q) (r : ℕ) (p : ℤ) :
    P.targetMap r p = Q.targetMap r p := by
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on
    ((K.boundaries r p).comap (K.G p).subtype) y ?_
  intro x
  rw [P.targetMap_mk, Q.targetMap_mk]
  apply (Submodule.Quotient.eq _).2
  change P.g (x : M) - Q.g (x : M) ∈ K.boundaries r (p - d)
  exact Submodule.mem_sup.mpr
    ⟨0, Submodule.zero_mem _, P.g (x : M) - Q.g (x : M),
      hPQ p (x : M) x.property, by simp⟩

theorem targetMapAtDrop_eq_of_sameSymbol {Q : K.PageOperator d}
    (hPQ : P.SameSymbol Q) (r : ℕ) (p : ℤ) :
    P.targetMapAtDrop r p = Q.targetMapAtDrop r p := by
  rw [P.targetMapAtDrop_eq_cast_targetMap,
    Q.targetMapAtDrop_eq_cast_targetMap,
    P.targetMap_eq_of_sameSymbol hPQ r (p + r)]


end PageOperator

end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
