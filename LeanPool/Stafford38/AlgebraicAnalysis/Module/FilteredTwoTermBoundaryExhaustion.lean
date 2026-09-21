/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalPages
import Mathlib.Algebra.DirectSum.Module

/-!
# Boundary exhaustion on the total target pages

The concrete boundary inclusions give maps from the first target page to every
later target page.  Surjectivity of the underlying differential and exhaustive
filtration imply pointwise eventual vanishing; finite support then gives the
same statement on the external direct sum.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

private theorem boundaries_one_le (r : ℕ) (p : ℤ) :
    K.boundaries 1 p ≤ K.boundaries (r + 1) p := by
  induction r with
  | zero => exact le_rfl
  | succ r ihr =>
      exact ihr.trans (K.boundaries_le_succ (r + 1) p)

private theorem boundaries_mono {a b : ℕ} (hab : a ≤ b) (p : ℤ) :
    K.boundaries a p ≤ K.boundaries b p := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih => exact ih.trans (K.boundaries_le_succ b p)

/-- The quotient map induced by `B₁ ⊆ B_{r+1}` at one target component. -/
def targetBoundaryMap (r : ℕ) (p : ℤ) :
    K.TargetPage 1 p →ₗ[k] K.TargetPage (r + 1) p :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    exact K.boundaries_one_le r p hx)

@[simp] theorem targetBoundaryMap_mk (r : ℕ) (p : ℤ) (x : K.G p) :
    K.targetBoundaryMap r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.mapQ_apply _ _ _ _

theorem targetBoundaryMap_surjective (r : ℕ) (p : ℤ) :
    Function.Surjective (K.targetBoundaryMap r p) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    ((K.boundaries (r + 1) p).comap (K.G p).subtype) y
  exact ⟨Submodule.Quotient.mk x, K.targetBoundaryMap_mk r p x⟩

/-- The component kernels grow with the page index. -/
theorem targetBoundaryMap_ker_mono (r s : ℕ) (hrs : r ≤ s) (p : ℤ) :
    LinearMap.ker (K.targetBoundaryMap r p) ≤
      LinearMap.ker (K.targetBoundaryMap s p) := by
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    ((K.boundaries 1 p).comap (K.G p).subtype) y
  change K.targetBoundaryMap r p (Submodule.Quotient.mk x) = 0 at hy
  change K.targetBoundaryMap s p (Submodule.Quotient.mk x) = 0
  rw [K.targetBoundaryMap_mk, Submodule.Quotient.mk_eq_zero] at hy ⊢
  have hpage : r + 1 ≤ s + 1 := by omega
  exact K.boundaries_mono hpage p hy

/-- The total target map into page `r+1`. -/
def totalBoundaryMap (r : ℕ) :
    K.TargetTotal 1 →ₗ[k] K.TargetTotal (r + 1) :=
  DirectSum.lmap (K.targetBoundaryMap r)

@[simp] theorem totalBoundaryMap_lof (r : ℕ) (p : ℤ)
    (x : K.TargetPage 1 p) :
    K.totalBoundaryMap r
        (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage 1 q) p x) =
      DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage (r + 1) q) p
        (K.targetBoundaryMap r p x) := by
  rw [totalBoundaryMap]
  exact DirectSum.lmap_of _ _ _

theorem totalBoundaryMap_surjective (r : ℕ) :
    Function.Surjective (K.totalBoundaryMap r) := by
  apply (DirectSum.lmap_surjective _).mpr
  exact K.targetBoundaryMap_surjective r

theorem totalBoundaryMap_ker_mono (r s : ℕ) (hrs : r ≤ s) :
    LinearMap.ker (K.totalBoundaryMap r) ≤
      LinearMap.ker (K.totalBoundaryMap s) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply DirectSum.ext_component k
  intro p
  have hlocal : K.targetBoundaryMap r p (x p) = 0 := by
    apply LinearMap.mem_ker.mp
    exact congrArg (fun z => z p) hx
  have hker := K.targetBoundaryMap_ker_mono r s hrs p
  exact LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hlocal))

private theorem pointwise_boundary_exhaustion
    (hG : ∀ z : M, ∃ s : ℤ, z ∈ K.G s)
    (hf : Function.Surjective K.f) (p : ℤ) (y : K.TargetPage 1 p) :
    ∃ r : ℕ, K.targetBoundaryMap r p y = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    ((K.boundaries 1 p).comap (K.G p).subtype) y
  obtain ⟨n, hn⟩ := K.exists_mem_boundaries_of_surjective hG hf x.property
  let r := n - 1
  have hnr : n ≤ r + 1 := by dsimp [r]; omega
  have hbound : K.boundaries n p ≤ K.boundaries (r + 1) p := by
    rcases n with _ | n
    · exact (K.boundaries_le_succ 0 p).trans (K.boundaries_one_le r p)
    · simpa [r] using le_rfl
  refine ⟨r, ?_⟩
  rw [K.targetBoundaryMap_mk, Submodule.Quotient.mk_eq_zero]
  exact hbound hn

/-- Every finitely supported total target vector is killed at some page. -/
theorem totalBoundaryMap_eventually_zero
    (hG : ∀ z : M, ∃ s : ℤ, z ∈ K.G s)
    (hf : Function.Surjective K.f) (x : K.TargetTotal 1) :
    ∃ r : ℕ, K.totalBoundaryMap r x = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of p y =>
      obtain ⟨r, hr⟩ := K.pointwise_boundary_exhaustion hG hf p y
      refine ⟨r, ?_⟩
      rw [show DirectSum.of _ p y =
        DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage 1 q) p y from rfl,
        K.totalBoundaryMap_lof, hr]
      simp
  | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      let t := max r s
      refine ⟨t, ?_⟩
      have hrt : r ≤ t := le_max_left _ _
      have hst : s ≤ t := le_max_right _ _
      have hxr := K.totalBoundaryMap_ker_mono r t hrt (LinearMap.mem_ker.mpr hr)
      have hys := K.totalBoundaryMap_ker_mono s t hst (LinearMap.mem_ker.mpr hs)
      rw [map_add]
      rw [LinearMap.mem_ker.mp hxr, LinearMap.mem_ker.mp hys, add_zero]


end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
