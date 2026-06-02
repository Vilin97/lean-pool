/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.InvariantSubmodule
import LeanPool.Monlib4.LinearAlgebra.Ips.Basic
import LeanPool.Monlib4.LinearAlgebra.Ips.Ips
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import LeanPool.Monlib4.LinearAlgebra.Ips.MinimalProj
import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne

/-!

# A bit on von Neumann algebras

This file contains two simple results about von Neumann algebras.

-/


namespace VonNeumannAlgebra

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma star_commutant_iff {M : VonNeumannAlgebra H} {e : H →L[ℂ] H} :
  star e ∈ M.commutant ↔ e ∈ M.commutant :=
by
  simp only [mem_commutant_iff]
  constructor
  · rintro h g hg
    have : star g ∈ M := by aesop
    specialize h (star g) this
    simp_rw [← star_mul, star_inj] at h
    exact h.symm
  · rintro h g hg
    have : star g ∈ M := by aesop
    specialize h (star g) this
    rw [← star_star g]
    simp_rw [← star_mul, h]

/-- a continuous linear map `e` is in the von Neumann algebra `M`
if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem elem_idempotent_iff_ker_and_range_invariantUnder_commutant (M : VonNeumannAlgebra H)
    (e : H →L[ℂ] H) (h : IsIdempotentElem e) :
    e ∈ M ↔ ∀ y : H →L[ℂ] H, y ∈ M.commutant →
      (LinearMap.ker e.toLinearMap).InvariantUnder y.toLinearMap ∧
        (LinearMap.range e.toLinearMap).InvariantUnder y.toLinearMap :=
  by
  simp_rw [Submodule.invariantUnder_iff, Set.subset_def,
    ContinuousLinearMap.coe_coe, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro he y hy
    have : e.comp y = y.comp e :=
      by
      rw [← VonNeumannAlgebra.commutant_commutant M, VonNeumannAlgebra.mem_commutant_iff] at he
      exact (he y hy).symm
    exact
      ⟨fun x hx => by
        have hxy := congrArg (fun f : H →L[ℂ] H => f x) this
        change e (y x) = y (e x) at hxy
        change e x = 0 at hx
        change e (y x) = 0
        rw [hxy, hx, map_zero],
      fun u ⟨v, hv⟩ => by
        refine ⟨y v, ?_⟩
        have hxy := congrArg (fun f : H →L[ℂ] H => f v) this
        change e (y v) = y (e v) at hxy
        change e v = u at hv
        change e (y v) = y u
        rw [hxy, hv]⟩
  · intro H'
    rw [← VonNeumannAlgebra.commutant_commutant M]
    intro m hm; ext x
    obtain ⟨v, w, hvw, _⟩ :=
      Submodule.existsUnique_add_of_isCompl
        (IsIdempotentElem.isCompl_range_ker (IsIdempotentElem.clm_to_lm.mp h)) x
    obtain ⟨y, hy⟩ := SetLike.coe_mem w
    simp_rw [ContinuousLinearMap.coe_coe] at hy
    simp_rw [Set.mem_union, Set.mem_star, SetLike.mem_coe,
      star_commutant_iff, or_self] at hm
    have hv_ker : e (v : H) = 0 := LinearMap.map_coe_ker e.toLinearMap v
    have hw_fixed : e (w : H) = w := by
      rw [← hy, ← ContinuousLinearMap.mul_apply e e, IsIdempotentElem.eq h, hy]
    have hmv_ker : e (m (v : H)) = 0 := (H' m hm).1 (v : H) hv_ker
    have hmw_fixed : e (m (w : H)) = m w := by
      obtain ⟨p, hp⟩ := (H' m hm).2 (w : H) ⟨y, hy⟩
      rw [← hp]
      change (e * e) p = e p
      rw [IsIdempotentElem.eq h]
    calc
      (m * e) x = m (e ((v : H) + w)) := by
        rw [← hvw]
        rfl
      _ = m (w : H) := by
        rw [map_add, hv_ker, hw_fixed, zero_add]
      _ = e (m ((v : H) + w)) := by
        rw [map_add, map_add, hmv_ker, hmw_fixed, zero_add]
      _ = (e * m) x := by
        rw [hvw]
        rfl

/-- The algebra of all bounded linear operators on a Hilbert space as a von Neumann algebra. -/
def ofHilbertSpace : VonNeumannAlgebra H
    where
  carrier := Set.univ
  mul_mem' _ _ := Set.mem_univ _
  add_mem' _ _ := Set.mem_univ _
  star_mem' _ := Set.mem_univ _
  algebraMap_mem' _ := Set.mem_univ _
  centralizer_centralizer' := ContinuousLinearMap.centralizer_centralizer

end VonNeumannAlgebra
