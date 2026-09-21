/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Relative
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeCompletion
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Prescribed quotient counts

The integer coefficients give a natural multiplicity on the quotient.
For a zero-dimensional fibre, this already proves relative expansion.
-/

open scoped BigOperators

namespace EGZ.Expansion

theorem mod_injective_on_support {p r K : ℕ} [NeZero p]
    (S : Finset (IntCoord r)) (hbox : ∀ q ∈ S, latticeSupNorm q ≤ K) (hKp : 2 * K < p) :
    Function.Injective (fun q : S ↦ q.val.mod p) := by
  intro q z hqz
  apply Subtype.ext
  apply IsCenteredLift.eq_of_mod_eq (p := p) _ _ hqz
  · exact (hbox q q.property).trans (by omega)
  · exact (hbox z z.property).trans (by omega)

theorem pushWeight_le_of_injective {A B : Type*} [Fintype A]
    (f : A → B) (hf : Function.Injective f) (u : A → ℕ) (w : B → ℕ)
    (hu : ∀ a, u a ≤ w (f a)) : pushWeight f u ≤ w := by
  classical
  intro b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    simpa [pushWeight, hf.eq_iff] using hu a
  · have hz : pushWeight f u b = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun h ↦ hb ⟨a, h⟩)
    rw [hz]
    exact Nat.zero_le _

theorem prescribed_quotient_counts {p r t K : ℕ} [NeZero p]
    (S : Finset (IntCoord r)) (w : FpCoord p (r + t) → ℕ) (α : S → ℤ)
    (hbox : ∀ q ∈ S, latticeSupNorm q ≤ K) (hKp : 2 * K < p)
    (hz : (∑ q : S, α q • q.val) = 0) (hm : (∑ q : S, α q) = (p : ℤ))
    (ha : ∀ q : S, 0 ≤ α q ∧ α q ≤ (pushWeight (Coord.first r t) w (q.val.mod p) : ℤ)) :
    ∃ a : FpCoord p r → ℕ,
      a ≤ pushWeight (Coord.first r t) w ∧ natMass a = p ∧ vectorSum a = 0 := by
  classical
  let a : S → ℕ := fun q ↦ (α q).toNat
  have haZ (q : S) : (a q : ℤ) = α q := Int.toNat_of_nonneg (ha q).1
  refine ⟨pushWeight (fun q : S ↦ q.val.mod p) a, ?_, ?_, ?_⟩
  · apply pushWeight_le_of_injective _ (mod_injective_on_support S hbox hKp)
    intro q
    have hh := (ha q).2
    rw [← haZ] at hh
    exact_mod_cast hh
  · rw [natMass_pushWeight]
    change (∑ q, a q) = p
    have hh : (∑ q, (a q : ℤ)) = (p : ℤ) := by simpa only [haZ] using hm
    exact_mod_cast hh
  · rw [vectorSum, sum_pushWeight]
    ext i
    have hh := congrFun hz i
    simp only [Finset.sum_apply, zsmul_eq_mul, Pi.zero_apply] at hh
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod p)) hh
    simpa [Finset.sum_apply, IntCoord.mod, nsmul_eq_mul,
      Pi.mul_apply, ← haZ] using hcast

theorem relativeExpansionAt_zero_fibre {p r K T : ℕ} [NeZero p] {δ : ℝ}
    (hδ : 0 < δ) (hKp : 2 * K < p) : RelativeExpansionAt r 0 K δ T p := by
  intro S w α hbox _hs hz hm ha _hthick
  have ha' (q : S) : 0 ≤ α q ∧ α q ≤ (pushWeight (Coord.first r 0) w (q.val.mod p) : ℤ) := by
    have hh := ha q
    have hδp : 0 ≤ δ * (p : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg p)
    constructor
    · exact_mod_cast hδp.trans hh.1
    · have hle : (α q : ℝ) ≤ pushWeight (Coord.first r 0) w (q.val.mod p) := by linarith
      exact_mod_cast hle
  obtain ⟨a, hale, ham, haz⟩ := prescribed_quotient_counts S w α hbox hKp hz hm ha'
  obtain ⟨u, hu, hua⟩ := exists_subweight_pushWeight (Coord.first r 0) w a hale
  refine ⟨u, hu, ?_, ?_⟩
  · rw [← natMass_pushWeight (Coord.first r 0) u, hua, ham]
  · apply Coord.ext_first_last (m := r) (k := 0)
    · have hh := map_vectorSum (Coord.first r 0).toAddMonoidHom u
      change Coord.first r 0 (vectorSum u) = vectorSum (pushWeight (Coord.first r 0) u) at hh
      rw [hua, haz] at hh
      simpa only [map_zero, vectorSum] using hh
    · exact Subsingleton.elim _ _

end EGZ.Expansion
