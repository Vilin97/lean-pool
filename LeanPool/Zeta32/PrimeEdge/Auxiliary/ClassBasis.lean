/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Arith.Local.Entry
public import LeanPool.Zeta5Irrational.Arith.Unimodular

/-! Generic CRT product-basis independence and the unimodularity criterion,
Generic independence lemmas reuse LeanPool.Zeta5Irrational; the determinant adapter was
copied from Li₂ `Li2Unified/Modular/Base/ClassBasis.lean` (itself adapted from
Apery/Arith/Unimodular.lean in mo271/Zeta5 by Moritz Firsching (https://github.com/mo271/Zeta5,
commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741), Apache-2.0), restated for
`Zeta32.Arith.Local.coeffMat`. -/

public section

open Finset Polynomial

namespace Zeta32.PrimeEdge.Auxiliary

open Zeta32.Arith.Local

export Zeta5Irrational (sum_pow_X_sub_C_eq_zero classBasis_independent)

/-- A polynomial family independent modulo `p` has a `p`-unit coefficient determinant. -/
theorem coeffMat_det_unit_of_independent {h p : ℕ} [hp : Fact p.Prime]
    (Ez : Fin h → ℤ[X]) (hdeg : ∀ a, (Ez a).natDegree < h)
    (hind : ∀ v : Fin h → ZMod p,
      (∑ a, C (v a) * (Ez a).map (Int.castRingHom (ZMod p))) = 0 → v = 0) :
    (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det ≠ 0 ∧
      padicValRat p (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det = 0 := by
  set Mz : Matrix (Fin h) (Fin h) ℤ := fun a k => (Ez a).coeff k with hMz
  have hQ : coeffMat (fun a => (Ez a).map (Int.castRingHom ℚ)) = Mz.map (Int.castRingHom ℚ) := by
    ext a k
    simp [coeffMat, Zeta5Irrational.coeffMat, hMz, coeff_map, Matrix.map, Matrix.of_apply]
  have hdetQ : (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det = (Mz.det : ℚ) := by
    rw [hQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp
  have hdetP : (Mz.det : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (Mz.map (Int.castRingHom (ZMod p))).transpose.det = 0 := by
      rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
    apply hv0
    apply hind v
    ext k
    rw [finsetSum_coeff, coeff_zero]
    simp only [coeff_C_mul, coeff_map]
    by_cases hk : k < h
    · have ht := congrFun hv ⟨k, hk⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hMz, Pi.zero_apply] at ht
      rw [← ht]
      apply Finset.sum_congr rfl
      intro a _
      simp [Matrix.map, Matrix.of_apply, mul_comm]
    · apply Finset.sum_eq_zero
      intro a _
      rw [coeff_eq_zero_of_natDegree_lt (by have := hdeg a; omega)]
      simp
  have hndvd : ¬(p:ℤ) ∣ Mz.det :=
    fun h => hdetP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  rw [hdetQ]
  constructor
  · intro h
    have hz : Mz.det = 0 := by exact_mod_cast h
    exact hndvd (hz ▸ dvd_zero _)
  · rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hndvd]
    rfl

end Zeta32.PrimeEdge.Auxiliary

end
