/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ZeroSumAlgebra
/-! # Mean/deviation decomposition -/
namespace NRR
open scoped BigOperators
variable {n : ℕ}

noncomputable def coordinateMean (hn : 0 < n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := (∑ i, v i) / (n : ℝ)
  map_add' u v := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

@[simp] theorem coordinateMean_apply (hn : 0 < n) (v : Fin n → ℝ) :
    coordinateMean hn v = (∑ i, v i) / (n : ℝ) := rfl

noncomputable def coordinateDeviation (hn : 0 < n) :
    (Fin n → ℝ) →ₗ[ℝ] ZeroSum n where
  toFun v := ⟨fun i => v i - coordinateMean hn v, by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, coordinateMean_apply]
    field_simp
    ring⟩
  map_add' u v := by
    apply ZeroSum.ext
    intro i
    change u i + v i - coordinateMean hn (u + v) =
      (u i - coordinateMean hn u) + (v i - coordinateMean hn v)
    rw [map_add]
    ring
  map_smul' c v := by
    apply ZeroSum.ext
    intro i
    change c * v i - coordinateMean hn (c • v) =
      c * (v i - coordinateMean hn v)
    rw [map_smul]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem coordinateDeviation_apply
    (hn : 0 < n) (v : Fin n → ℝ) (i : Fin n) :
    coordinateDeviation hn v i = v i - coordinateMean hn v := by
      rfl

/-- Reconstruct coordinates from a zero-sum vector and a constant. -/
def reconstructCoordinates (n : ℕ) :
    ZeroSum n × ℝ →ₗ[ℝ] (Fin n → ℝ) where
  toFun z i := z.1 i + z.2
  map_add' u v := by funext i; simp [add_assoc, add_left_comm, add_comm]
  map_smul' c v := by funext i; simp [mul_add]

@[simp] theorem reconstructCoordinates_apply
    (u : ZeroSum n) (c : ℝ) (i : Fin n) :
    reconstructCoordinates n (u, c) i = u i + c := rfl

@[simp] theorem coordinateMean_reconstruct
    (hn : 0 < n) (u : ZeroSum n) (c : ℝ) :
    coordinateMean hn (reconstructCoordinates n (u, c)) = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [coordinateMean_apply]
  simp only [reconstructCoordinates_apply, Finset.sum_add_distrib,
    u.sum_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, zero_add]
  field_simp

@[simp] theorem coordinateDeviation_reconstruct
    (hn : 0 < n) (u : ZeroSum n) (c : ℝ) :
    coordinateDeviation hn (reconstructCoordinates n (u, c)) = u := by
  apply ZeroSum.ext
  intro i
  rw [coordinateDeviation_apply, coordinateMean_reconstruct,
    reconstructCoordinates_apply]
  ring

noncomputable def coordinateDecomposition (hn : 0 < n) :
    (Fin n → ℝ) ≃ₗ[ℝ] ZeroSum n × ℝ where
  toFun v := (coordinateDeviation hn v, coordinateMean hn v)
  invFun := reconstructCoordinates n
  left_inv v := by
    funext i
    rw [reconstructCoordinates_apply, coordinateDeviation_apply]
    ring
  right_inv z := by
    rcases z with ⟨u, c⟩
    apply Prod.ext
    · exact coordinateDeviation_reconstruct hn u c
    · exact coordinateMean_reconstruct hn u c
  map_add' u v := by
    apply Prod.ext
    · exact map_add (coordinateDeviation hn) u v
    · exact map_add (coordinateMean hn) u v
  map_smul' c v := by
    apply Prod.ext
    · exact map_smul (coordinateDeviation hn) c v
    · exact map_smul (coordinateMean hn) c v

/-- A coordinate vector vanishes iff both its deviation and mean vanish. -/
theorem coordinate_eq_zero_iff (hn : 0 < n) (v : Fin n → ℝ) :
    v = 0 ↔ coordinateDeviation hn v = 0 ∧ coordinateMean hn v = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero (coordinateDeviation hn), map_zero (coordinateMean hn)⟩
  · rintro ⟨hdev, hmean⟩
    apply (coordinateDecomposition hn).injective
    change (coordinateDeviation hn v, coordinateMean hn v) =
      (coordinateDeviation hn 0, coordinateMean hn 0)
    rw [hdev, hmean, map_zero, map_zero]

/-- Permutations preserve the coordinate mean. -/
theorem coordinateMean_relabel
    (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ) :
    coordinateMean hn (fun i => v (σ.symm i)) = coordinateMean hn v := by
  rw [coordinateMean_apply, coordinateMean_apply, Equiv.sum_comp]

/-- Mean subtraction commutes with relabelling. -/
theorem coordinateDeviation_relabel
    (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ) :
    coordinateDeviation hn (fun i => v (σ.symm i)) =
      ZeroSum.relabel σ (coordinateDeviation hn v) := by
  apply ZeroSum.ext
  intro i
  rw [coordinateDeviation_apply, ZeroSum.relabel_apply,
    coordinateDeviation_apply, coordinateMean_relabel]

end NRR
