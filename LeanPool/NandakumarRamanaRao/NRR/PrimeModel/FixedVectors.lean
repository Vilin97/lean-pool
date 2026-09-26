/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Actions

/-!
# Fixed-vector rigidity

Transitivity of the label action forces fixed coordinate vectors to be constant. Intersecting this
fixed subspace with the zero-sum representation leaves only the origin.
-/

@[expose] public section

namespace NRR

variable {p : ℕ}

theorem PrimeSymmetry.coordinate_fixed_constant
    (hp : Nat.Prime p) (v : Fin p → ℝ)
    (hfix : ∀ g : PrimeSymmetry p, g • v = v) :
    ∀ i j, v i = v j := by
  intro i j
  obtain ⟨g, hg⟩ := PrimeSymmetry.exists_map_label hp j i
  have h := congrFun (hfix g) i
  have hsymm : (PrimeSymmetry.toPerm p g).symm i = j := by
    exact (PrimeSymmetry.toPerm p g).symm_apply_eq.mpr hg.symm
  rw [PrimeSymmetry.smul_coordinate_apply, hsymm] at h
  exact h.symm

theorem PrimeSymmetry.coordinate_fixed_iff_constant
    (hp : Nat.Prime p) (v : Fin p → ℝ) :
    (∀ g : PrimeSymmetry p, g • v = v) ↔
      ∃ c : ℝ, v = fun _ => c := by
  constructor
  · intro h
    let i0 : Fin p := ⟨0, hp.pos⟩
    refine ⟨v i0, ?_⟩
    funext i
    exact PrimeSymmetry.coordinate_fixed_constant hp v h i i0
  · rintro ⟨c, rfl⟩ g
    funext i
    rfl

theorem PrimeSymmetry.zeroSum_fixed_eq_zero
    (hp : Nat.Prime p) (v : ZeroSum p)
    (hfix : ∀ g : PrimeSymmetry p, g • v = v) :
    v = 0 := by
  have hconst : ∀ i j, v i = v j := by
    apply PrimeSymmetry.coordinate_fixed_constant hp (fun i => v i)
    intro g
    funext i
    simpa [PrimeSymmetry.smul_coordinate_apply,
      PrimeSymmetry.smul_zeroSum_apply] using
      congrArg (fun w : ZeroSum p => w i) (hfix g)
  let i0 : Fin p := ⟨0, hp.pos⟩
  have hsum : (p : ℝ) * v i0 = 0 := by
    calc
      (p : ℝ) * v i0 = ∑ _i : Fin p, v i0 := by simp
      _ = ∑ i : Fin p, v i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hconst i i0).symm
      _ = 0 := v.sum_coe
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hi0 : v i0 = 0 := by
    exact (mul_eq_zero.mp hsum).resolve_left hp0
  apply ZeroSum.ext
  intro i
  calc
    v i = v i0 := hconst i i0
    _ = 0 := hi0
    _ = (0 : ZeroSum p) i := (ZeroSum.zero_apply i).symm

theorem coordinateMean_prime_smul
    (p : Nat) (v : Fin p → ℝ) (g : PrimeSymmetry p) :
    coordinateMean p (g • v) = coordinateMean p v :=
  coordinateMean_relabel p (PrimeSymmetry.toPerm p g) v

theorem coordinateDeviation_prime_smul
    (hp : Nat.Prime p) (v : Fin p → ℝ) (g : PrimeSymmetry p) :
    coordinateDeviation hp.pos (g • v) = g • coordinateDeviation hp.pos v :=
  coordinateDeviation_relabel hp.pos (PrimeSymmetry.toPerm p g) v

end NRR
