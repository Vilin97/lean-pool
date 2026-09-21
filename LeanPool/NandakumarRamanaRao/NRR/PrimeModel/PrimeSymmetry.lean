/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.CoordinateDecomposition
/-!
# Prime symmetry subgroup

For two labels the symmetry group is the full permutation group. For an odd prime number of labels
it is the alternating group. This is the symmetry used by the prime configuration model.
-/

namespace NRR

open Equiv

variable {p : ℕ}

def primeSymmetrySubgroup (hp : Nat.Prime p) :
    Subgroup (Equiv.Perm (Fin p)) := by
  classical
  exact if p = 2 then ⊤ else alternatingGroup (Fin p)

abbrev PrimeSymmetry (hp : Nat.Prime p) := primeSymmetrySubgroup hp

/-- Faithful inclusion of the selected subgroup into all label permutations. -/
def PrimeSymmetry.toPerm (hp : Nat.Prime p) :
    PrimeSymmetry hp →* Equiv.Perm (Fin p) :=
  (primeSymmetrySubgroup hp).subtype


@[simp] theorem PrimeSymmetry.toPerm_apply
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) :
    PrimeSymmetry.toPerm hp g = (g : Equiv.Perm (Fin p)) := rfl

 theorem PrimeSymmetry.toPerm_injective (hp : Nat.Prime p) :
    Function.Injective (PrimeSymmetry.toPerm hp) :=
  (primeSymmetrySubgroup hp).subtype_injective

 theorem primeSymmetrySubgroup_eq_top
    (hp : Nat.Prime p) (h2 : p = 2) :
    primeSymmetrySubgroup hp = ⊤ := by
  classical
  simp [primeSymmetrySubgroup, h2]

 theorem primeSymmetrySubgroup_eq_alternating
    (hp : Nat.Prime p) (h2 : p ≠ 2) :
    primeSymmetrySubgroup hp = alternatingGroup (Fin p) := by
  classical
  simp [primeSymmetrySubgroup, h2]

private theorem exists_third_label
    (hp : Nat.Prime p) (h2 : p ≠ 2)
    (i j : Fin p) (hij : i ≠ j) :
    ∃ k : Fin p, k ≠ i ∧ k ≠ j := by
  classical
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  let s : Finset (Fin p) := (Finset.univ.erase i).erase j
  have hi : i ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin p)) := by
    simp [hij.symm]
  have hspos : 0 < s.card := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hspos
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  exact ⟨k, hki, hkj⟩

/-- The chosen prime symmetry group acts transitively on the labels. -/
theorem PrimeSymmetry.exists_map_label
    (hp : Nat.Prime p) (i j : Fin p) :
    ∃ g : PrimeSymmetry hp, (PrimeSymmetry.toPerm hp g) i = j := by
  classical
  by_cases h2 : p = 2
  · by_cases hij : i = j
    · refine ⟨1, ?_⟩
      simpa [hij]
    · let σ : Equiv.Perm (Fin p) := Equiv.swap i j
      have hmem : σ ∈ primeSymmetrySubgroup hp := by
        rw [primeSymmetrySubgroup_eq_top hp h2]
        trivial
      refine ⟨⟨σ, hmem⟩, ?_⟩
      simp [σ, hij]
  · by_cases hij : i = j
    · refine ⟨1, ?_⟩
      simpa [hij]
    · obtain ⟨k, hki, hkj⟩ := exists_third_label hp h2 i j hij
      let σ : Equiv.Perm (Fin p) := Equiv.swap k j * Equiv.swap i k
      have hσalt : σ ∈ alternatingGroup (Fin p) := by
        apply Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        · exact ⟨k, j, hkj, rfl⟩
        · exact ⟨i, k, hki.symm, rfl⟩
      have hmem : σ ∈ primeSymmetrySubgroup hp := by
        rw [primeSymmetrySubgroup_eq_alternating hp h2]
        exact hσalt
      refine ⟨⟨σ, hmem⟩, ?_⟩
      simp [σ, hki, hki.symm, hkj, hij]

end NRR
