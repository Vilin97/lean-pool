/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.CoordinateDecomposition
/-!
# Prime symmetry subgroup

For two labels the symmetry group is the full permutation group; for every other number of labels
it is the alternating group. The prime configuration model uses this construction at prime cardinality.
-/

namespace NRR

open Equiv

variable {p : ℕ}

/-- The permutation subgroup used for prime symmetry: all permutations for two labels and even
permutations otherwise. -/
def primeSymmetrySubgroup (p : ℕ) :
    Subgroup (Equiv.Perm (Fin p)) := by
  classical
  exact if p = 2 then ⊤ else alternatingGroup (Fin p)

/-- The group of prime symmetries acting on the labelled coordinates. -/
abbrev PrimeSymmetry (p : ℕ) := primeSymmetrySubgroup p

/-- Faithful inclusion of the selected subgroup into all label permutations. -/
def PrimeSymmetry.toPerm (p : ℕ) :
    PrimeSymmetry p →* Equiv.Perm (Fin p) :=
  (primeSymmetrySubgroup p).subtype


@[simp] theorem PrimeSymmetry.toPerm_apply
    (p : ℕ) (g : PrimeSymmetry p) :
    PrimeSymmetry.toPerm p g = (g : Equiv.Perm (Fin p)) := rfl

 theorem PrimeSymmetry.toPerm_injective (p : ℕ) :
    Function.Injective (PrimeSymmetry.toPerm p) :=
  (primeSymmetrySubgroup p).subtype_injective

 theorem primeSymmetrySubgroup_eq_top
    (p : ℕ) (h2 : p = 2) :
    primeSymmetrySubgroup p = ⊤ := by
  classical
  simp [primeSymmetrySubgroup, h2]

 theorem primeSymmetrySubgroup_eq_alternating
    (p : ℕ) (h2 : p ≠ 2) :
    primeSymmetrySubgroup p = alternatingGroup (Fin p) := by
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
    ∃ g : PrimeSymmetry p, (PrimeSymmetry.toPerm p g) i = j := by
  classical
  by_cases h2 : p = 2
  · by_cases hij : i = j
    · refine ⟨1, ?_⟩
      simpa [hij]
    · let σ : Equiv.Perm (Fin p) := Equiv.swap i j
      have hmem : σ ∈ primeSymmetrySubgroup p := by
        rw [primeSymmetrySubgroup_eq_top p h2]
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
      have hmem : σ ∈ primeSymmetrySubgroup p := by
        rw [primeSymmetrySubgroup_eq_alternating p h2]
        exact hσalt
      refine ⟨⟨σ, hmem⟩, ?_⟩
      simp [σ, hki, hki.symm, hkj, hij]

end NRR
