/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
/-!
# Density of torsion in the finite profinite-unit factor
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory

open LocalFieldTheory.Padic

/-- The torsion elements are dense in an arbitrary product of finite
commutative groups. -/
theorem dense_torsion_pi_of_finite
    {ι : Type*} (G : ι → Type*)
    [(i : ι) → CommGroup (G i)]
    [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → Finite (G i)] :
    Dense
      (CommGroup.torsion ((i : ι) → G i) :
        Set ((i : ι) → G i)) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨S, u, hu, hSu⟩ :=
    isOpen_pi_iff.mp hU x hx
  let y : (i : ι) → G i :=
    fun i => if hi : i ∈ S then x i else 1
  refine ⟨y, hSu ?_, ?_⟩
  · intro i hi
    have hiS : i ∈ S := hi
    change (if _ : i ∈ S then x i else 1) ∈ u i
    simp only [hiS, ↓reduceDIte]
    exact (hu i hi).2
  · change IsOfFinOrder y
    let N := ∏ i ∈ S, orderOf (x i)
    have hN : 0 < N := by
      dsimp only [N]
      exact Finset.prod_pos fun i _ => orderOf_pos (x i)
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨N, hN, ?_⟩
    funext i
    by_cases hi : i ∈ S
    · rw [Pi.pow_apply]
      dsimp only [y]
      rw [dite_eq_left hi]
      exact orderOf_dvd_iff_pow_eq_one.mp
        (Finset.dvd_prod_of_mem
          (fun j => orderOf (x j)) hi)
    · simp [y, hi]

/-- The torsion subgroup of the finite cyclotomic factor is dense. -/
theorem dense_torsion_cyclotomicFinitePart :
    Dense
      (CommGroup.torsion CyclotomicFinitePart :
        Set CyclotomicFinitePart) :=
  dense_torsion_pi_of_finite
    (fun p : Nat.Primes => padicUnitFiniteFactor p.1)

end KummerTheory
