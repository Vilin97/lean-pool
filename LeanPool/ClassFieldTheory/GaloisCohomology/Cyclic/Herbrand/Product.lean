/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
/-!
# Herbrand quotients of finite products

This file extracts the cardinality consequence of the product
decompositions of low-degree Tate cohomology, giving the corresponding
product formula for Herbrand quotients.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]
variable (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

local instance :
    MulDistribMulAction G (∀ i, A i) :=
  piMulDistribMulAction G A

/-- The Herbrand quotient of a finite dependent product is the product of
the component Herbrand quotients. -/
theorem herbrandQuotient_pi
    (σ : G)
    [∀ i, Finite (HerbrandH0 G (A i))]
    [∀ i, Finite (HerbrandHMinusOne G (A i) σ)] :
    letI : Finite (HerbrandH0 G (∀ i, A i)) :=
      Finite.of_equiv
        (∀ i, HerbrandH0 G (A i))
        (herbrandH0PiEquiv (G := G) A).symm.toEquiv
    letI : Finite (HerbrandHMinusOne G (∀ i, A i) σ) :=
      Finite.of_equiv
        (∀ i, HerbrandHMinusOne G (A i) σ)
        (herbrandHMinusOnePiEquiv
          (G := G) A σ).symm.toEquiv
    herbrandQuotient (G := G) (A := ∀ i, A i) σ =
      ∏ i, herbrandQuotient (G := G) (A := A i) σ := by
  let : Finite (HerbrandH0 G (∀ i, A i)) :=
    Finite.of_equiv
      (∀ i, HerbrandH0 G (A i))
      (herbrandH0PiEquiv (G := G) A).symm.toEquiv
  let : Finite (HerbrandHMinusOne G (∀ i, A i) σ) :=
    Finite.of_equiv
      (∀ i, HerbrandHMinusOne G (A i) σ)
      (herbrandHMinusOnePiEquiv
        (G := G) A σ).symm.toEquiv
  unfold herbrandQuotient
  rw [Nat.card_congr
      (herbrandH0PiEquiv (G := G) A).toEquiv,
    Nat.card_congr
      (herbrandHMinusOnePiEquiv
        (G := G) A σ).toEquiv,
    Nat.card_pi, Nat.card_pi]
  simp only [Nat.cast_prod]
  simpa only [Finset.mem_univ, Finset.prod_const_one,
    Finset.prod_filter, true_and] using
    (Finset.prod_div_distrib
      (s := Finset.univ)
      (fun i : ι ↦
        (Nat.card (HerbrandH0 G (A i)) : ℚ))
      (fun i : ι ↦
        (Nat.card
          (HerbrandHMinusOne G (A i) σ) : ℚ))).symm

end CyclicCohomology
