/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
/-!
# Cardinal consequences of a Herbrand quotient

This file isolates the elementary cardinal arithmetic at the end of the
low-degree Herbrand quotient calculation.  If a finite low-degree Tate quotient has Herbrand
quotient equal to a natural number `n`, then its degree-zero cardinality is
`n` times its negative-first cardinality.  In particular the degree-zero
cardinality is at least `n`.
-/

@[expose] public section

noncomputable
section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} {A : Type uA}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

/-- Clearing the nonzero denominator in a Herbrand quotient whose value is
a natural number. -/
theorem herbrandH0_card_eq_mul_herbrandHMinusOne_card
    (σ : G) (n : ℕ)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n) :
    Nat.card (HerbrandH0 G A) =
      n * Nat.card
        (HerbrandHMinusOne G A σ) := by
  rw [herbrandQuotient_eq_card_ratio] at hquotient
  have hden :
      ((Nat.card
          (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos
        (α := HerbrandHMinusOne G A σ)).ne'
  have hrat :
      (Nat.card (HerbrandH0 G A) : ℚ) =
        (n : ℚ) *
          Nat.card
            (HerbrandHMinusOne G A σ) :=
    (div_eq_iff hden).mp hquotient
  exact_mod_cast hrat

/-- Cardinal-arithmetic step for low-degree Herbrand cohomology: a natural-valued Herbrand quotient
is a lower bound for the degree-zero Tate quotient. -/
theorem le_herbrandH0_card_of_herbrandQuotient_eq_nat
    (σ : G) (n : ℕ)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n) :
    n ≤ Nat.card (HerbrandH0 G A) := by
  rw [herbrandH0_card_eq_mul_herbrandHMinusOne_card
    σ n hquotient]
  calc
    n = n * 1 := by simp
    _ ≤ n *
        Nat.card
          (HerbrandHMinusOne G A σ) :=
      Nat.mul_le_mul_left n
        (Finite.card_pos
          (α := HerbrandHMinusOne G A σ))

/-- If the degree-zero cardinality is also bounded above by the natural
value of the Herbrand quotient, both low-degree cardinalities are forced:
`#H⁰ = n` and `#H⁻¹ = 1`. -/
theorem lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le
    (σ : G) (n : ℕ) (hn : 0 < n)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n)
    (hle : Nat.card (HerbrandH0 G A) ≤ n) :
    Nat.card (HerbrandH0 G A) = n ∧
      Nat.card (HerbrandHMinusOne G A σ) = 1 := by
  let a := Nat.card (HerbrandH0 G A)
  let b := Nat.card (HerbrandHMinusOne G A σ)
  have hmul : a = n * b :=
    herbrandH0_card_eq_mul_herbrandHMinusOne_card
      σ n hquotient
  have hb : 1 ≤ b :=
    Finite.card_pos
      (α := HerbrandHMinusOne G A σ)
  have hnle : n ≤ a := by
    rw [hmul]
    simpa using Nat.mul_le_mul_left n hb
  have ha : a = n :=
    Nat.le_antisymm hle hnle
  refine ⟨ha, ?_⟩
  have hcancel : n * b = n * 1 := by
    rw [← hmul, ha, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hn hcancel

/-- Subsingleton form of the negative-first conclusion. -/
theorem herbrandHMinusOne_subsingleton_of_herbrandQuotient_eq_nat_of_le
    (σ : G) (n : ℕ) (hn : 0 < n)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n)
    (hle : Nat.card (HerbrandH0 G A) ≤ n) :
    Subsingleton (HerbrandHMinusOne G A σ) := by
  have hcard :
      Nat.card (HerbrandHMinusOne G A σ) = 1 := by
    exact
      (lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le
        σ n hn hquotient hle).2
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

end CyclicCohomology
