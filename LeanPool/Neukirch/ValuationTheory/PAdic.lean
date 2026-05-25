/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeiBichang
-/

/-
GOAL : Prove `aux1`, i.e., find `y n ∈ ℤ/p^n` forming an inverse limit s.t. `F (y n) = 0`.

-/
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.WellKnown


-- The universal property of `ℤ_[p]` as projective limit.
#check PadicInt.lift_unique
#check PadicInt.lift_spec

noncomputable section Prop_1_4_weaker

open Polynomial PadicInt

variable {p : ℕ} [Fact p.Prime]
variable {F : ℤ[X]}
variable {x0 : ℕ → ℤ}


def indexes_cong (x : ℕ → ℤ) (a : ℤ) (M : ℕ) : sorry := sorry

def x
  (hx0 : ∀n : ℕ, F.eval₂ (Int.castRingHom (ZMod (p ^ n))) (x0 n) = 0)
: ℕ → ℕ → ℤ := fun
    | .zero => x0
    | .succ n => by
      let i : ℕ → ℕ := sorry
      sorry

def cpt_sol
    (h : ∀n : ℕ, ∃x : ZMod (p ^ n),
    F.eval₂ (Int.castRingHom (ZMod (p ^ n))) x = 0)
    (n : ℕ) : ZMod (p ^ n) := sorry

-- Given a series of solutions `mod p^n`, there is a series of compatible solutions `mod p^n`.
lemma aux1
    (h : ∀n : ℕ, ∃x : ZMod (p ^ n),
      F.eval₂ (Int.castRingHom (ZMod (p ^ n))) x = 0)
: ∃y : (n : ℕ) → ZMod (p ^ n), (
      ∀n : ℕ,
        F.eval₂ (Int.castRingHom (ZMod (p ^ n))) (y n) = 0
    ) ∧ (
      ∀(m n : ℕ) (mlen : m ≤ n),
        ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m)) (y n) = y m
    ) := by
  -- revert h
  sorry

example (m n : ℕ) (mlen : m ≤ n) : p^m ∣ p^n := pow_dvd_pow p mlen

-- A ring homomorphism `ℤ[X] → R` is determined by its value on `X`.
theorem Polynomial.ringHom_ext_Z {R : Type _} [Semiring R] {f g : Polynomial ℤ →+* R} (h : f X = g X) : f = g :=
  ringHom_ext' (RingHom.ext_int (RingHom.comp f C) (RingHom.comp g C)) h

-- A polynomial with integral coeff has a solution in `ℤ_[p]` iff it has a solution mod `p ^ n` for all `n : ℕ`
theorem prop1_4_weaker:
  (∃x : ℤ_[p], F.eval₂ (Int.castRingHom ℤ_[p]) x = 0) ↔ (∀m : ℕ, ∃x : ZMod (p ^ m), F.eval₂ (Int.castRingHom (ZMod (p ^ m))) x = 0) := by
  constructor
  · rintro ⟨x, Fx⟩ m
    use (toZModPow m) x
    let Fxm := ext_of_toZModPow.mpr Fx m
    rw [(toZModPow m).map_zero, hom_eval₂,
      ← RingHom.ext_int (Int.castRingHom (ZMod (p ^ m))) (RingHom.comp (toZModPow m) (Int.castRingHom ℤ_[p]))] at Fxm
    exact Fxm
  · intro h
    -- use `aux1`
    rcases aux1 h with ⟨y, ⟨Fy, cpt⟩⟩
    let g : (n : ℕ) → Polynomial ℤ →+* ZMod (p ^ n) :=
      fun n ↦ eval₂RingHom (Int.castRingHom (ZMod (p ^ n))) (y n)
    have g_cpt : ∀ (m n : ℕ) (mlen : m ≤ n), RingHom.comp (ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m))) (g n) = g m := by
      intro m n mlen
      apply Polynomial.ringHom_ext_Z
      simp only [RingHom.coe_comp, coe_eval₂RingHom, Function.comp_apply, eval₂_X, ZMod.castHom_apply]
      exact cpt m n mlen
    -- use PadicInt.limNthHom on `ℤ[X]`
    use lift g_cpt X
    rw [← ext_of_toZModPow]
    intro n
    rw [(toZModPow n).map_zero, hom_eval₂,
      ← RingHom.ext_int (Int.castRingHom (ZMod (p ^ n))) (RingHom.comp (toZModPow n) (Int.castRingHom ℤ_[p])),
      ← Fy n]
    congr
    rw [show y n = (g n) X by simp only [coe_eval₂RingHom, eval₂_X],
      (lift_spec g_cpt n).symm]
    simp only [RingHom.coe_comp, Function.comp_apply]


end Prop_1_4_weaker
