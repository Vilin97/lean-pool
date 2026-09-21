/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Finite.Basic
/-!
# Power-residue symbols over finite fields

For a finite field `k` of cardinality `q` and `n ∣ q - 1`, the tame
power-residue symbol is

`u ↦ u ^ ((q - 1) / n)`.

Its kernel is exactly the subgroup of `n`-th powers.
-/

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

variable (k : Type*) [Field k] [Fintype k]

/-- The finite-field `n`-th power-residue symbol. -/
def finiteFieldPowerResidueSymbol
    (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card k - 1) :
    kˣ →* rootsOfUnity (n : ℕ) k where
  toFun u :=
    ⟨u ^ ((Fintype.card k - 1) / (n : ℕ)), by
      change (u ^ ((Fintype.card k - 1) / (n : ℕ))) ^ (n : ℕ) = 1
      rw [← pow_mul, Nat.div_mul_cancel hn]
      apply Units.ext
      exact FiniteField.pow_card_sub_one_eq_one
        (u : k) (Units.ne_zero u)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp [mul_pow]

@[simp]
theorem finiteFieldPowerResidueSymbol_apply
    (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card k - 1) (u : kˣ) :
    ((finiteFieldPowerResidueSymbol k n hn u :
        rootsOfUnity (n : ℕ) k) : kˣ) =
      u ^ ((Fintype.card k - 1) / (n : ℕ)) :=
  rfl

/-- The finite-field symbol is trivial exactly on `n`-th powers. -/
theorem finiteFieldPowerResidueSymbol_eq_one_iff
    (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card k - 1) (u : kˣ) :
    finiteFieldPowerResidueSymbol k n hn u = 1 ↔
      ∃ v : kˣ, v ^ (n : ℕ) = u := by
  classical
  let m := (Fintype.card k - 1) / (n : ℕ)
  let powerN : kˣ →* kˣ := powMonoidHom (n : ℕ)
  let powerM : kˣ →* kˣ := powMonoidHom m
  have hRange_le_ker : powerN.range ≤ powerM.ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker]
    change (v ^ (n : ℕ)) ^ m = 1
    rw [← pow_mul]
    have hnm : (n : ℕ) * m = Fintype.card k - 1 := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hn
    rw [hnm]
    apply Units.ext
    exact FiniteField.pow_card_sub_one_eq_one
      (v : k) (Units.ne_zero v)
  have hCard : Nat.card powerM.ker ≤ Nat.card powerN.range := by
    have hm : m ∣ Fintype.card k - 1 :=
      Nat.div_dvd_of_dvd hn
    have hUnitsCard : Nat.card kˣ = Fintype.card k - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units]
    dsimp only [powerM, powerN]
    rw [IsCyclic.card_powMonoidHom_ker,
      IsCyclic.card_powMonoidHom_range, hUnitsCard,
      Nat.gcd_eq_right hm, Nat.gcd_eq_right hn]
  have hRange_eq_ker : powerN.range = powerM.ker :=
    Subgroup.eq_of_le_of_card_ge hRange_le_ker hCard
  constructor
  · intro hsymbol
    have huPow : u ^ m = 1 := by
      have hval := congrArg
        (fun z : rootsOfUnity (n : ℕ) k => (z : kˣ)) hsymbol
      change
        u ^ ((Fintype.card k - 1) / (n : ℕ)) = (1 : kˣ) at hval
      simpa only [m] using hval
    have huKer : u ∈ powerM.ker := by
      rw [MonoidHom.mem_ker]
      exact huPow
    have huRange : u ∈ powerN.range := by
      rw [hRange_eq_ker]
      exact huKer
    rcases huRange with ⟨v, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    have huRange : u ∈ powerN.range := ⟨v, hv⟩
    have huKer : u ∈ powerM.ker := by
      rw [← hRange_eq_ker]
      exact huRange
    apply Subtype.ext
    change u ^ m = 1
    simpa only [powerM, powMonoidHom_apply] using
      (MonoidHom.mem_ker.mp huKer)

end PowerResidueSymbols
end AlgebraicNumberTheory
