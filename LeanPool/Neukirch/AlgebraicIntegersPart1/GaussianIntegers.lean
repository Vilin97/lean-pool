/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sun Tiantong
-/

/-
Copyright (c) 2023 Sun Tiantong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sun Tiantong
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Zsqrtd.Basic

open Complex GaussianInt
local notation "ℤ[i]" => GaussianInt
namespace GaussianInt
variable (k:ℤ )(d : ℤ[i]) (u : ℤ[i]ˣ)  



theorem odd_sum_decomposition (p:ℕ ) (a b : ℤ ) (h_sum : p = a + b) (h_odd_p : Odd p) : (Odd a ∧ Even b) ∨ (Even a ∧ Odd b) := by
  have h_odd_p1 : Odd (p:ℤ ):= by exact Iff.mpr (Int.odd_coe_nat p) h_odd_p
  rcases Int.even_or_odd a with h|h
  . right    
    rw [h_sum,add_comm,Int.odd_add] at h_odd_p1
    constructor
    . exact h
    . apply h_odd_p1.mpr h
  . left 
    constructor
    . exact h
    . rw [h_sum,Int.odd_add] at h_odd_p1
      apply h_odd_p1.mp h


theorem odd_iff_odd_square   (a : ℤ ) (h: Odd (a^2) ) : Odd a:=by 
  rw[pow_two,Int.odd_mul] at h
  rcases h with ⟨ h1 , h2⟩ 
  exact h1
theorem even_iff_even_square (a : ℤ ) (h: Even (a^2) ): Even a:=by 
  rw[pow_two,Int.even_mul] at h
  rcases h with  h | h
  exact h
  exact h

theorem Int.sq_mod_four_eq_zero_of_even {x : ℤ} :Even x → x ^ 2 % 4 = 0 :=by
  intro hx
  unfold Even at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  apply Int.mul_emod_left


--Theorem. For all prime numbers p :I 2, one has: p=a^2 +b^2 (a,b ∈ ℤ ) <==> p==1 mod 4.( a b : ℕ ℤ  )
theorem mod_four_eq_one_of_nat__odd_prime (p : ℕ )( a b : ℤ  ) (h_not_2 : p ≠ 2) (h_prime : Nat.Prime p) (h_form : p = a^2 + b^2) : p % 4 = 1 := by
  have odd_p:Odd p:=by
    have :p= 2 ∨ p % 2 = 1 :=by apply Nat.Prime.eq_two_or_odd h_prime
    rcases this with h|h
    . exfalso
      apply h_not_2
      exact h
    . rw[Nat.odd_iff ]
      exact h
  have odd_prime_of_form : (Odd (a^2) ∧ Even (b^2)) ∨ (Even (a^2) ∧ Odd (b^2)):=by
    exact odd_sum_decomposition (p:ℕ ) (a^2) (b^2) h_form (odd_p)  
  have odd_12:(Odd a ∧ Even b) ∨ (Even a ∧ Odd b):=by 
    rcases odd_prime_of_form with h | h
    . left
      rcases h with ⟨ h1 , h2⟩  
      constructor
      . exact odd_iff_odd_square a h1
      . exact even_iff_even_square b h2

    . right
      rcases h with ⟨ h1 , h2⟩  
      constructor
      . exact even_iff_even_square a h1
      . exact odd_iff_odd_square b h2

  rcases odd_12 with (l | r)
  . show p % 4 = 1   
    have h1: (a^2)%4=1  :=by exact Int.sq_mod_four_eq_one_of_odd l.1  
    have h2: (b^2)%4 =0 :=by exact Int.sq_mod_four_eq_zero_of_even l.2 
    have :(p :ℤ ) %4 =1 := by 
      rw[h_form,Int.add_emod,h1,h2] 
      simp
    apply Int.ofNat_inj.mp
    norm_num
    exact this
  . show p % 4 = 1
    have h1: (b^2)%4=1  :=by exact Int.sq_mod_four_eq_one_of_odd r.2  
    have h2: (a^2)%4 =0 :=by exact Int.sq_mod_four_eq_zero_of_even r.1
    have :(p :ℤ ) %4 =1 := by 
      rw[h_form,Int.add_emod,h1,h2] 
      simp
    apply Int.ofNat_inj.mp
    norm_num
    exact this


theorem odd_prime_of_form_1_mod_4_eq_square_add (p : ℕ ) (h_not_2 : p ≠ 2)(h_prime : Nat.Prime p) (h_form : p % 4 = 1)
  : ∃ a b :ℤ, p = a^2 + b^2 :=by
  have h1:∃α β :ℤ[i], ↑p =α *β :=by sorry
  rcases h1 with ⟨α,β,h1_1⟩
  have : ¬ (IsUnit α ) ∧ ¬ (IsUnit β ) :=by sorry
  have h2:  (↑p)*(↑p) = (Zsqrtd.norm α)*(Zsqrtd.norm β) :=by 
    have h2_1:Zsqrtd.norm ↑p = Zsqrtd.norm (α * β) :=by rw[h1_1]
    rw[Zsqrtd.norm_mul _ _,Zsqrtd.norm_nat_cast _] at h2_1
    apply h2_1
  have h3: ↑p= (Zsqrtd.norm α):=by sorry--UFD
  have h4:p= α.re * α.re + α.im * α.im :=by 
    rw[Zsqrtd.norm_def α] at  h3
    rw[h3]
    norm_num
  use α.re ,α.im
  rw[pow_two]
  rw[pow_two] 
  apply h4

  

 

/-wasx-/
-- theorem EisU {A : Type _}[EuclideanDomain A]: UniqueFactorizationMonoid A := by 
--   exact  PrincipalIdealRing.to_uniqueFactorizationMonoid

-- theorem EisU1 {A : Type _}[EuclideanDomain A]: UniqueFactorizationMonoid A := by 
--   sorry
-- instance : EuclideanDomain ℤ[i] := by sorry

-- instance : EuclideanDomain ℤ[i] := by sorry

-- theorem units_in_gaussian_integers1 : ({ 1, -1, i, -i } : Set ℤ[i]  )= ℤ[i]ˣ  := by
--   sorry   


open Zsqrtd Complex

def i : ℤ[i] where
  re := 0
  im := 1

-- structure prime_elements_of_ℤi where
--   prime' : (d: ℤ[i]) → Irreducible d
  --irre' ： prime' d  
  -- a: Irreducible d 

-- #check Nat.Prime
-- a + bi with a2 + b2 = p, P == 1 mod 4, a > Ibl > 0  p, p == 3 mod 4
-- Define a set to represent the prime elements of ℤ[i]

-- def B : Set ℤ[i]  := {1 + i}  
--                   ∪ {z : ℤ[i] | (∃ p :Nat, (Nat.Prime p) ∧ (z.re^2 +z.im^2 = p) ∧ (z.re > z.im) ∧ (p%4 =1 )) } 
--                   ∪ {p | p%4 =3}

-- def ABX : ℂ := (i : ℂ) 

-- #check B


open scoped ComplexConjugate
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220
open PrincipalIdealRing

theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime]
    (hpi : Prime (p : ℤ[i])) : p % 4 = 3 :=
  hp.1.eq_two_or_odd.elim
    (fun hp2 =>
      absurd hpi
        (mt irreducible_iff_prime.2 fun ⟨_, h⟩ => by
          have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl)
          rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this
          exact absurd this (by decide)))
    fun hp1 =>
    by_contradiction fun hp3 : p % 4 ≠ 3 => by
      have hp41 : p % 4 = 1 := by
        rw [← Nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4 from rfl] at hp1
        have := Nat.mod_lt p (show 0 < 4 by decide)
        revert this hp3 hp1
        generalize p % 4 = m
        intros; interval_cases m <;> simp_all -- Porting note: was `decide!`
      let ⟨k, hk⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 <| by rw [hp41]; exact by decide
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = k := by
        refine' ⟨k.val, k.val_lt, ZMod.nat_cast_zmod_val k⟩
      have hpk : p ∣ k ^ 2 + 1 := by
        rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          ← hk, add_left_neg]
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ := by simp [sq, Zsqrtd.ext]
      have hkltp : 1 + k * k < p * p :=
        calc
          1 + k * k ≤ k + k * k := by
            apply add_le_add_right
            exact (Nat.pos_of_ne_zero fun (hk0 : k = 0) => by clear_aux_decl; simp_all [pow_succ'])
          _ = k * (k + 1) := by simp [add_comm, mul_add]
          _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_pos _) (Nat.zero_le _)
      have hpk₁ : ¬(p : ℤ[i]) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, -1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (-1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using congr_arg Zsqrtd.im hx
      have hpk₂ : ¬(p : ℤ[i]) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, 1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using congr_arg Zsqrtd.im hx
      obtain ⟨y, hy⟩ := hpk
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← Nat.cast_mul p, ← hy]; simp⟩
      clear_aux_decl
      tauto






