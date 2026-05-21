/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.compreals.pre
import LeanPool.HopfieldNet.compreals.dyadic

namespace Computable

/--
`CRealRep AQ` is a *computational* representation of a real number whose
approximants live in an implementation type `AQ` (e.g. `Dyadic`).

All semantic statements are phrased by transporting to the existing ℚ-based
specification model `CReal.Pre` via `toPre`.
-/
structure CRealRep (AQ : Type) [ApproxRationals AQ] where
  /-- The approximation sequence. -/
  approx : ℕ → AQ
  /-- Regularity of approximations, stated in `ℚ` via `ApproxRationals.toRat`. -/
  is_regular :
    ∀ n m : ℕ, n ≤ m →
      |ApproxRationals.toRat (approx n) - ApproxRationals.toRat (approx m)| ≤
        (1 : ℚ) / (2 ^ n)

namespace CRealRep

variable {AQ : Type} [ApproxRationals AQ]

/-- Project a computational representative to the ℚ-specification carrier. -/
def toPre (x : CRealRep AQ) : CReal.Pre where
  approx := fun n => ApproxRationals.toRat (x.approx n)
  is_regular := x.is_regular

/-- Extensional equivalence on computational representatives, defined by projection. -/
def Equiv (x y : CRealRep AQ) : Prop := CReal.Pre.Equiv x.toPre y.toPre

instance : Setoid (CRealRep AQ) where
  r := Equiv
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact CReal.Pre.equiv_refl x.toPre
    · intro x y h
      exact CReal.Pre.equiv_symm h
    · intro x y z hxy hyz
      exact CReal.Pre.equiv_trans hxy hyz

/-- Infix notation for the induced equivalence relation. -/
infix:50 " ≈ᵣ " => CRealRep.Equiv

/-- Convenience lemma: `0 ≤ 1/2^n` in `ℚ`. -/
private lemma zero_le_modulus (n : ℕ) : (0 : ℚ) ≤ (1 : ℚ) / (2 ^ n) := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ n := by
    exact pow_pos (by norm_num) _
  exact le_of_lt (div_pos (show (0 : ℚ) < 1 by norm_num) hpow)

/-! ### Unrounded operations on representatives -/

/-- Zero as a computational representative. -/
protected def zero : CRealRep AQ where
  approx := fun _ => 0
  is_regular := by
    intro n m _
    simp

/-- One as a computational representative. -/
protected def one : CRealRep AQ where
  approx := fun _ => 1
  is_regular := by
    intro n m _
    simp

/-- Negation on representatives. -/
protected def neg (x : CRealRep AQ) : CRealRep AQ where
  approx := fun n => -x.approx n
  is_regular := by
    intro n m hnm
    -- transport from `x.is_regular`.
    have h := x.is_regular n m hnm
    -- The new difference is the negative of the old difference, and `abs` ignores signs.
    have habs :
        |-(ApproxRationals.toRat (x.approx n)) + ApproxRationals.toRat (x.approx m)| =
          |ApproxRationals.toRat (x.approx n) - ApproxRationals.toRat (x.approx m)| := by
      have hr :
          (-(ApproxRationals.toRat (x.approx n)) + ApproxRationals.toRat (x.approx m)) =
            -(ApproxRationals.toRat (x.approx n) - ApproxRationals.toRat (x.approx m)) := by
        ring
      calc
        |-(ApproxRationals.toRat (x.approx n)) + ApproxRationals.toRat (x.approx m)|
            = |-(ApproxRationals.toRat (x.approx n) - ApproxRationals.toRat (x.approx m))| := by
                simp [hr]
        _ = |ApproxRationals.toRat (x.approx n) - ApproxRationals.toRat (x.approx m)| := by
              simpa using abs_neg (ApproxRationals.toRat (x.approx n) - ApproxRationals.toRat (x.approx m))
    simpa [ApproxRationals.toRat_neg, habs] using h

/-- Addition on representatives (spec-compatible, unrounded). -/
protected def add (x y : CRealRep AQ) : CRealRep AQ where
  approx := fun n => x.approx (n + 1) + y.approx (n + 1)
  is_regular := by
    intro n m hnm
    -- Delegate to the spec addition regularity on `toPre`.
    simpa [CRealRep.toPre] using (CReal.Pre.add x.toPre y.toPre).is_regular n m hnm

/-- The multiplication shift, delegated to the specification model. -/
def mulShift (x y : CRealRep AQ) : ℕ := (x.toPre : CReal.Pre).mulShift (y.toPre : CReal.Pre)

/-- Multiplication on representatives (spec-compatible, unrounded). -/
protected def mul (x y : CRealRep AQ) : CRealRep AQ where
  approx := fun n =>
    let S := mulShift (AQ := AQ) x y
    x.approx (n + S) * y.approx (n + S)
  is_regular := by
    intro n m hnm
    simpa [CRealRep.toPre, mulShift] using (CReal.Pre.mul x.toPre y.toPre).is_regular n m hnm

/-! ### Rounded/compressed operations (fast layer) -/

/--
Compression/rounding of a representative.

We shift the sequence by `+2` to gain slack and then round at the same precision.
This is the minimal constant shift that lets the triangle inequality budget close.
-/
protected def compress (x : CRealRep AQ) : CRealRep AQ where
  approx := fun n => ApproxRationals.approx (x.approx (n + 2)) (n + 2)
  is_regular := by
    intro n m hnm
    -- three-term triangle inequality
    set a : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (n + 2)) (n + 2))
    set b : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (m + 2)) (m + 2))
    set xn : ℚ := ApproxRationals.toRat (x.approx (n + 2))
    set xm : ℚ := ApproxRationals.toRat (x.approx (m + 2))
    have hn_round : |a - xn| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      simpa [a, xn] using (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (n + 2)) (n + 2))
    have hm_round : |xm - b| ≤ (1 : ℚ) / (2 ^ (m + 2)) := by
      -- same inequality but symmetric
      have := (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (m + 2)) (m + 2))
      -- |b - xm| ≤ ...  ⇒  |xm - b| ≤ ...
      simpa [abs_sub_comm, a, b, xm] using this
    have hmid : |xn - xm| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := by exact Nat.add_le_add_right hnm 2
      simpa [xn, xm] using x.is_regular (n + 2) (m + 2) hnm'
    have hab : |a - b| ≤ |a - xn| + |xn - xm| + |xm - b| := by
      -- `|a-b| ≤ |a-xn| + |xn-xm| + |xm-b|`
      have h1 : |a - b| ≤ |a - xn| + |xn - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a xn b)
      have h2 : |xn - b| ≤ |xn - xm| + |xm - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le xn xm b)
      linarith
    -- bound the RHS by `3 / 2^(n+2)` and close
    have h_pow_mon : (1 : ℚ) / (2 ^ (m + 2)) ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      -- `n+2 ≤ m+2` implies `2^(n+2) ≤ 2^(m+2)` so the reciprocals reverse.
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      have hpow : (2 : ℚ) ^ (n + 2) ≤ (2 : ℚ) ^ (m + 2) := by
        exact (pow_le_pow_iff_right₀ rfl).mpr hnm'-- pow_le_pow_of_le_left (by norm_num) hnm'
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 2) := pow_pos (by norm_num) _
      have hpos' : (0 : ℚ) < (2 : ℚ) ^ (m + 2) := pow_pos (by norm_num) _
      -- use `1/a ≤ 1/b` if `b ≤ a` with positivity
      have := one_div_le_one_div_of_le hpos hpow
      -- rewrite `1 / 2^k` as `1 / ((2:ℚ)^k)`
      simpa [one_div, div_eq_mul_inv] using this
    have hR : |a - xn| + |xn - xm| + |xm - b|
        ≤ (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) := by
      have hm_round' : |xm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) := hm_round.trans h_pow_mon
      linarith [hn_round, hmid, hm_round']
    have h3 : (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2))
        ≤ (1 : ℚ) / (2 ^ n) := by
      -- 3 * 2^{-(n+2)} ≤ 2^{-n}
      have hcoeff : (3 : ℚ) / 4 ≤ 1 := by norm_num
      have hpos : 0 ≤ (1 : ℚ) / (2 ^ n) := zero_le_modulus (n := n)
      -- rewrite
      have : (1 : ℚ) / (2 ^ (n + 2)) = (1 : ℚ) / (2 ^ n) / 4 := by
        -- `2^(n+2) = 4*2^n`
        simp [pow_add, pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
        ring
      -- use linear arithmetic
      -- `a+a+a = 3*a`
      rw [this]
      -- after rw, goal becomes `1/2^n/4 + 1/2^n/4 + 1/2^n/4 ≤ 1/2^n`.
      -- which is `3/4 * (1/2^n) ≤ (1/2^n)`.
      have h2n_pos : (0 : ℚ) < 2 ^ n := pow_pos (by norm_num) n
      field_simp
      ring_nf
      nlinarith [h2n_pos]
    -- assemble
    have hab_final : |a - b| ≤ (1 : ℚ) / (2 ^ n) := by
      have := hab.trans (le_trans hR h3)
      simpa using this
    -- now unfold `a b`
    simpa [a, b, xn, xm] using hab_final

/-- Rounded addition on representatives. -/
protected def addC (x y : CRealRep AQ) : CRealRep AQ where
  approx := fun n =>
    ApproxRationals.approx (x.approx (n + 2) + y.approx (n + 2)) (n + 2)
  is_regular := by
    intro n m hnm
    set a : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (n + 2) + y.approx (n + 2)) (n + 2))
    set b : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (m + 2) + y.approx (m + 2)) (m + 2))
    set sn : ℚ := ApproxRationals.toRat (x.approx (n + 2) + y.approx (n + 2))
    set sm : ℚ := ApproxRationals.toRat (x.approx (m + 2) + y.approx (m + 2))
    have hn_round : |a - sn| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      simpa [a, sn] using (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (n + 2) + y.approx (n + 2)) (n + 2))
    have hm_round : |sm - b| ≤ (1 : ℚ) / (2 ^ (m + 2)) := by
      have := (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (m + 2) + y.approx (m + 2)) (m + 2))
      simpa [abs_sub_comm, b, sm] using this
    have hmid : |sn - sm| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
      -- use regularity of the spec addition on `toPre`
      have hnm' : n + 1 ≤ m + 1 := Nat.add_le_add_right hnm 1
      have := (CReal.Pre.add x.toPre y.toPre).is_regular (n + 1) (m + 1) hnm'
      -- unfold `sn`, `sm`
      -- (add.toPre).approx (k) = toRat (x.approx (k+1) + y.approx (k+1))
      simpa [CRealRep.toPre, CReal.Pre.add, sn, sm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using this
    have hab : |a - b| ≤ |a - sn| + |sn - sm| + |sm - b| := by
      have h1 : |a - b| ≤ |a - sn| + |sn - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a sn b)
      have h2 : |sn - b| ≤ |sn - sm| + |sm - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le sn sm b)
      linarith
    -- `1/2^(m+2) ≤ 1/2^(n+2)`
    have h_pow_mon : (1 : ℚ) / (2 ^ (m + 2)) ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      have hpow : (2 : ℚ) ^ (n + 2) ≤ (2 : ℚ) ^ (m + 2) :=
        (pow_le_pow_iff_right₀ rfl).mpr hnm' --pow_le_pow_of_le_left (by norm_num) hnm'
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 2) := pow_pos (by norm_num) _
      have := one_div_le_one_div_of_le hpos hpow
      simpa [one_div, div_eq_mul_inv] using this
    have hm_round' : |sm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) := hm_round.trans h_pow_mon
    have hsum : |a - sn| + |sn - sm| + |sm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) := by
      linarith [hn_round, hmid, hm_round']
    have hclose : (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) ≤ (1 : ℚ) / (2 ^ n) := by
      -- `1/2^(n+1) + 2/2^(n+2) = 1/2^n`.
      ring_nf
      have : (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) := by
        -- `2 * 2^{-(n+1)} = 2^{-n}`
        simp [pow_succ, div_eq_mul_inv]
        ring
      nlinarith
    have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := hab.trans (le_trans hsum hclose)
    simpa [a, b] using this

/-- Rounded multiplication on representatives. -/
protected def mulC (x y : CRealRep AQ) : CRealRep AQ where
  approx := fun n =>
    let S := mulShift (AQ := AQ) x y
    ApproxRationals.approx (x.approx (n + 2 + S) * y.approx (n + 2 + S)) (n + 2)
  is_regular := by
    intro n m hnm
    let S := mulShift (AQ := AQ) x y
    set a : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (n + 2 + S) * y.approx (n + 2 + S)) (n + 2))
    set b : ℚ := ApproxRationals.toRat (ApproxRationals.approx (x.approx (m + 2 + S) * y.approx (m + 2 + S)) (m + 2))
    set pn : ℚ := ApproxRationals.toRat (x.approx (n + 2 + S) * y.approx (n + 2 + S))
    set pm : ℚ := ApproxRationals.toRat (x.approx (m + 2 + S) * y.approx (m + 2 + S))
    have hn_round : |a - pn| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      simpa [a, pn] using (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (n + 2 + S) * y.approx (n + 2 + S)) (n + 2))
    have hm_round : |pm - b| ≤ (1 : ℚ) / (2 ^ (m + 2)) := by
      have := (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (m + 2 + S) * y.approx (m + 2 + S)) (m + 2))
      simpa [abs_sub_comm, b, pm] using this
    have hmid : |pn - pm| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
      -- Use regularity of the spec multiplication at indices `n+2` and `m+2`,
      -- then weaken `1/2^(n+2) ≤ 1/2^(n+1)`.
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      have hspec := (CReal.Pre.mul x.toPre y.toPre).is_regular (n + 2) (m + 2) hnm'
      have hspec' : |pn - pm| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
        simpa [CRealRep.toPre, CReal.Pre.mul, mulShift, pn, pm, S] using hspec
      have hmono : (1 : ℚ) / (2 ^ (n + 2)) ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
        have hpow : (2 : ℚ) ^ (n + 1) ≤ (2 : ℚ) ^ (n + 2) := by
          exact (pow_le_pow_iff_right₀ rfl).2 (Nat.le_succ (n + 1))
        have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 1) := pow_pos (by norm_num) _
        have := one_div_le_one_div_of_le hpos hpow
        -- rewrite `1 / 2^k` as `1 / ((2:ℚ)^k)`
        simpa [one_div, div_eq_mul_inv] using this
      exact hspec'.trans hmono
    have hab : |a - b| ≤ |a - pn| + |pn - pm| + |pm - b| := by
      have h1 : |a - b| ≤ |a - pn| + |pn - b| := by exact abs_sub_le a pn b --abs_sub_abs_le_abs_sub a pn ▸ abs_sub_le a pn b
      have h2 : |pn - b| ≤ |pn - pm| + |pm - b| := by exact abs_sub_le pn pm b --abs_sub_abs_le_abs_sub pn pm ▸ abs_sub_le pn pm b
      --  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le pn pm b)
      linarith
    have h_pow_mon : (1 : ℚ) / (2 ^ (m + 2)) ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      have hpow : (2 : ℚ) ^ (n + 2) ≤ (2 : ℚ) ^ (m + 2) :=
        (pow_le_pow_iff_right₀ rfl).mpr hnm' --pow_le_pow_of_le_left (by norm_num) hnm'
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 2) := pow_pos (by norm_num) _
      have := one_div_le_one_div_of_le hpos hpow
      simpa [one_div, div_eq_mul_inv] using this
    have hm_round' : |pm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) := hm_round.trans h_pow_mon
    have hsum : |a - pn| + |pn - pm| + |pm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) := by
      linarith [hn_round, hmid, hm_round']
    have hclose : (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) ≤ (1 : ℚ) / (2 ^ n) := by
      ring_nf
      -- same as in `addC`
      have : (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) := by
        simp [pow_succ, div_eq_mul_inv]
        ring
      nlinarith
    have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := hab.trans (le_trans hsum hclose)
    simpa [a, b, S] using this

/-- Rounded negation: exact, so this is just `neg`. -/
@[inline] protected def negC (x : CRealRep AQ) : CRealRep AQ := CRealRep.neg x

/-- Rounded subtraction, defined via rounded addition and exact negation. -/
@[inline] protected def subC (x y : CRealRep AQ) : CRealRep AQ :=
  CRealRep.addC x (CRealRep.neg y)

/-! ### Rounded inverse and division -/

protected def invC (x : CRealRep AQ) (W : CReal.Pre.InvWitness x.toPre) : CRealRep AQ where
  approx n := ApproxRationals.approxRat ((CReal.Pre.inv x.toPre W).approx (n + 1)) (n + 2)
  is_regular := by
    intro n m hnm
    set u : CReal.Pre := CReal.Pre.inv x.toPre W
    set qn : ℚ := u.approx (n + 1)
    set qm : ℚ := u.approx (m + 1)
    -- `approxRat` does not determine the carrier `AQ`, so we must specify it.
    set a : ℚ := ApproxRationals.toRat (AQ := AQ) (ApproxRationals.approxRat qn (n + 2))
    set b : ℚ := ApproxRationals.toRat (AQ := AQ) (ApproxRationals.approxRat qm (m + 2))
    have hn_round : |a - qn| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      simpa [a] using (ApproxRationals.abs_toRat_approxRat_sub_le (AQ := AQ) qn (n + 2))
    have hm_round : |qm - b| ≤ (1 : ℚ) / (2 ^ (m + 2)) := by
      have := (ApproxRationals.abs_toRat_approxRat_sub_le (AQ := AQ) qm (m + 2))
      simpa [b, abs_sub_comm] using this
    have hmid : |qn - qm| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
      have hnm' : n + 1 ≤ m + 1 := by omega
      simpa [u, qn, qm] using (u.is_regular (n + 1) (m + 1) hnm')
    have hab : |a - b| ≤ |a - qn| + |qn - qm| + |qm - b| := by
      have h1 : |a - b| ≤ |a - qn| + |qn - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a qn b)
      have h2 : |qn - b| ≤ |qn - qm| + |qm - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le qn qm b)
      exact le_trans h1 (by linarith [h2])
    have h_pow_mon : (1 : ℚ) / (2 ^ (m + 2)) ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := by omega
      have hpow : (2 : ℚ) ^ (n + 2) ≤ (2 : ℚ) ^ (m + 2) :=
        (pow_le_pow_iff_right₀ rfl).mpr hnm'
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 2) := pow_pos (by norm_num) _
      have := one_div_le_one_div_of_le hpos hpow
      simpa [one_div, div_eq_mul_inv] using this
    have hm_round' : |qm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) := hm_round.trans h_pow_mon
    have hsum : |a - qn| + |qn - qm| + |qm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) := by
      linarith [hn_round, hmid, hm_round']
    have hclose : (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 2)) ≤ (1 : ℚ) / (2 ^ n) := by
      ring_nf
      have : (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) := by
        simp [pow_succ, div_eq_mul_inv]; ring
      nlinarith
    have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := hab.trans (le_trans hsum hclose)
    -- Unfold the local abbreviations; we cannot unfold `invC` inside its own definition.
    simpa [u, qn, qm, a, b] using this

@[inline] protected def divC (x y : CRealRep AQ) (Wy : CReal.Pre.InvWitness y.toPre) : CRealRep AQ :=
  CRealRep.mulC x (CRealRep.invC y Wy)

/-! ### Compatibility lemmas (projection correctness) -/

theorem toPre_zero_equiv : CReal.Pre.Equiv (CRealRep.zero (AQ := AQ)).toPre CReal.Pre.zero := by
  intro n
  simp [CRealRep.zero, CRealRep.toPre, CReal.Pre.zero]

theorem toPre_one_equiv : CReal.Pre.Equiv (CRealRep.one (AQ := AQ)).toPre CReal.Pre.one := by
  intro n
  simp [CRealRep.one, CRealRep.toPre, CReal.Pre.one]

theorem toPre_neg_equiv (x : CRealRep AQ) : CReal.Pre.Equiv (CRealRep.neg x).toPre (CReal.Pre.neg x.toPre) := by
  intro n
  simp [CRealRep.neg, CRealRep.toPre, CReal.Pre.neg]

theorem toPre_add_equiv (x y : CRealRep AQ) :
    CReal.Pre.Equiv (CRealRep.add x y).toPre (CReal.Pre.add x.toPre y.toPre) := by
  intro n
  simp [CRealRep.add, CRealRep.toPre, CReal.Pre.add]

theorem toPre_mul_equiv (x y : CRealRep AQ) :
    CReal.Pre.Equiv (CRealRep.mul x y).toPre (CReal.Pre.mul x.toPre y.toPre) := by
  intro n
  simp [CRealRep.mul, CRealRep.toPre, CReal.Pre.mul, mulShift]

/-- Compression is equivalent to the identity in the ℚ-specification model. -/
theorem toPre_compress_equiv (x : CRealRep AQ) : CReal.Pre.Equiv (CRealRep.compress x).toPre x.toPre := by
  intro n
  -- compare at index `n+1`
  -- `compress` uses `x.approx (n+3)` rounded at precision `n+3`.
  set a : ℚ := (CRealRep.compress x).toPre.approx (n + 1)
  set b : ℚ := x.toPre.approx (n + 1)
  set c : ℚ := x.toPre.approx (n + 3)
  have h_round : |a - c| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
    -- rounding error bound
    simpa [CRealRep.compress, CRealRep.toPre, a, c] using
      (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (n + 3)) (n + 3))
  have h_reg : |c - b| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
    have := x.is_regular (n + 1) (n + 3) (by omega)
    -- `x.is_regular` gives a bound on `|b - c|`; use symmetry of `abs` to rewrite.
    simpa [CRealRep.toPre, b, c, abs_sub_comm] using this
  have h_tri : |a - b| ≤ |a - c| + |c - b| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a c b)
  have h_close : (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 1)) ≤ (1 : ℚ) / (2 ^ n) := by
    -- `2^{-(n+1)} + 2^{-(n+3)} = (1/2 + 1/8)*2^{-n} = 5/8*2^{-n}`
    have : (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) / 2 := by
      simp [pow_succ, div_eq_mul_inv]; ring
    have : (1 : ℚ) / (2 ^ (n + 3)) = (1 : ℚ) / (2 ^ n) / 8 := by
      simp [pow_succ, div_eq_mul_inv, mul_comm]; ring
    -- Use `nlinarith` after rewriting.
    -- (We re-simp using the two equalities above.)
    nlinarith [zero_le_modulus (n := n)]
  have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := by
    exact (h_tri.trans (by linarith [h_round, h_reg])).trans h_close
  simpa [CReal.Pre.Equiv, a, b] using this

/-- Rounded addition is equivalent to spec addition. -/
theorem toPre_addC_equiv (x y : CRealRep AQ) :
    CReal.Pre.Equiv (CRealRep.addC x y).toPre (CReal.Pre.add x.toPre y.toPre) := by
  intro n
  -- compare at index `n+1`
  set a : ℚ := (CRealRep.addC x y).toPre.approx (n + 1)
  set b : ℚ := (CReal.Pre.add x.toPre y.toPre).approx (n + 1)
  set c : ℚ := (CReal.Pre.add x.toPre y.toPre).approx (n + 2)
  have h_round : |a - c| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
    -- `a` rounds the sum at precision `n+3`
    simpa [CRealRep.addC, CRealRep.toPre, a, c, CReal.Pre.add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ) (x.approx (n + 3) + y.approx (n + 3)) (n + 3))
  have h_reg : |c - b| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
    have := (CReal.Pre.add x.toPre y.toPre).is_regular (n + 1) (n + 2) (by omega)
    simpa [b, c, abs_sub_comm] using this
  have h_tri : |a - b| ≤ |a - c| + |c - b| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a c b)
  have h_close : (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 1)) ≤ (1 : ℚ) / (2 ^ n) := by
    have h1 : (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) / 2 := by
      simp [pow_succ, div_eq_mul_inv]; ring
    have h2 : (1 : ℚ) / (2 ^ (n + 3)) = (1 : ℚ) / (2 ^ n) / 8 := by
      simp [pow_succ, div_eq_mul_inv, mul_comm]; ring
    nlinarith [h1, h2, zero_le_modulus (n := n)]
  have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := by
    exact (h_tri.trans (by linarith [h_round, h_reg])).trans h_close
  simpa [CReal.Pre.Equiv, a, b] using this

/-- Rounded multiplication is equivalent to spec multiplication. -/
theorem toPre_mulC_equiv (x y : CRealRep AQ) :
    CReal.Pre.Equiv (CRealRep.mulC x y).toPre (CReal.Pre.mul x.toPre y.toPre) := by
  intro n
  let S := mulShift (AQ := AQ) x y
  set a : ℚ := (CRealRep.mulC x y).toPre.approx (n + 1)
  set b : ℚ := (CReal.Pre.mul x.toPre y.toPre).approx (n + 1)
  set c : ℚ := (CReal.Pre.mul x.toPre y.toPre).approx (n + 3)
  have h_round : |a - c| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
    -- `a` rounds the product at precision `n+3` (with the same shift as the spec product).
    let T : ℕ := (x.toPre : CReal.Pre).mulShift (y.toPre : CReal.Pre)
    have hidx : n + (1 + (2 + T)) = n + (3 + T) := by omega
    have hT : (x.toPre : CReal.Pre).mulShift (y.toPre : CReal.Pre) = T := by rfl
    have ha :
        a =
          ApproxRationals.toRat
            (ApproxRationals.approx (x.approx (n + (3 + T)) * y.approx (n + (3 + T))) (n + 3)) := by
      -- Unfold `a` and rewrite the internal shift to `T`.
      have hShift : mulShift (AQ := AQ) x y = T := by rfl
      simp [a, CRealRep.mulC, CRealRep.toPre, Nat.add_assoc, hShift, hidx]
    have hc :
        c =
          ApproxRationals.toRat (x.approx (n + (3 + T))) *
            ApproxRationals.toRat (y.approx (n + (3 + T))) := by
      -- unfold `c` and normalize the index using associativity
      simp [c, CReal.Pre.mul, CRealRep.toPre, T, Nat.add_assoc]
    have hlem :=
      ApproxRationals.abs_toRat_approx_sub_le (AQ := AQ)
        (x.approx (n + (3 + T)) * y.approx (n + (3 + T))) (n + 3)
    have hlem' :
        |ApproxRationals.toRat
              (ApproxRationals.approx (x.approx (n + (3 + T)) * y.approx (n + (3 + T))) (n + 3)) -
            (ApproxRationals.toRat (x.approx (n + (3 + T))) *
              ApproxRationals.toRat (y.approx (n + (3 + T))))| ≤
            (1 : ℚ) / (2 ^ (n + 3)) := by
      simpa using hlem
    simpa [ha, hc] using hlem'
  have h_reg : |c - b| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
    have := (CReal.Pre.mul x.toPre y.toPre).is_regular (n + 1) (n + 3) (by omega)
    simpa [b, c, abs_sub_comm] using this
  have h_tri : |a - b| ≤ |a - c| + |c - b| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a c b)
  have h_close : (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 1)) ≤ (1 : ℚ) / (2 ^ n) := by
    have h1 : (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) / 2 := by
      simp [pow_succ, div_eq_mul_inv]; ring
    have h2 : (1 : ℚ) / (2 ^ (n + 3)) = (1 : ℚ) / (2 ^ n) / 8 := by
      simp [pow_succ, div_eq_mul_inv, mul_comm]; ring
    nlinarith [h1, h2, zero_le_modulus (n := n)]
  have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := by
    exact (h_tri.trans (by linarith [h_round, h_reg])).trans h_close
  simpa [CReal.Pre.Equiv, a, b] using this

/-- Rounded subtraction agrees with spec subtraction (implemented as `add` + `neg`). -/
theorem toPre_subC_equiv (x y : CRealRep AQ) :
    CReal.Pre.Equiv (CRealRep.subC x y).toPre (CReal.Pre.add x.toPre (CReal.Pre.neg y.toPre)) := by
  -- unfold `subC` and use the already-proved correctness lemmas.
  refine CReal.Pre.equiv_trans (toPre_addC_equiv (AQ := AQ) x (CRealRep.neg y)) ?_
  have hy : CReal.Pre.Equiv (CRealRep.neg y).toPre (CReal.Pre.neg y.toPre) := toPre_neg_equiv (AQ := AQ) y
  simpa using
    (CReal.add_respects_equiv (x₁ := x.toPre) (x₂ := x.toPre)
      (y₁ := (CRealRep.neg y).toPre) (y₂ := CReal.Pre.neg y.toPre) (CReal.Pre.equiv_refl _) hy)

/-- Rounded inverse is equivalent to spec inverse. -/
theorem toPre_invC_equiv (x : CRealRep AQ) (W : CReal.Pre.InvWitness x.toPre) :
    CReal.Pre.Equiv (CRealRep.invC x W).toPre (CReal.Pre.inv x.toPre W) := by
  intro n
  set u : CReal.Pre := CReal.Pre.inv x.toPre W
  set a : ℚ := (CRealRep.invC x W).toPre.approx (n + 1)
  set b : ℚ := u.approx (n + 1)
  set c : ℚ := u.approx (n + 2)
  have h_round : |a - c| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
    -- `a` rounds `u.approx (n+2)` at precision `n+3`.
    simpa [CRealRep.invC, CRealRep.toPre, a, c, u, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ApproxRationals.abs_toRat_approxRat_sub_le (AQ := AQ) (u.approx (n + 2)) (n + 3))
  have h_reg : |c - b| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
    have := u.is_regular (n + 1) (n + 2) (by omega)
    simpa [b, c, abs_sub_comm] using this
  have h_tri : |a - b| ≤ |a - c| + |c - b| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a c b)
  have h_close : (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 1)) ≤ (1 : ℚ) / (2 ^ n) := by
    have h1 : (1 : ℚ) / (2 ^ (n + 1)) = (1 : ℚ) / (2 ^ n) / 2 := by
      simp [pow_succ, div_eq_mul_inv]; ring
    have h2 : (1 : ℚ) / (2 ^ (n + 3)) = (1 : ℚ) / (2 ^ n) / 8 := by
      simp [pow_succ, div_eq_mul_inv, mul_comm]; ring
    nlinarith [h1, h2, zero_le_modulus (n := n)]
  have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := by
    exact (h_tri.trans (by linarith [h_round, h_reg])).trans h_close
  simpa [CReal.Pre.Equiv, a, b] using this

/-- Rounded division agrees with spec division (implemented as `mul` + `inv`). -/
theorem toPre_divC_equiv (x y : CRealRep AQ) (Wy : CReal.Pre.InvWitness y.toPre) :
    CReal.Pre.Equiv (CRealRep.divC x y Wy).toPre (CReal.Pre.mul x.toPre (CReal.Pre.inv y.toPre Wy)) := by
  -- unfold `divC` and chain existing lemmas.
  refine CReal.Pre.equiv_trans (toPre_mulC_equiv (AQ := AQ) x (CRealRep.invC y Wy)) ?_
  have hy : CReal.Pre.Equiv (CRealRep.invC y Wy).toPre (CReal.Pre.inv y.toPre Wy) :=
    toPre_invC_equiv (AQ := AQ) y Wy
  simpa using
    (CReal.mul_respects_equiv (x₁ := x.toPre) (x₂ := x.toPre)
      (y₁ := (CRealRep.invC y Wy).toPre) (y₂ := CReal.Pre.inv y.toPre Wy) (CReal.Pre.equiv_refl _) hy)

/-! ### Transport of “respects equivalence” theorems from the ℚ-specification -/

theorem neg_respects_equiv {x y : CRealRep AQ} (h : x ≈ᵣ y) : CRealRep.neg x ≈ᵣ CRealRep.neg y := by
  refine CReal.Pre.equiv_trans (toPre_neg_equiv (AQ := AQ) x) ?_
  refine CReal.Pre.equiv_trans ?_ (CReal.Pre.equiv_symm (toPre_neg_equiv (AQ := AQ) y))
  exact CReal.neg_respects_equiv (x := x.toPre) (y := y.toPre) h

theorem addC_respects_equiv {x₁ x₂ y₁ y₂ : CRealRep AQ} (hx : x₁ ≈ᵣ x₂) (hy : y₁ ≈ᵣ y₂) :
    CRealRep.addC x₁ y₁ ≈ᵣ CRealRep.addC x₂ y₂ := by
  -- (addC x₁ y₁).toPre ≈ add x₁.toPre y₁.toPre ≈ add x₂.toPre y₂.toPre ≈ (addC x₂ y₂).toPre
  refine CReal.Pre.equiv_trans (toPre_addC_equiv (AQ := AQ) x₁ y₁) ?_
  refine CReal.Pre.equiv_trans ?_ (CReal.Pre.equiv_symm (toPre_addC_equiv (AQ := AQ) x₂ y₂))
  exact CReal.add_respects_equiv (x₁ := x₁.toPre) (x₂ := x₂.toPre) (y₁ := y₁.toPre) (y₂ := y₂.toPre) hx hy

theorem mulC_respects_equiv {x₁ x₂ y₁ y₂ : CRealRep AQ} (hx : x₁ ≈ᵣ x₂) (hy : y₁ ≈ᵣ y₂) :
    CRealRep.mulC x₁ y₁ ≈ᵣ CRealRep.mulC x₂ y₂ := by
  refine CReal.Pre.equiv_trans (toPre_mulC_equiv (AQ := AQ) x₁ y₁) ?_
  refine CReal.Pre.equiv_trans ?_ (CReal.Pre.equiv_symm (toPre_mulC_equiv (AQ := AQ) x₂ y₂))
  exact CReal.mul_respects_equiv (x₁ := x₁.toPre) (x₂ := x₂.toPre) (y₁ := y₁.toPre) (y₂ := y₂.toPre) hx hy

theorem subC_respects_equiv {x₁ x₂ y₁ y₂ : CRealRep AQ} (hx : x₁ ≈ᵣ x₂) (hy : y₁ ≈ᵣ y₂) :
    CRealRep.subC x₁ y₁ ≈ᵣ CRealRep.subC x₂ y₂ := by
  dsimp [CRealRep.subC]
  exact addC_respects_equiv (AQ := AQ) hx (neg_respects_equiv (AQ := AQ) hy)

theorem invC_respects_equiv {x y : CRealRep AQ} (h : x ≈ᵣ y)
    (Wx : CReal.Pre.InvWitness x.toPre) (Wy : CReal.Pre.InvWitness y.toPre) :
    CRealRep.invC x Wx ≈ᵣ CRealRep.invC y Wy := by
  refine CReal.Pre.equiv_trans (toPre_invC_equiv (AQ := AQ) x Wx) ?_
  refine CReal.Pre.equiv_trans ?_ (CReal.Pre.equiv_symm (toPre_invC_equiv (AQ := AQ) y Wy))
  -- `inv_respects_equiv` lives in the nested namespace created in `CRealPre.lean`.
  exact CReal.Pre.CReal.Pre.inv_respects_equiv x.toPre y.toPre h Wx Wy

theorem divC_respects_equiv {x₁ x₂ y₁ y₂ : CRealRep AQ} (hx : x₁ ≈ᵣ x₂) (hy : y₁ ≈ᵣ y₂)
    (Wy₁ : CReal.Pre.InvWitness y₁.toPre) (Wy₂ : CReal.Pre.InvWitness y₂.toPre) :
    CRealRep.divC x₁ y₁ Wy₁ ≈ᵣ CRealRep.divC x₂ y₂ Wy₂ := by
  dsimp [CRealRep.divC]
  exact mulC_respects_equiv (AQ := AQ) hx (invC_respects_equiv (AQ := AQ) hy Wy₁ Wy₂)

/-! ### Denotation into the existing extensional `CReal` (ℚ-quotient) -/

/-- Denote a computational representative as an extensional `CReal`. -/
def denote (x : CRealRep AQ) : CReal := Quotient.mk _ x.toPre

theorem denote_congr {x y : CRealRep AQ} (h : x ≈ᵣ y) : denote (AQ := AQ) x = denote (AQ := AQ) y :=
  Quotient.sound h

theorem denote_zero : denote (AQ := AQ) (CRealRep.zero (AQ := AQ)) = (0 : CReal) := by
  refine Quotient.sound ?_
  exact toPre_zero_equiv (AQ := AQ)

theorem denote_one : denote (AQ := AQ) (CRealRep.one (AQ := AQ)) = (1 : CReal) := by
  refine Quotient.sound ?_
  exact toPre_one_equiv (AQ := AQ)

theorem denote_neg (x : CRealRep AQ) : denote (AQ := AQ) (CRealRep.neg x) = - denote (AQ := AQ) x := by
  refine Quotient.sound ?_
  exact toPre_neg_equiv (AQ := AQ) x

theorem denote_add (x y : CRealRep AQ) :
    denote (AQ := AQ) (CRealRep.add x y) = denote (AQ := AQ) x + denote (AQ := AQ) y := by
  refine Quotient.sound ?_
  exact toPre_add_equiv (AQ := AQ) x y

theorem denote_mul (x y : CRealRep AQ) :
    denote (AQ := AQ) (CRealRep.mul x y) = denote (AQ := AQ) x * denote (AQ := AQ) y := by
  refine Quotient.sound ?_
  exact toPre_mul_equiv (AQ := AQ) x y

theorem denote_compress (x : CRealRep AQ) : denote (AQ := AQ) (CRealRep.compress x) = denote (AQ := AQ) x := by
  refine Quotient.sound ?_
  exact toPre_compress_equiv (AQ := AQ) x

theorem denote_addC (x y : CRealRep AQ) :
    denote (AQ := AQ) (CRealRep.addC x y) = denote (AQ := AQ) x + denote (AQ := AQ) y := by
  refine Quotient.sound ?_
  exact toPre_addC_equiv (AQ := AQ) x y

theorem denote_mulC (x y : CRealRep AQ) :
    denote (AQ := AQ) (CRealRep.mulC x y) = denote (AQ := AQ) x * denote (AQ := AQ) y := by
  refine Quotient.sound ?_
  exact toPre_mulC_equiv (AQ := AQ) x y

theorem denote_subC (x y : CRealRep AQ) :
    denote (AQ := AQ) (CRealRep.subC x y) = denote (AQ := AQ) x - denote (AQ := AQ) y := by
  dsimp [CRealRep.subC]
  -- `sub` on `CReal` is `add` + `neg`
  simp [sub_eq_add_neg, denote_addC, denote_neg]

theorem denote_invC (x : CRealRep AQ) (W : CReal.Pre.InvWitness x.toPre) :
    denote (AQ := AQ) (CRealRep.invC x W) = Quotient.mk _ (CReal.Pre.inv x.toPre W) := by
  refine Quotient.sound ?_
  exact toPre_invC_equiv (AQ := AQ) x W

theorem denote_divC (x y : CRealRep AQ) (Wy : CReal.Pre.InvWitness y.toPre) :
    denote (AQ := AQ) (CRealRep.divC x y Wy) =
      denote (AQ := AQ) x * Quotient.mk _ (CReal.Pre.inv y.toPre Wy) := by
  dsimp [CRealRep.divC]
  -- use the multiplicative correctness of `mulC` and the spec correctness of `invC`
  simp [denote_mulC, denote_invC]

end CRealRep

/-- Dyadic computational representatives for computable reals. -/
abbrev CRealDyadicRep : Type := CRealRep Dyadic

end Computable
