/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
-- RakeSieve uses a rake to implement a prime sieve.
import LeanPool.Leansieve.RakeMap.RakeMap
import LeanPool.Leansieve.PrimeSieve.PrimeSieve

/-!
# A concrete prime sieve (`RakeSieve`)

`RakeSieve` instantiates the generic `PrimeSieve` correctness logic with a
concrete rake-based representation of the residue set. `init` builds the state
for the numbers coprime to `2`; `next` sifts out multiples of the current prime;
and the `PrimeSieveState`/`PrimeSieveDriver` instances tie these to the abstract
correctness proofs, yielding a sieve-of-Eratosthenes-style prime generator.
-/

namespace Leansieve

/-- A concrete sieve state: a rake map enumerating the residue set `R p`,
together with the current prime `p` and the next candidate `c`. -/
structure RakeSieve where
  /-- The predicate characterizing the residue set. -/
  prop : Nat → Prop
  /-- The rake map enumerating `prop`. -/
  rm : RakeMap prop
  /-- The current prime. -/
  p : NPrime               -- the current prime
  /-- The candidate for the next prime. -/
  c : Nat                  -- the candidate for next prime
  /-- `prop` agrees with membership in the residue set `R p`. -/
  hprop : ∀ n : Nat, prop n ↔ n ∈ R p
  /-- The candidate lies in the residue set. -/
  hCinR : c ∈ R p
  /-- The candidate is the minimum of the residue set. -/
  hRmin : ∀ r ∈ R p, c ≤ r
  -- Q : Array RakeMap     -- queue of found primes

namespace RakeSieve

open RakeMap

/-- The initial sieve state: the numbers coprime to `2`, current prime `2`,
candidate `3`. -/
def init : RakeSieve :=
  let rm : RakeMap (fun n => n ≥ 2 ∧ ¬2 ∣ n) := rmGe2 |>.rem 2 (by simp) (by
    use 3; use 1; simp[rmGe2, Rake.ge2, Rake.term])
  let p := ⟨2, Nat.prime_two⟩
  { prop := rm.pred, rm := rm, p := p, c := 3,
    hprop := by
      have hrm : rm.pred = fun n => n ≥ 2 ∧ ¬ 2 ∣ n := by simp[RakeMap.pred]
      -- goal: `∀ n, rm.pred n ↔ n ∈ R p`
      have hbij := rm.hbij
      unfold R; simp_all only [ge_iff_le, Nat.two_dvd_ne_zero, Set.mem_setOf_eq]; intro n
      apply Iff.intro
      case mp =>
        intro hn
        apply And.intro
        · rw[← hbij] at hn; exact hn.left
        · intro q hq hq'
          simp only [← hbij] at hn
          have hp2 : (p : Nat) = 2 := rfl
          have hq2 : 2 ≤ q := Nat.Prime.two_le hq'
          have : 2 = q := by omega
          rw[this] at hn
          omega
      case mpr =>
        simp only [and_imp]; intro hn hn2; rw[←hbij]; simp_all only [true_and]
        have hp2 : p.val = 2 := by rfl
        have hn2' := hn2
        set p' := p.val
        specialize hn2' p'; simp only [hp2, Std.le_refl, Nat.two_dvd_ne_zero, forall_const] at hn2'
        exact hn2' Nat.prime_two
    hCinR := by
      -- clearly 3 isn't divisible by 2, so is in r
      unfold R; simp only [ge_iff_le, Set.mem_setOf_eq, Nat.reduceLeDiff, true_and]
      intro q hqle hq'
      have hp2 : (p : Nat) = 2 := rfl
      have hq2 : 2 ≤ q := Nat.Prime.two_le hq'
      have : q = 2 := by omega
      aesop
    hRmin := by
      -- to show that every number in R 2 is ≥ 3,
      -- show that an r∈R 2 where r<3 leads to a contradiction.
      dsimp[R]; intro r ⟨hr, hrr⟩; by_contra h; simp_all
      -- r ≥ 2 and r < 3, so r must be 2
      have r2 : r = 2 := by omega
      -- but R 2 means not divisible by primes ≤ 2
      -- now we can use hrr to prove ¬2∣2, which is absurd
      have := Nat.prime_two; aesop }

/-- Advance the sieve: sift out multiples of the current prime, yielding the
next sieve state with the old candidate as the new prime. -/
def next (rs₀ : RakeSieve) (hC₀ : Nat.Prime rs₀.c) (hNS : nosk' rs₀.p rs₀.c) : RakeSieve :=
  let h₀ := rs₀.prop
  have hh₀ : ∀ n, h₀ n ↔ n ∈ R rs₀.p := rs₀.hprop
  have hCR₀ := rs₀.hCinR
  have hpgt : PrimeGt rs₀.p rs₀.c := by
    constructor
    · exact hC₀
    · exact r_gt_p (↑rs₀.p) rs₀.c hCR₀
  have hmin : ∀ q < rs₀.c, ¬PrimeGt (↑rs₀.p) q := by
    simp_all only [not_exists, not_and, not_lt]; intro q hq hq'; apply hNS at hq'; omega
  let c' : MinPrimeGt rs₀.p := { p := rs₀.c, hpgt := hpgt, hmin := hmin}
  -- to call `rem`, we have to prove that it won't remove everything.
  -- so we must produce a proof that another prime besides c exists.
  have : ∃ n m, ¬c'.p ∣ n ∧ rs₀.rm.term m = n := by
    have hC₀' : Nat.Prime rs₀.c := hC₀
    obtain ⟨q, hqgt, hq⟩ : ∃ q, rs₀.c.succ ≤ q ∧ Nat.Prime q :=
      Nat.exists_infinite_primes rs₀.c.succ
    have hqR : q ∈ R rs₀.p := by
      unfold R
      constructor
      · exact Nat.Prime.two_le hq
      · intro q' hq'le hq' hdiv
        have : q' = q := Nat.prime_dvd_prime_iff_eq hq' hq |>.mp hdiv
        omega
    have hqprop : rs₀.prop q := (hh₀ q).mpr hqR
    obtain ⟨m, hm⟩ := (rs₀.rm.hbij q).mp hqprop
    refine ⟨q, m, ?_, hm⟩
    intro hdiv
    have : rs₀.c = q := Nat.prime_dvd_prime_iff_eq hC₀' hq |>.mp hdiv
    omega
  -- now we can use this fact to remove multiples of c
  let rs := rs₀.rm.rem c'.p (Nat.Prime.pos hC₀) this
  let c₁ := rs.rake.term 0
  have hc₁ : ∃ i, rs.rake.term i = c₁ := by
    exact exists_apply_eq_apply (fun a => rs.rake.term a) 0
  let h₁ := rs.pred
  have hh₁ : ∀ n, h₁ n ↔ h₀ n ∧ ¬(c'.p ∣ n) := by
    intro n
    rfl
  have hprop : ∀ n, h₁ n ↔ n ∈ R c'.p := by
    intro n; exact r_next_prop (hh₀ n) (hh₁ n)
  { prop := rs.pred, rm := rs, p := ⟨c'.p, hC₀⟩, c := c₁,
    hprop := hprop
    hCinR := by
      -- goal: `c₁ ∈ R c'.p`
      have : h₁ c₁ := by rw[← rs.hbij] at hc₁; exact hc₁
      specialize hprop c₁
      exact hprop.mp this
    hRmin := by
      dsimp[c₁, p, h₁] at *
      intro r hr
      have : ∃ k, rs.rake.term k = r := by
        exact (rs.hbij r).mp ((hprop r).mpr hr)
      obtain ⟨k, hk⟩ := this
      rw[←hk]
      exact rs.min_term_zero k }

instance : PrimeSieveState RakeSieve where
  P x := x.p
  C x := x.c
  next := .next
  hNext := by
    intro s hC hNS s' hs'; simp_all only [gt_iff_lt]; rw[←hs']
    unfold next at hs'; simp at hs'
    have hpc : s'.p = s.c := by simp_all
    apply And.intro
    · exact hpc
    · -- goal: `s'.c > s.c`
      have := s'.hCinR
      have := r_gt_p
      aesop

open PrimeSieveState

instance : PrimeSieveDriver RakeSieve where
  hCinR x := by dsimp[C]; dsimp[P]; exact x.hCinR
  hRmin x := by dsimp[C]; dsimp[P]; exact x.hRmin

end RakeSieve

end Leansieve
