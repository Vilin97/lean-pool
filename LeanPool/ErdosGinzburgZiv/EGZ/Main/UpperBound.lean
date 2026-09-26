/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Asymptotics
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Multiplicity

/-!
# The exact finite target for the main theorem

The final section first proves a zero-sum assertion at a ceiling length. This is
enough for `MainUpperBound`, but the ceiling must be absorbed using a smaller
internal error parameter.  It cannot simply be dropped.
-/

@[expose] public section

namespace EGZ

/-- The finite multiplicity statement to be supplied by the structural
argument.  The prime threshold is uniform over the input multiset. -/
def EventualCeilZeroSum (d : ℕ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ P : ℕ, ∀ (p : ℕ) (hp : p.Prime), P < p →
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ f : FpCoord p d → ℕ,
        natMass f = ⌈((hollowConstant p d : ℝ) + ζ) * (p : ℝ)⌉₊ →
        HasZeroSumMultiplicity f

/-- Absorb the ceiling by applying the finite theorem with half the
requested error (or less), and then taking sufficiently large primes. -/
theorem mainUpperBound_of_eventualCeilZeroSum (d : ℕ)
    (h : EventualCeilZeroSum d) : MainUpperBound d := by
  intro ε hε
  let ζ : ℝ := min (ε / 2) (1 / 2)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hζε : ζ ≤ ε / 2 := min_le_left _ _
  obtain ⟨P, hP⟩ := h ζ hζ hζ1
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  rw [atTopAlongPrimes, Filter.eventually_inf_principal]
  filter_upwards [Filter.eventually_gt_atTop (max P N)] with p hp hpPrime
  let : NeZero p := ⟨hpPrime.ne_zero⟩
  have hPP : P < p := (le_max_left _ _).trans_lt hp
  have hNP : (N : ℝ) < (p : ℝ) := by
    exact_mod_cast (le_max_right P N).trans_lt hp
  have hlarge : 1 ≤ (ε / 2) * (p : ℝ) := by
    have h' : 2 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hprop : EGZProperty p d
      ⌈((hollowConstant p d : ℝ) + ζ) * (p : ℝ)⌉₊ :=
    egzProperty_of_multiplicity (hP p hpPrime hPP)
  have hmin : (egzConstant p d : ℝ) ≤
      (⌈((hollowConstant p d : ℝ) + ζ) * (p : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast egzConstant_min hprop
  have hnonneg : 0 ≤ ((hollowConstant p d : ℝ) + ζ) * (p : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hζε hp0]

/-- The completed lower estimate and polynomial bound turn the corrected
finite target into the paper's asymptotic statement. -/
theorem mainAsymptotic_of_eventualCeilZeroSum (d : ℕ) (hd : 0 < d)
    (h : EventualCeilZeroSum d) : MainAsymptotic d :=
  mainAsymptotic_of_mainUpperBound d hd
    (mainUpperBound_of_eventualCeilZeroSum d h)

end EGZ
