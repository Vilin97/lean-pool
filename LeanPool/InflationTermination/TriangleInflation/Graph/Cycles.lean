/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanPool.InflationTermination.TriangleInflation.Graph.FivePath

/-!
# Cycles (A5)

Statements split from the original `Statements.lean` skeleton (one file per proving task).
See AUDIT-NOTES A5 and the packet sources `B4-cycles-and-stronger-hierarchies.md` (§3-6) and
`B5-pair-source-classification.md` (§4) for the mathematics.

The Walsh section is general Boolean-cube Fourier analysis (orthogonality, inversion,
uniqueness) and is reusable by the other pair-source files.
-/

@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## Walsh characters on a finite Boolean cube -/

section Walsh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_sgn_mul_self (F : Finset ι) (w : ι → Bool) :
    (∏ v ∈ F, sgn (w v)) * (∏ v ∈ F, sgn (w v)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ => sgn_mul_self _

/-- A Walsh character as a product over the whole index type. -/
theorem prod_sgn_eq_prod_univ (F : Finset ι) (w : ι → Bool) :
    (∏ v ∈ F, sgn (w v)) = ∏ v : ι, (if v ∈ F then sgn (w v) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

omit [Fintype ι] in
/-- The product of two Walsh characters is the character of their symmetric difference. -/
theorem prod_sgn_mul_prod_sgn [Finite ι] (F F' : Finset ι) (w : ι → Bool) :
    (∏ v ∈ F', sgn (w v)) * (∏ v ∈ F, sgn (w v)) = ∏ v ∈ symmDiff F' F, sgn (w v) := by
  classical
  let := Fintype.ofFinite ι
  rw [prod_sgn_eq_prod_univ, prod_sgn_eq_prod_univ, prod_sgn_eq_prod_univ,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases h1 : v ∈ F' <;> by_cases h2 : v ∈ F <;>
    simp [h1, h2, Finset.mem_symmDiff, sgn_mul_self]

/-- Orthogonality of the Walsh characters on `ι → Bool`. -/
theorem sum_prod_sgn (F : Finset ι) :
    (∑ w : ι → Bool, ∏ v ∈ F, sgn (w v)) = if F = ∅ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp_rw [prod_sgn_eq_prod_univ]
  rw [← Fintype.prod_sum (fun (v : ι) (b : Bool) => if v ∈ F then sgn b else 1)]
  by_cases hF : F = ∅
  · subst hF
    simp
  · rw [ite_eq_right hF]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hF
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simp [hv, sgn]

omit [DecidableEq ι] in
/-- The Walsh characters are their own dual basis. -/
theorem sum_prod_sgn_mul (u w : ι → Bool) :
    (∑ F : Finset ι, ∏ v ∈ F, (sgn (u v) * sgn (w v)))
      = if u = w then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have h := Fintype.prod_add (fun v : ι => sgn (u v) * sgn (w v)) (fun _ : ι => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  by_cases huw : u = w
  · subst huw
    rw [ite_eq_left rfl]
    rw [Finset.prod_congr rfl (fun v _ => by rw [sgn_mul_self]), Finset.prod_const,
      Finset.card_univ]
    norm_num
  · rw [ite_eq_right huw]
    obtain ⟨v, hv⟩ : ∃ v, u v ≠ w v := by
      by_contra hc
      exact huw (funext fun v => by simpa using not_exists.1 hc v)
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    cases hu : u v <;> cases hw : w v <;> simp_all [sgn]

/-- **Walsh uniqueness.** Two weight functions on a finite Boolean cube with the same Walsh
moments are equal. -/
theorem eq_of_walsh_moments_eq (P Q : (ι → Bool) → ℝ)
    (h : ∀ F : Finset ι, (∑ w : ι → Bool, P w * ∏ v ∈ F, sgn (w v))
      = ∑ w : ι → Bool, Q w * ∏ v ∈ F, sgn (w v)) : P = Q := by
  have key : ∀ (R : (ι → Bool) → ℝ) (w : ι → Bool),
      (∑ F : Finset ι, (∑ u : ι → Bool, R u * ∏ v ∈ F, sgn (u v)) * ∏ v ∈ F, sgn (w v))
        = (2 : ℝ) ^ Fintype.card ι * R w := by
    intro R w
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have step : ∀ u : ι → Bool,
        (∑ F : Finset ι, R u * (∏ v ∈ F, sgn (u v)) * ∏ v ∈ F, sgn (w v))
          = R u * ∑ F : Finset ι, ∏ v ∈ F, (sgn (u v) * sgn (w v)) := by
      intro u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [Finset.prod_mul_distrib]; ring
    simp_rw [step, sum_prod_sgn_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ w (fun u => R u * (2 : ℝ) ^ Fintype.card ι)]
    simp [mul_comm]
  funext w
  have h1 := key P w
  have h2 := key Q w
  simp_rw [h] at h1
  rw [h2] at h1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  exact (mul_right_cancel₀ (ne_of_gt hpow)
    (by linarith [h1] : Q w * (2:ℝ)^Fintype.card ι =
      P w * (2:ℝ)^Fintype.card ι)).symm

end Walsh


/-! ## The boundary map of the cycle -/

section CycleBoundary

variable {m : ℕ}

/-- The successor vertex on the cycle `C_m`. The edge recorded by `v` joins `v` and
`cycleNext v`. -/
def cycleNext (v : Fin m) : Fin m := ⟨(v.val + 1) % m, Nat.mod_lt _ v.pos⟩

theorem mem_cycleBoundary (F : Finset (Fin m)) (v : Fin m) :
    v ∈ cycleBoundary m F ↔ ¬((v ∈ F) ↔ (cycleNext v ∈ F)) := by
  simp [cycleBoundary, cycleNext, eq_iff_iff]

theorem cycleNext_injective : Function.Injective (cycleNext (m := m)) := by
  intro a b hab
  have h : (a.val + 1) % m = (b.val + 1) % m := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge (a.val + 1) m with h1 | h1 <;>
    rcases Nat.lt_or_ge (b.val + 1) m with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
    exact Fin.ext (by omega)
  · exfalso
    have hb' : b.val + 1 = m := by omega
    rw [Nat.mod_eq_of_lt h1, hb', Nat.mod_self] at h
    omega
  · exfalso
    have ha' : a.val + 1 = m := by omega
    rw [Nat.mod_eq_of_lt h2, ha', Nat.mod_self] at h
    omega
  · exact Fin.ext (by omega)

theorem prod_cycleNext (f : Fin m → ℝ) : (∏ v : Fin m, f (cycleNext v)) = ∏ v : Fin m, f v :=
  Fintype.prod_bijective cycleNext
    ((Finite.injective_iff_bijective).1 cycleNext_injective) _ _ (fun _ => rfl)

theorem cycleBoundary_empty : cycleBoundary m (∅ : Finset (Fin m)) = ∅ := by
  ext v; simp [mem_cycleBoundary]

theorem cycleBoundary_univ : cycleBoundary m (Finset.univ : Finset (Fin m)) = ∅ := by
  ext v; simp [mem_cycleBoundary]

theorem cycleBoundary_compl (F : Finset (Fin m)) : cycleBoundary m Fᶜ = cycleBoundary m F := by
  ext v; simp only [mem_cycleBoundary, Finset.mem_compl]; tauto

/-- The source boundary of a vertex set of the cycle has even size. -/
theorem cycleBoundary_card_even (F : Finset (Fin m)) : Even (cycleBoundary m F).card := by
  set σ : Fin m → ℝ := fun v => if v ∈ F then -1 else 1 with hσ
  have hpt : ∀ v : Fin m,
      (if ¬((v ∈ F) ↔ (cycleNext v ∈ F)) then (-1 : ℝ) else 1) = σ v * σ (cycleNext v) := by
    intro v
    by_cases h1 : v ∈ F <;> by_cases h2 : cycleNext v ∈ F <;> simp [hσ, h1, h2]
  have h1 : (∏ v : Fin m, (if ¬((v ∈ F) ↔ (cycleNext v ∈ F)) then (-1 : ℝ) else 1))
      = (-1 : ℝ) ^ (cycleBoundary m F).card := by
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 2
    ext v
    simp [mem_cycleBoundary]
  have h2 : (∏ v : Fin m, σ v * σ (cycleNext v)) = 1 := by
    rw [Finset.prod_mul_distrib, prod_cycleNext, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun v _ => by by_cases h : v ∈ F <;> simp [hσ, h]
  have h3 : (-1 : ℝ) ^ (cycleBoundary m F).card = 1 := by
    rw [← h1]
    simp_rw [hpt]
    exact h2
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h3

/-- A vertex set of the cycle is determined by its source boundary together with the
membership of the vertex `0`. -/
theorem cycle_eq_of_boundary_eq (hm : 0 < m) {F F' : Finset (Fin m)}
    (hb : cycleBoundary m F = cycleBoundary m F')
    (h0 : ((⟨0, hm⟩ : Fin m) ∈ F ↔ (⟨0, hm⟩ : Fin m) ∈ F')) : F = F' := by
  have key : ∀ (j : ℕ) (hj : j < m), ((⟨j, hj⟩ : Fin m) ∈ F ↔ (⟨j, hj⟩ : Fin m) ∈ F') := by
    intro j
    induction j with
    | zero => intro hj; exact h0
    | succ n ih =>
      intro hj
      have hn : n < m := Nat.lt_of_succ_lt hj
      have hstep : cycleNext (⟨n, hn⟩ : Fin m) = ⟨n + 1, hj⟩ :=
        Fin.ext (by simp only [cycleNext]; exact Nat.mod_eq_of_lt hj)
      have h1 := ih hn
      have h2 : ((⟨n, hn⟩ : Fin m) ∈ cycleBoundary m F)
          ↔ ((⟨n, hn⟩ : Fin m) ∈ cycleBoundary m F') := by rw [hb]
      rw [mem_cycleBoundary, mem_cycleBoundary, hstep] at h2
      tauto
  ext v
  have := key v.val v.isLt
  simpa using this

theorem cycleBoundary_eq_empty_iff (hm : 0 < m) (F : Finset (Fin m)) :
    cycleBoundary m F = ∅ ↔ F = ∅ ∨ F = Finset.univ := by
  constructor
  · intro h
    by_cases h0 : (⟨0, hm⟩ : Fin m) ∈ F
    · exact Or.inr (cycle_eq_of_boundary_eq hm (by rw [h, cycleBoundary_univ]) (by simp [h0]))
    · exact Or.inl (cycle_eq_of_boundary_eq hm (by rw [h, cycleBoundary_empty]) (by simp [h0]))
  · rintro (rfl | rfl)
    · exact cycleBoundary_empty
    · exact cycleBoundary_univ

end CycleBoundary



/-! ## A5: the cycle target is a law -/

section CycleTarget

variable {m : ℕ}

theorem cycleTarget_sum (m : ℕ) (q : ℝ) :
    (∑ w : Fin m → Bool, cycleTarget m q w) = 1 := by
  simp only [cycleTarget]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ F : Finset (Fin m),
      (∑ w : Fin m → Bool, (-q) ^ ((cycleBoundary m F).card / 2) * ∏ v ∈ F, sgn (w v))
        = (-q) ^ ((cycleBoundary m F).card / 2) * (if F = ∅ then (2 : ℝ) ^ m else 0) := by
    intro F
    rw [← Finset.mul_sum, sum_prod_sgn]
    simp
  simp_rw [h1, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (Fin m))
    (fun F => (-q) ^ ((cycleBoundary m F).card / 2) * (2 : ℝ) ^ m)]
  rw [ite_eq_left (Finset.mem_univ _), cycleBoundary_empty]
  simp only [Finset.card_empty, Nat.zero_div, pow_zero, one_mul]
  rw [← mul_pow]
  norm_num

/-- The cycle target vanishes on the odd-parity outcomes and is bounded below by
`(1/2)^m (2 - 2((1+√q)^m - 1))` on the even-parity ones. -/
theorem cycleTarget_nonneg (m : ℕ) (hm : 0 < m) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : (m : ℝ) ^ 2 * q ≤ 1 / 4) (w : Fin m → Bool) : 0 ≤ cycleTarget m q w := by
  set ρ := Real.sqrt q with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg q
  have hρsq : ρ * ρ = q := Real.mul_self_sqrt hq0
  have hmρ : (m : ℝ) * ρ ≤ 1 / 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hρ0, sq_nonneg ((m : ℝ) * ρ)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hρhalf : ρ ≤ 1 / 2 := by nlinarith
  -- `(1+ρ)^m ≤ 2`, by Bernoulli on `(1-ρ)^m` and `(1-ρ²)^m ≤ 1`
  have hexp : (1 + ρ) ^ m ≤ 2 := by
    have hb : 1 + (m : ℝ) * (-ρ) ≤ (1 + -ρ) ^ m := one_add_mul_le_pow (by linarith) m
    have hb2 : (1 : ℝ) / 2 ≤ (1 - ρ) ^ m := by
      have h3 : (1 + -ρ) ^ m = (1 - ρ) ^ m := by ring_nf
      rw [h3] at hb
      linarith
    have hmul : (1 + ρ) ^ m * (1 - ρ) ^ m ≤ 1 := by
      rw [← mul_pow]
      have h1 : (1 + ρ) * (1 - ρ) = 1 - ρ * ρ := by ring
      rw [h1]
      exact pow_le_one₀ (by nlinarith) (by nlinarith)
    have hpos : (0 : ℝ) ≤ (1 + ρ) ^ m := by positivity
    nlinarith
  set T : Finset (Fin m) → ℝ :=
    fun F => (-q) ^ ((cycleBoundary m F).card / 2) * ∏ v ∈ F, sgn (w v) with hTdef
  have habs : ∀ F : Finset (Fin m), |T F| = ρ ^ (cycleBoundary m F).card := by
    intro F
    have hprod : |∏ v ∈ F, sgn (w v)| = 1 := by
      have := prod_sgn_mul_self F w
      have h2 : |∏ v ∈ F, sgn (w v)| * |∏ v ∈ F, sgn (w v)| = 1 := by
        rw [← abs_mul, this, abs_one]
      nlinarith [abs_nonneg (∏ v ∈ F, sgn (w v))]
    rw [hTdef]
    simp only [abs_mul, hprod, mul_one, abs_pow, abs_neg, abs_of_nonneg hq0]
    obtain ⟨j, hj⟩ := cycleBoundary_card_even F
    rw [hj]
    have : (j + j) / 2 = j := by omega
    rw [this, ← hρsq]
    ring
  have hprod_univ : (∏ v : Fin m, sgn (w v)) = 1 ∨ (∏ v : Fin m, sgn (w v)) = -1 :=
    mul_self_eq_one_iff.1 (prod_sgn_mul_self Finset.univ w)
  have hzero : ∀ F : Finset (Fin m),
      (∏ v ∈ Fᶜ, sgn (w v)) = (∏ v : Fin m, sgn (w v)) * ∏ v ∈ F, sgn (w v) := by
    intro F
    have h := Finset.prod_mul_prod_compl F (fun v => sgn (w v))
    have hs := prod_sgn_mul_self F w
    linear_combination (∏ v ∈ F, sgn (w v)) * h - (∏ v ∈ Fᶜ, sgn (w v)) * hs
  have key : 0 ≤ ∑ F : Finset (Fin m), T F := by
    rcases hprod_univ with hp | hp
    · -- even parity
      have hsub : ({∅, Finset.univ} : Finset (Finset (Fin m))) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hne : (∅ : Finset (Fin m)) ≠ Finset.univ := by
        intro h
        have : (⟨0, hm⟩ : Fin m) ∈ (∅ : Finset (Fin m)) := by rw [h]; exact Finset.mem_univ _
        simp at this
      have hsplit := Finset.sum_sdiff (f := T) hsub
      rw [Finset.sum_pair hne] at hsplit
      have hT0 : T ∅ = 1 := by
        rw [hTdef]; simp [cycleBoundary_empty]
      have hT1 : T Finset.univ = 1 := by
        rw [hTdef]; simp [cycleBoundary_univ, hp]
      rw [hT0, hT1] at hsplit
      -- the remaining terms are small
      set D : Finset (Finset (Fin m)) := Finset.univ \ {∅, Finset.univ} with hD
      have hDmem : ∀ F ∈ D, cycleBoundary m F ≠ ∅ := by
        intro F hF hb
        rw [hD, Finset.mem_sdiff] at hF
        rcases (cycleBoundary_eq_empty_iff hm F).1 hb with h | h
        · exact hF.2 (by simp [h])
        · exact hF.2 (by simp [h])
      have hfib : ∀ E : Finset (Fin m),
          ((D.filter (fun F => cycleBoundary m F = E)).card : ℕ) ≤ 2 := by
        intro E
        have : (D.filter (fun F => cycleBoundary m F = E)).card
            ≤ (Finset.univ : Finset Bool).card := by
          refine Finset.card_le_card_of_injOn
            (fun F => decide ((⟨0, hm⟩ : Fin m) ∈ F)) (fun _ _ => Finset.mem_univ _) ?_
          intro F hF F' hF' hEq
          simp only [Finset.mem_coe, Finset.mem_filter] at hF hF'
          refine cycle_eq_of_boundary_eq hm (by rw [hF.2, hF'.2]) ?_
          simpa using congrArg (fun b => b = true) hEq
        simpa using this
      have hbound : (∑ F ∈ D, |T F|) ≤ 2 := by
        have e1 : (∑ F ∈ D, |T F|) = ∑ F ∈ D, ρ ^ (cycleBoundary m F).card :=
          Finset.sum_congr rfl fun F _ => habs F
        have e2 : (∑ F ∈ D, ρ ^ (cycleBoundary m F).card)
            = ∑ E : Finset (Fin m), ∑ F ∈ D.filter (fun F => cycleBoundary m F = E),
                ρ ^ E.card :=
          (Finset.sum_fiberwise' D (cycleBoundary m) (fun E => ρ ^ E.card)).symm
        have e3 : ∀ E : Finset (Fin m),
            (∑ F ∈ D.filter (fun F => cycleBoundary m F = E), ρ ^ E.card)
              ≤ if E = ∅ then 0 else 2 * ρ ^ E.card := by
          intro E
          by_cases hE : E = ∅
          · subst hE
            rw [ite_eq_left rfl]
            have : D.filter (fun F => cycleBoundary m F = ∅) = ∅ := by
              refine Finset.filter_eq_empty_iff.2 ?_
              intro F hF
              exact hDmem F hF
            rw [this]
            simp
          · rw [ite_eq_right hE, Finset.sum_const, nsmul_eq_mul]
            have hcard := hfib E
            have hpos : (0 : ℝ) ≤ ρ ^ E.card := pow_nonneg hρ0 _
            have : ((D.filter (fun F => cycleBoundary m F = E)).card : ℝ) ≤ 2 := by
              exact_mod_cast hcard
            nlinarith
        have e4 : (∑ E : Finset (Fin m), if E = ∅ then (0 : ℝ) else 2 * ρ ^ E.card)
            = 2 * ((1 + ρ) ^ m - 1) := by
          have hsplit2 : ∀ E : Finset (Fin m),
              (if E = ∅ then (0 : ℝ) else 2 * ρ ^ E.card)
                = 2 * ρ ^ E.card - (if E = ∅ then 2 * ρ ^ E.card else 0) := by
            intro E; by_cases h : E = ∅ <;> simp [h]
          simp_rw [hsplit2]
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (∅ : Finset (Fin m))
            (fun E => 2 * ρ ^ E.card)]
          have hgeom : (∑ E : Finset (Fin m), ρ ^ E.card) = (1 + ρ) ^ m := by
            have := Fintype.prod_add (fun _ : Fin m => ρ) (fun _ : Fin m => (1 : ℝ))
            simp only [Finset.prod_const_one, mul_one, Finset.prod_const] at this
            rw [← this]
            simp [add_comm]
          rw [← Finset.mul_sum, hgeom]
          simp only [Finset.mem_univ, ite_true, Finset.card_empty, pow_zero, mul_one]
          ring
        calc (∑ F ∈ D, |T F|) = ∑ F ∈ D, ρ ^ (cycleBoundary m F).card := e1
          _ = ∑ E : Finset (Fin m), ∑ F ∈ D.filter (fun F => cycleBoundary m F = E),
                ρ ^ E.card := e2
          _ ≤ ∑ E : Finset (Fin m), if E = ∅ then (0 : ℝ) else 2 * ρ ^ E.card :=
              Finset.sum_le_sum fun E _ => e3 E
          _ = 2 * ((1 + ρ) ^ m - 1) := e4
          _ ≤ 2 := by nlinarith
      have hge : -(2 : ℝ) ≤ ∑ F ∈ D, T F := by
        have := Finset.abs_sum_le_sum_abs T D
        have h2 : |∑ F ∈ D, T F| ≤ 2 := le_trans this hbound
        cases abs_le.1 h2 with
        | intro h3 _ => exact h3
      linarith [hsplit]
    · -- odd parity: the Fourier sum vanishes term by term
      have hvanish : (∑ F : Finset (Fin m), T F) = 0 := by
        refine Finset.sum_ninvolution (fun F => Fᶜ) ?_ ?_ (fun _ => Finset.mem_univ _) ?_
        · intro F
          rw [hTdef]
          simp only
          rw [cycleBoundary_compl, hzero F, hp]
          ring
        · intro F _ h
          have h0 : ((⟨0, hm⟩ : Fin m) ∈ Fᶜ) ↔ ((⟨0, hm⟩ : Fin m) ∈ F) := by rw [h]
          simp at h0
        · intro F; exact compl_compl F
      rw [hvanish]
  have : cycleTarget m q w = (1 / 2 : ℝ) ^ m * ∑ F : Finset (Fin m), T F := rfl
  rw [this]
  positivity

/-- The Walsh moments of the cycle target: the character of a vertex set `F` has moment
`(−q)^{|∂F|/2}` (AUDIT-NOTES A5; packet B5 §4, equation (12)). -/
theorem cycleTarget_moment (m : ℕ) (q : ℝ) (F : Finset (Fin m)) :
    (∑ w : Fin m → Bool, cycleTarget m q w * ∏ v ∈ F, sgn (w v))
      = (-q) ^ ((cycleBoundary m F).card / 2) := by
  have e1 : ∀ w : Fin m → Bool, cycleTarget m q w * ∏ v ∈ F, sgn (w v)
      = (1 / 2 : ℝ) ^ m * ∑ F' : Finset (Fin m),
          (-q) ^ ((cycleBoundary m F').card / 2) * ∏ v ∈ symmDiff F' F, sgn (w v) := by
    intro w
    simp only [cycleTarget]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F' _ => ?_
    rw [mul_assoc, prod_sgn_mul_prod_sgn]
  rw [Finset.sum_congr rfl fun w _ => e1 w, ← Finset.mul_sum, Finset.sum_comm]
  have e2 : ∀ F' : Finset (Fin m),
      (∑ w : Fin m → Bool, (-q) ^ ((cycleBoundary m F').card / 2) *
          ∏ v ∈ symmDiff F' F, sgn (w v))
        = (-q) ^ ((cycleBoundary m F').card / 2) *
            (if symmDiff F' F = ∅ then (2 : ℝ) ^ m else 0) := by
    intro F'
    rw [← Finset.mul_sum, sum_prod_sgn]
    simp
  simp_rw [e2, ← Finset.bot_eq_empty, symmDiff_eq_bot, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ F
    (fun F' => (-q) ^ ((cycleBoundary m F').card / 2) * (2 : ℝ) ^ m)]
  rw [ite_eq_left (Finset.mem_univ _)]
  have h2 : ((1 : ℝ) / 2) ^ m * (2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((-q) ^ ((cycleBoundary m F).card / 2)) * h2

end CycleTarget

/-! ## A5: every cycle -/

/-- The cycle target is a law when `m² q ≤ 1/4`: the nonconstant Fourier terms sum to at most
`∑_{j≥1} 4^{-j} = 1/3` of the uniform weight (AUDIT-NOTES A5). -/
theorem cycleTarget_isLaw (m : ℕ) (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : (m : ℝ) ^ 2 * q ≤ 1 / 4) : IsLaw (cycleTarget m q) :=
  ⟨fun w => cycleTarget_nonneg m (by omega) q hq0 hq w, cycleTarget_sum m q⟩

/-! ## A5: exact parity rigidity for the triangle -/

theorem exists_pos_of_isLaw {α : Type*} [Fintype α] (μ : α → ℝ) (h : IsLaw μ) :
    ∃ a, 0 < μ a := by
  by_contra hc
  push Not at hc
  have hz : ∑ a, μ a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (hc a) (h.1 a)
  rw [h.2] at hz
  norm_num at hz

/-- Products of numbers in `[-1,1]` stay in `[-1,1]`. -/
theorem neg_one_le_mul_le_one {u v : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v)
    (hv2 : v ≤ 1) : -1 ≤ u * v ∧ u * v ≤ 1 := by
  constructor <;> nlinarith

/-- A product of three numbers of `[-1,1]` equal to `1` forces all three to be signs. -/
theorem sq_eq_one_of_prod_eq_one {u v w : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v)
    (hv2 : v ≤ 1) (hw1 : -1 ≤ w) (hw2 : w ≤ 1) (h : u * v * w = 1) :
    u * u = 1 ∧ v * v = 1 ∧ w * w = 1 := by
  have habc : ∀ A B C : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ C → B ≤ 1 → C ≤ 1 → A * (B * C) = 1 → 1 ≤ A := by
    intro A B C hA hB hC hB1 hC1 hABC
    have h1 : B * C ≤ 1 := by nlinarith
    have h2 : A * (B * C) ≤ A * 1 := mul_le_mul_of_nonneg_left h1 hA
    rw [hABC, mul_one] at h2
    exact h2
  have huu : u * u ≤ 1 := by nlinarith
  have hvv : v * v ≤ 1 := by nlinarith
  have hww : w * w ≤ 1 := by nlinarith
  have hu0 : (0 : ℝ) ≤ u * u := mul_self_nonneg u
  have hv0 : (0 : ℝ) ≤ v * v := mul_self_nonneg v
  have hw0 : (0 : ℝ) ≤ w * w := mul_self_nonneg w
  have hsq : (u * u) * ((v * v) * (w * w)) = 1 := by linear_combination (u * v * w + 1) * h
  exact ⟨le_antisymm huu (habc _ _ _ hu0 hv0 hw0 hvv hww hsq),
    le_antisymm hvv (habc _ _ _ hv0 hu0 hw0 huu hww (by linear_combination hsq)),
    le_antisymm hww (habc _ _ _ hw0 hu0 hv0 huu hvv (by linear_combination hsq))⟩

private theorem triangleModel_mixed_moment (M : TriangleModel) (φ ψ χ : Bool → ℝ) :
  (∑ w : ThreeBit, φ w.1 * ψ w.2.1 * χ w.2.2 * M.law w)
    = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z *
        ((∑ β : Bool, φ β * respMass (M.f (x, z)) β) *
         (∑ β : Bool, ψ β * respMass (M.g (x, y)) β) *
         (∑ β : Bool, χ β * respMass (M.h (z, y)) β))
 := by
  -- the three-bit sum factorizes over coordinates
  have factor : ∀ F G H : Bool → ℝ,
      (∑ w : ThreeBit, F w.1 * G w.2.1 * H w.2.2)
        = (∑ β : Bool, F β) * (∑ β : Bool, G β) * (∑ β : Bool, H β) := by
    intro F G H
    simp [Fintype.sum_prod_type]
    ring
  conv_lhs => simp only [TriangleModel.law, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e : ∀ w : ThreeBit,
      φ w.1 * ψ w.2.1 * χ w.2.2 * (M.μX x * M.μY y * M.μZ z *
        respMass (M.f (x, z)) w.1 * respMass (M.g (x, y)) w.2.1 * respMass (M.h (z, y)) w.2.2)
        = (M.μX x * M.μY y * M.μZ z) *
          ((fun β => φ β * respMass (M.f (x, z)) β) w.1 *
           (fun β => ψ β * respMass (M.g (x, y)) β) w.2.1 *
           (fun β => χ β * respMass (M.h (z, y)) β) w.2.2) := by
    intro w; simp only; ring
  rw [Finset.sum_congr rfl fun w _ => e w, ← Finset.mul_sum]
  congr 1
  exact factor (fun β => φ β * respMass (M.f (x, z)) β)
    (fun β => ψ β * respMass (M.g (x, y)) β) (fun β => χ β * respMass (M.h (z, y)) β)

private theorem triangleModel_total_mass (M : TriangleModel)
    (hμX : IsLaw M.μX) (hμY : IsLaw M.μY) (hμZ : IsLaw M.μZ) :
    (∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z) = 1 := by
  have : ∀ x : M.X, (∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z) = M.μX x := by
    intro x
    have : ∀ y : M.Y, (∑ z : M.Z, M.μX x * M.μY y * M.μZ z) = M.μX x * M.μY y := by
      intro y
      rw [← Finset.mul_sum, hμZ.2, mul_one]
    rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.mul_sum, hμY.2, mul_one]
  rw [Finset.sum_congr rfl fun x _ => this x, hμX.2]

/-- AUDIT-NOTES A5, exact parity rigidity for the triangle. A compatible three-bit law
supported on the even-parity outcomes has `E[A] E[B] E[C] ≥ 0`. (Absorb the seeds, fix `y₀`,
put `S = B(·,y₀)`, `T = C(·,y₀)`; then `A = ST`, `B = SU`, `C = TU` for a sign `U` of the
third source, so the three means are `st`, `su`, `tu`.) -/
theorem parity_rigidity (P : ThreeBit → ℝ) (hP : IsLaw P)
    (hpar : ∀ w : ThreeBit, xor (xor w.1 w.2.1) w.2.2 = true → P w = 0)
    (hC : TriangleInflation.TriangleCompatible P) :
    0 ≤ triMeanA P * triMeanB P * triMeanC P := by
  obtain ⟨M, hvalid, hlaw⟩ := hC
  obtain ⟨hμX, hμY, hμZ, hfb, hgb, hhb⟩ := hvalid
  set a : M.X → M.Z → ℝ := fun x z => 2 * M.f (x, z) - 1 with hadef
  set b : M.X → M.Y → ℝ := fun x y => 2 * M.g (x, y) - 1 with hbdef
  set c : M.Z → M.Y → ℝ := fun z y => 2 * M.h (z, y) - 1 with hcdef
  have habnd : ∀ x z, -1 ≤ a x z ∧ a x z ≤ 1 := by
    intro x z; rw [hadef]; constructor <;> [linarith [(hfb (x, z)).1]; linarith [(hfb (x, z)).2]]
  have hbbnd : ∀ x y, -1 ≤ b x y ∧ b x y ≤ 1 := by
    intro x y; rw [hbdef]; constructor <;> [linarith [(hgb (x, y)).1]; linarith [(hgb (x, y)).2]]
  have hcbnd : ∀ z y, -1 ≤ c z y ∧ c z y ≤ 1 := by
    intro z y; rw [hcdef]; constructor <;> [linarith [(hhb (z, y)).1]; linarith [(hhb (z, y)).2]]
  have hrm1 : ∀ r : ℝ, (∑ β : Bool, respMass r β) = 1 := by
    intro r; simp [respMass]
  have hrms : ∀ r : ℝ, (∑ β : Bool, sgn β * respMass r β) = 2 * r - 1 := by
    intro r; simp [respMass, sgn]; ring
  have main : ∀ φ ψ χ : Bool → ℝ,
      (∑ w : ThreeBit, φ w.1 * ψ w.2.1 * χ w.2.2 * P w)
        = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z *
            ((∑ β : Bool, φ β * respMass (M.f (x, z)) β) *
             (∑ β : Bool, ψ β * respMass (M.g (x, y)) β) *
             (∑ β : Bool, χ β * respMass (M.h (z, y)) β)) := by
    intro φ ψ χ
    rw [← hlaw]
    exact triangleModel_mixed_moment M φ ψ χ
  -- the three means and the parity moment
  have hA : triMeanA P = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
      M.μX x * M.μY y * M.μZ z * a x z := by
    have h := main sgn (fun _ => 1) (fun _ => 1)
    simp only [one_mul, mul_one] at h
    rw [triMeanA, h]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rw [hrms, hrm1, hrm1, hadef]
    ring
  have hB : triMeanB P = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
      M.μX x * M.μY y * M.μZ z * b x y := by
    have h := main (fun _ => 1) sgn (fun _ => 1)
    simp only [one_mul, mul_one] at h
    rw [triMeanB, h]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rw [hrms, hrm1, hrm1, hbdef]
    ring
  have hCm : triMeanC P = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
      M.μX x * M.μY y * M.μZ z * c z y := by
    have h := main (fun _ => 1) (fun _ => 1) sgn
    simp only [one_mul, mul_one] at h
    rw [triMeanC, h]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rw [hrms, hrm1, hrm1, hcdef]
    ring
  have hABC : (∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
      M.μX x * M.μY y * M.μZ z * (a x z * b x y * c z y)) = 1 := by
    have h := main sgn sgn sgn
    have hone : (∑ w : ThreeBit, sgn w.1 * sgn w.2.1 * sgn w.2.2 * P w) = 1 := by
      have e : (∑ w : ThreeBit, sgn w.1 * sgn w.2.1 * sgn w.2.2 * P w) = ∑ w : ThreeBit, P w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        obtain ⟨b1, b2, b3⟩ := w
        have hp := hpar (b1, b2, b3)
        cases b1 <;> cases b2 <;> cases b3 <;> simp_all [sgn]
      rw [e, hP.2]
    have e : (∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
        M.μX x * M.μY y * M.μZ z * (a x z * b x y * c z y))
        = ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z *
            ((∑ β : Bool, sgn β * respMass (M.f (x, z)) β) *
             (∑ β : Bool, sgn β * respMass (M.g (x, y)) β) *
             (∑ β : Bool, sgn β * respMass (M.h (z, y)) β)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => ?_
      rw [hrms, hrms, hrms, hadef, hbdef, hcdef]
    rw [e, ← h]
    exact hone
  -- parity perfectness forces the responses to be deterministic on the support
  have htot : (∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z, M.μX x * M.μY y * M.μZ z) = 1 :=
    triangleModel_total_mass M hμX hμY hμZ
  have hzero : (∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
      M.μX x * M.μY y * M.μZ z * (1 - a x z * b x y * c z y)) = 0 := by
    have e : ∀ x y z, M.μX x * M.μY y * M.μZ z * (1 - a x z * b x y * c z y)
        = M.μX x * M.μY y * M.μZ z - M.μX x * M.μY y * M.μZ z * (a x z * b x y * c z y) := by
      intro x y z; ring
    simp_rw [e, Finset.sum_sub_distrib]
    rw [htot, hABC, sub_self]
  have hnn : ∀ x y z, 0 ≤ M.μX x * M.μY y * M.μZ z * (1 - a x z * b x y * c z y) := by
    intro x y z
    have h1 : 0 ≤ M.μX x * M.μY y * M.μZ z :=
      mul_nonneg (mul_nonneg (hμX.1 x) (hμY.1 y)) (hμZ.1 z)
    have hab := neg_one_le_mul_le_one (habnd x z).1 (habnd x z).2 (hbbnd x y).1 (hbbnd x y).2
    have h2 : a x z * b x y * c z y ≤ 1 :=
      (neg_one_le_mul_le_one hab.1 hab.2 (hcbnd z y).1 (hcbnd z y).2).2
    nlinarith
  have hdet : ∀ x y z, 0 < M.μX x → 0 < M.μY y → 0 < M.μZ z →
      a x z * b x y * c z y = 1 := by
    intro x y z hx hy hz
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x' _ => Finset.sum_nonneg fun y' _ => Finset.sum_nonneg fun z' _ => hnn x' y' z')).1
      hzero x (Finset.mem_univ x)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y' _ => Finset.sum_nonneg fun z' _ => hnn x y' z')).1 h1 y (Finset.mem_univ y)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun z' _ => hnn x y z')).1 h2 z
      (Finset.mem_univ z)
    have hpos : 0 < M.μX x * M.μY y * M.μZ z := mul_pos (mul_pos hx hy) hz
    have := mul_eq_zero.1 h3
    rcases this with h | h
    · exact absurd h (ne_of_gt hpos)
    · linarith
  obtain ⟨x0, hx0⟩ := exists_pos_of_isLaw M.μX hμX
  obtain ⟨y0, hy0⟩ := exists_pos_of_isLaw M.μY hμY
  obtain ⟨z0, hz0⟩ := exists_pos_of_isLaw M.μZ hμZ
  have hsqb : ∀ x y, 0 < M.μX x → 0 < M.μY y → b x y * b x y = 1 := by
    intro x y hx hy
    exact (sq_eq_one_of_prod_eq_one (habnd x z0).1 (habnd x z0).2 (hbbnd x y).1 (hbbnd x y).2
      (hcbnd z0 y).1 (hcbnd z0 y).2 (hdet x y z0 hx hy hz0)).2.1
  have hsqc : ∀ z y, 0 < M.μZ z → 0 < M.μY y → c z y * c z y = 1 := by
    intro z y hz hy
    exact (sq_eq_one_of_prod_eq_one (habnd x0 z).1 (habnd x0 z).2 (hbbnd x0 y).1 (hbbnd x0 y).2
      (hcbnd z y).1 (hcbnd z y).2 (hdet x0 y z hx0 hy hz)).2.2
  -- the rigidity factorizations
  have R1 : ∀ x z, 0 < M.μX x → 0 < M.μZ z → a x z = b x y0 * c z y0 := by
    intro x z hx hz
    have h := hdet x y0 z hx hy0 hz
    have hS := hsqb x y0 hx hy0
    have hT := hsqc z y0 hz hy0
    linear_combination (b x y0 * c z y0) * h - (a x z) * hS - (a x z * b x y0 * b x y0) * hT
  have R2 : ∀ x y, 0 < M.μX x → 0 < M.μY y →
      b x y = b x y0 * (c z0 y0 * c z0 y) := by
    intro x y hx hy
    have h := hdet x y z0 hx hy hz0
    rw [R1 x z0 hx hz0] at h
    have hS := hsqb x y0 hx hy0
    have hT := hsqc z0 y0 hz0 hy0
    have hG := hsqc z0 y hz0 hy
    linear_combination (b x y0 * c z0 y0 * c z0 y) * h - (b x y) * hS
      - (b x y * b x y0 * b x y0) * hT
      - (b x y * b x y0 * b x y0 * c z0 y0 * c z0 y0) * hG
  have R3 : ∀ z y, 0 < M.μZ z → 0 < M.μY y →
      c z y = c z y0 * (c z0 y0 * c z0 y) := by
    intro z y hz hy
    have h := hdet x0 y z hx0 hy hz
    rw [R1 x0 z hx0 hz, R2 x0 y hx0 hy] at h
    have hS := hsqb x0 y0 hx0 hy0
    have hT := hsqc z y0 hz hy0
    have hU : (c z0 y0 * c z0 y) * (c z0 y0 * c z0 y) = 1 := by
      have h1 := hsqc z0 y0 hz0 hy0
      have h2 := hsqc z0 y hz0 hy
      linear_combination (c z0 y * c z0 y) * h1 + h2
    linear_combination (c z y0 * (c z0 y0 * c z0 y)) * h - (c z y) * hS
      - (c z y * b x0 y0 * b x0 y0) * hT
      - (c z y * b x0 y0 * b x0 y0 * c z y0 * c z y0) * hU
  -- the three means factor
  have hAval : triMeanA P = (∑ x, M.μX x * b x y0) * (∑ z, M.μZ z * c z y0) := by
    rw [hA, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rcases eq_or_lt_of_le (hμX.1 x) with hx | hx
    · simp [← hx]
    rcases eq_or_lt_of_le (hμZ.1 z) with hz | hz
    · simp [← hz]
    have hr := R1 x z hx hz
    have e : ∀ y : M.Y, M.μX x * M.μY y * M.μZ z * a x z
        = M.μY y * (M.μX x * b x y0 * (M.μZ z * c z y0)) := by
      intro y; rw [hr]; ring
    rw [Finset.sum_congr rfl fun y _ => e y, ← Finset.sum_mul, hμY.2, one_mul]
  have hBval : triMeanB P =
      (∑ x, M.μX x * b x y0) * (∑ y, M.μY y * (c z0 y0 * c z0 y)) := by
    rw [hB, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rcases eq_or_lt_of_le (hμX.1 x) with hx | hx
    · simp [← hx]
    rcases eq_or_lt_of_le (hμY.1 y) with hy | hy
    · simp [← hy]
    have hr := R2 x y hx hy
    have e : ∀ z : M.Z, M.μX x * M.μY y * M.μZ z * b x y
        = M.μZ z * (M.μX x * b x y0 * (M.μY y * (c z0 y0 * c z0 y))) := by
      intro z; rw [hr]; ring
    rw [Finset.sum_congr rfl fun z _ => e z, ← Finset.sum_mul, hμZ.2, one_mul]
  have hCval : triMeanC P =
      (∑ y, M.μY y * (c z0 y0 * c z0 y)) * (∑ z, M.μZ z * c z y0) := by
    rw [hCm, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rcases eq_or_lt_of_le (hμZ.1 z) with hz | hz
    · simp [← hz]
    rcases eq_or_lt_of_le (hμY.1 y) with hy | hy
    · simp [← hy]
    have hr := R3 z y hz hy
    have e : ∀ x : M.X, M.μX x * M.μY y * M.μZ z * c z y
        = M.μX x * (M.μY y * (c z0 y0 * c z0 y) * (M.μZ z * c z y0)) := by
      intro x; rw [hr]; ring
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_mul, hμX.2, one_mul]
  rw [hAval, hBval, hCval]
  have key : ((∑ x, M.μX x * b x y0) * (∑ z, M.μZ z * c z y0)) *
      ((∑ x, M.μX x * b x y0) * (∑ y, M.μY y * (c z0 y0 * c z0 y))) *
      ((∑ y, M.μY y * (c z0 y0 * c z0 y)) * (∑ z, M.μZ z * c z y0))
      = ((∑ x, M.μX x * b x y0) * (∑ z, M.μZ z * c z y0) *
          (∑ y, M.μY y * (c z0 y0 * c z0 y))) ^ 2 := by ring
  rw [key]
  positivity

end TriangleInflation.Graph
