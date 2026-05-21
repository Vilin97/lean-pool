/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Foundations.Basic
import LeanPool.HopfieldNet.SampCert.Samplers.Uniform.Basic
import LeanPool.HopfieldNet.SampCert.Samplers.Bernoulli.Basic
import LeanPool.HopfieldNet.SampCert.Samplers.BernoulliNegativeExponential.Code
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# ``BernoulliNegExpSample`` Properties

This file proves evaluation and normalization for ``BernoulliNegExpSample``.
-/

noncomputable section

open PMF Nat BigOperators Finset

namespace SLang

@[simp]
theorem BernoulliExpNegSampleUnitAux_zero (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) 0 st st' = 0 := by
  simp [probWhileCut]

@[simp]
theorem BernoulliExpNegSampleUnitAux_returns_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (true, r) = 0 := by
  revert st r
  induction fuel
  · simp [probWhileCut]
  · rename_i fuel IH
    intro st r
    simp [probWhileCut, probWhileFunctional]
    unfold probBind
    unfold probPure
    simp [ite_apply]
    split
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      conv =>
        left
        right
        intro a
        rw [IH a r]
      simp
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_ite_simpl (x r : ℕ+) (k : ENNReal) :
  @ite ENNReal (x = r + 1) (Classical.propDecidable (x = r + 1)) 0
  (@ite ENNReal (x = r + 1) (instPNatDecidableEq x (r + 1)) k 0) = 0 := by
  split
  · simp
  · simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (true, r + 1) st
    + (1 - (num / (r * den))) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st := by
  cases st
  rename_i b' r'
  simp [probWhileCut, probWhileFunctional, ite_apply, ENNReal.tsum_prod', tsum_bool, BernoulliExpNegSampleUnitLoop]
  conv =>
    left
    congr
    · rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]
    · rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]
  simp
  rw [add_comm]


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (false, r) st =
  if st = (false,r) then 1 else 0 := by
  cases st
  simp [probWhileCut, probWhileFunctional]

@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_counter (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  · simp
  · rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    · simp
      exact Ne.symm (h1 rfl)
    · simp [BernoulliExpNegSampleUnitAux_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact eq_or_lt_of_le h2
        cases OR
        · rename_i h
          subst h
          exact _root_.ne_of_gt le.refl
        · rename_i h
          exact _root_.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by exact
        (bne_iff_ne (true, stn + 1) (false, n)).mp rfl
      rw [IH _ A]
      rw [IH _ B]
      simp
      exact le.step h2
      exact le.step h2

-- The following two functions are useful to keep the dependent definition of PNat under control
-- Otherwise, the terms become large and unreadable

def plus_one (k : ℕ) : ℕ+ := ⟨ k + (1 : ℕ+) , Nat.add_pos_right k le.refl ⟩

def plus_two (k fuel : ℕ) : ℕ+ := ⟨ fuel + k + 2 , Nat.add_pos_right (fuel + k) (le.step le.refl) ⟩

@[simp]
theorem plus_one_p1 (k e : ℕ) :
  plus_one k + e = plus_one (k + e) := by
  simp [plus_one]
  conv =>
    right
    rw [add_assoc]
    right
    rw [add_comm]
  conv =>
    right
    rw [← add_assoc]

theorem plus_one_prop (k : ℕ) :
  plus_one k = k + 1 := by
  simp [plus_one]

theorem plus_two_zero_prop (k : ℕ) :
  plus_two k 0 = k + 2 := by
  simp [plus_two]

theorem nm2p2 (n : ℕ) (h : n > 1) :
  n - 2 + 2 = n := by
  exact Nat.sub_add_cancel h

-- Warning! BernoulliExpNegSampleUnitAux has a transition phase
-- This min is suspicious: (min (fuel + 2) (fuel + k + 1) - 2)
@[simp]
theorem BernoulliExpNegSampleUnitAux_progress (num : ℕ) (den : ℕ+) (fuel k : ℕ) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel ) = (∏ i in range fuel, (num : ENNReal) / ((k + 1 + i) * den)) * (1 - ((num : ENNReal) / ((fuel + k + 1) * den))) := by
  revert k
  induction fuel
  · intro k
    simp
    split
    · rename_i h
      rw [plus_one_prop]
      simp
    · rename_i h
      have A : ¬ k + 2 = k + 2 := by
        conv =>
          right
          congr
          · rw [← plus_two_zero_prop]
          · change k + (1 + 1)
            rw [← add_assoc]
            rw [← plus_one_prop]
        refine (Function.Injective.ne_iff ?hf).mpr h
        exact PNat.coe_injective
      contradiction
  · rename_i fuel IH
    intro k
    rw [BernoulliExpNegSampleUnitAux_succ_true]
    rw [BernoulliExpNegSampleUnitAux_succ_false]
    have IH' := IH (k + 1)
    clear IH
    have A : plus_one (k + 1) = plus_one k + 1 := rfl
    have B : plus_two (k + 1) fuel = plus_two k (succ fuel) := by
      simp [plus_two]
      have X : fuel + (k + 1) + 2 = succ fuel + k + 2 := by
        conv =>
          left
          left
          right
          rw [add_comm]
        rw [← add_assoc]
      conv =>
        left
        left
        rw [X]
    rw [← A]
    rw [← B]
    rw [IH']
    have C : ¬ plus_two (k + 1) fuel = plus_one (k + 1) := by
      by_contra
      rename_i h
      simp [plus_one, plus_two] at h
      cases h
    simp [C]
    have E : fuel + (k + (1 : ENNReal)) + (1 : ENNReal) = ↑fuel + 1 + ↑k + 1 := by -- duplicate later on
      conv =>
        left
        left
        right
        rw [add_comm]
      rw [← add_assoc]
    rw [E]
    clear IH' A B C E
    simp [prod_range_succ']
    rw [plus_one_prop]
    conv =>
      right
      left
      rw [mul_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      right
      rw [add_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      rw [← add_assoc]
    simp
    rw [mul_assoc]

theorem adhoc (n : ℕ) (h : n > 1) :
  n - 2 + 1 = n - 1 := by
  rw [← tsub_tsub_assoc]
  · exact h
  · exact le.step le.refl

theorem adhoc' (n : ℕ) (h : n > 1) :
  (n : ENNReal) - 2 + 1 = (n : ENNReal) - 1 := by
  have C := @congrArg ℕ ENNReal (n - 2 + 1) (n - 1) Nat.cast  (adhoc n h)
  simp at C
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_progress' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1 ) (false, ⟨ n , lt_of_succ_lt h ⟩ ) = (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  have prog := BernoulliExpNegSampleUnitAux_progress num den (n - 2) 0 wf
  have A := nm2p2 n h
  rw [A] at prog
  have B : plus_two 0 (n - 2) = ⟨ n , lt_of_succ_lt h ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [A]
  rw [B] at prog
  simp [plus_one] at prog
  have C := adhoc' n h
  rw [C] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation (num : ℕ) (den : ℕ+) (fuel fuel' k : ℕ) (wf : num ≤ den) (h1 : fuel ≥ fuel') :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (1 + fuel + 2) (true, plus_one k ) (false, plus_two k fuel')
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel') := by
  revert fuel' k
  induction fuel
  · intro fuel' k h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [BernoulliExpNegSampleUnitAux_succ_true]
    -- rewrites of plus_* properties do not work because the type is wrong
    have B : ¬ plus_two k 0 = plus_one k + 1 + 1 := by
      simp [plus_two, plus_one]
      by_contra
      rename_i h
      cases h -- similar proof in BernoulliExpNegSampleUnitAux_progress
    simp [B]
  · rename_i fuel IH
    intro fuel' k h1
    conv =>
      congr
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (k + 1) Pre
    clear IH
    cases fuel'
    · rw [BernoulliExpNegSampleUnitAux_succ_false]
      rw [BernoulliExpNegSampleUnitAux_succ_false]
      have C : plus_two k Nat.zero = plus_one k + 1 := by   -- Useful for cleanup
        simp [plus_two, plus_one]
        rfl
      rw [C]
      simp
    · rename_i fuel'
      have C : succ fuel' - 1 = fuel' := by exact rfl
      rw [C] at IH'
      have D : plus_two (k + 1) fuel' = plus_two k (succ fuel') := by -- Important example for cleanup
        simp [plus_two]
        have X : fuel' + (k + 1) + 2 = succ fuel' + k + 2 := by
          conv =>
            left
            left
            right
            rw [add_comm]
          rw [← add_assoc]
        conv =>
          left
          left
          rw [X]
      rw [D] at IH'
      have E : plus_one (k + 1) = plus_one k + 1 := by  -- Useful for cleanup
        simp [plus_one]
        rfl
      rw [E] at IH'
      rw [IH']
      exact rfl

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation' (num : ℕ) (den : ℕ+) (n m : ℕ) (wf : num ≤ den) (h1 : m > 1) (h2 : n ≥ m) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (n + 1) (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩ )
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩) := by
  have X : n - 2 ≥ m - 2 := by exact Nat.sub_le_sub_right h2 2
  have prog := BernoulliExpNegSampleUnitAux_preservation num den (n - 2) (m - 2) 0 wf X
  have A : 1 + (n - 2) + 2 = n + 1 := by
    rw [add_assoc]
    rw [add_comm]
    rw [_root_.add_left_inj]
    rw [nm2p2 n (Nat.lt_of_lt_of_le h1 h2)]
  have B := nm2p2 n (Nat.lt_of_lt_of_le h1 h2)
  have C : plus_one 0 = 1 := by
    simp [plus_one]
  have D : plus_two 0 (m - 2) = ⟨ m, zero_lt_of_lt h1 ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [nm2p2 m h1]
  rw [A, B, C, D] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_characterization (num : ℕ) (den : ℕ+) (n extra : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (extra + n) (true, 1) (false, ⟨ n, by exact zero_lt_of_lt h ⟩)
    =  (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  revert n
  induction extra
  · simp
    intro n h
    apply BernoulliExpNegSampleUnitAux_progress' num den n wf h
  · rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    rw [← BernoulliExpNegSampleUnitAux_preservation'] at IH'
    · have B : extra + n + 1 = succ extra + n := by
        clear IH'
        clear IH'
        conv =>
          left
          rw [add_comm]
          rw [← add_assoc]
        rw [add_left_inj]
        exact one_add extra
      rw [← B]
      trivial
    · trivial
    · exact Nat.le_add_left n extra

theorem BernoulliExpNegSampleUnitAux_sup (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  ⨆ i, probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) i (true, 1) (false, n)
    = if n = 1 then 0 else (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  apply iSup_eq_of_tendsto
  · apply probWhileCut_monotonic
  · rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat n)]
    split
    · rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [BernoulliExpNegSampleUnitAux_monotone_counter]
    · rename_i h
      have h' : n > 1 := by
        by_contra
        rename_i h'
        simp at *
        subst h'
        contradiction
      have FOO (n_1 : ℕ) := @BernoulliExpNegSampleUnitAux_characterization num den n n_1 wf h'
      have BAR : n = (@Subtype.mk.{1} Nat (fun (n : Nat) => @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)
          (PNat.val n) (@Nat.zero_lt_of_lt (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (PNat.val n) h')) := rfl
      conv =>
        congr
        intro n_1
        right
        rw [BAR]
      conv =>
        congr
        intro E
        rw [FOO E]
      rw [tendsto_const_nhds_iff]

@[simp]
theorem BernoulliExpNegSampleUnitAux_at_zero (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 0 = 0 := by
  simp only [BernoulliExpNegSampleUnitAux, Bind.bind, Pure.pure, SLang.bind_apply, probWhile,
    SLang.pure_apply, ENNReal.tsum_eq_zero, _root_.mul_eq_zero, ENNReal.iSup_eq_zero, Prod.forall,
    Bool.forall_bool, ne_eq, Prod.mk.injEq, false_and, not_false_eq_true,
    BernoulliExpNegSampleUnitAux_returns_false, forall_const, true_or, and_true]
  intro b
  right
  split
  · rename_i h
    cases b
    rename_i b pb
    subst h
    contradiction
  simp only

theorem if_simpl' (num : ℕ) (den : ℕ+) (x n : ℕ+) :
  @ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
  (@ite ENNReal (n = x) (instPNatDecidableEq n x)
  (@ite ENNReal (x = 1) (instPNatDecidableEq x 1) 0
  ((∏ i in range (↑x - 2), ↑num / (((1 : ENNReal) + ↑i) * ↑↑den)) * (1 - ↑num / ((↑↑x - 1) * ↑↑den)))) 0) = 0 := by
  split
  · simp
  · split
    · split
      · simp
      · rename_i h1 h2 h3
        subst h2
        contradiction
    · simp

theorem BernoulliExpNegSampleUnitAux_apply (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
    if n = 1 then 0 else (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  simp [BernoulliExpNegSampleUnitAux]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [probWhile]
  simp [BernoulliExpNegSampleUnitAux_sup]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  conv =>
    left
    right
    right
    intro x
    rw [if_simpl']
  simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_at_one (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 1 = 0 := by
  change (BernoulliExpNegSampleUnitAux num den wf) (1 : ℕ+) = 0
  rw [BernoulliExpNegSampleUnitAux_apply]
  simp

theorem gamma_extract' (num : Nat) (den : PNat) (x : ENNReal) (h1 : x ≠ 0) (h2 : x ≠ ⊤) :
  ((num : ENNReal) / (x * den)) = ((num : ENNReal) / (den : ENNReal)) * x⁻¹ := by
  simp [division_def]
  rw [mul_assoc]
  congr
  rw [mul_comm]
  refine (ENNReal.eq_inv_of_mul_eq_one_left ?_).symm
  rw [← mul_assoc]
  conv =>
    left
    left
    rw [mul_comm]
    rw [← mul_assoc]
  simp [ENNReal.mul_inv_cancel, h1, h2]
  rw [mul_comm]
  simp [ENNReal.mul_inv_cancel, h1, h2]

theorem gamma_extract (num : Nat) (den : PNat) (n : ℕ) (h : n > 1) :
  (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) =
  (((num : ENNReal) / (den : ENNReal))^(n - 2) * ((factorial (n - 2)) : ENNReal)⁻¹) := by
  have X : ∀ i : ℕ, (1 : ENNReal) + i ≠ 0 := by
    intro i
    simp
  have Y : ∀ i : ℕ, (1 : ENNReal) + i ≠ ⊤ := by
    intro i
    simp
  conv =>
    left
    right
    intro i
    rw [gamma_extract' _ _ _ (X i) (Y i)]
  rw [prod_mul_distrib]
  rw [← pow_eq_prod_const]
  congr
  rw [← prod_range_add_one_eq_factorial]
  rw [cast_prod]
  conv =>
    right
    right
    right
    intro i
    rw [cast_add]
    rw [add_comm]
    simp
  clear X Y
  cases n
  · contradiction
  · rename_i n
    cases n
    · contradiction
    · rename_i n
      clear h
      induction n
      · simp
      · rename_i n IH
        have A : succ (succ (succ n)) - 2 = succ n := rfl
        rw [A]
        rw [prod_range_succ]
        rw [prod_range_succ]
        have B : succ (succ n) - 2 = n := rfl
        rw [B] at IH
        rw [IH]
        rw [ENNReal.mul_inv]
        · simp
        · simp

noncomputable def mass (n : ℕ) (γ : ENNReal) := (γ^(n - 2) * (((n - 2)!) : ENNReal)⁻¹) * (1 - (γ * ((n : ENNReal) - 1)⁻¹))

theorem BernoulliExpNegSampleUnitAux_apply' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnitAux num den wf) n = mass n γ := by
  unfold mass
  cases n
  · contradiction
  · rename_i n
    let m : ℕ+ := ⟨ succ n , by exact Fin.pos { val := n, isLt := le.refl } ⟩
    have A : n + 1 = m := rfl
    rw [A]
    rw [BernoulliExpNegSampleUnitAux_apply num den m wf]
    split
    · rename_i h'
      rw [h'] at A
      rw [A] at h
      contradiction
    · rename_i h'
      cases n
      · contradiction
      · rename_i n
        rw [gamma_extract]
        · rw [← A]
          simp only [succ_sub_succ_eq_sub, add_tsub_cancel_right, cast_succ, cast_add, cast_one,
            ne_eq, ENNReal.one_ne_top, not_false_eq_true, ENNReal.add_sub_cancel_right]
          have B : (n : ENNReal) + 1 ≠ 0 := by exact cast_add_one_ne_zero n
          have C : (n : ENNReal) + 1 ≠ ⊤ := by simp
          rw [gamma_extract' num den (↑n + 1) B C]
          simp only [gam]
        · rw [← A]
          simp only [gt_iff_lt, one_lt_succ_succ]

noncomputable def mass' (n : ℕ) (γ : ENNReal) := (γ^n * (((n)!) : ENNReal)⁻¹)

theorem mass'_neq_top (n : ℕ) (γ : ENNReal) (h : γ ≠ ⊤) :
  mass' n γ ≠ ⊤ := by
  unfold mass'
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · induction n
    · simp
    · rename_i n IH
      rw [_root_.pow_succ]
      rw [ENNReal.mul_lt_top_iff]
      left
      constructor
      · trivial
      · exact Ne.lt_top h
  · have A : n ! > 0 := by exact factorial_pos n
    rw [@ENNReal.inv_lt_iff_inv_lt]
    simp
    exact A

theorem mass'_series_exp (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ).toReal = Real.exp (γ.toReal) := by
  unfold mass'
  rw [ENNReal.tsum_toReal_eq]
  · conv =>
      left
      right
      intro a
      rw [ENNReal.toReal_mul]
      rw [ENNReal.toReal_pow]
      rw [ENNReal.toReal_inv]
      simp
      rw [← division_def]
    conv =>
      left
      change ((λ x : ℝ => ∑' (a : ℕ), x ^ a / ↑a !) (ENNReal.toReal γ))
    rw [← @NormedSpace.exp_eq_tsum_div ℝ ℝ]
    rw [← Real.exp_eq_exp_ℝ]
  · intro a
    apply mass'_neq_top _ _ h

theorem mass'_series_converges (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ) ≠ ⊤ := by
  by_contra h'
  have A := mass'_series_exp γ h
  rw [h'] at A
  simp at A
  have B := Real.exp_pos (ENNReal.toReal γ)
  rw [← A] at B
  simp at B

theorem mass'_series_converges' (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at A
  have B := tsum_shift'_1 (λ x => mass' x γ)
  have C : ∀ n, @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0 (mass' n γ) = @ite ENNReal (n = 0) (Classical.propDecidable (n = 0)) 0 (mass' n γ) := by
    intro n
    split
    · simp
    · simp
  revert B
  conv =>
    left
    left
    right
    intro n
    rw [C n]
  intro B
  rw [B] at A
  clear C B
  by_contra h
  rw [h] at A
  simp at A

theorem mass'_series_converges'_even (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd] at A
  · by_contra h'
    rw [h'] at A
    simp at A
  · exact ENNReal.summable
  · exact ENNReal.summable

theorem mass'_series_converges'_odd (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd] at A
  · by_contra h'
    rw [h'] at A
    simp at A
  · exact ENNReal.summable
  · exact ENNReal.summable

theorem mass'_series_exp' (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ) = ENNReal.ofReal (Real.exp (γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (i : ℕ), mass' i γ)]
  · unfold mass'
    rw [ENNReal.tsum_toReal_eq]
    · conv =>
        left
        right
        right
        intro a
        rw [ENNReal.toReal_mul]
        rw [ENNReal.toReal_pow]
        rw [ENNReal.toReal_inv]
        simp
        rw [← division_def]
      conv =>
        left
        right
        change ((λ x : ℝ => ∑' (a : ℕ), x ^ a / ↑a !) (ENNReal.toReal γ))
      rw [← @NormedSpace.exp_eq_tsum_div ℝ ℝ]
      rw [← Real.exp_eq_exp_ℝ]
    · intro a
      apply mass'_neq_top _ _ h
  · apply mass'_series_converges _ h

theorem mass_simpl (n : ℕ) (γ : ENNReal) (h : n ≥ 2) :
  mass n γ = mass' (n - 2) γ - mass' (n - 1) γ := by
  unfold mass
  unfold mass'
  rw [ENNReal.mul_sub]
  · simp only [mul_one]
    rw [mul_mul_mul_comm]
    conv =>
      left
      right
      left
      rw [mul_comm]
      rw [← _root_.pow_succ']
    rw [adhoc n h]
    congr
    rw [← ENNReal.mul_inv]
    · rw [inv_eq_iff_eq_inv]
      rw [inv_inv]
      rw [mul_comm]
      have A := @Nat.mul_factorial_pred (n - 1) (Nat.sub_pos_of_lt h)
      have B : n - 1 - 1 = n - 2 := rfl
      rw [B] at A
      clear B
      rw [← A]
      simp only [cast_mul, ENNReal.natCast_sub, cast_one]
    · simp only [ne_eq, cast_eq_zero, ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top,
      ENNReal.one_ne_top, not_false_eq_true, and_true, or_true]
    · simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true, true_or]
  · intro h1 h2
    rw [ne_iff_lt_or_gt] -- Proof to simplify with mass'_neq_top
    left
    rw [ENNReal.mul_lt_top_iff]
    left
    constructor
    · have X : γ ≠ ⊤ := by
        by_contra
        rename_i h
        subst h
        simp only [ge_iff_le, ne_eq, ENNReal.inv_eq_zero, ENNReal.sub_eq_top_iff,
          ENNReal.natCast_ne_top, ENNReal.one_ne_top, not_false_eq_true, and_true, ENNReal.top_mul,
          ENNReal.zero_lt_top, not_top_lt] at *
      clear h1 h2
      induction n
      · simp only [zero_eq, ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, _root_.pow_zero,
        ENNReal.one_lt_top]
      · rename_i n IH
        have OR : n = 1 ∨ n ≥ 2 := by
          clear IH γ X
          cases n
          · simp at h
          · rename_i n
            cases n
            · simp
            · rename_i n
              right
              exact AtLeastTwo.prop
        cases OR
        · rename_i h'
          subst h'
          simp only [reduceSucc, ge_iff_le, le_refl, tsub_eq_zero_of_le, _root_.pow_zero,
            ENNReal.one_lt_top]
        · rename_i h'
          have IH' := IH h'
          clear IH
          have A : succ n - 2 = succ (n - 2) := by
            cases n
            · contradiction
            · rename_i n
              cases n
              · contradiction
              · rename_i n
                rfl
          rw [A]
          rw [_root_.pow_succ]
          rw [ENNReal.mul_lt_top_iff]
          left
          constructor
          · exact IH'
          · exact Ne.lt_top X
    · have A : (n - 2)! > 0 := by exact factorial_pos (n - 2)
      rw [@ENNReal.inv_lt_iff_inv_lt]
      simp only [ENNReal.inv_top, cast_pos]
      exact A

theorem if_ge_2 (x : ℕ) (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (@ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
  (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (BernoulliExpNegSampleUnitAux num den wf x)))
    = if x = 0 then 0 else if x = 1 then 0 else mass x γ := by
  split
  · simp
  · split
    · simp
    · rename_i h1 h2
      rw [BernoulliExpNegSampleUnitAux_apply']
      · exact one_lt_iff_ne_zero_and_ne_one.mpr { left := h1, right := h2 }
      · exact gam

theorem if_split_minus (x : ℕ) (γ : ENNReal) :
  (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (@ite ENNReal (x = 1) (instDecidableEqNat x 1) 0 (mass' (x - 2) γ - mass' (x - 1) γ)))
    = (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (@ite ENNReal (x = 1) (instDecidableEqNat x 1) 0 (mass' (x - 2) γ))) - (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (@ite ENNReal (x = 1) (instDecidableEqNat x 1) 0 (mass' (x - 1) γ))) := by
  split
  · simp
  · split
    · simp
    · simp

theorem mass'_antitone (n : ℕ) (γ : ENNReal) (h : γ ≤ 1) :
  mass' n γ ≥ mass' (n + 1) γ  := by
  unfold mass'
  rw [pow_add]
  simp [factorial]
  rw [ENNReal.mul_inv]
  · have A : γ ^ n * γ * (((n : ENNReal) + 1)⁻¹ * (↑n !)⁻¹) = (γ ^ n * (↑n !)⁻¹) * (γ * ((n : ENNReal) + 1)⁻¹) := by
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      conv =>
        right
        rw [mul_comm]
      rw [mul_assoc]
    rw [A]
    clear A
    have B := @mul_le_of_le_one_right ENNReal (γ ^ n * (↑n !)⁻¹) (γ * ((n : ENNReal) + 1)⁻¹) _ _ _ _
    apply B
    clear B
    · simp
    · have C : ((n: ENNReal) + 1)⁻¹ ≤ 1 := by
        simp only [ENNReal.inv_le_one, self_le_add_left]
      exact mul_le_one' h C
  · simp
  · simp

theorem mass'_series_converges'_sub (γ : ENNReal) (h1 : γ ≠ ⊤) (h2 : γ ≤ 1) :
  ∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ) ≠ ⊤ := by
  rw [ENNReal.tsum_sub]
  · have A := mass'_series_converges'_even _ h1
    apply ENNReal.sub_ne_top A
  · apply mass'_series_converges'_odd _ h1
  · rw [Pi.le_def]
    intro i
    rw [← ge_iff_le]
    apply mass'_antitone _ _ h2

theorem γ_ne_top (num : ℕ) (den : ℕ+) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≠ ⊤ := by
  subst gam
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · rw [ENNReal.inv_lt_top]
    apply NeZero.pos
  · apply (cmp_eq_gt_iff _ _).mp
    rfl

theorem γ_le_1 (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≤ 1 := by
  subst gam
  have A : (num : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top num
  have B : (den : ENNReal) ≠ 0 := NeZero.natCast_ne (↑den) ENNReal
  have C : ((den : ENNReal)⁻¹ ) ≠ ⊤ := ENNReal.inv_ne_top.mpr B
  have D : 0 ≤ ENNReal.toReal (den : ENNReal)⁻¹ := ENNReal.toReal_nonneg
  rw [ENNReal.div_eq_inv_mul]
  rw [← @ENNReal.ofReal_toReal (num : ENNReal) A]
  rw [← @ENNReal.ofReal_toReal ((den : ENNReal)⁻¹) C]
  rw [← ENNReal.ofReal_mul D]
  rw [ENNReal.toReal_nat]
  rw [ENNReal.ofReal_le_one]
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_nat]
  rw [inv_mul_eq_div]
  rw [div_le_one]
  · rw [cast_le]
    exact wf
  · simp only [cast_pos, PNat.pos]

theorem BernoulliExpNegSampleUnitAux_normalizes (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  ∑' n : ℕ, (BernoulliExpNegSampleUnitAux num den wf) n = 1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite 1]
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  simp
  conv =>
    left
    right
    intro x
    rw [if_ge_2 x]
  rw [← gam]
  rw [tsum_shift'_2]
  conv =>
    left
    right
    intro n
    rw [mass_simpl _ _ (by simp)]
  simp
  rw [ENNReal.tsum_sub]
  · rw [ENNReal.tsum_eq_add_tsum_ite 0]
    have X := tsum_shift'_1 (fun n => mass' n γ)
    have A : ∀ n : ℕ, @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0 (mass' n γ) = @ite ENNReal (n = 0) (Classical.propDecidable (n = 0)) 0 (mass' n γ) := by
      intro n
      split
      · simp
      · simp
    conv =>
      left
      left
      right
      right
      intro n
      rw [← A]
    rw [X]
    rw [ENNReal.add_sub_cancel_right]
    · simp [mass']
    · apply mass'_series_converges' _ (γ_ne_top num den gam)
  · apply mass'_series_converges' _ (γ_ne_top num den gam)
  · rw [@Pi.le_def]
    intro i
    rw [← ge_iff_le]
    apply mass'_antitone
    · -- γ ≤ 1
      rw [gam]
      apply γ_le_1 num den wf rfl

theorem series_step_1 (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' (a : ℕ), if a % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf a else 0)
    = (∑' (n : ℕ), mass (2 * (n + 1)) γ) := by
  rw [← tsum_even_add_odd]
  · conv =>
      left
      left
      right
      intro k
      simp
    have A : forall k, (((2 * k + 1) % 2 = 0) ↔ False) := by
      intro k
      simp
      exact odd_iff.mp (Exists.intro k rfl)
    conv =>
      left
      right
      right
      intro k
      simp [A k]
    clear A
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    simp only [mul_zero, BernoulliExpNegSampleUnitAux_at_zero, zero_add]
    have X := tsum_shift'_1 (fun n => BernoulliExpNegSampleUnitAux num den wf (2 * n))
    have B : ∀ n, @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0 (BernoulliExpNegSampleUnitAux num den wf (2 * n)) = @ite ENNReal (n = 0) (Classical.propDecidable (n = 0)) 0 (BernoulliExpNegSampleUnitAux num den wf (2 * n)) := by
      intro n
      split
      · simp
      · simp
    conv =>
      left
      right
      intro x
      rw [← B]
    clear B
    rw [X]
    clear X
    have C : ∀ n, 2 * (n + 1) > 1 := by exact fun n => one_lt_succ_succ (Nat.mul 2 (Nat.add n 0))
    conv =>
      left
      right
      intro k
      rw [BernoulliExpNegSampleUnitAux_apply' _ _ _ wf (C k) γ gam]
  · exact ENNReal.summable
  · exact ENNReal.summable

theorem series_step_3 (γ : ENNReal) :
  (∑' n : ℕ, mass (2 * (n + 1)) γ)
    = ∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ) := by
  have A : ∀ n : ℕ, 2 * (n + 1) ≥ 2 := by
    intro n
    simp
  conv =>
    left
    right
    intro n
    rw [mass_simpl (2 * (n + 1)) γ (A n)]
  rfl

noncomputable def mass'' (n : ℕ) (γ : ℝ) := (γ^n * (((n)!) : ℝ)⁻¹)

theorem series_step_4_pre (γ : ENNReal) (h : γ ≠ ⊤) (h' : γ ≤ 1) :
  (∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ))
    = ENNReal.ofReal (∑' n : ℕ, mass'' n (- γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ))]
  · rw [ENNReal.tsum_sub]
    · congr
      rw [ENNReal.toReal_sub_of_le]
      · rw [ENNReal.tsum_toReal_eq]
        · rw [ENNReal.tsum_toReal_eq]
          · unfold mass'
            conv =>
              left
              left
              right
              intro a
              rw [ENNReal.toReal_mul]
              rw [ENNReal.toReal_pow]
              rw [ENNReal.toReal_inv]
            conv =>
              left
              right
              right
              intro a
              rw [ENNReal.toReal_mul]
              rw [ENNReal.toReal_pow]
              rw [ENNReal.toReal_inv]
            simp
            have A : Summable fun k => mass'' (2 * k) (-ENNReal.toReal γ) := by
              have X := @NormedSpace.expSeries_div_summable ℝ ℝ _ _ _ _ (-ENNReal.toReal γ)
              have Y := @Summable.comp_injective ℝ ℕ ℕ _ _ _ (fun n => (-ENNReal.toReal γ) ^ n / ↑n !) _ (fun n => 2 * n) X (by simp [Function.Injective] )
              simp [mass'', Function.comp] at *
              trivial
            have B : Summable fun k => mass'' (2 * k + 1) (-ENNReal.toReal γ) := by
              have X := @NormedSpace.expSeries_div_summable ℝ ℝ _ _ _ _ (-ENNReal.toReal γ)
              have Y := @Summable.comp_injective ℝ ℕ ℕ _ _ _ (fun n => (-ENNReal.toReal γ) ^ n / ↑n !) _ (fun n => 2 * n + 1) X (by simp [Function.Injective] )
              simp [mass'', Function.comp] at *
              trivial
            have X := @tsum_even_add_odd ℝ _ _ _ _ (fun k => mass'' k (-ENNReal.toReal γ)) A B
            conv =>
              right
              rw [← X]
            simp
            clear A B X
            unfold mass''
            simp
            have A : ∀ k : ℕ, (-ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹ = - ((ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹) := by
              intro k
              rw [neg_mul_eq_neg_mul]
              congr
              rw [Odd.neg_pow (Exists.intro k rfl) (ENNReal.toReal γ)]
            conv =>
              right
              right
              right
              intro k
              rw [A]
            rw [tsum_neg]
            rfl
          · intro a
            apply mass'_neq_top _ _ h
        · intro a
          apply mass'_neq_top _ _ h
      · apply ENNReal.tsum_le_tsum
        intro a
        rw [← ge_iff_le]
        apply mass'_antitone
        exact h'
      · apply mass'_series_converges'_even _ h
    · apply mass'_series_converges'_odd _ h
    · rw [Pi.le_def]
      intro i
      rw [← ge_iff_le]
      apply mass'_antitone
      exact h'
  · apply mass'_series_converges'_sub _ h
    exact h'

theorem series_step_4 (γ : ENNReal) (h : γ ≠ ⊤) (h' : γ ≤ 1) :
  (∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ))
    = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  rw [series_step_4_pre _ h h']
  congr
  unfold mass''
  rw [Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]
  simp
  congr

@[simp]
theorem BernoulliExpNegSampleUnit_apply_true (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) true = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [series_step_1 num den wf γ gam]
  rw [series_step_3 γ]
  rw [series_step_4 γ]
  · apply γ_ne_top num den gam
  · apply γ_le_1 num den wf gam

theorem BernoulliExpNegSampleAux_split (num : Nat) (den : PNat)  (wf : num ≤ den) :
  (∑' (a : ℕ), BernoulliExpNegSampleUnitAux num den wf a)
    = (BernoulliExpNegSampleUnit num den wf) false
      +
      (BernoulliExpNegSampleUnit num den wf) true := by
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro b
  split
  · simp
  · simp

theorem BernoulliExpNegSampleUnit_normalizes (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' b : Bool, (BernoulliExpNegSampleUnit num den wf) b) = 1 := by
  simp [tsum_bool]
  rw [← BernoulliExpNegSampleAux_split num den wf]
  rw [BernoulliExpNegSampleUnitAux_normalizes num den wf gam]

@[simp]
theorem BernoulliExpNegSampleUnit_apply_false (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) false = 1 - ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  have A := BernoulliExpNegSampleUnit_normalizes num den wf γ gam
  simp [tsum_bool] at A
  rw [BernoulliExpNegSampleUnit_apply_true num den wf γ gam] at A
  rw [← ENNReal.eq_sub_of_add_eq]
  · exact ENNReal.ofReal_ne_top
  · trivial

theorem BernoulliExpNegSampleGenLoop_normalizes (iter : Nat) :
  (∑' b : Bool, (BernoulliExpNegSampleGenLoop iter) b) = 1 := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop, tsum_bool]
  · rename_i iter IH
    rw [BernoulliExpNegSampleGenLoop]
    simp [tsum_bool, ite_apply]
    rw [BernoulliExpNegSampleUnit_apply_true 1 1 le.refl ((1 : ENNReal) / (1 : ENNReal)) (by simp only [div_one, cast_one, PNat.one_coe] )]
    rw [BernoulliExpNegSampleUnit_apply_false 1 1 le.refl ((1 : ENNReal) / (1 : ENNReal)) (by simp only [div_one, cast_one, PNat.one_coe] )]
    simp
    simp [tsum_bool] at IH
    rw [add_assoc]
    rw [← mul_add]
    rw [IH]
    simp
    rw [tsub_add_cancel_of_le]
    simp

theorem BernoulliExpNegSampleGenLoop_apply_true (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) true = ENNReal.ofReal (Real.exp (- iter)) := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop]
  · rename_i iter IH
    unfold BernoulliExpNegSampleGenLoop
    split
    · contradiction
    · rename_i h
      simp [h]
      simp [tsum_bool, IH]
      clear IH
      have A : (1 : ENNReal) = (1 : ℕ) / (1 : ℕ+) := by
        simp only [cast_one, PNat.one_coe, div_one]
      rw [BernoulliExpNegSampleUnit_apply_true 1 1 (le_refl 1) 1 A]
      rw [Real.exp_add]
      rw [ENNReal.ofReal_mul']
      · exact rfl
      · apply Real.exp_nonneg (-↑iter)

theorem BernoulliExpNegSampleGenLoop_apply_false (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) false = 1 - ENNReal.ofReal (Real.exp (- iter)) := by
  have A := BernoulliExpNegSampleGenLoop_normalizes iter
  simp [tsum_bool] at A
  rw [BernoulliExpNegSampleGenLoop_apply_true] at A
  rw [← A]
  simp

/--
Bernoulli negative exponential sampler is a proper distribution
-/
@[simp]
theorem BernoulliExpNegSample_normalizes (num : Nat) (den : PNat) :
  (∑' b : Bool, (BernoulliExpNegSample num den) b) = 1 := by
  unfold BernoulliExpNegSample
  split
  · rename_i h
    have A := BernoulliExpNegSampleUnit_normalizes num den h ((num : NNReal) / (den : NNReal)) rfl
    simp [tsum_bool] at *
    rw [A]
  · rename_i h
    simp [tsum_bool]
    rw [add_assoc]
    rw [← mul_add]
    have A := BernoulliExpNegSampleUnit_normalizes (num % den) den (rat_less_floor_le1 num den) (((num % (den : ℕ)) : ENNReal) / (den : ENNReal)) rfl
    simp [tsum_bool] at A
    rw [A]
    clear A
    simp
    have A := BernoulliExpNegSampleGenLoop_normalizes (num / den)
    simp [tsum_bool] at A
    rw [A]

theorem ENNReal_Real_mul_absorb (a : ENNReal) (b : ℝ) (h1 : b ≥ 0) :
  ENNReal.toReal a * b = ENNReal.toReal (a * (ENNReal.ofReal b)) := by
  simp
  left
  exact (ENNReal.toReal_ofReal h1).symm

theorem Nat_eq_to_ENNReal_eq (a b : ℕ) (h : a = b) :
  (a : ENNReal) = (b : ENNReal) := by
  exact congrArg Nat.cast h

theorem ENNReal_eq_to_Real_eq (a b : ENNReal) (h : a = b) :
  a.toReal = b.toReal := by
  exact congrArg ENNReal.toReal h

/--
Evaluation of Bernoulli negative exponential sampler at ``true``
-/
@[simp]
theorem BernoulliExpNegSample_apply_true (num : Nat) (den : PNat):
  (BernoulliExpNegSample num den) true = ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  simp [BernoulliExpNegSample, ite_apply]
  split
  · rename_i h
    rw [BernoulliExpNegSampleUnit_apply_true num den h ((num : NNReal) / (den : NNReal)) rfl]
    congr
    rw [ENNReal.toReal_div]
    simp
  · rename_i h
    simp [tsum_bool]
    rw [BernoulliExpNegSampleGenLoop_apply_true]
    rw [BernoulliExpNegSampleUnit_apply_true (num % den) den _ (((num % (den : ℕ)) : NNReal) / (den : NNReal)) rfl]
    · rw [← ENNReal.ofReal_mul']
      · rw [← Real.exp_add]
        congr
        rw [← @neg_add_rev]
        congr
        have A := (@ENNReal.toReal_ofReal_eq_iff ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) : ℝ)).2
        have B : 0 ≤ ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) : ℝ) := cast_nonneg (num / ↑den)
        have C := A B
        rw [← C]
        rw [← ENNReal.toReal_add]
        · clear A C
          have FOO := Nat.mod_add_div num den
          have BAR := Nat_eq_to_ENNReal_eq _ _ FOO
          have QUUX := ENNReal_eq_to_Real_eq _ _ BAR
          simp at QUUX
          have X : (den : ℝ) ≠ 0 := NeZero.natCast_ne (↑den) ℝ
          rw [eq_div_iff X]
          rw [← QUUX]
          have A : (den : ℝ) ≥ 0 := by
            exact cast_nonneg ↑den
          rw [ENNReal_Real_mul_absorb _ _ A]
          congr
          simp
          rw [add_mul]
          conv =>
            right
            right
            rw [mul_comm]
          congr
          clear X
          have X : (den : ENNReal) ≠ 0 := NeZero.natCast_ne (↑den) ENNReal
          have Y : (den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top ↑den
          rw [ENNReal.div_mul_cancel X Y]
        · have X : (den : ENNReal) ≠ 0 := NeZero.natCast_ne (↑den) ENNReal
          have Z : (den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top ↑den
          clear A B C h
          rw [← lt_top_iff_ne_top]
          rw [ENNReal.div_lt_iff (by exact Or.inl X) (by exact Or.inl Z)]
          have A := @Nat.mod_lt num den (PNat.pos den)
          rw [ENNReal.top_mul (by exact X)]
          rw [← lt_top_iff_ne_top] at Z
          exact (cmp_eq_gt_iff (⊤ : ENNReal) ↑(num % ↑den)).mp rfl
        · exact ENNReal.ofReal_ne_top
      · apply Real.exp_nonneg

/--
Evaluation of Bernoulli negative exponential sampler at ``false``
-/
@[simp]
theorem BernoulliExpNegSample_apply_false (num : Nat) (den : PNat) :
  (BernoulliExpNegSample num den) false = 1 - ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  have A := BernoulliExpNegSample_normalizes num den
  simp [tsum_bool] at A
  rw [← A]
  simp

end SLang
