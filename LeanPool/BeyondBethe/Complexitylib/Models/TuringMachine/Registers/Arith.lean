/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.ForReg
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.RegisterOps

/-!
# Derived register arithmetic

Addition, copying, and multiply-accumulate over unary registers, composed from
`forRegTM`, `incRegTM`, and `clearRegTM` — no new hand-rolled machines. Each
spec is one application of `forRegTM_hoareTime` with an iteration-indexed
ghost family, plus `Function.update` bookkeeping.

Time bounds are deliberately loose (rounded up via `HoareTime.mono_bound`);
only their polynomial shape matters downstream.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- `dst += src` (repeat-increment, fueled by `src`). -/
def addIntoTM (src dst : Fin n) : TM n := forRegTM (incRegTM dst) src

/-- **`addIntoTM` Hoare specification.** From `regTape a` in `src` and `regTape b` in
    `dst`, reach `regTape (b + a)` in `dst`; `src` and everything else untouched. -/
theorem addIntoTM_hoareTime (src dst : Fin n) (hne : src ≠ dst) (a b : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ src → Parked (work₀ i))
    (hsrc : work₀ src = regTape a) (hdst : work₀ dst = regTape b) :
    (addIntoTM src dst).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ dst (regTape (b + a))) ys)
      (a * ((2 * (b + a) + 4) + 2) + (a + 2)) := by
  have hbody : ∀ i, i < a → (incRegTM dst).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst (regTape (b + i))) src
          ⟨i + 2, regCells a⟩ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst (regTape (b + (i + 1)))) src
          ⟨i + 2, regCells a⟩ ∧ OutAcc ys out)
      (2 * (b + a) + 4) := by
    intro i hi
    have hspec := incRegTM_hoareTime dst (b + i) inp₀
      (Function.update (Function.update work₀ dst (regTape (b + i))) src
        ⟨i + 2, regCells a⟩) ys hinp₀
      (fun j hj => by
        by_cases hjs : j = src
        · subst hjs
          rw [Function.update_self]
          exact parked_regCells (by omega)
        · rw [Function.update_of_ne hjs]
          by_cases hjd : j = dst
          · subst hjd
            rw [Function.update_self]
            exact parked_regTape _
          · rw [Function.update_of_ne hjd]
            exact hwork₀ j hjs)
      (by
        rw [Function.update_of_ne (fun h => hne h.symm), Function.update_self])
    have hfun : Function.update
        (Function.update (Function.update work₀ dst (regTape (b + i))) src
          ⟨i + 2, regCells a⟩) dst (regTape (b + i + 1))
        = Function.update (Function.update work₀ dst (regTape (b + (i + 1)))) src
            ⟨i + 2, regCells a⟩ := by
      rw [Function.update_comm hne, Function.update_idem]
      rfl
    refine (hspec.consequence (fun inp work out h => h) ?_ ?_)
    · rintro inp work out ⟨h1, h2, h3⟩
      exact ⟨h1, by rw [h2, hfun], h3⟩
    · omega
  have hrule := forRegTM_hoareTime (incRegTM dst) src a inp₀
    (fun i => Function.update work₀ dst (regTape (b + i))) (fun _ => ys)
    (2 * (b + a) + 4) hinp₀
    (fun i => by
      show Function.update work₀ dst (regTape (b + i)) src = regTape a
      rw [Function.update_of_ne hne]
      exact hsrc)
    (fun i j hj => by
      show Parked (Function.update work₀ dst (regTape (b + i)) j)
      by_cases hjd : j = dst
      · subst hjd
        rw [Function.update_self]
        exact parked_regTape _
      · rw [Function.update_of_ne hjd]
        exact hwork₀ j hj)
    hbody
  have hw0 : Function.update work₀ dst (regTape (b + 0)) = work₀ := by
    rw [show regTape (b + 0) = work₀ dst from by rw [Nat.add_zero, hdst],
      Function.update_eq_self]
  exact hrule.weaken_pre (fun inp work out h => by
    show EmitPred inp₀ (Function.update work₀ dst (regTape (b + 0))) ys inp work out
    rw [hw0]
    exact h)

/-- `dst := src` (clear then add). -/
def copyIntoTM (src dst : Fin n) : TM n := seqTM (clearRegTM dst) (addIntoTM src dst)

/-- **`copyIntoTM` Hoare specification.** -/
theorem copyIntoTM_hoareTime (src dst : Fin n) (hne : src ≠ dst) (a b : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ src → Parked (work₀ i))
    (hsrc : work₀ src = regTape a) (hdst : work₀ dst = regTape b) :
    (copyIntoTM src dst).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ dst (regTape a)) ys)
      ((2 * b + 4) + 1 + (a * ((2 * (0 + a) + 4) + 2) + (a + 2))) := by
  have hclear := clearRegTM_hoareTime dst b inp₀ work₀ ys hinp₀
    (fun i hi => by
      by_cases his : i = src
      · subst his; rw [hsrc]; exact parked_regTape _
      · exact hwork₀ i (fun h => his h)) hdst
  have hadd := addIntoTM_hoareTime src dst hne a 0 inp₀
    (Function.update work₀ dst (regTape 0)) ys hinp₀
    (fun i hi => by
      by_cases hid : i = dst
      · subst hid; rw [Function.update_self]; exact parked_regTape _
      · rw [Function.update_of_ne hid]; exact hwork₀ i hi)
    (by rw [Function.update_of_ne hne]; exact hsrc)
    (by rw [Function.update_self])
  have hmidP : ∀ i, Parked (Function.update work₀ dst (regTape 0) i) := by
    intro i
    by_cases hid : i = dst
    · subst hid; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hid]
      by_cases his : i = src
      · subst his; rw [hsrc]; exact parked_regTape _
      · exact hwork₀ i his
  have hseq := seqTM_hoareTime (clearRegTM dst) (addIntoTM src dst) hclear
    (emitPred_transition hinp₀ hmidP ys) hadd
  refine hseq.strengthen_post ?_
  rintro inp work out ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2, Function.update_idem, Nat.zero_add]

/-- `dst += src₁ * src₂` (repeat-add, fueled by `src₁`). -/
def mulAddIntoTM (src₁ src₂ dst : Fin n) : TM n :=
  forRegTM (addIntoTM src₂ dst) src₁

/-- The (loose) per-iteration budget of `mulAddIntoTM`. -/
def mulAddBound (a b d : ℕ) : ℕ := b * ((2 * (d + a * b + b) + 4) + 2) + (b + 2)

/-- **`mulAddIntoTM` Hoare specification.** From `regTape a`, `regTape b`, `regTape d`
    in `src₁`, `src₂`, `dst`, reach `regTape (d + a·b)` in `dst`. -/
theorem mulAddIntoTM_hoareTime (src₁ src₂ dst : Fin n)
    (h12 : src₁ ≠ src₂) (h1d : src₁ ≠ dst) (h2d : src₂ ≠ dst) (a b d : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ src₁ → Parked (work₀ i))
    (h1 : work₀ src₁ = regTape a) (h2 : work₀ src₂ = regTape b)
    (hd : work₀ dst = regTape d) :
    (mulAddIntoTM src₁ src₂ dst).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ dst (regTape (d + a * b))) ys)
      (a * (mulAddBound a b d + 2) + (a + 2)) := by
  have hbody : ∀ i, i < a → (addIntoTM src₂ dst).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst (regTape (d + i * b))) src₁
          ⟨i + 2, regCells a⟩ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst (regTape (d + (i + 1) * b)))
          src₁ ⟨i + 2, regCells a⟩ ∧ OutAcc ys out)
      (mulAddBound a b d) := by
    intro i hi
    have hspec := addIntoTM_hoareTime src₂ dst h2d b (d + i * b) inp₀
      (Function.update (Function.update work₀ dst (regTape (d + i * b))) src₁
        ⟨i + 2, regCells a⟩) ys hinp₀
      (fun j hj => by
        by_cases hj1 : j = src₁
        · subst hj1
          rw [Function.update_self]
          exact parked_regCells (by omega)
        · rw [Function.update_of_ne hj1]
          by_cases hjd : j = dst
          · subst hjd
            rw [Function.update_self]
            exact parked_regTape _
          · rw [Function.update_of_ne hjd]
            exact hwork₀ j hj1)
      (by
        rw [Function.update_of_ne (fun h => h12 h.symm),
          Function.update_of_ne h2d]
        exact h2)
      (by
        rw [Function.update_of_ne (fun h => h1d h.symm), Function.update_self])
    have hfun : Function.update
        (Function.update (Function.update work₀ dst (regTape (d + i * b))) src₁
          ⟨i + 2, regCells a⟩) dst (regTape (d + i * b + b))
        = Function.update (Function.update work₀ dst (regTape (d + (i + 1) * b)))
            src₁ ⟨i + 2, regCells a⟩ := by
      rw [Function.update_comm h1d, Function.update_idem,
        show d + i * b + b = d + (i + 1) * b from by rw [Nat.succ_mul]; omega]
    have him : i * b ≤ a * b := Nat.mul_le_mul_right b (le_of_lt hi)
    have hinner : (2 * (d + i * b + b) + 4) + 2 ≤ (2 * (d + a * b + b) + 4) + 2 := by
      omega
    have hbnd := Nat.mul_le_mul_left b hinner
    refine hspec.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      exact ⟨g1, by rw [g2, hfun], g3⟩
    · show b * ((2 * (d + i * b + b) + 4) + 2) + (b + 2) ≤ mulAddBound a b d
      rw [mulAddBound]
      omega
  have hrule := forRegTM_hoareTime (addIntoTM src₂ dst) src₁ a inp₀
    (fun i => Function.update work₀ dst (regTape (d + i * b))) (fun _ => ys)
    (mulAddBound a b d) hinp₀
    (fun i => by
      show Function.update work₀ dst (regTape (d + i * b)) src₁ = regTape a
      rw [Function.update_of_ne h1d]
      exact h1)
    (fun i j hj => by
      show Parked (Function.update work₀ dst (regTape (d + i * b)) j)
      by_cases hjd : j = dst
      · subst hjd
        rw [Function.update_self]
        exact parked_regTape _
      · rw [Function.update_of_ne hjd]
        exact hwork₀ j hj)
    hbody
  have hw0 : Function.update work₀ dst (regTape (d + 0 * b)) = work₀ := by
    rw [show regTape (d + 0 * b) = work₀ dst from by
        rw [Nat.zero_mul, Nat.add_zero, hd],
      Function.update_eq_self]
  exact hrule.weaken_pre (fun inp work out h => by
    show EmitPred inp₀ (Function.update work₀ dst (regTape (d + 0 * b))) ys inp work out
    rw [hw0]
    exact h)

-- ════════════════════════════════════════════════════════════════════════
-- Iterated machines (constant-building)
-- ════════════════════════════════════════════════════════════════════════

/-- Run `m` in sequence `c` times. -/
def iterTM (m : TM n) : ℕ → TM n
  | 0 => skipTM
  | c + 1 => seqTM m (iterTM m c)

/-- **Iterated increment**: add the constant `c` to register `q`. -/
theorem iterTM_incRegTM_hoareTime (q : Fin n) (c : ℕ) :
    ∀ (d : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool),
    Parked inp₀ → (∀ i, Parked (work₀ i)) → work₀ q = regTape d →
    (iterTM (incRegTM q) c).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ q (regTape (d + c))) ys)
      (c * (2 * (d + c) + 5) + 1) := by
  induction c with
  | zero =>
    intro d inp₀ work₀ ys hinp₀ hwork₀ hq
    have hskip := skipTM_hoareTime inp₀ work₀ ys hinp₀ hwork₀
    refine hskip.consequence (fun _ _ _ h => h) ?_ (by omega)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, show regTape (d + 0) = work₀ q from by rw [Nat.add_zero, hq],
      Function.update_eq_self]
  | succ c ih =>
    intro d inp₀ work₀ ys hinp₀ hwork₀ hq
    have hinc := incRegTM_hoareTime q d inp₀ work₀ ys hinp₀
      (fun i _ => hwork₀ i) hq
    have hmidP : ∀ i, Parked (Function.update work₀ q (regTape (d + 1)) i) := by
      intro i
      by_cases hiq : i = q
      · subst hiq; rw [Function.update_self]; exact parked_regTape _
      · rw [Function.update_of_ne hiq]; exact hwork₀ i
    have hrest := ih (d + 1) inp₀ (Function.update work₀ q (regTape (d + 1))) ys
      hinp₀ hmidP (by rw [Function.update_self])
    have hseq := seqTM_hoareTime (incRegTM q) (iterTM (incRegTM q) c) hinc
      (emitPred_transition hinp₀ hmidP ys) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, g3⟩
      rw [g2, Function.update_idem,
        show d + 1 + c = d + (c + 1) from by omega]
    · have hmul : (c + 1) * (2 * (d + (c + 1)) + 5)
          = c * (2 * (d + (c + 1)) + 5) + (2 * (d + (c + 1)) + 5) :=
        Nat.succ_mul ..
      have hmono : c * (2 * (d + 1 + c) + 5) ≤ c * (2 * (d + (c + 1)) + 5) :=
        Nat.mul_le_mul_left c (by omega)
      omega

end TM

end Complexity
