/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.EmitSeq
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.Arith

/-!
# Horner layers: polynomial register evaluation

The reduction emitter's variable indices are mixed-radix numerals
(`flatVar`), and its time budget is `p.eval n` — both are computed by
iterating the single **Horner layer** `tmp := tmp · X + c` over unary
registers. This file builds that layer from the `Arith` register calculus
and folds it into `polyEvalTM`.

To keep the time accounting sane across long `seqTM` chains, every stage
bound is rounded up to the single monotone budget `opBudget M`, where `M`
bounds every register value in play. Only the polynomial shape of the final
bound matters (`FP` quantifies the degree existentially), so all budgets
are deliberately loose.

## Main definitions

- `TM.opBudget` — the uniform per-operation time budget
- `TM.setConstTM` — `q := c`
- `TM.hornerLayerRegTM` — `tmp := tmp · X + comp` (register addend)
- `TM.hornerLayerConstTM` — `tmp := tmp · X + c` (constant addend)

## Main results

- the `_hoareTime` specification of each machine
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- The uniform operation budget
-- ════════════════════════════════════════════════════════════════════════

/-- One budget bounds every register operation whose values are at most `M`:
    increments, clears, copies, additions, multiply-accumulates, and literal
    emissions. Cubic in `M` because `mulAddIntoTM`'s bound is (product value)
    × (per-mark sweep length). -/
def opBudget (M : ℕ) : ℕ := 32 * ((M + 2) * (M + 2) * (M + 2))

/-- Anything at most quadratic in `M + 2` (with constant `6`) fits in `opBudget M`. -/
theorem le_opBudget_of_le {a M : ℕ} (h : a ≤ 6 * (M + 2) * (M + 2)) :
    a ≤ opBudget M := by
  refine le_trans h ?_
  rw [opBudget]
  have h2 : 2 ≤ M + 2 := by omega
  calc 6 * (M + 2) * (M + 2) = 6 * ((M + 2) * (M + 2)) := by ring
    _ ≤ 32 * ((M + 2) * ((M + 2) * (M + 2))) := by
        have : (M + 2) * (M + 2) ≤ (M + 2) * ((M + 2) * (M + 2)) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
    _ = 32 * ((M + 2) * (M + 2) * (M + 2)) := by ring

/-- `incRegTM` fits the budget. -/
theorem incRegTM_le_opBudget {d M : ℕ} (h : d ≤ M) : 2 * d + 4 ≤ opBudget M :=
  le_opBudget_of_le (by nlinarith)

/-- `clearRegTM` fits the budget. -/
theorem clearRegTM_le_opBudget {d M : ℕ} (h : d ≤ M) : 2 * d + 4 ≤ opBudget M :=
  incRegTM_le_opBudget h

/-- `skipTM` fits the budget. -/
theorem one_le_opBudget {M : ℕ} : 1 ≤ opBudget M :=
  le_opBudget_of_le (by nlinarith)

/-- `addIntoTM` fits the budget. -/
theorem addIntoTM_le_opBudget {a b M : ℕ} (ha : a ≤ M) (hab : b + a ≤ M) :
    a * ((2 * (b + a) + 4) + 2) + (a + 2) ≤ opBudget M := by
  refine le_opBudget_of_le ?_
  have h1 : a * ((2 * (b + a) + 4) + 2) ≤ M * (2 * M + 6) :=
    Nat.mul_le_mul ha (by omega)
  nlinarith

/-- `iterTM (incRegTM q) c` fits the budget. -/
theorem iterTM_incRegTM_le_opBudget {c d M : ℕ} (h : d + c ≤ M) :
    c * (2 * (d + c) + 5) + 1 ≤ opBudget M := by
  refine le_opBudget_of_le ?_
  have h1 : c * (2 * (d + c) + 5) ≤ M * (2 * M + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- `copyIntoTM` fits the budget. -/
theorem copyIntoTM_le_opBudget {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    (2 * b + 4) + 1 + (a * ((2 * (0 + a) + 4) + 2) + (a + 2)) ≤ opBudget M := by
  refine le_opBudget_of_le ?_
  have h1 : a * ((2 * (0 + a) + 4) + 2) ≤ M * (2 * M + 6) :=
    Nat.mul_le_mul ha (by omega)
  nlinarith

/-- `setConstTM` fits the budget. -/
theorem setConstTM_le_opBudget {c d M : ℕ} (hc : c ≤ M) (hd : d ≤ M) :
    (2 * d + 4) + 1 + (c * (2 * c + 5) + 1) ≤ opBudget M := by
  refine le_opBudget_of_le ?_
  have h1 : c * (2 * c + 5) ≤ M * (2 * M + 5) := Nat.mul_le_mul hc (by omega)
  nlinarith

/-- `emitLitTM` fits the budget. -/
theorem emitLitTM_le_opBudget {v M : ℕ} (h : v ≤ M) : 3 * v + 9 ≤ opBudget M :=
  le_opBudget_of_le (by nlinarith)

/-- `mulAddIntoTM` fits the budget, provided the accumulated product stays
    below `M`. -/
theorem mulAddIntoTM_le_opBudget {a b d M : ℕ} (ha : a ≤ M) (hb : b ≤ M)
    (hd : d + a * b ≤ M) :
    a * (mulAddBound a b d + 2) + (a + 2) ≤ opBudget M := by
  have h1 : mulAddBound a b d ≤ M * (4 * M + 10) + (M + 2) := by
    rw [mulAddBound]
    exact Nat.add_le_add (Nat.mul_le_mul hb (by omega)) (by omega)
  have h2 : a * (mulAddBound a b d + 2) + (a + 2)
      ≤ M * ((M * (4 * M + 10) + (M + 2)) + 2) + (M + 2) :=
    Nat.add_le_add (Nat.mul_le_mul ha (by omega)) (by omega)
  refine le_trans h2 ?_
  rw [opBudget]
  nlinarith

-- ════════════════════════════════════════════════════════════════════════
-- setConstTM: load a constant into a register
-- ════════════════════════════════════════════════════════════════════════

/-- `q := c` (clear, then increment `c` times). -/
def setConstTM (q : Fin n) (c : ℕ) : TM n :=
  seqTM (clearRegTM q) (iterTM (incRegTM q) c)

/-- **`setConstTM` Hoare specification.** -/
theorem setConstTM_hoareTime (q : Fin n) (c d : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hq : work₀ q = regTape d) :
    (setConstTM q c).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ q (regTape c)) ys)
      ((2 * d + 4) + 1 + (c * (2 * c + 5) + 1)) := by
  have hclear := clearRegTM_hoareTime q d inp₀ work₀ ys hinp₀
    (fun i _ => hwork₀ i) hq
  have hmidP : ∀ i, Parked (Function.update work₀ q (regTape 0) i) := by
    intro i
    by_cases hiq : i = q
    · subst hiq; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hiq]; exact hwork₀ i
  have hiter := iterTM_incRegTM_hoareTime q c 0 inp₀ (Function.update work₀ q (regTape 0))
    ys hinp₀ hmidP (by rw [Function.update_self])
  have hseq := seqTM_hoareTime (clearRegTM q) (iterTM (incRegTM q) c) hclear
    (emitPred_transition hinp₀ hmidP ys) hiter
  refine hseq.consequence (fun _ _ _ h => h) ?_
    (by simp only [Nat.zero_add]; exact le_refl _)
  rintro inp work out ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2, Function.update_idem, Nat.zero_add]

-- ════════════════════════════════════════════════════════════════════════
-- Horner layers: tmp := tmp · X + addend
-- ════════════════════════════════════════════════════════════════════════

/-- One Horner layer with a **register** addend:
    `tmp := tmp · X + comp` (scratch `tmp2` ends holding the same value). -/
def hornerLayerRegTM (X comp tmp tmp2 : Fin n) : TM n :=
  seqTM (clearRegTM tmp2)
    (seqTM (mulAddIntoTM tmp X tmp2)
      (seqTM (addIntoTM comp tmp2) (copyIntoTM tmp2 tmp)))

/-- One Horner layer with a **constant** addend:
    `tmp := tmp · X + c` (scratch `tmp2` ends holding the same value). -/
def hornerLayerConstTM (X tmp tmp2 : Fin n) (c : ℕ) : TM n :=
  seqTM (clearRegTM tmp2)
    (seqTM (mulAddIntoTM tmp X tmp2)
      (seqTM (iterTM (incRegTM tmp2) c) (copyIntoTM tmp2 tmp)))

/-- The (uniform) time budget of one Horner layer. -/
def layerBudget (M : ℕ) : ℕ := 4 * opBudget M + 3

section HornerLayer

variable {X comp tmp tmp2 : Fin n}

/-- **`hornerLayerRegTM` Hoare specification.** From `tmp = v`, `X = x`,
    `comp = w` (and any `tmp2 = u`), reach `tmp = tmp2 = v·x + w` with all
    other tapes untouched, within `layerBudget M` steps, provided every value
    in play is at most `M`. -/
theorem hornerLayerRegTM_hoareTime
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (hct2 : comp ≠ tmp2)
    (M x v w u : ℕ) (hx : x ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (hres : v * x + w ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hX : work₀ X = regTape x) (hc : work₀ comp = regTape w)
    (ht : work₀ tmp = regTape v) (ht2 : work₀ tmp2 = regTape u) :
    (hornerLayerRegTM X comp tmp tmp2).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2 (regTape (v * x + w))) tmp
          (regTape (v * x + w))) ys)
      (layerBudget M) := by
  set A : Fin n → Tape := Function.update work₀ tmp2 (regTape 0) with hA
  set B : Fin n → Tape := Function.update work₀ tmp2 (regTape (v * x)) with hB
  set C : Fin n → Tape := Function.update work₀ tmp2 (regTape (v * x + w)) with hC
  have hAP : ∀ i, Parked (A i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hA, Function.update_self]; exact parked_regTape _
    · rw [hA, Function.update_of_ne hi]; exact hwork₀ i
  have hBP : ∀ i, Parked (B i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hB, Function.update_self]; exact parked_regTape _
    · rw [hB, Function.update_of_ne hi]; exact hwork₀ i
  have hCP : ∀ i, Parked (C i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hC, Function.update_self]; exact parked_regTape _
    · rw [hC, Function.update_of_ne hi]; exact hwork₀ i
  -- Stage 1: clear tmp2.
  have h₁ : (clearRegTM tmp2).HoareTime (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ A ys) (opBudget M) :=
    (clearRegTM_hoareTime tmp2 u inp₀ work₀ ys hinp₀
      (fun i _ => hwork₀ i) ht2).mono_bound (clearRegTM_le_opBudget hu)
  -- Stage 2: tmp2 += tmp · X.
  have h₂ : (mulAddIntoTM tmp X tmp2).HoareTime (EmitPred inp₀ A ys)
      (EmitPred inp₀ B ys) (opBudget M) := by
    refine (mulAddIntoTM_hoareTime tmp X tmp2 (fun h => hXt h.symm) htt2 hXt2
      v x 0 inp₀ A ys hinp₀ (fun i _ => hAP i)
      (by rw [hA, Function.update_of_ne htt2]; exact ht)
      (by rw [hA, Function.update_of_ne hXt2]; exact hX)
      (by rw [hA, Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (mulAddIntoTM_le_opBudget hv hx (by omega))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hA, Function.update_idem, Nat.zero_add, hB]
  -- Stage 3: tmp2 += comp.
  have h₃ : (addIntoTM comp tmp2).HoareTime (EmitPred inp₀ B ys)
      (EmitPred inp₀ C ys) (opBudget M) := by
    refine (addIntoTM_hoareTime comp tmp2 hct2 w (v * x) inp₀ B ys hinp₀
      (fun i _ => hBP i)
      (by rw [hB, Function.update_of_ne hct2]; exact hc)
      (by rw [hB, Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (addIntoTM_le_opBudget (by omega) hres)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hB, Function.update_idem, hC]
  -- Stage 4: tmp := tmp2.
  have h₄ : (copyIntoTM tmp2 tmp).HoareTime (EmitPred inp₀ C ys)
      (EmitPred inp₀ (Function.update C tmp (regTape (v * x + w))) ys)
      (opBudget M) := by
    refine (copyIntoTM_hoareTime tmp2 tmp (fun h => htt2 h.symm) (v * x + w) v
      inp₀ C ys hinp₀ (fun i _ => hCP i)
      (by rw [hC, Function.update_self])
      (by rw [hC, Function.update_of_ne htt2]; exact ht)).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) (copyIntoTM_le_opBudget hres hv)
  -- Glue.
  have h₃₄ := seqTM_hoareTime (addIntoTM comp tmp2) (copyIntoTM tmp2 tmp) h₃
    (emitPred_transition hinp₀ hCP ys) h₄
  have h₂₃₄ := seqTM_hoareTime (mulAddIntoTM tmp X tmp2) _ h₂
    (emitPred_transition hinp₀ hBP ys) h₃₄
  have h := seqTM_hoareTime (clearRegTM tmp2) _ h₁
    (emitPred_transition hinp₀ hAP ys) h₂₃₄
  refine h.consequence (fun _ _ _ hp => hp) ?_ (by rw [layerBudget]; omega)
  rintro inp work out ⟨g1, g2, g3⟩
  exact ⟨g1, by rw [g2, hC], g3⟩

/-- **`hornerLayerConstTM` Hoare specification.** From `tmp = v`, `X = x`
    (and any `tmp2 = u`), reach `tmp = tmp2 = v·x + c`. -/
theorem hornerLayerConstTM_hoareTime
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (M x v c u : ℕ) (hx : x ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (hres : v * x + c ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hX : work₀ X = regTape x)
    (ht : work₀ tmp = regTape v) (ht2 : work₀ tmp2 = regTape u) :
    (hornerLayerConstTM X tmp tmp2 c).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2 (regTape (v * x + c))) tmp
          (regTape (v * x + c))) ys)
      (layerBudget M) := by
  set A : Fin n → Tape := Function.update work₀ tmp2 (regTape 0) with hA
  set B : Fin n → Tape := Function.update work₀ tmp2 (regTape (v * x)) with hB
  set C : Fin n → Tape := Function.update work₀ tmp2 (regTape (v * x + c)) with hC
  have hAP : ∀ i, Parked (A i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hA, Function.update_self]; exact parked_regTape _
    · rw [hA, Function.update_of_ne hi]; exact hwork₀ i
  have hBP : ∀ i, Parked (B i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hB, Function.update_self]; exact parked_regTape _
    · rw [hB, Function.update_of_ne hi]; exact hwork₀ i
  have hCP : ∀ i, Parked (C i) := by
    intro i
    by_cases hi : i = tmp2
    · subst hi; rw [hC, Function.update_self]; exact parked_regTape _
    · rw [hC, Function.update_of_ne hi]; exact hwork₀ i
  -- Stage 1: clear tmp2.
  have h₁ : (clearRegTM tmp2).HoareTime (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ A ys) (opBudget M) :=
    (clearRegTM_hoareTime tmp2 u inp₀ work₀ ys hinp₀
      (fun i _ => hwork₀ i) ht2).mono_bound (clearRegTM_le_opBudget hu)
  -- Stage 2: tmp2 += tmp · X.
  have h₂ : (mulAddIntoTM tmp X tmp2).HoareTime (EmitPred inp₀ A ys)
      (EmitPred inp₀ B ys) (opBudget M) := by
    refine (mulAddIntoTM_hoareTime tmp X tmp2 (fun h => hXt h.symm) htt2 hXt2
      v x 0 inp₀ A ys hinp₀ (fun i _ => hAP i)
      (by rw [hA, Function.update_of_ne htt2]; exact ht)
      (by rw [hA, Function.update_of_ne hXt2]; exact hX)
      (by rw [hA, Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (mulAddIntoTM_le_opBudget hv hx (by omega))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hA, Function.update_idem, Nat.zero_add, hB]
  -- Stage 3: tmp2 += c.
  have h₃ : (iterTM (incRegTM tmp2) c).HoareTime (EmitPred inp₀ B ys)
      (EmitPred inp₀ C ys) (opBudget M) := by
    refine (iterTM_incRegTM_hoareTime tmp2 c (v * x) inp₀ B ys hinp₀ hBP
      (by rw [hB, Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (iterTM_incRegTM_le_opBudget hres)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hB, Function.update_idem, hC]
  -- Stage 4: tmp := tmp2.
  have h₄ : (copyIntoTM tmp2 tmp).HoareTime (EmitPred inp₀ C ys)
      (EmitPred inp₀ (Function.update C tmp (regTape (v * x + c))) ys)
      (opBudget M) := by
    refine (copyIntoTM_hoareTime tmp2 tmp (fun h => htt2 h.symm) (v * x + c) v
      inp₀ C ys hinp₀ (fun i _ => hCP i)
      (by rw [hC, Function.update_self])
      (by rw [hC, Function.update_of_ne htt2]; exact ht)).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) (copyIntoTM_le_opBudget hres hv)
  -- Glue.
  have h₃₄ := seqTM_hoareTime (iterTM (incRegTM tmp2) c) (copyIntoTM tmp2 tmp) h₃
    (emitPred_transition hinp₀ hCP ys) h₄
  have h₂₃₄ := seqTM_hoareTime (mulAddIntoTM tmp X tmp2) _ h₂
    (emitPred_transition hinp₀ hBP ys) h₃₄
  have h := seqTM_hoareTime (clearRegTM tmp2) _ h₁
    (emitPred_transition hinp₀ hAP ys) h₂₃₄
  refine h.consequence (fun _ _ _ hp => hp) ?_ (by rw [layerBudget]; omega)
  rintro inp work out ⟨g1, g2, g3⟩
  exact ⟨g1, by rw [g2, hC], g3⟩

end HornerLayer

-- ════════════════════════════════════════════════════════════════════════
-- Folding layers: polynomial evaluation
-- ════════════════════════════════════════════════════════════════════════

/-- Horner accumulator over a coefficient list (highest degree first). -/
def hornerFold (x : ℕ) : List ℕ → ℕ → ℕ
  | [], a => a
  | c :: cs, a => hornerFold x cs (a * x + c)

/-- `hornerFold` over the empty coefficient list returns the accumulator. -/
@[simp] theorem hornerFold_nil (x a : ℕ) : hornerFold x [] a = a := rfl

/-- Unfolding lemma: one Horner layer replaces the accumulator `a` by `a * x + c`. -/
theorem hornerFold_cons (x c a : ℕ) (cs : List ℕ) :
    hornerFold x (c :: cs) a = hornerFold x cs (a * x + c) := rfl

/-- The Horner fold of a reversed coefficient window is the polynomial sum. -/
theorem hornerFold_reverse_range (f : ℕ → ℕ) (x : ℕ) :
    ∀ (k a : ℕ),
    hornerFold x ((List.range k).map f).reverse a
      = a * x ^ k + ∑ i ∈ Finset.range k, f i * x ^ i := by
  intro k
  induction k with
  | zero => intro a; simp
  | succ k ih =>
    intro a
    rw [List.range_succ, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
    rw [hornerFold_cons, ih, Finset.sum_range_succ]
    ring

/-- Crude but monotone bound on the Horner accumulator. -/
theorem hornerFold_le (x : ℕ) : ∀ (cs : List ℕ) (a : ℕ),
    hornerFold x cs a ≤ (a + cs.sum) * (x + 1) ^ cs.length := by
  intro cs
  induction cs with
  | nil => intro a; simp
  | cons c cs ih =>
    intro a
    rw [hornerFold_cons]
    refine le_trans (ih (a * x + c)) ?_
    rw [List.sum_cons, List.length_cons, pow_succ]
    have h1 : a * x + c + cs.sum ≤ (a + (c + cs.sum)) * (x + 1) := by
      have hexp : (a + (c + cs.sum)) * (x + 1)
          = a * x + a + ((c + cs.sum) * x + (c + cs.sum)) := by ring
      omega
    calc (a * x + c + cs.sum) * (x + 1) ^ cs.length
        ≤ ((a + (c + cs.sum)) * (x + 1)) * (x + 1) ^ cs.length :=
          Nat.mul_le_mul_right _ h1
      _ = (a + (c + cs.sum)) * ((x + 1) ^ cs.length * (x + 1)) := by ring

/-- Every prefix of the Horner fold is bounded by the full coefficient sum
    times the dominating power — the hypothesis-discharger for
    `hornerLayersTM_hoareTime`'s value cap. -/
theorem hornerFold_take_le (x : ℕ) (cs : List ℕ) (k : ℕ) :
    hornerFold x (cs.take k) 0 ≤ (cs.sum + 1) * (x + 1) ^ cs.length := by
  refine le_trans (hornerFold_le x _ 0) ?_
  have h1 : (cs.take k).sum ≤ cs.sum := by
    conv_rhs => rw [← List.take_append_drop k cs]
    rw [List.sum_append]
    omega
  have h2 : (x + 1) ^ (cs.take k).length ≤ (x + 1) ^ cs.length :=
    Nat.pow_le_pow_right (by omega)
      (by rw [List.length_take]; omega)
  calc (0 + (cs.take k).sum) * (x + 1) ^ (cs.take k).length
      ≤ (cs.sum + 1) * (x + 1) ^ cs.length :=
        Nat.mul_le_mul (by omega) h2

/-- Fold Horner layers (constant addends, highest first) over a register. -/
def hornerLayersTM (X tmp tmp2 : Fin n) (cs : List ℕ) : TM n :=
  bigSeqTM (cs.map (hornerLayerConstTM X tmp tmp2))

/-- **`hornerLayersTM` Hoare specification** (nonempty coefficient list).
    From `tmp = v`, reach `tmp = tmp2 = hornerFold x (c :: cs) v`, provided
    every intermediate accumulator value is at most `M`. -/
theorem hornerLayersTM_hoareTime (X tmp tmp2 : Fin n)
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (M x : ℕ) (hx : x ≤ M) (inp₀ : Tape) (hinp₀ : Parked inp₀) :
    ∀ (c : ℕ) (cs : List ℕ) (v u : ℕ) (work₀ : Fin n → Tape) (ys : List Bool),
    (∀ k, k ≤ (c :: cs).length → hornerFold x (List.take k (c :: cs)) v ≤ M) →
    u ≤ M →
    (∀ i, Parked (work₀ i)) →
    work₀ X = regTape x → work₀ tmp = regTape v → work₀ tmp2 = regTape u →
    (hornerLayersTM X tmp tmp2 (c :: cs)).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2
          (regTape (hornerFold x (c :: cs) v))) tmp
          (regTape (hornerFold x (c :: cs) v))) ys)
      ((c :: cs).length * (layerBudget M + 1) + 1) := by
  intro c cs
  induction cs generalizing c with
  | nil =>
    intro v u work₀ ys hpre hu hwork₀ hX ht ht2
    have hv : v ≤ M := by
      have := hpre 0 (by omega)
      simpa using this
    have hres : v * x + c ≤ M := by
      have := hpre 1 (by simp)
      simpa [hornerFold_cons] using this
    have hlayer := hornerLayerConstTM_hoareTime hXt hXt2 htt2 M x v c u
      hx hv hu hres inp₀ work₀ ys hinp₀ hwork₀ hX ht ht2
    set P : Fin n → Tape :=
      Function.update (Function.update work₀ tmp2 (regTape (v * x + c))) tmp
        (regTape (v * x + c)) with hP
    have hPP : ∀ i, Parked (P i) := by
      intro i
      by_cases hi : i = tmp
      · subst hi; rw [hP, Function.update_self]; exact parked_regTape _
      · rw [hP, Function.update_of_ne hi]
        by_cases hi2 : i = tmp2
        · subst hi2; rw [Function.update_self]; exact parked_regTape _
        · rw [Function.update_of_ne hi2]; exact hwork₀ i
    have hskip := skipTM_hoareTime inp₀ P ys hinp₀ hPP
    have hseq := seqTM_hoareTime (hornerLayerConstTM X tmp tmp2 c) skipTM hlayer
      (emitPred_transition hinp₀ hPP ys) hskip
    refine hseq.consequence (fun _ _ _ h => h) ?_
      (by simp only [List.length_cons, List.length_nil, Nat.zero_add,
            Nat.one_mul]; omega)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, hP, hornerFold_cons, hornerFold_nil], g3⟩
  | cons c' cs' ih =>
    intro v u work₀ ys hpre hu hwork₀ hX ht ht2
    have hv : v ≤ M := by
      have := hpre 0 (by omega)
      simpa using this
    have hv₁ : v * x + c ≤ M := by
      have := hpre 1 (by simp)
      simpa [hornerFold_cons] using this
    have hlayer := hornerLayerConstTM_hoareTime hXt hXt2 htt2 M x v c u
      hx hv hu hv₁ inp₀ work₀ ys hinp₀ hwork₀ hX ht ht2
    set P : Fin n → Tape :=
      Function.update (Function.update work₀ tmp2 (regTape (v * x + c))) tmp
        (regTape (v * x + c)) with hP
    have hPP : ∀ i, Parked (P i) := by
      intro i
      by_cases hi : i = tmp
      · subst hi; rw [hP, Function.update_self]; exact parked_regTape _
      · rw [hP, Function.update_of_ne hi]
        by_cases hi2 : i = tmp2
        · subst hi2; rw [Function.update_self]; exact parked_regTape _
        · rw [Function.update_of_ne hi2]; exact hwork₀ i
    have hpre' : ∀ k, k ≤ (c' :: cs').length →
        hornerFold x (List.take k (c' :: cs')) (v * x + c) ≤ M := by
      intro k hk
      have := hpre (k + 1) (by simpa using Nat.succ_le_succ hk)
      rwa [List.take_succ_cons, hornerFold_cons] at this
    have hrest := ih c' (v * x + c) (v * x + c) P ys hpre' hv₁ hPP
      (by rw [hP, Function.update_of_ne hXt, Function.update_of_ne hXt2]; exact hX)
      (by rw [hP, Function.update_self])
      (by rw [hP, Function.update_of_ne (fun h => htt2 h.symm),
            Function.update_self])
    have hseq := seqTM_hoareTime (hornerLayerConstTM X tmp tmp2 c)
      (hornerLayersTM X tmp tmp2 (c' :: cs')) hlayer
      (emitPred_transition hinp₀ hPP ys) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, g3⟩
      rw [g2, hP, Function.update_comm htt2, Function.update_idem,
        Function.update_idem,
        show hornerFold x (c' :: cs') (v * x + c)
          = hornerFold x (c :: c' :: cs') v from rfl]
    · have hmul : (c :: c' :: cs').length * (layerBudget M + 1)
          = (c' :: cs').length * (layerBudget M + 1) + (layerBudget M + 1) := by
        rw [List.length_cons]
        exact Nat.succ_mul ..
      omega

-- ════════════════════════════════════════════════════════════════════════
-- polyEvalTM
-- ════════════════════════════════════════════════════════════════════════

/-- The coefficient list of `p`, highest degree first. -/
def polyCoeffs (p : Polynomial ℕ) : List ℕ :=
  ((List.range (p.natDegree + 1)).map p.coeff).reverse

/-- The coefficient list of a polynomial is never empty (it has `natDegree + 1` entries). -/
theorem polyCoeffs_ne_nil (p : Polynomial ℕ) : polyCoeffs p ≠ [] := by
  simp [polyCoeffs]

/-- `polyCoeffs p` has exactly `p.natDegree + 1` entries. -/
@[simp] theorem polyCoeffs_length (p : Polynomial ℕ) :
    (polyCoeffs p).length = p.natDegree + 1 := by
  simp [polyCoeffs]

/-- **The Horner fold computes `p.eval`.** -/
theorem hornerFold_polyCoeffs (p : Polynomial ℕ) (x : ℕ) :
    hornerFold x (polyCoeffs p) 0 = p.eval x := by
  rw [polyCoeffs, hornerFold_reverse_range, Polynomial.eval_eq_sum_range]
  simp

/-- `tmp := p.eval x`, reading `x` from register `X` (Horner's rule over the
    hardwired coefficient list; `tmp2` is scratch and ends equal to `tmp`). -/
def polyEvalTM (X tmp tmp2 : Fin n) (p : Polynomial ℕ) : TM n :=
  seqTM (setConstTM tmp 0) (hornerLayersTM X tmp tmp2 (polyCoeffs p))

/-- **`polyEvalTM` Hoare specification.** From `X = x` (and any `tmp = v`,
    `tmp2 = u`), reach `tmp = tmp2 = p.eval x`, provided `M` caps `x`, the
    starting scratch values, and every Horner prefix value. -/
theorem polyEvalTM_hoareTime (X tmp tmp2 : Fin n)
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (p : Polynomial ℕ) (M x v u : ℕ) (hx : x ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (hpre : ∀ k, k ≤ p.natDegree + 1 →
      hornerFold x (List.take k (polyCoeffs p)) 0 ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hX : work₀ X = regTape x) (ht : work₀ tmp = regTape v)
    (ht2 : work₀ tmp2 = regTape u) :
    (polyEvalTM X tmp tmp2 p).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2 (regTape (p.eval x))) tmp
          (regTape (p.eval x))) ys)
      (opBudget M + 1 + ((p.natDegree + 1) * (layerBudget M + 1) + 1)) := by
  have hset := (setConstTM_hoareTime tmp 0 v inp₀ work₀ ys hinp₀ hwork₀
    ht).mono_bound (setConstTM_le_opBudget (by omega) hv)
  set A : Fin n → Tape := Function.update work₀ tmp (regTape 0) with hA
  have hAP : ∀ i, Parked (A i) := by
    intro i
    by_cases hi : i = tmp
    · subst hi; rw [hA, Function.update_self]; exact parked_regTape _
    · rw [hA, Function.update_of_ne hi]; exact hwork₀ i
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (polyCoeffs_ne_nil p)
  have hlen : (c :: cs).length = p.natDegree + 1 := by
    rw [← hcs, polyCoeffs_length]
  have hrest := hornerLayersTM_hoareTime X tmp tmp2 hXt hXt2 htt2 M x hx inp₀
    hinp₀ c cs 0 u A ys
    (by rw [← hcs, polyCoeffs_length]; exact hpre)
    hu hAP
    (by rw [hA, Function.update_of_ne hXt]; exact hX)
    (by rw [hA, Function.update_self])
    (by rw [hA, Function.update_of_ne (fun h => htt2 h.symm)]; exact ht2)
  have heval : hornerFold x (c :: cs) 0 = p.eval x := by
    rw [← hcs, hornerFold_polyCoeffs]
  rw [heval] at hrest
  have hseq := seqTM_hoareTime (setConstTM tmp 0)
    (hornerLayersTM X tmp tmp2 (c :: cs)) hset
    (emitPred_transition hinp₀ hAP ys) hrest
  have hmach : polyEvalTM X tmp tmp2 p
      = seqTM (setConstTM tmp 0) (hornerLayersTM X tmp tmp2 (c :: cs)) := by
    rw [polyEvalTM, hcs]
  rw [hmach]
  refine hseq.consequence (fun _ _ _ h => h) ?_ (by rw [hlen])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, g3⟩
  rw [g2, hA, Function.update_comm htt2, Function.update_idem]

end TM

end Complexity
