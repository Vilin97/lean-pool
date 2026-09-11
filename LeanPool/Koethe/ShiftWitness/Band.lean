/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Ring
public import LeanPool.Koethe.Pencil

/-!
# Backward shifts and exact polynomial mortality

The coefficientwise band identity below retains the pencil's independent formal
variable. It does not deduce polynomial nilpotence from one specialization.
-/

@[expose] public section

noncomputable section

namespace KoetheCounterexample
namespace ShiftWitness

universe u v

/-- The full sequence space on which the backward shifts act. -/
abbrev Space (K : Type v) := ℕ → K

/-- The endomorphism algebra of the sequence space. -/
abbrev End (K : Type v) [Field K] := Module.End K (Space K)

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Backward weighted shifts: composition follows the forward chronological
order of the shared `Pencil.wordProd`. -/
def backShift (v : ℕ → Triple k) (i : Fin 3) : End K where
  toFun u n := algebraMap k K (v n i) * u (n + 1)
  map_add' u w := by ext n; simp [mul_add]
  map_smul' c u := by ext n; simp [mul_left_comm]

@[simp] theorem backShift_apply (v : ℕ → Triple k) (i : Fin 3)
    (u : Space K) (n : ℕ) :
    backShift (K := K) v i u n = algebraMap k K (v n i) * u (n + 1) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact coefficient action of a polynomial matrix supported on one shift band. -/
def HasBand (m : ℕ) (Q : Matrix ι ι (Polynomial (End K)))
    (C : ℕ → Matrix ι ι (Polynomial k)) : Prop :=
  ∀ r c q (u : Space K) n,
    ((Q r c).coeff q) u n = algebraMap k K ((C n r c).coeff q) * u (n + m)

omit [Fintype ι] in
theorem hasBand_one :
    HasBand (k := k) (K := K) (ι := ι) 0 1 (fun _ => 1) := by
  intro r c q u n
  by_cases hrc : r = c
  · subst c
    by_cases hq : q = 0
    · subst q; simp
    · simp [Polynomial.coeff_one, hq]
  · simp [hrc]

omit [DecidableEq ι] in
/-- Multiplication of bands keeps the chronological order and shifts the second
kernel by the width of the first band. -/
theorem HasBand.mul {m l : ℕ}
    {Q T : Matrix ι ι (Polynomial (End K))}
    {C D : ℕ → Matrix ι ι (Polynomial k)}
    (hQ : HasBand m Q C) (hT : HasBand l T D) :
    HasBand (m + l) (Q * T) (fun n => C n * D (n + m)) := by
  unfold HasBand at hQ hT
  intro r c q u n
  simp only [Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul,
    LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, hQ, hT,
    map_sum, map_mul, Finset.sum_mul, Nat.add_assoc, mul_assoc]

theorem linear_combination_apply (v : ℕ → Triple k) (b : Fin 3 → k)
    (u : Space K) (n : ℕ) :
    (∑ i : Fin 3, algebraMap k (End K) (b i) * backShift v i : End K) u n =
      algebraMap k K (∑ i : Fin 3, v n i * b i) * u (n + 1) := by
  simp [LinearMap.sum_apply, Finset.sum_apply, Module.algebraMap_end_apply,
    Algebra.smul_def, Finset.mul_sum, mul_comm, mul_left_comm]

/-- The band kernel of a lifted pencil is its scalar polynomial evaluation at
the edge vector. -/
theorem pencil_hasBand {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) :
    HasBand 1 (P.lift (backShift (K := K) v)) (fun n => P.eval (v n)) := by
  intro r c q u n
  cases q with
  | zero =>
      simpa [Pencil.lift, Pencil.eval] using
        linear_combination_apply v (fun i => P.scalar i r c) u n
  | succ q =>
      cases q with
      | zero =>
          simpa [Pencil.lift, Pencil.eval] using
            linear_combination_apply v (fun i => P.linear i r c) u n
      | succ q =>
          simp [Pencil.lift, Pencil.eval, Polynomial.coeff_X_mul]

@[simp] theorem window_zero {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (n : ℕ) :
    P.window v n 0 = 1 := by simp [Pencil.window]

theorem window_succ {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (n N : ℕ) :
    P.window v n (N + 1) = P.eval (v n) * P.window v (n + 1) N := by
  simp [Pencil.window, Pencil.wordProd, List.ofFn_succ, Nat.add_comm, Nat.add_left_comm]

/-- All coefficients of every power have the window kernel, not just its value
at a chosen rational function. -/
theorem pencil_pow_hasBand {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (N : ℕ) :
    HasBand N ((P.lift (backShift (K := K) v)) ^ N) (fun n => P.window v n N) := by
  induction N with
  | zero => simpa using (hasBand_one (k := k) (K := K) (ι := Fin (d + 1)))
  | succ N ih =>
      simpa only [pow_succ', window_succ, Nat.add_comm 1 N] using (pencil_hasBand P v).mul ih

/-- Uniformly zero windows imply actual nilpotence in the polynomial matrix
ring over the endomorphisms. -/
theorem pencil_nil_of_windows {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k)
    (N : ℕ) (hN : ∀ n, P.window v n N = 0) :
    (P.lift (backShift (K := K) v)) ^ N = 0 := by
  ext r c q u n
  have h := pencil_pow_hasBand (K := K) P v N r c q u n
  simpa [hN] using h

theorem all_pencils_nil (v : ℕ → Triple k) (hv : UniversalMortalSequence k v) :
    ∀ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift (backShift (K := K) v)) := by
  intro d P
  obtain ⟨N, _, hN⟩ := hv.2 d P
  exact ⟨N, pencil_nil_of_windows P v N hN⟩

end ShiftWitness
end KoetheCounterexample

end
