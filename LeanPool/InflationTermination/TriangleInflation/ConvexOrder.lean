/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Rate

/-!
# The convex-order distance rate for the triangle

The sharpening of `rate_triangle` (paper Corollary 6.1) recorded as item B3 of the
`2026-09-13` audit notes: for a law feasible at order `n` the Euclidean distance to the
triangle-compatible set is at most `(1 - ‖P‖₂²)/n`, with no factor counting the three
independent source types.

The argument is the convex-order one. Let `Γ` be a Navascués–Wolfe witness at order `n` and
let `ω` be a deterministic assignment. Shifting the three families of copy indices by a
common triple `a ∈ [n]³` is an element of the symmetry group `S_n³`, and the `n` diagonal
triangles of the shifted assignment are the `n` copied triangles
`Δ_{a_X + ℓ, a_Z + ℓ, a_Y + ℓ}`. Averaging the empirical law of those `n` triangles over the
`n³` shifts returns the empirical law `q_ω` of all `n³` copied triangles, so `q_ω` is a
mixture of `n`-point empirical laws. Cauchy–Schwarz (conditional Jensen for the convex
functional `‖·‖₂²`) therefore bounds `‖q_ω‖₂²` by the mean over shifts of the squared norm
of the `n`-point empirical law, and the symmetry of `Γ` together with the diagonal
prescription `P^{⊗n}` evaluates that mean exactly: the `n` coinciding pairs contribute `1`
each and the `n² - n` distinct pairs contribute `‖P‖₂²` each.

The total-variation corollaries convert with Cauchy–Schwarz on the eight atoms:
`d_TV(P, q_ω) ≤ (√8/2)‖P - q_ω‖₂ ≤ (√8/2)√((1-‖P‖₂²)/n) ≤ √7/(2√n)`, the last step by
`‖P‖₂² ≥ 1/8` for a law on eight atoms.

Nothing here restates or weakens `Rate.lean`; `rate_triangle` is kept as the formalization
of the manuscript's Corollary 6.1 as written, and the theorems below are the improvement.
-/

namespace TriangleInflation

open Finset

noncomputable
section

/-- Total variation distance between two three-bit weight functions: half the `ℓ¹`
distance. -/
def tvDist (P Q : ThreeBit → ℝ) : ℝ := (1 / 2) * ∑ x : ThreeBit, |P x - Q x|

/-! ## Collisions among the diagonal triangles -/

/-- The number of ordered pairs of diagonal triangles that a deterministic assignment reads
alike. This is `n²‖P̂‖₂²` for the empirical law `P̂` of the `n` diagonal triangles. -/
private def diagCount {n : ℕ} (ω : Assign n) : ℝ :=
  ∑ p : Fin n × Fin n,
    if readTriangle p.1 p.1 p.1 ω = readTriangle p.2 p.2 p.2 ω then (1:ℝ) else 0

/-- The mean collision count of the diagonal triangles under a Navascués–Wolfe witness: the
`n` coinciding pairs contribute `1` each and the `n² - n` distinct pairs contribute `‖P‖₂²`
each, by the two-coordinate marginal of the diagonal law `P^{⊗n}`. -/
private theorem expect_diagCount {n : ℕ} {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hΓ : IsLaw Γ) (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P) :
    ∑ ω : Assign n, Γ ω * diagCount ω
      = (n:ℝ) ^ 2 - (1 - sqNorm P) * ((n:ℝ) ^ 2 - (n:ℝ)) := by
  have e : ∀ ω : Assign n, Γ ω * diagCount ω
      = ∑ p : Fin n × Fin n, Γ ω
          * (if readTriangle p.1 p.1 p.1 ω = readTriangle p.2 p.2 p.2 ω then (1:ℝ) else 0) := by
    intro ω
    rw [diagCount, Finset.mul_sum]
  have hp : ∀ p : Fin n × Fin n,
      (∑ ω : Assign n, Γ ω
        * (if readTriangle p.1 p.1 p.1 ω = readTriangle p.2 p.2 p.2 ω then (1:ℝ) else 0))
        = 1 - (1 - sqNorm P) * (if p.1 ≠ p.2 then (1:ℝ) else 0) := by
    intro p
    by_cases h : p.1 = p.2
    · have h1 : ∀ ω : Assign n,
          Γ ω * (if readTriangle p.1 p.1 p.1 ω = readTriangle p.2 p.2 p.2 ω then (1:ℝ) else 0)
            = Γ ω := by
        intro ω
        rw [h, ite_eq_left rfl, mul_one]
      rw [Finset.sum_congr rfl fun ω _ => h1 ω, hΓ.2, ite_eq_right (by simpa using h)]
      ring
    · rw [marg_two hP hsym hdiag h h h, ite_eq_left h]
      ring
  have hconst : (∑ _p : Fin n × Fin n, (1:ℝ)) = (n:ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => hp p, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ne_pair,
    hconst]

/-! ## The common shift of the three copy-index families -/

section Shift

variable {n : ℕ} [NeZero n]

/-- The element of `S_n × S_n × S_n` that shifts the three families of copy indices by the
three components of `a`. -/
private def shiftTriple (a : Cell n) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) × Equiv.Perm (Fin n) :=
  (Equiv.addLeft a.1, Equiv.addLeft a.2.1, Equiv.addLeft a.2.2)

/-- The diagonal triangles of a shifted assignment are the copied triangles on the shifted
diagonal. -/
private theorem readTriangle_shiftTriple (a : Cell n) (l : Fin n) (ω : Assign n) :
    readTriangle l l l (relabel (shiftTriple a) ω)
      = readTriangle (a.1 + l) (a.2.1 + l) (a.2.2 + l) ω := rfl

/-- The empirical law of the `n` diagonal triangles of the assignment shifted by `a`,
carried unnormalized (the masses are counts out of `n`). -/
private def shiftEmp (a : Cell n) (ω : Assign n) (w : ThreeBit) : ℝ :=
  ∑ l : Fin n, if readTriangle l l l (relabel (shiftTriple a) ω) = w then (1:ℝ) else 0

/-- Shifting all three copy indices by a common triple is a bijection of the cube. -/
private theorem sum_shift (l : Fin n) (g : Cell n → ℝ) :
    (∑ a : Cell n, g (a.1 + l, a.2.1 + l, a.2.2 + l)) = ∑ c : Cell n, g c := by
  have h := Equiv.sum_comp
    ((Equiv.addRight l).prodCongr ((Equiv.addRight l).prodCongr (Equiv.addRight l))) g
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- Step (a) of the convex-order argument: averaging the `n`-point empirical law over the
`n³` common shifts returns the empirical law of all `n³` copied triangles. -/
private theorem sum_shiftEmp (ω : Assign n) (w : ThreeBit) :
    (∑ a : Cell n, shiftEmp a ω w) = (n:ℝ) * triCount ω w := by
  have hrw : ∀ a : Cell n, shiftEmp a ω w
      = ∑ l : Fin n,
          if readTriangle (a.1 + l) (a.2.1 + l) (a.2.2 + l) ω = w then (1:ℝ) else 0 := by
    intro a
    rfl
  have hinner : ∀ l : Fin n,
      (∑ a : Cell n,
          if readTriangle (a.1 + l) (a.2.1 + l) (a.2.2 + l) ω = w then (1:ℝ) else 0)
        = triCount ω w :=
    fun l => sum_shift l (fun c => if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0)
  rw [Finset.sum_congr rfl fun a _ => hrw a, Finset.sum_comm,
    Finset.sum_congr rfl fun l _ => hinner l, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Step (c): the squared norm of the shifted `n`-point empirical law counts the collisions
among the diagonal triangles of the shifted assignment. -/
private theorem sum_sq_shiftEmp (a : Cell n) (ω : Assign n) :
    (∑ w : ThreeBit, shiftEmp a ω w ^ 2) = diagCount (relabel (shiftTriple a) ω) := by
  set ω' : Assign n := relabel (shiftTriple a) ω with hω'
  have hsq : ∀ w : ThreeBit, shiftEmp a ω w ^ 2
      = ∑ l : Fin n, ∑ l' : Fin n,
          (if readTriangle l l l ω' = w then (1:ℝ) else 0)
            * (if readTriangle l' l' l' ω' = w then (1:ℝ) else 0) := by
    intro w
    rw [shiftEmp, ← hω', sq, Finset.sum_mul_sum]
  calc ∑ w : ThreeBit, shiftEmp a ω w ^ 2
      = ∑ w : ThreeBit, ∑ l : Fin n, ∑ l' : Fin n,
          (if readTriangle l l l ω' = w then (1:ℝ) else 0)
            * (if readTriangle l' l' l' ω' = w then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun w _ => hsq w
    _ = ∑ l : Fin n, ∑ w : ThreeBit, ∑ l' : Fin n,
          (if readTriangle l l l ω' = w then (1:ℝ) else 0)
            * (if readTriangle l' l' l' ω' = w then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ l : Fin n, ∑ l' : Fin n, ∑ w : ThreeBit,
          (if readTriangle l l l ω' = w then (1:ℝ) else 0)
            * (if readTriangle l' l' l' ω' = w then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l : Fin n, ∑ l' : Fin n,
          (if readTriangle l l l ω' = readTriangle l' l' l' ω' then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ =>
          sum_ind_eq (readTriangle l l l ω') (readTriangle l' l' l' ω')
    _ = diagCount ω' := by rw [diagCount, Fintype.sum_prod_type]

/-- Step (b), Cauchy–Schwarz: the square of the shift average is at most the average of the
squares. -/
private theorem triCount_sq_le_shift (ω : Assign n) (w : ThreeBit) :
    triCount ω w ^ 2 ≤ (n:ℝ) * ∑ a : Cell n, shiftEmp a ω w ^ 2 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hcard : ((Finset.univ : Finset (Cell n)).card : ℝ) = (n:ℝ) ^ 3 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cell n)))
    (f := fun a => shiftEmp a ω w)
  rw [hcard, sum_shiftEmp ω w] at h
  have hsq : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hsq
  have e1 : ((n:ℝ) * triCount ω w) ^ 2 = (n:ℝ) ^ 2 * triCount ω w ^ 2 := by ring
  have e2 : (n:ℝ) ^ 3 * (∑ a : Cell n, shiftEmp a ω w ^ 2)
      = (n:ℝ) ^ 2 * ((n:ℝ) * ∑ a : Cell n, shiftEmp a ω w ^ 2) := by ring
  rw [← e1, ← e2]
  exact h

/-- Steps (a)–(c) combined: the squared norm of the empirical law of all `n³` copied
triangles is dominated by the mean collision count of the shifted diagonals. -/
private theorem sum_triCount_sq_le (ω : Assign n) :
    (∑ w : ThreeBit, triCount ω w ^ 2)
      ≤ (n:ℝ) * ∑ a : Cell n, diagCount (relabel (shiftTriple a) ω) := by
  calc (∑ w : ThreeBit, triCount ω w ^ 2)
      ≤ ∑ w : ThreeBit, (n:ℝ) * ∑ a : Cell n, shiftEmp a ω w ^ 2 :=
        Finset.sum_le_sum fun w _ => triCount_sq_le_shift ω w
    _ = (n:ℝ) * ∑ w : ThreeBit, ∑ a : Cell n, shiftEmp a ω w ^ 2 := by rw [Finset.mul_sum]
    _ = (n:ℝ) * ∑ a : Cell n, ∑ w : ThreeBit, shiftEmp a ω w ^ 2 := by rw [Finset.sum_comm]
    _ = (n:ℝ) * ∑ a : Cell n, diagCount (relabel (shiftTriple a) ω) := by
        rw [Finset.sum_congr rfl fun a _ => sum_sq_shiftEmp a ω]

end Shift

/-! ## The sharp mean squared norm -/

/-- The convex-order replacement for `Rate.lean`'s `expect_sq_le`: the mean squared norm of
the empirical law of a random copied triangle is at most `‖P‖₂² + (1 - ‖P‖₂²)/n`. -/
private theorem expect_sq_le_sharp {n : ℕ} (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hΓ : IsLaw Γ) (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P) :
    ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2)
      ≤ 1 - (1 - sqNorm P) * (1 - 1 / (n:ℝ)) := by
  have : NeZero n := ⟨by omega⟩
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have step1 : ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, triCount ω w ^ 2)
      ≤ (n:ℝ) ^ 4 * ∑ ω : Assign n, Γ ω * diagCount ω := by
    calc ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, triCount ω w ^ 2)
        ≤ ∑ ω : Assign n, Γ ω
            * ((n:ℝ) * ∑ a : Cell n, diagCount (relabel (shiftTriple a) ω)) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (sum_triCount_sq_le ω) (hΓ.1 ω)
      _ = ∑ ω : Assign n, ∑ a : Cell n,
            (n:ℝ) * (Γ ω * diagCount (relabel (shiftTriple a) ω)) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a : Cell n, ∑ ω : Assign n,
            (n:ℝ) * (Γ ω * diagCount (relabel (shiftTriple a) ω)) := Finset.sum_comm
      _ = ∑ _a : Cell n, (n:ℝ) * ∑ ω : Assign n, Γ ω * diagCount ω := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, sym_sum hsym (shiftTriple a) diagCount]
      _ = (n:ℝ) ^ 4 * ∑ ω : Assign n, Γ ω * diagCount ω := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hq : ∀ ω : Assign n, (∑ w : ThreeBit, qLaw n ω w ^ 2)
      = (∑ w : ThreeBit, triCount ω w ^ 2) / (n:ℝ) ^ 6 := by
    intro ω
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [qLaw, div_pow]
    ring
  have hΓsum : ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2)
      = (∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, triCount ω w ^ 2)) / (n:ℝ) ^ 6 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [hq ω, mul_div_assoc]
  rw [hΓsum, div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) ^ 6)]
  refine step1.trans ?_
  rw [expect_diagCount hP hΓ hsym hdiag]
  have hfin : (1 - (1 - sqNorm P) * (1 - 1 / (n:ℝ))) * (n:ℝ) ^ 6
      = (n:ℝ) ^ 4 * ((n:ℝ) ^ 2 - (1 - sqNorm P) * ((n:ℝ) ^ 2 - (n:ℝ))) := by
    field_simp
  rw [hfin]

/-! ## The sharp distance rate -/

/-- Audit item B3: the convex-order sharpening of paper Corollary 6.1 for the binary
triangle. If `P` is feasible at order `n` then some triangle-compatible law `Qc` satisfies
`‖P - Qc‖₂² ≤ (1 - ‖P‖₂²)/n`. The constant carries no factor counting the three
independent source types, so it improves `rate_triangle`, whose constant
`1 - (1 - 1/n)³` is asymptotically `3/n`. -/
theorem rate_triangle_sharp (n : ℕ) (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible n P) :
    ∃ Qc : ThreeBit → ℝ, IsLaw Qc ∧ TriangleCompatible Qc ∧
      sqNorm (fun x => P x - Qc x) ≤ (1 - sqNorm P) / n := by
  obtain ⟨Γ, hΓ, hsym, hdiag⟩ := h
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hB : ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w) = sqNorm P := by
    have e : ∀ ω : Assign n, Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w)
        = ∑ w : ThreeBit, P w * (Γ ω * qLaw n ω w) := by
      intro ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have e2 : ∀ w : ThreeBit, (∑ ω : Assign n, P w * (Γ ω * qLaw n ω w)) = P w * P w := by
      intro w
      rw [← Finset.mul_sum, expect_qLaw hn hP hsym hdiag w]
    rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm,
      Finset.sum_congr rfl fun w _ => e2 w]
    simp [sqNorm, sq]
  have key : ∑ ω : Assign n, Γ ω * sqNorm (fun x => P x - qLaw n ω x)
      ≤ (1 - sqNorm P) / (n:ℝ) := by
    have step1 : ∀ ω : Assign n, sqNorm (fun x => P x - qLaw n ω x)
        = sqNorm P - 2 * (∑ w : ThreeBit, P w * qLaw n ω w)
          + (∑ w : ThreeBit, qLaw n ω w ^ 2) := by
      intro ω
      simp only [sqNorm]
      have e : ∀ w : ThreeBit, (P w - qLaw n ω w) ^ 2
          = P w ^ 2 - 2 * (P w * qLaw n ω w) + qLaw n ω w ^ 2 := fun w => by ring
      rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have e1 : ∀ ω : Assign n, Γ ω * sqNorm (fun x => P x - qLaw n ω x)
        = Γ ω * sqNorm P - 2 * (Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w))
          + Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2) := by
      intro ω
      rw [step1 ω]
      ring
    rw [Finset.sum_congr rfl fun ω _ => e1 ω, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hΓ.2, one_mul, hB]
    have hC := expect_sq_le_sharp hn hP hΓ hsym hdiag
    have hring : (1:ℝ) - (1 - sqNorm P) * (1 - 1 / (n:ℝ)) - sqNorm P
        = (1 - sqNorm P) / (n:ℝ) := by
      field_simp
      ring
    linarith
  obtain ⟨ω, hω⟩ := exists_le_of_weighted hΓ.1 hΓ.2
    (fun ω => sqNorm (fun x => P x - qLaw n ω x)) _ key
  exact ⟨qLaw n ω, qLaw_isLaw hn ω, qLaw_compatible hn ω, hω⟩

/-! ## Total variation -/

/-- Cauchy–Schwarz on the eight atoms: the `ℓ¹` norm is at most `√8` times the `ℓ²` norm. -/
private theorem l1_le_sqrt_eight_l2 (v : ThreeBit → ℝ) :
    (∑ x : ThreeBit, |v x|) ≤ Real.sqrt 8 * Real.sqrt (∑ x : ThreeBit, v x ^ 2) := by
  have hcard : ((Finset.univ : Finset ThreeBit).card : ℝ) = 8 := by
    rw [Finset.card_univ]
    norm_num
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ThreeBit))
    (f := fun x => |v x|)
  rw [hcard] at h
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (Finset.univ : Finset ThreeBit)) => sq_abs (v x)] at h
  have hnn : (0:ℝ) ≤ ∑ x : ThreeBit, |v x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc (∑ x : ThreeBit, |v x|) = Real.sqrt ((∑ x : ThreeBit, |v x|) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (8 * ∑ x : ThreeBit, v x ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt 8 * Real.sqrt (∑ x : ThreeBit, v x ^ 2) :=
        Real.sqrt_mul (by norm_num) _

/-- A law on the eight atoms has squared Euclidean norm at least `1/8`. -/
private theorem sqNorm_ge_eighth {P : ThreeBit → ℝ} (hP : IsLaw P) : 1 / 8 ≤ sqNorm P := by
  have hcard : ((Finset.univ : Finset ThreeBit).card : ℝ) = 8 := by
    rw [Finset.card_univ]
    norm_num
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ThreeBit)) (f := P)
  rw [hcard, hP.2, one_pow] at h
  have hs : (∑ x : ThreeBit, P x ^ 2) = sqNorm P := rfl
  rw [hs] at h
  linarith

/-- The total-variation form of `rate_triangle_sharp`: a law feasible at order `n` is within
`(√8/2)√((1 - ‖P‖₂²)/n)` in total variation of a triangle-compatible law. -/
theorem tv_le_of_nwFeasible (n : ℕ) (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible n P) :
    ∃ Qc : ThreeBit → ℝ, IsLaw Qc ∧ TriangleCompatible Qc ∧
      tvDist P Qc ≤ Real.sqrt 8 / 2 * Real.sqrt ((1 - sqNorm P) / n) := by
  obtain ⟨Qc, hQ, hcomp, hd⟩ := rate_triangle_sharp n hn hP h
  refine ⟨Qc, hQ, hcomp, ?_⟩
  have h1 := l1_le_sqrt_eight_l2 (fun x => P x - Qc x)
  have h2 : Real.sqrt (sqNorm (fun x => P x - Qc x))
      ≤ Real.sqrt ((1 - sqNorm P) / (n:ℝ)) := Real.sqrt_le_sqrt hd
  have h3 : (∑ x : ThreeBit, |P x - Qc x|)
      ≤ Real.sqrt 8 * Real.sqrt ((1 - sqNorm P) / (n:ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 8))
  calc tvDist P Qc = (1 / 2) * ∑ x : ThreeBit, |P x - Qc x| := rfl
    _ ≤ (1 / 2) * (Real.sqrt 8 * Real.sqrt ((1 - sqNorm P) / (n:ℝ))) := by linarith
    _ = Real.sqrt 8 / 2 * Real.sqrt ((1 - sqNorm P) / (n:ℝ)) := by ring

/-- The source-count-free rate in its cleanest form: a law feasible at order `n` is within
`√7/(2√n)` in total variation of a triangle-compatible law, using `‖P‖₂² ≥ 1/8`. -/
theorem tv_le_sqrt_seven (n : ℕ) (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible n P) :
    ∃ Qc : ThreeBit → ℝ, IsLaw Qc ∧ TriangleCompatible Qc ∧
      tvDist P Qc ≤ Real.sqrt 7 / (2 * Real.sqrt n) := by
  obtain ⟨Qc, hQ, hcomp, hd⟩ := tv_le_of_nwFeasible n hn hP h
  refine ⟨Qc, hQ, hcomp, ?_⟩
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnum : (1 - sqNorm P) ≤ 7 / 8 := by
    have := sqNorm_ge_eighth hP
    linarith
  have hinv : (0:ℝ) ≤ ((n:ℝ))⁻¹ := by positivity
  have h8 : (1 - sqNorm P) / (n:ℝ) ≤ (7 / 8) / (n:ℝ) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum hinv
  have hmono : Real.sqrt ((1 - sqNorm P) / (n:ℝ)) ≤ Real.sqrt ((7 / 8) / (n:ℝ)) :=
    Real.sqrt_le_sqrt h8
  have hkey : Real.sqrt 8 / 2 * Real.sqrt ((7 / 8) / (n:ℝ))
      = Real.sqrt 7 / (2 * Real.sqrt n) := by
    have hs8 : Real.sqrt 8 ≠ 0 := by positivity
    have hsn : Real.sqrt (n:ℝ) ≠ 0 := by
      have : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
      exact ne_of_gt this
    rw [show ((7:ℝ) / 8) / (n:ℝ) = 7 / (8 * (n:ℝ)) by ring,
      Real.sqrt_div (by norm_num : (0:ℝ) ≤ 7), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
    field_simp
  calc tvDist P Qc ≤ Real.sqrt 8 / 2 * Real.sqrt ((1 - sqNorm P) / (n:ℝ)) := hd
    _ ≤ Real.sqrt 8 / 2 * Real.sqrt ((7 / 8) / (n:ℝ)) := by
        have : (0:ℝ) ≤ Real.sqrt 8 / 2 := by positivity
        exact mul_le_mul_of_nonneg_left hmono this
    _ = Real.sqrt 7 / (2 * Real.sqrt n) := hkey

end

end TriangleInflation
