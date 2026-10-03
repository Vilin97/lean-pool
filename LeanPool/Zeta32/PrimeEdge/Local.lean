/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family

/-! the proof notes, §1 (Corollary 2): the local functional on a disc, in a
finite rational form.

For `0 ≤ b < p` put `t = p u - b` (the variable `u` is written `X`). For `f = A / D_{5n}` the
dissected function `g_b(u) = (t f)(p u - b)` is
`g_b = p^{-|near_b|} · dissectNum(u) / (nearProd(u) · farProd(u))`, where
* `nearSet n p b = {m = (j - b)/p : j ∈ [1, 5n], j ≡ b (mod p)}` (near poles `u = -m`),
* `nearProd = ∏_{m ∈ nearSet} (u + m)`,
* `farProd = ∏_{j ∈ [1,5n], j ≢ b} ((j - b) + p u)` (constant term a `p`-unit),
* `dissectNum = (t · A)(p u - b)`.
`seriesPart` is the power series `dissectNum / farProd ∈ ℚ[[u]]` truncated to degree `< 10n + 2`.

The local functional (the `X`-free part of `V_Y`, Corollary 2) on `S / ∏_{m ∈ M} (u + m)`:
`V(u^e) = e B_{e-1} + 2 s B_e` (`B = bernoulli'`, `B_1 = +1/2`), and
`V((u+m)^{-1}) = 2 H_m^{(3)} - 2 s H_m^{(2)}` (the `-2Y` part is dropped; `Y ∈ p³ ℤ_p[X]`).
`s = r p` gives `V_Y` without `Y`; `s = 0` gives `V⁰`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

noncomputable section

/-- Near poles on the disc `b`. -/
def nearSet (n p b : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (5 * n)).filter (fun j => j % p = b)).image (fun j => (j - b) / p)

/-- Denominator factors in the residue class selected by `b`. -/
def nearProd (n p b : ℕ) : ℚ[X] := ∏ m ∈ nearSet n p b, (X + C (m : ℚ))

/-- Transformed denominator factors outside the residue class selected by `b`. -/
def farProd (n p b : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.Icc 1 (5 * n)).filter (fun j => j % p ≠ b), (C ((j : ℚ) - b) + C (p : ℚ) * X)

/-- `(t · A)(p u - b)` as a polynomial in `u`. -/
def dissectNum (p b : ℕ) (A : ℚ[X]) : ℚ[X] := (X * A).comp (C (p : ℚ) * X - C (b : ℚ))

/-- Truncation order of the far-pole expansions. -/
def truncOrder (n : ℕ) : ℕ := 10 * n + 2

/-- `dissectNum / farProd`, expanded in `ℚ[[u]]` and truncated to degree `< truncOrder n`. -/
def seriesPart (n p b : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc (truncOrder n)
    ((dissectNum p b A : PowerSeries ℚ) * (farProd n p b : PowerSeries ℚ)⁻¹)

/-- `V(u^e) = e B_{e-1} + 2 s B_e`. -/
@[expose]
def locMoment (s : ℚ) (e : ℕ) : ℚ := (e : ℚ) * bernoulli' (e - 1) + 2 * s * bernoulli' e

/-- Linear extension of the local moments to a polynomial. -/
@[expose]
def locPoly (s : ℚ) (P : ℚ[X]) : ℚ := P.sum fun e a => a * locMoment s e

/-- `V((u+m)^{-1})` without the `-2Y` part. -/
@[expose]
def locPole (s : ℚ) (m : ℕ) : ℚ := 2 * Zeta32.H 3 m - 2 * s * Zeta32.H 2 m

/-- The local functional on `S / ∏_{m ∈ M} (u + m)` (polynomial part plus Lagrange residues). -/
@[expose]
def locValue (s : ℚ) (S : ℚ[X]) (M : Finset ℕ) : ℚ :=
  locPoly s (S /ₘ ∏ m ∈ M, (X + C (m : ℚ))) +
    ∑ m ∈ M, S.eval (-(m : ℚ)) / (∏ m' ∈ M.erase m, ((m' : ℚ) - m)) * locPole s m

lemma locPoly_add_linear (s : ℚ) (P Q : ℚ[X]) :
    locPoly s (P + Q) = locPoly s P + locPoly s Q := by
  unfold locPoly
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma locPoly_C_mul_linear (s c : ℚ) (P : ℚ[X]) : locPoly s (C c * P) = c * locPoly s P := by
  unfold locPoly
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum,
    Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma locPoly_zero_linear (s : ℚ) : locPoly s 0 = 0 := by simp [locPoly]

lemma locValue_add_linear (s : ℚ) (S T : ℚ[X]) (M : Finset ℕ) :
    locValue s (S + T) M = locValue s S M + locValue s T M := by
  unfold locValue
  rw [add_divByMonic, locPoly_add_linear]
  simp only [eval_add, add_div, add_mul, Finset.sum_add_distrib]
  ring

lemma locValue_C_mul_linear (s c : ℚ) (S : ℚ[X]) (M : Finset ℕ) :
    locValue s (C c * S) M = c * locValue s S M := by
  unfold locValue
  rw [← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul, locPoly_C_mul_linear,
    mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_smul, smul_eq_mul]; ring

lemma locValue_zero_linear (s : ℚ) (M : Finset ℕ) : locValue s 0 M = 0 := by
  simpa using locValue_C_mul_linear s 0 0 M

lemma locValue_sum_linear {ι : Type*} (s : ℚ) (t : Finset ι) (S : ι → ℚ[X]) (M : Finset ℕ) :
    locValue s (∑ i ∈ t, S i) M = ∑ i ∈ t, locValue s (S i) M := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [locValue_zero_linear]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, locValue_add_linear, ih]


/-- `V_Y(g_b)` without the `Y` part, with far poles truncated: `p^{-|near|} V(seriesPart /
nearProd)`. -/
def discLocal (r : ℚ) (n p b : ℕ) (A : ℚ[X]) : ℚ :=
  (p : ℚ) ^ (-((nearSet n p b).card : ℤ)) *
    locValue (r * p) (seriesPart n p b A) (nearSet n p b)

/-- `V⁰(u^e r_type)` for the three class types of §6:
zero `r_0 = u/((u+1)…(u+4))`, low `r_L = u³/((u+1)…(u+4))`, high `r_H = u³/((u+1)(u+2)(u+3))`. -/
@[expose]
def blockMoment (p b e : ℕ) : ℚ :=
  if b = 0 then locValue 0 (X ^ (e + 1)) {1, 2, 3, 4}
  else if b + 5 ≤ p then locValue 0 (X ^ (e + 3)) {1, 2, 3, 4}
  else locValue 0 (X ^ (e + 3)) {1, 2, 3}

end

end Zeta32.PrimeEdge

end
