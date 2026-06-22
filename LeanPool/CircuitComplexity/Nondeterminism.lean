/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Nondeterminism.Defs
import LeanPool.CircuitComplexity.Internal.Nondeterminism
import LeanPool.CircuitComplexity.Shannon

/-! # Nondeterministic Circuit Complexity Bounds

Upper bounds on the circuit complexity of existentially quantified
Boolean functions.

Given `f : BitString (k + m) → Bool`, the existential quantification
`existQuantify f : BitString m → Bool` is defined by
`g(y) = ∃ x ∈ {0,1}^k, f(x ++ y)`.  This models a nondeterministic
circuit that guesses the first `k` input bits.

## Definitions (from `Circ.Nondeterminism.Defs`)

* `existQuantify` — existential quantification over first `k` inputs
* `forallQuantify` — universal quantification over first `k` inputs
* `restrictFirst` — fix the first input to a constant

## Main results

* `restrict_size_complexity_le` — hardwiring one input does not increase
  circuit complexity.

* `or_size_complexity_le` — the OR of two functions has complexity at most
  the sum of their complexities plus one.

* `existQuantify_complexity_le` — **naive upper bound**:
  `sizeComplexity(existQuantify f) ≤ 2^k · (sizeComplexity(f) + 1)`.
  Proof by induction on `k` using `existQuantify_succ`, restriction,
  and OR combination.

* `existQuantify_complexity_shannon` — **Shannon upper bound**:
  `sizeComplexity(existQuantify f) ≤ 18 · 2^m / m`.
  Unconditional (the quantified function has only `m` inputs).

* `existQuantify_complexity_min` — the minimum of the two bounds above.

The naive bound is tighter when `k` is small and `f` has low complexity;
the Shannon bound wins when `k` is large, regardless of `f`'s complexity.
-/

namespace CircuitComplexity


variable {k m : Nat}

/-- `k + m ≥ 1` whenever `m ≥ 1`.  Enables `sizeComplexity` on
    `BitString (k + m)`. -/
instance instNeZeroAddLeft [NeZero m] : NeZero (k + m) :=
  ⟨by have := NeZero.ne m; omega⟩

/-! ## Building-block bounds -/

/-- Hardwiring one input does not increase fan-in-2 AND/OR circuit complexity.

    Given a circuit of size `s` computing `f`, we modify each gate in-place
    (via `restrictGateP`): any input that referenced the hardwired variable
    is redirected using the gate's negation flags to produce the correct
    constant, without adding extra gates.  See `Circ.Internal.Nondeterminism`
    for the construction. -/
theorem restrict_size_complexity_le [CompleteBasis Basis.andOr2] [NeZero m]
    (f : BitString ((k + 1) + m) → Bool) (b : Bool) :
    Circuit.sizeComplexity Basis.andOr2 (restrictFirst f b) ≤
      Circuit.sizeComplexity Basis.andOr2 f := by
  obtain ⟨G, c, hsize, heval⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) f
  calc Circuit.sizeComplexity Basis.andOr2 (restrictFirst f b)
      ≤ (restrictCircuit (k := k) b c).size :=
        Circuit.size_complexity_le _ _ (restrictCircuit_eval b c f heval)
    _ = c.size := rfl
    _ = Circuit.sizeComplexity Basis.andOr2 f := hsize

/-- The OR of two Boolean functions has circuit complexity bounded by the
    sum of their individual complexities plus one (for the OR output gate).

    Uses `ShannonUpper.binopCircuit` to compose two circuits side-by-side. -/
theorem or_size_complexity_le [CompleteBasis Basis.andOr2] [NeZero N]
    (g₁ g₂ : BitString N → Bool) :
    Circuit.sizeComplexity Basis.andOr2 (fun x => g₁ x || g₂ x) ≤
      Circuit.sizeComplexity Basis.andOr2 g₁ +
      Circuit.sizeComplexity Basis.andOr2 g₂ + 1 := by
  obtain ⟨G₁, c₁, hsize₁, heval₁⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) g₁
  obtain ⟨G₂, c₂, hsize₂, heval₂⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) g₂
  let c := ShannonUpper.binopCircuit AONOp.or c₁ c₂
  have hcorrect : (fun x => (c.eval x) 0) = fun x => g₁ x || g₂ x :=
    ShannonUpper.binopCircuit_or_correct c₁ c₂ g₁ g₂ heval₁ heval₂
  calc Circuit.sizeComplexity Basis.andOr2 (fun x => g₁ x || g₂ x)
      ≤ c.size := Circuit.size_complexity_le c _ hcorrect
    _ = (G₁ + G₂ + 2) + 1 := rfl
    _ = Circuit.sizeComplexity Basis.andOr2 g₁ +
        Circuit.sizeComplexity Basis.andOr2 g₂ + 1 := by
        rw [← hsize₁, ← hsize₂]
        unfold Circuit.size
        omega

/-! ## Transport lemma for the base case -/

/-- Circuit complexity is invariant under propositional equality of input
    dimension. -/
private theorem size_complexity_cast [CompleteBasis B] [NeZero n] [NeZero n']
    (h : n = n') (f : BitString n → Bool) :
    Circuit.sizeComplexity B (h ▸ f : BitString n' → Bool) =
      Circuit.sizeComplexity B f := by
  subst h; rfl

/-- Transport of a function: `(h ▸ f) y = f (h.symm ▸ y)`. -/
private theorem cast_fun_apply {n n' : Nat}
    (h : n = n') (f : BitString n → Bool) (y : BitString n') :
    (h ▸ f) y = f (h.symm ▸ y) := by
  subst h; rfl

/-- Transport of a `Fin`-indexed function:
    `(h ▸ f) i = f (Fin.cast h.symm i)`. -/
private theorem cast_fun_fin_apply {n n' : Nat}
    (h : n = n') (f : Fin n → Bool) (i : Fin n') :
    (h ▸ f) i = f (Fin.cast h.symm i) := by
  subst h; rfl

/-! ## Main results -/

/-- **Naive upper bound for existential quantification.**

    If `f : BitString (k + m) → Bool` has fan-in-2 AND/OR circuit complexity
    `s`, then `existQuantify f : BitString m → Bool` has circuit complexity
    at most `2^k · (s + 1)`.

    **Proof.**  By induction on `k`.  We prove the tighter statement
    `sizeComplexity + 1 ≤ 2^k · (s + 1)`, which absorbs the OR-gate
    overhead at each step.

    * **Base case** (`k = 0`):  `existQuantify` is the identity (up to a
      transport along `0 + m = m`), so complexity is preserved.

    * **Inductive step** (`k → k + 1`):  `existQuantify (k+1) f` factors
      as `(existQuantify k (f|₀)) OR (existQuantify k (f|₁))` via
      `existQuantify_succ`.  Restriction preserves complexity; the OR adds
      one gate; and the inductive hypothesis bounds each branch by
      `2^k · (s + 1) − 1`.  After the "+1 trick":
      `(size₁ + size₂ + 1) + 1 = (size₁ + 1) + (size₂ + 1) ≤ 2^(k+1) · (s + 1)`. -/
theorem existQuantify_complexity_le [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1) := by
  suffices h : Circuit.sizeComplexity Basis.andOr2 (existQuantify f) + 1 ≤
      2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1) by omega
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    suffices hle : Circuit.sizeComplexity Basis.andOr2 (existQuantify (k := 0) f) ≤
        Circuit.sizeComplexity Basis.andOr2 f by omega
    suffices heq : existQuantify (k := 0) f = (Nat.zero_add m) ▸ f by
      rw [heq, size_complexity_cast]
    funext y
    unfold existQuantify
    simp only [Unique.exists_iff, Bool.decide_eq_true]
    rw [cast_fun_apply]
    congr 1
    funext i
    simp only [Fin.append, Fin.addCases, not_lt_zero, ↓reduceDIte, Nat.add_zero, Fin.subNat_zero,
      eq_rec_constant]
    rw [cast_fun_fin_apply]
  | succ k ih =>
    have hfun : existQuantify (k := k + 1) f = fun y =>
        (existQuantify (k := k) (restrictFirst f false) y ||
         existQuantify (k := k) (restrictFirst f true) y) :=
      funext (existQuantify_succ f)
    rw [hfun]
    set g₁ := existQuantify (k := k) (restrictFirst f false)
    set g₂ := existQuantify (k := k) (restrictFirst f true)
    set s := Circuit.sizeComplexity Basis.andOr2 f
    have hor := or_size_complexity_le g₁ g₂
    have h₁ : Circuit.sizeComplexity Basis.andOr2 g₁ + 1 ≤ 2 ^ k * (s + 1) :=
      le_trans (ih (restrictFirst f false))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (restrict_size_complexity_le f false) 1))
    have h₂ : Circuit.sizeComplexity Basis.andOr2 g₂ + 1 ≤ 2 ^ k * (s + 1) :=
      le_trans (ih (restrictFirst f true))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (restrict_size_complexity_le f true) 1))
    calc Circuit.sizeComplexity Basis.andOr2 (fun y => g₁ y || g₂ y) + 1
        ≤ (Circuit.sizeComplexity Basis.andOr2 g₁ +
           Circuit.sizeComplexity Basis.andOr2 g₂ + 1) + 1 :=
          Nat.add_le_add_right hor 1
      _ = (Circuit.sizeComplexity Basis.andOr2 g₁ + 1) +
          (Circuit.sizeComplexity Basis.andOr2 g₂ + 1) := by omega
      _ ≤ 2 ^ k * (s + 1) + 2 ^ k * (s + 1) := Nat.add_le_add h₁ h₂
      _ = 2 ^ (k + 1) * (s + 1) := by ring

/-- **Shannon upper bound for existential quantification.**

    The quantified function `existQuantify f : BitString m → Bool` is just
    an `m`-input Boolean function, so the Shannon upper bound applies
    unconditionally.  Even if `f` has exponential circuit complexity,
    `existQuantify f` has complexity at most `O(2^m / m)`, which decreases
    exponentially as more variables are quantified away. -/
theorem existQuantify_complexity_shannon [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] (hm : 16 ≤ m) :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤ 18 * 2 ^ m / m :=
  shannon_upper_bound m hm (existQuantify f)

/-- **Combined upper bound**: the minimum of the naive and Shannon bounds.

    When `sizeComplexity(f) ≈ 2^(k+m)/2`, the Shannon bound
    `18 · 2^m / m` is exponentially better than the naive
    `2^k · (s + 1)`, especially for large `k`. -/
theorem existQuantify_complexity_min [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] (hm : 16 ≤ m) :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      min (2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1)) (18 * 2 ^ m / m) :=
  le_min (existQuantify_complexity_le f) (existQuantify_complexity_shannon f hm)

end CircuitComplexity
