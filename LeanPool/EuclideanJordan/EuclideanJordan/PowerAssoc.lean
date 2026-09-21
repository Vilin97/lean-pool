/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.Power


/-!
# Albert's theorem: power associativity

**`jpow_mul_jpow`: `x^{m+1} ∘ x^{n+1} = x^{m+n+2}` in any real commutative Jordan algebra.**
Unconditional; closure is Lean's three core axioms.

This is the gateway to the Jordan spectral theorem: the spectral resolution of `x` lives in
the subalgebra `ℝ[x]`, and that argument cannot begin until `ℝ[x]` is associative. We are aware
of no formalization of Albert's theorem in any proof assistant, though we have not searched
them systematically, and Mathlib has nothing between `IsCommJordan` and this.

## The proof

Write `cm x i j w` for the commutator `[L_{x^{i+1}}, L_{x^{j+1}}]` applied to `w`. The whole
theorem is `cm x i j w = 0`, since `EuclideanJordan/Power.lean`'s `jpow_mul_jpow_of_commuteAt`
    already
turns commutation into the product law.

The engine is `cm_cyclic`: for `i + j = N` (and given the product law at level `N`), the
fully linearised Jordan identity `four_lin2_apply` collapses to

  `cm x j (i+1) w + cm x 0 (N+1) w + cm x i (j+1) w = 0`.

Now fix `N` and `w` and look at the "antidiagonal" `d k := cm x k (N+1-k) w`. The identity
says exactly `d j + d 0 + d i = 0` whenever `i + j = N`, and antisymmetry says
`d k = − d (N+1−k)`. Together these force

  `d (k+1) = d k + d 0`,  hence  `d k = (k+1) · d 0`,

and the wrap-around `d (N+1) = − d 0` then gives `(N+3) · d 0 = 0`. In a real vector space
that means `d 0 = 0`, so the whole antidiagonal vanishes and the induction advances.

★ **`(N+3)` is where the characteristic hypothesis bites *hardest*.** Albert's theorem needs
**every** positive integer invertible — it would fail in characteristic `p` for any `p ≤ N+3`
— whereas the Peirce layer needs only `2`. So `Module ℝ J` is load-bearing everywhere in this
development, and unboundedly so here.
## Relation to Mathlib

The Mathlib-facing shape is `instance : PNatPowAssoc J` — the class
(`Mathlib/Algebra/Group/PNatPowAssoc.lean`, `ppow_add : x ^ (k + n) = x ^ k * x ^ n`) already
exists with two users. Supplying the `Pow J ℕ+` instance and transporting `jpow_mul_jpow`
across it is the upstream contribution. **Not done here** — that translation is unwritten, and
this file should not be read as providing it.
-/

namespace EuclideanJordan

section Albert

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

/-- The commutator `[L_{x^{i+1}}, L_{x^{j+1}}]` applied to `w`. Albert's theorem is that this
vanishes identically. -/
def cm (x : J) (i j : ℕ) (w : J) : J :=
  jpow x i * (jpow x j * w) - jpow x j * (jpow x i * w)

omit [IsCommJordan J] [Module ℝ J] in
theorem cm_antisymm (x : J) (i j : ℕ) (w : J) : cm x i j w = - cm x j i w := by simp [cm]

omit [IsCommJordan J] [Module ℝ J] in
theorem cm_self (x : J) (i : ℕ) (w : J) : cm x i i w = 0 := by simp [cm]

omit [IsCommJordan J] [Module ℝ J] in
/-- `cm x 0 i ≡ 0` is precisely `CommuteAt x i`. -/
theorem commuteAt_of_cm {x : J} {i : ℕ} (h : ∀ w, cm x 0 i w = 0) : CommuteAt x i := by
  intro w
  have hw := h w
  rw [cm, jpow_zero] at hw
  exact sub_eq_zero.mp hw

/-- **The engine.** The fully linearised Jordan identity, instantiated at `(x, x^{i+1},
x^{j+1})` and evaluated at `w`, with the middle product already reduced by the level-`N`
product law. This is the relation that ties the antidiagonal together. -/
theorem cm_cyclic (x : J) (i j : ℕ) (hij : jpow x i * jpow x j = jpow x (i + j + 1)) (w : J) :
    cm x j (i + 1) w + cm x 0 (i + j + 1) w + cm x i (j + 1) w = 0 := by
  have h := four_lin2_apply (jpow x 0) (jpow x i) (jpow x j) w
  simp only [jpow_zero] at h
  rw [show x * jpow x i = jpow x (i + 1) from rfl] at h
  rw [show x * jpow x j = jpow x (j + 1) from rfl] at h
  rw [hij] at h
  refine nsmul_eq_zero_iff' (n := 4) (by norm_num) ?_
  rw [← h]
  simp only [cm, jpow_zero]

/-- **Albert's theorem, commutator form.** All multiplication operators of powers of a single
element commute. The induction is on the total degree `N`; at each level the antidiagonal
argument of the module docstring forces the new commutators to vanish. -/
theorem cm_eq_zero (x : J) (N : ℕ) : ∀ i j : ℕ, i + j ≤ N → ∀ w : J, cm x i j w = 0 := by
  induction N with
  | zero =>
      intro i j hij w
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
      exact cm_self x 0 w
  | succ N ih =>
      have hA : ∀ i j : ℕ, i + j ≤ N → jpow x i * jpow x j = jpow x (i + j + 1) := fun i j hij =>
        jpow_mul_jpow_of_commuteAt (commuteAt_of_cm (fun w => ih 0 i (by omega) w)) j
      intro i j hij w
      rcases Nat.lt_or_ge (i + j) (N + 1) with hlt | hge
      · exact ih i j (by omega) w
      · have hsum : i + j = N + 1 := by omega
        set c : J := cm x 0 (N + 1) w with hc
        have key : ∀ k : ℕ, k ≤ N + 1 → ∀ l : ℕ, k + l = N + 1 → cm x k l w = (k + 1) • c := by
          intro k
          induction k with
          | zero =>
              intro _ l hl
              obtain rfl : l = N + 1 := by omega
              simp [hc]
          | succ k ihk =>
              intro hk l hl
              have hcyc := cm_cyclic x l k (hA l k (by omega)) w
              rw [show l + k + 1 = N + 1 from by omega] at hcyc
              rw [ihk (by omega) (l + 1) (by omega), cm_antisymm x l (k + 1) w, ← hc] at hcyc
              rw [(add_neg_eq_zero.mp hcyc).symm, ← succ_nsmul]
        have hlast : cm x (N + 1) 0 w = (N + 2) • c := key (N + 1) le_rfl 0 (by omega)
        have hneg : cm x (N + 1) 0 w = - c := by rw [cm_antisymm x (N + 1) 0 w, ← hc]
        have hzero : (N + 3) • c = 0 := by
          have h2 : (N + 2) • c = -c := by rw [← hlast, hneg]
          rw [show N + 3 = (N + 2) + 1 from rfl, succ_nsmul, h2]
          exact neg_add_cancel c
        rw [key i (by omega) j (by omega), nsmul_eq_zero_iff' (n := N + 3) (by omega) hzero,
          smul_zero]

/-- `L_{x^{m+1}}` commutes with `L_x`, for every `m` — the gap this arc's wall certificate
priced as open. -/
theorem commuteAt_all (x : J) (m : ℕ) : CommuteAt x m :=
  commuteAt_of_cm (fun w => cm_eq_zero x m 0 m (by omega) w)

/-- **POWER ASSOCIATIVITY (Albert's theorem).** `x^{m+1} ∘ x^{n+1} = x^{m+n+2}` in any real
commutative Jordan algebra. No formal reality, no finite dimension, no unit, no inner
product — only the Jordan identity and the real scalars. -/
theorem jpow_mul_jpow (x : J) (m n : ℕ) : jpow x m * jpow x n = jpow x (m + n + 1) :=
  jpow_mul_jpow_of_commuteAt (commuteAt_all x m) n

/-- The operator form: the multiplication operators of powers of one element mutually
commute. This, not the product law, is what a spectral argument consumes. -/
theorem opCommute_jpow (x : J) (i j : ℕ) (w : J) :
    jpow x i * (jpow x j * w) = jpow x j * (jpow x i * w) :=
  sub_eq_zero.mp (cm_eq_zero x (i + j) i j le_rfl w)

end Albert

end EuclideanJordan
