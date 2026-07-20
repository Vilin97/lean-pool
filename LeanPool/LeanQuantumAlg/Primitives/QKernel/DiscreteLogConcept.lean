/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Common
/-!
# The discrete-logarithm concept class and its secret-homogeneity

The genuine heart of Liu, Arunachalam, Temme (2021) Theorem 1. On a finite cyclic group
`G` with generator `g`, the half-interval discrete-log labeling `f_s` is *secret-homogeneous*:
its uniform learning accuracy is independent of the secret `s`. This is exactly why a learner
for one secret breaks every secret (and hence the discrete-log problem). Pure finite-group
theory; no Haar / complexity assumptions.
-/

@[expose] public section

namespace QuantumAlg

open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] [IsCyclic G]
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The discrete-log isomorphism induced by the generator `g`
(`Multiplicative (ZMod (Nat.card G)) ≃* G`, sending `ofAdd 1 ↦ g`). -/
noncomputable def dlogEquiv : Multiplicative (ZMod (Nat.card G)) ≃* G :=
  zmodMulEquivOfGenerator hg rfl

/-- Discrete logarithm base `g`. -/
noncomputable def dlog (x : G) : ZMod (Nat.card G) :=
  Multiplicative.toAdd ((dlogEquiv g hg).symm x)

/-- `g` raised to a `ZMod (Nat.card G)` exponent. -/
noncomputable def gpow (t : ZMod (Nat.card G)) : G :=
  dlogEquiv g hg (Multiplicative.ofAdd t)

omit [Fintype G] [IsCyclic G] in
theorem dlog_mul (x y : G) : dlog g hg (x * y) = dlog g hg x + dlog g hg y := by
  simp only [dlog, map_mul]
  rfl

omit [Fintype G] [IsCyclic G] in
theorem dlog_gpow (t : ZMod (Nat.card G)) : dlog g hg (gpow g hg t) = t := by
  simp only [dlog, gpow, MulEquiv.symm_apply_apply]
  rfl

omit [Fintype G] [IsCyclic G] in
theorem dlog_mul_gpow (x : G) (t : ZMod (Nat.card G)) :
    dlog g hg (x * gpow g hg t) = dlog g hg x + t := by
  rw [dlog_mul, dlog_gpow]

omit [Fintype G] [IsCyclic G] in
theorem gpow_zero : gpow g hg 0 = 1 := by
  unfold gpow
  simp

/-- The half-interval discrete-log concept `f_s`: label `x` by whether `dlog x - s` lies in
the lower half of `ZMod (Nat.card G)`. -/
noncomputable def dlogConcept (s : ZMod (Nat.card G)) (x : G) : Bool :=
  decide ((dlog g hg x - s).val < Nat.card G / 2)

omit [Fintype G] [IsCyclic G] in
/-- **Shift-equivariance** (workhorse): translating the data by `gᵗ` shifts the secret by `t`. -/
theorem dlogConcept_shift (s t : ZMod (Nat.card G)) (x : G) :
    dlogConcept g hg s (x * gpow g hg t) = dlogConcept g hg (s - t) x := by
  unfold dlogConcept
  rw [dlog_mul_gpow, show dlog g hg x + t - s = dlog g hg x - (s - t) from by ring]

omit [Fintype G] [IsCyclic G] in
/-- **Reduction corollary**: shifting by `g^{s-1}` maps the secret-`s` concept to the fixed
secret-`1` concept. -/
theorem dlogConcept_reduction (s : ZMod (Nat.card G)) (y : G) :
    dlogConcept g hg s (y * gpow g hg (s - 1)) = dlogConcept g hg 1 y := by
  rw [dlogConcept_shift, show s - (s - 1) = 1 from by ring]

/-- Uniform (counting) accuracy of a Boolean predictor `p` against the concept `f_s`. -/
noncomputable def acc (p : G → Bool) (s : ZMod (Nat.card G)) : ℝ :=
  ((Finset.univ.filter (fun x => p x = dlogConcept g hg s x)).card : ℝ) / (Nat.card G : ℝ)

omit [IsCyclic G] in
/-- **Accuracy-level secret-homogeneity** (load-bearing): the accuracy of any predictor on
the secret-`s` concept equals the accuracy of the shifted predictor on the fixed secret-`1`
concept. So breaking any secret is equivalent to breaking the single fixed concept. -/
theorem acc_shift (p : G → Bool) (s : ZMod (Nat.card G)) :
    acc g hg (fun y => p (y * gpow g hg (s - 1))) 1 = acc g hg p s := by
  have key : (Finset.univ.filter
        (fun y => p (y * gpow g hg (s - 1)) = dlogConcept g hg 1 y)).card
      = (Finset.univ.filter (fun x => p x = dlogConcept g hg s x)).card := by
    apply Finset.card_equiv (Equiv.mulRight (gpow g hg (s - 1)))
    intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [dlogConcept_reduction]
  simp only [acc]
  rw [key]

end QuantumAlg
