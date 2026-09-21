/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotateLeft
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal

/-!
# The composition ideal, left half

The mirror of `SkeinIdeal.lean`: composing a kernel element with
any fragment on the *left* stays in the kernel, because every
closure row of `w ∘ x` is a closure row of `x` — the mirror
rotation moves the left factor into the test fragment.  Together
with `composeFinsupp_ker_left` this makes the pairing kernel a
two-sided ideal (accompanying paper, Lemma 3.3(a)), so composition
descends to the Hom spaces.
-/

namespace RS

/-- **Rotation of connection rows, left** (accompanying paper,
Lemma 3.3(a), left): for an isomorphism-invariant parameter, the
closure row of a left-composite is a closure row of the
original. -/
theorem connectionPairing_compose_left
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u : ℕ} (W : Fragment (Fin (s + t)))
    (F : Fragment (Fin (t + u))) (K : Fragment (Fin (s + u))) :
    connectionPairing f (s + u) (W.compose F) K =
      connectionPairing f (t + u) F
        ((W.relabel (transposeEquiv s t)).compose K) :=
  hf _ _ (pairCloseComposeRotateLeft W F K)

/-- The closure row of a left-composite, linearized: each row of
`W ∘ y` is a row of `y` at a rotated test fragment. -/
theorem connectionMap_compose_left_single
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u : ℕ} (W : Fragment (Fin (s + t)))
    (y : Fragment (Fin (t + u)) →₀ ℂ)
    (K : Fragment (Fin (s + u))) :
    connectionMap f (s + u)
        (composeFinsupp s t u (Finsupp.single W 1) y) K =
      connectionMap f (t + u) y
        ((W.relabel (transposeEquiv s t)).compose K) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | add y z hy hz =>
    rw [map_add, map_add]
    show connectionMap f (s + u) _ K +
      connectionMap f (s + u) _ K = _
    rw [hy, hz, map_add]
    rfl
  | single F c =>
    rw [composeFinsupp_single, one_mul, connectionMap_single,
      connectionMap_single,
      connectionPairing_compose_left f hf]

/-- A kernel element composed with a single fragment on the left
stays in the kernel. -/
theorem composeFinsupp_single_ker_left
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u : ℕ} (W : Fragment (Fin (s + t)))
    {y : Fragment (Fin (t + u)) →₀ ℂ}
    (hy : y ∈ LinearMap.ker (connectionMap f (t + u))) :
    composeFinsupp s t u (Finsupp.single W 1) y ∈
      LinearMap.ker (connectionMap f (s + u)) := by
  rw [LinearMap.mem_ker] at hy ⊢
  funext K
  rw [connectionMap_compose_left_single f hf W y K, hy]
  rfl

/-- **The left ideal property** (accompanying paper, Lemma 3.3(a),
left): anything composed with a kernel element on the left stays
in the kernel. -/
theorem composeFinsupp_ker_right
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u : ℕ} (x : Fragment (Fin (s + t)) →₀ ℂ)
    {y : Fragment (Fin (t + u)) →₀ ℂ}
    (hy : y ∈ LinearMap.ker (connectionMap f (t + u))) :
    composeFinsupp s t u x y ∈
      LinearMap.ker (connectionMap f (s + u)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ h₁ h₂
  | single W c =>
    have h1 : composeFinsupp s t u (Finsupp.single W c) y =
        c • composeFinsupp s t u (Finsupp.single W 1) y := by
      rw [show (Finsupp.single W c : Fragment (Fin (s + t)) →₀ ℂ)
          = c • Finsupp.single W 1 by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
        map_smul, LinearMap.smul_apply]
    rw [h1]
    exact Submodule.smul_mem _ c
      (composeFinsupp_single_ker_left f hf W hy)

end RS
