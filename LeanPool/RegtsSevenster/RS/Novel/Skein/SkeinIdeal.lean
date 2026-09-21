/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomSpaces

/-!
# The composition ideal

Bilinear composition on the free modules of fragments, and the
first half of the ideal lemma (accompanying paper, Lemma 3.3(a)):
composing a
kernel element with any fragment on the right stays in the
kernel, because every closure row of the composite is a closure
row of the original — the rotation of closures moves the
composed factor into the test fragment.
-/

noncomputable section

namespace RS

/-- Bilinear composition on the free modules of fragments. -/
noncomputable def composeFinsupp (m n p : ℕ) :
    (Fragment (Fin (m + n)) →₀ ℂ) →ₗ[ℂ]
      (Fragment (Fin (n + p)) →₀ ℂ) →ₗ[ℂ]
        (Fragment (Fin (m + p)) →₀ ℂ) :=
  Finsupp.lift _ ℂ _ (fun F =>
    Finsupp.lift _ ℂ _ (fun G =>
      Finsupp.single (F.compose G) (1 : ℂ)))

/-- Composition of weighted single fragments. -/
theorem composeFinsupp_single (m n p : ℕ)
    (F : Fragment (Fin (m + n))) (c : ℂ)
    (G : Fragment (Fin (n + p))) (d : ℂ) :
    composeFinsupp m n p (Finsupp.single F c)
        (Finsupp.single G d) =
      Finsupp.single (F.compose G) (c * d) := by
  unfold composeFinsupp
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp),
    LinearMap.smul_apply, Finsupp.lift_apply,
    Finsupp.sum_single_index (by simp), Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]

/-- The connection row of a weighted single fragment. -/
theorem connectionMap_single (f : ClosedFragment → ℂ) (t : ℕ)
    (X : Fragment (Fin t)) (c : ℂ) (G : Fragment (Fin t)) :
    connectionMap f t (Finsupp.single X c) G =
      c * connectionPairing f t X G := by
  unfold connectionMap
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  rfl

/-- **Rotation of connection rows** (accompanying paper,
Lemma 3.3(a), right): for an isomorphism-invariant parameter, the
closure row of a right-composite is a closure row of the
original. -/
theorem connectionPairing_compose_right
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {m n p : ℕ} (F : Fragment (Fin (m + n)))
    (H : Fragment (Fin (n + p))) (K : Fragment (Fin (m + p))) :
    connectionPairing f (m + p) (F.compose H) K =
      connectionPairing f (m + n) F
        (K.compose (H.relabel (transposeEquiv n p))) :=
  hf _ _ (pairCloseComposeRotate F H K)

/-- The closure row of a right-composite, linearized: each row of
`x ∘ H` is a row of `x` at a rotated test fragment. -/
theorem connectionMap_compose_single
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {m n p : ℕ} (x : Fragment (Fin (m + n)) →₀ ℂ)
    (H : Fragment (Fin (n + p))) (K : Fragment (Fin (m + p))) :
    connectionMap f (m + p)
        (composeFinsupp m n p x (Finsupp.single H 1)) K =
      connectionMap f (m + n) x
        (K.compose (H.relabel (transposeEquiv n p))) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, map_zero]
    rfl
  | add y z hy hz =>
    rw [map_add, LinearMap.add_apply, map_add]
    show connectionMap f (m + p) _ K + connectionMap f (m + p) _ K
      = _
    rw [hy, hz, map_add]
    rfl
  | single F c =>
    rw [composeFinsupp_single, mul_one, connectionMap_single,
      connectionMap_single,
      connectionPairing_compose_right f hf]

/-- **The right ideal property** (accompanying paper, Lemma 3.3(a),
right): a kernel element composed with any single fragment on the
right stays in the kernel. -/
theorem composeFinsupp_single_ker (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {m n p : ℕ} {x : Fragment (Fin (m + n)) →₀ ℂ}
    (hx : x ∈ LinearMap.ker (connectionMap f (m + n)))
    (H : Fragment (Fin (n + p))) :
    composeFinsupp m n p x (Finsupp.single H 1) ∈
      LinearMap.ker (connectionMap f (m + p)) := by
  rw [LinearMap.mem_ker] at hx ⊢
  funext K
  rw [connectionMap_compose_single f hf x H K, hx]
  rfl

/-- **The right ideal property, bilinear form**: a kernel element
composed with anything on the right stays in the kernel. -/
theorem composeFinsupp_ker_left (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {m n p : ℕ} {x : Fragment (Fin (m + n)) →₀ ℂ}
    (hx : x ∈ LinearMap.ker (connectionMap f (m + n)))
    (y : Fragment (Fin (n + p)) →₀ ℂ) :
    composeFinsupp m n p x y ∈
      LinearMap.ker (connectionMap f (m + p)) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | single H c =>
    have h1 : composeFinsupp m n p x (Finsupp.single H c) =
        c • composeFinsupp m n p x (Finsupp.single H 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem _ c
      (composeFinsupp_single_ker f hf hx H)

end RS
