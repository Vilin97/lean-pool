/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorIdeal
import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic

/-!
# Tensor commutativity and the right-slot ideal

The tensor of fragments commutes up to the block-swap relabel,
so the closure rows of `x ⊗ z` are closure rows of `z` — the
right-slot half of the monoidal ideal follows from the left-slot
machinery through the swap.
-/

namespace RS

/-- The block swap of interleaved boundaries. -/
noncomputable def tensorSwapEquiv (s t u v : ℕ) :
    Fin ((u + s) + (v + t)) ≃ Fin ((s + u) + (t + v)) :=
  (interleaveEquiv u v s t).symm.trans
    ((_root_.Equiv.sumComm (Fin (u + v)) (Fin (s + t))).trans
      (interleaveEquiv s t u v))

/-- **Tensor commutativity**: the tensor is the swapped tensor,
relabelled by the block swap. -/
noncomputable def tensorFragmentComm {s t u v : ℕ}
    (X : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v))) :
    (tensorFragment X z).Equiv
      ((tensorFragment z X).relabel (tensorSwapEquiv s t u v)) :=
  (Fragment.Equiv.relabelCongr
      (Fragment.disjUnionComm X z) (interleaveEquiv s t u v)).trans
    ((Fragment.Equiv.relabelTrans (z.disjUnion X)
        (_root_.Equiv.sumComm (Fin (u + v)) (Fin (s + t)))
        (interleaveEquiv s t u v)).trans
      ((Fragment.Equiv.relabelEq (z.disjUnion X)
          (show (_root_.Equiv.sumComm (Fin (u + v))
              (Fin (s + t))).trans (interleaveEquiv s t u v) =
            (interleaveEquiv u v s t).trans
              (tensorSwapEquiv s t u v) from
          _root_.Equiv.ext fun x => by
            simp [tensorSwapEquiv])).trans
        (Fragment.Equiv.relabelTrans (z.disjUnion X)
          (interleaveEquiv u v s t)
          (tensorSwapEquiv s t u v)).symm))

/-- The closure rows of a tensor are closure rows of the second
factor. -/
theorem connectionPairing_tensor_right (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} (X : Fragment (Fin (s + t)))
    (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    connectionPairing f ((s + u) + (t + v))
        (tensorFragment X z) G =
      connectionPairing f (u + v) z
        (partialClose X
          (G.relabel (tensorSwapEquiv s t u v).symm)) := by
  rw [show connectionPairing f ((s + u) + (t + v))
      (tensorFragment X z) G =
      connectionPairing f ((s + u) + (t + v))
        ((tensorFragment z X).relabel
          (tensorSwapEquiv s t u v)) G from
    hf _ _ (pairCloseCongr (tensorFragmentComm X z)
      (Fragment.Equiv.refl G))]
  rw [show connectionPairing f ((s + u) + (t + v))
      ((tensorFragment z X).relabel
        (tensorSwapEquiv s t u v)) G =
      connectionPairing f ((u + s) + (v + t))
        (tensorFragment z X)
        (G.relabel (tensorSwapEquiv s t u v).symm) from
    hf _ _ (pairCloseRelabel (tensorSwapEquiv s t u v)
      (tensorFragment z X) G)]
  exact connectionPairing_tensor f hf z X
    (G.relabel (tensorSwapEquiv s t u v).symm)

/-- The connection row of a single-fragment tensor, linearized in
the second slot. -/
theorem connectionMap_tensor_right_single
    (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} (X : Fragment (Fin (s + t)))
    (y : Fragment (Fin (u + v)) →₀ ℂ)
    (K : Fragment (Fin ((s + u) + (t + v)))) :
    connectionMap f ((s + u) + (t + v))
        (tensorFinsupp s t u v (Finsupp.single X 1) y) K =
      connectionMap f (u + v) y
        (partialClose X
          (K.relabel (tensorSwapEquiv s t u v).symm)) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | add y z hy hz =>
    rw [map_add, map_add]
    show connectionMap f ((s + u) + (t + v)) _ K +
      connectionMap f ((s + u) + (t + v)) _ K = _
    rw [hy, hz, map_add]
    rfl
  | single z c =>
    rw [tensorFinsupp_single, one_mul, connectionMap_single,
      connectionMap_single,
      connectionPairing_tensor_right f hf]

/-- **The right-slot monoidal ideal**: anything tensored with a
kernel element stays in the kernel. -/
theorem tensorFinsupp_ker_right (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} (x : Fragment (Fin (s + t)) →₀ ℂ)
    {y : Fragment (Fin (u + v)) →₀ ℂ}
    (hy : y ∈ LinearMap.ker (connectionMap f (u + v))) :
    tensorFinsupp s t u v x y ∈
      LinearMap.ker (connectionMap f ((s + u) + (t + v))) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ h₁ h₂
  | single X c =>
    have h1 : tensorFinsupp s t u v (Finsupp.single X c) y =
        c • tensorFinsupp s t u v (Finsupp.single X 1) y := by
      rw [show (Finsupp.single X c :
          Fragment (Fin (s + t)) →₀ ℂ) =
          c • Finsupp.single X 1 by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
        map_smul, LinearMap.smul_apply]
    rw [h1]
    refine Submodule.smul_mem _ c ?_
    rw [LinearMap.mem_ker] at hy ⊢
    funext K
    rw [connectionMap_tensor_right_single f hf X y K, hy]
    rfl

end RS
