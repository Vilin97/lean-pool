/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCore

/-!
# Bounded Riccati graph reduction

This leaf module completes the geometric upgrade from bounded graph invariance
to graph reduction.  The block operator determined by self-adjoint diagonal
blocks and mutually adjoint off-diagonal blocks is symmetric.  Consequently,
invariance of an angular graph already implies invariance of its orthogonal
complement.  Combining this observation with the algebraic result in
`BoundedCore` identifies reducing graph subspaces exactly with bounded
solutions of the operator Riccati equation.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Coordinate action of the bounded block operator on an arbitrary direct-sum
vector. -/
@[simp]
theorem blockOperator_apply
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : WithLp 2 (E0 × E1)) :
    blockOperator H z =
      WithLp.toLp 2
        (H.A0 (WithLp.fst z) + H.B01 (WithLp.snd z),
          H.B10 (WithLp.fst z) + H.A1 (WithLp.snd z)) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The bounded block operator associated with self-adjoint diagonal blocks
and mutually adjoint off-diagonal blocks is symmetric. -/
theorem blockOperator_isSelfAdjoint
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    (blockOperator H).IsSymmetric := by
  intro x y
  let x0 : E0 := WithLp.fst x
  let x1 : E1 := WithLp.snd x
  let y0 : E0 := WithLp.fst y
  let y1 : E1 := WithLp.snd y
  have h00 := H.selfAdjoint0 x0 y0
  change ⟪H.A0 x0, y0⟫_𝕜 = ⟪x0, H.A0 y0⟫_𝕜 at h00
  have h11 := H.selfAdjoint1 x1 y1
  change ⟪H.A1 x1, y1⟫_𝕜 = ⟪x1, H.A1 y1⟫_𝕜 at h11
  have h01 : ⟪H.B01 x1, y0⟫_𝕜 = ⟪x1, H.B10 y0⟫_𝕜 :=
    H.offDiagonalAdjoint y0 x1
  have h10 : ⟪H.B10 x0, y1⟫_𝕜 = ⟪x0, H.B01 y1⟫_𝕜 := by
    calc
      ⟪H.B10 x0, y1⟫_𝕜 =
          (starRingEnd 𝕜) ⟪y1, H.B10 x0⟫_𝕜 :=
        (inner_conj_symm (H.B10 x0) y1).symm
      _ = (starRingEnd 𝕜) ⟪H.B01 y1, x0⟫_𝕜 := by
        exact congrArg (starRingEnd 𝕜) (H.offDiagonalAdjoint x0 y1).symm
      _ = ⟪x0, H.B01 y1⟫_𝕜 :=
        inner_conj_symm x0 (H.B01 y1)
  change
    ⟪blockOperator H x, y⟫_𝕜 =
      ⟪x, blockOperator H y⟫_𝕜
  simp only [blockOperator_apply, WithLp.prod_inner_apply,
    inner_add_left, inner_add_right]
  change
    (⟪H.A0 x0, y0⟫_𝕜 + ⟪H.B01 x1, y0⟫_𝕜) +
        (⟪H.B10 x0, y1⟫_𝕜 + ⟪H.A1 x1, y1⟫_𝕜) =
      (⟪x0, H.A0 y0⟫_𝕜 + ⟪x0, H.B01 y1⟫_𝕜) +
        (⟪x1, H.B10 y0⟫_𝕜 + ⟪x1, H.A1 y1⟫_𝕜)
  calc
    (⟪H.A0 x0, y0⟫_𝕜 + ⟪H.B01 x1, y0⟫_𝕜) +
          (⟪H.B10 x0, y1⟫_𝕜 + ⟪H.A1 x1, y1⟫_𝕜) =
        (⟪x0, H.A0 y0⟫_𝕜 + ⟪x1, H.B10 y0⟫_𝕜) +
          (⟪x0, H.B01 y1⟫_𝕜 + ⟪x1, H.A1 y1⟫_𝕜) := by
      exact congrArg₂ (fun a b : 𝕜 => a + b)
        (congrArg₂ (fun a b : 𝕜 => a + b) h00 h01)
        (congrArg₂ (fun a b : 𝕜 => a + b) h10 h11)
    _ =
        (⟪x0, H.A0 y0⟫_𝕜 + ⟪x0, H.B01 y1⟫_𝕜) +
          (⟪x1, H.B10 y0⟫_𝕜 + ⟪x1, H.A1 y1⟫_𝕜) := by
      abel

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A bounded angular graph reduces the self-adjoint block operator exactly
when the angular operator solves the bounded Riccati equation. -/
theorem blockGraph_reduces_iff_solvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    ContinuousLinearMap.Reduces (blockOperator H) (blockGraph X) ↔ SolvesRiccati H X := by
  constructor
  · intro hred
    exact (blockGraph_invariant_iff_solvesRiccati H X).1 hred.1
  · intro hX
    apply ContinuousLinearMap.IsSymmetric.reduces_of_invariant (blockOperator_isSelfAdjoint H)
    exact (blockGraph_invariant_iff_solvesRiccati H X).2 hX

end DavisKahanExt
end TauCeti
