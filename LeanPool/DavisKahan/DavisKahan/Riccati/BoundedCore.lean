/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedBasic

/-!
# Bounded graph invariance and the operator Riccati equation

This leaf module proves the algebraic foundation for the bounded Riccati
program.  For the self-adjoint block data used by Davis--Kahan, invariance of
the graph of an angular operator is equivalent to vanishing of its Riccati
defect.  The later reduction, existence, uniqueness, and block-diagonalization
steps can build on this result without repeating direct-sum coordinate algebra.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The standard graph vector with first coordinate `u` and second coordinate
`X u`, represented in the Hilbert direct sum. -/
noncomputable def boundedBlockGraphVector (X : E0 →L[𝕜] E1) (u : E0) :
    WithLp 2 (E0 × E1) :=
  WithLp.toLp 2 (u, X u)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The block graph vector, unfolded to its two coordinates. -/
@[simp]
theorem boundedBlockGraphVector_apply
    (X : E0 →L[𝕜] E1) (u : E0) :
    boundedBlockGraphVector X u = WithLp.toLp 2 (u, X u) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Coordinate action of the bounded block operator. -/
@[simp]
theorem blockOperator_toLp_apply
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (u : E0) (v : E1) :
    blockOperator H (WithLp.toLp 2 (u, v)) =
      WithLp.toLp 2 (H.A0 u + H.B01 v, H.B10 u + H.A1 v) := by
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A direct-sum vector belongs to the graph exactly when its second coordinate
is the angular operator applied to its first coordinate. -/
theorem toLp_mem_blockGraph_iff
    (X : E0 →L[𝕜] E1) (u : E0) (v : E1) :
    WithLp.toLp 2 (u, v) ∈ blockGraph X ↔ v = X u := by
  constructor
  · intro hmem
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    change WithLp.toLp 2 (w, X w) = WithLp.toLp 2 (u, v) at hw
    have hp : (w, X w) = (u, v) :=
      (WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.injective hw
    have hfst : w = u := congrArg Prod.fst hp
    have hsnd : X w = v := congrArg Prod.snd hp
    calc
      v = X w := hsnd.symm
      _ = X u := congrArg X hfst
  · intro hv
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    change WithLp.toLp 2 (u, X u) = WithLp.toLp 2 (u, v)
    rw [hv]

/-- Invariance of the bounded graph under the block operator. -/
def BoundedBlockGraphInvariant
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ z ∈ blockGraph X, blockOperator H z ∈ blockGraph X

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Pointwise form of the bounded Riccati equation. -/
theorem solvesRiccati_iff_pointwise
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    SolvesRiccati H X ↔
      ∀ u : E0,
        H.B10 u + H.A1 (X u) = X (H.A0 u + H.B01 (X u)) := by
  constructor
  · intro hX u
    have hu : riccatiDefect H X u = 0 := by
      rw [hX]
      rfl
    change
      H.A1 (X u) - X (H.A0 u) - X (H.B01 (X u)) + H.B10 u = 0 at hu
    rw [map_add]
    calc
      H.B10 u + H.A1 (X u) =
          (H.A1 (X u) - X (H.A0 u) - X (H.B01 (X u)) + H.B10 u) +
            (X (H.A0 u) + X (H.B01 (X u))) := by
              abel
      _ = 0 + (X (H.A0 u) + X (H.B01 (X u))) := by rw [hu]
      _ = X (H.A0 u) + X (H.B01 (X u)) := zero_add _
  · intro hpoint
    apply ContinuousLinearMap.ext
    intro u
    change
      H.A1 (X u) - X (H.A0 u) - X (H.B01 (X u)) + H.B10 u = 0
    have hu := hpoint u
    rw [map_add] at hu
    calc
      H.A1 (X u) - X (H.A0 u) - X (H.B01 (X u)) + H.B10 u =
          (H.B10 u + H.A1 (X u)) -
            (X (H.A0 u) + X (H.B01 (X u))) := by
              abel
      _ = 0 := sub_eq_zero.mpr hu

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A bounded block graph is invariant exactly when its angular operator solves
the operator Riccati equation. -/
theorem blockGraph_invariant_iff_solvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    BoundedBlockGraphInvariant H X ↔ SolvesRiccati H X := by
  rw [solvesRiccati_iff_pointwise]
  constructor
  · intro hinv u
    have hgraph : boundedBlockGraphVector X u ∈ blockGraph X := by
      apply (toLp_mem_blockGraph_iff X u (X u)).2
      rfl
    have hout := hinv (boundedBlockGraphVector X u) hgraph
    change
      WithLp.toLp 2
        (H.A0 u + H.B01 (X u), H.B10 u + H.A1 (X u)) ∈
          blockGraph X at hout
    exact (toLp_mem_blockGraph_iff X
      (H.A0 u + H.B01 (X u)) (H.B10 u + H.A1 (X u))).1 hout
  · intro hpoint z hz
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
    subst z
    change
      blockOperator H (WithLp.toLp 2 (u, X u)) ∈ blockGraph X
    rw [blockOperator_toLp_apply]
    apply (toLp_mem_blockGraph_iff X
      (H.A0 u + H.B01 (X u)) (H.B10 u + H.A1 (X u))).2
    exact hpoint u

end DavisKahanExt
end TauCeti
