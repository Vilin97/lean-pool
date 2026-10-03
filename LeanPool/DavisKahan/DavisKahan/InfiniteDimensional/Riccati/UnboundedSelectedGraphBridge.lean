/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.UnboundedPublic
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedGraphAcute

/-!
# Rectangular extraction from an ambient selected graph

Continuation constructs graph operators as ambient endomorphisms of the Hilbert
direct sum.  Strong unbounded Riccati theory instead uses a rectangular map
from the first coordinate to the second.  This leaf identifies those two graph
languages at the zero coordinate graph.

The result is deliberately independent of any particular continuation theorem.
Once an ambient selected endpoint has been proved angular over the zero graph,
this module extracts its rectangular angular part and proves that the resulting
unbounded block graph is exactly the ambient graph subspace.  Domain
preservation and reduction of the closed block operator remain separate,
genuinely unbounded obligations.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The Hilbert direct sum on which an ambient selected graph operator acts. -/
abbrev DirectSum (E0 E1 : Type*) := WithLp 2 (E0 × E1)

/-- The rectangular first-to-second block of an ambient direct-sum operator. -/
noncomputable def rectangularAngularPart
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1) : E0 →L[ℂ] E1 :=
  WithLp.sndL 2 ℂ E0 E1 ∘L Y ∘L
    blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The rectangular angular part reads off the second component of `Y` on the first block. -/
@[simp]
theorem rectangularAngularPart_apply
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1) (x : E0) :
    rectangularAngularPart Y x =
      WithLp.snd
        (Y (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) x)) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The unbounded and bounded block-graph definitions use the same direct-sum
range construction. -/
theorem unboundedBlockGraph_eq_blockGraph (X : E0 →L[ℂ] E1) :
    unboundedBlockGraph X = blockGraph X :=
  rfl

/-- An ambient angular operator over the zero coordinate graph is exactly the
ambient block angular operator induced by its rectangular part. -/
theorem ambientAngular_eq_blockAngularOperator
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1)
    (hY : IsAngularOperator
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y) :
    Y = blockAngularOperator (rectangularAngularPart Y) := by
  change IsAngularOperator (blockGraph (0 : E0 →L[ℂ] E1)) Y at hY
  ext z
  have hYP :
      Y ((blockGraph (0 : E0 →L[ℂ] E1)).starProjection z) = Y z := by
    have h := ContinuousLinearMap.ext_iff.mp hY.1 z
    change Y ((blockGraph (0 : E0 →L[ℂ] E1)).starProjection z) = Y z at h
    exact h
  have hPY :
      (blockGraph (0 : E0 →L[ℂ] E1)).starProjection (Y z) = 0 := by
    have h := ContinuousLinearMap.ext_iff.mp hY.2 z
    change (blockGraph (0 : E0 →L[ℂ] E1)).starProjection (Y z) = 0 at h
    exact h
  rw [zeroGraph_starProjection_apply] at hYP hPY
  have hfst : WithLp.fst (Y z) = 0 := by
    have h := congrArg WithLp.fst hPY
    simpa using h
  have hyreconstruct :=
    blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (Y z)
  rw [hfst, map_zero, zero_add] at hyreconstruct
  have hsnd :
      WithLp.snd
          (Y (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
            (WithLp.fst z))) =
        WithLp.snd (Y z) := by
    exact congrArg WithLp.snd hYP
  calc
    Y z = blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.snd (Y z)) := hyreconstruct.symm
    _ = blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.snd
          (Y (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
            (WithLp.fst z)))) := by rw [hsnd]
    _ = blockAngularOperator (rectangularAngularPart Y) z := by
      rfl

/-- The ambient graph subspace of an angular operator over the zero graph is
exactly the rectangular block graph extracted from that operator. -/
theorem graphSubspace_eq_unboundedBlockGraph_rectangularAngularPart
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1)
    (hY : IsAngularOperator
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y) :
    graphSubspace (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y =
      unboundedBlockGraph (rectangularAngularPart Y) := by
  change graphSubspace (blockGraph (0 : E0 →L[ℂ] E1)) Y =
    blockGraph (rectangularAngularPart Y)
  have hY' : IsAngularOperator (blockGraph (0 : E0 →L[ℂ] E1)) Y := hY
  rw [graphSubspace_eq_range _ hY']
  rw [ambientAngular_eq_blockAngularOperator Y hY]
  exact (blockGraph_eq_range_zeroGraph_angularParam
    (rectangularAngularPart Y)).symm

/-- Build the canonical partial-map continuation-to-Riccati handoff from an
ambient angular graph.  The domain and reduction hypotheses are expressed over
the raw block core, so this endpoint does not reconstruct local closed-operator
bundles. -/
noncomputable def ContractiveReducingGraphSelection.ofAmbientAngularGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1)
    (hY : IsAngularOperator
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y)
    (hdom : PreservesRiccatiDomains H (rectangularAngularPart Y))
    (hnorm : ‖rectangularAngularPart Y‖ < 1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H)
      (graphSubspace (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y)) :
    ContractiveReducingGraphSelection H where
  X := rectangularAngularPart Y
  preservesDomains := hdom
  norm_lt_one := hnorm
  reduces := by
    simpa only [graphSubspace_eq_unboundedBlockGraph_rectangularAngularPart Y hY]
      using hred

/-- Canonical strong-solution conclusion from an ambient selected graph and
its domain-aware partial-map reduction data. -/
theorem exists_strongRiccati_solution_of_ambientAngularGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (Y : DirectSum E0 E1 →L[ℂ] DirectSum E0 E1)
    (hY : IsAngularOperator
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y)
    (hdom : PreservesRiccatiDomains H (rectangularAngularPart Y))
    (hnorm : ‖rectangularAngularPart Y‖ < 1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H)
      (graphSubspace (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) Y)) :
    ∃ X : E0 →L[ℂ] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperatorCore H)
        (unboundedBlockGraph X) := by
  exact (ContractiveReducingGraphSelection.ofAmbientAngularGraph
    H Y hY hdom hnorm hred).exists_strongRiccati_solution

end DavisKahanExt
end TauCeti
