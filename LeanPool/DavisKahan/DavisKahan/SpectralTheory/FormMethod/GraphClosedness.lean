/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.TraceKernelModel
import Mathlib.Tactic

/-!
# Closedness of the transported fourth-order graph

A concrete Sobolev realization usually equips the maximal fourth-order domain
with a graph Hilbert norm.  In that norm the map

`u ↦ (u, u'''')`

is bounded below, hence anti-Lipschitz.  Its range is therefore closed.  This
file proves that this closed range is exactly the ambient graph of the
transported fourth derivative constructed in `TraceKernelModel`.

The result turns a graph-norm estimate on the free trace kernel into the closed
graph field required by `DavisKahanExt.PartialMap`.
-/

open Set
open scoped InnerProductSpace NNReal

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

namespace FourthOrderTraceModel

/-- Graph embedding of the free trace kernel into the product Hilbert space. -/
noncomputable def freeGraphMap
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeSubspace →L[𝕜] H × H :=
  D.freeEmbed.prod D.freeFourth

omit [CompleteSpace H] [CompleteSpace V] in
/-- The free graph map, unfolded. -/
@[simp] theorem freeGraphMap_apply
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeGraphMap x = (D.freeEmbed x, D.freeFourth x) := rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- The ambient image of the inverse range equivalence is the original domain
vector. -/
@[simp] theorem freeEmbed_freeAmbientInverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeAmbientDomain) :
    D.freeEmbed (D.freeAmbientInverse x) = (x : H) := by
  have h := D.freeRangeEquiv.apply_symm_apply x
  exact congrArg Subtype.val h

omit [CompleteSpace H] [CompleteSpace V] in
/-- The fourth derivative transported to the ambient domain agrees with the
free fourth derivative of the recovered graph-space vector. -/
@[simp] theorem freeFourthAmbient_inverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeAmbientDomain) :
    D.freeFourthAmbient x = D.freeFourth (D.freeAmbientInverse x) := by
  rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- The graph-space range and the ambient partial-operator graph are the same
subset of `H × H`. -/
theorem range_freeGraphMap_eq_ambientGraph
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    Set.range D.freeGraphMap =
      Set.range (fun x : D.freeAmbientDomain =>
        ((x : H), D.freeFourthAmbient x)) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    let y : D.freeAmbientDomain :=
      ⟨D.freeEmbed x, LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩
    refine ⟨y, ?_⟩
    ext
    · rfl
    · exact D.freeFourthAmbient_freeEmbed x
  · rintro ⟨x, rfl⟩
    refine ⟨D.freeAmbientInverse x, ?_⟩
    ext
    · exact D.freeEmbed_freeAmbientInverse x
    · rfl

omit [CompleteSpace H] in
/-- An anti-Lipschitz graph embedding has closed ambient operator graph. -/
theorem isClosed_ambientGraph_of_antilipschitz
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    {K : NNReal}
    (hanti : AntilipschitzWith K D.freeGraphMap) :
    IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x)) := by
  rw [← D.range_freeGraphMap_eq_ambientGraph]
  exact hanti.isClosed_range D.freeGraphMap.uniformContinuous

omit [CompleteSpace H] [CompleteSpace V] in
/-- A lower graph-norm estimate gives the anti-Lipschitz hypothesis needed for
closedness. -/
theorem freeGraphMap_antilipschitz_of_bound
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : D.freeSubspace, c * ‖x‖ ≤ ‖D.freeGraphMap x‖) :
    AntilipschitzWith (Real.toNNReal c)⁻¹ D.freeGraphMap := by
  refine ContinuousLinearMap.antilipschitz_of_bound D.freeGraphMap ?_
  intro x
  have hcoe : (((Real.toNNReal c)⁻¹ : NNReal) : ℝ) = c⁻¹ := by
    rw [NNReal.coe_inv, Real.coe_toNNReal c hc.le]
  rw [hcoe, le_inv_mul_iff₀ hc]
  exact hbound x

omit [CompleteSpace H] in
/-- A positive lower graph-norm estimate proves the transported operator graph
closed. -/
theorem isClosed_ambientGraph_of_graphNorm_bound
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : D.freeSubspace, c * ‖x‖ ≤ ‖D.freeGraphMap x‖) :
    IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x)) :=
  D.isClosed_ambientGraph_of_antilipschitz
    (D.freeGraphMap_antilipschitz_of_bound hc hbound)

omit [CompleteSpace H] in
/-- A graph norm normalized so that `‖x‖ ≤ ‖(Jx,D⁴x)‖` immediately gives
closedness. -/
theorem isClosed_ambientGraph_of_normalized_graphNorm
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (hbound : ∀ x : D.freeSubspace, ‖x‖ ≤ ‖D.freeGraphMap x‖) :
    IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x)) := by
  apply D.isClosed_ambientGraph_of_graphNorm_bound (c := 1) one_pos
  simpa using hbound

/-- Build the closed free-beam operator directly from dense range and a graph
norm lower bound. -/
noncomputable def toPartialMapOfGraphNorm
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (_hdense : DenseRange D.freeEmbed)
    {c : ℝ} (_hc : 0 < c)
    (_hbound : ∀ x : D.freeSubspace, c * ‖x‖ ≤ ‖D.freeGraphMap x‖) :
    H →ₗ.[𝕜] H :=
  D.toPartialMap

end FourthOrderTraceModel

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
