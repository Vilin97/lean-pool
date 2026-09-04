/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.Result
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Minimal construction interface for the Wallace counterexample

The construction supplies characters compatible with all prescribed ultrafilter limits and
separating the points of the free group.  For the Wallace corollary it is enough that, for every
nonzero element `x`, one compatible character does not annihilate `x`.  This file isolates
precisely that output.

No topology on the free Abelian group and no compactness conclusion is stored in
`SeparationPackage`; both are derived below from its algebraic and filter-theoretic fields.
-/

open Filter Set Topology

universe u

namespace Wallace

noncomputable section

/-- An injective sequence bundled with the proof of injectivity. -/
def InjectiveSequence' (G : Type u) :=
  {s : ℕ → G // Function.Injective s}

/--
The minimal post-fusion data needed for Wallace's problem.

The difficult construction must supply the coding, the prepared subsequences and free
ultrafilters, and a compatible separating character for every nonzero element.  The structure
does not assume any topology or compactness property of the free Abelian group.
-/
structure SeparationPackage (I : Type u) where
  Code : Type u
  codeEquiv : Code ≃ InjectiveSequence' (I →₀ ℤ)
  codeIndex : Code → I
  subsequence : Code → ℕ → ℕ
  subsequence_strictMono : ∀ c, StrictMono (subsequence c)
  ultrafilter : Code → Ultrafilter ℕ
  ultrafilter_free : ∀ c, (ultrafilter c : Filter ℕ) ≤ cofinite
  character : {x : I →₀ ℤ // x ≠ 0} → (I →₀ ℤ) →+ UnitAddCircle
  character_self_ne_zero : ∀ x, character x x ≠ 0
  character_limit :
    ∀ (c : Code) (x : {x : I →₀ ℤ // x ≠ 0}),
      Tendsto
        (fun n ↦ character x ((codeEquiv c).1 (subsequence c n)))
        (ultrafilter c)
        (nhds (character x (Finsupp.single (codeIndex c) (1 : ℤ))))

namespace SeparationPackage

variable {I : Type u}

/-- Simultaneous evaluation by all compatible separating characters. -/
def evaluation (C : SeparationPackage I) :
    (I →₀ ℤ) →+ ({x : I →₀ ℤ // x ≠ 0} → UnitAddCircle) where
  toFun y x := C.character x y
  map_zero' := by
    funext x
    exact map_zero (C.character x)
  map_add' x y := by
    funext z
    exact map_add (C.character z) x y

/-- The initial topology induced by the compatible separating characters. -/
@[reducible] def initialTopology (C : SeparationPackage I) :
    TopologicalSpace (I →₀ ℤ) :=
  TopologicalSpace.induced C.evaluation inferInstance

theorem evaluation_injective (C : SeparationPackage I) :
    Function.Injective C.evaluation := by
  intro x y hxy
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  let z : {z : I →₀ ℤ // z ≠ 0} := ⟨x - y, hsub⟩
  have hz := C.character_self_ne_zero z
  apply hz
  rw [map_sub]
  have hcoord : C.character z x = C.character z y := congrFun hxy z
  rw [hcoord, sub_self]

theorem initial_isTopologicalAddGroup (C : SeparationPackage I) :
    @IsTopologicalAddGroup (I →₀ ℤ) C.initialTopology _ := by
  exact topologicalAddGroup_induced C.evaluation

theorem initial_t2Space (C : SeparationPackage I) :
    @T2Space (I →₀ ℤ) C.initialTopology := by
  letI : TopologicalSpace (I →₀ ℤ) := C.initialTopology
  exact C.evaluation_injective.isEmbedding_induced.t2Space

/-- The prepared subsequence converges to its prescribed basis point in the initial topology. -/
theorem prepared_tendsto_basis (C : SeparationPackage I) (c : C.Code) :
    Tendsto
      (fun n ↦ (C.codeEquiv c).1 (C.subsequence c n))
      (C.ultrafilter c)
      (@nhds (I →₀ ℤ) C.initialTopology
        (Finsupp.single (C.codeIndex c) (1 : ℤ))) := by
  letI : TopologicalSpace (I →₀ ℤ) := C.initialTopology
  have hinducing : IsInducing C.evaluation := ⟨rfl⟩
  refine hinducing.tendsto_nhds_iff.mpr ?_
  refine tendsto_pi_nhds.2 fun x ↦ ?_
  simpa [evaluation, Function.comp_def] using C.character_limit c x

/-- The package supplies the exact free-ultrafilter limit property used by the cone argument. -/
theorem positiveCone_hasWallaceLimitProperty (C : SeparationPackage I) :
    @HasWallaceLimitProperty (I →₀ ℤ) C.initialTopology _ (positiveCone I) := by
  letI : TopologicalSpace (I →₀ ℤ) := C.initialTopology
  intro s hs _hscone
  let encoded : InjectiveSequence' (I →₀ ℤ) := ⟨s, hs⟩
  let c : C.Code := C.codeEquiv.symm encoded
  have hcoded : (C.codeEquiv c).1 = s := by
    exact congrArg Subtype.val (C.codeEquiv.apply_symm_apply encoded)
  refine ⟨C.subsequence c, Finsupp.single (C.codeIndex c) 1, C.ultrafilter c,
    C.subsequence_strictMono c, single_one_mem_positiveCone I (C.codeIndex c),
    C.ultrafilter_free c, ?_⟩
  change Tendsto (fun n ↦ s (C.subsequence c n)) (C.ultrafilter c) _
  rw [← hcoded]
  exact C.prepared_tendsto_basis c

end SeparationPackage

end

end Wallace
