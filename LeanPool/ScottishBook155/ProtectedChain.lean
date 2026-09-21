/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CoherentBiSystem
import LeanPool.ScottishBook155.DirectedLimitStage
import LeanPool.ScottishBook155.ProtectedChainCore

/-!
# Coherent protected chains

This is the invariant carried by the transfinite recursion: protected stages,
coherent forward embeddings and backward projections, and the fixed-band
recovery identity between every two stages.
-/

namespace ScottishBook155

universe u

/-- A coherent chain of protected stages with uniform recovery radius `L`. -/
structure ProtectedChain {ι : Type u} [LinearOrder ι] (r L : ℝ) where
  stage : ι → ProtectedStage.{u} r
  sourceSystem : CoherentBiSystem (fun i => (stage i).source)
  targetSystem : CoherentBiSystem (fun i => (stage i).target)
  compatible : ∀ i j (hij : i ≤ j) x,
    (stage j).map (sourceSystem.embed i j hij x) =
      targetSystem.embed i j hij ((stage i).map x)
  recovers : ∀ i j (hij : i ≤ j) z,
    dist z (sourceSystem.embed i j hij
      (sourceSystem.project i j hij z)) < L →
    targetSystem.project i j hij ((stage j).map z) =
      (stage i).map (sourceSystem.project i j hij z)

namespace ProtectedChain

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {r L : ℝ} (C : ProtectedChain (ι := ι) r L)

/-- Protected chains are determined by their stage family and their two
bidirectional systems; the remaining fields are propositions. -/
theorem ext {C D : ProtectedChain (ι := ι) r L}
    (hstage : C.stage = D.stage)
    (hsource : HEq C.sourceSystem D.sourceSystem)
    (htarget : HEq C.targetSystem D.targetSystem) : C = D := by
  cases C
  cases D
  dsimp at hstage hsource htarget ⊢
  cases hstage
  cases eq_of_heq hsource
  cases eq_of_heq htarget
  rfl

abbrev Source (i : ι) := (C.stage i).source
abbrev Target (i : ι) := (C.stage i).target

/-- Every stage map in a protected chain is nonexpansive at positive protected
scale. -/
theorem stage_nonexpansive (hr : 0 < r) (i : ι) (x y : C.Source i) :
    dist ((C.stage i).map x) ((C.stage i).map y) ≤ dist x y :=
  preservesUpTo_nonexpansive hr (C.stage i).preservesUpTo x y

end ProtectedChain

end ScottishBook155
