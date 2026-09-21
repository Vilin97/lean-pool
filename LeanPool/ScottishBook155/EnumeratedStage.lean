/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.ScheduledSuccessor

/-!
# Cardinal-controlled enumerated stages
-/

namespace ScottishBook155

private abbrev RI := RecursionIndex.{0}

/-- A protected stage together with the uniform cardinal bounds and the
enumeration used by bookkeeping. -/
structure EnumeratedStage where
  stage : ProtectedStage.{0} ((1 : ℝ) / 2)
  source_mk_le : Cardinal.mk stage.source ≤ stageCardinal
  target_mk_le : Cardinal.mk stage.target ≤ stageCardinal
  enumerate : RI → stage.target
  enumerate_surjective : Function.Surjective enumerate

/-- Add the canonical recursion-indexed enumeration to a bounded stage. -/
noncomputable def EnumeratedStage.ofBounded
    (S : ProtectedStage.{0} ((1 : ℝ) / 2))
    (hM : Cardinal.mk S.source ≤ stageCardinal)
    (hN : Cardinal.mk S.target ≤ stageCardinal) : EnumeratedStage where
  stage := S
  source_mk_le := hM
  target_mk_le := hN
  enumerate := stageEnumeration hN
  enumerate_surjective := stageEnumeration_surjective hN

/-- The cardinal-controlled bent initial stage. -/
noncomputable def enumeratedBentSeed : EnumeratedStage :=
  EnumeratedStage.ofBounded bentSeedStage
    bentSeedStage_source_mk_le bentSeedStage_target_mk_le

/-- The next enumerated stage after processing one named target point. -/
noncomputable def EnumeratedStage.successor (S : EnumeratedStage)
    (y : S.stage.target) : EnumeratedStage :=
  EnumeratedStage.ofBounded (scheduledSuccessor S.stage y).next
    (scheduledSuccessor_source_mk_le S.stage y S.source_mk_le)
    (scheduledSuccessor_target_mk_le S.stage y S.source_mk_le S.target_mk_le)

/-- The point processed by `successor` belongs to the image of its new stage. -/
theorem EnumeratedStage.successor_hits (S : EnumeratedStage)
    (y : S.stage.target) :
    ∃ x : (S.successor y).stage.source,
      (S.successor y).stage.map x = (scheduledSuccessor S.stage y).targetEmbedding y :=
  scheduledSuccessor_hits S.stage y

end ScottishBook155
