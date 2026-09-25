/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedContraction
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ReorientContraction

/-!
# Dispatching one exact closed face to its contracted core

`ClosedContraction` lifts a positive target subdivision into a face of a
larger closed row.  This module records the converse use of the same data: if
the zero set of an already-given closed length vector is exactly the forest
stored in `ContractionData`, its degenerate subdivision is equivalent to a
positive subdivision of the displayed target core.
-/

@[expose] public section
namespace Utilities.Certificate.ClosedFaceDispatch

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ClosedContraction
open Utilities.Certificate.ClosedFaceCensus
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ReorientContraction

variable {n p n' p' : ℕ}
variable {core : ExplicitPotential.Core n p}
variable {core' : ExplicitPotential.Core n' p'}

namespace ContractionData

/-- The honest positive target subdivision obtained by retaining the slots
named by an exact contraction face. -/
def targetSpec (c : ContractionData core core') (hn' : 0 < n')
    (length : Fin p → ℕ) (hZero : zeroSet length = c.F) :
    SubdivisionGraph.Spec n' p' where
  core := core'
  length := fun edge => length (c.slot edge)
  core_nonempty := hn'
  core_loopless := by
    intro edge hLoop
    apply c.notLoopy
    refine ⟨c.slot edge, c.slot_notMem edge, ?_⟩
    rw [← c.tail_eq edge, ← c.head_eq edge, hLoop]
  length_pos := by
    intro edge
    have hSurvives : c.slot edge ∉ zeroSet length := by
      rw [hZero]
      exact c.slot_notMem edge
    rw [mem_zeroSet] at hSurvives
    omega

/-- Lifting the descended target subdivision recovers the original exact-face
length vector, slot by slot. -/
theorem lift_targetSpec (c : ContractionData core core') (hn' : 0 < n')
    (length : Fin p → ℕ) (hZero : zeroSet length = c.F) :
    c.lift (targetSpec c hn' length hZero) = length := by
  funext edge
  by_cases hF : edge ∈ c.F
  · rw [c.lift_of_mem _ hF]
    have hZeroEdge : edge ∈ zeroSet length := by
      rw [hZero]
      exact hF
    exact (mem_zeroSet length edge).mp hZeroEdge |>.symm
  · obtain ⟨edge', hSlot⟩ := c.slot_surj edge hF
    subst edge
    exact c.lift_slot (targetSpec c hn' length hZero) edge'

end ContractionData

/-- An exact forest face is equivalent to the positive subdivision of its
`ContractionData` target.  This is the small reusable dispatcher behind
human-readable finite face ledgers. -/
theorem bnExists_censusSpec_of_exact_contraction
    (c : ContractionData core core') (hn : 0 < n) (hn' : 0 < n')
    (length : Fin p → ℕ)
    (hForest : IsForest core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy core (zeroSet length))
    (hZero : zeroSet length = c.F) (degree : ℤ)
    (hTarget : ∀ s : SubdivisionGraph.Spec n' p', s.core = core' →
      BNExists s.graph 1 degree) :
    BNExists (censusSpec core hn length hForest hNotLoopy).graph 1 degree := by
  let target := ContractionData.targetSpec c hn' length hZero
  have hLift : c.lift target = length :=
    ContractionData.lift_targetSpec c hn' length hZero
  have hSource :
      censusSpec core hn length hForest hNotLoopy =
        censusSpec core hn (c.lift target) (c.isForest_lift target)
          (c.notLoopy_lift target) := by
    apply degSpec_ext
    · rfl
    · exact hLift.symm
    · change compFold core (zeroSet length) =
        compFold core (zeroSet (c.lift target))
      rw [hZero, c.zeroSet_lift target]
  rw [hSource]
  exact ((c.contraction target hn rfl).laplacianEquiv.bnExists_iff 1 degree).mp
    (hTarget target rfl)

/-- A positive-subdivision theorem for a core also applies when some target
slots are presented backwards. -/
theorem bnExists_spec_of_reoriented_core
    (rev : Fin p' → Bool) (degree : ℤ)
    (hTarget : ∀ t : SubdivisionGraph.Spec n' p', t.core = core' →
      BNExists t.graph 1 degree)
    (s : SubdivisionGraph.Spec n' p')
    (hCore : s.core = ReorientContraction.Core.reorient core' rev) :
    BNExists s.graph 1 degree := by
  have hDouble : (ReorientContraction.reorientSpec s rev).core = core' := by
    apply ClosedContraction.core_ext
    · funext edge
      change (ReorientContraction.Core.reorient s.core rev).tail edge = core'.tail edge
      rw [hCore]
      by_cases hRev : rev edge <;> simp [ReorientContraction.Core.reorient, hRev]
    · funext edge
      change (ReorientContraction.Core.reorient s.core rev).head edge = core'.head edge
      rw [hCore]
      by_cases hRev : rev edge <;> simp [ReorientContraction.Core.reorient, hRev]
  have hReoriented : BNExists (ReorientContraction.reorientSpec s rev).graph 1 degree :=
    hTarget (ReorientContraction.reorientSpec s rev) hDouble
  exact ((SubdivisionGraph.Spec.laplacianEquiv s
    (ReorientContraction.reorientSpec s rev)
    (ReorientContraction.reorientRelabeling s rev)).bnExists_iff 1 degree).mpr
      hReoriented

end Utilities.Certificate.ClosedFaceDispatch
