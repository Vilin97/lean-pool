/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Ore.PairStage


/-!
# Iterated coordinate-momentum pair stages

This file recursively repeats the checked `PairStage` construction over an
arbitrary coefficient ring.  It records only the resulting tower and the
canonical data introduced at each successor; it does not identify the tower
with a presented Weyl algebra.
-/

@[expose] public section

namespace Stafford38.OreIteratedPairStage

open Stafford38.OrePairStage

noncomputable section

universe u

/-- A type together with the ring structure used at the next Ore stage. -/
private structure RingStage where
  carrier : Type u
  ring : Ring carrier

variable (B : Type u) [Ring B]

/-- The recursively constructed ring data after adjoining `n` Weyl pairs. -/
private def iteratedPairData : Nat → RingStage
  | 0 => ⟨B, inferInstance⟩
  | n + 1 =>
      let previous := iteratedPairData n
      letI : Ring previous.carrier := previous.ring
      ⟨PairStage (B := previous.carrier), inferInstance⟩

/-- The ring obtained from `B` after recursively adjoining `n` checked
coordinate-momentum pairs. -/
def IteratedPairStage (n : Nat) : Type u :=
  (iteratedPairData B n).carrier

instance iteratedPairStageRing (n : Nat) : Ring (IteratedPairStage B n) :=
  (iteratedPairData B n).ring

/-- The zeroth stage is the original coefficient type. -/
theorem iteratedPairStage_zero : IteratedPairStage B 0 = B := rfl

/-- Every successor is definitionally the checked `PairStage` construction
over its predecessor. -/
theorem iteratedPairStage_succ (n : Nat) :
    IteratedPairStage B (n + 1) =
      PairStage (B := IteratedPairStage B n) := rfl

/-- The canonical embedding from stage `n` into stage `n + 1`. -/
def stageEmbedding (n : Nat) :
    IteratedPairStage B n →+* IteratedPairStage B (n + 1) :=
  pairCoefficient (B := IteratedPairStage B n)

/-- The coordinate introduced at the successor of stage `n`. -/
def stageCoordinate (n : Nat) : IteratedPairStage B (n + 1) :=
  pairCoordinate (B := IteratedPairStage B n)

/-- The momentum introduced at the successor of stage `n`. -/
def stageMomentum (n : Nat) : IteratedPairStage B (n + 1) :=
  pairMomentum (B := IteratedPairStage B n)

/-- The coordinate introduced at stage `n + 1` commutes with the embedded
predecessor ring. -/
theorem stageCoordinate_mul_embedding (n : Nat)
    (b : IteratedPairStage B n) :
    stageCoordinate B n * stageEmbedding B n b =
      stageEmbedding B n b * stageCoordinate B n :=
  pairCoordinate_mul_coefficient b

/-- The momentum introduced at stage `n + 1` commutes with the embedded
predecessor ring. -/
theorem stageMomentum_mul_embedding (n : Nat)
    (b : IteratedPairStage B n) :
    stageMomentum B n * stageEmbedding B n b =
      stageEmbedding B n b * stageMomentum B n :=
  pairMomentum_mul_coefficient b

/-- The generators introduced at stage `n + 1` satisfy the checked Weyl
relation. -/
theorem stageMomentum_mul_coordinate (n : Nat) :
    stageMomentum B n * stageCoordinate B n =
      stageCoordinate B n * stageMomentum B n + 1 :=
  pairMomentum_mul_coordinate


end

end Stafford38.OreIteratedPairStage
