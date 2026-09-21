/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.Generated.G4Row096
import LeanPool.BrillNoetherGraphs.LowGenus.Generated.G4Row099
import LeanPool.BrillNoetherGraphs.LowGenus.Generated.G4Row100
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations

/-!
# Generated closed-face checks for genus-four cubic rows

These are the public, kernel-checked fallbacks for the three cubic rows whose
closed-face proofs are represented by `.rpf` certificate trees.  They are not
intended to displace human-readable positive-length arguments:

* row 096 has the symbolic cone-march proof in
  `LowGenus.GenusFourRow096Pencil`;
* row 099 has the hand-written `K₃,₃` pencil retained in the private source
  tree;
* row 100 has its hand-written positive-length construction retained there as
  well.

The generated certificates add the fact needed by the public pseudocore
reduction: the same pencils survive every genus-preserving nonloopy forest
face.  Their Farkas receipts and firing scripts are rechecked by Lean's kernel;
no external checker is trusted.
-/
namespace AtanasovRanganathan.GenusFourGeneratedRows

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas

/-- Closed-face degree-three pencil for public atlas row 096. -/
theorem row096_closed (length : Fin 9 → ℕ)
    (hForest : IsForest row096Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row096Core (zeroSlots length)) :
    BNExists (faceSpec row096Core (by norm_num) length hForest hNotLoopy).graph 1 3 := by
  rw [faceSpec_eq_censusSpec]
  exact G4Row096.bnExists length hForest hNotLoopy

/-- Closed-face degree-three pencil for public atlas row 099. -/
theorem row099_closed (length : Fin 9 → ℕ)
    (hForest : IsForest row099Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row099Core (zeroSlots length)) :
    BNExists (faceSpec row099Core (by norm_num) length hForest hNotLoopy).graph 1 3 := by
  rw [faceSpec_eq_censusSpec]
  exact G4Row099.bnExists length hForest hNotLoopy

/-- Closed-face degree-three pencil for public atlas row 100. -/
theorem row100_closed (length : Fin 9 → ℕ)
    (hForest : IsForest row100Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row100Core (zeroSlots length)) :
    BNExists (faceSpec row100Core (by norm_num) length hForest hNotLoopy).graph 1 3 := by
  rw [faceSpec_eq_censusSpec]
  exact G4Row100.bnExists length hForest hNotLoopy

end AtanasovRanganathan.GenusFourGeneratedRows
