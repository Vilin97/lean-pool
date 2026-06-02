/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

import LeanPool.TwoColoringOneRound.LowerBound.CorrAvgMatrix
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WedderburnData

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000RelaxationPsdSoundness
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000RelaxationPsdSoundness

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000WedderburnData

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := N1000000WeakDuality.Block

/--
Scaled compression hypothesis: each reduced PSD block, after multiplying by its positive scale
factor, is a congruence transform of `corrAvgMatrix f`.
-/
def CompressionHypScaled : Prop :=
  ∃ B : Block → Matrix V (Fin 3) Q,
    ∀ f : Coloring n, ∀ r : Block,
      (blockScales[r.1]! : Q) • S (xFromColoring f) r = (B r)ᴴ * (corrAvgMatrix (f := f)) * (B r)

private lemma posSemidef_of_pos_smul {M : Matrix (Fin 3) (Fin 3) Q} {a : Q}
    (ha : 0 < a) (h : (a • M).PosSemidef) : M.PosSemidef := by
  have ha' : 0 ≤ (1 / a : Q) := by
    exact div_nonneg (show (0 : Q) ≤ 1 by norm_num) (le_of_lt ha)
  have := Matrix.PosSemidef.smul (x := (a • M)) h (a := (1 / a : Q)) ha'
  simpa [smul_smul, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), one_smul] using this

theorem psd_of_compressionHypScaled (h : CompressionHypScaled) :
    ∀ f : Coloring n, ∀ r : Block, (S (xFromColoring f) r).PosSemidef := by
  classical
  rcases h with ⟨B, hB⟩
  intro f r
  have hX : (corrAvgMatrix (f := f)).PosSemidef :=
    Correlation.corrAvgMatrix_posSemidef (f := f)
  have hCong :
      ((B r)ᴴ * (corrAvgMatrix (f := f)) * (B r)).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same (A := (corrAvgMatrix (f := f))) hX (B := (B r))
  have hs : ((blockScales[r.1]! : Q) • S (xFromColoring f) r).PosSemidef := by
    simpa [hB f r] using hCong
  have hscale : 0 < (blockScales[r.1]! : Q) := by
    fin_cases r <;> decide
  exact posSemidef_of_pos_smul (ha := hscale) hs

end N1000000RelaxationPsdSoundness

end Distributed2Coloring.LowerBound
