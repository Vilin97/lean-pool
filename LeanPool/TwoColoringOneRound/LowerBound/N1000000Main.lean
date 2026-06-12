/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionForB
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Bound
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000RelaxationPsdSoundness

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Main
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000

open Distributed2Coloring.LowerBound.N1000000BCompressionForB
open Distributed2Coloring.LowerBound.N1000000Bound
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000RelaxationPsdSoundness
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := N1000000WeakDuality.Block

/--
Main deliverable (kernel-checked):

For `n = 1,000,000`, every `Coloring n` has monochromatic-edge fraction at least `23879/100000`.

Definitions:
- `Coloring` / `monoFraction` / `Edge.monochromatic` are in `Distributed2Coloring.LowerBound.Defs`.
- The proof combines a precomputed exact rational dual certificate with weak duality, and shows the
  required PSD constraints for `xFromColoring f` via a compression/congruence argument.
-/
theorem monoFraction_ge_23879 (f : Coloring n) :
    (23879 : Q) / 100000 ≤ monoFraction f := by
  have hcomp : CompressionHypScaled := N1000000BCompressionForB.compressionHypScaled
  have hpsd : ∀ r : Block, (S (xFromColoring f) r).PosSemidef :=
    psd_of_compressionHypScaled hcomp f
  exact N1000000Bound.monoFraction_ge_23879_of_psd (f := f) hpsd

end N1000000

end Distributed2Coloring.LowerBound
