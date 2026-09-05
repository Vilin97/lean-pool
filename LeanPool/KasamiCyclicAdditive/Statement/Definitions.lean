/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Statement definitions for the cyclic-additive statement surface

These definitions intentionally duplicate the concrete statement definitions
in `Challenge.lean`.  The Challenge may not import candidate-local helper
files, so the proof development carries its own copies.  Their semantic
agreement with an independently structured literature specification is audited
in `Validation/LiteratureBridge.lean`.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The Kasami exponent `4^k - 2^k + 1`. -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The normalized derivative of the Kasami monomial in direction `1`:
`δ(b) = (b+1)^d + b^d + 1`. -/
def kasamiDerivative (k : ℕ) (b : K) : K :=
  (b + 1) ^ kasamiExponent k + b ^ kasamiExponent k + 1

/-- The image `Δ` of the normalized Kasami derivative. -/
def derivativeImage (k : ℕ) (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  Finset.image (kasamiDerivative k) Finset.univ

/-- The number of triples `(x,y,z) ∈ Δ³` satisfying
`v₁ x + v₂ y + (v₁+v₂) z = 0`. -/
def coefficientTripleCount (k : ℕ) (v₁ v₂ : K) : ℕ :=
  (((derivativeImage k K) ×ˢ (derivativeImage k K) ×ˢ (derivativeImage k K)).filter
    (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)).card

end KasamiCyclicAdditive
