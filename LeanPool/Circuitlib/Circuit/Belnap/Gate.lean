/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Belnap.Basic
import LeanPool.Circuitlib.Circuit.Gate

/-! # Belnap gates

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- The gate set for Belnap circuits: the logical AND, OR and NOT gates. -/
inductive BelnapGate
  | and
  | or
  | not

namespace BelnapGate

instance : Gate BelnapLevel BelnapGate where
  inputs
  | .and => 2
  | .or => 2
  | .not => 1
  outputs _ := 1
  gate
  | .and => Belnap.and
  | .or => Belnap.or
  | .not => Belnap.not
  gate_monotone
  | .and => Belnap.and_monotonic
  | .or => Belnap.or_monotonic
  | .not => Belnap.not_monotonic

end BelnapGate

end Circuit
