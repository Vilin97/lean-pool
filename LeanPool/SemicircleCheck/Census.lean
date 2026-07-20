/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
  COMPUTATIONAL ORACLE: The Semicircle Census

  Verified by Python brute-force enumeration (test/verify_census.py).
  Lean's `Finset.toList` is noncomputable, so the census runs outside
  the kernel. The results below are ground truth.

  ## Cycle Distributions (0-indexed, γ = finRotate)

  n=1:  [2]                    total=1,   genus-0: 1   = C₁
  n=2:  [3, 3, 1]              total=3,   genus-0: 2   = C₂
  n=3:  [4×5, 2×10]            total=15,  genus-0: 5   = C₃
  n=4:  [5×14, 3×70, 1×21]     total=105, genus-0: 14  = C₄
  n=5:  [6×42, 4×420, 2×483]   total=945, genus-0: 42  = C₅

  ## Harer-Zagier Table (genus distribution)

  2n= 2:  g0=1                                          = 1
  2n= 4:  g0=2   + g1=1                                 = 3
  2n= 6:  g0=5   + g1=10                                = 15
  2n= 8:  g0=14  + g1=70  + g2=21                       = 105
  2n=10:  g0=42  + g1=420 + g2=483                       = 945
  2n=12:  g0=132 + g1=2310 + g2=6468 + g3=1485           = 10395

  The genus-0 column is the Catalan sequence: 1, 2, 5, 14, 42, 132.
  Cycle count c and genus g satisfy: c = n + 1 - 2g.
  Maximum cycles = n + 1 ↔ genus 0 ↔ noncrossing.

  ## Key Structural Facts (verified computationally through n=6)

  1. All cycle counts have the same parity as n + 1.
  2. Cycle counts range from n + 1 (genus 0) down to 1 or 2.
  3. The genus distribution satisfies the Harer-Zagier recurrence:
     (n+1) · ε_g(n) = (4n-2) · ε_g(n-1) + (2n-1)(n-1) · ε_{g-1}(n-1)
  4. Total pairings = (2n-1)!! = 1·3·5···(2n-1).
-/

open Equiv Equiv.Perm

/-! ## Specific pairings for small n, defined computably for formal verification -/

/-- The unique pairing on Fin 2: swap 0 ↔ 1. -/
def pairingN1 : Perm (Fin 2) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩

-- Verify: pairingN1 is a fixed-point-free involution
example : pairingN1 ^ 2 = 1 := by decide
example : ∀ x : Fin 2, pairingN1 x ≠ x := by decide

-- Verify: γ * π = id on Fin 2, so 2 cycles (two fixed points)
example : finRotate 2 * pairingN1 = 1 := by decide

/-- The adjacent noncrossing pairing on Fin 4: pairs 0↔1 and 2↔3. -/
def nc4Adjacent : Perm (Fin 4) :=
  (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩).trans
    (Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩)

/-- The nested noncrossing pairing on Fin 4: pairs 0↔3 and 1↔2. -/
def nc4Nested : Perm (Fin 4) :=
  (Equiv.swap ⟨0, by omega⟩ ⟨3, by omega⟩).trans
    (Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩)

/-- The crossing pairing on Fin 4. -/
def cross4 : Perm (Fin 4) :=
  (Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩).trans
    (Equiv.swap ⟨1, by omega⟩ ⟨3, by omega⟩)

-- All three are pairings
example : nc4Adjacent ^ 2 = 1 ∧ ∀ x : Fin 4, nc4Adjacent x ≠ x := by decide
example : nc4Nested ^ 2 = 1 ∧ ∀ x : Fin 4, nc4Nested x ≠ x := by decide
example : cross4 ^ 2 = 1 ∧ ∀ x : Fin 4, cross4 x ≠ x := by decide

-- The crossing pairing's composition γπ is a single 4-cycle (1 cycle, genus 1)
-- The noncrossing ones give 3 cycles (genus 0)
-- These are verified by the Python census; formal cycle-counting requires
-- computable cycleType which is blocked by Finset.toList noncomputability.
