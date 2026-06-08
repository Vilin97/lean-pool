/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanPool.LeanLJ.Instance

/-!
# Lennard-Jones potential and energy functions

This file defines the periodic-boundary distance helpers (`pbc`, `minImageDistance`),
several formulations of the truncated Lennard-Jones pair potential (`lj`, `Ljp`, `LJ`),
the long-range correction `uLRC`, and the energy-summation routines over atom pairs.
-/

open LeanLJ
namespace LeanLJ

/-- Periodic-boundary wrap of `x` into a cell of size `L`, for any `RealLike` type. -/
def pbc {α} [RealLike α] (x L : α) : α := x - L * (HasRound.pround (x / L) : α)

/-- Periodic-boundary wrap of a `Float` position into a cell of size `boxLength`. -/
def pbcFloat (position boxLength : Float) : Float :=
  position - boxLength * Float.round (position / boxLength)

/-- Periodic-boundary wrap of a real position into a cell of size `boxLength`. -/
noncomputable def pbcReal (position boxLength : ℝ) : ℝ :=
  position - boxLength * round (position / boxLength)

/-- The squared real minimum-image distance between two 3-vectors under a box. -/
noncomputable def squaredminImageDistanceReal (posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbcReal (posB (0 : Fin 3) - posA (0 : Fin 3)) (boxLength (0 : Fin 3))
  let dy := pbcReal (posB (1 : Fin 3) - posA (1 : Fin 3)) (boxLength (1 : Fin 3))
  let dz := pbcReal (posB (2 : Fin 3) - posA (2 : Fin 3)) (boxLength (2 : Fin 3))
  dx ^ 2 + dy ^ 2 + dz ^ 2

/-- The real minimum-image distance between two 3-vectors under a box. -/
noncomputable def minImageDistanceReal (posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  (squaredminImageDistanceReal posA posB boxLength).sqrt

/-- The minimum-image distance between two 3-vectors over any `RealLike` type. -/
def minImageDistance {α : Type} [RealLike α]
    (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) : α :=
  let dx := pbc (posB (0 : Fin 3) - posA (0 : Fin 3)) (boxLength (0 : Fin 3))
  let dy := pbc (posB (1 : Fin 3) - posA (1 : Fin 3)) (boxLength (1 : Fin 3))
  let dz := pbc (posB (2 : Fin 3) - posA (2 : Fin 3)) (boxLength (2 : Fin 3))
  HasSqrt.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

/-- The minimum-image distance between two `Float` 3-vectors under a box. -/
def minImageDistanceFloat (posA posB : Fin 3 → Float) (boxLength : Fin 3 → Float) : Float :=
  let dx := pbcFloat (posB (0 : Fin 3) - posA (0 : Fin 3)) (boxLength (0 : Fin 3))
  let dy := pbcFloat (posB (1 : Fin 3) - posA (1 : Fin 3)) (boxLength (1 : Fin 3))
  let dz := pbcFloat (posB (2 : Fin 3) - posA (2 : Fin 3)) (boxLength (2 : Fin 3))
  Float.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

/-- The truncated Lennard-Jones pair potential over any `RealLike` type. -/
def ljP {α : Type} [RealLike α] (r r_c ε σ : α) : α :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

/-- The truncated real Lennard-Jones pair potential, in nested-power form. -/
noncomputable def ljReal (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

/-- The truncated real Lennard-Jones pair potential, written with `^6` and `^2`. -/
noncomputable def Ljp (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0

/-- The truncated real Lennard-Jones pair potential, written with `^12` and `^6`. -/
noncomputable def LJ (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)
  else
    0

/-- The truncated `Float` Lennard-Jones pair potential. -/
def ljFloat (r r_c ε σ : Float) : Float :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

/-- A `Float` approximation of `π`. -/
def pi : Float := 3.141592653589793

/-- The `Float` number density `N / boxlength ^ 3`. -/
def rho (N boxlength : Float) : Float := N / boxlength ^ 3

/-- The Lennard-Jones long-range correction over any `RealLike` type. -/
def uLRC {α : Type} [RealLike α]
    (ρ pi ε σ rc : α) : α :=
  (8 * pi * ρ * ε) *
    ((1 / (9 : α)) * (σ ^ (12 : Nat) / rc ^ (9 : Nat))
       - (1 / (3 : α)) * (σ ^ (6 : Nat) / rc ^ (3 : Nat)))

/-- The `Float` Lennard-Jones long-range correction. -/
def uLRCFloat (rho pi ε σ rc : Float) : Float :=
  (8 * rho * pi * ε) * ((1 / 9) * (σ ^ 12 / rc ^ 9) - (1 / 3) * (σ ^ 6 / rc ^ 3))

/-- The real Lennard-Jones long-range correction, using `Real.pi`. -/
noncomputable def uLRCReal (ρ ε σ rc : ℝ) : ℝ :=
  (8 * Real.pi * ρ * ε) * ((1 / 9) * (σ ^ 12 / rc ^ 9) - (1 / 3) * (σ ^ 6 / rc ^ 3))

/-- The truncated real Lennard-Jones pair potential in its simplest form. -/
noncomputable def lj (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)
  else
    0

/-- The list of unordered index pairs `(i, j)` with `i < j` for `n` atoms. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i =>
    (List.range' (i + 1) (n - (i + 1))).map fun j => (i, j)

/-- Total Lennard-Jones energy of a configuration, summed over the enumerated pairs. -/
def totalEnergyPairs (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  let n := positions.length
  let indexPairs := pairs n
  indexPairs.foldl (fun acc (i, j) =>
    let r := minImageDistanceFloat positions[i]! positions[j]! boxLength
    acc + ljFloat r cutoff ε σ
  ) 0.0

/-- Total Lennard-Jones energy of a configuration, computed with an imperative loop. -/
def totalEnergyLoop (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float) (cutoff ε σ : Float) : Float :=
  Id.run do
    let mut energy := 0.0
    for i in [0 : positions.length] do
      for j in [i + 1 : positions.length] do
        let r := minImageDistanceFloat positions[i]! positions[j]! boxLength
        let e := ljFloat r cutoff ε σ
        energy := energy + e
    return energy

/-- Total Lennard-Jones energy of a configuration, computed by explicit recursion. -/
def totalEnergyRecursive (positions : List (Fin 3 → Float)) (box_length : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  energy positions.length (positions.length - 1) 0.0
where
  /-- Accumulator recursion over the lower-triangular pair indices. -/
  energy (i j : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else if j = 0 then energy (i - 1) (i - 2) acc
    else
      let r := minImageDistanceFloat (positions[i - 1]!) (positions[j - 1]!) box_length
      let e := ljFloat r cutoff ε σ
      energy i (j - 1) (acc + e)

/-- Total Lennard-Jones energy of a configuration, via structural recursion. -/
def computeTotalEnergy (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float) (cutoff ε σ : Float) : Float :=
  energy positions.length (positions.length - 1) 0.0
where
  /-- Accumulator recursion over the lower-triangular pair indices. -/
  energy : Nat → Nat → Float → Float
    | 0, _, acc => acc
    | i + 1, 0, acc => energy i (i - 1) acc
    | i + 1, j + 1, acc =>
      let r := minImageDistanceFloat positions[i]! positions[j]! boxLength
      let e := ljFloat r cutoff ε σ
      energy (i + 1) j (acc + e)

/-- Reference NIST total energies for benchmark configurations of `n` atoms. -/
def getNISTEnergy (n : Nat) : Option Float :=
  match n with
  | 30 => some (-16.790)
  | 200 => some (-690.000)
  | 400 => some (-1146.700)
  | 800 => some (-4351.500)
  | _ => none

/-- Reference NIST long-range-correction energies for benchmark configurations. -/
def getNISTEnergyLRC (n : Nat) : Option Float :=
  match n with
  | 30 => some (-0.54517)
  | 200 => some (-24.230)
  | 400 => some (-49.622)
  | 800 => some (-198.49)
  | _ => none

end LeanLJ
