/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Tactic
import LeanPool.LeanLJ.Instance
open LeanLJ
namespace LeanLJ

def pbc {α} [RealLike α] (x L : α) : α := x - L * (HasRound.pround (x / L) : α)
def pbc_Float (position boxLength : Float) : Float := position - boxLength * Float.round (position / boxLength)
noncomputable def pbc_Real (position boxLength : ℝ) : ℝ := position - boxLength * round (position / boxLength)

noncomputable def squaredminImageDistance_Real ( posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbc_Real (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc_Real (posB (1:Fin 3) - posA (1: Fin 3)) (boxLength (1: Fin 3))
  let dz := pbc_Real (posB (2:Fin 3) - posA (2: Fin 3)) (boxLength (2: Fin 3))
  dx^2 + dy^2 + dz^2


noncomputable def minImageDistance_Real ( posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  (squaredminImageDistance_Real  posA posB boxLength).sqrt


def minImageDistance {α : Type } [RealLike α]
    (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) : α :=
  let dx := pbc (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  HasSqrt.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

/-
noncomputable def minImageDistance_real (posA posB : Fin 3 → ℝ) (boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbc_real (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc_real (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc_real (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  HasSqrt.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))
-/

def minImageDistance_Float (posA posB : Fin 3 → Float) (boxLength : Fin 3 → Float) : Float :=
  let dx := pbc_Float (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc_Float (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc_Float (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  Float.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))


def lj_p {α : Type} [RealLike α] (r r_c ε σ : α) : α :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0


noncomputable def lj_Real  (r r_c ε σ  : ℝ) : ℝ :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

noncomputable def Ljp  (r r_c ε σ  : ℝ) : ℝ :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0

noncomputable def LJ (r r_c ε σ  : ℝ) : ℝ :=
  if r ≤ r_c then
    4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)
  else
    0

def lj_Float (r r_c ε σ : Float) : Float :=
    if r ≤ r_c then
      let r3 := (σ / r) ^ (3 : Nat)
      let r6 := r3 * r3
      let r12 := r6 * r6
      4 * ε * (r12 - r6)
    else
      0


def pi : Float := 3.141592653589793

def rho (N boxlength : Float) : Float := N / (boxlength)^3


def U_LRC {α : Type} [RealLike α]
    (ρ pi ε σ rc : α) : α :=
  (8 * pi * ρ * ε) *
    ((1 / (9 : α)) * (σ ^ (12 : Nat) / rc ^ (9 : Nat))
       - (1 / (3 : α)) * (σ ^ (6 : Nat)  / rc ^ (3 : Nat)))


def U_LRC_Float (rho pi ε σ rc  : Float) : Float :=
  (8 * rho * pi * ε) * ((1/9) * (σ ^ 12 / rc ^ 9) - (1/3) * (σ ^ 6 / rc ^ 3))


noncomputable def U_LRC_Real (ρ ε σ rc  : ℝ) : ℝ :=
  (8 * Real.pi * ρ * ε) * ((1/9) * (σ ^ 12 / rc ^ 9) - (1/3) * (σ ^ 6 / rc ^ 3))


noncomputable def lj (r r_c ε σ : ℝ) : ℝ :=
    if r ≤ r_c then
      4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)
    else
      0


def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i =>
    (List.range' (i + 1) (n - (i + 1))).map fun j => (i, j)


def total_energy_pairs (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  let n := positions.length
  let indexPairs := pairs n
  indexPairs.foldl (fun acc (i, j) =>
    let r := minImageDistance_Float positions[i]! positions[j]! boxLength
    acc + lj_Float r cutoff ε σ
  ) 0.0


def total_energy_loop (positions : List (Fin 3 → Float))
(boxLength : Fin 3 → Float) (cutoff ε σ : Float) : Float :=
  Id.run do
    let mut energy := 0.0
    for i in [0 : positions.length] do
      for j in [i+1 : positions.length] do
        let r := minImageDistance_Float positions[i]! positions[j]! boxLength
        let e := lj_Float r cutoff ε σ
        energy := energy + e
    return energy


def total_energy_recursive (positions : List (Fin 3 → Float)) (box_length : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  let num_atoms := positions.length
  let rec energy (i j : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else if j = 0 then energy (i - 1) (i - 2) acc
    else
      let r := minImageDistance_Float (positions[i - 1]!) (positions[j - 1]!) box_length
      let e := lj_Float r cutoff ε σ
      energy i (j - 1) (acc + e)
  energy num_atoms (num_atoms - 1) 0.0


def computeTotal_Energy (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float) (cutoff ε σ : Float) : Float :=
  let numAtoms := positions.length
  let rec energy : Nat → Nat → Float → Float
    | 0, _, acc => acc
    | i+1, 0, acc => energy i (i - 1) acc
    | i+1, j+1, acc =>
      let r := minImageDistance_Float positions[i]! positions[j]! boxLength
      let e := lj_Float r cutoff ε σ
      energy (i+1) j (acc + e)
  energy numAtoms (numAtoms - 1) 0.0


def getNISTEnergy (n : Nat) : Option Float :=
  match n with
  | 30 => some (-16.790)
  | 200 => some (-690.000)
  | 400 => some (-1146.700)
  | 800 => some (-4351.500)
  | _ => none


def getNISTEnergy_LRC (n : Nat) : Option Float :=
  match n with
  | 30 => some (-0.54517)
  | 200 => some (-24.230)
  | 400 => some (-49.622)
  | 800 => some (-198.49)
  | _ => none


end LeanLJ
