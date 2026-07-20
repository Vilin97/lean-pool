/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init

/-!
# Trusted cost annotations

This module connects Lean-QuantumAlg theorem endpoints to a small trusted cost
interface. A value of `Timed α` returns an object of type `α` and carries a
trusted natural-number cost annotation.

The cost annotation is intentionally not derived from the Lean evaluator or from
matrix dimensions. Correctness is proved on `.ret`, while `.time` records the
selected model. In the current quantum algorithm bridge, one unit means one
oracle query for the single-query Walsh-Hadamard algorithms, and one
good/bad-plane iterate for amplitude amplification and Grover.

This is an operator-level bridge over the existing pure-state and gate
semantics. Fuller quantum program logics, such as density-operator or
Hoare-style semantics for quantum while programs, are future extensions rather
than prerequisites for this TimeM layer.
-/

@[expose] public section

namespace QuantumAlg

universe u

/-- A computation result paired with a natural-number cost. -/
structure Timed (α : Type u) where
  /-- The trusted return value. -/
  ret : α
  /-- The trusted cost annotation. -/
  time : ℕ

namespace Timed

/-- Attach a trusted cost to a return value. -/
def trusted {α : Type u} (cost : ℕ) (ret : α) : Timed α := ⟨ret, cost⟩

@[simp]
theorem trusted_ret {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).ret = ret := rfl

@[simp]
theorem trusted_time {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).time = cost := rfl

end Timed

/-- A trusted resource profile for registered theorem endpoints.

The fields are intentionally lightweight counters. They record the resource
model claimed beside a correctness theorem, not a derivation from Lean
evaluation. -/
structure ResourceProfile where
  /-- Number of oracle queries. -/
  oracleQueries : ℕ
  /-- Number of Hadamard gates. -/
  hadamardGates : ℕ
  /-- Number of non-oracle elementary gates. -/
  elementaryGates : ℕ
  /-- Number of trusted classical operations. -/
  classicalOps : ℕ
deriving DecidableEq

namespace ResourceProfile

/-- The empty resource profile. -/
def zero : ResourceProfile where
  oracleQueries := 0
  hadamardGates := 0
  elementaryGates := 0
  classicalOps := 0

/-- Sequential composition adds every resource counter. -/
def sequential (left right : ResourceProfile) : ResourceProfile where
  oracleQueries := left.oracleQueries + right.oracleQueries
  hadamardGates := left.hadamardGates + right.hadamardGates
  elementaryGates := left.elementaryGates + right.elementaryGates
  classicalOps := left.classicalOps + right.classicalOps

/-- Tensor/parallel circuit composition uses the same additive counters. -/
def tensor (left right : ResourceProfile) : ResourceProfile :=
  sequential left right

/-- Exact counter claim used by supporting public theorem statements. -/
def HasExactCounts (profile : ResourceProfile)
    (oracleQueries hadamardGates elementaryGates classicalOps : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.hadamardGates = hadamardGates ∧
    profile.elementaryGates = elementaryGates ∧
    profile.classicalOps = classicalOps

@[simp]
theorem sequential_oracleQueries (left right : ResourceProfile) :
    (sequential left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem sequential_hadamardGates (left right : ResourceProfile) :
    (sequential left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem sequential_elementaryGates (left right : ResourceProfile) :
    (sequential left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem sequential_classicalOps (left right : ResourceProfile) :
    (sequential left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

@[simp]
theorem tensor_oracleQueries (left right : ResourceProfile) :
    (tensor left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem tensor_hadamardGates (left right : ResourceProfile) :
    (tensor left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem tensor_elementaryGates (left right : ResourceProfile) :
    (tensor left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem tensor_classicalOps (left right : ResourceProfile) :
    (tensor left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

end ResourceProfile

/-- Gate counts for fixed circuit statements with named gate families. -/
structure CircuitGateProfile where
  /-- Number of Hadamard gates. -/
  hadamardGates : ℕ
  /-- Number of controlled phase gates. -/
  controlledPhaseGates : ℕ
  /-- Number of swap gates. -/
  swapGates : ℕ
deriving DecidableEq

namespace CircuitGateProfile

/-- Exact fixed-circuit gate-count claim. -/
def HasExactCounts (profile : CircuitGateProfile)
    (hadamardGates controlledPhaseGates swapGates : ℕ) : Prop :=
  profile.hadamardGates = hadamardGates ∧
    profile.controlledPhaseGates = controlledPhaseGates ∧
    profile.swapGates = swapGates

end CircuitGateProfile

/-- A return value paired with a trusted resource profile. -/
structure Profiled (α : Type u) where
  /-- The returned value. -/
  ret : α
  /-- Trusted resource accounting attached to the value. -/
  resources : ResourceProfile

namespace Profiled

/-- Attach a trusted resource profile to a return value. -/
def trusted {α : Type u} (resources : ResourceProfile) (ret : α) : Profiled α :=
  ⟨ret, resources⟩

@[simp]
theorem trusted_ret {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).ret = ret := rfl

@[simp]
theorem trusted_resources {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).resources = resources := rfl

end Profiled

/-- Communication resources for protocol statements. -/
structure CommunicationProfile where
  /-- Number of classical bits communicated. -/
  classicalBits : ℕ
  /-- Number of qubits transmitted. -/
  transmittedQubits : ℕ
  /-- Number of Bell pairs consumed. -/
  bellPairs : ℕ
deriving DecidableEq

namespace CommunicationProfile

/-- Exact communication-resource claim for protocol supporting theorems. -/
def HasExactCounts (profile : CommunicationProfile)
    (classicalBits transmittedQubits bellPairs : ℕ) : Prop :=
  profile.classicalBits = classicalBits ∧
    profile.transmittedQubits = transmittedQubits ∧
    profile.bellPairs = bellPairs

@[simp]
theorem hasExactCounts_mk (classicalBits transmittedQubits bellPairs : ℕ) :
    HasExactCounts
      { classicalBits := classicalBits, transmittedQubits := transmittedQubits,
        bellPairs := bellPairs }
      classicalBits transmittedQubits bellPairs := by
  simp [HasExactCounts]

end CommunicationProfile

end QuantumAlg
