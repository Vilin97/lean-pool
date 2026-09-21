/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.EquivariantMap

/-!
# Abstract compact prime configuration model

The concrete polyhedron used in the paper will eventually instantiate this structure. The
structure records only compact topological and equivariant data; it does not postulate a zero-count
or separation theorem.
-/

namespace NRR

variable {p : ℕ}

/-- A compact prime configuration space with its equivariant configuration and reference maps. -/
structure PrimeConfigurationModel (hp : Nat.Prime p) where
  /-- The compact metric parameter space of the prime configuration model. -/
  Point : Type
  [metricSpace : MetricSpace Point]
  [compactSpace : CompactSpace Point]
  [nonemptyPoint : Nonempty Point]
  [pointAction : MulAction (PrimeSymmetry hp) Point]
  continuous_smul :
    ∀ g : PrimeSymmetry hp, Continuous fun x : Point => g • x
  /-- The continuous map from model points to labelled configurations. -/
  toConfig : C(Point, Config p)
  toConfig_equivariant : IsPrimeEquivariant (hp := hp) toConfig
  /-- The reference continuous map to the zero-sum representation. -/
  reference : C(Point, ZeroSum p)
  reference_equivariant : IsPrimeEquivariant (hp := hp) reference

namespace PrimeConfigurationModel

variable {hp : Nat.Prime p}

attribute [instance] PrimeConfigurationModel.metricSpace
  PrimeConfigurationModel.compactSpace
  PrimeConfigurationModel.nonemptyPoint
  PrimeConfigurationModel.pointAction

@[simp] theorem toConfig_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry hp) (x : M.Point) :
    M.toConfig (g • x) = g • M.toConfig x :=
  M.toConfig_equivariant g x

@[simp] theorem reference_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry hp) (x : M.Point) :
    M.reference (g • x) = g • M.reference x :=
  M.reference_equivariant g x

 theorem smul_eq_self_imp
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry hp) (x : M.Point)
    (h : g • x = x) : g = 1 := by
  apply PrimeSymmetry.config_smul_eq_self_imp g (M.toConfig x)
  calc
    g • M.toConfig x = M.toConfig (g • x) := (M.toConfig_smul g x).symm
    _ = M.toConfig x := by rw [h]

 theorem action_free (M : PrimeConfigurationModel hp) :
    ∀ {g : PrimeSymmetry hp} {x : M.Point}, g • x = x → g = 1 := by
  intro g x h
  exact M.smul_eq_self_imp g x h

/-- Zero set of the model's equivariant reference map. -/
def referenceZeroSet (M : PrimeConfigurationModel hp) : Set M.Point :=
  {x | M.reference x = 0}

 theorem referenceZeroSet_invariant (M : PrimeConfigurationModel hp) :
    IsPrimeInvariant (hp := hp) M.referenceZeroSet :=
  M.reference_equivariant.zeroSet_invariant (fun g =>
    PrimeSymmetry.zeroSumSMulZero.smul_zero g)

 theorem isClosed_referenceZeroSet (M : PrimeConfigurationModel hp) :
    IsClosed M.referenceZeroSet :=
  isClosed_eq M.reference.continuous continuous_const

end PrimeConfigurationModel

end NRR
