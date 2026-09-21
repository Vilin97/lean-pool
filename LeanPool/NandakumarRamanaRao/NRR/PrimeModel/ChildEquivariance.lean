/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ModelSites

/-!
# Equivariance of variable-body children

The proof is set-theoretic: normalized weights reindex by `σ.symm`, restricted power cells reindex
by the same convention, and extensionality lifts carrier equality to `ConvexSubbody` and
`BodySpace`.
-/

namespace NRR

open Geometry

variable {n p : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

 theorem EMP.VariableBody.normalizedWeight_relabel
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n)
    (σ : Equiv.Perm (Fin n)) :
    EMP.VariableBody.normalizedWeight hA hn C (Config.relabel σ s) =
      fun i => EMP.VariableBody.normalizedWeight hA hn C s (σ.symm i) := by
  simpa [EMP.VariableBody.normalizedWeight] using
    EMP.normalizedWeight_relabel (EMP.VariableBody.solidBody hA C) hn σ s

 theorem EMP.VariableBody.canonicalCellSet_relabel
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (s : Config n)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    EMP.VariableBody.cellSet hA C (Config.relabel σ s)
      (EMP.VariableBody.normalizedWeight hA hn C (Config.relabel σ s)) i =
    EMP.VariableBody.cellSet hA C s
      (EMP.VariableBody.normalizedWeight hA hn C s) (σ.symm i) := by
  unfold EMP.VariableBody.cellSet
  rw [EMP.VariableBody.normalizedWeight_relabel hA hn C s σ]
  exact PowerDiagram.bodyCellSet_relabel
    (EMP.VariableBody.solidBody hA C) σ s.pts
      (EMP.VariableBody.normalizedWeight hA hn C s) i

variable {hp : Nat.Prime p}

 theorem PrimeConfigurationModel.child_smul
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A) (C : BodySpace K A)
    (g : PrimeSymmetry p) (x : M.Point) (i : Fin p) :
    EMP.VariableBody.child M.sites hA hp.pos (C, g • x) i =
      EMP.VariableBody.child M.sites hA hp.pos (C, x)
        ((PrimeSymmetry.toPerm p g).symm i) := by
  apply Subtype.ext
  apply ConvexSubbody.ext
  change EMP.VariableBody.cellSet hA C (M.sites (g • x))
      (EMP.VariableBody.normalizedWeight hA hp.pos C (M.sites (g • x))) i = _
  change EMP.VariableBody.cellSet hA C (M.toConfig (g • x))
      (EMP.VariableBody.normalizedWeight hA hp.pos C (M.toConfig (g • x))) i = _
  rw [M.toConfig_smul, PrimeSymmetry.smul_config]
  change EMP.VariableBody.cellSet hA C
      (Config.relabel (PrimeSymmetry.toPerm p g) (M.sites x))
      (EMP.VariableBody.normalizedWeight hA hp.pos C
        (Config.relabel (PrimeSymmetry.toPerm p g) (M.sites x))) i = _
  exact EMP.VariableBody.canonicalCellSet_relabel hA hp.pos C (M.sites x)
    (PrimeSymmetry.toPerm p g) i

 theorem PrimeConfigurationModel.child_carrier_smul
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A) (C : BodySpace K A)
    (g : PrimeSymmetry p) (x : M.Point) (i : Fin p) :
    ((EMP.VariableBody.child M.sites hA hp.pos (C, g • x) i).body : Set Plane) =
      ((EMP.VariableBody.child M.sites hA hp.pos (C, x)
        ((PrimeSymmetry.toPerm p g).symm i)).body : Set Plane) := by
  rw [M.child_smul hA C g x i]

end NRR
