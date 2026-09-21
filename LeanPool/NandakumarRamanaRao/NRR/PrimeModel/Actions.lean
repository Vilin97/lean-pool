/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PrimeSymmetry

/-!
# Restricted prime-symmetry actions

All actions use the established relabelling convention `v i = old (σ.symm i)`.
-/

namespace NRR

variable {p : ℕ} {hp : Nat.Prime p}

namespace PrimeSymmetry


instance labelAction : MulAction (PrimeSymmetry p) (Fin p) where
  smul g i := (PrimeSymmetry.toPerm p g) i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem smul_label (g : PrimeSymmetry p) (i : Fin p) :
    g • i = (PrimeSymmetry.toPerm p g) i := rfl

instance configAction : MulAction (PrimeSymmetry p) (Config p) where
  smul g s := Config.relabel (PrimeSymmetry.toPerm p g) s
  one_smul s := Config.relabel_one s
  mul_smul g h s := Config.relabel_mul
    (PrimeSymmetry.toPerm p g) (PrimeSymmetry.toPerm p h) s

@[simp] theorem smul_config (g : PrimeSymmetry p) (s : Config p) :
    g • s = Config.relabel (PrimeSymmetry.toPerm p g) s := rfl

instance coordinateAction : MulAction (PrimeSymmetry p) (Fin p → ℝ) where
  smul g v := fun i => v ((PrimeSymmetry.toPerm p g).symm i)
  one_smul v := by
    funext i
    change v ((PrimeSymmetry.toPerm p 1).symm i) = v i
    rw [map_one]
    rfl
  mul_smul g h v := by funext i; rfl

@[simp] theorem smul_coordinate_apply
    (g : PrimeSymmetry p) (v : Fin p → ℝ) (i : Fin p) :
    (g • v) i = v ((PrimeSymmetry.toPerm p g).symm i) := rfl

instance coordinateSMulZero : SMulZeroClass (PrimeSymmetry p) (Fin p → ℝ) where
  smul_zero g := by funext i; simp

instance zeroSumAction : MulAction (PrimeSymmetry p) (ZeroSum p) where
  smul g v := ZeroSum.relabel (PrimeSymmetry.toPerm p g) v
  one_smul v := ZeroSum.relabel_one v
  mul_smul g h v := ZeroSum.relabel_mul
    (PrimeSymmetry.toPerm p g) (PrimeSymmetry.toPerm p h) v

@[simp] theorem smul_zeroSum_apply
    (g : PrimeSymmetry p) (v : ZeroSum p) (i : Fin p) :
    (g • v) i = v ((PrimeSymmetry.toPerm p g).symm i) := rfl

instance zeroSumSMulZero : SMulZeroClass (PrimeSymmetry p) (ZeroSum p) where
  smul_zero g := by
    apply ZeroSum.ext
    intro i
    simp

 theorem continuous_smul_config (g : PrimeSymmetry p) :
    Continuous fun s : Config p => g • s :=
  Config.continuous_relabel (PrimeSymmetry.toPerm p g)

 theorem continuous_smul_zeroSum (g : PrimeSymmetry p) :
    Continuous fun v : ZeroSum p => g • v :=
  ZeroSum.continuous_relabel (PrimeSymmetry.toPerm p g)

 theorem config_smul_eq_self_imp
    (g : PrimeSymmetry p) (s : Config p) (h : g • s = s) :
    g = 1 := by
  apply PrimeSymmetry.toPerm_injective p
  exact Config.relabel_eq_self_imp (PrimeSymmetry.toPerm p g) s h

 theorem config_action_free :
    ∀ {g : PrimeSymmetry p} {s : Config p}, g • s = s → g = 1 := by
  intro g s h
  exact config_smul_eq_self_imp g s h

end PrimeSymmetry

end NRR
