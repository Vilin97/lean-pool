/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.FixedVectors

/-!
# Elementary equivariant-map API

This file deliberately stays below the PL and obstruction-theory layers. It records only the
pointwise equations needed by the configuration-model construction.
-/

namespace NRR

variable {p : ℕ} {hp : Nat.Prime p}
variable {X Y Z P : Type*}

/-- A map commuting with the selected prime-symmetry actions. -/
def IsPrimeEquivariant
    [MulAction (PrimeSymmetry hp) X]
    [MulAction (PrimeSymmetry hp) Y]
    (f : X → Y) : Prop :=
  ∀ (g : PrimeSymmetry hp) (x : X), f (g • x) = g • f x

 theorem IsPrimeEquivariant.id
    [MulAction (PrimeSymmetry hp) X] :
    IsPrimeEquivariant (hp := hp) (fun x : X => x) := by
  intro g x
  rfl

 theorem IsPrimeEquivariant.comp
    [MulAction (PrimeSymmetry hp) X]
    [MulAction (PrimeSymmetry hp) Y]
    [MulAction (PrimeSymmetry hp) Z]
    {f : X → Y} {g : Y → Z}
    (hg : IsPrimeEquivariant (hp := hp) g)
    (hf : IsPrimeEquivariant (hp := hp) f) :
    IsPrimeEquivariant (hp := hp) (g ∘ f) := by
  intro a x
  change g (f (a • x)) = a • g (f x)
  rw [hf a x, hg a (f x)]

 theorem IsPrimeEquivariant.const_zero
    [MulAction (PrimeSymmetry hp) X]
    [Zero Y] [MulAction (PrimeSymmetry hp) Y]
    (hzero : ∀ g : PrimeSymmetry hp, g • (0 : Y) = 0) :
    IsPrimeEquivariant (hp := hp) (fun _ : X => (0 : Y)) := by
  intro g x
  exact (hzero g).symm

/-- Invariance of a subset under the selected action. -/
def IsPrimeInvariant
    [MulAction (PrimeSymmetry hp) X]
    (S : Set X) : Prop :=
  ∀ (g : PrimeSymmetry hp) (x : X), x ∈ S → g • x ∈ S

 theorem IsPrimeEquivariant.preimage_invariant
    [MulAction (PrimeSymmetry hp) X]
    [MulAction (PrimeSymmetry hp) Y]
    {f : X → Y} {T : Set Y}
    (hf : IsPrimeEquivariant (hp := hp) f)
    (hT : IsPrimeInvariant (hp := hp) T) :
    IsPrimeInvariant (hp := hp) (f ⁻¹' T) := by
  intro g x hx
  change f (g • x) ∈ T
  rw [hf g x]
  exact hT g (f x) hx

 theorem IsPrimeEquivariant.zeroSet_invariant
    [MulAction (PrimeSymmetry hp) X]
    [Zero Y] [MulAction (PrimeSymmetry hp) Y]
    {f : X → Y} (hf : IsPrimeEquivariant (hp := hp) f)
    (hzero : ∀ g : PrimeSymmetry hp, g • (0 : Y) = 0) :
    IsPrimeInvariant (hp := hp) {x | f x = 0} := by
  intro g x hx
  change f (g • x) = 0
  rw [hf g x, hx]
  exact hzero g

/-- Trivial action on a parameter and the existing action on the second factor. -/
def PrimeSymmetry.smulParamProd
    [MulAction (PrimeSymmetry hp) X]
    (g : PrimeSymmetry hp) (z : P × X) : P × X :=
  (z.1, g • z.2)

theorem PrimeSymmetry.smulParamProd_one
    [MulAction (PrimeSymmetry hp) X] (z : P × X) :
    PrimeSymmetry.smulParamProd (hp := hp) (1 : PrimeSymmetry hp) z = z := by
  ext <;> simp [PrimeSymmetry.smulParamProd]

 theorem PrimeSymmetry.smulParamProd_mul
    [MulAction (PrimeSymmetry hp) X]
    (g h : PrimeSymmetry hp) (z : P × X) :
    PrimeSymmetry.smulParamProd (hp := hp) (g * h) z =
      PrimeSymmetry.smulParamProd (hp := hp) g
        (PrimeSymmetry.smulParamProd (hp := hp) h z) := by
  ext <;> simp [PrimeSymmetry.smulParamProd, mul_smul]

@[simp] theorem PrimeSymmetry.smulParamProd_apply
    [MulAction (PrimeSymmetry hp) X]
    (g : PrimeSymmetry hp) (z : P × X) :
    PrimeSymmetry.smulParamProd (hp := hp) g z = (z.1, g • z.2) := rfl

/-- Pointwise equivariance of a homotopy with a trivially acted-on interval parameter. -/
def IsPrimeEquivariantHomotopy
    [MulAction (PrimeSymmetry hp) X]
    [MulAction (PrimeSymmetry hp) Y]
    (H : X × Set.Icc (0 : ℝ) 1 → Y) : Prop :=
  ∀ (g : PrimeSymmetry hp) (x : X) (t : Set.Icc (0 : ℝ) 1),
    H (g • x, t) = g • H (x, t)

end NRR
