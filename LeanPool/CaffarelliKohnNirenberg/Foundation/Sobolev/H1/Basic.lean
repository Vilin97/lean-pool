/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic

/-!
# Representative-level `H¹`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port is the exact `p = 2` facade over the independent CKN
representative-level `W1pFunction` API.

## Main definitions

* `MemL2On` and `GradMemL2On`: scalar and coordinatewise `L²` membership.
* `H1Function`: a concrete scalar representative with a chosen weak gradient.

## Main results

* `H1Function.restrict`: restriction to an open subset.
* The conversion lemmas preserve values and gradients definitionally.
-/

public section

open scoped ENNReal

namespace CKN

/-- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u

/-- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du

/-- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  /-- Chosen scalar representative of the H¹ function. -/
  toFun : Vec d → ℝ
  /-- Chosen weak gradient of the H¹ representative. -/
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Representative-level membership of a concrete function in `H¹(U)`. -/
def MemH1 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H1Function U, v.toFun = u

namespace H1Function

@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

/-- The coordinate weak-derivative identity stored in an `H1Function`. -/
theorem hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

/-- The `i`th chosen gradient component belongs to `L²(U)`. -/
theorem grad_memL2 {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => u.grad x i) :=
  u.gradMemL2 i

/-- The underlying representative belongs to representative-level `H¹(U)`. -/
theorem memH1 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemH1 U u.toFun :=
  ⟨u, rfl⟩

/-- Regard an `H1Function` as the corresponding `W1pFunction` at `p = 2`. -/
@[expose]
def toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

@[simp]
theorem toW1pFunction_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toFun = u.toFun :=
  rfl

@[simp]
theorem toW1pFunction_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.grad = u.grad :=
  rfl

@[simp]
theorem toW1pFunction_apply {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (x : Vec d) :
    u.toW1pFunction x = u x :=
  rfl

end H1Function

namespace W1pFunction

/-- Regard a `W1pFunction` at `p = 2` as the corresponding `H1Function`. -/
@[expose]
def toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient

@[simp]
theorem toH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toFun = u.toFun :=
  rfl

@[simp]
theorem toH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.grad = u.grad :=
  rfl

@[simp]
theorem toH1Function_apply {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) (x : Vec d) :
    u.toH1Function x = u x :=
  rfl

end W1pFunction

namespace H1Function

@[simp]
theorem toH1Function_toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toH1Function = u := by
  apply H1Function.ext <;> rfl

/-- Restrict an `H1Function` to an open subset. -/
@[expose]
def restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function

@[simp]
theorem restrict_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).toFun = u.toFun :=
  rfl

@[simp]
theorem restrict_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).grad = u.grad :=
  rfl

@[simp]
theorem restrict_apply {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U)
    (x : Vec d) :
    u.restrict hVOpen hVU x = u x :=
  rfl

end H1Function

namespace W1pFunction

@[simp]
theorem toW1pFunction_toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toW1pFunction = u := by
  apply W1pFunction.ext <;> rfl

end W1pFunction

end CKN
