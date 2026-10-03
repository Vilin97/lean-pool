/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import Aesop
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle001
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Zip
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.ContinuousAffineMap.Topology
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.Foundation.Batch002`.
* `GerverSofa.KernelOnly.Foundation.Batch001`.
* `GerverSofa.KernelOnly.PartF.Semantics.Batch001`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `SE2`.
* `SupportingHallway`.
* `Systems`.
* `Boxes`.
* `Geometry`.
-/

public section

noncomputable section

section

/-!
# Orientation-preserving rigid motions of the plane

An element is represented by `(c,s,tₓ,tᵧ)` with `c²+s²=1`.  Its linear
part is the rotation matrix `[[c,-s],[s,c]]`, hence every value is an element
of `SE(2)` and not an arbitrary affine equivalence.
-/

public section

namespace GerverSofa

/-- An orientation-preserving planar rigid motion represented by rotation and translation. -/
structure SE2 where
  /-- The cosine coefficient of the rotation. -/
  c : ℝ
  /-- The sine coefficient of the rotation. -/
  s : ℝ
  /-- The horizontal translation component. -/
  tx : ℝ
  /-- The vertical translation component. -/
  ty : ℝ
  unit : c * c + s * s = 1

namespace SE2

/-- Action of an orientation-preserving rigid motion on the plane. -/
@[expose]
def act (g : SE2) (p : Point) : Point :=
  (g.c * p.1 - g.s * p.2 + g.tx,
   g.s * p.1 + g.c * p.2 + g.ty)

/-- Identity element. -/
@[expose]
def one : SE2 where
  c := 1
  s := 0
  tx := 0
  ty := 0
  unit := by norm_num

/-- Inverse orientation-preserving rigid motion. -/
@[expose]
def inv (g : SE2) : SE2 where
  c := g.c
  s := -g.s
  tx := -(g.c * g.tx + g.s * g.ty)
  ty := g.s * g.tx - g.c * g.ty
  unit := by nlinarith [g.unit]

@[simp] theorem one_act (p : Point) : one.act p = p := by
  rcases p with ⟨x, y⟩
  simp [one, act]

@[simp] theorem inv_act_act (g : SE2) (p : Point) :
    g.inv.act (g.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination x * g.unit
  · dsimp [act, inv]
    linear_combination y * g.unit

@[simp] theorem act_inv_act (g : SE2) (p : Point) :
    g.act (g.inv.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination (x - g.tx) * g.unit
  · dsimp [act, inv]
    linear_combination (y - g.ty) * g.unit

/-- Componentwise continuity is the topology-free representation of a path
in `SE(2)` used by the formal moving-sofa definition. -/
@[expose]
def ContinuousPath (g : ℝ → SE2) : Prop :=
  Continuous (fun t => (g t).c) ∧
  Continuous (fun t => (g t).s) ∧
  Continuous (fun t => (g t).tx) ∧
  Continuous (fun t => (g t).ty)

/-- Inversion preserves continuous `SE(2)` paths. -/
theorem continuousPath_inv {g : ℝ → SE2} (hg : ContinuousPath g) :
    ContinuousPath (fun t => (g t).inv) := by
  rcases hg with ⟨hc, hs, htx, hty⟩
  refine ⟨hc, hs.neg, ?_, ?_⟩
  · exact ((hc.mul htx).add (hs.mul hty)).neg
  · exact (hs.mul htx).sub (hc.mul hty)

end SE2
end GerverSofa

end

end

section

/-!
# Supporting hallway and inverse motion
-/

public section

namespace GerverSofa

/-- World-frame hallway obtained from the standard hallway by `frame`. -/
@[expose]
def supportingHallway (frame : SE2) : Set Point :=
  frame.act '' hallway

/-- Membership in a supporting hallway is equivalent to standard-hallway
membership after applying the inverse frame. -/
theorem mem_supportingHallway_iff (frame : SE2) (q : Point) :
    q ∈ supportingHallway frame ↔ frame.inv.act q ∈ hallway := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hq
    refine ⟨frame.inv.act q, hq, ?_⟩
    exact frame.act_inv_act q

/-- Set-level version of `mem_supportingHallway_iff`. -/
theorem inv_image_subset_hallway_of_subset_supporting
    (frame : SE2) (S : Set Point)
    (hS : S ⊆ supportingHallway frame) :
    frame.inv.act '' S ⊆ hallway := by
  rintro p ⟨q, hqS, rfl⟩
  exact (mem_supportingHallway_iff frame q).1 (hS hqS)

end GerverSofa

end

end

section

/-!
# The concrete reduced and 22-dimensional Romik systems

These are direct Lean transcriptions of equations (F1)--(F4) and of the
independent equations (27)--(39), (41), (43) used by the companion verifier.
-/

public section

namespace GerverSofa

noncomputable section

namespace Reduced

/-- The four real parameters of the reduced Gerver equations. -/
structure Params where
  /-- The first scalar parameter in the reduced equations. -/
  a : ℝ
  /-- The second scalar parameter in the reduced equations. -/
  b : ℝ
  /-- The first switching angle. -/
  phi : ℝ
  /-- The second switching angle. -/
  theta : ℝ

/-- Four-dimensional reduced switching system. -/
@[expose]
def system (p : Params) : Fin 4 → ℝ :=
  let cp := Real.cos p.phi
  let sp := Real.sin p.phi
  let ct := Real.cos p.theta
  let st := Real.sin p.theta
  let delta := p.theta - p.phi
  ![
    p.a * (ct - cp) - 2 * p.b * sp + (delta - 1) * ct - st + cp + sp,
    p.a * (3 * st + sp) - 2 * p.b * cp + 3 * (delta - 1) * st + 3 * ct - sp + cp,
    p.a * cp - sp - (1 / 2 : ℝ) + (1 / 2 : ℝ) * cp - p.b * sp,
    p.a + Real.pi / 2 - p.phi - p.theta - p.b
      + (1 / 2 : ℝ) * delta * (1 + p.a) + (1 / 4 : ℝ) * delta * delta
  ]

/-- The proposition that all four reduced equations vanish. -/
@[expose]
def Equations (p : Params) : Prop := system p = 0

end Reduced

namespace Romik

/-- Translation, phase, and switching-angle parameters of the five Romik branches. -/
structure Params where
  /-- Horizontal translation coefficient for phase 1. -/
  k11 : ℝ
  /-- Vertical translation coefficient for phase 1. -/
  k12 : ℝ
  /-- Horizontal translation coefficient for phase 2. -/
  k21 : ℝ
  /-- Vertical translation coefficient for phase 2. -/
  k22 : ℝ
  /-- Horizontal translation coefficient for phase 3. -/
  k31 : ℝ
  /-- Vertical translation coefficient for phase 3. -/
  k32 : ℝ
  /-- Horizontal translation coefficient for phase 4. -/
  k41 : ℝ
  /-- Vertical translation coefficient for phase 4. -/
  k42 : ℝ
  /-- Horizontal translation coefficient for phase 5. -/
  k51 : ℝ
  /-- Vertical translation coefficient for phase 5. -/
  k52 : ℝ
  /-- Coefficient 1 in the phase 1 closed formula. -/
  a1 : ℝ
  /-- Coefficient 2 in the phase 1 closed formula. -/
  a2 : ℝ
  /-- Coefficient 1 in the phase 2 closed formula. -/
  b1 : ℝ
  /-- Coefficient 2 in the phase 2 closed formula. -/
  b2 : ℝ
  /-- Coefficient 1 in the phase 3 closed formula. -/
  c1 : ℝ
  /-- Coefficient 2 in the phase 3 closed formula. -/
  c2 : ℝ
  /-- Coefficient 1 in the phase 4 closed formula. -/
  d1 : ℝ
  /-- Coefficient 2 in the phase 4 closed formula. -/
  d2 : ℝ
  /-- Coefficient 1 in the phase 5 closed formula. -/
  e1 : ℝ
  /-- Coefficient 2 in the phase 5 closed formula. -/
  e2 : ℝ
  /-- First switching angle. -/
  phi : ℝ
  /-- Second switching angle. -/
  theta : ℝ

/-- Rotation of a body-frame vector into the world frame. -/
@[expose]
def rot (t : ℝ) (z : Point) : Point :=
  (Real.cos t * z.1 - Real.sin t * z.2,
   Real.sin t * z.1 + Real.cos t * z.2)

/-- Translate a point by the two specified coordinate offsets. -/
@[expose]
def addK (r : Point) (kx ky : ℝ) : Point := (r.1 + kx, r.2 + ky)

/-- Phase 1 of the five-phase Gerver path. -/
@[expose]
def path1 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.a1 * Real.cos t + p.a2 * Real.sin t - 1,
     -p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2)
  addK (rot t z) p.k11 p.k12

/-- Phase 2 of the five-phase Gerver path. -/
@[expose]
def path2 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2,
     (1 / 2 : ℝ) * t - p.b1 - 1)
  addK (rot t z) p.k21 p.k22

/-- Phase 3 of the five-phase Gerver path. -/
@[expose]
def path3 (p : Params) (t : ℝ) : Point :=
  addK (rot t (p.c1 - t, p.c2 + t)) p.k31 p.k32

/-- Phase 4 of the five-phase Gerver path. -/
@[expose]
def path4 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 2 : ℝ) * t + p.d1 - 1,
     -(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2)
  addK (rot t z) p.k41 p.k42

/-- Phase 5 of the five-phase Gerver path. -/
@[expose]
def path5 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2,
     -p.e2 * Real.cos t + p.e1 * Real.sin t - 1)
  addK (rot t z) p.k51 p.k52

/-- Body-frame derivative coefficients `(alpha,beta)` on phase 1. -/
@[expose]
def alphaBeta1 (p : Params) (t : ℝ) : Point :=
  (-2 * p.a1 * Real.sin t + 2 * p.a2 * Real.cos t + 1 / 2,
   2 * p.a1 * Real.cos t + 2 * p.a2 * Real.sin t - 1)

/-- Body-frame velocity coordinates for phase 2. -/
@[expose]
def alphaBeta2 (p : Params) (t : ℝ) : Point :=
  (1 + 2 * p.b1 - t,
   -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 + 1 / 2)

/-- Body-frame velocity coordinates for phase 3. -/
@[expose]
def alphaBeta3 (p : Params) (t : ℝ) : Point :=
  (-1 - p.c2 - t, 1 + p.c1 - t)

/-- Body-frame velocity coordinates for phase 4. -/
@[expose]
def alphaBeta4 (p : Params) (t : ℝ) : Point :=
  ((1 / 4 : ℝ) * t * t - p.d1 * t - p.d2 - 1 / 2,
   2 * p.d1 - 1 - t)

/-- Body-frame velocity coordinates for phase 5. -/
@[expose]
def alphaBeta5 (p : Params) (t : ℝ) : Point :=
  (1 - 2 * p.e1 * Real.sin t + 2 * p.e2 * Real.cos t,
   2 * p.e1 * Real.cos t + 2 * p.e2 * Real.sin t - 1 / 2)

/-- Rotate body-frame velocity coordinates into the world frame. -/
@[expose]
def pathPrimeFromAB (t : ℝ) (ab : Point) : Point := rot t ab

/-- World-frame velocity formula for phase 1. -/
@[expose]
def pathPrime1 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta1 p t)
/-- World-frame velocity formula for phase 2. -/
@[expose]
def pathPrime2 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta2 p t)
/-- World-frame velocity formula for phase 3. -/
@[expose]
def pathPrime3 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta3 p t)

/-- Romik's 22 independent scalar equations. -/
@[expose]
def system (p : Params) : Fin 22 → ℝ :=
  let halfPi := Real.pi / 2
  let quarterPi := Real.pi / 4
  let eta := halfPi - p.theta
  let tau := halfPi - p.phi
  let x1phi := path1 p p.phi
  let x2phi := path2 p p.phi
  let v1phi := pathPrime1 p p.phi
  let v2phi := pathPrime2 p p.phi
  let x2theta := path2 p p.theta
  let x3theta := path3 p p.theta
  let v2theta := pathPrime2 p p.theta
  let v3theta := pathPrime3 p p.theta
  let x3eta := path3 p eta
  let x4eta := path4 p eta
  let x4tau := path4 p tau
  let x5tau := path5 p tau
  let abEta := alphaBeta3 p eta
  let bEta : Point :=
    (x3eta.1 - abEta.1 * Real.sin eta,
     x3eta.2 + abEta.1 * Real.cos eta)
  ![
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * (2 * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - 1 + p.a1,
    p.k12 - 1 / 4,
    p.a2 + 1 / 4,
    x1phi.1 - x2phi.1,
    x1phi.2 - x2phi.2,
    v1phi.1 - v2phi.1,
    v1phi.2 - v2phi.2,
    x2theta.1 - x3theta.1,
    x2theta.2 - x3theta.2,
    v2theta.1 - v3theta.1,
    v2theta.2 - v3theta.2,
    x3eta.1 - x4eta.1,
    x3eta.2 - x4eta.2,
    x4tau.1 - x5tau.1,
    x4tau.2 - x5tau.2,
    x1phi.1 - bEta.1,
    x1phi.2 - bEta.2
  ]

/-- The proposition that all 22 independent equations vanish. -/
@[expose]
def Equations (p : Params) : Prop := system p = 0

/-- The physical five-phase path on `[0,π/2]`.  At a switching angle either
adjacent formula may be chosen; the certified matching equations prove they
coincide. -/
@[expose]
def path (p : Params) (t : ℝ) : Point :=
  let eta := Real.pi / 2 - p.theta
  let tau := Real.pi / 2 - p.phi
  if t ≤ p.phi then path1 p t
  else if t ≤ p.theta then path2 p t
  else if t ≤ eta then path3 p t
  else if t ≤ tau then path4 p t
  else path5 p t

/-- Linear normalization from unit time to physical rotation angle. -/
@[expose]
def angle (u : ℝ) : ℝ := u * (Real.pi / 2)

/-- Standard-to-world frame `q ↦ x(t)+R_t q` for normalized time. -/
@[expose]
def frame (p : Params) (u : ℝ) : SE2 :=
  let t := angle u
  let x := path p t
  { c := Real.cos t
    s := Real.sin t
    tx := x.1
    ty := x.2
    unit := by nlinarith [Real.sin_sq_add_cos_sq t] }

@[simp] theorem angle_zero : angle 0 = 0 := by
  simp [angle]

@[simp] theorem angle_one : angle 1 = Real.pi / 2 := by
  simp [angle]

/-- The normalized physical angle depends continuously on time. -/
theorem continuous_angle : Continuous angle := by
  unfold angle
  fun_prop

/-- Continuity of the five-phase path implies componentwise continuity of the
supporting `SE(2)` frame. -/
theorem continuousPath_frame_of_path
    (p : Params) (hpath : Continuous (path p)) :
    SE2.ContinuousPath (frame p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Continuous (fun u : ℝ => Real.cos (angle u))
    simpa [Function.comp_def] using (Real.continuous_cos.comp continuous_angle)
  · change Continuous (fun u : ℝ => Real.sin (angle u))
    simpa [Function.comp_def] using (Real.continuous_sin.comp continuous_angle)
  · change Continuous (fun u : ℝ => (path p (angle u)).1)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.fst
  · change Continuous (fun u : ℝ => (path p (angle u)).2)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.snd

/-! ## Continuity from the independent matching equations -/

/-- Ordering data needed to read the five branches in their intended order. -/
structure SwitchOrder (p : Params) : Prop where
  phi_le_theta : p.phi ≤ p.theta
  theta_le_eta : p.theta ≤ Real.pi / 2 - p.theta
  eta_le_tau : Real.pi / 2 - p.theta ≤ Real.pi / 2 - p.phi

private theorem continuous_path1 (p : Params) : Continuous (path1 p) := by
  unfold path1 addK rot
  fun_prop

private theorem continuous_path2 (p : Params) : Continuous (path2 p) := by
  unfold path2 addK rot
  fun_prop

private theorem continuous_path3 (p : Params) : Continuous (path3 p) := by
  unfold path3 addK rot
  fun_prop

private theorem continuous_path4 (p : Params) : Continuous (path4 p) := by
  unfold path4 addK rot
  fun_prop

private theorem continuous_path5 (p : Params) : Continuous (path5 p) := by
  unfold path5 addK rot
  fun_prop

/-- Equation (35), extracted from the direct 22D system. -/
theorem match_path12_of_equations {p : Params} (heq : Equations p) :
    path1 p p.phi = path2 p p.phi := by
  have h8 := congrFun heq (8 : Fin 22)
  have h9 := congrFun heq (9 : Fin 22)
  simp [system] at h8 h9
  apply Prod.ext <;> linarith

/-- Equation (37), extracted from the direct 22D system. -/
theorem match_path23_of_equations {p : Params} (heq : Equations p) :
    path2 p p.theta = path3 p p.theta := by
  have h12 := congrFun heq (12 : Fin 22)
  have h13 := congrFun heq (13 : Fin 22)
  simp [system] at h12 h13
  apply Prod.ext <;> linarith

/-- Equation (39), extracted from the direct 22D system. -/
theorem match_path34_of_equations {p : Params} (heq : Equations p) :
    path3 p (Real.pi / 2 - p.theta) =
      path4 p (Real.pi / 2 - p.theta) := by
  have h16 := congrFun heq (16 : Fin 22)
  have h17 := congrFun heq (17 : Fin 22)
  simp [system] at h16 h17
  apply Prod.ext <;> linarith

/-- Equation (41), extracted from the direct 22D system. -/
theorem match_path45_of_equations {p : Params} (heq : Equations p) :
    path4 p (Real.pi / 2 - p.phi) =
      path5 p (Real.pi / 2 - p.phi) := by
  have h18 := congrFun heq (18 : Fin 22)
  have h19 := congrFun heq (19 : Fin 22)
  simp [system] at h18 h19
  apply Prod.ext <;> linarith

/-- The four positional matching equations make the literal nested-`if`
five-phase path continuous whenever its switches are ordered. -/
theorem continuous_path_of_order_and_equations
    {p : Params} (hord : SwitchOrder p) (heq : Equations p) :
    Continuous (path p) := by
  have h12 := match_path12_of_equations heq
  have h23 := match_path23_of_equations heq
  have h34 := match_path34_of_equations heq
  have h45 := match_path45_of_equations heq
  have hc45 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path4 p).if_le (continuous_path5 p)
      continuous_id continuous_const (by
        intro t ht
        subst t
        exact h45)
  have hc345 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path3 p).if_le hc45
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.eta_le_tau]
        exact h34)
  have hc2345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path2 p).if_le hc345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.theta_le_eta]
        exact h23)
  have hc12345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.phi then path1 p t
        else if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path1 p).if_le hc2345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.phi_le_theta]
        exact h12)
  unfold path
  exact hc12345

end Romik

end
end GerverSofa

end

end

section

/-!
# Exact real boxes used by the Krawczyk certificates

Every endpoint is written as an exact integer quotient.  There are no binary
floating-point constants in these definitions.
-/

public section

noncomputable section

namespace GerverSofa

/-- Interpret an integer numerator and natural denominator as a real quotient. -/
@[expose]
def qR (n : Int) (d : Nat) : ℝ := (n : ℝ) / (d : ℝ)

namespace Reduced

/-- Input box `X_a × X_b × X_phi × X_theta`. -/
@[expose]
def box : Set Params :=
  {p |
    qR 1888531216873 20000000000000 ≤ p.a ∧ p.a ≤ qR 4721328042183 50000000000000 ∧
    qR 69960186366677 50000000000000 ≤ p.b ∧ p.b ≤ qR 34980093183339 25000000000000 ∧
    qR 122429264969 3125000000000 ≤ p.phi ∧ p.phi ≤ qR 3917736479009 100000000000000 ∧
    qR 2129067216821 3125000000000 ≤ p.theta ∧ p.theta ≤ qR 68130150938273 100000000000000}

end Reduced

namespace Romik

/-- The direct 22-dimensional box `Y × Phi × Theta`. -/
@[expose]
def box : Set Params :=
  {p |
    qR (-21032242207268875141628571849) 100000000000000000000000000000 ≤ p.k11 ∧ p.k11 ≤ qR
      (-21032242207268875141608571849) 100000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.k12 ∧ p.k12 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR (-91917929277159332227479610289) 100000000000000000000000000000 ≤ p.k21 ∧ p.k21 ≤ qR
      (-91917929277159332227459610289) 100000000000000000000000000000 ∧
    qR 29525413734425341573853797657 62500000000000000000000000000 ≤ p.k22 ∧ p.k22 ≤ qR
      29525413734425341573866297657 62500000000000000000000000000 ∧
    qR (-15344080735756291713875357283) 25000000000000000000000000000 ≤ p.k31 ∧ p.k31 ≤ qR
      (-15344080735756291713870357283) 25000000000000000000000000000 ∧
    qR 17792529580064437214538861001 20000000000000000000000000000 ≤ p.k32 ∧ p.k32 ≤ qR
      17792529580064437214542861001 20000000000000000000000000000 ∧
    qR (-15417358304445500741761623987) 50000000000000000000000000000 ≤ p.k41 ∧ p.k41 ≤ qR
      (-15417358304445500741751623987) 50000000000000000000000000000 ∧
    qR 29525413734425341573853797657 62500000000000000000000000000 ≤ p.k42 ∧ p.k42 ≤ qR
      29525413734425341573866297657 62500000000000000000000000000 ∧
    qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ p.k51 ∧ p.k51 ≤ qR
      (-20344080735756291713870857283) 20000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.k52 ∧ p.k52 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR 2420644844145377502832171437 2000000000000000000000000000 ≤ p.a1 ∧ p.a1 ≤ qR
      2420644844145377502832571437 2000000000000000000000000000 ∧
    qR (-2500000000000000000001) 10000000000000000000000 ≤ p.a2 ∧ p.a2 ≤ qR
      (-2499999999999999999999) 10000000000000000000000 ∧
    qR (-52762459802678462416060380937) 100000000000000000000000000000 ≤ p.b1 ∧ p.b1 ≤ qR
      (-52762459802678462416040380937) 100000000000000000000000000000 ∧
    qR 92025838516063762289360579501 100000000000000000000000000000 ≤ p.b2 ∧ p.b2 ≤ qR
      92025838516063762289380579501 100000000000000000000000000000 ∧
    qR 313022761424232933776114655193 500000000000000000000000000000 ≤ p.c1 ∧ p.c1 ≤ qR
      313022761424232933776214655193 500000000000000000000000000000 ∧
    qR (-151160128631428920268654781) 160000000000000000000000000 ≤ p.c2 ∧ p.c2 ≤ qR
      (-151160128631428920268622781) 160000000000000000000000000 ∧
    qR 1641278451780291167220080819 1250000000000000000000000000 ≤ p.d1 ∧ p.d1 ≤ qR
      1641278451780291167220330819 1250000000000000000000000000 ∧
    qR (-105076534082910887440587258861) 200000000000000000000000000000 ≤ p.d2 ∧ p.d2 ≤ qR
      (-105076534082910887440547258861) 200000000000000000000000000000 ∧
    qR 2420644844145377502832171437 2000000000000000000000000000 ≤ p.e1 ∧ p.e1 ≤ qR
      2420644844145377502832571437 2000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.e2 ∧ p.e2 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR 1958868239504182093160893749 50000000000000000000000000000 ≤ p.phi ∧ p.phi ≤ qR
      78354729580167283726435751 2000000000000000000000000000 ∧
    qR 34065075469136244723692787727 50000000000000000000000000000 ≤ p.theta ∧ p.theta ≤ qR
      34065075469136244723692787983 50000000000000000000000000000}

end Romik
end GerverSofa

namespace GerverSofa.Romik

/-- Every point in the certified direct-system box has a positive first
switching angle. -/
theorem phi_pos_of_mem_box {p : Params} (hp : p ∈ box) : 0 < p.phi := by
  dsimp [box, qR] at hp
  have hlo :
      ((1958868239504182093160893749 : ℝ) /
        50000000000000000000000000000) ≤ p.phi := by
    aesop
  have hpositive :
      (0 : ℝ) <
        ((1958868239504182093160893749 : ℝ) /
          50000000000000000000000000000) := by
    norm_num
  exact lt_of_lt_of_le hpositive hlo

/-- Equations (32)--(34), together with the certified box, force the exact
initial path normalisation `x(0)=(0,0)`. -/
theorem path_zero_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    path p 0 = (0, 0) := by
  have hphi : 0 < p.phi := phi_pos_of_mem_box hp
  have h5 := congrFun heq (5 : Fin 22)
  have h6 := congrFun heq (6 : Fin 22)
  have h7 := congrFun heq (7 : Fin 22)
  simp [system] at h5 h6 h7
  have h0phi : (0 : ℝ) ≤ p.phi := le_of_lt hphi
  apply Prod.ext <;>
    simp [path, h0phi, path1, rot, addK] <;>
    linarith

/-- The exact direct-system box orders the four physical switching times. -/
theorem switchOrder_of_mem_box {p : Params} (hp : p ∈ box) : SwitchOrder p := by
  dsimp [box, qR] at hp
  have hphiLo :
      ((1958868239504182093160893749 : ℝ) /
        50000000000000000000000000000) ≤ p.phi := by
    aesop
  have hphiHi :
      p.phi ≤ ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) := by
    aesop
  have hthetaLo :
      ((34065075469136244723692787727 : ℝ) /
        50000000000000000000000000000) ≤ p.theta := by
    aesop
  have hthetaHi :
      p.theta ≤ ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) := by
    aesop
  have hphiTheta : p.phi ≤ p.theta := by
    norm_num at hphiHi hthetaLo
    linarith
  have hthetaEta : p.theta ≤ Real.pi / 2 - p.theta := by
    norm_num at hthetaHi
    nlinarith [Real.pi_gt_three]
  exact
    { phi_le_theta := hphiTheta
      theta_le_eta := hthetaEta
      eta_le_tau := by linarith }

/-- The certified box and the positional equations discharge the path
continuity field needed by the moving-sofa assembly. -/
theorem continuous_path_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    Continuous (path p) :=
  continuous_path_of_order_and_equations (switchOrder_of_mem_box hp) heq

/-- The direct-system box supplies the strict lower bound on `a₁` used in the
area proposition. -/
theorem a1_lower_bound_of_mem_box {p : Params} (hp : p ∈ box) :
    ((2420644844145377502832171437 : ℝ) /
      2000000000000000000000000000) ≤ p.a1 := by
  dsimp [box, qR] at hp
  aesop

end GerverSofa.Romik

end

end

end

section

/-!
# Concrete Gerver cap, niche and fixed sofa

The definitions follow the manuscript literally.  This file also proves the
closedness part of the main topological certificate directly from the
half-plane definitions; it does not use the numerical certificate or Baek's
cap theory.
-/

public section

noncomputable section

namespace GerverSofa

/-- Euclidean scalar product in the fixed coordinate representation. -/
@[expose]
def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

/-- Rotating outer-wall normals. -/
@[expose]
def u (t : ℝ) : Point := (Real.cos t, Real.sin t)
/-- The vertical unit vector rotated counterclockwise through angle `t`. -/
@[expose]
def v (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The lower fan in the manuscript normalisation. -/
@[expose]
def capFan : Set Point := {q | 0 ≤ q.2}

/-- First rotating supporting half-plane. -/
@[expose]
def supportHalfU (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (u t) ≤ dot (Romik.path p t) (u t) + 1}

/-- Second rotating supporting half-plane. -/
@[expose]
def supportHalfV (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (v t) ≤ dot (Romik.path p t) (v t) + 1}

/-- The cap `K₀` reconstructed from the five-phase path. -/
@[expose]
def Romik.K0 (p : Romik.Params) : Set Point :=
  {q | 0 ≤ q.2 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      q ∈ supportHalfU p t ∩ supportHalfV p t}

/-- Open inner quadrant of the supporting hallway at physical angle `t`. -/
@[expose]
def Romik.innerQuadrantAt (p : Romik.Params) (t : ℝ) : Set Point :=
  let x := Romik.path p t
  {q | dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) < 0}

/-- Union of all forbidden inner quadrants at interior rotation times. -/
@[expose]
def Romik.innerUnion (p : Romik.Params) : Set Point :=
  {q | ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), q ∈ Romik.innerQuadrantAt p t}

/-- The niche removed from the cap. -/
@[expose]
def Romik.niche (p : Romik.Params) : Set Point :=
  capFan ∩ Romik.innerUnion p

/-- The fixed Gerver candidate `G = K₀ \ N(K₀)`. -/
@[expose]
def Romik.sofa (p : Romik.Params) : Set Point :=
  Romik.K0 p \ Romik.niche p

/-- Physical supporting hallway at normalized time `s`. -/
@[expose]
def Romik.hallwayAt (p : Romik.Params) (s : ℝ) : Set Point :=
  supportingHallway (Romik.frame p s)

/-! ## Closedness facts independent of the numerical certificate -/

private theorem continuous_dot_fixed (a : Point) :
    Continuous (fun q : Point => dot q a) := by
  unfold dot
  fun_prop

private theorem continuous_shifted_dot (x a : Point) :
    Continuous (fun q : Point => dot (q.1 - x.1, q.2 - x.2) a) := by
  unfold dot
  fun_prop

/-- A fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfU (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfU p t) := by
  change IsClosed ((fun q : Point => dot q (u t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (u t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (u t))

/-- The other fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfV (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfV p t) := by
  change IsClosed ((fun q : Point => dot q (v t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (v t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (v t))

/-- The fan constraint is closed. -/
theorem isClosed_capFan : IsClosed capFan := by
  change IsClosed ((fun q : Point => q.2) ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage continuous_snd

/-- The bounded-quantifier definition of `K₀` as an explicit intersection. -/
theorem Romik.K0_eq_inter_iInter (p : Romik.Params) :
    Romik.K0 p = capFan ∩
      ⋂ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)},
        (supportHalfU p t.1 ∩ supportHalfV p t.1) := by
  ext q
  constructor
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, Set.mem_iInter.mpr ?_⟩
    intro t
    exact hall t.1 t.2
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, ?_⟩
    intro t ht
    exact Set.mem_iInter.mp hall ⟨t, ht⟩

/-- `K₀` is closed, before any support-maximisation or compactness argument. -/
theorem Romik.isClosed_K0 (p : Romik.Params) : IsClosed (Romik.K0 p) := by
  rw [Romik.K0_eq_inter_iInter]
  exact isClosed_capFan.inter <|
    isClosed_iInter fun t =>
      (isClosed_supportHalfU p t.1).inter (isClosed_supportHalfV p t.1)

/-- Every instantaneous inner quadrant is open. -/
theorem Romik.isOpen_innerQuadrantAt (p : Romik.Params) (t : ℝ) :
    IsOpen (Romik.innerQuadrantAt p t) := by
  let x := Romik.path p t
  have hu : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (u t))
  have hv : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (v t))
  change IsOpen
    (((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) ∩
     ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0))
  exact hu.inter hv

/-- The union of all interior-time inner quadrants is open. -/
theorem Romik.isOpen_innerUnion (p : Romik.Params) :
    IsOpen (Romik.innerUnion p) := by
  have hrepr : Romik.innerUnion p =
      ⋃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)},
        Romik.innerQuadrantAt p t.1 := by
    ext q
    constructor
    · rintro ⟨t, ht, hq⟩
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hq⟩
    · intro hq
      rcases Set.mem_iUnion.mp hq with ⟨t, hq⟩
      exact ⟨t.1, t.2, hq⟩
  rw [hrepr]
  exact isOpen_iUnion fun t => Romik.isOpen_innerQuadrantAt p t.1

/-- The cap lies in its fan by definition. -/
theorem Romik.K0_subset_capFan (p : Romik.Params) : Romik.K0 p ⊆ capFan := by
  intro q hq
  exact hq.1

/-- Since `K₀ ⊆ capFan`, removing the niche is the same as removing the open
union of forbidden quadrants. -/
theorem Romik.sofa_eq_K0_diff_innerUnion (p : Romik.Params) :
    Romik.sofa p = Romik.K0 p \ Romik.innerUnion p := by
  ext q
  constructor
  · rintro ⟨hqK, hqN⟩
    refine ⟨hqK, ?_⟩
    intro hqU
    exact hqN ⟨Romik.K0_subset_capFan p hqK, hqU⟩
  · rintro ⟨hqK, hqU⟩
    refine ⟨hqK, ?_⟩
    rintro ⟨_hqFan, hqInner⟩
    exact hqU hqInner

/-- The concrete fixed sofa candidate is closed for every parameter vector. -/
theorem Romik.isClosed_sofa (p : Romik.Params) : IsClosed (Romik.sofa p) := by
  rw [Romik.sofa_eq_K0_diff_innerUnion]
  simpa [Set.sdiff_eq] using
    (Romik.isClosed_K0 p).inter (Romik.isOpen_innerUnion p).isClosed_compl

/-! ## Algebraic hallway characterisation and endpoint assembly -/

@[simp] theorem Romik.mem_supportHalfU (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfU p t ↔
      dot q (u t) ≤ dot (Romik.path p t) (u t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_supportHalfV (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfV p t ↔
      dot q (v t) ≤ dot (Romik.path p t) (v t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_K0 (p : Romik.Params) (q : Point) :
    q ∈ Romik.K0 p ↔
      0 ≤ q.2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        q ∈ supportHalfU p t ∩ supportHalfV p t := Iff.rfl

@[simp] theorem Romik.mem_innerUnion (p : Romik.Params) (q : Point) :
    q ∈ Romik.innerUnion p ↔
      ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        q ∈ Romik.innerQuadrantAt p t := Iff.rfl

@[simp] theorem Romik.mem_niche (p : Romik.Params) (q : Point) :
    q ∈ Romik.niche p ↔ q ∈ capFan ∧ q ∈ Romik.innerUnion p := Iff.rfl

@[simp] theorem Romik.mem_sofa (p : Romik.Params) (q : Point) :
    q ∈ Romik.sofa p ↔ q ∈ Romik.K0 p ∧ q ∉ Romik.niche p := Iff.rfl

/-- The inverse supporting frame has exactly the two signed wall coordinates
used in the manuscript. -/
theorem Romik.frame_inv_act_formula (p : Romik.Params) (s : ℝ) (q : Point) :
    (Romik.frame p s).inv.act q =
      (dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (u (Romik.angle s)),
       dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (v (Romik.angle s))) := by
  apply Prod.ext <;>
    simp [Romik.frame, SE2.inv, SE2.act, dot, u, v] <;> ring

/-- A point is in the supporting hallway iff its two wall coordinates lie in
`Q⁺` but not simultaneously in the open inner quadrant `Q⁻`. -/
theorem Romik.mem_hallwayAt_iff_wall_coordinates
    (p : Romik.Params) (s : ℝ) (q : Point) :
    q ∈ Romik.hallwayAt p s ↔
      let t := Romik.angle s
      let x := Romik.path p t
      (dot (q.1 - x.1, q.2 - x.2) (u t) ≤ 1 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
         dot (q.1 - x.1, q.2 - x.2) (v t) < 0) := by
  rw [Romik.hallwayAt, mem_supportingHallway_iff]
  rw [Romik.frame_inv_act_formula]
  rw [hallway_eq_outer_diff_inner]
  simp [outerQuarter, innerQuarter]

/-- A sofa point cannot lie in an instantaneous forbidden quadrant at an
interior physical time. -/
theorem Romik.not_mem_innerQuadrantAt_of_mem_sofa
    (p : Romik.Params) {q : Point} (hq : q ∈ Romik.sofa p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    q ∉ Romik.innerQuadrantAt p t := by
  intro hinner
  exact hq.2 ⟨Romik.K0_subset_capFan p hq.1, ⟨t, ht, hinner⟩⟩

/-- The lower-fan constraint excludes the initial inner quadrant once the
physical path starts at the origin. -/
theorem Romik.not_mem_initial_innerQuadrant
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0))
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p 0 := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hzero] using hinner.2
  exact (not_lt_of_ge hbase) hneg

/-- The lower-fan constraint excludes the final inner quadrant once the final
path point has second coordinate zero. -/
theorem Romik.not_mem_final_innerQuadrant
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0)
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p (Real.pi / 2) := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hend] using hinner.1
  exact (not_lt_of_ge hbase) hneg

/-- The concrete cap-minus-niche set lies in every supporting hallway.  The
only endpoint input is the pair of path normalisations used in the paper. -/
theorem Romik.sofa_subset_hallwayAt
    (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0))
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Romik.sofa p ⊆ Romik.hallwayAt p s := by
  intro s hs q hq
  rw [Romik.mem_hallwayAt_iff_wall_coordinates]
  dsimp only
  have hangle : Romik.angle s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact mul_nonneg hs.1 (by positivity)
    · have hm := mul_le_mul_of_nonneg_right hs.2
          (show 0 ≤ Real.pi / 2 by positivity)
      simpa [Romik.angle] using hm
  have hsupports := hq.1.2 (Romik.angle s) hangle
  constructor
  · constructor
    · have hu := hsupports.1
      change dot q (u (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (u (Romik.angle s)) + 1 at hu
      dsimp [dot] at hu ⊢
      linarith
    · have hv := hsupports.2
      change dot q (v (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (v (Romik.angle s)) + 1 at hv
      dsimp [dot] at hv ⊢
      linarith
  · change q ∉ Romik.innerQuadrantAt p (Romik.angle s)
    by_cases hs0 : s = 0
    · subst s
      simpa using Romik.not_mem_initial_innerQuadrant p hzero hq
    by_cases hs1 : s = 1
    · subst s
      simpa using Romik.not_mem_final_innerQuadrant p hend hq
    · have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),
          lt_of_le_of_ne hs.2 hs1⟩
      have hangleIoo : Romik.angle s ∈
          Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        constructor
        · exact mul_pos hsIoo.1 (by positivity)
        · have hm := mul_lt_mul_of_pos_right hsIoo.2
              (show 0 < Real.pi / 2 by positivity)
          simpa [Romik.angle] using hm
      exact Romik.not_mem_innerQuadrantAt_of_mem_sofa p hq hangleIoo

/-- The inverse frame at time zero places the concrete sofa in the horizontal
arm. -/
theorem Romik.initial_arm_of_path_zero
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0)) :
    ((Romik.frame p 0).inv.act '' Romik.sofa p) ⊆ horizontalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor <;> positivity
  have hs := hq.1.2 0 htime
  have hx : q.1 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hzero] using hu
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hv := hs.2
    simpa [supportHalfV, dot, v, hzero] using hv
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, hzero, dot, u, v, horizontalArm] using
    (show q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1 from ⟨hx, hy0, hy1⟩)

/-- The inverse frame at time one places the concrete sofa in the vertical
arm. -/
theorem Romik.final_arm_of_path_end_y_zero
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ((Romik.frame p 1).inv.act '' Romik.sofa p) ⊆ verticalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · positivity
    · rfl
  have hs := hq.1.2 (Real.pi / 2) htime
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hend] using hu
  have hv := hs.2
  have hv1 :
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1 := by
    change dot q (v (Real.pi / 2)) ≤
      dot (Romik.path p (Real.pi / 2)) (v (Real.pi / 2)) + 1 at hv
    dsimp [dot] at hv ⊢
    linarith
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, dot, u, v, hend, verticalArm] using
    (show 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1
      from ⟨hy0, hy1, hv1⟩)

end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.AlternatingSeries`.
* `KernelOnly.Coordinates`.
* `KernelOnly.EndpointSymmetry`.
* `KernelOnly.Identification`.
* `KernelOnly.ReplayConsequences`.
* `KernelOnly.SoundnessInterfaces`.
* `KernelOnly.TranscendentalSoundness`.
* `KernelOnly.ADCoreSoundness`.
* `KernelOnly.ReducedADSoundness`.
* `KernelOnly.FullADSoundness`.
-/

public section

noncomputable section

section

/-!
# Alternating-series kernel for the executable transcendental layer

This file connects the exact rational partial sums used by `ExactReplay` to
Mathlib's real power-series theorems.  The Taylor evaluator is intentionally
used only on arguments in `[0, 1]`; the range-reduction layer proves this
precondition before calling these results.
-/

public section

noncomputable section

namespace GerverSofa.ExactReplay

open scoped BigOperators
open Filter Finset

/-- Real magnitude of the `n`th sine-series term. -/
@[expose]
def sinMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

/-- Real magnitude of the `n`th cosine-series term. -/
@[expose]
def cosMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

/-- Real magnitude of the `n`th arctangent-series term. -/
def atanMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- On `[0,1]`, the unsigned sine Taylor terms decrease. -/
theorem antitone_sinMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [sinMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned cosine Taylor terms decrease. -/
theorem antitone_cosMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [cosMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned arctangent Taylor terms decrease. -/
theorem antitone_atanMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (atanMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [atanMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast (show 2 * n + 1 ≤ 2 * (n + 1) + 1 by omega)

/-- Casting the executable sine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_sinPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.sinPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          (Nat.factorial (2 * k + 1) : ℝ) := by
  simp only [sinPartial, signedTerm, factorialQ, Rat.cast_sum, neg_one_pow_eq_ite, Nat.even_iff,
    ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable cosine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_cosPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.cosPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) /
          (Nat.factorial (2 * k) : ℝ) := by
  simp only [cosPartial, signedTerm, factorialQ, Rat.cast_sum, neg_one_pow_eq_ite, Nat.even_iff,
    ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable arctangent partial sum to `ℝ` gives the
corresponding Mathlib finite Taylor sum. -/
theorem coe_atanPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          ((2 * k + 1 : ℕ) : ℝ) := by
  simp only [atanPartial, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Rat.cast_sum,
    neg_one_pow_eq_ite, Nat.even_iff, ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- The 20-term sine partial sum is a lower bound and the 19-term partial sum
is an upper bound for every rational argument in `[0,1]`. -/
theorem sine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.sinPartial x 20 : ℚ) : ℝ) ≤ Real.sin (x : ℝ) ∧
      Real.sin (x : ℝ) ≤ ((GerverSofa.ExactReplay.sinPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (sinMagnitude (x : ℝ)) :=
    antitone_sinMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_sin (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * sinMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.sin (x : ℝ))) := by
    simpa only [sinMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h19] using hupper

/-- The 20-term cosine partial sum is a lower bound and the 19-term partial
sum is an upper bound for every rational argument in `[0,1]`. -/
theorem cosine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.cosPartial x 20 : ℚ) : ℝ) ≤ Real.cos (x : ℝ) ∧
      Real.cos (x : ℝ) ≤ ((GerverSofa.ExactReplay.cosPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (cosMagnitude (x : ℝ)) :=
    antitone_cosMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_cos (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * cosMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.cos (x : ℝ))) := by
    simpa only [cosMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h19] using hupper

/-- Even/odd arctangent partial sums provide certified lower/upper bounds. -/
theorem arctan_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x < 1) (k : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x (2 * k + 2) : ℚ) : ℝ) ≤ Real.arctan (x : ℝ) ∧
      Real.arctan (x : ℝ) ≤ ((GerverSofa.ExactReplay.atanPartial x (2 * k + 1) : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hx1le : (x : ℝ) ≤ 1 := hx1r.le
  have habs : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0r]
    exact hx1r
  have hanti : Antitone (atanMagnitude (x : ℝ)) :=
    antitone_atanMagnitude hx0r hx1le
  have htendRaw := (Real.hasSum_arctan habs).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * atanMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.arctan (x : ℝ))) := by
    simpa only [atanMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti (k + 1)
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti k
  constructor
  · rw [coe_atanPartial]
    have hidx : 2 * (k + 1) = 2 * k + 2 := by omega
    simpa only [atanMagnitude, mul_div_assoc, hidx] using hlower
  · rw [coe_atanPartial]
    simpa only [atanMagnitude, mul_div_assoc] using hupper

end GerverSofa.ExactReplay

end

end

end

section

/-!
# Coordinate equivalences for the certified systems

The executable interval layer works with `Fin n → ℝ`, while the manuscript
layer uses named parameter records.  These equivalences are the explicit,
kernel-checked bridge between the two representations.
-/

public section

noncomputable section

namespace GerverSofa

namespace Reduced

/-- Named reduced parameters as a four-vector in manuscript order. -/
def coordEquiv : Params ≃ Vec 4 where
  toFun p := ![p.a, p.b, p.phi, p.theta]
  invFun x :=
    { a := x 0
      b := x 1
      phi := x 2
      theta := x 3 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Reduced system expressed in finite-vector coordinates. -/
def vectorSystem (x : Vec 4) : Vec 4 :=
  system (coordEquiv.symm x)

/-- The reduced parameter box expressed in finite-vector coordinates. -/
def vectorBox : Set (Vec 4) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 4) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named reduced
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique_iff y hy := by
    constructor
    · intro hEq
      have hyVec : coordEquiv y ∈ vectorBox := by
        simpa [vectorBox] using hy
      have hzero : vectorSystem (coordEquiv y) = 0 := by
        simpa [Equations, vectorSystem] using hEq
      have h := c.unique (coordEquiv y) hyVec hzero
      apply coordEquiv.injective
      simpa using h
    · rintro rfl
      simpa [Equations, vectorSystem] using c.satisfies

end Reduced

namespace Romik

/-- Named Romik parameters as a 22-vector in verifier order. -/
@[expose]
def coordEquiv : Params ≃ Vec 22 where
  toFun p := ![
    p.k11, p.k12, p.k21, p.k22, p.k31, p.k32, p.k41, p.k42, p.k51, p.k52,
    p.a1, p.a2, p.b1, p.b2, p.c1, p.c2, p.d1, p.d2, p.e1, p.e2,
    p.phi, p.theta
  ]
  invFun x :=
    { k11 := x 0
      k12 := x 1
      k21 := x 2
      k22 := x 3
      k31 := x 4
      k32 := x 5
      k41 := x 6
      k42 := x 7
      k51 := x 8
      k52 := x 9
      a1 := x 10
      a2 := x 11
      b1 := x 12
      b2 := x 13
      c1 := x 14
      c2 := x 15
      d1 := x 16
      d2 := x 17
      e1 := x 18
      e2 := x 19
      phi := x 20
      theta := x 21 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Direct Romik system expressed in finite-vector coordinates. -/
@[expose]
def vectorSystem (x : Vec 22) : Vec 22 :=
  system (coordEquiv.symm x)

/-- The direct Romik box expressed in finite-vector coordinates. -/
@[expose]
def vectorBox : Set (Vec 22) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 22) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named Romik
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique_iff y hy := by
    constructor
    · intro hEq
      have hyVec : coordEquiv y ∈ vectorBox := by
        simpa [vectorBox] using hy
      have hzero : vectorSystem (coordEquiv y) = 0 := by
        simpa [Equations, vectorSystem] using hEq
      have h := c.unique (coordEquiv y) hyVec hzero
      apply coordEquiv.injective
      simpa using h
    · rintro rfl
      simpa [Equations, vectorSystem] using c.satisfies

end Romik

end GerverSofa

end

end

end

section

/-!
# Endpoint symmetry derived from the direct 22-dimensional system

The manuscript obtains the terminal condition `x₂(π/2)=0` from the reflection
symmetry of the five phases.  This file proves the required consequence
without introducing a symmetry assumption and without using numerical
approximations.

FIX12 keeps the BATCH11 mathematics and public theorem statements unchanged,
but factors the formula-level algebra into small coordinate identities.  This
avoids asking `ring` to normalize the fully unfolded five-phase expressions in
one large proof term.
-/

/-! ## Exact parameter consequences of equations 27--34 -/

public section

noncomputable section

namespace GerverSofa.Romik

/-- Equation 27. -/
theorem e1_eq_a1_of_equations {p : Params} (heq : Equations p) :
    p.e1 = p.a1 := by
  have h0 := congrFun heq (0 : Fin 22)
  simp [system] at h0
  linarith

/-- Equation 28. -/
theorem e2_eq_neg_a2_of_equations {p : Params} (heq : Equations p) :
    p.e2 = -p.a2 := by
  have h1 := congrFun heq (1 : Fin 22)
  simp [system] at h1
  linarith

/-- Equation 29. -/
theorem d1_eq_quarterPi_sub_b1_of_equations
    {p : Params} (heq : Equations p) :
    p.d1 = Real.pi / 4 - p.b1 := by
  have h2 := congrFun heq (2 : Fin 22)
  simp [system] at h2
  linarith

/-- Equation 30. -/
theorem d2_eq_b2_add_quarterPi_correction_of_equations
    {p : Params} (heq : Equations p) :
    p.d2 = p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4) := by
  have h3 := congrFun heq (3 : Fin 22)
  simp [system] at h3
  linarith

/-- Equation 31. -/
theorem c2_eq_c1_sub_halfPi_of_equations
    {p : Params} (heq : Equations p) :
    p.c2 = p.c1 - Real.pi / 2 := by
  have h4 := congrFun heq (4 : Fin 22)
  simp [system] at h4
  linarith

/-- Equation 33. -/
theorem k12_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k12 = (1 / 4 : ℝ) := by
  have h6 := congrFun heq (6 : Fin 22)
  simp [system] at h6
  linarith

/-- Equation 34. -/
theorem a2_eq_neg_quarter_of_equations {p : Params} (heq : Equations p) :
    p.a2 = -(1 / 4 : ℝ) := by
  have h7 := congrFun heq (7 : Fin 22)
  simp [system] at h7
  linarith

/-- Equations 28 and 34. -/
theorem e2_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.e2 = (1 / 4 : ℝ) := by
  rw [e2_eq_neg_a2_of_equations heq, a2_eq_neg_quarter_of_equations heq]
  norm_num

/-! ## Small definitional coordinate identities

These are deliberately `rfl`: they expose only the second coordinate of one
phase at a time.  Downstream algebra therefore operates on compact scalar
expressions rather than on the fully unfolded `Point`/`rot`/`addK` terms. -/

private theorem path1_snd_formula (p : Params) (t : ℝ) :
    (path1 p t).2 =
      Real.sin t *
          (p.a1 * Real.cos t + p.a2 * Real.sin t - 1) +
        Real.cos t *
          (-p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2) +
        p.k12 := by
  rfl

private theorem path2_snd_formula (p : Params) (t : ℝ) :
    (path2 p t).2 =
      Real.sin t *
          (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2) +
        Real.cos t *
          ((1 / 2 : ℝ) * t - p.b1 - 1) +
        p.k22 := by
  rfl

private theorem path3_snd_formula (p : Params) (t : ℝ) :
    (path3 p t).2 =
      Real.sin t * (p.c1 - t) +
        Real.cos t * (p.c2 + t) +
        p.k32 := by
  rfl

private theorem path4_snd_formula (p : Params) (t : ℝ) :
    (path4 p t).2 =
      Real.sin t *
          (-(1 / 2 : ℝ) * t + p.d1 - 1) +
        Real.cos t *
          (-(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2) +
        p.k42 := by
  rfl

private theorem path5_snd_formula (p : Params) (t : ℝ) :
    (path5 p t).2 =
      Real.sin t *
          (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2) +
        Real.cos t *
          (-p.e2 * Real.cos t + p.e1 * Real.sin t - 1) +
        p.k52 := by
  rfl

/-! ## Formula-level reflection identities -/

/-- The vertical phase-5 formula at reflected time differs from phase 1 only
by its vertical translation constant. -/
theorem phase15_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path5 p (Real.pi / 2 - t)).2 - p.k52 =
      (path1 p t).2 - p.k12 := by
  rw [path5_snd_formula, path1_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [e1_eq_a1_of_equations heq, e2_eq_neg_a2_of_equations heq]
  ring

/-- The vertical phase-4 formula at reflected time differs from phase 2 only
by its vertical translation constant. -/
theorem phase24_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path4 p (Real.pi / 2 - t)).2 - p.k42 =
      (path2 p t).2 - p.k22 := by
  rw [path4_snd_formula, path2_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [d1_eq_quarterPi_sub_b1_of_equations heq,
    d2_eq_b2_add_quarterPi_correction_of_equations heq]
  have hlinear :
      -(1 / 2 : ℝ) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) - 1 =
        (1 / 2 : ℝ) * t - p.b1 - 1 := by
    ring
  have hquadratic :
      -(1 / 4 : ℝ) * (Real.pi / 2 - t) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) * (Real.pi / 2 - t) +
          (p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4)) =
        -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 := by
    ring
  rw [hlinear, hquadratic]
  ring

/-- The middle phase has exact vertical reflection symmetry. -/
theorem phase3_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path3 p (Real.pi / 2 - t)).2 = (path3 p t).2 := by
  rw [path3_snd_formula, path3_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  have hleft :
      p.c1 - (Real.pi / 2 - t) = p.c2 + t := by
    rw [hc2]
    ring
  have hright :
      p.c2 + (Real.pi / 2 - t) = p.c1 - t := by
    rw [hc2]
    ring
  rw [hleft, hright]
  ring

/-! ## Translation constants forced by matching -/

/-- Matching at `θ` and `π/2-θ`, together with middle-phase reflection,
forces the phase-2 and phase-4 vertical translations to coincide. -/
theorem k42_eq_k22_of_equations {p : Params} (heq : Equations p) :
    p.k42 = p.k22 := by
  have h23 : (path2 p p.theta).2 = (path3 p p.theta).2 :=
    congrArg Prod.snd (match_path23_of_equations heq)
  have h34 : (path3 p (Real.pi / 2 - p.theta)).2 =
      (path4 p (Real.pi / 2 - p.theta)).2 :=
    congrArg Prod.snd (match_path34_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.theta
  have h33 := phase3_vertical_reflection_of_equations heq p.theta
  rw [← h34, h33, ← h23] at h24
  linarith

/-- Matching at `φ` and `π/2-φ` then forces the phase-1 and phase-5 vertical
translations to coincide. -/
theorem k52_eq_k12_of_equations {p : Params} (heq : Equations p) :
    p.k52 = p.k12 := by
  have h12 : (path1 p p.phi).2 = (path2 p p.phi).2 :=
    congrArg Prod.snd (match_path12_of_equations heq)
  have h45 : (path4 p (Real.pi / 2 - p.phi)).2 =
      (path5 p (Real.pi / 2 - p.phi)).2 :=
    congrArg Prod.snd (match_path45_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.phi
  have hk := k42_eq_k22_of_equations heq
  rw [hk] at h24
  have hy42 :
      (path4 p (Real.pi / 2 - p.phi)).2 = (path2 p p.phi).2 := by
    linarith
  have hy51 :
      (path5 p (Real.pi / 2 - p.phi)).2 = (path1 p p.phi).2 := by
    calc
      (path5 p (Real.pi / 2 - p.phi)).2 =
          (path4 p (Real.pi / 2 - p.phi)).2 := by
            exact h45.symm
      _ = (path2 p p.phi).2 := hy42
      _ = (path1 p p.phi).2 := h12.symm
  have h15 := phase15_vertical_reflection_of_equations heq p.phi
  rw [hy51] at h15
  linarith

/-- Equations 27--41 force the previously dependent coefficient `k₅₂=1/4`.
It is not an independent hypothesis of the final certificate. -/
theorem k52_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k52 = (1 / 4 : ℝ) := by
  rw [k52_eq_k12_of_equations heq, k12_eq_quarter_of_equations heq]

/-! ## Terminal condition -/

/-- The explicit fifth phase ends at vertical coordinate zero. -/
theorem path5_end_y_zero_of_equations {p : Params} (heq : Equations p) :
    (path5 p (Real.pi / 2)).2 = 0 := by
  rw [path5_snd_formula]
  simp [e2_eq_quarter_of_equations heq,
    k52_eq_quarter_of_equations heq]; norm_num

/-- The certified direct-system box places `π/2` strictly after the fourth
switch, so the literal nested-`if` path uses phase 5 at the endpoint. -/
theorem path_halfPi_eq_path5_of_mem_box {p : Params} (hp : p ∈ box) :
    path p (Real.pi / 2) = path5 p (Real.pi / 2) := by
  have hphi : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have hthetaPos : 0 < p.theta := lt_of_lt_of_le hphi hord.phi_le_theta
  have hthetaLt : p.theta < Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiLt : p.phi < Real.pi / 2 :=
    lt_of_le_of_lt hord.phi_le_theta hthetaLt
  have hetaLt : Real.pi / 2 - p.theta < Real.pi / 2 := by
    linarith
  have htauLt : Real.pi / 2 - p.phi < Real.pi / 2 := by
    linarith
  simp [path, not_le.mpr hphiLt, not_le.mpr hthetaLt,
    not_le.mpr hetaLt, not_le.mpr htauLt]

/-- The terminal vertical normalisation is a theorem of the concrete box and
22 equations.  No reflection hypothesis and no certificate field remain. -/
theorem path_end_y_zero_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    (path p (Real.pi / 2)).2 = 0 := by
  rw [path_halfPi_eq_path5_of_mem_box hp]
  exact path5_end_y_zero_of_equations heq

end GerverSofa.Romik

end

end

end

section

/-!
# Identification with Romik's hallway-intersection reconstruction

This is the set-theoretic part of Proposition `prop:gerver`.  It uses only the
literal definitions and the two endpoint normalisations; the eighteen-piece
boundary statement remains a separate field of `FullArticleCertificate`.
-/

public section

noncomputable section

namespace GerverSofa.Romik

/-- Romik's fixed-frame reconstruction: initial arm, every supporting hallway,
and the final transported vertical arm. -/
@[expose]
def reconstructedSet (p : Params) : Set Point :=
  {q | q ∈ horizontalArm ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) ∧
    q ∈ (frame p 1).act '' verticalArm}

/-- Convert a physical angle in `[0,π/2]` to normalized time. -/
def normalizedTime (t : ℝ) : ℝ := t / (Real.pi / 2)

@[simp] theorem angle_normalizedTime (t : ℝ) :
    angle (normalizedTime t) = t := by
  have hT : Real.pi / 2 ≠ 0 := by positivity
  simp [angle, normalizedTime, hT]

theorem normalizedTime_mem_unit {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    normalizedTime t ∈ Set.Icc (0 : ℝ) 1 := by
  have hT : 0 < Real.pi / 2 := by positivity
  constructor
  · exact div_nonneg ht.1 (le_of_lt hT)
  · exact (div_le_iff₀ hT).2 (by simpa using ht.2)

/-- Every point of the cap-minus-niche set lies in Romik's hallway
intersection reconstruction. -/
theorem sofa_subset_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p ⊆ reconstructedSet p := by
  intro q hq
  refine ⟨?_, ?_, ?_⟩
  · have hi : (frame p 0).inv.act q ∈ horizontalArm :=
      initial_arm_of_path_zero p hzero ⟨q, hq, rfl⟩
    simpa [frame, angle, hzero, SE2.inv, SE2.act] using hi
  · intro s hs
    exact sofa_subset_hallwayAt p hzero hend s hs hq
  · have hf : (frame p 1).inv.act q ∈ verticalArm :=
      final_arm_of_path_end_y_zero p hend ⟨q, hq, rfl⟩
    exact ⟨(frame p 1).inv.act q, hf, (frame p 1).act_inv_act q⟩

/-- Membership in every physical supporting hallway gives all outer support
inequalities in the cap definition. -/
theorem mem_K0_of_mem_all_hallways
    (p : Params) {q : Point}
    (hbase : 0 ≤ q.2)
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∈ K0 p := by
  refine ⟨hbase, ?_⟩
  intro t ht
  let s := normalizedTime t
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit ht
  have hhall := hall s hs
  have hwall :
      (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) ≤ 1 ∧
       dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    rw [mem_hallwayAt_iff_wall_coordinates] at hhall
    simpa [s] using hhall
  constructor
  · change dot q (u t) ≤ dot (path p t) (u t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.1]
  · change dot q (v t) ≤ dot (path p t) (v t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.2]

/-- Membership in every physical hallway excludes every open interior-time
inner quadrant. -/
theorem not_mem_innerUnion_of_mem_all_hallways
    (p : Params) {q : Point}
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∉ innerUnion p := by
  rintro ⟨t, ht, hinner⟩
  let s := normalizedTime t
  have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit htIcc
  have hhall := hall s hs
  rw [mem_hallwayAt_iff_wall_coordinates] at hhall
  have hwall :
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    simpa [s] using hhall.2
  exact hwall (by simpa [innerQuadrantAt] using hinner)

/-- Conversely, Romik's hallway intersection lies in the concrete
cap-minus-niche set. -/
theorem reconstructedSet_subset_sofa (p : Params) :
    reconstructedSet p ⊆ sofa p := by
  intro q hq
  have hbase : 0 ≤ q.2 := hq.1.2.1
  have hK : q ∈ K0 p := mem_K0_of_mem_all_hallways p hbase hq.2.1
  have hU : q ∉ innerUnion p :=
    not_mem_innerUnion_of_mem_all_hallways p hq.2.1
  refine ⟨hK, ?_⟩
  rintro ⟨_hfan, hinner⟩
  exact hU hinner

/-- Set-theoretic identification `G = Sₓ`, conditional only on the endpoint
normalisations already isolated by the main certificate. -/
theorem sofa_eq_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p = reconstructedSet p := by
  apply Set.Subset.antisymm
  · exact sofa_subset_reconstructedSet p hzero hend
  · exact reconstructedSet_subset_sofa p

end GerverSofa.Romik

end

end

end

section

/-!
# Named consequences of the frozen kernel-only certificate

These handles intentionally reason about the proof-carrying rational data, not
about re-running the expensive Krawczyk/grid search inside kernel reduction.
The latter remains available under `ExactReplay.executable*` for independent
diagnostic comparison.
-/

public section

namespace GerverSofa.CertificateManifest
theorem machin_inside_declared :
    RatInterval.strictInsideB machinPi declaredPi = true := by
  simpa [piCheck] using piCheck_eq_true

end GerverSofa.CertificateManifest

end

end

section

/-!
# Semantic interfaces for the executable interval certificate

These definitions state, without hiding any mathematical assumption, the
bridges that turn the frozen rational replay into facts about `Real.sin`,
`Real.cos`, the two real systems, and their Jacobians.  Concrete proof terms
for these interfaces are the remaining analytic part of the end-to-end
certificate; no axiom is declared here.
-/

public section

noncomputable section

namespace GerverSofa

open RatInterval

/-- A rational interval list encloses a finite real vector coordinatewise. -/
@[expose]
def EnclosesVec {n : Nat} (box : List RatInterval) (x : Vec n) : Prop :=
  box.length = n ∧
    ∀ i : Fin n, Contains (box.getD i.1 (point 0)) (x i)

/-- A one-dimensional real derivative certificate in the classical
difference-quotient form.  This is the exact real specialization of the
right-hand side of Mathlib's `hasDerivAt_iff_tendsto_slope_zero`: it states
that `(f (x+t)-f x)/t` tends to `f'` as `t → 0`, `t ≠ 0`.

Unlike storing raw `HasDerivAt`/`DifferentiableAt`, this proposition contains
no hidden `AddCommGroup`/`Module` instance path for the codomain `ℝ`; this
removes the instance diamond exposed by Lean 4.33 while retaining the full
mathematical meaning of an actual derivative. -/
def RealDerivativeAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => t⁻¹ * (f (x + t) - f x))
    (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
    (nhds f')

/-- Exact analytic correctness required from the executable trigonometric
layer.  The domain is the physical range used by the Gerver certificate. -/
structure TranscendentalSoundness : Prop where
  pi_mem : Contains ExactReplay.declaredPiInterval Real.pi
  sine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.sineInterval z) (Real.sin x)
  cosine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.cosineInterval z) (Real.cos x)

end GerverSofa

end

end

end

section

/-!
# Soundness of the exact transcendental interval evaluator

This file proves the analytic trust bridge omitted by the executable replay:

* the alternating rational arctangent sums enclose the two Machin terms;
* the computed Machin interval encloses `Real.pi` and lies in the declared
  interval;
* fixed-decimal rounding is outward;
* the small-argument Taylor intervals enclose `Real.sin` and `Real.cos`;
* complementary-angle reduction is sound on `[0, π/2]`;
* externally over-wide intervals fail closed to `[-1,1]` rather than silently
  violating the Taylor precondition.

No project axiom and no floating-point literal occurs in this file.
-/

/-! ## Partial-sum interval consequences -/

public section

noncomputable section

namespace GerverSofa.ExactReplay

open RatInterval

/-- The executable sine Taylor hull contains the exact real sine value on
`[0,1]`. -/
theorem sinBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (sinBound x) (Real.sin (x : ℝ)) := by
  have h := sine_between_partials hx0 hx1
  constructor
  · have hmin : min (sinPartial x 19) (sinPartial x 20) ≤ sinPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : sinPartial x 19 ≤ max (sinPartial x 19) (sinPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- The executable cosine Taylor hull contains the exact real cosine value on
`[0,1]`. -/
theorem cosBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (cosBound x) (Real.cos (x : ℝ)) := by
  have h := cosine_between_partials hx0 hx1
  constructor
  · have hmin : min (cosPartial x 19) (cosPartial x 20) ≤ cosPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : cosPartial x 19 ≤ max (cosPartial x 19) (cosPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- Consecutive odd/even arctangent sums form a semantic interval. -/
theorem atanBound_contains {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Contains (atanBound x (2 * k + 1) (2 * k + 2))
      (Real.arctan (x : ℝ)) := by
  have h := arctan_between_partials hx0 hx1 k
  constructor
  · have hmin :
        min (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) ≤
          atanPartial x (2 * k + 2) := min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax :
        atanPartial x (2 * k + 1) ≤
          max (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-! ## Machin identity and the declared interval for π -/

/-- The interval computed from the two exact arctangent Taylor certificates
contains the true value of `π`. -/
theorem machinPi_contains_pi : Contains machinPi Real.pi := by
  have h5 : Contains (atanBound (1 / 5) 43 44)
      (Real.arctan ((1 / 5 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 5 : ℚ)) (by norm_num) (by norm_num) 21)
  have h239 : Contains (atanBound (1 / 239) 13 14)
      (Real.arctan ((1 / 239 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 239 : ℚ)) (by norm_num) (by norm_num) 6)
  have h16 := RatInterval.contains_scale (a := (16 : ℚ)) h5
  have h4 := RatInterval.contains_scale (a := (4 : ℚ)) h239
  have hsub := RatInterval.contains_sub h16 h4
  have hMachin :
      (16 : ℝ) * Real.arctan (1 / 5) -
          4 * Real.arctan (1 / 239) = Real.pi := by
    nlinarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  have hsub' : Contains machinPi
      ((16 : ℝ) * Real.arctan (1 / 5) -
        4 * Real.arctan (1 / 239)) := by
    simpa [machinPi, scale] using hsub
  exact hMachin ▸ hsub'

/-- The executable and proof-carrying manifests contain byte-for-byte equal
Machin intervals.  This is a finite rational normalization, not a numerical
assumption. -/
private theorem ratInterval_eq_of_endpoints {a b : RatInterval}
    (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact lower endpoint agreement between the executable Machin evaluation
and the frozen manifest.  This is a small bounded kernel computation (two
arctangent sums), deliberately separated from the old monolithic replay. -/
private theorem machinPi_lo_eq_manifest :
    machinPi.lo = CertificateManifest.machinPi.lo := by
    decide +kernel

/-- Exact upper endpoint agreement between the executable Machin evaluation
and the frozen manifest. -/
private theorem machinPi_hi_eq_manifest :
    machinPi.hi = CertificateManifest.machinPi.hi := by
    decide +kernel

theorem machinPi_eq_manifest :
    machinPi = CertificateManifest.machinPi :=
  ratInterval_eq_of_endpoints machinPi_lo_eq_manifest machinPi_hi_eq_manifest

/-- The executable declared interval agrees with the frozen manifest. -/
theorem piI_eq_manifest : piI = CertificateManifest.declaredPi := by
  apply ratInterval_eq_of_endpoints
  · decide +kernel
  · decide +kernel

/-- The exact interval used by every transcendental call encloses `Real.pi`. -/
theorem piI_contains_pi : Contains piI Real.pi := by
  have hm : Contains CertificateManifest.machinPi Real.pi := by
    simpa [machinPi_eq_manifest] using machinPi_contains_pi
  have hd : Contains CertificateManifest.declaredPi Real.pi :=
    RatInterval.contains_of_strictInsideB
      CertificateManifest.machin_inside_declared hm
  simpa [piI_eq_manifest] using hd

/-! ## Outward decimal rounding -/

/-- Fixed-decimal floor rounding never exceeds the input rational. -/
theorem floorDecimal_le (x : ℚ) (digits : ℕ := 60) :
    floorDecimal x digits ≤ x := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (div_le_iff₀ hs).2
  have hf : (((⌊x * s⌋ : ℤ) : ℚ)) ≤ x * s := Int.floor_le _
  simpa [floorDecimal, s] using hf

/-- Fixed-decimal ceiling rounding never lies below the input rational. -/
theorem le_ceilDecimal (x : ℚ) (digits : ℕ := 60) :
    x ≤ ceilDecimal x digits := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (le_div_iff₀ hs).2
  have hc : x * s ≤ (((⌈x * s⌉ : ℤ) : ℚ)) := Int.le_ceil _
  simpa [ceilDecimal, s] using hc

/-- The exact 60-decimal conversion is outward in real semantics. -/
theorem outwardDecimal_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) : Contains (outwardDecimal z) x := by
  constructor
  · exact le_trans (by exact_mod_cast floorDecimal_le z.lo (digits := 60)) hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_ceilDecimal z.hi (digits := 60))

/-! ## Small-argument sine and cosine -/

/-- The small sine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem sinSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (sinSmall z) (Real.sin x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := sinBound_contains hz0 hlo1
  have hhiBound := sinBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hloMem : -(Real.pi / 2) ≤ (z.lo : ℝ) := by
    have : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
    nlinarith [Real.pi_pos]
  have hhiMem : (z.hi : ℝ) ≤ Real.pi / 2 := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hmonoLo : Real.sin (z.lo : ℝ) ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hloMem (le_trans hx.2 hhiMem) hx.1
  have hxLower : -(Real.pi / 2) ≤ x := by
    have hneg : -(Real.pi / 2) ≤ (0 : ℝ) := by
      nlinarith [Real.pi_pos]
    exact le_trans hneg (le_trans (by exact_mod_cast hz0) hx.1)
  have hmonoHi : Real.sin x ≤ Real.sin (z.hi : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hxLower hhiMem hx.2
  apply outwardDecimal_contains
  constructor
  · exact le_trans hloBound.1 hmonoLo
  · exact le_trans hmonoHi hhiBound.2

/-- The small cosine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem cosSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (cosSmall z) (Real.cos x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := cosBound_contains hz0 hlo1
  have hhiBound := cosBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlo0 : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
  have hhiPi : (z.hi : ℝ) ≤ Real.pi := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hx0 : (0 : ℝ) ≤ x := le_trans hlo0 hx.1
  have hxPi : x ≤ Real.pi := le_trans hx.2 hhiPi
  have hcosLower : Real.cos (z.hi : ℝ) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx0 hhiPi hx.2
  have hcosUpper : Real.cos x ≤ Real.cos (z.lo : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hlo0 hxPi hx.1
  apply outwardDecimal_contains
  constructor
  · exact le_trans hhiBound.1 hcosLower
  · exact le_trans hcosUpper hloBound.2

/-! ## Range reduction and fail-closed totality -/

/-- Physical clamping preserves every enclosed angle in `[0,π/2]`. -/
theorem physicalClamp_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (physicalClamp z) x := by
  have hpi := piI_contains_pi
  constructor
  · simpa [physicalClamp] using (max_le hx0 hz.1)
  · have hupper : x ≤ ((piI.hi / 2 : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hxhi : x ≤ (piI.hi : ℝ) / 2 := by
        linarith [hxpi, hhi]
      have hcast : (((piI.hi / 2 : ℚ) : ℝ)) = (piI.hi : ℝ) / 2 := by
        norm_num
      rw [hcast]
      exact hxhi
    simpa [physicalClamp] using (le_min hupper hz.2)

/-- Complementary-angle range reduction encloses `π/2-x`. -/
theorem complementInterval_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hxpi : x ≤ Real.pi / 2) :
    Contains (complementInterval z) (Real.pi / 2 - x) := by
  have hpi := piI_contains_pi
  constructor
  · have hzero : 0 ≤ Real.pi / 2 - x := by linarith
    have hdiff : ((piI.lo / 2 - z.hi : ℚ) : ℝ) ≤ Real.pi / 2 - x := by
      have hlo : (piI.lo : ℝ) ≤ Real.pi := hpi.1
      have hdiff' : (piI.lo : ℝ) / 2 - (z.hi : ℝ) ≤ Real.pi / 2 - x := by
        linarith [hlo, hz.2]
      have hcast : (((piI.lo / 2 - z.hi : ℚ) : ℝ)) =
          (piI.lo : ℝ) / 2 - (z.hi : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using (max_le hzero hdiff)
  · have hdiff : Real.pi / 2 - x ≤ ((piI.hi / 2 - z.lo : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hdiff' : Real.pi / 2 - x ≤ (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        linarith [hhi, hz.1]
      have hcast : (((piI.hi / 2 - z.lo : ℚ) : ℝ)) =
          (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using hdiff

/-- Universal fallback for sine. -/
theorem universal_contains_sin (x : ℝ) :
    Contains universalTrigInterval (Real.sin x) := by
  simpa [Contains, universalTrigInterval] using Real.sin_mem_Icc x

/-- Universal fallback for cosine. -/
theorem universal_contains_cos (x : ℝ) :
    Contains universalTrigInterval (Real.cos x) := by
  simpa [Contains, universalTrigInterval] using Real.cos_mem_Icc x

/-- Full soundness of the executable sine interval on the physical angular
range. -/
theorem sinI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (sinI z) (Real.sin x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [sinI]
  split_ifs with hsmall hcomp
  · exact sinSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hcy := cosSmall_contains hy hy0 hcomp
    simpa [Real.cos_pi_div_two_sub] using hcy
  · exact universal_contains_sin x

/-- Full soundness of the executable cosine interval on the physical angular
range. -/
theorem cosI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (cosI z) (Real.cos x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [cosI]
  split_ifs with hsmall hcomp
  · exact cosSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hsy := sinSmall_contains hy hy0 hcomp
    simpa [Real.sin_pi_div_two_sub] using hsy
  · exact universal_contains_cos x

end GerverSofa.ExactReplay

namespace GerverSofa

open RatInterval

end GerverSofa

end

end

end

section

/-!
# Structural soundness of first-order interval automatic differentiation

The executable `ExactReplay.D` object stores a value interval and one interval
for every first partial derivative.  This file supplies the reusable semantic
induction for all constructors actually used by the 4D and 22D certificates.
The concrete systems are handled in a separate module by instantiating these
constructor theorems.
-/

/-! ## Smooth scalar models -/

public section

noncomputable section

namespace GerverSofa

open RatInterval

/-- A scalar function together with its coordinate gradient and a proof that
those coordinates are the actual partial derivatives.  The derivative witness
is stored as `RealDerivativeAt`, a first-principles real difference-quotient
limit.  Constructor proofs temporarily move through Mathlib's `HasDerivAt`
API and immediately return to this instance-stable semantic proposition. -/
structure ScalarModel (n : Nat) where
  /-- The real scalar function represented by the model. -/
  value : Vec n → ℝ
  /-- The coordinate gradient of the scalar function. -/
  gradient : Vec n → Vec n
  hasDeriv_update : ∀ x j,
    RealDerivativeAt (fun t : ℝ => value (Function.update x j t))
      (gradient x j) (x j)

namespace ScalarModel

/-- Constant scalar model. -/
@[expose]
def const (n : Nat) (c : ℝ) : ScalarModel n where
  value := fun _ => c
  gradient := fun _ _ => 0
  hasDeriv_update := by
    intro x j
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hasDerivAt_const (x j) c).tendsto_slope_zero

/-- Coordinate projection. -/
@[expose]
def var (n : Nat) (k : Fin n) : ScalarModel n where
  value := fun x => x k
  gradient := fun _ j => if j = k then 1 else 0
  hasDeriv_update := by
    intro x j
    by_cases h : j = k
    · subst k
      have hid : RealDerivativeAt (fun t : ℝ => t) 1 (x j) := by
        simpa only [RealDerivativeAt, smul_eq_mul] using
          (hasDerivAt_id' (x j)).tendsto_slope_zero
      convert hid using 1 <;> simp
    · have hkj : k ≠ j := Ne.symm h
      simpa only [RealDerivativeAt, Function.update_of_ne hkj, ite_eq_right h,
        smul_eq_mul] using (hasDerivAt_const (x j) (x k)).tendsto_slope_zero

/-- Pointwise addition. -/
@[expose]
def add {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x + g.value x
  gradient := fun x j => f.gradient x j + g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hfh.fun_add hgh).tendsto_slope_zero

/-- Pointwise negation. -/
@[expose]
def neg {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => -f.value x
  gradient := fun x j => -f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      hfh.fun_neg.tendsto_slope_zero

/-- Pointwise subtraction. -/
@[expose]
def sub {n : Nat} (f g : ScalarModel n) : ScalarModel n :=
  add f (neg g)

/-- Pointwise multiplication. -/
@[expose]
def mul {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x * g.value x
  gradient := fun x j =>
    f.gradient x j * g.value x + f.value x * g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      (hfh.fun_mul hgh).tendsto_slope_zero

/-- Rational scaling. -/
@[expose]
def scale {n : Nat} (a : ℚ) (f : ScalarModel n) : ScalarModel n where
  value := fun x => (a : ℝ) * f.value x
  gradient := fun x j => (a : ℝ) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hs := HasDerivAt.const_mul (a : ℝ) hfh
    simpa only [RealDerivativeAt, smul_eq_mul] using hs.tendsto_slope_zero

/-- Sine composition. -/
@[expose]
def sin {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.sin (f.value x)
  gradient := fun x j => Real.cos (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.sin.tendsto_slope_zero

/-- Cosine composition. -/
@[expose]
def cos {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.cos (f.value x)
  gradient := fun x j => -Real.sin (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.cos.tendsto_slope_zero

instance {n : Nat} : Add (ScalarModel n) := ⟨add⟩
instance {n : Nat} : Neg (ScalarModel n) := ⟨neg⟩
instance {n : Nat} : Sub (ScalarModel n) := ⟨sub⟩
instance {n : Nat} : Mul (ScalarModel n) := ⟨mul⟩
instance {n : Nat} : HMul ℚ (ScalarModel n) (ScalarModel n) := ⟨scale⟩

/-! The executable systems are written with notation, while constructor-level
    soundness lemmas produce the named operations above.  These tiny simp
    bridges make that definitional equality explicit without unfolding the
    proof-carrying structures themselves. -/
@[simp] theorem add_notation {n : Nat} (f g : ScalarModel n) :
    f + g = add f g := rfl

@[simp] theorem neg_notation {n : Nat} (f : ScalarModel n) :
    -f = neg f := rfl

@[simp] theorem sub_notation {n : Nat} (f g : ScalarModel n) :
    f - g = sub f g := rfl

@[simp] theorem mul_notation {n : Nat} (f g : ScalarModel n) :
    f * g = mul f g := rfl

@[simp] theorem scale_notation {n : Nat} (a : ℚ) (f : ScalarModel n) :
    a * f = scale a f := rfl

@[simp] theorem add_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (add f g).value x = f.value x + g.value x := rfl

@[simp] theorem neg_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (neg f).value x = -f.value x := rfl

@[simp] theorem sub_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (sub f g).value x = f.value x - g.value x := rfl

@[simp] theorem mul_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (mul f g).value x = f.value x * g.value x := rfl

@[simp] theorem scale_value {n : Nat} (a : ℚ) (f : ScalarModel n) (x : Vec n) :
    (scale a f).value x = (a : ℝ) * f.value x := rfl

@[simp] theorem sin_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (sin f).value x = Real.sin (f.value x) := rfl

@[simp] theorem cos_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (cos f).value x = Real.cos (f.value x) := rfl

end ScalarModel

namespace ExactReplay.D

/-! Matching notation bridges for the executable dual intervals. -/
@[simp] theorem add_notation (x y : ExactReplay.D) :
    x + y = addD x y := rfl

@[simp] theorem neg_notation (x : ExactReplay.D) :
    -x = negD x := rfl

@[simp] theorem sub_notation (x y : ExactReplay.D) :
    x - y = subD x y := rfl

@[simp] theorem mul_notation (x y : ExactReplay.D) :
    x * y = mulD x y := rfl

@[simp] theorem scale_notation (a : ℚ) (x : ExactReplay.D) :
    a * x = scaleD a x := rfl

end ExactReplay.D

/-! ## Semantic relation for the executable dual interval -/

/-- An executable dual interval encloses a smooth scalar model on a set. -/
structure DSoundOn {n : Nat} (X : Set (Vec n))
    (d : ExactReplay.D) (f : ScalarModel n) : Prop where
  value_sound : ∀ x ∈ X, Contains d.val (f.value x)
  derivative_length : d.der.length = n
  derivative_sound : ∀ x ∈ X, ∀ j : Fin n,
    Contains (d.der.getD j.1 ExactReplay.zeroI) (f.gradient x j)

/-! ## List access lemmas used by the AD constructors -/

private theorem getD_map_of_lt
    {α β : Type*} (f : α → β) (xs : List α)
    (i : Nat) (h : i < xs.length) (da : α) (db : β) :
    (xs.map f).getD i db = f (xs.getD i da) := by
  have hmap : i < (xs.map f).length := by simpa using h
  rw [List.getD_eq_getElem (xs.map f) db hmap]
  rw [List.getD_eq_getElem xs da h]
  simp

private theorem getD_zipWith_of_lt
    {α β γ : Type*} (f : α → β → γ)
    (xs : List α) (ys : List β) (i : Nat)
    (hx : i < xs.length) (hy : i < ys.length)
    (da : α) (db : β) (dc : γ) :
    (List.zipWith f xs ys).getD i dc =
      f (xs.getD i da) (ys.getD i db) := by
  have hz : i < (List.zipWith f xs ys).length := by
    simpa only [List.length_zipWith] using (lt_min hx hy)
  rw [List.getD_eq_getElem (List.zipWith f xs ys) dc hz]
  rw [List.getD_eq_getElem xs da hx]
  rw [List.getD_eq_getElem ys db hy]
  simp

/-! ## Constructor soundness -/

/-- Exact interval constant. -/
theorem DSoundOn.const {n : Nat} {X : Set (Vec n)}
    {z : RatInterval} {c : ℝ} (hc : Contains z c) :
    DSoundOn X (ExactReplay.D.const z n) (ScalarModel.const n c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hc
  · simp [ExactReplay.D.const]
  · intro x hx j
    simp [ExactReplay.D.const, ExactReplay.zeroI, ScalarModel.const,
      RatInterval.Contains, RatInterval.point]

/-- Rational point constant. -/
theorem DSoundOn.pointConst {n : Nat} {X : Set (Vec n)} (q : ℚ) :
    DSoundOn X (ExactReplay.D.pointConst q n)
      (ScalarModel.const n (q : ℝ)) := by
  apply DSoundOn.const
  exact (RatInterval.contains_point_iff q (q : ℝ)).2 rfl

/-- Coordinate variable read from an enclosing input interval. -/
theorem DSoundOn.varD {n : Nat} {X : Set (Vec n)}
    (input : RatInterval) (k : Fin n)
    (hinput : ∀ x ∈ X, Contains input (x k)) :
    DSoundOn X (ExactReplay.D.varD input k.1 n) (ScalarModel.var n k) := by
  refine ⟨hinput, ?_, ?_⟩
  · simp [ExactReplay.D.varD]
  · intro x hx j
    have hj : j.1 < (List.range n).length := by simp
    change Contains
      (((List.range n).map
        (fun m => RatInterval.point (if m = k.1 then 1 else 0))).getD
          j.1 ExactReplay.zeroI)
      (if j = k then 1 else 0)
    rw [getD_map_of_lt (fun m => RatInterval.point (if m = k.1 then 1 else 0))
      (List.range n) j.1 hj 0 ExactReplay.zeroI]
    have hjrange : (List.range n).getD j.1 0 = j.1 := by
      rw [List.getD_eq_getElem (List.range n) 0 hj]
      simp
    rw [hjrange]
    by_cases hjk : j = k
    · subst k
      simp [RatInterval.Contains, RatInterval.point]
    · have hval : j.1 ≠ k.1 := by
        intro hval
        exact hjk (Fin.ext hval)
      simp [hjk, hval, RatInterval.Contains, RatInterval.point]

/-- Addition constructor. -/
theorem DSoundOn.add {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.addD dx dy) (ScalarModel.add f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_add (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.addD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simp [hx.derivative_length]
    have hjy : j.1 < dy.der.length := by simp [hy.derivative_length]
    change Contains
      ((List.zipWith RatInterval.add dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j + g.gradient x j)
    rw [getD_zipWith_of_lt RatInterval.add dx.der dy.der j.1 hjx hjy
      ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (hx.derivative_sound x hX j) (hy.derivative_sound x hX j)

/-- Negation constructor. -/
theorem DSoundOn.neg {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.negD d) (ScalarModel.neg f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_neg (h.value_sound x hX)
  · simp [ExactReplay.D.negD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map RatInterval.neg).getD j.1 ExactReplay.zeroI)
      (-f.gradient x j)
    rw [getD_map_of_lt RatInterval.neg d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_neg (h.derivative_sound x hX j)

/-- Subtraction constructor. -/
theorem DSoundOn.sub {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.subD dx dy) (ScalarModel.sub f g) := by
  simpa [ExactReplay.D.subD, ScalarModel.sub] using hx.add hy.neg

/-- Multiplication constructor and product rule. -/
theorem DSoundOn.mul {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.mulD dx dy) (ScalarModel.mul f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_mul (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.mulD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simp [hx.derivative_length]
    have hjy : j.1 < dy.der.length := by simp [hy.derivative_length]
    change Contains
      ((List.zipWith
        (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
          (RatInterval.mul dx.val ddy))
        dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j * g.value x + f.value x * g.gradient x j)
    rw [getD_zipWith_of_lt
      (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
        (RatInterval.mul dx.val ddy))
      dx.der dy.der j.1 hjx hjy ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (RatInterval.contains_mul (hx.derivative_sound x hX j)
        (hy.value_sound x hX))
      (RatInterval.contains_mul (hx.value_sound x hX)
        (hy.derivative_sound x hX j))

/-- Rational scaling constructor. -/
theorem DSoundOn.scale {n : Nat} {X : Set (Vec n)}
    (a : ℚ) {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.scaleD a d) (ScalarModel.scale a f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_scale (h.value_sound x hX)
  · simp [ExactReplay.D.scaleD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (ExactReplay.scale a)).getD j.1 ExactReplay.zeroI)
      ((a : ℝ) * f.gradient x j)
    rw [getD_map_of_lt (ExactReplay.scale a) d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_scale (h.derivative_sound x hX j)

/-- Sine constructor and chain rule. -/
theorem DSoundOn.sin {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.sinD d) (ScalarModel.sin f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.sinI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.sinD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (RatInterval.mul (ExactReplay.cosI d.val))).getD
        j.1 ExactReplay.zeroI)
      (Real.cos (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (RatInterval.mul (ExactReplay.cosI d.val)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_mul
      (ExactReplay.cosI_contains (h.value_sound x hX)
        (hphysical x hX).1 (hphysical x hX).2)
      (h.derivative_sound x hX j)

/-- Cosine constructor and chain rule. -/
theorem DSoundOn.cos {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.cosD d) (ScalarModel.cos f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.cosI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.cosD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (fun z => RatInterval.neg
        (RatInterval.mul (ExactReplay.sinI d.val) z))).getD
        j.1 ExactReplay.zeroI)
      (-Real.sin (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (fun z => RatInterval.neg
      (RatInterval.mul (ExactReplay.sinI d.val) z)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    simpa only [neg_mul] using
      RatInterval.contains_neg (RatInterval.contains_mul
        (ExactReplay.sinI_contains (h.value_sound x hX)
          (hphysical x hX).1 (hphysical x hX).2)
        (h.derivative_sound x hX j))

end GerverSofa

end

end

end

section

/-!
# Concrete interval-AD soundness for the reduced 4D system

This module instantiates the constructor-level AD theorem with equations
(F1)--(F4), proves that the frozen rational list is exactly the manuscript box,
and identifies the four smooth scalar models with `Reduced.vectorSystem`.
-/

public section

noncomputable section

namespace GerverSofa

open RatInterval

namespace Reduced

/-- The four frozen rational intervals are exactly the named reduced box. -/
theorem inputBox_exact (x : Vec 4) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.reducedInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, qR, coordEquiv] at hx
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4]
    · intro i
      fin_cases i <;>
        simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
          CertificateManifest.q, RatInterval.Contains] <;>
        aesop
  · rintro ⟨hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, qR, coordEquiv]
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, RatInterval.Contains] at h0 h1 h2 h3
    aesop

/-- Scalar models matching the four reduced equations. -/
@[expose]
def models : Fin 4 → ScalarModel 4 :=
  let a := ScalarModel.var 4 (0 : Fin 4)
  let b := ScalarModel.var 4 (1 : Fin 4)
  let phi := ScalarModel.var 4 (2 : Fin 4)
  let theta := ScalarModel.var 4 (3 : Fin 4)
  let one := ScalarModel.const 4 1
  let half := ScalarModel.const 4 (1 / 2 : ℝ)
  let quarter := ScalarModel.const 4 (1 / 4 : ℝ)
  let piM := ScalarModel.const 4 Real.pi
  let cp := ScalarModel.cos phi
  let sp := ScalarModel.sin phi
  let ct := ScalarModel.cos theta
  let st := ScalarModel.sin theta
  let delta := theta - phi
  let f1 := a * (ct - cp) - (2 : ℚ) * b * sp + (delta - one) * ct - st + cp + sp
  let f2 := a * ((3 : ℚ) * st + sp) - (2 : ℚ) * b * cp
    + (3 : ℚ) * (delta - one) * st + (3 : ℚ) * ct - sp + cp
  let f3 := a * cp - sp - half + half * cp - b * sp
  let f4 := a + (1 / 2 : ℚ) * piM - phi - theta - b
    + half * delta * (one + a) + quarter * delta * delta
  ![f1, f2, f3, f4]

/-- The model values are definitionally the manuscript reduced system after
coordinate conversion. -/
theorem vectorSystem_eq_models (x : Vec 4) :
    vectorSystem x = fun i => (models i).value x := by
  funext i
  fin_cases i <;>
    simp [vectorSystem, coordEquiv, system, models, ScalarModel.var,
      ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
      ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos] <;>
    ring

end Reduced

end GerverSofa

end

end

end

section

/-!
# Concrete interval-AD soundness for the direct 22D Romik system

The direct system contains five trigonometric path pieces, three derivative
pieces and six matching pairs.  To avoid 22 unrelated derivative proofs, this
file evaluates every expression in a proof-carrying dual object.  Its first
projection is the exact executable `ExactReplay.D`; its second projection is a
smooth real scalar model; and its third field is the constructor-level
soundness theorem from `ADCoreSoundness`.
-/

/-! ## Exact identification of the 22D input box

The 22 coordinates are kept as separate tiny lemmas.  This is deliberately
chunked: expanding all 44 rational endpoint inequalities in one `simp` call
exhausts the default heartbeat budget even though every coordinate identity is
individually trivial. -/

public section

noncomputable section

namespace GerverSofa

open RatInterval

namespace Romik

private theorem fullInputBox_coord_0_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 0) (x 0) ↔
      qR (-21032242207268875141628571849) 100000000000000000000000000000 ≤ x 0 ∧
      x 0 ≤ qR (-21032242207268875141608571849) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_1_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 1) (x 1) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 1 ∧
      x 1 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_2_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 2) (x 2) ↔
      qR (-91917929277159332227479610289) 100000000000000000000000000000 ≤ x 2 ∧
      x 2 ≤ qR (-91917929277159332227459610289) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_3_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 3) (x 3) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 3 ∧
      x 3 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_4_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 4) (x 4) ↔
      qR (-15344080735756291713875357283) 25000000000000000000000000000 ≤ x 4 ∧
      x 4 ≤ qR (-15344080735756291713870357283) 25000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_5_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 5) (x 5) ↔
      qR 17792529580064437214538861001 20000000000000000000000000000 ≤ x 5 ∧
      x 5 ≤ qR 17792529580064437214542861001 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_6_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 6) (x 6) ↔
      qR (-15417358304445500741761623987) 50000000000000000000000000000 ≤ x 6 ∧
      x 6 ≤ qR (-15417358304445500741751623987) 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_7_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 7) (x 7) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 7 ∧
      x 7 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_8_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 8) (x 8) ↔
      qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ x 8 ∧
      x 8 ≤ qR (-20344080735756291713870857283) 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_9_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 9) (x 9) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 9 ∧
      x 9 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_10_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 10) (x 10) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 10 ∧
      x 10 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_11_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 11) (x 11) ↔
      qR (-2500000000000000000001) 10000000000000000000000 ≤ x 11 ∧
      x 11 ≤ qR (-2499999999999999999999) 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_12_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 12) (x 12) ↔
      qR (-52762459802678462416060380937) 100000000000000000000000000000 ≤ x 12 ∧
      x 12 ≤ qR (-52762459802678462416040380937) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_13_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 13) (x 13) ↔
      qR 92025838516063762289360579501 100000000000000000000000000000 ≤ x 13 ∧
      x 13 ≤ qR 92025838516063762289380579501 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_14_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 14) (x 14) ↔
      qR 313022761424232933776114655193 500000000000000000000000000000 ≤ x 14 ∧
      x 14 ≤ qR 313022761424232933776214655193 500000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_15_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 15) (x 15) ↔
      qR (-151160128631428920268654781) 160000000000000000000000000 ≤ x 15 ∧
      x 15 ≤ qR (-151160128631428920268622781) 160000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_16_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 16) (x 16) ↔
      qR 1641278451780291167220080819 1250000000000000000000000000 ≤ x 16 ∧
      x 16 ≤ qR 1641278451780291167220330819 1250000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_17_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 17) (x 17) ↔
      qR (-105076534082910887440587258861) 200000000000000000000000000000 ≤ x 17 ∧
      x 17 ≤ qR (-105076534082910887440547258861) 200000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_18_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 18) (x 18) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 18 ∧
      x 18 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_19_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 19) (x 19) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 19 ∧
      x 19 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_20_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 20) (x 20) ↔
      qR 1958868239504182093160893749 50000000000000000000000000000 ≤ x 20 ∧
      x 20 ≤ qR 78354729580167283726435751 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_21_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 21) (x 21) ↔
      qR 34065075469136244723692787727 50000000000000000000000000000 ≤ x 21 ∧
      x 21 ≤ qR 34065075469136244723692787983 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]

/-- The 22 frozen rational intervals are exactly the named direct-system box. -/
theorem inputBox_exact (x : Vec 22) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.fullInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, coordEquiv] at hx
    rcases hx with ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi, h3lo, h3hi, h4lo, h4hi, h5lo, h5hi, h6lo,
      h6hi, h7lo, h7hi, h8lo, h8hi, h9lo, h9hi, h10lo, h10hi, h11lo, h11hi, h12lo, h12hi, h13lo,
      h13hi, h14lo, h14hi, h15lo, h15hi, h16lo, h16hi, h17lo, h17hi, h18lo, h18hi, h19lo, h19hi,
      h20lo, h20hi, h21lo, h21hi⟩
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.fullInputBox, CertificateManifest.z22]
    · intro i
      fin_cases i
      · exact (fullInputBox_coord_0_iff x).2 ⟨h0lo, h0hi⟩
      · exact (fullInputBox_coord_1_iff x).2 ⟨h1lo, h1hi⟩
      · exact (fullInputBox_coord_2_iff x).2 ⟨h2lo, h2hi⟩
      · exact (fullInputBox_coord_3_iff x).2 ⟨h3lo, h3hi⟩
      · exact (fullInputBox_coord_4_iff x).2 ⟨h4lo, h4hi⟩
      · exact (fullInputBox_coord_5_iff x).2 ⟨h5lo, h5hi⟩
      · exact (fullInputBox_coord_6_iff x).2 ⟨h6lo, h6hi⟩
      · exact (fullInputBox_coord_7_iff x).2 ⟨h7lo, h7hi⟩
      · exact (fullInputBox_coord_8_iff x).2 ⟨h8lo, h8hi⟩
      · exact (fullInputBox_coord_9_iff x).2 ⟨h9lo, h9hi⟩
      · exact (fullInputBox_coord_10_iff x).2 ⟨h10lo, h10hi⟩
      · exact (fullInputBox_coord_11_iff x).2 ⟨h11lo, h11hi⟩
      · exact (fullInputBox_coord_12_iff x).2 ⟨h12lo, h12hi⟩
      · exact (fullInputBox_coord_13_iff x).2 ⟨h13lo, h13hi⟩
      · exact (fullInputBox_coord_14_iff x).2 ⟨h14lo, h14hi⟩
      · exact (fullInputBox_coord_15_iff x).2 ⟨h15lo, h15hi⟩
      · exact (fullInputBox_coord_16_iff x).2 ⟨h16lo, h16hi⟩
      · exact (fullInputBox_coord_17_iff x).2 ⟨h17lo, h17hi⟩
      · exact (fullInputBox_coord_18_iff x).2 ⟨h18lo, h18hi⟩
      · exact (fullInputBox_coord_19_iff x).2 ⟨h19lo, h19hi⟩
      · exact (fullInputBox_coord_20_iff x).2 ⟨h20lo, h20hi⟩
      · exact (fullInputBox_coord_21_iff x).2 ⟨h21lo, h21hi⟩
  · rintro ⟨_hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, coordEquiv]
    have h0 := (fullInputBox_coord_0_iff x).1 (hx (0 : Fin 22))
    have h1 := (fullInputBox_coord_1_iff x).1 (hx (1 : Fin 22))
    have h2 := (fullInputBox_coord_2_iff x).1 (hx (2 : Fin 22))
    have h3 := (fullInputBox_coord_3_iff x).1 (hx (3 : Fin 22))
    have h4 := (fullInputBox_coord_4_iff x).1 (hx (4 : Fin 22))
    have h5 := (fullInputBox_coord_5_iff x).1 (hx (5 : Fin 22))
    have h6 := (fullInputBox_coord_6_iff x).1 (hx (6 : Fin 22))
    have h7 := (fullInputBox_coord_7_iff x).1 (hx (7 : Fin 22))
    have h8 := (fullInputBox_coord_8_iff x).1 (hx (8 : Fin 22))
    have h9 := (fullInputBox_coord_9_iff x).1 (hx (9 : Fin 22))
    have h10 := (fullInputBox_coord_10_iff x).1 (hx (10 : Fin 22))
    have h11 := (fullInputBox_coord_11_iff x).1 (hx (11 : Fin 22))
    have h12 := (fullInputBox_coord_12_iff x).1 (hx (12 : Fin 22))
    have h13 := (fullInputBox_coord_13_iff x).1 (hx (13 : Fin 22))
    have h14 := (fullInputBox_coord_14_iff x).1 (hx (14 : Fin 22))
    have h15 := (fullInputBox_coord_15_iff x).1 (hx (15 : Fin 22))
    have h16 := (fullInputBox_coord_16_iff x).1 (hx (16 : Fin 22))
    have h17 := (fullInputBox_coord_17_iff x).1 (hx (17 : Fin 22))
    have h18 := (fullInputBox_coord_18_iff x).1 (hx (18 : Fin 22))
    have h19 := (fullInputBox_coord_19_iff x).1 (hx (19 : Fin 22))
    have h20 := (fullInputBox_coord_20_iff x).1 (hx (20 : Fin 22))
    have h21 := (fullInputBox_coord_21_iff x).1 (hx (21 : Fin 22))
    exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
      h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2, h12.1, h12.2, h13.1, h13.2,
      h14.1, h14.2, h15.1, h15.2, h16.1, h16.2, h17.1, h17.2, h18.1, h18.2, h19.1, h19.2, h20.1,
      h20.2, h21.1, h21.2⟩

/-- All four switching times used by the direct evaluator lie in `[0,π/2]`. -/
theorem full_switches_physical {x : Vec 22} (hx : x ∈ vectorBox) :
    (0 ≤ x 20 ∧ x 20 ≤ Real.pi / 2) ∧
    (0 ≤ x 21 ∧ x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 21 ∧ Real.pi / 2 - x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 20 ∧ Real.pi / 2 - x 20 ≤ Real.pi / 2) := by
  let p := coordEquiv.symm x
  have hp : p ∈ box := hx
  have hphiPos : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have htheta0 : 0 ≤ p.theta :=
    le_trans hphiPos.le hord.phi_le_theta
  have hthetaHalf : p.theta ≤ Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiHalf : p.phi ≤ Real.pi / 2 :=
    le_trans hord.phi_le_theta hthetaHalf
  change
    (0 ≤ p.phi ∧ p.phi ≤ Real.pi / 2) ∧
    (0 ≤ p.theta ∧ p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.theta ∧
      Real.pi / 2 - p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.phi ∧
      Real.pi / 2 - p.phi ≤ Real.pi / 2)
  constructor
  · exact ⟨hphiPos.le, hphiHalf⟩
  constructor
  · exact ⟨htheta0, hthetaHalf⟩
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-! ## Proof-carrying dual expressions -/

/-- One executable interval dual paired with its real semantic model. -/
structure SoundDual (n : Nat) (X : Set (Vec n)) where
  /-- The interval value and derivative data being certified. -/
  d : ExactReplay.D
  /-- The real scalar function and gradient represented by the interval data. -/
  model : ScalarModel n
  sound : DSoundOn X d model

namespace SoundDual

variable {n : Nat} {X : Set (Vec n)}

/-- A constant scalar model with a certified interval enclosure. -/
@[expose]
def const (z : RatInterval) (c : ℝ) (h : Contains z c) : SoundDual n X :=
  ⟨ExactReplay.D.const z n, ScalarModel.const n c, DSoundOn.const h⟩

/-- A rational constant represented by a singleton interval and zero gradient. -/
@[expose]
def pointConst (q : ℚ) : SoundDual n X :=
  ⟨ExactReplay.D.pointConst q n, ScalarModel.const n (q : ℝ),
    DSoundOn.pointConst q⟩

/-- A coordinate projection with its certified input interval. -/
@[expose]
def var (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) : SoundDual n X :=
  ⟨ExactReplay.D.varD input k.1 n, ScalarModel.var n k,
    DSoundOn.varD input k h⟩

/-- Addition with certified interval value and gradient enclosures. -/
@[expose]
def add (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.addD a.d b.d, ScalarModel.add a.model b.model,
    a.sound.add b.sound⟩

/-- Negation with certified interval value and gradient enclosures. -/
@[expose]
def neg (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.negD a.d, ScalarModel.neg a.model, a.sound.neg⟩

/-- Subtraction with certified interval value and gradient enclosures. -/
@[expose]
def sub (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.subD a.d b.d, ScalarModel.sub a.model b.model,
    a.sound.sub b.sound⟩

/-- Multiplication with certified interval value and gradient enclosures. -/
@[expose]
def mul (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.mulD a.d b.d, ScalarModel.mul a.model b.model,
    a.sound.mul b.sound⟩

/-- Rational scaling with certified interval value and gradient enclosures. -/
@[expose]
def scale (q : ℚ) (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.scaleD q a.d, ScalarModel.scale q a.model,
    DSoundOn.scale q a.sound⟩

/-- Sine with certified interval value and gradient enclosures. -/
@[expose]
def sin (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.sinD a.d, ScalarModel.sin a.model, a.sound.sin h⟩

/-- Cosine with certified interval value and gradient enclosures. -/
@[expose]
def cos (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.cosD a.d, ScalarModel.cos a.model, a.sound.cos h⟩

instance : Add (SoundDual n X) := ⟨add⟩
instance : Neg (SoundDual n X) := ⟨neg⟩
instance : Sub (SoundDual n X) := ⟨sub⟩
instance : Mul (SoundDual n X) := ⟨mul⟩
instance : HMul ℚ (SoundDual n X) (SoundDual n X) := ⟨scale⟩

/-! Small projection lemmas keep the simplifier away from the proof fields of
`SoundDual`.  All are definitional equalities. -/
@[simp] theorem const_model_value (z : RatInterval) (c : ℝ)
    (h : Contains z c) (x : Vec n) :
    (const z c h : SoundDual n X).model.value x = c := rfl

@[simp] theorem pointConst_model_value (q : ℚ) (x : Vec n) :
    (pointConst q : SoundDual n X).model.value x = (q : ℝ) := rfl

@[simp] theorem var_model_value (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) (x : Vec n) :
    (var input k h : SoundDual n X).model.value x = x k := rfl

@[simp] theorem add_model_value (a b : SoundDual n X) (x : Vec n) :
    (a + b).model.value x = a.model.value x + b.model.value x := rfl

@[simp] theorem neg_model_value (a : SoundDual n X) (x : Vec n) :
    (-a).model.value x = -a.model.value x := rfl

@[simp] theorem sub_model_value (a b : SoundDual n X) (x : Vec n) :
    (a - b).model.value x = a.model.value x - b.model.value x := rfl

@[simp] theorem mul_model_value (a b : SoundDual n X) (x : Vec n) :
    (a * b).model.value x = a.model.value x * b.model.value x := rfl

@[simp] theorem scale_model_value (q : ℚ) (a : SoundDual n X) (x : Vec n) :
    (q * a).model.value x = (q : ℝ) * a.model.value x := rfl

@[simp] theorem sin_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (sin a h).model.value x = Real.sin (a.model.value x) := rfl

@[simp] theorem cos_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (cos a h).model.value x = Real.cos (a.model.value x) := rfl

end SoundDual

/-- A certified physical angle, used to justify every sine/cosine constructor. -/
structure AngleDual (n : Nat) (X : Set (Vec n)) where
  /-- The certified scalar model for the angle variable. -/
  dual : SoundDual n X
  physical : ∀ x ∈ X, 0 ≤ dual.model.value x ∧
    dual.model.value x ≤ Real.pi / 2

namespace AngleDual

variable {n : Nat} {X : Set (Vec n)}

/-- Sine with certified interval value and gradient enclosures. -/
@[expose]
def sin (t : AngleDual n X) : SoundDual n X :=
  SoundDual.sin t.dual t.physical

/-- Cosine with certified interval value and gradient enclosures. -/
@[expose]
def cos (t : AngleDual n X) : SoundDual n X :=
  SoundDual.cos t.dual t.physical

@[simp] theorem sin_model_value (t : AngleDual n X) (x : Vec n) :
    t.sin.model.value x = Real.sin (t.dual.model.value x) := rfl

@[simp] theorem cos_model_value (t : AngleDual n X) (x : Vec n) :
    t.cos.model.value x = Real.cos (t.dual.model.value x) := rfl

end AngleDual

/-- Named proof-carrying versions of all direct-system variables. -/
structure FullVars (X : Set (Vec 22)) where
  /-- Horizontal translation coefficient for phase 1 as a certified dual interval. -/
  k11 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 1 as a certified dual interval. -/
  k12 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 2 as a certified dual interval. -/
  k21 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 2 as a certified dual interval. -/
  k22 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 3 as a certified dual interval. -/
  k31 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 3 as a certified dual interval. -/
  k32 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 4 as a certified dual interval. -/
  k41 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 4 as a certified dual interval. -/
  k42 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 5 as a certified dual interval. -/
  k51 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 5 as a certified dual interval. -/
  k52 : SoundDual 22 X
  /-- Coefficient 1 in the phase 1 closed formula as a certified dual interval. -/
  a1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 1 closed formula as a certified dual interval. -/
  a2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 2 closed formula as a certified dual interval. -/
  b1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 2 closed formula as a certified dual interval. -/
  b2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 3 closed formula as a certified dual interval. -/
  c1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 3 closed formula as a certified dual interval. -/
  c2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 4 closed formula as a certified dual interval. -/
  d1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 4 closed formula as a certified dual interval. -/
  d2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 5 closed formula as a certified dual interval. -/
  e1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 5 closed formula as a certified dual interval. -/
  e2 : SoundDual 22 X

/-- The 22 coordinate variables equipped with their input-enclosure proofs. -/
@[expose]
def inputDual (i : Fin 22) : SoundDual 22 vectorBox :=
  SoundDual.var (ExactReplay.getI ExactReplay.fullInputBox i.1) i (by
    intro x hx
    exact ((inputBox_exact x).1 hx).2 i)

@[simp] theorem inputDual_model_value (i : Fin 22) (x : Vec 22) :
    (inputDual i).model.value x = x i := rfl

/-- Named first twenty variables in verifier order. -/
@[expose]
def fullVars : FullVars vectorBox where
  k11 := inputDual 0
  k12 := inputDual 1
  k21 := inputDual 2
  k22 := inputDual 3
  k31 := inputDual 4
  k32 := inputDual 5
  k41 := inputDual 6
  k42 := inputDual 7
  k51 := inputDual 8
  k52 := inputDual 9
  a1 := inputDual 10
  a2 := inputDual 11
  b1 := inputDual 12
  b2 := inputDual 13
  c1 := inputDual 14
  c2 := inputDual 15
  d1 := inputDual 16
  d2 := inputDual 17
  e1 := inputDual 18
  e2 := inputDual 19

/-- Exact proof-carrying π constant. -/
@[expose]
def piDual : SoundDual 22 vectorBox :=
  SoundDual.const ExactReplay.piI Real.pi ExactReplay.piI_contains_pi

@[simp] theorem piDual_model_value (x : Vec 22) :
    piDual.model.value x = Real.pi := rfl

/-- First switching angle. -/
@[expose]
def phiDual : AngleDual 22 vectorBox where
  dual := inputDual 20
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).1

@[simp] theorem phiDual_model_value (x : Vec 22) :
    phiDual.dual.model.value x = x 20 := rfl

/-- Second switching angle. -/
@[expose]
def thetaDual : AngleDual 22 vectorBox where
  dual := inputDual 21
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).2.1

@[simp] theorem thetaDual_model_value (x : Vec 22) :
    thetaDual.dual.model.value x = x 21 := rfl

private theorem eta_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - thetaDual.dual).model.value x) =
      Real.pi / 2 - x 21 := by
  simp; ring

/-- Reflected third switching angle `π/2-θ`. -/
@[expose]
def etaDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - thetaDual.dual
  physical := by
    intro x hx
    rw [eta_raw_model_value]
    exact (full_switches_physical hx).2.2.1

@[simp] theorem etaDual_model_value (x : Vec 22) :
    etaDual.dual.model.value x = Real.pi / 2 - x 21 := by
  exact eta_raw_model_value x

private theorem tau_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - phiDual.dual).model.value x) =
      Real.pi / 2 - x 20 := by
  simp; ring

/-- Reflected fourth switching angle `π/2-φ`. -/
@[expose]
def tauDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - phiDual.dual
  physical := by
    intro x hx
    rw [tau_raw_model_value]
    exact (full_switches_physical hx).2.2.2

@[simp] theorem tauDual_model_value (x : Vec 22) :
    tauDual.dual.model.value x = Real.pi / 2 - x 20 := by
  exact tau_raw_model_value x

/-- Rotation of a proof-carrying body-frame vector. -/
@[expose]
def rotDual (t : AngleDual 22 vectorBox)
    (z1 z2 : SoundDual 22 vectorBox) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ct := t.cos
  let st := t.sin
  (ct * z1 - st * z2, st * z1 + ct * z2)

/-- One proof-carrying path piece. -/
@[expose]
def pathPieceDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  let data : SoundDual 22 vectorBox × SoundDual 22 vectorBox ×
      SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
    if j = 1 then
      (p.a1 * ct + p.a2 * st - one,
       -p.a2 * ct + p.a1 * st - half,
       p.k11, p.k12)
    else if j = 2 then
      (-quarter * t.dual * t.dual + p.b1 * t.dual + p.b2,
       half * t.dual - p.b1 - one,
       p.k21, p.k22)
    else if j = 3 then
      (p.c1 - t.dual, p.c2 + t.dual, p.k31, p.k32)
    else if j = 4 then
      (-half * t.dual + p.d1 - one,
       -quarter * t.dual * t.dual + p.d1 * t.dual + p.d2,
       p.k41, p.k42)
    else
      (p.e1 * ct + p.e2 * st - half,
       -p.e2 * ct + p.e1 * st - one,
       p.k51, p.k52)
  let rr := rotDual t data.1 data.2.1
  (rr.1 + data.2.2.1, rr.2 + data.2.2.2)

/-- Body-frame derivative coefficients for one phase. -/
@[expose]
def alphaBetaDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  if j = 1 then
    (-(2 : ℚ) * p.a1 * st + (2 : ℚ) * p.a2 * ct + half,
     (2 : ℚ) * p.a1 * ct + (2 : ℚ) * p.a2 * st - one)
  else if j = 2 then
    (one + (2 : ℚ) * p.b1 - t.dual,
     -quarter * t.dual * t.dual + p.b1 * t.dual + p.b2 + half)
  else if j = 3 then
    (-one - p.c2 - t.dual, one + p.c1 - t.dual)
  else if j = 4 then
    (quarter * t.dual * t.dual - p.d1 * t.dual - p.d2 - half,
     (2 : ℚ) * p.d1 - one - t.dual)
  else
    (one - (2 : ℚ) * p.e1 * st + (2 : ℚ) * p.e2 * ct,
     (2 : ℚ) * p.e1 * ct + (2 : ℚ) * p.e2 * st - half)

/-- World-frame derivative piece. -/
@[expose]
def pathPrimeDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ab := alphaBetaDual j t p
  rotDual t ab.1 ab.2

/-- The complete proof-carrying direct system in manuscript order. -/
@[expose]
def fullDualOutput : List (SoundDual 22 vectorBox) :=
  let p := fullVars
  let halfPi := (1 / 2 : ℚ) * piDual
  let quarterPi := (1 / 4 : ℚ) * piDual
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let first : List (SoundDual 22 vectorBox) := [
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * ((2 : ℚ) * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - one + p.a1,
    p.k12 - quarter,
    p.a2 + quarter
  ]
  let pairs := [
    (pathPieceDual 1 phiDual p, pathPieceDual 2 phiDual p),
    (pathPrimeDual 1 phiDual p, pathPrimeDual 2 phiDual p),
    (pathPieceDual 2 thetaDual p, pathPieceDual 3 thetaDual p),
    (pathPrimeDual 2 thetaDual p, pathPrimeDual 3 thetaDual p),
    (pathPieceDual 3 etaDual p, pathPieceDual 4 etaDual p),
    (pathPieceDual 4 tauDual p, pathPieceDual 5 tauDual p)
  ]
  let matchEqs := pairs.flatMap (fun lr =>
    [lr.1.1 - lr.2.1, lr.1.2 - lr.2.2])
  let lhs := pathPieceDual 1 phiDual p
  let xe := pathPieceDual 3 etaDual p
  let ae := (alphaBetaDual 3 etaDual p).1
  let be :=
    (xe.1 - ae * etaDual.sin, xe.2 + ae * etaDual.cos)
  first ++ matchEqs ++ [lhs.1 - be.1, lhs.2 - be.2]

/-! Public-shape unfold lemmas for the three derivative path pieces.

`Systems.lean` deliberately hides the helper `pathPrimeFromAB`.  When `system`
is unfolded outside that file, the private helper survives as an inaccessible
constant, so `ring` cannot see that the right-hand side is just a rotation.
These `rfl` lemmas expose exactly the public normal form needed by the four
derivative-matching equations. -/
private theorem pathPrime1_eq_rot (p : Params) (t : ℝ) :
    pathPrime1 p t = rot t (alphaBeta1 p t) := rfl

private theorem pathPrime2_eq_rot (p : Params) (t : ℝ) :
    pathPrime2 p t = rot t (alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot (p : Params) (t : ℝ) :
    pathPrime3 p t = rot t (alphaBeta3 p t) := rfl

/-! The semantic identification is split coordinatewise so each normalization
gets its own heartbeat budget.  A single 22-way `fin_cases <;> simp <;> ring`
command is mathematically fine but deterministically exhausts 200000 heartbeats. -/

private theorem fullDualOutput_model_eq_0 (x : Vec 22) :
    ((fullDualOutput.getD 0 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (0 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_1 (x : Vec 22) :
    ((fullDualOutput.getD 1 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (1 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_2 (x : Vec 22) :
    ((fullDualOutput.getD 2 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (2 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_3 (x : Vec 22) :
    ((fullDualOutput.getD 3 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (3 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_4 (x : Vec 22) :
    ((fullDualOutput.getD 4 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (4 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_5 (x : Vec 22) :
    ((fullDualOutput.getD 5 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (5 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_6 (x : Vec 22) :
    ((fullDualOutput.getD 6 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (6 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_7 (x : Vec 22) :
    ((fullDualOutput.getD 7 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (7 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_8 (x : Vec 22) :
    ((fullDualOutput.getD 8 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (8 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_9 (x : Vec 22) :
    ((fullDualOutput.getD 9 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (9 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_10 (x : Vec 22) :
    ((fullDualOutput.getD 10 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (10 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_11 (x : Vec 22) :
    ((fullDualOutput.getD 11 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (11 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_12 (x : Vec 22) :
    ((fullDualOutput.getD 12 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (12 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_13 (x : Vec 22) :
    ((fullDualOutput.getD 13 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (13 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_14 (x : Vec 22) :
    ((fullDualOutput.getD 14 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (14 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_15 (x : Vec 22) :
    ((fullDualOutput.getD 15 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (15 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_16 (x : Vec 22) :
    ((fullDualOutput.getD 16 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (16 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_17 (x : Vec 22) :
    ((fullDualOutput.getD 17 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (17 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_18 (x : Vec 22) :
    ((fullDualOutput.getD 18 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (18 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_19 (x : Vec 22) :
    ((fullDualOutput.getD 19 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (19 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_20 (x : Vec 22) :
    ((fullDualOutput.getD 20 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (20 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

private theorem fullDualOutput_model_eq_21 (x : Vec 22) :
    ((fullDualOutput.getD 21 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (21 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]

/-- The real models carried by `fullDualOutput` are exactly the 22 manuscript
functions in finite-vector coordinates. -/
theorem fullDualOutput_model_eq (x : Vec 22) :
    (fun i : Fin 22 =>
      ((fullDualOutput.getD i.1
        (SoundDual.pointConst 0)).model.value x)) = vectorSystem x := by
  funext i
  fin_cases i
  · exact fullDualOutput_model_eq_0 x
  · exact fullDualOutput_model_eq_1 x
  · exact fullDualOutput_model_eq_2 x
  · exact fullDualOutput_model_eq_3 x
  · exact fullDualOutput_model_eq_4 x
  · exact fullDualOutput_model_eq_5 x
  · exact fullDualOutput_model_eq_6 x
  · exact fullDualOutput_model_eq_7 x
  · exact fullDualOutput_model_eq_8 x
  · exact fullDualOutput_model_eq_9 x
  · exact fullDualOutput_model_eq_10 x
  · exact fullDualOutput_model_eq_11 x
  · exact fullDualOutput_model_eq_12 x
  · exact fullDualOutput_model_eq_13 x
  · exact fullDualOutput_model_eq_14 x
  · exact fullDualOutput_model_eq_15 x
  · exact fullDualOutput_model_eq_16 x
  · exact fullDualOutput_model_eq_17 x
  · exact fullDualOutput_model_eq_18 x
  · exact fullDualOutput_model_eq_19 x
  · exact fullDualOutput_model_eq_20 x
  · exact fullDualOutput_model_eq_21 x

end Romik

end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartF.F01AffineOrder`.
* `KernelOnly.PartF.F01PhaseAlgebra`.
* `KernelOnly.PartF.F01SetMotion`.
* `KernelOnly.PartF.F02Coordinates`.
* `KernelOnly.PartF.F04IntegralPrimitives`.
* `KernelOnly.PartF.F04IntegralEvaluation`.
* `KernelOnly.PartF.F05DictionaryEquations`.
* `KernelOnly.PartF.F06ReverseSystem`.
* `KernelOnly.PartF.F06FullReconstruction`.
-/

public section

noncomputable section

section

/-!
# F01: the affine-order bridge for issue #5270

The two constructors are deliberately given different names. No upstream
definition is changed or imported, and no theorem from the conjecture file
is used. Both application conventions and the conversion between them are
proved for an arbitrary linear isometry equivalence.
-/

public section

noncomputable section

namespace GerverSofa.PartF

/-- The Euclidean plane used for the continuous rigid-motion formulation. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- Affine isometries of the Euclidean plane. -/
abbrev Rigid := Plane ≃ᵃⁱ[ℝ] Plane

/-- The ordered coordinate-basis orientation used by the pinned upstream
`FormalConjecturesForMathlib/Geometry/2d.lean`. Importing `Mathlib` alone
does not install that project's plane-orientation instance. -/
instance planeOriented : Module.Oriented ℝ Plane (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The second instance supplied by the same upstream plane helper. -/
instance planeFactFinrank : Fact (Module.finrank ℝ Plane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The topology used by the pinned `MovingSofa.IsMovingSofa` definition. -/
instance rigidTopology : TopologicalSpace Rigid :=
  .induced (fun e => e.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- The composition currently implemented upstream: `q ↦ R q + p`. -/
@[expose]
def rotateThenTranslate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)

/-- The documented composition: `q ↦ R (q + p)`. -/
@[expose]
def translateThenRotate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans R.toAffineIsometryEquiv

@[simp] theorem rotateThenTranslate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    rotateThenTranslate R p q = R q + p := rfl

@[simp] theorem translateThenRotate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    translateThenRotate R p q = R (q + p) := rfl

/-- Keeping the old composition is equivalent to rotating the translation. -/
theorem translateThenRotate_eq_rotateThenTranslate
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    translateThenRotate R p = rotateThenTranslate R (R p) := by
  ext q
  simp only [translateThenRotate_apply, rotateThenTranslate_apply, map_add]

/-- Counterclockwise rotation of the oriented plane through angle `t`. -/
@[expose]
def rotation (t : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  EuclideanGeometry.o.rotation (t : Real.Angle)

/-- Translate by the body-frame offset and then rotate through `t`. -/
@[expose]
def bodyFrame (t : ℝ) (p : Plane) : Rigid :=
  translateThenRotate (rotation t) p

/-- Rotate through `t` and then translate by the world position. -/
@[expose]
def worldFrame (t : ℝ) (x : Plane) : Rigid :=
  rotateThenTranslate (rotation t) x

theorem bodyFrame_eq_worldFrame (t : ℝ) (p : Plane) :
    bodyFrame t p = worldFrame t (rotation t p) :=
  translateThenRotate_eq_rotateThenTranslate (rotation t) p

end GerverSofa.PartF

end

end

end

section

/-!
# F01: algebraic half of the integral-to-five-phase representation

The coefficient dictionary and the five explicit body-frame branches come
from the 4 September integral-motion excerpt. They are compared to the
actual `Romik.path1` ... `Romik.path5` definitions, then assembled using the
same `if` boundaries as `Romik.path`.

This module does NOT evaluate the integrals: `closedPath` is explicitly
named as a closed-form candidate. Proving that the pinned integral path
equals it, and identifying `dictionary d` with the certified 22D tuple,
remain separate obligations. No such equality is assumed here.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Phases

/-- The terminal rotation angle π/2. -/
@[expose]
def T : ℝ := Real.pi / 2
/-- The auxiliary height parameter `(a + θ - φ - 1) / 2`. -/
def hStar (d : Reduced.Params) : ℝ := (d.a + d.theta - d.phi - 1) / 2
/-- Phase 4 integration constant for the vertical primitive. -/
def U4 (d : Reduced.Params) : ℝ :=
  (1 + d.a) / 2 * Real.cos d.phi - (d.b + 1 / 2) * Real.sin d.phi
/-- Phase 4 integration constant for the horizontal primitive. -/
def V4 (d : Reduced.Params) : ℝ :=
  1 - (d.b + 1 / 2) * Real.cos d.phi - (1 + d.a) / 2 * Real.sin d.phi
/-- Phase 3 integration constant for the vertical primitive. -/
def U3 (d : Reduced.Params) : ℝ :=
  U4 d + 1 / 2 * Real.sin d.theta - hStar d * Real.cos d.theta
/-- Phase 3 integration constant for the horizontal primitive. -/
def V3 (d : Reduced.Params) : ℝ :=
  V4 d + 1 / 2 * Real.cos d.theta + hStar d * Real.sin d.theta
/-- Phase 2 integration constant for the vertical primitive. -/
@[expose]
def U2 (d : Reduced.Params) : ℝ := U4 d
/-- Phase 2 integration constant for the horizontal primitive. -/
def V2 (d : Reduced.Params) : ℝ :=
  V4 d + Real.cos d.theta + 2 * hStar d * Real.sin d.theta
/-- Phase 1 integration constant for the vertical primitive. -/
def U1 (d : Reduced.Params) : ℝ :=
  U2 d + d.a / 2 * Real.cos d.phi - 1 / 2 * Real.sin d.phi
/-- Phase 1 integration constant for the horizontal primitive. -/
def V1 (d : Reduced.Params) : ℝ :=
  V2 d + d.a / 2 * Real.sin d.phi + 1 / 2 * Real.cos d.phi
/-- The first-phase offset determined by `4 V1 - 2`. -/
@[expose]
def ell (d : Reduced.Params) : ℝ := 4 * V1 d - 2

theorem U1_eq_half (d : Reduced.Params) (hd : Reduced.Equations d) :
    U1 d = 1 / 2 := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (2 : Fin 4)
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h
  dsimp [U1, U2, U4]
  linear_combination h

theorem ell_eq (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = V2 d + V4 d := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (1 : Fin 4)
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi +
    3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h
  dsimp [ell, V1, V2, V4, hStar]
  linear_combination h

theorem ell_eq_two_V3 (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = 2 * V3 d := by
  rw [ell_eq d hd]
  dsimp [V2, V3]
  ring

/-- Express all twenty-two Romik parameters in terms of the four reduced parameters. -/
@[expose]
def dictionary (d : Reduced.Params) : Romik.Params where
  k11 := 1 - 3 / 2 * (1 - V1 d)
  k12 := 1 / 4
  k21 := V4 d
  k22 := U4 d
  k31 := V3 d
  k32 := U3 d
  k41 := V2 d
  k42 := U4 d
  k51 := V1 d - 3 / 2 * (1 - V1 d)
  k52 := 1 / 4
  a1 := 3 / 2 * (1 - V1 d)
  a2 := -1 / 4
  b1 := (d.phi - 1 - d.a) / 2
  b2 := d.b - 1 / 2 + (1 + d.a) / 2 * d.phi - d.phi ^ 2 / 4
  c1 := d.a + T - d.phi - 1
  c2 := d.a - d.phi - 1
  d1 := (T - d.phi + 1 + d.a) / 2
  d2 := d.b - 1 / 2 - (1 + d.a) / 2 * (T - d.phi) - (T - d.phi)^2 / 4
  e1 := 3 / 2 * (1 - V1 d)
  e2 := 1 / 4
  phi := d.phi
  theta := d.theta

@[simp] theorem dictionary_phi (d : Reduced.Params) : (dictionary d).phi = d.phi := rfl
@[simp] theorem dictionary_theta (d : Reduced.Params) : (dictionary d).theta = d.theta := rfl

/-- The polynomial profile for phase 2 of the path. -/
@[expose]
def g2 (d : Reduced.Params) (t : ℝ) : ℝ := (1 + d.a + t - d.phi) / 2
/-- The polynomial profile for phase 3 of the path. -/
@[expose]
def g3 (d : Reduced.Params) (t : ℝ) : ℝ := d.a + t - d.phi
/-- The polynomial profile for phase 4 of the path. -/
def g4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b + 1 / 2 - (T - d.phi - t) * (1 + d.a) / 2 - (T - d.phi - t)^2 / 4

/-- The closed rotation-path formula for phase 1. -/
@[expose]
def closed1 (d : Reduced.Params) (t : ℝ) : Point :=
  (Real.cos t - 1,
    -1 / 2 + 1 / 2 * Real.cos t + (V1 d - ell d) * Real.sin t)

/-- The closed rotation-path formula for phase 2. -/
@[expose]
def closed2 (d : Reduced.Params) (t : ℝ) : Point :=
  (g4 d (T - t) + U4 d * Real.sin t + V4 d * Real.cos t - 1,
    g2 d t + U4 d * Real.cos t + (V2 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 3. -/
@[expose]
def closed3 (d : Reduced.Params) (t : ℝ) : Point :=
  (g3 d (T - t) + U3 d * Real.sin t + V3 d * Real.cos t - 1,
    g3 d t + U3 d * Real.cos t + (V3 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 4. -/
@[expose]
def closed4 (d : Reduced.Params) (t : ℝ) : Point :=
  (g2 d (T - t) + U4 d * Real.sin t + V2 d * Real.cos t - 1,
    g4 d t + U4 d * Real.cos t + (V4 d - ell d) * Real.sin t - 1)

/-- The closed rotation-path formula for phase 5. -/
@[expose]
def closed5 (d : Reduced.Params) (t : ℝ) : Point :=
  (-1 / 2 + V1 d * Real.cos t + 1 / 2 * Real.sin t,
    (1 - ell d) * Real.sin t - 1)

theorem phase1 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed1 d t) = Romik.path1 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

theorem phase2 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed2 d t) = Romik.path2 (dictionary d) t := by
  unfold closed2
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination V4 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase3 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed3 d t) = Romik.path3 (dictionary d) t := by
  unfold closed3
  rw [ell_eq_two_V3 d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination V3 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination U3 d * Real.sin_sq_add_cos_sq t

theorem phase4 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed4 d t) = Romik.path4 (dictionary d) t := by
  unfold closed4
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination V2 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase5 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed5 d t) = Romik.path5 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (V1 d - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

/-- The five-branch closed formula for the rotation path. -/
@[expose]
def closedPath (d : Reduced.Params) (t : ℝ) : Point :=
  if t ≤ d.phi then closed1 d t
  else if t ≤ d.theta then closed2 d t
  else if t ≤ Real.pi / 2 - d.theta then closed3 d t
  else if t ≤ Real.pi / 2 - d.phi then closed4 d t
  else closed5 d t

/-- Exact assembly for the explicit closed path, including every switching
endpoint. This is not yet the corresponding theorem for the integral path. -/
theorem fivePhaseRepresentation (d : Reduced.Params)
    (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closedPath d t) = Romik.path (dictionary d) t := by
  -- Expose both sets of conditions, including the local `eta` and `tau`
  -- definitions inside `Romik.path`, before choosing a branch.
  change Romik.rot t
      (if t ≤ d.phi then closed1 d t
       else if t ≤ d.theta then closed2 d t
       else if t ≤ Real.pi / 2 - d.theta then closed3 d t
       else if t ≤ Real.pi / 2 - d.phi then closed4 d t
       else closed5 d t) =
    (if t ≤ d.phi then Romik.path1 (dictionary d) t
     else if t ≤ d.theta then Romik.path2 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.theta then Romik.path3 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.phi then Romik.path4 (dictionary d) t
     else Romik.path5 (dictionary d) t)
  by_cases h1 : t ≤ d.phi
  · simpa only [ite_eq_left h1] using phase1 d t
  by_cases h2 : t ≤ d.theta
  · simpa only [ite_eq_right h1, ite_eq_left h2] using phase2 d hd t
  by_cases h3 : t ≤ Real.pi / 2 - d.theta
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] using phase3 d hd t
  by_cases h4 : t ≤ Real.pi / 2 - d.phi
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4] using phase4 d
      hd t
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] using phase5 d t

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F01: supporting intersections and their continuous inverse motion

`Model.IsMovingSofa` has the seven fields and the rigid-motion topology of
the upstream definition. This local, independently named model avoids
importing upstream conjectures with unfinished proof terms. Its concrete
instantiation for the integral Gerver path still needs the analytic bridge.
-/

public section

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF

/-- Intersect the endpoint hallway arms and all intermediate moving hallways. -/
@[expose]
def frameIntersection (F : I → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F 1 '' V ∩ ⋂ s, F s '' L

/-- The hallway intersection parametrized by angles from zero to π/2. -/
@[expose]
def angleIntersection (F : ℝ → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F (Real.pi / 2) '' V ∩
    ⋂ t ∈ Set.Icc 0 (Real.pi / 2), F t '' L

/-- The hallway intersection generated by a path in body-frame coordinates. -/
@[expose]
def bodySofa (p : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => bodyFrame t (p t)) H V L

/-- The hallway intersection generated by a path in world-frame coordinates. -/
@[expose]
def worldSofa (x : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => worldFrame t (x t)) H V L

theorem bodySofa_eq_worldSofa_of_path_identity
    (p x : ℝ → Plane) (H V L : Set Plane)
    (hpath : ∀ t ∈ Set.Icc 0 (Real.pi / 2), x t = rotation t (p t)) :
    bodySofa p H V L = worldSofa x H V L := by
  have hT : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h0 := hpath 0 ⟨le_rfl, hT⟩
  have h1 := hpath (Real.pi / 2) ⟨hT, le_rfl⟩
  -- Expose the applications before rewriting under the image coercions.
  change
    bodyFrame 0 (p 0) '' H ∩
      bodyFrame (Real.pi / 2) (p (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), bodyFrame t (p t) '' L) =
    worldFrame 0 (x 0) '' H ∩
      worldFrame (Real.pi / 2) (x (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), worldFrame t (x t) '' L)
  rw [bodyFrame_eq_worldFrame, ← h0, bodyFrame_eq_worldFrame, ← h1]
  congr 1
  apply Set.iInter_congr
  intro t
  apply Set.iInter_congr
  intro ht
  rw [bodyFrame_eq_worldFrame, ← hpath t ht]

/-- Normalizing the physical angle does not change the intersection. -/
theorem angleIntersection_eq_frameIntersection
    (F : ℝ → Rigid) (H V L : Set Plane) :
    angleIntersection F H V L =
      frameIntersection (fun s : I => F ((s : ℝ) * (Real.pi / 2))) H V L := by
  have hT : (0 : ℝ) < Real.pi / 2 := by positivity
  have hz : ((0 : I) : ℝ) = 0 := rfl
  have ho : ((1 : I) : ℝ) = 1 := rfl
  ext q
  simp only [angleIntersection, frameIntersection, Set.mem_inter_iff,
    Set.mem_iInter, hz, ho, zero_mul, one_mul]
  constructor
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro s
    apply hall
    exact ⟨mul_nonneg s.property.1 hT.le,
      by nlinarith [s.property.2]⟩
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro t ht
    let s : I := ⟨t / (Real.pi / 2), div_nonneg ht.1 hT.le,
      (div_le_iff₀ hT).2 (by simpa using ht.2)⟩
    have h := hall s
    simpa only [s, div_mul_cancel₀ t (ne_of_gt hT)] using h

namespace Model

/-- The horizontal unit-width hallway arm extending to the left. -/
@[expose]
def horizontalHallway : Set Plane := {q | q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1}
/-- The vertical unit-width hallway arm extending downwards. -/
@[expose]
def verticalHallway : Set Plane := {q | 0 ≤ q 0 ∧ q 0 ≤ 1 ∧ q 1 ≤ 1}
/-- The union of the two perpendicular unit-width hallway arms. -/
@[expose]
def hallway : Set Plane := horizontalHallway ∪ verticalHallway

/-- A nonempty closed connected set moving continuously between the hallway arms. -/
structure IsMovingSofa (S : Set Plane) (m : I → Rigid) : Prop where
  isConnected : IsConnected S
  isClosed : IsClosed S
  continuous : Continuous m
  zero : m 0 = AffineIsometryEquiv.refl ℝ Plane
  initial : S ⊆ horizontalHallway
  subset_hallway : ∀ s, m s '' S ⊆ hallway
  final : m 1 '' S ⊆ verticalHallway

end Model

end GerverSofa.PartF

end

end

end

section

/-!
# F02: the coordinate homeomorphism

The product `Point = ℝ × ℝ` and `Plane = EuclideanSpace ℝ (Fin 2)`
have the same coordinates and topology. Their norms differ. Accordingly,
the coordinate identification below is a linear equivalence and a
homeomorphism. Euclidean isometries are constructed separately.
-/

public section

noncomputable section

namespace GerverSofa.PartF.Coordinates

/-- Convert a pair of real coordinates to a Euclidean vector. -/
@[expose]
def toPlane (q : Point) : Plane := WithLp.toLp 2 ![q.1, q.2]

/-- Extract the two real coordinates of a Euclidean vector. -/
@[expose]
def fromPlane (q : Plane) : Point := (q 0, q 1)

@[simp] theorem toPlane_zero_coord (q : Point) : toPlane q 0 = q.1 := rfl
@[simp] theorem toPlane_one_coord (q : Point) : toPlane q 1 = q.2 := rfl

theorem plane_ext {q r : Plane} (h0 : q 0 = r 0) (h1 : q 1 = r 1) : q = r := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] theorem fromPlane_toPlane (q : Point) : fromPlane (toPlane q) = q := rfl

@[simp] theorem toPlane_fromPlane (q : Plane) : toPlane (fromPlane q) = q := by
  exact plane_ext rfl rfl

theorem toPlane_add (q r : Point) : toPlane (q + r) = toPlane q + toPlane r := by
  exact plane_ext rfl rfl

theorem toPlane_smul (c : ℝ) (q : Point) : toPlane (c • q) = c • toPlane q := by
  exact plane_ext rfl rfl

/-- The coordinate equivalence, without any assertion that the two norms agree. -/
@[expose]
def linearEquiv : Point ≃ₗ[ℝ] Plane where
  toFun := toPlane
  invFun := fromPlane
  left_inv := fromPlane_toPlane
  right_inv := toPlane_fromPlane
  map_add' := toPlane_add
  map_smul' := toPlane_smul

/-- The coordinate homeomorphism between real pairs and the Euclidean plane. -/
def homeomorph : Point ≃ₜ Plane := linearEquiv.toContinuousLinearEquiv.toHomeomorph

theorem continuous_toPlane : Continuous toPlane :=
  linearEquiv.toContinuousLinearEquiv.continuous

theorem continuous_fromPlane : Continuous fromPlane :=
  linearEquiv.toContinuousLinearEquiv.symm.continuous

theorem image_eq_preimage (S : Set Point) :
    toPlane '' S = fromPlane ⁻¹' S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem isClosed_image {S : Set Point} (hS : IsClosed S) : IsClosed (toPlane '' S) := by
  rw [image_eq_preimage]
  exact hS.preimage continuous_fromPlane

theorem isConnected_image {S : Set Point} (hS : IsConnected S) :
    IsConnected (toPlane '' S) :=
  hS.image toPlane continuous_toPlane.continuousOn

theorem horizontal_image : toPlane '' horizontalArm = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem vertical_image : toPlane '' verticalArm = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem hallway_image : toPlane '' GerverSofa.hallway = Model.hallway := by
  simp only [GerverSofa.hallway, Model.hallway, Set.image_union,
    horizontal_image, vertical_image]

end GerverSofa.PartF.Coordinates

end

end

end

section

/-!
# F04: literal integral data and its branch primitives

The parameterized definitions below are the pinned upstream scalar integrals.
The phase boundaries are preserved. Integrating across the jumps will use
equality on open intervals, not an incorrect global continuity assertion for r.
-/

public section

noncomputable section
open MeasureTheory
namespace GerverSofa.PartF.Integrals

open Phases

/-- The reflected second switching angle `π/2 - θ`. -/
@[expose]
def eta (d : Reduced.Params) : ℝ := T - d.theta
/-- The reflected first switching angle `π/2 - φ`. -/
@[expose]
def tau (d : Reduced.Params) : ℝ := T - d.phi
/-- The switching-angle condition `0 ≤ φ ≤ θ ≤ π/4`. -/
@[expose]
def Ordered (d : Reduced.Params) : Prop :=
  0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ Real.pi / 4

theorem ordered_knots (d : Reduced.Params) (ho : Ordered d) :
    0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ eta d ∧
      eta d ≤ tau d ∧ tau d ≤ T := by
  rcases ho with ⟨h0, h1, h2⟩
  dsimp [eta, tau, T]
  exact ⟨h0, h1, by linarith, by linarith, by linarith⟩

/-- The integrand profile on phase 1. -/
@[expose]
def r1 (_d : Reduced.Params) (_t : ℝ) : ℝ := 1 / 2
/-- The integrand profile on phase 2. -/
@[expose]
def r2 (d : Reduced.Params) (t : ℝ) : ℝ := g2 d t
/-- The integrand profile on phase 3. -/
@[expose]
def r3 (d : Reduced.Params) (t : ℝ) : ℝ := g3 d t
/-- The integrand profile on phase 4. -/
@[expose]
def r4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b - (T - t - d.phi) * (1 + d.a) / 2 - (T - t - d.phi) ^ 2 / 4

/-- The piecewise phase profile used in the integral representation. -/
@[expose]
def r (d : Reduced.Params) (t : ℝ) : ℝ :=
  if t ≤ d.phi then r1 d t
  else if t ≤ d.theta then r2 d t
  else if t ≤ eta d then r3 d t
  else if t ≤ tau d then r4 d t
  else 0

/-- One minus the cosine-weighted profile integral from `t` to the last switching angle. -/
@[expose]
def xi (d : Reduced.Params) (t : ℝ) : ℝ :=
  1 - ∫ s in t..tau d, r d s * Real.cos s
/-- The sine-weighted profile integral from `t` to the last switching angle. -/
@[expose]
def zeta (d : Reduced.Params) (t : ℝ) : ℝ :=
  ∫ s in t..tau d, r d s * Real.sin s

/-- The rotation path expressed using the two profile integrals. -/
@[expose]
def path (d : Reduced.Params) (t : ℝ) : Point :=
  (if t ≤ d.phi then Real.cos t - 1
   else xi d (T - t) * Real.cos t + zeta d (T - t) * Real.sin t - 1,
   if t ≤ tau d then
     zeta d t * Real.cos t - (4 * xi d 0 - 2 - xi d t) * Real.sin t - 1
   else -(4 * xi d 0 - 3) * Real.sin t - 1)

/-- The derivative formula for the fourth phase profile. -/
def dg4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  (1 + d.a) / 2 + (T - d.phi - t) / 2

/-- The horizontal primitive assembled from a profile, its derivative, and an offset. -/
def primitiveX (V : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  V + g t * Real.sin t + gp t * Real.cos t
/-- The vertical primitive assembled from a profile, its derivative, and an offset. -/
def primitiveY (U : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  U + g t * Real.cos t - gp t * Real.sin t

/-- Horizontal primitive specialized to phase 1. -/
def X1 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V1 d) (r1 d) (fun _ => 0)
/-- Vertical primitive specialized to phase 1. -/
def Y1 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U1 d) (r1 d) (fun _ => 0)
/-- Horizontal primitive specialized to phase 2. -/
def X2 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V2 d) (g2 d) (fun _ => 1 / 2)
/-- Vertical primitive specialized to phase 2. -/
def Y2 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U2 d) (g2 d) (fun _ => 1 / 2)
/-- Horizontal primitive specialized to phase 3. -/
def X3 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V3 d) (g3 d) (fun _ => 1)
/-- Vertical primitive specialized to phase 3. -/
def Y3 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U3 d) (g3 d) (fun _ => 1)
/-- Horizontal primitive specialized to phase 4. -/
def X4 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V4 d) (g4 d) (dg4 d)
/-- Vertical primitive specialized to phase 4. -/
def Y4 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U4 d) (g4 d) (dg4 d)

/-- F05 repair: normalize only the scalar derivative, never typeclass arguments. -/
theorem primitiveX_hasDerivAt (V : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveX V g gp) ((g t + gpp) * Real.cos t) t := by
  change HasDerivAt (fun s => V + g s * Real.sin s + gp s * Real.cos s) _ t
  have h := ((hasDerivAt_const t V).fun_add
    (hg.fun_mul (Real.hasDerivAt_sin t))).fun_add
    (hgp.fun_mul (Real.hasDerivAt_cos t))
  exact h.congr_deriv (by ring)

theorem primitiveY_hasDerivAt (U : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveY U g gp) (-(g t + gpp) * Real.sin t) t := by
  change HasDerivAt (fun s => U + g s * Real.cos s - gp s * Real.sin s) _ t
  have h := ((hasDerivAt_const t U).fun_add
    (hg.fun_mul (Real.hasDerivAt_cos t))).fun_sub
    (hgp.fun_mul (Real.hasDerivAt_sin t))
  exact h.congr_deriv (by ring)

theorem g2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g2 d) (1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a + s - d.phi) / 2) _ t
  have h := (((hasDerivAt_const t (1 + d.a)).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)).div_const 2
  exact h.congr_deriv (by ring)

theorem g3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g3 d) 1 t := by
  change HasDerivAt (fun s => d.a + s - d.phi) _ t
  have h := ((hasDerivAt_const t d.a).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)
  exact h.congr_deriv (by ring)

theorem g4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g4 d) (dg4 d t) t := by
  change HasDerivAt (fun s => d.b + 1 / 2 -
    (T - d.phi - s) * (1 + d.a) / 2 - (T - d.phi - s)^2 / 4) _ t
  have h := (hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)
  have hfull := ((hasDerivAt_const t (d.b + 1 / 2)).fun_sub
    ((h.mul_const (1 + d.a)).div_const 2)).fun_sub ((h.pow 2).div_const 4)
  exact hfull.congr_deriv (by dsimp [dg4]; ring)

theorem dg4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (dg4 d) (-1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a) / 2 + (T - d.phi - s) / 2) _ t
  have h := (hasDerivAt_const t ((1 + d.a) / 2)).fun_add
    (((hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)).div_const 2)
  exact h.congr_deriv (by ring)

theorem X1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X1 d) (r1 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y1 d) (-r1 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X2 d) (r2 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y2 d) (-r2 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X3 d) (r3 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y3 d) (-r3 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X4 d) (r4 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y4 d) (-r4 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X1_join (d : Reduced.Params) :
    X1 d d.phi = X2 d d.phi := by
  dsimp [X1, X2, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y1_join (d : Reduced.Params) :
    Y1 d d.phi = Y2 d d.phi := by
  dsimp [Y1, Y2, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem X2_join (d : Reduced.Params) :
    X2 d d.theta = X3 d d.theta := by
  dsimp [X2, X3, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y2_join (d : Reduced.Params) :
    Y2 d d.theta = Y3 d d.theta := by
  dsimp [Y2, Y3, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem fourth_equation (d : Reduced.Params) (hd : Reduced.Equations d) :
    d.a + T - d.phi - d.theta - d.b +
      (1 / 2 : ℝ) * (d.theta - d.phi) * (1 + d.a) +
      (1 / 4 : ℝ) * (d.theta - d.phi) * (d.theta - d.phi) = 0 := by
  exact congrFun hd (3 : Fin 4)

theorem X3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    X3 d (eta d) = X4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [X3, X4, primitiveX, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.cos d.theta * he

theorem Y3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    Y3 d (eta d) = Y4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [Y3, Y4, primitiveY, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.sin d.theta * he

theorem X4_terminal (d : Reduced.Params) :
    X4 d (tau d) = 1 := by
  dsimp [X4, primitiveX, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem Y4_terminal (d : Reduced.Params) :
    Y4 d (tau d) = 0 := by
  dsimp [Y4, primitiveY, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem r_phase1 (d : Reduced.Params) {t : ℝ} (ht : t ≤ d.phi) :
    r d t = r1 d t := by simp only [r, ite_eq_left ht]

theorem r_phase2 (d : Reduced.Params) {t : ℝ}
    (hlo : d.phi < t) (hhi : t ≤ d.theta) : r d t = r2 d t := by
  simp only [r, ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

theorem r_phase3 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : d.theta < t) (hhi : t ≤ eta d) : r d t = r3 d t := by
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 hlo
  simp only [r, ite_eq_right (not_le.mpr hphi), ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

theorem r_phase4 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : eta d < t) (hhi : t ≤ tau d) : r d t = r4 d t := by
  have htheta : d.theta < t := lt_of_le_of_lt (ordered_knots d ho).2.2.1 hlo
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 htheta
  simp only [r, ite_eq_right (not_le.mpr hphi), ite_eq_right (not_le.mpr htheta),
    ite_eq_right (not_le.mpr hlo), ite_eq_left hhi]

end GerverSofa.PartF.Integrals

end

end

end

section

/-!
# F04: evaluation of the literal integrals on all four closed intervals

The fundamental theorem is applied to smooth branch primitives. Equality with
the discontinuous integrand is required only on the open interval. Adjacent
integrals are then added, using the proved matching values at every switch.
-/

public section

noncomputable section
open MeasureTheory
namespace GerverSofa.PartF.Integrals

open Phases

theorem integrate_branch (f f' P : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt P (f' t) t)
    (heq : ∀ t ∈ Set.Ioo a b, f t = f' t) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) = P b - P a := by
  have hi : IntervalIntegrable f' volume a b := hf'.intervalIntegrable a b
  have hf : IntervalIntegrable f volume a b := hi.congr_uIoo (by
    rw [Set.uIoo_of_le hab]
    intro t ht
    exact (heq t ht).symm)
  refine ⟨hf, ?_⟩
  calc
    (∫ t in a..b, f t) = ∫ t in a..b, f' t :=
      intervalIntegral.integral_congr_Ioo_of_le hab heq
    _ = P b - P a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hi

theorem cos_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r4 d u * Real.cos u)
    (X4 d) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X4_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [X4_terminal]

theorem sin_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r4 d u * Real.sin u)
    (fun u => -Y4 d u) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y4_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [Y4_terminal]; ring

theorem cos_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r3 d u * Real.cos u)
    (X3 d) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X3_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X3_join d hd]; ring

theorem sin_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r3 d u * Real.sin u)
    (fun u => -Y3 d u) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y3_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y3_join d hd]; ring

theorem cos_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r2 d u * Real.cos u)
    (X2 d) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X2_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X2_join d]; ring

theorem sin_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r2 d u * Real.sin u)
    (fun u => -Y2 d u) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y2_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y2_join d]; ring

theorem cos_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r1 d u * Real.cos u)
    (X1 d) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X1_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := cos_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X1_join d]; ring

theorem sin_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r1 d u * Real.sin u)
    (fun u => -Y1 d u) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y1_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := sin_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y1_join d]; ring

theorem xi_zeta_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    xi d t = X1 d t ∧ zeta d t = Y1 d t := by
  constructor
  · unfold xi
    rw [(cos_tail1 d ho hd t ht).2]
    ring
  · exact (sin_tail1 d ho hd t ht).2

theorem xi_zeta_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    xi d t = X2 d t ∧ zeta d t = Y2 d t := by
  constructor
  · unfold xi
    rw [(cos_tail2 d ho hd t ht).2]
    ring
  · exact (sin_tail2 d ho hd t ht).2

theorem xi_zeta_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    xi d t = X3 d t ∧ zeta d t = Y3 d t := by
  constructor
  · unfold xi
    rw [(cos_tail3 d ho hd t ht).2]
    ring
  · exact (sin_tail3 d ho hd t ht).2

theorem xi_zeta_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    xi d t = X4 d t ∧ zeta d t = Y4 d t := by
  constructor
  · unfold xi
    rw [(cos_tail4 d ho t ht).2]
    ring
  · exact (sin_tail4 d ho t ht).2

theorem xi_zero (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) : xi d 0 = V1 d := by
  have h := (xi_zeta_phase1 d ho hd 0 ⟨le_rfl, ho.1⟩).1
  simpa [X1, primitiveX] using h

/-- The projection `ξ sin t + ζ cos t` used in the integral identities. -/
@[expose]
def W (d : Reduced.Params) (t : ℝ) : ℝ :=
  xi d t * Real.sin t + zeta d t * Real.cos t

theorem primitive_W (g gp U V t : ℝ) :
    (V + g * Real.sin t + gp * Real.cos t) * Real.sin t +
      (U + g * Real.cos t - gp * Real.sin t) * Real.cos t =
      g + U * Real.cos t + V * Real.sin t := by
  linear_combination g * Real.sin_sq_add_cos_sq t

theorem W_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    W d t = r1 d t + U1 d * Real.cos t + V1 d * Real.sin t := by
  rcases xi_zeta_phase1 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (r1 d t) (0) (U1 d) (V1 d) t

theorem W_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    W d t = g2 d t + U2 d * Real.cos t + V2 d * Real.sin t := by
  rcases xi_zeta_phase2 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g2 d t) (1 / 2) (U2 d) (V2 d) t

theorem W_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    W d t = g3 d t + U3 d * Real.cos t + V3 d * Real.sin t := by
  rcases xi_zeta_phase3 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g3 d t) (1) (U3 d) (V3 d) t

theorem W_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    W d t = g4 d t + U4 d * Real.cos t + V4 d * Real.sin t := by
  rcases xi_zeta_phase4 d ho t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g4 d t) (dg4 d t) (U4 d) (V4 d) t

end GerverSofa.PartF.Integrals

end

end

end

section

/-!
# F05: the four-parameter dictionary satisfies the full 22 equations

These polynomial certificates use the four reduced equations and the two
trigonometric circle identities. No box membership or uniqueness is assumed.
They do not identify the dictionary with the independently certified 22D root.
The module is independent of the F04 integral evaluation.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem dictionary_equations (d : Reduced.Params) (hd : Reduced.Equations d) :
    Romik.Equations (dictionary d) := by
  have h1 := congrFun hd (0 : Fin 4)
  have h2 := congrFun hd (1 : Fin 4)
  have h3 := congrFun hd (2 : Fin 4)
  have h4 := congrFun hd (3 : Fin 4)
  change d.a * (Real.cos d.theta - Real.cos d.phi) -
    2 * d.b * Real.sin d.phi + (d.theta - d.phi - 1) * Real.cos d.theta -
    Real.sin d.theta + Real.cos d.phi + Real.sin d.phi = 0 at h1
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi + 3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h2
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h3
  change d.a + Real.pi / 2 - d.phi - d.theta - d.b +
    1 / 2 * (d.theta - d.phi) * (1 + d.a) +
    1 / 4 * (d.theta - d.phi) * (d.theta - d.phi) = 0 at h4
  have hcphi := Real.sin_sq_add_cos_sq d.phi
  have hctheta := Real.sin_sq_add_cos_sq d.theta
  change Romik.system (dictionary d) = 0
  funext i
  fin_cases i
  -- Row 0: exact scalar certificate.
  · change (dictionary d).e1 - (dictionary d).a1 = 0
    dsimp [dictionary, T]; ring
  -- Row 1: exact scalar certificate.
  · change (dictionary d).e2 + (dictionary d).a2 = 0
    dsimp [dictionary, T]; ring
  -- Row 2: exact scalar certificate.
  · change (dictionary d).d1 + (dictionary d).b1 - Real.pi / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 3: exact scalar certificate.
  · change (dictionary d).d2 - (dictionary d).b2 - Real.pi / 4 * (2 * (dictionary d).b1 - Real.pi
    / 4) = 0
    dsimp [dictionary, T]; ring
  -- Row 4: exact scalar certificate.
  · change (dictionary d).c2 - (dictionary d).c1 + Real.pi / 2 = 0
    dsimp [dictionary, T]; ring
  -- Row 5: exact scalar certificate.
  · change (dictionary d).k11 - 1 + (dictionary d).a1 = 0
    dsimp [dictionary, T]; ring
  -- Row 6: exact scalar certificate.
  · change (dictionary d).k12 - 1 / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 7: exact scalar certificate.
  · change (dictionary d).a2 + 1 / 4 = 0
    dsimp [dictionary, T]; ring
  -- Row 8: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).1 - (Romik.path2 (dictionary d) (d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.phi) ^ 2) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 9: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).2 - (Romik.path2 (dictionary d) (d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi
  -- Row 10: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).1 - (Romik.rot (d.phi)
    (Romik.alphaBeta2 (dictionary d) (d.phi))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-2 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-2 * (d.b) * (Real.sin d.phi) + -2 * (Real.sin d.phi) + (-1 / 2 : ℝ)) * hcphi
  -- Row 11: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).2 - (Romik.rot (d.phi)
    (Romik.alphaBeta2 (dictionary d) (d.phi))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) ^ 2 + -1) * h2 +
      (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-2 * (d.a) * (Real.sin d.phi) + -3 * (d.a) * (Real.sin d.theta) + 3 * (d.b) * (Real.cos
        d.phi) + 3 * (d.phi) * (Real.sin d.theta) + -3 * (d.theta) * (Real.sin d.theta) + (1 / 2 :
        ℝ) * (Real.sin d.phi) + 3 * (Real.sin d.theta) + -3 * (Real.cos d.theta)) * hcphi
  -- Row 12: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).1 - (Romik.path3 (dictionary d) (d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 13: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).2 - (Romik.path3 (dictionary d) (d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.theta)) * h4
  -- Row 14: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).1 - (Romik.rot
    (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 15: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).2 - (Romik.rot
    (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 16: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).1 - (Romik.path4 (dictionary d)
    (Real.pi / 2 - d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 17: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).2 - (Romik.path4 (dictionary d)
    (Real.pi / 2 - d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 18: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).1 - (Romik.path5 (dictionary d)
    (Real.pi / 2 - d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + -1) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 19: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).2 - (Romik.path5 (dictionary d)
    (Real.pi / 2 - d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-1 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-1 * (d.b) * (Real.sin d.phi) + -1 * (Real.sin d.phi) + (-1 / 4 : ℝ)) * hcphi
  -- Row 20: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).1 - ((Romik.path3 (dictionary d) (Real.pi / 2 -
    d.theta)).1 - (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.sin (Real.pi
    / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + (-1 / 2 : ℝ)) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) *
        (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) *
        (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin
        d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 21: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).2 - ((Romik.path3 (dictionary d) (Real.pi / 2 -
    d.theta)).2 + (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.cos (Real.pi
    / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((-1 / 2 : ℝ)) * h1 +
      (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi

/-- Read back the four free parameters from the 22D representation. -/
@[expose]
def undictionary (p : Romik.Params) : Reduced.Params where
  a := p.phi - 1 - 2 * p.b1
  b := p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4
  phi := p.phi
  theta := p.theta

theorem undictionary_dictionary (d : Reduced.Params) :
    undictionary (dictionary d) = d := by
  rcases d with ⟨a, b, phi, theta⟩
  dsimp [undictionary, dictionary]
  congr 1 <;> ring

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F06: reverse reduction from the full Romik equations

This direction uses velocity matching and the two contact equations. It does
not assume membership in either numerical box or any strict angle inequality.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [Romik.rot] at hx hy
  apply Prod.ext
  · linear_combination Real.cos t * hx + Real.sin t * hy -
      (z.1 - w.1) * Real.sin_sq_add_cos_sq t
  · linear_combination -Real.sin t * hx + Real.cos t * hy -
      (z.2 - w.2) * Real.sin_sq_add_cos_sq t

theorem alphaBeta12_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta1 p p.phi = Romik.alphaBeta2 p p.phi := by
  apply rot_injective p.phi
  apply Prod.ext
  · have h := congrFun hp (10 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).1 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (11 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).2 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem alphaBeta23_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta2 p p.theta = Romik.alphaBeta3 p p.theta := by
  apply rot_injective p.theta
  apply Prod.ext
  · have h := congrFun hp (14 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).1 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (15 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).2 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem c2_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c2 = -2 - 2 * p.b1 := by
  have h := congrArg Prod.fst (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  linarith only [h]

theorem c1_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c1 = Real.pi / 2 - 2 - 2 * p.b1 := by
  have hs := Romik.c2_eq_c1_sub_halfPi_of_equations hp
  have hc := c2_eq_of_full hp
  linarith only [hs, hc]

theorem reverse_equation4 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 3 = 0 := by
  have h := congrArg Prod.snd (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  rw [c1_eq_of_full hp] at h
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0
  dsimp [undictionary]
  linear_combination -h

theorem reverse_equation3 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 2 = 0 := by
  have ha := congrArg Prod.fst (alphaBeta12_eq hp)
  have hb := congrArg Prod.snd (alphaBeta12_eq hp)
  dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at ha hb
  rw [Romik.a2_eq_neg_quarter_of_equations hp] at ha hb
  change (undictionary p).a * Real.cos (undictionary p).phi -
    Real.sin (undictionary p).phi - 1 / 2 +
    1 / 2 * Real.cos (undictionary p).phi -
    (undictionary p).b * Real.sin (undictionary p).phi = 0
  dsimp [undictionary]
  linear_combination Real.cos p.phi * ha + Real.sin p.phi * hb +
    (1 / 2 : ℝ) * Real.sin_sq_add_cos_sq p.phi

theorem reverse_equation1 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 0 = 0 := by
  have h9 := congrFun hp (9 : Fin 22)
  have h13 := congrFun hp (13 : Fin 22)
  have h21 := congrFun hp (21 : Fin 22)
  change (Romik.path1 p p.phi).2 - (Romik.path2 p p.phi).2 = 0 at h9
  change (Romik.path2 p p.theta).2 - (Romik.path3 p p.theta).2 = 0 at h13
  change (Romik.path1 p p.phi).2 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).2 +
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.cos (Real.pi / 2 - p.theta)) = 0 at h21
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h9 h13 h21
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h13 h21
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h21
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (Real.cos (undictionary p).theta -
    Real.cos (undictionary p).phi) - 2 * (undictionary p).b *
    Real.sin (undictionary p).phi +
    ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.cos (undictionary p).theta - Real.sin (undictionary p).theta +
    Real.cos (undictionary p).phi + Real.sin (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h21 + 2 * h9 + 2 * h13 + 2 * Real.sin p.theta * h4

theorem reverse_equation2 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 1 = 0 := by
  have h8 := congrFun hp (8 : Fin 22)
  have h12 := congrFun hp (12 : Fin 22)
  have h20 := congrFun hp (20 : Fin 22)
  change (Romik.path1 p p.phi).1 - (Romik.path2 p p.phi).1 = 0 at h8
  change (Romik.path2 p p.theta).1 - (Romik.path3 p p.theta).1 = 0 at h12
  change (Romik.path1 p p.phi).1 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).1 -
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.sin (Real.pi / 2 - p.theta)) = 0 at h20
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h8 h12 h20
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h12 h20
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h20
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (3 * Real.sin (undictionary p).theta +
    Real.sin (undictionary p).phi) - 2 * (undictionary p).b *
    Real.cos (undictionary p).phi +
    3 * ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.sin (undictionary p).theta + 3 * Real.cos (undictionary p).theta -
    Real.sin (undictionary p).phi + Real.cos (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h20 + 2 * h8 + 2 * h12 + 2 * Real.cos p.theta * h4

theorem undictionary_equations {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.Equations (undictionary p) := by
  change Reduced.system (undictionary p) = 0
  funext i
  fin_cases i
  · exact reverse_equation1 hp
  · exact reverse_equation2 hp
  · exact reverse_equation3 hp
  · exact reverse_equation4 hp

end GerverSofa.PartF.Phases

end

end

end

section

/-!
# F06: the reverse parameters determine the full solution

Velocity matching determines the shape coefficients. Positional matching
then determines each successive translation. No numerical enclosure is used.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Phases

theorem full_equations_injective {p q : Romik.Params}
    (hp : Romik.Equations p) (hq : Romik.Equations q)
    (h : undictionary p = undictionary q) : p = q := by
  have hphi : p.phi = q.phi := congrArg Reduced.Params.phi h
  have htheta : p.theta = q.theta := congrArg Reduced.Params.theta h
  have ha := congrArg Reduced.Params.a h
  have hb := congrArg Reduced.Params.b h
  dsimp [undictionary] at ha hb
  have hb1 : p.b1 = q.b1 := by
    rw [hphi] at ha
    linarith only [ha]
  have hb2 : p.b2 = q.b2 := by
    simp only [hphi, hb1] at hb
    linarith only [hb]
  have ha2 : p.a2 = q.a2 := by
    rw [Romik.a2_eq_neg_quarter_of_equations hp,
      Romik.a2_eq_neg_quarter_of_equations hq]
  have ha1 : p.a1 = q.a1 := by
    have hpa := congrArg Prod.fst (alphaBeta12_eq hp)
    have hpb := congrArg Prod.snd (alphaBeta12_eq hp)
    have hqa := congrArg Prod.fst (alphaBeta12_eq hq)
    have hqb := congrArg Prod.snd (alphaBeta12_eq hq)
    dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at hpa hpb hqa hqb
    simp only [hphi, hb1, hb2, ha2] at hpa hpb
    linear_combination (-Real.sin q.phi / 2) * hpa +
      (Real.sin q.phi / 2) * hqa + (Real.cos q.phi / 2) * hpb -
      (Real.cos q.phi / 2) * hqb -
      (p.a1 - q.a1) * Real.sin_sq_add_cos_sq q.phi
  have hc1 : p.c1 = q.c1 := by
    rw [c1_eq_of_full hp, c1_eq_of_full hq, hb1]
  have hc2 : p.c2 = q.c2 := by
    rw [c2_eq_of_full hp, c2_eq_of_full hq, hb1]
  have hd1 : p.d1 = q.d1 := by
    rw [Romik.d1_eq_quarterPi_sub_b1_of_equations hp,
      Romik.d1_eq_quarterPi_sub_b1_of_equations hq, hb1]
  have hd2 : p.d2 = q.d2 := by
    rw [Romik.d2_eq_b2_add_quarterPi_correction_of_equations hp,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations hq, hb1, hb2]
  have he1 : p.e1 = q.e1 := by
    rw [Romik.e1_eq_a1_of_equations hp, Romik.e1_eq_a1_of_equations hq, ha1]
  have he2 : p.e2 = q.e2 := by
    rw [Romik.e2_eq_neg_a2_of_equations hp, Romik.e2_eq_neg_a2_of_equations hq, ha2]
  have hk11 : p.k11 = q.k11 := by
    have h5p := congrFun hp (5 : Fin 22)
    have h5q := congrFun hq (5 : Fin 22)
    change p.k11 - 1 + p.a1 = 0 at h5p
    change q.k11 - 1 + q.a1 = 0 at h5q
    linarith only [h5p, h5q, ha1]
  have hk12 : p.k12 = q.k12 := by
    rw [Romik.k12_eq_quarter_of_equations hp, Romik.k12_eq_quarter_of_equations hq]
  have hpath1 (t : ℝ) : Romik.path1 p t = Romik.path1 q t := by
    simp only [Romik.path1, ha1, ha2, hk11, hk12]
  have hj2 : Romik.path1 p (q.phi) = Romik.path2 p (q.phi) := by
    simpa only [hphi] using Romik.match_path12_of_equations hp
  have hx2 : Romik.path2 p (q.phi) = Romik.path2 q (q.phi) :=
    hj2.symm.trans ((hpath1 (q.phi)).trans (Romik.match_path12_of_equations hq))
  dsimp [Romik.path2, Romik.addK] at hx2
  simp only [hb1, hb2] at hx2
  have hk21 : p.k21 = q.k21 := add_left_cancel (congrArg Prod.fst hx2)
  have hk22 : p.k22 = q.k22 := add_left_cancel (congrArg Prod.snd hx2)
  have hpath2 (t : ℝ) : Romik.path2 p t = Romik.path2 q t := by
    simp only [Romik.path2, hb1, hb2, hk21, hk22]
  have hj3 : Romik.path2 p (q.theta) = Romik.path3 p (q.theta) := by
    simpa only [htheta] using Romik.match_path23_of_equations hp
  have hx3 : Romik.path3 p (q.theta) = Romik.path3 q (q.theta) :=
    hj3.symm.trans ((hpath2 (q.theta)).trans (Romik.match_path23_of_equations hq))
  dsimp [Romik.path3, Romik.addK] at hx3
  simp only [hc1, hc2] at hx3
  have hk31 : p.k31 = q.k31 := add_left_cancel (congrArg Prod.fst hx3)
  have hk32 : p.k32 = q.k32 := add_left_cancel (congrArg Prod.snd hx3)
  have hpath3 (t : ℝ) : Romik.path3 p t = Romik.path3 q t := by
    simp only [Romik.path3, hc1, hc2, hk31, hk32]
  have hj4 : Romik.path3 p (Real.pi / 2 - q.theta) = Romik.path4 p (Real.pi / 2 - q.theta) := by
    simpa only [htheta] using Romik.match_path34_of_equations hp
  have hx4 : Romik.path4 p (Real.pi / 2 - q.theta) = Romik.path4 q (Real.pi / 2 - q.theta) :=
    hj4.symm.trans ((hpath3 (Real.pi / 2 - q.theta)).trans (Romik.match_path34_of_equations hq))
  dsimp [Romik.path4, Romik.addK] at hx4
  simp only [hd1, hd2] at hx4
  have hk41 : p.k41 = q.k41 := add_left_cancel (congrArg Prod.fst hx4)
  have hk42 : p.k42 = q.k42 := add_left_cancel (congrArg Prod.snd hx4)
  have hpath4 (t : ℝ) : Romik.path4 p t = Romik.path4 q t := by
    simp only [Romik.path4, hd1, hd2, hk41, hk42]
  have hj5 : Romik.path4 p (Real.pi / 2 - q.phi) = Romik.path5 p (Real.pi / 2 - q.phi) := by
    simpa only [hphi] using Romik.match_path45_of_equations hp
  have hx5 : Romik.path5 p (Real.pi / 2 - q.phi) = Romik.path5 q (Real.pi / 2 - q.phi) :=
    hj5.symm.trans ((hpath4 (Real.pi / 2 - q.phi)).trans (Romik.match_path45_of_equations hq))
  dsimp [Romik.path5, Romik.addK] at hx5
  simp only [he1, he2] at hx5
  have hk51 : p.k51 = q.k51 := add_left_cancel (congrArg Prod.fst hx5)
  have hk52 : p.k52 = q.k52 := add_left_cancel (congrArg Prod.snd hx5)
  cases p
  cases q
  congr 1

theorem dictionary_undictionary_of_equations {p : Romik.Params}
    (hp : Romik.Equations p) : dictionary (undictionary p) = p := by
  apply full_equations_injective (dictionary_equations _ (undictionary_equations hp)) hp
  exact undictionary_dictionary (undictionary p)

end GerverSofa.PartF.Phases

end

end

end

end

end

end
