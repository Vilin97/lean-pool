/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import LeanPool.EcTateLean.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Basic
import LeanPool.EcTateLean.FieldTheory.PerfectClosure
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Common

/-!
# LeanPool.EcTateLean.Algebra.EllipticCurve.Model

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.EllipticCurve.Model`.
-/
-- import Aesop


-- TODO cleanup variables, sections assumption strength

--#print AddCommGroup.toDivisionCommMonoid -- TODO a way to tell if this works



/-- A model of a (possibly singular) elliptic curve is given
by `a` invariants $$a₁, a₂, a₃, a₄, a₆$$ which represent the curve
$$
y^2 + a₁ xy + a₃ y = x^ 3 + a₂ x ^ 2 + a₄ x + a₆
$$
-/
structure Model (R : Type u) [CommRing R] where
  /-- The `a₁` coefficient of the Weierstrass model. -/
  a1 : R
  /-- The `a₂` coefficient of the Weierstrass model. -/
  a2 : R
  /-- The `a₃` coefficient of the Weierstrass model. -/
  a3 : R
  /-- The `a₄` coefficient of the Weierstrass model. -/
  a4 : R
  /-- The `a₆` coefficient of the Weierstrass model. -/
  a6 : R
deriving Inhabited, DecidableEq

namespace Model
variable {R : Type u} [CommRing R]

instance [Repr R] : Repr (Model R) :=
  ⟨fun (e : Model R) _ => repr (e.a1, e.a2, e.a3, e.a4, e.a6)⟩

/-- The `b₂` invariant of a Weierstrass model. -/
def b2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

/-- The `b₄` invariant of a Weierstrass model. -/
def b4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

/-- The `b₆` invariant of a Weierstrass model. -/
def b6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

/-- The `b₈` invariant of a Weierstrass model. -/
def b8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

/-- The `b₅` invariant of a Weierstrass model (from Connell). -/
def b5 (e : Model R) : R := e.a1 * e.a4 - 2 * e.a2 * e.a3

/-- The `b₇` invariant of a Weierstrass model (from Connell). -/
def b7 (e : Model R) : R := e.a1 * (e.a3 ^ 2 - 12 * e.a6) + 8 * e.a3 * e.a4

lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 :=
by
  simp only [b2, b4, b6, b8]
  ring

/-- The `c₄` invariant of a Weierstrass model. -/
def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

/-- The `c₆` invariant of a Weierstrass model. -/
def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

/-- The discriminant of a Weierstrass model. -/
def discr (e : Model R) : R :=
  -e.b2 * e.b2 * e.b8 - 8 * e.b4 ^ 3 - 27 * e.b6 * e.b6 + 9 * e.b2 * e.b4 * e.b6

lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 3 - e.c6 ^ 2 :=
by
  simp only [c4, c6, discr, mul_sub, mul_add]
  rw [(by ring : 1728 * (-e.b2 * e.b2 * e.b8) = -432 * e.b2 * e.b2 * (4 * e.b8))]
  rw [b8_identity]
  ring

-- TODO rename
/-- A change of coordinates `(u, r, s, t)` of a Weierstrass model, with `u` a
unit and `r`, `s`, `t` ring elements. -/
structure urstTransform (R : Type _) [Ring R] where
  /-- The scaling unit of the change of coordinates. -/
  u : Rˣ
  /-- The `x`-translation of the change of coordinates. -/
  r : R
  /-- The `xy`-shear of the change of coordinates. -/
  s : R
  /-- The `y`-translation of the change of coordinates. -/
  t : R

namespace urstTransform
instance instMulURSTTransform : Mul (urstTransform R) where
  mul f g := ⟨f.u * g.u, f.r + f.u * g.r, f.s + f.u * g.s, f.t + f.u * g.t⟩
lemma mul_def (f g : urstTransform R) :
  f * g = ⟨f.u * g.u, f.r + f.u * g.r, f.s + f.u * g.s, f.t + f.u * g.t⟩ := rfl
instance : One (urstTransform R) where
  one := ⟨1, 0, 0, 0⟩
lemma one_def : (1 : urstTransform R) = ⟨1, 0, 0, 0⟩ := rfl

instance : Monoid (urstTransform R) where
  mul_one := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  one_mul := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  mul_assoc := by
    intros
    simp only [urstTransform.mul_def, mk.injEq]
    refine ⟨mul_assoc _ _ _, ?_, ?_, ?_⟩ <;> push_cast <;> ring
instance : Inv (urstTransform R) where
  inv f := ⟨f.u⁻¹, -f.u⁻¹ * f.r, -f.u⁻¹ * f.s, -f.u⁻¹ * f.t⟩
lemma inv_def (f : urstTransform R) :
  f⁻¹ = ⟨f.u⁻¹, -f.u⁻¹ * f.r, -f.u⁻¹ * f.s, -f.u⁻¹ * f.t⟩ := rfl

instance : Group (urstTransform R) where
  inv_mul_cancel := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def, urstTransform.inv_def]
  mul_one := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  one_mul := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  mul_assoc := by
    intros
    simp only [urstTransform.mul_def, mk.injEq]
    refine ⟨mul_assoc _ _ _, ?_, ?_, ?_⟩ <;> push_cast <;> ring

end urstTransform

-- TODO maybe define as a subgroup?
/-- The change-of-coordinates transformations with trivial scaling unit `u = 1`. -/
def rstTransform := {urst : urstTransform R // urst.u = 1}

--TODO instance Group
/-- The Weierstrass model obtained from `e` by the change of coordinates
`(1, r, s, t)`. -/
def rstIso (r s t : R) (e : Model R) : Model R :=
{ a1 := e.a1 + 2*s
  a2 := e.a2 - s*e.a1 + 3*r - s*s
  a3 := e.a3 + r*e.a1 + 2*t
  a4 := e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t
  a6 := e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1) }

lemma rst_b2 (r s t : R) (e : Model R) : (rstIso r s t e).b2 = e.b2 + 12*r := by
  simp [rstIso, b2]
  ring

lemma rst_b4 (r s t : R) (e : Model R) :
  (rstIso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  simp only [rstIso, b2, b4]
  ring

lemma rst_b6 (r s t : R) (e : Model R) :
  (rstIso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r :=
by
  simp only [rstIso, b2, b4, b6]
  ring

lemma rst_b8 (r s t : R) (e : Model R) :
  (rstIso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r :=
by
  simp only [rstIso, b2, b4, b6, b8]
  ring

@[simp]
lemma rst_c4 (r s t : R) (e : Model R) :
  (rstIso r s t e).c4 = e.c4 :=
by
  simp only [rstIso, b2, b4, c4]
  ring

@[simp]
lemma rst_c6 (r s t : R) (e : Model R) :
  (rstIso r s t e).c6 = e.c6 :=
by
  simp only [rstIso, b2, b4, b6, c6]
  ring

lemma rst_discr (r s t : R) (e : Model R) : (rstIso r s t e).discr = e.discr :=
by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  simp only [mul_add]
  rw [(by ring :
    (-(b2 e + 12 * r) * b2 e + -(b2 e + 12 * r) * (12 * r)) * b8 e =
      -(b2 e ^ 2 * b8 e) + (- (3 * r) * b2 e + -(b2 e + 12 * r) * (3 * r)) * (4 * b8 e))]
  rw [b8_identity]
  ring

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Pushes a Weierstrass model forward along a ring homomorphism `f`. -/
@[simps]
def map : Model R → Model S := fun e => ⟨f e.a1, f e.a2, f e.a3, f e.a4, f e.a6⟩

@[simp] lemma map_b2 : (map f e).b2 = f e.b2 := by simp [Model.b2, map_ofNat]
@[simp] lemma map_b4 : (map f e).b4 = f e.b4 := by simp [Model.b4, map_ofNat]
@[simp] lemma map_b5 : (map f e).b5 = f e.b5 := by simp [Model.b5, map_ofNat]
@[simp] lemma map_b6 : (map f e).b6 = f e.b6 := by simp [Model.b6, map_ofNat]
@[simp] lemma map_b7 : (map f e).b7 = f e.b7 := by simp [Model.b7, map_ofNat]
@[simp] lemma map_b8 : (map f e).b8 = f e.b8 := by simp [Model.b8, map_ofNat]

@[simp] lemma map_c4 : (map f e).c4 = f e.c4 := by simp [Model.c4, map_ofNat]
@[simp] lemma map_c6 : (map f e).c6 = f e.c6 := by simp [Model.c6, map_ofNat]

@[simp] lemma map_discr : (map f e).discr = f e.discr := by simp [Model.discr, map_ofNat]

/-- The Weierstrass polynomial of `e` evaluated at a point `P = (x, y)`, i.e.
the difference of the two sides of the Weierstrass equation. -/
def weierstrass (e : Model R) (P : R × R) : R :=
  P.2 ^ 2 + e.a1 * P.1 * P.2 + e.a3 * P.2 - (P.1 ^ 3 + e.a2 * P.1 ^ 2 + e.a4 * P.1 + e.a6)

--partial derivation library?

/-- The partial derivative of the Weierstrass polynomial with respect to `x`,
evaluated at `P`. -/
def dweierstrassDx (e : Model R) (P : R × R) : R :=
  e.a1 * P.2 - (3 * P.1 ^ 2 + 2 * e.a2 * P.1 + e.a4)

/-- The partial derivative of the Weierstrass polynomial with respect to `y`,
evaluated at `P`. -/
def dweierstrassDy (e : Model R) (P : R × R) : R :=
  2 * P.2 + e.a1 * P.1 + e.a3

@[simp]
lemma weierstrass_map (e : Model R) (P : R × R) : weierstrass (e.map f) (P.map f f) =
  f (weierstrass e P) :=
by simp [weierstrass]

@[simp]
lemma dweierstrassDx_map (e : Model R) (P : R × R) : dweierstrassDx (e.map f) (P.map f f) =
  f (dweierstrassDx e P) :=
by simp [dweierstrassDx, map_ofNat]

@[simp]
lemma dweierstrassDy_map (e : Model R) (P : R × R) : dweierstrassDy (e.map f) (P.map f f) =
  f (dweierstrassDy e P) :=
by simp [dweierstrassDy, map_ofNat]

/--
The discriminant equals (minus) the standard order-`a6` generator of the elimination ideal
of the Weierstrass and partial-derivative polynomials. This identity (verified with
`Singular.jl`, part of `OSCAR`) is the negative of the `a6`-resultant polynomial below.
-/
lemma discr_eq_neg_singular (e : Model R) : e.discr = -(
  e.a1^4*e.a2*e.a3^2 - e.a1^5*e.a3*e.a4 + e.a1^6*e.a6 + 8*e.a1^2*e.a2^2*e.a3^2 - e.a1^3*e.a3^3
    - 8*e.a1^3*e.a2*e.a3*e.a4 - e.a1^4*e.a4^2 + 12*e.a1^4*e.a2*e.a6 + 16*e.a2^3*e.a3^2
    - 36*e.a1*e.a2*e.a3^3 - 16*e.a1*e.a2^2*e.a3*e.a4 + 30*e.a1^2*e.a3^2*e.a4 - 8*e.a1^2*e.a2*e.a4^2
    + 48*e.a1^2*e.a2^2*e.a6 - 36*e.a1^3*e.a3*e.a6 + 27*e.a3^4 - 72*e.a2*e.a3^2*e.a4
    - 16*e.a2^2*e.a4^2 + 96*e.a1*e.a3*e.a4^2 + 64*e.a2^3*e.a6 - 144*e.a1*e.a2*e.a3*e.a6
    - 72*e.a1^2*e.a4*e.a6 + 64*e.a4^3 + 216*e.a3^2*e.a6 - 288*e.a2*e.a4*e.a6 + 432*e.a6^2) :=
by
  simp only [discr, b2, b4, b6, b8]
  ring



lemma discr_in_jacobian_ideal (e : Model R) (P : R × R) : e.discr =
  -((48*P.1*P.2*e.a2^2 +24*e.a1*e.a2*e.a6 +216*P.2*e.a6 +P.2*e.a1^6 +11*P.2*e.a1^4*e.a2
      +P.1*e.a1^4*e.a3 +38*P.1*e.a1^2*e.a2*e.a3 +8*e.a1^2*e.a2^2*e.a3
  +e.a1^4*e.a2*e.a3 +40*P.2*e.a1^2*e.a2^2 +32*P.2*e.a2^3 +24*P.1*P.2*e.a1*e.a3 +30*P.1^2*e.a2*e.a3
      +3*P.1*e.a1^3*e.a4 +60*P.1^2*e.a1*e.a4 +30*P.1^2*e.a1^2*e.a3
  +31*e.a1^2*e.a3*e.a4 +144*P.2^2*e.a3 +198*P.2*e.a3^2 +27*e.a3^3 +60*e.a1*e.a4^2 +36*P.1*e.a1*e.a6
      +76*P.1*e.a2^2*e.a3 +16*e.a2^3*e.a3 +84*P.1*e.a1*e.a2*e.a4
  -(36*e.a3*e.a6 +P.1^2*e.a1^5 +P.1*e.a1^5*e.a2 +P.1*P.2*e.a1^4 +9*P.1^2*e.a1^3*e.a2
      +10*P.1*e.a1^3*e.a2^2 +e.a1^5*e.a4 +6*P.2^2*e.a1^3 +8*P.1*P.2*e.a1^2*e.a2
  +24*P.1^2*e.a1*e.a2^2 +32*P.1*e.a1*e.a2^3 +35*P.2*e.a1^3*e.a3 +e.a1^3*e.a3^2 +9*e.a1^3*e.a2*e.a4
      +48*P.2^2*e.a1*e.a2 +134*P.2*e.a1*e.a2*e.a3 +27*P.1*e.a1*e.a3^2 +36*e.a1*e.a2*e.a3^2
  +58*P.2*e.a1^2*e.a4 +24*e.a1*e.a2^2*e.a4 +144*P.1*P.2*e.a4 +120*P.2*e.a2*e.a4 +168*P.1*e.a3*e.a4
      +34*e.a2*e.a3*e.a4))*(dweierstrassDy e P)
  +(e.a1^2*e.a3^2 +12*e.a1^2*e.a6 +16*e.a2^2*e.a4 +32*P.1*e.a2^3 +e.a1^4*e.a4 +144*P.1*e.a6
      +48*e.a2*e.a6 +P.1*e.a1^4*e.a2 +84*P.1*e.a3^2 +56*P.2*e.a1*e.a4 +8*e.a1^2*e.a2*e.a4
      +28*P.2*e.a1^2*e.a3 +52*P.2*e.a2*e.a3
  +96*P.1*P.2*e.a3 +8*P.1*e.a1^2*e.a2^2 +38*e.a2*e.a3^2 +32*P.1^2*e.a2^2
  -(2*P.1*e.a1^3*e.a3 +112*P.1*e.a2*e.a4 +e.a1^3*e.a2*e.a3 +36*e.a1*e.a3*e.a4 +96*P.1^2*e.a4
      +32*P.1*P.2*e.a1*e.a2 +32*P.2*e.a1*e.a2^2 +64*e.a4^2
  +4*P.1*P.2*e.a1^3 +10*P.2*e.a1^3*e.a2 +P.2*e.a1^5 +8*e.a1*e.a2^2*e.a3
      +46*P.1*e.a1*e.a2*e.a3))*(dweierstrassDx e P)
  +(60*e.a1^2*e.a4 +288*P.1*e.a4 +240*e.a2*e.a4 +12*P.2*e.a1^3 +36*e.a1^3*e.a3 +96*P.2*e.a1*e.a2
      +168*e.a1*e.a2*e.a3
  -(432*e.a6 +e.a1^6 +288*P.2*e.a3 +252*e.a3^2 +12*e.a1^4*e.a2 +48*e.a1^2*e.a2^2 +96*P.1*e.a2^2
      +64*e.a2^3))*(weierstrass e P))
 :=
by
  rw [discr_eq_neg_singular]
  simp only [weierstrass, dweierstrassDx, dweierstrassDy]
  ring

/-- The change of variables on points induced by the change of coordinates
`(1, r, s, t)`. -/
def varChange (r s t : R) (P' : R × R) : R × R :=
  (P'.1 + r, P'.2 + s * P'.1 + t)

@[simp]
lemma varChange_comp (r s t : R) (r' s' t' : R) (P : R × R) :
  varChange r s t (varChange r' s' t' P) = varChange (r + r') (s + s') (t + t' + s * r') P :=
by
  simp only [varChange, Prod.mk.injEq]
  apply And.intro <;>
  ring

@[simp]
lemma varChange_zero (P : R × R) : varChange (0 : R) 0 0 P = P :=
by simp [varChange]

-- TODO probably these proofs should be more conceptual

theorem weierstrass_iso_eq_varChange (e : Model R) (P : R × R) :
  weierstrass (rstIso r s t e) P = weierstrass e (varChange r s t P) :=
by
  simp only [weierstrass, rstIso, varChange]
  ring

theorem dweierstrassDx_iso_eq_varChange (e : Model R) (P : R × R) :
  dweierstrassDx (rstIso r s t e) P =
  dweierstrassDx e (varChange r s t P) + s * dweierstrassDy e (varChange r s t P) :=
by
  simp only [dweierstrassDx, dweierstrassDy, rstIso, varChange]
  ring

theorem dweierstrassDy_iso_eq_varChange (e : Model R) (P : R × R) :
  dweierstrassDy (rstIso r s t e) P = dweierstrassDy e (varChange r s t P) :=
by
  simp only [dweierstrassDy, rstIso, varChange]
  ring

/-- The change of coordinates `(1, r, s, t)` applied to `e`, with the triple
`rst = (r, s, t)` packaged as a single argument. -/
def rstTriple (e : Model R) (rst : R × R × R) : Model R :=
  rstIso rst.fst rst.snd.fst rst.snd.snd e

lemma rstIso_to_triple (e : Model R) (r s t : R) : rstIso r s t e = rstTriple e (r, s, t) := rfl

end Model

/-- A Weierstrass model with nonzero discriminant, i.e. a nonsingular elliptic
curve. -/
structure ValidModel (R : Type u) [CommRing R] extends Model R where
  /-- The discriminant of the underlying model is nonzero. -/
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel
variable {R : Type u} [CommRing R]
instance [Repr R] : Repr (ValidModel R) := ⟨fun (e : ValidModel R) _ => repr e.toModel⟩

/-- The valid model obtained from `e` by the change of coordinates `(1, r, s, t)`. -/
@[simps!]
def rstIso (r s t : R) (e : ValidModel R) : ValidModel R := {
  toModel := Model.rstIso r s t e.toModel,
  discr_not_zero := by
    rw [Model.rst_discr]
    exact e.discr_not_zero }

@[simp]
lemma rst_discr_valid (r s t : R) (e : ValidModel R) : (rstIso r s t e).discr = e.discr :=
  Model.rst_discr r s t e.toModel

--more [simp] lemmas
lemma rt_of_a1 (e : ValidModel R) (r t : R) : (rstIso r 0 t e).a1 = e.a1 :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero]

lemma t_of_a2 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a2 = e.a2 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

lemma r_of_a2 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a2 = e.a2 + 3 * r :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

lemma t_of_a3 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a3 = e.a3 + 2 * t :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

lemma r_of_a3 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a3 = e.a3 + r * e.a1 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

lemma t_of_a4 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a4 = e.a4 - t * e.a1 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

lemma r_of_a4 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a4 = e.a4 + 2 * r * e.a2 + 3 * r ^ 2 :=
by simp only [rstIso, Model.rstIso, zero_mul,
  sub_zero, mul_zero, add_zero, mul_assoc, ←pow_two r]

lemma t_of_a6 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rstIso, Model.rstIso, zero_mul, mul_zero,
  add_zero, mul_add, ←pow_two t, sub_eq_add_neg, neg_add, ←add_assoc]

lemma r_of_a6 (e : ValidModel R) (r : R) :
  (rstIso r 0 0 e).a6 = e.a6 + r * e.a4 + r ^ 2 * e.a2 + r ^ 3 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero,
  mul_zero, add_zero, mul_assoc, pow_two r, pow_succ r]

lemma st_of_a1 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a1 = e.a1 + 2 * s :=
by simp only [rstIso, Model.rstIso, mul_zero]

lemma st_of_a2 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a2 = e.a2 - s * e.a1 - s ^ 2 :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, ←pow_two s]

lemma st_of_a3 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a3 = e.a3 + 2 * t :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, zero_mul]

lemma st_of_a4 (e : ValidModel R) (s t : R) :
  (rstIso 0 s t e).a4 = e.a4 - s * e.a3 - t * e.a1 - 2 * s * t :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, zero_mul]

lemma st_of_a6 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rstIso, Model.rstIso, mul_zero,
  add_zero, mul_assoc, ←pow_two t, zero_mul, mul_add, sub_sub]

lemma st_of_b8 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).b8 = e.b8 := by
  rw [rstIso, Model.rst_b8]
  simp only [mul_zero, add_zero, zero_mul]

/-- The change of coordinates `(1, r, s, t)` applied to the valid model `e`, with
the triple `rst = (r, s, t)` packaged as a single argument. -/
def rstTriple (e : ValidModel R) (rst : R × R × R) : ValidModel R :=
  rstIso rst.fst rst.snd.fst rst.snd.snd e

lemma rstIso_to_triple (e : ValidModel R) (r s t : R) : rstIso r s t e = rstTriple e (r, s, t) :=
rfl

end ValidModel


namespace Model

variable {K : Type u} [CommRing K]

/-- A point `P` is a singular point of the model `e` when the Weierstrass
polynomial and both of its partial derivatives vanish at `P`. -/
def isSingularPoint (e : Model K) (P : K × K) : Prop :=
weierstrass e P = 0 ∧ dweierstrassDx e P = 0 ∧ dweierstrassDy e P = 0

lemma discr_eq_zero_of_singular (e : Model K) {P} (h : isSingularPoint e P) :
  e.discr = 0 :=
by
  rcases h with ⟨h₁, h₂, h₃⟩
  rw [discr_in_jacobian_ideal, h₁, h₂, h₃, mul_zero,
    mul_zero, mul_zero, add_zero, add_zero, neg_eq_zero]

variable [IsDomain K]

lemma c4_zero_iff_a1_zero_of_char_two (e : Model K) (h : ringChar K = 2) :
  e.c4 = 0 ↔ e.a1 = 0 :=
by
  have hchar' : (ringChar K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar']
  -- TODO use the nicer mod strategy from cubic roots here or a tactic
  rw [c4, b2, show (24 : K) = 2 * 12 by norm_num, show (4 : K) = 2 * 2 by norm_num,
    hchar'', ← pow_two]
  simp only [mul_zero, zero_mul, add_zero, ← pow_mul, sub_zero]
  rw [pow_eq_zero_iff]
  norm_num

lemma c4_zero_iff_b2_zero_of_char_three (e : Model K) (h : ringChar K = 3) :
  e.c4 = 0 ↔ e.b2 = 0 :=
by
  have hchar' : (ringChar K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar']
  rw [c4, show (24 : K) = 3 * 8 by norm_num, hchar'']
  simp only [zero_mul, sub_zero] -- TODO simp? doesn't do back arrows
  rw [pow_eq_zero_iff]
  norm_num

-- TODO is this actually an iff
lemma a3_zero_of_a1_zero_of_disc_zero_of_char_two
  (e : Model K) (h : ringChar K = 2) (hdisc : e.discr = 0) (ha1 : e.a1 = 0) :
  e.a3 = 0 :=
by
  have hchar' : (ringChar K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar']
  rw [discr, b2, b4, b6, b8, ha1,
    show (8 : K) = 2 * 4 by norm_num, show (4 : K) = 2 * 2 by norm_num, show (27 : K) = 2 * 13
        + 1 by norm_num, hchar''] at hdisc
  simp only [mul_zero, zero_mul, add_zero, neg_zero, sub_self, zero_add, one_mul, zero_sub,
    neg_eq_zero] at hdisc
  rw [← pow_two, ← pow_two, ← pow_mul] at hdisc
  rwa [pow_eq_zero_iff] at hdisc
  norm_num

-- TODO is this actually an iff discr
lemma b4_zero_of_b2_zero_of_disc_zero_of_char_three
  (e : Model K) (h : ringChar K = 3) (hdisc : e.discr = 0) (hb2 : e.b2 = 0) :
  e.b4 = 0 :=
by
  have hchar' : (ringChar K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar']
  rw [discr, hb2,
    show (27 : K) = 3 * 9 by norm_num,
    show (8 : K) = 3 * 3 - 1 by norm_num,
    hchar''] at hdisc
  simpa using hdisc

namespace Field
variable {K : Type u} [Field K]

open ECTate ECTate.PerfectRing

open Classical in
/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def singularPoint [PerfectRing K] (e : Model K) : K × K :=
  if e.c4 = 0 then
    match ringChar K with
    | 2 => (pthRoot e.a4, pthRoot (e.a2 * e.a4 + e.a6))
    | 3 => (pthRoot (-(e.a3 ^ 2) - e.a6), e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
    | _ => (-e.b2 / 12, -(-e.a1 * e.b2 / 12 + e.a3) / 2)
  else
    ((18 * e.b6 - e.b2 * e.b4) / e.c4, (e.b2 * e.b5 + 3 * e.b7) / e.c4)


lemma ringChar_eq_of_Prime [Nat.AtLeastTwo n] (hn : @OfNat.ofNat K n _ = 0) (hnp : Nat.Prime n) :
  ringChar K = n :=
by
  rw [← Nat.cast_ofNat, ringChar.spec] at hn
  cases (Nat.dvd_prime hnp).mp hn with
  | inl h =>
    have hh := CharP.char_is_prime_or_zero K (ringChar K)
    rw [h] at hh
    exact absurd hh (by simp [Nat.not_prime_one])
  | inr h =>
    assumption

-- lemma test (e : Model K) :
--   c4 e ^ 3 * ((b2 e * b5 e + 3 * b7 e) ^ 2 * (c4 e)⁻¹ ^ 2) + 0 =
--             c4 e^ 3 * (c4 e)⁻¹ ^ 2 * ((b2 e * b5 e + 3 * b7 e) ^ 2) :=
-- by
--   rw [show c4 e ^ 3 * ((b2 e * b5 e+ 3 * b7 e) ^ 2 * (c4 e)⁻¹ ^ 2) =
--             c4 e^ 3 * (c4 e)⁻¹ ^ 2 * ((b2 e * b5 e + 3 * b7 e) ^ 2) by ac_rfl]
--   sorry
-- TODO a field should be a division comm monoid

-- TODO maybe rewrite to take an explicit point

lemma isSingularPoint_singularPoint [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  isSingularPoint e (singularPoint e) :=
by
  rw [singularPoint]
  split_ifs with hc4
  · have hc6 : c6 e = 0 := by
      simpa [h, hc4, pow_succ, mul_eq_zero] using discr_identity e
    split
    -- case _ hchar => TODO get this working, but its subtly different
    · rw [isSingularPoint]
      have hchar : ringChar K = 2 := by assumption
      have hchar' : (ringChar K : K) = 2 := by simp [hchar]
      have hchar'' : (2 : K) = 0 := by simp [← hchar']
      have hcharne : ringChar K ≠ 0 := by simp [hchar]
      have ha1 : e.a1 = 0 := by simpa [c4_zero_iff_a1_zero_of_char_two e hchar] using hc4
      have ha3 : e.a3 = 0 := a3_zero_of_a1_zero_of_disc_zero_of_char_two e hchar h ha1
      refine ⟨?_, ?_, ?_⟩
      · rw [weierstrass]
        simp only [ha1, ha3, zero_mul, add_zero]
        rw [show 3 = 2 + 1 by norm_num]
        rw [pow_succ _ 2]
        rw [← hchar, pthRoot_pow_char hcharne]
        rw [pthRoot_pow_char hcharne]
        ring_nf
        simp [hchar'']
      · rw [dweierstrassDx]
        simp only [ha1, zero_mul, hchar'', add_zero, zero_sub, neg_add_rev]
        rw [← hchar, pthRoot_pow_char hcharne, ← sub_eq_add_neg]
        simp only [sub_eq_iff_eq_add, zero_add]
        rw [show (3 : K) = 2 * 2 - 1 by norm_num]
        rw [hchar'']
        simp []
      · simp [dweierstrassDy, ha1, ha3, hchar'']
    · rw [isSingularPoint]
      have hchar : ringChar K = 3 := by assumption
      have hcharne : ringChar K ≠ 0 := by simp [hchar]
      have hchar' : (ringChar K : K) = 3 := by simp [hchar]
      have hchar'' : (3 : K) = 0 := by simp [← hchar']
      have hb2 : e.b2 = 0 := by simpa [c4_zero_iff_b2_zero_of_char_three e hchar] using hc4
      have hb4 : e.b4 = 0 := b4_zero_of_b2_zero_of_disc_zero_of_char_three e hchar h hb2
      rw [b2] at hb2 -- TODO get versions that elim one b
      rw [b4] at hb4
      refine ⟨?_, ?_, ?_⟩
      · rw [weierstrass]
        rw [← hchar, pthRoot_pow_char hcharne]
        simp only
        rw [show
          (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) ^ 2 +
          e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) +
          e.a3 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) -
          (-(e.a3 ^ 2) - e.a6 + e.a2 * pthRoot (-(e.a3 ^ 2) - e.a6) ^ 2
              + e.a4 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a6) =
          (2 * e.a1 ^ 2 - e.a2) * pthRoot (-(e.a3 ^ 2) - e.a6) ^ 2 +
          (4 * e.a1 * e.a3 - e.a4) * pthRoot (-(e.a3 ^ 2) - e.a6) +
          3 * e.a3 ^ 2
          by ring]
        have hfac2 : 2 * e.a1 ^ 2 - e.a2 = 0 := by
          linear_combination (norm := (ring_nf; simp [hchar''])) -hb2
        have hfac4 : 4 * e.a1 * e.a3 - e.a4 = 0 := by
          rw [show (2 : K) = -1 by rw [← add_zero (-1), ← hchar'']; norm_num] at hb4
          rw [show (4 : K) = 1 by rw [← add_zero 1, ← hchar'']; norm_num]
          simp only [neg_mul, one_mul] at hb4
          simp [sub_eq_add_neg, hb4]
        rw [hfac2, hfac4]
        simp only [zero_mul, add_zero, hchar'']
      · rw [dweierstrassDx]
        rw [hchar'', zero_mul, zero_add]
        simp only
        rw [show e.a1 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
            - (2 * e.a2 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a4) =
                 (e.a1 * e.a1 - 2 * e.a2) * pthRoot (-(e.a3 ^ 2) - e.a6) + (e.a1 * e.a3 - e.a4)
          by ring]
        rw [show (2 : K) = -1 by rw [← add_zero (-1), ← hchar'']; norm_num] at hb4
        rw [show (4 : K) =
            -2 by rw [← add_zero (-2), ← zero_mul (2 : K), ← hchar'']; norm_num] at hb2
        simp only [neg_mul, one_mul, ← sub_eq_add_neg] at hb4 hb2
        rw [hb4, hb2, zero_mul, zero_add]
      · rw [dweierstrassDy]
        simp only
        rw [show 2 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
            + e.a1 * pthRoot (- (e.a3 ^ 2) - e.a6) + e.a3 = 3 * ((e.a1 * pthRoot (-(e.a3 ^ 2)
                - e.a6)) + e.a3) by ring]
        rw [hchar'', zero_mul]
    · rename_i hn2 hn3
      rw [isSingularPoint]
      -- have hb4 : e.b2 ^ 2 = 24 * e.b4 := sorry
      have h2 : (2 : K) ≠ 0 := fun hh => hn2 (ringChar_eq_of_Prime (n := 2) hh Nat.prime_two)
      have h3 : (3 : K) ≠ 0 := fun hh => hn3 (ringChar_eq_of_Prime (n := 3) hh Nat.prime_three)
      have h12 : (12 : K) ≠ 0 := by
        rw [show (12 : K) = 2 * 2 * 3 by norm_num]
        repeat' apply mul_ne_zero
        all_goals assumption
      refine ⟨?_, ?_, ?_⟩
      · apply nzero_mul_left_cancel (12 ^ 3) _ _ (pow_ne_zero _ h12)
        simp only [weierstrass, div_eq_mul_inv, mul_zero]
        rw [show
          12 ^ 3 * ((-(-e.a1 * b2 e * 12⁻¹ + e.a3) * 2⁻¹) ^ 2 +
          e.a1 * (-b2 e * 12⁻¹) * (-(-e.a1 * b2 e * 12⁻¹ + e.a3) * 2⁻¹) +
          e.a3 * (-(-e.a1 * b2 e * 12⁻¹ + e.a3) * 2⁻¹) -
          ((-b2 e * 12⁻¹) ^ 3 + e.a2 * (-b2 e * 12⁻¹) ^ 2 + e.a4 * (-b2 e * 12⁻¹)
            + e.a6)) =
          3*(-(-e.a1 * b2 e * (12 * 12⁻¹) + 12 * e.a3) * (2 * 2⁻¹)) ^ 2 +
          e.a1 * (-b2 e * (12 * 12⁻¹)) * (-(-e.a1 * b2 e * (12 * 12⁻¹)
              + 12 * e.a3) * (6 * (2 * 2⁻¹))) +
          12 * e.a3 * (-(-e.a1 * b2 e * (12 * 12⁻¹) + 12 * e.a3) * (6 * (2 * 2⁻¹))) -
          ((-b2 e * (12 * 12⁻¹)) ^ 3 + 12 * e.a2 * (-b2 e * (12 * 12⁻¹)) ^ 2
              + 12 ^ 2 * e.a4 * (-b2 e * (12 * 12⁻¹)) + 12 ^ 3 * e.a6) by ring]
        simp only [mul_inv_cancel₀ h2, mul_inv_cancel₀ h12, mul_one]
        -- This is 2*c6
        rw [← mul_zero (2 : K), ← hc6]
        simp only [c6, b2, b4, b6]
        ring
      · apply nzero_mul_left_cancel (12 ^ 2) _ _ (pow_ne_zero _ h12)
        simp only [dweierstrassDx, div_eq_mul_inv, mul_zero]
        rw [show
          12 ^ 2 * (e.a1 * (-(-e.a1 * b2 e * 12⁻¹ + e.a3) * 2⁻¹) - (3 * (-b2 e * 12⁻¹) ^ 2
              + 2 * e.a2 * (-b2 e * 12⁻¹) + e.a4))
          =
          e.a1 * (-(-e.a1 * b2 e * (12 * 12⁻¹) + 12* e.a3) * 6 * (2 * 2⁻¹))
              - (3 * (-b2 e * (12 * 12⁻¹)) ^ 2 + 24 * e.a2 * (-b2 e * (12 * 12⁻¹))
                + 144 * e.a4)
          by ring]
        simp only [mul_inv_cancel₀ h2, mul_inv_cancel₀ h12, mul_one]
        -- This is 2*c6
        rw [← mul_zero (3 : K), ← hc4]
        simp only [c4, b2, b4]
        ring
      · apply nzero_mul_left_cancel 12 _ _ h12
        simp only [dweierstrassDy, div_eq_mul_inv, mul_zero]
        rw [show
          12 * (2 * (-(-e.a1 * b2 e * 12⁻¹ + e.a3) * 2⁻¹) + e.a1 * (-b2 e * 12⁻¹) + e.a3)
          =
          (-(-e.a1 * b2 e * (12 * 12⁻¹) + 12 * e.a3) * (2 * 2⁻¹))
            + e.a1 * (-b2 e * (12 * 12⁻¹))
              + 12 * e.a3
          by ring]
        simp only [mul_inv_cancel₀ h2, mul_inv_cancel₀ h12, mul_one]
        -- This is 2*c6
        simp only [b2]
        ring
  · rw [isSingularPoint]
    refine ⟨?_, ?_, ?_⟩
    · rw [weierstrass]
      -- simp [b2, b5, b7]
      apply nzero_mul_left_cancel (e.c4 ^ 3) _ _ (pow_ne_zero _ hc4)
      rw [mul_zero]
      -- simp only [mul_add, mul_sub, div_eq_mul_inv, mul_pow]
      -- have : c4 e ^ 3 * ((b2 e * b5 e + 3 * b7 e) ^ 2 * (c4 e)⁻¹ ^ 2) =
      --     c4 e ^ 3 * (c4 e)⁻¹ ^ 2 * ((b2 e * b5 e + 3 * b7 e) ^ 2 ) :=
      --       by ac_rfl -- TODO ac_rfl bug or show bug?
      -- rw [this]
      simp only [div_eq_mul_inv]
      rw [show c4 e ^ 3 * (((b2 e * b5 e + 3 * b7 e) * (c4 e)⁻¹) ^ 2 +
            e.a1 * ((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹)
              * ((b2 e * b5 e + 3 * b7 e) * (c4 e)⁻¹) +
          e.a3 * ((b2 e * b5 e + 3 * b7 e) * (c4 e)⁻¹) -
          (((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹) ^ 3 + e.a2 * ((18 * b6 e
              - b2 e * b4 e) * (c4 e)⁻¹) ^ 2 +
          e.a4 * ((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹) + e.a6)) =
        (c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹ * c4 e * ((b2 e * b5 e + 3 * b7 e)) ^ 2 +
          c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹ * c4 e * e.a1 * ((18 * b6 e
              - b2 e * b4 e)) * ((b2 e * b5 e + 3 * b7 e)) +
        c4 e * (c4 e)⁻¹ * c4 e * c4 e * e.a3 * ((b2 e * b5 e + 3 * b7 e)) -
        (c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹
          * ((18 * b6 e - b2 e * b4 e)) ^ 3 +
        c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹ * c4 e * e.a2 * ((18 * b6 e - b2 e * b4 e)) ^ 2 +
          c4 e * (c4 e)⁻¹ * c4 e * c4 e * e.a4 * ((18 * b6 e - b2 e * b4 e)) +
        c4 e * c4 e * c4 e * e.a6)) by ring]
      simp only [mul_inv_cancel₀ hc4, one_mul]
      rw [b5, b7, c4, b2, b4, b6]
      -- what remains factors the discriminant (up to sign)
      rw [← mul_zero (e.a1^6 + 12*e.a1^4*e.a2 + 48*e.a1^2*e.a2^2 - 36*e.a1^3*e.a3 + 64*e.a2^3
        - 144*e.a1*e.a2*e.a3 - 72*e.a1^2*e.a4 + 216*e.a3^2 - 288*e.a2*e.a4 + 864*e.a6),
        ← h, discr_eq_neg_singular]
      ring
    · rw [dweierstrassDx]
      apply nzero_mul_left_cancel (e.c4 ^ 2) _ _ (pow_ne_zero _ hc4)
      rw [mul_zero, pow_two]
      simp only [div_eq_mul_inv]
      rw [show c4 e * c4 e *
        (e.a1 * ((b2 e * b5 e + 3 * b7 e) * (c4 e)⁻¹) -
          (3 * ((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹) ^ 2
          + 2 * e.a2 * ((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹) + e.a4)) =
          c4 e * (c4 e)⁻¹ * c4 e * (e.a1 * (b2 e * b5 e + 3 * b7 e)
          - 2 * e.a2 * ((18 * b6 e - b2 e * b4 e)))
          - c4 e * (c4 e)⁻¹ * c4 e * (c4 e)⁻¹ *
          3 * (18 * b6 e - b2 e * b4 e) ^ 2 - e.a4 * c4 e * c4 e
        by ring]
      simp only [mul_inv_cancel₀ hc4, one_mul]
      rw [b5, b7, c4, b2, b4, b6]
      -- what remains is just 36 times the discriminant (up to sign)
      rw [← mul_zero (36 : K), ← h, discr_eq_neg_singular]
      ring
    · rw [dweierstrassDy]
      apply nzero_mul_left_cancel e.c4 _ _ hc4
      simp only [div_eq_mul_inv, mul_zero]
      rw [show c4 e * (2 * ((b2 e * b5 e + 3 * b7 e) * (c4 e)⁻¹)
          + e.a1 * ((18 * b6 e - b2 e * b4 e) * (c4 e)⁻¹) + e.a3) =
        c4 e * (c4 e)⁻¹ * (2 * (b2 e * b5 e + 3 * b7 e)
        + e.a1 * ((18 * b6 e - b2 e * b4 e))) + c4 e * e.a3 by ring]
      simp only [mul_inv_cancel₀ hc4, one_mul]
      rw [b5, b7, c4, b2, b4, b6]
      ring


/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def moveSingularPointToOriginTriple [PerfectRing K] (e : Model K) : K × K × K :=
⟨(singularPoint e).1, 0, (singularPoint e).2⟩

/-- The model obtained from `e` by the change of coordinates that moves its
singular point to the origin. -/
noncomputable
def moveSingularPointToOriginIso [PerfectRing K] (e : Model K) : Model K :=
rstTriple e (moveSingularPointToOriginTriple e)

lemma move_singularPoint (e : Model K) (r t : K) {P : K × K} (h : isSingularPoint e P) :
  isSingularPoint (rstIso r 0 t e) (varChange (-r) 0 (-t) P) :=
by
  rw [isSingularPoint, weierstrass_iso_eq_varChange,
    dweierstrassDx_iso_eq_varChange, zero_mul, add_zero,
    dweierstrassDy_iso_eq_varChange, varChange_comp]
  simpa

lemma move_singularPoint_to_origin [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  isSingularPoint (moveSingularPointToOriginIso e) (0, 0) :=
by
  rw [moveSingularPointToOriginIso, rstTriple, moveSingularPointToOriginTriple]
  convert move_singularPoint e (singularPoint e).fst (singularPoint e).snd
    (isSingularPoint_singularPoint e h) using 2 <;> -- TODO convert does too much here
  simp [varChange]

lemma move_singularPoint_to_origin' [PerfectRing K] (e : Model K) :
  (∃ P, isSingularPoint e P) →
    isSingularPoint (moveSingularPointToOriginIso e) (0, 0) :=
by
  rintro ⟨P, hP⟩
  have hd := discr_eq_zero_of_singular e hP
  exact move_singularPoint_to_origin e hd

end Field

end Model
