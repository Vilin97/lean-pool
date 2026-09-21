/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Ore.PairStage

/-!
# Universal property of a coordinate-momentum pair stage

The construction is the universal property of `NormalOre` applied twice.
First a coefficient map and a commuting coordinate define a map from the
central-coordinate stage.  A momentum satisfying the derivation relation
against that map then defines a map from `PairStage`.
-/

namespace Stafford38.OrePairUniversal

open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreCoordinateStage
open Stafford38.OrePairStage

noncomputable section

variable {B A : Type*} [Ring B] [Ring A]

/-- The Ore ambient determined by a coefficient map and a centralizing
coordinate image. -/
def coordinateAmbient (f : B →+* A) (X : A)
    (hX : ∀ b, X * f b = f b * X) :
    OreAmbient B A (zeroDerivation : OreDivisionDerivation B) where
  embed := f
  x := X
  relation := by
    intro b
    simpa using hX b

/-- The universal map from the central-coordinate stage. -/
def coordinateLift (f : B →+* A) (X : A)
    (hX : ∀ b, X * f b = f b * X) :
    CoordinateStage (B := B) →+* A :=
  oreLift zeroDerivation (coordinateAmbient f X hX)

@[simp] theorem coordinateLift_coefficient (f : B →+* A) (X : A)
    (hX : ∀ b, X * f b = f b * X) (b : B) :
    coordinateLift f X hX (normalCoefficient zeroDerivation b) = f b :=
  oreLift_coefficient zeroDerivation (coordinateAmbient f X hX) b

@[simp] theorem coordinateLift_variable (f : B →+* A) (X : A)
    (hX : ∀ b, X * f b = f b * X) :
    coordinateLift f X hX (normalVariable zeroDerivation) = X :=
  oreLift_variable zeroDerivation (coordinateAmbient f X hX)

/-- A map out of the coordinate stage is determined by the old coefficients
and the new coordinate. -/
theorem coordinateLift_unique (f : B →+* A) (X : A)
    (hX : ∀ b, X * f b = f b * X)
    (g : CoordinateStage (B := B) →+* A)
    (hCoefficient : ∀ b, g (normalCoefficient zeroDerivation b) = f b)
    (hVariable : g (normalVariable zeroDerivation) = X) :
    g = coordinateLift f X hX :=
  oreLift_unique zeroDerivation (coordinateAmbient f X hX) g
    hCoefficient hVariable

private theorem momentum_mul_coordinate_pow (X P : A)
    (hPX : P * X = X * P + 1) (n : ℕ) :
    P * X ^ n = X ^ n * P + n • X ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc, hPX, mul_add]
      by_cases hn : n = 0
      · subst n
        simp
      · have hpow : X ^ (n - 1) * X = X ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
        rw [nsmul_eq_mul, mul_assoc, hpow, ← nsmul_eq_mul]
        simp only [Nat.add_sub_cancel, mul_one, mul_assoc, succ_nsmul]
        abel

/-- The coefficient and generator relations imply the full coordinate
derivation relation.  No commutativity of either coefficient ring is used. -/
theorem coordinateLift_derivation_relation (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) (z : CoordinateStage (B := B)) :
    P * coordinateLift f X hX z =
      coordinateLift f X hX z * P +
        coordinateLift f X hX (coordinateDerivation z) := by
  rcases normalForm_surjective zeroDerivation z with ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [normalForm_add, (coordinateLift f X hX).map_add,
        coordinateDerivation.map_add, (coordinateLift f X hX).map_add,
        mul_add, add_mul, hp, hq]
      abel
  | monomial n b =>
      rw [coordinateDerivation_normalForm, Polynomial.derivative_monomial,
        normalForm_monomial, map_mul, map_pow,
        coordinateLift_coefficient, coordinateLift_variable,
        normalForm_monomial, map_mul, map_pow,
        coordinateLift_coefficient, coordinateLift_variable]
      rw [← mul_assoc, hP, mul_assoc, momentum_mul_coordinate_pow X P hPX n]
      simp only [add_mul, mul_add, mul_assoc]
      congr 1
      rw [map_mul, map_natCast, nsmul_eq_mul]
      simp only [mul_assoc]

/-- The outer Ore ambient determined by commuting coefficient images and a
coordinate-momentum Weyl pair. -/
def pairAmbient (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    OreAmbient (CoordinateStage (B := B)) A coordinateDerivation where
  embed := coordinateLift f X hX
  x := P
  relation := coordinateLift_derivation_relation f X P hX hP hPX

/-- The universal ring map from a coordinate-momentum pair stage. -/
def pairLift (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    PairStage (B := B) →+* A :=
  oreLift coordinateDerivation (pairAmbient f X P hX hP hPX)

@[simp] theorem pairLift_coefficient (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1)
    (b : B) :
    pairLift f X P hX hP hPX (pairCoefficient b) = f b := by
  change pairLift f X P hX hP hPX
      (normalCoefficient coordinateDerivation
        (normalCoefficient zeroDerivation b)) = f b
  rw [pairLift, oreLift_coefficient]
  change coordinateLift f X hX (normalCoefficient zeroDerivation b) = f b
  exact coordinateLift_coefficient f X hX b

@[simp] theorem pairLift_coordinate (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    pairLift f X P hX hP hPX pairCoordinate = X := by
  change pairLift f X P hX hP hPX
      (normalCoefficient coordinateDerivation
        (normalVariable zeroDerivation)) = X
  rw [pairLift, oreLift_coefficient]
  change coordinateLift f X hX (normalVariable zeroDerivation) = X
  exact coordinateLift_variable f X hX

@[simp] theorem pairLift_momentum (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    pairLift f X P hX hP hPX pairMomentum = P := by
  exact oreLift_variable coordinateDerivation (pairAmbient f X P hX hP hPX)

/-- A ring map out of `PairStage` is determined by the old coefficients and
the two newly adjoined generators. -/
theorem pairLift_unique (f : B →+* A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1)
    (g : PairStage (B := B) →+* A)
    (hCoefficient : ∀ b, g (pairCoefficient b) = f b)
    (hCoordinate : g pairCoordinate = X)
    (hMomentum : g pairMomentum = P) :
    g = pairLift f X P hX hP hPX := by
  let inner : CoordinateStage (B := B) →+* A :=
    g.comp (normalCoefficient coordinateDerivation)
  have hInner : inner = coordinateLift f X hX := by
    apply coordinateLift_unique f X hX
    · intro b
      exact hCoefficient b
    · exact hCoordinate
  apply oreLift_unique coordinateDerivation (pairAmbient f X P hX hP hPX)
  · intro z
    exact DFunLike.congr_fun hInner z
  · exact hMomentum

section Scalars

variable {k : Type*} [CommRing k] [Algebra k B] [Algebra k A]

local instance : Algebra k (PairStage (B := B)) :=
  pairStageAlgebra (k := k) (B := B)

/-- The pair lift as a scalar-preserving algebra map. -/
def pairLiftAlgHom (f : B →ₐ[k] A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    PairStage (B := B) →ₐ[k] A where
  toRingHom := pairLift f.toRingHom X P hX hP hPX
  commutes' c := by
    rw [pairStageAlgebra_algebraMap]
    exact pairLift_coefficient f.toRingHom X P hX hP hPX (algebraMap k B c)
      |>.trans (f.commutes c)

@[simp] theorem pairLiftAlgHom_coefficient (f : B →ₐ[k] A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1)
    (b : B) :
    pairLiftAlgHom f X P hX hP hPX (pairCoefficient b) = f b := by
  change pairLift f.toRingHom X P hX hP hPX (pairCoefficient b) = f b
  exact pairLift_coefficient f.toRingHom X P hX hP hPX b

@[simp] theorem pairLiftAlgHom_coordinate (f : B →ₐ[k] A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    pairLiftAlgHom f X P hX hP hPX pairCoordinate = X := by
  change pairLift f.toRingHom X P hX hP hPX pairCoordinate = X
  exact pairLift_coordinate f.toRingHom X P hX hP hPX

@[simp] theorem pairLiftAlgHom_momentum (f : B →ₐ[k] A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1) :
    pairLiftAlgHom f X P hX hP hPX pairMomentum = P := by
  change pairLift f.toRingHom X P hX hP hPX pairMomentum = P
  exact pairLift_momentum f.toRingHom X P hX hP hPX

theorem pairLiftAlgHom_unique (f : B →ₐ[k] A) (X P : A)
    (hX : ∀ b, X * f b = f b * X)
    (hP : ∀ b, P * f b = f b * P)
    (hPX : P * X = X * P + 1)
    (g : PairStage (B := B) →ₐ[k] A)
    (hCoefficient : ∀ b, g (pairCoefficient b) = f b)
    (hCoordinate : g pairCoordinate = X)
    (hMomentum : g pairMomentum = P) :
    g = pairLiftAlgHom f X P hX hP hPX := by
  apply AlgHom.ext
  intro z
  exact DFunLike.congr_fun
    (pairLift_unique f.toRingHom X P hX hP hPX g.toRingHom
      hCoefficient hCoordinate hMomentum) z

end Scalars


end
end Stafford38.OrePairUniversal
