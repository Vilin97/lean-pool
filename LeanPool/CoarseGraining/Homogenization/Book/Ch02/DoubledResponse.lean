/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.FieldSpaces
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Block

/-! # Doubled Response -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public doubled field, represented by potential and flux components. -/
structure DoubledField (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

namespace DoubledField

/-- Evaluate a doubled field as a block vector. -/
def eval {d : ℕ} (X : DoubledField d) (x : Vec d) : BlockVec d :=
  (X.potential x, X.flux x)

/-- A.e. equality of public doubled fields on a Chapter 2 domain. -/
def SameAE {d : ℕ} {U : Domain d} (X Y : DoubledField d) : Prop :=
  X.potential =ᵐ[volumeMeasureOn (U : Set (Vec d))] Y.potential ∧
    X.flux =ᵐ[volumeMeasureOn (U : Set (Vec d))] Y.flux

instance {d : ℕ} : Zero (DoubledField d) where
  zero := { potential := 0, flux := 0 }

instance {d : ℕ} : Add (DoubledField d) where
  add X Y := { potential := X.potential + Y.potential, flux := X.flux + Y.flux }

instance {d : ℕ} : Neg (DoubledField d) where
  neg X := { potential := -X.potential, flux := -X.flux }

instance {d : ℕ} : Sub (DoubledField d) where
  sub X Y := { potential := X.potential - Y.potential, flux := X.flux - Y.flux }

instance {d : ℕ} : SMul ℝ (DoubledField d) where
  smul c X := { potential := c • X.potential, flux := c • X.flux }

@[simp] theorem eval_zero {d : ℕ} (x : Vec d) :
    (0 : DoubledField d).eval x = 0 :=
  rfl

@[simp] theorem eval_add {d : ℕ} (X Y : DoubledField d) (x : Vec d) :
    (X + Y).eval x = X.eval x + Y.eval x :=
  rfl

@[simp] theorem eval_neg {d : ℕ} (X : DoubledField d) (x : Vec d) :
    (-X).eval x = -X.eval x :=
  rfl

@[simp] theorem eval_sub {d : ℕ} (X Y : DoubledField d) (x : Vec d) :
    (X - Y).eval x = X.eval x - Y.eval x :=
  rfl

@[simp] theorem eval_smul {d : ℕ} (c : ℝ) (X : DoubledField d) (x : Vec d) :
    (c • X).eval x = c • X.eval x :=
  rfl

end DoubledField

/-- Public field in `\Lpot(U) × \Lsol(U)`. -/
def IsDoubledAmbientField {d : ℕ} (U : Domain d) (X : DoubledField d) : Prop :=
  Book.Ch01.PotentialFieldOn (U : Set (Vec d)) X.potential ∧
    Book.Ch01.SolenoidalFieldOn (U : Set (Vec d)) X.flux

/-- Public test field in `\Lpoto(U) × \Lsolo(U)`. -/
def IsDoubledTestField {d : ℕ} (U : Domain d) (X : DoubledField d) : Prop :=
  Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d)) X.potential ∧
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn (U : Set (Vec d)) X.flux

/-- Block pairing integrand `Y · A X` for doubled fields. -/
noncomputable def doubledBlockPairingIntegrand {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (Y X : DoubledField d) : Vec d → ℝ :=
  fun x => blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (X.eval x))

/-- Public doubled response space `S(U; a)`. -/
def IsDoubledResponseField {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (X : DoubledField d) : Prop :=
  IsDoubledAmbientField U X ∧
    ∀ Y : DoubledField d, IsDoubledTestField U Y →
      ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume = 0

/-- Public admissibility for the doubled `mu` problem:
`X ∈ P + Lpoto(U) × Lsolo(U)`. -/
def IsDoubledMuAdmissible {d : ℕ} (U : Domain d) (P : BlockVec d)
    (X : DoubledField d) : Prop :=
  Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d))
      (fun x => X.potential x - P.1) ∧
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn (U : Set (Vec d))
      (fun x => X.flux x - P.2)

/-- Public doubled `mu` energy value of an admissible field. -/
noncomputable def doubledMuValue {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (X : DoubledField d) : ℝ :=
  average U fun x => blockEnergyDensityAt a (X.eval x) x

/-- Public value set whose infimum is `mu(U,P;a)`. -/
noncomputable def doubledMuValueSet {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P : BlockVec d) : Set ℝ :=
  {m | ∃ X : DoubledField d, IsDoubledMuAdmissible U P X ∧
      m = doubledMuValue U a X}

/-- Public doubled variational quantity `mu(U,P;a)`. -/
noncomputable def doubledMu {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P : BlockVec d) : ℝ :=
  sInf (doubledMuValueSet U a P)

/-- A public minimizer for `mu(U,P;a)`. -/
def IsDoubledMuMinimizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P : BlockVec d) (X : DoubledField d) : Prop :=
  IsDoubledMuAdmissible U P X ∧
    ∀ Y : DoubledField d, IsDoubledMuAdmissible U P Y →
      doubledMuValue U a X ≤ doubledMuValue U a Y

/-- Public doubled response integrand from `e.def.block.J.basic.definitions`. -/
noncomputable def doubledResponseIntegrand {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (P Q : BlockVec d) (X : DoubledField d) : Vec d → ℝ :=
  fun x =>
    -blockEnergyDensityAt a (X.eval x) x
      - blockVecDot P (blockMatVecMul (blockMatrixField a x) (X.eval x))
      + blockVecDot Q (X.eval x)

/-- Public doubled response value of one field. -/
noncomputable def doubledResponseValue {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (P Q : BlockVec d) (X : DoubledField d) : ℝ :=
  average U (doubledResponseIntegrand U a P Q X)

/-- Public value set whose supremum is `Jbold(U,P,Q;a)`. -/
noncomputable def doubledResponseValueSet {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (P Q : BlockVec d) : Set ℝ :=
  {m | ∃ X : DoubledField d, IsDoubledResponseField U a X ∧
      m = doubledResponseValue U a P Q X}

/-- Public doubled response functional `Jbold(U,P,Q;a)`. -/
noncomputable def doubledResponseJ {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (P Q : BlockVec d) : ℝ :=
  sSup (doubledResponseValueSet U a P Q)

/-- A public maximizer for the doubled response functional. -/
def IsDoubledResponseMaximizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P Q : BlockVec d) (X : DoubledField d) : Prop :=
  IsDoubledResponseField U a X ∧
    ∀ Y : DoubledField d, IsDoubledResponseField U a Y →
      doubledResponseValue U a P Q Y ≤ doubledResponseValue U a P Q X

/-- Public existence statement for doubled response maximizers. -/
def DoubledResponseMaximizerExists {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P Q : BlockVec d) : Prop :=
  ∃ X : DoubledField d, IsDoubledResponseMaximizer U a P Q X

/-- Public doubled field generated by a primal and adjoint solution. -/
noncomputable def doubledFieldOfSolutions {d : ℕ} {U : Domain d}
    (a : CoeffOn U) (v : Solution U a) (vStar : Solution U a.transpose) :
    DoubledField d :=
  { potential := fun x => v.toH1.grad x + vStar.toH1.grad x
    flux := fun x =>
      matVecMul (a.toCoeffField x) (v.toH1.grad x) -
        matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x) }

/-- Public doubled maximizer candidate generated by the scalar maximizers in
`e.block.maximizer.by.v.vstar.basic.definitions`. -/
noncomputable def doubledFieldOfScalarMaximizers {d : ℕ} {U : Domain d}
    (a : CoeffOn U) (v : Solution U a) (vStar : Solution U a.transpose) :
    DoubledField d :=
  (1 / 2 : ℝ) • doubledFieldOfSolutions a v vStar

end

end Ch02
end Book
end Homogenization
