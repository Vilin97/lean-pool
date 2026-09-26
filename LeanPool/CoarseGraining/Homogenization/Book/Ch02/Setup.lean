/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic

/-! # Setup -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 domains: nonempty bounded open convex subsets of `R^d`. -/
structure Domain (d : ℕ) where
  carrier : Set (Vec d)
  isDomain : IsOpenBoundedConvexDomain carrier
  nonempty : carrier.Nonempty

namespace Domain

instance {d : ℕ} : Coe (Domain d) (Set (Vec d)) where
  coe U := U.carrier

@[simp] theorem coe_mk {d : ℕ} (U : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    ((Domain.mk U hU hne : Domain d) : Set (Vec d)) = U :=
  rfl

theorem isOpen {d : ℕ} (U : Domain d) : IsOpen (U : Set (Vec d)) :=
  U.isDomain.isOpen

theorem isBoundedDomain {d : ℕ} (U : Domain d) :
    IsBoundedDomain (U : Set (Vec d)) :=
  U.isDomain.isBoundedDomain

theorem convex {d : ℕ} (U : Domain d) : Convex ℝ (U : Set (Vec d)) :=
  U.isDomain.convex

theorem measurableSet {d : ℕ} (U : Domain d) : MeasurableSet (U : Set (Vec d)) :=
  U.isOpen.measurableSet

instance instIsFiniteMeasureVolumeMeasureOn {d : ℕ} (U : Domain d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) := by
  simpa [volumeMeasureOn] using U.isDomain.isFiniteMeasure_restrict_volume

end Domain

/-- Public version of `a in Omega(U)`.

This is deliberately an almost-everywhere object: the coefficient field is a
representative, and all public regularity/ellipticity data is stated with respect
to `volumeMeasureOn U`.
-/
structure CoeffOn {d : ℕ} (U : Domain d) where
  toCoeffField : CoeffField d
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aeStronglyMeasurable :
    ∀ i j : Fin d,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) toCoeffField x i j)
        (volumeMeasureOn (U : Set (Vec d)))
  aeElliptic :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      IsEllipticMatrix lam Lam (toCoeffField x)

namespace CoeffOn

instance {d : ℕ} {U : Domain d} : CoeFun (CoeffOn U) (fun _ => CoeffField d) where
  coe a := a.toCoeffField

theorem measurableSet {d : ℕ} {U : Domain d} (_a : CoeffOn U) :
    MeasurableSet (U : Set (Vec d)) :=
  U.measurableSet

/-- Public adjoint coefficient field `a^t`, still as an a.e. coefficient object
on the same Chapter 2 domain. -/
noncomputable def transpose {d : ℕ} {U : Domain d} (a : CoeffOn U) : CoeffOn U where
  toCoeffField := fun x => matTranspose (a.toCoeffField x)
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have h := a.aeStronglyMeasurable j i
    have hcoord :
        (fun x : Vec d =>
            restrictCoeffField (U : Set (Vec d))
              (fun y => matTranspose (a.toCoeffField y)) x i j) =
          fun x : Vec d =>
            restrictCoeffField (U : Set (Vec d)) a.toCoeffField x j i := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;>
        simp [restrictCoeffField, matTranspose, hx]
    simpa [hcoord] using h
  aeElliptic := by
    exact a.aeElliptic.mono fun x hx => isEllipticMatrix_transpose hx

@[simp] theorem transpose_apply {d : ℕ} {U : Domain d} (a : CoeffOn U)
    (x : Vec d) :
    a.transpose.toCoeffField x = matTranspose (a.toCoeffField x) :=
  rfl

/-- Equality of public coefficient fields is equality of representatives almost
everywhere on the public domain. -/
def AEEq {d : ℕ} {U : Domain d} (a b : CoeffOn U) : Prop :=
  a.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] b.toCoeffField

/-- Public a.e. symmetry predicate for coefficient representatives.

The Chapter 2 public layer deliberately does not use pointwise symmetry as a
theorem hypothesis. -/
def IsSymmetric {d : ℕ} {U : Domain d} (a : CoeffOn U) : Prop :=
  ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), (a.toCoeffField x).IsSymm

/-- `b` is the a.e. scalar rescaling `c a` on the public domain. -/
def AEScaled {d : ℕ} {U : Domain d} (c : ℝ) (a b : CoeffOn U) : Prop :=
  b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x => c • a.toCoeffField x

/-- `b` is the restriction of `a` to a smaller public domain, modulo null sets.

This is deliberately an a.e. relation between coefficient representatives, rather
than a pointwise restriction definition. -/
def RestrictsTo {d : ℕ} {U V : Domain d} (a : CoeffOn U) (b : CoeffOn V) : Prop :=
  b.toCoeffField =ᵐ[volumeMeasureOn (V : Set (Vec d))] a.toCoeffField

namespace AEEq

theorem refl {d : ℕ} {U : Domain d} (a : CoeffOn U) : AEEq a a :=
  Filter.EventuallyEq.rfl

theorem symm {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : AEEq a b) : AEEq b a :=
  Filter.EventuallyEq.symm h

theorem trans {d : ℕ} {U : Domain d} {a b c : CoeffOn U}
    (hab : AEEq a b) (hbc : AEEq b c) : AEEq a c :=
  Filter.EventuallyEq.trans hab hbc

end AEEq

theorem AEEq.transpose {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : AEEq a b) : AEEq a.transpose b.transpose :=
  h.mono fun x hx => by
    simp [hx]

theorem transpose_transpose_aeeq {d : ℕ} {U : Domain d} (a : CoeffOn U) :
    AEEq a.transpose.transpose a := by
  exact Filter.Eventually.of_forall fun x => by
    ext i j
    simp [matTranspose]

end CoeffOn

/-- Public Chapter 2 notation for `A(U; a)`. -/
abbrev Solution {d : ℕ} (U : Domain d) (a : CoeffOn U) :=
  AHarmonicFunction a.toCoeffField (U : Set (Vec d))

namespace Solution

/-- Two public solutions have the same gradient on `U`, modulo null sets. -/
def SameGradientAE {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (u v : Solution U a) : Prop :=
  u.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.toH1.grad

namespace SameGradientAE

theorem refl {d : ℕ} {U : Domain d} {a : CoeffOn U} (u : Solution U a) :
    SameGradientAE u u :=
  Filter.EventuallyEq.rfl

theorem symm {d : ℕ} {U : Domain d} {a : CoeffOn U} {u v : Solution U a}
    (h : SameGradientAE u v) : SameGradientAE v u :=
  Filter.EventuallyEq.symm h

theorem trans {d : ℕ} {U : Domain d} {a : CoeffOn U} {u v w : Solution U a}
    (huv : SameGradientAE u v) (hvw : SameGradientAE v w) : SameGradientAE u w :=
  Filter.EventuallyEq.trans huv hvw

end SameGradientAE

/-- Transport a solution across a change of coefficient representative on a null set. -/
def ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (u : Solution U a) : Solution U b where
  toH1 := u.toH1
  isHarmonic := by
    rcases u.isHarmonic with ⟨hpot, hsol⟩
    refine ⟨hpot, ?_⟩
    intro φ
    calc
      ∫ x in (U : Set (Vec d)),
          vecDot (matVecMul (b.toCoeffField x) (u.toH1.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume
          = ∫ x in (U : Set (Vec d)),
              vecDot (matVecMul (a.toCoeffField x) (u.toH1.grad x))
                (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              refine MeasureTheory.integral_congr_ae ?_
              exact h.symm.mono fun x hx => by
                simp [hx]
      _ = 0 := hsol φ

@[simp] theorem toH1_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (u : Solution U a) :
    (ofAEEq h u).toH1 = u.toH1 :=
  rfl

@[simp] theorem ofAEEq_refl {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (u : Solution U a) :
    ofAEEq (CoeffOn.AEEq.refl a) u = u :=
  rfl

theorem sameGradientAE_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {u v : Solution U a}
    (huv : SameGradientAE u v) : SameGradientAE (ofAEEq h u) (ofAEEq h v) :=
  huv

end Solution

/-- Public Chapter 2 notation for the adjoint solution space `A*(U; a)`. -/
abbrev AdjointSolution {d : ℕ} (U : Domain d) (a : CoeffOn U) :=
  AStarHarmonicFunction (U : Set (Vec d)) a.toCoeffField

/-- The zero solution, used to show that the response supremum is over a
nonempty set. -/
def zeroSolution {d : ℕ} (U : Domain d) (a : CoeffOn U) : Solution U a where
  toH1 := 0
  isHarmonic := isAHarmonicGradient_zero

end

end Ch02
end Book
end Homogenization
