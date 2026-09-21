/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.FiniteSeparableDVRChartFoundation
import LeanPool.Stafford38.Stafford38.Geometry.RelativeCoefficientDVRPlace
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# A residue-field section in the adic completion of the retained DVR

Let `V` be a commutative local `E`-algebra and let `K` be its residue field.
If `K/E` is separable, formal etaleness gives a unique coefficient section in
every positive quotient `V / m^(n+1)`.  Uniqueness makes those sections
compatible with the quotient transition maps.  This file assembles the
compatible family in Mathlib's `m`-adic completion and proves that the
level-one residue map retracts it.

The retained DVR produced by `RelativeCoefficientDVRPlace` satisfies the
separability hypothesis in characteristic zero, so the construction applies
to it directly.  No equivalence with a power-series ring is asserted.
-/

namespace Stafford38.Geometry.CompletedDVRCoefficientSection

open IsLocalRing
open Stafford38.Geometry.FiniteSeparableDVRChartFoundation
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.AsymptoticDivisorExistence

noncomputable section


universe u

section LocalAlgebra

variable (E V : Type u)
variable [Field E] [CommRing V] [IsLocalRing V] [Algebra E V]

private abbrev K := ResidueField V
private abbrev m : Ideal V := maximalIdeal V

/-- The positive `n`-th nilpotent quotient of the local ring. -/
abbrev AdicJet (n : ℕ) := V ⧸ ((m V) ^ (n + 1))

/-- Reduction of a positive adic jet to the residue field. -/
def adicJetResidue (n : ℕ) : AdicJet V n →ₐ[E] K V :=
  Ideal.Quotient.liftₐ ((m V) ^ (n + 1))
    (IsScalarTower.toAlgHom E V (K V)) (by
      intro x hx
      change residue V x = 0
      rw [residue_eq_zero_iff]
      exact Ideal.pow_le_self (Nat.succ_ne_zero n) hx)

/-- Reduction from every positive adic jet is surjective. -/
theorem adicJetResidue_surjective (n : ℕ) :
    Function.Surjective (adicJetResidue E V n) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective (R := V) z
  exact ⟨Ideal.Quotient.mk ((m V) ^ (n + 1)) x, rfl⟩

/-- The kernel of positive-jet reduction is nilpotent. -/
theorem adicJetResidue_kernel_isNilpotent (n : ℕ) :
    IsNilpotent (RingHom.ker (adicJetResidue E V n).toRingHom) := by
  have hkerLift :
      RingHom.ker (adicJetResidue E V n).toRingHom =
        (RingHom.ker (IsScalarTower.toAlgHom E V (K V)).toRingHom).map
          (Ideal.Quotient.mk ((m V) ^ (n + 1))) := by
    exact Ideal.ker_quotient_lift _ _
  rw [hkerLift]
  have hker :
      RingHom.ker (IsScalarTower.toAlgHom E V (K V)).toRingHom = m V := by
    change RingHom.ker (algebraMap V (K V)) = m V
    rw [ResidueField.algebraMap_eq, ker_residue]
  rw [hker]
  refine ⟨n + 1, ?_⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

/-- The unique coefficient section in the positive `n`-th adic jet. -/
def adicJetCoefficientSection
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ) :
    K V →ₐ[E] AdicJet V n :=
  finiteSeparableSection E (K V) (AdicJet V n) hsep
    (adicJetResidue E V n) (adicJetResidue_surjective E V n)
    (adicJetResidue_kernel_isNilpotent E V n)

/-- Each finite-level coefficient map is a section of reduction. -/
@[simp]
theorem adicJetResidue_comp_adicJetCoefficientSection
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ) :
    (adicJetResidue E V n).comp (adicJetCoefficientSection E V hsep n) =
      AlgHom.id E (K V) :=
  residue_comp_finiteSeparableSection E (K V) (AdicJet V n) hsep
    (adicJetResidue E V n) (adicJetResidue_surjective E V n)
    (adicJetResidue_kernel_isNilpotent E V n)

/-- The transition map between two positive adic jets. -/
def adicJetTransition {a b : ℕ} (hab : a ≤ b) :
    AdicJet V b →ₐ[E] AdicJet V a :=
  Ideal.quotientMapₐ ((m V) ^ (a + 1)) (AlgHom.id E V) (by
    simpa using Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))

/-- Reduction commutes with every positive-jet transition. -/
theorem adicJetResidue_comp_transition {a b : ℕ} (hab : a ≤ b) :
    (adicJetResidue E V a).comp (adicJetTransition E V hab) =
      adicJetResidue E V b := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Uniqueness forces the positive finite-level sections to be compatible. -/
theorem adicJetCoefficientSection_compatible
    (hsep : Algebra.IsSeparable E (K V)) {a b : ℕ} (hab : a ≤ b) :
    (adicJetTransition E V hab).comp
        (adicJetCoefficientSection E V hsep b) =
      adicJetCoefficientSection E V hsep a := by
  exact finiteSeparableSection_naturality E (K V)
    (AdicJet V a) (AdicJet V b) hsep
    (adicJetResidue E V a) (adicJetResidue_surjective E V a)
    (adicJetResidue_kernel_isNilpotent E V a)
    (adicJetResidue E V b) (adicJetResidue_surjective E V b)
    (adicJetResidue_kernel_isNilpotent E V b)
    (adicJetTransition E V hab) (adicJetResidue_comp_transition E V hab)

/-- Convert the usual quotient by `m^n` to the coordinate quotient used in
the definition of `AdicCompletion`. -/
private def exactQuotientToCompletionCoordinate (n : ℕ) :
    (V ⧸ ((m V) ^ n)) ≃ₐ[E]
      V ⧸ ((m V) ^ n • ⊤ : Ideal V) := by
  have h : ((m V) ^ n • ⊤ : Ideal V) = (m V) ^ n := by
    ext x
    simp
  exact (Ideal.quotientEquivAlgOfEq V h).symm.restrictScalars E

/-- The zeroth completion coordinate is the zero quotient, so it has a unique
`E`-algebra map from the residue field. -/
private def zeroCompletionCoordinateSection :
    K V →ₐ[E] V ⧸ ((m V) ^ 0 • ⊤ : Ideal V) := by
  have htop : ((m V) ^ 0 • ⊤ : Ideal V) = ⊤ := by simp
  letI : Subsingleton (V ⧸ ((m V) ^ 0 • ⊤ : Ideal V)) := by
    rw [htop]
    infer_instance
  exact {
    toFun := fun _ ↦ 0
    map_one' := Subsingleton.elim _ _
    map_mul' := fun _ _ ↦ Subsingleton.elim _ _
    map_zero' := rfl
    map_add' := fun _ _ ↦ Subsingleton.elim _ _
    commutes' := fun _ ↦ Subsingleton.elim _ _ }

/-- The coefficient section in every coordinate of Mathlib's adic inverse
limit.  Coordinate zero is trivial; coordinate `n+1` is the formally etale
section in `V / m^(n+1)`. -/
def completionCoordinateSection
    (hsep : Algebra.IsSeparable E (K V)) :
    ∀ n : ℕ, K V →ₐ[E] V ⧸ ((m V) ^ n • ⊤ : Ideal V)
  | 0 => zeroCompletionCoordinateSection E V
  | n + 1 =>
      (exactQuotientToCompletionCoordinate E V (n + 1)).toAlgHom.comp
        (adicJetCoefficientSection E V hsep n)

/-- Transition on exact power quotients agrees with transition on the raw
coordinates occurring in `AdicCompletion`. -/
private theorem transition_exactQuotientToCompletionCoordinate
    {a b : ℕ} (hab : a ≤ b) (x : V ⧸ ((m V) ^ b)) :
    AdicCompletion.transitionMap (m V) V hab
        (exactQuotientToCompletionCoordinate E V b x) =
      exactQuotientToCompletionCoordinate E V a
        (Ideal.quotientMapₐ ((m V) ^ a) (AlgHom.id E V)
          (by simpa using Ideal.pow_le_pow_right hab) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The completion-coordinate sections form a compatible inverse-limit
family. -/
theorem completionCoordinateSection_compatible
    (hsep : Algebra.IsSeparable E (K V)) {a b : ℕ} (hab : a ≤ b)
    (x : K V) :
    AdicCompletion.transitionMap (m V) V hab
        (completionCoordinateSection E V hsep b x) =
      completionCoordinateSection E V hsep a x := by
  cases a with
  | zero =>
      have htop : ((m V) ^ 0 • ⊤ : Ideal V) = ⊤ := by simp
      letI : Subsingleton (V ⧸ ((m V) ^ 0 • ⊤ : Ideal V)) := by
        rw [htop]
        infer_instance
      exact Subsingleton.elim _ _
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          have hab' : a ≤ b := Nat.succ_le_succ_iff.mp hab
          change AdicCompletion.transitionMap (m V) V hab
              (exactQuotientToCompletionCoordinate E V (b + 1)
                (adicJetCoefficientSection E V hsep b x)) =
            exactQuotientToCompletionCoordinate E V (a + 1)
              (adicJetCoefficientSection E V hsep a x)
          rw [transition_exactQuotientToCompletionCoordinate E V hab]
          change exactQuotientToCompletionCoordinate E V (a + 1)
              (adicJetTransition E V hab'
                (adicJetCoefficientSection E V hsep b x)) =
            exactQuotientToCompletionCoordinate E V (a + 1)
              (adicJetCoefficientSection E V hsep a x)
          exact congrArg (exactQuotientToCompletionCoordinate E V (a + 1))
            (DFunLike.congr_fun
              (adicJetCoefficientSection_compatible E V hsep hab') x)

/-- The compatible finite-level sections assemble to an actual
`E`-algebra coefficient section in the adic completion. -/
def completedCoefficientSection
    (hsep : Algebra.IsSeparable E (K V)) :
    K V →ₐ[E] AdicCompletion (m V) V where
  toFun x :=
    ⟨fun n ↦ completionCoordinateSection E V hsep n x,
      fun hab ↦ completionCoordinateSection_compatible E V hsep hab x⟩
  map_one' := AdicCompletion.ext fun n ↦
    (completionCoordinateSection E V hsep n).map_one
  map_mul' x y := AdicCompletion.ext fun n ↦
    (completionCoordinateSection E V hsep n).map_mul x y
  map_zero' := AdicCompletion.ext fun n ↦
    (completionCoordinateSection E V hsep n).map_zero
  map_add' x y := AdicCompletion.ext fun n ↦
    (completionCoordinateSection E V hsep n).map_add x y
  commutes' e := AdicCompletion.ext fun n ↦
    (completionCoordinateSection E V hsep n).commutes e

/-- Evaluation of the completed section at every positive level recovers the
finite-level section constructed by formal etaleness. -/
theorem eval_completedCoefficientSection
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ) :
    ((AdicCompletion.evalₐ (m V) (n + 1)).restrictScalars E).comp
        (completedCoefficientSection E V hsep) =
      adicJetCoefficientSection E V hsep n := by
  ext x
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    completedCoefficientSection, AdicCompletion.evalₐ, AdicCompletion.eval_apply,
    completionCoordinateSection, exactQuotientToCompletionCoordinate]
  have h : ((m V) ^ (n + 1) • ⊤ : Ideal V) = (m V) ^ (n + 1) := by
    ext y
    simp
  change (Ideal.quotientEquivAlgOfEq V h)
      ((Ideal.quotientEquivAlgOfEq V h).symm
        (adicJetCoefficientSection E V hsep n x)) =
    adicJetCoefficientSection E V hsep n x
  exact (Ideal.quotientEquivAlgOfEq V h).apply_symm_apply _

/-- Residue specialization of the completion is evaluation modulo `m`,
followed by the ordinary residue map. -/
def completedResidue :
    AdicCompletion (m V) V →ₐ[E] K V :=
  (adicJetResidue E V 0).comp
    ((AdicCompletion.evalₐ (m V) 1).restrictScalars E)

/-- The adic-completion coefficient map is an actual section of residue. -/
@[simp]
theorem completedResidue_comp_completedCoefficientSection
    (hsep : Algebra.IsSeparable E (K V)) :
    (completedResidue E V).comp (completedCoefficientSection E V hsep) =
      AlgHom.id E (K V) := by
  ext x
  change adicJetResidue E V 0
      (AdicCompletion.evalₐ (m V) 1
        (completedCoefficientSection E V hsep x)) = x
  have heval :=
    DFunLike.congr_fun (eval_completedCoefficientSection E V hsep 0) x
  change AdicCompletion.evalₐ (m V) 1
      (completedCoefficientSection E V hsep x) =
    adicJetCoefficientSection E V hsep 0 x at heval
  rw [heval]
  exact DFunLike.congr_fun
    (adicJetResidue_comp_adicJetCoefficientSection E V hsep 0) x

end LocalAlgebra

section RetainedDVR

private abbrev SourceDVR (E : Type u) [Field E] :=
  CoordinateZeroLocalRing E

/-- The actual residue-field coefficient section in the maximal-ideal adic
completion of a retained DVR place. -/
def retainedCompletedCoefficientSection
    (E : Type u) [Field E] [CharZero E]
    {L : Type u} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    ResidueField D.valuation.toSubring →ₐ[E]
      AdicCompletion (maximalIdeal D.valuation.toSubring)
        D.valuation.toSubring := by
  letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
  letI : Algebra E D.valuation.toSubring :=
    (relativeCoefficientMap E D).toAlgebra
  exact completedCoefficientSection E D.valuation.toSubring
    (relativeResidue_isSeparable E D)

/-- The retained completed coefficient section is split by completed residue
specialization. -/
theorem retainedCompletedCoefficientSection_isSection
    (E : Type u) [Field E] [CharZero E]
    {L : Type u} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    (completedResidue E D.valuation.toSubring).comp
        (retainedCompletedCoefficientSection E D) =
      AlgHom.id E (ResidueField D.valuation.toSubring) := by
  letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
  letI : Algebra E D.valuation.toSubring :=
    (relativeCoefficientMap E D).toAlgebra
  exact completedResidue_comp_completedCoefficientSection E
    D.valuation.toSubring (relativeResidue_isSeparable E D)

end RetainedDVR


end

end Stafford38.Geometry.CompletedDVRCoefficientSection
