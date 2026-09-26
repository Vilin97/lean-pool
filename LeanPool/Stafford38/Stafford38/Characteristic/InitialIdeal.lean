/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.EulerRemainder
public import Mathlib.RingTheory.Support


/-!
# Bernstein initial ideals and characteristic support

For a right ideal in the presented Weyl algebra, its Bernstein principal
components generate an ordinary ideal in the commutative symbol ring.  This
file defines the resulting cyclic graded module and its support.  The
construction is concrete: no abstract D-module or characteristic-variety
interface is assumed.
-/

@[expose] public section

namespace Stafford38.CharacteristicInitialIdeal

open Stafford38.Characteristic
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylEulerResidue

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Principal components of Bernstein-filtered elements of a right ideal. -/
def bernsteinInitialGeneratorSet {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Set (SymbolRing k n) :=
  {P | ∃ (N : ℕ) (z : PresentedWeyl k n),
      z ∈ bernsteinPiece k n N ∧ z ∈ I ∧
        P = presentedPrincipalComponent k bernsteinWeight N z}

/-- The commutative initial ideal of a right ideal for the Bernstein
filtration. -/
def bernsteinInitialIdeal {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Ideal (SymbolRing k n) :=
  Ideal.span (bernsteinInitialGeneratorSet k I)

/-- The cyclic commutative module defined by the Bernstein initial ideal. -/
abbrev BernsteinCharacteristicModule {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :=
  SymbolRing k n ⧸ bernsteinInitialIdeal k I

private theorem quotient_subsingleton_iff_top {R : Type u} [CommRing R]
    (J : Ideal R) : Subsingleton (R ⧸ J) ↔ J = ⊤ := by
  constructor
  · intro h
    apply le_antisymm le_top
    intro r hr
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    exact Subsingleton.elim (Ideal.Quotient.mk J r) 0
  · intro h
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : Ideal.Quotient.mk J a = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 (h ▸ trivial)
    have hb : Ideal.Quotient.mk J b = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 (h ▸ trivial)
    exact ha.trans hb.symm

/-- Characteristic support as module support on the affine symbol spectrum. -/
def bernsteinCharacteristicSupport {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Set (PrimeSpectrum (SymbolRing k n)) :=
  Module.support (SymbolRing k n) (BernsteinCharacteristicModule k I)

/-- The characteristic module is cyclic, so its support is exactly the closed
set cut out by the initial ideal. -/
theorem bernsteinCharacteristicSupport_eq_zeroLocus {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :
    bernsteinCharacteristicSupport k I =
      PrimeSpectrum.zeroLocus (bernsteinInitialIdeal k I) := by
  rw [bernsteinCharacteristicSupport, Module.support_of_algebra]
  apply congrArg PrimeSpectrum.zeroLocus
  ext P
  change algebraMap (SymbolRing k n) (BernsteinCharacteristicModule k I) P = 0 ↔
    P ∈ bernsteinInitialIdeal k I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Empty characteristic support is equivalent to the initial ideal being
the unit ideal.  Reflecting this condition back to the Weyl right ideal is a
separate filtered degree-lowering theorem. -/
theorem bernsteinCharacteristicSupport_eq_empty_iff {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :
    bernsteinCharacteristicSupport k I = ∅ ↔
      bernsteinInitialIdeal k I = ⊤ := by
  rw [bernsteinCharacteristicSupport, Module.support_eq_empty_iff,
    quotient_subsingleton_iff_top]

theorem principalComponent_mem_bernsteinInitialIdeal {n N : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (z : PresentedWeyl k n)
    (hz : z ∈ bernsteinPiece k n N) (hI : z ∈ I) :
    presentedPrincipalComponent k bernsteinWeight N z ∈
      bernsteinInitialIdeal k I := by
  apply Ideal.subset_span
  exact ⟨N, z, hz, hI, rfl⟩

theorem mem_annihilator_bernsteinCharacteristicModule {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) {P : SymbolRing k n}
    (hP : P ∈ bernsteinInitialIdeal k I) :
    P ∈ Module.annihilator (SymbolRing k n)
      (BernsteinCharacteristicModule k I) := by
  rw [Module.mem_annihilator]
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (bernsteinInitialIdeal k I) (P * r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (bernsteinInitialIdeal k I).mul_mem_right r hP

/-- Every element of the initial ideal vanishes on characteristic support. -/
theorem bernsteinCharacteristicSupport_subset_zeroLocus {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) {P : SymbolRing k n}
    (hP : P ∈ bernsteinInitialIdeal k I) :
    bernsteinCharacteristicSupport k I ⊆
      PrimeSpectrum.zeroLocus ({P} : Set (SymbolRing k n)) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus]
  intro f hf
  rw [Set.mem_singleton_iff.mp hf]
  exact Module.annihilator_le_of_mem_support hp
    (mem_annihilator_bernsteinCharacteristicModule k I hP)

/-- The defining operator belongs to the literal canonical right ideal, so
its Bernstein principal component belongs to the corresponding initial
ideal. -/
theorem canonical_principalComponent_mem_initialIdeal
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    presentedPrincipalComponent k bernsteinWeight N d ∈
      bernsteinInitialIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N) := by
  exact principalComponent_mem_bernsteinInitialIdeal k _ d hd.1
    (firstGenerator_mem (presentedCoordinate k n) d N)

/-- The concrete characteristic support is contained in the normalized
principal-symbol hypersurface. -/
theorem canonical_bernsteinCharacteristicSupport_subset_principal_zeroLocus
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    bernsteinCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N) ⊆
      PrimeSpectrum.zeroLocus
        ({presentedPrincipalComponent k bernsteinWeight N d} :
          Set (SymbolRing k (n + 1))) := by
  exact bernsteinCharacteristicSupport_subset_zeroLocus k _
    (canonical_principalComponent_mem_initialIdeal k n N hd)

theorem canonical_principalComponent_pureMomentumCoefficient
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedPrincipalComponent k bernsteinWeight N d).coeff (Finsupp.single (.inr (0 : Fin (n
      + 1))) N) = 1 := by
  rw [coeff_principal_pure_eq_normalForm]
  exact hd.2

/-! ## Differential-order characteristic support

The preceding Bernstein construction is a finite-weight scaffold. The
noncharacteristic theorem uses the differential-order filtration, whose base
variables have weight zero and fibre variables weight one. The canonical
theorems below deliberately retain the normalized Bernstein bound: the
in characteristic zero, symplectic normalization produces it for every nonzero
non-scalar operator
(`Stafford38.WeylMonicNormalization.scalar_or_normalized_symplectic_image`), and together
with order degree `N` it forces the order principal symbol to involve fibre
variables only. This implication is proved explicitly below.

The cyclic quotient by `orderInitialIdeal` is the intended concrete model for
the associated graded quotient. Its identification with the filtration
quotients, and reflection of an empty order support back to the Weyl quotient,
remain separate theorems; neither is assumed here. -/

/-- Principal order components of elements of a right ideal, in every filtration degree. -/
def orderInitialGeneratorSet {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Set (SymbolRing k n) :=
  {P | ∃ (N : ℕ) (z : PresentedWeyl k n),
      z ∈ orderPiece k n N ∧ z ∈ I ∧
        P = presentedPrincipalComponent k orderWeight N z}

/-- The symbol ideal generated by principal order components of the right ideal. -/
def orderInitialIdeal {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Ideal (SymbolRing k n) :=
  Ideal.span (orderInitialGeneratorSet k I)

/-- The symbol-ring quotient defining the order characteristic module. -/
abbrev OrderCharacteristicModule {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :=
  SymbolRing k n ⧸ orderInitialIdeal k I

/-- The prime-spectrum support of the order characteristic module. -/
def orderCharacteristicSupport {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) : Set (PrimeSpectrum (SymbolRing k n)) :=
  Module.support (SymbolRing k n) (OrderCharacteristicModule k I)

theorem orderCharacteristicSupport_eq_zeroLocus {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :
    orderCharacteristicSupport k I =
      PrimeSpectrum.zeroLocus (orderInitialIdeal k I) := by
  rw [orderCharacteristicSupport, Module.support_of_algebra]
  apply congrArg PrimeSpectrum.zeroLocus
  ext P
  change algebraMap (SymbolRing k n) (OrderCharacteristicModule k I) P = 0 ↔
    P ∈ orderInitialIdeal k I
  exact Ideal.Quotient.eq_zero_iff_mem

theorem orderCharacteristicSupport_eq_empty_iff {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) :
    orderCharacteristicSupport k I = ∅ ↔ orderInitialIdeal k I = ⊤ := by
  rw [orderCharacteristicSupport, Module.support_eq_empty_iff,
    quotient_subsingleton_iff_top]

/-- Differential order is bounded above by Bernstein degree on every PBW
monomial. -/
theorem monomialWeight_order_le_bernstein {n : ℕ}
    (m : PhaseVar n →₀ ℕ) :
    monomialWeight (@orderWeight n) m ≤
      monomialWeight (@bernsteinWeight n) m := by
  classical
  simp only [monomialWeight]
  apply Finsupp.sum_le_sum
  intro j hj
  cases j <;> simp [orderWeight, fibreWeight, bernsteinWeight]

/-- If order degree reaches a Bernstein bound, no coordinate exponent can
occur. -/
theorem coordinateExponent_eq_zero_of_order_eq_of_bernstein_le
    {n N : ℕ} (m : PhaseVar n →₀ ℕ)
    (horder : monomialWeight (@orderWeight n) m = N)
    (hbernstein : monomialWeight (@bernsteinWeight n) m ≤ N)
    (i : Fin n) : m (.inl i) = 0 := by
  by_contra hi
  let m' := m - Finsupp.single (.inl i) 1
  have hordSub := Finsupp.weight_sub_single_add
    (w := @orderWeight n) hi
  have hbernSub := Finsupp.weight_sub_single_add
    (w := @bernsteinWeight n) hi
  have hle := monomialWeight_order_le_bernstein m'
  have hordCoordinate : orderWeight (.inl i) = 0 := by
    simp [orderWeight, fibreWeight]
  have hbernCoordinate : bernsteinWeight (.inl i) = 1 := by
    simp [bernsteinWeight]
  change monomialWeight (@orderWeight n) m' + orderWeight (.inl i) =
    monomialWeight (@orderWeight n) m at hordSub
  change monomialWeight (@bernsteinWeight n) m' + bernsteinWeight (.inl i) =
    monomialWeight (@bernsteinWeight n) m at hbernSub
  rw [hordCoordinate, add_zero, horder] at hordSub
  rw [hbernCoordinate] at hbernSub
  omega

/-- A symbol uses only fibre variables when every monomial carrying a
coordinate exponent has zero coefficient. -/
def IsFibreOnly {n : ℕ} (P : SymbolRing k n) : Prop :=
  ∀ m, P.coeff m ≠ 0 →
    ∀ i : Fin n, m (.inl i) = 0

theorem orderPrincipalComponent_mem_initialIdeal {n N : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (z : PresentedWeyl k n)
    (hz : z ∈ orderPiece k n N) (hI : z ∈ I) :
    presentedPrincipalComponent k orderWeight N z ∈ orderInitialIdeal k I := by
  apply Ideal.subset_span
  exact ⟨N, z, hz, hI, rfl⟩

theorem orderCharacteristicSupport_subset_zeroLocus {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) {P : SymbolRing k n}
    (hP : P ∈ orderInitialIdeal k I) :
    orderCharacteristicSupport k I ⊆
      PrimeSpectrum.zeroLocus ({P} : Set (SymbolRing k n)) := by
  rw [orderCharacteristicSupport_eq_zeroLocus]
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
  intro f hf
  rw [Set.mem_singleton_iff.mp hf]
  exact hp hP

theorem canonical_orderPrincipalComponent_mem_initialIdeal
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    presentedPrincipalComponent k orderWeight N d ∈
      orderInitialIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N) := by
  exact orderPrincipalComponent_mem_initialIdeal k _ d
    (bernsteinPiece_le_orderPiece k (n + 1) N hd.1)
    (firstGenerator_mem (presentedCoordinate k n) d N)

theorem canonical_orderCharacteristicSupport_subset_principal_zeroLocus
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N) ⊆
      PrimeSpectrum.zeroLocus
        ({presentedPrincipalComponent k orderWeight N d} :
          Set (SymbolRing k (n + 1))) := by
  exact orderCharacteristicSupport_subset_zeroLocus k _
    (canonical_orderPrincipalComponent_mem_initialIdeal k n N hd)

theorem canonical_orderPrincipalComponent_pureMomentumCoefficient
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedPrincipalComponent k orderWeight N d).coeff (Finsupp.single (.inr (0 : Fin (n +
      1))) N) = 1 := by
  rw [coeff_presentedPrincipalComponent]
  have hweight : monomialWeight (@orderWeight (n + 1))
      (Finsupp.single (.inr (0 : Fin (n + 1))) N) = N := by
    simp [monomialWeight, orderWeight, fibreWeight]
  rw [ite_eq_left hweight]
  exact hd.2

/-- The normalized Bernstein bound makes the degree-`N` order symbol a
constant-coefficient polynomial in the fibre variables. -/
theorem canonical_orderPrincipalComponent_isFibreOnly
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    IsFibreOnly k (presentedPrincipalComponent k orderWeight N d) := by
  intro m hm i
  rw [coeff_presentedPrincipalComponent] at hm
  by_cases horder : monomialWeight (@orderWeight (n + 1)) m = N
  · rw [ite_eq_left horder] at hm
    have hbernstein :=
      (mem_presentedWeightPiece k (@bernsteinWeight (n + 1)) N d).mp
        hd.1 m hm
    exact coordinateExponent_eq_zero_of_order_eq_of_bernstein_le
      m horder hbernstein i
  · rw [ite_eq_right horder] at hm
    exact (hm rfl).elim


end

end Stafford38.CharacteristicInitialIdeal
