/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Normal.Basic

/-! # Unique Ring -/

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  hasExtension_valuation_of_valuationSubring_pullback →
    hasExtension_valuation_of_valuationSubring_pullback

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_pullback_of_hasExtension_valuation →
    valuationSubring_pullback_of_hasExtension_valuation

namespace ValuationTheory

/-!
# The unique-extension characterization: automorphism invariance from unique extension

The pullback of an extension valuation ring by a ground-field automorphism is
again an extension valuation ring.  Hence uniqueness forces the chosen ring
to be fixed by every automorphism of the extension field.  This is the first
Galois-theoretic step in the converse direction of the unique-extension characterization.
-/

noncomputable section

open scoped Pointwise

namespace Valuations

/-- Translating an extension valuation ring by a `K`-automorphism preserves
the extension property. -/
theorem algEquiv_smul_valuationSubring_hasExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (σ : L ≃ₐ[K] L) :
    V.valuation.HasExtension (σ • W).valuation := by
  let : V.valuation.HasExtension W.valuation := hW
  have hpullback : ∀ x : K,
      algebraMap K L x ∈ (σ • W).toSubring ↔ x ∈ V.toSubring := by
    intro x
    calc
      algebraMap K L x ∈ (σ • W).toSubring ↔
          algebraMap K L x ∈ (σ • W : ValuationSubring L) :=
        (σ • W).mem_toSubring (algebraMap K L x)
      _ ↔ σ⁻¹ • algebraMap K L x ∈ W :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      _ ↔ algebraMap K L x ∈ W := by
        simp
      _ ↔ x ∈ V := by
        simpa only [ValuationSubring.mem_toSubring,
          ValuationSubring.valuationSubring_valuation] using
          (valuationSubring_pullback_of_hasExtension_valuation
            V.valuation W x)
      _ ↔ x ∈ V.toSubring := (V.mem_toSubring x).symm
  apply
    hasExtension_valuation_of_valuationSubring_pullback
  intro x
  simpa only [ValuationSubring.mem_toSubring,
    ValuationSubring.valuationSubring_valuation] using hpullback x

/-- If the extension valuation ring is unique, every ground-field
automorphism stabilizes it. -/
theorem algEquiv_smul_valuationSubring_eq_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) :
    σ • W = W :=
  huniq (σ • W)
    (algEquiv_smul_valuationSubring_hasExtension V W hW σ)

/-- The preceding equality in elementwise form. -/
theorem algEquiv_mem_valuationSubring_iff_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : L) :
    σ x ∈ W.toSubring ↔ x ∈ W.toSubring := by
  have hstable :=
    algEquiv_smul_valuationSubring_eq_of_unique_extension V W hW huniq σ
  constructor
  · intro hx
    have : σ x ∈ σ • W := by simpa [hstable] using hx
    exact (ValuationSubring.smul_mem_pointwise_smul_iff
      (g := σ) (S := W) (x := x)).1 this
  · intro hx
    have : σ x ∈ σ • W :=
      ValuationSubring.smul_mem_pointwise_smul σ x W hx
    simpa [hstable] using this

/-- A ground-field automorphism restricts to an automorphism of the unique
extension valuation ring. -/
def valuationSubringEquivOfUniqueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) : W ≃+* W where
  toFun x := ⟨σ (x : L),
    (algEquiv_mem_valuationSubring_iff_of_unique_extension
      V W hW huniq σ (x : L)).2 x.2⟩
  invFun x := ⟨σ⁻¹ (x : L),
    (algEquiv_mem_valuationSubring_iff_of_unique_extension
      V W hW huniq σ⁻¹ (x : L)).2 x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

/-- The unique-extension equivalence acts on underlying valuation-ring elements as expected. -/
@[simp]
theorem coe_valuationSubringEquivOfUniqueExtension_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : W) :
    ((valuationSubringEquivOfUniqueExtension V W hW huniq σ x : W) : L) =
      σ (x : L) :=
  rfl

/-- The induced automorphism of the residue field of the unique extension
valuation ring. -/
def residueFieldEquivOfUniqueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) :
    IsLocalRing.ResidueField W ≃+* IsLocalRing.ResidueField W :=
  IsLocalRing.ResidueField.mapEquiv
    (valuationSubringEquivOfUniqueExtension V W hW huniq σ)

/-- Reduction commutes with the automorphism induced on the unique
extension's residue field. -/
theorem residueFieldEquivOfUniqueExtension_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : W) :
    residueFieldEquivOfUniqueExtension V W hW huniq σ
        (IsLocalRing.residue W x) =
      IsLocalRing.residue W
        ⟨σ (x : L),
          (algEquiv_mem_valuationSubring_iff_of_unique_extension
            V W hW huniq σ (x : L)).2 x.2⟩ := by
  change
    IsLocalRing.ResidueField.map
        (valuationSubringEquivOfUniqueExtension V W hW huniq σ : W →+* W)
        (IsLocalRing.residue W x) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 1

/-- The canonical homomorphism from the base valuation ring into an extension
valuation ring, without identifying either ring with the valuation subring of
its canonical valuation. -/
def valuationSubringMapOfHasExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) : V →+* W := by
  letI : V.valuation.HasExtension W.valuation := hW
  exact (algebraMap K L).restrict V.toSubring W.toSubring (by
    intro x hx
    exact
      (valuationSubring_pullback_of_hasExtension_valuation
        V.valuation W x).2 (by
          simpa only [ValuationSubring.valuationSubring_valuation,
            ValuationSubring.mem_toSubring] using hx))

/-- The canonical map of valuation rings attached to an extension is local. -/
theorem valuationSubringMapOfHasExtension_isLocalHom
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) :
    IsLocalHom (valuationSubringMapOfHasExtension V W hW) := by
  let : V.valuation.HasExtension W.valuation := hW
  apply ((IsLocalRing.local_hom_TFAE
    (valuationSubringMapOfHasExtension V W hW)).out 5 1).mp
  ext x
  rw [Ideal.mem_comap, W.valuation_lt_one_iff, V.valuation_lt_one_iff]
  change
    W.valuation (algebraMap K L (x : K)) < 1 ↔
      V.valuation (x : K) < 1
  exact
    _root_.Valuation.HasExtension.val_map_lt_one_iff
      V.valuation W.valuation (x : K)

/-- The residue-field homomorphism induced by the canonical local map of
valuation rings. -/
def residueFieldMapOfHasExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) :
    IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField W := by
  letI : IsLocalHom (valuationSubringMapOfHasExtension V W hW) :=
    valuationSubringMapOfHasExtension_isLocalHom V W hW
  exact IsLocalRing.ResidueField.map
    (valuationSubringMapOfHasExtension V W hW)

/-- The induced residue-field automorphism fixes the embedded residue field
of the base valuation ring. -/
theorem residueFieldEquivOfUniqueExtension_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L)
    (x : IsLocalRing.ResidueField V) :
    residueFieldEquivOfUniqueExtension V W hW huniq σ
        (residueFieldMapOfHasExtension V W hW x) =
      residueFieldMapOfHasExtension V W hW x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change
    residueFieldEquivOfUniqueExtension V W hW huniq σ
        (IsLocalRing.residue W
          (valuationSubringMapOfHasExtension V W hW a)) =
      IsLocalRing.residue W (valuationSubringMapOfHasExtension V W hW a)
  rw [residueFieldEquivOfUniqueExtension_residue]
  congr 1
  ext
  exact σ.commutes (a : K)

/-- Conjugate integral elements have conjugate reductions over the residue
field of the base valuation ring.  In particular, their reductions have the
same minimal polynomial.  This is the residue-field form of the Galois
argument used in the converse direction of the unique-extension characterization. -/
theorem minpoly_residue_eq_of_minpoly_eq_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Normal K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    {x y : L} (hxy : minpoly K x = minpoly K y)
    (hx : x ∈ W.toSubring) (hy : y ∈ W.toSubring) :
    letI : Algebra (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W) :=
      (residueFieldMapOfHasExtension V W hW).toAlgebra
    minpoly (IsLocalRing.ResidueField V)
        (IsLocalRing.residue W ⟨x, hx⟩) =
      minpoly (IsLocalRing.ResidueField V)
        (IsLocalRing.residue W ⟨y, hy⟩) := by
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (residueFieldMapOfHasExtension V W hW).toAlgebra
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hxy
  let e : IsLocalRing.ResidueField W ≃ₐ[IsLocalRing.ResidueField V]
      IsLocalRing.ResidueField W :=
    { residueFieldEquivOfUniqueExtension V W hW huniq σ with
      commutes' := fun z =>
        residueFieldEquivOfUniqueExtension_algebraMap V W huniq σ z }
  have hred :
      e (IsLocalRing.residue W ⟨y, hy⟩) =
        IsLocalRing.residue W ⟨x, hx⟩ := by
    change
      residueFieldEquivOfUniqueExtension V W hW huniq σ
          (IsLocalRing.residue W ⟨y, hy⟩) =
        IsLocalRing.residue W ⟨x, hx⟩
    rw [residueFieldEquivOfUniqueExtension_residue]
    congr 1
    exact Subtype.ext hσ
  rw [← hred]
  exact minpoly.algEquiv_eq e _

end Valuations
end

end ValuationTheory
