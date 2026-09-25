/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.Ideal.Quotient.Index
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
/-!
Develops quotients of valuation-ring units by higher principal units and compares their first
layer with residue-field units.
-/

@[expose] public section

namespace LocalFieldTheory

open ValuationTheory

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField.DVF

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/--
Characterizes `QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u = QuotientGroup.mk'
(higherPrincipalUnitGroup F 1) v` by the equivalent condition
`higherPrincipalUnitGroup.residueUnitHom F u = higherPrincipalUnitGroup.residueUnitHom F v`.
-/
theorem unitsModOne_mk_eq_iff_residueUnitHom_eq
    (u v : F.valuationSubringˣ) :
    QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u =
        QuotientGroup.mk' (higherPrincipalUnitGroup F 1) v ↔
      higherPrincipalUnitGroup.residueUnitHom F u =
        higherPrincipalUnitGroup.residueUnitHom F v := by
  constructor
  · intro h
    have h' := congrArg
      (higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F) h
    rw [higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk,
      higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk] at h'
    exact h'
  · intro h
    apply (higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F).injective
    rw [higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk,
      higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk]
    exact h

/--
Characterizes `QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u = QuotientGroup.mk'
(higherPrincipalUnitGroup F 1) v` by the equivalent condition `F.residueMap (u :
F.valuationSubring) = F.residueMap (v : F.valuationSubring)`.
-/
theorem unitsModOne_mk_eq_iff_residue_eq
    (u v : F.valuationSubringˣ) :
    QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u =
        QuotientGroup.mk' (higherPrincipalUnitGroup F 1) v ↔
      F.residueMap (u : F.valuationSubring) =
        F.residueMap (v : F.valuationSubring) := by
  rw [higherPrincipalUnitGroup.unitsModOne_mk_eq_iff_residueUnitHom_eq F u v,
    higherPrincipalUnitGroup.residueUnitHom_eq_iff_residue_eq F u v]

/-- A valuation-ring-preserving field automorphism induces a ring automorphism
on every quotient `O/m^n`. -/
noncomputable def quotientMaximalIdealPowRingEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    F.valuationSubring ⧸ F.maximalIdeal ^ n ≃+*
      F.valuationSubring ⧸ F.maximalIdeal ^ n := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hpow :
      F.maximalIdeal ^ n =
        (F.maximalIdeal ^ n).map
          (r : F.valuationSubring →+* F.valuationSubring) := by
    rw [Ideal.map_pow, hmax]
  exact
    Ideal.quotientEquiv (F.maximalIdeal ^ n) (F.maximalIdeal ^ n) r
      hpow

/--
Establishes the identity `quotientMaximalIdealPowRingEquivOfPreserves F e hmem n
(Ideal.Quotient.mk (F.maximalIdeal ^ n) x) = Ideal.Quotient.mk (F.maximalIdeal ^ n)
(valuationSubringRingEquivOfPreserves F e hmem x)`.
-/
@[simp] theorem quotientMaximalIdealPowRingEquivOfPreserves_mk
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (x : F.valuationSubring) :
    quotientMaximalIdealPowRingEquivOfPreserves F e hmem n
        (Ideal.Quotient.mk (F.maximalIdeal ^ n) x) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n)
        (valuationSubringRingEquivOfPreserves F e hmem x) := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hpow :
      F.maximalIdeal ^ n =
        (F.maximalIdeal ^ n).map
          (r : F.valuationSubring →+* F.valuationSubring) := by
    rw [Ideal.map_pow, hmax]
  exact
    Ideal.quotientEquiv_mk (F.maximalIdeal ^ n) (F.maximalIdeal ^ n) r
      hpow x

/-- Reduction of valuation-ring units modulo the `n`-th power of the maximal
ideal. -/
def quotientUnitHom (n : ℕ) :
    F.valuationSubringˣ →*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk (F.maximalIdeal ^ n))

/--
The defining evaluation formula for `quotientUnitHom` is
`((higherPrincipalUnitGroup.quotientUnitHom F n u : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
F.valuationSubring ⧸ F.maximalIdeal ^ n) = Ideal.Quotient.mk (F.maximalIdeal ^ n) (u :
F.valuationSubring)`.
-/
@[simp] theorem quotientUnitHom_apply (n : ℕ) (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.quotientUnitHom F n u :
        (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
      F.valuationSubring ⧸ F.maximalIdeal ^ n) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) :=
  rfl

/-- Compatibility between the induced action on `O^*`, the induced action on
`O/m^n`, and reduction of units modulo `m^n`. -/
theorem quotientUnitHom_valuationSubringUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (u : F.valuationSubringˣ) :
    Units.map
        (quotientMaximalIdealPowRingEquivOfPreserves F e hmem n).toMonoidHom
        (higherPrincipalUnitGroup.quotientUnitHom F n u) =
      higherPrincipalUnitGroup.quotientUnitHom F n
        (valuationSubringUnitEquivOfPreserves F e hmem u) := by
  apply Units.ext
  simp [higherPrincipalUnitGroup.quotientUnitHom_apply,
    valuationSubringUnitEquivOfPreserves_apply]

/-- The kernel of unit reduction modulo `m^n` is exactly the concrete
principal-unit subgroup `U^n`. -/
theorem quotientUnitHom_ker_eq (n : ℕ) :
    (higherPrincipalUnitGroup.quotientUnitHom F n).ker =
      higherPrincipalUnitGroup F n := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    have hval := congrArg
      (fun z : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ =>
        (z : F.valuationSubring ⧸ F.maximalIdeal ^ n)) hu
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1 at hval
    have hmk :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n)
            (1 : F.valuationSubring) := by
      simpa using hval
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).1 hmk
  · intro hu
    apply Units.ext
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1
    simpa using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).2 hu

/-- First-isomorphism form of unit reduction modulo `m^n`: `O^*/U^n` is the
range of the unit group of `O/m^n`. -/
noncomputable def unitsModHigherPrincipalUnitGroupEquivRange (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (higherPrincipalUnitGroup.quotientUnitHom F n).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (higherPrincipalUnitGroup.quotientUnitHom F n))

/-- For `n ≥ 1`, every unit modulo `m^n` is the reduction of a valuation-ring
unit. -/
theorem quotientUnitHom_surjective_of_pos {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (higherPrincipalUnitGroup.quotientUnitHom F n) := by
  intro y
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective
      (((y : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
        F.valuationSubring ⧸ F.maximalIdeal ^ n))
  have ha_unit : IsUnit a := by
    by_contra hnot
    have ha_mem : a ∈ F.maximalIdeal := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact (mem_nonunits_iff).2 hnot
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective
        (((y⁻¹ : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
          F.valuationSubring ⧸ F.maximalIdeal ^ n))
    have habq :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (a * b) =
          (1 : F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
      calc
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (a * b) =
            Ideal.Quotient.mk (F.maximalIdeal ^ n) a *
              Ideal.Quotient.mk (F.maximalIdeal ^ n) b := by simp
        _ = ((y : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
              F.valuationSubring ⧸ F.maximalIdeal ^ n) *
              ((y⁻¹ : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
                F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
              rw [ha, hb]
        _ = 1 := by simp
    have hdiff_pow : a * b - 1 ∈ F.maximalIdeal ^ n := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (a * b) (1 : F.valuationSubring)).1
        (by simpa using habq)
    have hn0 : n ≠ 0 := by omega
    have hdiff_max : a * b - 1 ∈ F.maximalIdeal :=
      Ideal.pow_le_self hn0 hdiff_pow
    have hab_mem : a * b ∈ F.maximalIdeal :=
      F.maximalIdeal.mul_mem_right b ha_mem
    have hone : (1 : F.valuationSubring) ∈ F.maximalIdeal := by
      have hsub : a * b - (a * b - 1) ∈ F.maximalIdeal :=
        F.maximalIdeal.sub_mem hab_mem hdiff_max
      simp at hsub
    exact (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime.one_notMem hone
  rcases ha_unit with ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa [higherPrincipalUnitGroup.quotientUnitHom_apply] using ha

/-- The unit-quotient coordinate theorem, first unit-quotient form:
`O^*/U^n ≃ (O/m^n)^*` for `n ≥ 1`. -/
noncomputable def unitsModHigherPrincipalUnitGroupEquivQuotientUnits
    (n : ℕ) (hn : 1 ≤ n) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (higherPrincipalUnitGroup.quotientUnitHom F n)
      (higherPrincipalUnitGroup.quotientUnitHom_surjective_of_pos F hn))

/-- The maximal ideal of a complete DVF valuation ring is finitely generated:
it is generated by any uniformizer. -/
theorem maximalIdeal_fg :
    F.maximalIdeal.FG := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  refine ⟨{pi}, ?_⟩
  simpa using (F.maximalIdeal_eq_span_uniformizer hpi).symm

/-- If the residue field is finite, then every quotient by a power of the
maximal ideal is finite. -/
theorem finite_quotient_maximalIdeal_pow_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal) := by
    change Finite F.residueField
    infer_instance
  exact Ideal.finite_quotient_pow
    (I := F.maximalIdeal) (higherPrincipalUnitGroup.maximalIdeal_fg F) n

/-- Finite-residue complete DVFs have finite unit quotients `O^*/U^n`. -/
theorem finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
    higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue
      F n
  exact
    Finite.of_equiv
      ((higherPrincipalUnitGroup.quotientUnitHom F n).range)
      (higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupEquivRange F n).symm

/-- The type in `Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n)` is finite. -/
noncomputable instance quotientMaximalIdealPowFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
  higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue F n

/-- The type in `Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n)` is finite. -/
noncomputable instance unitsModHigherPrincipalUnitGroupFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) :=
  higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    F n

/-- Cardinality form of `O^*/U^n ≃ (O/m^n)^*` for `n ≥ 1` over a
finite residue field.  The finite instances are derived from the residue
field before either natural cardinal is formed. -/
theorem card_unitsModHigherPrincipalUnitGroup_eq_quotientUnits
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) =
      Nat.card ((F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) := by
  exact Nat.card_congr
    (higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupEquivQuotientUnits
      F n hn).toEquiv

/-- Every concrete principal-unit subquotient is finite when the residue
field is finite.  It is identified with the range of the inclusion into the
finite full unit quotient. -/
theorem finite_principalUnitSubquotient_of_finite_residue
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) := by
  let : Finite
      (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
    exact
      higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
        F n
  let f : higherPrincipalUnitGroup F m →*
      F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n :=
    (QuotientGroup.mk' (higherPrincipalUnitGroup F n)).comp
      (higherPrincipalUnitGroup F m).subtype
  have hker : f.ker =
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' (higherPrincipalUnitGroup F n)
        (x : F.valuationSubringˣ) = 1 ↔
      (x : F.valuationSubringˣ) ∈ higherPrincipalUnitGroup F n
    exact QuotientGroup.eq_one_iff
      (N := higherPrincipalUnitGroup F n) (x : F.valuationSubringˣ)
  let e : (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact Finite.of_equiv f.range e.symm

/--
The type in `Finite (higherPrincipalUnitGroup F m ⧸ (higherPrincipalUnitGroup F n).subgroupOf
(higherPrincipalUnitGroup F m))` is finite.
-/
noncomputable instance principalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) :=
  higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue
    F m n

/-- The concrete principal-unit filtration as the abstract filtration API. -/
def toPrincipalUnitFiltration :
    AntitoneSubgroupFiltration F.valuationSubringˣ where
  subgroup := higherPrincipalUnitGroup F
  antitone := fun h => higherPrincipalUnitGroup.antitone F h

/--
Establishes the identity `(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
higherPrincipalUnitGroup F n`.
-/
@[simp] theorem toPrincipalUnitFiltration_subgroup (n : ℕ) :
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
      higherPrincipalUnitGroup F n :=
  rfl

/--
The type in `Finite ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
F).principalUnitSubquotient m n)` is finite.
-/
noncomputable instance toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite
      ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotient
        m n) := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  exact Finite.of_equiv
    (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m))
    (U.principalUnitSubquotientConcreteEquiv m n).symm.toEquiv

/-! ### Successive principal-unit quotients -/

/-- The adjacent quotient `U^n/U^(n+1)` for the concrete complete-DVF
principal-unit filtration. -/
def principalUnitSuccQuot (n : ℕ) : Type u :=
  higherPrincipalUnitGroup F n ⧸
    (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)

/--
Equips the target with its canonical `CommGroup` structure, namely `CommGroup
(higherPrincipalUnitGroup.principalUnitSuccQuot F n)`.
-/
instance principalUnitSuccQuotCommGroup (n : ℕ) :
    CommGroup (higherPrincipalUnitGroup.principalUnitSuccQuot F n) := by
  change CommGroup
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  infer_instance

/-- Explicit access to the concrete quotient used to implement
`principalUnitSuccQuot`. -/
def principalUnitSuccQuotConcreteEquiv (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) ≃*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact MulEquiv.refl _

/-- The quotient map `U^n → U^n/U^(n+1)`. -/
def principalUnitSuccQuotMk (n : ℕ) :
    higherPrincipalUnitGroup F n →*
      higherPrincipalUnitGroup.principalUnitSuccQuot F n := by
  change higherPrincipalUnitGroup F n →*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact QuotientGroup.mk' ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = QuotientGroup.mk u`.
-/
@[simp] theorem principalUnitSuccQuotConcreteEquiv_mk (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      QuotientGroup.mk u :=
  rfl

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n)`.
-/
theorem principalUnitSuccQuotMk_surjective (n : ℕ) :
    Function.Surjective (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n) :=
  QuotientGroup.mk'_surjective ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/-- Eliminate an adjacent principal-unit quotient through its canonical
representatives. -/
protected theorem principalUnitSuccQuot.inductionOn
    (n : ℕ)
    {motive : higherPrincipalUnitGroup.principalUnitSuccQuot F n → Prop}
    (q : higherPrincipalUnitGroup.principalUnitSuccQuot F n)
    (h : ∀ u : higherPrincipalUnitGroup F n,
      motive (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u)) :
    motive q := by
  change motive
    (show
      higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n) from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u

/-- Descend a homomorphism from `U^n` that kills `U^(n+1)`. -/
def principalUnitSuccQuotLift
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n →* H := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) →* H
  exact QuotientGroup.lift
    ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n)) f h

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u`.
-/
@[simp] theorem principalUnitSuccQuotLift_mk
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u :=
  rfl

/-- The type in `Finite (higherPrincipalUnitGroup.principalUnitSuccQuot F n)` is finite. -/
noncomputable instance principalUnitSuccQuotFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  Finite.of_equiv
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
    (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).symm.toEquiv

/-- The concrete complete-DVF adjacent quotient agrees with the generic
graded-piece wrapper through explicit public equivalences. -/
def principalUnitSuccQuotEquivGradedPiece (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPiece n :=
  (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).trans
    ((AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n).trans
      (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n (n + 1))).symm

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk n u`.
-/
@[simp] theorem principalUnitSuccQuotEquivGradedPiece_mk
    (n : ℕ) (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk
        n u :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1` by the equivalent
condition `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
-/
theorem principalUnitSuccQuotMk_eq_one_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1 ↔
      u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) = 1 ↔ _)
  exact QuotientGroup.eq_one_iff u

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v` by the equivalent condition `u / v ∈
(higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
-/
theorem principalUnitSuccQuotMk_eq_iff_div_mem (n : ℕ)
    (u v : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
        higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v ↔
      u / v ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) =
      (v : higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) ↔ _)
  exact QuotientGroup.eq_iff_div_mem

/--
Characterizes `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`
by the equivalent condition `((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal
^ (n + 1)`.
-/
theorem mem_succ_subgroupOf_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) ↔
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
        F.maximalIdeal ^ (n + 1) := by
  rw [Subgroup.mem_subgroupOf, higherPrincipalUnitGroup.mem_iff]

/-- If `a ∈ m^n` with `n ≥ 1`, then `1 + a` is a unit of the valuation ring. -/
theorem isUnit_one_add_of_mem_maximalIdeal_pow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : IsUnit (1 + a) := by
  have ha1 : a ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa using hle ha
  have hnon : (-a) ∈ nonunits F.valuationSubring := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact F.maximalIdeal.neg_mem ha1
  have hunit : IsUnit (1 - (-a)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon
  simpa [sub_neg_eq_add] using hunit

/-- The unit `1 + a` attached to an element `a ∈ m^n`, for `n ≥ 1`. -/
noncomputable def principalUnitOneAddOfMemPow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : F.valuationSubringˣ :=
  (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha).unit

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
F.valuationSubringˣ) : F.valuationSubring) = 1 + a`.
-/
@[simp] theorem principalUnitOneAddOfMemPow_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
        F.valuationSubringˣ) : F.valuationSubring) =
      1 + a :=
  IsUnit.unit_spec
    (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha)

/-- The unit `1 + a`, viewed as an element of `U^n`. -/
noncomputable def principalUnitOneAddOfMemPowSubgroup {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    higherPrincipalUnitGroup F n :=
  ⟨higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha, by
    rw [higherPrincipalUnitGroup.mem_iff]
    simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]
  ⟩

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha
: higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha`.
-/
@[simp] theorem principalUnitOneAddOfMemPowSubgroup_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha :
        higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :=
  rfl

/-- The concrete map `m^n → U^n/U^(n+1)` sending `a` to the class of
`1 + a`. -/
noncomputable def principalUnitSuccQuotOfIdealPow (n : ℕ) (hn : 1 ≤ n) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  fun a =>
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
      (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)

/--
The defining evaluation formula for `principalUnitSuccQuotOfIdealPow` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
(higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)`.
-/
@[simp] theorem principalUnitSuccQuotOfIdealPow_apply (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
        (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2) :=
  rfl

/-- Elements of `m^(n+1)` map to the trivial class in `U^n/U^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (ha : (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
    higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]

/-- The map `a ↦ [1 + a]` is insensitive to changing `a` modulo `m^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (hab : ((a : F.valuationSubring) - (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) - (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          (b : F.valuationSubring) b.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2]
    have hbval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) = 1 + (b : F.valuationSubring) :=
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2
    have hbinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2)⁻¹ = 1 := by
      simp
    calc
      (1 + (a : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ - 1 =
          (1 + (a : F.valuationSubring)) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbinv]
      _ = ((a : F.valuationSubring) - (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _ hab

/-- The class `[1+a]` is trivial exactly when `a ∈ m^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 ↔
      (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1) := by
  constructor
  · intro h
    have hmem :=
      (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).1 h
    rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff] at hmem
    simpa [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val] using hmem
  · intro ha
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
      F n hn a ha

/-- Products of two elements of `m^n`, for `n ≥ 1`, lie in `m^(n+1)`. -/
theorem maximalIdealPow_mul_mem_succ {n : ℕ} (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1) := by
  have hmul :
      ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
        F.maximalIdeal ^ (n + n) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : F.maximalIdeal ^ (n + n) ≤ F.maximalIdeal ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul

/-- The map `a ↦ [1+a]` is additive after passing to the successive
principal-unit quotient. -/
theorem principalUnitSuccQuotOfIdealPow_add
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn (a + b) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    ← map_mul]
  symm
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) * (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
            F.valuationSubring) (a + b).2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2]
    have habval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) =
          1 + (a : F.valuationSubring) + (b : F.valuationSubring) := by
      rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring) (a + b).2]
      change 1 + ((a : F.valuationSubring) + (b : F.valuationSubring)) =
        1 + (a : F.valuationSubring) + (b : F.valuationSubring)
      ring
    have habinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2)⁻¹ = 1 := by
      simp
    calc
      ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ - 1 =
          ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habinv]
      _ = ((a : F.valuationSubring) * (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _
    (higherPrincipalUnitGroup.maximalIdealPow_mul_mem_succ F hn a b)

/-- The descent of `a ↦ [1+a]` to `m^n/m^(n+1)`. -/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  maximalIdealPowSuccQuotLift
    F.toDVF n
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn)
    (fun a b hsub =>
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
        F n hn a b (by simpa using hsub))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
F n hn (maximalIdealPowSuccQuotMk F.toDVF n a) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n a) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a :=
  rfl

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` has the zero-value formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero
    (n : ℕ) (hn : 1 ≤ n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1 := by
  rw [← map_zero
    (maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (maximalIdealPowSuccQuotMk F.toDVF n
        (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))) = 1
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    F n hn (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) (by simp)

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` satisfies the addition formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add
    (n : ℕ) (hn : 1 ≤ n)
    (x y : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y := by
  refine
    MaximalIdealPowSuccQuot.inductionOn₂
      (motive := fun x' y' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn (x' + y') =
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn x' *
            higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn y')
      F.toDVF n x y ?_
  intro a b
  let qa :
      MaximalIdealPowSuccQuot F.toDVF n :=
    maximalIdealPowSuccQuotMk F.toDVF n a
  let qb :
      MaximalIdealPowSuccQuot F.toDVF n :=
    maximalIdealPowSuccQuotMk F.toDVF n b
  have hleft :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (qa + qb) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) := by
    have hadd : qa + qb =
        maximalIdealPowSuccQuotMk
          F.toDVF n (a + b) := by
      exact (map_add
        (maximalIdealPowSuccQuotMk
          F.toDVF n) a b).symm
    exact congrArg
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) hadd
  have hrep :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qa *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qb := by
    dsimp [qa, qb]
    change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n (a + b)) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n a) *
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n b)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_add F n hn a b
  exact hleft.trans hrep

/-- Additive form of the descended map `m^n/m^(n+1) → U^n/U^(n+1)`. -/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n →+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) where
  toFun x := Additive.ofMul
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x)
  map_zero' := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0) = 0
    simp
  map_add' x y := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y)) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add]

/--
The defining evaluation formula for `principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
Additive.ofMul (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
x)`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x =
1` by the equivalent condition `x = 0`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x = 1 ↔
      x = 0 := by
  refine
    MaximalIdealPowSuccQuot.inductionOn
      (motive := fun x' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn x' = 1 ↔ x' = 0)
      F.toDVF n x ?_
  intro a
  rw [← map_zero
    (maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (maximalIdealPowSuccQuotMk F.toDVF n a) = 1 ↔
    (maximalIdealPowSuccQuotMk F.toDVF n a :
      MaximalIdealPowSuccQuot F.toDVF n) = 0
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    maximalIdealPowSuccQuotMk_eq_zero_iff]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_iff F n hn a

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) := by
  intro x
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotMk_surjective F n x with ⟨u, rfl⟩
  let a0 : F.valuationSubring := ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  have ha0 : a0 ∈ F.maximalIdeal ^ n := by
    dsimp [a0]
    exact (higherPrincipalUnitGroup.mem_iff F n (u : F.valuationSubringˣ)).1 u.2
  let a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) := ⟨a0, ha0⟩
  refine ⟨maximalIdealPowSuccQuotMk F.toDVF n a, ?_⟩
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply]
  congr 1
  dsimp [a]
  apply Subtype.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val]
  apply Units.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val]
  dsimp [a0]
  ring

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro y
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
      F n hn (Additive.toMul y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) = y
  rw [hx]
  rfl

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro x y hxy
  have hzero :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn
        (x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_self
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
        F n hn y)
  have hmul :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (x - y) = 1 := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (x - y)) =
      Additive.ofMul (1 : higherPrincipalUnitGroup.principalUnitSuccQuot F n) at hzero
    exact Additive.ofMul.injective hzero
  have hxmy : x - y = 0 :=
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
      F n hn (x - y)).1 hmul
  exact sub_eq_zero.mp hxmy

/-- The additive isomorphism `m^n/m^(n+1) ≃ U^n/U^(n+1)` induced by
`a ↦ 1+a`. -/
noncomputable def maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n ≃+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  AddEquiv.ofBijective
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)
    ⟨higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
        F n hn,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
        F n hn⟩

/--
The defining evaluation formula for `maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot` is
`higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot F n hn x =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x`.
-/
@[simp] theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
        F n hn x =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x :=
  rfl

/-- The unit-quotient coordinate theorem for a complete DVF with a specified
uniformizer: `U^n/U^(n+1)` is additively the residue field. -/
noncomputable def principalUnitSuccQuotAddEquivResidueOfUniformizer
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) ≃+ F.residueField :=
  (higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
      F n hn).symm.trans
    (residueAddEquivMaximalIdealPowSuccQuotOfUniformizer F.toDVF hpi n).symm

/-- Cardinality form of the associated-graded identification
`U^n/U^(n+1) ≃ k` for `n ≥ 1`. -/
theorem card_principalUnitSuccQuot_eq_residue_of_uniformizer
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (higherPrincipalUnitGroup.principalUnitSuccQuot F n) =
      Nat.card F.residueField := by
  calc
    Nat.card (higherPrincipalUnitGroup.principalUnitSuccQuot F n) =
        Nat.card (Additive
          (higherPrincipalUnitGroup.principalUnitSuccQuot F n)) :=
      Nat.card_congr
        (Additive.ofMul :
          higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃
            Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n))
    _ = Nat.card F.residueField :=
      Nat.card_congr
        (higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
          F hpi n hn).toEquiv

/-- Cardinality of the finite principal-unit range `U^1/U^n`, obtained by
iterating the adjacent quotients `U^i/U^(i+1) ≃ k`. -/
theorem card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
    [Finite F.residueField]
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (higherPrincipalUnitGroup F 1 ⧸
        (higherPrincipalUnitGroup F n).subgroupOf
          (higherPrincipalUnitGroup F 1)) =
      Nat.card F.residueField ^ (n - 1) := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  let hfinite (i j : ℕ) : Finite (U.principalUnitSubquotient i j) := by
    exact
      higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue
        F i j
  have hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal := by
    intro i
    change (higherPrincipalUnitGroup F i).Normal
    infer_instance
  have hn_eq : 1 + (n - 1) = n :=
    by
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos hn)
  calc
    Nat.card (U.principalUnitSubquotient 1 n) =
        Nat.card (U.principalUnitSubquotient 1 (1 + (n - 1))) := by
          rw [hn_eq]
    _ =
        ∏ i ∈ Finset.range (n - 1),
          Nat.card (U.principalUnitGradedPiece (1 + i)) := by
          rw [U.card_principalUnitSubquotient_eq_prod_gradedPiece hN 1 (n - 1)]
    _ =
        ∏ _i ∈ Finset.range (n - 1), Nat.card F.residueField := by
          apply Finset.prod_congr rfl
          intro i _hi
          have hpos : 1 ≤ 1 + i := by omega
          calc
            Nat.card (U.principalUnitGradedPiece (1 + i)) =
                Nat.card
                  (higherPrincipalUnitGroup.principalUnitSuccQuot F (1 + i)) :=
              Nat.card_congr
                (higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece
                  F (1 + i)).symm.toEquiv
            _ = Nat.card F.residueField :=
              higherPrincipalUnitGroup.card_principalUnitSuccQuot_eq_residue_of_uniformizer
                F hpi (1 + i) hpos
    _ = Nat.card F.residueField ^ (n - 1) := by
          simp

/-- Under the inverse of `U^n/U^(n+1) ≃ k`, the residue of `r` is represented
by the principal unit `1 + r * pi^n`. -/
@[simp] theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    (higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn).symm (F.residueMap r) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer]
  rw [AddEquiv.symm_trans_apply]
  simp only [AddEquiv.symm_symm]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfUniformizer_residue]
  rw [higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply]
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply]
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
        (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]

/-- The equivalence `U^n/U^(n+1) ≃ k` sends the coordinate class
`[1 + r * pi^n]` to the residue of `r`. -/
theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_coord
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn
        (Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
      F.residueMap r := by
  let E := higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
    F hpi n hn
  have hcoord :
      E.symm (F.residueMap r) =
        Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
    simp [E]
  change E
      (Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    F.residueMap r
  rw [← hcoord]
  exact E.apply_symm_apply (F.residueMap r)

/-- The induced action on `O^*/U^n` preserves the image of `U^m` in that
quotient.  This is the finite-stage principal-unit class compatibility needed
before applying prime-to-`p` quotient invisibility. -/
theorem unitsModPrincipalUnitEquivOfPreserves_mem_principalUnitClassInQuotient_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    {m n : ℕ} (hmn : m ≤ n)
    (q : F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) :
    unitsModPrincipalUnitEquivOfPreserves F e hmem n q ∈
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
          m n ↔
      q ∈
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
          m n := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (higherPrincipalUnitGroup F n) q
  have hleft' :
      QuotientGroup.mk' (higherPrincipalUnitGroup F n)
          (valuationSubringUnitEquivOfPreserves F e hmem u) ∈
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
          m n ↔
      valuationSubringUnitEquivOfPreserves F e hmem u ∈
        higherPrincipalUnitGroup F m := by
    exact
      AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) hmn
          (valuationSubringUnitEquivOfPreserves F e hmem u)
  have hright' :
      QuotientGroup.mk' (higherPrincipalUnitGroup F n) u ∈
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
          m n ↔
      u ∈ higherPrincipalUnitGroup F m := by
    exact
      AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) hmn u
  rw [unitsModPrincipalUnitEquivOfPreserves_mk]
  rw [hleft', hright']
  exact valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff F e hmem m u

/-- If the induced residue-field automorphism is pointwise trivial, then the
displacement of the induced action on `O^*/U^n` lies in the image of
`U^1/U^n`. -/
theorem unitsModPrincipalUnitEquivOfPreserves_div_mem_principalUnitClass_one
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (hres :
      ∀ x : F.residueField,
        valuationSubringResidueFieldEquivOfPreserves F e hmem x = x)
    (n : ℕ)
    (q : F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) :
    unitsModPrincipalUnitEquivOfPreserves F e hmem n q / q ∈
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
        1 n := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (higherPrincipalUnitGroup F n) q
  have hdisp :
      valuationSubringUnitEquivOfPreserves F e hmem u / u ∈
        higherPrincipalUnitGroup F 1 :=
    unitEquiv_div_mem_principalUnit_one_of_residueFieldEquiv_fixed
      F e hmem hres u
  have hclass' :
      QuotientGroup.mk' (higherPrincipalUnitGroup F n)
          (valuationSubringUnitEquivOfPreserves F e hmem u / u) ∈
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
          1 n := by
    apply
      AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient_mk_mem
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F)
    exact hdisp
  rw [unitsModPrincipalUnitEquivOfPreserves_mk]
  simpa only [map_div] using hclass'

/-- Therefore every adjacent concrete principal-unit class
`U^i/U^(i+1)` is finite when the residue field is finite. -/
theorem finite_principalUnitSubgroupClassInQuotient_of_finite_residue
    [Finite F.residueField] (i : ℕ) :
    Finite
      ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
        i (i + 1)) := by
  have :
      Finite
        (F.valuationSubringˣ ⧸
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroup
            (i + 1)) := by
    change Finite
      (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F (i + 1))
    exact
      higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
        F (i + 1)
  exact Finite.of_injective Subtype.val Subtype.val_injective

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
