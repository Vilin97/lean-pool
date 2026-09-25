/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaIndexing
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitInverseLimitSurjectivity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.EqualCharacteristicLaurent
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.NumberTheory.Padics.ProperSpace
/-!
# The convergent Iwasawa product for principal units

This module assembles the finite-level Iwasawa factors into a compatible
family in the principal-unit inverse limit, proves continuity and bijectivity,
and packages the resulting topological additive equivalence.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  higherPrincipalUnitGroup →
    classFieldHigherPrincipalUnitGroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitOneAddOfMemPowSubgroup →
    classFieldPrincipalUnitOneAddOfMemPowSubgroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitOneAddOfMemPowSubgroup_val →
    classFieldPrincipalUnitOneAddOfMemPowSubgroup_val

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitOneAddOfMemPow_val →
    classFieldPrincipalUnitOneAddOfMemPow_val

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitPadic_smul_mem_higher →
    classFieldPrincipalUnitPadic_smul_mem_higher

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuot →
    classFieldPrincipalUnitSuccQuot

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotAddEquivResidueOfUniformizer →
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue →
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotMk →
    classFieldPrincipalUnitSuccQuotMk

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  principalUnitSuccQuotOfIdealPow_apply →
    principalUnitSuccQuotOfIdealPow_apply

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueMap_residueTeichmullerLift →
    classFieldResidueMap_residueTeichmullerLift

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueTeichmullerLift →
    classFieldResidueTeichmullerLift

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  toPrincipalUnitFiltration →
    toPrincipalUnitFiltration


/-!
# Finite-level Iwasawa generators for principal units

This file develops an explicit topological product decomposition of principal units.  In equal
  characteristic, choose
a residue-field basis `omega_i` over `F_p`.  For a positive degree `n`, the
prime-to-`p` Iwasawa map is

`g_n(a_i) = product_i (1 + [omega_i] pi^n) ^ a_i`.

The powers by p-adic integers are the canonical powers constructed from the
finite principal-unit quotients in `PrincipalUnitPadicAction`.  This module
constructs each finite-level factor `g_n`, proves its filtration properties,
and establishes its algebraic injectivity.  The convergent global product is
assembled in `IwasawaPrincipalUnits`.
-/

noncomputable section

open scoped BigOperators

universe u v

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

noncomputable instance residueFieldZModAlgebra
    (F : LocalField.{u, v} K) :
    Algebra (ZMod F.residueCharacteristic) F.residueField :=
  ZMod.algebra F.residueField F.residueCharacteristic

/-- The number of vectors in a basis of the residue field over its prime
field.  This is the `f` in `q = p^f` in the field-unit structure theorem. -/
abbrev iwasawaResidueRank (F : LocalField.{u, v} K) : ℕ :=
  Module.finrank (ZMod F.residueCharacteristic) F.residueField

/-- A fixed `F_p`-basis of the residue field, denoted `omega_1,...,omega_f`
in this construction. -/
noncomputable def iwasawaResidueBasis (F : LocalField.{u, v} K) :
    Module.Basis (Fin (iwasawaResidueRank F))
      (ZMod F.residueCharacteristic) F.residueField :=
  Module.finBasis (ZMod F.residueCharacteristic) F.residueField

/-- The rank chosen above is the exponent in the finite-field cardinality
identity `q = p^f`. -/
theorem residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank
    (F : LocalField.{u, v} K) :
    Nat.card F.residueField =
      F.residueCharacteristic ^ iwasawaResidueRank F := by
  simpa [iwasawaResidueRank, Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank
      (K := ZMod F.residueCharacteristic) (V := F.residueField))

/-- The element `[omega_i] pi^n` of the `n`-th maximal-ideal power. -/
noncomputable def iwasawaSeedIdeal
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (i : Fin (iwasawaResidueRank F)) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
  DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n
    (classFieldResidueTeichmullerLift F.toCompleteDVF
      (iwasawaResidueBasis F i))

/--
Establishes the identity `(iwasawaSeedIdeal F hpi n i : F.valuationSubring) =
CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF (iwasawaResidueBasis F
i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeedIdeal_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (i : Fin (iwasawaResidueRank F)) :
    (iwasawaSeedIdeal F hpi n i : F.valuationSubring) =
      classFieldResidueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n :=
  rfl

/-- The generator `1 + [omega_i] pi^n`, first as an element of `U^n`. -/
noncomputable def iwasawaSeedAtLevel
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n :=
  classFieldPrincipalUnitOneAddOfMemPowSubgroup
    F.toCompleteDVF hn (iwasawaSeedIdeal F hpi n i)
      (iwasawaSeedIdeal F hpi n i).property

/--
Establishes the identity `(((iwasawaSeedAtLevel F hpi n hn i :
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n) : F.valuationSubringˣ) :
F.valuationSubring) = 1 + CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift
F.toCompleteDVF (iwasawaResidueBasis F i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeedAtLevel_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    (((iwasawaSeedAtLevel F hpi n hn i :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) n) : F.valuationSubringˣ) :
      F.valuationSubring) =
      1 + classFieldResidueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n := by
  rw [iwasawaSeedAtLevel,
    classFieldPrincipalUnitOneAddOfMemPowSubgroup_val,
    classFieldPrincipalUnitOneAddOfMemPow_val]
  rfl

/-- The same generator regarded as a first principal unit, so that the
canonical p-adic scalar action is available. -/
noncomputable def iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1 :=
  ⟨(iwasawaSeedAtLevel F hpi n hn i : F.valuationSubringˣ),
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone
      F.toCompleteDVF hn
      (iwasawaSeedAtLevel F hpi n hn i).property⟩

/--
Establishes the identity `(((iwasawaSeed F hpi n hn i : ((CompleteDVF.higherPrincipalUnitGroup
F.toCompleteDVF)) 1) : F.valuationSubringˣ) : F.valuationSubring) = 1 +
CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF (iwasawaResidueBasis F
i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeed_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    (((iwasawaSeed F hpi n hn i :
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1) :
        F.valuationSubringˣ) : F.valuationSubring) =
      1 + classFieldResidueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n := by
  exact iwasawaSeedAtLevel_val F hpi n hn i

/-- The leading coefficient of `1 + [omega_i] pi^n` in
`U^n/U^(n+1)` is exactly the basis vector `omega_i`. -/
@[simp] theorem principalUnitSuccQuotAddEquivResidue_iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer
        F.toCompleteDVF hpi n hn
      (Additive.ofMul
        (classFieldPrincipalUnitSuccQuotMk F.toCompleteDVF n
          (iwasawaSeedAtLevel F hpi n hn i))) =
      iwasawaResidueBasis F i := by
  let r : F.valuationSubring :=
    classFieldResidueTeichmullerLift F.toCompleteDVF
      (iwasawaResidueBasis F i)
  let e :=
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi n hn
  have hs :=
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
      F.toCompleteDVF hpi n hn r
  have he := congrArg e hs
  simpa [e, r, iwasawaSeedAtLevel, iwasawaSeedIdeal,
    principalUnitSuccQuotOfIdealPow_apply,
    classFieldResidueMap_residueTeichmullerLift] using he.symm

/-- The basis-coordinate form of the leading-layer calculation.  This is the
linear algebra behind formula (1) at `s = 0`: the chosen `f` seed units give
every class in `U^n/U^(n+1)`, uniquely modulo `p`. -/
noncomputable def iwasawaLeadingLayerAddEquiv
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (iwasawaResidueRank F) → ZMod F.residueCharacteristic) ≃+
      Additive
        (classFieldPrincipalUnitSuccQuot
        F.toCompleteDVF n) :=
  (iwasawaResidueBasis F).equivFun.symm.toAddEquiv.trans
    (classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi n hn).symm

/--
Establishes the identity `iwasawaLeadingLayerAddEquiv F hpi n hn (Pi.single i 1) = Additive.ofMul
(CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotMk F.toCompleteDVF n
(iwasawaSeedAtLevel F hpi n hn i))`.
-/
@[simp] theorem iwasawaLeadingLayerAddEquiv_single
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    iwasawaLeadingLayerAddEquiv F hpi n hn (Pi.single i 1) =
      Additive.ofMul
        (classFieldPrincipalUnitSuccQuotMk F.toCompleteDVF n
          (iwasawaSeedAtLevel F hpi n hn i)) := by
  let e :=
    classFieldPrincipalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi n hn
  let z := Additive.ofMul
    (classFieldPrincipalUnitSuccQuotMk F.toCompleteDVF n
      (iwasawaSeedAtLevel F hpi n hn i))
  calc
    iwasawaLeadingLayerAddEquiv F hpi n hn (Pi.single i 1) =
        e.symm ((iwasawaResidueBasis F).equivFun.symm (Pi.single i 1)) := rfl
    _ = e.symm (iwasawaResidueBasis F i) := by
      rw [Basis.equivFun_symm_single]
    _ = e.symm (e z) := by
      exact congrArg e.symm
        (principalUnitSuccQuotAddEquivResidue_iwasawaSeed
          F hpi n hn i).symm
    _ = z := e.symm_apply_apply z

/--
Characterizes `iwasawaLeadingLayerAddEquiv F hpi n hn a = 0` by the equivalent condition `a = 0`.
-/
theorem iwasawaLeadingLayerAddEquiv_eq_zero_iff
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ZMod F.residueCharacteristic) :
    iwasawaLeadingLayerAddEquiv F hpi n hn a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    apply (iwasawaLeadingLayerAddEquiv F hpi n hn).injective
    simpa using ha
  · rintro rfl
    exact map_zero _

/-! ## Reduction of p-adic exponents on one graded layer -/

/-- A p-adic integer differs from the ordinary representative of its
reduction modulo `p` by a multiple of `p`. -/
theorem exists_padicInt_sub_toZMod_val_eq_residueCharacteristic_mul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic]) :
    ∃ b : ℤ_[F.residueCharacteristic],
      a - ((PadicInt.toZMod a).val : ℤ_[F.residueCharacteristic]) =
        (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) * b := by
  have h := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p] at h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [ZMod.cast_eq_val] at hb
  simpa [mul_comm] using hb

/-- A p-adic power of a first principal unit, remembered at a specified
higher-unit level. -/
noncomputable def principalUnitPadicSmulAtLevel
    (F : LocalField.{u, v} K) (r : ℕ) (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) r) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) r :=
  ⟨(Additive.toMul (a • Additive.ofMul x) :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1),
    principalUnitPadic_smul_mem_higher F hr a x hx⟩

/-- On `U^r/U^(r+1)`, a p-adic exponent may be replaced by its first
ordinary approximation.  This is the precise version of choosing the
integers `b_i ≡ a_i (mod p)` in the coefficient calculation. -/
theorem principalUnitSuccQuotMk_padicSmulAtLevel_eq_toZMod_val
    (F : LocalField.{u, v} K) (r : ℕ) (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) r) :
    principalUnitSuccQuotMk F.toCompleteDVF r
        (principalUnitPadicSmulAtLevel F r hr a x hx) =
      principalUnitSuccQuotMk F.toCompleteDVF r
        (principalUnitPadicSmulAtLevel F r hr
          ((PadicInt.toZMod a).val : ℤ_[F.residueCharacteristic]) x hx) := by
  apply (principalUnitSuccQuotMk_eq_iff_div_mem F.toCompleteDVF r _ _).2
  change
    ((principalUnitPadicSmulAtLevel F r hr a x hx /
        principalUnitPadicSmulAtLevel F r hr
          ((PadicInt.toZMod a).val : ℤ_[F.residueCharacteristic]) x hx :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) r) : F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (r + 1)
  obtain ⟨b, hb⟩ :=
    exists_padicInt_sub_toZMod_val_eq_residueCharacteristic_mul F a
  have hdeep :=
    principalUnitPadic_residueCharacteristic_mul_smul_mem_succ
      F hr b x hx
  rw [← hb] at hdeep
  change
    (((Additive.toMul (a • Additive.ofMul x) :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) /
        (Additive.toMul
          (((PadicInt.toZMod a).val : ℤ_[F.residueCharacteristic]) •
            Additive.ofMul x) :
              ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) 1) :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (r + 1)
  have hsub := sub_smul a
    ((PadicInt.toZMod a).val : ℤ_[F.residueCharacteristic])
    (Additive.ofMul x)
  rw [hsub] at hdeep
  exact hdeep

/-- The leading coefficient map `U^r -> k`, written additively. -/
noncomputable def principalUnitLeadingCoefficientAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (r : ℕ) (hr : 1 ≤ r) :
    Additive (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) r) →+ F.residueField :=
  (principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi r hr).toAddMonoidHom.comp
    { toFun := fun x => Additive.ofMul
        (principalUnitSuccQuotMk F.toCompleteDVF r (Additive.toMul x))
      map_zero' := by
        change Additive.ofMul
            (principalUnitSuccQuotMk F.toCompleteDVF r 1) = 0
        simp
      map_add' := by
        intro x y
        change Additive.ofMul
            (principalUnitSuccQuotMk F.toCompleteDVF r
              (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul
              (principalUnitSuccQuotMk F.toCompleteDVF r (Additive.toMul x)) +
            Additive.ofMul
              (principalUnitSuccQuotMk F.toCompleteDVF r (Additive.toMul y))
        rw [map_mul]
        rfl }

/--
Characterizes `principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul x) = 0` by the
equivalent condition `((x : F.valuationSubringˣ) : F.valuationSubringˣ) ∈
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) (n + 1)`.
-/
theorem principalUnitLeadingCoefficientAddHom_eq_zero_iff_mem_succ
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (x :
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul x) = 0 ↔
      ((x : F.valuationSubringˣ) : F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (n + 1) := by
  let e := principalUnitSuccQuotAddEquivResidueOfUniformizer
    F.toCompleteDVF hpi n hn
  let q := principalUnitSuccQuotMk F.toCompleteDVF n x
  change e (Additive.ofMul q) = 0 ↔ _
  constructor
  · intro h
    have hqadd : Additive.ofMul q = 0 := by
      apply e.injective
      simpa using h
    have hq : q = 1 := Additive.ofMul.injective hqadd
    exact (principalUnitSuccQuotMk_eq_one_iff F.toCompleteDVF n x).1 hq
  · intro hx
    have hq : q = 1 :=
      (principalUnitSuccQuotMk_eq_one_iff F.toCompleteDVF n x).2 hx
    simp [hq]

/-- Reduction modulo `p` detects divisibility by `p` in `Z_p`. -/
theorem padicInt_toZMod_eq_zero_iff_exists_residueCharacteristic_mul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic]) :
    PadicInt.toZMod a = 0 ↔
      ∃ b : ℤ_[F.residueCharacteristic],
        a = (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) * b := by
  constructor
  · intro ha
    have hker : a ∈ RingHom.ker
        (PadicInt.toZMod : ℤ_[F.residueCharacteristic] →+*
          ZMod F.residueCharacteristic) := ha
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hker
    obtain ⟨b, hb⟩ := hker
    exact ⟨b, by simpa [mul_comm] using hb⟩
  · rintro ⟨b, rfl⟩
    simp

/-- A vector lies in `p Z_p^f` exactly when all of its residue coordinates
vanish. -/
theorem exists_residueCharacteristic_smul_eq_iff_toZMod_eq_zero
    (F : LocalField.{u, v} K)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    (∃ b : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) • b) ↔
      ∀ i, PadicInt.toZMod (a i) = 0 := by
  constructor
  · rintro ⟨b, rfl⟩ i
    simp
  · intro h
    choose b hb using fun i =>
      (padicInt_toZMod_eq_zero_iff_exists_residueCharacteristic_mul
        F (a i)).1 (h i)
    refine ⟨b, funext fun i => ?_⟩
    change a i = (F.residueCharacteristic :
      ℤ_[F.residueCharacteristic]) * b i
    exact hb i

/-- The residue-basis combination is zero exactly when all reduced
coordinates are zero. -/
theorem iwasawa_residue_combination_eq_zero_iff
    (F : LocalField.{u, v} K)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    (∑ i, PadicInt.toZMod (a i) • iwasawaResidueBasis F i) = 0 ↔
      ∀ i, PadicInt.toZMod (a i) = 0 := by
  rw [← (iwasawaResidueBasis F).equivFun_symm_apply]
  constructor
  · intro h i
    have hf : (fun j => PadicInt.toZMod (a j)) = 0 := by
      apply (iwasawaResidueBasis F).equivFun.symm.injective
      simpa using h
    exact congrFun hf i
  · intro h
    have hf : (fun i => PadicInt.toZMod (a i)) = 0 :=
      funext fun i => h i
    rw [hf, map_zero]

/-- The principal unit `1 + r*pi^n`, used as a canonical representative of
a prescribed leading residue coefficient. -/
noncomputable def principalUnitOneAddUniformizerPowAtLevel
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n :=
  principalUnitOneAddOfMemPowSubgroup F.toCompleteDVF hn
    (DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)
    (DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r).property

/--
Establishes the identity `(((principalUnitOneAddUniformizerPowAtLevel F hpi n hn r :
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n) : F.valuationSubringˣ) :
F.valuationSubring) = 1 + r * pi ^ n`.
-/
@[simp] theorem principalUnitOneAddUniformizerPowAtLevel_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    (((principalUnitOneAddUniformizerPowAtLevel F hpi n hn r :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) n) : F.valuationSubringˣ) :
      F.valuationSubring) = 1 + r * pi ^ n := by
  rw [principalUnitOneAddUniformizerPowAtLevel,
    principalUnitOneAddOfMemPowSubgroup_val,
    principalUnitOneAddOfMemPow_val]
  rfl

/-- The leading coefficient of `1 + r*pi^n` is the residue of `r`. -/
@[simp] theorem principalUnitLeadingCoefficientAddHom_oneAddUniformizerPow
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    principalUnitLeadingCoefficientAddHom F hpi n hn
        (Additive.ofMul
          (principalUnitOneAddUniformizerPowAtLevel F hpi n hn r)) =
      F.residueMap r := by
  let e := principalUnitSuccQuotAddEquivResidueOfUniformizer
    F.toCompleteDVF hpi n hn
  have hs :=
    principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
      F.toCompleteDVF hpi n hn r
  change e
      (Additive.ofMul
        (principalUnitSuccQuotOfIdealPow F.toCompleteDVF n hn
          (DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    F.residueMap r
  rw [← hs, e.apply_symm_apply]

/-- In equal characteristic, a `p^s`-th power sends `U^n` into
`U^(n*p^s)`.  This is the depth multiplication used in both (1) and (2). -/
theorem pow_residueCharacteristic_pow_mem_higher_mul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {n : ℕ} (s : ℕ)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    (((x ^ (F.residueCharacteristic ^ s) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) :
      F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF))
          (n * F.residueCharacteristic ^ s) := by
  rw [LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff]
  have ha :
      (((x : F.valuationSubringˣ) : F.valuationSubring) - 1) ∈
        F.maximalIdeal ^ n :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
      F.toCompleteDVF n
      (x : F.valuationSubringˣ)).1 hx
  have hapow :
      ((((x : F.valuationSubringˣ) : F.valuationSubring) - 1) ^
          (F.residueCharacteristic ^ s)) ∈
        F.maximalIdeal ^ (n * F.residueCharacteristic ^ s) := by
    have h := Ideal.pow_mem_pow ha (F.residueCharacteristic ^ s)
    simpa [pow_mul] using h
  have heq :
      ((((x ^ (F.residueCharacteristic ^ s) :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
        (((x : F.valuationSubringˣ) : F.valuationSubring) - 1) ^
          (F.residueCharacteristic ^ s) := by
    let z : F.valuationSubring :=
      ((x : F.valuationSubringˣ) : F.valuationSubring) - 1
    have hxz : ((x : F.valuationSubringˣ) : F.valuationSubring) = 1 + z := by
      dsimp [z]
      ring
    change
      ((x : F.valuationSubringˣ) : F.valuationSubring) ^
          (F.residueCharacteristic ^ s) - 1 = z ^
            (F.residueCharacteristic ^ s)
    rw [hxz, add_pow_char_pow]
    simp
  rw [heq]
  exact hapow

/-- Inclusion `U^n -> U^1`. -/
def higherUnitToFirst
    (F : LocalField.{u, v} K) (n : ℕ) (hn : 1 ≤ n)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1 :=
  ⟨(x : F.valuationSubringˣ),
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone
      F.toCompleteDVF hn x.property⟩

/-- Proves the bound `1 ≤ n * F.residueCharacteristic ^ s`. -/
theorem one_le_mul_residueCharacteristic_pow
    (F : LocalField.{u, v} K) {n : ℕ} (hn : 1 ≤ n) (s : ℕ) :
    1 ≤ n * F.residueCharacteristic ^ s := by
  have hp : 0 < F.residueCharacteristic ^ s :=
    pow_pos F.residueCharacteristic_prime.pos s
  exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hn) hp

/-- A `p^s`-th power from `U^n`, with its exact equal-characteristic depth
`n*p^s` built into the codomain. -/
noncomputable def principalUnitFrobeniusAtLevel
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) (n * F.residueCharacteristic ^ s) :=
  ⟨((higherUnitToFirst F n hn x) ^ (F.residueCharacteristic ^ s) :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1),
    pow_residueCharacteristic_pow_mem_higher_mul F s
      (higherUnitToFirst F n hn x) x.property⟩

/-- Frobenius on a canonical representative:
`(1+r*pi^n)^(p^s) = 1+r^(p^s) pi^(n*p^s)`. -/
theorem principalUnitFrobeniusAtLevel_oneAddUniformizerPow
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ) (r : F.valuationSubring) :
    let m := n * F.residueCharacteristic ^ s
    let hm : 1 ≤ m := one_le_mul_residueCharacteristic_pow F hn s
    principalUnitFrobeniusAtLevel F n hn s
        (principalUnitOneAddUniformizerPowAtLevel F hpi n hn r) =
      principalUnitOneAddUniformizerPowAtLevel F hpi m hm
        (r ^ (F.residueCharacteristic ^ s)) := by
  dsimp only
  apply Subtype.ext
  apply Units.ext
  change
    (1 + r * pi ^ n) ^ (F.residueCharacteristic ^ s) =
      1 + r ^ (F.residueCharacteristic ^ s) *
        pi ^ (n * F.residueCharacteristic ^ s)
  rw [add_pow_char_pow, mul_pow, pow_mul]
  simp

/-- Frobenius raises the leading residue coefficient to its `p^s`-th
power. -/
theorem principalUnitLeadingCoefficientAddHom_frobenius
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    let m := n * F.residueCharacteristic ^ s
    let hm : 1 ≤ m := one_le_mul_residueCharacteristic_pow F hn s
    principalUnitLeadingCoefficientAddHom F hpi m hm
        (Additive.ofMul (principalUnitFrobeniusAtLevel F n hn s x)) =
      (principalUnitLeadingCoefficientAddHom F hpi n hn
        (Additive.ofMul x)) ^ (F.residueCharacteristic ^ s) := by
  dsimp only
  let q : ℕ := F.residueCharacteristic ^ s
  let m : ℕ := n * q
  have hq : 1 ≤ q := by
    exact pow_pos F.residueCharacteristic_prime.pos s
  have hm : 1 ≤ m := by
    exact one_le_mul_residueCharacteristic_pow F hn s
  let lead : F.residueField :=
    principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul x)
  let r : F.valuationSubring :=
    residueTeichmullerLift F.toCompleteDVF lead
  let y : ((classFieldHigherPrincipalUnitGroup
    F.toCompleteDVF)) n :=
    principalUnitOneAddUniformizerPowAtLevel F hpi n hn r
  have hyLead :
      principalUnitLeadingCoefficientAddHom F hpi n hn
          (Additive.ofMul y) = lead := by
    rw [principalUnitLeadingCoefficientAddHom_oneAddUniformizerPow]
    exact residueMap_residueTeichmullerLift F.toCompleteDVF lead
  have hxyQuot :
      principalUnitSuccQuotMk F.toCompleteDVF n x =
        principalUnitSuccQuotMk F.toCompleteDVF n y := by
    apply (principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi n hn).injective
    change
      principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul x) =
        principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul y)
    exact hyLead.symm
  have hxyDeep :
      (((x / y : ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) n) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (n + 1) :=
    (principalUnitSuccQuotMk_eq_iff_div_mem F.toCompleteDVF n x y).1 hxyQuot
  let d : ((classFieldHigherPrincipalUnitGroup
    F.toCompleteDVF)) (n + 1) :=
    ⟨((x / y : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) : F.valuationSubringˣ), hxyDeep⟩
  have hdPow := pow_residueCharacteristic_pow_mem_higher_mul F s
    (higherUnitToFirst F (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) d)
    d.property
  have hlevel : m + 1 ≤ (n + 1) * q := by
    calc
      m + 1 ≤ m + q := Nat.add_le_add_left hq m
      _ = (n + 1) * q := by simp [m, Nat.add_mul]
  have hdPow' :
      ((((higherUnitToFirst F (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) d) ^ q :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone
      F.toCompleteDVF hlevel (by
      simpa [q] using hdPow)
  have hpowQuot :
      principalUnitSuccQuotMk F.toCompleteDVF m
          (principalUnitFrobeniusAtLevel F n hn s x) =
        principalUnitSuccQuotMk F.toCompleteDVF m
          (principalUnitFrobeniusAtLevel F n hn s y) := by
    apply (principalUnitSuccQuotMk_eq_iff_div_mem F.toCompleteDVF m _ _).2
    change
      (((principalUnitFrobeniusAtLevel F n hn s x /
          principalUnitFrobeniusAtLevel F n hn s y :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) m) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)
    simpa [principalUnitFrobeniusAtLevel, higherUnitToFirst, d, q, m,
      div_pow] using hdPow'
  have hleadEq :
      principalUnitLeadingCoefficientAddHom F hpi m hm
          (Additive.ofMul (principalUnitFrobeniusAtLevel F n hn s x)) =
        principalUnitLeadingCoefficientAddHom F hpi m hm
          (Additive.ofMul (principalUnitFrobeniusAtLevel F n hn s y)) := by
    exact congrArg
      (fun z : principalUnitSuccQuot F.toCompleteDVF m =>
        (principalUnitSuccQuotAddEquivResidueOfUniformizer
          F.toCompleteDVF hpi m hm) (Additive.ofMul z)) hpowQuot
  rw [hleadEq, principalUnitFrobeniusAtLevel_oneAddUniformizerPow,
    principalUnitLeadingCoefficientAddHom_oneAddUniformizerPow, map_pow]
  change F.residueMap r ^ q = lead ^ q
  rw [show F.residueMap r = lead from
    residueMap_residueTeichmullerLift F.toCompleteDVF lead]

/--
Establishes the identity `principalUnitLeadingCoefficientAddHom F hpi r hr (Additive.ofMul
(iwasawaSeedAtLevel F hpi r hr i)) = iwasawaResidueBasis F i`.
-/
@[simp] theorem principalUnitLeadingCoefficientAddHom_iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (r : ℕ) (hr : 1 ≤ r) (i : Fin (iwasawaResidueRank F)) :
    principalUnitLeadingCoefficientAddHom F hpi r hr
        (Additive.ofMul (iwasawaSeedAtLevel F hpi r hr i)) =
      iwasawaResidueBasis F i :=
  principalUnitSuccQuotAddEquivResidue_iwasawaSeed F hpi r hr i

/-- The leading coefficient of one p-adically powered seed only depends on
the exponent modulo `p`. -/
theorem principalUnitLeadingCoefficientAddHom_padicSmul_iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (r : ℕ) (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (i : Fin (iwasawaResidueRank F)) :
    principalUnitLeadingCoefficientAddHom F hpi r hr
        (Additive.ofMul
          (principalUnitPadicSmulAtLevel F r hr a
            (iwasawaSeed F hpi r hr i)
            (iwasawaSeedAtLevel F hpi r hr i).property)) =
      PadicInt.toZMod a •
        iwasawaResidueBasis F i := by
  let k : ℕ := (PadicInt.toZMod a).val
  let xa := principalUnitPadicSmulAtLevel F r hr a
    (iwasawaSeed F hpi r hr i)
    (iwasawaSeedAtLevel F hpi r hr i).property
  let xk := principalUnitPadicSmulAtLevel F r hr
    (k : ℤ_[F.residueCharacteristic])
    (iwasawaSeed F hpi r hr i)
    (iwasawaSeedAtLevel F hpi r hr i).property
  have hquot :
      principalUnitSuccQuotMk F.toCompleteDVF r xa =
        principalUnitSuccQuotMk F.toCompleteDVF r xk := by
    simpa [xa, xk, k] using
      principalUnitSuccQuotMk_padicSmulAtLevel_eq_toZMod_val
        F r hr a (iwasawaSeed F hpi r hr i)
          (iwasawaSeedAtLevel F hpi r hr i).property
  have hxk : xk = (iwasawaSeedAtLevel F hpi r hr i) ^ k := by
    apply Subtype.ext
    exact congrArg
      (fun z : ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1 => (z : F.valuationSubringˣ))
      (principalUnitPadic_nsmul_eq_pow
        F k (iwasawaSeed F hpi r hr i))
  change
    (principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi r hr)
        (Additive.ofMul (principalUnitSuccQuotMk F.toCompleteDVF r xa)) = _
  rw [hquot, hxk, map_pow]
  change
    (principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi r hr)
        (k • Additive.ofMul
          (principalUnitSuccQuotMk F.toCompleteDVF r
            (iwasawaSeedAtLevel F hpi r hr i))) = _
  rw [map_nsmul,
    principalUnitSuccQuotAddEquivResidue_iwasawaSeed]
  calc
    k • iwasawaResidueBasis F i =
        (k : ZMod F.residueCharacteristic) • iwasawaResidueBasis F i :=
      (Nat.cast_smul_eq_nsmul
        (R := ZMod F.residueCharacteristic) k
          (iwasawaResidueBasis F i)).symm
    _ = PadicInt.toZMod a • iwasawaResidueBasis F i := by
      rw [show (k : ZMod F.residueCharacteristic) = PadicInt.toZMod a by
        exact ZMod.natCast_zmod_val (PadicInt.toZMod a)]

/-- The Iwasawa homomorphism `g_n : Z_p^f -> U^1`.  Its range is shown
below to lie in `U^n`.  In additive notation the Iwasawa product is a
finite sum of p-adic scalar multiples of the seed units. -/
noncomputable def iwasawaGn
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) →ₗ[ℤ_[F.residueCharacteristic]]
      Additive (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1) :=
  Fintype.linearCombination ℤ_[F.residueCharacteristic]
    (fun i => Additive.ofMul (iwasawaSeed F hpi n hn i))

/--
The defining evaluation formula for `iwasawaGn` is `iwasawaGn F hpi n hn a = ∑ i, a i •
Additive.ofMul (iwasawaSeed F hpi n hn i)`.
-/
@[simp] theorem iwasawaGn_apply
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    iwasawaGn F hpi n hn a =
      ∑ i, a i • Additive.ofMul (iwasawaSeed F hpi n hn i) :=
  Fintype.linearCombination_apply
    ℤ_[F.residueCharacteristic]
    (fun i => Additive.ofMul (iwasawaSeed F hpi n hn i)) a

/-- Every value of `g_n` belongs to `U^n`, as asserted by its codomain in
the canonical construction. -/
theorem iwasawaGn_mem_higher
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    ((Additive.toMul (iwasawaGn F hpi n hn a) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) n := by
  classical
  rw [iwasawaGn_apply]
  induction (Finset.univ : Finset (Fin (iwasawaResidueRank F)))
      using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      change
        ((Additive.toMul
            (a i • Additive.ofMul (iwasawaSeed F hpi n hn i)) :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) *
          ((Additive.toMul
            (∑ j ∈ s, a j • Additive.ofMul (iwasawaSeed F hpi n hn j)) :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) n
      apply (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) n).mul_mem
      · exact
          classFieldPrincipalUnitPadic_smul_mem_higher
          F hn (a i) (iwasawaSeed F hpi n hn i)
          (iwasawaSeedAtLevel F hpi n hn i).property
      · exact ih

/-- `g_n(a)`, now with its proved membership in `U^n` built into the type. -/
noncomputable def iwasawaGnAtLevel
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n :=
  ⟨(Additive.toMul (iwasawaGn F hpi n hn a) :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1),
    iwasawaGn_mem_higher F hpi n hn a⟩

/--
Establishes the identity `Additive.ofMul (iwasawaGnAtLevel F hpi n hn a) = ∑ i, Additive.ofMul
(principalUnitPadicSmulAtLevel F n hn (a i) (iwasawaSeed F hpi n hn i) (iwasawaSeedAtLevel F hpi n
hn i).property)`.
-/
theorem additive_iwasawaGnAtLevel_eq_sum
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    Additive.ofMul (iwasawaGnAtLevel F hpi n hn a) =
      ∑ i, Additive.ofMul
        (principalUnitPadicSmulAtLevel F n hn (a i)
          (iwasawaSeed F hpi n hn i)
          (iwasawaSeedAtLevel F hpi n hn i).property) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change
    ((Additive.toMul (iwasawaGn F hpi n hn a) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) =
      ((Additive.toMul
          (∑ i, Additive.ofMul
            (principalUnitPadicSmulAtLevel F n hn (a i)
              (iwasawaSeed F hpi n hn i)
              (iwasawaSeedAtLevel F hpi n hn i).property)) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) n) : F.valuationSubringˣ)
  rw [iwasawaGn_apply]
  have hsum : ∀ s : Finset (Fin (iwasawaResidueRank F)),
      ((Additive.toMul
          (∑ i ∈ s, a i • Additive.ofMul (iwasawaSeed F hpi n hn i)) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) =
      ((Additive.toMul
          (∑ i ∈ s, Additive.ofMul
            (principalUnitPadicSmulAtLevel F n hn (a i)
              (iwasawaSeed F hpi n hn i)
              (iwasawaSeedAtLevel F hpi n hn i).property)) :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) n) : F.valuationSubringˣ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change
          ((Additive.toMul
              (a i • Additive.ofMul (iwasawaSeed F hpi n hn i)) :
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) 1) : F.valuationSubringˣ) * _ =
          ((principalUnitPadicSmulAtLevel F n hn (a i)
              (iwasawaSeed F hpi n hn i)
              (iwasawaSeedAtLevel F hpi n hn i).property :
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) n) : F.valuationSubringˣ) * _
        have hfirst :
            ((Additive.toMul
                (a i • Additive.ofMul (iwasawaSeed F hpi n hn i)) :
              ((classFieldHigherPrincipalUnitGroup
                F.toCompleteDVF)) 1) : F.valuationSubringˣ) =
              ((principalUnitPadicSmulAtLevel F n hn (a i)
                  (iwasawaSeed F hpi n hn i)
                  (iwasawaSeedAtLevel F hpi n hn i).property :
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF)) n) : F.valuationSubringˣ) := rfl
        rw [hfirst, ih]
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum (Finset.univ : Finset (Fin (iwasawaResidueRank F)))

/-- The exact leading coefficient of `g_n(a)`: it is the residue-basis
linear combination of the reductions of the p-adic coordinates. -/
theorem principalUnitLeadingCoefficientAddHom_iwasawaGnAtLevel
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    principalUnitLeadingCoefficientAddHom F hpi n hn
        (Additive.ofMul (iwasawaGnAtLevel F hpi n hn a)) =
      ∑ i,
        PadicInt.toZMod (a i) •
          iwasawaResidueBasis F i := by
  rw [additive_iwasawaGnAtLevel_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact principalUnitLeadingCoefficientAddHom_padicSmul_iwasawaSeed
    F hpi n hn (a i) i

/-- Multiplying every coordinate by the ordinary scalar `p^s` turns `g_n`
into the ordinary `p^s`-th power of `g_n(a)`. -/
theorem iwasawaGn_residueCharacteristic_pow_smul_eq_pow
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    Additive.toMul
        (iwasawaGn F hpi n hn
          ((F.residueCharacteristic ^ s :
              ℤ_[F.residueCharacteristic]) • a)) =
      (Additive.toMul (iwasawaGn F hpi n hn a)) ^
        (F.residueCharacteristic ^ s) := by
  have hlinear := (iwasawaGn F hpi n hn).map_smul'
    (F.residueCharacteristic ^ s : ℤ_[F.residueCharacteristic]) a
  change Additive.toMul
      ((iwasawaGn F hpi n hn).toFun
        ((F.residueCharacteristic ^ s : ℤ_[F.residueCharacteristic]) • a)) = _
  rw [hlinear]
  change Additive.toMul
      ((F.residueCharacteristic ^ s : ℤ_[F.residueCharacteristic]) •
        Additive.ofMul (Additive.toMul (iwasawaGn F hpi n hn a))) = _
  simpa only [Nat.cast_pow] using
    principalUnitPadic_nsmul_eq_pow F
      (F.residueCharacteristic ^ s)
      (Additive.toMul (iwasawaGn F hpi n hn a))

/-- The canonical `g_n(p^s a)`, with the exact depth `m = n*p^s` built into
its type. -/
noncomputable def iwasawaGnScaledAtLevel
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    ((classFieldHigherPrincipalUnitGroup F.toCompleteDVF))
      (n * F.residueCharacteristic ^ s) :=
  ⟨(Additive.toMul
      (iwasawaGn F hpi n hn
        ((F.residueCharacteristic ^ s :
            ℤ_[F.residueCharacteristic]) • a)) :
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1), by
    rw [iwasawaGn_residueCharacteristic_pow_smul_eq_pow]
    exact pow_residueCharacteristic_pow_mem_higher_mul F s
      (Additive.toMul (iwasawaGn F hpi n hn a))
      (iwasawaGn_mem_higher F hpi n hn a)⟩

/--
Establishes the identity `iwasawaGnScaledAtLevel F hpi n hn s a = principalUnitFrobeniusAtLevel F
n hn s (iwasawaGnAtLevel F hpi n hn a)`.
-/
theorem iwasawaGnScaledAtLevel_eq_frobenius
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    iwasawaGnScaledAtLevel F hpi n hn s a =
      principalUnitFrobeniusAtLevel F n hn s
        (iwasawaGnAtLevel F hpi n hn a) := by
  apply Subtype.ext
  exact congrArg
    (fun z : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1 => (z : F.valuationSubringˣ))
    (iwasawaGn_residueCharacteristic_pow_smul_eq_pow F hpi n hn s a)

/-- The coefficient congruence:
the leading coefficient of `g_n(p^s a)` is the `p^s`-th power of the
residue-basis combination represented by `a`. -/
theorem principalUnitLeadingCoefficientAddHom_iwasawaGnScaledAtLevel
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    let m := n * F.residueCharacteristic ^ s
    let hm : 1 ≤ m := one_le_mul_residueCharacteristic_pow F hn s
    principalUnitLeadingCoefficientAddHom F hpi m hm
        (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a)) =
      (∑ i, PadicInt.toZMod (a i) • iwasawaResidueBasis F i) ^
        (F.residueCharacteristic ^ s) := by
  dsimp only
  rw [iwasawaGnScaledAtLevel_eq_frobenius,
    principalUnitLeadingCoefficientAddHom_frobenius,
    principalUnitLeadingCoefficientAddHom_iwasawaGnAtLevel]

/-- The first coefficient congruence, for `m = n*p^s`:
`U^m = g_n(p^s Z_p^f) U^(m+1)`. -/
theorem exists_iwasawaGnScaled_mul_mem_succ
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF))
      (n * F.residueCharacteristic ^ s)) :
    ∃ a : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      (((x / iwasawaGnScaledAtLevel F hpi n hn s a :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF))
            (n * F.residueCharacteristic ^ s)) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF))
            (n * F.residueCharacteristic ^ s + 1) := by
  let m : ℕ := n * F.residueCharacteristic ^ s
  have hm : 1 ≤ m := one_le_mul_residueCharacteristic_pow F hn s
  let lead : F.residueField :=
    principalUnitLeadingCoefficientAddHom F hpi m hm (Additive.ofMul x)
  let beta : F.residueField :=
    ((frobeniusEquiv F.residueField F.residueCharacteristic).symm^[s]) lead
  have hbeta : beta ^ (F.residueCharacteristic ^ s) = lead := by
    exact iterate_frobeniusEquiv_symm_pow_p_pow
      F.residueField F.residueCharacteristic lead s
  let c : Fin (iwasawaResidueRank F) → ZMod F.residueCharacteristic :=
    (iwasawaResidueBasis F).equivFun beta
  let a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic] :=
    fun i => ((c i).val : ℤ_[F.residueCharacteristic])
  refine ⟨a, ?_⟩
  have hcoord :
      (∑ i, PadicInt.toZMod (a i) • iwasawaResidueBasis F i) = beta := by
    have hcmod : ∀ i, PadicInt.toZMod (a i) = c i := by
      intro i
      change PadicInt.toZMod
          ((c i).val : ℤ_[F.residueCharacteristic]) = c i
      rw [map_natCast]
      exact ZMod.natCast_zmod_val (c i)
    simp_rw [hcmod]
    simp [c, beta]
  have hscaledLead :
      principalUnitLeadingCoefficientAddHom F hpi m hm
          (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a)) =
        lead := by
    rw [principalUnitLeadingCoefficientAddHom_iwasawaGnScaledAtLevel,
      hcoord, hbeta]
  change (x / iwasawaGnScaledAtLevel F hpi n hn s a) ∈
    (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) (m + 1)).subgroupOf
      (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) m)
  apply (principalUnitSuccQuotMk_eq_one_iff F.toCompleteDVF m _).1
  rw [map_div]
  have hquot :
      principalUnitSuccQuotMk F.toCompleteDVF m x =
        principalUnitSuccQuotMk F.toCompleteDVF m
          (iwasawaGnScaledAtLevel F hpi n hn s a) := by
    apply (principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi m hm).injective
    change
      principalUnitLeadingCoefficientAddHom F hpi m hm (Additive.ofMul x) =
        principalUnitLeadingCoefficientAddHom F hpi m hm
          (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a))
    exact hscaledLead.symm
  rw [hquot]
  exact div_self'
    (principalUnitSuccQuotMk F.toCompleteDVF m
      (iwasawaGnScaledAtLevel F hpi n hn s a))

/-- Positive form of formula (2): `g_n(p^s a)` drops into `U^(m+1)`
exactly when every coordinate of `a` is divisible by `p`. -/
theorem iwasawaGnScaled_mem_succ_iff_exists_residueCharacteristic_smul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    (((iwasawaGnScaledAtLevel F hpi n hn s a :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF))
          (n * F.residueCharacteristic ^ s)) : F.valuationSubringˣ) :
      F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF))
          (n * F.residueCharacteristic ^ s + 1) ↔
      ∃ b : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic],
        a = (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) • b := by
  let m : ℕ := n * F.residueCharacteristic ^ s
  have hm : 1 ≤ m := one_le_mul_residueCharacteristic_pow F hn s
  let omega : F.residueField :=
    ∑ i, PadicInt.toZMod (a i) • iwasawaResidueBasis F i
  have hlead :
      principalUnitLeadingCoefficientAddHom F hpi m hm
          (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a)) =
        omega ^ (F.residueCharacteristic ^ s) := by
    simpa [m, omega] using
      principalUnitLeadingCoefficientAddHom_iwasawaGnScaledAtLevel
        F hpi n hn s a
  have hq0 : F.residueCharacteristic ^ s ≠ 0 :=
    pow_ne_zero s F.residueCharacteristic_prime.ne_zero
  constructor
  · intro hz
    have hzero :
        principalUnitLeadingCoefficientAddHom F hpi m hm
            (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a)) = 0 :=
      (principalUnitLeadingCoefficientAddHom_eq_zero_iff_mem_succ
        F hpi m hm (iwasawaGnScaledAtLevel F hpi n hn s a)).2 hz
    rw [hlead] at hzero
    have homega : omega = 0 := (pow_eq_zero_iff hq0).1 hzero
    have hall : ∀ i, PadicInt.toZMod (a i) = 0 :=
      (iwasawa_residue_combination_eq_zero_iff F a).1 (by
        simpa [omega] using homega)
    exact (exists_residueCharacteristic_smul_eq_iff_toZMod_eq_zero F a).2 hall
  · intro ha
    have hall : ∀ i, PadicInt.toZMod (a i) = 0 :=
      (exists_residueCharacteristic_smul_eq_iff_toZMod_eq_zero F a).1 ha
    have homega : omega = 0 := by
      apply (iwasawa_residue_combination_eq_zero_iff F a).2
      exact hall
    have hzero :
        principalUnitLeadingCoefficientAddHom F hpi m hm
            (Additive.ofMul (iwasawaGnScaledAtLevel F hpi n hn s a)) = 0 := by
      rw [hlead, homega]
      exact zero_pow hq0
    exact (principalUnitLeadingCoefficientAddHom_eq_zero_iff_mem_succ
      F hpi m hm (iwasawaGnScaledAtLevel F hpi n hn s a)).1 hzero

/-- The second coefficient congruence. -/
theorem iwasawa_formula_two
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    (¬ ∃ b : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic],
        a = (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) • b) ↔
      ¬ (((iwasawaGnScaledAtLevel F hpi n hn s a :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF))
            (n * F.residueCharacteristic ^ s)) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF))
            (n * F.residueCharacteristic ^ s + 1) := by
  exact (not_congr
    (iwasawaGnScaled_mem_succ_iff_exists_residueCharacteristic_smul
      F hpi n hn s a)).symm

/-! ## Algebraic injectivity of each Iwasawa factor -/

/-- A p-adic integer divisible by every power of `p` is zero. -/
theorem padicInt_eq_zero_of_forall_exists_eq_pow_mul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic])
    (h : ∀ r : ℕ, ∃ b : ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) ^ r * b) :
    a = 0 := by
  by_contra ha
  have hnorm : 0 < ‖a‖ := (norm_pos_iff.mpr ha)
  obtain ⟨r, hr⟩ := PadicInt.exists_pow_neg_lt
    (p := F.residueCharacteristic) hnorm
  obtain ⟨b, hb⟩ := h r
  have hle : ‖a‖ ≤
      (F.residueCharacteristic : ℝ) ^ (-(r : ℤ)) := by
    calc
      ‖a‖ = ‖(F.residueCharacteristic :
          ℤ_[F.residueCharacteristic]) ^ r‖ * ‖b‖ := by
            rw [hb, norm_mul]
      _ ≤ ‖(F.residueCharacteristic :
          ℤ_[F.residueCharacteristic]) ^ r‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (PadicInt.norm_le_one b)
              (norm_nonneg _)
      _ = (F.residueCharacteristic : ℝ) ^ (-(r : ℤ)) := by
            rw [PadicInt.norm_p_pow, mul_one]
  exact (not_lt_of_ge hle) hr

/-- Equal-characteristic first principal units have no `p`-torsion. -/
theorem principalUnit_residueCharacteristic_smul_eq_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (x : Additive
      (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1))
    (hx : (F.residueCharacteristic :
        ℤ_[F.residueCharacteristic]) • x = 0) :
    x = 0 := by
  let u : ((classFieldHigherPrincipalUnitGroup
    F.toCompleteDVF)) 1 := Additive.toMul x
  have hpowAdd : Additive.ofMul (u ^ F.residueCharacteristic) = 0 := by
    change (F.residueCharacteristic :
      ℤ_[F.residueCharacteristic]) • Additive.ofMul u = 0 at hx
    rw [principalUnitPadic_natCast_smul] at hx
    exact hx
  have hpow : u ^ F.residueCharacteristic = 1 :=
    Additive.ofMul.injective hpowAdd
  let z : K := (((u : F.valuationSubringˣ) : F.valuationSubring) : K)
  have hpowK : z ^ F.residueCharacteristic = 1 := by
    simpa [z] using congrArg
      (fun w : ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1 =>
        ((((w : F.valuationSubringˣ) : F.valuationSubring) : K))) hpow
  have hdiffpow : (z - 1) ^ F.residueCharacteristic = 0 := by
    have hf := sub_pow_char_pow z 1 1
    simpa [hpowK] using hf
  have hdiff : z - 1 = 0 :=
    (pow_eq_zero_iff F.residueCharacteristic_prime.ne_zero).1 hdiffpow
  have hz : z = 1 := sub_eq_zero.mp hdiff
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simpa [u, z] using hz

/-- If `g_n(a)=1`, then all coordinates of `a` are divisible by every
power of `p`. -/
theorem forall_exists_iwasawaGn_eq_pow_smul_of_eq_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    (ha : iwasawaGn F hpi n hn a = 0) :
    ∀ r : ℕ, ∃ b : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ r :
        ℤ_[F.residueCharacteristic]) • b := by
  have H : ∀ r : ℕ, ∃ b : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ r :
          ℤ_[F.residueCharacteristic]) • b ∧
        iwasawaGn F hpi n hn b = 0 := by
    intro r
    induction r with
    | zero =>
        exact ⟨a, by simp [ha]⟩
    | succ r ih =>
        obtain ⟨b, hab, hb⟩ := ih
        have hscaledMem :
            (((iwasawaGnScaledAtLevel F hpi n hn 0 b :
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF))
                  (n * F.residueCharacteristic ^ 0)) : F.valuationSubringˣ) :
              F.valuationSubringˣ) ∈
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF))
                  (n * F.residueCharacteristic ^ 0 + 1) := by
          simp [iwasawaGnScaledAtLevel, hb]
        obtain ⟨c, hbc⟩ :=
          (iwasawaGnScaled_mem_succ_iff_exists_residueCharacteristic_smul
            F hpi n hn 0 b).1 hscaledMem
        have hgcScalar :
            (F.residueCharacteristic : ℤ_[F.residueCharacteristic]) •
              iwasawaGn F hpi n hn c = 0 := by
          rw [← map_smul, ← hbc, hb]
        have hgc : iwasawaGn F hpi n hn c = 0 :=
          principalUnit_residueCharacteristic_smul_eq_zero F
            (iwasawaGn F hpi n hn c) hgcScalar
        refine ⟨c, ?_, hgc⟩
        calc
          a = (F.residueCharacteristic ^ r :
              ℤ_[F.residueCharacteristic]) • b := hab
          _ = (F.residueCharacteristic ^ r :
              ℤ_[F.residueCharacteristic]) •
                ((F.residueCharacteristic :
                    ℤ_[F.residueCharacteristic]) • c) := by rw [hbc]
          _ = (F.residueCharacteristic ^ (r + 1) :
              ℤ_[F.residueCharacteristic]) • c := by
                rw [← mul_smul, pow_succ]
  intro r
  obtain ⟨b, hb, _⟩ := H r
  exact ⟨b, hb⟩

/-- Every individual Iwasawa map `g_n` is injective in equal
characteristic. -/
theorem iwasawaGn_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (iwasawaGn F hpi n hn) := by
  intro a b hab
  have hzero : iwasawaGn F hpi n hn (a - b) = 0 := by
    rw [map_sub, hab]
    exact sub_self _
  have habzero : a - b = 0 := by
    apply funext
    intro i
    apply padicInt_eq_zero_of_forall_exists_eq_pow_mul F ((a - b) i)
    intro r
    obtain ⟨c, hc⟩ :=
      forall_exists_iwasawaGn_eq_pow_smul_of_eq_zero
        F hpi n hn (a - b) hzero r
    refine ⟨c i, ?_⟩
    have hi := congrFun hc i
    simpa [Pi.smul_apply] using hi
  exact sub_eq_zero.mp habzero

/-- A vector of p-adic coefficients is primitive when it is not divisible
coordinatewise by the residue characteristic. -/
def IwasawaPrimitive
    (F : LocalField.{u, v} K)
    (a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic]) : Prop :=
  ¬ ∃ b : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
    a = (F.residueCharacteristic :
      ℤ_[F.residueCharacteristic]) • b

/-- Every nonzero p-adic coefficient block has a unique-depth form
`p^s b` with `b` primitive.  This is the coefficient valuation used in
Iwasawa's minimal-depth argument. -/
theorem exists_pow_smul_iwasawaPrimitive_of_ne_zero
    (F : LocalField.{u, v} K)
    (a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic]) (ha : a ≠ 0) :
    ∃ s : ℕ, ∃ b : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ s :
          ℤ_[F.residueCharacteristic]) • b ∧
        IwasawaPrimitive F b := by
  classical
  have hex : ∃ r : ℕ, ¬ ∃ c : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ r :
        ℤ_[F.residueCharacteristic]) • c := by
    by_contra h
    push Not at h
    apply ha
    funext i
    apply padicInt_eq_zero_of_forall_exists_eq_pow_mul F (a i)
    intro r
    obtain ⟨c, hc⟩ := h r
    refine ⟨c i, ?_⟩
    simpa [Pi.smul_apply] using congrFun hc i
  let r : ℕ := Nat.find hex
  have hrSpec : ¬ ∃ c : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ r :
        ℤ_[F.residueCharacteristic]) • c := by
    simpa [r] using Nat.find_spec hex
  have hr0 : r ≠ 0 := by
    intro hr
    apply hrSpec
    refine ⟨a, ?_⟩
    simp [hr]
  let s : ℕ := r - 1
  have hsr : s + 1 = r := by
    omega
  have hslt : s < r := by omega
  have hsNot : ¬ (¬ ∃ c : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
      a = (F.residueCharacteristic ^ s :
        ℤ_[F.residueCharacteristic]) • c) := by
    exact Nat.find_min hex (by simpa [r] using hslt)
  obtain ⟨b, hab⟩ := not_not.mp hsNot
  refine ⟨s, b, hab, ?_⟩
  intro hdiv
  obtain ⟨c, hbc⟩ := hdiv
  apply hrSpec
  refine ⟨c, ?_⟩
  calc
    a = (F.residueCharacteristic ^ s :
          ℤ_[F.residueCharacteristic]) • b := hab
    _ = (F.residueCharacteristic ^ s :
          ℤ_[F.residueCharacteristic]) •
        ((F.residueCharacteristic :
          ℤ_[F.residueCharacteristic]) • c) := by rw [hbc]
    _ = (F.residueCharacteristic ^ (s + 1) :
          ℤ_[F.residueCharacteristic]) • c := by
      rw [← mul_smul, pow_succ]
    _ = (F.residueCharacteristic ^ r :
          ℤ_[F.residueCharacteristic]) • c := by rw [hsr]

/-- The first coefficient congruence in the base case `s = 0`:
`U^n = g_n(Z_p^f) U^(n+1)`. -/
theorem exists_iwasawaGn_mul_mem_succ
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n) :
    ∃ a : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      (((x / iwasawaGnAtLevel F hpi n hn a :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) n) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (n + 1) := by
  let lead : F.residueField :=
    principalUnitLeadingCoefficientAddHom F hpi n hn (Additive.ofMul x)
  let c : Fin (iwasawaResidueRank F) → ZMod F.residueCharacteristic :=
    (iwasawaResidueBasis F).equivFun lead
  let a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic] :=
    fun i => ((c i).val : ℤ_[F.residueCharacteristic])
  refine ⟨a, ?_⟩
  have hlead :
      principalUnitLeadingCoefficientAddHom F hpi n hn
          (Additive.ofMul (iwasawaGnAtLevel F hpi n hn a)) = lead := by
    rw [principalUnitLeadingCoefficientAddHom_iwasawaGnAtLevel]
    change
      (∑ i, PadicInt.toZMod ((c i).val :
          ℤ_[F.residueCharacteristic]) • iwasawaResidueBasis F i) = lead
    have hcmod : ∀ i,
        PadicInt.toZMod ((c i).val : ℤ_[F.residueCharacteristic]) = c i := by
      intro i
      rw [map_natCast]
      exact ZMod.natCast_zmod_val (c i)
    simp_rw [hcmod]
    simp [c, lead]
  change (x / iwasawaGnAtLevel F hpi n hn a) ∈
    (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) (n + 1)).subgroupOf
      (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) n)
  apply (principalUnitSuccQuotMk_eq_one_iff F.toCompleteDVF n _).1
  rw [map_div]
  have hquot :
      principalUnitSuccQuotMk F.toCompleteDVF n x =
        principalUnitSuccQuotMk F.toCompleteDVF n
          (iwasawaGnAtLevel F hpi n hn a) := by
    apply
      (principalUnitSuccQuotAddEquivResidueOfUniformizer
        F.toCompleteDVF hpi n hn).injective
    change
      principalUnitLeadingCoefficientAddHom F hpi n hn
          (Additive.ofMul x) =
        principalUnitLeadingCoefficientAddHom F hpi n hn
          (Additive.ofMul (iwasawaGnAtLevel F hpi n hn a))
    exact hlead.symm
  rw [hquot]
  exact div_self'
    (principalUnitSuccQuotMk F.toCompleteDVF n
      (iwasawaGnAtLevel F hpi n hn a))

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

noncomputable section

open scoped BigOperators

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

/-! ## The convergent product, constructed through finite quotients -/

/-- The product of one copy of `Z_p^f` for every positive prime-to-`p`
degree. -/
abbrev iwasawaDomain (F : LocalField.{u, v} K) :=
  IwasawaIndex F.residueCharacteristic (iwasawaResidueRank F) →
    ℤ_[F.residueCharacteristic]

/-- The p-adic coefficient vector belonging to one prime-to-`p` degree. -/
def iwasawaBlock
    (F : LocalField.{u, v} K) (a : iwasawaDomain F)
    (d : IwasawaDegree F.residueCharacteristic) :
    Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic] :=
  fun i => a (d, i)

/-- A depth occurring in a nonzero Iwasawa coefficient family. -/
def IwasawaDepthWitness
    (F : LocalField.{u, v} K) (a : iwasawaDomain F) (m : ℕ) : Prop :=
  ∃ d : IwasawaDegree F.residueCharacteristic,
    ∃ s : ℕ, ∃ b : Fin (iwasawaResidueRank F) →
        ℤ_[F.residueCharacteristic],
      iwasawaBlock F a d =
          (F.residueCharacteristic ^ s :
            ℤ_[F.residueCharacteristic]) • b ∧
        IwasawaPrimitive F b ∧
        m = d.1 * F.residueCharacteristic ^ s

/-- A nonzero coefficient family has a least depth `n*p^s`. -/
theorem exists_minimal_iwasawaDepthWitness_of_ne_zero
    (F : LocalField.{u, v} K) (a : iwasawaDomain F) (ha : a ≠ 0) :
    ∃ m : ℕ, ∃ d : IwasawaDegree F.residueCharacteristic,
      ∃ s : ℕ, ∃ b : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic],
        iwasawaBlock F a d =
            (F.residueCharacteristic ^ s :
              ℤ_[F.residueCharacteristic]) • b ∧
          IwasawaPrimitive F b ∧
          m = d.1 * F.residueCharacteristic ^ s ∧
          ∀ e : IwasawaDegree F.residueCharacteristic,
            ∀ t : ℕ, ∀ c : Fin (iwasawaResidueRank F) →
                ℤ_[F.residueCharacteristic],
              iwasawaBlock F a e =
                  (F.residueCharacteristic ^ t :
                    ℤ_[F.residueCharacteristic]) • c →
                IwasawaPrimitive F c →
                m ≤ e.1 * F.residueCharacteristic ^ t := by
  classical
  have hnonzeroBlock : ∃ d : IwasawaDegree F.residueCharacteristic,
      iwasawaBlock F a d ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext j
    exact congrFun (h j.1) j.2
  have hex : ∃ m : ℕ, IwasawaDepthWitness F a m := by
    obtain ⟨d, hd⟩ := hnonzeroBlock
    obtain ⟨s, b, hab, hb⟩ :=
      exists_pow_smul_iwasawaPrimitive_of_ne_zero F
        (iwasawaBlock F a d) hd
    exact ⟨d.1 * F.residueCharacteristic ^ s,
      d, s, b, hab, hb, rfl⟩
  let m : ℕ := Nat.find hex
  obtain ⟨d, s, b, hab, hb, hm⟩ := Nat.find_spec hex
  refine ⟨m, d, s, b, hab, hb, hm, ?_⟩
  intro e t c hec hc
  apply Nat.find_min' hex
  exact ⟨e, t, c, hec, hc, rfl⟩

/-- A vector supported in one prime-to-`p` degree. -/
noncomputable def iwasawaSingleBlock
    (F : LocalField.{u, v} K)
    (d : IwasawaDegree F.residueCharacteristic)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    iwasawaDomain F := by
  classical
  exact fun j => if j.1 = d then b j.2 else 0

/-- Establishes the identity `iwasawaSingleBlock F d b (d, i) = b i`. -/
@[simp] theorem iwasawaSingleBlock_apply_same
    (F : LocalField.{u, v} K)
    (d : IwasawaDegree F.residueCharacteristic)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    (i : Fin (iwasawaResidueRank F)) :
    iwasawaSingleBlock F d b (d, i) = b i := by
  classical
  simp [iwasawaSingleBlock]

/-- Establishes the identity `iwasawaSingleBlock F d b (e, i) = 0`. -/
@[simp] theorem iwasawaSingleBlock_apply_ne
    (F : LocalField.{u, v} K)
    {d e : IwasawaDegree F.residueCharacteristic} (hde : e ≠ d)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    (i : Fin (iwasawaResidueRank F)) :
    iwasawaSingleBlock F d b (e, i) = 0 := by
  classical
  simp [iwasawaSingleBlock, hde]

/-- Remove the largest residue-characteristic power from a positive depth. -/
def iwasawaPrimeToPPart (F : LocalField.{u, v} K) (m : ℕ) : ℕ :=
  m / F.residueCharacteristic ^ padicValNat F.residueCharacteristic m

/-- Every positive depth has the canonical form `m = n*p^s`, with `n`
positive and prime to `p`. -/
theorem iwasawaPrimeToPPart_spec
    (F : LocalField.{u, v} K) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ iwasawaPrimeToPPart F m ∧
      Nat.Coprime (iwasawaPrimeToPPart F m) F.residueCharacteristic ∧
      iwasawaPrimeToPPart F m *
          F.residueCharacteristic ^ padicValNat F.residueCharacteristic m = m := by
  let p : ℕ := F.residueCharacteristic
  let s : ℕ := padicValNat p m
  let n : ℕ := m / p ^ s
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hp0 : p ≠ 0 := F.residueCharacteristic_prime.ne_zero
  have hpPow0 : p ^ s ≠ 0 := pow_ne_zero s hp0
  have hdiv : p ^ s ∣ m := pow_padicValNat_dvd
  have heq : n * p ^ s = m := Nat.div_mul_cancel hdiv
  have hnpos : 1 ≤ n := by
    have hle : p ^ s ≤ m := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hm) hdiv
    exact Nat.div_pos hle (Nat.zero_lt_of_ne_zero hpPow0)
  have hnot : ¬ p ∣ n := by
    intro hpn
    apply pow_succ_padicValNat_not_dvd (p := p) hm0
    obtain ⟨c, hc⟩ := hpn
    refine ⟨c, ?_⟩
    calc
      m = n * p ^ s := heq.symm
      _ = (p * c) * p ^ s := by rw [hc]
      _ = p ^ (s + 1) * c := by rw [pow_succ]; ring
  have hcop : Nat.Coprime n p :=
    (F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr hnot).symm
  simpa [iwasawaPrimeToPPart, p, s, n] using ⟨hnpos, hcop, heq⟩

/-- The depths `n*p^s` attached to distinct prime-to-`p` factors are
distinct.  This is the uniqueness assertion used in Iwasawa's injectivity
coefficient-lifting argument. -/
theorem iwasawaDepth_eq_iff
    (F : LocalField.{u, v} K)
    (d e : IwasawaDegree F.residueCharacteristic) (s t : ℕ) :
    d.1 * F.residueCharacteristic ^ s =
        e.1 * F.residueCharacteristic ^ t ↔
      d = e ∧ s = t := by
  let p : ℕ := F.residueCharacteristic
  have hd0 : d.1 ≠ 0 :=
    Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one d.property.1)
  have he0 : e.1 ≠ 0 :=
    Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one e.property.1)
  have hpd : ¬ p ∣ d.1 :=
    F.residueCharacteristic_prime.coprime_iff_not_dvd.mp d.property.2.symm
  have hpe : ¬ p ∣ e.1 :=
    F.residueCharacteristic_prime.coprime_iff_not_dvd.mp e.property.2.symm
  have hvd : padicValNat p (d.1 * p ^ s) = s := by
    rw [padicValNat.mul hd0 (pow_ne_zero s
      F.residueCharacteristic_prime.ne_zero),
      padicValNat.eq_zero_of_not_dvd hpd, padicValNat.prime_pow, zero_add]
  have hve : padicValNat p (e.1 * p ^ t) = t := by
    rw [padicValNat.mul he0 (pow_ne_zero t
      F.residueCharacteristic_prime.ne_zero),
      padicValNat.eq_zero_of_not_dvd hpe, padicValNat.prime_pow, zero_add]
  constructor
  · intro hdepth
    have hst : s = t := by
      rw [← hvd, ← hve, hdepth]
    subst t
    have hde : d.1 = e.1 :=
      Nat.mul_right_cancel
        (pow_pos F.residueCharacteristic_prime.pos s) hdepth
    exact ⟨Subtype.ext hde, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The `n`-th factor in Iwasawa's infinite product.  It is `1` when `n`
is zero or is divisible by `p`; this lets finite partial products be indexed
by ordinary ranges without making any choice of an enumeration. -/
noncomputable def iwasawaDegreeTerm
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1 :=
  if hn : 1 ≤ n ∧ Nat.Coprime n F.residueCharacteristic then
    Additive.toMul
      (iwasawaGn F hpi n hn.1
        (fun i => a (⟨n, hn⟩, i)))
  else 1

/-- A coefficient block `p^s b` gives exactly the scaled factor occurring
at depth `n*p^s`. -/
theorem iwasawaDegreeTerm_eq_iwasawaGnScaled
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F)
    (d : IwasawaDegree F.residueCharacteristic) (s : ℕ)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    (hab : iwasawaBlock F a d =
      (F.residueCharacteristic ^ s :
        ℤ_[F.residueCharacteristic]) • b) :
    ((iwasawaDegreeTerm F hpi a d.1 :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) =
      ((iwasawaGnScaledAtLevel F hpi d.1 d.property.1 s b :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF))
          (d.1 * F.residueCharacteristic ^ s)) : F.valuationSubringˣ) := by
  classical
  rw [iwasawaDegreeTerm]
  split_ifs with hvalid
  · have he :
        (⟨d.1, hvalid⟩ : IwasawaDegree F.residueCharacteristic) = d :=
      Subtype.ext rfl
    have hvec :
        (fun i => a (⟨d.1, hvalid⟩, i)) =
          (F.residueCharacteristic ^ s :
            ℤ_[F.residueCharacteristic]) • b := by
      rw [he]
      exact hab
    rw [hvec]
    rfl
  · exact (hvalid d.property).elim

/--
Establishes the membership statement `((iwasawaDegreeTerm F hpi a n :
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n`.
-/
theorem iwasawaDegreeTerm_mem_higher
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ) :
    ((iwasawaDegreeTerm F hpi a n :
      ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1) :
      F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) n := by
  classical
  unfold iwasawaDegreeTerm
  split_ifs with hn
  · exact iwasawaGn_mem_higher F hpi n hn.1
      (fun i => a (⟨n, hn⟩, i))
  · exact (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) n).one_mem

/-- Establishes the identity `iwasawaDegreeTerm F hpi (0 : iwasawaDomain F) n = 1`. -/
@[simp] theorem iwasawaDegreeTerm_zero
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    iwasawaDegreeTerm F hpi (0 : iwasawaDomain F) n = 1 := by
  classical
  rw [iwasawaDegreeTerm]
  split_ifs with hn
  · change Additive.toMul
        (iwasawaGn F hpi n hn.1 (0 : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic])) = 1
    rw [map_zero]
    rfl
  · rfl

/--
`iwasawaDegreeTerm` satisfies the addition formula `iwasawaDegreeTerm F hpi (a + b) n =
iwasawaDegreeTerm F hpi a n * iwasawaDegreeTerm F hpi b n`.
-/
theorem iwasawaDegreeTerm_add
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a b : iwasawaDomain F) (n : ℕ) :
    iwasawaDegreeTerm F hpi (a + b) n =
      iwasawaDegreeTerm F hpi a n * iwasawaDegreeTerm F hpi b n := by
  classical
  rw [iwasawaDegreeTerm, iwasawaDegreeTerm, iwasawaDegreeTerm]
  split_ifs with hn
  · change Additive.toMul
        (iwasawaGn F hpi n hn.1
          (fun i => a (⟨n, hn⟩, i) + b (⟨n, hn⟩, i))) = _
    rw [show (fun i => a (⟨n, hn⟩, i) + b (⟨n, hn⟩, i)) =
        (fun i => a (⟨n, hn⟩, i)) +
          (fun i => b (⟨n, hn⟩, i)) by rfl,
      map_add]
    rfl
  · simp

/-- The product of the Iwasawa factors of degree at most `r`. -/
noncomputable def iwasawaPartialProduct
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1 :=
  ∏ n ∈ Finset.range (r + 1), iwasawaDegreeTerm F hpi a n

/-- A single-block domain element contributes precisely its one `g_n`
factor to every sufficiently deep partial product. -/
theorem iwasawaPartialProduct_singleBlock
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (d : IwasawaDegree F.residueCharacteristic)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    {r : ℕ} (hdr : d.1 ≤ r) :
    iwasawaPartialProduct F hpi (iwasawaSingleBlock F d b) r =
      Additive.toMul (iwasawaGn F hpi d.1 d.property.1 b) := by
  classical
  rw [iwasawaPartialProduct]
  calc
    ∏ k ∈ Finset.range (r + 1),
        iwasawaDegreeTerm F hpi (iwasawaSingleBlock F d b) k =
      iwasawaDegreeTerm F hpi (iwasawaSingleBlock F d b) d.1 := by
        apply Finset.prod_eq_single d.1
        · intro k hk hkd
          rw [iwasawaDegreeTerm]
          split_ifs with hkvalid
          · let e : IwasawaDegree F.residueCharacteristic := ⟨k, hkvalid⟩
            have hed : e ≠ d := by
              intro heq
              exact hkd (congrArg Subtype.val heq)
            have hvec :
                (fun i => iwasawaSingleBlock F d b (e, i)) = 0 := by
              funext i
              exact iwasawaSingleBlock_apply_ne F hed b i
            rw [hvec, map_zero]
            rfl
          · rfl
        · intro hdnot
          exact (hdnot (Finset.mem_range.mpr
            (Nat.lt_succ_of_le hdr))).elim
    _ = Additive.toMul (iwasawaGn F hpi d.1 d.property.1 b) := by
      rw [iwasawaDegreeTerm]
      split_ifs with hvalid
      · have he :
            (⟨d.1, hvalid⟩ : IwasawaDegree F.residueCharacteristic) = d :=
          Subtype.ext rfl
        have hvec :
            (fun i => iwasawaSingleBlock F d b
              (⟨d.1, hvalid⟩, i)) = b := by
          funext i
          rw [he]
          exact iwasawaSingleBlock_apply_same F d b i
        rw [hvec]
      · exact (hvalid d.property).elim

/-- Establishes the identity `iwasawaPartialProduct F hpi (0 : iwasawaDomain F) r = 1`. -/
@[simp] theorem iwasawaPartialProduct_zero_input
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (r : ℕ) :
    iwasawaPartialProduct F hpi (0 : iwasawaDomain F) r = 1 := by
  classical
  simp [iwasawaPartialProduct]

/--
`iwasawaPartialProduct` satisfies the addition formula `iwasawaPartialProduct F hpi (a + b) r =
iwasawaPartialProduct F hpi a r * iwasawaPartialProduct F hpi b r`.
-/
theorem iwasawaPartialProduct_add
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a b : iwasawaDomain F) (r : ℕ) :
    iwasawaPartialProduct F hpi (a + b) r =
      iwasawaPartialProduct F hpi a r *
        iwasawaPartialProduct F hpi b r := by
  classical
  simp only [iwasawaPartialProduct, iwasawaDegreeTerm_add]
  exact Finset.prod_mul_distrib

/-- Establishes the identity `iwasawaDegreeTerm F hpi a n = 1`. -/
theorem iwasawaDegreeTerm_eq_one_of_block_eq_zero
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ)
    (ha : ∀ hn : 1 ≤ n ∧ Nat.Coprime n F.residueCharacteristic,
      ∀ i : Fin (iwasawaResidueRank F), a (⟨n, hn⟩, i) = 0) :
    iwasawaDegreeTerm F hpi a n = 1 := by
  classical
  rw [iwasawaDegreeTerm]
  split_ifs with hn
  · have hvec :
        (fun i => a (⟨n, hn⟩, i)) =
          (0 : Fin (iwasawaResidueRank F) →
            ℤ_[F.residueCharacteristic]) := by
      funext i
      exact ha hn i
    rw [hvec, map_zero]
    rfl
  · rfl

/-- Expanding the cutoff by one only adds the factor whose degree is the
new cutoff. -/
theorem iwasawaPartialProduct_succ
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    iwasawaPartialProduct F hpi a (r + 1) =
      iwasawaPartialProduct F hpi a r *
        iwasawaDegreeTerm F hpi a (r + 1) := by
  classical
  unfold iwasawaPartialProduct
  change
    (∏ n ∈ Finset.range (Nat.succ (r + 1)),
        iwasawaDegreeTerm F hpi a n) = _
  rw [Finset.prod_range_succ]

/-- The finite approximation implicit in formula (1): every first
principal unit is represented modulo `U^(r+1)` by the product of the
Iwasawa factors of degree at most `r`.  The support condition records the
inductive coefficient construction. -/
theorem exists_iwasawaPartialProduct_div_mem_higher
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (x : ((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) 1) (r : ℕ) :
    ∃ a : iwasawaDomain F,
      (∀ j, r < j.1.1 → a j = 0) ∧
      (((x / iwasawaPartialProduct F hpi a r :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) :
        F.valuationSubringˣ) ∈
          ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (r + 1) := by
  classical
  induction r with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · intro j _hj
        rfl
      · simp [iwasawaPartialProduct]
  | succ r ih =>
      obtain ⟨a, haSupport, haDeep⟩ := ih
      let n : ℕ := iwasawaPrimeToPPart F (r + 1)
      let s : ℕ := padicValNat F.residueCharacteristic (r + 1)
      have hm : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hspec := iwasawaPrimeToPPart_spec F hm
      have hn : 1 ≤ n := by simpa [n] using hspec.1
      have hcop : Nat.Coprime n F.residueCharacteristic := by
        simpa [n] using hspec.2.1
      have hdepth : n * F.residueCharacteristic ^ s = r + 1 := by
        simpa [n, s] using hspec.2.2
      let d : IwasawaDegree F.residueCharacteristic := ⟨n, hn, hcop⟩
      have hnle : n ≤ r + 1 := by
        rw [← hdepth]
        exact Nat.le_mul_of_pos_right n
          (pow_pos F.residueCharacteristic_prime.pos s)
      let z : ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF))
          (n * F.residueCharacteristic ^ s) :=
        ⟨((x / iwasawaPartialProduct F hpi a r :
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) 1) : F.valuationSubringˣ), by
          simpa [hdepth] using haDeep⟩
      obtain ⟨beta, hbeta⟩ :=
        exists_iwasawaGnScaled_mul_mem_succ F hpi n hn s z
      let b : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic] :=
        (F.residueCharacteristic ^ s :
          ℤ_[F.residueCharacteristic]) • beta
      let a' : iwasawaDomain F := a + iwasawaSingleBlock F d b
      refine ⟨a', ?_, ?_⟩
      · intro j hj
        have haj : a j = 0 := haSupport j (by omega)
        have hjd : j.1 ≠ d := by
          intro hjd
          have hjval : j.1.1 = n := congrArg Subtype.val hjd
          omega
        change a j + iwasawaSingleBlock F d b j = 0
        rw [haj]
        simpa using iwasawaSingleBlock_apply_ne F hjd b j.2
      · have hterm : iwasawaDegreeTerm F hpi a (r + 1) = 1 := by
          apply iwasawaDegreeTerm_eq_one_of_block_eq_zero F hpi
          intro hvalid i
          exact haSupport (⟨⟨r + 1, hvalid⟩, i⟩)
            (Nat.lt_succ_self r)
        have hpartialSucc :
            iwasawaPartialProduct F hpi a (r + 1) =
              iwasawaPartialProduct F hpi a r := by
          rw [iwasawaPartialProduct_succ, hterm, mul_one]
        have hpartial :
            iwasawaPartialProduct F hpi a' (r + 1) =
              iwasawaPartialProduct F hpi a r *
                Additive.toMul (iwasawaGn F hpi n hn b) := by
          rw [show a' = a + iwasawaSingleBlock F d b by rfl,
            iwasawaPartialProduct_add, hpartialSucc,
            iwasawaPartialProduct_singleBlock F hpi d b hnle]
        rw [hpartial]
        have hbeta' :
            (((z / iwasawaGnScaledAtLevel F hpi n hn s beta :
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF))
                  (n * F.residueCharacteristic ^ s)) :
              F.valuationSubringˣ) : F.valuationSubringˣ) ∈
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF)) (r + 1 + 1) := by
          rw [← hdepth]
          exact hbeta
        have hunitEq :
            (((x /
                (iwasawaPartialProduct F hpi a r *
                  Additive.toMul (iwasawaGn F hpi n hn b)) :
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF)) 1) : F.valuationSubringˣ) :
              F.valuationSubringˣ) =
            (((z / iwasawaGnScaledAtLevel F hpi n hn s beta :
                ((classFieldHigherPrincipalUnitGroup
                  F.toCompleteDVF))
                  (n * F.residueCharacteristic ^ s)) :
              F.valuationSubringˣ) : F.valuationSubringˣ) := by
          change
            (x : F.valuationSubringˣ) /
                ((iwasawaPartialProduct F hpi a r :
                    F.valuationSubringˣ) *
                  ((Additive.toMul (iwasawaGn F hpi n hn b) :
                    ((classFieldHigherPrincipalUnitGroup F.toCompleteDVF)) 1) :
                      F.valuationSubringˣ)) =
              (x : F.valuationSubringˣ) /
                  (iwasawaPartialProduct F hpi a r :
                    F.valuationSubringˣ) /
                ((Additive.toMul (iwasawaGn F hpi n hn b) :
                  ((classFieldHigherPrincipalUnitGroup
                    F.toCompleteDVF)) 1) : F.valuationSubringˣ)
          exact div_mul_eq_div_div _ _ _
        rw [hunitEq]
        exact hbeta'

/-- Higher-degree factors disappear in every fixed finite quotient.  Thus
the partial products define a compatible family; this is the formal
convergence argument for the infinite product. -/
theorem Internal.principalUnitQuotientCarrier_mk_iwasawaPartialProduct_eq_of_le
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) {m r : ℕ} (hmr : m ≤ r) :
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (m + 1) (iwasawaPartialProduct F hpi a r) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (m + 1) (iwasawaPartialProduct F hpi a m) := by
  classical
  induction r, hmr using Nat.le_induction with
  | base => rfl
  | @succ r hmr ihr =>
      rw [iwasawaPartialProduct, Finset.prod_range_succ]
      let N :=
        (((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)).subgroupOf
            (((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) 1)
      change
        QuotientGroup.mk' N
            (iwasawaPartialProduct F hpi a r *
              iwasawaDegreeTerm F hpi a (r + 1)) =
          QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m)
      change
        QuotientGroup.mk' N (iwasawaPartialProduct F hpi a r) =
          QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m) at ihr
      rw [map_mul, ihr]
      have hterm :
          QuotientGroup.mk' N (iwasawaDegreeTerm F hpi a (r + 1)) = 1 := by
        apply (QuotientGroup.eq_one_iff
          (N := N) (iwasawaDegreeTerm F hpi a (r + 1))).2
        change
          ((iwasawaDegreeTerm F hpi a (r + 1) :
              ((classFieldHigherPrincipalUnitGroup
                F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) (m + 1)
        exact
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone
          F.toCompleteDVF
          (Nat.succ_le_succ hmr)
          (iwasawaDegreeTerm_mem_higher F hpi a (r + 1))
      rw [hterm]
      exact mul_one
        (QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m))

/-- The compatible family of all finite Iwasawa partial products. -/
noncomputable def Internal.iwasawaGlobalInverseLimitCarrier
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) :
    Internal.principalUnitInverseLimitCarrier F.toCompleteDVF :=
  ⟨fun r =>
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (r + 1) (iwasawaPartialProduct F hpi a r), by
    intro m r hmr
    rw [principalUnitQuotientCarrierTransition_mk]
    exact
      principalUnitQuotientCarrier_mk_iwasawaPartialProduct_eq_of_le
        F hpi a hmr⟩

/--
The defining evaluation formula for `Internal.iwasawaGlobalInverseLimitCarrier` is
`(iwasawaGlobalInverseLimitCarrier F hpi a).1 r =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk 1
(r + 1) (iwasawaPartialProduct F hpi a r)`.
-/
@[simp] theorem Internal.iwasawaGlobalInverseLimitCarrier_apply
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    (iwasawaGlobalInverseLimitCarrier F hpi a).1 r =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (r + 1) (iwasawaPartialProduct F hpi a r) :=
  rfl

/-- Every finite coordinate of the Iwasawa product is onto.  This is the
finite-quotient consequence of formula (1) used in the compactness argument
in the coefficient calculation. -/
theorem Internal.surjective_iwasawaGlobalInverseLimitCarrier_coordinate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (r : ℕ) :
    Function.Surjective (fun a : iwasawaDomain F =>
      (iwasawaGlobalInverseLimitCarrier F hpi a).1 r) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    ((((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) (r + 1)).subgroupOf
      (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1)) q
  obtain ⟨a, _haSupport, ha⟩ :=
    exists_iwasawaPartialProduct_div_mem_higher F hpi x r
  refine ⟨a, ?_⟩
  change
    (QuotientGroup.mk (iwasawaPartialProduct F hpi a r) :
        Internal.principalUnitQuotientCarrier F.toCompleteDVF r) =
      QuotientGroup.mk x
  symm
  let U :=
    toPrincipalUnitFiltration F.toCompleteDVF
  exact (U.principalUnitSubquotient_mk_eq_iff_div_mem x
    (iwasawaPartialProduct F hpi a r)).2 ha

/-- One Iwasawa factor valued in the type-level adic principal-unit model. -/
noncomputable def adicIwasawaGn
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    AdicPrincipalUnits F.toCompleteDVF :=
  AdicPrincipalUnits.of F.toCompleteDVF (iwasawaGn F hpi n hn a)

/-- One degree term valued in the type-level adic principal-unit model. -/
noncomputable def adicIwasawaDegreeTerm
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ) :
    AdicPrincipalUnits F.toCompleteDVF :=
  AdicPrincipalUnits.of F.toCompleteDVF
    (Additive.ofMul (iwasawaDegreeTerm F hpi a n))

/-- A finite Iwasawa partial product valued in the type-level adic
principal-unit model. -/
noncomputable def adicIwasawaPartialProduct
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    AdicPrincipalUnits F.toCompleteDVF :=
  AdicPrincipalUnits.of F.toCompleteDVF
    (Additive.ofMul (iwasawaPartialProduct F hpi a r))

/-- Continuity of one Iwasawa factor; the adic topology is carried by the
codomain type. -/
theorem continuous_adicIwasawaGn
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Continuous (adicIwasawaGn F hpi n hn) := by
  have h : Continuous fun a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic] =>
      ∑ i, a i • AdicPrincipalUnits.of F.toCompleteDVF
        (Additive.ofMul (iwasawaSeed F hpi n hn i)) := by
    fun_prop
  have hof (x : Additive
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF) 1)) :
      AdicPrincipalUnits.linearEquivUnderlying F
          (AdicPrincipalUnits.of F.toCompleteDVF x) = x := rfl
  have hfun : ∀ a : Fin (iwasawaResidueRank F) →
      ℤ_[F.residueCharacteristic],
      (∑ i, a i • AdicPrincipalUnits.of F.toCompleteDVF
          (Additive.ofMul (iwasawaSeed F hpi n hn i))) =
        AdicPrincipalUnits.of F.toCompleteDVF (iwasawaGn F hpi n hn a) := by
    intro a
    apply (AdicPrincipalUnits.linearEquivUnderlying F).injective
    simp only [map_sum, map_smul, hof, iwasawaGn_apply]
  change Continuous fun a =>
    AdicPrincipalUnits.of F.toCompleteDVF (iwasawaGn F hpi n hn a)
  exact h.congr hfun

/--
The specified map is continuous: `Continuous fun a : iwasawaDomain F => adicIwasawaDegreeTerm F
hpi a n`.
-/
theorem continuous_adicIwasawaDegreeTerm
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    Continuous fun a : iwasawaDomain F =>
      adicIwasawaDegreeTerm F hpi a n := by
  classical
  by_cases hn : 1 ≤ n ∧ Nat.Coprime n F.residueCharacteristic
  · have hcoordinates : Continuous fun a : iwasawaDomain F =>
        (fun i => a (⟨n, hn⟩, i)) := by
      exact continuous_pi fun i => continuous_apply
        ((⟨n, hn⟩ : IwasawaDegree F.residueCharacteristic), i)
    have hcont :=
      (continuous_adicIwasawaGn F hpi n hn.1).comp hcoordinates
    apply hcont.congr
    intro a
    simp only [Function.comp_apply, adicIwasawaDegreeTerm,
      iwasawaDegreeTerm, dite_eq_left hn, adicIwasawaGn, ofMul_toMul]
  · simpa only [adicIwasawaDegreeTerm, iwasawaDegreeTerm, dite_eq_right hn,
      ofMul_one] using
      (continuous_const : Continuous fun _ : iwasawaDomain F =>
        AdicPrincipalUnits.of F.toCompleteDVF 0)

/--
The specified map is continuous: `Continuous fun a : iwasawaDomain F => adicIwasawaPartialProduct
F hpi a r`.
-/
theorem continuous_adicIwasawaPartialProduct
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (r : ℕ) :
    Continuous fun a : iwasawaDomain F =>
      adicIwasawaPartialProduct F hpi a r := by
  unfold adicIwasawaPartialProduct iwasawaPartialProduct
  classical
  induction Finset.range (r + 1) using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty, ofMul_one] using
        (continuous_const : Continuous fun _ : iwasawaDomain F =>
          AdicPrincipalUnits.of F.toCompleteDVF 0)
  | @insert n s hns ih =>
      simp only [Finset.prod_insert hns]
      have hcont := (continuous_adicIwasawaDegreeTerm F hpi n).add ih
      apply hcont.congr
      intro a
      apply (AdicPrincipalUnits.addEquiv F.toCompleteDVF).injective
      change
        Additive.ofMul (iwasawaDegreeTerm F hpi a n) +
            Additive.ofMul
              (∏ k ∈ s, iwasawaDegreeTerm F hpi a k) =
          Additive.ofMul
            (iwasawaDegreeTerm F hpi a n *
              ∏ k ∈ s, iwasawaDegreeTerm F hpi a k)
      rw [ofMul_mul]

/-- Internal bridge from the type-level adic partial product to the raw
carrier used by the algebraic inverse-limit construction. -/
theorem Internal.continuous_iwasawaPartialProduct
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (r : ℕ) :
    letI : TopologicalSpace F.valuationSubring :=
      (LubinTate.Valuations.uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F.toCompleteDVF) 1).adicTopology
    Continuous fun a : iwasawaDomain F =>
      iwasawaPartialProduct F hpi a r := by
  let : TopologicalSpace F.valuationSubring :=
    (LubinTate.Valuations.uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F.toCompleteDVF) 1).adicTopology
  let e := Internal.adicPrincipalUnitsHomeomorphUnderlying F.toCompleteDVF
  have h := e.continuous.comp
    (continuous_adicIwasawaPartialProduct F hpi r)
  exact h

/-- Continuity of the compatible finite products.  The target has the
product topology of the discrete finite principal-unit quotients. -/
theorem Internal.continuous_iwasawaGlobalInverseLimitCarrier
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
    Continuous (iwasawaGlobalInverseLimitCarrier F hpi) := by
  let : TopologicalSpace F.valuationSubring :=
    (LubinTate.Valuations.uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F.toCompleteDVF) 1).adicTopology
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let E := Internal.principalUnitHomeomorphInverseLimitCarrier F.toCompleteDVF
  exact Continuous.subtype_mk
    (continuous_pi fun r => by
      have hcoord : Continuous fun x :
        ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1 =>
          (E x).1 r :=
        ((continuous_apply r).comp continuous_subtype_val).comp E.continuous
      change Continuous fun x :
        ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1 =>
        Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF r
          (Internal.principalUnitMulEquivInverseLimitCarrier
            F.toCompleteDVF x) at hcoord
      have hquot : Continuous fun x :
        ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1 =>
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration
            F.toCompleteDVF).principalUnitSubquotientMk 1 (r + 1) x := by
        simpa only [principalUnitMulEquivInverseLimitCarrier_apply] using hcoord
      exact hquot.comp (Internal.continuous_iwasawaPartialProduct F hpi r))
    (fun a => by
      intro m r hmr
      exact (iwasawaGlobalInverseLimitCarrier F hpi a).property hmr)

/-- Additive-homomorphism form of the infinite product in the inverse
limit. -/
noncomputable def Internal.iwasawaGlobalInverseLimitCarrierAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F →+
      Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) where
  toFun a := Additive.ofMul (iwasawaGlobalInverseLimitCarrier F hpi a)
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext r
    change
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk 1 (r + 1)
          (iwasawaPartialProduct F hpi (0 : iwasawaDomain F) r) =
        (1 : Internal.principalUnitQuotientCarrier F.toCompleteDVF r)
    rw [iwasawaPartialProduct_zero_input]
    exact map_one _
  map_add' a b := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext r
    change
      (QuotientGroup.mk (iwasawaPartialProduct F hpi (a + b) r) :
        Internal.principalUnitQuotientCarrier F.toCompleteDVF r) =
      (QuotientGroup.mk (iwasawaPartialProduct F hpi a r) :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF r) *
        (QuotientGroup.mk (iwasawaPartialProduct F hpi b r) :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF r)
    rw [iwasawaPartialProduct_add]
    exact map_mul
      (QuotientGroup.mk'
        ((((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (r + 1)).subgroupOf
          (((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1))) _ _

/-- The Iwasawa compatible family valued in its type-level prodiscrete model.
For a local field all coordinate quotients are finite. -/
noncomputable def iwasawaGlobalProdiscreteLimitAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F →+
      PrincipalUnitProdiscreteLimit F.toCompleteDVF :=
  (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm.toAddMonoidHom.comp
    (iwasawaGlobalInverseLimitCarrierAddHom F hpi)

/-- The specified map is continuous: `Continuous (iwasawaGlobalProdiscreteLimitAddHom F hpi)`. -/
theorem Internal.continuous_iwasawaGlobalProdiscreteLimitAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Continuous (iwasawaGlobalProdiscreteLimitAddHom F hpi) := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let e := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying
    F.toCompleteDVF
  have h := e.continuous_symm.comp
    (Internal.continuous_iwasawaGlobalInverseLimitCarrier F hpi)
  exact h

/-- Continuity of the Iwasawa compatible family; discreteness of every
finite coordinate is encoded by the codomain type. -/
theorem continuous_iwasawaGlobalProdiscreteLimitAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Continuous (iwasawaGlobalProdiscreteLimitAddHom F hpi) :=
  Internal.continuous_iwasawaGlobalProdiscreteLimitAddHom F hpi

/-- Compactness upgrades formula (1), already proved on every finite
coordinate, to surjectivity of the complete Iwasawa product. -/
theorem surjective_iwasawaGlobalProdiscreteLimitAddHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Function.Surjective (iwasawaGlobalProdiscreteLimitAddHom F hpi) := by
  apply
    surjective_principalUnitProdiscreteLimit_of_surjective_coordinates
      F.toCompleteDVF (iwasawaGlobalProdiscreteLimitAddHom F hpi)
      (continuous_iwasawaGlobalProdiscreteLimitAddHom F hpi)
  intro r y
  obtain ⟨a, ha⟩ :=
    surjective_iwasawaGlobalInverseLimitCarrier_coordinate F hpi r
      (Additive.toMul y.val)
  refine ⟨a, ?_⟩
  apply DiscretePrincipalUnitQuotient.ext
  exact congrArg Additive.ofMul ha

/--
The specified map is surjective: `Function.Surjective (iwasawaGlobalInverseLimitCarrierAddHom F
hpi)`.
-/
theorem Internal.surjective_iwasawaGlobalInverseLimitCarrierAddHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Function.Surjective (iwasawaGlobalInverseLimitCarrierAddHom F hpi) := by
  have h := surjective_iwasawaGlobalProdiscreteLimitAddHom F hpi
  exact (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).surjective.comp h

/-- Iwasawa's product homomorphism `g : A -> U^1`, obtained from its
compatible finite quotients via the adic inverse-limit isomorphism. -/
noncomputable def Internal.iwasawaGlobalAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F →+
      Additive (((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) 1) :=
  (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm.toAddMonoidHom.comp
    (iwasawaGlobalInverseLimitCarrierAddHom F hpi)

/-- The specified map is surjective: `Function.Surjective (iwasawaGlobalAddHom F hpi)`. -/
theorem Internal.surjective_iwasawaGlobalAddHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Function.Surjective (iwasawaGlobalAddHom F hpi) := by
  exact
    (principalUnitAddEquivInverseLimitCarrier
      F.toCompleteDVF).symm.surjective.comp
        (surjective_iwasawaGlobalInverseLimitCarrierAddHom F hpi)

/--
Establishes the identity `principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
(iwasawaGlobalAddHom F hpi a) = Additive.ofMul (iwasawaGlobalInverseLimitCarrier F hpi a)`.
-/
@[simp] theorem Internal.principalUnitAddEquivInverseLimitCarrier_iwasawaGlobalAddHom
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) :
    principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
        (iwasawaGlobalAddHom F hpi a) =
      Additive.ofMul (iwasawaGlobalInverseLimitCarrier F hpi a) := by
  exact (principalUnitAddEquivInverseLimitCarrier
    F.toCompleteDVF).apply_symm_apply _

/-- Every factor distinct from a chosen least-depth factor vanishes in the
next finite quotient. -/
theorem iwasawaDegreeTerm_mem_succ_of_ne_minimal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (m : ℕ)
    (d : IwasawaDegree F.residueCharacteristic) (s : ℕ)
    (hm : m = d.1 * F.residueCharacteristic ^ s)
    (hmin : ∀ e : IwasawaDegree F.residueCharacteristic,
      ∀ t : ℕ, ∀ c : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic],
        iwasawaBlock F a e =
            (F.residueCharacteristic ^ t :
              ℤ_[F.residueCharacteristic]) • c →
          IwasawaPrimitive F c →
          m ≤ e.1 * F.residueCharacteristic ^ t)
    (k : ℕ)
    (hk : 1 ≤ k ∧ Nat.Coprime k F.residueCharacteristic)
    (hkd : k ≠ d.1) :
    ((iwasawaDegreeTerm F hpi a k :
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
      ((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) (m + 1) := by
  classical
  let e : IwasawaDegree F.residueCharacteristic := ⟨k, hk⟩
  by_cases he0 : iwasawaBlock F a e = 0
  · have hterm : iwasawaDegreeTerm F hpi a k = 1 := by
      apply iwasawaDegreeTerm_eq_one_of_block_eq_zero F hpi
      intro hvalid i
      have heq :
          (⟨k, hvalid⟩ : IwasawaDegree F.residueCharacteristic) = e :=
        Subtype.ext rfl
      change iwasawaBlock F a (⟨k, hvalid⟩ :
        IwasawaDegree F.residueCharacteristic) i = 0
      rw [heq, he0]
      rfl
    rw [hterm]
    exact (((classFieldHigherPrincipalUnitGroup
      F.toCompleteDVF)) (m + 1)).one_mem
  · obtain ⟨t, c, hec, hc⟩ :=
      exists_pow_smul_iwasawaPrimitive_of_ne_zero F
        (iwasawaBlock F a e) he0
    have hle : m ≤ e.1 * F.residueCharacteristic ^ t :=
      hmin e t c hec hc
    have hne : m ≠ e.1 * F.residueCharacteristic ^ t := by
      intro heqDepth
      have hdepth :
          d.1 * F.residueCharacteristic ^ s =
            e.1 * F.residueCharacteristic ^ t := by
        rw [← hm, heqDepth]
      have hde := (iwasawaDepth_eq_iff F d e s t).1 hdepth
      apply hkd
      exact congrArg Subtype.val hde.1.symm
    have hlevel : m + 1 ≤ e.1 * F.residueCharacteristic ^ t :=
      Nat.succ_le_of_lt (lt_of_le_of_ne hle hne)
    have hscaled :
        (((iwasawaGnScaledAtLevel F hpi e.1 e.property.1 t c :
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF))
              (e.1 * F.residueCharacteristic ^ t)) :
          F.valuationSubringˣ) : F.valuationSubringˣ) ∈
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) (m + 1) :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone
        F.toCompleteDVF hlevel
        (iwasawaGnScaledAtLevel F hpi e.1 e.property.1 t c).property
    have hterm :=
      iwasawaDegreeTerm_eq_iwasawaGnScaled F hpi a e t c hec
    change
      ((iwasawaDegreeTerm F hpi a e.1 :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)
    rw [hterm]
    exact hscaled

/-- The chosen primitive least-depth factor survives in the next quotient;
this is the second coefficient congruence. -/
theorem iwasawaDegreeTerm_not_mem_succ_of_primitive
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (m : ℕ)
    (d : IwasawaDegree F.residueCharacteristic) (s : ℕ)
    (b : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic])
    (hab : iwasawaBlock F a d =
      (F.residueCharacteristic ^ s :
        ℤ_[F.residueCharacteristic]) • b)
    (hb : IwasawaPrimitive F b)
    (hm : m = d.1 * F.residueCharacteristic ^ s) :
    ¬ (((iwasawaDegreeTerm F hpi a d.1 :
          ((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
        ((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)) := by
  have hnotScaled :=
    (iwasawa_formula_two F hpi d.1 d.property.1 s b).1 hb
  intro htermMem
  apply hnotScaled
  have hterm :=
    iwasawaDegreeTerm_eq_iwasawaGnScaled F hpi a d s b hab
  rw [← hterm]
  simpa only [hm] using htermMem

/-- A nonzero coefficient family has nonzero image in the inverse limit.
The least depth supplied above is detected in its `m`-th coordinate. -/
theorem Internal.iwasawaGlobalInverseLimitCarrierAddHom_ne_zero_of_ne_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (ha : a ≠ 0) :
    iwasawaGlobalInverseLimitCarrierAddHom F hpi a ≠ 0 := by
  classical
  obtain ⟨m, d, s, b, hab, hb, hm, hmin⟩ :=
    exists_minimal_iwasawaDepthWitness_of_ne_zero F a ha
  have hdle : d.1 ≤ m := by
    rw [hm]
    exact Nat.le_mul_of_pos_right d.1
      (pow_pos F.residueCharacteristic_prime.pos s)
  have hdmem : d.1 ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hdle)
  have hchosenNot :=
    iwasawaDegreeTerm_not_mem_succ_of_primitive
      F hpi a m d s b hab hb hm
  have hpartialEq :
      (QuotientGroup.mk (iwasawaPartialProduct F hpi a m) :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF m) =
        QuotientGroup.mk (iwasawaDegreeTerm F hpi a d.1) := by
    change
      (QuotientGroup.mk'
        ((((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)).subgroupOf
          (((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) 1)))
          (∏ k ∈ Finset.range (m + 1),
            iwasawaDegreeTerm F hpi a k) =
        QuotientGroup.mk (iwasawaDegreeTerm F hpi a d.1)
    rw [map_prod]
    apply Finset.prod_eq_single d.1
    · intro k hk hkd
      by_cases hvalid :
          1 ≤ k ∧ Nat.Coprime k F.residueCharacteristic
      · apply (QuotientGroup.eq_one_iff
          (N := (((classFieldHigherPrincipalUnitGroup
            F.toCompleteDVF)) (m + 1)).subgroupOf
            (((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) 1))
          (iwasawaDegreeTerm F hpi a k)).2
        change
          ((iwasawaDegreeTerm F hpi a k :
              ((classFieldHigherPrincipalUnitGroup
                F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
            ((classFieldHigherPrincipalUnitGroup
              F.toCompleteDVF)) (m + 1)
        exact iwasawaDegreeTerm_mem_succ_of_ne_minimal
          F hpi a m d s hm hmin k hvalid hkd
      · have hterm : iwasawaDegreeTerm F hpi a k = 1 := by
          simp [iwasawaDegreeTerm, hvalid]
        rw [hterm, map_one]
    · intro hdnot
      exact (hdnot hdmem).elim
  intro hzero
  have hcoord := congrArg
    (fun z : Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      Additive.ofMul ((Additive.toMul z).1 m)) hzero
  have hpartialOne :
      (QuotientGroup.mk (iwasawaPartialProduct F hpi a m) :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF m) = 1 := by
    apply Additive.ofMul.injective
    exact hcoord
  rw [hpartialEq] at hpartialOne
  apply hchosenNot
  exact (QuotientGroup.eq_one_iff
    (N :=
      ((((classFieldHigherPrincipalUnitGroup
        F.toCompleteDVF)) (m + 1)).subgroupOf
        (((classFieldHigherPrincipalUnitGroup
          F.toCompleteDVF)) 1)))
    (iwasawaDegreeTerm F hpi a d.1)).1 hpartialOne

/--
The specified map is injective: `Function.Injective (iwasawaGlobalInverseLimitCarrierAddHom F
hpi)`.
-/
theorem Internal.injective_iwasawaGlobalInverseLimitCarrierAddHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Function.Injective (iwasawaGlobalInverseLimitCarrierAddHom F hpi) := by
  intro a b hab
  have hzero : iwasawaGlobalInverseLimitCarrierAddHom F hpi (a - b) = 0 := by
    rw [map_sub, hab]
    exact sub_self _
  have habzero : a - b = 0 := by
    by_contra hne
    exact (iwasawaGlobalInverseLimitCarrierAddHom_ne_zero_of_ne_zero
      F hpi (a - b) hne) hzero
  exact sub_eq_zero.mp habzero

/--
The specified map is injective: `Function.Injective (iwasawaGlobalProdiscreteLimitAddHom F hpi)`.
-/
theorem injective_iwasawaGlobalProdiscreteLimitAddHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    Function.Injective (iwasawaGlobalProdiscreteLimitAddHom F hpi) := by
  intro a b hab
  apply injective_iwasawaGlobalInverseLimitCarrierAddHom F hpi
  change
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
        (iwasawaGlobalInverseLimitCarrierAddHom F hpi a) =
      (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
        (iwasawaGlobalInverseLimitCarrierAddHom F hpi b) at hab
  exact (PrincipalUnitProdiscreteLimit.addEquiv
    F.toCompleteDVF).symm.injective hab

/-- The equal-characteristic Iwasawa isomorphism, with the prodiscrete
topology fixed in its codomain type.  In the local-field case this topology
is profinite. -/
noncomputable def iwasawaGlobalProdiscreteLimitAddEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F ≃+ PrincipalUnitProdiscreteLimit F.toCompleteDVF :=
  AddEquiv.ofBijective (iwasawaGlobalProdiscreteLimitAddHom F hpi)
    ⟨injective_iwasawaGlobalProdiscreteLimitAddHom F hpi,
      surjective_iwasawaGlobalProdiscreteLimitAddHom F hpi⟩

/-- The Iwasawa product is a homeomorphism onto the type-level prodiscrete
principal-unit limit. -/
noncomputable def iwasawaGlobalProdiscreteLimitContinuousAddEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F ≃ₜ+ PrincipalUnitProdiscreteLimit F.toCompleteDVF := by
  let e := iwasawaGlobalProdiscreteLimitAddEquiv F hpi
  have he : Continuous e :=
    continuous_iwasawaGlobalProdiscreteLimitAddHom F hpi
  let h := e.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap
  exact ContinuousAddEquiv.mk' h (fun x y => e.map_add x y)

/-- Topological form of the equal-characteristic Iwasawa isomorphism.  The
adic topology is part of the codomain type. -/
noncomputable def iwasawaGlobalAdicPrincipalUnitsContinuousAddEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    iwasawaDomain F ≃ₜ+ AdicPrincipalUnits F.toCompleteDVF :=
  (iwasawaGlobalProdiscreteLimitContinuousAddEquiv F hpi).trans
    (adicPrincipalUnitsContinuousAddEquivProdiscreteLimit
      F.toCompleteDVF).symm

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
