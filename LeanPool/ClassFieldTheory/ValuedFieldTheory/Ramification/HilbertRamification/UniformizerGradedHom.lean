/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Monogeneity
/-!
# First ramification-quotient homomorphism over general DVFs

This file constructs the graded uniformizer homomorphism under the standing
hypotheses of ramification-number theory.  Completeness is not assumed.  The
injectivity statement includes the necessary separability hypothesis on the
residue extension; the unconditional printed assertion is false for fiercely
ramified extensions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField.ResidueField


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

/-- The principal-unit filtration attached to a general DVF. -/
def dvfHigherPrincipalUnitGroup
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) (n : ℕ) :
    Subgroup target.valuationSubringˣ where
  carrier := {a | (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hre :
        ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          (a : target.valuationSubring) *
              ((b : target.valuationSubring) - 1) +
            ((a : target.valuationSubring) - 1) := by
      simp
      ring
    change
      ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb) ha
  inv_mem' := by
    intro a ha
    have hre :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          -(((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
            ((a : target.valuationSubring) - 1)) := by
      calc
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 =
            ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) -
              ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
                (a : target.valuationSubring) := by simp
        _ = _ := by ring
    change
      ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact (target.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left _ _ ha)

/-- States the theorem `mem_dvfHigherPrincipalUnitGroup_iff`. -/
@[simp] theorem mem_dvfHigherPrincipalUnitGroup_iff
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (n : ℕ) (a : target.valuationSubringˣ) :
    a ∈ dvfHigherPrincipalUnitGroup target n ↔
      (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n :=
  Iff.rfl

/-- States the theorem `dvfHigherPrincipalUnitGroup_antitone`. -/
theorem dvfHigherPrincipalUnitGroup_antitone
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) :
    Antitone (dvfHigherPrincipalUnitGroup target) := by
  intro m n hmn a ha
  exact Ideal.pow_le_pow_right hmn ha

/-- The literal target U_L^n/U_L^(n+1). -/
abbrev dvfPrincipalUnitGradedPiece
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) (n : ℕ) :=
  dvfHigherPrincipalUnitGroup target n ⧸
    (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
      (dvfHigherPrincipalUnitGroup target n)

/-- The literal source G_n/G_(n+1) formed from the real lower groups. -/
abbrev lowerRamificationGradedPiece
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) :=
  lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ) ⧸
    (lowerRamificationGroup
      (base := base) (target := target) huniq ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ))

/-- The unique-extension action on target valuation-ring units. -/
abbrev dvfValuationSubringUnitAut
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    target.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma).toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfValuationSubringUnitAut_apply`. -/
@[simp] theorem dvfValuationSubringUnitAut_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubringˣ) :
    ((dvfValuationSubringUnitAut
      (base := base) (target := target) huniq sigma a :
        target.valuationSubringˣ) : target.valuationSubring) =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma
        (a : target.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every Galois conjugate of a target uniformizer differs from it by a
valuation-ring unit. -/
theorem exists_dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    ∃ a : target.valuationSubringˣ,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma pi =
        (a : target.valuationSubring) * pi := by
  let sigmaPi :=
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma pi
  have hpiMem : pi ∈ target.maximalIdeal :=
    target.uniformizer_mem_maximalIdeal hpi
  have hpiDvd : pi ∣ sigmaPi := by
    have hsigmaMem : sigmaPi ∈ target.maximalIdeal ^ 1 := by
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
          (base := base) (target := target) huniq sigma 1 pi).2
          (by simpa using hpiMem)
    rw [← Ideal.mem_span_singleton]
    have hsigmaMem' : sigmaPi ∈ target.maximalIdeal := by
      simpa using hsigmaMem
    rw [target.maximalIdeal_eq_span_uniformizer hpi] at hsigmaMem'
    exact hsigmaMem'
  have hsigmaDvd : sigmaPi ∣ pi := by
    have hinvMem :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma⁻¹ pi ∈
          target.maximalIdeal ^ 1 :=
      (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
        (base := base) (target := target) huniq sigma⁻¹ 1 pi).2
        (by simpa using hpiMem)
    have hdiv :
        pi ∣ valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma⁻¹ pi := by
      rw [← Ideal.mem_span_singleton]
      have hinvMem' :
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma⁻¹ pi ∈
            target.maximalIdeal := by
        simpa using hinvMem
      rw [target.maximalIdeal_eq_span_uniformizer hpi] at hinvMem'
      exact hinvMem'
    rcases hdiv with ⟨b, hb⟩
    refine
      ⟨valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma b, ?_⟩
    calc
      pi =
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma⁻¹ pi) := by
        rw [valuationSubringAutOfUniqueExtension_apply_inv_apply]
      _ = valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (pi * b) := by
        rw [hb]
      _ = sigmaPi *
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma b := by
        simp [sigmaPi]
  rcases hpiDvd with ⟨a, ha⟩
  rcases hsigmaDvd with ⟨b, hb⟩
  have hpi0 : pi ≠ 0 := by
    intro hzero
    have hzeroL :=
      congrArg (fun z : target.valuationSubring => (z : L)) hzero
    exact hpi.ne_zero (by simpa using hzeroL)
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hpi0
    calc
      pi * (a * b) = (pi * a) * b := by rw [mul_assoc]
      _ = sigmaPi * b := by rw [← ha]
      _ = pi := hb.symm
      _ = pi * 1 := by rw [mul_one]
  refine ⟨⟨a, b, hab, ?_⟩, ?_⟩
  · simpa [mul_comm] using hab
  · change sigmaPi = a * pi
    simpa [mul_comm] using ha

/-- The chosen unit sigma(pi)/pi. -/
noncomputable def dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) : target.valuationSubringˣ :=
  Classical.choose
    (exists_dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerQuotientUnit_mul_uniformizer`. -/
@[simp] theorem dvfUniformizerQuotientUnit_mul_uniformizer
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma pi =
      (dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma :
          target.valuationSubring) * pi :=
  Classical.choose_spec
    (exists_dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Exact cocycle identity for the chosen quotient units. -/
theorem dvfUniformizerQuotientUnit_mul_eq
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma tau : Gal(L/K)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi (sigma * tau) =
      dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma
          (dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi tau) *
        dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi sigma := by
  apply Units.ext
  have hpi0 : pi ≠ 0 := by
    intro hzero
    have hzeroL :=
      congrArg (fun z : target.valuationSubring => (z : L)) hzero
    exact hpi.ne_zero (by simpa using hzeroL)
  apply mul_right_cancel₀ hpi0
  calc
    ((dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi (sigma * tau) :
          target.valuationSubringˣ) : target.valuationSubring) * pi =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi (sigma * tau)]
    _ = valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau pi) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply]
    _ = valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          ((dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi tau :
                target.valuationSubringˣ) : target.valuationSubring) *
            valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi tau]
      simp
    _ =
        ((dvfValuationSubringUnitAut
              (base := base) (target := target) huniq sigma
              (dvfUniformizerQuotientUnit
                (base := base) (target := target) huniq pi hpi tau) *
            dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi sigma :
            target.valuationSubringˣ) : target.valuationSubring) * pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi sigma]
      simp [mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Quotient-unit membership is equivalent to one-deeper displacement of the
uniformizer. -/
theorem dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) (sigma : Gal(L/K)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma pi - pi ∈
        target.maximalIdeal ^ (n + 1) := by
  let a : target.valuationSubring :=
    (dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq pi hpi sigma :
        target.valuationSubring)
  change a - 1 ∈ target.maximalIdeal ^ n ↔ _
  have hmul :
      (a - 1) * pi =
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma pi - pi := by
    dsimp [a]
    rw [dvfUniformizerQuotientUnit_mul_uniformizer
      (base := base) (target := target) huniq pi hpi sigma]
    ring
  constructor
  · intro ha
    rw [← hmul]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n] at ha
    rcases ha with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      (a - 1) * pi = (pi ^ n * b) * pi := by rw [hb]
      _ = pi ^ (n + 1) * b := by rw [pow_succ]; ring
  · intro hdiff
    rw [← hmul] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n]
    rcases hdiff with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hpi0 : pi ≠ 0 := by
      intro hzero
      have hzeroL :=
        congrArg (fun z : target.valuationSubring => (z : L)) hzero
      exact hpi.ne_zero (by simpa using hzeroL)
    apply mul_right_cancel₀ hpi0
    calc
      (a - 1) * pi = pi ^ (n + 1) * b := hb
      _ = (pi ^ n * b) * pi := by rw [pow_succ]; ring

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If sigma lies in G_n, then sigma(pi)/pi lies in U_L^n. -/
theorem dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n := by
  exact
    (dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
      (base := base) (target := target) huniq hpi n sigma).2
      ((mem_lowerRamificationGroup_nat_iff
        (base := base) (target := target) huniq n sigma).1 hsigma pi)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A G_n automorphism acts trivially on every unit modulo U_L^(n+1). -/
theorem dvfValuationSubringUnitAut_div_mem_succ
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ))
    (a : target.valuationSubringˣ) :
    dvfValuationSubringUnitAut
        (base := base) (target := target) huniq sigma a / a ∈
      dvfHigherPrincipalUnitGroup target (n + 1) := by
  rw [mem_dvfHigherPrincipalUnitGroup_iff]
  have hdiff :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (a : target.valuationSubring) -
        (a : target.valuationSubring) ∈
      target.maximalIdeal ^ (n + 1) :=
    (mem_lowerRamificationGroup_nat_iff
      (base := base) (target := target) huniq n sigma).1 hsigma a
  have hre :
      ((dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma a / a :
            target.valuationSubringˣ) : target.valuationSubring) - 1 =
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma
              (a : target.valuationSubring) -
            (a : target.valuationSubring)) := by
    simp [div_eq_mul_inv]
    have hinv :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (a : target.valuationSubring) = 1 := by
      exact_mod_cast Units.inv_mul a
    rw [mul_sub, hinv]
    ring
  rw [hre]
  exact Ideal.mul_mem_left _ _ hdiff

/-- Any two target uniformizers differ by a valuation-ring unit. -/
theorem exists_dvf_unit_mul_uniformizer_eq_uniformizer
    {pi pi' : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hpi' : target.valuation.IsUniformizer (pi' : L)) :
    ∃ a : target.valuationSubringˣ,
      pi' = (a : target.valuationSubring) * pi := by
  rcases Valuation.associated_of_isUniformizer
      (v := target.valuation) hpi hpi' with
    ⟨a, ha⟩
  exact ⟨a, by rw [← ha, mul_comm]⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Exact change-of-uniformizer formula. -/
theorem dvfUniformizerQuotientUnit_eq_of_uniformizer_eq_unit_mul
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi pi' : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hpi' : target.valuation.IsUniformizer (pi' : L))
    (a : target.valuationSubringˣ)
    (hpiA : pi' = (a : target.valuationSubring) * pi)
    (sigma : Gal(L/K)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi' hpi' sigma =
      dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma a *
        dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi sigma * a⁻¹ := by
  apply Units.ext
  have hpi'0 : pi' ≠ 0 := by
    intro hzero
    have hzeroL :=
      congrArg (fun z : target.valuationSubring => (z : L)) hzero
    exact hpi'.ne_zero (by simpa using hzeroL)
  apply mul_right_cancel₀ hpi'0
  calc
    ((dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi' hpi' sigma :
          target.valuationSubringˣ) : target.valuationSubring) * pi' =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma pi' := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi' hpi' sigma]
    _ = valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          ((a : target.valuationSubring) * pi) := by
      rw [hpiA]
    _ =
        (dvfValuationSubringUnitAut
            (base := base) (target := target) huniq sigma a :
            target.valuationSubringˣ) *
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma pi := by
      simp
    _ =
        (dvfValuationSubringUnitAut
            (base := base) (target := target) huniq sigma a :
            target.valuationSubringˣ) *
          ((dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi sigma :
              target.valuationSubringˣ) : target.valuationSubring) * pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi sigma]
      ring
    _ =
        ((dvfValuationSubringUnitAut
              (base := base) (target := target) huniq sigma a *
            dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi sigma * a⁻¹ :
            target.valuationSubringˣ) : target.valuationSubring) * pi' := by
      rw [hpiA]
      simp [mul_assoc, mul_comm]

/-- Representative homomorphism from G_n to the literal principal-unit
graded quotient. -/
noncomputable def dvfUniformizerRepresentativeHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) →*
      dvfPrincipalUnitGradedPiece target n where
  toFun sigma :=
    QuotientGroup.mk'
      ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
        (dvfHigherPrincipalUnitGroup target n))
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)),
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi sigma.property⟩
  map_one' := by
    let oneN :
        lowerRamificationGroup
          (base := base) (target := target) huniq (n : ℝ) := 1
    let u1 : dvfHigherPrincipalUnitGroup target n :=
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi 1,
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi oneN.property⟩
    change
      QuotientGroup.mk'
          ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n)) u1 = 1
    apply
      (QuotientGroup.eq_one_iff
        (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n)) u1).2
    change
      dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi 1 ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    exact
      dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
        (base := base) (target := target) huniq hpi
        (lowerRamificationGroup
          (base := base) (target := target) huniq
          ((n + 1 : ℕ) : ℝ)).one_mem
  map_mul' := by
    intro sigma tau
    apply
      (QuotientGroup.eq_iff_div_mem
        (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n))).2
    change
      dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            ((sigma : Gal(L/K)) * (tau : Gal(L/K))) /
          (dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (sigma : Gal(L/K)) *
            dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (tau : Gal(L/K))) ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    have hact :=
      dvfValuationSubringUnitAut_div_mem_succ
        (base := base) (target := target) huniq sigma.property
        (dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (tau : Gal(L/K)))
    rw [dvfUniformizerQuotientUnit_mul_eq
      (base := base) (target := target) huniq pi hpi
      (sigma : Gal(L/K)) (tau : Gal(L/K))]
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hact

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerRepresentativeHom_apply`. -/
@[simp] theorem dvfUniformizerRepresentativeHom_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi hpi n sigma =
      QuotientGroup.mk'
        ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n))
        ⟨dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            (sigma : Gal(L/K)),
          dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
            (base := base) (target := target) huniq hpi sigma.property⟩ :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Representative-level independence of the chosen uniformizer. -/
theorem dvfUniformizerRepresentativeHom_apply_eq_of_uniformizers
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi pi' : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hpi' : target.valuation.IsUniformizer (pi' : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi' hpi' n sigma =
      dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi hpi n sigma := by
  rcases exists_dvf_unit_mul_uniformizer_eq_uniformizer
      (target := target) hpi hpi' with
    ⟨a, hpiA⟩
  apply
    (QuotientGroup.eq_iff_div_mem
      (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
        (dvfHigherPrincipalUnitGroup target n))).2
  change
    dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi' hpi'
          (sigma : Gal(L/K)) /
        dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)) ∈
      dvfHigherPrincipalUnitGroup target (n + 1)
  have hact :=
    dvfValuationSubringUnitAut_div_mem_succ
      (base := base) (target := target) huniq sigma.property a
  rw [dvfUniformizerQuotientUnit_eq_of_uniformizer_eq_unit_mul
    (base := base) (target := target) huniq hpi hpi' a hpiA
    (sigma : Gal(L/K))]
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hact

/-- The first ramification-quotient homomorphism: the uniformizer quotient descends
to G_n/G_(n+1) with values in U_L^n/U_L^(n+1). -/
noncomputable def uniformizerGradedHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGradedPiece (base := base) (target := target) huniq n →*
      dvfPrincipalUnitGradedPiece target n :=
  QuotientGroup.lift
    ((lowerRamificationGroup
      (base := base) (target := target) huniq
      ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)))
    (dvfUniformizerRepresentativeHom
      (base := base) (target := target) huniq pi hpi n)
    (by
      intro sigma hsigma
      rw [MonoidHom.mem_ker]
      change
        QuotientGroup.mk'
            ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
              (dvfHigherPrincipalUnitGroup target n))
            ⟨dvfUniformizerQuotientUnit
                (base := base) (target := target) huniq pi hpi
                (sigma : Gal(L/K)),
              dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
                (base := base) (target := target) huniq hpi sigma.property⟩ =
          1
      apply
        (QuotientGroup.eq_one_iff
          (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n))
          ⟨dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (sigma : Gal(L/K)),
            dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
              (base := base) (target := target) huniq hpi sigma.property⟩).2
      change
        dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            (sigma : Gal(L/K)) ∈
          dvfHigherPrincipalUnitGroup target (n + 1)
      exact
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi
          (by simpa [Subgroup.mem_subgroupOf] using hsigma))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `uniformizerGradedHom_mk`. -/
@[simp] theorem uniformizerGradedHom_mk
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n
        (QuotientGroup.mk'
          ((lowerRamificationGroup
            (base := base) (target := target) huniq
            ((n + 1 : ℕ) : ℝ)).subgroupOf
            (lowerRamificationGroup
              (base := base) (target := target) huniq (n : ℝ))) sigma) =
      dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi hpi n sigma :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The graded homomorphism is independent of the chosen uniformizer. -/
theorem uniformizerGradedHom_eq_of_uniformizers
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi pi' : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hpi' : target.valuation.IsUniformizer (pi' : L))
    (n : ℕ) :
    uniformizerGradedHom
        (base := base) (target := target) huniq pi' hpi' n =
      uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n := by
  apply MonoidHom.ext
  intro q
  obtain ⟨sigma, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((lowerRamificationGroup
        (base := base) (target := target) huniq
        ((n + 1 : ℕ) : ℝ)).subgroupOf
        (lowerRamificationGroup
          (base := base) (target := target) huniq (n : ℝ))) q
  exact
    dvfUniformizerRepresentativeHom_apply_eq_of_uniformizers
      (base := base) (target := target) huniq hpi hpi' n sigma

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Kernel criterion at a representative. -/
theorem uniformizerGradedHom_mk_eq_one_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n
        (QuotientGroup.mk'
          ((lowerRamificationGroup
            (base := base) (target := target) huniq
            ((n + 1 : ℕ) : ℝ)).subgroupOf
            (lowerRamificationGroup
              (base := base) (target := target) huniq (n : ℝ))) sigma) = 1 ↔
      dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)) ∈
        dvfHigherPrincipalUnitGroup target (n + 1) := by
  rw [uniformizerGradedHom_mk]
  exact
    QuotientGroup.eq_one_iff
      (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
        (dvfHigherPrincipalUnitGroup target n))
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)),
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi sigma.property⟩

/-- The unique-extension ring automorphism as an algebra automorphism over
the base valuation ring. -/
def valuationSubringAlgEquivOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    target.valuationSubring ≃ₐ[base.valuationSubring]
      target.valuationSubring :=
  { valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma with
    commutes' := by
      intro a
      apply Subtype.ext
      simp [valuationSubringAutOfUniqueExtension] }

/-- Taylor's one-step argument over a general DVF. -/
theorem polynomial_argument_sub_mem_succ_dvf
    {P : Polynomial target.valuationSubring}
    {a b : target.valuationSubring} {n : ℕ}
    (hderiv : IsUnit (P.derivative.eval a))
    (hab : b - a ∈ target.maximalIdeal ^ (n + 1))
    (hP : P.eval b - P.eval a ∈ target.maximalIdeal ^ (n + 2)) :
    b - a ∈ target.maximalIdeal ^ (n + 2) := by
  let q : Polynomial target.valuationSubring :=
    P /ₘ (Polynomial.X - Polynomial.C a)
  have hdecomp :
      P = Polynomial.C (P.eval a) +
        (Polynomial.X - Polynomial.C a) * q := by
    dsimp [q]
    calc
      P = P %ₘ (Polynomial.X - Polynomial.C a) +
          (Polynomial.X - Polynomial.C a) *
            (P /ₘ (Polynomial.X - Polynomial.C a)) :=
        (Polynomial.modByMonic_add_div P
          (Polynomial.X - Polynomial.C a)).symm
      _ = Polynomial.C (P.eval a) +
          (Polynomial.X - Polynomial.C a) *
            (P /ₘ (Polynomial.X - Polynomial.C a)) := by
        rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
  have hEval :
      P.eval b - P.eval a = (b - a) * q.eval b := by
    rw [hdecomp]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub]
  have hqEval : q.eval a = P.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval
        (p := P) a
  have hqUnitA : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqdiff :
      q.eval b - q.eval a ∈ target.maximalIdeal ^ (n + 1) := by
    simpa using
      polynomial_eval₂_sub_mem_of_sub_mem
        (f := RingHom.id target.valuationSubring)
        (I := target.maximalIdeal ^ (n + 1))
        (x := b) (y := a) hab q
  have hqdiffM : q.eval b - q.eval a ∈ target.maximalIdeal := by
    simpa using
      Ideal.pow_le_pow_right (Nat.succ_pos n) hqdiff
  have hres :
      target.residueMap (q.eval b) =
        target.residueMap (q.eval a) := by
    rw [residue_eq_residue_iff_sub_mem_maximalIdeal
      (R := target.valuationSubring)]
    exact hqdiffM
  have hresA : target.residueMap (q.eval a) ≠ 0 :=
    (target.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnitA
  have hresB : target.residueMap (q.eval b) ≠ 0 := by
    rw [hres]
    exact hresA
  have hqUnitB : IsUnit (q.eval b) :=
    (target.residue_ne_zero_iff_isUnit (q.eval b)).1 hresB
  have hmul :
      q.eval b * (b - a) ∈ target.maximalIdeal ^ (n + 2) := by
    simpa [hEval, mul_comm] using hP
  exact
    ((target.maximalIdeal ^ (n + 2)).unit_mul_mem_iff_mem hqUnitB).1
      hmul

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A displacement bound on an algebra generator propagates to the algebra
it generates. -/
theorem valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin_graded
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {generator : target.valuationSubring} {r : ℕ} {sigma : Gal(L/K)}
    (hgenerator :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma generator -
        generator ∈ target.maximalIdeal ^ r)
    {a : target.valuationSubring}
    (ha :
      a ∈ Algebra.adjoin base.valuationSubring
        ({generator} : Set target.valuationSubring)) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a -
        a ∈ target.maximalIdeal ^ r := by
  let e :=
    valuationSubringAlgEquivOfUniqueExtension
      (base := base) (target := target) huniq sigma
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact hgenerator
  | algebraMap a =>
      rw [show
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring a) =
          algebraMap base.valuationSubring target.valuationSubring a from
        e.commutes a, sub_self]
      exact Ideal.zero_mem _
  | add a b _ha _hb ha hb =>
      have hre :
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a + b) -
            (a + b) =
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a - a) +
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma b - b) := by
        simp
        ring
      rw [hre]
      exact Ideal.add_mem _ ha hb
  | mul a b _ha _hb ha hb =>
      have hre :
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a * b) -
            a * b =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a *
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma b - b) +
            (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma a - a) * b := by
        simp
        ring
      rw [hre]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ hb)
        (Ideal.mul_mem_right _ _ ha)

/-- Corrected maximal form of the first ramification-quotient homomorphism over
general DVFs.  Residue separability is essential: the unconditional
injectivity without additional hypotheses fails for fiercely ramified extensions. -/
theorem uniformizerGradedHom_injective_of_residue_isSeparable
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    [Algebra.IsSeparable base.residueField target.residueField]
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    Function.Injective
      (uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n) := by
  rcases exists_valuationSubring_generator_data_of_uniqueExtension
      (base := base) (target := target) huniq with
    ⟨P, generator, _hprim, hpiGenerator, hderiv, hgenerator⟩
  let piGenerator : target.valuationSubring :=
    Polynomial.aeval generator P
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    obtain ⟨sigma, rfl⟩ :=
      QuotientGroup.mk'_surjective
        ((lowerRamificationGroup
          (base := base) (target := target) huniq
          ((n + 1 : ℕ) : ℝ)).subgroupOf
          (lowerRamificationGroup
            (base := base) (target := target) huniq (n : ℝ))) q
    have hmapPi :
        uniformizerGradedHom
            (base := base) (target := target) huniq pi hpi n
            (QuotientGroup.mk'
              ((lowerRamificationGroup
                (base := base) (target := target) huniq
                ((n + 1 : ℕ) : ℝ)).subgroupOf
                (lowerRamificationGroup
                  (base := base) (target := target) huniq (n : ℝ))) sigma) =
          1 :=
      MonoidHom.mem_ker.mp hq
    have hmapGenerator :
        uniformizerGradedHom
            (base := base) (target := target) huniq
            piGenerator hpiGenerator n
            (QuotientGroup.mk'
              ((lowerRamificationGroup
                (base := base) (target := target) huniq
                ((n + 1 : ℕ) : ℝ)).subgroupOf
                (lowerRamificationGroup
                  (base := base) (target := target) huniq (n : ℝ))) sigma) =
          1 := by
      rw [uniformizerGradedHom_eq_of_uniformizers
        (base := base) (target := target) huniq hpi hpiGenerator n]
      exact hmapPi
    have hu :
        dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq
            piGenerator hpiGenerator (sigma : Gal(L/K)) ∈
          dvfHigherPrincipalUnitGroup target (n + 1) :=
      (uniformizerGradedHom_mk_eq_one_iff
        (base := base) (target := target) huniq
        piGenerator hpiGenerator n sigma).1 hmapGenerator
    let e :=
      valuationSubringAlgEquivOfUniqueExtension
        (base := base) (target := target) huniq (sigma : Gal(L/K))
    let Q : Polynomial target.valuationSubring :=
      P.map (algebraMap base.valuationSubring target.valuationSubring)
    have hx :
        e generator - generator ∈ target.maximalIdeal ^ (n + 1) :=
      (mem_lowerRamificationGroup_nat_iff
        (base := base) (target := target) huniq n (sigma : Gal(L/K))).1
        sigma.property generator
    have hpiDeep :
        e piGenerator - piGenerator ∈ target.maximalIdeal ^ (n + 2) := by
      exact
        (dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
          (base := base) (target := target) huniq
          hpiGenerator (n + 1) (sigma : Gal(L/K))).1 hu
    have hmap :
        e (Polynomial.aeval generator P) =
          Polynomial.aeval (e generator) P := by
      simpa [e] using
        (Polynomial.aeval_algHom_apply e.toAlgHom generator P).symm
    have hQeval :
        Q.eval (e generator) - Q.eval generator =
          e piGenerator - piGenerator := by
      calc
        Q.eval (e generator) - Q.eval generator =
            Polynomial.aeval (e generator) P -
              Polynomial.aeval generator P := by
          simp [Q, Polynomial.aeval_def]
        _ = e (Polynomial.aeval generator P) -
              Polynomial.aeval generator P := by
          rw [← hmap]
        _ = e piGenerator - piGenerator := rfl
    have hQdeep :
        Q.eval (e generator) - Q.eval generator ∈
          target.maximalIdeal ^ (n + 2) := by
      rw [hQeval]
      exact hpiDeep
    have hxDeep :
        e generator - generator ∈ target.maximalIdeal ^ (n + 2) :=
      polynomial_argument_sub_mem_succ_dvf
        (target := target) (P := Q)
        (a := generator) (b := e generator) (n := n)
        (by simpa [Q] using hderiv) hx hQdeep
    have hnext :
        (sigma : Gal(L/K)) ∈
          lowerRamificationGroup
            (base := base) (target := target) huniq ((n + 1 : ℕ) : ℝ) := by
      rw [mem_lowerRamificationGroup_nat_iff]
      intro a
      apply
        valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin_graded
          (base := base) (target := target) huniq
          (generator := generator) (r := n + 2)
          (sigma := (sigma : Gal(L/K)))
      · exact hxDeep
      · rw [hgenerator]
        simp
    exact
      (QuotientGroup.eq_one_iff
        (N := (lowerRamificationGroup
          (base := base) (target := target) huniq
          ((n + 1 : ℕ) : ℝ)).subgroupOf
          (lowerRamificationGroup
            (base := base) (target := target) huniq (n : ℝ)))
        sigma).2 (by
          simpa [Subgroup.mem_subgroupOf] using hnext)
  · exact bot_le

end Higher
end RamificationTheory.HilbertRamification
