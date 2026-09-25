/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Finite.Extension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.HenselLemma

/-! # Unramified Frobenius -/

@[expose] public section
namespace LocalFieldTheory

/-!
# Actual unramified Frobenius

The arithmetic Frobenius is first defined as finite-field Frobenius on the
residue extension, then lifted to `Gal(L / K)` through the canonical
residue-action isomorphism for a finite unramified extension.
-/

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- Arithmetic Frobenius of the actual residue-field extension supplied by a
valuation extension. This is finite Galois ramification theory's finite-field Frobenius,
applied to the canonical residue extension `𝓀[L]/𝓀[K]`. -/
noncomputable def residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] := by
  letI := Fintype.ofFinite 𝓀[K]
  letI : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  exact FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]

/-- The arithmetic Frobenius of a finite residue extension raises each residue element to the size
of the base residue field. -/
theorem residueExtensionArithmeticFrobeniusOfValuationExtension_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝓀[L]) :
    residueExtensionArithmeticFrobeniusOfValuationExtension K L x =
      x ^ Nat.card 𝓀[K] := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  change
    FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] x =
      x ^ Nat.card 𝓀[K]
  simp [Nat.card_eq_fintype_card]

/-- Arithmetic Frobenius fixes the image of the base residue field. -/
theorem residueExtensionArithmeticFrobeniusOfValuationExtension_preserves_base
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝓀[K]) :
    residueExtensionArithmeticFrobeniusOfValuationExtension K L
        (algebraMap 𝓀[K] 𝓀[L] x) =
      algebraMap 𝓀[K] 𝓀[L] x := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  simp [residueExtensionArithmeticFrobeniusOfValuationExtension]

/-- The order of residue arithmetic Frobenius is the degree of the finite residue-field
extension. -/
theorem orderOf_residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    orderOf (residueExtensionArithmeticFrobeniusOfValuationExtension K L) =
      Module.finrank 𝓀[K] 𝓀[L] := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  simpa [residueExtensionArithmeticFrobeniusOfValuationExtension] using
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
      (K := 𝓀[K]) (L := 𝓀[L]))

/-- For an unramified valued extension, residue arithmetic Frobenius has order equal to the
field-extension degree. -/
theorem orderOf_residueExtensionArithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    orderOf (residueExtensionArithmeticFrobeniusOfValuationExtension K L) =
      Module.finrank K L := by
  rw [orderOf_residueExtensionArithmeticFrobeniusOfValuationExtension K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank K L]

/-- Arithmetic Frobenius generates the automorphism group of a finite residue-field extension. -/
theorem residueExtensionArithmeticFrobeniusOfValuationExtension_generates
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    ∀ σ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L],
      σ ∈ Subgroup.zpowers (residueExtensionArithmeticFrobeniusOfValuationExtension K L) := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  intro σ
  rcases
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (K := 𝓀[K]) (L := 𝓀[L])).2 σ with
    ⟨n, hn⟩
  refine ⟨(n : ℕ), ?_⟩
  rw [← hn]
  simp [residueExtensionArithmeticFrobeniusOfValuationExtension]

/-- Actual arithmetic Frobenius in `Gal(L / K)`, obtained by lifting the residue
finite-field Frobenius through the already constructed unramified residue-action
isomorphism. -/
noncomputable def arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L/K) :=
  (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).symm
    (residueExtensionArithmeticFrobeniusOfValuationExtension K L)

/-- The unramified Galois-residue equivalence lifts residue arithmetic Frobenius to field arithmetic
Frobenius. -/
theorem galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      residueExtensionArithmeticFrobeniusOfValuationExtension K L := by
  simp [arithmeticFrobeniusOfUnramifiedValuation]

/-- The residue action of field arithmetic Frobenius is residue arithmetic Frobenius. -/
@[simp]
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      residueExtensionArithmeticFrobeniusOfValuationExtension K L := by
  simpa [galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply]
    using
      galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius
        K L

/-- Field arithmetic Frobenius acts on residues by raising them to the size of the base residue
field. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]) :
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) x =
      x ^ Nat.card 𝓀[K] := by
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius]
  exact residueExtensionArithmeticFrobeniusOfValuationExtension_apply K L x

/-- Two simple roots over a local domain with the same residue are equal. -/
theorem eq_of_simple_roots_of_residue_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : IsLocalRing.residue R b = IsLocalRing.residue R a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : Polynomial R := f /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor : (Polynomial.X - Polynomial.C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hqEval : q.eval a = f.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval f a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqResidue :
      IsLocalRing.residue R (q.eval b) =
        IsLocalRing.residue R (q.eval a) := by
    calc
      IsLocalRing.residue R (q.eval b) =
          (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R b) := by
        exact (Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) b).symm
      _ = (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R a) := by rw [hres]
      _ = IsLocalRing.residue R (q.eval a) := by
        exact Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) a
  have hqResidueNe : IsLocalRing.residue R (q.eval b) ≠ 0 := by
    rw [hqResidue]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnit
  have hqNe : q.eval b ≠ 0 := by
    intro hzero
    exact hqResidueNe (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hbEval : ((Polynomial.X - Polynomial.C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hbEval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hqNe)

/-- Arithmetic Frobenius sends a primitive root of unity of order prime to the
base residue cardinality to its residue-cardinality power. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {n : Nat} {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hcoprime : (Nat.card 𝓀[K]).Coprime n) :
    arithmeticFrobeniusOfUnramifiedValuation K L ζ =
      ζ ^ Nat.card 𝓀[K] := by
  classical
  let := Fintype.ofFinite 𝓀[K]
  obtain ⟨d, hp, hcard⟩ :=
    FiniteField.card 𝓀[K] (ringChar 𝓀[K])
  have hpCard : ringChar 𝓀[K] ∣ Nat.card 𝓀[K] := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self (ringChar 𝓀[K]) d.ne_zero
  have hnChar : ¬ringChar 𝓀[K] ∣ n :=
    hp.coprime_iff_not_dvd.mp (hcoprime.coprime_dvd_left hpCard)
  have hnK : (n : 𝓀[K]) ≠ 0 := by
    intro hzero
    exact hnChar ((ringChar.spec 𝓀[K] n).mp hzero)
  have hnL : (n : 𝓀[L]) ≠ 0 := by
    intro hzero
    apply hnK
    apply (algebraMap 𝓀[K] 𝓀[L]).injective
    calc
      algebraMap 𝓀[K] 𝓀[L] (n : 𝓀[K]) = (n : 𝓀[L]) := map_natCast _ n
      _ = 0 := hzero
      _ = algebraMap 𝓀[K] 𝓀[L] 0 := (map_zero _).symm
  have hn : n ≠ 0 := by
    intro hzero
    exact hnK (by simp [hzero])
  have hζIntegral : IsIntegral 𝒪[K] ζ := by
    apply IsIntegral.of_pow (Nat.pos_iff_ne_zero.mpr hn)
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hζIntegral with
    ⟨a, ha⟩
  change (a : L) = ζ at ha
  let φ : Gal(L/K) :=
    arithmeticFrobeniusOfUnramifiedValuation K L
  let b : 𝒪[L] :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L φ a
  let c : 𝒪[L] := a ^ Nat.card 𝓀[K]
  let f : Polynomial 𝒪[L] := Polynomial.X ^ n - 1
  have haPow : a ^ n = 1 := by
    apply 𝒪[L].subtype_injective
    change (a : L) ^ n = 1
    rw [ha]
    exact hζ.pow_eq_one
  have hbPow : b ^ n = 1 := by
    have hφa : φ (a : L) ^ n = 1 := by
      rw [ha]
      simpa using congrArg φ hζ.pow_eq_one
    apply 𝒪[L].subtype_injective
    simpa [b] using hφa
  have hcPow : c ^ n = 1 := by
    change (a ^ Nat.card 𝓀[K]) ^ n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, haPow, one_pow]
  have hbRoot : f.IsRoot b := by
    rw [Polynomial.IsRoot.def]
    simp [f, hbPow]
  have hcRoot : f.IsRoot c := by
    rw [Polynomial.IsRoot.def]
    simp [f, hcPow]
  have hres :
      IsLocalRing.residue 𝒪[L] b =
        IsLocalRing.residue 𝒪[L] c := by
    calc
      IsLocalRing.residue 𝒪[L] b =
          galoisGroupResidueAlgEquivOfIsIntegralClosure K L φ
            (IsLocalRing.residue 𝒪[L] a) := by
        exact
          (galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
            K L φ a).symm
      _ = (IsLocalRing.residue 𝒪[L] a) ^ Nat.card 𝓀[K] := by
        simpa [φ] using
          galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
            K L (IsLocalRing.residue 𝒪[L] a)
      _ = IsLocalRing.residue 𝒪[L] c := by
        simp [c]
  have hnUnit : IsUnit (n : 𝒪[L]) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : 𝒪[L])).1
    simpa using hnL
  have hcUnit : IsUnit c :=
    IsUnit.of_pow_eq_one hcPow hn
  have hderiv : IsUnit (f.derivative.eval c) := by
    simpa [f, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.eval_mul] using
      hnUnit.mul (hcUnit.pow (n - 1))
  have hbc : b = c :=
    eq_of_simple_roots_of_residue_eq hcRoot hbRoot hres hderiv
  have hval := congrArg (fun x : 𝒪[L] => (x : L)) hbc
  have hval' :
      φ (a : L) = (a : L) ^ Nat.card 𝓀[K] := by
    simpa [b, c] using hval
  change φ ζ = ζ ^ Nat.card 𝓀[K]
  calc
    φ ζ = φ (a : L) := by rw [ha]
    _ = (a : L) ^ Nat.card 𝓀[K] := hval'
    _ = ζ ^ Nat.card 𝓀[K] := by rw [ha]

/-- Arithmetic Frobenius in an unramified Galois extension has order equal to the extension
degree. -/
theorem orderOf_arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    orderOf (arithmeticFrobeniusOfUnramifiedValuation K L) =
      Module.finrank K L := by
  have horder :=
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).orderOf_eq
      (arithmeticFrobeniusOfUnramifiedValuation K L)
  rw [galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius]
    at horder
  exact horder.symm.trans
    (orderOf_residueExtensionArithmeticFrobeniusOfUnramifiedValuation K L)

/-- Arithmetic Frobenius generates the Galois group of a finite unramified extension. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_generates
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    ∀ σ : Gal(L/K),
      σ ∈ Subgroup.zpowers (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  intro σ
  let e := galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L
  rcases residueExtensionArithmeticFrobeniusOfValuationExtension_generates K L (e σ) with
    ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply e.injective
  simpa [e, map_zpow,
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius]
    using hi

/-- The subgroup of integral powers of arithmetic Frobenius is the full Galois group. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Subgroup.zpowers (arithmeticFrobeniusOfUnramifiedValuation K L) = ⊤ := by
  ext σ
  simp [arithmeticFrobeniusOfUnramifiedValuation_generates K L σ]

/-- The Galois group of a finite unramified extension is cyclic. -/
theorem isCyclic_galoisGroup_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    IsCyclic Gal(L/K) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨arithmeticFrobeniusOfUnramifiedValuation K L,
    arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L⟩

/-- The order of the actual unramified Galois group is the degree. This is the
cardinality consequence of the normalized Frobenius construction: arithmetic
Frobenius has order `[L : K]` and generates `Gal(L/K)`. -/
theorem galoisGroup_card_eq_finrank_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card Gal(L/K) = Module.finrank K L := by
  have hcard :=
    orderOf_eq_card_of_zpowers_eq_top
      (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)
  exact hcard.symm.trans (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)

/-- A `ZMod` model of the unramified Galois group obtained from cyclicity and
the order of arithmetic Frobenius. This equivalence does not prescribe which
generator maps to `1`; the normalized model below does. -/
noncomputable def galoisGroupEquivZModOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)) := by
  letI : IsCyclic Gal(L/K) :=
    isCyclic_galoisGroup_of_unramifiedValuation K L
  exact (galoisGroup_card_eq_finrank_of_unramifiedValuation K L) ▸
    (zmodCyclicMulEquiv (G := Gal(L/K)) inferInstance).symm

/-- Internal quotient construction for a specified additive generator. The
public local-field API below supplies `horder` and `hgen` from the already proved
Frobenius source lemmas, so these hypotheses are not exposed as new endpoints. -/
private noncomputable def zmodAddEquivOfGenerator {A : Type*} [AddGroup A]
    (g : A) {n : Nat} (horder : addOrderOf g = n)
    (hgen : AddSubgroup.zmultiples g = ⊤) :
    ZMod n ≃+ A := by
  let f : { f : ℤ →+ A // f n = 0 } :=
    ⟨zmultiplesHom A g, by
      rw [← horder]
      simp [zmultiplesHom_apply]⟩
  refine AddEquiv.ofBijective (ZMod.lift n f) ⟨?_, ?_⟩
  · rw [ZMod.lift_injective]
    intro m hm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [show f.1 m = (m : ℤ) • g by rfl] at hm
    rw [← horder]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := g)).mpr hm
  · intro x
    have hx : x ∈ AddSubgroup.zmultiples g := by
      rw [hgen]
      exact AddSubgroup.mem_top x
    rcases hx with ⟨i, hi⟩
    exact ⟨(i : ZMod n), by simpa [f, ZMod.lift_coe] using hi⟩

private theorem zmodAddEquivOfGenerator_apply_one {A : Type*} [AddGroup A]
    (g : A) {n : Nat} (horder : addOrderOf g = n)
    (hgen : AddSubgroup.zmultiples g = ⊤) :
    zmodAddEquivOfGenerator g horder hgen (1 : ZMod n) = g := by
  unfold zmodAddEquivOfGenerator
  dsimp [AddEquiv.ofBijective, Equiv.ofBijective]
  let f : { f : ℤ →+ A // f n = 0 } :=
    ⟨zmultiplesHom A g, by
      rw [← horder]
      simp [zmultiplesHom_apply]⟩
  change (ZMod.lift n f) (1 : ZMod n) = g
  have hcast : Int.castAddHom (ZMod n) (1 : ℤ) = (1 : ZMod n) := by
    simp [Int.castAddHom]
  rw [← hcast, ZMod.lift_castAddHom]
  simp [f, zmultiplesHom_apply]

private lemma additive_zmultiples_eq_top_of_zpowers_eq_top {G : Type*} [Group G]
    (g : G) (hgen : Subgroup.zpowers g = ⊤) :
    AddSubgroup.zmultiples (Additive.ofMul g) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    change x ∈ (AddSubgroup.zmultiples (Additive.ofMul g) : Set (Additive G))
    rw [← ofMul_image_zpowers_eq_zmultiples_ofMul]
    refine ⟨Additive.toMul x, ?_, rfl⟩
    rw [hgen]
    exact Subgroup.mem_top (Additive.toMul x)

private noncomputable def zmodCyclicMulEquivOfGenerator {G : Type*} [Group G]
    (g : G) {n : Nat} (horder : orderOf g = n)
    (hgen : Subgroup.zpowers g = ⊤) :
    Multiplicative (ZMod n) ≃* G :=
  AddEquiv.toMultiplicative <|
    zmodAddEquivOfGenerator (Additive.ofMul g)
      (by simpa [addOrderOf_ofMul_eq_orderOf] using horder)
      (additive_zmultiples_eq_top_of_zpowers_eq_top g hgen)

private theorem zmodCyclicMulEquivOfGenerator_apply_one {G : Type*} [Group G]
    (g : G) {n : Nat} (horder : orderOf g = n)
    (hgen : Subgroup.zpowers g = ⊤) :
    zmodCyclicMulEquivOfGenerator g horder hgen
      (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  unfold zmodCyclicMulEquivOfGenerator
  change Additive.toMul
      (zmodAddEquivOfGenerator (Additive.ofMul g)
        (by simpa [addOrderOf_ofMul_eq_orderOf] using horder)
        (additive_zmultiples_eq_top_of_zpowers_eq_top g hgen) (1 : ZMod n)) = g
  rw [zmodAddEquivOfGenerator_apply_one]
  rfl

/-- The generator-normalized ZMod model of the actual unramified Galois group.
Unlike `galoisGroupEquivZModOfUnramifiedValuation`, this quotient construction uses
the specified arithmetic Frobenius as the generator, following the normalized Frobenius
  construction before the uniformizer/Frobenius calculation. -/
noncomputable def galoisGroupEquivZModOfUnramifiedValuationNormalized
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)) :=
  (zmodCyclicMulEquivOfGenerator
    (arithmeticFrobeniusOfUnramifiedValuation K L)
    (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)).symm

/-- The normalized equivalence from the unramified Galois group to `ZMod` sends arithmetic Frobenius
to one. -/
@[simp]
theorem galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupEquivZModOfUnramifiedValuationNormalized K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      Multiplicative.ofAdd (1 : ZMod (Module.finrank K L)) := by
  let e :=
    zmodCyclicMulEquivOfGenerator
      (arithmeticFrobeniusOfUnramifiedValuation K L)
      (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
      (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)
  change e.symm (arithmeticFrobeniusOfUnramifiedValuation K L) =
    Multiplicative.ofAdd (1 : ZMod (Module.finrank K L))
  rw [← zmodCyclicMulEquivOfGenerator_apply_one
    (arithmeticFrobeniusOfUnramifiedValuation K L)
    (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)]
  exact e.symm_apply_apply _

/-- Power form of the generator-normalized Frobenius model.  This is the
Frobenius-side model used before composing with the
valuation quotient. -/
@[simp]
theorem galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (m : Int) :
    galoisGroupEquivZModOfUnramifiedValuationNormalized K L
        ((arithmeticFrobeniusOfUnramifiedValuation K L) ^ m) =
      Multiplicative.ofAdd (m : ZMod (Module.finrank K L)) := by
  rw [map_zpow, galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius]
  rw [← ofAdd_zsmul]
  simp [zsmul_eq_mul]

end
end LocalFieldTheory
