/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
/-!
# Galois actions on residue fields

Restricts field automorphisms to residue-field automorphisms and identifies
the resulting kernels and stabilizers with inertia subgroups.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- Actual integral-closure version of the residue-field automorphism induced by
a real Galois automorphism.

the local class-field calculation reduces the product of conjugates modulo the maximal ideal;
  this is the source map for that reduction, built from the already constructed
  integral-closure action on `𝒪[L]`. -/
def galoisGroupResidueFieldEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝓀[L] ≃+* 𝓀[L] :=
  IsLocalRing.ResidueField.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The residue-field action of a Galois automorphism sends a reduced integer to the reduction of
its conjugate. -/
@[simp]
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) := by
  rfl

/-- The Galois action on residue units agrees with reducing the conjugate of an integer unit. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (u : 𝒪[L]ˣ) :
    Units.mapEquiv (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
        (integerUnitsToResidueUnits L u) =
      integerUnitsToResidueUnits L
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  rfl

/-- The induced residue-field automorphism fixes the image of the base residue field. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝓀[K]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) =
      algebraMap 𝓀[K] 𝓀[L] x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
      (algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)) =
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)
  rw [residueField_algebraMap_residue K L a]
  rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue]
  exact congrArg (fun z : 𝒪[L] => IsLocalRing.residue 𝒪[L] z)
    (galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ a)

/-- Actual integral-closure residue action as a `𝓀[K]`-algebra automorphism. -/
@[implicit_reducible]
def galoisGroupResidueAlgEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] where
  __ := galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
  commutes' := galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ

/-- Actual integral-closure residue action as a group homomorphism. -/
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L
  map_one' := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_mul' := by
    intro σ τ
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- The residue representation of the Galois group evaluates to the induced residue-field algebra
automorphism. -/
@[simp]
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl

/-- Reducing the sum of the actual integral-closure Galois conjugates gives the
sum of the induced residue-field conjugates. -/
theorem galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      Finset.univ.sum fun σ : Gal(L/K) =>
        galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] a) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  simp [galoisGroupResidueAlgEquivOfIsIntegralClosure]

/-- The mathlib stabilizer action on the residue field, specialized to the
actual integral-closure action of `Gal(L / K)` on `𝒪[L]`. -/
def galoisGroupResidueStabilizerHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    @MulAction.stabilizer Gal(L/K) (Ideal 𝒪[L]) _
        (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
        (𝓂[L] : Ideal 𝒪[L]) →*
      (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L/K)

/-- The inertia subgroup for the actual integral-closure action on `𝒪[L]`. -/
def galoisGroupMaximalIdealInertiaOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Subgroup Gal(L/K) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact (𝓂[L] : Ideal 𝒪[L]).toAddSubgroup.inertia Gal(L/K)

/-- The actual residue action obtained through the maximal-ideal stabilizer. -/
def galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).comp
    (galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L)

/-- The stabilizer representation obtained from the Galois group agrees with the canonical residue
stabilizer map. -/
theorem galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure K L =
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L := by
  ext σ x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- A Galois automorphism acts trivially on the residue field exactly when its stabilizer image is
trivial. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L σ ∈
        (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker := by
  rw [← galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq K L]
  rfl

/-- The kernel of the residue stabilizer action is the maximal-ideal inertia subgroup. -/
theorem galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker =
      (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L).subgroupOf
        (@MulAction.stabilizer Gal(L/K) (Ideal 𝒪[L]) _
          (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
          (𝓂[L] : Ideal 𝒪[L])) := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  let := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.ker_stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L/K)

/-- A Galois automorphism acts trivially on the residue field exactly when it belongs to
maximal-ideal inertia. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      σ ∈ galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom]
  rw [galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  rfl

/-- The kernel of the residue-field Galois representation is the maximal-ideal inertia subgroup. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  ext σ
  exact galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    K L σ

/-- A Galois automorphism lies in the residue kernel exactly when every integer has the same residue
as its conjugate. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      ∀ x : 𝒪[L],
        IsLocalRing.residue 𝒪[L]
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
          IsLocalRing.residue 𝒪[L] x := by
  constructor
  · intro h x
    have hfun := congrArg (fun e : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      e (IsLocalRing.residue 𝒪[L] x)) h
    simpa [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply,
      galoisGroupResidueAlgEquivOfIsIntegralClosure,
      galoisGroupResidueFieldEquivOfIsIntegralClosure_residue] using hfun
  · intro h
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    change IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
      IsLocalRing.residue 𝒪[L] x
    exact h x

/-- A Galois automorphism lies in residue inertia exactly when each conjugate difference belongs to
the maximal ideal. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      ∀ x : 𝒪[L],
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈
          (𝓂[L] : Ideal 𝒪[L]) := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq K L σ]
  constructor
  · intro h x
    have hx0 : IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x) = 0 := by
      simpa using congrArg (fun z => z - IsLocalRing.residue 𝒪[L] x) (h x)
    exact (IsLocalRing.residue_eq_zero_iff
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x)).1 hx0
  · intro h x
    have hx0 : IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x)).2 (h x)
    have : IsLocalRing.residue 𝒪[L]
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) -
        IsLocalRing.residue 𝒪[L] x = 0 := by
      simpa using hx0
    exact sub_eq_zero.mp this

/-- The actual integral-closure inertia subgroup has cardinality equal to the
mathlib ramification index over the base maximal ideal. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[K] : Ideal 𝒪[K]).ramificationIdxIn 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    integerRing_moduleFinite_of_isIntegralClosure K L
  let : Algebra.IsSeparable (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))
      (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  let : Finite (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) := by
    change Finite 𝓀[K]
    infer_instance
  simpa [galoisGroupMaximalIdealInertiaOfIsIntegralClosure] using
    (Ideal.card_inertia_eq_ramificationIdxIn
      (R := 𝒪[K]) (S := 𝒪[L]) (G := Gal(L/K))
      (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]))

/-- The actual integral-closure inertia cardinality, rewritten with the
concrete ramification index of the valuation-integer-ring extension. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  rw [galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn K L]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) Gal(L/K)

/-- If the valuation-integer-ring extension has ramification index one, then
the actual integral-closure inertia subgroup has cardinality one. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_one_of_ramificationIdx_eq_one
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (h :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) = 1 := by
  rw [galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx K L, h]

/-- The kernel cardinality of the actual integral-closure residue action is the
ramification index over the base maximal ideal. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdxIn
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      (𝓂[K] : Ideal 𝒪[K]).ramificationIdxIn 𝒪[L] := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  exact galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn K L

/-- The kernel cardinality of the actual integral-closure residue action,
rewritten using the concrete ramification index. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  exact galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx K L

/-- If the valuation-integer-ring extension has ramification index one, then
the actual integral-closure residue action has kernel of cardinality one. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (h :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L, h]


end
end LocalFieldTheory
