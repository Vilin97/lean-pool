/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Permutation.LatticeHerbrand
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
/-!
# Galois actions on `S`-units and their logarithmic lattice

This file supplies the equivariant input for the `S`-unit calculation. A Galois
automorphism acts on finite places through its restriction to the ring of
integers, on infinite places by precomposition, and on field units in the
usual way.  For a stable finite set of finite places these actions restrict
to the actual `S`-unit group.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The permutation of finite places induced by a Galois automorphism. -/
noncomputable def finitePlaceEquiv
    (σ : L ≃ₐ[K] L) :
    HeightOneSpectrum (𝓞 L) ≃
      HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv

/-- Transport of ideals along a ring automorphism, as a multiplicative
equivalence. -/
noncomputable def idealMapMulEquiv
    {R : Type*} [CommRing R]
    (e : R ≃+* R) : Ideal R ≃* Ideal R where
  toFun I := I.map e
  invFun I := I.map e.symm
  left_inv _ := Ideal.map_of_equiv e
  right_inv _ := Ideal.map_of_equiv e.symm
  map_mul' I J := Ideal.map_mul e I J

@[simp]
theorem idealMapMulEquiv_apply
    {R : Type*} [CommRing R]
    (e : R ≃+* R) (I : Ideal R) :
    idealMapMulEquiv e I = I.map e :=
  rfl

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_asIdeal
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv K L σ v).asIdeal =
      v.asIdeal.map
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_one
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L (1 : L ≃ₐ[K] L) v = v := by
  apply HeightOneSpectrum.ext
  ext x
  change
    NumberField.RingOfIntegers.mapRingHom (1 : L ≃ₐ[K] L).symm.toRingHom x ∈
        v.asIdeal ↔
      x ∈ v.asIdeal
  have hx :
      NumberField.RingOfIntegers.mapRingHom (1 : L ≃ₐ[K] L).symm.toRingHom x =
        x := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_mul
    (σ τ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L (σ * τ) v =
      finitePlaceEquiv K L σ
        (finitePlaceEquiv K L τ v) := by
  apply HeightOneSpectrum.ext
  ext x
  change
    NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x ∈
        v.asIdeal ↔
      NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
          (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) ∈
        v.asIdeal
  have hx :
      NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x =
        NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
          (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_inv_apply
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L σ
        (finitePlaceEquiv K L σ⁻¹ v) = v := by
  rw [← finitePlaceEquiv_mul]
  simp

/-- The actual Galois action on finite places of `L`. -/
@[reducible]
noncomputable def finitePlaceMulAction :
    MulAction (L ≃ₐ[K] L)
      (HeightOneSpectrum (𝓞 L)) where
  smul σ v := finitePlaceEquiv K L σ v
  one_smul := finitePlaceEquiv_one K L
  mul_smul := finitePlaceEquiv_mul K L

omit [NumberField K] in
/-- The integral adic valuation is invariant under simultaneous transport
of the finite place and the integer. -/
theorem intValuation_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (r : 𝓞 L) :
    (finitePlaceEquiv K L σ v).intValuation
        (NumberField.RingOfIntegers.mapAlgEquiv σ r) =
      v.intValuation r := by
  let e := (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  by_cases hr : r = 0
  · subst r
    simp
  change
    (finitePlaceEquiv K L σ v).intValuation (e r) =
      v.intValuation r
  have her : e r ≠ 0 := by
    simpa using e.injective.ne hr
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity
      (finitePlaceEquiv K L σ v) her,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hr]
  congr 2
  have hspan :
      Ideal.span ({e r} : Set (𝓞 L)) =
        idealMapMulEquiv e (Ideal.span ({r} : Set (𝓞 L))) := by
    simp [idealMapMulEquiv, Ideal.map_span]
  rw [finitePlaceEquiv_asIdeal, hspan]
  norm_cast
  exact multiplicity_map_eq (idealMapMulEquiv e)
    (a := v.asIdeal) (b := Ideal.span ({r} : Set (𝓞 L)))

omit [NumberField K] in
/-- The field-valued adic valuation is invariant under simultaneous
transport of the finite place and the field element. -/
theorem valuation_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (x : L) :
    (finitePlaceEquiv K L σ v).valuation L (σ x) =
      v.valuation L x := by
  obtain ⟨r, d, hrd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 L)⁰ x
  rw [← hrd, IsFractionRing.mk'_eq_div, map_div₀,
    map_div₀, map_div₀]
  have hσr :
      σ ((algebraMap (𝓞 L) L) r) =
        (algebraMap (𝓞 L) L)
          (NumberField.RingOfIntegers.mapAlgEquiv σ r) :=
    rfl
  have hσd :
      σ ((algebraMap (𝓞 L) L) (d : 𝓞 L)) =
        (algebraMap (𝓞 L) L)
          (NumberField.RingOfIntegers.mapAlgEquiv σ (d : 𝓞 L)) :=
    rfl
  rw [hσr, hσd]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_finitePlaceEquiv, intValuation_finitePlaceEquiv]

/-- Absolute ideal norms are invariant under a ring automorphism. -/
theorem absNorm_map_ringEquiv
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Infinite R]
    (e : R ≃+* R) (I : Ideal R) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

private theorem toNNReal_apply_congr
    {e f : NNReal} (he : e ≠ 0) (hf : f ≠ 0)
    (hef : e = f) (q : WithZero (Multiplicative ℤ)) :
    ((WithZeroMulInt.toNNReal he q : NNReal) : ℝ) =
      ((WithZeroMulInt.toNNReal hf q : NNReal) : ℝ) := by
  subst f
  rfl

omit [NumberField K] in
/-- The normalized finite absolute value is invariant under simultaneous
transport of its finite place and its field element. -/
theorem adicAbv_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L
        (finitePlaceEquiv K L σ v) (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L v x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_finitePlaceEquiv]
  have hnorm :
      Ideal.absNorm (finitePlaceEquiv K L σ v).asIdeal =
        Ideal.absNorm v.asIdeal := by
    rw [finitePlaceEquiv_asIdeal, absNorm_map_ringEquiv]
  have hnorm_nnreal :
      (Ideal.absNorm
          (finitePlaceEquiv K L σ v).asIdeal : NNReal) =
        (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast hnorm
  exact toNNReal_apply_congr
    (NumberField.HeightOneSpectrum.absNorm_ne_zero
      (finitePlaceEquiv K L σ v))
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    hnorm_nnreal (v.valuation L x)

omit [NumberField K] [NumberField L] in
/-- Archimedean multiplicities are constant on Galois orbits. -/
@[simp]
theorem infinitePlace_mult_smul
    (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    (σ • w).mult = w.mult := by
  unfold NumberField.InfinitePlace.mult
  rw [NumberField.InfinitePlace.isReal_smul_iff]

/-- The usual action of the relative Galois group on field units. -/
@[reducible]
noncomputable def fieldUnitsMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) Lˣ where
  smul σ x := Units.mapEquiv σ.toMulEquiv x
  one_smul x := by
    ext
    rfl
  mul_smul σ τ x := by
    ext
    rfl
  smul_one σ := map_one (Units.mapEquiv σ.toMulEquiv)
  smul_mul σ x y := map_mul (Units.mapEquiv σ.toMulEquiv) x y

section FinitePlaceAction

local instance :
    MulAction (L ≃ₐ[K] L)
      (HeightOneSpectrum (𝓞 L)) :=
  finitePlaceMulAction K L

local instance :
    MulDistribMulAction (L ≃ₐ[K] L) Lˣ :=
  fieldUnitsMulDistribMulAction K L

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlace_smul_def
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    σ • v = finitePlaceEquiv K L σ v :=
  rfl

/-- A finite set of finite places is Galois-stable when it is invariant
under the concrete place permutation. -/
def IsGaloisStableFinitePlaces
    (S : Finset (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)),
      v ∈ S ↔ σ • v ∈ S

omit [NumberField K] [NumberField L] in
theorem IsGaloisStableFinitePlaces.smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 L)}
    (hv : v ∈ S) :
    σ • v ∈ S :=
  (hS σ v).mp hv

omit [NumberField K] [NumberField L] in
theorem IsGaloisStableFinitePlaces.smul_not_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 L)}
    (hv : v ∉ S) :
    σ • v ∉ S := by
  intro hmem
  exact hv ((hS σ v).mpr hmem)

omit [NumberField K] in
/-- Galois automorphisms preserve the concrete `S`-unit subgroup when
the finite-place set is stable. -/
theorem sUnit_smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L) (x : Lˣ)
    (hx : x ∈ SUnitGroup (K := L) S) :
    σ • x ∈ SUnitGroup (K := L) S := by
  intro v hv
  let w : HeightOneSpectrum (𝓞 L) := σ⁻¹ • v
  have hw : w ∉ S := by
    intro hwmem
    exact hv ((hS σ⁻¹ v).mpr hwmem)
  have hxw : w.valuation L (x : L) = 1 :=
    hx w hw
  have htransport :=
    valuation_finitePlaceEquiv K L σ w (x : L)
  have hvw : finitePlaceEquiv K L σ w = v := by
    change
      finitePlaceEquiv K L σ
          (finitePlaceEquiv K L σ⁻¹ v) = v
    rw [← finitePlaceEquiv_mul]
    simp
  rw [hvw] at htransport
  change v.valuation L (σ (x : L)) = 1
  exact htransport.trans hxw

/-- The actual Galois action on the `S`-unit group. -/
@[reducible]
noncomputable def sUnitMulDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup (K := L) S) :=
  stableSubgroupMulDistribMulAction
    (SUnitGroup (K := L) S)
    (sUnit_smul_mem K L hS)

omit [NumberField K] in
@[simp]
theorem sUnit_smul_coe
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : SUnitGroup (K := L) S) :
    letI := sUnitMulDistribMulAction K L S hS
    ((σ • x : SUnitGroup (K := L) S) : Lˣ) =
      Units.mapEquiv σ.toMulEquiv (x : Lˣ) :=
  rfl

/-- The action on the finite set `S` obtained by restricting the
finite-place permutation. -/
@[reducible]
noncomputable def stableFinitePlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulAction (L ≃ₐ[K] L) S where
  smul σ v :=
    ⟨σ • (v : HeightOneSpectrum (𝓞 L)),
      IsGaloisStableFinitePlaces.smul_mem K L hS σ
        v.property⟩
  one_smul v := by
    apply Subtype.ext
    exact one_smul _ (v : HeightOneSpectrum (𝓞 L))
  mul_smul σ τ v := by
    apply Subtype.ext
    exact mul_smul σ τ (v : HeightOneSpectrum (𝓞 L))

/-- The permutation action on all logarithmic places
`InfinitePlace L ⊕ S`. -/
@[reducible]
noncomputable def logPlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogPlace (K := L) S) := by
  letI : MulAction (L ≃ₐ[K] L) S :=
    stableFinitePlaceMulAction K L S hS
  exact
    { smul := fun σ p =>
        match p with
        | Sum.inl w => Sum.inl (σ • w)
        | Sum.inr v => Sum.inr (σ • v)
      one_smul := by
        intro p
        cases p with
        | inl w =>
            change Sum.inl ((1 : L ≃ₐ[K] L) • w) =
              Sum.inl w
            rw [one_smul]
        | inr v =>
            change Sum.inr ((1 : L ≃ₐ[K] L) • v) =
              Sum.inr v
            rw [one_smul]
      mul_smul := by
        intro σ τ p
        cases p with
        | inl w =>
            change Sum.inl ((σ * τ) • w) =
              Sum.inl (σ • (τ • w))
            rw [mul_smul]
        | inr v =>
            change Sum.inr ((σ * τ) • v) =
              Sum.inr (σ • (τ • v))
            rw [mul_smul] }

/-- The additive action on the additive form of the `S`-unit group. -/
@[reducible]
noncomputable def additiveSUnitDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (Additive (SUnitGroup (K := L) S)) := by
  letI := sUnitMulDistribMulAction K L S hS
  exact
    { smul := fun σ x =>
        Additive.ofMul
          (σ • (Additive.toMul x :
            SUnitGroup (K := L) S))
      one_smul := by
        intro x
        apply Additive.toMul.injective
        exact one_smul (L ≃ₐ[K] L) (Additive.toMul x :
          SUnitGroup (K := L) S)
      mul_smul := by
        intro σ τ x
        apply Additive.toMul.injective
        exact mul_smul σ τ (Additive.toMul x :
          SUnitGroup (K := L) S)
      smul_zero := by
        intro σ
        apply Additive.toMul.injective
        change σ • (1 : SUnitGroup (K := L) S) = 1
        exact MulDistribMulAction.smul_one σ
      smul_add := by
        intro σ x y
        apply Additive.toMul.injective
        exact MulDistribMulAction.smul_mul σ
          (Additive.toMul x : SUnitGroup (K := L) S)
          (Additive.toMul y : SUnitGroup (K := L) S) }

/-- The contragredient coordinate-permutation action on the full
logarithmic coordinate space. -/
@[reducible]
noncomputable def fullLogSpaceDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.FullLogSpace (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  exact
    { smul := fun σ z p => z (σ⁻¹ • p)
      one_smul := by
        intro z
        funext p
        change z ((1 : L ≃ₐ[K] L)⁻¹ • p) = z p
        rw [inv_one, one_smul]
      mul_smul := by
        intro σ τ z
        funext p
        change z ((σ * τ)⁻¹ • p) =
          z (τ⁻¹ • (σ⁻¹ • p))
        rw [mul_inv_rev, mul_smul]
      smul_zero := by
        intro σ
        rfl
      smul_add := by
        intro σ z z'
        rfl }

omit [NumberField K] [NumberField L] in
@[simp]
theorem fullLogSpace_smul_apply
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S)
    (p : SUnitGroup.LogPlace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    (σ • z) p = z (σ⁻¹ • p) :=
  rfl

/-- The permutation representation on the set of logarithmic places. -/
noncomputable def logPlacePermutationHom
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    (L ≃ₐ[K] L) →*
      Equiv.Perm (SUnitGroup.LogPlace (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  exact MulAction.toPermHom
    (L ≃ₐ[K] L) (SUnitGroup.LogPlace (K := L) S)

omit [NumberField K] [NumberField L] in
@[simp]
theorem logPlacePermutationHom_apply
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (p : SUnitGroup.LogPlace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    logPlacePermutationHom K L S hS σ p = σ • p :=
  rfl

omit [NumberField K] [NumberField L] in
/-- The concrete contragredient action is the coordinate permutation
representation associated to the action on logarithmic places. -/
theorem permutationRepresentation_logPlace
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    permutationRepresentation
        (logPlacePermutationHom K L S hS) σ z =
      σ • z := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  ext p
  rfl

omit [NumberField K] in
/-- Coordinate sum is invariant under the place permutation. -/
theorem coordinateSum_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    SUnitGroup.coordinateSum (K := L) S (σ • z) =
      SUnitGroup.coordinateSum (K := L) S z := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  change
    (∑ p : SUnitGroup.LogPlace (K := L) S,
      z (σ⁻¹ • p)) = ∑ p, z p
  exact
    Fintype.sum_equiv (MulAction.toPerm σ⁻¹)
      (fun p : SUnitGroup.LogPlace (K := L) S =>
        z (σ⁻¹ • p))
      z (fun _ => rfl)

/-- The constant vector whose coordinate sum is one. -/
noncomputable def normalizedLogDiagonal
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S :=
  fun _ =>
    (Fintype.card
      (SUnitGroup.LogPlace (K := L) S) : ℝ)⁻¹

@[simp]
theorem coordinateSum_normalizedLogDiagonal
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.coordinateSum (K := L) S
        (normalizedLogDiagonal L S) = 1 := by
  change
    (∑ _ : SUnitGroup.LogPlace (K := L) S,
      (Fintype.card
        (SUnitGroup.LogPlace (K := L) S) : ℝ)⁻¹) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀
    (by exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (SUnitGroup.LogPlace (K := L) S) ≠ 0))

/-- Splitting of the full coordinate space into the sum-zero
hyperplane and its coordinate sum. -/
noncomputable def fullLogSpaceSplit
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S →ₗ[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) where
  toFun z :=
    (⟨z -
        SUnitGroup.coordinateSum (K := L) S z •
          normalizedLogDiagonal L S, by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, map_smul,
        coordinateSum_normalizedLogDiagonal]
      simp⟩,
      SUnitGroup.coordinateSum (K := L) S z)
  map_add' z z' := by
    apply Prod.ext
    · ext p
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add,
        Prod.fst_add, Submodule.coe_add]
      module
    · exact map_add
        (SUnitGroup.coordinateSum (K := L) S) z z'
  map_smul' c z := by
    apply Prod.ext
    · ext p
      simp only [Pi.smul_apply, Pi.sub_apply, map_smul,
        Prod.smul_fst, RingHom.id_apply, Submodule.coe_smul]
      module
    · exact map_smul
        (SUnitGroup.coordinateSum (K := L) S) c z

theorem fullLogSpaceSplit_injective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Injective (fullLogSpaceSplit L S) := by
  intro z z' h
  have hfirst :
      z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S =
        z' -
          SUnitGroup.coordinateSum (K := L) S z' •
            normalizedLogDiagonal L S :=
    congrArg
      (fun q =>
        ((q.1 :
          SUnitGroup.LogHyperplane (K := L) S) :
            SUnitGroup.FullLogSpace (K := L) S)) h
  have hsecond :
      SUnitGroup.coordinateSum (K := L) S z =
        SUnitGroup.coordinateSum (K := L) S z' :=
    congrArg Prod.snd h
  calc
    z =
        (z -
            SUnitGroup.coordinateSum (K := L) S z •
              normalizedLogDiagonal L S) +
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S := by
              symm
              exact sub_add_cancel _ _
    _ =
        (z' -
            SUnitGroup.coordinateSum (K := L) S z' •
              normalizedLogDiagonal L S) +
          SUnitGroup.coordinateSum (K := L) S z' •
            normalizedLogDiagonal L S := by
              rw [hfirst, hsecond]
    _ = z' := sub_add_cancel _ _

theorem fullLogSpaceSplit_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective (fullLogSpaceSplit L S) := by
  intro q
  let z : SUnitGroup.FullLogSpace (K := L) S :=
    (q.1 : SUnitGroup.FullLogSpace (K := L) S) +
      q.2 • normalizedLogDiagonal L S
  refine ⟨z, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change
      z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S =
        (q.1 : SUnitGroup.FullLogSpace (K := L) S)
    have hq :
        SUnitGroup.coordinateSum (K := L) S
            (q.1 : SUnitGroup.FullLogSpace (K := L) S) = 0 :=
      LinearMap.mem_ker.mp q.1.property
    simp [z, hq, coordinateSum_normalizedLogDiagonal]
  · change
      SUnitGroup.coordinateSum (K := L) S z = q.2
    have hq :
        SUnitGroup.coordinateSum (K := L) S
            (q.1 : SUnitGroup.FullLogSpace (K := L) S) = 0 :=
      LinearMap.mem_ker.mp q.1.property
    simp [z, hq, coordinateSum_normalizedLogDiagonal]

/-- Linear coordinate splitting used to adjoin one invariant diagonal
direction to the logarithmic lattice. -/
noncomputable def fullLogSpaceEquivHyperplaneProd
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S ≃ₗ[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  LinearEquiv.ofBijective
    (fullLogSpaceSplit L S)
    ⟨fullLogSpaceSplit_injective L S,
      fullLogSpaceSplit_surjective L S⟩

/-- The coordinate splitting as a continuous linear equivalence. -/
noncomputable def fullLogSpaceContinuousEquivHyperplaneProd
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S ≃L[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  (fullLogSpaceEquivHyperplaneProd L S).toContinuousLinearEquiv

/-- A real basis of the logarithmic hyperplane obtained from an
integral basis of the complete logarithmic lattice. -/
noncomputable def fullLogLatticeRealBasis
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Basis
      (Module.Free.ChooseBasisIndex ℤ
        (SUnitGroup.fullLogLattice (K := L) S))
      ℝ (SUnitGroup.LogHyperplane (K := L) S) :=
  (Module.Free.chooseBasis ℤ
      (SUnitGroup.fullLogLattice (K := L) S)).ofZLatticeBasis
        ℝ (SUnitGroup.fullLogLattice (K := L) S)

/-- A basis of the product of the logarithmic hyperplane with the
one-dimensional diagonal direction. -/
noncomputable def fullLogHyperplaneDiagonalBasis
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Basis
      (Module.Free.ChooseBasisIndex ℤ
          (SUnitGroup.fullLogLattice (K := L) S) ⊕ Unit)
      ℝ (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  (fullLogLatticeRealBasis L S).prod (Basis.singleton Unit ℝ)

/-- The product lattice formed from the logarithmic lattice and one
integral diagonal direction. -/
noncomputable def fullLogHyperplaneDiagonalLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Submodule ℤ
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  Submodule.span ℤ
    (Set.range (fullLogHyperplaneDiagonalBasis L S))

/-- The complete lattice in the full logarithmic coordinate space
obtained by adjoining an integral invariant diagonal direction. -/
noncomputable def extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Submodule ℤ (SUnitGroup.FullLogSpace (K := L) S) :=
  ZLattice.comap ℝ
    (fullLogHyperplaneDiagonalLattice L S)
    (fullLogSpaceContinuousEquivHyperplaneProd L S).toLinearMap

instance instDiscreteTopology_extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    DiscreteTopology (extendedFullLogLattice L S) := by
  let : Module.Finite ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_finite ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let : Module.Free ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_free ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let :
      DiscreteTopology
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let e := fullLogSpaceContinuousEquivHyperplaneProd L S
  change
    DiscreteTopology
      (ZLattice.comap ℝ
        (fullLogHyperplaneDiagonalLattice L S)
        e.toLinearMap)
  exact
    ZLattice.comap_discreteTopology ℝ
      (fullLogHyperplaneDiagonalLattice L S)
      e.continuous e.injective

instance instIsZLattice_extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    IsZLattice ℝ (extendedFullLogLattice L S) := by
  let : Module.Finite ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_finite ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let : Module.Free ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_free ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let :
      DiscreteTopology
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let :
      IsZLattice ℝ
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let e := fullLogSpaceContinuousEquivHyperplaneProd L S
  change
    IsZLattice ℝ
      (ZLattice.comap ℝ
        (fullLogHyperplaneDiagonalLattice L S)
        e.toLinearMap)
  exact inferInstance

omit [NumberField K] in
/-- The normalized all-place logarithm is equivariant for the actual
`S`-unit and place-permutation actions. -/
theorem fullLogAmbient_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : Additive (SUnitGroup (K := L) S)) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    SUnitGroup.fullLogAmbient (K := L) S (σ • x) =
      σ • SUnitGroup.fullLogAmbient (K := L) S x := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let y : L :=
    (((Additive.toMul x :
      SUnitGroup (K := L) S) : Lˣ) : L)
  funext p
  cases p with
  | inl w =>
      change
        w.mult *
            Real.log (w (σ y)) =
          (σ⁻¹ • w).mult *
            Real.log ((σ⁻¹ • w) y)
      rw [infinitePlace_mult_smul]
      rfl
  | inr v =>
      change
        Real.log
            (NumberField.HeightOneSpectrum.adicAbv L
              (v : HeightOneSpectrum (𝓞 L))
              (σ y)) =
          Real.log
            (NumberField.HeightOneSpectrum.adicAbv L
              (finitePlaceEquiv K L σ⁻¹
                (v : HeightOneSpectrum (𝓞 L)))
              y)
      congr 1
      have h :=
        adicAbv_finitePlaceEquiv K L σ
          (finitePlaceEquiv K L σ⁻¹
            (v : HeightOneSpectrum (𝓞 L)))
          y
      simpa using h

/-- The coordinate-permutation action restricted to the
coordinate-sum-zero hyperplane. -/
@[reducible]
noncomputable def logHyperplaneDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogHyperplane (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  letI := fullLogSpaceDistribMulAction K L S hS
  exact
    { smul := fun σ z =>
        ⟨σ • (z :
            SUnitGroup.FullLogSpace (K := L) S), by
          apply LinearMap.mem_ker.mpr
          rw [coordinateSum_smul K L hS]
          exact LinearMap.mem_ker.mp z.property⟩
      one_smul := by
        intro z
        apply Subtype.ext
        exact one_smul (L ≃ₐ[K] L)
          (z : SUnitGroup.FullLogSpace (K := L) S)
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact mul_smul σ τ
          (z : SUnitGroup.FullLogSpace (K := L) S)
      smul_zero := by
        intro σ
        apply Subtype.ext
        exact DistribMulAction.smul_zero σ
      smul_add := by
        intro σ z z'
        apply Subtype.ext
        exact DistribMulAction.smul_add σ
          (z : SUnitGroup.FullLogSpace (K := L) S)
          (z' : SUnitGroup.FullLogSpace (K := L) S) }

omit [NumberField K] in
/-- Equivariance of the logarithmic map after restricting its codomain
to the coordinate-sum-zero hyperplane. -/
theorem fullLog_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : Additive (SUnitGroup (K := L) S)) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    SUnitGroup.fullLog (K := L) S (σ • x) =
      σ • SUnitGroup.fullLog (K := L) S x := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  apply Subtype.ext
  exact fullLogAmbient_smul K L hS σ x

/-- The kernel of `fullLog`, stated as an equality of additive
subgroups. -/
theorem fullLog_ker_eq_torsion
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (SUnitGroup.fullLog (K := L) S).ker =
      AddCommGroup.torsion
        (Additive (SUnitGroup (K := L) S)) := by
  ext x
  change
    SUnitGroup.fullLog (K := L) S x = 0 ↔
      x ∈ AddCommGroup.torsion
        (Additive (SUnitGroup (K := L) S))
  exact SUnitGroup.fullLog_eq_zero_iff (K := L) S x

/-- The first-isomorphism identification of `S`-units modulo torsion
with the actual logarithmic lattice. -/
noncomputable def
    additiveSUnitQuotientTorsionEquivFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (Additive (SUnitGroup (K := L) S) ⧸
        AddCommGroup.torsion
          (Additive (SUnitGroup (K := L) S))) ≃+
      SUnitGroup.fullLogLattice (K := L) S := by
  let f :=
    SUnitGroup.fullLog (K := L) S
  have hker :
      f.ker =
        AddCommGroup.torsion
          (Additive (SUnitGroup (K := L) S)) :=
    fullLog_ker_eq_torsion L S
  have hrange :
      f.range =
        (SUnitGroup.fullLogLattice
          (K := L) S).toAddSubgroup := by
    rw [SUnitGroup.fullLogLattice_eq_range]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  exact
    (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
      ((QuotientAddGroup.quotientKerEquivRange f).trans
        (AddEquiv.addSubgroupCongr hrange))

omit [NumberField K] in
/-- The complete logarithmic lattice is stable under the concrete
Galois action. -/
theorem fullLogLattice_smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.LogHyperplane (K := L) S)
    (hz : z ∈ SUnitGroup.fullLogLattice (K := L) S) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    σ • z ∈ SUnitGroup.fullLogLattice (K := L) S := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  rw [SUnitGroup.fullLogLattice_eq_range] at hz ⊢
  obtain ⟨x, hx⟩ := hz
  change SUnitGroup.fullLog (K := L) S x = z at hx
  refine ⟨σ • x, ?_⟩
  change
    SUnitGroup.fullLog (K := L) S (σ • x) = σ • z
  rw [fullLog_smul K L hS, hx]

omit [NumberField K] in
/-- Under the coordinate splitting, the hyperplane component transforms
by the restricted Galois action. -/
theorem fullLogSpaceSplit_fst_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    (fullLogSpaceSplit L S (σ • z)).1 =
      σ • (fullLogSpaceSplit L S z).1 := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  apply Subtype.ext
  change
    σ • z -
        SUnitGroup.coordinateSum (K := L) S (σ • z) •
          normalizedLogDiagonal L S =
      σ •
        (z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S)
  rw [coordinateSum_smul K L hS]
  ext p
  rfl

omit [NumberField K] in
/-- Under the coordinate splitting, the diagonal coordinate is
Galois-invariant. -/
theorem fullLogSpaceSplit_snd_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    (fullLogSpaceSplit L S (σ • z)).2 =
      (fullLogSpaceSplit L S z).2 := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  exact coordinateSum_smul K L hS σ z

omit [NumberField K] in
/-- The full logarithmic lattice with its adjoined diagonal direction is
stable under the place-permutation representation. -/
theorem extendedFullLogLattice_permutation_stable
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    ∀ (σ : L ≃ₐ[K] L)
      (z : SUnitGroup.FullLogSpace (K := L) S),
      z ∈ extendedFullLogLattice L S →
        permutationRepresentation
            (logPlacePermutationHom K L S hS) σ z ∈
          extendedFullLogLattice L S := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  intro σ z hz
  rw [permutationRepresentation_logPlace K L hS]
  change
    fullLogSpaceSplit L S z ∈
      fullLogHyperplaneDiagonalLattice L S at hz
  change
    fullLogSpaceSplit L S (σ • z) ∈
      fullLogHyperplaneDiagonalLattice L S
  let b :=
    fullLogHyperplaneDiagonalBasis L S
  have hzrepr :
      ∀ i, b.repr (fullLogSpaceSplit L S z) i ∈
        Set.range (algebraMap ℤ ℝ) := by
    apply (b.mem_span_iff_repr_mem ℤ _).mp
    exact hz
  apply (b.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  cases i with
  | inl j =>
      have hzfirst :
          (fullLogSpaceSplit L S z).1 ∈
            SUnitGroup.fullLogLattice (K := L) S := by
        rw [←
          (Module.Free.chooseBasis ℤ
            (SUnitGroup.fullLogLattice
              (K := L) S)).ofZLatticeBasis_span ℝ]
        apply
          ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
            ℤ _).mpr
        intro k
        simpa only [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inl] using hzrepr (Sum.inl k)
      have hstable :=
        fullLogLattice_smul_mem K L hS σ
          (fullLogSpaceSplit L S z).1 hzfirst
      have hspanstable :
          σ • (fullLogSpaceSplit L S z).1 ∈
            Submodule.span ℤ
              (Set.range (fullLogLatticeRealBasis L S)) := by
        simpa only [fullLogLatticeRealBasis,
          (Module.Free.chooseBasis ℤ
            (SUnitGroup.fullLogLattice
              (K := L) S)).ofZLatticeBasis_span ℝ] using hstable
      have hcoord :=
        ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
          ℤ _).mp hspanstable j
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inl,
        fullLogSpaceSplit_fst_smul K L hS] using hcoord
  | inr j =>
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inr,
        fullLogSpaceSplit_snd_smul K L hS] using
        hzrepr (Sum.inr j)

/-- The canonical complete permutation sublattice of the extended
logarithmic lattice has finite index. -/
theorem extendedFullLogPermutationSublattice_finite_quotient
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    Finite
      (extendedFullLogLattice L S ⧸
        (permutationSublattice
          (logPlacePermutationHom K L S hS)
          (extendedFullLogLattice L S)
          (extendedFullLogLattice_permutation_stable K L hS)).comap
            (extendedFullLogLattice L S).subtype) :=
  permutationSublattice_finite_quotient
    (logPlacePermutationHom K L S hS)
    (extendedFullLogLattice L S)
    (extendedFullLogLattice_permutation_stable K L hS)

/-- For the actual full logarithmic `S`-unit
lattice.  The Herbrand quotient is the product of the orders of the
stabilizers of the Galois orbits of logarithmic places. -/
theorem
    extendedFullLogLattice_herbrandQuotient_eq_stabilizerProduct
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _ambientAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _ambientMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S))
          _ _ _ _ σ h.1 h.2 =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) := by
  let ρ :=
    logPlacePermutationHom K L S hS
  exact
    completePermutationLattice_herbrandQuotient_eq_stabilizerProduct
      (G := L ≃ₐ[K] L)
      (ι := SUnitGroup.LogPlace (K := L) S)
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS) σ hgen

end FinitePlaceAction
