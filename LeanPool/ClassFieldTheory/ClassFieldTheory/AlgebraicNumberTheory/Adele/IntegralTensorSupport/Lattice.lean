/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
/-!
# Integral lattices in relative tensor coordinates

This module chooses a common integral scale for a field basis, constructs the
associated integer lattice, and isolates the finite set of primes where its
local integrality properties can fail.
-/

@[expose] public section

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] in
/-- One common nonzero integer scales every vector of the chosen
`K`-basis into the ring of integers of `L`. -/
theorem exists_integral_relativeBasis_scale :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral ℤ
          (d • relativeExtensionBasis
            (K := K) (L := L) i) := by
  classical
  let : Algebra.IsAlgebraic ℤ L :=
    (IsFractionRing.isAlgebraic_iff' ℤ (𝓞 L) L).mp
      inferInstance
  let s : Finset L :=
    Finset.univ.image fun i :
      RelativeAdeleBasisIndex (K := K) (L := L) =>
        relativeExtensionBasis (K := K) (L := L) i
  obtain ⟨d, hd, hint⟩ :=
    Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d, hd, ?_⟩
  intro i
  exact
    hint
      (relativeExtensionBasis (K := K) (L := L) i)
      (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)

/-- The chosen common integral scale. -/
noncomputable def chosenRelativeBasisIntegralScale : ℤ :=
  Classical.choose
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))

omit [NumberField K] in
/-- The chosen integral scale is nonzero. -/
theorem chosenRelativeBasisIntegralScale_ne_zero :
    chosenRelativeBasisIntegralScale (K := K) (L := L) ≠ 0 :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).1

omit [NumberField K] in
/-- The chosen integral scale is integral in the base field. -/
theorem chosenRelativeBasisIntegralScale_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (chosenRelativeBasisIntegralScale (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i) :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).2 i

/-- The integral scale viewed in the base field. -/
noncomputable def relativeBasisIntegralScaleInK : K :=
  algebraMap ℤ K
    (chosenRelativeBasisIntegralScale (K := K) (L := L))

/-- The base-field coercion of the chosen integral scale is nonzero. -/
theorem relativeBasisIntegralScaleInK_ne_zero :
    relativeBasisIntegralScaleInK (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : K) =
        ((0 : ℤ) : K) := by
    simpa [relativeBasisIntegralScaleInK] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)

/-- The integral scale as a unit of `K`. -/
noncomputable def relativeBasisIntegralScaleUnit : Kˣ :=
  Units.mk0
    (relativeBasisIntegralScaleInK (K := K) (L := L))
    (relativeBasisIntegralScaleInK_ne_zero
      (K := K) (L := L))

/-- The chosen basis after multiplying every vector by the common
integral scale. -/
noncomputable def scaledRelativeExtensionBasis :
    Module.Basis
      (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  (relativeExtensionBasis (K := K) (L := L)).unitsSMul
    fun _ => relativeBasisIntegralScaleUnit
      (K := K) (L := L)

/-- Evaluation and integrality properties of the scaled relative basis. -/
@[simp]
theorem scaledRelativeExtensionBasis_apply
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    scaledRelativeExtensionBasis (K := K) (L := L) i =
      relativeBasisIntegralScaleInK
          (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i := by
  rw [scaledRelativeExtensionBasis,
    Module.Basis.unitsSMul_apply]
  rfl

/-- Every vector of the scaled relative basis is integral. -/
theorem scaledRelativeExtensionBasis_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) := by
  simpa [scaledRelativeExtensionBasis_apply,
    relativeBasisIntegralScaleInK, Algebra.smul_def] using
      chosenRelativeBasisIntegralScale_isIntegral
        (K := K) (L := L) i

/-- Every scaled basis vector belongs to the valuation ring of every
nonarchimedean extension of an absolute value of `K`. -/
theorem scaledRelativeExtensionBasis_absoluteValue_le_one
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 :=
  absoluteValue_le_one_of_isIntegral
    wL.1
    (absoluteValueExtension_isNonarchimedean
      vK hvK wL)
    (scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i)

/-- The scaled basis vector as an actual element of `𝓞 L`. -/
noncomputable def scaledRelativeExtensionInteger
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    𝓞 L :=
  ⟨scaledRelativeExtensionBasis (K := K) (L := L) i,
    scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i⟩

/-- The named scaled integer is the corresponding scaled basis vector. -/
@[simp]
theorem scaledRelativeExtensionInteger_coe
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (scaledRelativeExtensionInteger
        (K := K) (L := L) i : L) =
      scaledRelativeExtensionBasis (K := K) (L := L) i :=
  rfl

/-- The `𝓞 K`-lattice in `𝓞 L` generated by the scaled basis. -/
noncomputable def scaledRelativeIntegerLattice :
    Submodule (𝓞 K) (𝓞 L) :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionInteger
        (K := K) (L := L)))

/-- The same scaled lattice, viewed inside the field `L`. -/
noncomputable def scaledRelativeFieldLattice :
    Submodule (𝓞 K) L :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L)))

/-- The canonical `𝓞 K`-linear inclusion `𝓞 L → L`. -/
noncomputable def ringOfIntegersToFieldLinearMap :
    𝓞 L →ₗ[𝓞 K] L :=
  (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap

/-- Mapping the integral lattice into `L` gives the field-valued
lattice spanned by the scaled basis. -/
theorem scaledRelativeIntegerLattice_map_toField :
    (scaledRelativeIntegerLattice
      (K := K) (L := L)).map
        (ringOfIntegersToFieldLinearMap
          (K := K) (L := L)) =
      scaledRelativeFieldLattice
        (K := K) (L := L) := by
  rw [scaledRelativeIntegerLattice,
    scaledRelativeFieldLattice,
    Submodule.map_span]
  congr 1
  exact
    (Set.range_comp
      (ringOfIntegersToFieldLinearMap (K := K) (L := L))
      (scaledRelativeExtensionInteger (K := K) (L := L))).symm

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The inclusion `𝓞 L → L` used above is injective. -/
theorem ringOfIntegersToFieldLinearMap_injective :
    Function.Injective
      (ringOfIntegersToFieldLinearMap
        (K := K) (L := L)) := by
  intro x y h
  exact NumberField.RingOfIntegers.ext h

/-- Every algebraic integer becomes a member of the scaled lattice
after multiplication by some non-zero-divisor of `𝓞 K`.  This is the
direct denominator-clearing statement behind torsion of the lattice
quotient. -/
theorem exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
    (x : 𝓞 L) :
    ∃ d : nonZeroDivisors (𝓞 K),
      (d : 𝓞 K) • x ∈
        scaledRelativeIntegerLattice
          (K := K) (L := L) := by
  let s : Set L :=
    Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L))
  have hx :
      (x : L) ∈ Submodule.span K s := by
    change
      (x : L) ∈
        Submodule.span K
          (Set.range
            (scaledRelativeExtensionBasis
              (K := K) (L := L)))
    rw [(scaledRelativeExtensionBasis
      (K := K) (L := L)).span_eq]
    exact Submodule.mem_top
  obtain ⟨d, hd⟩ :=
    multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (𝓞 K)) K s (x : L) hx
  refine ⟨d, ?_⟩
  have hdmap :
      d • (x : L) ∈
        (scaledRelativeIntegerLattice
          (K := K) (L := L)).map
            (ringOfIntegersToFieldLinearMap
              (K := K) (L := L)) := by
    rw [scaledRelativeIntegerLattice_map_toField
      (K := K) (L := L)]
    exact hd
  obtain ⟨y, hy, hyx⟩ := hdmap
  have hyx' : y = (d : 𝓞 K) • x := by
    apply ringOfIntegersToFieldLinearMap_injective
      (K := K) (L := L)
    simpa [ringOfIntegersToFieldLinearMap,
      Submonoid.smul_def] using hyx
  rw [← hyx']
  exact hy

/-- The finite quotient measuring the index of the scaled basis
lattice in `𝓞 L`. -/
abbrev ScaledRelativeIntegerLatticeQuotient :=
  (𝓞 L) ⧸
    scaledRelativeIntegerLattice
      (K := K) (L := L)

/-- The lattice quotient is finitely generated over `𝓞 K`. -/
noncomputable instance
    scaledRelativeIntegerLatticeQuotientFinite :
    Module.Finite (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) :=
  Module.Finite.quotient (𝓞 K)
    (scaledRelativeIntegerLattice
      (K := K) (L := L))

/-- The lattice quotient is torsion. -/
theorem scaledRelativeIntegerLatticeQuotient_isTorsion :
    Module.IsTorsion (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) := by
  intro q
  refine
    Submodule.Quotient.induction_on
      (p := scaledRelativeIntegerLattice
        (K := K) (L := L)) q ?_
  intro x
  obtain ⟨d, hd⟩ :=
    exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
      (K := K) (L := L) x
  refine ⟨d, ?_⟩
  rw [Submonoid.smul_def,
    ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact hd

/-- A chosen nonzero element of the annihilator of the finite lattice
quotient. -/
noncomputable def chosenScaledRelativeIntegerLatticeAnnihilatorData :
    { r : 𝓞 K //
      r ∈
          (⊤ : Submodule (𝓞 K)
            (ScaledRelativeIntegerLatticeQuotient
              (K := K) (L := L))).annihilator ∧
        r ∈ nonZeroDivisors (𝓞 K) } := by
  let h :=
    Submodule.annihilator_top_inter_nonZeroDivisors
      (scaledRelativeIntegerLatticeQuotient_isTorsion
        (K := K) (L := L))
  exact
    ⟨Classical.choose h,
      (Classical.choose_spec h).1,
      (Classical.choose_spec h).2⟩

/-- The chosen annihilator element in `𝓞 K`. -/
noncomputable def scaledRelativeIntegerLatticeAnnihilator :
    𝓞 K :=
  (chosenScaledRelativeIntegerLatticeAnnihilatorData
    (K := K) (L := L) : 𝓞 K)

/-- The selected annihilator element lies in the annihilator ideal. -/
theorem scaledRelativeIntegerLatticeAnnihilator_mem :
    scaledRelativeIntegerLatticeAnnihilator
        (K := K) (L := L) ∈
      (⊤ : Submodule (𝓞 K)
        (ScaledRelativeIntegerLatticeQuotient
          (K := K) (L := L))).annihilator :=
  (chosenScaledRelativeIntegerLatticeAnnihilatorData
    (K := K) (L := L)).2.1

/-- The selected annihilator element is nonzero. -/
theorem scaledRelativeIntegerLatticeAnnihilator_ne_zero :
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L) ≠ 0 :=
  nonZeroDivisors.ne_zero
    (chosenScaledRelativeIntegerLatticeAnnihilatorData
      (K := K) (L := L)).2.2

/-- The chosen annihilator uniformly carries all of `𝓞 L` into the
scaled basis lattice. -/
theorem scaledRelativeIntegerLatticeAnnihilator_smul_mem
    (x : 𝓞 L) :
    scaledRelativeIntegerLatticeAnnihilator
          (K := K) (L := L) • x ∈
      scaledRelativeIntegerLattice
        (K := K) (L := L) := by
  have hkill :
      scaledRelativeIntegerLatticeAnnihilator
          (K := K) (L := L) •
          Submodule.Quotient.mk x = 0 :=
    Submodule.mem_annihilator.mp
      (scaledRelativeIntegerLatticeAnnihilator_mem
        (K := K) (L := L))
      (Submodule.Quotient.mk x) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at hkill
  exact hkill

/-- The original integral scaling factor, now viewed in `𝓞 K`. -/
noncomputable def relativeBasisIntegralScaleInRingOfIntegers :
    𝓞 K :=
  algebraMap ℤ (𝓞 K)
    (chosenRelativeBasisIntegralScale (K := K) (L := L))

/-- The integral scale remains nonzero in the ring of integers. -/
theorem relativeBasisIntegralScaleInRingOfIntegers_ne_zero :
    relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : 𝓞 K) =
        ((0 : ℤ) : 𝓞 K) := by
    simpa [relativeBasisIntegralScaleInRingOfIntegers] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)

/-- One nonzero element controlling both the initial basis scaling and
the finite index of the resulting lattice. -/
noncomputable def integralTensorControlElement :
    𝓞 K :=
  relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) *
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L)

/-- The tensor control element is nonzero. -/
theorem integralTensorControlElement_ne_zero :
    integralTensorControlElement
      (K := K) (L := L) ≠ 0 :=
  mul_ne_zero
    (relativeBasisIntegralScaleInRingOfIntegers_ne_zero
      (K := K) (L := L))
    (scaledRelativeIntegerLatticeAnnihilator_ne_zero
      (K := K) (L := L))

/-- The nonzero principal ideal defining the bad primes. -/
noncomputable def integralTensorControlIdeal :
    Ideal (𝓞 K) :=
  Ideal.span
    ({integralTensorControlElement
      (K := K) (L := L)} : Set (𝓞 K))

/-- The tensor control ideal is nontrivial. -/
theorem integralTensorControlIdeal_ne_bot :
    integralTensorControlIdeal
      (K := K) (L := L) ≠ ⊥ := by
  rw [integralTensorControlIdeal,
    ne_eq, Ideal.span_singleton_eq_bot]
  exact integralTensorControlElement_ne_zero
    (K := K) (L := L)

/-- The actual finite set of primes at which either the basis scaling
or the lattice index can fail to be invertible. -/
noncomputable def integralTensorBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (integralTensorControlIdeal_ne_bot
      (K := K) (L := L))).toFinset

/-- Membership in the finite bad-place set is ideal membership. -/
@[simp]
theorem mem_integralTensorBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ integralTensorBadPlaces
        (K := K) (L := L) ↔
      w.asIdeal ∣
        integralTensorControlIdeal
          (K := K) (L := L) :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (integralTensorControlIdeal_ne_bot
        (K := K) (L := L)))

/-- Outside the bad set the common control element is not in the
corresponding height-one prime. -/
theorem integralTensorControlElement_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    integralTensorControlElement
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  apply hw
  rw [mem_integralTensorBadPlaces_iff,
    integralTensorControlIdeal,
    Ideal.dvd_span_singleton]
  exact hmem

/-- The annihilator alone is invertible away from the bad set. -/
theorem scaledRelativeIntegerLatticeAnnihilator_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    scaledRelativeIntegerLatticeAnnihilator
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  exact
    integralTensorControlElement_not_mem_of_notMem
      (K := K) (L := L) w hw
      (w.asIdeal.mul_mem_left
        (relativeBasisIntegralScaleInRingOfIntegers
          (K := K) (L := L)) hmem)

/-- The initial integer scale is also invertible away from the bad
set. -/
theorem relativeBasisIntegralScale_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  exact
    integralTensorControlElement_not_mem_of_notMem
      (K := K) (L := L) w hw
      (w.asIdeal.mul_mem_right
        (scaledRelativeIntegerLatticeAnnihilator
          (K := K) (L := L)) hmem)

/-- Away from the bad set, the original (unscaled) relative basis is
integral for every extension of the corresponding finite absolute
value to `L`. -/
theorem relativeExtensionBasis_absoluteValue_le_one_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (relativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  have hdnot :
      relativeBasisIntegralScaleInRingOfIntegers
          (K := K) (L := L) ∉ w.asIdeal :=
    relativeBasisIntegralScale_not_mem_of_notMem
      (K := K) (L := L) w hw
  have hnorm :
      ‖FinitePlace.embedding w
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)))‖ = 1 :=
    (FinitePlace.norm_eq_one_iff_notMem
      (R := 𝓞 K) K w
      (relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L))).2 hdnot
  have hvscaleInteger :
      vK
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L))) = 1 := by
    simpa [vK, FinitePlace.norm_embedding] using hnorm
  have hscaleField :
      relativeBasisIntegralScaleInK
          (K := K) (L := L) =
        algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)) := by
    simp [relativeBasisIntegralScaleInK,
      relativeBasisIntegralScaleInRingOfIntegers]
  have hvscale :
      vK
        (relativeBasisIntegralScaleInK
          (K := K) (L := L)) = 1 := by
    rw [hscaleField]
    exact hvscaleInteger
  have hwscale :
      wL.1
        (algebraMap K L
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))) = 1 := by
    rw [wL.2]
    exact hvscale
  have hscaled :=
    scaledRelativeExtensionBasis_absoluteValue_le_one
      (K := K) (L := L) vK
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
        K w) wL i
  rw [scaledRelativeExtensionBasis_apply,
    Algebra.smul_def, map_mul, hwscale, one_mul] at hscaled
  exact hscaled
