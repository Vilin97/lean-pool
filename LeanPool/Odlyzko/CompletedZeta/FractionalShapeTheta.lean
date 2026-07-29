/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeCovolume

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A fractional ideal element shape map used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealElementShapeMap
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    shapeIdealLattice K I q hq :=
  ⟨traceRadialScale K q hq (traceEmbedding K (x : K)),
    (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
      K I q hq _).2 x.prop⟩

open Classical in
theorem fractionalIdealElementShapeMap_bijective
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (fractionalIdealElementShapeMap K I q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (x : K) = traceEmbedding K (y : K) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm
            (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K x) = v
    simp_all

open Classical in
/-- A fractional ideal element shape equiv used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealElementShapeEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≃ shapeIdealLattice K I q hq :=
  Equiv.ofBijective (fractionalIdealElementShapeMap K I q hq)
    (fractionalIdealElementShapeMap_bijective K I q hq)

open Classical in
@[simp]
theorem fractionalIdealElementShapeEquiv_coe
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    ((fractionalIdealElementShapeEquiv K I q hq x :
        shapeIdealLattice K I q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq (traceEmbedding K (x : K)) :=
  rfl

variable [IsTotallyComplex K]

open Classical in
/-- A fractional shape ideal theta used in the Odlyzko-bound argument. -/
noncomputable def fractionalShapeIdealTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta (shapeIdealLattice K I q hq) Real.pi

open Classical in
theorem fractionalShapeIdealTheta_eq_tsum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K),
        complexPlaceGaussian K (x : K) q := by
  rw [fractionalShapeIdealTheta, latticeTheta,
    ← (fractionalIdealElementShapeEquiv K I q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [fractionalIdealElementShapeEquiv_coe,
    ← complexPlaceGaussian_eq_latticeGaussian]

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeIdealTheta_poissonSummation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      (Real.toNNReal
        (ZLattice.covolume (shapeIdealLattice K I q hq)))⁻¹ •
        fractionalShapeIdealTheta K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  rw [fractionalShapeIdealTheta,
    latticeGaussian_poissonSummation
      (shapeIdealLattice K I q hq) Real.pi_pos]
  have hpi : ((Real.pi : ℂ) / Real.pi) = 1 := by simp
  have hparam : Real.pi ^ 2 / Real.pi = Real.pi := by grind
  rw [hpi, one_cpow, one_mul, hparam,
    dualLatticeTheta_shapeIdealLattice]
  rfl

open Classical in
/-- A fractional ideal numerator used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealNumerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (Ideal (𝓞 K))⁰ :=
  ⟨(I : FractionalIdeal (𝓞 K)⁰ K).num,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun hnum ↦
      Units.ne_zero I
        (FractionalIdeal.num_eq_zero_iff.mp hnum)⟩

omit [IsTotallyComplex K] in
open Classical in
theorem mk0_fractionalIdealNumerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk0 (fractionalIdealNumerator K I) =
      ClassGroup.mk K I := by
  rw [← ClassGroup.mk_mk0 K]
  rw [← ClassGroup.mk_canonicalEquiv K (FractionRing (𝓞 K)) I]
  rw [← ClassGroup.mk_canonicalEquiv K (FractionRing (𝓞 K))
    (FractionalIdeal.mk0 K (fractionalIdealNumerator K I))]
  rw [FractionalIdeal.map_canonicalEquiv_mk0]
  symm
  apply ClassGroup.mk_eq_mk.mpr
  let d : (FractionRing (𝓞 K))ˣ := Units.mk0
    (algebraMap (𝓞 K) (FractionRing (𝓞 K))
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (I : FractionalIdeal (𝓞 K)⁰ K).den.prop)
  refine ⟨d, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal]
  simp only [d, Units.val_mk0]
  have h := congrArg
    (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
      (FractionRing (𝓞 K)))
    (FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K
      (I : FractionalIdeal (𝓞 K)⁰ K))
  rw [map_mul, FractionalIdeal.canonicalEquiv_spanSingleton] at h
  let m : K →+* FractionRing (𝓞 K) :=
    IsLocalization.map (M := (𝓞 K)⁰) (T := (𝓞 K)⁰)
      (FractionRing (𝓞 K)) (RingHom.id (𝓞 K))
      (by intro x hx; simpa using hx)
  have hm (r : 𝓞 K) :
      m (algebraMap (𝓞 K) K r) =
        algebraMap (𝓞 K) (FractionRing (𝓞 K)) r := by
    exact IsLocalization.map_eq (M := (𝓞 K)⁰) _ _
  change FractionalIdeal.spanSingleton (𝓞 K)⁰
      (m (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))) *
      (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K))) (I : FractionalIdeal (𝓞 K)⁰ K) =
      (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K)))
          ((I : FractionalIdeal (𝓞 K)⁰ K).num :
            FractionalIdeal (𝓞 K)⁰ K) at h
  rw [hm, FractionalIdeal.canonicalEquiv_coeIdeal] at h
  change
    (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K)))
        (I : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) (FractionRing (𝓞 K))
          ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) =
      ((I : FractionalIdeal (𝓞 K)⁰ K).num :
        FractionalIdeal (𝓞 K)⁰ (FractionRing (𝓞 K)))
  grind

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalIdeal_den_ne_zero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp
    (I : FractionalIdeal (𝓞 K)⁰ K).den.prop

open Classical in
/-- A numerator radii used in the Odlyzko-bound argument. -/
noncomputable def numeratorRadii
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ q w /
    w (algebraMap (𝓞 K) K
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))

omit [IsTotallyComplex K] in
open Classical in
theorem numeratorRadii_ne_zero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ∀ w, numeratorRadii K I q w ≠ 0 := by
  intro w
  apply div_ne_zero (hq w)
  simp

omit [IsTotallyComplex K] in
open Classical in
theorem complexPlaceGaussian_equivNum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    complexPlaceGaussian K (x : K) q =
      complexPlaceGaussian K
        (((FractionalIdeal.equivNum
          (fractionalIdeal_den_ne_zero K I) x :
            (I : FractionalIdeal (𝓞 K)⁰ K).num) : 𝓞 K) : K)
        (numeratorRadii K I q) := by
  rw [complexPlaceGaussian, complexPlaceGaussian]
  congr 1
  push_cast
  congr 2
  apply Finset.sum_congr rfl
  intro w _
  have heq :
      ((((FractionalIdeal.equivNum
        (fractionalIdeal_den_ne_zero K I) x :
          (I : FractionalIdeal (𝓞 K)⁰ K).num) : 𝓞 K) : K)) =
        algebraMap (𝓞 K) K
          ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K) * (x : K) := by
    calc
      _ = (I : FractionalIdeal (𝓞 K)⁰ K).den • (x : K) :=
        FractionalIdeal.equivNum_apply
          (fractionalIdeal_den_ne_zero K I) x
      _ = _ := rfl
  rw [heq]
  norm_cast
  change
    w (x : K) ^ 2 * q w ^ 2 =
      w ((algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) * (x : K)) ^ 2 *
        (q w /
          w (algebraMap (𝓞 K) K
            ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))) ^ 2
  rw [map_mul]
  have hd :
      w (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) ≠ 0 := by
    simp
  grind

open Classical in
theorem fractionalShapeIdealTheta_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      shapeIdealTheta K (fractionalIdealNumerator K I)
        (numeratorRadii K I q) (numeratorRadii_ne_zero K I q hq) := by
  rw [fractionalShapeIdealTheta_eq_tsum,
    shapeIdealTheta_eq_tsum]
  change
    (∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K),
      complexPlaceGaussian K (x : K) q) =
      ∑' x : (I : FractionalIdeal (𝓞 K)⁰ K).num,
        complexPlaceGaussian K (((x : 𝓞 K) : K))
          (numeratorRadii K I q)
  rw [← (FractionalIdeal.equivNum
    (fractionalIdeal_den_ne_zero K I)).toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  exact complexPlaceGaussian_equivNum K I q x

open Classical in
/-- A denominator log coordinates used in the Odlyzko-bound argument. -/
noncomputable def denominatorLogCoordinates
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.realSpace K :=
  mixedEmbedding.fundamentalCone.expMapBasis.symm
    (fun w ↦ w (algebraMap (𝓞 K) K
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)))

omit [IsTotallyComplex K] in
open Classical in
theorem expMapBasis_denominatorLogCoordinates
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      mixedEmbedding.fundamentalCone.expMapBasis
        (denominatorLogCoordinates K I) =
      fun w ↦ w (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) := by
  apply mixedEmbedding.fundamentalCone.expMapBasis.right_inv
  exact Set.mem_univ_pi.mpr fun w ↦
    InfinitePlace.pos_iff.mpr
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
        (fractionalIdeal_den_ne_zero K I))

omit [IsTotallyComplex K] in
open Classical in
theorem expMapBasis_add
    (x y : mixedEmbedding.realSpace K) :
    mixedEmbedding.fundamentalCone.expMapBasis (x + y) =
      mixedEmbedding.fundamentalCone.expMapBasis x *
        mixedEmbedding.fundamentalCone.expMapBasis y := by
  rw [mixedEmbedding.fundamentalCone.expMapBasis_apply,
    mixedEmbedding.fundamentalCone.expMapBasis_apply,
    mixedEmbedding.fundamentalCone.expMapBasis_apply]
  rw [map_add]
  exact mixedEmbedding.fundamentalCone.expMap_add _ _

open Classical in
theorem numeratorRadii_expMapBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    numeratorRadii K I
        (mixedEmbedding.fundamentalCone.expMapBasis y) =
      mixedEmbedding.fundamentalCone.expMapBasis
        (y - denominatorLogCoordinates K I) := by
  rw [sub_eq_add_neg, expMapBasis_add]
  funext w
  rw [Pi.mul_apply, expMapBasis_neg,
    expMapBasis_denominatorLogCoordinates]
  rfl

open Classical in
theorem fractionalShapeIdealTheta_expMapBasis_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    fractionalShapeIdealTheta K I
        (mixedEmbedding.fundamentalCone.expMapBasis y)
        (fun w ↦ (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).ne') =
      shapeIdealTheta K (fractionalIdealNumerator K I)
        (mixedEmbedding.fundamentalCone.expMapBasis
          (y - denominatorLogCoordinates K I))
        (fun w ↦
          (mixedEmbedding.fundamentalCone.expMapBasis_pos
            (y - denominatorLogCoordinates K I) w).ne') := by
  rw [fractionalShapeIdealTheta_eq_numerator,
    shapeIdealTheta_eq_tsum, shapeIdealTheta_eq_tsum]
  have hq :
      numeratorRadii K I
          (mixedEmbedding.fundamentalCone.expMapBasis y) =
        mixedEmbedding.fundamentalCone.expMapBasis
          (y - denominatorLogCoordinates K I) :=
    numeratorRadii_expMapBasis K I y
  simp_all

end NumberField.Odlyzko
