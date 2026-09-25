/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.FiniteNormArithmetic
/-!
# Scalar-extension behavior of idele norms

Scalar extension raises the finite, archimedean, and absolute idele norms to
the degree of the number-field extension. The rational relative-idele
base-change realization is included as the endpoint used by cyclotomic
reciprocity.
-/

@[expose] public section

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable
section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

omit [NumberField L] in
open scoped Classical in
private theorem infinitePlaceCompletionMap_isometry
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    [W.1.LiesOver v₀.1] :
    Isometry
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W)) := by
  unfold NumberField.LiesOver.completionMap
  exact
    (InfinitePlace.Completion.isometryEquivCompletion W).symm.isometry.comp
      ((UniformSpace.Completion.isometry_mapRingHom
          (InfinitePlace.LiesOver.isometry_algebraMap W v₀)).comp
        (InfinitePlace.Completion.isometryEquivCompletion v₀).isometry)

omit [NumberField L] in
open scoped Classical in
/-- Mapping a unit along an infinite-place completion map preserves its
positive norm. -/
private theorem nnnormUnitHom_infinitePlaceCompletionMap
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    [W.1.LiesOver v₀.1]
    (x : v₀.Completionˣ) :
    nnnormUnitHom W.Completion
        (Units.map
          (NumberField.LiesOver.completionMap
            (v := v₀) (w := W)) x) =
      nnnormUnitHom v₀.Completion x := by
  apply Units.ext
  change
    ‖NumberField.LiesOver.completionMap
        (v := v₀) (w := W) (x : v₀.Completion)‖₊ =
      ‖(x : v₀.Completion)‖₊
  apply NNReal.eq
  exact
    (infinitePlaceCompletionMap_isometry
      (K := K) (L := L) v₀ W).norm_map_of_map_zero
      (map_zero
        (NumberField.LiesOver.completionMap
          (v := v₀) (w := W)))
      (x : v₀.Completion)

open scoped Classical in
/-- The fiber of restriction of infinite places is the set of places
lying over the chosen base place. -/
private noncomputable def infinitePlaceFiberEquivPlacesOver
    (v₀ : InfinitePlace K) :
    {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀} ≃
      {W : InfinitePlace L // W ∈ v₀.placesOver L} where
  toFun W :=
    ⟨W.1, ⟨congrArg (fun v : InfinitePlace K => v.1) W.2⟩⟩
  invFun W :=
    ⟨W.1, by
      change W.1.comap (algebraMap K L) = v₀
      let : W.1.1.LiesOver v₀.1 := W.2
      exact InfinitePlace.LiesOver.comap_eq W.1 v₀⟩
  left_inv W := Subtype.ext rfl
  right_inv W := Subtype.ext rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
open scoped Classical in
/-- The archimedean multiplicity upstairs is the base multiplicity
times the local inertia degree. -/
private theorem infinitePlace_mult_eq_base_mult_mul_inertiaDeg
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    (hW : W ∈ v₀.placesOver L) :
    W.mult = v₀.mult * v₀.inertiaDeg W := by
  let : W.1.LiesOver v₀.1 := hW
  rcases v₀.isReal_or_isComplex with hvReal | hvComplex
  · rcases W.isReal_or_isComplex with hWReal | hWComplex
    · have hUnramified : W.IsUnramified K :=
        InfinitePlace.isUnramified_iff.mpr (Or.inl hWReal)
      rw [InfinitePlace.mult_isReal ⟨W, hWReal⟩,
        InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.inertiaDeg_eq_one
          ⟨hW, hUnramified⟩]
    · have hComapReal :
          (W.comap (algebraMap K L)).IsReal := by
        rw [InfinitePlace.LiesOver.comap_eq W v₀]
        exact hvReal
      have hRamified : W.IsRamified K :=
        InfinitePlace.isRamified_iff.mpr
          ⟨hWComplex, hComapReal⟩
      rw [InfinitePlace.mult_isComplex ⟨W, hWComplex⟩,
        InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.inertiaDeg_eq_two
          ⟨hW, hRamified⟩]
  · have hWComplex :
        W.IsComplex :=
      InfinitePlace.LiesOver.isComplex_of_isComplex_under
        W hvComplex
    have hComapComplex :
        (W.comap (algebraMap K L)).IsComplex := by
      rw [InfinitePlace.LiesOver.comap_eq W v₀]
      exact hvComplex
    have hUnramified : W.IsUnramified K :=
      InfinitePlace.isUnramified_iff.mpr
        (Or.inr hComapComplex)
    rw [InfinitePlace.mult_isComplex ⟨W, hWComplex⟩,
      InfinitePlace.mult_isComplex ⟨v₀, hvComplex⟩,
      InfinitePlace.inertiaDeg_eq_one
        ⟨hW, hUnramified⟩]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The inertia degrees in a restriction fiber sum to the global
extension degree. -/
private theorem infinitePlaceFiber_inertiaDeg_sum
    (v₀ : InfinitePlace K) :
    ∑ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
      v₀.inertiaDeg W.1 =
        Module.finrank K L := by
  classical
  calc
    (∑ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        v₀.inertiaDeg W.1) =
        ∑ W : {W : InfinitePlace L //
            W ∈ v₀.placesOver L},
          v₀.inertiaDeg W.1 :=
      Fintype.sum_equiv
        (infinitePlaceFiberEquivPlacesOver
          (K := K) (L := L) v₀)
        (fun W => v₀.inertiaDeg W.1)
        (fun W => v₀.inertiaDeg W.1)
        (fun _ => rfl)
    _ =
        ∑ W ∈ v₀.placesOver L,
          v₀.inertiaDeg W := by
      symm
      apply Finset.sum_subtype
      intro W
      simp
    _ = Module.finrank K L := by
      exact
        InfinitePlace.sum_inertiaDeg_eq_finrank
          K L v₀

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The total archimedean multiplicity in a restriction fiber is the
base multiplicity times the extension degree. -/
private theorem infinitePlaceFiber_mult_sum
    (v₀ : InfinitePlace K) :
    ∑ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.mult =
        v₀.mult * Module.finrank K L := by
  classical
  calc
    (∑ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        W.1.mult) =
        ∑ W : {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀},
          v₀.mult * v₀.inertiaDeg W.1 := by
      apply Finset.sum_congr rfl
      intro W _
      exact
        infinitePlace_mult_eq_base_mult_mul_inertiaDeg
          (K := K) (L := L) v₀ W.1
          ⟨congrArg (fun v : InfinitePlace K => v.1) W.2⟩
    _ =
        v₀.mult *
          ∑ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            v₀.inertiaDeg W.1 := by
      rw [Finset.mul_sum]
    _ = v₀.mult * Module.finrank K L := by
      rw [infinitePlaceFiber_inertiaDeg_sum
        (K := K) (L := L) v₀]

open scoped Classical in
/-- Scalar extension raises the archimedean idele norm to the degree of
the extension. -/
theorem archimedeanNorm_extension
    (a : IdeleGroup K) :
    InfiniteIdeleGroup.archimedeanNorm
        (extension K L a).1 =
      InfiniteIdeleGroup.archimedeanNorm a.1 ^
        Module.finrank K L := by
  classical
  have hlocal (W : InfinitePlace L) :
      nnnormUnitHom W.Completion
          (infiniteComponent W (extension K L a)) =
        nnnormUnitHom
          (_root_.infinitePlaceBelow (K := K) W).Completion
          (infiniteComponent
            (_root_.infinitePlaceBelow (K := K) W) a) := by
    let v₀ := _root_.infinitePlaceBelow (K := K) W
    let : W.1.LiesOver v₀.1 := ⟨rfl⟩
    rw [extension_infiniteComponent K L a W]
    exact
      nnnormUnitHom_infinitePlaceCompletionMap
        (K := K) (L := L) v₀ W
        (infiniteComponent v₀ a)
  rw [InfiniteIdeleGroup.archimedeanNorm_apply,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  change
    (∏ W : InfinitePlace L,
        nnnormUnitHom W.Completion
          (infiniteComponent W (extension K L a)) ^ W.mult) =
      (∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a) ^ v₀.mult) ^
        Module.finrank K L
  simp_rw [hlocal]
  calc
    (∏ W : InfinitePlace L,
        nnnormUnitHom
            (_root_.infinitePlaceBelow (K := K) W).Completion
            (infiniteComponent
              (_root_.infinitePlaceBelow (K := K) W) a) ^
          W.mult) =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom
                (_root_.infinitePlaceBelow
                  (K := K) W.1).Completion
                (infiniteComponent
                  (_root_.infinitePlaceBelow
                    (K := K) W.1) a) ^
              W.1.mult :=
      (Fintype.prod_fiberwise
        (_root_.infinitePlaceBelow (K := K))
        (fun W : InfinitePlace L =>
          nnnormUnitHom
              (_root_.infinitePlaceBelow (K := K) W).Completion
              (infiniteComponent
                (_root_.infinitePlaceBelow (K := K) W) a) ^
            W.mult)).symm
    _ =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom v₀.Completion
                (infiniteComponent v₀ a) ^
              W.1.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      apply Finset.prod_congr rfl
      intro W _
      rw [W.2]
    _ =
        ∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^
            (∑ W : {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀},
              W.1.mult) := by
      apply Finset.prod_congr rfl
      intro v₀ _
      exact
        Finset.prod_pow_eq_pow_sum
          Finset.univ
          (fun W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀} =>
            W.1.mult)
          (nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a))
    _ =
        ∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^
            (v₀.mult * Module.finrank K L) := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [infinitePlaceFiber_mult_sum
        (K := K) (L := L) v₀]
    _ =
        ∏ v₀ : InfinitePlace K,
          (nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^ v₀.mult) ^
            Module.finrank K L := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [pow_mul]
    _ =
        (∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a) ^ v₀.mult) ^
          Module.finrank K L := by
      exact
        Finset.prod_pow
          Finset.univ
          (Module.finrank K L)
          (fun v₀ : InfinitePlace K =>
            nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^ v₀.mult)

open scoped Classical in
/-- Scalar extension raises the absolute idele norm to the degree of the
number-field extension. -/
theorem absoluteNorm_extension
    (a : IdeleGroup K) :
    absoluteNorm (extension K L a) =
      absoluteNorm a ^ Module.finrank K L := by
  rw [absoluteNorm_apply, absoluteNorm_apply,
    finiteAbsoluteNorm_extension,
    archimedeanNorm_extension]
  calc
    FiniteIdeleGroup.absoluteNorm a.2 ^ Module.finrank K L *
          (InfiniteIdeleGroup.archimedeanNorm a.1 ^
            Module.finrank K L)⁻¹ =
        FiniteIdeleGroup.absoluteNorm a.2 ^ Module.finrank K L *
          (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹ ^
            Module.finrank K L := by
      rw [inv_pow]
    _ =
        (FiniteIdeleGroup.absoluteNorm a.2 *
          (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹) ^
            Module.finrank K L := by
      rw [mul_pow]

open scoped Classical in
/-- If the finite part of a rational idele is trivial, then its scalar
extension has absolute norm equal to the extension degree power of the
original absolute norm. -/
theorem absoluteNorm_relativeIdeleBaseChange_inclusion_of_finite_eq_one
    (a : IdeleGroup ℚ)
    (ha : a.2 = 1) :
    absoluteNorm
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := L)
          (RelativeIdeleGroup.inclusion ℚ L a)) =
      absoluteNorm a ^ Module.finrank ℚ L := by
  change
    absoluteNorm (extension ℚ L a) =
      absoluteNorm a ^ Module.finrank ℚ L
  have hfinite : (extension ℚ L a).2 = 1 := by
    apply RestrictedProduct.ext
    intro W
    change finiteComponent W (extension ℚ L a) = 1
    rw [extension_finiteComponent]
    change
      Units.map
          (finitePlaceAdicCompletionMap ℚ L
            (_root_.finitePlaceBelow (K := ℚ) W)
            ⟨W, rfl⟩).toMonoidHom
          (a.2 (_root_.finitePlaceBelow (K := ℚ) W)) =
        1
    rw [ha]
    exact map_one _
  rw [absoluteNorm_apply, absoluteNorm_apply, hfinite, ha,
    map_one, one_mul,
    archimedeanNorm_extension (K := ℚ) (L := L)]
  simpa only [map_one, one_mul] using
    (inv_pow (InfiniteIdeleGroup.archimedeanNorm a.1)
      (Module.finrank ℚ L)).symm


end IdeleGroup

end
