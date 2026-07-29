/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeLattice

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An ideal element shape map used in the Odlyzko-bound argument. -/
noncomputable def idealElementShapeMap
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  ⟨traceRadialScale K q hq
      (traceEmbedding K (((x : 𝓞 K) : K))),
      (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
        K (FractionalIdeal.mk0 K J) q hq _).2 (by
          rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
          exact ⟨x, x.prop, rfl⟩)⟩

open Classical in
theorem idealElementShapeMap_bijective
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (idealElementShapeMap K J q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (((x : 𝓞 K) : K)) =
          traceEmbedding K (((y : 𝓞 K) : K)) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K (FractionalIdeal.mk0 K J) :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice
        K (FractionalIdeal.mk0 K J) hv
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K ((y : 𝓞 K) : K)) = v
    simp_all

open Classical in
/-- An ideal element shape equiv used in the Odlyzko-bound argument. -/
noncomputable def idealElementShapeEquiv
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥(J : Ideal (𝓞 K)) ≃
      shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  Equiv.ofBijective (idealElementShapeMap K J q hq)
    (idealElementShapeMap_bijective K J q hq)

open Classical in
@[simp]
theorem idealElementShapeEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    ((idealElementShapeEquiv K J q hq x :
        shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq
        (traceEmbedding K (((x : 𝓞 K) : K))) :=
  by rfl

variable [IsTotallyComplex K]

open Classical in
/-- A shape ideal theta used in the Odlyzko-bound argument. -/
noncomputable def shapeIdealTheta
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta
    (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi

open Classical in
theorem shapeIdealTheta_eq_tsum
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    shapeIdealTheta K J q hq =
      ∑' x : ↥(J : Ideal (𝓞 K)),
        complexPlaceGaussian K (((x : 𝓞 K) : K)) q := by
  rw [shapeIdealTheta, latticeTheta,
    ← (idealElementShapeEquiv K J q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [idealElementShapeEquiv_coe,
    ← complexPlaceGaussian_eq_latticeGaussian]

omit [IsTotallyComplex K] in
open Classical in
theorem dualLatticeTheta_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLatticeTheta (shapeIdealLattice K I q hq) Real.pi =
      latticeTheta
        (shapeIdealLattice K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w))) Real.pi := by
  rw [dualLatticeTheta, dualLattice_shapeIdealLattice,
    conjugateShapeIdealLattice]
  exact latticeTheta_map_linearIsometryEquiv
    (shapeIdealLattice K (traceDualIdealUnit K I)
      (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)))
    (traceConjugation K) Real.pi

open Classical in
/-- A nonzero ideal element equiv singleton compl used in the Odlyzko-bound argument. -/
def nonzeroIdealElementEquivSingletonCompl
    (J : (Ideal (𝓞 K))⁰) :
    nonzeroIdealElement K J ≃
      {x : ↥(J : Ideal (𝓞 K)) // x ∉ ({0} : Finset ↥(J : Ideal (𝓞 K)))} where
  toFun x :=
    ⟨⟨x.1, x.2.1⟩, by
      simp only [Finset.mem_singleton]
      intro hx
      exact x.2.2 (congrArg Subtype.val hx)⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      intro hx
      apply x.2
      simp_all⟩
  left_inv x := by
    simp
  right_inv x := by
    apply Subtype.ext
    simp

open Classical in
theorem shapeIdealTheta_eq_one_add_nonzero
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    shapeIdealTheta K J q hq =
      1 + ∑' x : nonzeroIdealElement K J,
        complexPlaceGaussian K (((x : 𝓞 K) : K)) q := by
  let f : ↥(J : Ideal (𝓞 K)) → ℂ :=
    fun x ↦ complexPlaceGaussian K (((x : 𝓞 K) : K)) q
  have hsL :
      Summable (fun v :
          shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq ↦
        latticeGaussian Real.pi
          (v : mixedEmbedding.euclidean.mixedSpace K)) :=
    summable_latticeTheta
      (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi_pos
  have hs : Summable f := by
    have h := (Equiv.summable_iff
      (idealElementShapeEquiv K J q hq)).mpr hsL
    exact h.congr fun x ↦ by
      dsimp only [Function.comp_apply, f]
      rw [idealElementShapeEquiv_coe,
        ← complexPlaceGaussian_eq_latticeGaussian]
  rw [shapeIdealTheta_eq_tsum]
  change (∑' x, f x) = _
  rw [← hs.sum_add_tsum_subtype_compl ({0} : Finset ↥(J : Ideal (𝓞 K)))]
  simp only [Finset.sum_singleton, f, complexPlaceGaussian]
  have hzero :
      Complex.exp
        (-((2 * Real.pi *
          ∑ w : InfinitePlace K,
            (w (((0 : ↥(J : Ideal (𝓞 K))) : 𝓞 K) : K)) ^ 2 *
              (q w) ^ 2 : ℝ) : ℂ)) = 1 := by
    simp
  rw [hzero]
  rw [← (nonzeroIdealElementEquivSingletonCompl K J).tsum_eq]
  rfl

open Classical in
theorem nonzeroIdealShapeTheta_eq_shapeIdealTheta_sub_one
    (J : (Ideal (𝓞 K))⁰) (y : mixedEmbedding.realSpace K) :
    nonzeroIdealShapeTheta K J y =
      shapeIdealTheta K J (mixedEmbedding.fundamentalCone.expMapBasis y)
        (fun w ↦ (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).ne') - 1 := by
  rw [shapeIdealTheta_eq_one_add_nonzero, nonzeroIdealShapeTheta]
  ring

end NumberField.Odlyzko
