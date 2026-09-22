/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension
import Mathlib.RingTheory.Complex
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
/-!
# Unique extension to algebraic field extensions

A nontrivial real-valued absolute value on a complete field extends uniquely to
every algebraic field extension. Both the archimedean and nonarchimedean
branches are included.
-/

noncomputable section

namespace AbsoluteValue

private abbrev algebraicExtension_standardRealAbsoluteValue : AbsoluteValue ℝ ℝ :=
  NormedField.toAbsoluteValue ℝ

/-- archimedean standard branch: the usual absolute value on
`ℂ`. -/
private abbrev algebraicExtension_standardComplexAbsoluteValue : AbsoluteValue ℂ ℝ :=
  NormedField.toAbsoluteValue ℂ

/-- If `0 < s ≤ 1`, the `s`-power of a real-valued absolute value is again a
real-valued absolute value.  This is the exponent transport needed for the
archimedean branch after Ostrowski's theorem. -/
noncomputable def rpow
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) : AbsoluteValue F ℝ where
  toFun x := v x ^ s
  map_mul' x y := by
    rw [v.map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) s
  eq_zero' x := by
    rw [Real.rpow_eq_zero (v.nonneg x) hs0.ne']
    exact v.eq_zero
  add_le' x y := by
    calc
      v (x + y) ^ s ≤ (v x + v y) ^ s :=
        Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) hs0.le
      _ ≤ v x ^ s + v y ^ s :=
        Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) hs0.le hs1

/-- Raising an absolute value to a real power evaluates by real exponentiation. -/
@[simp]
theorem rpow_apply
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (x : F) :
    rpow v s hs0 hs1 x = v x ^ s :=
  rfl

/-- A positive real power of a nonarchimedean absolute value is again an
absolute value.

Unlike `AbsoluteValue.rpow`, no upper bound on the exponent is needed here:
the ultrametric inequality is preserved by every strictly increasing positive
power.  This is the normalization operation for a nonarchimedean valuation
class. -/
noncomputable def nonarchimedeanRpow
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (hv : IsNonarchimedean (v : F → ℝ))
    (s : ℝ) (hs : 0 < s) : AbsoluteValue F ℝ where
  toFun x := v x ^ s
  map_mul' x y := by
    rw [v.map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) s
  eq_zero' x := by
    rw [Real.rpow_eq_zero (v.nonneg x) hs.ne']
    exact v.eq_zero
  add_le' x y := by
    rcases le_total (v x) (v y) with hxy | hyx
    · calc
        v (x + y) ^ s ≤ v y ^ s := by
          apply Real.rpow_le_rpow (v.nonneg _)
          · simpa [max_eq_right hxy] using hv x y
          · exact hs.le
        _ ≤ v x ^ s + v y ^ s :=
          le_add_of_nonneg_left (Real.rpow_nonneg (v.nonneg x) s)
    · calc
        v (x + y) ^ s ≤ v x ^ s := by
          apply Real.rpow_le_rpow (v.nonneg _)
          · simpa [max_eq_left hyx] using hv x y
          · exact hs.le
        _ ≤ v x ^ s + v y ^ s :=
          le_add_of_nonneg_right (Real.rpow_nonneg (v.nonneg y) s)

@[simp]
theorem nonarchimedeanRpow_apply
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (hv : IsNonarchimedean (v : F → ℝ))
    (s : ℝ) (hs : 0 < s) (x : F) :
    nonarchimedeanRpow v hv s hs x = v x ^ s :=
  rfl

/-- Positive-power normalization does not change the underlying
nonarchimedean valuation class. -/
theorem isEquiv_nonarchimedeanRpow
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (hv : IsNonarchimedean (v : F → ℝ))
    (s : ℝ) (hs : 0 < s) :
    v.IsEquiv (nonarchimedeanRpow v hv s hs) := by
  rw [AbsoluteValue.isEquiv_iff_exists_rpow_eq]
  exact ⟨s, hs, rfl⟩

/-- The usual complex absolute value restricts to the usual real absolute value. -/
private theorem algebraicExtension_standardComplexAbsoluteValue_extends_standardReal
    (x : ℝ) :
    algebraicExtension_standardComplexAbsoluteValue (algebraMap ℝ ℂ x) =
      algebraicExtension_standardRealAbsoluteValue x := by
  change ‖(algebraMap ℝ ℂ x)‖ = ‖x‖
  simp

/-- Pull back an absolute value along a `K`-algebra equivalence.  This is the
transport step used after the archimedean classification identifies a complete
archimedean field with `ℝ` or `ℂ`. -/
noncomputable def compAlgEquiv
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := e.toRingHom) e.injective

/-- Composition with an algebra equivalence evaluates the absolute value after transport. -/
@[simp]
theorem compAlgEquiv_apply
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) (x : L) :
    compAlgEquiv e w x = w (e x) :=
  rfl

/-- Transporting an extending absolute value along an algebra equivalence preserves extension. -/
theorem compAlgEquiv_extends_apply
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) (v : AbsoluteValue K ℝ)
    (hw : ∀ x : K, w (algebraMap K E x) = v x)
    (x : K) :
    compAlgEquiv e w (algebraMap K L x) =
      v x := by
  change w (e (algebraMap K L x)) = v x
  rw [AlgEquiv.commutes, hw]

/-- Pullback along an algebra equivalence preserves exact extension of the base value. -/
theorem compAlgEquiv_extends
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) (v : AbsoluteValue K ℝ)
    (hw : Extends v w) :
    Extends v (compAlgEquiv e w) :=
  compAlgEquiv_extends_apply e w v hw

/-- Completeness is preserved when an absolute value is pulled back along an
algebra equivalence. -/
theorem compAlgEquiv_complete
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ)
    (hwcomplete : CompleteSpace (WithAbs w)) :
    CompleteSpace (WithAbs (compAlgEquiv e w)) := by
  let e' : WithAbs (compAlgEquiv e w) ≃ WithAbs w :=
    (WithAbs.congr (compAlgEquiv e w) w e.toRingEquiv).toEquiv
  have he' : Isometry e' := by
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
    dsimp only [e']
    rw [WithAbs.ofAbs_sub, WithAbs.ofAbs_sub]
    change w (e x.ofAbs - e y.ofAbs) =
      w (e (x.ofAbs - y.ofAbs))
    exact congrArg w (map_sub e x.ofAbs y.ofAbs).symm
  exact (completeSpace_congr he'.isUniformEmbedding).2 hwcomplete

private theorem algebraicExtension_real_algEquiv_real_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      algebraicExtension_standardRealAbsoluteValue x ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardRealAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℝ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℝ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (compAlgEquiv_extends_apply e
      algebraicExtension_standardRealAbsoluteValue algebraicExtension_standardRealAbsoluteValue
      (fun x => rfl) (e x)).symm

/-- In the `ℂ` branch over `ℝ`, the `s`-power of the usual complex absolute
value is the unique extension of the `s`-power of the usual real absolute
value. -/
private theorem algebraicExtension_real_algEquiv_complex_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      algebraicExtension_standardRealAbsoluteValue x ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardComplexAbsoluteValue)
      s hs0 hs1 := by
  let e' : WithAbs w ≃ₐ[ℝ] ℂ :=
    (WithAbs.algEquiv ℝ w).trans e
  have hnorm :
      ∀ r : ℝ, ‖algebraMap ℝ (WithAbs w) r‖ = ‖r‖ ^ s := by
    intro r
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.algebraMap_right_apply]
    change w (algebraMap ℝ L r) =
      algebraicExtension_standardRealAbsoluteValue r ^ s
    exact hw r
  ext x
  let y : WithAbs w := WithAbs.toAbs w x
  change w x = ‖e x‖ ^ s
  calc
    w x = ‖y‖ := by
      simp [y, WithAbs.norm_eq_apply_ofAbs]
    _ = ‖e'.symm (e' y)‖ := by simp
    _ = ‖e' y‖ ^ s :=
      AlgEquiv.norm_symm_apply_eq_norm_rpow
        (F := WithAbs w) (s := s) hs0 hnorm e' (e' y)
    _ = ‖e x‖ ^ s := by simp [y, e']

/-- Over `ℂ`, an absolute value extending the `s`-power of the usual complex
absolute value is the transported `s`-power. -/
private theorem algebraicExtension_complex_algEquiv_complex_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℂ L] (e : L ≃ₐ[ℂ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ z : ℂ, w (algebraMap ℂ L z) =
      algebraicExtension_standardComplexAbsoluteValue z ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardComplexAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℂ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℂ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (compAlgEquiv_extends_apply e
      algebraicExtension_standardComplexAbsoluteValue
        algebraicExtension_standardComplexAbsoluteValue
      (fun z => rfl) (e x)).symm

/-- A chosen absolute-value extension together with its uniqueness property. -/
structure UniqueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) where
  /-- The chosen absolute value on the extension field. -/
  extension : AbsoluteValue L ℝ
  /-- The chosen absolute value restricts to the given base absolute value. -/
  isExtension : Extends v extension
  /-- Every extension of the base absolute value equals the chosen one. -/
  unique :
    ∀ w : AbsoluteValue L ℝ,
      Extends v w → w = extension

private noncomputable def algebraicExtension_realRpow
    {L : Type*} [Field L] [Algebra ℝ L] [Algebra.IsAlgebraic ℝ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    UniqueExtension (K := ℝ) (L := L)
      (rpow
        algebraicExtension_standardRealAbsoluteValue s hs0 hs1) :=
  Classical.choice <| by
    rcases Real.nonempty_algEquiv_or L with hreal | hcomplex
    · rcases hreal with ⟨e⟩
      exact ⟨
        { extension :=
            rpow
              (compAlgEquiv
                e algebraicExtension_standardRealAbsoluteValue)
              s hs0 hs1
          isExtension := by
            intro x
            simp only [rpow_apply]
            rw [compAlgEquiv_extends_apply e
              algebraicExtension_standardRealAbsoluteValue
              algebraicExtension_standardRealAbsoluteValue (fun x => rfl) x]
          unique :=
            algebraicExtension_real_algEquiv_real_unique_rpow_extension
              e s hs0 hs1 }⟩
    · rcases hcomplex with ⟨e⟩
      exact ⟨
        { extension :=
            rpow
              (compAlgEquiv
                e algebraicExtension_standardComplexAbsoluteValue)
              s hs0 hs1
          isExtension := by
            intro x
            simp only [rpow_apply]
            rw [compAlgEquiv_extends_apply e
              algebraicExtension_standardComplexAbsoluteValue
              algebraicExtension_standardRealAbsoluteValue
              algebraicExtension_standardComplexAbsoluteValue_extends_standardReal x]
          unique :=
            algebraicExtension_real_algEquiv_complex_unique_rpow_extension
              e s hs0 hs1 }⟩

/-- archimedean `s`-power theorem over `ℂ`: every algebraic
extension of `ℂ` has a unique absolute value extending `|z|^s`, for
`0 < s ≤ 1`. -/
private noncomputable def algebraicExtension_complexRpow
    {L : Type*} [Field L] [Algebra ℂ L] [Algebra.IsAlgebraic ℂ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    UniqueExtension (K := ℂ) (L := L)
      (rpow
        algebraicExtension_standardComplexAbsoluteValue s hs0 hs1) := by
  letI : Algebra.IsIntegral ℂ L := Algebra.IsAlgebraic.isIntegral
  let e0 : ℂ ≃ₐ[ℂ] L :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ L)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := L))
  let e : L ≃ₐ[ℂ] ℂ := e0.symm
  exact
    { extension :=
        rpow
          (compAlgEquiv
            e algebraicExtension_standardComplexAbsoluteValue)
          s hs0 hs1
      isExtension := by
        intro z
        simp only [rpow_apply]
        rw [compAlgEquiv_extends_apply e
          algebraicExtension_standardComplexAbsoluteValue
          algebraicExtension_standardComplexAbsoluteValue (fun z => rfl) z]
      unique :=
        algebraicExtension_complex_algEquiv_complex_unique_rpow_extension
          e s hs0 hs1 }

/-- Algebraicity is preserved under transport of the base field by a ring equivalence. -/
private theorem algebraicExtension_isAlgebraic_of_base_ringEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : K ≃+* E) :
    letI : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
    letI : Algebra E L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    Algebra.IsAlgebraic E L := by
  let : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
  let : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  have : IsScalarTower E K L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simp [RingHom.algebraMap_toAlgebra])
  let e : K ≃ₐ[E] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro r
    simp [RingHom.algebraMap_toAlgebra])
  have : Algebra.IsAlgebraic E K := e.symm.isAlgebraic
  exact Algebra.IsAlgebraic.trans E K L

/-- Transport a unique algebraic absolute-value extension after replacing the
base field by a ring-equivalent field; the top algebra structure is
transported along the same equivalence. -/
private noncomputable def algebraicExtension_baseRingEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    (σ : K ≃+* E) (vK : AbsoluteValue K ℝ) (vE : AbsoluteValue E ℝ)
    (hvσ : ∀ x : K, vE (σ x) = vK x)
    (R :
      letI : Algebra E L :=
        RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
      UniqueExtension (K := E) (L := L) vE) :
    UniqueExtension (K := K) (L := L) vK := by
  letI : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  exact
    { extension := R.extension
      isExtension := by
        intro x
        have hbase := R.isExtension (σ x)
        have hmap :
            algebraMap E L (σ x) = algebraMap K L x := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          R.extension (algebraMap K L x)
              = R.extension (algebraMap E L (σ x)) := by rw [hmap]
          _ = vE (σ x) := hbase
          _ = vK x := hvσ x
      unique := by
        intro w hw
        apply R.unique w
        intro z
        have hmap :
            algebraMap E L z = algebraMap K L (σ.symm z) := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          w (algebraMap E L z)
              = w (algebraMap K L (σ.symm z)) := by rw [hmap]
          _ = vK (σ.symm z) := hw (σ.symm z)
          _ = vE z := by
            simpa using (hvσ (σ.symm z)).symm }

/-- The archimedean branch of the unique algebraic-extension construction. -/
private noncomputable def algebraicExtension_archimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    UniqueExtension (K := K) (L := L) v :=
  Classical.choice <| by
  classical
  let : CharZero K := AbsoluteValue.charZero_of_not_isNonarchimedean v harch
  rcases AbsoluteValue.ostrowski_of_complete v hcomplete harch with
    ⟨s, hs0, hs1, hbranch⟩
  rcases hbranch with hreal | hcomplex
  · rcases hreal with ⟨σ, hσ⟩
    let : Algebra ℝ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℝ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℝ L :=
      algebraicExtension_isAlgebraic_of_base_ringEquiv (K := K) (E := ℝ)
        (L := L) σ
    let R :=
      algebraicExtension_realRpow
        (L := L) s hs0 hs1
    exact ⟨
      algebraicExtension_baseRingEquiv
        (K := K) (E := ℝ) (L := L) σ v
        (rpow
          algebraicExtension_standardRealAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩
  · rcases hcomplex with ⟨σ, hσ⟩
    let : Algebra ℂ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℂ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℂ L :=
      algebraicExtension_isAlgebraic_of_base_ringEquiv (K := K) (E := ℂ)
        (L := L) σ
    let R :=
      algebraicExtension_complexRpow
        (L := L) s hs0 hs1
    exact ⟨
      algebraicExtension_baseRingEquiv
        (K := K) (E := ℂ) (L := L) σ v
        (rpow
          algebraicExtension_standardComplexAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩

/-- nonarchimedean algebraic-extension theorem:
existence and uniqueness of the extension over any algebraic extension. -/
private noncomputable def algebraicExtension_nonarchimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) :
    UniqueExtension (K := K) (L := L) v where
  extension :=
    spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv
  isExtension :=
    spectralExtension_extends
      (K := K) (L := L) v hcomplete hnonarch hv
  unique :=
    eq_spectralExtension_of_extends
      (K := K) (L := L) v hcomplete hnonarch hv

/-- algebraic-extension theorem for the nontrivial
valuations: a complete valued field has a unique absolute-value extension to
every algebraic extension.  The proof splits into the archimedean branch above
and the nonarchimedean spectral branch. -/
noncomputable def uniqueAlgebraicExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hv : v.IsNontrivial) :
    UniqueExtension (K := K) (L := L) v := by
  by_cases hnonarch : IsNonarchimedean (v : K → ℝ)
  · exact algebraicExtension_nonarchimedean
      v hcomplete hnonarch hv
  · exact algebraicExtension_archimedean
      v hcomplete hnonarch


/-- Existence and uniqueness as a unique-existence statement. -/
theorem existsUnique_extends_of_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hv : v.IsNontrivial) :
    ∃! w : AbsoluteValue L ℝ, Extends v w := by
  let R := uniqueAlgebraicExtension (K := K) (L := L) v hcomplete hv
  exact ⟨R.extension, R.isExtension, fun w hw => R.unique w hw⟩

end AbsoluteValue

end
