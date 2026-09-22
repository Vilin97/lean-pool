/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
/-!
# Naturality of tower base change under number-field equivalences

The ordinary idele group of a finite extension is obtained from the
relative tensor presentation by scalar extension.  This file proves that
this comparison is natural when both fields in the extension are replaced
by compatible equivalent number fields.  The proof passes through the
fixed-bottom tower

`(𝔸_ℚ ⊗[ℚ] K) ⊗[K] L`

and therefore uses only tensor-product coherence; no new description of
local components is introduced.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

variable
    {K K' L L' : Type}
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K' L']
    [FiniteDimensional K L]
    [FiniteDimensional K' L']

section CongrComposition

variable
    {M N : Type}
    [Field M] [NumberField M]
    [Field N] [NumberField N]

/-- Relative adelic transport over `ℚ` is functorial in the transported
top field. -/
theorem relativeAdeleCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (z : RelativeAdeleRing ℚ K) :
    relativeAdeleCongr (K := ℚ) f
        (relativeAdeleCongr (K := ℚ) e z) =
      relativeAdeleCongr (K := ℚ) (e.trans f) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      rw [relativeAdeleCongr_tmul,
        relativeAdeleCongr_tmul,
        relativeAdeleCongr_tmul]
      rfl

/-- Canonical transport of ordinary adele rings is functorial. -/
theorem adeleCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (a : NumberField.AdeleRing (𝓞 K) K) :
    adeleCongr f (adeleCongr e a) =
      adeleCongr (e.trans f) a := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := N)
        (relativeAdeleCongr (K := ℚ) f
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := M)).symm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := M)
              (relativeAdeleCongr (K := ℚ) e
                ((relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K)).symm a))))) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := N)
        (relativeAdeleCongr (K := ℚ) (e.trans f)
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm a))
  rw [RingEquiv.symm_apply_apply,
    relativeAdeleCongr_trans]

/-- Canonical transport of ordinary ideles is functorial. -/
theorem ideleCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (a : IdeleGroup K) :
    ideleCongr f (ideleCongr e a) =
      ideleCongr (e.trans f) a := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := N)).injective
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  exact adeleCongr_trans e f
    (((IdeleGroup.equivAdeleRingUnits
      (K := K) a :
        (NumberField.AdeleRing (𝓞 K) K)ˣ) :
      NumberField.AdeleRing (𝓞 K) K))

/-- Canonical transport of ordinary idele classes is functorial. -/
theorem ideleClassCongr_trans
    (e : K ≃ₐ[ℚ] M)
    (f : M ≃ₐ[ℚ] N)
    (c : IdeleClassGroup K) :
    ideleClassCongr f (ideleClassCongr e c) =
      ideleClassCongr (e.trans f) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup N))
    (ideleCongr_trans e f a)

/-- Transport of ordinary idele classes along the identity
number-field equivalence is the identity. -/
@[simp]
theorem ideleClassCongr_refl
    (c : IdeleClassGroup K) :
    ideleClassCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) c =
      c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ideleClassCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [ideleClassCongr_mk]
  congr 1
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K)).injective
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  let u : NumberField.AdeleRing (𝓞 K) K :=
    ((IdeleGroup.equivAdeleRingUnits (K := K) a :
      (NumberField.AdeleRing (𝓞 K) K)ˣ) :
      NumberField.AdeleRing (𝓞 K) K)
  change
    adeleCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) u =
      u
  let z : RelativeAdeleRing ℚ K :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm u
  have hz :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = u :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply u
  have hcongr :
      relativeAdeleCongr (K := ℚ)
          (AlgEquiv.refl : K ≃ₐ[ℚ] K) z = z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul b x =>
        rw [relativeAdeleCongr_tmul]
        rfl
  calc
    adeleCongr
          (AlgEquiv.refl : K ≃ₐ[ℚ] K) u =
        adeleCongr
          (AlgEquiv.refl : K ≃ₐ[ℚ] K)
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K) z) :=
      congrArg _ hz.symm
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K)
          (relativeAdeleCongr (K := ℚ)
            (AlgEquiv.refl : K ≃ₐ[ℚ] K) z) :=
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) z).symm
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z := by
      rw [hcongr]
    _ = u := hz

end CongrComposition

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- Before passing to ordinary adeles, compatible transport of a tower
agrees with transporting its flattened rational tensor presentation. -/
theorem relativeAdeleCongrOfAlgEquiv_towerActual
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : TowerRelativeAdeleRing ℚ K L) :
    relativeAdeleCongrOfAlgEquiv eK eL h
        (towerActualRelativeAdeleRingEquiv ℚ K L z) =
      towerActualRelativeAdeleRingEquiv ℚ K' L'
        (towerRelativeAdeleUnflatten ℚ K' L'
          (relativeAdeleCongr (K := ℚ) eL
            (towerRelativeAdeleFlatten ℚ K L z))) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hb₁ hb₂
      | tmul a y =>
          have hK :
              adeleCongr eK
                  (relativeAdeleBaseChangeRingEquiv
                    (K := ℚ) (L := K) (a ⊗ₜ[ℚ] y)) =
                relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K')
                  (a ⊗ₜ[ℚ] eK y) := by
            rw [←
              relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
                eK (a ⊗ₜ[ℚ] y),
              relativeAdeleCongr_tmul]
          change
            relativeAdeleCongrOfAlgEquiv eK eL h
                (relativeAdeleBaseChangeRingEquiv
                    (K := ℚ) (L := K) (a ⊗ₜ[ℚ] y) ⊗ₜ[K] x) =
              towerActualRelativeAdeleRingEquiv ℚ K' L'
                (towerRelativeAdeleUnflatten ℚ K' L'
                  (relativeAdeleCongr (K := ℚ) eL
                    (towerRelativeAdeleFlatten ℚ K L
                      ((a ⊗ₜ[ℚ] y) ⊗ₜ[K] x))))
          rw [relativeAdeleCongrOfAlgEquiv_tmul,
            towerRelativeAdeleFlatten_tmul,
            intermediateAdeleInclusion_tmul,
            topFieldToOneStep_apply,
            Algebra.TensorProduct.tmul_mul_tmul,
            mul_one,
            relativeAdeleCongr_tmul,
            map_mul, h,
            towerRelativeAdeleUnflatten_tmul,
            bottomAdeleToTower_apply,
            topFieldToTower_apply,
            Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul,
            towerActualRelativeAdeleRingEquiv_tmul]
          rw [hK]
          change
            relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K') (a ⊗ₜ[ℚ] eK y) ⊗ₜ[K'] eL x =
              relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K') (a ⊗ₜ[ℚ] (1 : K')) ⊗ₜ[K']
                ((algebraMap K' L') (eK y) * eL x)
          have htmul :
              (a ⊗ₜ[ℚ] eK y : RelativeAdeleRing ℚ K') =
                (a ⊗ₜ[ℚ] (1 : K')) *
                  ((1 : NumberField.AdeleRing (𝓞 ℚ) ℚ) ⊗ₜ[ℚ] eK y) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul,
              mul_one, one_mul]
          rw [htmul, map_mul,
            relativeAdeleBaseChangeRingEquiv_fieldInclusion]
          rw [mul_comm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K') (a ⊗ₜ[ℚ] (1 : K')))
            (algebraMap K'
              (NumberField.AdeleRing (𝓞 K') K') (eK y)),
            ← Algebra.smul_def, TensorProduct.smul_tmul,
            Algebra.smul_def]

/-- The relative-to-ordinary adele comparison commutes with compatible
equivalences of both fields in a finite extension. -/
theorem relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : RelativeAdeleRing K L) :
    relativeAdeleBaseChangeRingEquiv
        (K := K') (L := L')
        (relativeAdeleCongrOfAlgEquiv eK eL h z) =
      adeleCongr eL
        (relativeAdeleBaseChangeRingEquiv
          (K := K) (L := L) z) := by
  let t : TowerRelativeAdeleRing ℚ K L :=
    (towerActualRelativeAdeleRingEquiv ℚ K L).symm z
  let q : RelativeAdeleRing ℚ L' :=
    relativeAdeleCongr (K := ℚ) eL
      (towerRelativeAdeleFlatten ℚ K L t)
  calc
    relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (relativeAdeleCongrOfAlgEquiv eK eL h z) =
        relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (relativeAdeleCongrOfAlgEquiv eK eL h
            (towerActualRelativeAdeleRingEquiv ℚ K L t)) := by
      rw [(towerActualRelativeAdeleRingEquiv ℚ K L).apply_symm_apply]
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (towerActualRelativeAdeleRingEquiv ℚ K' L'
            (towerRelativeAdeleUnflatten ℚ K' L' q)) := by
      rw [relativeAdeleCongrOfAlgEquiv_towerActual]
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := L')
          (towerRelativeAdeleRingEquiv ℚ K' L'
            (towerRelativeAdeleUnflatten ℚ K' L' q)) :=
      relativeAdeleBaseChangeRingEquiv_tower
        ℚ K' L' (towerRelativeAdeleUnflatten ℚ K' L' q)
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := L') q := by
      change
        relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L')
            ((towerRelativeAdeleRingEquiv ℚ K' L')
              ((towerRelativeAdeleRingEquiv ℚ K' L').symm q)) =
          relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L') q
      rw [RingEquiv.apply_symm_apply]
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L)
            (towerRelativeAdeleFlatten ℚ K L t)) :=
      relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        eL (towerRelativeAdeleFlatten ℚ K L t)
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := K) (L := L)
            (towerActualRelativeAdeleRingEquiv ℚ K L t)) := by
      change
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L)
            ((towerRelativeAdeleRingEquiv ℚ K L) t)) =
          adeleCongr eL
            (relativeAdeleBaseChangeRingEquiv
              (K := K) (L := L)
              (towerActualRelativeAdeleRingEquiv ℚ K L t))
      rw [← relativeAdeleBaseChangeRingEquiv_tower]
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := K) (L := L) z) := by
      rw [(towerActualRelativeAdeleRingEquiv ℚ K L).apply_symm_apply]

/-- The relative-to-ordinary idele comparison commutes with compatible
equivalences of both fields in a finite extension. -/
theorem relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    relativeIdeleBaseChangeMulEquiv
        (K := K') (L := L')
        (relativeIdeleCongrOfAlgEquiv eK eL h a) =
      ideleCongr eL
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := L')).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply,
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv
      eK eL h (a : RelativeAdeleRing K L)

/-- The relative-to-ordinary idele-class comparison commutes with
compatible equivalences of both fields in a finite extension. -/
@[simp]
theorem relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K') (L := L')
        (relativeIdeleClassCongrOfAlgEquiv eK eL h c) =
      ideleClassCongr eL
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup L'))
    (relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv
      eK eL h a)

/-- Ordinary idele-class norms are natural under compatible
equivalences of finite number-field extensions. -/
theorem ideleClassCongr_ideleClassNorm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : IdeleClassGroup L) :
    ideleClassCongr eK (_root_.ideleClassNorm K L c) =
      _root_.ideleClassNorm K' L' (ideleClassCongr eL c) := by
  let d : RelativeIdeleGroup.ClassGroup K L :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).symm c
  have hd :
      relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d = c :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).apply_symm_apply c
  calc
    ideleClassCongr eK (_root_.ideleClassNorm K L c) =
        ideleClassCongr eK
          (_root_.ideleClassNorm K L
            (relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d)) := by rw [hd]
    _ =
        ideleClassCongr eK
          (RelativeIdeleGroup.classNorm K L d) := by
      rw [ordinaryIdeleClassNorm_relativeIdeleClassBaseChange]
    _ =
        RelativeIdeleGroup.classNorm K' L'
          (relativeIdeleClassCongrOfAlgEquiv eK eL h d) :=
      relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
        eK eL h d
    _ =
        _root_.ideleClassNorm K' L'
          (relativeIdeleClassBaseChangeMulEquiv
            (K := K') (L := L')
            (relativeIdeleClassCongrOfAlgEquiv eK eL h d)) := by
      rw [ordinaryIdeleClassNorm_relativeIdeleClassBaseChange]
    _ =
        _root_.ideleClassNorm K' L'
          (ideleClassCongr eL
            (relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d)) := by
      rw [relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv]
    _ =
        _root_.ideleClassNorm K' L'
          (ideleClassCongr eL c) := by
      rw [hd]
