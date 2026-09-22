/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionAutomorphism
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension

/-!
# Towers of exact constant extensions

Let `C` be the exact constant field of `N`, let `M` be an intermediate field
in a tower `C ⊆ M ⊆ N`, and let `S / C` be finite Galois.  Tensoring the
inclusion `M → N` with the identity of `S` gives

`S ⊗[C] M → S ⊗[C] N`.

This file packages that map as the algebra structure needed by the
constant-extension place and Frobenius APIs.  It proves that the extended
top is finite Galois over the extended intermediate field, with the same
degree and hence the same Galois-group cardinality as `N / M`.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section


variable (C M N S : Type*) [Field C] [Field M] [Field N] [Field S]
  [Algebra C M] [Algebra C N] [Algebra M N] [IsScalarTower C M N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

/-- Exact constants descend from a field to every intermediate field in a
compatible scalar tower. -/
theorem algebraicClosure_eq_bot_of_tower
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    algebraicClosure C M = (⊥ : IntermediateField C M) := by
  let i : M →ₐ[C] N := IsScalarTower.toAlgHom C M N
  apply eq_bot_iff.mpr
  intro x hx
  have hxi : i x ∈ algebraicClosure C N :=
    (map_mem_algebraicClosure_iff i).mpr hx
  rw [hExactN] at hxi
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxi
  apply IntermediateField.mem_bot.mpr
  refine ⟨c, ?_⟩
  exact i.injective (by simpa using hc)

/-- Tensor the inclusion `M → N` with the identity on the enlarged
constant field. -/
noncomputable def exactConstantExtensionTowerAlgHom :
    ExactConstantExtension C M S →ₐ[C] ExactConstantExtension C N S :=
  Algebra.TensorProduct.map (AlgHom.id C S)
    (IsScalarTower.toAlgHom C M N)

@[simp]
theorem exactConstantExtensionTowerAlgHom_tmul (s : S) (m : M) :
    exactConstantExtensionTowerAlgHom C M N S (s ⊗ₜ[C] m) =
      s ⊗ₜ[C] algebraMap M N m := by
  rw [exactConstantExtensionTowerAlgHom,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- The algebra structure on the extended top induced by the tensor map. -/
@[reducible] noncomputable def exactConstantExtensionTowerAlgebra :
    Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
  (exactConstantExtensionTowerAlgHom C M N S).toAlgebra

/-- The tensor map preserves the enlarged constants on the left factor. -/
theorem exactConstantExtensionTower_leftScalarTower :
    letI : Algebra S (ExactConstantExtension C M S) :=
      Algebra.TensorProduct.leftAlgebra
    letI : Algebra S (ExactConstantExtension C N S) :=
      Algebra.TensorProduct.leftAlgebra
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    IsScalarTower S (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) := by
  let : Algebra S (ExactConstantExtension C M S) :=
    Algebra.TensorProduct.leftAlgebra
  let : Algebra S (ExactConstantExtension C N S) :=
    Algebra.TensorProduct.leftAlgebra
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  apply IsScalarTower.of_algebraMap_eq'
  ext s
  change s ⊗ₜ[C] (1 : N) =
    exactConstantExtensionTowerAlgHom C M N S (s ⊗ₜ[C] (1 : M))
  rw [exactConstantExtensionTowerAlgHom_tmul, map_one]

/-- The tensor map also preserves the original right factor `M`. -/
theorem exactConstantExtensionTower_rightScalarTower
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    letI : Field (ExactConstantExtension C M S) :=
      exactConstantExtensionField C M S hExactM
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExactN
    letI : Algebra M (ExactConstantExtension C M S) :=
      exactConstantExtensionAlgebra C M S
    letI : Algebra M (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C M N S
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    IsScalarTower M (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) := by
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let : Field (ExactConstantExtension C M S) :=
    exactConstantExtensionField C M S hExactM
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExactN
  let : Algebra M (ExactConstantExtension C M S) :=
    exactConstantExtensionAlgebra C M S
  let : Algebra M (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C M N S
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  apply IsScalarTower.of_algebraMap_eq'
  ext m
  change (1 : S) ⊗ₜ[C] algebraMap M N m =
    exactConstantExtensionTowerAlgHom C M N S ((1 : S) ⊗ₜ[C] m)
  rw [exactConstantExtensionTowerAlgHom_tmul]

section Galois

variable [FiniteDimensional M N] [IsGalois M N]

/-- The extended top is finite-dimensional over the extended intermediate
field. -/
theorem exactConstantExtensionTower_finiteDimensional
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    letI : Field (ExactConstantExtension C M S) :=
      exactConstantExtensionField C M S hExactM
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExactN
    letI : Algebra M (ExactConstantExtension C M S) :=
      exactConstantExtensionAlgebra C M S
    letI : Algebra M (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C M N S
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    FiniteDimensional (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) := by
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let : Field (ExactConstantExtension C M S) :=
    exactConstantExtensionField C M S hExactM
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExactN
  let : Algebra M (ExactConstantExtension C M S) :=
    exactConstantExtensionAlgebra C M S
  let : Algebra M (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C M N S
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  let : IsScalarTower M (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_rightScalarTower C M N S hExactN
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : IsScalarTower M N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C M N S
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  let : Module.Finite M (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  exact Module.Finite.of_restrictScalars_finite M
    (ExactConstantExtension C M S) (ExactConstantExtension C N S)

/-- Base change by finite constants preserves the Galois extension. -/
theorem exactConstantExtensionTower_isGalois
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    letI : Field (ExactConstantExtension C M S) :=
      exactConstantExtensionField C M S hExactM
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExactN
    letI : Algebra M (ExactConstantExtension C M S) :=
      exactConstantExtensionAlgebra C M S
    letI : Algebra M (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C M N S
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    IsGalois (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) := by
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let : Field (ExactConstantExtension C M S) :=
    exactConstantExtensionField C M S hExactM
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExactN
  let : Algebra M (ExactConstantExtension C M S) :=
    exactConstantExtensionAlgebra C M S
  let : Algebra M (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C M N S
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  let : IsScalarTower M (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_rightScalarTower C M N S hExactN
  let : IsGalois M (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C M N S hExactN
  exact IsGalois.tower_top_of_isGalois M
    (ExactConstantExtension C M S) (ExactConstantExtension C N S)

/-- Finite constant base change preserves the relative extension degree. -/
theorem exactConstantExtensionTower_finrank
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    letI : Field (ExactConstantExtension C M S) :=
      exactConstantExtensionField C M S hExactM
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExactN
    letI : Algebra M (ExactConstantExtension C M S) :=
      exactConstantExtensionAlgebra C M S
    letI : Algebra M (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C M N S
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    letI : FiniteDimensional (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTower_finiteDimensional C M N S hExactN
    Module.finrank (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) = Module.finrank M N := by
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let : Field (ExactConstantExtension C M S) :=
    exactConstantExtensionField C M S hExactM
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExactN
  let : Algebra M (ExactConstantExtension C M S) :=
    exactConstantExtensionAlgebra C M S
  let : Algebra M (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C M N S
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  let : IsScalarTower M (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_rightScalarTower C M N S hExactN
  let : FiniteDimensional (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_finiteDimensional C M N S hExactN
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := C) (M := S))
  calc
    Module.finrank C S * Module.finrank (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) =
        Module.finrank M (ExactConstantExtension C M S) *
          Module.finrank (ExactConstantExtension C M S)
            (ExactConstantExtension C N S) := by
              rw [exactConstantExtension_finrank C M S]
    _ = Module.finrank M (ExactConstantExtension C N S) :=
      Module.finrank_mul_finrank M (ExactConstantExtension C M S)
        (ExactConstantExtension C N S)
    _ = Module.finrank M N * Module.finrank C S :=
      exactConstantExtension_finrank_over_base C M N S
    _ = Module.finrank C S * Module.finrank M N := Nat.mul_comm _ _

/-- Consequently the Galois group has the same finite cardinality after
constant base change. -/
theorem exactConstantExtensionTower_card_aut_eq
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    letI : Field (ExactConstantExtension C M S) :=
      exactConstantExtensionField C M S hExactM
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExactN
    letI : Algebra M (ExactConstantExtension C M S) :=
      exactConstantExtensionAlgebra C M S
    letI : Algebra M (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C M N S
    letI : Algebra (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTowerAlgebra C M N S
    letI : FiniteDimensional (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTower_finiteDimensional C M N S hExactN
    letI : IsGalois (ExactConstantExtension C M S)
        (ExactConstantExtension C N S) :=
      exactConstantExtensionTower_isGalois C M N S hExactN
    Nat.card (ExactConstantExtension C N S ≃ₐ[
        ExactConstantExtension C M S] ExactConstantExtension C N S) =
      Nat.card (N ≃ₐ[M] N) := by
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let : Field (ExactConstantExtension C M S) :=
    exactConstantExtensionField C M S hExactM
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExactN
  let : Algebra M (ExactConstantExtension C M S) :=
    exactConstantExtensionAlgebra C M S
  let : Algebra M (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C M N S
  let : Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTowerAlgebra C M N S
  let : FiniteDimensional (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_finiteDimensional C M N S hExactN
  let : IsGalois (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
    exactConstantExtensionTower_isGalois C M N S hExactN
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    exactConstantExtensionTower_finrank C M N S hExactN]

end Galois

end

noncomputable section

section RatFuncCompatibility


variable (C M N S : Type*) [Field C] [Field M] [Field N] [Field S]
  [Algebra (RatFunc C) M] [Algebra (RatFunc C) N]
  [Algebra M N] [IsScalarTower (RatFunc C) M N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

/-- The constant algebra obtained by restricting a rational-function-field
algebra along `C → C(X)`.  Naming this definition makes the canonical
constant structures in the source and target definitionally transparent. -/
@[reducible] noncomputable def
    exactConstantExtensionTowerCanonicalConstantAlgebra
    (C T : Type*) [Field C] [Field T] [Algebra (RatFunc C) T] :
    Algebra C T :=
  RingHom.toAlgebra
    ((algebraMap (RatFunc C) T).comp (algebraMap C (RatFunc C)))

/-- Restricting a compatible `C(X)`-tower along `C → C(X)` gives the
canonical constant scalar tower used by exact constant extensions. -/
theorem exactConstantExtensionTowerCanonicalConstantScalarTower :
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    IsScalarTower C M N := by
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact IsScalarTower.algebraMap_apply (RatFunc C) M N
    (algebraMap C (RatFunc C) c)

/-- The tensor map between two exact constant extensions is linear over the
enlarged rational-function field `S(X)` for the canonical structures on both
extensions. -/
noncomputable def exactConstantExtensionTowerRatFuncAlgHom :
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    letI : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact IsScalarTower.algebraMap_apply (RatFunc C) M N
        (algebraMap C (RatFunc C) c))
    ∀ (hExactN : algebraicClosure C N =
        (⊥ : IntermediateField C N)),
      let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
      let E_M := ExactConstantExtension C M S
      let E_N := ExactConstantExtension C N S
      letI : Field E_M := exactConstantExtensionField C M S hExactM
      letI : Field E_N := exactConstantExtensionField C N S hExactN
      letI : Algebra (RatFunc S) E_M :=
        ratFuncExactConstantExtensionAlgebra C S M hExactM
      letI : Algebra (RatFunc S) E_N :=
        ratFuncExactConstantExtensionAlgebra C S N hExactN
      E_M →ₐ[RatFunc S] E_N := by
  letI : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  letI : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  letI : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact IsScalarTower.algebraMap_apply (RatFunc C) M N
      (algebraMap C (RatFunc C) c))
  intro hExactN
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  letI : Field E_M := exactConstantExtensionField C M S hExactM
  letI : Field E_N := exactConstantExtensionField C N S hExactN
  letI : Algebra S E_M := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S E_N := Algebra.TensorProduct.leftAlgebra
  letI : Algebra (RatFunc S) E_M :=
    ratFuncExactConstantExtensionAlgebra C S M hExactM
  letI : Algebra (RatFunc S) E_N :=
    ratFuncExactConstantExtensionAlgebra C S N hExactN
  letI : Algebra C[X] M :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) M).comp
        (algebraMap C[X] (RatFunc C)))
  letI : Algebra C[X] N :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) N).comp
        (algebraMap C[X] (RatFunc C)))
  let φS : E_M →ₐ[S] E_N :=
    { exactConstantExtensionTowerAlgHom C M N S with
      commutes' := by
        intro s
        change exactConstantExtensionTowerAlgHom C M N S
            (s ⊗ₜ[C] (1 : M)) = s ⊗ₜ[C] (1 : N)
        rw [exactConstantExtensionTowerAlgHom_tmul, map_one] }
  let f : RatFunc S →ₐ[S] E_N :=
    φS.comp (ratFuncToExactConstantExtension C S M hExactM)
  let g : RatFunc S →ₐ[S] E_N :=
    ratFuncToExactConstantExtension C S N hExactN
  have hX : f RatFunc.X = g RatFunc.X := by
    change exactConstantExtensionTowerAlgHom C M N S
        (ratFuncToExactConstantExtension C S M hExactM RatFunc.X) =
      ratFuncToExactConstantExtension C S N hExactN RatFunc.X
    rw [ratFuncToExactConstantExtension_X,
      ratFuncToExactConstantExtension_X]
    simp only [polynomialTensorCancelEvaluationPoint,
      Algebra.TensorProduct.includeRight_apply]
    rw [exactConstantExtensionTowerAlgHom_tmul]
    congr 1
    exact (IsScalarTower.algebraMap_apply (RatFunc C) M N
      (algebraMap C[X] (RatFunc C) Polynomial.X)).symm
  have hRing : f.toRingHom = g.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := S[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (fun x y => x + y) hp hq
    | monomial n s =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [map_mul, map_pow, RatFunc.algebraMap_C,
          RatFunc.algebraMap_X]
        rw [← RatFunc.algebraMap_eq_C]
        have hfs : f.toRingHom (algebraMap S (RatFunc S) s) =
            algebraMap S E_N s := f.commutes s
        have hgs : g.toRingHom (algebraMap S (RatFunc S) s) =
            algebraMap S E_N s := g.commutes s
        have hX' : f.toRingHom RatFunc.X = g.toRingHom RatFunc.X := hX
        rw [hfs, hgs, hX']
  have hfg : f = g :=
    DFunLike.ext _ _ (fun r => DFunLike.congr_fun hRing r)
  refine { φS with commutes' := ?_ }
  intro r
  exact DFunLike.congr_fun hfg r

/-- The algebra structure underlying the `S(X)`-linear tensor map.  Its
underlying ring homomorphism is the same tensor map as
`exactConstantExtensionTowerAlgebra`; the separate name records the intended
canonical rational-function-field interface. -/
@[reducible] noncomputable def exactConstantExtensionTowerRatFuncAlgebra :
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    letI : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact IsScalarTower.algebraMap_apply (RatFunc C) M N
        (algebraMap C (RatFunc C) c))
    Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) :=
  by
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    letI : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact IsScalarTower.algebraMap_apply (RatFunc C) M N
        (algebraMap C (RatFunc C) c))
    exact exactConstantExtensionTowerAlgebra C M N S

/-- The canonical `S(X)`-algebras on the two exact constant extensions and
the tensor inclusion form a scalar tower. -/
theorem exactConstantExtensionTower_ratFuncScalarTower
    (hExactN :
      letI : Algebra C N :=
        exactConstantExtensionTowerCanonicalConstantAlgebra C N
      algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    letI : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact IsScalarTower.algebraMap_apply (RatFunc C) M N
        (algebraMap C (RatFunc C) c))
    let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M := exactConstantExtensionField C M S hExactM
    letI : Field E_N := exactConstantExtensionField C N S hExactN
    letI : Algebra (RatFunc S) E_M :=
      ratFuncExactConstantExtensionAlgebra C S M hExactM
    letI : Algebra (RatFunc S) E_N :=
      ratFuncExactConstantExtensionAlgebra C S N hExactN
    letI : Algebra E_M E_N :=
      exactConstantExtensionTowerRatFuncAlgebra C M N S
    IsScalarTower (RatFunc S) E_M E_N := by
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact IsScalarTower.algebraMap_apply (RatFunc C) M N
      (algebraMap C (RatFunc C) c))
  let hExactM := algebraicClosure_eq_bot_of_tower C M N hExactN
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M := exactConstantExtensionField C M S hExactM
  let : Field E_N := exactConstantExtensionField C N S hExactN
  let : Algebra (RatFunc S) E_M :=
    ratFuncExactConstantExtensionAlgebra C S M hExactM
  let : Algebra (RatFunc S) E_N :=
    ratFuncExactConstantExtensionAlgebra C S N hExactN
  let : Algebra E_M E_N :=
    exactConstantExtensionTowerRatFuncAlgebra C M N S
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  change ratFuncToExactConstantExtension C S N hExactN r =
    exactConstantExtensionTowerAlgHom C M N S
      (ratFuncToExactConstantExtension C S M hExactM r)
  exact (exactConstantExtensionTowerRatFuncAlgHom C M N S hExactN).commutes r
    |>.symm

end RatFuncCompatibility

end

end BGS.HasseWeil
