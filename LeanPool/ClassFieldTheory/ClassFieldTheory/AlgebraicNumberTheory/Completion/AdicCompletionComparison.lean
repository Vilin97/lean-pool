/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import Mathlib.NumberTheory.RamificationInertia.Valuation
/-!
# Comparing the exact-extension and concrete adic-completion maps

The completion map attached to an exact extension of a finite-place
absolute value agrees with the canonical map between the concrete adic
completions at the corresponding finite places.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The concrete homomorphism of adic completions associated with an
exact extension of the normalized absolute value. -/
noncomputable def finitePlaceExtensionAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    w.adicCompletion K →+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) w a).adicCompletion L :=
  (finitePlaceExtensionAdicCompletionRingEquiv
      (K := K) (L := L) w a).toRingHom.comp
    ((AbsoluteValue.completionMap
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom)

/-- The exact-extension completion map agrees with the field embedding
on elements of the base number field. -/
theorem finitePlaceExtensionAdicCompletionMap_coe
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : K) :
    finitePlaceExtensionAdicCompletionMap K L w a
        (x : w.adicCompletion K) =
      (algebraMap K L x :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L) := by
  have hcomparison :
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          (x : w.adicCompletion K) =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x := by
    change
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          (algebraMap K (w.adicCompletion K) x) =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x
    exact (relativeFinitePlaceCompletionAlgEquiv w).symm.commutes x
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm
            (x : w.adicCompletion K))) =
      _
  rw [hcomparison,
    AbsoluteValue.completionMap_coe,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- The completion map defined using an exact absolute-value extension
is continuous. -/
theorem finitePlaceExtensionAdicCompletionMap_continuous
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    Continuous
      (finitePlaceExtensionAdicCompletionMap K L w a) := by
  have hrelative :
      Isometry (relativeFinitePlaceCompletionAlgEquiv w).symm :=
    AddMonoidHomClass.isometry_of_norm
      (relativeFinitePlaceCompletionAlgEquiv w).symm
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm w)
  exact
    ((relativeFinitePlaceCompletionRingHom_isometry
      (finitePlaceExtensionCentre
        (K := K) (L := L) w a)).continuous.comp
      (finitePlaceExtensionCompletionRingEquiv_continuous
        (K := K) (L := L) w a)).comp
      ((AbsoluteValue.completionMap_isometry
        (HeightOneSpectrum.adicAbv K w) a.1 a.2).continuous.comp
        hrelative.continuous)

/-- The exact-extension construction and the canonical completion of the
field embedding agree.  Equality on the dense copy of `K` is extended by
continuity. -/
theorem finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    finitePlaceExtensionAdicCompletionMap K L w a x =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a) x := by
  let P : (w.valuation K).Completion → Prop := fun y =>
    finitePlaceExtensionAdicCompletionMap K L w a
        (HeightOneSpectrum.adicCompletion.ofCompletion y) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (HeightOneSpectrum.adicCompletion.ofCompletion y)
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (w.valuation K)) x.toCompletion ?_ ?_
  · change IsClosed
      {y | finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion y) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion y)}
    exact isClosed_eq
      ((finitePlaceExtensionAdicCompletionMap_continuous K L w a).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
      ((finitePlaceAdicCompletionMap_continuous K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
  · intro r
    let k : K := WithVal.equiv (w.valuation K) r
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion)) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion))
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          (k : w.adicCompletion K) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (k : w.adicCompletion K)
    rw [finitePlaceExtensionAdicCompletionMap_coe,
      finitePlaceAdicCompletionMap_coe]
    change
      (algebraMap K L k :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L) =
      (algebraMap K L k :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L)
    rfl

/-- The concrete completion at a finite place above `w` is finite over the
concrete completion at `w`, for the canonical completion map. -/
theorem finitePlaceAdicCompletionMap_moduleFinite
    [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    letI : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L w W).toAlgebra
    Module.Finite (w.adicCompletion K) (W.1.adicCompletion L) := by
  classical
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : Algebra
      (w.adicCompletion K)
      ((finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a).1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L w
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a)).toAlgebra
  let : Module
      (w.adicCompletion K)
      ((finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a).1.adicCompletion L) :=
    Algebra.toModule
  let : Algebra (w.adicCompletion K) vK.Completion :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom.toAlgebra
  let : Algebra vK.Completion a.1.Completion :=
    AbsoluteValue.completionAlgebra vK a.1 a.2
  let : Algebra (w.adicCompletion K) a.1.Completion :=
    ((algebraMap vK.Completion a.1.Completion).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom).toAlgebra
  let : IsScalarTower
      (w.adicCompletion K) vK.Completion a.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (w.adicCompletion K) vK.Completion :=
    Module.Finite.of_surjective
      (Algebra.linearMap (w.adicCompletion K) vK.Completion)
      (relativeFinitePlaceCompletionAlgEquiv w).symm.surjective
  let : Module.Finite vK.Completion a.1.Completion :=
    completionModuleFinite vK hvK a
  let : Module.Finite (w.adicCompletion K) a.1.Completion :=
    Module.Finite.trans vK.Completion a.1.Completion
  let e :
      a.1.Completion ≃ₐ[w.adicCompletion K]
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a).1.adicCompletion L :=
    { __ :=
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w a
      commutes' := fun x => by
        change
          finitePlaceExtensionAdicCompletionMap K L w a x =
            finitePlaceAdicCompletionMap K L w
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) w a) x
        exact
          finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
            K L w a x }
  exact Module.Finite.equiv e.toLinearEquiv

/-- The norm of the image under the concrete adic-completion map is
raised to the exact-extension exponent. -/
theorem finitePlaceExtensionAdicCompletionMap_norm
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) w a := by
  change
    ‖finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm x))‖ =
      _
  rw [
    finitePlaceExtensionAdicCompletionRingEquiv_norm,
    (AbsoluteValue.completionMap_isometry
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).norm_map_of_map_zero
        (map_zero
          (AbsoluteValue.completionMap
            (HeightOneSpectrum.adicAbv K w) a.1 a.2)),
    relativeFinitePlaceCompletionAlgEquiv_symm_norm]

/-- The canonical map between concrete adic completions preserves the
valuation ring, expressed by the norm bound defining its unit ball. -/
theorem finitePlaceAdicCompletionMap_norm_le_one_iff
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    ‖finitePlaceAdicCompletionMap K L w W x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  have hnorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
        ‖finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a) x‖ :=
    congrArg (fun y => ‖y‖)
      (finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
        K L w a x)
  rw [← hnorm,
    finitePlaceExtensionAdicCompletionMap_norm]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
      (finitePlaceExtensionExponent_pos
        (K := K) (L := L) w a)

/-- The valuation of the image under the concrete adic-completion map
is multiplied by the ramification index.  This extends the corresponding
formula for elements of `K` to every element of the completion. -/
theorem finitePlaceExtensionAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceExtensionAdicCompletionMap K L w a x) =
      Valued.v x ^ w.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).asIdeal := by
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) w a
  let : W.asIdeal.LiesOver w.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) w a
  by_cases hx : x = 0
  · subst x
    have he :
        w.asIdeal.ramificationIdx' W.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
        W.asIdeal w.ne_bot
    simp only [map_zero]
    exact (zero_pow he).symm
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x.toCompletion
  let k : K := WithVal.equiv (w.valuation K) r
  have hkval : w.valuation K k = Valued.v x := by
    change Valued.v r = Valued.v x
    rw [← HeightOneSpectrum.adicCompletion.valued_toCompletion]
    exact hr.symm
  have hk : k ≠ 0 := by
    intro hk
    have : Valued.v x = 0 := by
      rw [← hkval, hk, map_zero]
    apply hx
    simpa using this
  let z : w.adicCompletion K := x * (k : w.adicCompletion K)⁻¹
  have hzval : Valued.v z = 1 := by
    simp [z, hkval, hx]
  have hznorm : ‖z‖ = 1 := by
    simp [FinitePlace.norm_def, hzval]
  have hmapznorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a z‖ = 1 := by
    rw [finitePlaceExtensionAdicCompletionMap_norm, hznorm]
    simp
  have hmapzval :
      Valued.v
        (finitePlaceExtensionAdicCompletionMap K L w a z) = 1 := by
    rw [FinitePlace.norm_def] at hmapznorm
    exact
      (WithZeroMulInt.toNNReal_eq_one_iff
        (Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a z))
        (HeightOneSpectrum.absNorm_ne_zero W)
        (HeightOneSpectrum.one_lt_absNorm_nnreal W).ne').mp
        (NNReal.eq hmapznorm)
  have hkcoe :
      (k : w.adicCompletion K) ≠ 0 := by
    change algebraMap K (w.adicCompletion K) k ≠ 0
    exact (map_ne_zero
      (algebraMap K (w.adicCompletion K))).2 hk
  have hx_factor :
      x = z * (k : w.adicCompletion K) := by
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ hkcoe, mul_one]
  calc
    Valued.v
        (finitePlaceExtensionAdicCompletionMap K L w a x) =
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (z * (k : w.adicCompletion K))) := by
          rw [← hx_factor]
    _ = Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a z) *
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [map_mul, map_mul]
    _ = Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [hmapzval, one_mul]
    _ = W.valuation L (algebraMap K L k) := by
          rw [finitePlaceExtensionAdicCompletionMap_coe,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    _ = (w.valuation K k) ^
          w.asIdeal.ramificationIdx' W.asIdeal :=
      (HeightOneSpectrum.valuation_liesOver L w W k).symm
    _ = Valued.v x ^
          w.asIdeal.ramificationIdx' W.asIdeal := by
      rw [hkval]

/-- Under the canonical map to a place above `w`, the completed
valuation is raised to the ramification index. -/
theorem finitePlaceAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceAdicCompletionMap K L w W x) =
      Valued.v x ^ w.asIdeal.ramificationIdx' W.1.asIdeal := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [←
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap]
  exact finitePlaceExtensionAdicCompletionMap_valued K L w a x
