/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Product-Haar realization of Zhou's quadratic fiber shear.  The proof first
splits the actual compact dual into its two kernel summands, applies the
fiber-translation theorem to the product Haar measure, and transports the
result back to Zhou's coordinates. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualTopology

/-!
The dual shear measure component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperDualShearMeasure

open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperDualTopology
open PaperFactorIsomorphism
open MeasureTheory

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `Dadd` construction used in the Connes rigidity formalization.
-/
abbrev Dadd := PaperKernel.D
/--
The `Padd` construction used in the Connes rigidity formalization.
-/
abbrev Padd := PaperKernel.AVStar
/--
The `Qadd` construction used in the Connes rigidity formalization.
-/
abbrev Qadd := PaperKernel.C
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := Multiplicative Dadd
/--
The `P` construction used in the Connes rigidity formalization.
-/
abbrev P := Multiplicative Padd
/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := Multiplicative Qadd
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace

/- The two summand kernels use their discrete topologies. Paper: §3. -/
noncomputable instance paperAVStarTopology : TopologicalSpace P := ⊥
noncomputable instance paperCTopology : TopologicalSpace Q := ⊥
instance paperAVStarDiscrete : DiscreteTopology P := discreteTopology_bot _
instance paperCDiscrete : DiscreteTopology Q := discreteTopology_bot _

noncomputable instance paperAVStarCountable : Countable P :=
  Countable.of_equiv Padd Multiplicative.ofAdd
noncomputable instance paperCCountable : Countable Q :=
  Countable.of_equiv Qadd Multiplicative.ofAdd
/--
The `PChar` construction used in the Connes rigidity formalization.
-/
abbrev PChar := PontryaginDual P
/--
The `QChar` construction used in the Connes rigidity formalization.
-/
abbrev QChar := PontryaginDual Q

noncomputable instance paperAVCharSecondCountable :
    SecondCountableTopology PChar :=
  ContinuousMonoidHom.isClosedEmbedding_coe.toIsEmbedding.secondCountableTopology
noncomputable instance paperCCharSecondCountable :
    SecondCountableTopology QChar :=
  ContinuousMonoidHom.isClosedEmbedding_coe.toIsEmbedding.secondCountableTopology
noncomputable instance paperAVAdditiveSecondCountable :
    SecondCountableTopology (Additive PChar) :=
  paperAVCharSecondCountable
noncomputable instance paperCAdditiveSecondCountable :
    SecondCountableTopology (Additive QChar) :=
  paperCCharSecondCountable

noncomputable instance paperAVCharMeasurableSpace :
    MeasurableSpace (Additive PChar) := borel (Additive PChar)
instance paperAVCharBorelSpace : BorelSpace (Additive PChar) := ⟨rfl⟩
noncomputable instance paperCCharMeasurableSpace :
    MeasurableSpace (Additive QChar) := borel (Additive QChar)
instance paperCCharBorelSpace : BorelSpace (Additive QChar) := ⟨rfl⟩

/- Continuous inclusions and the product splitting of the discrete kernel.
Paper: §3.
-/
/--
The `pInl` construction used in the Connes rigidity formalization.
-/
def pInl : P →ₜ* D where
  toFun x := Multiplicative.ofAdd (x.toAdd, 0)
  map_one' := by rfl
  map_mul' x y := by rfl
  continuous_toFun := continuous_of_discreteTopology

/--
The `qInr` construction used in the Connes rigidity formalization.
-/
def qInr : Q →ₜ* D where
  toFun x := Multiplicative.ofAdd (0, x.toAdd)
  map_one' := by rfl
  map_mul' x y := by rfl
  continuous_toFun := continuous_of_discreteTopology

/--
The `productToD` construction used in the Connes rigidity formalization.
-/
def productToD : (P × Q) →ₜ* D where
  toFun x := Multiplicative.ofAdd (x.1.toAdd, x.2.toAdd)
  map_one' := by rfl
  map_mul' x y := by rfl
  continuous_toFun := continuous_of_discreteTopology

/--
The `dToProduct` construction used in the Connes rigidity formalization.
-/
def dToProduct : D →ₜ* (P × Q) where
  toFun x := (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  map_one' := by rfl
  map_mul' x y := by rfl
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem productToD_dToProduct (x : D) :
    productToD (dToProduct x) = x := by
  rfl

@[simp] theorem dToProduct_productToD (x : P × Q) :
    dToProduct (productToD x) = x := by
  rfl

/-- The actual dual is the product of the two compact summand duals.
Paper: §3.
-/
def productToCharacter (p : Additive PChar × Additive QChar) : CharacterSpace :=
  Additive.ofMul (((Additive.toMul p.1).coprod (Additive.toMul p.2)).comp
    dToProduct)

/--
The `characterToProduct` construction used in the Connes rigidity formalization.
-/
def characterToProduct (χ : CharacterSpace) : Additive PChar × Additive QChar :=
  (Additive.ofMul ((Additive.toMul χ).comp pInl),
    Additive.ofMul ((Additive.toMul χ).comp qInr))

/--
The `characterProductEquiv` construction used in the Connes rigidity formalization.
-/
def characterProductEquiv : CharacterSpace ≃+
    (Additive PChar × Additive QChar) where
  toFun := characterToProduct
  invFun := productToCharacter
  left_inv χ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (((Additive.toMul (characterToProduct χ).1).coprod
      (Additive.toMul (characterToProduct χ).2)).comp dToProduct) x =
        (Additive.toMul χ) x
    change ((((Additive.toMul χ).comp pInl).coprod
      ((Additive.toMul χ).comp qInr)).comp dToProduct) x =
        (Additive.toMul χ) x
    change (Additive.toMul χ)
          (Multiplicative.ofAdd ((Multiplicative.toAdd x).1, 0)) *
        (Additive.toMul χ)
          (Multiplicative.ofAdd (0, (Multiplicative.toAdd x).2)) =
      (Additive.toMul χ) x
    rw [← map_mul]
    rw [← ofAdd_add]
    simp
  right_inv p := by
    rcases p with ⟨p, q⟩
    apply Prod.ext
    · apply Additive.toMul.injective
      apply PontryaginDual.ext
      intro x
      change (Additive.toMul p) x * (Additive.toMul q) 1 =
        (Additive.toMul p) x
      simp
    · apply Additive.toMul.injective
      apply PontryaginDual.ext
      intro x
      change (Additive.toMul p) 1 * (Additive.toMul q) x =
        (Additive.toMul q) x
      simp
  map_add' χ ψ := by
    apply Prod.ext
    · apply Additive.toMul.injective
      apply PontryaginDual.ext
      intro x
      change (Additive.toMul χ) (pInl x) *
          (Additive.toMul ψ) (pInl x) =
        (Additive.toMul χ) (pInl x) * (Additive.toMul ψ) (pInl x)
      rfl
    · apply Additive.toMul.injective
      apply PontryaginDual.ext
      intro x
      change (Additive.toMul χ) (qInr x) *
          (Additive.toMul ψ) (qInr x) =
        (Additive.toMul χ) (qInr x) * (Additive.toMul ψ) (qInr x)
      rfl

theorem continuous_characterToProduct : Continuous (characterToProduct :
    CharacterSpace → (Additive PChar × Additive QChar)) := by
  change Continuous (fun χ : CharacterSpace =>
    ((Additive.toMul χ).comp pInl, (Additive.toMul χ).comp qInr))
  exact (ContinuousMonoidHom.continuous_comp_left pInl).prodMk
    (ContinuousMonoidHom.continuous_comp_left qInr)

theorem continuous_productToCharacter : Continuous (productToCharacter :
    (Additive PChar × Additive QChar) → CharacterSpace) := by
  apply (ContinuousMonoidHom.isInducing_toContinuousMap D Circle).continuous_iff.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_prod_of_discrete_right.mpr
  intro x
  change Continuous (fun p : Additive PChar × Additive QChar =>
    (Additive.toMul p.1) (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
      (Additive.toMul p.2) (Multiplicative.ofAdd (Multiplicative.toAdd x).2))
  let _ : ContinuousEvalConst PChar P Circle :=
    ContinuousEvalConst.of_continuous_forget
      (ContinuousMonoidHom.isInducing_toContinuousMap P Circle).continuous
  let _ : ContinuousEvalConst QChar Q Circle :=
    ContinuousEvalConst.of_continuous_forget
      (ContinuousMonoidHom.isInducing_toContinuousMap Q Circle).continuous
  have hp : Continuous (fun p : Additive PChar =>
      (Additive.toMul p) (Multiplicative.ofAdd (Multiplicative.toAdd x).1)) := by
    change Continuous (fun p : PChar =>
      p (Multiplicative.ofAdd (Multiplicative.toAdd x).1))
    exact continuous_eval_const _
  have hq : Continuous (fun q : Additive QChar =>
      (Additive.toMul q) (Multiplicative.ofAdd (Multiplicative.toAdd x).2)) := by
    change Continuous (fun q : QChar =>
      q (Multiplicative.ofAdd (Multiplicative.toAdd x).2))
    exact continuous_eval_const _
  exact (hp.comp continuous_fst).mul (hq.comp continuous_snd)

/--
The `characterProductHomeomorph` construction used in the Connes rigidity formalization.
-/
def characterProductHomeomorph :
    CharacterSpace ≃ₜ (Additive PChar × Additive QChar) :=
  Homeomorph.mk characterProductEquiv.toEquiv
    (by exact continuous_characterToProduct)
    (by exact continuous_productToCharacter)

/-- The compact dual shear and its product-coordinate form. Paper: §3.
-/
def productShear (p : Additive PChar × Additive QChar) :
    Additive PChar × Additive QChar :=
  characterProductEquiv
    (PaperDualTopology.characterFiberShear (productToCharacter p))

theorem continuous_productShear : Continuous productShear := by
  exact characterProductHomeomorph.continuous.comp
    (PaperDualTopology.continuous_characterFiberShear.comp
      characterProductHomeomorph.symm.continuous)

theorem productShear_first (p : Additive PChar × Additive QChar) :
    (productShear p).1 = p.1 := by
  rcases p with ⟨p, q⟩
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro x
  change (Additive.toMul
      (PaperDualTopology.characterFiberShear (productToCharacter (p, q))))
      (pInl x) = (Additive.toMul p) x
  change ZMod.toCircle
      (PaperDualTopology.shearedLinear (productToCharacter (p, q))
        (Multiplicative.toAdd (pInl x))) = _
  rw [PaperDualTopology.shearedLinear_eval]
  change ZMod.toCircle (_ + quadraticMap _ (0 : Qadd)) = _
  rw [map_zero, add_zero]
  rw [BinaryPontryaginDual.characterLinear_circle]
  have hfirst := congrArg
    (fun z : Additive PChar × Additive QChar => z.1)
    (characterProductEquiv.apply_symm_apply (p, q))
  have hvalue := congrArg
    (fun z : Additive PChar => (Additive.toMul z) x) hfirst
  change (Additive.toMul (productToCharacter (p, q))) (pInl x) =
    (Additive.toMul p) x at hvalue
  convert hvalue using 1 ; rfl

theorem productCoordinate_first_eq (p : Additive PChar) (q : Additive QChar) :
    (PaperDualHaar.characterCoordinatesEquiv
      (productToCharacter (p, q))).1 =
      (PaperDualHaar.characterCoordinatesEquiv
        (productToCharacter (p, 0))).1 := by
  apply LinearMap.ext
  intro a
  funext v
  rw [PaperDualTopology.character_coordinate_eval,
    PaperDualTopology.character_coordinate_eval]
  apply ZMod.injective_toCircle
  rw [BinaryPontryaginDual.characterLinear_circle,
    BinaryPontryaginDual.characterLinear_circle]
  have heq := characterProductEquiv.apply_symm_apply (p, q)
  have heq0 := characterProductEquiv.apply_symm_apply (p, 0)
  have hfirst := congrArg
    (fun z : Additive PChar × Additive QChar =>
      (Additive.toMul z.1)
        (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v)))
    heq
  have hfirst0 := congrArg
    (fun z : Additive PChar × Additive QChar =>
      (Additive.toMul z.1)
        (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v)))
    heq0
  change (Additive.toMul (productToCharacter (p, q)))
      (pInl (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v))) =
    (Additive.toMul p)
      (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v)) at hfirst
  change (Additive.toMul (productToCharacter (p, 0)))
      (pInl (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v))) =
    (Additive.toMul p)
      (Multiplicative.ofAdd (a ⊗ₜ[k] LinearMap.proj v)) at hfirst0
  convert hfirst.trans hfirst0.symm using 1 <;> rfl

theorem productShear_second (p : Additive PChar) (q : Additive QChar) :
    (productShear (p, q)).2 = q + (productShear (p, 0)).2 := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro x
  change (Additive.toMul
      (PaperDualTopology.characterFiberShear (productToCharacter (p, q))))
      (qInr x) =
    (Additive.toMul q) x *
      (Additive.toMul
        (PaperDualTopology.characterFiberShear (productToCharacter (p, 0))))
        (qInr x)
  change ZMod.toCircle
      (PaperDualTopology.shearedLinear (productToCharacter (p, q))
        (Multiplicative.toAdd (qInr x))) =
    (Additive.toMul q) x * ZMod.toCircle
      (PaperDualTopology.shearedLinear (productToCharacter (p, 0))
        (Multiplicative.toAdd (qInr x)))
  rw [PaperDualTopology.shearedLinear_eval,
    PaperDualTopology.shearedLinear_eval]
  have hbase := congrArg
    (fun z : Additive PChar × Additive QChar => z.2)
    (characterProductEquiv.apply_symm_apply (p, q))
  have hzero := congrArg
    (fun z : Additive PChar × Additive QChar => z.2)
    (characterProductEquiv.apply_symm_apply (p, 0))
  have hbase' := congrArg
    (fun z : Additive QChar => (Additive.toMul z) x) hbase
  have hzero' := congrArg
    (fun z : Additive QChar => (Additive.toMul z) x) hzero
  change (Additive.toMul (productToCharacter (p, q)))
      (qInr x) = (Additive.toMul q) x at hbase'
  change (Additive.toMul (productToCharacter (p, 0)))
      (qInr x) = (Additive.toMul (0 : Additive QChar)) x at hzero'
  have hbaseCircle :
      ZMod.toCircle
          (BinaryPontryaginDual.characterLinear
            (M := Dadd)
            (Additive.toMul (productToCharacter (p, q)))
            (Multiplicative.toAdd (qInr x))) =
        (Additive.toMul q) x := by
    rw [BinaryPontryaginDual.characterLinear_circle]
    exact hbase'
  have hzeroCircle :
      ZMod.toCircle
          (BinaryPontryaginDual.characterLinear
            (M := Dadd)
            (Additive.toMul (productToCharacter (p, 0)))
            (Multiplicative.toAdd (qInr x))) =
        1 := by
    rw [BinaryPontryaginDual.characterLinear_circle]
    convert hzero' using 1 <;> rfl
  have hquad :
      (quadraticMap (characterCoordinatesEquiv (productToCharacter (p, q))).1)
          (Multiplicative.toAdd (qInr x)).2 =
        (quadraticMap
          (characterCoordinatesEquiv (productToCharacter (p, 0))).1)
          (Multiplicative.toAdd (qInr x)).2 := by
    exact congrArg
        (fun z : PaperFactorIsomorphism.A →ₗ[k]
          PaperFactorIsomorphism.PaperV =>
            quadraticMap z (Multiplicative.toAdd (qInr x)).2)
      (productCoordinate_first_eq p q)
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  rw [hbaseCircle, hzeroCircle, hquad]
  simp

/--
The `productQuadraticCharacter` construction used in the Connes rigidity formalization.
-/
def productQuadraticCharacter (p : Additive PChar) : Additive QChar :=
  (productShear (p, 0)).2

theorem productShear_eq_skew (p : Additive PChar) (q : Additive QChar) :
    productShear (p, q) = (p, q + productQuadraticCharacter p) := by
  apply Prod.ext
  · exact productShear_first (p, q)
  · exact productShear_second p q

theorem continuous_productQuadraticCharacter :
    Continuous productQuadraticCharacter := by
  exact continuous_snd.comp (continuous_productShear.comp
    (continuous_id.prodMk continuous_const))

/- Product Haar is invariant under the quadratic skew map. Paper: §3. -/
theorem productShear_measurePreserving :
    MeasurePreserving productShear
      (NormalizedHaar.productHaar (Additive PChar) (Additive QChar))
      (NormalizedHaar.productHaar (Additive PChar) (Additive QChar)) := by
  have h := NormalizedHaar.skew_add_translation_measurePreserving
    (NormalizedHaar.normalizedAddHaar (Additive PChar))
    (NormalizedHaar.normalizedAddHaar (Additive QChar))
    (0 : Additive PChar) (0 : Additive QChar)
    productQuadraticCharacter continuous_productQuadraticCharacter
  rw [NormalizedHaar.productHaar]
  convert h using 1
  funext z
  rcases z with ⟨p, q⟩
  simpa only [zero_add] using productShear_eq_skew p q

theorem characterProductHaar_map :
    Measure.map characterProductEquiv PaperDualHaar.paperCharacterHaar =
      NormalizedHaar.productHaar (Additive PChar) (Additive QChar) := by
  let μ := PaperDualHaar.paperCharacterHaar
  have _ : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, PaperDualHaar.paperCharacterHaar]
    infer_instance
  have _ : Measure.IsAddHaarMeasure (Measure.map characterProductEquiv μ) :=
    AddEquiv.isAddHaarMeasure_map μ characterProductEquiv
      characterProductHomeomorph.continuous
      characterProductHomeomorph.symm.continuous
  have _ : IsProbabilityMeasure (Measure.map characterProductEquiv μ) :=
    μ.isProbabilityMeasure_map
      characterProductHomeomorph.continuous.measurable.aemeasurable
  rw [NormalizedHaar.productHaar_eq_normalizedAddHaar]
  exact NormalizedHaar.normalizedAddHaar_unique _
    (Measure.map characterProductEquiv μ)

/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

/--
The `coordinateProductEquiv` construction used in the Connes rigidity formalization.
-/
def coordinateProductEquiv : Coordinates ≃+
    (Additive PChar × Additive QChar) :=
  PaperDualHaar.characterCoordinatesEquiv.symm.trans characterProductEquiv

/--
The `coordinateProductHomeomorph` construction used in the Connes rigidity formalization.
-/
def coordinateProductHomeomorph : Coordinates ≃ₜ
    (Additive PChar × Additive QChar) :=
  PaperDualTopology.characterCoordinatesHomeomorph.symm.trans
    characterProductHomeomorph

noncomputable instance coordinatesSecondCountable :
    SecondCountableTopology Coordinates :=
  (PaperDualTopology.characterCoordinatesHomeomorph.symm.isInducing).secondCountableTopology

theorem coordinateProduct_shear_conj (p : Coordinates) :
    coordinateProductEquiv (PaperFactorIsomorphism.fiberShear p) =
      productShear (coordinateProductEquiv p) := by
  change characterProductEquiv
      (PaperDualHaar.characterCoordinatesEquiv.symm
        (PaperFactorIsomorphism.fiberShear p)) = _
  have htransport := PaperDualTopology.characterFiberShear_eq_transport
    (PaperDualHaar.characterCoordinatesEquiv.symm p)
  have htransport' :
      PaperDualHaar.characterCoordinatesEquiv.symm
          (PaperFactorIsomorphism.fiberShear p) =
        PaperDualTopology.characterFiberShear
          (PaperDualHaar.characterCoordinatesEquiv.symm p) := by
    simpa using htransport.symm
  rw [htransport']
  unfold productShear coordinateProductEquiv
  change characterProductEquiv
      (characterFiberShear (PaperDualHaar.characterCoordinatesEquiv.symm p)) =
    characterProductEquiv
      (characterFiberShear
        (productToCharacter
          (characterProductEquiv
            (PaperDualHaar.characterCoordinatesEquiv.symm p))))
  have hinv :
      productToCharacter
          (characterProductEquiv
            (PaperDualHaar.characterCoordinatesEquiv.symm p)) =
        PaperDualHaar.characterCoordinatesEquiv.symm p := by
    simpa [characterProductEquiv] using
      characterProductEquiv.left_inv
        (PaperDualHaar.characterCoordinatesEquiv.symm p)
  rw [hinv]

theorem coordinateHaar_map :
    Measure.map coordinateProductEquiv PaperDualTopology.coordinatesHaar =
      NormalizedHaar.productHaar (Additive PChar) (Additive QChar) := by
  let μ := PaperDualTopology.coordinatesHaar
  have _ : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, PaperDualTopology.coordinatesHaar]
    infer_instance
  have _ : Measure.IsAddHaarMeasure (Measure.map coordinateProductEquiv μ) :=
    AddEquiv.isAddHaarMeasure_map μ coordinateProductEquiv
      coordinateProductHomeomorph.continuous
      coordinateProductHomeomorph.symm.continuous
  have _ : IsProbabilityMeasure (Measure.map coordinateProductEquiv μ) :=
    μ.isProbabilityMeasure_map
      coordinateProductHomeomorph.continuous.measurable.aemeasurable
  rw [NormalizedHaar.productHaar_eq_normalizedAddHaar]
  exact NormalizedHaar.normalizedAddHaar_unique _
    (Measure.map coordinateProductEquiv μ)

/- The Zhou fiber shear preserves the transported normalized Haar measure.
Paper: §3. -/
theorem fiberShear_measurePreserving :
    MeasurePreserving PaperFactorIsomorphism.fiberShear
      PaperDualTopology.coordinatesHaar PaperDualTopology.coordinatesHaar := by
  refine ⟨PaperDualTopology.measurable_fiberShear, ?_⟩
  apply coordinateProductHomeomorph.measurableEmbedding.map_injective
  have hconj :
      coordinateProductEquiv ∘ PaperFactorIsomorphism.fiberShear =
        productShear ∘ coordinateProductEquiv := by
    funext p
    exact coordinateProduct_shear_conj p
  calc
    Measure.map coordinateProductEquiv
        (Measure.map PaperFactorIsomorphism.fiberShear
          PaperDualTopology.coordinatesHaar) =
        Measure.map (coordinateProductEquiv ∘
          PaperFactorIsomorphism.fiberShear)
          PaperDualTopology.coordinatesHaar := by
            simpa only [Function.comp_def] using
              (Measure.map_map
                coordinateProductHomeomorph.continuous.measurable
                PaperDualTopology.measurable_fiberShear
                (μ := PaperDualTopology.coordinatesHaar)
                (f := PaperFactorIsomorphism.fiberShear)
                (g := coordinateProductEquiv))
    _ = Measure.map (productShear ∘ coordinateProductEquiv)
          PaperDualTopology.coordinatesHaar := by rw [hconj]
    _ = Measure.map productShear
          (Measure.map coordinateProductEquiv
            PaperDualTopology.coordinatesHaar) := by
            simpa only [Function.comp_def] using
              (Measure.map_map
                continuous_productShear.measurable
                coordinateProductHomeomorph.continuous.measurable
                (μ := PaperDualTopology.coordinatesHaar)
                (f := coordinateProductEquiv)
                (g := productShear)).symm
    _ = Measure.map productShear
          (NormalizedHaar.productHaar (Additive PChar) (Additive QChar)) := by
            rw [coordinateHaar_map]
    _ = NormalizedHaar.productHaar (Additive PChar) (Additive QChar) :=
      productShear_measurePreserving.map_eq
    _ = Measure.map coordinateProductEquiv
          PaperDualTopology.coordinatesHaar := coordinateHaar_map.symm

end
end PaperDualShearMeasure
end Connes
