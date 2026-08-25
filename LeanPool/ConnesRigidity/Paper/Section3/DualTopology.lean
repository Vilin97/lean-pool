/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Topological and measurable structure on Zhou's dual coordinates.  The
topology is transported from the actual compact character group, so the
coordinate model is not an unrelated product placeholder.
Paper: §§3--4.
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualActions

/-!
The dual topology component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperDualTopology

open MeasureTheory
open Construction
open Construction.PaperKernel
open BinaryPontryaginDual
open PaperDualHaar
open PaperDualCoordinates
open PaperFactorIsomorphism

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `TensorAA` construction used in the Connes rigidity formalization.
-/
abbrev TensorAA := PaperKernel.TensorAA
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

theorem avDualEquiv_apply_proj (F : Module.Dual k PaperKernel.AVStar)
    (a : Construction.A) (v : OpenAIPort.SymplecticIndex) :
    (PaperDualCoordinates.avDualEquiv F a) v =
      F (a ⊗ₜ[k] LinearMap.proj v) := by
  have h := congrArg (fun g : PaperKernel.VStar →ₗ[k]
      Module.Dual k Construction.A => g (LinearMap.proj v) a)
    (PaperDualCoordinates.transposeEquiv.apply_symm_apply
      (PaperDualCoordinates.dualTensorPartialEquiv F))
  exact h

/- The binary value of a character at a fixed kernel element varies
continuously in the compact character. Paper: §3. -/
theorem continuous_characterLinear_eval (d : D) :
    Continuous (fun χ : CharacterSpace =>
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) d) := by
  rw [continuous_def]
  intro s hs
  classical
  have hopen (a : k) : IsOpen {χ : CharacterSpace |
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) d = a} := by
    have hto : Continuous (Additive.toMul : CharacterSpace →
        PontryaginDual (Multiplicative D)) := by
      change Continuous (id : CharacterSpace →
        PontryaginDual (Multiplicative D))
      exact continuous_id
    let _ : ContinuousEvalConst (PontryaginDual (Multiplicative D))
        (Multiplicative D) Circle :=
      ContinuousEvalConst.of_continuous_forget
        (ContinuousMonoidHom.isInducing_toContinuousMap
          (Multiplicative D) Circle).continuous
    have hcircle : Continuous (fun χ : CharacterSpace =>
        (Additive.toMul χ) (Multiplicative.ofAdd d)) :=
      (continuous_eval_const (Multiplicative.ofAdd d)).comp hto
    have hpre : IsOpen {χ : CharacterSpace |
        (Additive.toMul χ) (Multiplicative.ofAdd d) ≠
          ZMod.toCircle (a + 1)} :=
      isOpen_ne.preimage hcircle
    convert hpre using 1
    ext χ
    simp only [Set.mem_ofPred_eq]
    rw [← BinaryPontryaginDual.characterLinear_circle
      (M := D) (Additive.toMul χ) d]
    rw [ZMod.injective_toCircle.ne_iff]
    exact (show ∀ a b : k, b = a ↔ b ≠ a + 1 from by decide)
      a (BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) d)
  have hs' : (fun χ : CharacterSpace =>
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) d) ⁻¹' s =
      ⋃ a ∈ s, {χ : CharacterSpace |
        BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) d = a} := by
    ext χ
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq,
      exists_prop, exists_eq_right']
  rw [hs']
  apply isOpen_iUnion
  intro a
  exact isOpen_iUnion fun _ => hopen a

/- The two raw coordinate projections are evaluations of the actual full
dual. Paper: §3. -/
theorem character_coordinate_eval (χ : CharacterSpace)
    (a : Construction.A) (v : OpenAIPort.SymplecticIndex) :
    (PaperDualHaar.characterCoordinatesEquiv χ).1 a v =
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) (a ⊗ₜ[k] LinearMap.proj v, 0) := by
  let F := (Module.dualProdDualEquivDual k PaperKernel.AVStar PaperKernel.C).symm
    (PaperDualHaar.characterLinearEquiv χ)
  have h := avDualEquiv_apply_proj F.1 a v
  simpa [F, PaperDualHaar.characterCoordinatesEquiv,
    PaperDualHaar.characterLinearEquiv, PaperDualHaar.characterToLinear,
    PaperDualCoordinates.dualEquiv, Module.dualProdDualEquivDual] using h

theorem character_second_eval (χ : CharacterSpace)
    (c : PaperKernel.C) :
    (PaperDualHaar.characterCoordinatesEquiv χ).2 c =
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) (0, c) := by
  simp [PaperDualHaar.characterCoordinatesEquiv,
    PaperDualHaar.characterLinearEquiv, PaperDualHaar.characterToLinear,
    PaperDualCoordinates.dualEquiv, Module.dualProdDualEquivDual]

/- The quadratic term is continuous in the compact character variable.  The
proof expands only the finite tensor input, matching Zhou's fiber model.
Paper: §3. -/
theorem continuous_character_quadratic_eval (c : PaperKernel.C) :
    Continuous (fun χ : CharacterSpace =>
      PaperFactorIsomorphism.quadraticMap
        (PaperDualHaar.characterCoordinatesEquiv χ).1 c) := by
  let zfun : CharacterSpace →
      (Construction.A →ₗ[k] PaperKernel.PaperV) := fun χ =>
    (PaperDualHaar.characterCoordinatesEquiv χ).1
  let qfun : (Construction.A →ₗ[k] PaperKernel.PaperV) →
      TensorAA → k := fun z x =>
    PaperFactorIsomorphism.tensorFunctional
        (PaperFactorIsomorphism.coordinate z (Sum.inl 0))
        (PaperFactorIsomorphism.coordinate z (Sum.inr 0)) x +
      PaperFactorIsomorphism.tensorFunctional
        (PaperFactorIsomorphism.coordinate z (Sum.inl 1))
        (PaperFactorIsomorphism.coordinate z (Sum.inr 1)) x
  have hcoord (a : Construction.A) (i : OpenAIPort.SymplecticIndex) :
      Continuous (fun χ : CharacterSpace => zfun χ a i) := by
    apply (continuous_characterLinear_eval
      (d := (a ⊗ₜ[k] LinearMap.proj i, 0))).congr
    intro χ
    dsimp [zfun]
    exact (character_coordinate_eval χ a i).symm
  have hq : ∀ x : TensorAA, Continuous (fun χ => qfun (zfun χ) x) := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simpa [qfun] using
        (continuous_const : Continuous (fun _ : CharacterSpace => (0 : k)))
    · intro a b
      dsimp [qfun]
      have h := ((hcoord a (Sum.inl 0)).mul (hcoord b (Sum.inr 0))).add
        ((hcoord a (Sum.inl 1)).mul (hcoord b (Sum.inr 1)))
      convert h using 1
      funext χ
      rfl
    · intro x y hx hy
      have h := hx.add hy
      convert h using 1
      funext χ
      dsimp [qfun]
      simp only [map_add]
      abel
  have hc := hq (c : TensorAA)
  simpa [qfun, zfun, PaperFactorIsomorphism.quadraticMap,
    PaperFactorIsomorphism.tensorFunctionalOnC] using hc

/- The quadratic fiber shear is lifted from the raw Zhou coordinates to the
full binary dual. Paper: §3.
-/
/--
The `shearedLinear` construction used in the Connes rigidity formalization.
-/
def shearedLinear (χ : CharacterSpace) : Module.Dual k D :=
  PaperDualCoordinates.dualEquiv.symm
    (PaperFactorIsomorphism.fiberShear
      (PaperDualCoordinates.dualEquiv
        (PaperDualHaar.characterLinearEquiv χ)))

theorem shearedLinear_eval (χ : CharacterSpace) (d : D) :
    shearedLinear χ d =
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) d +
        PaperFactorIsomorphism.quadraticMap
          (PaperDualHaar.characterCoordinatesEquiv χ).1 d.2 := by
  rcases d with ⟨u, c⟩
  simp only [shearedLinear, PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual, LinearEquiv.trans_symm,
    LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm,
    LinearEquiv.symm_symm, PaperFactorIsomorphism.fiberShear,
    PaperDualHaar.characterLinearEquiv, PaperDualHaar.characterToLinear,
    AddEquiv.ofBijective_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearEquiv.trans_apply, LinearMap.coprodEquiv_symm_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    PaperFactorIsomorphism.quadraticMap, Fin.isValue,
    LinearEquiv.symm_apply_apply, LinearMap.coprodEquiv_apply,
    LinearMap.coprod_apply, LinearMap.coe_comp, LinearMap.coe_inl,
    Function.comp_apply, LinearMap.add_apply, LinearMap.coe_inr,
    PaperDualHaar.characterCoordinatesEquiv, AddEquiv.trans_apply,
    AddEquiv.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk]
  have hchar :
      BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) (u, 0) +
        BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) (0, c) =
        BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) (u, c) := by
    rw [← map_add]
    simp
  rw [← add_assoc, hchar]

/-- Every fixed kernel element has a continuous value after the fiber shear.
Paper: §3. -/
theorem continuous_shearedLinear_eval (d : D) :
    Continuous (fun χ : CharacterSpace => shearedLinear χ d) := by
  apply ((continuous_characterLinear_eval (d := d)).add
    (continuous_character_quadratic_eval d.2)).congr
  intro χ
  exact (shearedLinear_eval χ d).symm

/- The sheared linear form is converted back to the compact binary character.
Paper: §3.
-/
/--
The `characterFiberShearMul` construction used in the Connes rigidity formalization.
-/
def characterFiberShearMul (χ : CharacterSpace) :
    PontryaginDual (Multiplicative D) :=
  PaperDualHaar.linearCharacter (shearedLinear χ)

/-- The character-valued shear is continuous in the compact-open topology.
Paper: §3. -/
theorem continuous_characterFiberShearMul :
    Continuous characterFiberShearMul := by
  apply (ContinuousMonoidHom.isInducing_toContinuousMap
    (Multiplicative D) Circle).continuous_iff.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  let _ : ContinuousEval (PontryaginDual (Multiplicative D))
      (Multiplicative D) Circle :=
    ContinuousEval.of_continuous_forget
      (ContinuousMonoidHom.isInducing_toContinuousMap
        (Multiplicative D) Circle).continuous
  apply continuous_prod_of_discrete_right.mpr
  intro x
  change Continuous (fun χ : CharacterSpace =>
    ZMod.toCircle (shearedLinear χ (Multiplicative.toAdd x)))
  exact continuous_of_discreteTopology.comp
    (continuous_shearedLinear_eval (Multiplicative.toAdd x))

/- The compact character form of the Zhou fiber shear. Paper: §3.
-/
/--
The `characterFiberShear` construction used in the Connes rigidity formalization.
-/
def characterFiberShear (χ : CharacterSpace) : CharacterSpace :=
  Additive.ofMul (characterFiberShearMul χ)

theorem characterFiberShear_eq_transport (χ : CharacterSpace) :
    characterFiberShear χ =
      PaperDualHaar.characterCoordinatesEquiv.symm
        (PaperFactorIsomorphism.fiberShear
          (PaperDualHaar.characterCoordinatesEquiv χ)) := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro x
  change ZMod.toCircle (shearedLinear χ (Multiplicative.toAdd x)) =
    (Additive.toMul
      (PaperDualHaar.characterCoordinatesEquiv.symm
        (PaperFactorIsomorphism.fiberShear
          (PaperDualHaar.characterCoordinatesEquiv χ))))
      (Multiplicative.ofAdd (Multiplicative.toAdd x))
  rw [← BinaryPontryaginDual.characterLinear_circle
    (M := D)
    (Additive.toMul
      (PaperDualHaar.characterCoordinatesEquiv.symm
        (PaperFactorIsomorphism.fiberShear
          (PaperDualHaar.characterCoordinatesEquiv χ))))
    (Multiplicative.toAdd x)]
  have hlin :
      BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul
            (PaperDualHaar.characterCoordinatesEquiv.symm
              (PaperFactorIsomorphism.fiberShear
                (PaperDualHaar.characterCoordinatesEquiv χ)))) =
        shearedLinear χ := by
    change PaperDualHaar.characterLinearEquiv
        (PaperDualHaar.characterCoordinatesEquiv.symm
          (PaperFactorIsomorphism.fiberShear
            (PaperDualHaar.characterCoordinatesEquiv χ))) =
      PaperDualCoordinates.dualEquiv.symm
        (PaperFactorIsomorphism.fiberShear
          (PaperDualHaar.characterCoordinatesEquiv χ))
    simp [PaperDualHaar.characterCoordinatesEquiv]
  rw [hlin]

/- The compact character shear is continuous before transporting it to raw
coordinates. Paper: §3. -/
theorem continuous_characterFiberShear : Continuous characterFiberShear := by
  change Continuous (fun χ => Additive.ofMul (characterFiberShearMul χ))
  exact continuous_characterFiberShearMul

/- The actual dual-coordinate topology is the topology transported along
the algebraic Zhou coordinate equivalence. Paper: §3. -/
noncomputable instance paperCoordinatesTopology : TopologicalSpace Coordinates :=
  TopologicalSpace.induced (PaperDualHaar.characterCoordinatesEquiv.symm)
    inferInstance

/-- The character/coordinate equivalence is a homeomorphism for the
transported topology. Paper: §3. -/
def characterCoordinatesHomeomorph : CharacterSpace ≃ₜ Coordinates :=
  Homeomorph.mk PaperDualHaar.characterCoordinatesEquiv.toEquiv
    (by
      apply continuous_induced_rng.mpr
      have he :
          (PaperDualHaar.characterCoordinatesEquiv.symm ∘
            PaperDualHaar.characterCoordinatesEquiv.toFun) =
            (id : CharacterSpace → CharacterSpace) := by
        funext x
        exact PaperDualHaar.characterCoordinatesEquiv.symm_apply_apply x
      rw [he]
      exact continuous_id)
    continuous_induced_dom

noncomputable instance coordinatesCompactSpace : CompactSpace Coordinates :=
  characterCoordinatesHomeomorph.compactSpace

instance coordinatesIsTopologicalAddGroup : IsTopologicalAddGroup Coordinates where
  continuous_add := by
    apply continuous_induced_rng.mpr
    have h₁ : Continuous (fun p : Coordinates × Coordinates =>
        PaperDualHaar.characterCoordinatesEquiv.symm p.1) :=
      continuous_induced_dom.comp continuous_fst
    have h₂ : Continuous (fun p : Coordinates × Coordinates =>
        PaperDualHaar.characterCoordinatesEquiv.symm p.2) :=
      continuous_induced_dom.comp continuous_snd
    convert continuous_add.comp (h₁.prodMk h₂) using 1
    funext p
    simp
  continuous_neg := by
    apply continuous_induced_rng.mpr
    have h := continuous_neg.comp
      (continuous_induced_dom : Continuous
        (PaperDualHaar.characterCoordinatesEquiv.symm :
          Coordinates → CharacterSpace))
    simpa [Function.comp_def] using h

/- Borel structure for the transported compact model. Paper: §3. -/
noncomputable instance coordinatesMeasurableSpace : MeasurableSpace Coordinates :=
  borel Coordinates

instance coordinatesBorelSpace : BorelSpace Coordinates := ⟨rfl⟩

/- The raw Zhou fiber shear is continuous for the transported topology.
Paper: §3. -/
theorem continuous_fiberShear :
    Continuous (PaperFactorIsomorphism.fiberShear : Coordinates → Coordinates) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Coordinates =>
    PaperDualHaar.characterCoordinatesEquiv.symm
      (PaperFactorIsomorphism.fiberShear p))
  have h : Continuous (characterFiberShear ∘
      (PaperDualHaar.characterCoordinatesEquiv.symm :
        Coordinates → CharacterSpace)) :=
    continuous_characterFiberShear.comp
      (continuous_induced_dom : Continuous
        (PaperDualHaar.characterCoordinatesEquiv.symm :
          Coordinates → CharacterSpace))
  have heq :
      (fun p : Coordinates =>
        PaperDualHaar.characterCoordinatesEquiv.symm
          (PaperFactorIsomorphism.fiberShear p)) =
        characterFiberShear ∘
          (PaperDualHaar.characterCoordinatesEquiv.symm :
            Coordinates → CharacterSpace) := by
    funext p
    simp only [Function.comp_apply]
    simpa using
      (characterFiberShear_eq_transport
        (PaperDualHaar.characterCoordinatesEquiv.symm p)).symm
  rw [heq]
  exact h

theorem measurable_fiberShear :
    Measurable (PaperFactorIsomorphism.fiberShear : Coordinates → Coordinates) :=
  continuous_fiberShear.measurable

/-- The normalized Haar probability in raw Zhou coordinates. Paper: §3. -/
noncomputable def coordinatesHaar : Measure Coordinates :=
  NormalizedHaar.normalizedAddHaar Coordinates

instance coordinatesHaar_isProbability : IsProbabilityMeasure coordinatesHaar := by
  unfold coordinatesHaar
  infer_instance

instance coordinatesHaar_isAddHaar :
    Measure.IsAddLeftInvariant coordinatesHaar := by
  unfold coordinatesHaar
  infer_instance

end
end PaperDualTopology
end Connes
