/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowPoint
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210

/-!
# Exactness of tensoring with a dualizable object

The first stage of the reduction of the local splitting statement:
tensoring with a two-sided dualizable object is exact, because the
exact pairings make the tensor functor a left and a right adjoint
at once.  A short exact sequence therefore stays short exact after
tensoring, which produces the internal-hom extension that the
pullback stage consumes.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

section Exactness

/-- Tensoring on the left with an object with a left dual
preserves colimits: the exact pairing makes it a left adjoint. -/
theorem tensorLeftPreservesColimits [Category.{v} D] [MonoidalCategory D]
    (X : D)
    [HasLeftDual X] : PreservesColimitsOfSize.{0, 0}
      (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

/-- Tensoring on the left with an object with a right dual
preserves limits: the exact pairing makes it a right adjoint. -/
theorem tensorLeftPreservesLimits [Category.{v} D] [MonoidalCategory D]
    (X : D)
    [HasRightDual X] : PreservesLimitsOfSize.{0, 0}
      (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

/-- **Tensoring with a two-sided dualizable object is exact**:
a short exact sequence stays short exact after tensoring on the
left. -/
theorem ShortExact_tensorLeft [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    {S : ShortComplex D}
    (hS : S.ShortExact) (X : D) [HasLeftDual X]
    [HasRightDual X] :
    (S.map (tensorLeft X)).ShortExact := by
  have := tensorLeftPreservesColimits X
  have := tensorLeftPreservesLimits X
  have : PreservesFiniteColimits (tensorLeft X) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteLimits (tensorLeft X) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact hS.map_of_exact (tensorLeft X)

end Exactness

section Reduction

/-- The name of the identity: the coevaluation, braided into the
evaluation source. -/
noncomputable def unitName
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X : D) [HasRightDual X] :
    𝟙_ D ⟶ (Xᘁ) ⊗ X :=
  η_ X (Xᘁ) ≫ (β_ X (Xᘁ)).hom

/-- The middle object of the unit-form extension: the pullback of
the internal-hom epimorphism along the name of the identity. -/
noncomputable def unitFormMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual S.X₃] : D :=
  pullback (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃)

/-- The inclusion of the unit-form extension. -/
noncomputable def unitFormIn
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual S.X₃] :
    ((S.X₃)ᘁ) ⊗ S.X₁ ⟶ unitFormMid S :=
  pullback.lift (((S.X₃)ᘁ) ◁ S.f) 0
    (by rw [← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp])

/-- **The unit-form extension**: the given sequence, internally
hommed and pulled back along the name of the identity, now with
unit quotient. -/
noncomputable def unitForm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual S.X₃] :
    ShortComplex D :=
  ShortComplex.mk (unitFormIn S)
    (pullback.snd (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃))
    (pullback.lift_snd _ _ _)

/-- Defining square of the inclusion. -/
theorem unitFormIn_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual S.X₃] :
    unitFormIn S ≫ pullback.fst (((S.X₃)ᘁ) ◁ S.g)
        (unitName S.X₃) =
      ((S.X₃)ᘁ) ◁ S.f :=
  pullback.lift_fst _ _ _

/-- **The unit-form extension is short exact**: the pullback of a
short exact sequence along a point of its quotient. -/
theorem unitForm_shortExact
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual S.X₃]
    [HasLeftDual ((S.X₃)ᘁ : D)] [HasRightDual ((S.X₃)ᘁ : D)]
    (hS : S.ShortExact) :
    (unitForm S).ShortExact := by
  have hT := ShortExact_tensorLeft hS ((S.X₃)ᘁ)
  have hmf : Mono (((S.X₃)ᘁ) ◁ S.f) := hT.mono_f
  have : Mono ((S.map (tensorLeft ((S.X₃)ᘁ))).f) := hT.mono_f
  have hepig : Epi (((S.X₃)ᘁ) ◁ S.g) := hT.epi_g
  have hw : (((S.X₃)ᘁ) ◁ S.f) ≫ (((S.X₃)ᘁ) ◁ S.g) = 0 := by
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero]
  have hfker : IsLimit (KernelFork.ofι (((S.X₃)ᘁ) ◁ S.f) hw) :=
    hT.exact.fIsKernel
  have hmono : Mono (unitFormIn S) := by
    have h1 : Mono (unitFormIn S ≫
        pullback.fst (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃)) := by
      rw [unitFormIn_fst]; exact hmf
    exact mono_of_mono (unitFormIn S)
      (pullback.fst (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃))
  have : Mono ((unitForm S).f) := hmono
  have hker : IsLimit (KernelFork.ofι (unitForm S).f
      (unitForm S).zero) := by
    refine KernelFork.IsLimit.ofι' _ _ (fun {W} t ht => ?_)
    have htf : (t ≫ pullback.fst (((S.X₃)ᘁ) ◁ S.g)
        (unitName S.X₃)) ≫ (((S.X₃)ᘁ) ◁ S.g) = 0 :=
      (Category.assoc _ _ _).trans
        ((whisker_eq t pullback.condition).trans
          ((Category.assoc _ _ _).symm.trans
            ((eq_whisker ht _).trans zero_comp)))
    obtain ⟨u, hu⟩ := KernelFork.IsLimit.lift' hfker
      (t ≫ pullback.fst _ _) htf
    refine ⟨u, ?_⟩
    have h2 : (unitForm S).f ≫ pullback.fst
        (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃) =
      ((S.X₃)ᘁ) ◁ S.f := unitFormIn_fst S
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans
        ((whisker_eq u h2).trans hu)
    · exact (Category.assoc _ _ _).trans
        ((whisker_eq u (unitForm S).zero).trans
          (comp_zero.trans ht.symm))
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hker
          mono_f := hmono
          epi_g := Abelian.epi_pullback_of_epi_f
            (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃) }

end Reduction

section MateDetect

/-- **Epimorphisms dualise to monomorphisms**: the right adjoint
mate of an epimorphism is monic. -/
theorem mono_rightAdjointMate [Category.{v} D] [MonoidalCategory D]
    {X Y : D} [HasRightDual X]
    [HasRightDual Y]
    [∀ W : D, (tensorLeft W).PreservesEpimorphisms]
    (f : X ⟶ Y) (hf : Epi f) :
    Mono (fᘁ) := by
  have := hf
  constructor
  intro W a b h
  have : Epi (W ◁ f) := (tensorLeft W).map_epi f
  have hslide : ∀ c : W ⟶ ((Yᘁ) : D),
      ((c ≫ fᘁ) ▷ X) ≫ ε_ X (Xᘁ) =
        (W ◁ f) ≫ (c ▷ Y) ≫ ε_ Y (Yᘁ) := by
    intro c
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      rightAdjointMate_comp_evaluation,
      ← Category.assoc, ← whisker_exchange, Category.assoc]
  have key : (W ◁ f) ≫ (a ▷ Y) ≫ ε_ Y (Yᘁ) =
      (W ◁ f) ≫ (b ▷ Y) ≫ ε_ Y (Yᘁ) := by
    rw [← hslide a, ← hslide b, h]
  have hΨ : (a ▷ Y) ≫ ε_ Y (Yᘁ) = (b ▷ Y) ≫ ε_ Y (Yᘁ) :=
    (cancel_epi (W ◁ f)).mp key
  have h2 := congrArg (tensorRightHomEquiv W Y (Yᘁ) (𝟙_ D)) hΨ
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation,
    tensorRightHomEquiv_whiskerRight_comp_evaluation] at h2
  exact (cancel_mono (λ_ ((Yᘁ) : D)).inv).mp h2

end MateDetect

section PointDual

/-- The dual of the unit, canonically. -/
noncomputable def unitDualIso
    [Category.{v} D] [MonoidalCategory D] : (𝟙_ D : D) ≅ ((𝟙_ D : D)ᘁ) :=
  rightDualIso exactPairingUnit inferInstance

/-- **The monic point of the dual**: the unit-form quotient,
dualised into a point of the dual of the middle object. -/
noncomputable def unitFormPoint
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)] : 𝟙_ D ⟶ ((unitFormMid S)ᘁ) :=
  unitDualIso.hom ≫ ((unitForm S).g)ᘁ

/-- The point is monic when the sequence is short exact. -/
theorem mono_unitFormPoint
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    [HasLeftDual (((S.X₃)ᘁ) : D)]
    [HasRightDual (((S.X₃)ᘁ) : D)]
    [∀ W : D, (tensorLeft W).PreservesEpimorphisms]
    (hS : S.ShortExact) :
    Mono (unitFormPoint S) := by
  have hm := mono_rightAdjointMate (X := unitFormMid S)
    (Y := 𝟙_ D) ((unitForm S).g)
    ((unitForm_shortExact S hS).epi_g)
  exact mono_comp' inferInstance hm

end PointDual

section Transfer

open scoped MonObj

/-- The coevaluation meets the canonical unit-dual inverse as the
unit pairing's coevaluation. -/
theorem coevaluation_unitDualIso_inv [Category.{v} D] [MonoidalCategory D] :
    η_ (𝟙_ D) ((𝟙_ D)ᘁ) ≫ ((𝟙_ D) ◁ unitDualIso.inv) =
      (ρ_ (𝟙_ D)).inv := by
  have h := @coevaluation_comp_rightAdjointMate D _ _
    (𝟙_ D) (𝟙_ D) ⟨𝟙_ D⟩ inferInstance (𝟙 (𝟙_ D))
  rw [MonoidalCategory.id_whiskerRight, Category.comp_id] at h
  exact h

/-- **The point section**: the coevaluation, carried through a
class of the dual of the middle object. -/
noncomputable def pointSection
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D)
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    𝟙_ D ⟶ unitFormMid S ⊗ B :=
  η_ (unitFormMid S) ((unitFormMid S)ᘁ) ≫
    (unitFormMid S ◁ cls)

/-- The coevaluation carries the quotient onto the point, through
the canonical unit-dual identification. -/
theorem coevaluation_unitFormPoint
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)] :
    η_ (𝟙_ D) ((𝟙_ D)ᘁ) ≫
        ((𝟙_ D) ◁ (unitDualIso.inv ≫ unitFormPoint S)) =
      η_ (unitFormMid S) ((unitFormMid S)ᘁ) ≫
        ((unitForm S).g ▷ ((unitFormMid S)ᘁ)) := by
  rw [unitFormPoint, Iso.inv_hom_id_assoc]
  exact @coevaluation_comp_rightAdjointMate D _ _
    (unitFormMid S) (𝟙_ D) inferInstance hasRightDualUnit
    ((unitForm S).g)

/-- **The section property of the point section**: against the
unit-form quotient, a class restricting on the point to the unit
of the algebra yields the unit itself. -/
theorem pointSection_section
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    pointSection S B cls ≫ ((unitForm S).g ▷ B) =
      (ρ_ (𝟙_ D)).inv ≫ ((𝟙_ D) ◁ η[B]) := by
  have h1 : (unitFormMid S ◁ cls) ≫ ((unitForm S).g ▷ B) =
      ((unitForm S).g ▷ ((unitFormMid S)ᘁ)) ≫
        ((𝟙_ D) ◁ cls) :=
    whisker_exchange _ _
  have h' : (unitDualIso.inv ≫ unitFormPoint S) ≫ cls =
      unitDualIso.inv ≫ η[B] :=
    (Category.assoc _ _ _).trans (whisker_eq _ hcls)
  exact (Category.assoc _ _ _).trans
    ((whisker_eq (η_ _ _) h1).trans
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker (coevaluation_unitFormPoint S).symm _).trans
          ((Category.assoc _ _ _).trans
            ((whisker_eq (η_ _ _)
                (MonoidalCategory.whiskerLeft_comp _ _ _).symm
              ).trans
              ((whisker_eq (η_ _ _)
                  (congrArg (fun t => (𝟙_ D) ◁ t) h')).trans
                ((whisker_eq (η_ _ _)
                    (MonoidalCategory.whiskerLeft_comp
                      _ _ _)).trans
                  ((Category.assoc _ _ _).symm.trans
                    (eq_whisker
                      (coevaluation_unitDualIso_inv) _)))))))))

/-- **The free section carrier**: the point section, folded into
the free module through the multiplication. -/
noncomputable def freeSectionHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    B ⊗ 𝟙_ D ⟶ B ⊗ unitFormMid S :=
  (B ◁ pointSection S B cls) ≫
    (B ◁ (β_ (unitFormMid S) B).hom) ≫
    (α_ B B (unitFormMid S)).inv ≫
    (μ[B] ▷ unitFormMid S)

/-- **The free section splits the quotient**: when the class
restricts on the point to the unit, the free section carrier is a
section of the whiskered quotient. -/
theorem freeSectionHom_section
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    freeSectionHom S B cls ≫ (B ◁ (unitForm S).g) =
      𝟙 (B ⊗ 𝟙_ D) := by
  have h1 : (μ[B] ▷ unitFormMid S) ≫ (B ◁ (unitForm S).g) =
      ((B ⊗ B) ◁ (unitForm S).g) ≫ (μ[B] ▷ (𝟙_ D)) :=
    (whisker_exchange _ _).symm
  have h2 : (α_ B B (unitFormMid S)).inv ≫
      ((B ⊗ B) ◁ (unitForm S).g) =
    (B ◁ (B ◁ (unitForm S).g)) ≫ (α_ B B (𝟙_ D)).inv :=
    (associator_inv_naturality_right _ _ _).symm
  have h3 : (β_ (unitFormMid S) B).hom ≫
      (B ◁ (unitForm S).g) =
    ((unitForm S).g ▷ B) ≫ (β_ (𝟙_ D) B).hom :=
    (BraidedCategory.braiding_naturality_left _ _).symm
  have h4 : pointSection S B cls ≫ ((unitForm S).g ▷ B) =
      (ρ_ (𝟙_ D)).inv ≫ ((𝟙_ D) ◁ η[B]) :=
    pointSection_section S B cls hcls
  have h5 : ((𝟙_ D) ◁ η[B]) ≫ (β_ (𝟙_ D) B).hom =
      (β_ (𝟙_ D) (𝟙_ D)).hom ≫ (η[B] ▷ (𝟙_ D)) :=
    (BraidedCategory.braiding_naturality_right _ _)
  -- The inner element: the point section pushed through the
  -- quotient and the braiding is the unit against the unitor.
  have hinner : pointSection S B cls ≫
      (β_ (unitFormMid S) B).hom ≫ (B ◁ (unitForm S).g) =
    (ρ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)) :=
    (whisker_eq _ h3).trans
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker h4 _).trans
          ((Category.assoc _ _ _).trans
            ((whisker_eq _ h5).trans
              ((whisker_eq _
                  (eq_whisker braiding_unit_self _)).trans
                (whisker_eq _ (Category.id_comp _)))))))
  have hfold : (B ◁ ((ρ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)))) ≫
      (α_ B B (𝟙_ D)).inv ≫ (μ[B] ▷ (𝟙_ D)) =
    𝟙 (B ⊗ 𝟙_ D) := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.comp_whiskerRight, MonObj.mul_one]
    monoidal
  have hstart : freeSectionHom S B cls ≫ (B ◁ (unitForm S).g) =
      (B ◁ pointSection S B cls) ≫
        (B ◁ (β_ (unitFormMid S) B).hom) ≫
        (B ◁ (B ◁ (unitForm S).g)) ≫
        (α_ B B (𝟙_ D)).inv ≫ (μ[B] ▷ (𝟙_ D)) := by
    rw [freeSectionHom]
    simp only [Category.assoc]
    rw [h1]
    exact whisker_eq _ (whisker_eq _
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker h2 _).trans (Category.assoc _ _ _))))
  have hpack : (B ◁ pointSection S B cls) ≫
        (B ◁ (β_ (unitFormMid S) B).hom) ≫
        (B ◁ (B ◁ (unitForm S).g)) ≫
        (α_ B B (𝟙_ D)).inv ≫ (μ[B] ▷ (𝟙_ D)) =
      (B ◁ (pointSection S B cls ≫
        (β_ (unitFormMid S) B).hom ≫ (B ◁ (unitForm S).g))) ≫
        (α_ B B (𝟙_ D)).inv ≫ (μ[B] ▷ (𝟙_ D)) := by
    repeat' erw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hreplace := congrArg (fun t => (B ◁ t) ≫
    (α_ B B (𝟙_ D)).inv ≫ (μ[B] ▷ (𝟙_ D))) hinner
  exact hstart.trans (hpack.trans (hreplace.trans hfold))

/-- **Extend a point to the free module**: any morphism into the
carrier of a module extends to a linear map from the free module,
through the action. -/
noncomputable def freeModExtend [Category.{v} D] [MonoidalCategory D]
    (B : D) [MonObj B] {V : D}
    (M : Mod D B) (q : V ⟶ M.X) : freeMod B V ⟶ M :=
  Mod.Hom.mk' ((B ◁ q) ≫ actLeft B M.X)
    (by
      change ((α_ B B V).inv ≫ (μ[B] ▷ V)) ≫
          ((B ◁ q) ≫ actLeft B M.X) =
        (B ◁ ((B ◁ q) ≫ actLeft B M.X)) ≫ actLeft B M.X
      have h1 : (μ[B] ▷ V) ≫ (B ◁ q) =
          ((B ⊗ B) ◁ q) ≫ (μ[B] ▷ M.X) :=
        (whisker_exchange _ _).symm
      have h3 : (α_ B B V).inv ≫ ((B ⊗ B) ◁ q) =
          (B ◁ (B ◁ q)) ≫ (α_ B B M.X).inv :=
        (associator_inv_naturality_right _ _ _).symm
      calc ((α_ B B V).inv ≫ (μ[B] ▷ V)) ≫
          ((B ◁ q) ≫ actLeft B M.X)
          = (α_ B B V).inv ≫ ((μ[B] ▷ V) ≫ (B ◁ q)) ≫
              actLeft B M.X := by
            simp only [Category.assoc]
        _ = (α_ B B V).inv ≫ (((B ⊗ B) ◁ q) ≫
              (μ[B] ▷ M.X)) ≫ actLeft B M.X := by rw [h1]
        _ = ((α_ B B V).inv ≫ ((B ⊗ B) ◁ q)) ≫
              (μ[B] ▷ M.X) ≫ actLeft B M.X := by
            simp only [Category.assoc]
        _ = ((B ◁ (B ◁ q)) ≫ (α_ B B M.X).inv) ≫
              (μ[B] ▷ M.X) ≫ actLeft B M.X := by rw [h3]
        _ = (B ◁ (B ◁ q)) ≫ (α_ B B M.X).inv ≫
              (α_ B B M.X).hom ≫ (B ◁ actLeft B M.X) ≫
              actLeft B M.X := by
            rw [mul_actLeft]
            simp only [Category.assoc]
        _ = (B ◁ (B ◁ q)) ≫ (B ◁ actLeft B M.X) ≫
              actLeft B M.X := by rw [Iso.inv_hom_id_assoc]
        _ = (B ◁ ((B ◁ q) ≫ actLeft B M.X)) ≫
              actLeft B M.X := by
            simp only [MonoidalCategory.whiskerLeft_comp,
              Category.assoc])

/-- **The free section**: the point section, braided and extended
to the free module. -/
noncomputable def freeSection
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    freeMod B (𝟙_ D) ⟶ freeMod B (unitFormMid S) :=
  freeModExtend B (freeMod B (unitFormMid S))
    (pointSection S B cls ≫ (β_ (unitFormMid S) B).hom)

/-- The free section's carrier is the folded point section. -/
theorem freeSection_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    (freeSection S B cls).hom = freeSectionHom S B cls := by
  change (B ◁ (pointSection S B cls ≫
        (β_ (unitFormMid S) B).hom)) ≫
      ((α_ B B (unitFormMid S)).inv ≫
        (μ[B] ▷ unitFormMid S)) =
    freeSectionHom S B cls
  rw [freeSectionHom]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- **Contract the dual against the argument**: braid the payload
out and evaluate. -/
noncomputable def evalContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X W : D) [HasRightDual X] :
    (((Xᘁ) : D) ⊗ W) ⊗ X ⟶ W :=
  ((β_ ((Xᘁ) : D) W).hom ▷ X) ≫ (α_ W ((Xᘁ) : D) X).hom ≫
    (W ◁ ε_ X (Xᘁ)) ≫ (ρ_ W).hom

/-- The contraction is natural in the payload. -/
theorem evalContract_natural
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X : D) [HasRightDual X]
    {W W' : D} (h : W ⟶ W') :
    ((((Xᘁ) : D) ◁ h) ▷ X) ≫ evalContract X W' =
      evalContract X W ≫ h := by
  rw [evalContract, evalContract]
  have h1 : (((Xᘁ) : D) ◁ h) ≫ (β_ ((Xᘁ) : D) W').hom =
      (β_ ((Xᘁ) : D) W).hom ≫ (h ▷ ((Xᘁ) : D)) :=
    BraidedCategory.braiding_naturality_right _ _
  have h2 : ((h ▷ ((Xᘁ) : D)) ▷ X) ≫ (α_ W' _ X).hom =
      (α_ W _ X).hom ≫ (h ▷ (((Xᘁ) : D) ⊗ X)) :=
    associator_naturality_left _ _ _
  have h3 : (h ▷ (((Xᘁ) : D) ⊗ X)) ≫ (W' ◁ ε_ X (Xᘁ)) =
      (W ◁ ε_ X (Xᘁ)) ≫ (h ▷ (𝟙_ D)) :=
    (whisker_exchange _ _).symm
  have h4 : (h ▷ (𝟙_ D)) ≫ (ρ_ W').hom = (ρ_ W).hom ≫ h := by
    simp
  calc ((((Xᘁ) : D) ◁ h) ▷ X) ≫ (β_ ((Xᘁ) : D) W').hom ▷ X ≫
      (α_ W' ((Xᘁ) : D) X).hom ≫ (W' ◁ ε_ X (Xᘁ)) ≫
      (ρ_ W').hom
      = ((((β_ ((Xᘁ) : D) W).hom ≫ (h ▷ ((Xᘁ) : D)))) ▷ X) ≫
          (α_ W' ((Xᘁ) : D) X).hom ≫ (W' ◁ ε_ X (Xᘁ)) ≫
          (ρ_ W').hom := by
        rw [← MonoidalCategory.comp_whiskerRight_assoc, h1]
    _ = ((β_ ((Xᘁ) : D) W).hom ▷ X) ≫
          ((h ▷ ((Xᘁ) : D)) ▷ X) ≫
          (α_ W' ((Xᘁ) : D) X).hom ≫ (W' ◁ ε_ X (Xᘁ)) ≫
          (ρ_ W').hom := by
        rw [MonoidalCategory.comp_whiskerRight,
          Category.assoc]
    _ = ((β_ ((Xᘁ) : D) W).hom ▷ X) ≫ (α_ W _ X).hom ≫
          (h ▷ (((Xᘁ) : D) ⊗ X)) ≫ (W' ◁ ε_ X (Xᘁ)) ≫
          (ρ_ W').hom := by
        rw [← Category.assoc ((h ▷ ((Xᘁ) : D)) ▷ X), h2,
          Category.assoc]
    _ = ((β_ ((Xᘁ) : D) W).hom ▷ X) ≫ (α_ W _ X).hom ≫
          (W ◁ ε_ X (Xᘁ)) ≫ (h ▷ (𝟙_ D)) ≫ (ρ_ W').hom := by
        rw [← Category.assoc (h ▷ (((Xᘁ) : D) ⊗ X)), h3,
          Category.assoc]
    _ = ((β_ ((Xᘁ) : D) W).hom ▷ X) ≫ (α_ W _ X).hom ≫
          (W ◁ ε_ X (Xᘁ)) ≫ (ρ_ W).hom ≫ h := by
        rw [h4]
    _ = (((β_ ((Xᘁ) : D) W).hom ▷ X) ≫ (α_ W _ X).hom ≫
          (W ◁ ε_ X (Xᘁ)) ≫ (ρ_ W).hom) ≫ h := by
        simp only [Category.assoc]

/-- **The zigzag of the name**: the name of the identity,
contracted against the argument, is the unitor. -/
theorem unitName_evalContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X : D) [HasRightDual X] :
    ((unitName X) ▷ X) ≫ evalContract X X = (λ_ X).hom := by
  rw [unitName, evalContract, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  have hββ : ((β_ X ((Xᘁ) : D)).hom ▷ X) ≫
      ((β_ ((Xᘁ) : D) X).hom ▷ X) = 𝟙 _ := by
    rw [← MonoidalCategory.comp_whiskerRight,
      SymmetricCategory.symmetry,
      MonoidalCategory.id_whiskerRight]
  have hzig := ExactPairing.evaluation_coevaluation X ((Xᘁ) : D)
  calc (η_ X (Xᘁ) ▷ X) ≫ ((β_ X ((Xᘁ) : D)).hom ▷ X) ≫
      ((β_ ((Xᘁ) : D) X).hom ▷ X) ≫ (α_ X ((Xᘁ) : D) X).hom ≫
      (X ◁ ε_ X (Xᘁ)) ≫ (ρ_ X).hom
      = (η_ X (Xᘁ) ▷ X) ≫ (α_ X ((Xᘁ) : D) X).hom ≫
          (X ◁ ε_ X (Xᘁ)) ≫ (ρ_ X).hom := by
        rw [← Category.assoc ((β_ X ((Xᘁ) : D)).hom ▷ X), hββ,
          Category.id_comp]
    _ = ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by
        rw [← Category.assoc, ← Category.assoc,
          Category.assoc (η_ X (Xᘁ) ▷ X), hzig]
    _ = (λ_ X).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The element of the free section**: the unit, pushed through
the free section and out of the pullback. -/
noncomputable def freeSectionPoint
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    𝟙_ D ⟶ B ⊗ (((S.X₃)ᘁ) ⊗ S.X₂) :=
  (λ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)) ≫
    (freeSection S B cls).hom ≫
    (B ◁ pullback.fst (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃))

/-- The element carries the internal quotient onto the name. -/
theorem freeSectionPoint_g
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    freeSectionPoint S B cls ≫ (B ◁ (((S.X₃)ᘁ) ◁ S.g)) =
      (λ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)) ≫
        (B ◁ unitName S.X₃) := by
  have hpull : (B ◁ pullback.fst (((S.X₃)ᘁ) ◁ S.g)
      (unitName S.X₃)) ≫ (B ◁ (((S.X₃)ᘁ) ◁ S.g)) =
    (B ◁ (unitForm S).g) ≫ (B ◁ unitName S.X₃) := by
    erw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun t => B ◁ t) pullback.condition
  have hsec : (freeSection S B cls).hom ≫
      (B ◁ (unitForm S).g) = 𝟙 (B ⊗ 𝟙_ D) := by
    rw [freeSection_hom]
    exact freeSectionHom_section S B cls hcls
  have hsection : (freeSection S B cls).hom ≫
      (B ◁ pullback.fst (((S.X₃)ᘁ) ◁ S.g) (unitName S.X₃)) ≫
      (B ◁ (((S.X₃)ᘁ) ◁ S.g)) = B ◁ unitName S.X₃ :=
    (whisker_eq _ hpull).trans
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker hsec _).trans (Category.id_comp _)))
  rw [freeSectionPoint]
  simp only [Category.assoc]
  exact whisker_eq _ (whisker_eq _
    ((Category.assoc _ _ _).trans hsection))

/-- **The transferred point**: the free-section element,
contracted against the argument. -/
noncomputable def sectionPoint
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    S.X₃ ⟶ B ⊗ S.X₂ :=
  (λ_ (S.X₃)).inv ≫ (freeSectionPoint S B cls ▷ S.X₃) ≫
    (α_ B ((((S.X₃)ᘁ) ⊗ S.X₂)) (S.X₃)).hom ≫
    (B ◁ evalContract (S.X₃) (S.X₂))

/-- **The transferred point splits the quotient**: against the
quotient it is the unit against the argument. -/
theorem sectionPoint_g
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    sectionPoint S B cls ≫ (B ◁ S.g) =
      (λ_ (S.X₃)).inv ≫ (η[B] ▷ S.X₃) := by
  have hnat : (B ◁ evalContract (S.X₃) (S.X₂)) ≫
      (B ◁ S.g) =
    (B ◁ (((((S.X₃)ᘁ) : D) ◁ S.g) ▷ S.X₃)) ≫
      (B ◁ evalContract (S.X₃) (S.X₃)) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun t => B ◁ t)
      (evalContract_natural (S.X₃) S.g).symm
  have hα : (α_ B ((((S.X₃)ᘁ) ⊗ S.X₂)) (S.X₃)).hom ≫
      (B ◁ (((((S.X₃)ᘁ) : D) ◁ S.g) ▷ S.X₃)) =
    ((B ◁ ((((S.X₃)ᘁ) : D) ◁ S.g)) ▷ S.X₃) ≫
      (α_ B ((((S.X₃)ᘁ) ⊗ S.X₃)) (S.X₃)).hom :=
    (associator_naturality_middle _ _ _).symm
  have hfsp : (freeSectionPoint S B cls ▷ S.X₃) ≫
      ((B ◁ ((((S.X₃)ᘁ) : D) ◁ S.g)) ▷ S.X₃) =
    (((λ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)) ≫
      (B ◁ unitName S.X₃)) ▷ S.X₃) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      freeSectionPoint_g S B cls hcls]
  have hname : ((B ◁ unitName S.X₃) ▷ S.X₃) ≫
      (α_ B ((((S.X₃)ᘁ) ⊗ S.X₃)) (S.X₃)).hom ≫
      (B ◁ evalContract (S.X₃) (S.X₃)) =
    (α_ B (𝟙_ D) (S.X₃)).hom ≫ (B ◁ (λ_ (S.X₃)).hom) := by
    rw [associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp,
      unitName_evalContract]
  have hη : (((η[B] ▷ (𝟙_ D))) ▷ S.X₃) ≫
      (α_ B (𝟙_ D) (S.X₃)).hom ≫ (B ◁ (λ_ (S.X₃)).hom) =
    (α_ (𝟙_ D) (𝟙_ D) (S.X₃)).hom ≫
      ((𝟙_ D) ◁ (λ_ (S.X₃)).hom) ≫ (η[B] ▷ S.X₃) := by
    rw [associator_naturality_left_assoc]
    exact whisker_eq _ (whisker_exchange _ _).symm
  have hcoh : (λ_ (S.X₃)).inv ≫
      (((λ_ (𝟙_ D)).inv) ▷ S.X₃) ≫
      (α_ (𝟙_ D) (𝟙_ D) (S.X₃)).hom ≫
      ((𝟙_ D) ◁ (λ_ (S.X₃)).hom) = (λ_ (S.X₃)).inv := by
    monoidal
  calc sectionPoint S B cls ≫ (B ◁ S.g)
      = (λ_ (S.X₃)).inv ≫ (freeSectionPoint S B cls ▷ S.X₃) ≫
          (α_ B ((((S.X₃)ᘁ) ⊗ S.X₂)) (S.X₃)).hom ≫
          ((B ◁ evalContract (S.X₃) (S.X₂)) ≫ (B ◁ S.g)) := by
        rw [sectionPoint]
        simp only [Category.assoc]
    _ = (λ_ (S.X₃)).inv ≫ (freeSectionPoint S B cls ▷ S.X₃) ≫
          ((α_ B ((((S.X₃)ᘁ) ⊗ S.X₂)) (S.X₃)).hom ≫
            (B ◁ (((((S.X₃)ᘁ) : D) ◁ S.g) ▷ S.X₃))) ≫
          (B ◁ evalContract (S.X₃) (S.X₃)) := by
        rw [hnat]
        simp only [Category.assoc]
    _ = (λ_ (S.X₃)).inv ≫
          ((freeSectionPoint S B cls ▷ S.X₃) ≫
            ((B ◁ ((((S.X₃)ᘁ) : D) ◁ S.g)) ▷ S.X₃)) ≫
          (α_ B ((((S.X₃)ᘁ) ⊗ S.X₃)) (S.X₃)).hom ≫
          (B ◁ evalContract (S.X₃) (S.X₃)) := by
        rw [hα]
        simp only [Category.assoc]
    _ = (λ_ (S.X₃)).inv ≫
          ((((λ_ (𝟙_ D)).inv ≫ (η[B] ▷ (𝟙_ D)) ≫
            (B ◁ unitName S.X₃)) ▷ S.X₃)) ≫
          (α_ B ((((S.X₃)ᘁ) ⊗ S.X₃)) (S.X₃)).hom ≫
          (B ◁ evalContract (S.X₃) (S.X₃)) := by
        rw [hfsp]
    _ = (λ_ (S.X₃)).inv ≫ (((λ_ (𝟙_ D)).inv) ▷ S.X₃) ≫
          (((η[B] ▷ (𝟙_ D))) ▷ S.X₃) ≫
          (((B ◁ unitName S.X₃)) ▷ S.X₃ ≫
            (α_ B ((((S.X₃)ᘁ) ⊗ S.X₃)) (S.X₃)).hom ≫
            (B ◁ evalContract (S.X₃) (S.X₃))) := by
        simp only [MonoidalCategory.comp_whiskerRight,
          Category.assoc]
    _ = (λ_ (S.X₃)).inv ≫ (((λ_ (𝟙_ D)).inv) ▷ S.X₃) ≫
          (((η[B] ▷ (𝟙_ D))) ▷ S.X₃) ≫
          (α_ B (𝟙_ D) (S.X₃)).hom ≫
          (B ◁ (λ_ (S.X₃)).hom) := by
        rw [hname]
    _ = (λ_ (S.X₃)).inv ≫ (((λ_ (𝟙_ D)).inv) ▷ S.X₃) ≫
          (α_ (𝟙_ D) (𝟙_ D) (S.X₃)).hom ≫
          ((𝟙_ D) ◁ (λ_ (S.X₃)).hom) ≫ (η[B] ▷ S.X₃) := by
        rw [hη]
    _ = (λ_ (S.X₃)).inv ≫ (η[B] ▷ S.X₃) := by
        rw [reassoc_of% hcoh]

/-- **The section of the statement of record**: the transferred
point, extended to the free module. -/
noncomputable def rappel210Section
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B) :
    freeMod B (S.X₃) ⟶ freeMod B (S.X₂) :=
  freeModExtend B (freeMod B (S.X₂)) (sectionPoint S B cls)

/-- **The section splits the base-changed epimorphism**. -/
theorem rappel210Section_splits
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (B : D) [MonObj B]
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    rappel210Section S B cls ≫ freeModMap B S.g =
      𝟙 (freeMod B (S.X₃)) :=
  Mod.hom_ext _ _ (by
    change ((B ◁ sectionPoint S B cls) ≫
        ((α_ B B (S.X₂)).inv ≫ (μ[B] ▷ S.X₂))) ≫
        (B ◁ S.g) =
      𝟙 (B ⊗ S.X₃)
    have h1 : (μ[B] ▷ S.X₂) ≫ (B ◁ S.g) =
        ((B ⊗ B) ◁ S.g) ≫ (μ[B] ▷ S.X₃) :=
      (whisker_exchange _ _).symm
    have h2 : (α_ B B (S.X₂)).inv ≫ ((B ⊗ B) ◁ S.g) =
        (B ◁ (B ◁ S.g)) ≫ (α_ B B (S.X₃)).inv :=
      (associator_inv_naturality_right _ _ _).symm
    have h3 : (B ◁ sectionPoint S B cls) ≫
        (B ◁ (B ◁ S.g)) =
      B ◁ ((λ_ (S.X₃)).inv ≫ (η[B] ▷ S.X₃)) := by
      rw [← MonoidalCategory.whiskerLeft_comp,
        sectionPoint_g S B cls hcls]
    have hfold : (B ◁ ((λ_ (S.X₃)).inv ≫ (η[B] ▷ S.X₃))) ≫
        (α_ B B (S.X₃)).inv ≫ (μ[B] ▷ S.X₃) =
      𝟙 (B ⊗ S.X₃) := by
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
        associator_inv_naturality_middle_assoc,
        ← MonoidalCategory.comp_whiskerRight, MonObj.mul_one]
      monoidal
    calc ((B ◁ sectionPoint S B cls) ≫
        ((α_ B B (S.X₂)).inv ≫ (μ[B] ▷ S.X₂))) ≫
        (B ◁ S.g)
        = (B ◁ sectionPoint S B cls) ≫
            (α_ B B (S.X₂)).inv ≫
            (((B ⊗ B) ◁ S.g) ≫ (μ[B] ▷ S.X₃)) := by
          simp only [Category.assoc]
          rw [h1]
      _ = (B ◁ sectionPoint S B cls) ≫ (B ◁ (B ◁ S.g)) ≫
            (α_ B B (S.X₃)).inv ≫ (μ[B] ▷ S.X₃) := by
          rw [← Category.assoc (α_ B B (S.X₂)).inv, h2]
          simp only [Category.assoc]
      _ = (B ◁ ((λ_ (S.X₃)).inv ≫ (η[B] ▷ S.X₃))) ≫
            (α_ B B (S.X₃)).inv ≫ (μ[B] ▷ S.X₃) := by
          rw [← Category.assoc (B ◁ sectionPoint S B cls), h3]
      _ = 𝟙 (B ⊗ S.X₃) := hfold)

/-- **The local splitting statement holds given a unital class on
the dual of the unit-form middle object**: the full reduction. -/
theorem rappel210_of_class
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (hS : S.ShortExact) (B : D)
    [MonObj B] [IsCommMonObj B] (hnz : η[B] ≠ 0)
    (cls : ((unitFormMid S)ᘁ) ⟶ B)
    (hcls : unitFormPoint S ≫ cls = η[B]) :
    Rappel210Statement S hS :=
  ⟨B, ‹MonObj B›, ‹IsCommMonObj B›, hnz,
    rappel210Section S B cls, rappel210Section_splits S B cls hcls⟩

end Transfer

end RS
