/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Fourier coordinates for the actual discrete kernel in Zhou §3.  This file
proves the compact-dual character basis used by the spatial implementation;
the crossed-product generator calculation is kept in the factor layer.
Paper: §3.
-/
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Metrizable.Urysohn
import LeanPool.ConnesRigidity.Paper.Section3.DualHaar

/-!
The fourier component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFourier

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open scoped ENNReal Topology

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
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace

/- The character indexed by a kernel element. Paper: §3.
-/
/--
The `complexCharacter` construction used in the Connes rigidity formalization.
-/
def complexCharacter (d : D) : C(CharacterSpace, ℂ) where
  toFun χ := (Additive.toMul χ (Multiplicative.ofAdd d) : ℂ)
  continuous_toFun := by
    let _ : ContinuousEvalConst
        (PontryaginDual (Multiplicative D)) (Multiplicative D) Circle :=
      ContinuousEvalConst.of_continuous_forget
        (ContinuousMonoidHom.isInducing_toContinuousMap
          (Multiplicative D) Circle).continuous
    have hto : Continuous (Additive.toMul : CharacterSpace →
        PontryaginDual (Multiplicative D)) := by
      change Continuous (id : CharacterSpace → CharacterSpace)
      exact continuous_id
    exact continuous_subtype_val.comp
      ((continuous_eval_const (Multiplicative.ofAdd d)).comp hto)

@[simp] theorem complexCharacter_apply (d : D) (χ : CharacterSpace) :
    complexCharacter d χ =
      (Additive.toMul χ (Multiplicative.ofAdd d) : ℂ) := rfl

/-- Characters separate points of the compact dual. Paper: §3. -/
theorem complexCharacter_separates
    {χ ψ : CharacterSpace} (hχψ : χ ≠ ψ) :
    ∃ d : D, complexCharacter d χ ≠ complexCharacter d ψ := by
  by_contra h
  push Not at h
  apply hχψ
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro d
  apply Circle.coe_injective
  exact h d

/- A nonzero kernel element has a nontrivial evaluation character. Paper: §3.
-/
/--
The `evaluationCharacter` construction used in the Connes rigidity formalization.
-/
def evaluationCharacter (d : D) :
    PontryaginDual (Multiplicative CharacterSpace) where
  toMonoidHom :=
    { toFun := fun χ =>
        Additive.toMul (Multiplicative.toAdd χ) (Multiplicative.ofAdd d)
      map_one' := by simp
      map_mul' := by intro χ ψ; rfl }
  continuous_toFun := by
    let _ : ContinuousEvalConst
        (PontryaginDual (Multiplicative D)) (Multiplicative D) Circle :=
      ContinuousEvalConst.of_continuous_forget
        (ContinuousMonoidHom.isInducing_toContinuousMap
          (Multiplicative D) Circle).continuous
    change Continuous (fun χ : CharacterSpace =>
      Additive.toMul χ (Multiplicative.ofAdd d))
    have hto : Continuous (Additive.toMul : CharacterSpace →
        PontryaginDual (Multiplicative D)) := by
      change Continuous (id : CharacterSpace → CharacterSpace)
      exact continuous_id
    exact (continuous_eval_const (Multiplicative.ofAdd d)).comp hto

@[simp] theorem evaluationCharacter_apply (d : D) (χ : CharacterSpace) :
    evaluationCharacter d (Multiplicative.ofAdd χ) =
      Additive.toMul χ (Multiplicative.ofAdd d) := by rfl

theorem evaluationCharacter_ne_one {d : D} (hd : d ≠ 0) :
    evaluationCharacter d ≠ 1 := by
  intro h
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k hd
  have hvalue := congrArg
    (fun φ : PontryaginDual (Multiplicative CharacterSpace) =>
      φ (Multiplicative.ofAdd (linearCharacter ℓ))) h
  have hzero : ℓ d = 0 := by
    apply ZMod.injective_toCircle
    change ZMod.toCircle (ℓ d) = 1 at hvalue
    simpa using hvalue
  exact hℓ hzero

/-- A nontrivial continuous character integrates to zero against Haar. Paper: §3. -/
theorem integral_character_eq_zero
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsAddLeftInvariant μ]
    (χ : PontryaginDual (Multiplicative G)) (hχ : χ ≠ 1) :
    (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : G,
      χ (Multiplicative.ofAdd g) ≠ 1 := by
    by_contra h
    push Not at h
    apply hχ
    apply PontryaginDual.ext
    intro g
    simpa only [PontryaginDual.one_apply, ofAdd_toAdd] using
      h (Multiplicative.toAdd g)
  have htrans :
      (χ (Multiplicative.ofAdd g) : ℂ) *
        (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) =
        ∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ := by
    calc
      (χ (Multiplicative.ofAdd g) : ℂ) *
          (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) =
          ∫ x : G,
            (χ (Multiplicative.ofAdd g) : ℂ) *
              (χ (Multiplicative.ofAdd x) : ℂ) ∂μ :=
        (integral_const_mul (χ (Multiplicative.ofAdd g) : ℂ)
          (fun x : G => (χ (Multiplicative.ofAdd x) : ℂ))).symm
      _ = ∫ x : G, (χ (Multiplicative.ofAdd (g + x)) : ℂ) ∂μ := by
        congr 1
        funext x
        simp only [ofAdd_add, map_mul, Circle.coe_mul]
      _ = ∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ :=
        integral_add_left_eq_self
          (fun x : G => (χ (Multiplicative.ofAdd x) : ℂ)) g
  have hzero :
      ((χ (Multiplicative.ofAdd g) : ℂ) - 1) *
        (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) = 0 := by
    linear_combination htrans
  rcases mul_eq_zero.mp hzero with h | h
  · exfalso
    apply hg
    exact Circle.coe_eq_one.mp (sub_eq_zero.mp h)
  · exact h

/- Fourier expansion of the actual kernel into compact-dual L². Paper: §3.
-/
/--
The `characterL2` construction used in the Connes rigidity formalization.
-/
def characterL2 (d : D) : Lp ℂ 2 paperCharacterHaar :=
  ContinuousMap.toLp 2 paperCharacterHaar ℂ (complexCharacter d)

/- The compact-dual characters form an orthonormal family. Paper: §3. -/
theorem characterL2_orthonormal :
    Orthonormal ℂ (characterL2 : D → Lp ℂ 2 paperCharacterHaar) := by
  classical
  rw [orthonormal_iff_ite]
  intro d e
  change inner ℂ
      (ContinuousMap.toLp 2 paperCharacterHaar ℂ (complexCharacter d))
      (ContinuousMap.toLp 2 paperCharacterHaar ℂ (complexCharacter e)) =
    if d = e then 1 else 0
  rw [ContinuousMap.inner_toLp]
  split_ifs with h
  · subst e
    have hpoint : ∀ χ : CharacterSpace,
        complexCharacter d χ * starRingEnd ℂ (complexCharacter d χ) = 1 := by
      intro χ
      change
        ((Additive.toMul χ (Multiplicative.ofAdd d) : Circle) : ℂ) *
            starRingEnd ℂ
              ((Additive.toMul χ (Multiplicative.ofAdd d) : Circle) : ℂ) = 1
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel]
      rfl
    change (∫ χ : CharacterSpace,
        complexCharacter d χ * starRingEnd ℂ (complexCharacter d χ)
          ∂paperCharacterHaar) = 1
    simp_rw [hpoint]
    simp only [integral_const, probReal_univ, one_smul]
  · have hne : evaluationCharacter (e - d) ≠ 1 := by
      apply evaluationCharacter_ne_one
      intro hzero
      apply h
      exact (sub_eq_zero.mp hzero).symm
    have hz := integral_character_eq_zero paperCharacterHaar
      (evaluationCharacter (e - d)) hne
    convert hz using 1
    congr 1
    funext χ
    change
      ((Additive.toMul χ (Multiplicative.ofAdd e) : Circle) : ℂ) *
          starRingEnd ℂ
            ((Additive.toMul χ (Multiplicative.ofAdd d) : Circle) : ℂ) =
        ((Additive.toMul χ (Multiplicative.ofAdd (e - d)) : Circle) : ℂ)
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
    rw [ofAdd_sub, map_div (Additive.toMul χ)]
    simp only [div_eq_mul_inv]

/- The character functions form a star subalgebra. Paper: §3. -/
theorem complexCharacter_star (d : D) :
    star (complexCharacter d) = complexCharacter (-d) := by
  ext χ
  change starRingEnd ℂ
      ((Additive.toMul χ (Multiplicative.ofAdd d) : Circle) : ℂ) =
    ((Additive.toMul χ (Multiplicative.ofAdd (-d)) : Circle) : ℂ)
  rw [← Circle.coe_inv_eq_conj, ofAdd_neg, map_inv (Additive.toMul χ)]

/--
The `characterSubalgebra` construction used in the Connes rigidity formalization.
-/
def characterSubalgebra : StarSubalgebra ℂ C(CharacterSpace, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (complexCharacter : D →
    C(CharacterSpace, ℂ)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (complexCharacter : D →
      C(CharacterSpace, ℂ))) ≤
      star (Algebra.adjoin ℂ (Set.range (complexCharacter : D →
        C(CharacterSpace, ℂ))))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨d, rfl⟩
    exact Algebra.subset_adjoin ⟨-d, (complexCharacter_star d).symm⟩

theorem characterSubalgebra_toSubmodule :
    characterSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (complexCharacter : D →
        C(CharacterSpace, ℂ))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro z hz
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hz
  · ext1 χ
    simp [complexCharacter]
  · rintro - - - - ⟨d, rfl⟩ ⟨e, rfl⟩
    refine ⟨d + e, ?_⟩
    ext1 χ
    simp [complexCharacter]

/- The character span is dense in L² of the compact dual. Paper: §3. -/
theorem complexCharacter_span_closure_eq_top :
    (Submodule.span ℂ (Set.range (complexCharacter : D →
      C(CharacterSpace, ℂ)))).topologicalClosure = ⊤ := by
  have hsep : characterSubalgebra.SeparatesPoints := by
    intro χ ψ hχψ
    obtain ⟨d, hd⟩ := complexCharacter_separates hχψ
    refine ⟨_, ⟨complexCharacter d,
      Algebra.subset_adjoin ⟨d, rfl⟩, rfl⟩, ?_⟩
    exact hd
  rw [← characterSubalgebra_toSubmodule]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      characterSubalgebra hsep)

theorem characterL2_span_closure_eq_top :
    (Submodule.span ℂ (Set.range (characterL2 : D →
      Lp ℂ 2 paperCharacterHaar))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange (p := (2 : ℝ≥0∞)) ℂ
      paperCharacterHaar ℂ
        (by simp only [ne_eq, ENNReal.ofNat_ne_top,
          not_false_eq_true])).topologicalClosure_map_submodule
      complexCharacter_span_closure_eq_top
  rw [Submodule.map_span]
  unfold characterL2
  rw [Set.range_comp']
  simp only [ContinuousLinearMap.coe_coe]

/--
The `FourierBasis` construction used in the Connes rigidity formalization.
-/
def FourierBasis : HilbertBasis D ℂ (Lp ℂ 2 paperCharacterHaar) :=
  HilbertBasis.mk characterL2_orthonormal
    characterL2_span_closure_eq_top.ge

@[simp] theorem FourierBasis_coe :
    ⇑FourierBasis = characterL2 :=
  HilbertBasis.coe_mk _ _

/--
The `FourierTransform` construction used in the Connes rigidity formalization.
-/
def FourierTransform :
    lp (fun _ : D => ℂ) 2 ≃ₗᵢ[ℂ] Lp ℂ 2 paperCharacterHaar :=
  FourierBasis.repr.symm

end
end PaperFourier
end Connes
