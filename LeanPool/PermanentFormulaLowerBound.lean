/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Quartic-over-logarithmic lower bound for rational permanent formulas

Source: url:https://github.com/openai/ten-proofs
Authors: OpenAI, Dean Cureton
Status: verified
Main declarations: `PermanentFormulaLowerBound.permanent_rational_formula_logarithmic_lower_bound`
Tags: algebraic-complexity, arithmetic-formulas, permanent, lower-bounds, transcendence-degree
MSC: 68Q17, 68Q25, 15A15
-/

@[expose] public section

namespace PermanentFormulaLowerBound

universe u v w

open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

namespace TranscendenceBounds

private theorem trdeg_intermediateField_adjoin_le_card
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (s : Finset E) :
    Algebra.trdeg F (IntermediateField.adjoin F (s : Set E)) ≤
      (s.card : Cardinal) := by
  classical
  let K : IntermediateField F E := IntermediateField.adjoin F (s : Set E)
  let x : s → K := fun a =>
    ⟨a, IntermediateField.subset_adjoin F (s : Set E) a.property⟩
  have himage : Subtype.val '' Set.range x = (s : Set E) := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact b.property
    · intro ha
      exact ⟨x ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have htop :
      IntermediateField.adjoin F (Set.range x) =
        (⊤ : IntermediateField F K) := by
    apply IntermediateField.lift_injective K
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, himage]
  have halgebraic :
      Algebra.IsAlgebraic (Algebra.adjoin F (Set.range x)) K := by
    apply IntermediateField.isAlgebraic_adjoin_iff_top.mp
    rw [htop]
    refine ⟨fun a => ?_⟩
    simpa only [IntermediateField.algebraMap_apply] using
      (isAlgebraic_algebraMap (R := (⊤ : IntermediateField F K)) (A := K) (⟨a,
        by simp⟩ : (⊤ : IntermediateField F K)))
  let : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range x)) K :=
    halgebraic
  change Algebra.trdeg F K ≤ (s.card : Cardinal)
  calc
    Algebra.trdeg F K ≤ Cardinal.mk (Set.range x) :=
      Algebra.IsAlgebraic.trdeg_le_cardinalMk F (Set.range x)
    _ ≤ Cardinal.mk s := Cardinal.mk_range_le
    _ = (s.card : Cardinal) := Cardinal.mk_coe_finset

private theorem trdeg_intermediateField_le_adjoin_card
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (s : Finset E)
    (hK : K ≤ IntermediateField.adjoin F (s : Set E)) :
    Algebra.trdeg F K ≤ (s.card : Cardinal) := by
  calc
    Algebra.trdeg F K ≤
        Algebra.trdeg F (IntermediateField.adjoin F (s : Set E)) :=
      trdeg_le_of_injective (IntermediateField.inclusion hK)
        (IntermediateField.inclusion_injective hK)
    _ ≤ (s.card : Cardinal) :=
      trdeg_intermediateField_adjoin_le_card s

private theorem trdeg_intermediateField_le_of_adjoin_card_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (s : Finset E) {budget : ℕ}
    (hK : K ≤ IntermediateField.adjoin F (s : Set E))
    (hbudget : s.card ≤ budget) :
    Algebra.trdeg F K ≤ (budget : Cardinal) :=
  (trdeg_intermediateField_le_adjoin_card K s hK).trans
    (Nat.cast_le.mpr hbudget)

end TranscendenceBounds

/-- A rational arithmetic formula with variables indexed by `ι` and constants in `R`. -/
inductive RationalFormula (ι : Type u) (R : Type v) where
  | var : ι → RationalFormula ι R
  | const : R → RationalFormula ι R
  | add : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | sub : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | mul : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | div : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R

namespace RationalFormula

variable {ι : Type u} {R : Type v}

/-- Evaluates a rational formula in the fraction field of multivariate polynomials. -/
noncomputable def eval [Field R] :
    RationalFormula ι R → FractionRing (MvPolynomial ι R)
  | .var i =>
      algebraMap (MvPolynomial ι R) (FractionRing (MvPolynomial ι R))
        (MvPolynomial.X i)
  | .const c =>
      algebraMap (MvPolynomial ι R) (FractionRing (MvPolynomial ι R))
        (MvPolynomial.C c)
  | .add f g => eval f + eval g
  | .sub f g => eval f - eval g
  | .mul f g => eval f * eval g
  | .div f g => eval f / eval g

/-- A rational formula is valid when every divisor occurring in it evaluates to a nonzero value. -/
inductive Valid [Field R] : RationalFormula ι R → Prop where
  | var (i : ι) : Valid (.var i)
  | const (c : R) : Valid (.const c)
  | add {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.add f g)
  | sub {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.sub f g)
  | mul {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.mul f g)
  | div {f g : RationalFormula ι R} :
      Valid f → Valid g → eval g ≠ 0 → Valid (.div f g)

/-- The total number of variable and constant leaves in a rational formula. -/
def leafCount : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => leafCount f + leafCount g
  | .sub f g => leafCount f + leafCount g
  | .mul f g => leafCount f + leafCount g
  | .div f g => leafCount f + leafCount g

/-- The number of variable leaves in a rational formula. -/
def variableLeaves : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add f g => variableLeaves f + variableLeaves g
  | .sub f g => variableLeaves f + variableLeaves g
  | .mul f g => variableLeaves f + variableLeaves g
  | .div f g => variableLeaves f + variableLeaves g

private def blockLeaves [DecidableEq ι] (s : Finset ι) : RationalFormula ι R → ℕ
  | .var i => if i ∈ s then 1 else 0
  | .const _ => 0
  | .add f g => blockLeaves s f + blockLeaves s g
  | .sub f g => blockLeaves s f + blockLeaves s g
  | .mul f g => blockLeaves s f + blockLeaves s g
  | .div f g => blockLeaves s f + blockLeaves s g

/-- The number of arithmetic-operation gates in a rational formula. -/
def internalGateCount : RationalFormula ι R → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add f g => internalGateCount f + internalGateCount g + 1
  | .sub f g => internalGateCount f + internalGateCount g + 1
  | .mul f g => internalGateCount f + internalGateCount g + 1
  | .div f g => internalGateCount f + internalGateCount g + 1

/-- The total number of vertices in the syntax tree of a rational formula. -/
def vertexCount : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => vertexCount f + vertexCount g + 1
  | .sub f g => vertexCount f + vertexCount g + 1
  | .mul f g => vertexCount f + vertexCount g + 1
  | .div f g => vertexCount f + vertexCount g + 1

private theorem leafCount_eq_internalGateCount_add_one (f : RationalFormula ι R) :
    leafCount f = internalGateCount f + 1 := by
  induction f <;>
    simp_all [leafCount, internalGateCount, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm]

private theorem vertexCount_eq_leafCount_add_internalGateCount
    (f : RationalFormula ι R) :
    vertexCount f = leafCount f + internalGateCount f := by
  induction f <;>
    simp_all [vertexCount, leafCount, internalGateCount, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]

private theorem variableLeaves_le_leafCount (f : RationalFormula ι R) :
    variableLeaves f ≤ leafCount f := by
  induction f with
  | var i => simp only [variableLeaves, leafCount, Std.le_refl]
  | const c => simp only [variableLeaves, leafCount, zero_le]
  | add f g hf hg =>
      simpa only [variableLeaves, leafCount] using Nat.add_le_add hf hg
  | sub f g hf hg =>
      simpa only [variableLeaves, leafCount] using Nat.add_le_add hf hg
  | mul f g hf hg =>
      simpa only [variableLeaves, leafCount] using Nat.add_le_add hf hg
  | div f g hf hg =>
      simpa only [variableLeaves, leafCount] using Nat.add_le_add hf hg

private theorem leafCount_le_vertexCount (f : RationalFormula ι R) :
    leafCount f ≤ vertexCount f := by
  rw [vertexCount_eq_leafCount_add_internalGateCount]
  exact Nat.le_add_right _ _

end RationalFormula

namespace RationalFormula

noncomputable section RationalSkeletonInduction

variable {Y Z F : Type*}

private def yLeafCount : RationalFormula (Y ⊕ Z) F → ℕ
  | .var (.inl _) => 1
  | .var (.inr _) => 0
  | .const _ => 0
  | .add f g => yLeafCount f + yLeafCount g
  | .sub f g => yLeafCount f + yLeafCount g
  | .mul f g => yLeafCount f + yLeafCount g
  | .div f g => yLeafCount f + yLeafCount g

private abbrev rationalCoefficientField (Z F : Type*) [Field F] :=
  FractionRing (MvPolynomial Z F)

private abbrev rationalSplitField (Y Z F : Type*) [Field F] :=
  FractionRing (MvPolynomial Y (rationalCoefficientField Z F))

private def splitPolynomialHom [Field F] :
    MvPolynomial (Y ⊕ Z) F →+* rationalSplitField Y Z F :=
  (algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F)).comp
      ((MvPolynomial.map (σ := Y)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F))).comp
          (MvPolynomial.sumAlgEquiv F Y Z).toRingEquiv.toRingHom)

private theorem splitPolynomialHom_injective [Field F] :
    Function.Injective (splitPolynomialHom (Y := Y) (Z := Z) (F := F)) := by
  unfold splitPolynomialHom
  exact
    (IsFractionRing.injective
      (MvPolynomial Y (rationalCoefficientField Z F))
      (rationalSplitField Y Z F)).comp
      ((MvPolynomial.map_injective
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F))
        (IsFractionRing.injective
          (MvPolynomial Z F) (rationalCoefficientField Z F))).comp
            (MvPolynomial.sumAlgEquiv F Y Z).injective)

private def splitFractionHom [Field F] :
    FractionRing (MvPolynomial (Y ⊕ Z) F) →+* rationalSplitField Y Z F :=
  IsFractionRing.lift
    (splitPolynomialHom_injective (Y := Y) (Z := Z) (F := F))

private def splitEval [Field F] (f : RationalFormula (Y ⊕ Z) F) :
    rationalSplitField Y Z F :=
  splitFractionHom (Y := Y) (Z := Z) (F := F) (eval f)

private theorem splitFractionHom_injective [Field F] :
    Function.Injective (splitFractionHom (Y := Y) (Z := Z) (F := F)) :=
  RingHom.injective (splitFractionHom (Y := Y) (Z := Z) (F := F))

private def splitCoefficientHom [Field F] :
    rationalCoefficientField Z F →+* rationalSplitField Y Z F :=
  (algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F)).comp MvPolynomial.C

private theorem splitCoefficientHom_eq_algebraMap [Field F] :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) =
      algebraMap (rationalCoefficientField Z F)
        (rationalSplitField Y Z F) := by
  ext c
  exact (IsScalarTower.algebraMap_apply
    (rationalCoefficientField Z F)
    (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F) c).symm

@[simp] private theorem splitFractionHom_algebraMap [Field F]
    (p : MvPolynomial (Y ⊕ Z) F) :
    splitFractionHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial (Y ⊕ Z) F)
          (FractionRing (MvPolynomial (Y ⊕ Z) F)) p) =
      splitPolynomialHom (Y := Y) (Z := Z) (F := F) p := by
  exact IsFractionRing.lift_algebraMap
    (splitPolynomialHom_injective (Y := Y) (Z := Z) (F := F)) p

@[simp] private theorem splitEval_var_inl [Field F] (i : Y) :
    splitEval (Z := Z) (F := F) (.var (.inl i)) =
      algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i) := by
  simp only [splitEval, eval, splitFractionHom_algebraMap, splitPolynomialHom,
    RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X]

@[simp] private theorem splitEval_var_inr [Field F] (j : Z) :
    splitEval (Y := Y) (F := F) (.var (.inr j)) =
      splitCoefficientHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F)
          (MvPolynomial.X j)) := by
  simp only [splitEval, eval, splitFractionHom_algebraMap, splitPolynomialHom,
    RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C, splitCoefficientHom]

@[simp] private theorem splitEval_const [Field F] (c : F) :
    splitEval (Y := Y) (Z := Z) (.const c) =
      splitCoefficientHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F)
          (MvPolynomial.C c)) := by
  simp only [splitEval, eval, splitFractionHom_algebraMap, splitPolynomialHom,
    RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    MvPolynomial.sumAlgEquiv_C_inl, MvPolynomial.map_C, splitCoefficientHom]

@[simp] private theorem splitEval_add [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.add f g) = splitEval f + splitEval g := by
  exact (splitFractionHom (Y := Y) (Z := Z) (F := F)).map_add _ _

@[simp] private theorem splitEval_sub [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.sub f g) = splitEval f - splitEval g := by
  exact (splitFractionHom (Y := Y) (Z := Z) (F := F)).map_sub _ _

@[simp] private theorem splitEval_mul [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.mul f g) = splitEval f * splitEval g := by
  exact (splitFractionHom (Y := Y) (Z := Z) (F := F)).map_mul _ _

@[simp] private theorem splitEval_div [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.div f g) = splitEval f / splitEval g := by
  exact map_div₀ (splitFractionHom (Y := Y) (Z := Z) (F := F)) _ _

private theorem exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (h : yLeafCount f = 0) :
    ∃ c : rationalCoefficientField Z F,
      splitEval f = splitCoefficientHom (Y := Y) (Z := Z) (F := F) c := by
  induction f with
  | var i =>
      cases i with
      | inl i => simp only [yLeafCount, one_ne_zero] at h
      | inr j =>
          exact ⟨algebraMap (MvPolynomial Z F)
            (rationalCoefficientField Z F) (MvPolynomial.X j),
              splitEval_var_inr j⟩
  | const c =>
      exact ⟨algebraMap (MvPolynomial Z F)
        (rationalCoefficientField Z F) (MvPolynomial.C c),
          splitEval_const c⟩
  | add f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a + b, ?_⟩
      rw [splitEval_add, ha, hb]
      exact (splitCoefficientHom (Y := Y) (Z := Z) (F := F)).map_add _ _ |>.symm
  | sub f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a - b, ?_⟩
      rw [splitEval_sub, ha, hb]
      exact (splitCoefficientHom (Y := Y) (Z := Z) (F := F)).map_sub _ _ |>.symm
  | mul f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a * b, ?_⟩
      rw [splitEval_mul, ha, hb]
      exact (splitCoefficientHom (Y := Y) (Z := Z) (F := F)).map_mul _ _ |>.symm
  | div f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a / b, ?_⟩
      rw [splitEval_div, ha, hb]
      exact (map_div₀ (splitCoefficientHom (Y := Y) (Z := Z) (F := F)) _ _).symm

private def rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F)) :
    IntermediateField F (rationalSplitField Y Z F) :=
  IntermediateField.adjoin F
    (Set.range (fun i : Y =>
      algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i)) ∪
      (splitCoefficientHom (Y := Y) (Z := Z) (F := F)) ''
        (s : Set (rationalCoefficientField Z F)))

private theorem marked_variable_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F)) (i : Y) :
    algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i) ∈
      rationalSkeletonField (Y := Y) s := by
  apply IntermediateField.subset_adjoin F _
  exact Or.inl ⟨i, rfl⟩

private theorem coefficient_parameter_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F))
    (c : rationalCoefficientField Z F) (hc : c ∈ s) :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) c ∈
      rationalSkeletonField (Y := Y) s := by
  apply IntermediateField.subset_adjoin F _
  exact Or.inr ⟨c, hc, rfl⟩

private theorem coefficient_adjoin_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F))
    (c : rationalCoefficientField Z F)
    (hc : c ∈ IntermediateField.adjoin F
      (s : Set (rationalCoefficientField Z F))) :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) c ∈
      rationalSkeletonField (Y := Y) s := by
  refine IntermediateField.adjoin_induction F
    (p := fun x _ =>
      splitCoefficientHom (Y := Y) (Z := Z) (F := F) x ∈
        rationalSkeletonField (Y := Y) s)
    ?_ ?_ ?_ ?_ ?_ hc
  · intro x hx
    exact coefficient_parameter_mem_rationalSkeletonField s x hx
  · intro x
    rw [splitCoefficientHom_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply F
        (rationalCoefficientField Z F) (rationalSplitField Y Z F)]
    exact (rationalSkeletonField (Y := Y) s).algebraMap_mem x
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]
    exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy

private theorem rationalSkeletonField_mono [Field F]
    {s t : Finset (rationalCoefficientField Z F)} (h : s ⊆ t) :
    rationalSkeletonField (Y := Y) s ≤ rationalSkeletonField (Y := Y) t := by
  apply IntermediateField.adjoin.mono
  intro x hx
  rcases hx with hx | ⟨c, hc, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨c, h hc, rfl⟩

end RationalSkeletonInduction

end RationalFormula

/-- The generic `n`-by-`n` permanent polynomial over the complex numbers. -/
noncomputable def permanentPolynomial (n : ℕ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).permanent

private theorem permanentPolynomial_eq_sum (n : ℕ) :
    permanentPolynomial n =
      ∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin n, MvPolynomial.X (i, σ i) := by
  classical
  unfold permanentPolynomial
  rw [← Matrix.permanent_transpose]
  rfl

private theorem permanentPermutationMonomial_pderiv
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    MvPolynomial.pderiv (a, b)
        (∏ i : Fin n, (MvPolynomial.X (i, σ i) :
          MvPolynomial (Fin n × Fin n) ℂ)) =
      if σ a = b then
        ∏ i : {i : Fin n // i ≠ a},
          (MvPolynomial.X (i.1, σ i.1) :
            MvPolynomial (Fin n × Fin n) ℂ)
      else 0 := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun i : Fin n =>
      (MvPolynomial.X (i, σ i) : MvPolynomial (Fin n × Fin n) ℂ)) a,
    MvPolynomial.pderiv_mul]
  have hrest :
      MvPolynomial.pderiv (a, b)
        (∏ i : {i : Fin n // i ≠ a},
          (MvPolynomial.X (i.1, σ i.1) :
            MvPolynomial (Fin n × Fin n) ℂ)) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hsubset := MvPolynomial.vars_prod (s := Finset.univ)
      (fun i : {i : Fin n // i ≠ a} =>
        (MvPolynomial.X (i.1, σ i.1) :
          MvPolynomial (Fin n × Fin n) ℂ))
    have hbi := hsubset hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hbi
    have hpair : (a, b) = (i.1, σ i.1) := by
      simpa only [ne_eq, Prod.mk.injEq, MvPolynomial.vars_X, Finset.mem_singleton] using hi
    exact i.property (congrArg Prod.fst hpair).symm
  by_cases hab : σ a = b
  · subst b
    simp only [MvPolynomial.pderiv_X, Pi.single_eq_same, ne_eq, one_mul, hrest, mul_zero,
      add_zero, ↓reduceIte]
  · have hpair : (a, σ a) ≠ (a, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    simp only [MvPolynomial.pderiv_X_of_ne hpair, ne_eq, zero_mul, hrest, mul_zero, add_zero,
      hab, ↓reduceIte]

private theorem permanentPolynomial_pderiv_eq_sum
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) =
      ∑ σ : Equiv.Perm (Fin n),
        if σ a = b then
          ∏ i : {i : Fin n // i ≠ a},
            (MvPolynomial.X (i.1, σ i.1) :
              MvPolynomial (Fin n × Fin n) ℂ)
        else 0 := by
  classical
  rw [permanentPolynomial_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact permanentPermutationMonomial_pderiv σ a b

private theorem eval_one_permanentPolynomial_pderiv
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.eval
        (fun _ : Fin n × Fin n => (1 : ℂ))
        (MvPolynomial.pderiv (a, b) (permanentPolynomial n)) =
      (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) := by
  classical
  calc
    MvPolynomial.eval
        (fun _ : Fin n × Fin n => (1 : ℂ))
        (MvPolynomial.pderiv (a, b) (permanentPolynomial n)) =
      ∑ σ : Equiv.Perm (Fin n),
        if σ a = b then (1 : ℂ) else 0 := by
          rw [permanentPolynomial_pderiv_eq_sum, map_sum]
          apply Finset.sum_congr rfl
          intro σ _
          split_ifs <;> simp
    _ = ((Finset.univ.filter
          (fun σ : Equiv.Perm (Fin n) => σ a = b)).card : ℂ) :=
      Finset.sum_boole (fun σ : Equiv.Perm (Fin n) => σ a = b)
        Finset.univ
    _ = (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) := by
      rw [Fintype.card_subtype]

private theorem permanentPolynomial_pderiv_ne_zero
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) ≠ 0 := by
  classical
  have hnonempty :
      Nonempty {σ : Equiv.Perm (Fin n) // σ a = b} :=
    ⟨⟨Equiv.swap a b, by simp only [Equiv.swap_apply_left]⟩⟩
  let : Nonempty {σ : Equiv.Perm (Fin n) // σ a = b} := hnonempty
  intro hzero
  have hcardzero :
      (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) = 0 := by
    rw [← eval_one_permanentPolynomial_pderiv a b, hzero]
    simp only [map_zero]
  exact (Nat.cast_ne_zero.mpr
    (Fintype.card_ne_zero :
      Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} ≠ 0)) hcardzero


private def matchingBlockRow {n k : ℕ} (hk : 0 < k)
    (j : Fin (n / k)) (r : Fin k) : Fin n :=
  ⟨(j : ℕ) * k + (r : ℕ), by
    have hupper : ((j : ℕ) + 1) * k ≤ n :=
      (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt j.isLt)
    have hupper' : (j : ℕ) * k + k ≤ n := by
      simpa only [Nat.add_mul, one_mul] using hupper
    exact (Nat.add_lt_add_left r.isLt ((j : ℕ) * k)).trans_le hupper'⟩

private theorem matchingBlockRow_injective {n k : ℕ} (hk : 0 < k) :
    Function.Injective
      (fun jr : Fin (n / k) × Fin k =>
        matchingBlockRow hk jr.1 jr.2) := by
  intro x y h
  rcases x with ⟨j, r⟩
  rcases y with ⟨j', r'⟩
  have hval :
      (j : ℕ) * k + (r : ℕ) =
        (j' : ℕ) * k + (r' : ℕ) :=
    congrArg Fin.val h
  have hr : (r : ℕ) = (r' : ℕ) := by
    have hmod := congrArg (fun z : ℕ => z % k) hval
    simpa only [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt r.isLt, zero_add,
      Nat.mod_eq_of_lt r'.isLt] using
      hmod
  have hmul : (j : ℕ) * k = (j' : ℕ) * k := by
    omega
  have hj : (j : ℕ) = (j' : ℕ) :=
    Nat.eq_of_mul_eq_mul_right hk hmul
  apply Prod.ext
  · exact Fin.ext hj
  · exact Fin.ext hr

private def cyclicMatchingBlock {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Finset (Fin n × Fin n) := by
  classical
  letI : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  exact Finset.univ.image fun r : Fin k =>
    let i := matchingBlockRow hk j r
    (i, i + t)

private theorem card_cyclicMatchingBlock {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    (cyclicMatchingBlock hk t j).card = k := by
  classical
  unfold cyclicMatchingBlock
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro r r' heq
    have hrows : matchingBlockRow hk j r = matchingBlockRow hk j r' :=
      congrArg Prod.fst heq
    exact congrArg Prod.snd
      (matchingBlockRow_injective hk
        (a₁ := (j, r)) (a₂ := (j, r')) hrows)

private theorem cyclicMatchingBlock_disjoint {n k : ℕ}
    (hk : 0 < k) (x y : Fin n × Fin (n / k)) (hxy : x ≠ y) :
    Disjoint (cyclicMatchingBlock hk x.1 x.2)
      (cyclicMatchingBlock hk y.1 y.2) := by
  classical
  let : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (x.1 : ℕ)).trans_lt x.1.isLt)⟩
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp hy
  have hpair :
      (matchingBlockRow hk x.2 r,
        matchingBlockRow hk x.2 r + x.1) =
        (matchingBlockRow hk y.2 r',
          matchingBlockRow hk y.2 r' + y.1) :=
    hr.trans hr'.symm
  have hrow : matchingBlockRow hk x.2 r =
      matchingBlockRow hk y.2 r' := congrArg Prod.fst hpair
  have hcol :
      matchingBlockRow hk x.2 r + x.1 =
        matchingBlockRow hk y.2 r' + y.1 :=
    congrArg Prod.snd hpair
  have hoffset : x.1 = y.1 := by
    apply add_left_cancel (a := matchingBlockRow hk x.2 r)
    simpa only [hrow, add_right_inj] using hcol
  have hblock : x.2 = y.2 :=
    congrArg Prod.fst
      (matchingBlockRow_injective hk
        (a₁ := (x.2, r)) (a₂ := (y.2, r')) hrow)
  exact hxy (Prod.ext hoffset hblock)

private theorem cyclicMatchingBlock_fst_injective {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Function.Injective
      (fun x : ↥(cyclicMatchingBlock hk t j) => x.1.1) := by
  classical
  let : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  intro x y hrow
  change x.1.1 = y.1.1 at hrow
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp x.property
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp y.property
  have hxgraph : x.1.2 = x.1.1 + t := by
    rw [← hr]
  have hygraph : y.1.2 = y.1.1 + t := by
    rw [← hr']
  apply Subtype.ext
  apply Prod.ext
  · exact hrow
  · rw [hxgraph, hygraph, hrow]

private theorem cyclicMatchingBlock_snd_injective {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Function.Injective
      (fun x : ↥(cyclicMatchingBlock hk t j) => x.1.2) := by
  classical
  let : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  intro x y hcol
  change x.1.2 = y.1.2 at hcol
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp x.property
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp y.property
  have hxgraph : x.1.2 = x.1.1 + t := by
    rw [← hr]
  have hygraph : y.1.2 = y.1.1 + t := by
    rw [← hr']
  have hrow : x.1.1 = y.1.1 := by
    apply add_right_cancel (b := t)
    rw [← hxgraph, ← hygraph]
    exact hcol
  apply Subtype.ext
  exact Prod.ext hrow hcol

private theorem matchingBlock_floor_bound (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    n ≤ 2 * (k * (n / k)) := by
  have hq : 0 < n / k := Nat.div_pos hkn hk
  have hkq : k ≤ k * (n / k) := by
    simpa only [Nat.succ_eq_add_one, zero_add,
      mul_one] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt hq)
  have hrem : n % k < k := Nat.mod_lt n hk
  have hdecomp : n % k + k * (n / k) = n := Nat.mod_add_div n k
  omega

private theorem cyclicMatchingBlock_count_bound (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    n * n ≤ 2 * k * (n * (n / k)) := by
  calc
    n * n ≤ n * (2 * (k * (n / k))) :=
      Nat.mul_le_mul_left n (matchingBlock_floor_bound n k hk hkn)
    _ = 2 * k * (n * (n / k)) := by ring


namespace RationalFormula

private theorem sum_blockLeaves_le_variableLeaves_of_disjoint
    {ι κ R : Type*} [DecidableEq ι] [Fintype κ]
    (blocks : κ → Finset ι)
    (hdisjoint : ∀ a b : κ, a ≠ b → Disjoint (blocks a) (blocks b))
    (f : RationalFormula ι R) :
    (∑ a : κ, blockLeaves (blocks a) f) ≤ variableLeaves f := by
  classical
  induction f with
  | var i =>
      change (∑ a : κ, if i ∈ blocks a then 1 else 0) ≤ 1
      rw [Finset.sum_boole]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hne
      have hia : i ∈ blocks a := (Finset.mem_filter.mp ha).2
      have hib : i ∈ blocks b := (Finset.mem_filter.mp hb).2
      exact Finset.disjoint_left.mp (hdisjoint a b hne) hia hib
  | const _ =>
      simp only [blockLeaves, Finset.sum_const_zero, variableLeaves, Std.le_refl]
  | add f g hf hg =>
      simpa only [blockLeaves, Finset.sum_add_distrib, variableLeaves] using Nat.add_le_add hf hg
  | sub f g hf hg =>
      simpa only [blockLeaves, Finset.sum_add_distrib, variableLeaves] using Nat.add_le_add hf hg
  | mul f g hf hg =>
      simpa only [blockLeaves, Finset.sum_add_distrib, variableLeaves] using Nat.add_le_add hf hg
  | div f g hf hg =>
      simpa only [blockLeaves, Finset.sum_add_distrib, variableLeaves] using Nat.add_le_add hf hg

end RationalFormula


namespace RationalFormula

private theorem cyclicMatchingBlock_square_sum_le_variableLeaves
    {n k : ℕ} (hk : 0 < k) (m : ℕ)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    (n * (n / k)) * (m * m) ≤ 6 * variableLeaves f := by
  classical
  have hpack := sum_blockLeaves_le_variableLeaves_of_disjoint
    (fun x : Fin n × Fin (n / k) => cyclicMatchingBlock hk x.1 x.2)
    (fun a b hab => cyclicMatchingBlock_disjoint hk a b hab) f
  calc
    (n * (n / k)) * (m * m) =
        ∑ _x : Fin n × Fin (n / k), m * m := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul]
    _ ≤ ∑ x : Fin n × Fin (n / k),
          6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f := by
            exact Finset.sum_le_sum fun x _ => hblock x
    _ = 6 * ∑ x : Fin n × Fin (n / k),
          blockLeaves (cyclicMatchingBlock hk x.1 x.2) f := by
            rw [Finset.mul_sum]
    _ ≤ 6 * variableLeaves f := Nat.mul_le_mul_left 6 hpack

private theorem cyclicMatchingBlock_intermediate_bound
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : ℕ) (f : RationalFormula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n * n * (m * m) ≤ 12 * k * variableLeaves f := by
  have hcount := cyclicMatchingBlock_count_bound n k hk hkn
  have hsum := cyclicMatchingBlock_square_sum_le_variableLeaves
    hk m f hblock
  calc
    n * n * (m * m) ≤
        (2 * k * (n * (n / k))) * (m * m) :=
          Nat.mul_le_mul_right (m * m) hcount
    _ = 2 * k * ((n * (n / k)) * (m * m)) := by ring
    _ ≤ 2 * k * (6 * variableLeaves f) :=
      Nat.mul_le_mul_left (2 * k) hsum
    _ = 12 * k * variableLeaves f := by ring

private theorem cyclicMatchingBlock_fourth_power_bound
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : ℕ) (hhalf : n ≤ 2 * m)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n ^ 4 ≤ 48 * k * variableLeaves f := by
  have hsquare : n * n ≤ 4 * (m * m) := by
    calc
      n * n ≤ (2 * m) * (2 * m) := Nat.mul_self_le_mul_self hhalf
      _ = 4 * (m * m) := by ring
  have hintermediate := cyclicMatchingBlock_intermediate_bound
    hk hkn m f hblock
  calc
    n ^ 4 = (n * n) * (n * n) := by ring
    _ ≤ (n * n) * (4 * (m * m)) :=
      Nat.mul_le_mul_left (n * n) hsquare
    _ = 4 * (n * n * (m * m)) := by ring
    _ ≤ 4 * (12 * k * variableLeaves f) :=
      Nat.mul_le_mul_left 4 hintermediate
    _ = 48 * k * variableLeaves f := by ring

end RationalFormula

section Coefficients

variable {Y : Type u} {Z : Type v} {F : Type w} [Field F]

private noncomputable def coefficientPolynomial
    (f : MvPolynomial (Y ⊕ Z) F) (α : Y →₀ ℕ) : MvPolynomial Z F :=
  MvPolynomial.coeff α (MvPolynomial.sumAlgEquiv F Y Z f)

private noncomputable def coefficientField (f : MvPolynomial (Y ⊕ Z) F) :
    IntermediateField F (FractionRing (MvPolynomial Z F)) :=
  IntermediateField.adjoin F
    (Set.range fun α : Y →₀ ℕ =>
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (coefficientPolynomial f α))

private noncomputable def coefficientTranscendenceDegree
    (f : MvPolynomial (Y ⊕ Z) F) : Cardinal :=
  Algebra.trdeg F ↥(coefficientField f)

private theorem coefficient_mem_coefficientField
    (f : MvPolynomial (Y ⊕ Z) F) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (coefficientPolynomial f α) ∈ coefficientField f := by
  unfold coefficientField
  exact IntermediateField.subset_adjoin F _ ⟨α, rfl⟩

end Coefficients

private theorem coefficientTranscendenceDegree_ge_of_algebraicIndependent
    {Y Z F ι : Type*} [Field F] [Fintype ι]
    (p : MvPolynomial (Y ⊕ Z) F) (α : ι → Y →₀ ℕ)
    (hind : AlgebraicIndependent F
      (fun i => coefficientPolynomial p (α i))) :
    (Fintype.card ι : Cardinal) ≤ coefficientTranscendenceDegree p := by
  let φ : MvPolynomial Z F →ₐ[F] FractionRing (MvPolynomial Z F) :=
    IsScalarTower.toAlgHom F (MvPolynomial Z F)
      (FractionRing (MvPolynomial Z F))
  have hφ : Function.Injective φ :=
    IsFractionRing.injective (MvPolynomial Z F)
      (FractionRing (MvPolynomial Z F))
  have hfrac : AlgebraicIndependent F
      (fun i =>
        algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
          (coefficientPolynomial p (α i))) := by
    simpa [φ, Function.comp_def] using hind.map' hφ
  let g : ι → coefficientField p := fun i =>
    ⟨algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
      (coefficientPolynomial p (α i)),
      coefficient_mem_coefficientField p (α i)⟩
  have hg : AlgebraicIndependent F g := by
    apply
      (AlgHom.algebraicIndependent_iff
        (coefficientField p).val Subtype.val_injective).mp
    simpa only [IntermediateField.coe_val, Function.comp_def] using hfrac
  change (Fintype.card ι : Cardinal) ≤
    Algebra.trdeg F (coefficientField p)
  simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast, ge_iff_le, Cardinal.nat_le_lift_iff] using
    hg.lift_cardinalMk_le_trdeg

private theorem coefficientTranscendenceDegree_ge_square_of_algebraicIndependent
    {Y Z F : Type*} [Field F] {m : ℕ}
    (p : MvPolynomial (Y ⊕ Z) F)
    (α : Fin m × Fin m → Y →₀ ℕ)
    (hind : AlgebraicIndependent F
      (fun de => coefficientPolynomial p (α de))) :
    ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree p := by
  simpa only [Nat.cast_mul, Fintype.card_prod, Fintype.card_fin] using
    coefficientTranscendenceDegree_ge_of_algebraicIndependent p α hind

section Jacobian

variable {ι : Type u} {κ : Type v} {F : Type w}

private noncomputable def jacobianMinor [CommSemiring F]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) :
    Matrix ι ι (MvPolynomial κ F) :=
  fun i j => MvPolynomial.pderiv (cols j) (g i)

private noncomputable def evaluatedJacobianMinor [CommSemiring F]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F) :
    Matrix ι ι F :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (cols j) (g i))

private theorem pderiv_bind₁_chain_rule [CommSemiring F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (H : MvPolynomial ι F) (j : κ) :
    MvPolynomial.pderiv j (MvPolynomial.bind₁ g H) =
      ∑ i : ι,
        MvPolynomial.bind₁ g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.derivation_C, map_zero, zero_mul,
             Finset.sum_const_zero]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right,
        MvPolynomial.pderiv_mul, hp]
      simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul,
        MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_X,
        Pi.single_apply, add_mul]
      rw [Finset.sum_add_distrib]
      simp only [mul_comm, Finset.mul_sum, mul_assoc, MonoidWithZeroHom.map_ite_one_zero,
        ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem pderiv_aeval_chain_rule [CommSemiring F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (H : MvPolynomial ι F) (j : κ) :
    MvPolynomial.pderiv j (MvPolynomial.aeval g H) =
      ∑ i : ι,
        MvPolynomial.aeval g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by
  simpa only [MvPolynomial.aeval_eq_bind₁] using
    pderiv_bind₁_chain_rule g H j

private theorem relation_vecMul_jacobianMinor [CommRing F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (H : MvPolynomial ι F) (hH : MvPolynomial.aeval g H = 0) :
    (fun i : ι => MvPolynomial.aeval g (MvPolynomial.pderiv i H)) ᵥ*
        jacobianMinor g cols = 0 := by
  classical
  funext j
  have hj := congrArg (MvPolynomial.pderiv (cols j)) hH
  rw [pderiv_aeval_chain_rule] at hj
  simpa only [Matrix.vecMul, dotProduct, MvPolynomial.aeval_eq_bind₁, jacobianMinor, Pi.zero_apply,
    map_zero] using hj

private theorem jacobianMinor_det_ne_zero_of_evaluated [CommRing F]
    [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F)
    (h : (evaluatedJacobianMinor g cols x).det ≠ 0) :
    (jacobianMinor g cols).det ≠ 0 := by
  intro hzero
  apply h
  change Matrix.det ((MvPolynomial.eval x).mapMatrix (jacobianMinor g cols)) = 0
  rw [← RingHom.map_det, hzero, map_zero]

private theorem aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero [Field F]
    [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (H : MvPolynomial ι F)
    (hdet : (jacobianMinor g cols).det ≠ 0)
    (hH : MvPolynomial.aeval g H = 0) (i : ι) :
    MvPolynomial.aeval g (MvPolynomial.pderiv i H) = 0 := by
  have hzero := Matrix.eq_zero_of_vecMul_eq_zero hdet
    (relation_vecMul_jacobianMinor g cols H hH)
  exact congrFun hzero i

private theorem totalDegree_succ_le_of_mem_pderiv_support [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι) {m : ι →₀ ℕ}
    (hm : m ∈ (MvPolynomial.pderiv i p).support) :
    Multiset.card (Finsupp.toMultiset m) + 1 ≤ p.totalDegree := by
  classical
  have hmcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv i p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hparent : m + Finsupp.single i 1 ∈ p.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    apply hmcoeff
    rw [MvPolynomial.coeff_pderiv, hzero, zero_mul]
  have hdegree := MvPolynomial.le_totalDegree hparent
  rw [Finsupp.card_toMultiset]
  change m.sum (fun _ e => e) + 1 ≤ p.totalDegree
  simpa only [Order.add_one_le_iff, implies_true, Nat.add_left_cancel_iff, Finsupp.sum_add_index',
    Finsupp.sum_single_index] using hdegree

private theorem totalDegree_pderiv_lt_of_ne_zero [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι)
    (hp : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp
  have hpositive : 0 < p.totalDegree :=
    lt_of_lt_of_le (Nat.zero_lt_succ _)
      (totalDegree_succ_le_of_mem_pderiv_support p i hm)
  rw [MvPolynomial.totalDegree_eq]
  apply (Finset.sup_lt_iff hpositive).mpr
  intro m hm
  exact Nat.lt_of_succ_le (totalDegree_succ_le_of_mem_pderiv_support p i hm)

private theorem eq_C_of_forall_pderiv_eq_zero [Field F] [CharZero F]
    (p : MvPolynomial ι F)
    (hp : ∀ i : ι, MvPolynomial.pderiv i p = 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  classical
  apply MvPolynomial.ext _ _
  intro m
  by_cases hm : m = 0
  · subst m
    simp only [MvPolynomial.coeff_C, ↓reduceIte]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hnone
      apply hm
      ext i
      simp only [Finsupp.zero_apply]
      exact Classical.byContradiction (fun hi => hnone ⟨i, hi⟩)
    let m' : ι →₀ ℕ := m - Finsupp.single i 1
    have hcancel : m' + Finsupp.single i 1 = m := by
      exact Finsupp.sub_add_single_one_cancel hi
    have hder := congrArg (MvPolynomial.coeff m') (hp i)
    rw [MvPolynomial.coeff_pderiv, hcancel, MvPolynomial.coeff_zero] at hder
    have hcast : (↑(m' i) + 1 : F) ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    have hcoeff : MvPolynomial.coeff m p = 0 :=
      (mul_eq_zero.mp hder).resolve_right hcast
    simpa only [MvPolynomial.coeff_C, Ne.symm hm, ↓reduceIte] using hcoeff

private theorem algebraicIndependent_of_jacobianMinor_det_ne_zero
    [Field F] [CharZero F] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (hdet : (jacobianMinor g cols).det ≠ 0) :
    AlgebraicIndependent F g := by
  rw [algebraicIndependent_iff]
  intro H hH
  have hmain : ∀ n : ℕ, ∀ p : MvPolynomial ι F,
      p.totalDegree = n → MvPolynomial.aeval g p = 0 → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hrelation
      have hpartials : ∀ i : ι, MvPolynomial.pderiv i p = 0 := by
        intro i
        by_cases hi : MvPolynomial.pderiv i p = 0
        · exact hi
        · have hlt : (MvPolynomial.pderiv i p).totalDegree < n := by
            rw [← hdegree]
            exact totalDegree_pderiv_lt_of_ne_zero p i hi
          exact ih _ hlt (MvPolynomial.pderiv i p) rfl
            (aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
              g cols p hdet hrelation i)
      have hconstant := eq_C_of_forall_pderiv_eq_zero p hpartials
      rw [hconstant] at hrelation ⊢
      simpa only [map_eq_zero, MvPolynomial.aeval_eq_bind₁, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq] using
        hrelation
  exact hmain H.totalDegree H rfl hH

private theorem algebraicIndependent_of_evaluatedJacobianMinor_det_ne_zero
    [Field F] [CharZero F] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F)
    (hdet : (evaluatedJacobianMinor g cols x).det ≠ 0) :
    AlgebraicIndependent F g :=
  algebraicIndependent_of_jacobianMinor_det_ne_zero g cols
    (jacobianMinor_det_ne_zero_of_evaluated g cols x hdet)

end Jacobian

noncomputable section PolynomialIntersection

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

private def polynomialCoefficientProjection (φ : E →ₗ[K] K) :
    MvPolynomial ι E →ₗ[K] MvPolynomial ι K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap φ).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

private theorem polynomialCoefficientProjection_map_mul
    (φ : E →ₗ[K] K) (q : MvPolynomial ι K) (f : MvPolynomial ι E) :
    polynomialCoefficientProjection φ
        (MvPolynomial.map (algebraMap K E) q * f) =
      q * polynomialCoefficientProjection φ f := by
  classical
  apply MvPolynomial.ext
  intro s
  have hcoeff (g : MvPolynomial ι E) (index : ι →₀ ℕ) :
      MvPolynomial.coeff index (polynomialCoefficientProjection φ g) =
        φ (MvPolynomial.coeff index g) := rfl
  simp only [hcoeff, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simpa [Algebra.smul_def] using
    φ.map_smul (MvPolynomial.coeff a.1 q) (MvPolynomial.coeff a.2 f)

private theorem polynomialCoefficientProjection_map
    (φ : E →ₗ[K] K)
    (hφ : ∀ a : K, φ (algebraMap K E a) = a)
    (p : MvPolynomial ι K) :
    polynomialCoefficientProjection φ
        (MvPolynomial.map (algebraMap K E) p) = p := by
  apply MvPolynomial.ext
  intro s
  change
    φ (MvPolynomial.coeff s (MvPolynomial.map (algebraMap K E) p)) =
      MvPolynomial.coeff s p
  simpa only [MvPolynomial.coeff_map] using hφ (MvPolynomial.coeff s p)

private theorem polynomial_intersection_of_mul
    (f : MvPolynomial ι E) (p q : MvPolynomial ι K)
    (hq : q ≠ 0)
    (h : MvPolynomial.map (algebraMap K E) q * f =
      MvPolynomial.map (algebraMap K E) p) :
    ∃ g : MvPolynomial ι K,
      MvPolynomial.map (algebraMap K E) g = f := by
  classical
  let j : K →ₗ[K] E := Algebra.linearMap K E
  have hj : LinearMap.ker j = ⊥ :=
    LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap K E))
  let φ : E →ₗ[K] K := j.leftInverse
  have hφ (a : K) : φ (algebraMap K E a) = a :=
    LinearMap.leftInverse_apply_of_inj hj a
  let g : MvPolynomial ι K := polynomialCoefficientProjection φ f
  have hg : q * g = p := by
    have he := congrArg (polynomialCoefficientProjection φ) h
    simpa only [polynomialCoefficientProjection_map_mul,
      polynomialCoefficientProjection_map φ hφ] using he
  refine ⟨g, ?_⟩
  have hq' : MvPolynomial.map (algebraMap K E) q ≠ 0 := by
    intro hzero
    apply hq
    apply MvPolynomial.map_injective (algebraMap K E)
      (RingHom.injective (algebraMap K E))
    simpa only [map_zero] using hzero
  apply mul_left_cancel₀ hq'
  calc
    MvPolynomial.map (algebraMap K E) q *
        MvPolynomial.map (algebraMap K E) g =
      MvPolynomial.map (algebraMap K E) (q * g) := by rw [map_mul]
    _ = MvPolynomial.map (algebraMap K E) p := congrArg _ hg
    _ = MvPolynomial.map (algebraMap K E) q * f := h.symm

end PolynomialIntersection

noncomputable section RationalCoefficientExtraction

variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]

private def coefficientPolynomialEmbedding (K : IntermediateField F E) :
    MvPolynomial Y K →ₐ[F] FractionRing (MvPolynomial Y E) :=
  (IsScalarTower.toAlgHom F (MvPolynomial Y E)
    (FractionRing (MvPolynomial Y E))).comp
      (MvPolynomial.mapAlgHom K.val)

private theorem coefficientPolynomialEmbedding_injective
    (K : IntermediateField F E) :
    Function.Injective (coefficientPolynomialEmbedding (Y := Y) K) := by
  unfold coefficientPolynomialEmbedding
  exact
    (IsFractionRing.injective (MvPolynomial Y E)
      (FractionRing (MvPolynomial Y E))).comp
      (MvPolynomial.map_injective (algebraMap K E)
        (RingHom.injective (algebraMap K E)))

private def coefficientFractionEmbedding (K : IntermediateField F E) :
    FractionRing (MvPolynomial Y K) →ₐ[F]
      FractionRing (MvPolynomial Y E) :=
  IsFractionRing.liftAlgHom (coefficientPolynomialEmbedding_injective
    (Y := Y) K)

@[simp] private theorem coefficientFractionEmbedding_algebraMap
    (K : IntermediateField F E) (p : MvPolynomial Y K) :
    coefficientFractionEmbedding (Y := Y) K
      (algebraMap (MvPolynomial Y K)
        (FractionRing (MvPolynomial Y K)) p) =
      coefficientPolynomialEmbedding (Y := Y) K p := by
  exact IsFractionRing.lift_algebraMap
    (coefficientPolynomialEmbedding_injective (Y := Y) K) p

private def coefficientRationalField (s : Finset E) :
    IntermediateField F (FractionRing (MvPolynomial Y E)) :=
  IntermediateField.adjoin F
    (Set.range (fun i : Y =>
      algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E))
        (MvPolynomial.X i)) ∪
      (algebraMap E (FractionRing (MvPolynomial Y E))) '' (s : Set E))

private theorem coefficientRationalField_le_fractionRange (s : Finset E) :
    coefficientRationalField (F := F) (Y := Y) s ≤
      (coefficientFractionEmbedding (Y := Y)
        (IntermediateField.adjoin F (s : Set E))).fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with ⟨i, rfl⟩ | ⟨c, hc, rfl⟩
  · apply AlgHom.mem_fieldRange.mpr
    refine ⟨algebraMap
      (MvPolynomial Y (IntermediateField.adjoin F (s : Set E)))
      (FractionRing (MvPolynomial Y
        (IntermediateField.adjoin F (s : Set E))))
      (MvPolynomial.X i), ?_⟩
    rw [coefficientFractionEmbedding_algebraMap]
    simp only [coefficientPolynomialEmbedding, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom',
      Function.comp_apply,
      MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X]
  · let ck : IntermediateField.adjoin F (s : Set E) :=
      ⟨c, IntermediateField.subset_adjoin F (s : Set E) hc⟩
    apply AlgHom.mem_fieldRange.mpr
    refine ⟨algebraMap
      (MvPolynomial Y (IntermediateField.adjoin F (s : Set E)))
      (FractionRing (MvPolynomial Y
        (IntermediateField.adjoin F (s : Set E))))
      (MvPolynomial.C ck), ?_⟩
    rw [coefficientFractionEmbedding_algebraMap]
    simpa [coefficientPolynomialEmbedding, ck] using
      (IsScalarTower.algebraMap_apply E (MvPolynomial Y E)
        (FractionRing (MvPolynomial Y E)) c).symm

private theorem exists_polynomial_of_mem_coefficientRationalField
    (s : Finset E) (p : MvPolynomial Y E)
    (hp : algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p ∈
      coefficientRationalField (F := F) (Y := Y) s) :
    ∃ g : MvPolynomial Y (IntermediateField.adjoin F (s : Set E)),
      MvPolynomial.map
        (algebraMap (IntermediateField.adjoin F (s : Set E)) E) g = p := by
  let K : IntermediateField F E := IntermediateField.adjoin F (s : Set E)
  have hfield :
      algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p ∈
        (coefficientFractionEmbedding (Y := Y) K).fieldRange :=
    coefficientRationalField_le_fractionRange s hp
  obtain ⟨r, hr⟩ := AlgHom.mem_fieldRange.mp hfield
  obtain ⟨a, b, hb, hab⟩ :=
    IsFractionRing.div_surjective (MvPolynomial Y K) r
  have hbzero : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbembed : coefficientPolynomialEmbedding (Y := Y) K b ≠ 0 := by
    intro hzero
    apply hbzero
    apply coefficientPolynomialEmbedding_injective (Y := Y) K
    simpa only [map_zero] using hzero
  have hrat :
      coefficientPolynomialEmbedding (Y := Y) K a /
        coefficientPolynomialEmbedding (Y := Y) K b =
          algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p := by
    rw [← hab, map_div₀, coefficientFractionEmbedding_algebraMap,
      coefficientFractionEmbedding_algebraMap] at hr
    exact hr
  have hcrossFraction :
      coefficientPolynomialEmbedding (Y := Y) K b *
        algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p =
          coefficientPolynomialEmbedding (Y := Y) K a := by
    have hcross := (div_eq_iff hbembed).mp hrat
    simpa only [mul_comm] using hcross.symm
  have hcross :
      MvPolynomial.map (algebraMap K E) b * p =
        MvPolynomial.map (algebraMap K E) a := by
    have hval : K.val.toRingHom = algebraMap K E := rfl
    rw [← hval]
    apply IsFractionRing.injective (MvPolynomial Y E)
      (FractionRing (MvPolynomial Y E))
    simpa only [AlgHom.toRingHom_eq_coe, map_mul, coefficientPolynomialEmbedding, AlgHom.coe_comp,
      IsScalarTower.coe_toAlgHom', Function.comp_apply,
        MvPolynomial.mapAlgHom_apply] using hcrossFraction
  exact polynomial_intersection_of_mul p a b hbzero hcross

end RationalCoefficientExtraction

noncomputable section RationalSkeleton

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

private def fractionalNumerator (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  algebraMap E L (M 0 0) * q + algebraMap E L (M 0 1)

private def fractionalDenominator (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  algebraMap E L (M 1 0) * q + algebraMap E L (M 1 1)

private def fractionalApply (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  fractionalNumerator M q / fractionalDenominator M q

private theorem fractionalNumerator_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalNumerator (M * N) q =
      algebraMap E L (M 0 0) * fractionalNumerator N q +
        algebraMap E L (M 0 1) * fractionalDenominator N q := by
  obtain ⟨h₀₀, h₀₁, _, _⟩ := Matrix.two_mul_expl M N
  simp only [fractionalNumerator, fractionalDenominator]
  rw [h₀₀, h₀₁]
  simp only [map_add, map_mul]
  ring

private theorem fractionalDenominator_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalDenominator (M * N) q =
      algebraMap E L (M 1 0) * fractionalNumerator N q +
        algebraMap E L (M 1 1) * fractionalDenominator N q := by
  obtain ⟨_, _, h₁₀, h₁₁⟩ := Matrix.two_mul_expl M N
  simp only [fractionalNumerator, fractionalDenominator]
  rw [h₁₀, h₁₁]
  simp only [map_add, map_mul]
  ring

private theorem fractionalNumerator_mul_factor
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalNumerator (M * N) q =
      fractionalDenominator N q *
        fractionalNumerator M (fractionalApply N q) := by
  rw [fractionalNumerator_mul]
  change
    algebraMap E L (M 0 0) * fractionalNumerator N q +
        algebraMap E L (M 0 1) * fractionalDenominator N q =
      fractionalDenominator N q *
        (algebraMap E L (M 0 0) *
          (fractionalNumerator N q / fractionalDenominator N q) +
            algebraMap E L (M 0 1))
  field_simp [hN]

private theorem fractionalDenominator_mul_factor
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalDenominator (M * N) q =
      fractionalDenominator N q *
        fractionalDenominator M (fractionalApply N q) := by
  rw [fractionalDenominator_mul]
  change
    algebraMap E L (M 1 0) * fractionalNumerator N q +
        algebraMap E L (M 1 1) * fractionalDenominator N q =
      fractionalDenominator N q *
        (algebraMap E L (M 1 0) *
          (fractionalNumerator N q / fractionalDenominator N q) +
            algebraMap E L (M 1 1))
  field_simp [hN]

private theorem fractionalDenominator_mul_ne_zero
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0)
    (hM : fractionalDenominator M (fractionalApply N q) ≠ 0) :
    fractionalDenominator (M * N) q ≠ 0 := by
  rw [fractionalDenominator_mul_factor M N q hN]
  exact mul_ne_zero hN hM

private theorem fractionalApply_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalApply (M * N) q =
      fractionalApply M (fractionalApply N q) := by
  unfold fractionalApply
  rw [fractionalNumerator_mul_factor M N q hN,
    fractionalDenominator_mul_factor M N q hN]
  exact mul_div_mul_left _ _ hN

private theorem matrix_ne_zero_of_fractionalDenominator_ne_zero
    (M : Matrix (Fin 2) (Fin 2) E) (q : L)
    (h : fractionalDenominator M q ≠ 0) : M ≠ 0 := by
  intro hM
  apply h
  simp only [fractionalDenominator, hM, Fin.isValue, Matrix.zero_apply, map_zero, zero_mul,
    add_zero]

private def normalizedFractionalMatrix
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) :
    Matrix (Fin 2) (Fin 2) E :=
  (M ij.1 ij.2)⁻¹ • M

private theorem normalizedFractionalMatrix_pivot
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) :
    normalizedFractionalMatrix M ij ij.1 ij.2 = 1 := by
  simp only [normalizedFractionalMatrix, Matrix.smul_apply, smul_eq_mul, ne_eq, h,
    not_false_eq_true,
    inv_mul_cancel₀]

private theorem fractionalNumerator_smul
    (c : E) (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalNumerator (c • M) q =
      algebraMap E L c * fractionalNumerator M q := by
  simp only [fractionalNumerator, Fin.isValue, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem fractionalDenominator_smul
    (c : E) (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalDenominator (c • M) q =
      algebraMap E L c * fractionalDenominator M q := by
  simp only [fractionalDenominator, Fin.isValue, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem fractionalApply_smul
    (c : E) (hc : c ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalApply (c • M) q = fractionalApply M q := by
  have hc' : algebraMap E L c ≠ 0 :=
    (map_ne_zero_iff (algebraMap E L)
      (RingHom.injective (algebraMap E L))).mpr hc
  simp only [fractionalApply, fractionalNumerator_smul,
    fractionalDenominator_smul]
  exact mul_div_mul_left _ _ hc'

private theorem fractionalApply_normalizedFractionalMatrix
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) (q : L) :
    fractionalApply (normalizedFractionalMatrix M ij) q =
      fractionalApply M q := by
  unfold normalizedFractionalMatrix
  exact fractionalApply_smul _ (inv_ne_zero h) M q

private def projectiveMatrixGenerators
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) : Finset E := by
  classical
  exact (Finset.univ.erase ij).image
    (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)

private theorem card_projectiveMatrixGenerators_le_three
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) :
    (projectiveMatrixGenerators M ij).card ≤ 3 := by
  classical
  unfold projectiveMatrixGenerators
  calc
    ((Finset.univ.erase ij).image
      (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)).card ≤
        (Finset.univ.erase ij).card := Finset.card_image_le
    _ = 3 := by simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin,
                  Nat.reduceMul, Nat.add_one_sub_one]

private theorem normalizedFractionalMatrix_entry_mem_adjoin
    {F : Type*} [Field F] [Algebra F E]
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) (a b : Fin 2) :
    normalizedFractionalMatrix M ij a b ∈
      IntermediateField.adjoin F
        (projectiveMatrixGenerators M ij : Set E) := by
  classical
  by_cases hab : (a, b) = ij
  · have ha : a = ij.1 := congrArg Prod.fst hab
    have hb : b = ij.2 := congrArg Prod.snd hab
    rw [ha, hb, normalizedFractionalMatrix_pivot M ij h]
    exact one_mem _
  · apply IntermediateField.subset_adjoin F
      (projectiveMatrixGenerators M ij : Set E)
    change normalizedFractionalMatrix M ij a b ∈
      projectiveMatrixGenerators M ij
    change normalizedFractionalMatrix M ij a b ∈
      (Finset.univ.erase ij).image
        (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩, rfl⟩

end RationalSkeleton

namespace RationalFormula

noncomputable section RationalSkeletonContraction

variable {Y Z F : Type*}

section MarkedPathGates

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

private def rationalAddPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, c; 0, 1]

private def rationalSubPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, -c; 0, 1]

private def rationalReverseSubPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![-1, c; 0, 1]

private def rationalMulPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![c, 0; 0, 1]

private def rationalDivPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, 0; 0, c]

private def rationalReverseDivPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![0, c; 1, 0]

@[simp] private theorem fractionalDenominator_rationalAddPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalAddPathMatrix c) q = 1 := by
  simp only [fractionalDenominator, rationalAddPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_mul,
      map_one, zero_add]

@[simp] private theorem fractionalApply_rationalAddPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalAddPathMatrix c) q =
      q + algebraMap E L c := by
  simp only [fractionalApply, fractionalNumerator, rationalAddPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_one, one_mul,
      Matrix.cons_val_one,
    fractionalDenominator, map_zero, zero_mul, zero_add, div_one]

@[simp] private theorem fractionalDenominator_rationalSubPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalSubPathMatrix c) q = 1 := by
  simp only [fractionalDenominator, rationalSubPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_mul,
      map_one, zero_add]

@[simp] private theorem fractionalApply_rationalSubPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalSubPathMatrix c) q =
      q - algebraMap E L c := by
  simp only [fractionalApply, fractionalNumerator, rationalSubPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_one, one_mul,
      Matrix.cons_val_one, map_neg,
    fractionalDenominator, map_zero, zero_mul, zero_add, div_one, sub_eq_add_neg]

@[simp] private theorem fractionalDenominator_rationalReverseSubPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalReverseSubPathMatrix c) q = 1 := by
  simp only [fractionalDenominator, rationalReverseSubPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      map_zero, zero_mul, map_one,
    zero_add]

@[simp] private theorem fractionalApply_rationalReverseSubPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalReverseSubPathMatrix c) q =
      algebraMap E L c - q := by
  simp only [fractionalApply, fractionalNumerator, rationalReverseSubPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_neg, map_one, neg_mul,
      one_mul,
    Matrix.cons_val_one, fractionalDenominator, map_zero, zero_mul, zero_add, div_one,
      sub_eq_add_neg, add_comm]

@[simp] private theorem fractionalDenominator_rationalMulPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalMulPathMatrix c) q = 1 := by
  simp only [fractionalDenominator, rationalMulPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_mul,
      map_one, zero_add]

@[simp] private theorem fractionalApply_rationalMulPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalMulPathMatrix c) q =
      algebraMap E L c * q := by
  simp only [fractionalApply, fractionalNumerator, rationalMulPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      map_zero, add_zero,
    fractionalDenominator, zero_mul, map_one, zero_add, div_one]

@[simp] private theorem fractionalDenominator_rationalDivPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalDivPathMatrix c) q =
      algebraMap E L c := by
  simp only [fractionalDenominator, rationalDivPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_mul,
      zero_add]

@[simp] private theorem fractionalApply_rationalDivPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalDivPathMatrix c) q =
      q / algebraMap E L c := by
  simp only [fractionalApply, fractionalNumerator, rationalDivPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_one, one_mul,
      Matrix.cons_val_one, map_zero,
    add_zero, fractionalDenominator, zero_mul, zero_add]

@[simp] private theorem fractionalDenominator_rationalReverseDivPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalReverseDivPathMatrix c) q = q := by
  simp only [fractionalDenominator, rationalReverseDivPathMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      map_one, one_mul, map_zero,
    add_zero]

@[simp] private theorem fractionalApply_rationalReverseDivPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalReverseDivPathMatrix c) q =
      algebraMap E L c / q := by
  simp only [fractionalApply, fractionalNumerator, rationalReverseDivPathMatrix, Fin.isValue,
    Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_zero, zero_mul,
      Matrix.cons_val_one, zero_add,
    fractionalDenominator, map_one, one_mul, add_zero]

end MarkedPathGates

private structure ContractedRationalSkeleton [Field F]
    (f : RationalFormula (Y ⊕ Z) F) where
  generators : Finset (rationalCoefficientField Z F)
  matrix : Matrix (Fin 2) (Fin 2) (rationalCoefficientField Z F)
  core : rationalSplitField Y Z F
  core_mem : core ∈ rationalSkeletonField (Y := Y) generators
  denominator_ne : fractionalDenominator matrix core ≠ 0
  split_eq : splitEval f = fractionalApply matrix core
  generator_card : generators.card ≤ 6 * yLeafCount f - 6

private noncomputable def contractedRationalSkeletonVar [Field F] (i : Y) :
    ContractedRationalSkeleton (Z := Z) (F := F) (.var (.inl i)) where
  generators := ∅
  matrix := 1
  core := algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F) (MvPolynomial.X i)
  core_mem := marked_variable_mem_rationalSkeletonField ∅ i
  denominator_ne := by simp only [fractionalDenominator, Fin.isValue, ne_eq, one_ne_zero,
    not_false_eq_true, Matrix.one_apply_ne,
                         map_zero, zero_mul, Matrix.one_apply_eq, map_one, zero_add]
  split_eq := by
    simp only [splitEval_var_inl, fractionalApply, fractionalNumerator, Matrix.one_apply_eq,
      map_one, one_mul,
      Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, map_zero,
        add_zero, fractionalDenominator,
      one_ne_zero, zero_mul, zero_add, div_one]
  generator_card := by simp only [Finset.card_empty, yLeafCount, mul_one, tsub_self, Std.le_refl]

private noncomputable def contractedRationalSkeletonCompose [Field F]
    {f h : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f)
    (P : Matrix (Fin 2) (Fin 2) (rationalCoefficientField Z F))
    (heval : splitEval h = fractionalApply P (splitEval f))
    (hden : fractionalDenominator P (splitEval f) ≠ 0)
    (hleaves : yLeafCount h = yLeafCount f) :
    ContractedRationalSkeleton h where
  generators := w.generators
  matrix := P * w.matrix
  core := w.core
  core_mem := w.core_mem
  denominator_ne := by
    apply fractionalDenominator_mul_ne_zero P w.matrix w.core w.denominator_ne
    rwa [← w.split_eq]
  split_eq := by
    calc
      splitEval h = fractionalApply P (splitEval f) := heval
      _ = fractionalApply P (fractionalApply w.matrix w.core) :=
        congrArg (fractionalApply P) w.split_eq
      _ = fractionalApply (P * w.matrix) w.core :=
        (fractionalApply_mul P w.matrix w.core w.denominator_ne).symm
  generator_card := by
    simpa only [hleaves] using w.generator_card

namespace ContractedRationalSkeleton

private theorem exists_pivot [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    ∃ ij : Fin 2 × Fin 2, w.matrix ij.1 ij.2 ≠ 0 := by
  classical
  by_contra h
  have hzero : w.matrix = 0 := by
    apply Matrix.ext
    intro i j
    have hij : w.matrix i j = 0 := by
      by_contra hentry
      exact h ⟨(i, j), hentry⟩
    simpa only [Matrix.zero_apply] using hij
  exact (matrix_ne_zero_of_fractionalDenominator_ne_zero
    w.matrix w.core w.denominator_ne) hzero

private noncomputable def pivot [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) : Fin 2 × Fin 2 :=
  (exists_pivot w).choose

private theorem pivot_ne [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    w.matrix (pivot w).1 (pivot w).2 ≠ 0 :=
  (exists_pivot w).choose_spec

private noncomputable def extendedGenerators [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    Finset (rationalCoefficientField Z F) := by
  classical
  exact w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)

private theorem splitEval_mem_extended [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    splitEval f ∈ rationalSkeletonField (Y := Y) (extendedGenerators w) := by
  classical
  let s : Finset (rationalCoefficientField Z F) :=
    extendedGenerators w
  have hgenerators : w.generators ⊆ s := by
    intro c hc
    change c ∈ w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)
    exact Finset.mem_union_left _ hc
  have hcore : w.core ∈ rationalSkeletonField (Y := Y) s :=
    rationalSkeletonField_mono hgenerators w.core_mem
  have hentry (a b : Fin 2) :
      algebraMap (rationalCoefficientField Z F)
        (rationalSplitField Y Z F)
        (normalizedFractionalMatrix w.matrix (pivot w) a b) ∈
          rationalSkeletonField (Y := Y) s := by
    have hsmall := normalizedFractionalMatrix_entry_mem_adjoin
      (F := F) w.matrix (pivot w) (pivot_ne w) a b
    have hlarge :
        normalizedFractionalMatrix w.matrix (pivot w) a b ∈
          IntermediateField.adjoin F
            (s : Set (rationalCoefficientField Z F)) := by
      have hmono :
          IntermediateField.adjoin F
              (projectiveMatrixGenerators w.matrix (pivot w) :
                Set (rationalCoefficientField Z F)) ≤
            IntermediateField.adjoin F
              (s : Set (rationalCoefficientField Z F)) := by
        apply IntermediateField.adjoin.mono
        intro c hc
        change c ∈ projectiveMatrixGenerators w.matrix (pivot w) at hc
        change c ∈ s
        change c ∈
          w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)
        exact Finset.mem_union_right _ hc
      exact hmono hsmall
    rw [← splitCoefficientHom_eq_algebraMap]
    exact coefficient_adjoin_mem_rationalSkeletonField s _ hlarge
  change splitEval f ∈ rationalSkeletonField (Y := Y) s
  rw [w.split_eq, ← fractionalApply_normalizedFractionalMatrix
    w.matrix (pivot w) (pivot_ne w) w.core]
  unfold fractionalApply fractionalNumerator fractionalDenominator
  apply div_mem
  · exact add_mem (mul_mem (hentry 0 0) hcore) (hentry 0 1)
  · exact add_mem (mul_mem (hentry 1 0) hcore) (hentry 1 1)

private theorem extendedGenerators_card_le [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hmarked : 0 < yLeafCount f) :
    (extendedGenerators w).card ≤ 6 * yLeafCount f - 3 := by
  classical
  change
    (w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)).card ≤
      6 * yLeafCount f - 3
  have hunion := Finset.card_union_le w.generators
    (projectiveMatrixGenerators w.matrix (pivot w))
  have hmatrix := card_projectiveMatrixGenerators_le_three
    w.matrix (pivot w)
  have hgenerators := w.generator_card
  omega

end ContractedRationalSkeleton

private noncomputable def contractedRationalSkeletonMerge [Field F]
    {f g h : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g)
    (op : rationalSplitField Y Z F → rationalSplitField Y Z F →
      rationalSplitField Y Z F)
    (hclosed : ∀ (K : IntermediateField F (rationalSplitField Y Z F))
      (x y : rationalSplitField Y Z F),
        x ∈ K → y ∈ K → op x y ∈ K)
    (heval : splitEval h = op (splitEval f) (splitEval g))
    (hleaves : yLeafCount h = yLeafCount f + yLeafCount g) :
    ContractedRationalSkeleton h := by
  classical
  let s : Finset (rationalCoefficientField Z F) :=
    ContractedRationalSkeleton.extendedGenerators wf ∪
      ContractedRationalSkeleton.extendedGenerators wg
  have hleft : ContractedRationalSkeleton.extendedGenerators wf ⊆ s := by
    intro c hc
    exact Finset.mem_union_left _ hc
  have hright : ContractedRationalSkeleton.extendedGenerators wg ⊆ s := by
    intro c hc
    exact Finset.mem_union_right _ hc
  refine
    { generators := s
      matrix := 1
      core := op (splitEval f) (splitEval g)
      core_mem := ?_
      denominator_ne := ?_
      split_eq := ?_
      generator_card := ?_ }
  · apply hclosed (rationalSkeletonField (Y := Y) s)
    · exact rationalSkeletonField_mono hleft
        (ContractedRationalSkeleton.splitEval_mem_extended wf)
    · exact rationalSkeletonField_mono hright
        (ContractedRationalSkeleton.splitEval_mem_extended wg)
  · simp only [fractionalDenominator, Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true,
    Matrix.one_apply_ne,
      map_zero, zero_mul, Matrix.one_apply_eq, map_one, zero_add]
  · simpa only [fractionalApply, fractionalNumerator, Matrix.one_apply_eq, map_one, one_mul,
    Fin.isValue, ne_eq,
      zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, map_zero, add_zero,
        fractionalDenominator, one_ne_zero,
      zero_mul, zero_add, div_one] using heval
  · have hunion := Finset.card_union_le
      (ContractedRationalSkeleton.extendedGenerators wf)
      (ContractedRationalSkeleton.extendedGenerators wg)
    have hcardf := ContractedRationalSkeleton.extendedGenerators_card_le wf hf
    have hcardg := ContractedRationalSkeleton.extendedGenerators_card_le wg hg
    change s.card ≤ 6 * yLeafCount h - 6
    change
      (ContractedRationalSkeleton.extendedGenerators wf ∪
        ContractedRationalSkeleton.extendedGenerators wg).card ≤
        6 * yLeafCount h - 6
    omega

private theorem exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (h : yLeafCount f = 0) :
    ∃ c : rationalCoefficientField Z F,
      splitEval f =
        algebraMap (rationalCoefficientField Z F)
          (rationalSplitField Y Z F) c := by
  obtain ⟨c, hc⟩ :=
    exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero f h
  refine ⟨c, ?_⟩
  rwa [splitCoefficientHom_eq_algebraMap] at hc

private noncomputable def contractedRationalSkeletonAddLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.add f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalAddPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_add, fractionalApply_rationalAddPathMatrix, hc]
  · rw [fractionalDenominator_rationalAddPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]

private noncomputable def contractedRationalSkeletonAddRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.add f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalAddPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_add, fractionalApply_rationalAddPathMatrix, hc, add_comm]
  · rw [fractionalDenominator_rationalAddPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]

private noncomputable def contractedRationalSkeletonSubLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.sub f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalSubPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_sub, fractionalApply_rationalSubPathMatrix, hc]
  · rw [fractionalDenominator_rationalSubPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]

private noncomputable def contractedRationalSkeletonSubRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.sub f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalReverseSubPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_sub, fractionalApply_rationalReverseSubPathMatrix, hc]
  · rw [fractionalDenominator_rationalReverseSubPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]

private noncomputable def contractedRationalSkeletonMulLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.mul f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalMulPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_mul, fractionalApply_rationalMulPathMatrix, hc, mul_comm]
  · rw [fractionalDenominator_rationalMulPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]

private noncomputable def contractedRationalSkeletonMulRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.mul f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalMulPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_mul, fractionalApply_rationalMulPathMatrix, hc]
  · rw [fractionalDenominator_rationalMulPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]

private noncomputable def contractedRationalSkeletonDivLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0)
    (hden : splitEval g ≠ 0) :
    ContractedRationalSkeleton (.div f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalDivPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_div, fractionalApply_rationalDivPathMatrix, hc]
  · rw [fractionalDenominator_rationalDivPathMatrix]
    rw [hc] at hden
    exact hden
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]

private noncomputable def contractedRationalSkeletonDivRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0)
    (hden : splitEval g ≠ 0) :
    ContractedRationalSkeleton (.div f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w
    (rationalReverseDivPathMatrix c) ?_ ?_ ?_
  · rw [splitEval_div, fractionalApply_rationalReverseDivPathMatrix, hc]
  · rwa [fractionalDenominator_rationalReverseDivPathMatrix]
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]

private noncomputable def contractedRationalSkeletonAddBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.add f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· + ·)
    (fun K _ _ hx hy => K.add_mem hx hy)
    (splitEval_add f g) rfl

private noncomputable def contractedRationalSkeletonSubBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.sub f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· - ·)
    (fun K _ _ hx hy => K.sub_mem hx hy)
    (splitEval_sub f g) rfl

private noncomputable def contractedRationalSkeletonMulBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.mul f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· * ·)
    (fun K _ _ hx hy => K.mul_mem hx hy)
    (splitEval_mul f g) rfl

private noncomputable def contractedRationalSkeletonDivBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.div f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· / ·)
    (fun K _ _ hx hy => K.div_mem hx hy)
    (splitEval_div f g) rfl

private theorem splitEval_ne_zero_of_eval_ne_zero [Field F]
    {f : RationalFormula (Y ⊕ Z) F} (h : eval f ≠ 0) :
    splitEval f ≠ 0 := by
  intro hzero
  apply h
  apply splitFractionHom_injective (Y := Y) (Z := Z) (F := F)
  simpa only [map_zero, map_eq_zero, splitEval] using hzero

private theorem exists_contractedRationalSkeleton [Field F]
    (f : RationalFormula (Y ⊕ Z) F) :
    Valid f → 0 < yLeafCount f → Nonempty (ContractedRationalSkeleton f) := by
  induction f with
  | var i =>
      intro _ hmarked
      cases i with
      | inl i => exact ⟨contractedRationalSkeletonVar i⟩
      | inr i => simp only [yLeafCount, lt_self_iff_false] at hmarked
  | const c =>
      intro _ hmarked
      simp only [yLeafCount, lt_self_iff_false] at hmarked
  | add f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | add hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonAddRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonAddLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonAddBinary wf wg hfpos hgpos⟩
  | sub f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | sub hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonSubRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonSubLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonSubBinary wf wg hfpos hgpos⟩
  | mul f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | mul hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonMulRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonMulLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonMulBinary wf wg hfpos hgpos⟩
  | div f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | div hfvalid hgvalid hgden =>
          have hsplitden : splitEval g ≠ 0 :=
            splitEval_ne_zero_of_eval_ne_zero hgden
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonDivRight wg hfzero hsplitden⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonDivLeft wf hgzero hsplitden⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonDivBinary wf wg hfpos hgpos⟩

private theorem rational_skeleton [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (hvalid : Valid f)
    (hmarked : 0 < yLeafCount f) :
    ∃ s : Finset (rationalCoefficientField Z F),
      s.card ≤ 6 * yLeafCount f - 3 ∧
        splitEval f ∈ rationalSkeletonField (Y := Y) s := by
  obtain ⟨w⟩ := exists_contractedRationalSkeleton f hvalid hmarked
  exact ⟨ContractedRationalSkeleton.extendedGenerators w,
    ContractedRationalSkeleton.extendedGenerators_card_le w hmarked,
    ContractedRationalSkeleton.splitEval_mem_extended w⟩

private theorem rational_skeleton_trdeg [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (hvalid : Valid f)
    (hmarked : 0 < yLeafCount f) (p : MvPolynomial (Y ⊕ Z) F)
    (houtput : eval f =
      algebraMap (MvPolynomial (Y ⊕ Z) F)
        (FractionRing (MvPolynomial (Y ⊕ Z) F)) p) :
    coefficientTranscendenceDegree p ≤
      ((6 * yLeafCount f - 3 : ℕ) : Cardinal) := by
  obtain ⟨s, hcard, hmem⟩ := rational_skeleton f hvalid hmarked
  let E : Type _ := rationalCoefficientField Z F
  let pY : MvPolynomial Y E :=
    MvPolynomial.map (algebraMap (MvPolynomial Z F) E)
      (MvPolynomial.sumAlgEquiv F Y Z p)
  have hsplit :
      splitEval f =
        algebraMap (MvPolynomial Y E)
          (FractionRing (MvPolynomial Y E)) pY := by
    rw [splitEval, houtput, splitFractionHom_algebraMap]
    rfl
  have hfields :
      rationalSkeletonField (Y := Y) s =
        coefficientRationalField (F := F) (Y := Y) s := by
    simp only [rationalSkeletonField, splitCoefficientHom_eq_algebraMap, coefficientRationalField]
  have hpY :
      algebraMap (MvPolynomial Y E)
        (FractionRing (MvPolynomial Y E)) pY ∈
          coefficientRationalField (F := F) (Y := Y) s := by
    rw [← hsplit, ← hfields]
    exact hmem
  obtain ⟨g, hg⟩ :=
    exists_polynomial_of_mem_coefficientRationalField
      (F := F) (Y := Y) s pY hpY
  have hfield :
      coefficientField p ≤ IntermediateField.adjoin F (s : Set E) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨α, rfl⟩
    change
      algebraMap (MvPolynomial Z F) E (coefficientPolynomial p α) ∈
        IntermediateField.adjoin F (s : Set E)
    have hcoeff :
        algebraMap (IntermediateField.adjoin F (s : Set E)) E
            (MvPolynomial.coeff α g) =
          algebraMap (MvPolynomial Z F) E
            (coefficientPolynomial p α) := by
      simpa [pY, MvPolynomial.coeff_map, coefficientPolynomial]
        using congrArg (MvPolynomial.coeff α) hg
    rw [← hcoeff]
    exact (MvPolynomial.coeff α g).property
  exact
    TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
      (coefficientField p) s hfield hcard

end RationalSkeletonContraction

end RationalFormula

private abbrev matchingOutside {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :=
  {z : Fin n × Fin n // z ∉ Set.range d}

private noncomputable def matchingVariableEquiv {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :
    Y ⊕ matchingOutside d ≃ Fin n × Fin n := by
  classical
  exact
    (Equiv.sumCongr (Equiv.ofInjective d d.injective)
      (Equiv.refl (matchingOutside d))).trans
        (Equiv.Set.sumCompl (Set.range d))

@[simp] private theorem matchingVariableEquiv_inl {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (y : Y) :
    matchingVariableEquiv d (.inl y) = d y := by
  classical
  change
    (Equiv.Set.sumCompl (Set.range d))
      (.inl ((Equiv.ofInjective d d.injective) y)) = d y
  exact Equiv.Set.sumCompl_apply_inl (Set.range d)
    ((Equiv.ofInjective d d.injective) y)

@[simp] private theorem matchingVariableEquiv_inr {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (z : matchingOutside d) :
    matchingVariableEquiv d (.inr z) = z.1 := by
  classical
  change (Equiv.Set.sumCompl (Set.range d)) (.inr z) = z.1
  exact Equiv.Set.sumCompl_apply_inr (Set.range d) z

private noncomputable def matchingMarkedPermanent {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :
    MvPolynomial (Y ⊕ matchingOutside d) ℂ :=
  MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
    (permanentPolynomial n)

private noncomputable def matchingSquarefreeMonomial {Y : Type u}
    (S : Finset Y) : Y →₀ ℕ :=
  ∑ y ∈ S, Finsupp.single y 1

@[simp] private theorem matchingSquarefreeMonomial_apply {Y : Type u}
    [DecidableEq Y]
    (S : Finset Y) (y : Y) :
    matchingSquarefreeMonomial S y = if y ∈ S then 1 else 0 := by
  classical
  simp only [matchingSquarefreeMonomial, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq']

private noncomputable def matchingPermutationExponent {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (σ : Equiv.Perm (Fin n)) : Y →₀ ℕ :=
  ∑ i : Fin n,
    match (matchingVariableEquiv d).symm (i, σ i) with
    | .inl y => Finsupp.single y 1
    | .inr _ => 0

private noncomputable def matchingPermutationOutsideProduct
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) : MvPolynomial (matchingOutside d) ℂ :=
  ∏ i : Fin n,
    match (matchingVariableEquiv d).symm (i, σ i) with
    | .inl _ => 1
    | .inr z => MvPolynomial.X z

private theorem matchingPermutation_split_monomial
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
          (∏ i : Fin n,
            (MvPolynomial.X (i, σ i) :
              MvPolynomial (Fin n × Fin n) ℂ))) =
      MvPolynomial.monomial (matchingPermutationExponent d σ)
        (matchingPermutationOutsideProduct d σ) := by
  classical
  unfold matchingPermutationExponent matchingPermutationOutsideProduct
  rw [map_prod, map_prod]
  rw [MvPolynomial.monomial_sum_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  cases h : (matchingVariableEquiv d).symm (i, σ i) with
  | inl y =>
      simp only [MvPolynomial.sumAlgEquiv_X_inl, ← MvPolynomial.C_mul_X_eq_monomial,
        MvPolynomial.C_1, one_mul]
  | inr z =>
      simp only [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.monomial_zero']

private theorem matchingMarkedPermanent_split_eq_sum
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (matchingMarkedPermanent d) =
      ∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.monomial (matchingPermutationExponent d σ)
          (matchingPermutationOutsideProduct d σ) := by
  classical
  unfold matchingMarkedPermanent
  rw [permanentPolynomial_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact matchingPermutation_split_monomial d σ

private theorem matchingMarkedPermanent_coefficient_eq_sum
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n)
    (α : Y →₀ ℕ) :
    coefficientPolynomial (matchingMarkedPermanent d) α =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α then
          matchingPermutationOutsideProduct d σ
        else 0 := by
  classical
  unfold coefficientPolynomial
  rw [matchingMarkedPermanent_split_eq_sum,
    MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [MvPolynomial.coeff_monomial]

private theorem matchingMarkedPermanent_coefficient_pderiv_eq_sum
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n)
    (α : Y →₀ ℕ) (z : matchingOutside d) :
    MvPolynomial.pderiv z
        (coefficientPolynomial (matchingMarkedPermanent d) α) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α then
          MvPolynomial.pderiv z
            (matchingPermutationOutsideProduct d σ)
        else 0 := by
  classical
  rw [matchingMarkedPermanent_coefficient_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

private theorem matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_sum
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n)
    (α : Y →₀ ℕ) (z : matchingOutside d)
    (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ
        (MvPolynomial.pderiv z
          (coefficientPolynomial (matchingMarkedPermanent d) α)) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α then
          MvPolynomial.eval ξ
            (MvPolynomial.pderiv z
              (matchingPermutationOutsideProduct d σ))
        else 0 := by
  classical
  rw [matchingMarkedPermanent_coefficient_pderiv_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

private noncomputable def matchingPermutationOutsideFactor
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    MvPolynomial (matchingOutside d) ℂ :=
  match (matchingVariableEquiv d).symm (i, σ i) with
  | .inl _ => 1
  | .inr z => MvPolynomial.X z

private theorem matchingPermutationOutsideProduct_pderiv
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (z : matchingOutside d) :
    MvPolynomial.pderiv z (matchingPermutationOutsideProduct d σ) =
      if σ z.1.1 = z.1.2 then
        ∏ i : {i : Fin n // i ≠ z.1.1},
          matchingPermutationOutsideFactor d σ i.1
      else 0 := by
  classical
  change MvPolynomial.pderiv z
    (∏ i : Fin n, matchingPermutationOutsideFactor d σ i) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (matchingPermutationOutsideFactor d σ) z.1.1,
    MvPolynomial.pderiv_mul]
  have hrest :
      MvPolynomial.pderiv z
        (∏ i : {i : Fin n // i ≠ z.1.1},
          matchingPermutationOutsideFactor d σ i.1) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hsubset := MvPolynomial.vars_prod (s := Finset.univ)
      (fun i : {i : Fin n // i ≠ z.1.1} =>
        matchingPermutationOutsideFactor d σ i.1)
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hsubset hmem)
    unfold matchingPermutationOutsideFactor at hi
    split at hi
    · simp only [MvPolynomial.vars_one, Finset.notMem_empty] at hi
    · rename_i w hw
      have hzw : z = w := by
        simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hi
      have hpair : (i.1, σ i.1) = z.1 := by
        have heq := congrArg (matchingVariableEquiv d) hw
        simpa only [ne_eq, hzw, Equiv.apply_symm_apply, matchingVariableEquiv_inr] using heq
      exact i.property (congrArg Prod.fst hpair)
  by_cases hz : σ z.1.1 = z.1.2
  · have hmarked :
        (matchingVariableEquiv d).symm (z.1.1, σ z.1.1) =
          .inr z := by
        apply (matchingVariableEquiv d).injective
        simp only [hz, Prod.mk.eta, Equiv.apply_symm_apply, matchingVariableEquiv_inr]
    have hfactor :
        matchingPermutationOutsideFactor d σ z.1.1 =
          MvPolynomial.X z := by
      unfold matchingPermutationOutsideFactor
      rw [hmarked]
    rw [hrest, hfactor]
    simp only [MvPolynomial.pderiv_X, Pi.single_eq_same, ne_eq, one_mul, mul_zero, add_zero, hz,
      ↓reduceIte]
  · have hfirst :
        MvPolynomial.pderiv z
          (matchingPermutationOutsideFactor d σ z.1.1) = 0 := by
        unfold matchingPermutationOutsideFactor
        split
        · simp only [Derivation.map_one_eq_zero]
        · rename_i w hw
          apply MvPolynomial.pderiv_X_of_ne
          intro hzw
          have hpair : (z.1.1, σ z.1.1) = z.1 := by
            have heq := congrArg (matchingVariableEquiv d) hw
            simpa only [Equiv.apply_symm_apply, hzw, matchingVariableEquiv_inr] using heq
          exact hz (congrArg Prod.snd hpair)
    rw [hrest, hfirst]
    simp only [ne_eq, zero_mul, mul_zero, add_zero, hz, ↓reduceIte]

private theorem matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n) (α : Y →₀ ℕ)
    (z : matchingOutside d) (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ
        (MvPolynomial.pderiv z
          (coefficientPolynomial (matchingMarkedPermanent d) α)) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α ∧
          σ z.1.1 = z.1.2 then
          ∏ i : {i : Fin n // i ≠ z.1.1},
            MvPolynomial.eval ξ
              (matchingPermutationOutsideFactor d σ i.1)
        else 0 := by
  classical
  rw [matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingPermutationOutsideProduct_pderiv]
  split_ifs <;> simp_all

private noncomputable def matchingBlockIndexEquiv (ell m : ℕ) :
    ((Fin ell ⊕ Fin ell) ⊕ Fin m) ≃ Fin ((ell + ell) + m) :=
  (Equiv.sumCongr
    (finSumFinEquiv : Fin ell ⊕ Fin ell ≃ Fin (ell + ell))
    (Equiv.refl (Fin m))).trans finSumFinEquiv

private noncomputable def matchingDiagonalEmbedding (ell m : ℕ) :
    (Fin ell ⊕ Fin ell) ↪
      Fin ((ell + ell) + m) × Fin ((ell + ell) + m) where
  toFun y :=
    (matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inl y))
  inj' := by
    intro x y h
    exact Sum.inl_injective
      ((matchingBlockIndexEquiv ell m).injective
        (congrArg Prod.fst h))

private noncomputable def matchingExternalEntry
    (ell m : ℕ) (a b : Fin m) :
    matchingOutside (matchingDiagonalEmbedding ell m) := by
  refine ⟨(matchingBlockIndexEquiv ell m (.inr a),
    matchingBlockIndexEquiv ell m (.inr b)), ?_⟩
  rintro ⟨y, hy⟩
  have hrow := congrArg Prod.fst hy
  have hsum :
      (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) = .inr a :=
    (matchingBlockIndexEquiv ell m).injective hrow
  cases hsum

private noncomputable def matchingPermanentSpecialization
    {ell m : ℕ} (p q : Fin m → ℂ) :
    matchingOutside (matchingDiagonalEmbedding ell m) → ℂ :=
  fun z =>
    match (matchingBlockIndexEquiv ell m).symm z.1.1,
        (matchingBlockIndexEquiv ell m).symm z.1.2 with
    | .inl _, .inl _ => 0
    | .inl (.inl u), .inr b => p b ^ (2 ^ (u : ℕ))
    | .inl (.inr _), .inr _ => 1
    | .inr _, .inl (.inl _) => 1
    | .inr a, .inl (.inr v) => q a ^ (2 ^ (v : ℕ))
    | .inr _, .inr _ => 1

private theorem matchingPermutationOutsideFactor_internal_offDiagonal_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (y y' : Fin ell ⊕ Fin ell) (hne : y' ≠ y)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y')) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor
        (matchingDiagonalEmbedding ell m) σ
        (matchingBlockIndexEquiv ell m (.inl y))) = 0 := by
  classical
  let z : matchingOutside (matchingDiagonalEmbedding ell m) :=
    ⟨(matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inl y')), by
      rintro ⟨t, ht⟩
      have hrow := congrArg Prod.fst ht
      change
        matchingBlockIndexEquiv ell m (.inl t) =
          matchingBlockIndexEquiv ell m (.inl y) at hrow
      have hcol := congrArg Prod.snd ht
      change
        matchingBlockIndexEquiv ell m (.inl t) =
          matchingBlockIndexEquiv ell m (.inl y') at hcol
      have hty : t = y :=
        Sum.inl_injective ((matchingBlockIndexEquiv ell m).injective hrow)
      have hty' : t = y' :=
        Sum.inl_injective ((matchingBlockIndexEquiv ell m).injective hcol)
      exact hne (hty'.symm.trans hty)⟩
  have hsplit :
      (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).symm
        (matchingBlockIndexEquiv ell m (.inl y),
          matchingBlockIndexEquiv ell m (.inl y')) = .inr z := by
    apply (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).injective
    simp only [Equiv.apply_symm_apply, matchingVariableEquiv_inr, z]
  unfold matchingPermutationOutsideFactor
  rw [hσ, hsplit]
  simp only [MvPolynomial.eval_X, matchingPermanentSpecialization, Equiv.symm_apply_apply, z]

private theorem matchingPermutationOutsideFactor_internal_product_zero
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a b : Fin m) (y y' : Fin ell ⊕ Fin ell) (hne : y' ≠ y)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y')) :
    (∏ i : {i : Fin ((ell + ell) + m) //
        i ≠ (matchingExternalEntry ell m a b).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ i.1)) = 0 := by
  classical
  have hnot :
      matchingBlockIndexEquiv ell m (.inl y) ≠
        (matchingExternalEntry ell m a b).1.1 := by
    intro h
    have hsum :
        (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) = .inr a := by
      apply (matchingBlockIndexEquiv ell m).injective
      change
        matchingBlockIndexEquiv ell m (.inl y) =
          matchingBlockIndexEquiv ell m (.inr a) at h
      exact h
    cases hsum
  let i : {i : Fin ((ell + ell) + m) //
      i ≠ (matchingExternalEntry ell m a b).1.1} :=
    ⟨matchingBlockIndexEquiv ell m (.inl y), hnot⟩
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact matchingPermutationOutsideFactor_internal_offDiagonal_eval
    p q σ y y' hne hσ

private theorem matchingPermutationOutsideFactor_eval_of_not_mem_range
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (hij : σ i = j) (houtside : (i, j) ∉ Set.range d)
    (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ (matchingPermutationOutsideFactor d σ i) =
      ξ ⟨(i, j), houtside⟩ := by
  classical
  let z : matchingOutside d := ⟨(i, j), houtside⟩
  have hsplit : (matchingVariableEquiv d).symm (i, j) = .inr z := by
    apply (matchingVariableEquiv d).injective
    simp only [Equiv.apply_symm_apply, matchingVariableEquiv_inr, z]
  unfold matchingPermutationOutsideFactor
  rw [hij, hsplit]
  simp only [MvPolynomial.eval_X, z]

private theorem matching_internal_external_not_mem_diagonal
    {ell m : ℕ} (y : Fin ell ⊕ Fin ell) (b : Fin m) :
    (matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inr b)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hcol := congrArg Prod.snd ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr b) at hcol
  cases (matchingBlockIndexEquiv ell m).injective hcol

private theorem matching_external_internal_not_mem_diagonal
    {ell m : ℕ} (a : Fin m) (y : Fin ell ⊕ Fin ell) :
    (matchingBlockIndexEquiv ell m (.inr a),
      matchingBlockIndexEquiv ell m (.inl y)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hrow := congrArg Prod.fst ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr a) at hrow
  cases (matchingBlockIndexEquiv ell m).injective hrow

private theorem matching_external_external_not_mem_diagonal
    {ell m : ℕ} (a b : Fin m) :
    (matchingBlockIndexEquiv ell m (.inr a),
      matchingBlockIndexEquiv ell m (.inr b)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hrow := congrArg Prod.fst ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr a) at hrow
  cases (matchingBlockIndexEquiv ell m).injective hrow

private theorem matchingPermutationOutsideFactor_fixed_diagonal_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (y : Fin ell ⊕ Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl y))) = 1 := by
  classical
  have hsplit :
      (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).symm
        (matchingBlockIndexEquiv ell m (.inl y),
          matchingBlockIndexEquiv ell m (.inl y)) = .inl y := by
    apply (matchingVariableEquiv
      (matchingDiagonalEmbedding ell m)).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  unfold matchingPermutationOutsideFactor
  rw [hσ, hsplit]
  simp only [map_one]

private theorem matchingPermutationOutsideFactor_left_external_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (u : Fin ell) (b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl (.inl u))) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl (.inl u)))) =
      p b ^ (2 ^ (u : ℕ)) := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inl (.inl u)))
    (matchingBlockIndexEquiv ell m (.inr b)) hσ
    (matching_internal_external_not_mem_diagonal (.inl u) b)]
  simp only [matchingPermanentSpecialization, Equiv.symm_apply_apply]

private theorem matchingPermutationOutsideFactor_right_external_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (v : Fin ell) (b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl (.inr v))) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl (.inr v)))) = 1 := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inl (.inr v)))
    (matchingBlockIndexEquiv ell m (.inr b)) hσ
    (matching_internal_external_not_mem_diagonal (.inr v) b)]
  simp only [matchingPermanentSpecialization, Equiv.symm_apply_apply]

private theorem matchingPermutationOutsideFactor_external_left_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a : Fin m) (u : Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inl (.inl u))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) = 1 := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inr a))
    (matchingBlockIndexEquiv ell m (.inl (.inl u))) hσ
    (matching_external_internal_not_mem_diagonal a (.inl u))]
  simp only [matchingPermanentSpecialization, Equiv.symm_apply_apply]

private theorem matchingPermutationOutsideFactor_external_right_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a : Fin m) (v : Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inl (.inr v))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) =
      q a ^ (2 ^ (v : ℕ)) := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inr a))
    (matchingBlockIndexEquiv ell m (.inl (.inr v))) hσ
    (matching_external_internal_not_mem_diagonal a (.inr v))]
  simp only [matchingPermanentSpecialization, Equiv.symm_apply_apply]

private theorem matchingPermutationOutsideFactor_external_external_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) = 1 := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inr a))
    (matchingBlockIndexEquiv ell m (.inr b)) hσ
    (matching_external_external_not_mem_diagonal a b)]
  simp only [matchingPermanentSpecialization, Equiv.symm_apply_apply]

private structure MatchingCrossData (T A B : Type*) where
  rows : T ↪ B
  cols : T ↪ A
  remainder :
    {a : A // a ∉ Set.range cols} ≃
      {b : B // b ∉ Set.range rows}

private noncomputable def MatchingCrossData.assemble
    {T A B : Type*} (c : MatchingCrossData T A B) :
    T ⊕ A ≃ T ⊕ B := by
  classical
  let ce : T ≃ Set.range c.cols :=
    Equiv.ofInjective c.cols c.cols.injective
  let re : T ≃ Set.range c.rows :=
    Equiv.ofInjective c.rows c.rows.injective
  let splitA : A ≃ T ⊕ {a : A // a ∉ Set.range c.cols} :=
    (Equiv.Set.sumCompl (Set.range c.cols)).symm.trans
      (Equiv.sumCongr ce.symm (Equiv.refl _))
  let mergeB : T ⊕ {b : B // b ∉ Set.range c.rows} ≃ B :=
    (Equiv.sumCongr re (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range c.rows))
  exact
    (Equiv.sumCongr (Equiv.refl T) splitA).trans
      ((Equiv.sumAssoc T T _).symm.trans
        ((Equiv.sumCongr (Equiv.sumComm T T) (Equiv.refl _)).trans
          ((Equiv.sumAssoc T T _).trans
            (Equiv.sumCongr (Equiv.refl T)
              ((Equiv.sumCongr (Equiv.refl T) c.remainder).trans
                mergeB)))))

@[simp] private theorem MatchingCrossData.assemble_inl
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble (.inl t) = .inr (c.rows t) := by
  classical
  change
    Sum.inr ((Equiv.Set.sumCompl (Set.range c.rows))
      (.inl ((Equiv.ofInjective c.rows c.rows.injective) t))) =
        Sum.inr (c.rows t)
  rfl

@[simp] private theorem MatchingCrossData.assemble_cols
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble (.inr (c.cols t)) = .inl t := by
  classical
  simp only [assemble, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans,
    Sum.map_inr,
    Function.comp_apply, Set.mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq,
      Equiv.Set.sumCompl_symm_apply_of_mem,
    Sum.map_inl, Equiv.ofInjective_symm_apply, Equiv.sumAssoc_symm_apply_inr_inl,
      Equiv.sumComm_apply, Sum.swap_inr,
    Equiv.sumAssoc_apply_inl_inl, id_eq]

@[simp] private theorem MatchingCrossData.assemble_remainder
    {T A B : Type*} (c : MatchingCrossData T A B)
    (a : {a : A // a ∉ Set.range c.cols}) :
    c.assemble (.inr a.1) = .inr (c.remainder a).1 := by
  classical
  simp only [MatchingCrossData.assemble, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr,
    Function.comp_apply,
    Equiv.Set.sumCompl_symm_apply_of_notMem a.property,
    Subtype.coe_eta, id_eq, Equiv.sumAssoc_symm_apply_inr_inr,
    Equiv.sumComm_apply, Equiv.sumAssoc_apply_inr, Sum.inr.injEq]
  exact Equiv.Set.sumCompl_apply_inr (Set.range c.rows)
    (c.remainder a)

private theorem matching_card_compl_range
    {T A : Type*} [Fintype T] [Fintype A] [DecidableEq A]
    (f : T ↪ A) :
    Fintype.card {a : A // a ∉ Set.range f} =
      Fintype.card A - Fintype.card T := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_range]

private theorem matching_card_residual_equiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rows : T ↪ B) (cols : T ↪ A)
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card
      ({a : A // a ∉ Set.range cols} ≃
        {b : B // b ∉ Set.range rows}) =
      (Fintype.card A - Fintype.card T).factorial := by
  classical
  have hrem :
      Fintype.card {a : A // a ∉ Set.range cols} =
        Fintype.card {b : B // b ∉ Set.range rows} := by
    rw [matching_card_compl_range, matching_card_compl_range, hcard]
  let e := Fintype.equivOfCardEq hrem
  rw [Fintype.card_equiv e, matching_card_compl_range]

private abbrev MatchingCrossPermutation (T A B : Type*) :=
  {σ : T ⊕ A ≃ T ⊕ B //
    ∀ t : T, ∃ b : B, σ (.inl t) = .inr b}

private noncomputable def matchingCrossRows {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) : T ↪ B where
  toFun t := Classical.choose (σ.property t)
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply σ.1.injective
    calc
      σ.1 (.inl x) = .inr (Classical.choose (σ.property x)) :=
        Classical.choose_spec (σ.property x)
      _ = .inr (Classical.choose (σ.property y)) :=
        congrArg Sum.inr h
      _ = σ.1 (.inl y) :=
        (Classical.choose_spec (σ.property y)).symm

private theorem matchingCrossRows_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    σ.1 (.inl t) = .inr (matchingCrossRows σ t) :=
  Classical.choose_spec (σ.property t)

private theorem matchingCrossCols_exists {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    ∃ a : A, σ.1.symm (.inl t) = .inr a := by
  classical
  cases h : σ.1.symm (.inl t) with
  | inl u =>
      obtain ⟨b, hb⟩ := σ.property u
      have hu : σ.1 (.inl u) = .inl t := by
        calc
          σ.1 (.inl u) = σ.1 (σ.1.symm (.inl t)) := by rw [h]
          _ = .inl t := σ.1.apply_symm_apply _
      rw [hu] at hb
      cases hb
  | inr a => exact ⟨a, rfl⟩

private noncomputable def matchingCrossCols {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) : T ↪ A where
  toFun t := Classical.choose (matchingCrossCols_exists σ t)
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply σ.1.symm.injective
    calc
      σ.1.symm (.inl x) =
        .inr (Classical.choose (matchingCrossCols_exists σ x)) :=
          Classical.choose_spec (matchingCrossCols_exists σ x)
      _ = .inr (Classical.choose (matchingCrossCols_exists σ y)) := by
        exact congrArg Sum.inr h
      _ = σ.1.symm (.inl y) :=
        (Classical.choose_spec (matchingCrossCols_exists σ y)).symm

private theorem matchingCrossCols_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    σ.1.symm (.inl t) = .inr (matchingCrossCols σ t) :=
  Classical.choose_spec (matchingCrossCols_exists σ t)

private theorem matchingCrossResidual_exists {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    ∃ b : {b : B // b ∉ Set.range (matchingCrossRows σ)},
      σ.1 (.inr a.1) = .inr b.1 := by
  classical
  cases h : σ.1 (.inr a.1) with
  | inl t =>
      have hsym := congrArg σ.1.symm h
      rw [σ.1.symm_apply_apply, matchingCrossCols_spec] at hsym
      have ha : a.1 = matchingCrossCols σ t :=
        Sum.inr_injective hsym
      exact False.elim (a.property ⟨t, ha.symm⟩)
  | inr b =>
      have hb : b ∉ Set.range (matchingCrossRows σ) := by
        rintro ⟨t, ht⟩
        have hsame : σ.1 (.inr a.1) = σ.1 (.inl t) := by
          rw [h, matchingCrossRows_spec, ht]
        have hbad :
            (Sum.inr a.1 : T ⊕ A) = .inl t :=
          σ.1.injective hsame
        cases hbad
      exact ⟨⟨b, hb⟩, rfl⟩

private noncomputable def matchingCrossResidualValue {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    {b : B // b ∉ Set.range (matchingCrossRows σ)} :=
  Classical.choose (matchingCrossResidual_exists σ a)

private theorem matchingCrossResidualValue_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    σ.1 (.inr a.1) = .inr (matchingCrossResidualValue σ a).1 :=
  Classical.choose_spec (matchingCrossResidual_exists σ a)

private noncomputable def matchingCrossResidualEmbedding {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) :
    {a : A // a ∉ Set.range (matchingCrossCols σ)} ↪
      {b : B // b ∉ Set.range (matchingCrossRows σ)} where
  toFun := matchingCrossResidualValue σ
  inj' := by
    intro a a' h
    apply Subtype.ext
    apply Sum.inr_injective
    apply σ.1.injective
    rw [matchingCrossResidualValue_spec,
      matchingCrossResidualValue_spec, h]

private theorem matchingCrossPermutation_external_card
    {T A B : Type*} [Finite T] [Fintype A] [Fintype B]
    (σ : MatchingCrossPermutation T A B) :
    Fintype.card A = Fintype.card B := by
  let := Fintype.ofFinite T
  have h := Fintype.card_congr σ.1
  simpa only [Fintype.card_sum, Nat.add_left_cancel_iff] using h

private noncomputable def matchingCrossResidualEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    {a : A // a ∉ Set.range (matchingCrossCols σ)} ≃
      {b : B // b ∉ Set.range (matchingCrossRows σ)} := by
  let e := matchingCrossResidualEmbedding σ
  refine Equiv.ofBijective e
    ((Fintype.bijective_iff_injective_and_card e).2
      ⟨e.injective, ?_⟩)
  rw [matching_card_compl_range, matching_card_compl_range,
    matchingCrossPermutation_external_card σ]

private noncomputable def MatchingCrossData.ofPermutation
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    MatchingCrossData T A B where
  rows := matchingCrossRows σ
  cols := matchingCrossCols σ
  remainder := matchingCrossResidualEquiv σ

private theorem MatchingCrossData.ofPermutation_remainder_spec
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    σ.1 (.inr a.1) =
      .inr ((MatchingCrossData.ofPermutation σ).remainder a).1 :=
  matchingCrossResidualValue_spec σ a

@[simp] private theorem MatchingCrossData.assemble_symm_inl
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble.symm (.inl t) = .inr (c.cols t) := by
  apply c.assemble.injective
  rw [Equiv.apply_symm_apply, MatchingCrossData.assemble_cols]

private theorem MatchingCrossData.assemble_ofPermutation
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    (MatchingCrossData.ofPermutation σ).assemble = σ.1 := by
  classical
  apply Equiv.ext
  intro x
  cases x with
  | inl t =>
      rw [MatchingCrossData.assemble_inl]
      exact (matchingCrossRows_spec σ t).symm
  | inr a =>
      by_cases ha : a ∈ Set.range (matchingCrossCols σ)
      · obtain ⟨t, ht⟩ := ha
        subst a
        have hleft :
            (MatchingCrossData.ofPermutation σ).assemble
              (.inr (matchingCrossCols σ t)) = .inl t :=
          MatchingCrossData.assemble_cols
            (MatchingCrossData.ofPermutation σ) t
        rw [hleft]
        simpa only [Equiv.apply_symm_apply] using congrArg σ.1 (matchingCrossCols_spec σ t)
      · have hx := MatchingCrossData.ofPermutation_remainder_spec
          σ (⟨a, ha⟩ : {a : A // a ∉ Set.range (matchingCrossCols σ)})
        rw [MatchingCrossData.assemble_remainder
          (MatchingCrossData.ofPermutation σ)
            (⟨a, ha⟩ : {a : A // a ∉ Set.range (matchingCrossCols σ)})]
        exact hx.symm

private theorem MatchingCrossData.assemble_injective
    {T A B : Type*} :
    Function.Injective
      (MatchingCrossData.assemble (T := T) (A := A) (B := B)) := by
  classical
  intro c d h
  have hrows : c.rows = d.rows := by
    apply Function.Embedding.ext
    intro t
    apply Sum.inr_injective
    calc
      Sum.inr (c.rows t) = c.assemble (.inl t) :=
        (MatchingCrossData.assemble_inl c t).symm
      _ = d.assemble (.inl t) := DFunLike.congr_fun h (.inl t)
      _ = Sum.inr (d.rows t) :=
        MatchingCrossData.assemble_inl d t
  have hcols : c.cols = d.cols := by
    apply Function.Embedding.ext
    intro t
    apply Sum.inr_injective
    calc
      Sum.inr (c.cols t) = c.assemble.symm (.inl t) :=
        (MatchingCrossData.assemble_symm_inl c t).symm
      _ = d.assemble.symm (.inl t) := by rw [h]
      _ = Sum.inr (d.cols t) :=
        MatchingCrossData.assemble_symm_inl d t
  cases c with
  | mk cr cc ce =>
      cases d with
      | mk dr dc de =>
          change cr = dr at hrows
          subst dr
          change cc = dc at hcols
          subst dc
          congr 1
          apply Equiv.ext
          intro a
          apply Subtype.ext
          apply Sum.inr_injective
          calc
            Sum.inr (ce a).1 =
                (MatchingCrossData.mk cr cc ce).assemble (.inr a.1) :=
              (MatchingCrossData.assemble_remainder
                (MatchingCrossData.mk cr cc ce) a).symm
            _ = (MatchingCrossData.mk cr cc de).assemble (.inr a.1) :=
              DFunLike.congr_fun h (.inr a.1)
            _ = Sum.inr (de a).1 :=
              MatchingCrossData.assemble_remainder
                (MatchingCrossData.mk cr cc de) a

private noncomputable def MatchingCrossData.toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    MatchingCrossPermutation T A B :=
  ⟨c.assemble, fun t => ⟨c.rows t, c.assemble_inl t⟩⟩

private noncomputable def matchingCrossPermutationEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    MatchingCrossPermutation T A B ≃ MatchingCrossData T A B where
  toFun := MatchingCrossData.ofPermutation
  invFun := MatchingCrossData.toPermutation
  left_inv σ := by
    apply Subtype.ext
    exact MatchingCrossData.assemble_ofPermutation σ
  right_inv c := by
    apply MatchingCrossData.assemble_injective
    exact MatchingCrossData.assemble_ofPermutation
      (MatchingCrossData.toPermutation c)

private noncomputable def matchingCrossDataSigmaEquiv (T A B : Type*) :
    MatchingCrossData T A B ≃
      (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
        {a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}) where
  toFun c := ⟨c.rows, c.cols, c.remainder⟩
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv c := by cases c; rfl
  right_inv z := by rcases z with ⟨rows, cols, remainder⟩; rfl

private noncomputable def matchingCrossPermutationSigmaEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    MatchingCrossPermutation T A B ≃
      (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
        {a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}) :=
  matchingCrossPermutationEquiv.trans
    (matchingCrossDataSigmaEquiv T A B)

private noncomputable instance matchingCrossPermutationFintype
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    Fintype (MatchingCrossPermutation T A B) := by
  classical
  exact Fintype.ofEquiv _
    (matchingCrossPermutationSigmaEquiv
      (T := T) (A := A) (B := B)).symm

@[simp] private theorem matchingCrossRows_toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    matchingCrossRows c.toPermutation = c.rows := by
  apply Function.Embedding.ext
  intro t
  apply Sum.inr_injective
  calc
    Sum.inr (matchingCrossRows c.toPermutation t) =
        c.toPermutation.1 (.inl t) :=
      (matchingCrossRows_spec c.toPermutation t).symm
    _ = Sum.inr (c.rows t) := c.assemble_inl t

@[simp] private theorem matchingCrossCols_toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    matchingCrossCols c.toPermutation = c.cols := by
  apply Function.Embedding.ext
  intro t
  apply Sum.inr_injective
  calc
    Sum.inr (matchingCrossCols c.toPermutation t) =
        c.toPermutation.1.symm (.inl t) :=
      (matchingCrossCols_spec c.toPermutation t).symm
    _ = c.assemble.symm (.inl t) := rfl
    _ = Sum.inr (c.cols t) := c.assemble_symm_inl t

private theorem sum_matchingCrossPermutation
    {F T A B : Type*} [AddCommMonoid F]
    [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (w : MatchingCrossPermutation T A B → F) :
    (∑ σ : MatchingCrossPermutation T A B, w σ) =
      ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
        ∑ remainder :
          ({a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}),
          w (MatchingCrossData.toPermutation
            ⟨rows, cols, remainder⟩) := by
  classical
  let e := matchingCrossPermutationSigmaEquiv (T := T) (A := A) (B := B)
  calc
    (∑ σ : MatchingCrossPermutation T A B, w σ) =
        ∑ z : (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
          {a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}), w (e.symm z) := by
          refine Fintype.sum_equiv e _ _ ?_
          intro σ
          simp only [Equiv.symm_apply_apply]
    _ = ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
        ∑ remainder :
          ({a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}),
          w (MatchingCrossData.toPermutation
            ⟨rows, cols, remainder⟩) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro rows _
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro cols _
          apply Finset.sum_congr rfl
          intro remainder _
          rfl

private theorem sum_matchingCrossPermutation_rows_cols
    {F T A B : Type*} [Semiring F]
    [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hcard : Fintype.card A = Fintype.card B)
    (w : (T ↪ B) → (T ↪ A) → F) :
    (∑ σ : MatchingCrossPermutation T A B,
      w (matchingCrossRows σ) (matchingCrossCols σ)) =
      ((Fintype.card A - Fintype.card T).factorial : F) *
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A), w rows cols := by
  classical
  rw [sum_matchingCrossPermutation]
  calc
    (∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
      ∑ remainder :
        ({a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}),
        w (matchingCrossRows
            (MatchingCrossData.toPermutation ⟨rows, cols, remainder⟩))
          (matchingCrossCols
            (MatchingCrossData.toPermutation ⟨rows, cols, remainder⟩))) =
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
          ((Fintype.card A - Fintype.card T).factorial : F) *
            w rows cols := by
          apply Finset.sum_congr rfl
          intro rows _
          apply Finset.sum_congr rfl
          intro cols _
          have hres := matching_card_residual_equiv rows cols hcard
          simpa only [matchingCrossRows_toPermutation, matchingCrossCols_toPermutation,
            Finset.sum_const,
            Finset.card_univ, Set.mem_range, not_exists,
              nsmul_eq_mul] using congrArg (fun k : ℕ => (k : F) * w rows cols) hres
    _ = ((Fintype.card A - Fintype.card T).factorial : F) *
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A), w rows cols := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rows _
          rw [Finset.mul_sum]

private def matchingBinaryDegree {ell : ℕ} (P : Finset (Fin ell)) : ℕ :=
  ∑ u ∈ P, 2 ^ (u : ℕ)

private noncomputable def matchingInjectionSum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) : F := by
  classical
  exact ∑ rho : (↥P ↪ Fin m), ∏ u : ↥P, p (rho u) ^ (2 ^ (u.1 : ℕ))

private noncomputable def matchingPolynomial {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) : Polynomial F :=
  if hP : P.Nonempty then
    Polynomial.C (matchingInjectionSum p P) -
      ∑ u : ↥P,
        (Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)
  else
    1
termination_by P.card
decreasing_by
  exact Finset.card_erase_lt_of_mem u.property

@[simp] private theorem matchingPolynomial_empty {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) :
    matchingPolynomial (ell := ell) p ∅ = 1 := by
  simp only [matchingPolynomial, Finset.not_nonempty_empty, ↓reduceDIte]

private theorem matchingPolynomial_of_nonempty {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell))
    (hP : P.Nonempty) :
    matchingPolynomial p P =
      Polynomial.C (matchingInjectionSum p P) -
        ∑ u : ↥P,
          (Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
            matchingPolynomial p (P.erase u.1) := by
  rw [matchingPolynomial]
  simp only [hP, ↓reduceDIte, Finset.univ_eq_attach]

@[simp] private theorem matchingBinaryDegree_empty (ell : ℕ) :
    matchingBinaryDegree (ell := ell) ∅ = 0 := by
  simp only [matchingBinaryDegree, Finset.sum_empty]

private theorem matchingBinaryDegree_erase_add {ell : ℕ}
    (P : Finset (Fin ell)) (u : Fin ell) (hu : u ∈ P) :
    matchingBinaryDegree (P.erase u) + 2 ^ (u : ℕ) = matchingBinaryDegree P := by
  classical
  unfold matchingBinaryDegree
  rw [← Finset.sum_erase_add _ _ hu]

private theorem matchingPolynomial_natDegree_le {F : Type*} [CommRing F] [Nontrivial F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).natDegree ≤ matchingBinaryDegree P := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · rw [matchingPolynomial_of_nonempty p P hP]
    apply (Polynomial.natDegree_sub_le_of_le
      (m := matchingBinaryDegree P) (n := matchingBinaryDegree P) ?_ ?_).trans
      (by simp only [max_self, Std.le_refl])
    · simp only [Polynomial.natDegree_C, zero_le]
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro u _
      calc
        ((Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)).natDegree
            ≤ 2 ^ (u.1 : ℕ) + matchingBinaryDegree (P.erase u.1) :=
              Polynomial.natDegree_mul_le_of_le
                (by simp only [Polynomial.natDegree_X_pow,
                  Std.le_refl]) (ih (P.erase u.1) (Finset.erase_ssubset u.property))
        _ = matchingBinaryDegree P := by
          rw [Nat.add_comm, matchingBinaryDegree_erase_add P u.1 u.property]
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp only [matchingPolynomial_empty, Polynomial.natDegree_one, matchingBinaryDegree_empty,
      Std.le_refl]

private theorem matchingBinaryDegree_pos {ell : ℕ}
    (P : Finset (Fin ell)) (hP : P.Nonempty) :
    0 < matchingBinaryDegree P := by
  classical
  obtain ⟨u, hu⟩ := hP
  rw [← matchingBinaryDegree_erase_add P u hu]
  exact Nat.add_pos_right _ (Nat.pow_pos Nat.two_pos)

private theorem matchingPolynomial_coeff_binaryDegree {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).coeff (matchingBinaryDegree P) =
      (-1 : F) ^ P.card * (P.card.factorial : F) := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · have hD : matchingBinaryDegree P ≠ 0 :=
      (matchingBinaryDegree_pos P hP).ne'
    have hterm (u : ↥P) :
        ((Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)).coeff (matchingBinaryDegree P) =
            (-1 : F) ^ (P.card - 1) * ((P.card - 1).factorial : F) := by
      rw [← matchingBinaryDegree_erase_add P u.1 u.property,
        Polynomial.coeff_X_pow_mul,
        ih (P.erase u.1) (Finset.erase_ssubset u.property),
        Finset.card_erase_of_mem u.property]
    rw [matchingPolynomial_of_nonempty p P hP, Polynomial.coeff_sub,
      Polynomial.coeff_C_of_ne_zero hD]
    simp_rw [Polynomial.finsetSum_coeff, hterm]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hP.card_ne_zero
    rw [hr]
    simp only [Finset.univ_eq_attach, Nat.succ_eq_add_one, add_tsub_cancel_right, mul_comm,
      Finset.sum_const,
      Finset.card_attach, hr, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, zero_sub, pow_succ,
        neg_mul, one_mul,
      Nat.factorial_succ, Nat.cast_mul, mul_neg, mul_assoc, neg_inj]
    ac_rfl
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp only [matchingPolynomial_empty, matchingBinaryDegree_empty, Polynomial.coeff_one_zero,
      Finset.card_empty,
      pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]

private theorem matchingPolynomial_coeff_binaryDegree_ne_zero
    {F : Type*} [Field F] [CharZero F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).coeff (matchingBinaryDegree P) ≠ 0 := by
  rw [matchingPolynomial_coeff_binaryDegree]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero P.card))

private theorem matchingPolynomial_natDegree {F : Type*} [Field F] [CharZero F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).natDegree = matchingBinaryDegree P := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (matchingPolynomial_natDegree_le p P)
    (matchingPolynomial_coeff_binaryDegree_ne_zero p P)

private def matchingEraseEmbedding {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m)
    (rho : ↥P ↪ Fin m) (hrho : rho u = b) :
    ↥(P.erase u.1) ↪ {j : Fin m // j ≠ b} where
  toFun v :=
    ⟨rho ⟨v.1, (Finset.mem_erase.mp v.property).2⟩, by
      intro hv
      have hsame := rho.injective (hv.trans hrho.symm)
      exact (Finset.mem_erase.mp v.property).1
        (congrArg Subtype.val hsame)⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun x : ↥P => x.1)
      (rho.injective (congrArg Subtype.val h))

private def matchingInsertEmbedding {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m)
    (rho : ↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}) :
    ↥P ↪ Fin m where
  toFun v :=
    if hv : v.1 = u.1 then b
    else (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).1
  inj' := by
    intro v w h
    by_cases hv : v.1 = u.1
    · by_cases hw : w.1 = u.1
      · exact Subtype.ext (hv.trans hw.symm)
      · exfalso
        have heq :
            (rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩).1 = b := by
          simpa only [ne_eq, hw, ↓reduceDIte, hv] using h.symm
        exact (rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩).property heq
    · by_cases hw : w.1 = u.1
      · exfalso
        have heq :
            (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).1 = b := by
          simpa only [ne_eq, hv, ↓reduceDIte, hw] using h
        exact (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).property heq
      · apply Subtype.ext
        have himage :
            rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩ =
              rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩ := by
          apply Subtype.ext
          simpa only [ne_eq, hv, ↓reduceDIte, hw] using h
        exact congrArg (fun x : ↥(P.erase u.1) => x.1)
          (rho.injective himage)

private noncomputable def matchingHitEmbeddingEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m) :
    {rho : ↥P ↪ Fin m // rho u = b} ≃
      (↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}) where
  toFun rho := matchingEraseEmbedding u b rho.1 rho.2
  invFun rho :=
    ⟨matchingInsertEmbedding u b rho, by
      simp only [matchingInsertEmbedding, SetLike.coe_eq_coe, ne_eq,
        Function.Embedding.coeFn_mk, ↓reduceDIte]⟩
  left_inv rho := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    by_cases hv : v = u
    · subst v
      simpa only [matchingInsertEmbedding, SetLike.coe_eq_coe, ne_eq, Function.Embedding.coeFn_mk,
        ↓reduceDIte] using rho.property.symm
    · have hv' : v.1 ≠ u.1 := fun h => hv (Subtype.ext h)
      change
        (if h : v.1 = u.1 then b
          else (matchingEraseEmbedding u b rho.1 rho.2
            ⟨v.1, Finset.mem_erase.mpr ⟨h, v.property⟩⟩).1) = rho.1 v
      rw [dite_eq_right hv']
      rfl
  right_inv rho := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    have hv : v.1 ≠ u.1 := (Finset.mem_erase.mp v.property).1
    have hv' :
        (⟨v.1, (Finset.mem_erase.mp v.property).2⟩ : ↥P) ≠ u := by
      intro h
      exact hv (congrArg Subtype.val h)
    simp only [ne_eq, matchingEraseEmbedding, matchingInsertEmbedding, SetLike.coe_eq_coe,
      Function.Embedding.coeFn_mk, Subtype.coe_eta, dite_eq_ite, hv', ↓reduceIte]

private noncomputable def matchingAvoidingInjectionSum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) : F := by
  classical
  exact ∑ rho : (↥P ↪ {j : Fin m // j ≠ b}),
    ∏ u : ↥P, p (rho u).1 ^ (2 ^ (u.1 : ℕ))

private def matchingEraseIndexEquiv {ell : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) :
    {v : ↥P // v ≠ u} ≃ ↥(P.erase u.1) where
  toFun v :=
    ⟨v.1.1, Finset.mem_erase.mpr
      ⟨fun h => v.2 (Subtype.ext h), v.1.2⟩⟩
  invFun v :=
    ⟨⟨v.1, (Finset.mem_erase.mp v.2).2⟩, by
      intro h
      exact (Finset.mem_erase.mp v.2).1 (congrArg Subtype.val h)⟩
  left_inv _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv _ := by
    apply Subtype.ext
    rfl

private theorem matchingEmbedding_prod_split {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) {P : Finset (Fin ell)}
    (u : ↥P) (b : Fin m) (rho : ↥P ↪ Fin m) (hrho : rho u = b) :
    (∏ v : ↥P, p (rho v) ^ (2 ^ (v.1 : ℕ))) =
      p b ^ (2 ^ (u.1 : ℕ)) *
        ∏ v : ↥(P.erase u.1),
          p ((matchingEraseEmbedding u b rho hrho) v).1 ^
            (2 ^ (v.1 : ℕ)) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun v : ↥P => p (rho v) ^ (2 ^ (v.1 : ℕ))) u, hrho]
  congr 1
  refine Fintype.prod_equiv (matchingEraseIndexEquiv u) _ _ ?_
  intro v
  rfl

private theorem matchingHitFiber_sum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) {P : Finset (Fin ell)}
    (u : ↥P) (b : Fin m) :
    (∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
      ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
        p b ^ (2 ^ (u.1 : ℕ)) *
          matchingAvoidingInjectionSum p (P.erase u.1) b := by
  classical
  calc
    (∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
      ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
        ∑ rho : (↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}),
          p b ^ (2 ^ (u.1 : ℕ)) *
            ∏ v : ↥(P.erase u.1), p (rho v).1 ^ (2 ^ (v.1 : ℕ)) := by
              refine Fintype.sum_equiv (matchingHitEmbeddingEquiv u b) _ _ ?_
              intro rho
              exact matchingEmbedding_prod_split p u b rho.1 rho.2
    _ = p b ^ (2 ^ (u.1 : ℕ)) *
          matchingAvoidingInjectionSum p (P.erase u.1) b := by
            simp only [ne_eq, Finset.univ_eq_attach, matchingAvoidingInjectionSum, Finset.mul_sum]

private def matchingAvoidingEmbeddingEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m) :
    {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b} ≃
      (↥P ↪ {j : Fin m // j ≠ b}) where
  toFun rho :=
    { toFun := fun u => ⟨rho.1 u, rho.2 u⟩
      inj' := by
        intro u v h
        exact rho.1.injective (congrArg Subtype.val h) }
  invFun rho :=
    ⟨{ toFun := fun u => (rho u).1
       inj' := by
         intro u v h
         exact rho.injective (Subtype.ext h) },
      fun u => (rho u).2⟩
  left_inv _ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro _
    rfl
  right_inv _ := by
    apply Function.Embedding.ext
    intro _
    rfl

private theorem matching_exists_hit {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) :
    ∃ u : ↥P, rho.1 u = b := by
  classical
  by_contra h
  apply rho.property
  intro u hu
  exact h ⟨u, hu⟩

private noncomputable def matchingHitIndex {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) : ↥P :=
  Classical.choose (matching_exists_hit b rho)

private theorem matchingHitIndex_spec {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) :
    rho.1 (matchingHitIndex b rho) = b :=
  Classical.choose_spec (matching_exists_hit b rho)

private noncomputable def matchingHitSigmaEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m) :
    {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b} ≃
      Σ u : ↥P, {rho : ↥P ↪ Fin m // rho u = b} where
  toFun rho :=
    ⟨matchingHitIndex b rho, ⟨rho.1, matchingHitIndex_spec b rho⟩⟩
  invFun rho :=
    ⟨rho.2.1, by
      intro h
      exact h rho.1 rho.2.2⟩
  left_inv _ := by
    apply Subtype.ext
    rfl
  right_inv rho := by
    rcases rho with ⟨u, rho⟩
    have hindex :
        matchingHitIndex b
          (⟨rho.1, fun h => h u rho.2⟩ :
            {f : ↥P ↪ Fin m // ¬ ∀ v, f v ≠ b}) = u :=
      rho.1.injective
        ((matchingHitIndex_spec b
          ⟨rho.1, fun h => h u rho.2⟩).trans rho.2.symm)
    refine Sigma.ext hindex ?_
    exact (Subtype.heq_iff_coe_eq (fun f => by
      change
        f (matchingHitIndex b
          (⟨rho.1, fun h => h u rho.2⟩ :
            {g : ↥P ↪ Fin m // ¬ ∀ v, g v ≠ b})) = b ↔ f u = b
      rw [hindex])).2 rfl

private theorem matchingInjectionSum_partition {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) :
    matchingInjectionSum p P =
      matchingAvoidingInjectionSum p P b +
        ∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            matchingAvoidingInjectionSum p (P.erase u.1) b := by
  classical
  have havoid :
      (∑ rho : {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          matchingAvoidingInjectionSum p P b := by
    unfold matchingAvoidingInjectionSum
    refine Fintype.sum_equiv (matchingAvoidingEmbeddingEquiv b) _ _ ?_
    intro rho
    rfl
  have hhit :
      (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          ∑ u : ↥P,
            ∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
              ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ)) := by
    calc
      (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          ∑ rho : (Σ u : ↥P, {rho : ↥P ↪ Fin m // rho u = b}),
            ∏ v : ↥P, p (rho.2.1 v) ^ (2 ^ (v.1 : ℕ)) := by
              refine Fintype.sum_equiv (matchingHitSigmaEquiv b) _ _ ?_
              intro rho
              rfl
      _ = ∑ u : ↥P,
            ∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
              ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ)) :=
            Fintype.sum_sigma _
  calc
    matchingInjectionSum p P =
        (∑ rho : {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b},
          ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) +
        (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
          ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) := by
            simpa only [matchingInjectionSum] using
              (Fintype.sum_subtype_add_sum_subtype
                (fun rho : ↥P ↪ Fin m => ∀ u, rho u ≠ b)
                (fun rho => ∏ v : ↥P,
                  p (rho v) ^ (2 ^ (v.1 : ℕ)))).symm
    _ = matchingAvoidingInjectionSum p P b +
        ∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            matchingAvoidingInjectionSum p (P.erase u.1) b := by
              rw [havoid, hhit]
              refine congrArg₂ (· + ·) rfl ?_
              apply Finset.sum_congr rfl
              intro u _
              exact matchingHitFiber_sum p u b

@[simp] private theorem matchingAvoidingInjectionSum_empty
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (p : Fin m → F) (b : Fin m) :
    matchingAvoidingInjectionSum (ell := ell) p ∅ b = 1 := by
  classical
  simp only [matchingAvoidingInjectionSum, ne_eq, Finset.univ_unique, Finset.univ_eq_empty,
    Finset.prod_empty,
    Finset.sum_const, Finset.card_singleton, one_smul]

private theorem matchingPolynomial_eval {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) :
    (matchingPolynomial p P).eval (p b) =
      matchingAvoidingInjectionSum p P b := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · rw [matchingPolynomial_of_nonempty p P hP, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_X_pow]
    have hterms :
        (∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            (matchingPolynomial p (P.erase u.1)).eval (p b)) =
          ∑ u : ↥P,
            p b ^ (2 ^ (u.1 : ℕ)) *
              matchingAvoidingInjectionSum p (P.erase u.1) b := by
      apply Finset.sum_congr rfl
      intro u _
      rw [ih (P.erase u.1) (Finset.erase_ssubset u.property)]
    rw [hterms, matchingInjectionSum_partition p P b]
    simp only [Finset.univ_eq_attach, add_sub_cancel_right]
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp only [matchingPolynomial_empty, Polynomial.eval_one, matchingAvoidingInjectionSum_empty]

private noncomputable def matchingPolynomialEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p : Fin m → F) (P : Fin m → Finset (Fin ell)) :
    Matrix (Fin m) (Fin m) F :=
  fun b d => (matchingPolynomial p (P d)).eval (p b)

private theorem matchingPolynomialEvaluationMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p : Fin m → F) (hp : Function.Injective p)
    (P : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ)) :
    (matchingPolynomialEvaluationMatrix p P).det ≠ 0 := by
  classical
  let g : Fin m → Polynomial F := fun d => matchingPolynomial p (P d)
  have hdegree (d : Fin m) : (g d).natDegree = (d : ℕ) := by
    exact (matchingPolynomial_natDegree p (P d)).trans (hP d)
  change (Matrix.of (fun b d : Fin m => (g d).eval (p b))).det ≠ 0
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    p g (fun d => (hdegree d).le), Matrix.det_mul]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hp
  · rw [Matrix.det_of_isUpperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular g
        (fun d => (hdegree d).le))]
    apply Finset.prod_ne_zero_iff.mpr
    intro d _
    change (matchingPolynomial p (P d)).coeff (d : ℕ) ≠ 0
    rw [← hP d]
    exact matchingPolynomial_coeff_binaryDegree_ne_zero p (P d)

private def matchingBitSubset (ell d : ℕ) : Finset (Fin ell) := by
  classical
  exact Finset.univ.filter (fun u : Fin ell => (u : ℕ) ∈ d.bitIndices)

private theorem matchingBitSubset_map_val (ell d : ℕ) (hd : d < 2 ^ ell) :
    (matchingBitSubset ell d).map Fin.valEmbedding =
      d.bitIndices.toFinset := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    have hbit : (u : ℕ) ∈ d.bitIndices :=
      (Finset.mem_filter.mp hu).2
    simpa only [Fin.valEmbedding_apply, List.mem_toFinset, Nat.mem_bitIndices] using hbit
  · intro ha
    have hbit : a ∈ d.bitIndices := by simpa only [Nat.mem_bitIndices, List.mem_toFinset] using ha
    have hlt : a < ell := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      exact (Nat.two_pow_le_of_mem_bitIndices hbit).trans_lt hd
    refine Finset.mem_map.mpr ⟨⟨a, hlt⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩

private theorem matchingBinaryDegree_bitSubset (ell d : ℕ) (hd : d < 2 ^ ell) :
    matchingBinaryDegree (matchingBitSubset ell d) = d := by
  classical
  unfold matchingBinaryDegree
  calc
    (∑ u ∈ matchingBitSubset ell d, 2 ^ (u : ℕ)) =
        ∑ a ∈ (matchingBitSubset ell d).map Fin.valEmbedding, 2 ^ a :=
          (Finset.sum_map (matchingBitSubset ell d)
            Fin.valEmbedding (fun a : ℕ => 2 ^ a)).symm
    _ = ∑ a ∈ d.bitIndices.toFinset, 2 ^ a := by
      rw [matchingBitSubset_map_val ell d hd]
    _ = (d.bitIndices.map (fun a => 2 ^ a)).sum :=
      List.sum_toFinset (fun a : ℕ => 2 ^ a) Nat.bitIndices_nodup
    _ = d := Nat.sum_map_two_pow_bitIndices d

private noncomputable def matchingBivariateEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) F :=
  fun de ab =>
    (matchingPolynomial p (P de.1)).eval (p ab.2) *
      (matchingPolynomial q (Q de.2)).eval (q ab.1)

private theorem matchingBivariateEvaluationMatrix_eq_kronecker
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    matchingBivariateEvaluationMatrix p q P Q =
      ((matchingPolynomialEvaluationMatrix p P)ᵀ ⊗ₖ
        (matchingPolynomialEvaluationMatrix q Q)ᵀ).submatrix
          id (Equiv.prodComm (Fin m) (Fin m)) := by
  ext ⟨d, e⟩ ⟨a, b⟩
  rfl

private theorem matchingBivariateEvaluationMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p q : Fin m → F)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (P Q : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ))
    (hQ : ∀ e : Fin m, matchingBinaryDegree (Q e) = (e : ℕ)) :
    (matchingBivariateEvaluationMatrix p q P Q).det ≠ 0 := by
  have hpdet := matchingPolynomialEvaluationMatrix_det_ne_zero p hp P hP
  have hqdet := matchingPolynomialEvaluationMatrix_det_ne_zero q hq Q hQ
  rw [matchingBivariateEvaluationMatrix_eq_kronecker,
    Matrix.det_permute', Matrix.det_kronecker]
  rcases Int.units_eq_one_or
    (Equiv.Perm.sign (Equiv.prodComm (Fin m) (Fin m))) with hsign | hsign
  · simp only [hsign, Units.val_one, Int.cast_one, Matrix.det_transpose, Fintype.card_fin,
    one_mul, ne_eq,
      mul_eq_zero, pow_eq_zero_iff', hpdet, false_and, hqdet, or_self, not_false_eq_true]
  · simp only [hsign, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Matrix.det_transpose, Fintype.card_fin, neg_mul, one_mul, ne_eq, neg_eq_zero, mul_eq_zero,
        pow_eq_zero_iff', hpdet,
      false_and, hqdet, or_self, not_false_eq_true]

private def matchingJacobianWeight (m r s : ℕ) : ℕ :=
  (m - 1 - r - s).factorial *
    (m - 1 - r).descFactorial s *
      (m - 1 - s).descFactorial r

private theorem matchingJacobianWeight_pos (m r s : ℕ) (h : r + s < m) :
    0 < matchingJacobianWeight m r s := by
  have hs : s ≤ m - 1 - r := by omega
  have hr : r ≤ m - 1 - s := by omega
  unfold matchingJacobianWeight
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.factorial_pos _)
      (Nat.descFactorial_pos.mpr hs))
    (Nat.descFactorial_pos.mpr hr)

private noncomputable def matchingWeightedBivariateEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) F :=
  fun de ab =>
    (matchingJacobianWeight m (P de.1).card (Q de.2).card : F) *
      matchingBivariateEvaluationMatrix p q P Q de ab

private theorem matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    matchingWeightedBivariateEvaluationMatrix p q P Q =
      Matrix.diagonal
        (fun de : Fin m × Fin m =>
          (matchingJacobianWeight m (P de.1).card (Q de.2).card : F)) *
        matchingBivariateEvaluationMatrix p q P Q := by
  ext de ab
  rw [Matrix.diagonal_mul]
  rfl

private theorem matchingWeightedBivariateEvaluationMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p q : Fin m → F)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (P Q : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ))
    (hQ : ∀ e : Fin m, matchingBinaryDegree (Q e) = (e : ℕ))
    (hroom : 2 * ell < m) :
    (matchingWeightedBivariateEvaluationMatrix p q P Q).det ≠ 0 := by
  classical
  rw [matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul,
    Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro de _
    have hcardP : (P de.1).card ≤ ell := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (P de.1)
    have hcardQ : (Q de.2).card ≤ ell := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (Q de.2)
    have hfit : (P de.1).card + (Q de.2).card < m := by omega
    exact Nat.cast_ne_zero.mpr
      ((matchingJacobianWeight_pos m (P de.1).card (Q de.2).card hfit).ne')
  · exact matchingBivariateEvaluationMatrix_det_ne_zero
      p q hp hq P Q hP hQ

private theorem matchingWeightedBivariateBitEvaluationMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p q : Fin m → F)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    (matchingWeightedBivariateEvaluationMatrix p q
      (fun d : Fin m => matchingBitSubset ell (d : ℕ))
      (fun e : Fin m => matchingBitSubset ell (e : ℕ))).det ≠ 0 := by
  apply matchingWeightedBivariateEvaluationMatrix_det_ne_zero
    p q hp hq _ _ _ _ hroom
  · intro d
    exact matchingBinaryDegree_bitSubset ell d (lt_of_lt_of_le d.isLt hm)
  · intro e
    exact matchingBinaryDegree_bitSubset ell e (lt_of_lt_of_le e.isLt hm)

private noncomputable def matchingBitCoefficientSet (ell m : ℕ)
    (de : Fin m × Fin m) : Finset (Fin ell ⊕ Fin ell) := by
  classical
  exact Finset.univ.filter fun y =>
    match y with
    | .inl u => u ∉ matchingBitSubset ell (de.1 : ℕ)
    | .inr v => v ∉ matchingBitSubset ell (de.2 : ℕ)

@[simp] private theorem matchingBitCoefficientSet_mem_inl (ell m : ℕ)
    (de : Fin m × Fin m) (u : Fin ell) :
    Sum.inl u ∈ matchingBitCoefficientSet ell m de ↔
      u ∉ matchingBitSubset ell (de.1 : ℕ) := by
  classical
  simp only [matchingBitCoefficientSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] private theorem matchingBitCoefficientSet_mem_inr (ell m : ℕ)
    (de : Fin m × Fin m) (v : Fin ell) :
    Sum.inr v ∈ matchingBitCoefficientSet ell m de ↔
      v ∉ matchingBitSubset ell (de.2 : ℕ) := by
  classical
  simp only [matchingBitCoefficientSet, Finset.mem_filter, Finset.mem_univ, true_and]

private noncomputable def matchingPermanentJacobian
    {ell m : ℕ} (p q : Fin m → ℂ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  evaluatedJacobianMinor
    (fun de : Fin m × Fin m =>
      coefficientPolynomial
        (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
        (matchingSquarefreeMonomial
          (matchingBitCoefficientSet ell m de)))
    (fun ab : Fin m × Fin m =>
      matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)

private theorem matchingPermanentJacobian_apply
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m) :
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : Equiv.Perm (Fin ((ell + ell) + m)),
        if matchingPermutationExponent
          (matchingDiagonalEmbedding ell m) σ =
              matchingSquarefreeMonomial
                (matchingBitCoefficientSet ell m de) ∧
          σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
            (matchingExternalEntry ell m ab.1 ab.2).1.2 then
          ∏ i : {i : Fin ((ell + ell) + m) //
            i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
            MvPolynomial.eval (matchingPermanentSpecialization p q)
              (matchingPermutationOutsideFactor
                (matchingDiagonalEmbedding ell m) σ i.1)
        else 0 := by
  classical
  unfold matchingPermanentJacobian evaluatedJacobianMinor
  exact matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
    (matchingDiagonalEmbedding ell m)
    (matchingSquarefreeMonomial
      (matchingBitCoefficientSet ell m de))
    (matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)

private theorem sum_sumEmbedding_left_weight
    {F α β γ : Type*} [CommSemiring F]
    [Fintype α] [Fintype β] [Fintype γ]
    (w : (α ↪ γ) → F) :
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inl.trans rho)) =
        ((Fintype.card γ - Fintype.card α).descFactorial
          (Fintype.card β) : F) *
          ∑ rho : (α ↪ γ), w rho := by
  classical
  calc
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inl.trans rho)) =
        ∑ z : (Σ rho : (α ↪ γ), β ↪ ↥(Set.range rho)ᶜ), w z.1 := by
          refine Fintype.sum_equiv
            (Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted
              (α := α) (β := β) (γ := γ)) _ _ ?_
          intro rho
          rfl
    _ = ∑ rho : (α ↪ γ),
          ∑ _eta : (β ↪ ↥(Set.range rho)ᶜ), w rho :=
        Fintype.sum_sigma _
    _ = ∑ rho : (α ↪ γ),
          ((Fintype.card γ - Fintype.card α).descFactorial
            (Fintype.card β) : F) * w rho := by
        apply Finset.sum_congr rfl
        intro rho _
        have hcard :
            Fintype.card (↥(Set.range rho)ᶜ) =
              Fintype.card γ - Fintype.card α := by
          rw [Fintype.card_compl_set, Fintype.card_range]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, hcard,
          nsmul_eq_mul]
    _ = ((Fintype.card γ - Fintype.card α).descFactorial
          (Fintype.card β) : F) *
          ∑ rho : (α ↪ γ), w rho := by
        rw [Finset.mul_sum]

private theorem sum_sumEmbedding_right_weight
    {F α β γ : Type*} [CommSemiring F]
    [Fintype α] [Fintype β] [Fintype γ]
    (w : (β ↪ γ) → F) :
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inr.trans rho)) =
        ((Fintype.card γ - Fintype.card β).descFactorial
          (Fintype.card α) : F) *
          ∑ rho : (β ↪ γ), w rho := by
  classical
  calc
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inr.trans rho)) =
        ∑ rho : (β ⊕ α ↪ γ),
          w (Function.Embedding.inl.trans rho) := by
            refine Fintype.sum_equiv
              (Equiv.embeddingCongr (Equiv.sumComm α β)
                (Equiv.refl γ)) _ _ ?_
            intro rho
            apply congrArg w
            apply Function.Embedding.ext
            intro b
            rfl
    _ = ((Fintype.card γ - Fintype.card β).descFactorial
          (Fintype.card α) : F) *
          ∑ rho : (β ↪ γ), w rho :=
        sum_sumEmbedding_left_weight w

private theorem matching_card_omitted_external {m : ℕ} (b : Fin m) :
    Fintype.card {j : Fin m // j ≠ b} = m - 1 := by
  classical
  simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

private theorem matching_leftWeightedAvoidingInjectionSum
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (p : Fin m → F) (P Q : Finset (Fin ell)) (b : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ b}),
      ∏ u : ↥P,
        p (rho (Sum.inl u)).1 ^ (2 ^ (u.1 : ℕ))) =
      ((m - 1 - P.card).descFactorial Q.card : F) *
        matchingAvoidingInjectionSum p P b := by
  classical
  let w : (↥P ↪ {j : Fin m // j ≠ b}) → F :=
    fun rho => ∏ u : ↥P, p (rho u).1 ^ (2 ^ (u.1 : ℕ))
  have h := sum_sumEmbedding_left_weight
    (β := ↥Q) (γ := {j : Fin m // j ≠ b}) w
  simpa [w, matchingAvoidingInjectionSum,
    matching_card_omitted_external] using h

private theorem matching_rightWeightedAvoidingInjectionSum
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (q : Fin m → F) (P Q : Finset (Fin ell)) (a : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ a}),
      ∏ v : ↥Q,
        q (rho (Sum.inr v)).1 ^ (2 ^ (v.1 : ℕ))) =
      ((m - 1 - Q.card).descFactorial P.card : F) *
        matchingAvoidingInjectionSum q Q a := by
  classical
  let w : (↥Q ↪ {j : Fin m // j ≠ a}) → F :=
    fun rho => ∏ v : ↥Q, q (rho v).1 ^ (2 ^ (v.1 : ℕ))
  have h := sum_sumEmbedding_right_weight
    (α := ↥P) (γ := {j : Fin m // j ≠ a}) w
  simpa [w, matchingAvoidingInjectionSum,
    matching_card_omitted_external] using h

private noncomputable def matchingCrossWeight
    {F : Type*} [CommMonoid F] {ell m : ℕ}
    (p q : Fin m → F) (P Q : Finset (Fin ell)) (a b : Fin m)
    (σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b}) : F :=
  (∏ u : ↥P,
    p ((matchingCrossRows σ) (.inl u)).1 ^ (2 ^ (u.1 : ℕ))) *
  (∏ v : ↥Q,
    q ((matchingCrossCols σ) (.inr v)).1 ^ (2 ^ (v.1 : ℕ)))

private theorem matchingCrossWeight_sum
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F) (P Q : Finset (Fin ell)) (a b : Fin m) :
    (∑ σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b},
        matchingCrossWeight p q P Q a b σ) =
      (matchingJacobianWeight m P.card Q.card : F) *
        ((matchingPolynomial p P).eval (p b) *
          (matchingPolynomial q Q).eval (q a)) := by
  classical
  let wp : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}) → F :=
    fun rho => ∏ u : ↥P,
      p (rho (.inl u)).1 ^ (2 ^ (u.1 : ℕ))
  let wq : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}) → F :=
    fun theta => ∏ v : ↥Q,
      q (theta (.inr v)).1 ^ (2 ^ (v.1 : ℕ))
  have hcard :
      Fintype.card {j : Fin m // j ≠ a} =
        Fintype.card {j : Fin m // j ≠ b} :=
    (matching_card_omitted_external a).trans
      (matching_card_omitted_external b).symm
  have hfact :
      (Fintype.card {j : Fin m // j ≠ a} -
        Fintype.card (↥P ⊕ ↥Q)).factorial =
          (m - 1 - P.card - Q.card).factorial := by
    rw [matching_card_omitted_external]
    have hsum : Fintype.card (↥P ⊕ ↥Q) = P.card + Q.card := by
      simp only [Fintype.card_sum, Fintype.card_coe]
    rw [hsum]
    congr 1
    omega
  have hsplit :
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
        ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
          wp rho * wq theta) =
        (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) := by
    calc
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
        ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
          wp rho * wq theta) =
        ∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
          wp rho *
            (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
              wq theta) := by
            apply Finset.sum_congr rfl
            intro rho _
            rw [Finset.mul_sum]
      _ = (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wq theta) := by
            rw [Finset.sum_mul]
  have hleft :
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) =
        ((m - 1 - P.card).descFactorial Q.card : F) *
          (matchingPolynomial p P).eval (p b) := by
    calc
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) =
          ((m - 1 - P.card).descFactorial Q.card : F) *
            matchingAvoidingInjectionSum p P b := by
              exact matching_leftWeightedAvoidingInjectionSum p P Q b
      _ = ((m - 1 - P.card).descFactorial Q.card : F) *
          (matchingPolynomial p P).eval (p b) := by
            rw [matchingPolynomial_eval]
  have hright :
      (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) =
        ((m - 1 - Q.card).descFactorial P.card : F) *
          (matchingPolynomial q Q).eval (q a) := by
    calc
      (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) =
          ((m - 1 - Q.card).descFactorial P.card : F) *
            matchingAvoidingInjectionSum q Q a := by
              exact matching_rightWeightedAvoidingInjectionSum q P Q a
      _ = ((m - 1 - Q.card).descFactorial P.card : F) *
          (matchingPolynomial q Q).eval (q a) := by
            rw [matchingPolynomial_eval]
  have hcross := sum_matchingCrossPermutation_rows_cols
    (F := F) (T := ↥P ⊕ ↥Q)
    (A := {j : Fin m // j ≠ a})
    (B := {j : Fin m // j ≠ b}) hcard
      (fun rho theta => wp rho * wq theta)
  calc
    (∑ σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b},
        matchingCrossWeight p q P Q a b σ) =
      ((Fintype.card {j : Fin m // j ≠ a} -
        Fintype.card (↥P ⊕ ↥Q)).factorial : F) *
        (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
          ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wp rho * wq theta) := by
              simpa only [matchingCrossWeight, wp, wq] using hcross
    _ = ((m - 1 - P.card - Q.card).factorial : F) *
        ((∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wq theta)) := by
              rw [hfact, hsplit]
    _ = (matchingJacobianWeight m P.card Q.card : F) *
        ((matchingPolynomial p P).eval (p b) *
          (matchingPolynomial q Q).eval (q a)) := by
            rw [hleft, hright]
            simp only [matchingJacobianWeight, Nat.cast_mul]
            ring

private theorem matchingWeightedCrossBitPermutation_sum
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F) (de ab : Fin m × Fin m) :
    (∑ σ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2},
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2 σ) =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) de ab := by
  exact matchingCrossWeight_sum p q
    (matchingBitSubset ell (de.1 : ℕ))
    (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2

@[simp] private theorem matchingVariableEquiv_symm_marked
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) (y : Y) :
    (matchingVariableEquiv d).symm (d y) = .inl y := by
  apply (matchingVariableEquiv d).injective
  simp only [Equiv.apply_symm_apply, matchingVariableEquiv_inl]

private theorem matchingPermutationExponent_apply
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (y : Y) :
    matchingPermutationExponent d σ y =
      if σ (d y).1 = (d y).2 then 1 else 0 := by
  classical
  have hterm (i : Fin n) :
      (match (matchingVariableEquiv d).symm (i, σ i) with
        | .inl y' => Finsupp.single y' 1
        | .inr _ => (0 : Y →₀ ℕ)) y =
          if (i, σ i) = d y then 1 else 0 := by
    cases h : (matchingVariableEquiv d).symm (i, σ i) with
    | inl y' =>
        have hpair : (i, σ i) = d y' := by
          have heq := congrArg (matchingVariableEquiv d) h
          simpa only [Equiv.apply_symm_apply, matchingVariableEquiv_inl] using heq
        simp only [Finsupp.single_apply, hpair, d.injective.eq_iff]
    | inr z =>
        have hne : (i, σ i) ≠ d y := by
          intro heq
          have himage := congrArg (matchingVariableEquiv d).symm heq
          rw [h, matchingVariableEquiv_symm_marked] at himage
          cases himage
        simp only [Finsupp.coe_zero, Pi.zero_apply, hne, ↓reduceIte]
  calc
    matchingPermutationExponent d σ y =
        ∑ i : Fin n, if (i, σ i) = d y then 1 else 0 := by
          unfold matchingPermutationExponent
          rw [Finsupp.finsetSum_apply]
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = if σ (d y).1 = (d y).2 then 1 else 0 := by
      by_cases hfix : σ (d y).1 = (d y).2
      · have hi (i : Fin n) :
            (i, σ i) = d y ↔ i = (d y).1 := by
          constructor
          · exact congrArg Prod.fst
          · intro heq
            subst i
            exact Prod.ext rfl hfix
        simp_rw [hi]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hfix]
      · have hi (i : Fin n) : (i, σ i) ≠ d y := by
          intro heq
          have hrow := congrArg Prod.fst heq
          have hcol := congrArg Prod.snd heq
          exact hfix (hrow ▸ hcol)
        simp only [hi, ↓reduceIte, Finset.sum_const_zero, hfix]

private theorem matchingPermutationExponent_eq_squarefree_iff
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (S : Finset Y) :
    matchingPermutationExponent d σ = matchingSquarefreeMonomial S ↔
      ∀ y : Y, σ (d y).1 = (d y).2 ↔ y ∈ S := by
  classical
  constructor
  · intro h y
    have hy := DFunLike.congr_fun h y
    rw [matchingPermutationExponent_apply,
      matchingSquarefreeMonomial_apply] at hy
    by_cases hfix : σ (d y).1 = (d y).2 <;>
      by_cases hmem : y ∈ S <;> simp_all
  · intro h
    apply Finsupp.ext
    intro y
    rw [matchingPermutationExponent_apply,
      matchingSquarefreeMonomial_apply]
    by_cases hy : y ∈ S <;> simp [hy, (h y).2,
      mt (h y).1]

private noncomputable def matchingRestrictComplement
    {α β D : Type*} (e : α ≃ β)
    (r : D ↪ α) (c : D ↪ β)
    (h : ∀ d : D, e (r d) = c d) :
    {x : α // x ∉ Set.range r} ≃
      {y : β // y ∉ Set.range c} := by
  classical
  apply e.subtypeEquiv
  intro x
  apply not_congr
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, (h d).symm⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    apply e.injective
    exact (h d).trans hd

private noncomputable def matchingDeletedIndexEmbedding
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) : (↥S ⊕ Unit) ↪ I where
  toFun
    | .inl y => e (.inl y.1)
    | .inr _ => e (.inr a)
  inj' := by
    rintro (x | x) (y | y) h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective (e.injective h)
    · have hbad := e.injective h
      cases hbad
    · have hbad := e.injective h
      cases hbad
    · exact congrArg Sum.inr (Subsingleton.elim x y)

private noncomputable def matchingRemainingIndexEmbedding
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) ↪ I where
  toFun
    | .inl y => e (.inl y.1)
    | .inr j => e (.inr j.1)
  inj' := by
    rintro (x | x) (y | y) h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective (e.injective h)
    · have hbad := e.injective h
      cases hbad
    · have hbad := e.injective h
      cases hbad
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact Sum.inr_injective (e.injective h)

private theorem matchingRemainingIndexEmbedding_range
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    Set.range (matchingRemainingIndexEmbedding e S a) =
      (Set.range (matchingDeletedIndexEmbedding e S a))ᶜ := by
  classical
  ext i
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hxy :
        matchingRemainingIndexEmbedding e S a x =
          matchingDeletedIndexEmbedding e S a y :=
      hx.trans hy.symm
    rcases x with x | x <;> rcases y with y | y
    · have h := e.injective hxy
      have heq : x.1 = y.1 := Sum.inl_injective h
      exact x.property (heq ▸ y.property)
    · cases e.injective hxy
    · cases e.injective hxy
    · have h := e.injective hxy
      exact x.property (Sum.inr_injective h)
  · intro hi
    cases h : e.symm i with
    | inl y =>
        have hyi : e (.inl y) = i := by
          simpa only [h] using e.apply_symm_apply i
        have hy : y ∉ S := by
          intro hmem
          exact hi ⟨.inl ⟨y, hmem⟩, hyi⟩
        exact ⟨.inl ⟨y, hy⟩, hyi⟩
    | inr j =>
        have hji : e (.inr j) = i := by
          simpa only [h] using e.apply_symm_apply i
        have hj : j ≠ a := by
          intro heq
          subst j
          exact hi ⟨.inr (), hji⟩
        exact ⟨.inr ⟨j, hj⟩, hji⟩

private noncomputable def matchingRemainingIndexEquiv
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) ≃
      {i : I // i ∉ Set.range (matchingDeletedIndexEmbedding e S a)} :=
  (Equiv.ofInjective
    (matchingRemainingIndexEmbedding e S a)
    (matchingRemainingIndexEmbedding e S a).injective).trans
      (Equiv.setCongr (matchingRemainingIndexEmbedding_range e S a))

private noncomputable def matchingReducedEquiv
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b)) :
    ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a}) ≃
        ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
          {j : Fin m // j ≠ b}) := by
  let e := matchingBlockIndexEquiv ell m
  let r := matchingDeletedIndexEmbedding e S a
  let c := matchingDeletedIndexEmbedding e S b
  have hdel : ∀ d : ↥S ⊕ Unit, σ (r d) = c d := by
    rintro (y | y)
    · exact hfix y.1 y.property
    · exact hab
  exact
    (matchingRemainingIndexEquiv e S a).trans
      ((matchingRestrictComplement σ r c hdel).trans
        (matchingRemainingIndexEquiv e S b).symm)

private theorem matchingReducedEquiv_eq_iff
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b))
    (x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a})
    (y : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ b}) :
    matchingReducedEquiv S a b σ hfix hab x = y ↔
      σ (matchingRemainingIndexEmbedding
        (matchingBlockIndexEquiv ell m) S a x) =
          matchingRemainingIndexEmbedding
            (matchingBlockIndexEquiv ell m) S b y := by
  unfold matchingReducedEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  rfl

private noncomputable def matchingBitSurvivorEquiv
    (ell m : ℕ) (de : Fin m × Fin m) :
    (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ≃
        {y : Fin ell ⊕ Fin ell //
          y ∉ matchingBitCoefficientSet ell m de} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro (u | v)
    · exact ⟨.inl u.1, by
        simpa only [matchingBitCoefficientSet_mem_inl,
          not_not] using u.property⟩
    · exact ⟨.inr v.1, by
        simpa only [matchingBitCoefficientSet_mem_inr,
          not_not] using v.property⟩
  · intro y
    cases hy : y.1 with
    | inl u =>
        refine .inl ⟨u, ?_⟩
        have hnot : Sum.inl u ∉ matchingBitCoefficientSet ell m de := by
          simpa only [matchingBitCoefficientSet_mem_inl, Decidable.not_not, hy] using y.property
        simpa only [matchingBitCoefficientSet_mem_inl, not_not]
          using hnot
    | inr v =>
        refine .inr ⟨v, ?_⟩
        have hnot : Sum.inr v ∉ matchingBitCoefficientSet ell m de := by
          simpa only [matchingBitCoefficientSet_mem_inr, Decidable.not_not, hy] using y.property
        simpa only [matchingBitCoefficientSet_mem_inr, not_not]
          using hnot
  · rintro (u | v) <;> rfl
  · rintro ⟨y, hy⟩
    cases y <;> rfl

private abbrev MatchingBitSelectedPermutation
    (ell m : ℕ) (de ab : Fin m × Fin m) :=
  {σ : Equiv.Perm (Fin ((ell + ell) + m)) //
    matchingPermutationExponent (matchingDiagonalEmbedding ell m) σ =
        matchingSquarefreeMonomial (matchingBitCoefficientSet ell m de) ∧
      σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
        (matchingExternalEntry ell m ab.1 ab.2).1.2}

private theorem matchingBitSelectedPermutation_fixed
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab)
    (y : Fin ell ⊕ Fin ell)
    (hy : y ∈ matchingBitCoefficientSet ell m de) :
    σ.1 (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y) := by
  have h :=
    (matchingPermutationExponent_eq_squarefree_iff
      (matchingDiagonalEmbedding ell m) σ.1
      (matchingBitCoefficientSet ell m de)).mp σ.property.1 y
  exact h.mpr hy

private theorem matchingBitSelectedPermutation_external
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab) :
    σ.1 (matchingBlockIndexEquiv ell m (.inr ab.1)) =
      matchingBlockIndexEquiv ell m (.inr ab.2) :=
  σ.property.2

private noncomputable def matchingBitReducedEquiv
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab) :
    ((↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.1}) ≃
      ((↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
          {j : Fin m // j ≠ ab.2}) :=
  (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
    (Equiv.refl _)).trans
      ((matchingReducedEquiv
        (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1
        (matchingBitSelectedPermutation_fixed σ)
        (matchingBitSelectedPermutation_external σ)).trans
          (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
            (Equiv.refl _)))

private noncomputable def matchingDeletedRemainingEquiv
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ((↥S ⊕ Unit) ⊕
      ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a})) ≃ I := by
  classical
  exact
    (Equiv.sumCongr
      (Equiv.ofInjective (matchingDeletedIndexEmbedding e S a)
        (matchingDeletedIndexEmbedding e S a).injective)
      (matchingRemainingIndexEquiv e S a)).trans
        (Equiv.Set.sumCompl
          (Set.range (matchingDeletedIndexEmbedding e S a)))

@[simp] private theorem matchingDeletedRemainingEquiv_inl
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) (x : ↥S ⊕ Unit) :
    matchingDeletedRemainingEquiv e S a (.inl x) =
      matchingDeletedIndexEmbedding e S a x := by
  rfl

@[simp] private theorem matchingDeletedRemainingEquiv_inr
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E)
    (x : {y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) :
    matchingDeletedRemainingEquiv e S a (.inr x) =
      matchingRemainingIndexEmbedding e S a x := by
  rfl

private noncomputable def matchingExtendReducedEquiv
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    Equiv.Perm (Fin ((ell + ell) + m)) :=
  (matchingDeletedRemainingEquiv
    (matchingBlockIndexEquiv ell m) S a).symm.trans
      ((Equiv.sumCongr
        (Equiv.refl (↥S ⊕ Unit)) τ).trans
          (matchingDeletedRemainingEquiv
            (matchingBlockIndexEquiv ell m) S b))

private theorem matchingExtendReducedEquiv_deleted
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (x : ↥S ⊕ Unit) :
    matchingExtendReducedEquiv S a b τ
        (matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingDeletedIndexEmbedding
        (matchingBlockIndexEquiv ell m) S b x := by
  calc
    matchingExtendReducedEquiv S a b τ
        (matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingExtendReducedEquiv S a b τ
        (matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S a (.inl x)) := by
            rw [matchingDeletedRemainingEquiv_inl]
    _ = matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S b (.inl x) := by
            simp only [matchingExtendReducedEquiv, Equiv.trans_apply,
              Equiv.symm_apply_apply, Equiv.sumCongr_apply,
              Equiv.refl_apply, Sum.map_inl]
    _ = matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S b x :=
            matchingDeletedRemainingEquiv_inl _ _ _ _

private theorem matchingExtendReducedEquiv_remaining
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a}) :
    matchingExtendReducedEquiv S a b τ
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingRemainingIndexEmbedding
        (matchingBlockIndexEquiv ell m) S b (τ x) := by
  calc
    matchingExtendReducedEquiv S a b τ
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingExtendReducedEquiv S a b τ
        (matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S a (.inr x)) := by
            rw [matchingDeletedRemainingEquiv_inr]
    _ = matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S b (.inr (τ x)) := by
            simp only [matchingExtendReducedEquiv, Equiv.trans_apply,
              Equiv.symm_apply_apply, Equiv.sumCongr_apply,
              Sum.map_inr]
    _ = matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S b (τ x) :=
            matchingDeletedRemainingEquiv_inr _ _ _ _

private theorem matchingExtendReducedEquiv_fixed
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (y : Fin ell ⊕ Fin ell) (hy : y ∈ S) :
    matchingExtendReducedEquiv S a b τ
        (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y) :=
  matchingExtendReducedEquiv_deleted S a b τ
    (.inl ⟨y, hy⟩)

private theorem matchingExtendReducedEquiv_external
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    matchingExtendReducedEquiv S a b τ
        (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inr b) :=
  matchingExtendReducedEquiv_deleted S a b τ (.inr ())

private theorem matchingReducedEquiv_extend
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    matchingReducedEquiv S a b
      (matchingExtendReducedEquiv S a b τ)
      (matchingExtendReducedEquiv_fixed S a b τ)
      (matchingExtendReducedEquiv_external S a b τ) = τ := by
  apply Equiv.ext
  intro x
  apply (matchingReducedEquiv_eq_iff S a b
    (matchingExtendReducedEquiv S a b τ)
    (matchingExtendReducedEquiv_fixed S a b τ)
    (matchingExtendReducedEquiv_external S a b τ)
    x (τ x)).2
  exact matchingExtendReducedEquiv_remaining S a b τ x

private theorem matchingExtendReducedEquiv_reduced
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b)) :
    matchingExtendReducedEquiv S a b
      (matchingReducedEquiv S a b σ hfix hab) = σ := by
  apply Equiv.ext
  intro i
  obtain ⟨x, rfl⟩ := (matchingBlockIndexEquiv ell m).surjective i
  cases x with
  | inl y =>
      by_cases hy : y ∈ S
      · rw [matchingExtendReducedEquiv_fixed S a b _ y hy,
          hfix y hy]
      · let x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
            {j : Fin m // j ≠ a} := .inl ⟨y, hy⟩
        have hext := matchingExtendReducedEquiv_remaining
          S a b (matchingReducedEquiv S a b σ hfix hab) x
        have hred :=
          (matchingReducedEquiv_eq_iff S a b σ hfix hab x
            (matchingReducedEquiv S a b σ hfix hab x)).mp rfl
        exact hext.trans hred.symm
  | inr j =>
      by_cases hj : j = a
      · subst j
        rw [matchingExtendReducedEquiv_external S a b _, hab]
      · let x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
            {j : Fin m // j ≠ a} := .inr ⟨j, hj⟩
        have hext := matchingExtendReducedEquiv_remaining
          S a b (matchingReducedEquiv S a b σ hfix hab) x
        have hred :=
          (matchingReducedEquiv_eq_iff S a b σ hfix hab x
            (matchingReducedEquiv S a b σ hfix hab x)).mp rfl
        exact hext.trans hred.symm

private abbrev MatchingBitCrossSelectedPermutation
    (ell m : ℕ) (de ab : Fin m × Fin m) :=
  {σ : MatchingBitSelectedPermutation ell m de ab //
    ∀ y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de},
      ∃ j : Fin m,
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
          matchingBlockIndexEquiv ell m (.inr j)}

private theorem matchingBitCrossSelectedPermutation_external_ne
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de})
    (j : Fin m)
    (himage :
      σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
        matchingBlockIndexEquiv ell m (.inr j)) :
    j ≠ ab.2 := by
  intro hj
  subst j
  have hsame :
      σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
        σ.1.1 (matchingBlockIndexEquiv ell m (.inr ab.1)) :=
    himage.trans (matchingBitSelectedPermutation_external σ.1).symm
  have hbad :=
    (matchingBlockIndexEquiv ell m).injective
      (σ.1.1.injective hsame)
  cases hbad

private noncomputable def matchingBitCrossSelectedToCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2} := by
  refine ⟨matchingBitReducedEquiv σ.1, ?_⟩
  intro t
  let y := matchingBitSurvivorEquiv ell m de t
  obtain ⟨j, hj⟩ := σ.property y
  have hne := matchingBitCrossSelectedPermutation_external_ne σ y j hj
  refine ⟨⟨j, hne⟩, ?_⟩
  have hred :=
    (matchingReducedEquiv_eq_iff
      (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
      (matchingBitSelectedPermutation_fixed σ.1)
      (matchingBitSelectedPermutation_external σ.1)
      (.inl y) (.inr ⟨j, hne⟩)).2 hj
  unfold matchingBitReducedEquiv
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [hred]
  rfl

private noncomputable def matchingBitUnreduceCrossEquiv
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    ({y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de} ⊕
        {j : Fin m // j ≠ ab.1}) ≃
      ({y : Fin ell ⊕ Fin ell //
        y ∉ matchingBitCoefficientSet ell m de} ⊕
          {j : Fin m // j ≠ ab.2}) :=
  (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
    (Equiv.refl _)).trans
      (τ.1.trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
          (Equiv.refl _)))

private theorem matchingBitUnreduceCrossEquiv_internal
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2})
    (y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de}) :
    ∃ j : {j : Fin m // j ≠ ab.2},
      matchingBitUnreduceCrossEquiv τ (.inl y) = .inr j := by
  obtain ⟨j, hj⟩ :=
    τ.property ((matchingBitSurvivorEquiv ell m de).symm y)
  refine ⟨j, ?_⟩
  unfold matchingBitUnreduceCrossEquiv
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [hj]
  rfl

private noncomputable def matchingBitCrossToSelected
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    MatchingBitCrossSelectedPermutation ell m de ab := by
  let S := matchingBitCoefficientSet ell m de
  let r := matchingBitUnreduceCrossEquiv τ
  let σ := matchingExtendReducedEquiv S ab.1 ab.2 r
  have hfixed :
      matchingPermutationExponent (matchingDiagonalEmbedding ell m) σ =
        matchingSquarefreeMonomial S := by
    apply
      (matchingPermutationExponent_eq_squarefree_iff
        (matchingDiagonalEmbedding ell m) σ S).2
    intro y
    constructor
    · intro hfix
      by_contra hy
      let yy : {y : Fin ell ⊕ Fin ell // y ∉ S} := ⟨y, hy⟩
      obtain ⟨j, hj⟩ := matchingBitUnreduceCrossEquiv_internal τ yy
      have hmove := matchingExtendReducedEquiv_remaining
        S ab.1 ab.2 r (.inl yy)
      rw [hj] at hmove
      have hbad :
          (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) =
            .inr j.1 := by
        apply (matchingBlockIndexEquiv ell m).injective
        exact hfix.symm.trans hmove
      cases hbad
    · intro hy
      exact matchingExtendReducedEquiv_fixed
        S ab.1 ab.2 r y hy
  have hexternal :
      σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
        (matchingExternalEntry ell m ab.1 ab.2).1.2 :=
    matchingExtendReducedEquiv_external S ab.1 ab.2 r
  refine ⟨⟨σ, hfixed, hexternal⟩, ?_⟩
  intro y
  obtain ⟨j, hj⟩ := matchingBitUnreduceCrossEquiv_internal τ y
  refine ⟨j.1, ?_⟩
  have hmove := matchingExtendReducedEquiv_remaining
    S ab.1 ab.2 r (.inl y)
  rw [hj] at hmove
  exact hmove

private theorem matchingBitUnreduceCrossEquiv_toCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    matchingBitUnreduceCrossEquiv
      (matchingBitCrossSelectedToCross σ) =
        matchingReducedEquiv
          (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
          (matchingBitSelectedPermutation_fixed σ.1)
          (matchingBitSelectedPermutation_external σ.1) := by
  apply Equiv.ext
  intro x
  unfold matchingBitUnreduceCrossEquiv
  change
    ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
      (Equiv.refl _)).trans
      ((matchingBitReducedEquiv σ.1).trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
          (Equiv.refl _)))) x = _
  unfold matchingBitReducedEquiv
  simp only [ne_eq, Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl,
    Sum.map_map,
    Equiv.self_comp_symm, CompTriple.comp_eq, Sum.map_id_id, id_eq]

private theorem matchingBitCrossSelectedToCross_toSelected
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    matchingBitCrossSelectedToCross
      (matchingBitCrossToSelected τ) = τ := by
  apply Subtype.ext
  change
    (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
      (Equiv.refl _)).trans
      ((matchingReducedEquiv
        (matchingBitCoefficientSet ell m de) ab.1 ab.2
        (matchingExtendReducedEquiv
          (matchingBitCoefficientSet ell m de) ab.1 ab.2
          (matchingBitUnreduceCrossEquiv τ)) _ _).trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
          (Equiv.refl _))) = τ.1
  rw [matchingReducedEquiv_extend]
  apply Equiv.ext
  intro x
  unfold matchingBitUnreduceCrossEquiv
  simp only [ne_eq, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_map,
    Equiv.symm_comp_self,
    CompTriple.comp_eq, Sum.map_id_id, id_eq]

private theorem matchingBitCrossToSelected_toCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    matchingBitCrossToSelected
      (matchingBitCrossSelectedToCross σ) = σ := by
  apply Subtype.ext
  apply Subtype.ext
  change
    matchingExtendReducedEquiv
      (matchingBitCoefficientSet ell m de) ab.1 ab.2
      (matchingBitUnreduceCrossEquiv
        (matchingBitCrossSelectedToCross σ)) = σ.1.1
  rw [matchingBitUnreduceCrossEquiv_toCross]
  exact matchingExtendReducedEquiv_reduced
    (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
    (matchingBitSelectedPermutation_fixed σ.1)
    (matchingBitSelectedPermutation_external σ.1)

private noncomputable def matchingBitCrossSelectedEquiv
    (ell m : ℕ) (de ab : Fin m × Fin m) :
    MatchingBitCrossSelectedPermutation ell m de ab ≃
      MatchingCrossPermutation
        (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
          ↥(matchingBitSubset ell (de.2 : ℕ)))
        {j : Fin m // j ≠ ab.1}
        {j : Fin m // j ≠ ab.2} where
  toFun := matchingBitCrossSelectedToCross
  invFun := matchingBitCrossToSelected
  left_inv := matchingBitCrossToSelected_toCross
  right_inv := matchingBitCrossSelectedToCross_toSelected

private theorem matchingBitCrossSelected_factor_one_off_support
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m)
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (i : Fin ((ell + ell) + m))
    (hP : ∀ u : ↥(matchingBitSubset ell (de.1 : ℕ)),
      i ≠ matchingBlockIndexEquiv ell m (.inl (.inl u.1)))
    (hQ : ∀ v : ↥(matchingBitSubset ell (de.2 : ℕ)),
      i ≠ σ.1.1.symm
        (matchingBlockIndexEquiv ell m (.inl (.inr v.1)))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ.1.1 i) = 1 := by
  classical
  cases hi : (matchingBlockIndexEquiv ell m).symm i with
  | inl y =>
      have hi' : i = matchingBlockIndexEquiv ell m (.inl y) := by
        have h := congrArg (matchingBlockIndexEquiv ell m) hi
        simpa only [Equiv.apply_symm_apply] using h
      subst i
      cases y with
      | inl u =>
          by_cases hu : u ∈ matchingBitSubset ell (de.1 : ℕ)
          · exact False.elim (hP ⟨u, hu⟩ rfl)
          · have hmem :
                Sum.inl u ∈ matchingBitCoefficientSet ell m de :=
              (matchingBitCoefficientSet_mem_inl ell m de u).2 hu
            exact matchingPermutationOutsideFactor_fixed_diagonal_eval
              p q σ.1.1 (.inl u)
              (matchingBitSelectedPermutation_fixed σ.1 (.inl u) hmem)
      | inr v =>
          by_cases hv : v ∈ matchingBitSubset ell (de.2 : ℕ)
          · have hsurv :
                Sum.inr v ∉ matchingBitCoefficientSet ell m de := by
              simpa only [matchingBitCoefficientSet_mem_inr, not_not]
                using hv
            obtain ⟨j, hj⟩ := σ.property ⟨.inr v, hsurv⟩
            exact matchingPermutationOutsideFactor_right_external_eval
              p q σ.1.1 v j hj
          · have hmem :
                Sum.inr v ∈ matchingBitCoefficientSet ell m de :=
              (matchingBitCoefficientSet_mem_inr ell m de v).2 hv
            exact matchingPermutationOutsideFactor_fixed_diagonal_eval
              p q σ.1.1 (.inr v)
              (matchingBitSelectedPermutation_fixed σ.1 (.inr v) hmem)
  | inr a =>
      have hi' : i = matchingBlockIndexEquiv ell m (.inr a) := by
        have h := congrArg (matchingBlockIndexEquiv ell m) hi
        simpa only [Equiv.apply_symm_apply] using h
      subst i
      cases hj : (matchingBlockIndexEquiv ell m).symm
        (σ.1.1 (matchingBlockIndexEquiv ell m (.inr a))) with
      | inl y =>
          have hσ :
              σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                matchingBlockIndexEquiv ell m (.inl y) := by
            have h := congrArg (matchingBlockIndexEquiv ell m) hj
            simpa only [Equiv.apply_symm_apply] using h
          cases y with
          | inl u =>
              exact matchingPermutationOutsideFactor_external_left_eval
                p q σ.1.1 a u hσ
          | inr v =>
              by_cases hv : v ∈ matchingBitSubset ell (de.2 : ℕ)
              · have hpre := congrArg σ.1.1.symm hσ
                rw [σ.1.1.symm_apply_apply] at hpre
                exact False.elim (hQ ⟨v, hv⟩ hpre)
              · have hmem :
                    Sum.inr v ∈ matchingBitCoefficientSet ell m de :=
                  (matchingBitCoefficientSet_mem_inr ell m de v).2 hv
                have hfixed :=
                  matchingBitSelectedPermutation_fixed
                    σ.1 (.inr v) hmem
                have hsame :
                    σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                      σ.1.1
                        (matchingBlockIndexEquiv ell m
                          (.inl (.inr v))) :=
                  hσ.trans hfixed.symm
                have hbad :=
                  (matchingBlockIndexEquiv ell m).injective
                    (σ.1.1.injective hsame)
                cases hbad
      | inr b =>
          have hσ :
              σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                matchingBlockIndexEquiv ell m (.inr b) := by
            have h := congrArg (matchingBlockIndexEquiv ell m) hj
            simpa only [Equiv.apply_symm_apply] using h
          exact matchingPermutationOutsideFactor_external_external_eval
            p q σ.1.1 a b hσ

private theorem matchingBitCrossSelected_reduced_eq_iff
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (x : (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.1})
    (z : (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.2}) :
    (matchingBitCrossSelectedToCross σ).1 x = z ↔
      σ.1.1
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m)
          (matchingBitCoefficientSet ell m de) ab.1
          ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
            (Equiv.refl _)) x)) =
        matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m)
          (matchingBitCoefficientSet ell m de) ab.2
          ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
            (Equiv.refl _)) z) := by
  change matchingBitReducedEquiv σ.1 x = z ↔ _
  unfold matchingBitReducedEquiv
  simp only [Equiv.trans_apply]
  rw [← Equiv.eq_symm_apply]
  exact matchingReducedEquiv_eq_iff
    (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
    (matchingBitSelectedPermutation_fixed σ.1)
    (matchingBitSelectedPermutation_external σ.1) _ _

private theorem matchingBitCrossSelected_full_rows_spec
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    σ.1.1
        (matchingBlockIndexEquiv ell m
          (.inl (matchingBitSurvivorEquiv ell m de t).1)) =
      matchingBlockIndexEquiv ell m
        (.inr (matchingCrossRows
          (matchingBitCrossSelectedToCross σ) t).1) := by
  have h :=
    (matchingBitCrossSelected_reduced_eq_iff σ
      (.inl t)
      (.inr (matchingCrossRows
        (matchingBitCrossSelectedToCross σ) t))).mp
      (matchingCrossRows_spec
        (matchingBitCrossSelectedToCross σ) t)
  exact h

private theorem matchingBitCrossSelected_full_cols_spec
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    σ.1.1
        (matchingBlockIndexEquiv ell m
          (.inr (matchingCrossCols
            (matchingBitCrossSelectedToCross σ) t).1)) =
      matchingBlockIndexEquiv ell m
        (.inl (matchingBitSurvivorEquiv ell m de t).1) := by
  have hcross :
      (matchingBitCrossSelectedToCross σ).1
        (.inr (matchingCrossCols
          (matchingBitCrossSelectedToCross σ) t)) = .inl t := by
    exact ((matchingBitCrossSelectedToCross σ).1.symm_apply_eq.mp
      (matchingCrossCols_spec
        (matchingBitCrossSelectedToCross σ) t)).symm
  exact
    (matchingBitCrossSelected_reduced_eq_iff σ
      (.inr (matchingCrossCols
        (matchingBitCrossSelectedToCross σ) t)) (.inl t)).mp hcross

private noncomputable def matchingBitCrossSelectedSupportEmbedding
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ↪
        Fin ((ell + ell) + m) where
  toFun
    | .inl u =>
        matchingBlockIndexEquiv ell m (.inl (.inl u.1))
    | .inr v =>
        σ.1.1.symm
          (matchingBlockIndexEquiv ell m (.inl (.inr v.1)))
  inj' := by
    rintro (u | v) (u' | v') h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective
        (Sum.inl_injective
          ((matchingBlockIndexEquiv ell m).injective h))
    · have hact := congrArg σ.1.1 h
      rw [Equiv.apply_symm_apply] at hact
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u)).1)
        at hrow
      rw [hrow] at hact
      cases (matchingBlockIndexEquiv ell m).injective hact
    · have hact := congrArg σ.1.1 h.symm
      rw [Equiv.apply_symm_apply] at hact
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u')
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u'.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u')).1)
        at hrow
      rw [hrow] at hact
      cases (matchingBlockIndexEquiv ell m).injective hact
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact Sum.inr_injective
        (Sum.inl_injective
          ((matchingBlockIndexEquiv ell m).injective
            (σ.1.1.symm.injective h)))

private theorem matchingBitCrossSelectedSupportEmbedding_factor
    {ell m : ℕ} (p q : Fin m → ℂ)
    {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1
          (matchingBitCrossSelectedSupportEmbedding σ t)) =
      match t with
      | .inl u =>
          p ((matchingCrossRows
            (matchingBitCrossSelectedToCross σ) (.inl u)).1) ^
              (2 ^ (u.1 : ℕ))
      | .inr v =>
          q ((matchingCrossCols
            (matchingBitCrossSelectedToCross σ) (.inr v)).1) ^
              (2 ^ (v.1 : ℕ)) := by
  cases t with
  | inl u =>
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u)).1)
        at hrow
      exact matchingPermutationOutsideFactor_left_external_eval
        p q σ.1.1 u.1
        (matchingCrossRows
          (matchingBitCrossSelectedToCross σ) (.inl u)).1 hrow
  | inr v =>
      have hcol := matchingBitCrossSelected_full_cols_spec σ (.inr v)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m
          (.inr (matchingCrossCols
            (matchingBitCrossSelectedToCross σ) (.inr v)).1)) =
          matchingBlockIndexEquiv ell m (.inl (.inr v.1))
        at hcol
      have hpre :
          σ.1.1.symm
            (matchingBlockIndexEquiv ell m (.inl (.inr v.1))) =
              matchingBlockIndexEquiv ell m
                (.inr (matchingCrossCols
                  (matchingBitCrossSelectedToCross σ) (.inr v)).1) :=
        σ.1.1.symm_apply_eq.mpr hcol.symm
      change
        MvPolynomial.eval (matchingPermanentSpecialization p q)
          (matchingPermutationOutsideFactor
            (matchingDiagonalEmbedding ell m) σ.1.1
            (σ.1.1.symm
              (matchingBlockIndexEquiv ell m (.inl (.inr v.1))))) = _
      rw [hpre]
      exact matchingPermutationOutsideFactor_external_right_eval
        p q σ.1.1
        (matchingCrossCols
          (matchingBitCrossSelectedToCross σ) (.inr v)).1 v.1 hcol

private theorem matchingBitCrossSelectedPermutation_weight
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m)
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    (∏ i : {i : Fin ((ell + ell) + m) //
        i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1 i.1)) =
      matchingCrossWeight p q
        (matchingBitSubset ell (de.1 : ℕ))
        (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
        (matchingBitCrossSelectedToCross σ) := by
  classical
  let f : Fin ((ell + ell) + m) → ℂ := fun i =>
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor
        (matchingDiagonalEmbedding ell m) σ.1.1 i)
  have hrest (i : Fin ((ell + ell) + m))
      (hi : i ∉ Set.range (matchingBitCrossSelectedSupportEmbedding σ)) :
      f i = 1 := by
    apply matchingBitCrossSelected_factor_one_off_support
      p q de ab σ i
    · intro u hu
      exact hi ⟨.inl u, hu.symm⟩
    · intro v hv
      exact hi ⟨.inr v, hv.symm⟩
  have hfull :
      (∏ i : Fin ((ell + ell) + m), f i) =
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
    calc
      (∏ i : Fin ((ell + ell) + m), f i) =
          ∏ t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
            ↥(matchingBitSubset ell (de.2 : ℕ)),
              f (matchingBitCrossSelectedSupportEmbedding σ t) := by
        symm
        exact Fintype.prod_of_injective
          (matchingBitCrossSelectedSupportEmbedding σ)
          (matchingBitCrossSelectedSupportEmbedding σ).injective
          (fun t => f (matchingBitCrossSelectedSupportEmbedding σ t))
          f hrest (fun _ => rfl)
      _ =
          ∏ t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
            ↥(matchingBitSubset ell (de.2 : ℕ)),
              match t with
              | .inl u =>
                  p ((matchingCrossRows
                    (matchingBitCrossSelectedToCross σ) (.inl u)).1) ^
                      (2 ^ (u.1 : ℕ))
              | .inr v =>
                  q ((matchingCrossCols
                    (matchingBitCrossSelectedToCross σ) (.inr v)).1) ^
                      (2 ^ (v.1 : ℕ)) := by
        apply Finset.prod_congr rfl
        intro t _
        exact matchingBitCrossSelectedSupportEmbedding_factor p q σ t
      _ = matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
        rw [Fintype.prod_sum_type]
        rfl
  have hderiv :
      f (matchingExternalEntry ell m ab.1 ab.2).1.1 = 1 := by
    exact matchingPermutationOutsideFactor_external_external_eval
      p q σ.1.1 ab.1 ab.2
      (matchingBitSelectedPermutation_external σ.1)
  have hdeleted := Fintype.prod_eq_mul_prod_subtype_ne f
    (matchingExternalEntry ell m ab.1 ab.2).1.1
  rw [hderiv, one_mul] at hdeleted
  exact hdeleted.symm.trans hfull

private theorem matchingPermanentJacobian_eq_cross_selected_sum
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m) :
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) := by
  classical
  let w (σ : Equiv.Perm (Fin ((ell + ell) + m))) : ℂ :=
    ∏ i : {i : Fin ((ell + ell) + m) //
      i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ i.1)
  have hselected :
      matchingPermanentJacobian (ell := ell) p q de ab =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1 := by
    rw [matchingPermanentJacobian_apply]
    change
      (∑ σ : Equiv.Perm (Fin ((ell + ell) + m)),
        if matchingPermutationExponent
            (matchingDiagonalEmbedding ell m) σ =
              matchingSquarefreeMonomial
                (matchingBitCoefficientSet ell m de) ∧
            σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
              (matchingExternalEntry ell m ab.1 ab.2).1.2 then
          w σ
        else 0) =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hvanish
      (σ : MatchingBitSelectedPermutation ell m de ab)
      (hnot : ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
        y ∉ matchingBitCoefficientSet ell m de},
        ∃ j : Fin m,
          σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
            matchingBlockIndexEquiv ell m (.inr j)) :
      w σ.1 = 0 := by
    by_contra hnonzero
    apply hnot
    intro y
    cases himage :
      (matchingBlockIndexEquiv ell m).symm
        (σ.1 (matchingBlockIndexEquiv ell m (.inl y.1))) with
    | inl y' =>
        have hσ :
            σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
              matchingBlockIndexEquiv ell m (.inl y') := by
          have h := congrArg (matchingBlockIndexEquiv ell m) himage
          simpa only [Equiv.apply_symm_apply] using h
        have hne : y' ≠ y.1 := by
          intro heq
          subst y'
          have hfix :=
            (matchingPermutationExponent_eq_squarefree_iff
              (matchingDiagonalEmbedding ell m) σ.1
              (matchingBitCoefficientSet ell m de)).mp
                σ.property.1 y.1
          exact y.property (hfix.mp hσ)
        have hz :=
          matchingPermutationOutsideFactor_internal_product_zero
            p q σ.1 ab.1 ab.2 y.1 y' hne hσ
        exact (hnonzero hz).elim
    | inr j =>
        refine ⟨j, ?_⟩
        have h := congrArg (matchingBlockIndexEquiv ell m) himage
        simpa only [Equiv.apply_symm_apply] using h
  calc
    matchingPermanentJacobian (ell := ell) p q de ab =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1 :=
      hselected
    _ =
        (∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
          w σ.1.1) +
        ∑ σ : {σ : MatchingBitSelectedPermutation ell m de ab //
          ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
            y ∉ matchingBitCoefficientSet ell m de},
            ∃ j : Fin m,
              σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                matchingBlockIndexEquiv ell m (.inr j)}, w σ.1.1 := by
      exact
        (Fintype.sum_subtype_add_sum_subtype
          (fun σ : MatchingBitSelectedPermutation ell m de ab =>
            ∀ y : {y : Fin ell ⊕ Fin ell //
              y ∉ matchingBitCoefficientSet ell m de},
              ∃ j : Fin m,
                σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                  matchingBlockIndexEquiv ell m (.inr j))
          (fun σ => w σ.1)).symm
    _ = ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
          w σ.1.1 := by
      have hz :
          (∑ σ : {σ : MatchingBitSelectedPermutation ell m de ab //
            ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
              y ∉ matchingBitCoefficientSet ell m de},
              ∃ j : Fin m,
                σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                  matchingBlockIndexEquiv ell m (.inr j)},
            w σ.1.1) = 0 := by
        apply Finset.sum_eq_zero
        intro σ _
        exact hvanish σ.1 σ.property
      rw [hz, add_zero]
    _ =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) := by
      rfl


private noncomputable def matchingMarkedFinset {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.image d

@[simp] private theorem mem_matchingMarkedFinset {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) (i : Fin n × Fin n) :
    i ∈ matchingMarkedFinset d ↔ ∃ y : Y, d y = i := by
  classical
  simp only [matchingMarkedFinset, Finset.mem_image, Finset.mem_univ, true_and]

private theorem matchingMarkedPermanent_pderiv_ne_zero
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) (y : Y) :
    MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) ≠ 0 := by
  have hrename := MvPolynomial.pderiv_rename
    (matchingVariableEquiv d).symm.injective (d y)
    (permanentPolynomial n)
  have hy : (matchingVariableEquiv d).symm (d y) = .inl y :=
    (matchingVariableEquiv d).symm_apply_eq.mpr
      (matchingVariableEquiv_inl d y)
  have hderiv :
      MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) =
        MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
          (MvPolynomial.pderiv (d y) (permanentPolynomial n)) := by
    change MvPolynomial.pderiv (.inl y)
      (MvPolynomial.rename (matchingVariableEquiv d).symm
        (permanentPolynomial n)) =
      MvPolynomial.rename (matchingVariableEquiv d).symm
        (MvPolynomial.pderiv (d y) (permanentPolynomial n))
    rw [← hy]
    exact hrename
  intro hzero
  apply permanentPolynomial_pderiv_ne_zero (d y).1 (d y).2
  apply (MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm).injective
  rw [map_zero]
  exact hderiv.symm.trans hzero


namespace RationalFormula

variable {ι : Type u} {κ : Type v} {R : Type w}

private def rename (e : ι ≃ κ) : RationalFormula ι R → RationalFormula κ R
  | .var i => .var (e i)
  | .const c => .const c
  | .add f g => .add (rename e f) (rename e g)
  | .sub f g => .sub (rename e f) (rename e g)
  | .mul f g => .mul (rename e f) (rename e g)
  | .div f g => .div (rename e f) (rename e g)

private noncomputable def renameFractionEquiv [Field R] (e : ι ≃ κ) :
    FractionRing (MvPolynomial ι R) ≃+*
      FractionRing (MvPolynomial κ R) :=
  IsFractionRing.ringEquivOfRingEquiv
    (MvPolynomial.renameEquiv R e).toRingEquiv

@[simp] private theorem renameFractionEquiv_algebraMap [Field R]
    (e : ι ≃ κ) (p : MvPolynomial ι R) :
    renameFractionEquiv e
        (algebraMap (MvPolynomial ι R)
          (FractionRing (MvPolynomial ι R)) p) =
      algebraMap (MvPolynomial κ R)
        (FractionRing (MvPolynomial κ R))
        (MvPolynomial.renameEquiv R e p) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (MvPolynomial.renameEquiv R e).toRingEquiv p

private theorem eval_rename [Field R] (e : ι ≃ κ)
    (f : RationalFormula ι R) :
    eval (rename e f) = renameFractionEquiv e (eval f) := by
  induction f with
  | var i =>
      simp only [rename, eval, renameFractionEquiv_algebraMap, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X]
  | const c =>
      simp only [rename, eval, renameFractionEquiv_algebraMap, MvPolynomial.renameEquiv_apply,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add f g hf hg => simp only [rename, eval, hf, hg, map_add]
  | sub f g hf hg => simp only [rename, eval, hf, hg, map_sub]
  | mul f g hf hg => simp only [rename, eval, hf, hg, map_mul]
  | div f g hf hg => simp only [rename, eval, hf, hg, map_div₀]

private theorem valid_rename [Field R] (e : ι ≃ κ)
    {f : RationalFormula ι R} (h : Valid f) :
    Valid (rename e f) := by
  induction h with
  | var i => exact .var _
  | const c => exact .const _
  | add hf hg ihf ihg => exact .add ihf ihg
  | sub hf hg ihf ihg => exact .sub ihf ihg
  | mul hf hg ihf ihg => exact .mul ihf ihg
  | div hf hg hden ihf ihg =>
      apply Valid.div ihf ihg
      intro hzero
      apply hden
      apply (renameFractionEquiv e).injective
      simpa only [map_zero, EmbeddingLike.map_eq_zero_iff, eval_rename] using hzero

private theorem yLeafCount_rename_matchingVariableEquiv
    {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) (f : RationalFormula (Fin n × Fin n) R) :
    yLeafCount (rename (matchingVariableEquiv d).symm f) =
      blockLeaves (matchingMarkedFinset d) f := by
  classical
  induction f with
  | var i =>
      cases h : (matchingVariableEquiv d).symm i with
      | inl y =>
          have hi : d y = i := by
            have he := (matchingVariableEquiv d).apply_symm_apply i
            simpa only [h, matchingVariableEquiv_inl] using he
          have hmem : i ∈ matchingMarkedFinset d :=
            (mem_matchingMarkedFinset d i).mpr ⟨y, hi⟩
          simp only [rename, h, yLeafCount, blockLeaves, hmem, ↓reduceIte]
      | inr z =>
          have hi : i ∉ matchingMarkedFinset d := by
            intro hmem
            obtain ⟨y, hy⟩ := (mem_matchingMarkedFinset d i).mp hmem
            have he : (matchingVariableEquiv d).symm i = .inl y := by
              apply (matchingVariableEquiv d).injective
              simpa only [Equiv.apply_symm_apply, matchingVariableEquiv_inl]
                using hy.symm
            rw [h] at he
            cases he
          simp only [rename, h, yLeafCount, blockLeaves, hi, ↓reduceIte]
  | const c => simp only [rename, yLeafCount, blockLeaves]
  | add f g hf hg => simp only [rename, yLeafCount, hf, hg, blockLeaves]
  | sub f g hf hg => simp only [rename, yLeafCount, hf, hg, blockLeaves]
  | mul f g hf hg => simp only [rename, yLeafCount, hf, hg, blockLeaves]
  | div f g hf hg => simp only [rename, yLeafCount, hf, hg, blockLeaves]

private theorem eval_rename_eq_matchingMarkedPermanent
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    eval (rename (matchingVariableEquiv d).symm f) =
      algebraMap
        (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d) := by
  rw [eval_rename, hf, renameFractionEquiv_algebraMap]
  rfl

private theorem yLeafCount_pos_of_eval_eq_matchingMarkedPermanent
    {n : ℕ} {Y : Type u} [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Y ⊕ matchingOutside d) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d)) :
    0 < yLeafCount f := by
  classical
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨c, hc⟩ :=
    exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero f hzero
  have hsplit :
      splitPolynomialHom (Y := Y) (Z := matchingOutside d) (F := ℂ)
          (matchingMarkedPermanent d) =
        splitCoefficientHom (Y := Y) (Z := matchingOutside d) (F := ℂ) c := by
    rw [splitEval, hf, splitFractionHom_algebraMap] at hc
    exact hc
  let E := rationalCoefficientField (matchingOutside d) ℂ
  have hpoly :
      MvPolynomial.map
          (algebraMap (MvPolynomial (matchingOutside d) ℂ) E)
          (MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
            (matchingMarkedPermanent d)) =
        MvPolynomial.C c := by
    apply IsFractionRing.injective
      (MvPolynomial Y E) (rationalSplitField Y (matchingOutside d) ℂ)
    simpa only [algebraMap.coe_inj, splitPolynomialHom, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        splitCoefficientHom] using
      hsplit
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hderiv := congrArg (MvPolynomial.pderiv y) hpoly
  have hmarked :
      MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) = 0 := by
    apply (MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)).injective
    apply MvPolynomial.map_injective
      (algebraMap (MvPolynomial (matchingOutside d) ℂ) E)
      (IsFractionRing.injective (MvPolynomial (matchingOutside d) ℂ) E)
    simpa only [map_zero, MvPolynomial.pderiv_map, MvPolynomial.pderiv_sumAlgEquiv,
      MvPolynomial.derivation_C] using hderiv
  exact matchingMarkedPermanent_pderiv_ne_zero d y hmarked

private theorem blockLeaves_pos_of_eval_eq_permanent
    {n : ℕ} (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (s : Finset (Fin n × Fin n)) (a b : Fin n)
    (hab : (a, b) ∈ s) :
    0 < blockLeaves s f := by
  classical
  let d : (↥s) ↪ Fin n × Fin n :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let : Nonempty (↥s) := ⟨⟨(a, b), hab⟩⟩
  have hset : matchingMarkedFinset d = s := by
    ext i
    simp only [matchingMarkedFinset, Function.Embedding.coeFn_mk, Finset.univ_eq_attach,
      Finset.attach_image_val,
      d]
  have hrename := eval_rename_eq_matchingMarkedPermanent d f hf
  have hpos := yLeafCount_pos_of_eval_eq_matchingMarkedPermanent
    d (rename (matchingVariableEquiv d).symm f) hrename
  rw [yLeafCount_rename_matchingVariableEquiv, hset] at hpos
  exact hpos

end RationalFormula

private theorem four_mul_le_two_pow_pred (ell : ℕ) (hell : 6 ≤ ell) :
    4 * ell ≤ 2 ^ (ell - 1) := by
  induction ell, hell using Nat.le_induction with
  | base => norm_num
  | succ ell hell ih =>
      have hell_pos : 1 ≤ ell := by omega
      calc
        4 * (ell + 1) ≤ 2 * (4 * ell) := by omega
        _ ≤ 2 * 2 ^ (ell - 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((ell + 1) - 1) := by
          calc
            2 * 2 ^ (ell - 1) = 2 ^ (ell - 1) * 2 := by ac_rfl
            _ = 2 ^ (ell - 1 + 1) := by rw [pow_succ]
            _ = 2 ^ ((ell + 1) - 1) := by
              congr 1
              omega

private theorem five_le_clog_two {n : ℕ} (hn : 32 ≤ n) :
    5 ≤ Nat.clog 2 n := by
  calc
    5 = Nat.clog 2 (2 ^ 5) :=
      (Nat.clog_pow 2 5 (by norm_num)).symm
    _ ≤ Nat.clog 2 n := Nat.clog_mono_right 2 (by simpa only [Nat.reducePow] using hn)

private theorem four_mul_clog_two_lt_self {n : ℕ} (hn : 32 ≤ n) :
    4 * Nat.clog 2 n < n := by
  have hfive := five_le_clog_two hn
  by_cases hfive_eq : Nat.clog 2 n = 5
  · omega
  · have hsix : 6 ≤ Nat.clog 2 n := by omega
    have hpow : 2 ^ (Nat.clog 2 n - 1) < n := by
      simpa only [Nat.pred_eq_sub_one] using (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num)
        (x := n) (by omega))
    exact (four_mul_le_two_pow_pred (Nat.clog 2 n) hsix).trans_lt hpow

private theorem matching_block_size_le_half {n : ℕ} (hn : 32 ≤ n) :
    2 * Nat.clog 2 n ≤ n / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  have h := four_mul_clog_two_lt_self hn
  omega

private theorem matching_external_size_ge_block_add_one {n : ℕ} (hn : 32 ≤ n) :
    2 * Nat.clog 2 n + 1 ≤ n - 2 * Nat.clog 2 n := by
  have h := four_mul_clog_two_lt_self hn
  omega

private theorem matching_external_size_le_two_pow {n : ℕ} :
    n - 2 * Nat.clog 2 n ≤ 2 ^ Nat.clog 2 n :=
  (Nat.sub_le n _).trans (Nat.le_pow_clog (by norm_num) n)

private theorem clog_two_cast_le_two_mul_logb {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by
  have hclog : 0 < Nat.clog 2 n :=
    Nat.clog_pos (by norm_num) (by omega)
  have hpow : 2 ^ (Nat.clog 2 n).pred < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpow_real :
      (2 : ℝ) ^ (Nat.clog 2 n).pred < (n : ℝ) := by
    exact_mod_cast hpow
  have hpred_log :
      ((Nat.clog 2 n).pred : ℝ) < Real.logb 2 (n : ℝ) := by
    calc
      ((Nat.clog 2 n).pred : ℝ) =
          Real.logb 2 ((2 : ℝ) ^ (Nat.clog 2 n).pred) := by
            rw [Real.logb_pow]
            norm_num
      _ < Real.logb 2 (n : ℝ) :=
        Real.logb_lt_logb (by norm_num) (by positivity) hpow_real
  have hlog_one : 1 ≤ Real.logb 2 (n : ℝ) := by
    calc
      (1 : ℝ) = Real.logb 2 (2 : ℝ) := by norm_num
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num)
          (by exact_mod_cast hn)
  have hpred :
      (Nat.clog 2 n : ℝ) = ((Nat.clog 2 n).pred : ℝ) + 1 := by
    have hpred_nat :
        Nat.clog 2 n = (Nat.clog 2 n).pred + 1 := by
      simpa only [Nat.pred_eq_sub_one,
        Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hclog).symm
    exact_mod_cast hpred_nat
  linarith

private theorem fourth_power_logarithmic_lower_bound
    {n leaves c : ℕ} (hn : 32 ≤ n) (hc : 0 < c)
    (hbound : n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 /
        (4 * (c : ℝ) * Real.logb 2 (n : ℝ)) ≤ (leaves : ℝ) := by
  have hlog : 0 < Real.logb 2 (n : ℝ) := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (by omega : 1 < n)
  have hclog := clog_two_cast_le_two_mul_logb (by omega : 2 ≤ n)
  have hclog' :
      2 * (Nat.clog 2 n : ℝ) ≤ 4 * Real.logb 2 (n : ℝ) := by
    linarith
  have hbound' :
      (n : ℝ) ^ 4 ≤
        (c : ℝ) * (2 * (Nat.clog 2 n : ℝ)) * (leaves : ℝ) := by
    exact_mod_cast hbound
  have hdenom : 0 < 4 * (c : ℝ) * Real.logb 2 (n : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenom).2
  calc
    (n : ℝ) ^ 4 ≤
        (c : ℝ) * (2 * (Nat.clog 2 n : ℝ)) * (leaves : ℝ) := hbound'
    _ ≤ (c : ℝ) * (4 * Real.logb 2 (n : ℝ)) * (leaves : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hclog' (by positivity)) (by positivity)
    _ = (leaves : ℝ) *
        (4 * (c : ℝ) * Real.logb 2 (n : ℝ)) := by ring

private theorem rational_logarithmic_lower_bound
    {n leaves : ℕ} (hn : 32 ≤ n)
    (hbound : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤ (leaves : ℝ) := by
  convert fourth_power_logarithmic_lower_bound hn
    (by norm_num : 0 < 48) hbound using 1
  norm_num

private theorem two_le_leaves_of_fourth_power_bound
    {n leaves c : ℕ} (hn : 32 ≤ n) (hc : c ≤ 48)
    (hbound : n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves) :
    2 ≤ leaves := by
  have hclog : 2 * Nat.clog 2 n ≤ n := by
    have h := four_mul_clog_two_lt_self hn
    omega
  by_contra hleaves
  have hone : leaves ≤ 1 := by omega
  have hsmall : n ^ 4 ≤ 48 * n := by
    calc
      n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves := hbound
      _ ≤ c * (2 * Nat.clog 2 n) := by
        simpa only [mul_one] using Nat.mul_le_mul_left (c * (2 * Nat.clog 2 n)) hone
      _ ≤ 48 * (2 * Nat.clog 2 n) :=
        Nat.mul_le_mul_right (2 * Nat.clog 2 n) hc
      _ ≤ 48 * n := Nat.mul_le_mul_left 48 hclog
  have hcube : 32 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hnpos : 0 < n := by omega
  have hlarge : 48 * n < n ^ 4 := by
    calc
      48 * n < (32 ^ 3) * n :=
        (Nat.mul_lt_mul_right hnpos).2 (by norm_num)
      _ ≤ n ^ 3 * n := Nat.mul_le_mul_right n hcube
      _ = n ^ 4 := by ring
  omega

private theorem rational_internal_logarithmic_lower_bound
    {n leaves gates : ℕ} (hn : 32 ≤ n)
    (htree : leaves = gates + 1)
    (hbound : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 / (384 * Real.logb 2 (n : ℝ)) ≤ (gates : ℝ) := by
  have hleaves : 2 ≤ leaves :=
    two_le_leaves_of_fourth_power_bound hn (by norm_num : 48 ≤ 48) hbound
  have htwice : leaves ≤ 2 * gates := by omega
  have hgate :
      n ^ 4 ≤ 96 * (2 * Nat.clog 2 n) * gates := by
    calc
      n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves := hbound
      _ ≤ 48 * (2 * Nat.clog 2 n) * (2 * gates) :=
        Nat.mul_le_mul_left (48 * (2 * Nat.clog 2 n)) htwice
      _ = 96 * (2 * Nat.clog 2 n) * gates := by ring
  convert fourth_power_logarithmic_lower_bound hn
    (by norm_num : 0 < 96) hgate using 1
  norm_num

private theorem matchingPermanentJacobian_eq_weighted
    {ell m : ℕ} (p q : Fin m → ℂ) :
    matchingPermanentJacobian (ell := ell) p q =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) := by
  classical
  ext de ab
  calc
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) :=
      matchingPermanentJacobian_eq_cross_selected_sum p q de ab
    _ =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact matchingBitCrossSelectedPermutation_weight
        p q de ab σ
    _ =
      ∑ τ : MatchingCrossPermutation
        (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
          ↥(matchingBitSubset ell (de.2 : ℕ)))
        {j : Fin m // j ≠ ab.1}
        {j : Fin m // j ≠ ab.2},
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2 τ := by
      apply Fintype.sum_equiv
        (matchingBitCrossSelectedEquiv ell m de ab)
      intro σ
      rfl
    _ = matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) de ab :=
      matchingWeightedCrossBitPermutation_sum p q de ab

private theorem matchingPermanentJacobian_det_ne_zero
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    (matchingPermanentJacobian (ell := ell) p q).det ≠ 0 := by
  rw [matchingPermanentJacobian_eq_weighted]
  exact matchingWeightedBivariateBitEvaluationMatrix_det_ne_zero
    p q hp hq hm hroom

private theorem matchingMarkedPermanent_bit_coefficients_algebraicIndependent
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de))) := by
  apply algebraicIndependent_of_evaluatedJacobianMinor_det_ne_zero
    (fun de : Fin m × Fin m =>
      coefficientPolynomial
        (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
        (matchingSquarefreeMonomial
          (matchingBitCoefficientSet ell m de)))
    (fun ab : Fin m × Fin m =>
      matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)
  exact matchingPermanentJacobian_det_ne_zero p q hp hq hm hroom

private noncomputable def matchingCanonicalComplexPoints (m : ℕ) : Fin m → ℂ :=
  fun i => (i.1 : ℂ)

private theorem matchingCanonicalComplexPoints_injective (m : ℕ) :
    Function.Injective (matchingCanonicalComplexPoints m) := by
  intro a b h
  change (a.1 : ℂ) = (b.1 : ℂ) at h
  apply Fin.ext
  exact_mod_cast h

private theorem matchingMarkedPermanent_bitCoefficient_algebraicIndependent
    {ell m : ℕ} (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de))) :=
  matchingMarkedPermanent_bit_coefficients_algebraicIndependent
    (matchingCanonicalComplexPoints m)
    (matchingCanonicalComplexPoints m)
    (matchingCanonicalComplexPoints_injective m)
    (matchingCanonicalComplexPoints_injective m)
    hm hroom

private noncomputable def matchingEmbeddingPermutation
    {α : Type u} {β : Type v} [Finite α]
    (f g : α ↪ β) : Equiv.Perm β :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair
      (f : α → β) (g : α → β) f.injective g.injective)

@[simp] private theorem matchingEmbeddingPermutation_apply
    {α : Type u} {β : Type v} [Finite α]
    (f g : α ↪ β) (a : α) :
    matchingEmbeddingPermutation f g (f a) = g a :=
  Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (f : α → β) (g : α → β) f.injective g.injective) a

private theorem permanentPolynomial_rename_prodCongr
    {n : ℕ} (r c : Equiv.Perm (Fin n)) :
    MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) = permanentPolynomial n := by
  classical
  let M := Matrix.mvPolynomialX (Fin n) (Fin n) ℂ
  have hmap :
      MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) =
          (M.submatrix r c).permanent := by
    simp only [permanentPolynomial, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum, map_prod,
      MvPolynomial.renameEquiv_apply, Equiv.prodCongr_apply, MvPolynomial.rename_X, Prod.map_apply,
      Matrix.submatrix_apply, M]
  calc
    MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) =
      (M.submatrix r c).permanent := hmap
    _ = ((M.submatrix r id).submatrix id c).permanent := by rfl
    _ = (M.submatrix r id).permanent :=
      Matrix.permanent_permute_rows c (M.submatrix r id)
    _ = M.permanent := Matrix.permanent_permute_cols r M
    _ = permanentPolynomial n := rfl

private noncomputable def matchingOutsideRelabelEquiv
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y) :
    matchingOutside d₀ ≃ matchingOutside d := by
  classical
  apply e.subtypeEquiv
  intro x
  apply not_congr
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (he y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, e.injective ?_⟩
    exact (he y).trans hy

@[simp] private theorem matchingOutsideRelabelEquiv_apply_val
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y)
    (z : matchingOutside d₀) :
    (matchingOutsideRelabelEquiv d₀ d e he z).1 = e z.1 := by
  rfl

private theorem coefficientPolynomial_rename_outside
    {Y : Type u} {Z : Type v} {W : Type w}
    {F : Type*} [Field F]
    (e : Z ≃ W) (f : MvPolynomial (Y ⊕ Z) F)
    (α : Y →₀ ℕ) :
    coefficientPolynomial
        (MvPolynomial.renameEquiv F
          (Equiv.sumCongr (Equiv.refl Y) e) f) α =
      MvPolynomial.renameEquiv F e (coefficientPolynomial f α) := by
  classical
  let L : MvPolynomial (Y ⊕ Z) F →ₐ[F]
      MvPolynomial Y (MvPolynomial W F) :=
    (MvPolynomial.sumAlgEquiv F Y W).toAlgHom.comp
      (MvPolynomial.renameEquiv F
        (Equiv.sumCongr (Equiv.refl Y) e)).toAlgHom
  let R : MvPolynomial (Y ⊕ Z) F →ₐ[F]
      MvPolynomial Y (MvPolynomial W F) :=
    (MvPolynomial.mapAlgHom
      (MvPolynomial.renameEquiv F e).toAlgHom).comp
      (MvPolynomial.sumAlgEquiv F Y Z).toAlgHom
  have h : L = R := by
    ext i
    cases i with
    | inl y =>
        simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
          MvPolynomial.renameEquiv_apply,
          MvPolynomial.rename_X, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq,
            MvPolynomial.sumAlgEquiv_X_inl,
          MvPolynomial.mapAlgHom_apply, AlgEquiv.toAlgHom_toRingHom, MvPolynomial.map_X, L, R]
    | inr z =>
        simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
          MvPolynomial.renameEquiv_apply,
          MvPolynomial.rename_X, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr,
            MvPolynomial.sumAlgEquiv_X_inr,
          MvPolynomial.coeff_C, MvPolynomial.mapAlgHom_apply, AlgEquiv.toAlgHom_toRingHom,
            MvPolynomial.map_C,
          RingHom.coe_coe, L, R]
  change MvPolynomial.coeff α
    ((MvPolynomial.sumAlgEquiv F Y W)
      (MvPolynomial.renameEquiv F
        (Equiv.sumCongr (Equiv.refl Y) e) f)) = _
  change MvPolynomial.coeff α (L f) = _
  rw [h]
  change MvPolynomial.coeff α
    (MvPolynomial.map
      (MvPolynomial.renameEquiv F e).toRingHom
      ((MvPolynomial.sumAlgEquiv F Y Z) f)) = _
  rw [MvPolynomial.coeff_map]
  rfl

private theorem matchingVariableEquiv_relabel_commutes
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y) :
    (matchingVariableEquiv d₀).symm.trans
      (Equiv.sumCongr (Equiv.refl Y)
        (matchingOutsideRelabelEquiv d₀ d e he)) =
      e.trans (matchingVariableEquiv d).symm := by
  apply Equiv.ext
  intro x
  apply (matchingVariableEquiv d).injective
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change matchingVariableEquiv d
    ((Equiv.sumCongr (Equiv.refl Y)
      (matchingOutsideRelabelEquiv d₀ d e he))
        ((matchingVariableEquiv d₀).symm x)) = e x
  generalize hz : (matchingVariableEquiv d₀).symm x = z
  have hx : matchingVariableEquiv d₀ z = x := by
    rw [← hz, Equiv.apply_symm_apply]
  cases z with
  | inl y =>
      simpa only [Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq,
        matchingVariableEquiv_inl, ← hx] using
        (he y).symm
  | inr w =>
      simp only [Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, matchingVariableEquiv_inr,
        matchingOutsideRelabelEquiv_apply_val, ← hx]

private theorem matchingMarkedPermanent_rename_prodCongr
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y) :
    MvPolynomial.renameEquiv ℂ
        (Equiv.sumCongr (Equiv.refl Y)
          (matchingOutsideRelabelEquiv d₀ d
            (Equiv.prodCongr r c) he))
        (matchingMarkedPermanent d₀) =
      matchingMarkedPermanent d := by
  classical
  have hcomm := matchingVariableEquiv_relabel_commutes d₀ d
    (Equiv.prodCongr r c) he
  unfold matchingMarkedPermanent
  rw [← AlgEquiv.trans_apply, MvPolynomial.renameEquiv_trans, hcomm,
    ← MvPolynomial.renameEquiv_trans, AlgEquiv.trans_apply,
    permanentPolynomial_rename_prodCongr]

private theorem matchingMarkedPermanent_algebraicIndependent_of_prodCongr
    {n : ℕ} {Y : Type u} {ι : Type v}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y)
    (α : ι → Y →₀ ℕ)
    (hind : AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d₀) (α i))) :
    AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d) (α i)) := by
  let eo := matchingOutsideRelabelEquiv d₀ d
    (Equiv.prodCongr r c) he
  have hmap : AlgebraicIndependent ℂ
      (fun i => MvPolynomial.renameEquiv ℂ eo
        (coefficientPolynomial (matchingMarkedPermanent d₀) (α i))) := by
    change AlgebraicIndependent ℂ
      ((MvPolynomial.renameEquiv ℂ eo).toAlgHom ∘
        fun i => coefficientPolynomial (matchingMarkedPermanent d₀) (α i))
    exact hind.map' (MvPolynomial.renameEquiv ℂ eo).injective
  have hcoeff (i : ι) :
      coefficientPolynomial (matchingMarkedPermanent d) (α i) =
        MvPolynomial.renameEquiv ℂ eo
          (coefficientPolynomial (matchingMarkedPermanent d₀) (α i)) := by
    rw [← matchingMarkedPermanent_rename_prodCongr d₀ d r c he]
    exact coefficientPolynomial_rename_outside eo
      (matchingMarkedPermanent d₀) (α i)
  rw [show (fun i => coefficientPolynomial
      (matchingMarkedPermanent d) (α i)) =
      (fun i => MvPolynomial.renameEquiv ℂ eo
        (coefficientPolynomial (matchingMarkedPermanent d₀) (α i)))
    from funext hcoeff]
  exact hmap

private theorem exists_matchingDiagonal_prodCongr
    {ell m : ℕ}
    (d : (Fin ell ⊕ Fin ell) ↪
      Fin ((ell + ell) + m) × Fin ((ell + ell) + m))
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2)) :
    ∃ r c : Equiv.Perm (Fin ((ell + ell) + m)),
      ∀ y : Fin ell ⊕ Fin ell,
        Equiv.prodCongr r c
          (matchingDiagonalEmbedding ell m y) = d y := by
  classical
  let d₀ := matchingDiagonalEmbedding ell m
  let r₀ : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d₀ y).1, by
      intro x y h
      change matchingBlockIndexEquiv ell m (.inl x) =
        matchingBlockIndexEquiv ell m (.inl y) at h
      exact Sum.inl_injective
        ((matchingBlockIndexEquiv ell m).injective h)⟩
  let c₀ : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d₀ y).2, by
      intro x y h
      change matchingBlockIndexEquiv ell m (.inl x) =
        matchingBlockIndexEquiv ell m (.inl y) at h
      exact Sum.inl_injective
        ((matchingBlockIndexEquiv ell m).injective h)⟩
  let rd : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d y).1, hrows⟩
  let cd : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d y).2, hcols⟩
  refine ⟨matchingEmbeddingPermutation r₀ rd,
    matchingEmbeddingPermutation c₀ cd, ?_⟩
  intro y
  apply Prod.ext
  · change matchingEmbeddingPermutation r₀ rd (r₀ y) = rd y
    exact matchingEmbeddingPermutation_apply r₀ rd y
  · change matchingEmbeddingPermutation c₀ cd (c₀ y) = cd y
    exact matchingEmbeddingPermutation_apply c₀ cd y

private theorem matchingMarkedPermanent_square_of_matching_of_algebraicIndependent
    {n ell m : ℕ} (hn : n = (ell + ell) + m)
    (d : (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n)
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2))
    (hind : AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de)))) :
    ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d) := by
  subst n
  obtain ⟨r, c, he⟩ :=
    exists_matchingDiagonal_prodCongr d hrows hcols
  apply coefficientTranscendenceDegree_ge_square_of_algebraicIndependent
    (matchingMarkedPermanent d)
    (fun de : Fin m × Fin m =>
      matchingSquarefreeMonomial (matchingBitCoefficientSet ell m de))
  exact matchingMarkedPermanent_algebraicIndependent_of_prodCongr
    (matchingDiagonalEmbedding ell m) d r c he _ hind

private noncomputable def matchingCyclicBlockIndexEquiv
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    (Fin ell ⊕ Fin ell) ≃ ↥(cyclicMatchingBlock hk t j) := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, card_cyclicMatchingBlock,
    two_mul]

private noncomputable def matchingCyclicDiagonalEmbedding
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n where
  toFun y := (matchingCyclicBlockIndexEquiv hk t j y).1
  inj' := fun _ _ h =>
    (matchingCyclicBlockIndexEquiv hk t j).injective (Subtype.ext h)

private theorem matchingMarkedFinset_matchingCyclicDiagonalEmbedding
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    matchingMarkedFinset (matchingCyclicDiagonalEmbedding hk t j) =
      cyclicMatchingBlock hk t j := by
  classical
  ext i
  rw [mem_matchingMarkedFinset]
  constructor
  · rintro ⟨y, hy⟩
    change (matchingCyclicBlockIndexEquiv hk t j y).1 = i at hy
    rw [← hy]
    exact (matchingCyclicBlockIndexEquiv hk t j y).property
  · intro hi
    obtain ⟨y, hy⟩ :=
      (matchingCyclicBlockIndexEquiv hk t j).surjective ⟨i, hi⟩
    refine ⟨y, ?_⟩
    change (matchingCyclicBlockIndexEquiv hk t j y).1 = i
    exact congrArg Subtype.val hy

private theorem matchingCyclicDiagonalEmbedding_fst_injective
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    Function.Injective
      (fun y => (matchingCyclicDiagonalEmbedding hk t j y).1) := by
  change Function.Injective
    (fun y => (matchingCyclicBlockIndexEquiv hk t j y).1.1)
  exact
    (cyclicMatchingBlock_fst_injective hk t j).comp
      (matchingCyclicBlockIndexEquiv hk t j).injective

private theorem matchingCyclicDiagonalEmbedding_snd_injective
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    Function.Injective
      (fun y => (matchingCyclicDiagonalEmbedding hk t j y).2) := by
  change Function.Injective
    (fun y => (matchingCyclicBlockIndexEquiv hk t j y).1.2)
  exact
    (cyclicMatchingBlock_snd_injective hk t j).comp
      (matchingCyclicBlockIndexEquiv hk t j).injective


namespace RationalFormula

private theorem matching_block_six_leaves_of_coefficientTranscendenceDegree
    {n m : ℕ} {Y : Type*} [Fintype Y] [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : Valid f)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (htd : ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d)) :
    m * m ≤ 6 * blockLeaves (matchingMarkedFinset d) f := by
  classical
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  have hymem : d y ∈ matchingMarkedFinset d :=
    (mem_matchingMarkedFinset d (d y)).2 ⟨y, rfl⟩
  have hpos : 0 < blockLeaves (matchingMarkedFinset d) f :=
    blockLeaves_pos_of_eval_eq_permanent f hf
      (matchingMarkedFinset d) (d y).1 (d y).2 hymem
  let g : RationalFormula (Y ⊕ matchingOutside d) ℂ :=
    rename (matchingVariableEquiv d).symm f
  have hmarked : 0 < yLeafCount g := by
    simpa [g, yLeafCount_rename_matchingVariableEquiv] using hpos
  have hvalid' : Valid g :=
    valid_rename (matchingVariableEquiv d).symm hvalid
  have houtput : eval g =
      algebraMap (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d) :=
    eval_rename_eq_matchingMarkedPermanent d f hf
  have hupper := rational_skeleton_trdeg g hvalid' hmarked
    (matchingMarkedPermanent d) houtput
  dsimp [g] at hupper
  rw [yLeafCount_rename_matchingVariableEquiv d f] at hupper
  have hcard :
      ((m * m : ℕ) : Cardinal) ≤
        ((6 * blockLeaves (matchingMarkedFinset d) f - 3 : ℕ) : Cardinal) :=
    htd.trans hupper
  have hnat :
      m * m ≤ 6 * blockLeaves (matchingMarkedFinset d) f - 3 := by
    exact_mod_cast hcard
  omega

private theorem cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hkn : 2 * ell ≤ n) (hhalf : n ≤ 2 * m)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : Valid f)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (hcertificate : ∀ x : Fin n × Fin (n / (2 * ell)),
      ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
        (matchingMarkedPermanent
          (matchingCyclicDiagonalEmbedding hk x.1 x.2))) :
    n ^ 4 ≤ 48 * (2 * ell) * variableLeaves f := by
  classical
  have hell : 0 < ell := by omega
  let : Nonempty (Fin ell ⊕ Fin ell) :=
    ⟨.inl ⟨0, hell⟩⟩
  apply cyclicMatchingBlock_fourth_power_bound hk hkn m hhalf f
  intro x
  have h := matching_block_six_leaves_of_coefficientTranscendenceDegree
    (matchingCyclicDiagonalEmbedding hk x.1 x.2) f hvalid hf
      (hcertificate x)
  simpa only [matchingMarkedFinset_matchingCyclicDiagonalEmbedding]
    using h

private theorem permanent_size_bounds_of_fourth_power
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hfour : n ^ 4 ≤
      48 * (2 * Nat.clog 2 n) * variableLeaves f) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (384 * Real.logb 2 (n : ℝ)) ≤
        (internalGateCount f : ℝ) := by
  have hleaf : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leafCount f :=
    hfour.trans
      (Nat.mul_le_mul_left (48 * (2 * Nat.clog 2 n))
        (variableLeaves_le_leafCount f))
  have hvertex : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * vertexCount f :=
    hfour.trans
      (Nat.mul_le_mul_left (48 * (2 * Nat.clog 2 n))
        ((variableLeaves_le_leafCount f).trans
          (leafCount_le_vertexCount f)))
  exact
    ⟨rational_logarithmic_lower_bound hn hfour,
      rational_logarithmic_lower_bound hn hleaf,
      rational_logarithmic_lower_bound hn hvertex,
      rational_internal_logarithmic_lower_bound hn
        (leafCount_eq_internalGateCount_add_one f) hleaf⟩

end RationalFormula

private theorem matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
    {n ell m : ℕ} (hn : n = (ell + ell) + m)
    (d : (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n)
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2))
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d) :=
  matchingMarkedPermanent_square_of_matching_of_algebraicIndependent
    hn d hrows hcols
    (matchingMarkedPermanent_bitCoefficient_algebraicIndependent hm hroom)

private theorem matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hn : n = (ell + ell) + m)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
      (matchingMarkedPermanent (matchingCyclicDiagonalEmbedding hk t j)) :=
  matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
    hn (matchingCyclicDiagonalEmbedding hk t j)
    (matchingCyclicDiagonalEmbedding_fst_injective hk t j)
    (matchingCyclicDiagonalEmbedding_snd_injective hk t j)
    hm hroom

private theorem permanent_rational_formula_fourth_power_lower_bound
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : RationalFormula.Valid f)
    (hf : RationalFormula.eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) *
      RationalFormula.variableLeaves f := by
  classical
  let : NeZero n := ⟨by omega⟩
  let ell : ℕ := Nat.clog 2 n
  let m : ℕ := n - 2 * ell
  have hell : 5 ≤ ell := by
    simpa only using five_le_clog_two hn
  have hk : 0 < 2 * ell := by omega
  have hblockhalf : 2 * ell ≤ n / 2 := by
    simpa only using matching_block_size_le_half hn
  have hkn : 2 * ell ≤ n := by omega
  have hhalf : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hdecomp : n = (ell + ell) + m := by
    dsimp [m]
    omega
  have hm : m ≤ 2 ^ ell := by
    simpa [ell, m] using
      (matching_external_size_le_two_pow (n := n))
  have hroom : 2 * ell < m := by
    have h := matching_external_size_ge_block_add_one hn
    dsimp [ell, m]
    omega
  have hcertificate :
      ∀ x : Fin n × Fin (n / (2 * ell)),
        ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
          (matchingMarkedPermanent
            (matchingCyclicDiagonalEmbedding hk x.1 x.2)) := by
    intro x
    exact matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
      hk hdecomp hm hroom x.1 x.2
  have hfour :=
    RationalFormula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
      hk hkn hhalf f hvalid hf hcertificate
  simpa only [ge_iff_le] using hfour

/-- Simultaneous size lower bounds for rational formulas computing the permanent. -/
theorem permanent_rational_formula_lower_bound
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : RationalFormula.Valid f)
    (hf : RationalFormula.eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (384 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.internalGateCount f : ℝ) :=
  RationalFormula.permanent_size_bounds_of_fourth_power hn f
    (permanent_rational_formula_fourth_power_lower_bound hn f hvalid hf)

/-- Any valid rational formula computing the `n`-by-`n` permanent has at least
`n ^ 4 / (192 * logb 2 n)` variable leaves when `32 ≤ n`. -/
theorem permanent_rational_formula_logarithmic_lower_bound
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : RationalFormula.Valid f)
    (hf : RationalFormula.eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
      (RationalFormula.variableLeaves f : ℝ) :=
  (permanent_rational_formula_lower_bound hn f hvalid hf).1

end PermanentFormulaLowerBound

end
