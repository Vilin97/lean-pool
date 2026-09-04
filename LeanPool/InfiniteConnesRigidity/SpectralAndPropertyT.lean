/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Metrizable.Urysohn
import Std.Tactic.BVDecide.Normalize.Prop
public import LeanPool.InfiniteConnesRigidity.CarryAndCrossedProduct

/-!
# Spectral methods and property (T)
-/

noncomputable section

namespace ConnesRigidity
section

open ConnesRigidity MeasureTheory
open scoped ENNReal

universe u v

section

variable {K : Type u} [Group K]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- A local decidable equality used by finite-support constructions. -/
private local instance instDecidableEqLeanPool : DecidableEq K := Classical.decEq K

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def crossedOperatorBlock (X : HaarProbabilityAction K Ω)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X) (q k : K) :
    crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X :=
  (lp.evalCLM ℂ (fun _ : K ↦ crossedBaseHilbert X) 2 q).comp <|
    T.comp <|
      lp.singleContinuousLinearMap ℂ
        (fun _ : K ↦ crossedBaseHilbert X) 2 k



omit [Group K] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedFiberwiseOperator_single
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (k : K) (ξ : H) :
    crossedFiberwiseOperator (K := K) A (lp.single 2 k ξ) =
      lp.single 2 k (A ξ) := by
  classical
  ext q
  simp only [crossedFiberwiseOperator_apply, lp.single_apply]
  by_cases h : k = q
  · subst q
    simp only [Pi.single_eq_same]
  · simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne', map_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedOperatorBlock_commute_of_commute_fiberwise
    (X : HaarProbabilityAction K Ω)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X)
    (A : crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X)
    (hT : Commute T (crossedFiberwiseOperator (K := K) A))
    (q k : K) :
    Commute (crossedOperatorBlock X T q k) A := by
  apply ContinuousLinearMap.ext
  intro ξ
  change T (lp.single 2 k (A ξ)) q = A (T (lp.single 2 k ξ) q)
  rw [← crossedFiberwiseOperator_single A k ξ]
  have hcomm := DFunLike.congr_fun hT.eq (lp.single 2 k ξ)
  exact congrFun (congrArg ((↑) : crossedHilbert X →
    (K → crossedBaseHilbert X)) hcomm) q

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem commute_crossedFiberwiseOperator_of_blocks
    (X : HaarProbabilityAction K Ω)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X)
    (A : crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X)
    (hT : ∀ q k : K, Commute (crossedOperatorBlock X T q k) A) :
    Commute T (crossedFiberwiseOperator (K := K) A) := by
  apply lp.ext_continuousLinearMap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro k
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  funext q
  change
    T ((crossedFiberwiseOperator (K := K) A) (lp.single 2 k ξ)) q =
      A (T (lp.single 2 k ξ) q)
  rw [crossedFiberwiseOperator_single]
  exact DFunLike.congr_fun (hT q k).eq ξ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem commute_crossedMultiplier_iff_blocks
    (X : HaarProbabilityAction K Ω)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X)
    (f : crossedCoefficient X) :
    Commute T (crossedMultiplier X f) ↔
      ∀ q k : K,
        Commute (crossedOperatorBlock X T q k) (crossedBaseMultiplier X f) := by
  constructor
  · intro h q k
    exact crossedOperatorBlock_commute_of_commute_fiberwise X T
      (crossedBaseMultiplier X f) h q k
  · intro h
    exact commute_crossedFiberwiseOperator_of_blocks X T
      (crossedBaseMultiplier X f) h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedCharacterGeneratorSet {ι : Type*}
    (X : HaarProbabilityAction K Ω) (χ : ι → crossedCoefficient X) :
    Set (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  Set.range (fun i ↦ crossedMultiplier X (χ i)) ∪
    Set.range fun k : K ↦
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedMultiplier_mem_vonNeumannClosure_of_base_commutation
    {ι : Type*} (X : HaarProbabilityAction K Ω)
    (χ : ι → crossedCoefficient X)
    (hbase : ∀ T : crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X,
      (∀ i : ι, Commute T (crossedBaseMultiplier X (χ i))) →
        ∀ f : crossedCoefficient X, Commute T (crossedBaseMultiplier X f))
    (f : crossedCoefficient X) :
    crossedMultiplier X f ∈
      vonNeumannClosure (crossedCharacterGeneratorSet X χ) := by
  change
    crossedMultiplier X f ∈ StarSubalgebra.centralizer ℂ
      (↑(StarSubalgebra.centralizer ℂ
        (crossedCharacterGeneratorSet X χ)) :
          Set (crossedHilbert X →L[ℂ] crossedHilbert X))
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  have hcomm :
      ∀ S : crossedHilbert X →L[ℂ] crossedHilbert X,
        S ∈ StarSubalgebra.centralizer ℂ
          (crossedCharacterGeneratorSet X χ) →
          Commute S (crossedMultiplier X f) := by
    intro S hS
    apply (commute_crossedMultiplier_iff_blocks X S f).2
    intro q k
    apply hbase (crossedOperatorBlock X S q k)
    intro i
    apply crossedOperatorBlock_commute_of_commute_fiberwise X S
      (crossedBaseMultiplier X (χ i))
    have hi := (StarSubalgebra.mem_centralizer_iff ℂ).1 hS
      (crossedMultiplier X (χ i))
      (Or.inl ⟨i, rfl⟩)
    exact hi.1.symm
  exact ⟨(hcomm T hT).eq,
    (hcomm (star T) (star_mem hT)).eq⟩

section ContinuousCharacters

variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def crossedContinuousCharacterCoefficient
    (X : HaarProbabilityAction K Ω) (φ : C(Ω, ℂ)) :
    crossedCoefficient X := by
  let : IsProbabilityMeasure X.measure := X.probability
  exact ContinuousMap.toLp ⊤ X.measure ℂ φ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem commute_crossedBaseMultiplier_of_commute_characters
    {ι : Type*} (X : HaarProbabilityAction K Ω)
    [X.measure.WeaklyRegular]
    (χ : ι → C(Ω, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (T : crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X)
    (hT : ∀ i : ι, Commute T
      (crossedBaseMultiplier X
        (crossedContinuousCharacterCoefficient X (χ i))))
    (f : crossedCoefficient X) :
    Commute T (crossedBaseMultiplier X f) := by
  let : IsProbabilityMeasure X.measure := X.probability
  apply commute_multiplier_of_commute_units X.measure T
  intro u hu hunit
  apply commute_unitMultiplier_of_commute_characters
    X.measure χ hdense T
  intro i
  exact hT i

end ContinuousCharacters

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryCharacterCoefficient_eq_continuousToLp
    (n : ℕ) (η : E n) :
    carryCharacterCoefficient n η =
      ContinuousMap.toLp ⊤ (carryHaar n) ℂ (carryComplexCharacter n η) := by
  apply Lp.ext
  filter_upwards [
    carryCharacterCoefficient_apply_ae n η,
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
      (carryHaar n) (carryComplexCharacter n η)] with z hcoeff hcontinuous
  exact hcoeff.trans hcontinuous.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitCharacterCoefficient_eq_continuousToLp (d : D) :
    splitCharacterCoefficient d =
      ContinuousMap.toLp ⊤ productHaar ℂ (splitComplexCharacter d) := by
  apply Lp.ext
  filter_upwards [
    splitCharacterCoefficient_apply_ae d,
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
      productHaar (splitComplexCharacter d)] with z hcoeff hcontinuous
  exact hcoeff.trans hcontinuous.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryCharacterCoefficient_eq_crossedContinuousCharacterCoefficient
    (n : ℕ) (η : E n) :
    carryCharacterCoefficient n η =
      crossedContinuousCharacterCoefficient (paperCarryHaarAction n)
        (carryComplexCharacter n η) :=
  carryCharacterCoefficient_eq_continuousToLp n η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitCharacterCoefficient_eq_crossedContinuousCharacterCoefficient
    (d : D) :
    splitCharacterCoefficient d =
      crossedContinuousCharacterCoefficient paperSplitHaarAction
        (splitComplexCharacter d) :=
  splitCharacterCoefficient_eq_continuousToLp d

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryBaseMultiplier_commute_of_commute_characters
    (n : ℕ)
    (T : crossedBaseHilbert (paperCarryHaarAction n) →L[ℂ]
      crossedBaseHilbert (paperCarryHaarAction n))
    (hT : ∀ η : E n,
      Commute T (crossedBaseMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η)))
    (f : crossedCoefficient (paperCarryHaarAction n)) :
    Commute T (crossedBaseMultiplier (paperCarryHaarAction n) f) := by
  let : (paperCarryHaarAction n).measure.WeaklyRegular := by
    change (carryHaar n).WeaklyRegular
    infer_instance
  apply commute_crossedBaseMultiplier_of_commute_characters
    (paperCarryHaarAction n) (carryComplexCharacter n)
    (carryComplexCharacter_span_closure_eq_top n) T
  intro η
  rw [← carryCharacterCoefficient_eq_crossedContinuousCharacterCoefficient]
  exact hT η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitBaseMultiplier_commute_of_commute_characters
    (T : crossedBaseHilbert paperSplitHaarAction →L[ℂ]
      crossedBaseHilbert paperSplitHaarAction)
    (hT : ∀ d : D,
      Commute T (crossedBaseMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d)))
    (f : crossedCoefficient paperSplitHaarAction) :
    Commute T (crossedBaseMultiplier paperSplitHaarAction f) := by
  let : paperSplitHaarAction.measure.WeaklyRegular := by
    change productHaar.WeaklyRegular
    infer_instance
  apply commute_crossedBaseMultiplier_of_commute_characters
    paperSplitHaarAction splitComplexCharacter
    splitComplexCharacter_span_closure_eq_top T
  intro d
  rw [← splitCharacterCoefficient_eq_crossedContinuousCharacterCoefficient]
  exact hT d

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryMultiplier_mem_character_vonNeumannClosure
    (n : ℕ) (f : crossedCoefficient (paperCarryHaarAction n)) :
    crossedMultiplier (paperCarryHaarAction n) f ∈
      vonNeumannClosure
        (crossedCharacterGeneratorSet (paperCarryHaarAction n)
          (carryCharacterCoefficient n)) := by
  apply crossedMultiplier_mem_vonNeumannClosure_of_base_commutation
    (paperCarryHaarAction n) (carryCharacterCoefficient n)
  intro T hT g
  exact carryBaseMultiplier_commute_of_commute_characters n T hT g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitMultiplier_mem_character_vonNeumannClosure
    (f : crossedCoefficient paperSplitHaarAction) :
    crossedMultiplier paperSplitHaarAction f ∈
      vonNeumannClosure
        (crossedCharacterGeneratorSet paperSplitHaarAction
          splitCharacterCoefficient) := by
  apply crossedMultiplier_mem_vonNeumannClosure_of_base_commutation
    paperSplitHaarAction splitCharacterCoefficient
  intro T hT g
  exact splitBaseMultiplier_commute_of_commute_characters T hT g

section CrossedClosureEquality

universe u v w

variable {J : Type u} [Group J]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossed_character_vonNeumannClosure_eq_full_of_multipliers
    {ι : Type w} (A : HaarProbabilityAction J Ω)
    (χ : ι → crossedCoefficient A)
    (hχ : ∀ f : crossedCoefficient A,
      crossedMultiplier A f ∈
        vonNeumannClosure (crossedCharacterGeneratorSet A χ)) :
    vonNeumannClosure (crossedCharacterGeneratorSet A χ) =
      (crossedProductModel A).algebra := by
  let S : Set (crossedHilbert A →L[ℂ] crossedHilbert A) :=
    crossedCharacterGeneratorSet A χ
  let G : Set (crossedHilbert A →L[ℂ] crossedHilbert A) :=
    crossedGeneratorSet A
  have hsub : S ⊆ G := by
    rintro T (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inl ⟨χ i, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  have hcommutants :
      StarSubalgebra.centralizer ℂ S =
        StarSubalgebra.centralizer ℂ G := by
    apply StarSubalgebra.ext
    intro T
    constructor
    · intro hT
      rw [StarSubalgebra.mem_centralizer_iff]
      intro R hR
      rcases hR with ⟨f, rfl⟩ | ⟨k, rfl⟩
      · have hf : crossedMultiplier A f ∈
            vonNeumannClosure S := hχ f
        have hforward :=
          (StarSubalgebra.mem_centralizer_iff ℂ).1 hf T hT
        have hstar :=
          (StarSubalgebra.mem_centralizer_iff ℂ).1
            (star_mem hf) T hT
        exact ⟨hforward.1.symm, hstar.1.symm⟩
      · exact (StarSubalgebra.mem_centralizer_iff ℂ).1 hT _
          (Or.inr ⟨k, rfl⟩)
    · intro hT
      exact StarSubalgebra.centralizer_le ℂ S G hsub hT
  apply VonNeumannAlgebra.ext
  intro T
  change
    T ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ S :
        Set (crossedHilbert A →L[ℂ] crossedHilbert A)) ↔
      T ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ G :
          Set (crossedHilbert A →L[ℂ] crossedHilbert A))
  rw [hcommutants]

end CrossedClosureEquality

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carry_character_vonNeumannClosure_eq_full (n : ℕ) :
    vonNeumannClosure
      (crossedCharacterGeneratorSet (paperCarryHaarAction n)
        (carryCharacterCoefficient n)) =
      (crossedProductModel (paperCarryHaarAction n)).algebra :=
  crossed_character_vonNeumannClosure_eq_full_of_multipliers
    (paperCarryHaarAction n) (carryCharacterCoefficient n)
    (carryMultiplier_mem_character_vonNeumannClosure n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem split_character_vonNeumannClosure_eq_full :
    vonNeumannClosure
      (crossedCharacterGeneratorSet paperSplitHaarAction
        splitCharacterCoefficient) =
      (crossedProductModel paperSplitHaarAction).algebra :=
  crossed_character_vonNeumannClosure_eq_full_of_multipliers
    paperSplitHaarAction splitCharacterCoefficient
    splitMultiplier_mem_character_vonNeumannClosure

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal NNReal

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure SplitAbelianExtension
    (A : Type u) [AddCommGroup A]
    (G H : CountableDiscreteGroup.{u}) where
  /-- Inclusion of the abelian kernel. -/
  inclusion : Multiplicative A →* G
  /-- Projection to the quotient group. -/
  quotient : G →* H
  /-- A multiplicative splitting of the quotient. -/
  splitting : H →* G
  quotient_splitting : quotient.comp splitting = MonoidHom.id H
  exact : quotient.ker = inclusion.range
  /-- The induced action of the quotient on the kernel. -/
  action : H →* Multiplicative (AddAut A)
  conjugation : ∀ (h : H) (a : A),
    splitting h * inclusion (Multiplicative.ofAdd a) * (splitting h)⁻¹ =
      inclusion (Multiplicative.ofAdd
        ((Multiplicative.toAdd (action h)) a))

namespace SplitAbelianExtension

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem quotient_splitting_apply
    (E : SplitAbelianExtension A G H) (h : H) :
    E.quotient (E.splitting h) = h := by
  have heq := DFunLike.congr_fun E.quotient_splitting h
  exact heq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_kernel_mul_splitting
    (E : SplitAbelianExtension A G H) (g : G) :
    ∃ (a : A) (h : H),
      g = E.inclusion (Multiplicative.ofAdd a) * E.splitting h := by
  have hkernel : g * (E.splitting (E.quotient g))⁻¹ ∈ E.quotient.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, quotient_splitting_apply, mul_inv_cancel]
  rw [E.exact] at hkernel
  obtain ⟨a, ha⟩ := hkernel
  refine ⟨Multiplicative.toAdd a, E.quotient g, ?_⟩
  calc
    g = (g * (E.splitting (E.quotient g))⁻¹) *
      E.splitting (E.quotient g) := by simp only [inv_mul_cancel_right]
    _ = E.inclusion a * E.splitting (E.quotient g) := by rw [← ha]

end SplitAbelianExtension

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev DiscreteCharacterSpace (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] :=
  PontryaginDual (Multiplicative A)

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (χ : DiscreteCharacterSpace A) : DiscreteCharacterSpace A where
  toFun a := χ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (action h⁻¹)) (Multiplicative.toAdd a)))
  map_one' := by simp only [map_inv, toAdd_inv, toAdd_one, map_zero, ofAdd_zero, map_one]
  map_mul' a b := by
    change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹))
        (Multiplicative.toAdd a + Multiplicative.toAdd b))) = _
    rw [map_add]
    exact map_mul χ _ _
  continuous_toFun := continuous_of_discreteTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem dualCharacterAction_trivial
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    dualCharacterAction action h (1 : DiscreteCharacterSpace A) = 1 := by
  ext a
  rfl

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsInvariantSpectralMeasure
    (action : H →* Multiplicative (AddAut A))
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : Prop :=
  ∀ h : H,
    (μ : Measure (DiscreteCharacterSpace A)).map
      (dualCharacterAction action h) = μ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralTrivialAtom
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : ℝ :=
  (μ : Measure (DiscreteCharacterSpace A)).real {1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralDetectionEnergy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) : ℝ :=
  ∫ χ : DiscreteCharacterSpace A,
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
      ∂(μ : Measure (DiscreteCharacterSpace A))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure QuotientFixedUnitVector
    (E : SplitAbelianExtension A G H)
    (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) where
  vector : V
  norm_one : ‖vector‖ = 1
  quotient_fixed : ∀ h : H,
    (π (E.splitting h) : V →L[ℂ] V) vector = vector

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure SpectralMeasureInterface
    (E : SplitAbelianExtension A G H)
    (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) where
  quotient_fixed_approximation :
    HasKazhdanPropertyT H →
      π.HasAlmostInvariantUnitVectors →
        ∀ (J : Finset A) (ε : ℝ), 0 < ε →
          ∃ ξ : QuotientFixedUnitVector E V π,
            (∑ a ∈ J,
              ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
                  ξ.vector - ξ.vector‖ ^ 2) < ε
  measure : QuotientFixedUnitVector E V π →
    ProbabilityMeasure (DiscreteCharacterSpace A)
  measure_invariant : ∀ ξ,
    IsInvariantSpectralMeasure E.action (measure ξ)
  energy_eq : ∀ (ξ : QuotientFixedUnitVector E V π) (a : A),
    spectralDetectionEnergy (measure ξ) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          ξ.vector - ξ.vector‖ ^ 2
  positive_atom_invariant :
    ∀ ξ : QuotientFixedUnitVector E V π,
      0 < spectralTrivialAtom (measure ξ) →
        ∃ η : V, η ≠ 0 ∧
          (∀ a : A,
            (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) η = η) ∧
          (∀ h : H, (π (E.splitting h) : V →L[ℂ] V) η = η)

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem invariant_of_kernel_and_quotient
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (ξ : V)
    (hkernel : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) ξ = ξ)
    (hquotient : ∀ h : H,
      (π (E.splitting h) : V →L[ℂ] V) ξ = ξ) :
    π.IsInvariant ξ := by
  intro g
  obtain ⟨a, h, rfl⟩ := E.exists_kernel_mul_splitting g
  rw [map_mul]
  change
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
      ((π (E.splitting h) : V →L[ℂ] V) ξ) = ξ
  rw [hquotient h, hkernel a]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasFiniteSpectralDetection
    (E : SplitAbelianExtension A G H) (J : Finset A) (c : ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure (DiscreteCharacterSpace A),
    IsInvariantSpectralMeasure E.action μ →
      c * (1 - spectralTrivialAtom μ) ≤
        ∑ a ∈ J, spectralDetectionEnergy μ a

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_positive_spectral_atom
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V)
    (spectral : SpectralMeasureInterface E V π)
    (hH : HasKazhdanPropertyT H)
    (hπ : π.HasAlmostInvariantUnitVectors)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c) :
    ∃ ξ : QuotientFixedUnitVector E V π,
      0 < spectralTrivialAtom (spectral.measure ξ) := by
  obtain ⟨ξ, hsmall⟩ :=
    spectral.quotient_fixed_approximation hH hπ J c hc
  refine ⟨ξ, ?_⟩
  have hdet := hdetection (spectral.measure ξ)
    (spectral.measure_invariant ξ)
  simp_rw [spectral.energy_eq] at hdet
  nlinarith

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectral_criterion_representation
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V)
    (spectral : SpectralMeasureInterface E V π)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    ∃ ξ : V, ξ ≠ 0 ∧ π.IsInvariant ξ := by
  obtain ⟨ξ, hatom⟩ :=
    exists_positive_spectral_atom E π spectral hH hπ J hc hdetection
  obtain ⟨η, hη, hkernel, hquotient⟩ :=
    spectral.positive_atom_invariant ξ hatom
  exact ⟨η, hη, invariant_of_kernel_and_quotient E π η hkernel hquotient⟩

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectral_criterion
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (spectral : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        SpectralMeasureInterface E V π) :
    HasKazhdanPropertyT G := by
  intro V _ _ _ π hπ
  exact spectral_criterion_representation E π
    (spectral V inferInstance inferInstance inferInstance π)
    hH J hc hdetection hπ

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal NNReal

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure ProjectionValuedSpectralMeasure
    (E : SplitAbelianExtension A G H)
    (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) where
  /-- The projection assigned to each measurable set. -/
  projection : Set (DiscreteCharacterSpace A) → (V →L[ℂ] V)
  projection_empty : projection ∅ = 0
  projection_univ : projection Set.univ = 1
  projection_inter : ∀ s t,
    MeasurableSet s → MeasurableSet t →
      projection (s ∩ t) = (projection s).comp (projection t)
  projection_self_adjoint : ∀ s, MeasurableSet s →
    ∀ x y : V,
      inner ℂ (projection s x) y = inner ℂ x (projection s y)
  projection_iUnion : ∀ (s : ℕ → Set (DiscreteCharacterSpace A)),
    (∀ n, MeasurableSet (s n)) →
    (∀ i j, i ≠ j → Disjoint (s i) (s j)) →
      ∀ x : V,
        HasSum (fun n ↦ projection (s n) x) (projection (⋃ n, s n) x)
  /-- The scalar measure associated with each vector. -/
  scalar : V → Measure (DiscreteCharacterSpace A)
  scalar_apply : ∀ (x : V) (s : Set (DiscreteCharacterSpace A)),
    MeasurableSet s →
      (scalar x).real s = (inner ℂ x (projection s x)).re
  projection_covariance : ∀ (h : H) (s : Set (DiscreteCharacterSpace A))
    (x : V),
      (π (E.splitting h) : V →L[ℂ] V) (projection s x) =
        projection (dualCharacterAction E.action h '' s)
          ((π (E.splitting h) : V →L[ℂ] V) x)
  scalar_covariance : ∀ (h : H) (x : V),
    (scalar x).map (dualCharacterAction E.action h) =
      scalar ((π (E.splitting h) : V →L[ℂ] V) x)
  kernel_eigenprojection : ∀ (a : A) (χ : DiscreteCharacterSpace A) (x : V),
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        (projection {χ} x) =
      (((χ (Multiplicative.ofAdd a) : Circle) : ℂ) • projection {χ} x)
  energy_identity : ∀ (x : V) (a : A),
    (∫ χ : DiscreteCharacterSpace A,
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
        ∂(scalar x)) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x - x‖ ^ 2

namespace ProjectionValuedSpectralMeasure

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scalar_univ_real
    (P : ProjectionValuedSpectralMeasure E V π) (x : V) :
    (P.scalar x).real Set.univ = ‖x‖ ^ 2 := by
  rw [P.scalar_apply x Set.univ MeasurableSet.univ, P.projection_univ]
  simpa only [one_apply_eq_self, inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap,
    RCLike.re_to_complex] using (inner_self_eq_norm_sq (𝕜 := ℂ) x)

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem scalar_isProbabilityMeasure
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : V) (hx : ‖x‖ = 1) :
    IsProbabilityMeasure (P.scalar x) where
  measure_univ := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    change (P.scalar x).real Set.univ = 1
    rw [P.scalar_univ_real x, hx]
    norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def probabilityMeasure
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : V) (hx : ‖x‖ = 1) :
    ProbabilityMeasure (DiscreteCharacterSpace A) :=
  ⟨P.scalar x, P.scalar_isProbabilityMeasure x hx⟩

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem probabilityMeasure_invariant
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : QuotientFixedUnitVector E V π) :
    IsInvariantSpectralMeasure E.action
      (P.probabilityMeasure x.vector x.norm_one) := by
  intro h
  change (P.scalar x.vector).map (dualCharacterAction E.action h) =
    P.scalar x.vector
  rw [P.scalar_covariance h x.vector, x.quotient_fixed h]

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem probabilityMeasure_energy
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : QuotientFixedUnitVector E V π) (a : A) :
    spectralDetectionEnergy
        (P.probabilityMeasure x.vector x.norm_one) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          x.vector - x.vector‖ ^ 2 := by
  exact P.energy_identity x.vector a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialProjection_ne_zero_of_atom_pos
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (P.probabilityMeasure x.vector x.norm_one)) :
    P.projection {1} x.vector ≠ 0 := by
  intro hzero
  have hatom := P.scalar_apply x.vector {1} (measurableSet_singleton 1)
  change (P.scalar x.vector).real {1} =
    (inner ℂ x.vector (P.projection {1} x.vector)).re at hatom
  rw [hzero, inner_zero_right] at hatom
  change 0 < (P.scalar x.vector).real {1} at hx
  rw [hatom] at hx
  norm_num at hx

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialProjection_kernel_fixed
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : V) (a : A) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        (P.projection {1} x) = P.projection {1} x := by
  simpa only [PontryaginDual.one_apply, Circle.coe_one,
    one_smul] using P.kernel_eigenprojection a 1 x

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialProjection_quotient_fixed
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : QuotientFixedUnitVector E V π) (h : H) :
    (π (E.splitting h) : V →L[ℂ] V)
      (P.projection {1} x.vector) = P.projection {1} x.vector := by
  have hcov := P.projection_covariance h {1} x.vector
  simpa only [Set.image_singleton, dualCharacterAction_trivial, x.quotient_fixed h] using hcov

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem positive_atom_invariant
    (P : ProjectionValuedSpectralMeasure E V π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (P.probabilityMeasure x.vector x.norm_one)) :
    ∃ η : V, η ≠ 0 ∧
      (∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) η = η) ∧
      (∀ h : H,
        (π (E.splitting h) : V →L[ℂ] V) η = η) := by
  refine ⟨P.projection {1} x.vector,
    P.trivialProjection_ne_zero_of_atom_pos x hx, ?_, ?_⟩
  · exact P.trivialProjection_kernel_fixed x.vector
  · exact P.trivialProjection_quotient_fixed x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasQuotientFixedApproximation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : Prop :=
  HasKazhdanPropertyT H →
    π.HasAlmostInvariantUnitVectors →
      ∀ (J : Finset A) (ε : ℝ), 0 < ε →
        ∃ x : QuotientFixedUnitVector E V π,
          (∑ a ∈ J,
            ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
                x.vector - x.vector‖ ^ 2) < ε

end ProjectionValuedSpectralMeasure

end

section

open ConnesRigidity

universe u v

variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def normalizedVector (p : W) : W := ((‖p‖ : ℂ)⁻¹) • p

omit [CompleteSpace W] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_norm (p : W) (hp : p ≠ 0) :
    ‖normalizedVector p‖ = 1 := by
  have hpNorm : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  rw [normalizedVector, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg p), inv_mul_cancel₀ hpNorm]

omit [CompleteSpace W] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_rescale (p : W) (hp : p ≠ 0) :
    (‖p‖ : ℂ) • normalizedVector p = p := by
  have hpNorm : (‖p‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hp
  simp only [normalizedVector, smul_smul, ne_eq, hpNorm, not_false_eq_true, mul_inv_cancel₀,
    one_smul]

omit [InnerProductSpace ℂ W] [CompleteSpace W] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem ne_zero_of_distance_lt_one_of_unit
    (ξ p : W) (hξ : ‖ξ‖ = 1) (hclose : ‖p - ξ‖ < 1) :
    p ≠ 0 := by
  intro hp
  rw [hp, zero_sub, norm_neg, hξ] at hclose
  exact (lt_irrefl 1) hclose

omit [CompleteSpace W] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_sub_self_norm_le
    (ξ p : W) (hξ : ‖ξ‖ = 1) (hp : p ≠ 0) :
    ‖normalizedVector p - p‖ ≤ ‖p - ξ‖ := by
  have hrewrite : normalizedVector p - p =
      ((1 : ℂ) - (‖p‖ : ℂ)) • normalizedVector p := by
    rw [sub_smul, one_smul, normalizedVector_rescale p hp]
  rw [hrewrite, norm_smul, normalizedVector_norm p hp, mul_one]
  have hreal : ((1 : ℂ) - (‖p‖ : ℂ)) = ((1 - ‖p‖ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  have hbound := abs_norm_sub_norm_le ξ p
  rw [hξ, norm_sub_rev] at hbound
  exact hbound

omit [CompleteSpace W] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_sub_unit_norm_le
    (ξ p : W) (hξ : ‖ξ‖ = 1) (hp : p ≠ 0) :
    ‖normalizedVector p - ξ‖ ≤ 2 * ‖p - ξ‖ := by
  calc
    ‖normalizedVector p - ξ‖ =
        ‖(normalizedVector p - p) + (p - ξ)‖ := by
          congr 1
          abel
    _ ≤ ‖normalizedVector p - p‖ + ‖p - ξ‖ := norm_add_le _ _
    _ ≤ 2 * ‖p - ξ‖ := by
      linarith [normalizedVector_sub_self_norm_le ξ p hξ hp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_fixed
    (U : unitary (W →L[ℂ] W)) (p : W)
    (hfix : (U : W →L[ℂ] W) p = p) :
    (U : W →L[ℂ] W) (normalizedVector p) = normalizedVector p := by
  simp only [normalizedVector, map_smul, hfix]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitary_displacement_le_of_distance
    (U : unitary (W →L[ℂ] W)) (ξ x : W) :
    ‖(U : W →L[ℂ] W) x - x‖ ≤
      ‖(U : W →L[ℂ] W) ξ - ξ‖ + 2 * ‖x - ξ‖ := by
  calc
    ‖(U : W →L[ℂ] W) x - x‖ =
        ‖(U : W →L[ℂ] W) (x - ξ) +
            ((U : W →L[ℂ] W) ξ - ξ) + (ξ - x)‖ := by
          congr 1
          rw [map_sub]
          abel
    _ ≤ ‖(U : W →L[ℂ] W) (x - ξ) +
          ((U : W →L[ℂ] W) ξ - ξ)‖ + ‖ξ - x‖ :=
      norm_add_le _ _
    _ ≤ (‖(U : W →L[ℂ] W) (x - ξ)‖ +
          ‖(U : W →L[ℂ] W) ξ - ξ‖) + ‖ξ - x‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = ‖(U : W →L[ℂ] W) ξ - ξ‖ + 2 * ‖x - ξ‖ := by
      rw [Unitary.norm_map U, norm_sub_rev ξ x]
      ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedVector_unitary_displacement_le
    (U : unitary (W →L[ℂ] W)) (ξ p : W)
    (hξ : ‖ξ‖ = 1) (hp : p ≠ 0) :
    ‖(U : W →L[ℂ] W) (normalizedVector p) - normalizedVector p‖ ≤
      ‖(U : W →L[ℂ] W) ξ - ξ‖ + 4 * ‖p - ξ‖ := by
  calc
    ‖(U : W →L[ℂ] W) (normalizedVector p) - normalizedVector p‖ ≤
        ‖(U : W →L[ℂ] W) ξ - ξ‖ +
          2 * ‖normalizedVector p - ξ‖ :=
      unitary_displacement_le_of_distance U ξ (normalizedVector p)
    _ ≤ ‖(U : W →L[ℂ] W) ξ - ξ‖ + 4 * ‖p - ξ‖ := by
      linarith [normalizedVector_sub_unit_norm_le ξ p hξ hp]

end

section

open ConnesRigidity

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def quotientFixedSubmodule
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : Submodule ℂ V :=
  ⨅ h : H,
    LinearMap.ker
      (((π (E.splitting h) : V →L[ℂ] V) -
        ContinuousLinearMap.id ℂ V).toLinearMap)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_quotientFixedSubmodule
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    x ∈ quotientFixedSubmodule E π ↔
      ∀ h : H, (π (E.splitting h) : V →L[ℂ] V) x = x := by
  simp only [quotientFixedSubmodule, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.coe_id, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    ContinuousLinearMap.coe_coe, LinearMap.id_coe, id_eq, sub_eq_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedSubmodule_isClosed
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    IsClosed (quotientFixedSubmodule E π : Set V) := by
  rw [quotientFixedSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun h ↦
    (((π (E.splitting h) : V →L[ℂ] V) -
      ContinuousLinearMap.id ℂ V).isClosed_ker)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance quotientFixedSubmodule_completeSpace
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    CompleteSpace (quotientFixedSubmodule E π) :=
  (quotientFixedSubmodule_isClosed E π).isComplete.completeSpace_coe

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedOrthogonal_mem
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (h : H) {x : V} (hx : x ∈ (quotientFixedSubmodule E π)ᗮ) :
    (π (E.splitting h) : V →L[ℂ] V) x ∈
      (quotientFixedSubmodule E π)ᗮ := by
  apply ((quotientFixedSubmodule E π).mem_orthogonal _).mpr
  intro y hy
  have hyfixed := (mem_quotientFixedSubmodule E π y).mp hy h
  calc
    @inner ℂ V _ y ((π (E.splitting h) : V →L[ℂ] V) x) =
        @inner ℂ V _ ((π (E.splitting h) : V →L[ℂ] V) y)
          ((π (E.splitting h) : V →L[ℂ] V) x) := by rw [hyfixed]
    _ = @inner ℂ V _ y x := Unitary.inner_map_map (π (E.splitting h)) y x
    _ = 0 := ((quotientFixedSubmodule E π).mem_orthogonal x).mp hx y hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientFixedProjection
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : V →L[ℂ] V :=
  (quotientFixedSubmodule E π).starProjection

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedProjection_mem
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    quotientFixedProjection E π x ∈ quotientFixedSubmodule E π :=
  Submodule.starProjection_apply_mem _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedProjection_fixed
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) (h : H) :
    (π (E.splitting h) : V →L[ℂ] V)
        (quotientFixedProjection E π x) =
      quotientFixedProjection E π x :=
  (mem_quotientFixedSubmodule E π _).mp
    (quotientFixedProjection_mem E π x) h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientFixedOrthogonalIsometry
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    (quotientFixedSubmodule E π)ᗮ ≃ₗᵢ[ℂ]
      (quotientFixedSubmodule E π)ᗮ where
  toFun x := ⟨(π (E.splitting h) : V →L[ℂ] V) x,
    quotientFixedOrthogonal_mem E π h x.property⟩
  invFun x := ⟨(π (E.splitting h⁻¹) : V →L[ℂ] V) x,
    quotientFixedOrthogonal_mem E π h⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change
      (↑(π (E.splitting h⁻¹) * π (E.splitting h)) :
        V →L[ℂ] V) x = x
    rw [← map_mul, ← map_mul]
    simp only [inv_mul_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    apply Subtype.ext
    change
      (↑(π (E.splitting h) * π (E.splitting h⁻¹)) :
        V →L[ℂ] V) x = x
    rw [← map_mul, ← map_mul]
    simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (π (E.splitting h) : V →L[ℂ] V) (x : V) (y : V)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (π (E.splitting h) : V →L[ℂ] V) c (x : V)
  norm_map' x := Unitary.norm_map (π (E.splitting h)) x



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientFixedOrthogonalIsometryHom
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    H →* ((quotientFixedSubmodule E π)ᗮ ≃ₗᵢ[ℂ]
      (quotientFixedSubmodule E π)ᗮ) where
  toFun := quotientFixedOrthogonalIsometry E π
  map_one' := by
    ext x
    change (π (E.splitting 1) : V →L[ℂ] V) x = x
    simp only [map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    ext x
    change
      (π (E.splitting (g * h)) : V →L[ℂ] V) x =
        (π (E.splitting g) : V →L[ℂ] V)
          ((π (E.splitting h) : V →L[ℂ] V) x)
    rw [map_mul, map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientFixedOrthogonalRepresentation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    UnitaryRepresentation H (quotientFixedSubmodule E π)ᗮ :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (quotientFixedOrthogonalIsometryHom E π)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedOrthogonal_no_nonzero_invariant
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (x : (quotientFixedSubmodule E π)ᗮ)
    (hx : (quotientFixedOrthogonalRepresentation E π).IsInvariant x) :
    x = 0 := by
  have hfixed : (x : V) ∈ quotientFixedSubmodule E π := by
    apply (mem_quotientFixedSubmodule E π (x : V)).mpr
    intro h
    exact congrArg
      (fun y : (quotientFixedSubmodule E π)ᗮ => (y : V)) (hx h)
  apply Subtype.ext
  change (x : V) = 0
  exact inner_self_eq_zero.mp
    (((quotientFixedSubmodule E π).mem_orthogonal (x : V)).mp
      x.property x hfixed)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedOrthogonal_spectralGap
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (hH : HasKazhdanPropertyT H) :
    ∃ (F : Finset H) (δ : ℝ), 0 < δ ∧
      ∀ x : (quotientFixedSubmodule E π)ᗮ, ‖x‖ = 1 →
        ∃ h ∈ F,
          δ ≤ ‖(π (E.splitting h) : V →L[ℂ] V) (x : V) -
            (x : V)‖ := by
  have hno :
      ¬ (quotientFixedOrthogonalRepresentation E π).HasAlmostInvariantUnitVectors := by
    intro halmost
    obtain ⟨x, hxzero, hxinvariant⟩ :=
      hH (quotientFixedSubmodule E π)ᗮ
        inferInstance inferInstance inferInstance
        (quotientFixedOrthogonalRepresentation E π) halmost
    exact hxzero
      (quotientFixedOrthogonal_no_nonzero_invariant E π x hxinvariant)
  unfold ConnesRigidity.UnitaryRepresentation.HasAlmostInvariantUnitVectors at hno
  push Not at hno
  obtain ⟨F, δ, hδ, hgap⟩ := hno
  refine ⟨F, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨h, hh, hbound⟩ := hgap x hx
  exact ⟨h, hh, hbound⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixed_spectralGap
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (hH : HasKazhdanPropertyT H) :
    ∃ (F : Finset H) (δ : ℝ), 0 < δ ∧
      ∀ x : V, x ∈ (quotientFixedSubmodule E π)ᗮ → ‖x‖ = 1 →
        ∃ h ∈ F,
          δ ≤ ‖(π (E.splitting h) : V →L[ℂ] V) x - x‖ := by
  obtain ⟨F, δ, hδ, hgap⟩ := quotientFixedOrthogonal_spectralGap E π hH
  refine ⟨F, δ, hδ, ?_⟩
  intro x hx hnorm
  exact hgap ⟨x, hx⟩ hnorm

end

section

open ConnesRigidity

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientProjection_error_lt_of_spectralGap
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (M : Submodule ℂ V) [M.HasOrthogonalProjection]
    (hM : ∀ (v : V),
      v ∈ M ↔ ∀ h : H,
        (π (E.splitting h) : V →L[ℂ] V) v = v)
    (F : Finset H) {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ)
    (gap : ∀ z : V, z ∈ Mᗮ → ‖z‖ = 1 →
      ∃ h ∈ F,
        κ ≤ ‖(π (E.splitting h) : V →L[ℂ] V) z - z‖)
    (ξ : V)
    (hξ : ∀ h ∈ F,
      ‖(π (E.splitting h) : V →L[ℂ] V) ξ - ξ‖ < κ * θ) :
    ‖ξ - M.starProjection ξ‖ < θ := by
  classical
  let z : V := ξ - M.starProjection ξ
  have hzmem : z ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal ξ
  by_contra hnot
  have hzlower : θ ≤ ‖z‖ := le_of_not_gt hnot
  have hz : z ≠ 0 := by
    intro hzzero
    simp only [hzzero, norm_zero] at hzlower
    linarith
  let w : V := ((‖z‖ : ℂ)⁻¹) • z
  have hwmem : w ∈ Mᗮ := (Mᗮ).smul_mem _ hzmem
  have hwnorm : ‖w‖ = 1 := norm_smul_inv_norm hz
  obtain ⟨h, hh, hgap⟩ := gap w hwmem hwnorm
  have hpfix :
      (π (E.splitting h) : V →L[ℂ] V) (M.starProjection ξ) =
        M.starProjection ξ :=
    (hM _).mp (Submodule.starProjection_apply_mem M ξ) h
  have hdisplacement :
      (π (E.splitting h) : V →L[ℂ] V) z - z =
        (π (E.splitting h) : V →L[ℂ] V) ξ - ξ := by
    dsimp [z]
    rw [map_sub, hpfix]
    abel
  have hwnorm_formula :
      ‖(π (E.splitting h) : V →L[ℂ] V) w - w‖ =
        ‖(π (E.splitting h) : V →L[ℂ] V) z - z‖ / ‖z‖ := by
    dsimp [w]
    rw [map_smul, ← smul_sub, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    simp only [div_eq_mul_inv, mul_comm]
  rw [hwnorm_formula] at hgap
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hgap' : κ * ‖z‖ ≤
      ‖(π (E.splitting h) : V →L[ℂ] V) z - z‖ :=
    (le_div_iff₀ hzpos).mp hgap
  rw [hdisplacement] at hgap'
  have hsmall := hξ h hh
  nlinarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedApproximation_of_uniform
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (uniform :
      HasKazhdanPropertyT H →
      π.HasAlmostInvariantUnitVectors →
      ∀ (S : Finset G) (δ : ℝ), 0 < δ →
        ∃ x : QuotientFixedUnitVector E V π,
          ∀ g ∈ S, ‖(π g : V →L[ℂ] V) x.vector - x.vector‖ < δ) :
    ProjectionValuedSpectralMeasure.HasQuotientFixedApproximation E π := by
  classical
  intro hH hπ J ε hε
  let denominator : ℝ := (J.card : ℝ) + 1
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  let δ : ℝ := min 1 (ε / denominator)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hdenominator)
  obtain ⟨x, hx⟩ := uniform hH hπ
    (J.image (fun a ↦ E.inclusion (Multiplicative.ofAdd a))) δ hδ
  refine ⟨x, ?_⟩
  calc
    (∑ a ∈ J,
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          x.vector - x.vector‖ ^ 2)
        ≤ ∑ _a ∈ J, ε / denominator := by
          apply Finset.sum_le_sum
          intro a ha
          have ha' := hx (E.inclusion (Multiplicative.ofAdd a))
            (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
          have hnonneg :
              0 ≤ ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
                x.vector - x.vector‖ := norm_nonneg _
          have hδone : δ ≤ 1 := min_le_left _ _
          have hδenergy : δ ≤ ε / denominator := min_le_right _ _
          nlinarith [sq_nonneg
            (‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
              x.vector - x.vector‖)]
    _ = (J.card : ℝ) * (ε / denominator) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hdenominator]
      dsimp [denominator]
      linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedUnitVector_uniform
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (hH : HasKazhdanPropertyT H)
    (hπ : π.HasAlmostInvariantUnitVectors)
    (S : Finset G) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : QuotientFixedUnitVector E V π,
      ∀ g ∈ S, ‖(π g : V →L[ℂ] V) x.vector - x.vector‖ < ε := by
  classical
  obtain ⟨F, κ, hκ, hgap⟩ := quotientFixed_spectralGap E π hH
  let θ : ℝ := min (ε / 8) (1 / 4)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  let τ : ℝ := min θ (κ * θ)
  have hτ : 0 < τ := lt_min hθ (mul_pos hκ hθ)
  obtain ⟨ξ, hξunit, hξ⟩ :=
    hπ (S ∪ F.image E.splitting) τ hτ
  let p : V := quotientFixedProjection E π ξ
  have herr : ‖ξ - p‖ < θ := by
    change ‖ξ - (quotientFixedSubmodule E π).starProjection ξ‖ < θ
    apply quotientProjection_error_lt_of_spectralGap E π
      (quotientFixedSubmodule E π)
      (mem_quotientFixedSubmodule E π) F hκ hθ hgap ξ
    intro h hh
    exact lt_of_lt_of_le
      (hξ (E.splitting h)
        (Finset.mem_union_right S
          (Finset.mem_image.mpr ⟨h, hh, rfl⟩)))
      (min_le_right _ _)
  have hpclose : ‖p - ξ‖ < 1 := by
    rw [norm_sub_rev]
    have hθquarter : θ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hp : p ≠ 0 :=
    ne_zero_of_distance_lt_one_of_unit ξ p hξunit hpclose
  let x : QuotientFixedUnitVector E V π :=
    { vector := normalizedVector p
      norm_one := normalizedVector_norm p hp
      quotient_fixed := by
        intro h
        exact normalizedVector_fixed (π (E.splitting h)) p
          (quotientFixedProjection_fixed E π ξ h) }
  refine ⟨x, ?_⟩
  intro g hg
  have hξg := hξ g (Finset.mem_union_left _ hg)
  have hxg := normalizedVector_unitary_displacement_le
    (π g) ξ p hξunit hp
  have hτθ : τ ≤ θ := min_le_left _ _
  have hθε : θ ≤ ε / 8 := min_le_left _ _
  have hpξ : ‖p - ξ‖ < θ := by
    rw [norm_sub_rev]
    exact herr
  change ‖(π g : V →L[ℂ] V) (normalizedVector p) -
    normalizedVector p‖ < ε
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFixedApproximation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    ProjectionValuedSpectralMeasure.HasQuotientFixedApproximation E π :=
  quotientFixedApproximation_of_uniform E π
    (quotientFixedUnitVector_uniform E π)

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal NNReal CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_character_evaluation (a : A) :
    Continuous (fun χ : DiscreteCharacterSpace A ↦
      ((χ (Multiplicative.ofAdd a) : Circle) : ℂ)) := by
  change Continuous (fun χ : Multiplicative A →ₜ* Circle ↦
    ((χ (Multiplicative.ofAdd a) : Circle) : ℂ))
  exact continuous_subtype_val.comp
    (continuous_eval_const (Multiplicative.ofAdd a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralUnitTest (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun _ := 1
  continuous_toFun := continuous_const
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem spectralUnitTest_apply (χ : DiscreteCharacterSpace A) :
    spectralUnitTest A χ = 1 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralEnergyTest (a : A) :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun χ := ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
  continuous_toFun :=
    ((continuous_character_evaluation a).sub continuous_const).norm.pow 2
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem spectralEnergyTest_apply
    (a : A) (χ : DiscreteCharacterSpace A) :
    spectralEnergyTest a χ =
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure PositiveSpectralFunctional
    (E : SplitAbelianExtension A G H)
    (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) where
  /-- The positive functional associated with each vector. -/
  functional : V → C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ
  normalization : ∀ x : V,
    functional x (spectralUnitTest A) = ‖x‖ ^ 2
  energy : ∀ (x : V) (a : A),
    functional x (spectralEnergyTest a) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x - x‖ ^ 2
  covariance : ∀ (h : H) (x : V),
    (RealRMK.rieszMeasure (functional x)).map
      (dualCharacterAction E.action h) =
        RealRMK.rieszMeasure
          (functional ((π (E.splitting h) : V →L[ℂ] V) x))

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def measure (Φ : PositiveSpectralFunctional E V π) (x : V) :
    Measure (DiscreteCharacterSpace A) :=
  RealRMK.rieszMeasure (Φ.functional x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance measure_regular
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    (Φ.measure x).Regular := by
  unfold measure
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance measure_isFiniteMeasure
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    IsFiniteMeasure (Φ.measure x) := by
  unfold measure
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integral_measure
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    (f : C_c(DiscreteCharacterSpace A, ℝ)) :
    (∫ χ, f χ ∂(Φ.measure x)) = Φ.functional x f := by
  exact RealRMK.integral_rieszMeasure (Φ.functional x) f

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measure_univ_real
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    (Φ.measure x).real Set.univ = ‖x‖ ^ 2 := by
  have h := Φ.integral_measure x (spectralUnitTest A)
  simpa only [spectralUnitTest_apply, integral_const, smul_eq_mul, mul_one,
    Φ.normalization x] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem measure_isProbabilityMeasure
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (hx : ‖x‖ = 1) :
    IsProbabilityMeasure (Φ.measure x) := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [Φ.measure_univ_real x, hx]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def probabilityMeasure
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (hx : ‖x‖ = 1) :
    ProbabilityMeasure (DiscreteCharacterSpace A) :=
  ⟨Φ.measure x, Φ.measure_isProbabilityMeasure x hx⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem measure_energy
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (a : A) :
    (∫ χ : DiscreteCharacterSpace A,
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
        ∂(Φ.measure x)) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x - x‖ ^ 2 := by
  exact (Φ.integral_measure x (spectralEnergyTest a)).trans (Φ.energy x a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem probabilityMeasure_invariant
    (Φ : PositiveSpectralFunctional E V π)
    (x : QuotientFixedUnitVector E V π) :
    IsInvariantSpectralMeasure E.action
      (Φ.probabilityMeasure x.vector x.norm_one) := by
  intro h
  change (Φ.measure x.vector).map (dualCharacterAction E.action h) =
    Φ.measure x.vector
  change
    (RealRMK.rieszMeasure (Φ.functional x.vector)).map
        (dualCharacterAction E.action h) =
      RealRMK.rieszMeasure (Φ.functional x.vector)
  rw [Φ.covariance h x.vector, x.quotient_fixed h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem probabilityMeasure_energy
    (Φ : PositiveSpectralFunctional E V π)
    (x : QuotientFixedUnitVector E V π) (a : A) :
    spectralDetectionEnergy
        (Φ.probabilityMeasure x.vector x.norm_one) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          x.vector - x.vector‖ ^ 2 := by
  exact Φ.measure_energy x.vector a

end PositiveSpectralFunctional

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : Submodule ℂ V :=
  ⨅ a : A,
    LinearMap.ker
      (((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) -
        ContinuousLinearMap.id ℂ V).toLinearMap)

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V) :
    x ∈ kernelFixedSubmodule E π ↔
      ∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x = x := by
  simp only [kernelFixedSubmodule, ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
    LinearMap.id_coe, id_eq, sub_eq_zero]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernelFixedSubmodule_isClosed
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    IsClosed (kernelFixedSubmodule E π : Set V) := by
  rw [kernelFixedSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun a ↦
    (((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) -
      ContinuousLinearMap.id ℂ V).isClosed_ker)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance kernelFixedSubmodule_completeSpace
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    CompleteSpace (kernelFixedSubmodule E π) :=
  (kernelFixedSubmodule_isClosed E π).isComplete.completeSpace_coe

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def trivialCharacterProjection
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : V →L[ℂ] V :=
  (kernelFixedSubmodule E π).starProjection

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem trivialCharacterProjection_kernel_fixed
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V) (a : A) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        (trivialCharacterProjection E π x) =
      trivialCharacterProjection E π x := by
  apply (mem_kernelFixedSubmodule E π _).mp
  exact Submodule.starProjection_apply_mem _ _

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernel_map_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) :
    (kernelFixedSubmodule E π).map
      (Unitary.linearIsometryEquiv
        (π (E.inclusion (Multiplicative.ofAdd a)))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x ∈
        kernelFixedSubmodule E π
    rw [(mem_kernelFixedSubmodule E π x).mp hx a]
    exact hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    exact (mem_kernelFixedSubmodule E π x).mp hx a

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialCharacterProjection_kernel_commutes
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) (x : V) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
      (trivialCharacterProjection E π x) =
        trivialCharacterProjection E π
          ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) := by
  let U := Unitary.linearIsometryEquiv
    (π (E.inclusion (Multiplicative.ofAdd a)))
  have hmap :
      (kernelFixedSubmodule E π).map U.toLinearIsometry.toLinearMap =
        kernelFixedSubmodule E π := by
    change
      (kernelFixedSubmodule E π).map
        (Unitary.linearIsometryEquiv
          (π (E.inclusion
            (Multiplicative.ofAdd a)))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π
    exact kernel_map_kernelFixedSubmodule E π a
  let : ((kernelFixedSubmodule E π).map
      U.toLinearIsometry.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  have hprojection := U.toLinearIsometry.map_starProjection
    (kernelFixedSubmodule E π) x
  change
    U ((kernelFixedSubmodule E π).starProjection x) =
      (kernelFixedSubmodule E π).starProjection (U x)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, hmap] using hprojection

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialCharacterProjection_kernel_orbit
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) (x : V) :
    trivialCharacterProjection E π
      ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) =
        trivialCharacterProjection E π x := by
  rw [← trivialCharacterProjection_kernel_commutes E π a x,
    trivialCharacterProjection_kernel_fixed E π x a]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_preserves_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V)
    (h : H) {x : V} (hx : x ∈ kernelFixedSubmodule E π) :
    (π (E.splitting h) : V →L[ℂ] V) x ∈ kernelFixedSubmodule E π := by
  apply (mem_kernelFixedSubmodule E π _).mpr
  intro a
  let b : A := (Multiplicative.toAdd (E.action h⁻¹)) a
  have haction : (Multiplicative.toAdd (E.action h)) b = a := by
    change (Multiplicative.toAdd (E.action h * E.action h⁻¹)) a = a
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, toAdd_one, AddAut.zero_apply]
  have hconj := E.conjugation h b
  rw [haction] at hconj
  have hcomm :
      E.inclusion (Multiplicative.ofAdd a) * E.splitting h =
        E.splitting h * E.inclusion (Multiplicative.ofAdd b) := by
    calc
      E.inclusion (Multiplicative.ofAdd a) * E.splitting h =
          (E.splitting h * E.inclusion (Multiplicative.ofAdd b) *
            (E.splitting h)⁻¹) * E.splitting h := by rw [hconj]
      _ = E.splitting h * E.inclusion (Multiplicative.ofAdd b) := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hfixed := (mem_kernelFixedSubmodule E π x).mp hx b
  calc
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        ((π (E.splitting h) : V →L[ℂ] V) x) =
      (π (E.inclusion (Multiplicative.ofAdd a) * E.splitting h) :
        V →L[ℂ] V) x := by rw [map_mul]; rfl
    _ = (π (E.splitting h * E.inclusion (Multiplicative.ofAdd b)) :
        V →L[ℂ] V) x := by rw [hcomm]
    _ = (π (E.splitting h) : V →L[ℂ] V)
          ((π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V) x) := by
        rw [map_mul]
        rfl
    _ = (π (E.splitting h) : V →L[ℂ] V) x := by rw [hfixed]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_map_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (h : H) :
    (kernelFixedSubmodule E π).map
      (Unitary.linearIsometryEquiv (π (E.splitting h))).toLinearEquiv.toLinearMap =
        kernelFixedSubmodule E π := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact quotient_preserves_kernelFixedSubmodule E π h hx
  · intro x hx
    refine ⟨(π (E.splitting h⁻¹) : V →L[ℂ] V) x,
      quotient_preserves_kernelFixedSubmodule E π h⁻¹ hx, ?_⟩
    change
      (π (E.splitting h) : V →L[ℂ] V)
        ((π (E.splitting h⁻¹) : V →L[ℂ] V) x) = x
    have hop :
        π (E.splitting h) * π (E.splitting h⁻¹) = 1 := by
      rw [← map_mul, ← map_mul]
      simp only [mul_inv_cancel, map_one]
    have hx' := DFunLike.congr_fun
      (congrArg (fun U : unitary (V →L[ℂ] V) ↦ (U : V →L[ℂ] V)) hop) x
    exact hx'

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialCharacterProjection_quotient_commutes
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (h : H) (x : V) :
    (π (E.splitting h) : V →L[ℂ] V)
      (trivialCharacterProjection E π x) =
        trivialCharacterProjection E π
          ((π (E.splitting h) : V →L[ℂ] V) x) := by
  let U := Unitary.linearIsometryEquiv (π (E.splitting h))
  have hmap :
      (kernelFixedSubmodule E π).map U.toLinearIsometry.toLinearMap =
        kernelFixedSubmodule E π := by
    change
      (kernelFixedSubmodule E π).map
        (Unitary.linearIsometryEquiv
          (π (E.splitting h))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π
    exact quotient_map_kernelFixedSubmodule E π h
  let : ((kernelFixedSubmodule E π).map
      U.toLinearIsometry.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  have hprojection := U.toLinearIsometry.map_starProjection
    (kernelFixedSubmodule E π) x
  change
    U ((kernelFixedSubmodule E π).starProjection x) =
      (kernelFixedSubmodule E π).starProjection (U x)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, hmap] using hprojection

end

section
open ConnesRigidity MeasureTheory
open scoped BigOperators CompactlySupported

universe u v

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]
variable {E : SplitAbelianExtension A G H}
variable {π : UnitaryRepresentation G W}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measureReal_singleton_le_integral_of_nonneg
    {Ω : Type v} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (x : Ω)
    (hf : Integrable f μ) (hpos : ∀ y, 0 ≤ f y)
    (hone : 1 ≤ f x) :
    μ.real {x} ≤ ∫ y, f y ∂μ := by
  have hmass : 0 ≤ μ.real {x} := measureReal_nonneg
  calc
    μ.real {x} ≤ μ.real {x} * f x := by nlinarith
    _ = ∫ y in {x}, f y ∂μ := by
      rw [integral_singleton]
      simp only [smul_eq_mul]
    _ ≤ ∫ y, f y ∂μ :=
      setIntegral_le_integral hf (Filter.Eventually.of_forall hpos)

namespace PositiveSpectralFunctional

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivial_atom_le_functional_of_nonneg
    (Φ : PositiveSpectralFunctional E W π) (x : W)
    (f : C_c(DiscreteCharacterSpace A, ℝ))
    (hpos : ∀ χ, 0 ≤ f χ) (hone : 1 ≤ f 1) :
    (Φ.measure x).real {1} ≤ Φ.functional x f := by
  calc
    (Φ.measure x).real {1} ≤ ∫ χ, f χ ∂(Φ.measure x) := by
      apply measureReal_singleton_le_integral_of_nonneg
        (Φ.measure x) (fun χ ↦ f χ) 1
      · exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      · exact hpos
      · exact hone
    _ = Φ.functional x f := Φ.integral_measure x f

end PositiveSpectralFunctional

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernel_orbit_sub_norm
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a b : A) :
    ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
      (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x‖ =
    ‖(π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x‖ := by
  let U := π (E.inclusion (Multiplicative.ofAdd b))
  let z :=
    (π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x
  have hfactor :
      (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
        (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x =
      (U : W →L[ℂ] W) z := by
    dsimp [U, z]
    rw [map_sub]
    congr 1
    change (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x =
      ((π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W)
        ((π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x))
    have hmul :
        E.inclusion (Multiplicative.ofAdd a) =
          E.inclusion (Multiplicative.ofAdd b) *
            E.inclusion (Multiplicative.ofAdd (a - b)) := by
      rw [← map_mul]
      apply congrArg E.inclusion
      apply Multiplicative.toAdd.injective
      change a = b + (a - b)
      abel
    rw [hmul, map_mul]
    rfl
  rw [hfactor]
  exact Unitary.norm_map U z

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernel_orbit_sub_norm_sq
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a b : A) :
    ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
      (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x‖ ^ 2 =
    ‖(π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x‖ ^ 2 := by
  rw [kernel_orbit_sub_norm E π x a b]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem character_sub_norm
    (χ : DiscreteCharacterSpace A) (a b : A) :
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
      ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ =
    ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ := by
  calc
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
        ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ =
      ‖((χ (Multiplicative.ofAdd b) : Circle) : ℂ) *
        (((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one]
      congr 1
      change
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ) =
          ((χ (Multiplicative.ofAdd b) *
            χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ)
      congr 1
      rw [← map_mul]
      apply congrArg χ
      apply Multiplicative.toAdd.injective
      change a = b + (a - b)
      abel
    _ = ‖((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ *
      ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ :=
        norm_mul _ _
    _ = ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ := by
      rw [Circle.norm_coe, one_mul]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem character_sub_norm_sq
    (χ : DiscreteCharacterSpace A) (a b : A) :
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
      ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ ^ 2 =
    ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ ^ 2 := by
  rw [character_sub_norm χ a b]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralFiniteAverageTest
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ) :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun χ :=
    ‖∑ i ∈ s, (w i : ℂ) *
      ((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2
  continuous_toFun := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum s
    intro i _
    exact continuous_const.mul (continuous_character_evaluation (a i))
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem spectralFiniteAverageTest_apply
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (χ : DiscreteCharacterSpace A) :
    spectralFiniteAverageTest s a w χ =
      ‖∑ i ∈ s, (w i : ℂ) *
        ((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2 := rfl

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralFiniteAverageTest_nonneg
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (χ : DiscreteCharacterSpace A) :
    0 ≤ spectralFiniteAverageTest s a w χ := sq_nonneg _

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralFiniteAverageTest_one
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    spectralFiniteAverageTest s a w 1 = 1 := by
  change ‖∑ i ∈ s, (w i : ℂ) *
    (((1 : DiscreteCharacterSpace A)
      (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2 = 1
  have hchar (i : ι) :
      (((1 : DiscreteCharacterSpace A)
        (Multiplicative.ofAdd (a i)) : Circle) : ℂ) = 1 := rfl
  simp_rw [hchar, mul_one]
  rw [← Complex.ofReal_sum, hw]
  norm_num

namespace PositiveSpectralFunctional

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivial_atom_le_finiteAverage_functional
    (Φ : PositiveSpectralFunctional E W π) (x : W)
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    (Φ.measure x).real {1} ≤
      Φ.functional x (spectralFiniteAverageTest s a w) := by
  apply Φ.trivial_atom_le_functional_of_nonneg x
    (spectralFiniteAverageTest s a w)
  · exact spectralFiniteAverageTest_nonneg s a w
  · rw [spectralFiniteAverageTest_one s a w hw]

end PositiveSpectralFunctional

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal NNReal CompactlySupported

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem weighted_norm_sq_eq_sub_pairwise_dist_sq
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Finset ι) (w : ι → ℝ) (v : ι → V)
    (hw : ∑ i ∈ s, w i = 1) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 =
      (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        (1 / 2 : ℝ) *
          ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 := by
  have hinner :
      ‖∑ i ∈ s, w i • v i‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * @inner ℝ V _ (v i) (v j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirst :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i‖ ^ 2) =
        ∑ i ∈ s, w i * ‖v i‖ ^ 2 := by
    simp_rw [show ∀ i j, w i * w j * ‖v i‖ ^ 2 =
      (w i * ‖v i‖ ^ 2) * w j by intros; ring]
    simp_rw [← Finset.mul_sum, hw, mul_one]
  have hsecond :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v j‖ ^ 2) =
        ∑ j ∈ s, w j * ‖v j‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * ‖v j‖ ^ 2 =
      (w j * ‖v j‖ ^ 2) * w i by intros; ring]
    simp_rw [← Finset.mul_sum, hw, mul_one]
  rw [hinner]
  simp_rw [norm_sub_sq_real, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]
  have hcross :
      (∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (2 * @inner ℝ V _ (v i) (v j))) =
        2 * (∑ i ∈ s, ∑ j ∈ s,
          w i * w j * @inner ℝ V _ (v i) (v j)) := by
    simp_rw [show ∀ i j, w i * w j * (2 * @inner ℝ V _ (v i) (v j)) =
      2 * (w i * w j * @inner ℝ V _ (v i) (v j)) by intros; ring]
    simp_rw [← Finset.mul_sum]
  rw [hcross]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Finset ι) (w : ι → ℝ) (v : ι → V) (r : ℝ)
    (hw : ∑ i ∈ s, w i = 1)
    (hv : ∀ i ∈ s, ‖v i‖ = r) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 = r ^ 2 -
      (1 / 2 : ℝ) *
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 := by
  rw [weighted_norm_sq_eq_sub_pairwise_dist_sq s w v hw]
  congr 1
  calc
    (∑ i ∈ s, w i * ‖v i‖ ^ 2) =
        ∑ i ∈ s, w i * r ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi]
    _ = (∑ i ∈ s, w i) * r ^ 2 := by
          rw [Finset.sum_mul]
    _ = r ^ 2 := by rw [hw, one_mul]

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralFiniteAverageTest_eq_sub_energy {ι : Type*}
    (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    spectralFiniteAverageTest s a w = spectralUnitTest A -
      (1 / 2 : ℝ) •
        ∑ i ∈ s, ∑ j ∈ s,
          (w i * w j) • spectralEnergyTest (a i - a j) := by
  ext χ
  have hvariance := weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    s w (fun i ↦ (((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ))) 1 hw
      (fun i _ ↦ Circle.norm_coe _)
  simp only [one_pow, character_sub_norm_sq] at hvariance
  simpa only [spectralFiniteAverageTest_apply, one_div, CompactlySupportedContinuousMap.coe_sub,
    CompactlySupportedContinuousMap.coe_smul, CompactlySupportedContinuousMap.coe_sum, Pi.sub_apply,
    spectralUnitTest_apply, Pi.smul_apply, Finset.sum_apply, spectralEnergyTest_apply, ofAdd_sub,
    map_div, Circle.coe_div, smul_eq_mul, Complex.real_smul] using hvariance

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteAverage_functional_eq_kernel_orbit_norm_sq
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    {ι : Type*} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    Φ.functional x (spectralFiniteAverageTest s a w) =
      ‖∑ i ∈ s, w i •
        ((π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)‖ ^ 2 := by
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  have hvariance := weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    s w
      (fun i ↦
        (π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)
      ‖x‖ hw (fun i _ ↦ Unitary.norm_map _ x)
  simp only [kernel_orbit_sub_norm_sq] at hvariance
  rw [spectralFiniteAverageTest_eq_sub_energy s a w hw]
  simp only [map_sub, map_smul, map_sum, Φ.normalization, Φ.energy,
    smul_eq_mul]
  exact hvariance.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem trivial_atom_le_kernel_orbit_norm_sq
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    {ι : Type*} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    (Φ.measure x).real {1} ≤
      ‖∑ i ∈ s, w i •
        ((π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)‖ ^ 2 := by
  rw [← Φ.finiteAverage_functional_eq_kernel_orbit_norm_sq x s a w hw]
  exact Φ.trivial_atom_le_finiteAverage_functional x s a w hw

end PositiveSpectralFunctional

end

section

open ConnesRigidity MeasureTheory

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasKernelOrbitAffineApproximation
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : Prop :=
  ∀ (x : V), trivialCharacterProjection E π x = 0 →
    ∀ (ε : ℝ), 0 < ε →
      ∃ (s : Finset A) (w : A → ℝ),
        (∑ a ∈ s, w a) = 1 ∧
          ‖∑ a ∈ s, w a •
            ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)‖ < ε

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialCharacterProjection_ne_zero_of_atom_pos_of_orbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (Φ.probabilityMeasure x.vector x.norm_one)) :
    trivialCharacterProjection E π x.vector ≠ 0 := by
  intro hprojection
  change 0 < (Φ.measure x.vector).real {1} at hx
  let ε : ℝ := min 1 ((Φ.measure x.vector).real {1})
  have hε : 0 < ε := lt_min (by norm_num) hx
  obtain ⟨s, w, hw, hsmall⟩ :=
    approximation x.vector hprojection ε hε
  have hbound := Φ.trivial_atom_le_kernel_orbit_norm_sq
    x.vector s (fun a : A ↦ a) w hw
  let z : V := ∑ a ∈ s, w a •
    ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x.vector)
  change (Φ.measure x.vector).real {1} ≤ ‖z‖ ^ 2 at hbound
  change ‖z‖ < ε at hsmall
  have hzone : ‖z‖ < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hzatom : ‖z‖ < (Φ.measure x.vector).real {1} :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hznorm : 0 ≤ ‖z‖ := norm_nonneg _
  linarith [mul_nonneg hznorm (sub_nonneg.mpr (le_of_lt hzone))]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem positive_atom_invariant_of_orbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (Φ.probabilityMeasure x.vector x.norm_one)) :
    ∃ η : V, η ≠ 0 ∧
      (∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) η = η) ∧
      (∀ h : H,
        (π (E.splitting h) : V →L[ℂ] V) η = η) := by
  refine ⟨trivialCharacterProjection E π x.vector,
    Φ.trivialCharacterProjection_ne_zero_of_atom_pos_of_orbitApproximation
      approximation x hx,
    trivialCharacterProjection_kernel_fixed E π x.vector, ?_⟩
  intro h
  rw [trivialCharacterProjection_quotient_commutes E π h x.vector,
    x.quotient_fixed h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def toSpectralMeasureInterfaceOfOrbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π) :
    SpectralMeasureInterface E V π where
  quotient_fixed_approximation := quotientFixedApproximation E π
  measure x := Φ.probabilityMeasure x.vector x.norm_one
  measure_invariant := Φ.probabilityMeasure_invariant
  energy_eq := Φ.probabilityMeasure_energy
  positive_atom_invariant :=
    Φ.positive_atom_invariant_of_orbitApproximation approximation

end PositiveSpectralFunctional

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectral_criterion_of_positive_functional_and_orbitApproximation
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (functional : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        PositiveSpectralFunctional E V π)
    (approximation : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        HasKernelOrbitAffineApproximation E π) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion E hH J hc hdetection
  intro V _ _ _ π
  exact (functional V inferInstance inferInstance inferInstance π)
    |>.toSpectralMeasureInterfaceOfOrbitApproximation
      (approximation V inferInstance inferInstance inferInstance π)

end

section

open ConnesRigidity Metric WeakDual
open scoped CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralOperatorGenerators
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : Set (V →L[ℂ] V) :=
  Set.range fun a : A ↦
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralOperatorAlgebra
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : StarSubalgebra ℂ (V →L[ℂ] V) :=
  (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)).topologicalClosure

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralOperatorGenerators_commute
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    {S T : V →L[ℂ] V}
    (hS : S ∈ spectralOperatorGenerators E π)
    (hT : T ∈ spectralOperatorGenerators E π) : S * T = T * S := by
  obtain ⟨a, rfl⟩ := hS
  obtain ⟨b, rfl⟩ := hT
  have hkernel :
      E.inclusion (Multiplicative.ofAdd a) *
        E.inclusion (Multiplicative.ofAdd b) =
      E.inclusion (Multiplicative.ofAdd b) *
        E.inclusion (Multiplicative.ofAdd a) := by
    rw [← E.inclusion.map_mul, ← E.inclusion.map_mul]
    congr 1
    exact mul_comm _ _
  simpa only [map_mul, Submonoid.coe_mul] using congrArg
    (fun U : unitary (V →L[ℂ] V) ↦ (U : V →L[ℂ] V))
    (congrArg π hkernel)

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem star_mem_spectralOperatorGenerators
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    {T : V →L[ℂ] V}
    (hT : T ∈ spectralOperatorGenerators E π) :
    star T ∈ spectralOperatorGenerators E π := by
  obtain ⟨a, rfl⟩ := hT
  refine ⟨-a, ?_⟩
  change (π (E.inclusion (Multiplicative.ofAdd (-a))) : V →L[ℂ] V) =
    star (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
  change
    (π (E.inclusion ((Multiplicative.ofAdd a)⁻¹)) : V →L[ℂ] V) =
      star (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
  rw [map_inv, map_inv]
  rw [← Unitary.star_eq_inv]
  exact Unitary.coe_star

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance spectralOperatorAdjoin_isMulCommutative
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    IsMulCommutative
      (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · exact fun _ hS _ hT ↦ spectralOperatorGenerators_commute E π hS hT
  · intro S hS T hT
    exact spectralOperatorGenerators_commute E π hS
      (star_mem_spectralOperatorGenerators E π hT)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance spectralOperatorAlgebraCommCStarAlgebra
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    CommCStarAlgebra (spectralOperatorAlgebra E π) := by
  letI : CommRing (spectralOperatorAlgebra E π) :=
    StarSubalgebra.commRingTopologicalClosure _
      (isMulCommutative_iff.mp
        (spectralOperatorAdjoin_isMulCommutative E π))
  letI : IsClosed (spectralOperatorAlgebra E π : Set (V →L[ℂ] V)) :=
    (StarAlgebra.adjoin ℂ
      (spectralOperatorGenerators E π)).isClosed_topologicalClosure
  exact { mul_comm := mul_comm }

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralKernelOperator
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    spectralOperatorAlgebra E π :=
  ⟨(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V),
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩)⟩



omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem spectralKernelOperator_zero
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    spectralKernelOperator E π 0 = 1 := by
  apply Subtype.ext
  simp only [spectralKernelOperator, ofAdd_zero, map_one, OneMemClass.coe_one]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralKernelOperator_add
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a b : A) :
    spectralKernelOperator E π (a + b) =
      spectralKernelOperator E π a * spectralKernelOperator E π b := by
  apply Subtype.ext
  change
    (π (E.inclusion (Multiplicative.ofAdd (a + b))) : V →L[ℂ] V) =
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) *
        (π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V)
  change
    (π (E.inclusion
      (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) :
      V →L[ℂ] V) = _
  rw [E.inclusion.map_mul]
  simp only [map_mul, Submonoid.coe_mul]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralKernelOperator_unitary
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    spectralKernelOperator E π a ∈
      unitary (spectralOperatorAlgebra E π) := by
  rw [Unitary.mem_iff]
  constructor
  · apply Subtype.ext
    exact Unitary.coe_star_mul_self
      (π (E.inclusion (Multiplicative.ofAdd a)))
  · apply Subtype.ext
    exact Unitary.coe_mul_star_self
      (π (E.inclusion (Multiplicative.ofAdd a)))

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem spectralCharacter_generator_mem_circle
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) (a : A) :
    φ (spectralKernelOperator E π a) ∈ sphere (0 : ℂ) 1 := by
  apply mem_sphere_zero_iff_norm.mpr
  exact CStarRing.norm_of_mem_unitary
    (Unitary.map_mem φ (spectralKernelOperator_unitary E π a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralCharacter
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) :
    DiscreteCharacterSpace A where
  toFun a :=
    ⟨φ (spectralKernelOperator E π (Multiplicative.toAdd a)),
      spectralCharacter_generator_mem_circle E π φ
        (Multiplicative.toAdd a)⟩
  map_one' := by
    apply Circle.ext
    change φ (spectralKernelOperator E π 0) = 1
    rw [spectralKernelOperator_zero]
    exact map_one φ
  map_mul' a b := by
    apply Circle.ext
    change
      φ (spectralKernelOperator E π
        (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      φ (spectralKernelOperator E π (Multiplicative.toAdd a)) *
        φ (spectralKernelOperator E π (Multiplicative.toAdd b))
    rw [spectralKernelOperator_add, map_mul]
  continuous_toFun := continuous_of_discreteTopology



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem spectralCharacter_continuous
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    Continuous (spectralCharacter E π) := by
  apply
    (ContinuousMonoidHom.isClosedEmbedding_coe
      (A := Multiplicative A) (B := Circle)).toIsInducing.continuous_iff.mpr
  apply continuous_pi
  intro a
  exact Continuous.subtype_mk
    ((gelfandTransform ℂ (spectralOperatorAlgebra E π)
      (spectralKernelOperator E π (Multiplicative.toAdd a))).continuous) _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralCharacterMap
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    C(characterSpace ℂ (spectralOperatorAlgebra E π),
      DiscreteCharacterSpace A) :=
  ⟨spectralCharacter E π, spectralCharacter_continuous E π⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def jointFunctionalCalculus
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      spectralOperatorAlgebra E π :=
  (gelfandStarTransform (spectralOperatorAlgebra E π)).symm.toStarAlgHom.comp
    ((spectralCharacterMap E π).compStarAlgHom' ℂ ℂ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralCharacterEvaluation
    (a : A) : C(DiscreteCharacterSpace A, ℂ) :=
  ⟨fun χ ↦ ((χ (Multiplicative.ofAdd a) : Circle) : ℂ),
    continuous_character_evaluation a⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem jointFunctionalCalculus_characterEvaluation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    jointFunctionalCalculus E π (spectralCharacterEvaluation a) =
      spectralKernelOperator E π a := by
  apply (gelfandStarTransform (spectralOperatorAlgebra E π)).injective
  change
    (gelfandStarTransform (spectralOperatorAlgebra E π))
      ((gelfandStarTransform (spectralOperatorAlgebra E π)).symm
        ((spectralCharacterEvaluation a).comp
          (spectralCharacterMap E π))) =
      (gelfandStarTransform (spectralOperatorAlgebra E π))
        (spectralKernelOperator E π a)
  rw [StarAlgEquiv.apply_symm_apply]
  ext φ
  rfl

end

section

open WeakDual

universe u v

variable {B : Type u} [CommCStarAlgebra B]
variable {X : Type v} [TopologicalSpace X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inverseGelfand_naturality
    (α : B →⋆ₐ[ℂ] B)
    (p : C(WeakDual.characterSpace ℂ B, X))
    (d : C(X, X))
    (hp : ∀ φ : WeakDual.characterSpace ℂ B,
      p (WeakDual.CharacterSpace.compContinuousMap α φ) = d (p φ))
    (f : C(X, ℂ)) :
    α ((gelfandStarTransform B).symm (f.comp p)) =
      (gelfandStarTransform B).symm ((f.comp d).comp p) := by
  apply (gelfandStarTransform B).injective
  ext φ
  change
    (WeakDual.CharacterSpace.compContinuousMap α φ)
        ((gelfandStarTransform B).symm (f.comp p)) =
      φ ((gelfandStarTransform B).symm ((f.comp d).comp p))
  have hleft := congrArg
    (fun F : C(WeakDual.characterSpace ℂ B, ℂ) ↦
      F (WeakDual.CharacterSpace.compContinuousMap α φ))
    ((gelfandStarTransform B).apply_symm_apply (f.comp p))
  have hright := congrArg
    (fun F : C(WeakDual.characterSpace ℂ B, ℂ) ↦ F φ)
    ((gelfandStarTransform B).apply_symm_apply ((f.comp d).comp p))
  change
    (WeakDual.CharacterSpace.compContinuousMap α φ)
        ((gelfandStarTransform B).symm (f.comp p)) =
      f (p (WeakDual.CharacterSpace.compContinuousMap α φ)) at hleft
  change
    φ ((gelfandStarTransform B).symm ((f.comp d).comp p)) =
      f (d (p φ)) at hright
  calc
    _ = f (p (WeakDual.CharacterSpace.compContinuousMap α φ)) := hleft
    _ = f (d (p φ)) := congrArg f (hp φ)
    _ = _ := hright.symm

end

section

open scoped InnerProduct

universe u

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def positiveVectorState (x : V) : (V →L[ℂ] V) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ V) x)).restrictScalars ℝ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem positiveVectorState_star_mul_self (x : V) (T : V →L[ℂ] V) :
    positiveVectorState x (star T * T) = ‖T x‖ ^ 2 := by
  change (inner ℂ x ((star T) (T x))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem positiveVectorState_one (x : V) :
    positiveVectorState x (1 : V →L[ℂ] V) = ‖x‖ ^ 2 := by
  change (inner ℂ x x).re = _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

end

section

open ConnesRigidity MeasureTheory
open scoped CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualActionBaseContinuous
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Multiplicative A →ₜ* Multiplicative A where
  toMonoidHom := ((MulAutMultiplicative A).symm (action h)).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem dualCharacterAction_continuous
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Continuous (dualCharacterAction action h) := by
  change Continuous (fun χ : DiscreteCharacterSpace A ↦
    PontryaginDual.map (dualActionBaseContinuous action h⁻¹) χ)
  exact (PontryaginDual.map (dualActionBaseContinuous action h⁻¹)).continuous_toFun

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem dualCharacterAction_mul
    (action : H →* Multiplicative (AddAut A)) (g h : H)
    (χ : DiscreteCharacterSpace A) :
    dualCharacterAction action (g * h) χ =
      dualCharacterAction action g (dualCharacterAction action h χ) := by
  apply ContinuousMonoidHom.ext
  intro a
  change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action (g * h)⁻¹))
        (Multiplicative.toAdd a))) =
    χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹))
        ((Multiplicative.toAdd (action g⁻¹)) (Multiplicative.toAdd a))))
  rw [mul_inv_rev, map_mul]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem dualCharacterAction_one
    (action : H →* Multiplicative (AddAut A))
    (χ : DiscreteCharacterSpace A) :
    dualCharacterAction action (1 : H) χ = χ := by
  apply ContinuousMonoidHom.ext
  intro a
  change χ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (action 1⁻¹))
      (Multiplicative.toAdd a))) = χ a
  rw [inv_one, map_one]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def dualCharacterHomeomorph
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    DiscreteCharacterSpace A ≃ₜ DiscreteCharacterSpace A where
  toFun := dualCharacterAction action h
  invFun := dualCharacterAction action h⁻¹
  left_inv χ := by
    rw [← dualCharacterAction_mul, inv_mul_cancel, dualCharacterAction_one]
  right_inv χ := by
    rw [← dualCharacterAction_mul, mul_inv_cancel, dualCharacterAction_one]
  continuous_toFun := dualCharacterAction_continuous action h
  continuous_invFun := dualCharacterAction_continuous action h⁻¹



section Riesz

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def compactTestPrecomp (e : X ≃ₜ X) (f : C_c(X, ℝ)) : C_c(X, ℝ) where
  toFun x := f (e x)
  continuous_toFun := f.continuous.comp e.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rieszMeasure_map_homeomorph
    (e : X ≃ₜ X)
    (Λ Λ' : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (hfunctional : ∀ f : C_c(X, ℝ),
      Λ (compactTestPrecomp e f) = Λ' f) :
    (RealRMK.rieszMeasure Λ).map e = RealRMK.rieszMeasure Λ' := by
  let : ((RealRMK.rieszMeasure Λ).map e).Regular :=
    Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (μ := RealRMK.rieszMeasure Λ) (φ := e)
    e.continuous.measurable.aemeasurable
    (f := fun x : X ↦ f x) f.continuous.aestronglyMeasurable]
  change (∫ x, compactTestPrecomp e f x ∂(RealRMK.rieszMeasure Λ)) =
    ∫ x, f x ∂(RealRMK.rieszMeasure Λ')
  rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
  exact hfunctional f

end Riesz

section DualRiesz

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rieszMeasure_dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (Λ Λ' : C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ)
    (hfunctional : ∀ f : C_c(DiscreteCharacterSpace A, ℝ),
      Λ (compactTestPrecomp (dualCharacterHomeomorph action h) f) = Λ' f) :
    (RealRMK.rieszMeasure Λ).map (dualCharacterAction action h) =
      RealRMK.rieszMeasure Λ' :=
  rieszMeasure_map_homeomorph
    (dualCharacterHomeomorph action h) Λ Λ' hfunctional

end DualRiesz

section VectorState

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem positiveVectorState_unitary_pullback
    (x : V) (U : unitary (V →L[ℂ] V)) (T : V →L[ℂ] V) :
    positiveVectorState x
        (star (U : V →L[ℂ] V) * T * (U : V →L[ℂ] V)) =
      positiveVectorState ((U : V →L[ℂ] V) x) T := by
  change (inner ℂ x
    ((star (U : V →L[ℂ] V)) (T ((U : V →L[ℂ] V) x)))).re =
      (inner ℂ ((U : V →L[ℂ] V) x)
        (T ((U : V →L[ℂ] V) x))).re
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

end VectorState

end

section

open ConnesRigidity WeakDual

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientOperatorConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    (V →L[ℂ] V) ≃⋆ₐ[ℂ] (V →L[ℂ] V) :=
  Unitary.conjStarAlgAut ℂ (V →L[ℂ] V) (π (E.splitting h))

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem quotientOperatorConjugation_apply
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (T : V →L[ℂ] V) :
    quotientOperatorConjugation E π h T =
      (π (E.splitting h) : V →L[ℂ] V) * T *
        star (π (E.splitting h) : V →L[ℂ] V) := rfl

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientOperatorConjugation_kernel
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (a : A) :
    quotientOperatorConjugation E π h
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) =
        (π (E.inclusion (Multiplicative.ofAdd
          ((Multiplicative.toAdd (E.action h)) a))) : V →L[ℂ] V) := by
  change
    (π (E.splitting h) : V →L[ℂ] V) *
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) *
      star (π (E.splitting h) : V →L[ℂ] V) = _
  rw [← Unitary.coe_star, Unitary.star_eq_inv, ← map_inv]
  change
    (↑(π (E.splitting h) *
      π (E.inclusion (Multiplicative.ofAdd a)) *
      π ((E.splitting h)⁻¹)) : V →L[ℂ] V) = _
  rw [← map_mul, ← map_mul, E.conjugation]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientOperatorConjugation_generators_image
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    quotientOperatorConjugation E π h '' spectralOperatorGenerators E π =
      spectralOperatorGenerators E π := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨(Multiplicative.toAdd (E.action h)) a,
      (quotientOperatorConjugation_kernel E π h a).symm⟩
  · rintro _ ⟨a, rfl⟩
    let b : A := (Multiplicative.toAdd (E.action h⁻¹)) a
    refine ⟨(π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V),
      ⟨b, rfl⟩, ?_⟩
    rw [quotientOperatorConjugation_kernel]
    congr 3
    change (Multiplicative.toAdd (E.action h * E.action h⁻¹)) a = a
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, toAdd_one, AddAut.zero_apply]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientOperatorConjugation_mem
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    {T : V →L[ℂ] V} (hT : T ∈ spectralOperatorAlgebra E π) :
    quotientOperatorConjugation E π h T ∈ spectralOperatorAlgebra E π := by
  let F : (V →L[ℂ] V) →⋆ₐ[ℂ] (V →L[ℂ] V) :=
    (quotientOperatorConjugation E π h).toStarAlgHom
  have hcontinuous : Continuous F := by
    change Continuous (fun T : V →L[ℂ] V ↦
      (π (E.splitting h) : V →L[ℂ] V) * T *
        star (π (E.splitting h) : V →L[ℂ] V))
    fun_prop
  have hadjoin :
      (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)).map F =
        StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π) := by
    rw [StarAlgHom.map_adjoin]
    exact congrArg (StarAlgebra.adjoin ℂ)
      (quotientOperatorConjugation_generators_image E π h)
  have hmap := StarSubalgebra.map_topologicalClosure_le
    (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)) F hcontinuous
  rw [hadjoin] at hmap
  exact hmap ⟨T, hT, rfl⟩

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem quotientOperatorConjugation_inv
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    quotientOperatorConjugation E π h⁻¹ =
      (quotientOperatorConjugation E π h).symm := by
  change Unitary.conjStarAlgAut ℂ (V →L[ℂ] V)
      (π (E.splitting h⁻¹)) = _
  rw [map_inv, map_inv]
  exact map_inv (Unitary.conjStarAlgAut ℂ (V →L[ℂ] V)) _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientSpectralOperatorConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    spectralOperatorAlgebra E π ≃⋆ₐ[ℂ]
      spectralOperatorAlgebra E π where
  toFun T := ⟨quotientOperatorConjugation E π h T,
    quotientOperatorConjugation_mem E π h T.property⟩
  invFun T := ⟨quotientOperatorConjugation E π h⁻¹ T,
    quotientOperatorConjugation_mem E π h⁻¹ T.property⟩
  left_inv T := by
    apply Subtype.ext
    change quotientOperatorConjugation E π h⁻¹
      (quotientOperatorConjugation E π h (T : V →L[ℂ] V)) =
        (T : V →L[ℂ] V)
    rw [quotientOperatorConjugation_inv]
    exact (quotientOperatorConjugation E π h).symm_apply_apply T
  right_inv T := by
    apply Subtype.ext
    change quotientOperatorConjugation E π h
      (quotientOperatorConjugation E π h⁻¹ (T : V →L[ℂ] V)) =
        (T : V →L[ℂ] V)
    rw [quotientOperatorConjugation_inv]
    exact (quotientOperatorConjugation E π h).apply_symm_apply T
  map_mul' S T := by
    apply Subtype.ext
    exact map_mul (quotientOperatorConjugation E π h)
      (S : V →L[ℂ] V) (T : V →L[ℂ] V)
  map_add' S T := by
    apply Subtype.ext
    exact map_add (quotientOperatorConjugation E π h)
      (S : V →L[ℂ] V) (T : V →L[ℂ] V)
  map_star' T := by
    apply Subtype.ext
    exact map_star (quotientOperatorConjugation E π h)
      (T : V →L[ℂ] V)
  map_smul' c T := by
    apply Subtype.ext
    exact map_smul (quotientOperatorConjugation E π h) c
      (T : V →L[ℂ] V)



omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem quotientSpectralOperatorConjugation_kernel
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (a : A) :
    quotientSpectralOperatorConjugation E π h
      (spectralKernelOperator E π a) =
      spectralKernelOperator E π
        ((Multiplicative.toAdd (E.action h)) a) := by
  apply Subtype.ext
  exact quotientOperatorConjugation_kernel E π h a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralCharacter_quotientConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) :
    spectralCharacter E π
        (CharacterSpace.compContinuousMap
          (quotientSpectralOperatorConjugation E π h).toStarAlgHom φ) =
      dualCharacterAction E.action h⁻¹ (spectralCharacter E π φ) := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Circle.ext
  change
    φ ((quotientSpectralOperatorConjugation E π h)
      (spectralKernelOperator E π (Multiplicative.toAdd a))) =
      φ (spectralKernelOperator E π
        ((Multiplicative.toAdd (E.action (h⁻¹)⁻¹))
          (Multiplicative.toAdd a)))
  rw [quotientSpectralOperatorConjugation_kernel, inv_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualCharacterActionContinuousMap
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    C(DiscreteCharacterSpace A, DiscreteCharacterSpace A) :=
  ⟨dualCharacterAction action h, dualCharacterAction_continuous action h⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem jointFunctionalCalculus_quotient_covariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    (f : C(DiscreteCharacterSpace A, ℂ)) :
    ((jointFunctionalCalculus E π
        (f.comp (dualCharacterActionContinuousMap E.action h)) :
      spectralOperatorAlgebra E π) : V →L[ℂ] V) =
      star (π (E.splitting h) : V →L[ℂ] V) *
        ((jointFunctionalCalculus E π f : spectralOperatorAlgebra E π) :
          V →L[ℂ] V) *
        (π (E.splitting h) : V →L[ℂ] V) := by
  let α : spectralOperatorAlgebra E π →⋆ₐ[ℂ]
      spectralOperatorAlgebra E π :=
    (quotientSpectralOperatorConjugation E π h⁻¹).toStarAlgHom
  let d : C(DiscreteCharacterSpace A, DiscreteCharacterSpace A) :=
    dualCharacterActionContinuousMap E.action h
  have hp : ∀ φ : characterSpace ℂ (spectralOperatorAlgebra E π),
      spectralCharacterMap E π
        (CharacterSpace.compContinuousMap α φ) =
      d (spectralCharacterMap E π φ) := by
    intro φ
    change spectralCharacter E π
      (CharacterSpace.compContinuousMap
        (quotientSpectralOperatorConjugation E π h⁻¹).toStarAlgHom φ) =
      dualCharacterAction E.action h (spectralCharacter E π φ)
    simpa only [CharacterSpace.compContinuousMap_apply,
      inv_inv] using spectralCharacter_quotientConjugation E π h⁻¹ φ
  have hnaturality := inverseGelfand_naturality α
    (spectralCharacterMap E π) d hp f
  change
    (((gelfandStarTransform (spectralOperatorAlgebra E π)).symm
      ((f.comp d).comp (spectralCharacterMap E π)) :
      spectralOperatorAlgebra E π) : V →L[ℂ] V) = _
  rw [← hnaturality]
  change
    quotientOperatorConjugation E π h⁻¹
      ((jointFunctionalCalculus E π f : spectralOperatorAlgebra E π) :
        V →L[ℂ] V) = _
  rw [quotientOperatorConjugation_apply, map_inv, map_inv]
  rw [← Unitary.star_eq_inv, Unitary.coe_star, star_star]

end

section

open ConnesRigidity MeasureTheory
open scoped CompactlySupported

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {V : Type v} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterRealComplexification
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem characterRealComplexification_apply
    (f : C_c(X, ℝ)) (y : X) :
    characterRealComplexification f y = (f y : ℂ) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem characterRealComplexification_add
    (f g : C_c(X, ℝ)) :
    characterRealComplexification (f + g) =
      characterRealComplexification f + characterRealComplexification g := by
  ext y
  simp only [characterRealComplexification, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
    Complex.ofReal_add, ContinuousMap.coe_mk, ContinuousMap.add_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem characterRealComplexification_smul
    (r : ℝ) (f : C_c(X, ℝ)) :
    characterRealComplexification (r • f) =
      (r : ℂ) • characterRealComplexification f := by
  ext y
  simp only [characterRealComplexification, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, ContinuousMap.coe_mk, ContinuousMap.coe_smul]

variable [CompactSpace X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def characterRealSqrt (f : C_c(X, ℝ)) : C_c(X, ℝ) where
  toFun y := Real.sqrt (f y)
  continuous_toFun := Real.continuous_sqrt.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterRealComplexification_eq_star_mul_sqrt
    (f : C_c(X, ℝ)) (hf : ∀ y : X, 0 ≤ f y) :
    characterRealComplexification f =
      star (characterRealComplexification (characterRealSqrt f)) *
        characterRealComplexification (characterRealSqrt f) := by
  ext y
  simp only [characterRealComplexification, ContinuousMap.coe_mk, characterRealSqrt,
    CompactlySupportedContinuousMap.coe_mk, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj]
  exact (Real.mul_self_sqrt (hf y)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterVectorFunctionalLinear
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f :=
    (inner ℂ x ((calculus (characterRealComplexification f)) x)).re
  map_add' f g := by
    simp only [characterRealComplexification_add, map_add, add_apply, CStarModule.inner_add_right,
      Complex.add_re]
  map_smul' r f := by
    rw [characterRealComplexification_smul, map_smul]
    change
      (inner ℂ x ((r : ℂ) •
        ((calculus (characterRealComplexification f)) x))).re =
        r * (inner ℂ x
          ((calculus (characterRealComplexification f)) x)).re
    rw [inner_smul_right, Complex.re_ofReal_mul]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterVectorFunctionalLinear_nonneg
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (hf : ∀ y : X, 0 ≤ f y) :
    0 ≤ characterVectorFunctionalLinear calculus x f := by
  let g : C(X, ℂ) := characterRealComplexification (characterRealSqrt f)
  have hfactor : characterRealComplexification f = star g * g :=
    characterRealComplexification_eq_star_mul_sqrt f hf
  change 0 ≤ (inner ℂ x ((calculus (characterRealComplexification f)) x)).re
  rw [hfactor, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
  change 0 ≤ (inner ℂ x
    (((calculus g).adjoint.comp (calculus g)) x)).re
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact @inner_self_nonneg ℂ V _ _ _ ((calculus g) x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterVectorFunctional
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := characterVectorFunctionalLinear calculus x
  monotone' := by
    intro f g hfg
    have hnonneg : ∀ y : X, 0 ≤ (g - f) y := by
      intro y
      exact sub_nonneg.mpr (hfg y)
    have hpositive := characterVectorFunctionalLinear_nonneg
      calculus x (g - f) hnonneg
    change
      characterVectorFunctionalLinear calculus x f ≤
        characterVectorFunctionalLinear calculus x g
    rw [map_sub] at hpositive
    linarith



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterVectorFunctional_one
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (hf : ∀ y : X, f y = 1) :
    characterVectorFunctional calculus x f = ‖x‖ ^ 2 := by
  have hcomplex : characterRealComplexification f =
      (1 : C(X, ℂ)) := by
    ext y
    simp only [characterRealComplexification, ContinuousMap.coe_mk, hf y, Complex.ofReal_one,
      ContinuousMap.one_apply]
  change positiveVectorState x
    (calculus (characterRealComplexification f)) = ‖x‖ ^ 2
  rw [hcomplex, map_one, positiveVectorState_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterVectorFunctional_energy_of_operator
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (T : V →L[ℂ] V)
    (hf : calculus (characterRealComplexification f) =
      star (T - 1) * (T - 1)) :
    characterVectorFunctional calculus x f = ‖T x - x‖ ^ 2 := by
  change positiveVectorState x
    (calculus (characterRealComplexification f)) = ‖T x - x‖ ^ 2
  rw [hf, positiveVectorState_star_mul_self]
  simp only [sub_apply, one_apply_eq_self]

section PontryaginCharacter

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterEnergy_complexification
    (a : A) (evaluation : C(DiscreteCharacterSpace A, ℂ))
    (hevaluation : ∀ χ : DiscreteCharacterSpace A,
      evaluation χ =
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ)) :
    characterRealComplexification (spectralEnergyTest a) =
      star (evaluation - 1) * (evaluation - 1) := by
  ext χ
  change
    ((‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2 : ℝ) : ℂ) =
      star (evaluation χ - 1) * (evaluation χ - 1)
  rw [hevaluation]
  simpa only [Complex.ofReal_pow, star_sub, RCLike.star_def, star_one, Complex.normSq_eq_norm_sq,
    map_sub, map_one] using
    (Complex.normSq_eq_conj_mul_self
      (z := ((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterVectorFunctional_spectralEnergy
    (calculus : C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      (V →L[ℂ] V))
    (x : V) (a : A) (evaluation : C(DiscreteCharacterSpace A, ℂ))
    (hevaluation : ∀ χ : DiscreteCharacterSpace A,
      evaluation χ =
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ))
    (T : V →L[ℂ] V) (hT : calculus evaluation = T) :
    characterVectorFunctional calculus x (spectralEnergyTest a) =
      ‖T x - x‖ ^ 2 := by
  apply characterVectorFunctional_energy_of_operator calculus x
    (spectralEnergyTest a) T
  rw [characterEnergy_complexification a evaluation hevaluation,
    map_mul, map_star, map_sub, map_one, hT]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem characterVectorFunctional_spectralUnit
    (calculus : C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      (V →L[ℂ] V)) (x : V) :
    characterVectorFunctional calculus x (spectralUnitTest A) =
      ‖x‖ ^ 2 :=
  characterVectorFunctional_one calculus x (spectralUnitTest A)
    (fun _ ↦ rfl)

end PontryaginCharacter

section JointCharacterFunctional

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def jointFunctionalCalculusOperator
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) :
    C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ] (W →L[ℂ] W) :=
  (spectralOperatorAlgebra E π).subtype.comp
    (jointFunctionalCalculus E π)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem jointFunctionalCalculusOperator_characterEvaluation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (a : A) :
    jointFunctionalCalculusOperator E π (spectralCharacterEvaluation a) =
      (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) := by
  change ((jointFunctionalCalculus E π
    (spectralCharacterEvaluation a) : spectralOperatorAlgebra E π) :
      W →L[ℂ] W) = _
  rw [jointFunctionalCalculus_characterEvaluation]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def jointCharacterFunctional
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) :
    C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ :=
  characterVectorFunctional (jointFunctionalCalculusOperator E π) x



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem jointCharacterFunctional_normalization
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) :
    jointCharacterFunctional E π x (spectralUnitTest A) = ‖x‖ ^ 2 :=
  characterVectorFunctional_spectralUnit
    (jointFunctionalCalculusOperator E π) x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem jointCharacterFunctional_energy
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a : A) :
    jointCharacterFunctional E π x (spectralEnergyTest a) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x - x‖ ^ 2 := by
  exact characterVectorFunctional_spectralEnergy
    (jointFunctionalCalculusOperator E π) x a
    (spectralCharacterEvaluation a) (fun _ ↦ rfl)
    (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W)
    (jointFunctionalCalculusOperator_characterEvaluation E π a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem jointCharacterFunctional_pullback_of_operatorCovariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (h : H)
    (hcovariance : ∀ f : C(DiscreteCharacterSpace A, ℂ),
      jointFunctionalCalculusOperator E π
          (f.comp
            ⟨dualCharacterHomeomorph E.action h,
              (dualCharacterHomeomorph E.action h).continuous⟩) =
        star (π (E.splitting h) : W →L[ℂ] W) *
          jointFunctionalCalculusOperator E π f *
          (π (E.splitting h) : W →L[ℂ] W))
    (x : W) (f : C_c(DiscreteCharacterSpace A, ℝ)) :
    jointCharacterFunctional E π x
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f) =
      jointCharacterFunctional E π
        ((π (E.splitting h) : W →L[ℂ] W) x) f := by
  have hpullback :
      characterRealComplexification
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f) =
        (characterRealComplexification f).comp
          ⟨dualCharacterHomeomorph E.action h,
            (dualCharacterHomeomorph E.action h).continuous⟩ := by
    ext χ
    rfl
  change positiveVectorState x
    (jointFunctionalCalculusOperator E π
      (characterRealComplexification
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f))) =
    positiveVectorState
      ((π (E.splitting h) : W →L[ℂ] W) x)
      (jointFunctionalCalculusOperator E π
        (characterRealComplexification f))
  rw [hpullback, hcovariance]
  exact positiveVectorState_unitary_pullback x (π (E.splitting h))
    (jointFunctionalCalculusOperator E π
      (characterRealComplexification f))

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem jointCharacterFunctional_riesz_covariance_of_operatorCovariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (h : H)
    (hcovariance : ∀ f : C(DiscreteCharacterSpace A, ℂ),
      jointFunctionalCalculusOperator E π
          (f.comp
            ⟨dualCharacterHomeomorph E.action h,
              (dualCharacterHomeomorph E.action h).continuous⟩) =
        star (π (E.splitting h) : W →L[ℂ] W) *
          jointFunctionalCalculusOperator E π f *
          (π (E.splitting h) : W →L[ℂ] W))
    (x : W) :
    (RealRMK.rieszMeasure (jointCharacterFunctional E π x)).map
        (dualCharacterAction E.action h) =
      RealRMK.rieszMeasure
        (jointCharacterFunctional E π
          ((π (E.splitting h) : W →L[ℂ] W) x)) := by
  apply rieszMeasure_dualCharacterAction E.action h
  exact jointCharacterFunctional_pullback_of_operatorCovariance
    E π h hcovariance x

end JointCharacterFunctional

end

section

open ConnesRigidity InnerProductSpace

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def kernelUnitaryOrbit
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) : Set V :=
  Set.range fun a : A =>
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def kernelOrbitClosedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) : Set V :=
  closedConvexHull ℝ (kernelUnitaryOrbit E π x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_kernelOrbitClosedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    x ∈ kernelOrbitClosedConvexHull E π x := by
  apply subset_closedConvexHull
  refine ⟨0, ?_⟩
  simp only [ofAdd_zero, map_one, OneMemClass.coe_one, one_apply_eq_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernelUnitary_preserves_closedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) (a : A) :
    ∀ y ∈ kernelOrbitClosedConvexHull E π x,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y ∈
        kernelOrbitClosedConvexHull E π x := by
  let orbit : Set V := kernelUnitaryOrbit E π x
  let U : V →L[ℝ] V :=
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V).restrictScalars ℝ
  have horbit : U '' orbit ⊆ orbit := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨a + b, ?_⟩
    change
      (π (E.inclusion (Multiplicative.ofAdd (a + b))) : V →L[ℂ] V) x =
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          ((π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V) x)
    change
      (π (E.inclusion
        (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) : V →L[ℂ] V) x =
        ((↑(π (E.inclusion (Multiplicative.ofAdd a)) *
            π (E.inclusion (Multiplicative.ofAdd b))) : V →L[ℂ] V)) x
    rw [E.inclusion.map_mul, map_mul]
  have hhull : U '' convexHull ℝ orbit ⊆ convexHull ℝ orbit := by
    change U.toLinearMap '' convexHull ℝ orbit ⊆ convexHull ℝ orbit
    rw [LinearMap.image_convexHull]
    exact convexHull_mono horbit
  have hclosure : U '' closure (convexHull ℝ orbit) ⊆
      closure (convexHull ℝ orbit) :=
    (image_closure_subset_closure_image U.continuous).trans
      (closure_mono hhull)
  intro y hy
  have hy' : y ∈ closure (convexHull ℝ orbit) := by
    change y ∈ closedConvexHull ℝ orbit at hy
    rwa [closedConvexHull_eq_closure_convexHull] at hy
  have hUy : U y ∈ closure (convexHull ℝ orbit) :=
    hclosure ⟨y, hy', rfl⟩
  change U y ∈ closedConvexHull ℝ orbit
  rwa [closedConvexHull_eq_closure_convexHull]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralOrbit_norm_minimizer_fixed
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {S : Set W} (hconvex : Convex ℝ S)
    (U : W → W) (hUnorm : ∀ z, ‖U z‖ = ‖z‖)
    {y : W} (hy : y ∈ S)
    (hymin : ‖(0 : W) - y‖ = ⨅ z : S, ‖(0 : W) - z‖)
    (hU : ∀ z ∈ S, U z ∈ S) : U y = y := by
  have hinner :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hy).mp hymin
      (U y) (hU y hy)
  have hlower : ‖y‖ ^ 2 ≤ @inner ℝ W _ (U y) y := by
    rw [zero_sub, inner_neg_left, inner_sub_right,
      real_inner_self_eq_norm_sq] at hinner
    have hcomm : @inner ℝ W _ (U y) y = @inner ℝ W _ y (U y) :=
      real_inner_comm _ _
    rw [hcomm]
    linarith
  have hupper := real_inner_le_norm (U y) y
  rw [hUnorm] at hupper
  have heq : @inner ℝ W _ (U y) y = ‖y‖ ^ 2 := by
    linarith
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
  · exact le_of_eq (hUnorm y)
  · simpa only [RCLike.re_to_real] using heq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_kernel_fixed_norm_minimizer
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    ∃ y ∈ kernelOrbitClosedConvexHull E π x,
      (∀ z ∈ kernelOrbitClosedConvexHull E π x, ‖y‖ ≤ ‖z‖) ∧
        ∀ a : A,
          (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y = y := by
  let S : Set V := kernelOrbitClosedConvexHull E π x
  have hnonempty : S.Nonempty :=
    ⟨x, mem_kernelOrbitClosedConvexHull E π x⟩
  have hclosed : IsClosed S :=
    isClosed_closedConvexHull
  have hconvex : Convex ℝ S :=
    convex_closedConvexHull
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  obtain ⟨y, hy, hnorm⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hnonempty hclosed.isComplete hconvex (0 : V)
  have hnorm' : ‖y‖ = ⨅ z : S, ‖(z : V)‖ := by
    simpa only [zero_sub, norm_neg] using hnorm
  have hminimal : ∀ z ∈ S, ‖y‖ ≤ ‖z‖ := by
    intro z hz
    rw [hnorm']
    have hbounded :
        BddBelow (Set.range fun w : S => ‖(w : V)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbounded (⟨z, hz⟩ : S)
  refine ⟨y, hy, hminimal, ?_⟩
  intro a
  exact spectralOrbit_norm_minimizer_fixed hconvex
    (fun z =>
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) z)
    (fun z =>
      (Unitary.linearIsometryEquiv
        (π (E.inclusion (Multiplicative.ofAdd a)))).norm_map z)
    hy hnorm (kernelUnitary_preserves_closedConvexHull E π x a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_kernel_fixed_mem_closedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    ∃ y ∈ kernelOrbitClosedConvexHull E π x,
      ∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y = y := by
  obtain ⟨y, hy, _, hfixed⟩ :=
    exists_kernel_fixed_norm_minimizer E π x
  exact ⟨y, hy, hfixed⟩

end

section

open ConnesRigidity

section

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable (E : SplitAbelianExtension A G H)
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable (π : UnitaryRepresentation G V)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernelOrbit_closedConvexHull_projection_eq_zero
    (x : V) (hx : trivialCharacterProjection E π x = 0) :
    ∀ y ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x),
      trivialCharacterProjection E π y = 0 := by
  let P : V →L[ℝ] V :=
    (trivialCharacterProjection E π).restrictScalars ℝ
  have horbit :
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) ⊆
      (LinearMap.ker P.toLinearMap : Set V) := by
    rintro _ ⟨a, rfl⟩
    change trivialCharacterProjection E π
      ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) = 0
    rw [trivialCharacterProjection_kernel_orbit, hx]
  have hclosed : IsClosed (LinearMap.ker P.toLinearMap : Set V) :=
    P.isClosed_ker
  have hsubset :=
    closedConvexHull_min horbit (LinearMap.ker P.toLinearMap).convex hclosed
  intro y hy
  exact hsubset hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernel_fixed_inner_eq_zero_of_mem_closedConvexHull
    (x v y : V) (hx : trivialCharacterProjection E π x = 0)
    (hvfixed : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) v = v)
    (hy : y ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)) :
    inner ℂ v y = 0 := by
  have hprojection : trivialCharacterProjection E π y = 0 :=
    kernelOrbit_closedConvexHull_projection_eq_zero E π x hx y hy
  have horthogonal : y ∈ (kernelFixedSubmodule E π)ᗮ := by
    apply (Submodule.starProjection_apply_eq_zero_iff
      (kernelFixedSubmodule E π)).mp
    exact hprojection
  exact (Submodule.mem_orthogonal (kernelFixedSubmodule E π) y).mp
    horthogonal v ((mem_kernelFixedSubmodule E π v).mpr hvfixed)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernel_fixed_eq_zero_of_mem_closedConvexHull
    (x v : V) (hx : trivialCharacterProjection E π x = 0)
    (hv : v ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x))
    (hvfixed : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) v = v) :
    v = 0 := by
  exact inner_self_eq_zero.mp
    (kernel_fixed_inner_eq_zero_of_mem_closedConvexHull
      E π x v v hx hvfixed hv)

end

end

section

open ConnesRigidity

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_finset_affineCombination_approx_of_mem_closedConvexHull
    {I : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (orbit : I → V) {y : V}
    (hy : y ∈ closedConvexHull ℝ (Set.range orbit))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset I) (w : I → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      ‖(∑ i ∈ s, w i • orbit i) - y‖ < ε := by
  rw [closedConvexHull_eq_closure_convexHull] at hy
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hy ε hε
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_ofPred_eq] at hz
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hz
  refine ⟨s, w, hw, hsum, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination s orbit w hsum] at hcomb
  rw [hcomb]
  simpa only [dist_eq_norm] using
    (show dist z y < ε by simpa only [dist_comm] using hdist)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_finset_affineCombination_norm_lt_of_zero_mem_closedConvexHull
    {I : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (orbit : I → V)
    (hzero : (0 : V) ∈ closedConvexHull ℝ (Set.range orbit))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset I) (w : I → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      ‖∑ i ∈ s, w i • orbit i‖ < ε := by
  simpa only [sub_zero] using
    exists_finset_affineCombination_approx_of_mem_closedConvexHull
      orbit hzero hε

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kernelOrbit_exists_finset_affineCombination_norm_lt
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V)
    (hzero : (0 : V) ∈ closedConvexHull ℝ
      (Set.range fun a : A ↦
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset A) (w : A → ℝ),
      (∀ a ∈ s, 0 ≤ w a) ∧
      (∑ a ∈ s, w a) = 1 ∧
      ‖∑ a ∈ s, w a •
        ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)‖ < ε :=
  exists_finset_affineCombination_norm_lt_of_zero_mem_closedConvexHull
    (fun a : A ↦
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)
    hzero hε

end

section

open ConnesRigidity

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem zero_mem_kernelOrbitClosedConvexHull_of_projection_eq_zero
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V)
    (hx : trivialCharacterProjection E π x = 0) :
    (0 : V) ∈ kernelOrbitClosedConvexHull E π x := by
  obtain ⟨y, hy, hfixed⟩ :=
    exists_kernel_fixed_mem_closedConvexHull E π x
  have hzero : y = 0 := by
    apply kernel_fixed_eq_zero_of_mem_closedConvexHull E π x y hx
    · exact hy
    · exact hfixed
  simpa only [hzero] using hy

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem kernelOrbitAffineApproximation
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    HasKernelOrbitAffineApproximation E π := by
  intro x hx ε hε
  have hzero : (0 : V) ∈ closedConvexHull ℝ
      (Set.range fun a : A ↦
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) :=
    zero_mem_kernelOrbitClosedConvexHull_of_projection_eq_zero E π x hx
  obtain ⟨s, w, _, hw, hnorm⟩ :=
    kernelOrbit_exists_finset_affineCombination_norm_lt E π x hzero hε
  exact ⟨s, w, hw, hnorm⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectral_criterion_of_positive_functional_unconditional
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (functional : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        PositiveSpectralFunctional E V π) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion_of_positive_functional_and_orbitApproximation
    E hH J hc hdetection functional
  exact fun V _ _ _ π ↦ kernelOrbitAffineApproximation E π

end

section

open ConnesRigidity MeasureTheory

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def jointPositiveSpectralFunctional
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    PositiveSpectralFunctional E V π where
  functional x := jointCharacterFunctional E π x
  normalization x := jointCharacterFunctional_normalization E π x
  energy x a := jointCharacterFunctional_energy E π x a
  covariance h x := by
    apply jointCharacterFunctional_riesz_covariance_of_operatorCovariance
      E π h ?_ x
    intro f
    simpa only [jointFunctionalCalculusOperator, dualCharacterHomeomorph,
      Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, StarAlgHom.comp_apply,
      StarSubalgebra.coe_subtype, dualCharacterActionContinuousMap] using
      jointFunctionalCalculus_quotient_covariance E π h f

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem spectral_criterion_unconditional
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion_of_positive_functional_unconditional
    E hH J hc hdetection
  exact fun W _ _ _ π => jointPositiveSpectralFunctional E π

end

section

open ConnesRigidity MeasureTheory Set
open scoped BigOperators ENNReal NNReal CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def spectralLargeDisplacementSet (a : A) (r : ℝ) :
    Set (DiscreteCharacterSpace A) :=
  {χ | r ≤ ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem spectralDetection_integrable
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) :
    Integrable (fun χ : DiscreteCharacterSpace A =>
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2)
      (μ : Measure (DiscreteCharacterSpace A)) := by
  exact ((continuous_character_evaluation a).sub
    continuous_const).norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem spectralLargeDisplacement_measureReal_mul_sq_le_energy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A))
    (a : A) (r : ℝ) (hr : 0 ≤ r) :
    r ^ 2 * (μ : Measure (DiscreteCharacterSpace A)).real
        (spectralLargeDisplacementSet a r) ≤
      spectralDetectionEnergy μ a := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := (μ : Measure (DiscreteCharacterSpace A)))
    (f := fun χ : DiscreteCharacterSpace A =>
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (spectralDetection_integrable μ a) (r ^ 2)
  have hset :
      {χ : DiscreteCharacterSpace A |
        r ^ 2 ≤ ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2} =
      spectralLargeDisplacementSet a r := by
    ext χ
    change (r ^ 2 ≤ ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2) ↔ _
    exact (sq_le_sq₀ hr (norm_nonneg _))
  rwa [hset] at hmarkov

section ConditionalSpectralMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_measureReal_inter_sub_inter_le
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {U : Set Ω} (hU : MeasurableSet U) (s t : Set Ω) :
    |μ.real (s ∩ U) - μ.real (t ∩ U)| ≤
      |μ.real s - μ.real t| + μ.real Uᶜ := by
  have hsdecomp := measureReal_inter_add_sdiff (μ := μ) (s := s) hU
  have htdecomp := measureReal_inter_add_sdiff (μ := μ) (s := t) hU
  have hsbound : μ.real (s \ U) ≤ μ.real Uᶜ := by
    exact measureReal_mono (μ := μ) (Set.sdiff_subset_compl _ _)
  have htbound : μ.real (t \ U) ≤ μ.real Uᶜ := by
    exact measureReal_mono (μ := μ) (Set.sdiff_subset_compl _ _)
  have hsdiff : 0 ≤ μ.real (s \ U) := measureReal_nonneg
  have htdiff : 0 ≤ μ.real (t \ U) := measureReal_nonneg
  have hrest : |μ.real (s \ U) - μ.real (t \ U)| ≤ μ.real Uᶜ := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    |μ.real (s ∩ U) - μ.real (t ∩ U)| =
        |(μ.real s - μ.real t) -
          (μ.real (s \ U) - μ.real (t \ U))| := by
      congr 1
      linarith
    _ ≤ |μ.real s - μ.real t| +
          |μ.real (s \ U) - μ.real (t \ U)| := abs_sub _ _
    _ ≤ |μ.real s - μ.real t| + μ.real Uᶜ := by linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def conditionedProbability (μ : ProbabilityMeasure Ω)
    (U : Set Ω) (hU : 0 < (μ : Measure Ω).real U) :
    ProbabilityMeasure Ω :=
  ⟨ProbabilityTheory.cond (μ : Measure Ω) U,
    ProbabilityTheory.cond_isProbabilityMeasure (by
      intro hzero
      change 0 < ((μ : Measure Ω) U).toReal at hU
      simp only [hzero, ENNReal.toReal_zero, lt_self_iff_false] at hU)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem conditionedProbability_measureReal
    (μ : ProbabilityMeasure Ω) {U : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U) (s : Set Ω) :
    (conditionedProbability μ U hU : Measure Ω).real s =
      (μ : Measure Ω).real (s ∩ U) / (μ : Measure Ω).real U := by
  change (ProbabilityTheory.cond (μ : Measure Ω) U).real s = _
  rw [measureReal_def, ProbabilityTheory.cond_apply hUmeas,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((μ : Measure Ω).real U)⁻¹ *
    (μ : Measure Ω).real (U ∩ s) = _
  rw [Set.inter_comm]
  exact (div_eq_inv_mul _ _).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem abs_conditionedProbability_measureReal_sub_le
    (μ : ProbabilityMeasure Ω) {U : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U) (s t : Set Ω) :
    |(conditionedProbability μ U hU : Measure Ω).real s -
        (conditionedProbability μ U hU : Measure Ω).real t| ≤
      (|(μ : Measure Ω).real s - (μ : Measure Ω).real t| +
        (μ : Measure Ω).real Uᶜ) / (μ : Measure Ω).real U := by
  rw [conditionedProbability_measureReal μ hU hUmeas s,
    conditionedProbability_measureReal μ hU hUmeas t,
    ← sub_div, abs_div, abs_of_pos hU]
  exact (div_le_div_iff_of_pos_right hU).mpr
    (abs_measureReal_inter_sub_inter_le (μ : Measure Ω) hUmeas s t)

end ConditionalSpectralMeasure



end

section

open ConnesRigidity

universe u

variable {G : Type u} [Group G]
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev AffineHilbertAction (G V : Type u) [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] :=
  G →* (V ≃ᵃⁱ[ℂ] V)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsAffineFixed (α : AffineHilbertAction G V)
    (K : Subgroup G) (x : V) : Prop :=
  ∀ k : K, α (k : G) x = x





omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem IsAffineFixed.midpoint
    {α : AffineHilbertAction G V} {K : Subgroup G} {x y : V}
    (hx : IsAffineFixed α K x) (hy : IsAffineFixed α K y) :
    IsAffineFixed α K (midpoint ℂ x y) := by
  intro k
  change (α (k : G)).toAffineEquiv (_root_.midpoint ℂ x y) =
    _root_.midpoint ℂ x y
  rw [AffineEquiv.map_midpoint]
  have hx' : (α (k : G)).toAffineEquiv x = x := hx k
  have hy' : (α (k : G)).toAffineEquiv y = y := hy k
  rw [hx', hy']

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineLinearIsometryHom
    (α : AffineHilbertAction G V) : G →* (V ≃ₗᵢ[ℂ] V) where
  toFun g := (α g).linearIsometryEquiv
  map_one' := by
    ext x
    change (α 1).linearIsometryEquiv x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    rw [map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineLinearRepresentation
    (α : AffineHilbertAction G V) : UnitaryRepresentation G V :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (affineLinearIsometryHom α)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineLinearRepresentation_sub_fixed
    {α : AffineHilbertAction G V} {K : Subgroup G} {x y : V}
    (hx : IsAffineFixed α K x) (hy : IsAffineFixed α K y)
    (k : K) :
    (affineLinearRepresentation α (k : G) : V →L[ℂ] V) (x - y) = x - y := by
  change (α (k : G)).linearIsometryEquiv (x - y) = x - y
  simpa only [map_sub, vsub_eq_sub, hx k, hy k] using (α (k : G)).map_vsub x y

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem IsAffineFixed.normalizer_action
    {α : AffineHilbertAction G V} {K : Subgroup G}
    {x : V} (hx : IsAffineFixed α K x)
    (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsAffineFixed α K (α g x) := by
  intro k
  have hconj : g⁻¹ * (k : G) * g ∈ K := by
    exact ((Subgroup.mem_normalizer_iff''.mp hg) (k : G)).mp k.property
  let k' : K := ⟨g⁻¹ * (k : G) * g, hconj⟩
  have hkg : (k : G) * g = g * (k' : G) := by
    dsimp [k']
    group
  calc
    α (k : G) (α g x) = α ((k : G) * g) x := by
      rw [map_mul]
      rfl
    _ = α (g * (k' : G)) x := by rw [hkg]
    _ = α g (α (k' : G) x) := by
      rw [map_mul]
      rfl
    _ = α g x := by rw [hx k']

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem eq_of_norm_eq_and_midpoint_norm_ge
    (x y : V) (d : ℝ)
    (hx : ‖x‖ = d) (hy : ‖y‖ = d)
    (hmid : d ≤ ‖midpoint ℂ x y‖) : x = y := by
  have hmid' : 2 * d ≤ ‖x + y‖ := by
    rw [midpoint_eq_smul_add, norm_smul] at hmid
    norm_num at hmid ⊢
    linarith
  have hpar := parallelogram_law_with_norm ℂ x y
  rw [hx, hy] at hpar
  have hzero : ‖x - y‖ = 0 := by
    have hd : 0 ≤ d := hx ▸ norm_nonneg x
    have hsquare : (2 * d) ^ 2 ≤ ‖x + y‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hmid'
    have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure IsMinimizingAffinePair
    (α : AffineHilbertAction G V)
    (K₁ K₂ : Subgroup G) (x₁ x₂ : V) : Prop where
  fixed_left : IsAffineFixed α K₁ x₁
  fixed_right : IsAffineFixed α K₂ x₂
  minimal : ∀ y₁ y₂ : V,
    IsAffineFixed α K₁ y₁ → IsAffineFixed α K₂ y₂ →
      ‖x₁ - x₂‖ ≤ ‖y₁ - y₂‖

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem IsMinimizingAffinePair.sub_eq_of_norm_eq
    {α : AffineHilbertAction G V}
    {K₁ K₂ : Subgroup G} {x₁ x₂ : V}
    (hmin : IsMinimizingAffinePair α K₁ K₂ x₁ x₂)
    {y₁ y₂ : V}
    (hy₁ : IsAffineFixed α K₁ y₁)
    (hy₂ : IsAffineFixed α K₂ y₂)
    (hdist : ‖y₁ - y₂‖ = ‖x₁ - x₂‖) :
    x₁ - x₂ = y₁ - y₂ := by
  apply eq_of_norm_eq_and_midpoint_norm_ge
    (x₁ - x₂) (y₁ - y₂) ‖x₁ - x₂‖ rfl hdist
  have hmid := hmin.minimal
    (midpoint ℂ x₁ y₁) (midpoint ℂ x₂ y₂)
    (hmin.fixed_left.midpoint hy₁)
    (hmin.fixed_right.midpoint hy₂)
  have hsub : midpoint ℂ x₁ y₁ - midpoint ℂ x₂ y₂ =
      midpoint ℂ (x₁ - x₂) (y₁ - y₂) := by
    simpa only [vsub_eq_sub] using
      (midpoint_vsub_midpoint (R := ℂ) x₁ y₁ x₂ y₂)
  rwa [hsub] at hmid

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineLinearStabilizer
    (α : AffineHilbertAction G V) (x : V) : Subgroup G where
  carrier := {g | (affineLinearRepresentation α g : V →L[ℂ] V) x = x}
  one_mem' := by
    change (affineLinearRepresentation α 1 : V →L[ℂ] V) x = x
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change (affineLinearRepresentation α (g * h) : V →L[ℂ] V) x = x
    rw [map_mul]
    change (affineLinearRepresentation α g : V →L[ℂ] V)
      ((affineLinearRepresentation α h : V →L[ℂ] V) x) = x
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change (affineLinearRepresentation α g⁻¹ : V →L[ℂ] V) x = x
    calc
      (affineLinearRepresentation α g⁻¹ : V →L[ℂ] V) x =
          (affineLinearRepresentation α g⁻¹ : V →L[ℂ] V)
            ((affineLinearRepresentation α g : V →L[ℂ] V) x) := by rw [hg]
      _ = (affineLinearRepresentation α (g⁻¹ * g) : V →L[ℂ] V) x := by
        rw [map_mul]
        rfl
      _ = x := by simp only [inv_mul_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineLinear_invariant_of_sup_eq_top
    (α : AffineHilbertAction G V)
    (K₁ K₂ : Subgroup G) (hgen : K₁ ⊔ K₂ = ⊤)
    (x : V)
    (h₁ : ∀ k : K₁,
      (affineLinearRepresentation α (k : G) : V →L[ℂ] V) x = x)
    (h₂ : ∀ k : K₂,
      (affineLinearRepresentation α (k : G) : V →L[ℂ] V) x = x) :
    (affineLinearRepresentation α).IsInvariant x := by
  have hleft : K₁ ≤ affineLinearStabilizer α x := fun k hk => h₁ ⟨k, hk⟩
  have hright : K₂ ≤ affineLinearStabilizer α x := fun k hk => h₂ ⟨k, hk⟩
  have htop : (⊤ : Subgroup G) ≤ affineLinearStabilizer α x := by
    rw [← hgen]
    exact sup_le hleft hright
  intro g
  exact htop (Subgroup.mem_top g)

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem IsMinimizingAffinePair.sub_eq_normalizer_sub
    {α : AffineHilbertAction G V}
    {K₁ K₂ : Subgroup G} {x₁ x₂ : V}
    (hmin : IsMinimizingAffinePair α K₁ K₂ x₁ x₂)
    (g : G)
    (hg₁ : g ∈ Subgroup.normalizer (K₁ : Set G))
    (hg₂ : g ∈ Subgroup.normalizer (K₂ : Set G)) :
    x₁ - x₂ = α g x₁ - α g x₂ := by
  apply hmin.sub_eq_of_norm_eq
    (hmin.fixed_left.normalizer_action g hg₁)
    (hmin.fixed_right.normalizer_action g hg₂)
  calc
    ‖α g x₁ - α g x₂‖ =
        ‖(α g).linearIsometryEquiv (x₁ - x₂)‖ := by
      congr 1
      simpa only [vsub_eq_sub] using ((α g).map_vsub x₁ x₂).symm
    _ = ‖x₁ - x₂‖ := (α g).linearIsometryEquiv.norm_map _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem IsMinimizingAffinePair.normalizer_fixed_of_no_linear_invariants
    {α : AffineHilbertAction G V}
    {K₁ K₂ : Subgroup G} {x₁ x₂ : V}
    (hmin : IsMinimizingAffinePair α K₁ K₂ x₁ x₂)
    (hgen : K₁ ⊔ K₂ = ⊤)
    (hno : ∀ x : V,
      (affineLinearRepresentation α).IsInvariant x → x = 0)
    (g : G)
    (hg₁ : g ∈ Subgroup.normalizer (K₁ : Set G))
    (hg₂ : g ∈ Subgroup.normalizer (K₂ : Set G)) :
    α g x₁ = x₁ ∧ α g x₂ = x₂ := by
  have hy₁ := hmin.fixed_left.normalizer_action g hg₁
  have hy₂ := hmin.fixed_right.normalizer_action g hg₂
  have hdiff := hmin.sub_eq_normalizer_sub g hg₁ hg₂
  have hdisp : x₁ - α g x₁ = x₂ - α g x₂ :=
    sub_eq_sub_iff_sub_eq_sub.mp hdiff
  let v : V := x₁ - α g x₁
  have hv₁ : ∀ k : K₁,
      (affineLinearRepresentation α (k : G) : V →L[ℂ] V) v = v := by
    intro k
    exact affineLinearRepresentation_sub_fixed hmin.fixed_left hy₁ k
  have hv₂ : ∀ k : K₂,
      (affineLinearRepresentation α (k : G) : V →L[ℂ] V) v = v := by
    intro k
    have hfixed := affineLinearRepresentation_sub_fixed
      hmin.fixed_right hy₂ k
    simpa [v, hdisp] using hfixed
  have hvzero : v = 0 :=
    hno v (affineLinear_invariant_of_sup_eq_top α K₁ K₂ hgen v hv₁ hv₂)
  have hleft : α g x₁ = x₁ := by
    dsimp [v] at hvzero
    exact (sub_eq_zero.mp hvzero).symm
  have hright : α g x₂ = x₂ := by
    have hz : x₂ - α g x₂ = 0 := hdisp ▸ hvzero
    exact (sub_eq_zero.mp hz).symm
  exact ⟨hleft, hright⟩

end

section

namespace CornulierUltralimit

open Filter Topology
open scoped BigOperators ComplexOrder InnerProductSpace Topology

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def scalarOperatorKernel {I : Type u} (K : Matrix I I ℂ) :
    Matrix I I (ℂ →L[ℂ] ℂ) :=
  fun g h => ContinuousLinearMap.toSpanSingleton ℂ (K g h)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scalarOperatorKernel_posSemidef {I : Type u}
    (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (scalarOperatorKernel K).PosSemidef := by
  apply ((RKHS.posSemidef_tfae
    (K := scalarOperatorKernel K)).out 2 0).mp
  constructor
  · apply Matrix.IsHermitian.ext
    intro g h
    change star (ContinuousLinearMap.toSpanSingleton ℂ (K h g)) =
      ContinuousLinearMap.toSpanSingleton ℂ (K g h)
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_toSpanSingleton]
    apply ContinuousLinearMap.ext
    intro z
    calc
      (innerSL ℂ (K h g)) z = star (K h g) * z := by
        simp only [innerSL_apply_apply, RCLike.inner_apply',
          RCLike.star_def]
      _ = K g h * z := by rw [hK.isHermitian.apply g h]
      _ = z * K g h := mul_comm _ _
      _ = (ContinuousLinearMap.toSpanSingleton ℂ (K g h)) z := by
        simp only [ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul]
  · intro c
    have hc := hK.2 c
    have hreal :
        0 ≤ RCLike.re (c.sum fun g z =>
          c.sum fun h w => star z * K g h * w) :=
      (RCLike.nonneg_iff.mp hc).1
    simp only [scalarOperatorKernel,
      ContinuousLinearMap.toSpanSingleton_apply,
      RCLike.inner_apply', smul_eq_mul, map_mul]
    simpa only [← RCLike.star_def, hK.isHermitian.apply,
      mul_assoc, mul_left_comm, mul_comm] using hreal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem preKernel_inner_single {I : Type u}
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (i j : I × ℂ) (z w : ℂ) :
    ⟪(Finsupp.single i z : RKHS.H₀ (scalarOperatorKernel K)),
      (Finsupp.single j w : RKHS.H₀ (scalarOperatorKernel K))⟫_ℂ =
      star z * w *
        ⟪scalarOperatorKernel K j.1 i.1 i.2, j.2⟫_ℂ := by
  change
    (Finsupp.single i z).sum (fun yu c =>
      (Finsupp.single j w).sum (fun xv d =>
        star c * d *
          ⟪scalarOperatorKernel K xv.1 yu.1 yu.2, xv.2⟫_ℂ)) = _
  simp only [RCLike.star_def, RCLike.inner_apply, mul_zero, zero_mul, Finsupp.sum_single_index,
    map_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionPreKernelTranslation {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I) (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  Finsupp.domLCongr ((ρ a).prodCongr (Equiv.refl ℂ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actionPreKernelTranslation_inner {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f g : RKHS.H₀ (scalarOperatorKernel K)) :
    ⟪actionPreKernelTranslation K ρ a f,
      actionPreKernelTranslation K ρ a g⟫_ℂ = ⟪f, g⟫_ℂ := by
  induction f using Finsupp.induction_linear generalizing g with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ ih₁ ih₂ =>
    simp only [map_add, inner_add_left, ih₁ g, ih₂ g]
  | single i z =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ ih₁ ih₂ =>
      simp only [map_add, inner_add_right, ih₁, ih₂]
    | single j w =>
      simp only [actionPreKernelTranslation,
        Finsupp.domLCongr_single, preKernel_inner_single,
        scalarOperatorKernel,
        ContinuousLinearMap.toSpanSingleton_apply]
      change
        star z * w * ⟪i.2 • K (ρ a j.1) (ρ a i.1), j.2⟫_ℂ =
          star z * w * ⟪i.2 • K j.1 i.1, j.2⟫_ℂ
      rw [hinv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionPreKernelTranslationIsometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  (actionPreKernelTranslation K ρ a).isometryOfInner
    (actionPreKernelTranslation_inner K ρ hinv a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionKernelTranslationMap {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) →L[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) :=
  ContinuousLinearMap.completion
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem actionKernelTranslationMap_coe {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv a
      (f : RKHS.OfKernel (scalarOperatorKernel K)) =
        (actionPreKernelTranslation K ρ a f :
          RKHS.OfKernel (scalarOperatorKernel K)) := by
  exact ContinuousLinearMap.completion_apply_coe
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap) f

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actionKernelTranslationMap_isometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) : Isometry (actionKernelTranslationMap K ρ hinv a) := by
  change Isometry (UniformSpace.Completion.map
    (actionPreKernelTranslationIsometry K ρ hinv a))
  exact (actionPreKernelTranslationIsometry K ρ hinv a).isometry.completion_map

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actionPreKernelTranslation_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (a b : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ (a * b) f =
      actionPreKernelTranslation K ρ a
        (actionPreKernelTranslation K ρ b f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ (a * b) i.1, i.2) z =
      Finsupp.single (ρ a (ρ b i.1), i.2) z
    rw [map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem actionPreKernelTranslation_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ 1 f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ 1 i.1, i.2) z =
      Finsupp.single (i.1, i.2) z
    simp only [map_one, Equiv.Perm.coe_one, id_eq, Prod.mk.eta]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actionKernelTranslationMap_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a b : G) (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv (a * b)).continuous
      ((actionKernelTranslationMap K ρ hinv a).continuous.comp
        (actionKernelTranslationMap K ρ hinv b).continuous)
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_mul_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem actionKernelTranslationMap_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv 1).continuous
      continuous_id
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_one_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionKernelTranslationLinearEquiv {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearMap := (actionKernelTranslationMap K ρ hinv a).toLinearMap
  invFun := actionKernelTranslationMap K ρ hinv a⁻¹
  left_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a⁻¹
        (actionKernelTranslationMap K ρ hinv a x) =
          actionKernelTranslationMap K ρ hinv (a⁻¹ * a) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a⁻¹ a x).symm
      _ = x := by simp only [inv_mul_cancel, actionKernelTranslationMap_one_apply]
  right_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv a⁻¹ x) =
          actionKernelTranslationMap K ρ hinv (a * a⁻¹) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a a⁻¹ x).symm
      _ = x := by simp only [mul_inv_cancel, actionKernelTranslationMap_one_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionKernelTranslationUnitary {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearEquiv := actionKernelTranslationLinearEquiv K ρ hinv a
  norm_map' :=
    (actionKernelTranslationMap_isometry K ρ hinv a).norm_map_of_map_zero
      (map_zero (actionKernelTranslationMap K ρ hinv a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actionKernelUnitaryRepresentation {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j) :
    G →* (RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K)) where
  toFun := actionKernelTranslationUnitary K ρ hinv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv 1 x = x
    exact actionKernelTranslationMap_one_apply K ρ hinv x
  map_mul' a b := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x)
    exact actionKernelTranslationMap_mul_apply K ρ hinv a b x

/-- The canonical vector associated to an index of a scalar-valued kernel. -/
private def canonicalKernelVector {I : Type u} (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef] (i : I) :
    RKHS.OfKernel (scalarOperatorKernel K) :=
  ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) :
    RKHS.H₀ (scalarOperatorKernel K)) :
      RKHS.OfKernel (scalarOperatorKernel K))

/-- The canonical kernel vectors realize the original scalar Gram matrix. -/
private theorem canonicalKernelVector_inner {I : Type u}
    (K : Matrix I I ℂ) (hK : K.PosSemidef)
    [Fact (scalarOperatorKernel K).PosSemidef] (i j : I) :
    ⟪canonicalKernelVector K i, canonicalKernelVector K j⟫_ℂ = K i j := by
  simp only [canonicalKernelVector]
  rw [UniformSpace.Completion.inner_coe, preKernel_inner_single]
  have hscalar : (scalarOperatorKernel K j i) 1 = K j i := by
    simp [scalarOperatorKernel, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [star_one, mul_one, RCLike.inner_apply, one_mul, hscalar]
  exact hK.isHermitian.apply i j

/-- Moving a scalar from a pre-kernel index into its coefficient preserves inner products. -/
private theorem preKernel_single_scalar_inner {I : Type u}
    (K : Matrix I I ℂ) [Fact (scalarOperatorKernel K).PosSemidef]
    (i : I) (z c : ℂ) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    ⟪(Finsupp.single (i, z) c : RKHS.H₀ (scalarOperatorKernel K)), f⟫_ℂ =
      ⟪(Finsupp.single (i, (1 : ℂ)) (c * z) :
        RKHS.H₀ (scalarOperatorKernel K)), f⟫_ℂ := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [inner_zero_right]
  | add f g hf hg => simp only [inner_add_right, hf, hg]
  | single j d =>
      rw [preKernel_inner_single, preKernel_inner_single]
      simp [scalarOperatorKernel,
        ContinuousLinearMap.toSpanSingleton_apply]
      ring

/-- A pre-kernel basis vector is a scalar multiple of its canonical kernel vector. -/
private theorem coe_single_eq_smul_canonicalKernelVector {I : Type u}
    (K : Matrix I I ℂ) [Fact (scalarOperatorKernel K).PosSemidef]
    (i : I) (z c : ℂ) :
    ((Finsupp.single (i, z) c : RKHS.H₀ (scalarOperatorKernel K)) :
        RKHS.OfKernel (scalarOperatorKernel K)) =
      (c * z) • canonicalKernelVector K i := by
  rw [canonicalKernelVector, ← UniformSpace.Completion.coe_smul]
  refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left ℂ fun f ↦ ?_
  rw [UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe]
  simpa [smul_eq_mul] using preKernel_single_scalar_inner K i z c f

/-- The index action sends each canonical vector to the corresponding translated vector. -/
private theorem actionKernelUnitaryRepresentation_canonicalKernelVector
    {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (i : I) :
    actionKernelUnitaryRepresentation K ρ hinv a
      (canonicalKernelVector K i) =
      canonicalKernelVector K (ρ a i) := by
  simp only [canonicalKernelVector]
  change
    actionKernelTranslationMap K ρ hinv a
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) :
        RKHS.H₀ (scalarOperatorKernel K)) :
          RKHS.OfKernel (scalarOperatorKernel K)) = _
  rw [actionKernelTranslationMap_coe]
  simp only [actionPreKernelTranslation, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure HilbertKernelRealization {I : Type u}
    (K : Matrix I I ℂ) where
  /-- The Hilbert-space carrier of the realization. -/
  carrier : Type u
  /-- The normed additive group structure on the carrier. -/
  [normed : NormedAddCommGroup carrier]
  /-- The inner-product-space structure on the carrier. -/
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  /-- The realizing vector attached to each index. -/
  vector : I → carrier
  gram : ∀ g h, ⟪vector g, vector h⟫_ℂ = K g h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance hilbertKernelRealizationNormedAddCommGroup
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : NormedAddCommGroup R.carrier :=
  R.normed

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance hilbertKernelRealizationInnerProductSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : InnerProductSpace ℂ R.carrier :=
  R.inner

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance hilbertKernelRealizationCompleteSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : CompleteSpace R.carrier :=
  R.complete

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertKernelRealization_pair_vector_add
    {G : Type u} (K : Matrix (G × G) (G × G) ℂ)
    (R : HilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (g h j : G) :
    R.vector (g, h) + R.vector (h, j) = R.vector (g, j) := by
  have horth (q : G × G) :
      ⟪R.vector (g, h) + R.vector (h, j) - R.vector (g, j),
        R.vector q⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_add_left,
      R.gram, R.gram, R.gram, hadd]
    exact sub_self _
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_right, inner_add_right,
    horth (g, h), horth (h, j), horth (g, j)]
  simp only [add_zero, sub_self]







/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def unitaryCocycleAffineAction
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H ≃ₗᵢ[ℂ] H)) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h)) :
    G →* (H ≃ᵃⁱ[ℂ] H) where
  toFun g := (π g).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℂ (b g))
  map_one' := by
    have hb_one : b 1 = 0 := by
      have h := hb 1 1
      simpa only [map_one, LinearIsometryEquiv.coe_one, id_eq, add_sub_cancel_right, mul_one,
        sub_self] using (congrArg (fun x : H => x - b 1) h).symm
    apply AffineIsometryEquiv.ext
    intro x
    change π 1 x + b 1 = x
    simp only [map_one, LinearIsometryEquiv.coe_one, id_eq, hb_one, add_zero]
  map_mul' g h := by
    apply AffineIsometryEquiv.ext
    intro x
    change π (g * h) x + b (g * h) =
      π g (π h x + b h) + b g
    rw [map_mul, hb, map_add]
    change π g (π h x) + (b g + π g (b h)) =
      (π g (π h x) + π g (b h)) + b g
    abel



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem unitaryCocycleAffineAction_linearIsometryEquiv
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H ≃ₗᵢ[ℂ] H)) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (g : G) :
    (unitaryCocycleAffineAction π b hb g).linearIsometryEquiv = π g := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl







/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedPairAction
    {G I : Type u} [Group G] (ρ : G →* Equiv.Perm I) :
    G →* Equiv.Perm (I × I) where
  toFun g := (ρ g).prodCongr (ρ g)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Prod.ext <;> simp
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Prod.ext <;> simp [map_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure EquivariantMarkedHilbertKernelRealization
    {G I : Type u} [Group G]
    (ρ : G →* Equiv.Perm I)
    (K : Matrix (I × I) (I × I) ℂ) where
  /-- The underlying Hilbert-kernel realization. -/
  realization : HilbertKernelRealization K
  /-- The group representation on the realization. -/
  representation : G →*
    (realization.carrier ≃ₗᵢ[ℂ] realization.carrier)
  equivariant : ∀ (g : G) (i j : I),
    representation g (realization.vector (i, j)) =
      realization.vector (ρ g i, ρ g j)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scalarKernel_canonical_dense
    {I : Type u} (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef] :
    Dense
      (Submodule.span ℂ (Set.range fun i : I =>
        canonicalKernelVector K i) :
        Set (RKHS.OfKernel (scalarOperatorKernel K))) := by
  apply UniformSpace.Completion.denseRange_coe.mono
  rintro _ ⟨f, rfl⟩
  induction f using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg =>
      rw [UniformSpace.Completion.coe_add]
      exact Submodule.add_mem _ hf hg
  | single iz c =>
      rcases iz with ⟨i, z⟩
      rw [coe_single_eq_smul_canonicalKernelVector]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_equivariantMarkedHilbertKernelRealization_dense
    {G I : Type u} [Group G]
    (ρ : G →* Equiv.Perm I)
    (K : Matrix (I × I) (I × I) ℂ)
    (hpositive : K.PosSemidef)
    (hdiagonal : ∀ (g : G) (i j k l : I),
      K (ρ g i, ρ g j) (ρ g k, ρ g l) = K (i, j) (k, l)) :
    ∃ R : EquivariantMarkedHilbertKernelRealization ρ K,
      Dense (Submodule.span ℂ (Set.range R.realization.vector) :
        Set R.realization.carrier) := by
  let : Fact (scalarOperatorKernel K).PosSemidef :=
    ⟨scalarOperatorKernel_posSemidef K hpositive⟩
  let H := RKHS.OfKernel (scalarOperatorKernel K)
  let R : HilbertKernelRealization K := {
    carrier := H
    vector := fun q => canonicalKernelVector K q
    gram := by
      intro q r
      exact canonicalKernelVector_inner K hpositive q r
  }
  have hinvariant : ∀ (g : G) (q r : I × I),
      K (markedPairAction ρ g q) (markedPairAction ρ g r) = K q r := by
    intro g q r
    exact hdiagonal g q.1 q.2 r.1 r.2
  let S : EquivariantMarkedHilbertKernelRealization ρ K := {
    realization := R
    representation := actionKernelUnitaryRepresentation K
      (markedPairAction ρ) hinvariant
    equivariant := by
      intro g i j
      exact actionKernelUnitaryRepresentation_canonicalKernelVector K
        (markedPairAction ρ) hinvariant g (i, j)
  }
  refine ⟨S, ?_⟩
  exact scalarKernel_canonical_dense K

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inner_finsupp_sum_self
    {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : I → H) (c : I →₀ ℂ) :
    ⟪c.sum (fun i a => a • v i),
      c.sum (fun i a => a • v i)⟫_ℂ =
      c.sum (fun i a => c.sum (fun j b =>
        star a * ⟪v i, v j⟫_ℂ * b)) := by
  rw [Finsupp.sum_inner]
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.inner_sum]
  apply Finsupp.sum_congr
  intro j hj
  simp only [inner_smul_left, inner_smul_right, RCLike.star_def]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tendsto_norm_sq_finsupp_sum_of_gram
    {N I H : Type*} {V : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (V n)]
    [∀ n, InnerProductSpace ℂ (V n)]
    (l : Filter N) (v : ∀ n, I → V n) (w : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        l (𝓝 ⟪w i, w j⟫_ℂ))
    (c : I →₀ ℂ) :
    Tendsto (fun n => ‖c.sum (fun i a => a • v n i)‖ ^ 2)
      l (𝓝 (‖c.sum (fun i a => a • w i)‖ ^ 2)) := by
  have hquadratic :
      Tendsto
        (fun n => c.sum fun i a => c.sum fun j b =>
          star a * ⟪v n i, v n j⟫_ℂ * b)
        l
        (𝓝 (c.sum fun i a => c.sum fun j b =>
          star a * ⟪w i, w j⟫_ℂ * b)) := by
    simpa only [Finsupp.sum] using
      tendsto_finsetSum c.support (fun i _ =>
        tendsto_finsetSum c.support (fun j _ =>
          (tendsto_const_nhds.mul (hgram i j)).mul
            tendsto_const_nhds))
  have hinner :
      Tendsto
        (fun n =>
          ⟪c.sum (fun i a => a • v n i),
            c.sum (fun i a => a • v n i)⟫_ℂ)
        l
        (𝓝 ⟪c.sum (fun i a => a • w i),
          c.sum (fun i a => a • w i)⟫_ℂ) := by
    simpa only [inner_finsupp_sum_self] using hquadratic
  have hreal := (Complex.continuous_re.tendsto _).comp hinner
  change Tendsto
    (fun n => (⟪c.sum (fun i a => a • v n i),
      c.sum (fun i a => a • v n i)⟫_ℂ).re)
    l
    (𝓝 (⟪c.sum (fun i a => a • w i),
      c.sum (fun i a => a • w i)⟫_ℂ).re) at hreal
  convert hreal using 1
  · funext n
    exact norm_sq_eq_re_inner (𝕜 := ℂ)
      (c.sum (fun i a => a • v n i))
  · congr 1
    exact norm_sq_eq_re_inner (𝕜 := ℂ)
      (c.sum (fun i a => a • w i))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem tendsto_norm_finsupp_sum_of_gram
    {N I H : Type*} {V : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (V n)]
    [∀ n, InnerProductSpace ℂ (V n)]
    (l : Filter N) (v : ∀ n, I → V n) (w : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        l (𝓝 ⟪w i, w j⟫_ℂ))
    (c : I →₀ ℂ) :
    Tendsto (fun n => ‖c.sum (fun i a => a • v n i)‖)
      l (𝓝 ‖c.sum (fun i a => a • w i)‖) := by
  have hroot :=
    (Real.continuous_sqrt.tendsto
      (‖c.sum (fun i a => a • w i)‖ ^ 2)).comp
        (tendsto_norm_sq_finsupp_sum_of_gram l v w hgram c)
  convert hroot using 1
  · funext n
    exact (Real.sqrt_sq
      (norm_nonneg (c.sum (fun i a => a • v n i)))).symm
  · congr 1
    rw [Real.sqrt_sq
      (norm_nonneg (c.sum (fun i a => a • w i)))]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedPairCocycle
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    {K : Matrix (I × I) (I × I) ℂ}
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (i₀ : I) (g : G) : R.realization.carrier :=
  R.realization.vector (ρ g i₀, i₀)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem markedPairCocycle_mul
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    (K : Matrix (I × I) (I × I) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (hadd : ∀ i j k : I, ∀ q : I × I,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (i₀ : I) (g h : G) :
    markedPairCocycle R i₀ (g * h) =
      markedPairCocycle R i₀ g +
        R.representation g (markedPairCocycle R i₀ h) := by
  unfold markedPairCocycle
  rw [R.equivariant, map_mul]
  change R.realization.vector (ρ g (ρ h i₀), i₀) =
    R.realization.vector (ρ g i₀, i₀) +
      R.realization.vector (ρ g (ρ h i₀), ρ g i₀)
  rw [add_comm]
  exact (hilbertKernelRealization_pair_vector_add K R.realization
    hadd (ρ g (ρ h i₀)) (ρ g i₀) i₀).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedPairAffineAction
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    (K : Matrix (I × I) (I × I) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (hadd : ∀ i j k : I, ∀ q : I × I,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (i₀ : I) :
    G →* (R.realization.carrier ≃ᵃⁱ[ℂ] R.realization.carrier) :=
  unitaryCocycleAffineAction R.representation
    (markedPairCocycle R i₀)
    (markedPairCocycle_mul K R hadd i₀)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedPairPoint
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    {K : Matrix (I × I) (I × I) ℂ}
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (i₀ i : I) : R.realization.carrier :=
  R.realization.vector (i, i₀)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedPairAffineAction_point
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    (K : Matrix (I × I) (I × I) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (hadd : ∀ i j k : I, ∀ q : I × I,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (i₀ i : I) (g : G) :
    markedPairAffineAction K R hadd i₀ g (markedPairPoint R i₀ i) =
      markedPairPoint R i₀ (ρ g i) := by
  change R.representation g (R.realization.vector (i, i₀)) +
    R.realization.vector (ρ g i₀, i₀) =
      R.realization.vector (ρ g i, i₀)
  rw [R.equivariant]
  exact hilbertKernelRealization_pair_vector_add K R.realization
    hadd (ρ g i) (ρ g i₀) i₀

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedPairPoint_sub
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    (K : Matrix (I × I) (I × I) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (hadd : ∀ i j k : I, ∀ q : I × I,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (i₀ i j : I) :
    markedPairPoint R i₀ i - markedPairPoint R i₀ j =
      R.realization.vector (i, j) := by
  unfold markedPairPoint
  apply (sub_eq_iff_eq_add).mpr
  exact (hilbertKernelRealization_pair_vector_add K R.realization
    hadd i j i₀).symm

end CornulierUltralimit

namespace CornulierUltralimit

open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_hyperfilter_gram_limit_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ L : Matrix I I ℂ,
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (L i j)) := by
  have hinnerbound (n : ℕ) (i j : I) :
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ B i * B j := by
    calc
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ ‖v n i‖ * ‖v n j‖ :=
        norm_inner_le_norm _ _
      _ ≤ B i * B j :=
        mul_le_mul (hbound n i) (hbound n j)
          (norm_nonneg _) ((norm_nonneg _).trans (hbound n i))
  let b : ℕ → (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) :=
    fun n q =>
      ⟨⟪v n q.1, v n q.2⟫_ℂ,
        by simpa only [Metric.mem_closedBall, dist_zero_right]
          using hinnerbound n q.1 q.2⟩
  let u := Ultrafilter.map b (Filter.hyperfilter ℕ)
  let z : (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) := u.lim
  let L : Matrix I I ℂ := fun i j => (z (i, j) : ℂ)
  refine ⟨L, ?_⟩
  have hu : Tendsto b (Filter.hyperfilter ℕ) (𝓝 z) := by
    change Filter.map b (↑(Filter.hyperfilter ℕ) : Filter ℕ) ≤
      𝓝 u.lim
    simpa only [u, Ultrafilter.coe_map] using u.le_nhds_lim
  intro i j
  have heval :
      Tendsto
        (fun f : (q : I × I) →
          Metric.closedBall (0 : ℂ) (B q.1 * B q.2) => f (i, j))
        (𝓝 z) (𝓝 (z (i, j))) :=
    (continuous_apply (i, j)).tendsto z
  have hval :
      Tendsto
        (fun w : Metric.closedBall (0 : ℂ) (B i * B j) => (w : ℂ))
        (𝓝 (z (i, j))) (𝓝 (z (i, j) : ℂ)) :=
    continuous_subtype_val.tendsto (z (i, j))
  exact hval.comp (heval.comp hu)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gram_posSemidef_infinite
    {I H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : I → H) :
    (Matrix.gram ℂ v).PosSemidef := by
  refine ⟨Matrix.isHermitian_gram ℂ v, ?_⟩
  intro c
  calc
    (0 : ℂ) ≤
        ⟪c.sum (fun i z => z • v i),
          c.sum (fun i z => z • v i)⟫_ℂ :=
      RCLike.nonneg_iff.mpr ⟨inner_self_nonneg, inner_self_im _⟩
    _ = c.sum (fun i z =>
          c.sum (fun j w => star z * (Matrix.gram ℂ v) i j * w)) := by
      rw [Finsupp.sum_inner]
      apply Finsupp.sum_congr
      intro i hi
      rw [Finsupp.inner_sum]
      apply Finsupp.sum_congr
      intro j hj
      simp only [inner_smul_left, inner_smul_right,
        Matrix.gram_apply, RCLike.star_def]
      ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ L : Matrix I I ℂ,
      L.PosSemidef ∧
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (L i j)) := by
  obtain ⟨L, hconv⟩ :=
    exists_hyperfilter_gram_limit_of_pointwise_bound v B hbound
  have hhermitian : L.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    apply tendsto_nhds_unique (hconv j i).star
    have hsymm :
        (fun n => star ⟪v n j, v n i⟫_ℂ) =
          (fun n => ⟪v n i, v n j⟫_ℂ) := by
      funext n
      exact inner_conj_symm _ _
    rw [hsymm]
    exact hconv i j
  refine ⟨L, ⟨hhermitian, ?_⟩, hconv⟩
  intro c
  have hquadratic :
      Tendsto
        (fun n => c.sum fun i z =>
          c.sum fun j w => star z * ⟪v n i, v n j⟫_ℂ * w)
        (Filter.hyperfilter ℕ)
        (𝓝 (c.sum fun i z =>
          c.sum fun j w => star z * L i j * w)) := by
    simpa only [Finsupp.sum] using
      tendsto_finsetSum c.support (fun i _ =>
        tendsto_finsetSum c.support (fun j _ =>
          (tendsto_const_nhds.mul (hconv i j)).mul
            tendsto_const_nhds))
  apply ge_of_tendsto hquadratic
  exact Eventually.of_forall fun n =>
    (gram_posSemidef_infinite (v n)).2 c

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_hyperfilter_action_diagonal_positive_pair_kernel
    {G I : Type*} [Group G] {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (ρ : G →* Equiv.Perm I)
    (v : ∀ n, I × I → H n) (B : I × I → ℝ)
    (hbound : ∀ n q, ‖v n q‖ ≤ B q)
    (hdiagonal : ∀ a i j k l,
      ∀ᶠ n in Filter.atTop,
        ⟪v n (ρ a i, ρ a j), v n (ρ a k, ρ a l)⟫_ℂ =
          ⟪v n (i, j), v n (k, l)⟫_ℂ)
    (hadd : ∀ n (i j k : I),
      v n (i, j) + v n (j, k) = v n (i, k)) :
    ∃ L : Matrix (I × I) (I × I) ℂ,
      L.PosSemidef ∧
      (∀ a i j k l,
        L (ρ a i, ρ a j) (ρ a k, ρ a l) = L (i, j) (k, l)) ∧
      (∀ i j k : I, ∀ q : I × I,
        L (i, j) q + L (j, k) q = L (i, k) q) ∧
      ∀ q r, Tendsto (fun n => ⟪v n q, v n r⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (L q r)) := by
  obtain ⟨L, hpositive, hconv⟩ :=
    exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
      v B hbound
  refine ⟨L, hpositive, ?_, ?_, hconv⟩
  · intro a i j k l
    have hevent :
        (fun n =>
          ⟪v n (ρ a i, ρ a j), v n (ρ a k, ρ a l)⟫_ℂ) =ᶠ[
          (Filter.hyperfilter ℕ : Filter ℕ)]
            (fun n => ⟪v n (i, j), v n (k, l)⟫_ℂ) :=
      (hdiagonal a i j k l).filter_mono Nat.hyperfilter_le_atTop
    exact tendsto_nhds_unique
      (hconv (ρ a i, ρ a j) (ρ a k, ρ a l))
      (Tendsto.congr' hevent.symm (hconv (i, j) (k, l)))
  · intro i j k q
    have haddconv :=
      (hconv (i, j) q).add (hconv (j, k) q)
    have hfunctions :
        (fun n =>
          ⟪v n (i, j), v n q⟫_ℂ +
            ⟪v n (j, k), v n q⟫_ℂ) =
          (fun n => ⟪v n (i, k), v n q⟫_ℂ) := by
      funext n
      rw [← inner_add_left, hadd]
    exact tendsto_nhds_unique haddconv
      (by rw [hfunctions]; exact hconv (i, k) q)

end CornulierUltralimit

namespace CornulierUltralimit

open Filter
open scoped ComplexOrder InnerProductSpace Topology

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def AffineUniformGeneratorDisplacement
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) : Prop :=
  ∀ z : H, ∃ s ∈ S, (1 : ℝ) ≤ ‖α s z - z‖

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem AffineUniformGeneratorDisplacement.no_global_fixed
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    {α : G →* (H ≃ᵃⁱ[ℂ] H)} {S : Finset G}
    (h : AffineUniformGeneratorDisplacement α S) :
    ¬ ∃ z : H, ∀ g : G, α g z = z := by
  rintro ⟨z, hz⟩
  obtain ⟨s, _, hs⟩ := h z
  have hzero : (1 : ℝ) ≤ 0 := by
    simpa only [hz s, sub_self, norm_zero] using hs
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem ultrafilter_eventually_exists_finset
    {N G : Type*} (U : Ultrafilter N) (S : Finset G)
    (P : N → G → Prop)
    (h : ∀ᶠ n in (U : Filter N), ∃ s ∈ S, P n s) :
    ∃ s ∈ S, ∀ᶠ n in (U : Filter N), P n s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hempty : ∀ᶠ n in (U : Filter N), False := by
        filter_upwards [h] with n hn
        simp only [Finset.notMem_empty, false_and, exists_false] at hn
      obtain ⟨_, hn⟩ := hempty.exists
      exact hn.elim
  | @insert a S ha ih =>
      have hsplit : ∀ᶠ n in (U : Filter N),
          P n a ∨ ∃ s ∈ S, P n s := by
        filter_upwards [h] with n hn
        simpa only [Finset.mem_insert, exists_eq_or_imp] using hn
      rcases Ultrafilter.eventually_or.mp hsplit with hfirst | hrest
      · exact ⟨a, Finset.mem_insert_self a S, hfirst⟩
      · obtain ⟨s, hs, hevent⟩ := ih hrest
        exact ⟨s, Finset.mem_insert_of_mem hs, hevent⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedDisplacementCoefficients
    {G I : Type u} [Group G]
    (ρ : G →* Equiv.Perm I) (i₀ : I) (g : G)
    (c : (I × I) →₀ ℂ) : (I × I) →₀ ℂ :=
  Finsupp.mapDomain (markedPairAction ρ g) c - c +
    Finsupp.single (ρ g i₀, i₀) 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finsupp_sum_markedDisplacementCoefficients
    {G I H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ρ : G →* Equiv.Perm I) (i₀ : I) (g : G)
    (c : (I × I) →₀ ℂ) (v : I × I → H)
    (π : H ≃ₗᵢ[ℂ] H)
    (hequiv : ∀ q : I × I,
      v (ρ g q.1, ρ g q.2) = π (v q)) :
    (markedDisplacementCoefficients ρ i₀ g c).sum
        (fun q a => a • v q) =
      π (c.sum (fun q a => a • v q)) -
        c.sum (fun q a => a • v q) + v (ρ g i₀, i₀) := by
  classical
  unfold markedDisplacementCoefficients
  rw [Finsupp.sum_add_index'
      (by simp only [zero_smul, implies_true])
      (by intros; simp only [add_smul]),
    Finsupp.sum_sub_index (by intros; simp only [sub_smul]),
    Finsupp.sum_mapDomain_index (by simp only [zero_smul, implies_true])
      (by intros; simp only [add_smul]),
    Finsupp.sum_single_index (by simp only [zero_smul])]
  simp only [one_smul]
  congr 2
  calc
    c.sum (fun q a => a • v (markedPairAction ρ g q)) =
        c.sum (fun q a => a • π (v q)) := by
      apply Finsupp.sum_congr
      intro q hq
      exact congrArg (fun z : H => c q • z) (hequiv q)
    _ = π (c.sum (fun q a => a • v q)) := by
      rw [map_finsuppSum]
      simp only [map_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedOrbitAction (G : Type u) [Group G] :
    G →* Equiv.Perm (G × Bool) where
  toFun a := (Equiv.mulLeft a).prodCongr (Equiv.refl Bool)
  map_one' := by
    apply Equiv.ext
    intro x
    exact Prod.ext (one_mul x.1) rfl
  map_mul' a b := by
    apply Equiv.ext
    intro x
    exact Prod.ext (mul_assoc a b x.1) rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem markedOrbitAction_apply
    {G : Type u} [Group G] (a : G) (i : G × Bool) :
    markedOrbitAction G a i = (a * i.1, i.2) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedAffineOrbitPoint
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H) (i : G × Bool) : H :=
  α i.1 (if i.2 then x else y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def markedAffinePairDisplacement
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (q : (G × Bool) × (G × Bool)) : H :=
  markedAffineOrbitPoint α x y q.1 -
    markedAffineOrbitPoint α x y q.2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffineOrbitPoint_action
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (a : G) (i : G × Bool) :
    markedAffineOrbitPoint α x y (markedOrbitAction G a i) =
      α a (markedAffineOrbitPoint α x y i) := by
  change α (a * i.1) (if i.2 then x else y) =
    α a (α i.1 (if i.2 then x else y))
  rw [map_mul]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffinePairDisplacement_action
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (a : G) (i j : G × Bool) :
    markedAffinePairDisplacement α x y
      (markedOrbitAction G a i, markedOrbitAction G a j) =
        (α a).linearIsometryEquiv
          (markedAffinePairDisplacement α x y (i, j)) := by
  simp only [markedAffinePairDisplacement,
    markedAffineOrbitPoint_action]
  exact ((α a).map_vsub
    (markedAffineOrbitPoint α x y i)
    (markedAffineOrbitPoint α x y j)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffinePairDisplacement_inner_action
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (a : G) (i j k l : G × Bool) :
    ⟪markedAffinePairDisplacement α x y
        (markedOrbitAction G a i, markedOrbitAction G a j),
      markedAffinePairDisplacement α x y
        (markedOrbitAction G a k, markedOrbitAction G a l)⟫_ℂ =
      ⟪markedAffinePairDisplacement α x y (i, j),
        markedAffinePairDisplacement α x y (k, l)⟫_ℂ := by
  rw [markedAffinePairDisplacement_action,
    markedAffinePairDisplacement_action]
  exact (α a).linearIsometryEquiv.inner_map_map _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffinePairDisplacement_add
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (i j k : G × Bool) :
    markedAffinePairDisplacement α x y (i, j) +
      markedAffinePairDisplacement α x y (j, k) =
        markedAffinePairDisplacement α x y (i, k) := by
  simp only [markedAffinePairDisplacement]
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem markedAffinePairDisplacement_finsupp_action
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x y : H)
    (g : G) (c : ((G × Bool) × (G × Bool)) →₀ ℂ) :
    (markedDisplacementCoefficients (markedOrbitAction G)
      ((1 : G), false) g c).sum
        (fun q a => a • markedAffinePairDisplacement α x y q) =
      α g (y + c.sum (fun q a =>
        a • markedAffinePairDisplacement α x y q)) -
        (y + c.sum (fun q a =>
          a • markedAffinePairDisplacement α x y q)) := by
  let z : H := c.sum
    (fun q a => a • markedAffinePairDisplacement α x y q)
  rw [finsupp_sum_markedDisplacementCoefficients
    (markedOrbitAction G) ((1 : G), false) g c
    (markedAffinePairDisplacement α x y)
    (α g).linearIsometryEquiv
    (fun q => markedAffinePairDisplacement_action α x y g q.1 q.2)]
  have hbase :
      markedAffinePairDisplacement α x y
        (markedOrbitAction G g ((1 : G), false), ((1 : G), false)) =
        α g y - y := by
    simp only [markedAffinePairDisplacement, markedAffineOrbitPoint, markedOrbitAction_apply,
      mul_one, Bool.false_eq_true, ↓reduceIte, map_one, AffineIsometryEquiv.coe_one, id_eq]
  rw [hbase]
  have hmap : α g (y + z) =
      (α g).linearIsometryEquiv z + α g y := by
    calc
      α g (y + z) = α g (z + y) := by rw [add_comm]
      _ = (α g).linearIsometryEquiv z + α g y := by
        simpa only [vadd_eq_add] using (α g).map_vadd y z
  change (α g).linearIsometryEquiv z - z + (α g y - y) =
    α g (y + z) - (y + z)
  rw [hmap]
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem markedPairAffineAction_finsupp_action
    {G I : Type u} [Group G]
    {ρ : G →* Equiv.Perm I}
    (K : Matrix (I × I) (I × I) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization ρ K)
    (hadd : ∀ i j k : I, ∀ q : I × I,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (i₀ : I) (g : G) (c : (I × I) →₀ ℂ) :
    (markedDisplacementCoefficients ρ i₀ g c).sum
        (fun q a => a • R.realization.vector q) =
      markedPairAffineAction K R hadd i₀ g
        (c.sum (fun q a => a • R.realization.vector q)) -
        c.sum (fun q a => a • R.realization.vector q) := by
  rw [finsupp_sum_markedDisplacementCoefficients ρ i₀ g c
    R.realization.vector (R.representation g)
    (fun q => (R.equivariant g q.1 q.2).symm)]
  change _ =
    (R.representation g
      (c.sum (fun q a => a • R.realization.vector q)) +
      R.realization.vector (ρ g i₀, i₀)) -
        c.sum (fun q a => a • R.realization.vector q)
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineUniformGeneratorDisplacement_of_dense
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G)
    {T : Set H} (hT : Dense T)
    (hlower : ∀ z ∈ T, ∃ s ∈ S, (1 : ℝ) ≤ ‖α s z - z‖) :
    AffineUniformGeneratorDisplacement α S := by
  classical
  intro z
  by_contra hnot
  push Not at hnot
  let U : Set H := ⋂ s ∈ S, {w : H | ‖α s w - w‖ < (1 : ℝ)}
  have hUopen : IsOpen U := by
    apply isOpen_biInter_finset
    intro s hs
    exact isOpen_lt
      (continuous_norm.comp ((α s).continuous.sub continuous_id))
      continuous_const
  have hzU : z ∈ U := by
    simp only [U, Set.mem_iInter]
    exact hnot
  obtain ⟨w, hwT, hwU⟩ :=
    hT.exists_mem_open hUopen ⟨z, hzU⟩
  obtain ⟨s, hs, hmove⟩ := hlower w hwT
  have hsmall : ‖α s w - w‖ < (1 : ℝ) := by
    exact (Set.mem_iInter₂.mp hwU) s hs
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_marked_affine_pair_kernel
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (x y : ∀ n, H n)
    (B : (G × Bool) × (G × Bool) → ℝ)
    (hbound : ∀ n q,
      ‖markedAffinePairDisplacement (α n) (x n) (y n) q‖ ≤ B q) :
    ∃ L : Matrix ((G × Bool) × (G × Bool))
        ((G × Bool) × (G × Bool)) ℂ,
      L.PosSemidef ∧
      (∀ a i j k l,
        L (markedOrbitAction G a i, markedOrbitAction G a j)
            (markedOrbitAction G a k, markedOrbitAction G a l) =
          L (i, j) (k, l)) ∧
      (∀ i j k : G × Bool, ∀ q,
        L (i, j) q + L (j, k) q = L (i, k) q) ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪markedAffinePairDisplacement (α n) (x n) (y n) q,
              markedAffinePairDisplacement (α n) (x n) (y n) r⟫_ℂ)
          (Filter.hyperfilter ℕ) (𝓝 (L q r)) := by
  apply exists_hyperfilter_action_diagonal_positive_pair_kernel
    (markedOrbitAction G)
    (fun n => markedAffinePairDisplacement (α n) (x n) (y n))
    B hbound
  · intro a i j k l
    exact Eventually.of_forall fun n =>
      markedAffinePairDisplacement_inner_action
        (α n) (x n) (y n) a i j k l
  · intro n i j k
    exact markedAffinePairDisplacement_add (α n) (x n) (y n) i j k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tendsto_norm_sq_of_gram
    {N H : Type*} {V : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (V n)]
    [∀ n, InnerProductSpace ℂ (V n)]
    (l : Filter N) (v : ∀ n, V n) (w : H)
    (hgram : Tendsto (fun n => ⟪v n, v n⟫_ℂ)
      l (𝓝 ⟪w, w⟫_ℂ)) :
    Tendsto (fun n => ‖v n‖ ^ 2) l (𝓝 (‖w‖ ^ 2)) := by
  have hreal := (Complex.continuous_re.tendsto _).comp hgram
  change Tendsto (fun n => (⟪v n, v n⟫_ℂ).re)
    l (𝓝 (⟪w, w⟫_ℂ).re) at hreal
  convert hreal using 1
  · funext n
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (v n)
  · congr 1
    exact norm_sq_eq_re_inner (𝕜 := ℂ) w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_eq_of_gram_and_tendsto_norm
    {N H : Type*} {V : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (V n)]
    [∀ n, InnerProductSpace ℂ (V n)]
    (l : Filter N) [NeBot l]
    (v : ∀ n, V n) (w : H) (d : ℝ)
    (hgram : Tendsto (fun n => ⟪v n, v n⟫_ℂ)
      l (𝓝 ⟪w, w⟫_ℂ))
    (hnorm : Tendsto (fun n => ‖v n‖) l (𝓝 d)) :
    ‖w‖ = d := by
  have hsquare : ‖w‖ ^ 2 = d ^ 2 :=
    tendsto_nhds_unique
      (tendsto_norm_sq_of_gram l v w hgram) (hnorm.pow 2)
  have hd : 0 ≤ d :=
    ge_of_tendsto hnorm (Eventually.of_forall fun n => norm_nonneg (v n))
  nlinarith [norm_nonneg w]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem realization_vector_eq_of_kernel_rows
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) {i j : I}
    (hrows : ∀ q : I, K i q = K j q) :
    R.vector i = R.vector j := by
  have horth (q : I) :
      ⟪R.vector i - R.vector j, R.vector q⟫_ℂ = 0 := by
    rw [inner_sub_left, R.gram, R.gram, hrows q, sub_self]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_right, horth i, horth j]
  simp only [sub_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem exists_marked_affine_ultralimit
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (x y : ∀ n, H n)
    (K₁ K₂ : Subgroup G)
    (hx : ∀ n, ConnesRigidity.IsAffineFixed (α n) K₁ (x n))
    (hy : ∀ n, ConnesRigidity.IsAffineFixed (α n) K₂ (y n))
    (B : (G × Bool) × (G × Bool) → ℝ)
    (hbound : ∀ n q,
      ‖markedAffinePairDisplacement (α n) (x n) (y n) q‖ ≤ B q)
    (d : ℝ)
    (hdist : Tendsto (fun n => ‖x n - y n‖)
      Filter.atTop (𝓝 d)) :
    ∃ (L : Matrix ((G × Bool) × (G × Bool))
          ((G × Bool) × (G × Bool)) ℂ)
      (R : EquivariantMarkedHilbertKernelRealization
        (markedOrbitAction G) L)
      (hadd : ∀ i j k : G × Bool, ∀ q,
        L (i, j) q + L (j, k) q = L (i, k) q),
      L.PosSemidef ∧
      Dense (Submodule.span ℂ
        (Set.range R.realization.vector) : Set R.realization.carrier) ∧
      (∀ a i j k l,
        L (markedOrbitAction G a i, markedOrbitAction G a j)
            (markedOrbitAction G a k, markedOrbitAction G a l) =
          L (i, j) (k, l)) ∧
      ConnesRigidity.IsAffineFixed
        (markedPairAffineAction L R hadd ((1 : G), false)) K₁
        (markedPairPoint R ((1 : G), false) ((1 : G), true)) ∧
      ConnesRigidity.IsAffineFixed
        (markedPairAffineAction L R hadd ((1 : G), false)) K₂
        (markedPairPoint R ((1 : G), false) ((1 : G), false)) ∧
      ‖markedPairPoint R ((1 : G), false) ((1 : G), true) -
        markedPairPoint R ((1 : G), false) ((1 : G), false)‖ = d ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪markedAffinePairDisplacement (α n) (x n) (y n) q,
              markedAffinePairDisplacement (α n) (x n) (y n) r⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector q,
            R.realization.vector r⟫_ℂ) := by
  obtain ⟨L, hpositive, hdiagonal, hadd, hconv⟩ :=
    exists_marked_affine_pair_kernel α x y B hbound
  obtain ⟨R, hdense⟩ := exists_equivariantMarkedHilbertKernelRealization_dense
    (markedOrbitAction G) L hpositive hdiagonal
  refine ⟨L, R, hadd, hpositive, hdense, hdiagonal, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [markedPairAffineAction_point]
    apply realization_vector_eq_of_kernel_rows R.realization
    intro q
    let p : (G × Bool) × (G × Bool) :=
      (markedOrbitAction G (k : G) ((1 : G), true), ((1 : G), false))
    let p' : (G × Bool) × (G × Bool) :=
      (((1 : G), true), ((1 : G), false))
    have heq (n : ℕ) :
        markedAffinePairDisplacement (α n) (x n) (y n) p =
          markedAffinePairDisplacement (α n) (x n) (y n) p' := by
      simp [p, p', markedAffinePairDisplacement,
        markedAffineOrbitPoint, hx n k]
    exact tendsto_nhds_unique (hconv p q)
      (by simpa only [heq] using hconv p' q)
  · intro k
    rw [markedPairAffineAction_point]
    apply realization_vector_eq_of_kernel_rows R.realization
    intro q
    let p : (G × Bool) × (G × Bool) :=
      (markedOrbitAction G (k : G) ((1 : G), false), ((1 : G), false))
    let p' : (G × Bool) × (G × Bool) :=
      (((1 : G), false), ((1 : G), false))
    have heq (n : ℕ) :
        markedAffinePairDisplacement (α n) (x n) (y n) p =
          markedAffinePairDisplacement (α n) (x n) (y n) p' := by
      simp [p, p', markedAffinePairDisplacement,
        markedAffineOrbitPoint, hy n k]
    exact tendsto_nhds_unique (hconv p q)
      (by simpa only [heq] using hconv p' q)
  · let p : (G × Bool) × (G × Bool) :=
      (((1 : G), true), ((1 : G), false))
    have hgram :
        Tendsto (fun n => ⟪x n - y n, x n - y n⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector p,
            R.realization.vector p⟫_ℂ) := by
      have h := hconv p p
      rw [← R.realization.gram p p] at h
      simpa [p, markedAffinePairDisplacement,
        markedAffineOrbitPoint] using h
    rw [markedPairPoint_sub L R hadd]
    exact norm_eq_of_gram_and_tendsto_norm
      (Filter.hyperfilter ℕ)
      (fun n => x n - y n) (R.realization.vector p) d hgram
      (hdist.mono_left Nat.hyperfilter_le_atTop)
  · intro q r
    simpa only [R.realization.gram] using hconv q r

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineUniformGeneratorDisplacement_marked_limit
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (x y : ∀ n, H n)
    (S : Finset G)
    (hnormalized : ∀ n,
      AffineUniformGeneratorDisplacement (α n) S)
    (K : Matrix ((G × Bool) × (G × Bool))
      ((G × Bool) × (G × Bool)) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization
      (markedOrbitAction G) K)
    (hadd : ∀ i j k : G × Bool, ∀ q,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (hdense : Dense (Submodule.span ℂ
      (Set.range R.realization.vector) : Set R.realization.carrier))
    (hgram : ∀ q r,
      Tendsto
        (fun n =>
          ⟪markedAffinePairDisplacement (α n) (x n) (y n) q,
            markedAffinePairDisplacement (α n) (x n) (y n) r⟫_ℂ)
        (Filter.hyperfilter ℕ)
        (𝓝 ⟪R.realization.vector q,
          R.realization.vector r⟫_ℂ)) :
    AffineUniformGeneratorDisplacement
      (markedPairAffineAction K R hadd ((1 : G), false)) S := by
  apply affineUniformGeneratorDisplacement_of_dense
    (markedPairAffineAction K R hadd ((1 : G), false)) S hdense
  intro z hz
  obtain ⟨c, rfl⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  let zₙ : ∀ n, H n := fun n =>
    y n + c.sum (fun q a =>
      a • markedAffinePairDisplacement (α n) (x n) (y n) q)
  have hevent : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ∃ s ∈ S, (1 : ℝ) ≤ ‖α n s (zₙ n) - zₙ n‖ :=
    Eventually.of_forall fun n => hnormalized n (zₙ n)
  obtain ⟨s, hs, hmove⟩ :=
    ultrafilter_eventually_exists_finset (Filter.hyperfilter ℕ)
      S (fun n s => (1 : ℝ) ≤ ‖α n s (zₙ n) - zₙ n‖) hevent
  refine ⟨s, hs, ?_⟩
  have hlimit :=
    tendsto_norm_finsupp_sum_of_gram
      (Filter.hyperfilter ℕ)
      (fun n => markedAffinePairDisplacement (α n) (x n) (y n))
      R.realization.vector hgram
      (markedDisplacementCoefficients (markedOrbitAction G)
        ((1 : G), false) s c)
  rw [markedPairAffineAction_finsupp_action
    K R hadd ((1 : G), false) s c] at hlimit
  have hlimit' :
      Tendsto (fun n => ‖α n s (zₙ n) - zₙ n‖)
        (Filter.hyperfilter ℕ)
        (𝓝 ‖markedPairAffineAction K R hadd
          ((1 : G), false) s
            (c.sum (fun q a => a • R.realization.vector q)) -
          c.sum (fun q a => a • R.realization.vector q)‖) := by
    simpa only [markedAffinePairDisplacement_finsupp_action,
      zₙ] using hlimit
  exact ge_of_tendsto hlimit' hmove

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem exists_marked_affine_ultralimit_normalized
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (x y : ∀ n, H n)
    (K₁ K₂ : Subgroup G)
    (hx : ∀ n, ConnesRigidity.IsAffineFixed (α n) K₁ (x n))
    (hy : ∀ n, ConnesRigidity.IsAffineFixed (α n) K₂ (y n))
    (B : (G × Bool) × (G × Bool) → ℝ)
    (hbound : ∀ n q,
      ‖markedAffinePairDisplacement (α n) (x n) (y n) q‖ ≤ B q)
    (d : ℝ)
    (hdist : Tendsto (fun n => ‖x n - y n‖)
      Filter.atTop (𝓝 d))
    (S : Finset G)
    (hnormalized : ∀ n,
      AffineUniformGeneratorDisplacement (α n) S) :
    ∃ (L : Matrix ((G × Bool) × (G × Bool))
          ((G × Bool) × (G × Bool)) ℂ)
      (R : EquivariantMarkedHilbertKernelRealization
        (markedOrbitAction G) L)
      (hadd : ∀ i j k : G × Bool, ∀ q,
        L (i, j) q + L (j, k) q = L (i, k) q),
      L.PosSemidef ∧
      Dense (Submodule.span ℂ
        (Set.range R.realization.vector) : Set R.realization.carrier) ∧
      (∀ a i j k l,
        L (markedOrbitAction G a i, markedOrbitAction G a j)
            (markedOrbitAction G a k, markedOrbitAction G a l) =
          L (i, j) (k, l)) ∧
      ConnesRigidity.IsAffineFixed
        (markedPairAffineAction L R hadd ((1 : G), false)) K₁
        (markedPairPoint R ((1 : G), false) ((1 : G), true)) ∧
      ConnesRigidity.IsAffineFixed
        (markedPairAffineAction L R hadd ((1 : G), false)) K₂
        (markedPairPoint R ((1 : G), false) ((1 : G), false)) ∧
      ‖markedPairPoint R ((1 : G), false) ((1 : G), true) -
        markedPairPoint R ((1 : G), false) ((1 : G), false)‖ = d ∧
      AffineUniformGeneratorDisplacement
        (markedPairAffineAction L R hadd ((1 : G), false)) S ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪markedAffinePairDisplacement (α n) (x n) (y n) q,
              markedAffinePairDisplacement (α n) (x n) (y n) r⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector q,
            R.realization.vector r⟫_ℂ) := by
  obtain ⟨L, R, hadd, hpositive, hdense, hdiagonal,
    hleft, hright, hdist', hgram⟩ :=
      exists_marked_affine_ultralimit α x y K₁ K₂ hx hy B hbound
        d hdist
  refine ⟨L, R, hadd, hpositive, hdense, hdiagonal,
    hleft, hright, hdist', ?_, hgram⟩
  exact affineUniformGeneratorDisplacement_marked_limit
    α x y S hnormalized L R hadd hdense hgram

end CornulierUltralimit

end

section

open ConnesRigidity

section

universe u

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def normalFixedSubmodule (N : Subgroup G)
    (π : UnitaryRepresentation G H) : Submodule ℂ H where
  carrier := {x : H | ∀ n : N, (π (n : G) : H →L[ℂ] H) x = x}
  zero_mem' n := map_zero (π (n : G) : H →L[ℂ] H)
  add_mem' hx hy n := by
    rw [map_add, hx n, hy n]
  smul_mem' c x hx n := by
    rw [map_smul, hx n]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem mem_normalFixedSubmodule
    (N : Subgroup G) (π : UnitaryRepresentation G H) (x : H) :
    x ∈ normalFixedSubmodule N π ↔
      ∀ n : N, (π (n : G) : H →L[ℂ] H) x = x := Iff.rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalFixedSubmodule_isClosed
    (N : Subgroup G) (π : UnitaryRepresentation G H) :
    IsClosed (normalFixedSubmodule N π : Set H) := by
  have hset : (normalFixedSubmodule N π : Set H) =
      ⋂ n : N, {x : H | (π (n : G) : H →L[ℂ] H) x = x} := by
    ext x
    simp only [SetLike.mem_coe, mem_normalFixedSubmodule, Subtype.forall, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun n =>
    isClosed_eq (π (n : G) : H →L[ℂ] H).continuous continuous_id

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance normalFixedSubmodule_completeSpace
    (N : Subgroup G) (π : UnitaryRepresentation G H) :
    CompleteSpace (normalFixedSubmodule N π) :=
  (normalFixedSubmodule_isClosed N π).isComplete.completeSpace_coe

section Normality

variable (N : Subgroup G) [N.Normal] (π : UnitaryRepresentation G H)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitary_mem_normalFixedSubmodule
    (g : G) {x : H} (hx : x ∈ normalFixedSubmodule N π) :
    (π g : H →L[ℂ] H) x ∈ normalFixedSubmodule N π := by
  intro n
  let n' : N :=
    ⟨g⁻¹ * (n : G) * g,
      by simpa only [inv_inv] using
        (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩
  calc
    (π (n : G) : H →L[ℂ] H) ((π g : H →L[ℂ] H) x) =
        (π ((n : G) * g) : H →L[ℂ] H) x := by
          rw [map_mul]
          rfl
    _ = (π (g * (n' : G)) : H →L[ℂ] H) x := by
      have heq : (n : G) * g = g * (g⁻¹ * (n : G) * g) := by
        group
      change (π ((n : G) * g) : H →L[ℂ] H) x =
        (π (g * (g⁻¹ * (n : G) * g)) : H →L[ℂ] H) x
      rw [heq]
    _ = (π g : H →L[ℂ] H)
          ((π (n' : G) : H →L[ℂ] H) x) := by
      rw [map_mul]
      rfl
    _ = (π g : H →L[ℂ] H) x := by rw [hx n']

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem unitary_mem_normalFixedSubmodule_orthogonal
    (g : G) {x : H} (hx : x ∈ (normalFixedSubmodule N π)ᗮ) :
    (π g : H →L[ℂ] H) x ∈ (normalFixedSubmodule N π)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy' := unitary_mem_normalFixedSubmodule N π g⁻¹ hy
  have hinner := (Submodule.mem_orthogonal _ _).mp hx
    ((π g⁻¹ : H →L[ℂ] H) y) hy'
  calc
    @inner ℂ H _ y ((π g : H →L[ℂ] H) x) =
        @inner ℂ H _
          ((π g : H →L[ℂ] H)
            ((π g⁻¹ : H →L[ℂ] H) y))
          ((π g : H →L[ℂ] H) x) := by
      congr 1
      change y = (↑(π g * π g⁻¹) : H →L[ℂ] H) y
      rw [← map_mul]
      simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
    _ = @inner ℂ H _
          ((π g⁻¹ : H →L[ℂ] H) y) x :=
      Unitary.inner_map_map (π g)
        ((π g⁻¹ : H →L[ℂ] H) y) x
    _ = 0 := hinner













/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def normalFixedOrthogonalLinearIsometryEquiv (g : G) :
    (normalFixedSubmodule N π)ᗮ ≃ₗᵢ[ℂ]
      (normalFixedSubmodule N π)ᗮ where
  toFun x :=
    ⟨(π g : H →L[ℂ] H) x,
      unitary_mem_normalFixedSubmodule_orthogonal N π g x.property⟩
  invFun x :=
    ⟨(π g⁻¹ : H →L[ℂ] H) x,
      unitary_mem_normalFixedSubmodule_orthogonal N π g⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑(π g⁻¹ * π g) : H →L[ℂ] H) x = x
    rw [← map_mul]
    simp only [inv_mul_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    apply Subtype.ext
    change (↑(π g * π g⁻¹) : H →L[ℂ] H) x = x
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := Subtype.ext
    (map_add (π g : H →L[ℂ] H) (x : H) (y : H))
  map_smul' c x := Subtype.ext
    (map_smul (π g : H →L[ℂ] H) c (x : H))
  norm_map' x := Unitary.norm_map (π g) (x : H)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def normalFixedOrthogonalRepresentation :
    UnitaryRepresentation G ((normalFixedSubmodule N π)ᗮ) where
  toFun g := Unitary.linearIsometryEquiv.symm
    (normalFixedOrthogonalLinearIsometryEquiv N π g)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π 1 : H →L[ℂ] H) (x : H) = x
    simp only [map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π (g * h) : H →L[ℂ] H) (x : H) =
      (π g : H →L[ℂ] H) ((π h : H →L[ℂ] H) (x : H))
    rw [map_mul]
    rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem normalFixedOrthogonalRepresentation_no_fixed
    (x : (normalFixedSubmodule N π)ᗮ)
    (hx : ∀ n : N,
      (normalFixedOrthogonalRepresentation N π (n : G) :
        (normalFixedSubmodule N π)ᗮ →L[ℂ]
          (normalFixedSubmodule N π)ᗮ) x = x) : x = 0 := by
  have hfixed : (x : H) ∈ normalFixedSubmodule N π := by
    intro n
    exact congrArg Subtype.val (hx n)
  have hinner : @inner ℂ H _ (x : H) (x : H) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hfixed x.property
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem normalFixed_starProjection_commute
    (g : G) (x : H) :
    (normalFixedSubmodule N π).starProjection
        ((π g : H →L[ℂ] H) x) =
      (π g : H →L[ℂ] H)
        ((normalFixedSubmodule N π).starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact unitary_mem_normalFixedSubmodule N π g
      (Submodule.starProjection_apply_mem
        (normalFixedSubmodule N π) x)
  · rw [← map_sub]
    exact unitary_mem_normalFixedSubmodule_orthogonal N π g
      (Submodule.sub_starProjection_mem_orthogonal x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem normalFixed_orthogonalResidual_displacement_le
    (g : G) (x : H) :
    ‖(π g : H →L[ℂ] H)
          (x - (normalFixedSubmodule N π).starProjection x) -
        (x - (normalFixedSubmodule N π).starProjection x)‖ ≤
      ‖(π g : H →L[ℂ] H) x - x‖ := by
  calc
    ‖(π g : H →L[ℂ] H)
          (x - (normalFixedSubmodule N π).starProjection x) -
        (x - (normalFixedSubmodule N π).starProjection x)‖ =
        ‖((π g : H →L[ℂ] H) x - x) -
          ((π g : H →L[ℂ] H)
            ((normalFixedSubmodule N π).starProjection x) -
              (normalFixedSubmodule N π).starProjection x)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ = ‖((π g : H →L[ℂ] H) x - x) -
          (normalFixedSubmodule N π).starProjection
            ((π g : H →L[ℂ] H) x - x)‖ := by
      rw [map_sub, normalFixed_starProjection_commute]
    _ = ‖(normalFixedSubmodule N π)ᗮ.starProjection
          ((π g : H →L[ℂ] H) x - x)‖ := by
      rw [Submodule.starProjection_orthogonal_val]
    _ ≤ ‖(π g : H →L[ℂ] H) x - x‖ :=
      (normalFixedSubmodule N π)ᗮ.norm_starProjection_apply_le _

end Normality

end

end

section

open ConnesRigidity Bornology Filter Metric Set Topology

universe u

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def hilbertSquaredEnclosingRadii (S : Set V) : Set ℝ :=
  {r | 0 ≤ r ∧ ∃ c : V, ∀ z ∈ S, ‖c - z‖ ^ 2 ≤ r}

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertSquaredEnclosingRadii_nonempty
    {S : Set V} (hS : IsBounded S) :
    (hilbertSquaredEnclosingRadii S).Nonempty := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨(max R 0) ^ 2, sq_nonneg _, 0, ?_⟩
  intro z hz
  have hnorm : ‖z‖ ≤ max R 0 := (hR z hz).trans (le_max_left _ _)
  simpa only [zero_sub, norm_neg, ge_iff_le] using (pow_le_pow_left₀ (norm_nonneg z) hnorm 2)

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertSquaredEnclosingRadii_bddBelow (S : Set V) :
    BddBelow (hilbertSquaredEnclosingRadii S) :=
  ⟨0, fun _ hr => hr.1⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def hilbertCircumradiusSq (S : Set V) : ℝ :=
  sInf (hilbertSquaredEnclosingRadii S)

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbert_midpoint_sq_parallelogram
    (x y z : V) :
    4 * ‖midpoint ℂ x y - z‖ ^ 2 + ‖x - y‖ ^ 2 =
      2 * (‖x - z‖ ^ 2 + ‖y - z‖ ^ 2) := by
  have hmid : midpoint ℂ x y - z =
      midpoint ℂ (x - z) (y - z) := by
    simpa only [midpoint_self, vsub_eq_sub] using
      (midpoint_vsub_midpoint (R := ℂ) x y z z)
  have hsum : (x - z) + (y - z) =
      (2 : ℂ) • (midpoint ℂ x y - z) := by
    rw [hmid, midpoint_eq_smul_add, smul_smul]
    norm_num
  have hsub : (x - z) - (y - z) = x - y := by abel
  have hp := parallelogram_law_with_norm ℂ (x - z) (y - z)
  rw [hsum, hsub, norm_smul] at hp
  norm_num at hp
  linarith

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertSquaredEnclosingRadii_midpoint
    {S : Set V} (hS : S.Nonempty)
    {x y : V} {r s : ℝ}
    (hx : ∀ z ∈ S, ‖x - z‖ ^ 2 ≤ r)
    (hy : ∀ z ∈ S, ‖y - z‖ ^ 2 ≤ s) :
    (r + s) / 2 - ‖x - y‖ ^ 2 / 4 ∈
      hilbertSquaredEnclosingRadii S := by
  have hbound : ∀ z ∈ S,
      ‖midpoint ℂ x y - z‖ ^ 2 ≤
        (r + s) / 2 - ‖x - y‖ ^ 2 / 4 := by
    intro z hz
    have hp := hilbert_midpoint_sq_parallelogram x y z
    linarith [hx z hz, hy z hz]
  obtain ⟨z, hz⟩ := hS
  exact ⟨(sq_nonneg _).trans (hbound z hz),
    midpoint ℂ x y, hbound⟩

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertCircumradiusSq_le
    (S : Set V) {r : ℝ}
    (hr : r ∈ hilbertSquaredEnclosingRadii S) :
    hilbertCircumradiusSq S ≤ r :=
  csInf_le (hilbertSquaredEnclosingRadii_bddBelow S) hr

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_hilbert_near_circumcenter
    {S : Set V} (hS : IsBounded S) (n : ℕ) :
    ∃ c : V, ∀ z ∈ S,
      ‖c - z‖ ^ 2 ≤
        hilbertCircumradiusSq S + 1 / ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt
    (hilbertSquaredEnclosingRadii_nonempty hS)
    (lt_add_of_pos_right _ hpos)
  obtain ⟨c, hc⟩ := hr.2
  exact ⟨c, fun z hz => (hc z hz).trans (le_of_lt hlt)⟩

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbert_near_circumcenter_dist_sq_le
    {S : Set V} (hSne : S.Nonempty)
    {x y : V} {ε η : ℝ}
    (hx : ∀ z ∈ S,
      ‖x - z‖ ^ 2 ≤ hilbertCircumradiusSq S + ε)
    (hy : ∀ z ∈ S,
      ‖y - z‖ ^ 2 ≤ hilbertCircumradiusSq S + η) :
    ‖x - y‖ ^ 2 ≤ 2 * ε + 2 * η := by
  have hmid := hilbertCircumradiusSq_le S
    (hilbertSquaredEnclosingRadii_midpoint hSne hx hy)
  linarith

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbert_near_circumcenter_cauchy
    {S : Set V} (hSne : S.Nonempty)
    (c : ℕ → V)
    (hc : ∀ n z, z ∈ S →
      ‖c n - z‖ ^ 2 ≤
        hilbertCircumradiusSq S + 1 / ((n : ℝ) + 1)) :
    CauchySeq c := by
  rw [cauchySeq_iff_le_tendsto_0]
  refine ⟨fun N => Real.sqrt (4 / ((N : ℝ) + 1)),
    fun N => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro n m N hn hm
    have hpair := hilbert_near_circumcenter_dist_sq_le hSne
      (hc n) (hc m)
    have hdenn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hdenm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hdenN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfracn : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    have hfracm : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    have hsquare : ‖c n - c m‖ ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
      calc
        ‖c n - c m‖ ^ 2 ≤
            2 * (1 / ((n : ℝ) + 1)) +
              2 * (1 / ((m : ℝ) + 1)) := hpair
        _ ≤ 2 * (1 / ((N : ℝ) + 1)) +
            2 * (1 / ((N : ℝ) + 1)) := by gcongr
        _ = 4 / ((N : ℝ) + 1) := by ring
    rw [dist_eq_norm]
    exact Real.le_sqrt_of_sq_le hsquare
  · have hzero :
        Tendsto (fun n : ℕ => 4 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    change Tendsto (Real.sqrt ∘ fun n : ℕ => 4 / ((n : ℝ) + 1))
      atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hzero

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_hilbert_circumcenter
    {S : Set V} (hSne : S.Nonempty) (hS : IsBounded S) :
    ∃ c : V, ∀ z ∈ S,
      ‖c - z‖ ^ 2 ≤ hilbertCircumradiusSq S := by
  choose c hc using fun n : ℕ => exists_hilbert_near_circumcenter hS n
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete
    (hilbert_near_circumcenter_cauchy hSne c hc)
  refine ⟨p, ?_⟩
  intro z hz
  have hleft : Tendsto (fun n : ℕ => ‖c n - z‖ ^ 2)
      atTop (𝓝 (‖p - z‖ ^ 2)) :=
    (hp.sub tendsto_const_nhds).norm.pow 2
  have hright : Tendsto
      (fun n : ℕ => hilbertCircumradiusSq S + 1 / ((n : ℝ) + 1))
      atTop (𝓝 (hilbertCircumradiusSq S)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlimit := hleft.sub hright
  have hnonpos : ‖p - z‖ ^ 2 - hilbertCircumradiusSq S ≤ 0 :=
    le_of_tendsto' hlimit (fun n => sub_nonpos.mpr (hc n z hz))
  linarith

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbert_circumcenter_unique
    {S : Set V} (hSne : S.Nonempty)
    {x y : V}
    (hx : ∀ z ∈ S, ‖x - z‖ ^ 2 ≤ hilbertCircumradiusSq S)
    (hy : ∀ z ∈ S, ‖y - z‖ ^ 2 ≤ hilbertCircumradiusSq S) :
    x = y := by
  have hdist := hilbert_near_circumcenter_dist_sq_le
    hSne (ε := 0) (η := 0) (by simpa only [add_zero] using hx) (by simpa only [add_zero] using hy)
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [sq_nonneg ‖x - y‖, norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def hilbertCircumcenter
    (S : Set V) (hSne : S.Nonempty) (hS : IsBounded S) : V :=
  (exists_hilbert_circumcenter hSne hS).choose

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hilbertCircumcenter_encloses
    (S : Set V) (hSne : S.Nonempty) (hS : IsBounded S)
    (z : V) (hz : z ∈ S) :
    ‖hilbertCircumcenter S hSne hS - z‖ ^ 2 ≤
      hilbertCircumradiusSq S :=
  (exists_hilbert_circumcenter hSne hS).choose_spec z hz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineIsometryEquiv_hilbertCircumcenter_fixed
    (S : Set V) (hSne : S.Nonempty) (hS : IsBounded S)
    (f : V ≃ᵃⁱ[ℂ] V) (hf : f '' S = S) :
    f (hilbertCircumcenter S hSne hS) =
      hilbertCircumcenter S hSne hS := by
  apply hilbert_circumcenter_unique hSne
  · intro z hz
    have hzimage : z ∈ f '' S := by rwa [hf]
    obtain ⟨w, hw, rfl⟩ := hzimage
    have hdist := f.dist_map
      (hilbertCircumcenter S hSne hS) w
    rw [dist_eq_norm, dist_eq_norm] at hdist
    rw [hdist]
    exact hilbertCircumcenter_encloses S hSne hS w hw
  · exact hilbertCircumcenter_encloses S hSne hS

section AffineActions

variable {G : Type u} [Group G]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineSubgroupOrbit
    (α : AffineHilbertAction G V) (N : Subgroup G) (x : V) : Set V :=
  Set.range fun n : N => α (n : G) x

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineSubgroupOrbit_nonempty
    (α : AffineHilbertAction G V) (N : Subgroup G) (x : V) :
    (affineSubgroupOrbit α N x).Nonempty := by
  refine ⟨x, 1, ?_⟩
  simp only [OneMemClass.coe_one, map_one, AffineIsometryEquiv.coe_one, id_eq]

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineSubgroupOrbit_image
    (α : AffineHilbertAction G V) (N : Subgroup G)
    (x : V) (n : N) :
    α (n : G) '' affineSubgroupOrbit α N x =
      affineSubgroupOrbit α N x := by
  ext z
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨n * k, ?_⟩
    change α ((n : G) * (k : G)) x = α (n : G) (α (k : G) x)
    rw [map_mul]
    rfl
  · rintro ⟨k, rfl⟩
    let m : N := n⁻¹ * k
    refine ⟨α (m : G) x, ⟨m, rfl⟩, ?_⟩
    calc
      α (n : G) (α (m : G) x) =
          α ((n : G) * (m : G)) x := by
        rw [map_mul]
        rfl
      _ = α (k : G) x := by
        congr 1
        dsimp [m]
        simp only [mul_inv_cancel_left]

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineSubgroupOrbit_bounded
    (α : AffineHilbertAction G V) (N : Subgroup G) (x : V)
    (hbound : ∃ C : ℝ, ∀ n : N, ‖α (n : G) x - x‖ ≤ C) :
    IsBounded (affineSubgroupOrbit α N x) := by
  obtain ⟨C, hC⟩ := hbound
  apply (Metric.isBounded_iff_subset_closedBall x).2
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  change dist (α (n : G) x) x ≤ C
  simpa only [dist_eq_norm] using hC n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_subgroup_fixedPoint_of_bounded_orbit
    (α : AffineHilbertAction G V) (N : Subgroup G) (x : V)
    (hbound : ∃ C : ℝ, ∀ n : N, ‖α (n : G) x - x‖ ≤ C) :
    ∃ y : V, IsAffineFixed α N y := by
  let S : Set V := affineSubgroupOrbit α N x
  have hSne : S.Nonempty := affineSubgroupOrbit_nonempty α N x
  have hS : IsBounded S := affineSubgroupOrbit_bounded α N x hbound
  refine ⟨hilbertCircumcenter S hSne hS, ?_⟩
  intro n
  exact affineIsometryEquiv_hilbertCircumcenter_fixed
    S hSne hS (α (n : G))
    (affineSubgroupOrbit_image α N x n)

end AffineActions

end

section

open ConnesRigidity

universe u

section AffineContradiction

variable {G V : Type u} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasCorelativeAffineOrbitBound
    (H : Subgroup G) : Prop :=
  ∀ (W : Type u)
    (_ : NormedAddCommGroup W)
    (_ : InnerProductSpace ℂ W)
    (_ : CompleteSpace W)
    (α : AffineHilbertAction G W) (x : W),
      (∃ C : ℝ, ∀ h : H, ‖α (h : G) x - x‖ ≤ C) →
        ∃ C : ℝ, ∀ g : G, ‖α g x - x‖ ≤ C

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulier_normalized_minimizing_action_false
    (H K₁ K₂ : Subgroup G) (S : Finset G)
    (hgen : K₁ ⊔ K₂ = ⊤)
    (hH₁ : H ≤ Subgroup.normalizer (K₁ : Set G))
    (hH₂ : H ≤ Subgroup.normalizer (K₂ : Set G))
    (hcorel : HasCorelativeAffineOrbitBound H)
    (α : AffineHilbertAction G V)
    (hnormal : CornulierUltralimit.AffineUniformGeneratorDisplacement α S)
    (x₁ x₂ : V)
    (hmin : IsMinimizingAffinePair α K₁ K₂ x₁ x₂)
    (hno : ∀ x : V,
      (affineLinearRepresentation α).IsInvariant x → x = 0) :
    False := by
  have hHfixed : ∀ h : H, α (h : G) x₁ = x₁ := by
    intro h
    exact (hmin.normalizer_fixed_of_no_linear_invariants
      hgen hno (h : G) (hH₁ h.property) (hH₂ h.property)).1
  have hHbound : ∃ C : ℝ, ∀ h : H, ‖α (h : G) x₁ - x₁‖ ≤ C := by
    refine ⟨0, ?_⟩
    intro h
    simp only [hHfixed h, sub_self, norm_zero, Std.le_refl]
  obtain ⟨C, hC⟩ :=
    hcorel V inferInstance inferInstance inferInstance α x₁ hHbound
  obtain ⟨z, hz⟩ := affine_subgroup_fixedPoint_of_bounded_orbit
    α (⊤ : Subgroup G) x₁
      ⟨C, fun g => hC (g : G)⟩
  apply hnormal.no_global_fixed
  exact ⟨z, fun g => hz ⟨g, Subgroup.mem_top g⟩⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def realInnerCharacter (f : G →* Multiplicative V) (v : V) :
    G →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (@inner ℂ V _ v
    (Multiplicative.toAdd (f g))).re
  map_one' := by
    change (@inner ℂ V _ v
      (Multiplicative.toAdd (f 1))).re = 0
    simp only [map_one, toAdd_one, inner_zero_right, Complex.zero_re]
  map_mul' g h := by
    change (@inner ℂ V _ v
      (Multiplicative.toAdd (f (g * h)))).re =
        (@inner ℂ V _ v (Multiplicative.toAdd (f g))).re +
          (@inner ℂ V _ v (Multiplicative.toAdd (f h))).re
    rw [map_mul]
    change (@inner ℂ V _ v
      (Multiplicative.toAdd (f g) + Multiplicative.toAdd (f h))).re = _
    rw [inner_add_right, Complex.add_re]

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem multiplicativeHilbertHom_eq_zero_of_no_real_characters
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (f : G →* Multiplicative V) (g : G) :
    Multiplicative.toAdd (f g) = 0 := by
  let v : V := Multiplicative.toAdd (f g)
  have h := hreal (realInnerCharacter f v) g
  change (@inner ℂ V _ v v).re = 0 at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have hsquare : ‖v‖ ^ 2 = 0 := by
    norm_cast at h
  have hnorm : ‖v‖ = 0 := (sq_eq_zero_iff).mp hsquare
  exact norm_eq_zero.mp hnorm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineInvariantProjectionHom
    (α : AffineHilbertAction G V) :
    G →* Multiplicative
      (normalFixedSubmodule (⊤ : Subgroup G)
        (affineLinearRepresentation α)) where
  toFun g := Multiplicative.ofAdd
    ⟨(normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)).starProjection (α g 0),
      Submodule.starProjection_apply_mem _ _⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [map_one, AffineIsometryEquiv.coe_one, id_eq, map_zero, toAdd_ofAdd, toAdd_one,
      ZeroMemClass.coe_zero]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)).starProjection (α (g * h) 0) =
        (normalFixedSubmodule (⊤ : Subgroup G)
          (affineLinearRepresentation α)).starProjection (α g 0) +
        (normalFixedSubmodule (⊤ : Subgroup G)
          (affineLinearRepresentation α)).starProjection (α h 0)
    rw [map_mul]
    have hact : α g (α h 0) =
        (affineLinearRepresentation α g : V →L[ℂ] V) (α h 0) +
          α g 0 := by
      have he := (α g).map_vsub (α h 0) 0
      change (affineLinearRepresentation α g : V →L[ℂ] V)
        (α h 0 - 0) = α g (α h 0) - α g 0 at he
      simpa only [sub_zero] using (eq_sub_iff_add_eq.mp he).symm
    change (normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)).starProjection
        (α g (α h 0)) = _
    rw [hact, map_add,
      normalFixed_starProjection_commute (⊤ : Subgroup G)
        (affineLinearRepresentation α) g (α h 0)]
    have hfixed :=
      (Submodule.starProjection_apply_mem
        (normalFixedSubmodule (⊤ : Subgroup G)
          (affineLinearRepresentation α)) (α h 0))
          (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G))
    rw [hfixed]
    abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineInvariantProjection_zero_of_no_real_characters
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g : G) :
    (normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)).starProjection (α g 0) = 0 := by
  have h := multiplicativeHilbertHom_eq_zero_of_no_real_characters
    hreal (affineInvariantProjectionHom α) g
  exact congrArg Subtype.val h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineOrthogonalComplement
    (α : AffineHilbertAction G V) : Submodule ℂ V :=
  (normalFixedSubmodule (⊤ : Subgroup G)
    (affineLinearRepresentation α))ᗮ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance affineOrthogonalComplement_completeSpace
    (α : AffineHilbertAction G V) :
    CompleteSpace (affineOrthogonalComplement α) := by
  unfold affineOrthogonalComplement
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineTranslation_mem_orthogonal_of_no_real_characters
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g : G) :
    α g 0 ∈ affineOrthogonalComplement α := by
  exact (Submodule.starProjection_apply_eq_zero_iff _).mp
    (affineInvariantProjection_zero_of_no_real_characters hreal α g)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineOrthogonalTranslation
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g : G) : affineOrthogonalComplement α :=
  ⟨α g 0, affineTranslation_mem_orthogonal_of_no_real_characters hreal α g⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineOrthogonalLinearHom
    (α : AffineHilbertAction G V) :
    G →* (affineOrthogonalComplement α ≃ₗᵢ[ℂ]
      affineOrthogonalComplement α) where
  toFun g := normalFixedOrthogonalLinearIsometryEquiv
    (⊤ : Subgroup G) (affineLinearRepresentation α) g
  map_one' := by
    ext x
    change (affineLinearRepresentation α 1 : V →L[ℂ] V) x = x
    simp only [map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    ext x
    change (affineLinearRepresentation α (g * h) : V →L[ℂ] V) x =
      (affineLinearRepresentation α g : V →L[ℂ] V)
        ((affineLinearRepresentation α h : V →L[ℂ] V) x)
    rw [map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineOrthogonalTranslation_mul
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g h : G) :
    affineOrthogonalTranslation hreal α (g * h) =
      affineOrthogonalTranslation hreal α g +
        affineOrthogonalLinearHom α g
          (affineOrthogonalTranslation hreal α h) := by
  apply Subtype.ext
  change α (g * h) 0 =
    α g 0 + (affineLinearRepresentation α g : V →L[ℂ] V) (α h 0)
  rw [map_mul]
  change α g (α h 0) =
    α g 0 + (affineLinearRepresentation α g : V →L[ℂ] V) (α h 0)
  have he := (α g).map_vsub (α h 0) 0
  change (affineLinearRepresentation α g : V →L[ℂ] V)
    (α h 0 - 0) = α g (α h 0) - α g 0 at he
  simpa only [sub_zero, add_comm] using (eq_sub_iff_add_eq.mp he).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def affineOrthogonalAction
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) :
    AffineHilbertAction G (affineOrthogonalComplement α) :=
  CornulierUltralimit.unitaryCocycleAffineAction
    (affineOrthogonalLinearHom α)
    (affineOrthogonalTranslation hreal α)
    (affineOrthogonalTranslation_mul hreal α)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem affineOrthogonalAction_apply_coe
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V)
    (g : G) (x : affineOrthogonalComplement α) :
    (affineOrthogonalAction hreal α g x : V) = α g (x : V) := by
  change (affineLinearRepresentation α g : V →L[ℂ] V) (x : V) +
    α g 0 = α g (x : V)
  have he := (α g).map_vsub (x : V) 0
  change (affineLinearRepresentation α g : V →L[ℂ] V)
    ((x : V) - 0) = α g (x : V) - α g 0 at he
  simpa only [sub_zero] using (eq_sub_iff_add_eq.mp he)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineOrthogonalAction_no_linear_invariants
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V)
    (x : affineOrthogonalComplement α)
    (hx : (affineLinearRepresentation
      (affineOrthogonalAction hreal α)).IsInvariant x) : x = 0 := by
  apply normalFixedOrthogonalRepresentation_no_fixed
    (⊤ : Subgroup G) (affineLinearRepresentation α) x
  intro g
  have h := hx (g : G)
  change ((affineOrthogonalAction hreal α (g : G)).linearIsometryEquiv x) = x at h
  rw [affineOrthogonalAction,
    CornulierUltralimit.unitaryCocycleAffineAction_linearIsometryEquiv] at h
  apply Subtype.ext
  change (affineLinearRepresentation α (g : G) : V →L[ℂ] V) (x : V) = x
  exact congrArg Subtype.val h

end AffineContradiction

end

section

open ConnesRigidity
open scoped ENNReal

section

universe u

variable {G V : Type u} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_add_ne_zero_of_unit_coordinates
    (x : lp (fun _ : ℕ => V) 2)
    (v : ℕ → V) (hv : ∀ n, ‖v n‖ = 1) :
    ∃ n : ℕ, x n + v n ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hnorm : ∀ n : ℕ, ‖x n‖ = 1 := by
    intro n
    have hx : x n = -v n := eq_neg_of_add_eq_zero_left (h n)
    rw [hx, norm_neg, hv]
  have hsummable : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_ofNat, ENNReal.toReal_ofNat] using (lp.memℓp x).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hconstant : Summable (fun _ : ℕ => (1 : ℝ)) := by
    convert hsummable using 1
    funext n
    simp only [hnorm n, Real.rpow_ofNat, one_pow]
  exact (Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hconstant).false

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineDiagonal_subgroup_nonzero_invariant_of_fixed
    (π : UnitaryRepresentation G V)
    (v : ℕ → V) (hv : ∀ n, ‖v n‖ = 1)
    (α : AffineHilbertAction G (lp (fun _ : ℕ => V) 2))
    (hα : ∀ (g : G) (x : lp (fun _ : ℕ => V) 2) (n : ℕ),
      (α g x) n = (π g : V →L[ℂ] V) (x n + v n) - v n)
    (N : Subgroup G)
    (x : lp (fun _ : ℕ => V) 2)
    (hx : IsAffineFixed α N x) :
    ∃ ξ : V, ξ ≠ 0 ∧
      ∀ g : N, (π (g : G) : V →L[ℂ] V) ξ = ξ := by
  obtain ⟨n, hn⟩ := exists_add_ne_zero_of_unit_coordinates x v hv
  refine ⟨x n + v n, hn, ?_⟩
  intro g
  have hfixed := congrArg (fun y : lp (fun _ : ℕ => V) 2 => y n) (hx g)
  rw [hα] at hfixed
  exact sub_eq_iff_eq_add.mp hfixed

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem affineDiagonal_nonzero_invariant_of_fixed
    (π : UnitaryRepresentation G V)
    (v : ℕ → V) (hv : ∀ n, ‖v n‖ = 1)
    (α : AffineHilbertAction G (lp (fun _ : ℕ => V) 2))
    (hα : ∀ (g : G) (x : lp (fun _ : ℕ => V) 2) (n : ℕ),
      (α g x) n = (π g : V →L[ℂ] V) (x n + v n) - v n)
    (x : lp (fun _ : ℕ => V) 2)
    (hx : ∀ g : G, α g x = x) :
    ∃ ξ : V, ξ ≠ 0 ∧ π.IsInvariant ξ := by
  obtain ⟨ξ, hξ, hfixed⟩ :=
    affineDiagonal_subgroup_nonzero_invariant_of_fixed
      π v hv α hα ⊤ x (fun g => hx (g : G))
  exact ⟨ξ, hξ, fun g => hfixed ⟨g, Subgroup.mem_top g⟩⟩

end

end

section

open ConnesRigidity Filter
open scoped ENNReal

universe u

variable {G V : Type u} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem diagonalDisplacement_memℓp_of_summable
    (π : UnitaryRepresentation G V) (v : ℕ → V) (g : G)
    (hsum : Summable fun n : ℕ =>
      ‖(π g : V →L[ℂ] V) (v n) - v n‖ ^ (2 : ℕ)) :
    Memℓp (fun n : ℕ => (π g : V →L[ℂ] V) (v n) - v n) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using hsum

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def diagonalDisplacement
    (π : UnitaryRepresentation G V) (v : ℕ → V)
    (hsum : ∀ g : G, Summable fun n : ℕ =>
      ‖(π g : V →L[ℂ] V) (v n) - v n‖ ^ (2 : ℕ))
    (g : G) : lp (fun _ : ℕ => V) 2 :=
  ⟨fun n => (π g : V →L[ℂ] V) (v n) - v n,
    diagonalDisplacement_memℓp_of_summable π v g (hsum g)⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def diagonalLinearIsometryHom
    (π : UnitaryRepresentation G V) :
    G →* (lp (fun _ : ℕ => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => V) 2) where
  toFun g := crossedFiberwiseEquiv (K := ℕ)
    (Unitary.linearIsometryEquiv (π g))
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    apply lp.ext
    funext n
    change (π 1 : V →L[ℂ] V) (x n) = x n
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    apply lp.ext
    funext n
    change (π (g * h) : V →L[ℂ] V) (x n) =
      (π g : V →L[ℂ] V) ((π h : V →L[ℂ] V) (x n))
    rw [map_mul]
    rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def diagonalAffineAction
    (π : UnitaryRepresentation G V) (v : ℕ → V)
    (hsum : ∀ g : G, Summable fun n : ℕ =>
      ‖(π g : V →L[ℂ] V) (v n) - v n‖ ^ (2 : ℕ)) :
    AffineHilbertAction G (lp (fun _ : ℕ => V) 2) where
  toFun g := (diagonalLinearIsometryHom π g).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℂ (diagonalDisplacement π v hsum g))
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x
    apply lp.ext
    funext n
    change (π 1 : V →L[ℂ] V) (x n) +
      ((π 1 : V →L[ℂ] V) (v n) - v n) = x n
    rw [map_one]
    simp only [OneMemClass.coe_one, one_apply_eq_self, sub_self, add_zero]
  map_mul' g h := by
    apply AffineIsometryEquiv.ext
    intro x
    apply lp.ext
    funext n
    change
      (π (g * h) : V →L[ℂ] V) (x n) +
        ((π (g * h) : V →L[ℂ] V) (v n) - v n) =
      (π g : V →L[ℂ] V)
        ((π h : V →L[ℂ] V) (x n) +
          ((π h : V →L[ℂ] V) (v n) - v n)) +
        ((π g : V →L[ℂ] V) (v n) - v n)
    rw [map_mul]
    change
      (π g : V →L[ℂ] V) ((π h : V →L[ℂ] V) (x n)) +
        ((π g : V →L[ℂ] V) ((π h : V →L[ℂ] V) (v n)) - v n) = _
    rw [map_add, map_sub]
    abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem diagonalAffineAction_apply
    (π : UnitaryRepresentation G V) (v : ℕ → V)
    (hsum : ∀ g : G, Summable fun n : ℕ =>
      ‖(π g : V →L[ℂ] V) (v n) - v n‖ ^ (2 : ℕ))
    (g : G) (x : lp (fun _ : ℕ => V) 2) (n : ℕ) :
    diagonalAffineAction π v hsum g x n =
      (π g : V →L[ℂ] V) (x n + v n) - v n := by
  change (π g : V →L[ℂ] V) (x n) +
      ((π g : V →L[ℂ] V) (v n) - v n) = _
  rw [map_add]
  abel

section CountableNormalization

variable [Countable G]

/-- A local encoding used to exhaust the countable group. -/
private local instance instEncodableLeanPool : Encodable G := Encodable.ofCountable G

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def countableExhaustion (n : ℕ) : Finset G :=
  (Finset.range (n + 1)).filterMap (Encodable.decode₂ G) (by
    intro i j g hi hj
    exact (Encodable.mem_decode₂.mp hi).symm.trans
      (Encodable.mem_decode₂.mp hj))

omit [Group G] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_countableExhaustion (g : G) (n : ℕ)
    (hn : Encodable.encode g ≤ n) :
    g ∈ countableExhaustion (G := G) n := by
  unfold countableExhaustion
  rw [Finset.mem_filterMap]
  refine ⟨Encodable.encode g, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_iff.mpr hn
  · exact Encodable.decode₂_encode g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_almostInvariantUnitSequence
    (π : UnitaryRepresentation G V)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    ∃ ξ : ℕ → V,
      (∀ n : ℕ, ‖ξ n‖ = 1) ∧
      ∀ (g : G) (n : ℕ), Encodable.encode g ≤ n →
        ‖(π g : V →L[ℂ] V) (ξ n) - ξ n‖ <
          ((1 / 2 : ℝ) ^ n) := by
  have hchoose : ∀ n : ℕ, ∃ v : V,
      ‖v‖ = 1 ∧
      ∀ g ∈ countableExhaustion (G := G) n,
        ‖(π g : V →L[ℂ] V) v - v‖ < ((1 / 2 : ℝ) ^ n) := by
    intro n
    apply hπ (countableExhaustion (G := G) n)
      ((1 / 2 : ℝ) ^ n)
    positivity
  choose ξ hξ hbound using hchoose
  refine ⟨ξ, hξ, ?_⟩
  intro g n hn
  exact hbound n g (mem_countableExhaustion g n hn)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem exists_almostInvariantUnitSequence_summable
    (π : UnitaryRepresentation G V)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    ∃ ξ : ℕ → V,
      (∀ n : ℕ, ‖ξ n‖ = 1) ∧
      ∀ g : G,
        Summable (fun n : ℕ =>
          ‖(π g : V →L[ℂ] V) (ξ n) - ξ n‖ ^ (2 : ℕ)) := by
  obtain ⟨ξ, hunit, hbound⟩ :=
    exists_almostInvariantUnitSequence π hπ
  refine ⟨ξ, hunit, ?_⟩
  intro g
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (Encodable.encode g)] with n hn
  have hnonneg : 0 ≤ ‖(π g : V →L[ℂ] V) (ξ n) - ξ n‖ :=
    norm_nonneg _
  have hle : ‖(π g : V →L[ℂ] V) (ξ n) - ξ n‖ ≤
      (1 / 2 : ℝ) ^ n := (hbound g n hn).le
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((1 / 2 : ℝ) ^ n) ^ 2 := by nlinarith
    _ = (1 / 4 : ℝ) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num

end CountableNormalization

end

section

open Matrix
open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierColumnShear (s : Fin 3 → IntegralPolynomial) :
    integralElementaryGroup :=
  cornulierRoot 0 3 (by decide) (s 0) *
    cornulierRoot 1 3 (by decide) (s 1) *
    cornulierRoot 2 3 (by decide) (s 2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierRowShear (s : Fin 3 → IntegralPolynomial) :
    integralElementaryGroup :=
  cornulierRoot 3 0 (by decide) (s 0) *
    cornulierRoot 3 1 (by decide) (s 1) *
    cornulierRoot 3 2 (by decide) (s 2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnShear_mem (s : Fin 3 → IntegralPolynomial) :
    cornulierColumnShear s ∈ cornulierK₁ := by
  unfold cornulierColumnShear
  exact cornulierK₁.mul_mem
    (cornulierK₁.mul_mem (cornulierRoot_mem_K₁ 0 (by decide) (s 0))
      (cornulierRoot_mem_K₁ 1 (by decide) (s 1)))
    (cornulierRoot_mem_K₁ 2 (by decide) (s 2))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowShear_mem (s : Fin 3 → IntegralPolynomial) :
    cornulierRowShear s ∈ cornulierK₂ := by
  unfold cornulierRowShear
  exact cornulierK₂.mul_mem
    (cornulierK₂.mul_mem (cornulierRoot_mem_K₂ 0 (by decide) (s 0))
      (cornulierRoot_mem_K₂ 1 (by decide) (s 1)))
    (cornulierRoot_mem_K₂ 2 (by decide) (s 2))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem columnShear_mul_castSucc (s : Fin 3 → IntegralPolynomial)
    (g : integralElementaryGroup) (i : Fin 3) (j : Fin 4) :
    ((cornulierColumnShear s * g : integralElementaryGroup).val :
      Matrix (Fin 4) (Fin 4) IntegralPolynomial) i.castSucc j =
      (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i.castSucc j +
        s i * (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j := by
  change
    ((Matrix.transvection (0 : Fin 4) 3 (s 0) *
      Matrix.transvection (1 : Fin 4) 3 (s 1) *
      Matrix.transvection (2 : Fin 4) 3 (s 2) * g.val.val :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial)) i.castSucc j = _
  fin_cases i <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem columnShear_mul_last (s : Fin 3 → IntegralPolynomial)
    (g : integralElementaryGroup) (j : Fin 4) :
    ((cornulierColumnShear s * g : integralElementaryGroup).val :
      Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j =
      (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j := by
  change
    ((Matrix.transvection (0 : Fin 4) 3 (s 0) *
      Matrix.transvection (1 : Fin 4) 3 (s 1) *
      Matrix.transvection (2 : Fin 4) 3 (s 2) * g.val.val :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial)) 3 j = _
  simp only [transvection, Fin.isValue, Matrix.mul_apply, Matrix.add_apply, Fin.reduceEq, false_and,
    not_false_eq_true, single_apply_of_ne, add_zero, Fin.sum_univ_four, ne_eq, one_apply_ne,
    one_ne_zero, zero_mul, one_apply_eq, one_mul, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rowShear_mul_last (s : Fin 3 → IntegralPolynomial)
    (g : integralElementaryGroup) (j : Fin 4) :
    ((cornulierRowShear s * g : integralElementaryGroup).val :
      Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j =
      (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j +
        ∑ i : Fin 3, s i *
          (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i.castSucc j := by
  change
    ((Matrix.transvection (3 : Fin 4) 0 (s 0) *
      Matrix.transvection (3 : Fin 4) 1 (s 1) *
      Matrix.transvection (3 : Fin 4) 2 (s 2) * g.val.val :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial)) 3 j = _
  simp only [transvection, Fin.isValue, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
    ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne, single_apply_same, zero_add, false_and,
    single_apply_of_ne, add_zero, zero_ne_one, and_false, zero_mul, one_apply_eq, one_mul, mul_one,
    one_ne_zero, mul_zero, Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one,
    Fin.reduceCastSucc]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mul_rowShear_castSucc (s : Fin 3 → IntegralPolynomial)
    (g : integralElementaryGroup) (i : Fin 4) (j : Fin 3) :
    ((g * cornulierRowShear s : integralElementaryGroup).val :
      Matrix (Fin 4) (Fin 4) IntegralPolynomial) i j.castSucc =
      (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i j.castSucc +
        (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i 3 * s j := by
  change
    ((g.val.val * (Matrix.transvection (3 : Fin 4) 0 (s 0) *
      Matrix.transvection (3 : Fin 4) 1 (s 1) *
      Matrix.transvection (3 : Fin 4) 2 (s 2)) :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial)) i j.castSucc = _
  simp only [← mul_assoc]
  fin_cases j <;>
    simp [Matrix.mul_transvection_apply_same,
      Matrix.mul_transvection_apply_of_ne, mul_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mul_rowShear_last (s : Fin 3 → IntegralPolynomial)
    (g : integralElementaryGroup) (i : Fin 4) :
    ((g * cornulierRowShear s : integralElementaryGroup).val :
      Matrix (Fin 4) (Fin 4) IntegralPolynomial) i 3 =
      (g.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i 3 := by
  change
    ((g.val.val * (Matrix.transvection (3 : Fin 4) 0 (s 0) *
      Matrix.transvection (3 : Fin 4) 1 (s 1) *
      Matrix.transvection (3 : Fin 4) 2 (s 2)) :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial)) i 3 = _
  simp only [← mul_assoc]
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, mul_transvection_apply_of_ne]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierBoundedFactorization_of_stableRange
    (hstable : IntegralPolynomialStableRangeThree) :
    CornulierBoundedFactorization := by
  intro g
  obtain ⟨s, hs⟩ :=
    integralSpecialLinear_lastColumn_stableRange_shorten hstable g.val
  let p : integralElementaryGroup := cornulierColumnShear s
  let g₁ : integralElementaryGroup := p * g
  have hcolumn : UnimodularRow
      (fun i : Fin 3 =>
        (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i.castSucc 3) := by
    simpa only [g₁, p, columnShear_mul_castSucc] using hs
  obtain ⟨c, hc⟩ := hcolumn
  let qcoeff : Fin 3 → IntegralPolynomial :=
    fun i => c i * (1 -
      (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3)
  let q : integralElementaryGroup := cornulierRowShear qcoeff
  let g₂ : integralElementaryGroup := q * g₁
  have hg₂last :
      (g₂.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3 = 1 := by
    change
      ((cornulierRowShear qcoeff * g₁ : integralElementaryGroup).val :
        Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3 = 1
    rw [rowShear_mul_last]
    change
      (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3 +
        ∑ i : Fin 3, (c i * (1 -
          (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3)) *
            (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial)
              i.castSucc 3 = 1
    simp only [Fin.sum_univ_three] at hc ⊢
    linear_combination
      (1 - (g₁.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3) * hc
  let lcoeff : Fin 3 → IntegralPolynomial :=
    fun i => -
      (g₂.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i.castSucc 3
  let rcoeff : Fin 3 → IntegralPolynomial :=
    fun i => -
      (g₂.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 i.castSucc
  let l : integralElementaryGroup := cornulierColumnShear lcoeff
  let r : integralElementaryGroup := cornulierRowShear rcoeff
  let b : integralElementaryGroup := l * g₂ * r
  have hb : b ∈ cornulierH := by
    change
      (∀ i : Fin 4,
        (b.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) i 3 =
          if i = 3 then 1 else 0) ∧
      (∀ j : Fin 4,
        (b.val : Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 j =
          if (3 : Fin 4) = j then 1 else 0)
    constructor
    · intro i
      fin_cases i
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 0 3 = 0
        rw [mul_rowShear_last]
        simpa [lcoeff, hg₂last] using
          (columnShear_mul_castSucc lcoeff g₂ (0 : Fin 3) 3)
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 1 3 = 0
        rw [mul_rowShear_last]
        simpa [lcoeff, hg₂last] using
          (columnShear_mul_castSucc lcoeff g₂ (1 : Fin 3) 3)
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 2 3 = 0
        rw [mul_rowShear_last]
        simpa [lcoeff, hg₂last] using
          (columnShear_mul_castSucc lcoeff g₂ (2 : Fin 3) 3)
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3 = 1
        rw [mul_rowShear_last, columnShear_mul_last]
        exact hg₂last
    · intro j
      fin_cases j
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 0 = 0
        have hrow := mul_rowShear_castSucc rcoeff
          (cornulierColumnShear lcoeff * g₂) 3 (0 : Fin 3)
        have hzero := columnShear_mul_last lcoeff g₂ (0 : Fin 4)
        have hlast := columnShear_mul_last lcoeff g₂ (3 : Fin 4)
        simpa [hzero, hlast, rcoeff, hg₂last] using hrow
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 1 = 0
        have hrow := mul_rowShear_castSucc rcoeff
          (cornulierColumnShear lcoeff * g₂) 3 (1 : Fin 3)
        have hzero := columnShear_mul_last lcoeff g₂ (1 : Fin 4)
        have hlast := columnShear_mul_last lcoeff g₂ (3 : Fin 4)
        simpa [hzero, hlast, rcoeff, hg₂last] using hrow
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 2 = 0
        have hrow := mul_rowShear_castSucc rcoeff
          (cornulierColumnShear lcoeff * g₂) 3 (2 : Fin 3)
        have hzero := columnShear_mul_last lcoeff g₂ (2 : Fin 4)
        have hlast := columnShear_mul_last lcoeff g₂ (3 : Fin 4)
        simpa [hzero, hlast, rcoeff, hg₂last] using hrow
      · change
          (((cornulierColumnShear lcoeff * g₂) *
              cornulierRowShear rcoeff : integralElementaryGroup).val :
            Matrix (Fin 4) (Fin 4) IntegralPolynomial) 3 3 = 1
        rw [mul_rowShear_last, columnShear_mul_last]
        exact hg₂last
  refine ⟨p⁻¹, cornulierK₁.inv_mem (cornulierColumnShear_mem s),
    q⁻¹, cornulierK₂.inv_mem (cornulierRowShear_mem qcoeff),
    l⁻¹, cornulierK₁.inv_mem (cornulierColumnShear_mem lcoeff),
    b, hb, r⁻¹, cornulierK₂.inv_mem (cornulierRowShear_mem rcoeff), ?_⟩
  dsimp [b, g₂, g₁]
  group

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierBoundedFactorization : CornulierBoundedFactorization :=
  cornulierBoundedFactorization_of_stableRange
    integralPolynomial_stableRangeThree

end

section

open Matrix

variable {A : Type} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem rankTwo_transvection_smul_single
    {i j : Fin 2} (hij : i ≠ j) (a b : A) :
    (Matrix.SpecialLinearGroup.transvection hij a) •
        (Pi.single j b : Fin 2 → A) =
      Pi.single j b + Pi.single i (a * b) := by
  ext k
  simp only [Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup.transvection_coe,
    smul_eq_mulVec, mulVec_single, Pi.smul_apply, col_apply, Matrix.add_apply, Matrix.one_apply,
    eq_comm, single_apply, and_true, smul_add, smul_ite, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, smul_zero, Pi.add_apply, Pi.single_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryRankTwo (A : Type) [CommRing A] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) A) :=
  Subgroup.closure
    {g | ∃ (i j : Fin 2) (hij : i ≠ j) (a : A),
      Matrix.SpecialLinearGroup.transvection hij a = g}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryRankTwoRoot {i j : Fin 2} (hij : i ≠ j) (a : A) :
    elementaryRankTwo A :=
  ⟨Matrix.SpecialLinearGroup.transvection hij a,
    Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def rankTwoLinearAction (A : Type) [CommRing A] :
    Matrix.SpecialLinearGroup (Fin 2) A →*
      MulAut (Multiplicative (Fin 2 → A)) where
  toFun g := AddEquiv.toMultiplicative
    (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' 1 (Multiplicative.toAdd v) =
      Multiplicative.toAdd v
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' (g * h) (Multiplicative.toAdd v) =
      Matrix.SpecialLinearGroup.toLin' g
        (Matrix.SpecialLinearGroup.toLin' h (Multiplicative.toAdd v))
    rw [map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryRankTwoAction (A : Type) [CommRing A] :
    elementaryRankTwo A →* MulAut (Multiplicative (Fin 2 → A)) :=
  (rankTwoLinearAction A).comp (elementaryRankTwo A).subtype

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev ElementaryRankTwoSemidirect (A : Type) [CommRing A] :=
  SemidirectProduct (Multiplicative (Fin 2 → A))
    (elementaryRankTwo A) (elementaryRankTwoAction A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryRankTwoTranslationSubgroup (A : Type) [CommRing A] :
    Subgroup (ElementaryRankTwoSemidirect A) :=
  (SemidirectProduct.inl : Multiplicative (Fin 2 → A) →*
    ElementaryRankTwoSemidirect A).range

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem elementaryRankTwoAction_toAdd
    (g : elementaryRankTwo A) (v : Multiplicative (Fin 2 → A)) :
    Multiplicative.toAdd (elementaryRankTwoAction A g v) =
      (g : Matrix.SpecialLinearGroup (Fin 2) A) • Multiplicative.toAdd v := by
  rfl

open scoped commutatorElement

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance elementaryRankTwoMatrix_countable [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) := by
  let f : Matrix.SpecialLinearGroup (Fin 2) A →
      Fin 2 → Fin 2 → A := fun g i j => g i j
  exact (show Function.Injective f by
    intro g h hgh
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun hgh i) j).countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance elementaryRankTwo_countable [Countable A] :
    Countable (elementaryRankTwo A) := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance elementaryRankTwoMultiplicative_countable [Countable A] :
    Countable (Multiplicative (Fin 2 → A)) :=
  (Multiplicative.toAdd (α := Fin 2 → A)).injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance elementaryRankTwoSemidirect_countable [Countable A] :
    Countable (ElementaryRankTwoSemidirect A) :=
  SemidirectProduct.equivProd.injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryRankTwoGroup : ConnesRigidity.CountableDiscreteGroup where
  Carrier := ElementaryRankTwoSemidirect IntegralPolynomial
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev integralElementaryRankTwoTranslationSubgroup :
    Subgroup integralElementaryRankTwoGroup :=
  elementaryRankTwoTranslationSubgroup IntegralPolynomial

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryRankTwoActingGroup :
    ConnesRigidity.CountableDiscreteGroup where
  Carrier := elementaryRankTwo IntegralPolynomial
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev integralElementaryRankTwoInl :
    Multiplicative (Fin 2 → IntegralPolynomial) →*
      integralElementaryRankTwoGroup :=
  SemidirectProduct.inl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev integralElementaryRankTwoInr :
    integralElementaryRankTwoActingGroup →*
      integralElementaryRankTwoGroup :=
  SemidirectProduct.inr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev integralElementaryRankTwoProjection :
    integralElementaryRankTwoGroup →*
      integralElementaryRankTwoActingGroup :=
  SemidirectProduct.rightHom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryRankTwoSplitAbelianExtension :
    SplitAbelianExtension (Fin 2 → IntegralPolynomial)
      integralElementaryRankTwoGroup
      integralElementaryRankTwoActingGroup where
  inclusion := integralElementaryRankTwoInl
  quotient := integralElementaryRankTwoProjection
  splitting := integralElementaryRankTwoInr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative
    (Fin 2 → IntegralPolynomial)).toMonoidHom.comp
      (elementaryRankTwoAction IntegralPolynomial)
  conjugation g v := by
    change
      (⟨1, (g : elementaryRankTwo IntegralPolynomial)⟩ :
        ElementaryRankTwoSemidirect IntegralPolynomial) *
        (⟨Multiplicative.ofAdd v, 1⟩ :
          ElementaryRankTwoSemidirect IntegralPolynomial) *
        (⟨1, (g : elementaryRankTwo IntegralPolynomial)⟩ :
          ElementaryRankTwoSemidirect IntegralPolynomial)⁻¹ =
        (⟨(elementaryRankTwoAction IntegralPolynomial) g
          (Multiplicative.ofAdd v), 1⟩ :
          ElementaryRankTwoSemidirect IntegralPolynomial)
    refine SemidirectProduct.ext ?_ ?_
    · simp
    · change (g : elementaryRankTwo IntegralPolynomial) * 1 * g⁻¹ = 1
      rw [mul_one, mul_inv_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralElementaryRankTwoSplitAbelianExtension_range :
    integralElementaryRankTwoSplitAbelianExtension.inclusion.range =
      integralElementaryRankTwoTranslationSubgroup := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance integralElementaryRankTwoTranslationSubgroup_normal :
    integralElementaryRankTwoTranslationSubgroup.Normal := by
  rw [← integralElementaryRankTwoSplitAbelianExtension_range,
    ← integralElementaryRankTwoSplitAbelianExtension.exact]
  infer_instance

end

section

open ConnesRigidity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasUniformRelativeKazhdanDisplacement
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ (F : Finset G) (δ : ℝ), 0 < δ ∧
      ∀ (W : Type u)
        (_ : NormedAddCommGroup W)
        (_ : InnerProductSpace ℂ W)
        (_ : CompleteSpace W)
        (π : UnitaryRepresentation G W) (ξ : W),
        ‖ξ‖ = 1 →
          (∀ g ∈ F, ‖(π g : W →L[ℂ] W) ξ - ξ‖ < δ) →
            ∀ n : N, ‖(π (n : G) : W →L[ℂ] W) ξ - ξ‖ < ε

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsRelativeKazhdanPair
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G)
    (F : Finset G) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ (W : Type u)
      (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℂ W)
      (_ : CompleteSpace W)
      (π : UnitaryRepresentation G W) (ξ : W),
      ‖ξ‖ = 1 →
        (∀ g ∈ F, ‖(π g : W →L[ℂ] W) ξ - ξ‖ < κ) →
          ∃ η : W, η ≠ 0 ∧
            ∀ n : N, (π (n : G) : W →L[ℂ] W) η = η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem HasUniformRelativeKazhdanDisplacement.map
    {G H : CountableDiscreteGroup.{u}} {N : Subgroup G}
    (h : HasUniformRelativeKazhdanDisplacement G N) (f : G →* H) :
    HasUniformRelativeKazhdanDisplacement H (N.map f) := by
  classical
  intro ε hε
  obtain ⟨F, δ, hδ, hF⟩ := h ε hε
  refine ⟨F.image f, δ, hδ, ?_⟩
  intro W _ _ _ π ξ hξ hsmall
  have hsmall' :
      ∀ g ∈ F, ‖((π.comp f) g : W →L[ℂ] W) ξ - ξ‖ < δ := by
    intro g hg
    exact hsmall (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hN := hF W inferInstance inferInstance inferInstance
    (π.comp f) ξ hξ hsmall'
  rintro ⟨_, ⟨g, hg, rfl⟩⟩
  exact hN ⟨g, hg⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem uniformRelativeKazhdanDisplacement_of_pair
    {G : CountableDiscreteGroup.{u}} (N : Subgroup G) [N.Normal]
    {F : Finset G} {κ : ℝ}
    (hpair : IsRelativeKazhdanPair G N F κ) :
    HasUniformRelativeKazhdanDisplacement G N := by
  intro ε hε
  have hκ : 0 < κ := hpair.1
  refine ⟨F, κ * ε / 2, div_pos (mul_pos hκ hε) (by norm_num), ?_⟩
  intro W _ _ _ π ξ hξ hsmall
  let M : Submodule ℂ W := normalFixedSubmodule N π
  let z : W := ξ - M.starProjection ξ
  have hzmem : z ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal ξ
  have hzsmall : ‖z‖ < ε / 2 := by
    by_contra hnot
    have hzlower : ε / 2 ≤ ‖z‖ := le_of_not_gt hnot
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hzlower
      linarith
    let w : Mᗮ := ⟨((‖z‖ : ℂ)⁻¹) • z, (Mᗮ).smul_mem _ hzmem⟩
    have hwnorm : ‖w‖ = 1 := norm_smul_inv_norm hz
    have hwsmall :
        ∀ g ∈ F,
          ‖(normalFixedOrthogonalRepresentation N π g :
            Mᗮ →L[ℂ] Mᗮ) w - w‖ < κ := by
      intro g hg
      have hcontract :
          ‖(π g : W →L[ℂ] W) z - z‖ ≤
            ‖(π g : W →L[ℂ] W) ξ - ξ‖ :=
        normalFixed_orthogonalResidual_displacement_le N π g ξ
      have hwformula :
          ‖(normalFixedOrthogonalRepresentation N π g :
              Mᗮ →L[ℂ] Mᗮ) w - w‖ =
            ‖(π g : W →L[ℂ] W) z - z‖ / ‖z‖ := by
        change ‖(π g : W →L[ℂ] W)
          (((‖z‖ : ℂ)⁻¹) • z) - ((‖z‖ : ℂ)⁻¹) • z‖ = _
        rw [map_smul, ← smul_sub]
        rw [norm_smul, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg z)]
        simp only [div_eq_mul_inv, mul_comm]
      rw [hwformula]
      apply (div_lt_iff₀ (norm_pos_iff.mpr hz)).2
      have hsmallg := hsmall g hg
      nlinarith [hpair.1]
    obtain ⟨η, hη, hηfixed⟩ := hpair.2
      Mᗮ inferInstance inferInstance inferInstance
      (normalFixedOrthogonalRepresentation N π) w hwnorm hwsmall
    exact hη (normalFixedOrthogonalRepresentation_no_fixed N π η hηfixed)
  intro n
  have hfixed :
      (π (n : G) : W →L[ℂ] W) (M.starProjection ξ) =
        M.starProjection ξ :=
    (Submodule.starProjection_apply_mem M ξ) n
  calc
    ‖(π (n : G) : W →L[ℂ] W) ξ - ξ‖ =
        ‖(π (n : G) : W →L[ℂ] W) z - z‖ := by
      dsimp [z]
      rw [map_sub, hfixed]
      congr 1
      abel
    _ ≤ ‖(π (n : G) : W →L[ℂ] W) z‖ + ‖z‖ := norm_sub_le _ _
    _ = 2 * ‖z‖ := by rw [Unitary.norm_map]; ring
    _ < ε := by linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shalomPolynomialKazhdanConstant (m : ℕ) : ℝ :=
  2 / (22 : ℝ) ^ (m + 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shalomPolynomialKazhdanConstant_pos (m : ℕ) :
    0 < shalomPolynomialKazhdanConstant m := by
  unfold shalomPolynomialKazhdanConstant
  positivity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem shalomPolynomialKazhdanConstant_zero :
    shalomPolynomialKazhdanConstant 0 = (1 / 11 : ℝ) := by
  norm_num [shalomPolynomialKazhdanConstant]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem shalomPolynomialKazhdanConstant_one :
    shalomPolynomialKazhdanConstant 1 = (1 / 242 : ℝ) := by
  norm_num [shalomPolynomialKazhdanConstant]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shalomPolynomialTranslation (i : Fin 2) (a : IntegralPolynomial) :
    integralElementaryRankTwoGroup :=
  integralElementaryRankTwoInl
    (Multiplicative.ofAdd (Pi.single i a : Fin 2 → IntegralPolynomial))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shalomPolynomialUpperShear (a : IntegralPolynomial) :
    integralElementaryRankTwoGroup :=
  integralElementaryRankTwoInr
    (elementaryRankTwoRoot (show (0 : Fin 2) ≠ 1 by decide) a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shalomPolynomialLowerShear (a : IntegralPolynomial) :
    integralElementaryRankTwoGroup :=
  integralElementaryRankTwoInr
    (elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide) a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shalomPolynomialTranslationGenerators :
    Finset integralElementaryRankTwoGroup := by
  classical
  exact
    {shalomPolynomialTranslation 0 1,
      shalomPolynomialTranslation 0 (-1),
      shalomPolynomialTranslation 1 1,
      shalomPolynomialTranslation 1 (-1)}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shalomPolynomialShearGenerators :
    Finset integralElementaryRankTwoGroup := by
  classical
  exact
    {shalomPolynomialUpperShear 1,
      shalomPolynomialUpperShear (-1),
      shalomPolynomialUpperShear Polynomial.X,
      shalomPolynomialUpperShear (-Polynomial.X),
      shalomPolynomialLowerShear 1,
      shalomPolynomialLowerShear (-1),
      shalomPolynomialLowerShear Polynomial.X,
      shalomPolynomialLowerShear (-Polynomial.X)}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shalomPolynomialKazhdanGenerators :
    Finset integralElementaryRankTwoGroup := by
  classical
  exact shalomPolynomialTranslationGenerators ∪
    shalomPolynomialShearGenerators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def ShalomIntegralPolynomialRelativePair : Prop :=
  IsRelativeKazhdanPair integralElementaryRankTwoGroup
    integralElementaryRankTwoTranslationSubgroup
    shalomPolynomialKazhdanGenerators
    (shalomPolynomialKazhdanConstant 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shalom_uniformPolynomialTranslationDisplacement
    (h : ShalomIntegralPolynomialRelativePair) :
    HasUniformRelativeKazhdanDisplacement integralElementaryRankTwoGroup
      integralElementaryRankTwoTranslationSubgroup :=
  uniformRelativeKazhdanDisplacement_of_pair
    integralElementaryRankTwoTranslationSubgroup h

end

section

open ConnesRigidity
open scoped BigOperators

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussian_defect_le_parameter (u : ℝ) :
    1 - Real.exp (-u) ≤ u := by
  have h := Real.add_one_le_exp (-u)
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussian_parameter_lt_one_of_displacement
    {t r d : ℝ}
    (_ht : 0 < t) (_hr : 0 ≤ r) (hd : 0 ≤ d) (hdlt : d < 1)
    (hsq : d ^ 2 = 2 * (1 - Real.exp (-(t * r ^ 2)))) :
    t * r ^ 2 < 1 := by
  have hdsq : d ^ 2 < 1 := by nlinarith
  have hexpneg : (2 : ℝ)⁻¹ < Real.exp (-(t * r ^ 2)) := by
    norm_num
    linarith
  have hexp : Real.exp (t * r ^ 2) < 2 := by
    apply (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2)
      (Real.exp_pos (t * r ^ 2))).mp
    simpa only [Real.exp_neg] using hexpneg
  have hlower := Real.add_one_le_exp (t * r ^ 2)
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussian_affine_displacement_le
    {t r d : ℝ}
    (ht : 0 < t) (hr : 0 ≤ r) (hd : 0 ≤ d) (hdlt : d < 1)
    (hsq : d ^ 2 = 2 * (1 - Real.exp (-(t * r ^ 2)))) :
    r ≤ Real.sqrt (1 / t) := by
  apply Real.le_sqrt_of_sq_le
  have hlt := gaussian_parameter_lt_one_of_displacement ht hr hd hdlt hsq
  apply le_of_lt
  apply (lt_div_iff₀ ht).mpr
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasAffineGaussianRealization
    (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (V : Type u)
    (_ : NormedAddCommGroup V)
    (_ : InnerProductSpace ℂ V)
    (_ : CompleteSpace V)
    (α : AffineHilbertAction G V) (x : V)
    (t : ℝ), 0 < t →
    ∃ (W : Type u)
      (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℂ W)
      (_ : CompleteSpace W)
      (π : UnitaryRepresentation G W)
      (ξ : W),
      ‖ξ‖ = 1 ∧
        ∀ g : G,
          ‖(π g : W →L[ℂ] W) ξ - ξ‖ ^ 2 =
            2 * (1 - Real.exp (-(t * ‖α g x - x‖ ^ 2)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussian_relativeAffineFixedPoint_of_uniform
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G)
    (hgaussian : HasAffineGaussianRealization G)
    (huniform : HasUniformRelativeKazhdanDisplacement G N) :
    ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
      ∃ y : V, IsAffineFixed α N y := by
  intro V _ _ _ α
  let x : V := 0
  obtain ⟨F, δ, hδ, hF⟩ := huniform 1 (by norm_num)
  let B : ℝ := (∑ g ∈ F, ‖α g x - x‖ ^ 2) + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let t : ℝ := δ ^ 2 / (4 * B)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  obtain ⟨W, hW, hinner, hcomplete, π, ξ, hξ, hformula⟩ :=
    hgaussian V inferInstance inferInstance inferInstance α x t ht
  let : NormedAddCommGroup W := hW
  let : InnerProductSpace ℂ W := hinner
  let : CompleteSpace W := hcomplete
  have hfinite :
      ∀ g ∈ F, ‖(π g : W →L[ℂ] W) ξ - ξ‖ < δ := by
    intro g hg
    have hentry : ‖α g x - x‖ ^ 2 ≤ B := by
      calc
        ‖α g x - x‖ ^ 2 ≤
            ∑ h ∈ F, ‖α h x - x‖ ^ 2 :=
          Finset.single_le_sum
            (fun h _ => sq_nonneg ‖α h x - x‖) hg
        _ ≤ B := by
          dsimp [B]
          linarith
    have hsquare :
        ‖(π g : W →L[ℂ] W) ξ - ξ‖ ^ 2 < δ ^ 2 := by
      calc
        ‖(π g : W →L[ℂ] W) ξ - ξ‖ ^ 2 =
            2 * (1 - Real.exp (-(t * ‖α g x - x‖ ^ 2))) :=
          hformula g
        _ ≤ 2 * (t * ‖α g x - x‖ ^ 2) := by
          have h := gaussian_defect_le_parameter
            (t * ‖α g x - x‖ ^ 2)
          linarith
        _ ≤ 2 * t * B := by
          nlinarith
        _ = δ ^ 2 / 2 := by
          dsimp [t]
          field_simp
          ring
        _ < δ ^ 2 := by linarith [sq_pos_of_pos hδ]
    exact (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hδ)).mp hsquare
  have hN := hF W inferInstance inferInstance inferInstance π ξ hξ hfinite
  apply affine_subgroup_fixedPoint_of_bounded_orbit α N x
  refine ⟨Real.sqrt (1 / t), ?_⟩
  intro n
  exact gaussian_affine_displacement_le ht
    (norm_nonneg (α (n : G) x - x))
    (norm_nonneg ((π (n : G) : W →L[ℂ] W) ξ - ξ))
    (hN n) (hformula (n : G))

end

section

namespace CornulierUltralimit

open Filter
open scoped BigOperators ComplexOrder Matrix Topology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem constantOneKernel_posSemidef {I : Type*} :
    Matrix.PosSemidef (fun (_ _ : I) => (1 : ℂ)) := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_one]
  · intro c
    convert (star_mul_self_nonneg
      (∑ i ∈ c.support, c i) :
        (0 : ℂ) ≤ star (∑ i ∈ c.support, c i) *
          (∑ i ∈ c.support, c i)) using 1
    simp only [Finsupp.sum, star_sum, Finset.sum_mul, Finset.mul_sum,
      mul_one]
    rw [Finset.sum_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem schurProduct_posSemidef
    {I : Type*} {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef :=
  hA.hadamard hB

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def entrywisePow {I : Type*} (A : Matrix I I ℂ) (n : ℕ) :
    Matrix I I ℂ := fun i j => A i j ^ n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem entrywisePow_apply
    {I : Type*} (A : Matrix I I ℂ) (n : ℕ) (i j : I) :
    entrywisePow A n i j = A i j ^ n := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem entrywisePow_posSemidef
    {I : Type*} {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (n : ℕ) :
    (entrywisePow A n).PosSemidef := by
  induction n with
  | zero =>
      exact constantOneKernel_posSemidef
  | succ n ih =>
      have hproduct := schurProduct_posSemidef ih hA
      convert hproduct using 1
      ext i j
      simp only [entrywisePow, pow_succ, Matrix.hadamard_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem nonnegReal_smul_posSemidef
    {I : Type*} {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (r : ℝ) (hr : 0 ≤ r) :
    (r • A).PosSemidef :=
  hA.smul hr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem weightedSum_posSemidef
    {I J : Type*} (s : Finset J)
    (A : J → Matrix I I ℂ) (a : J → ℝ)
    (hA : ∀ j ∈ s, (A j).PosSemidef)
    (ha : ∀ j ∈ s, 0 ≤ a j) :
    (∑ j ∈ s, a j • A j).PosSemidef := by
  apply Matrix.posSemidef_sum s
  intro j hj
  exact nonnegReal_smul_posSemidef (hA j hj) (a j) (ha j hj)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem posSemidef_of_tendsto_entries
    {I N : Type*} (l : Filter N) [NeBot l]
    (A : N → Matrix I I ℂ) (B : Matrix I I ℂ)
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) l (𝓝 (B i j))) :
    B.PosSemidef := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    apply tendsto_nhds_unique (hlim j i).star
    have hfun :
        (fun n => star (A n j i)) =
          (fun n => A n i j) := by
      funext n
      exact (hA n).isHermitian.apply i j
    rw [hfun]
    exact hlim i j
  · intro c
    have hquadratic :
        Tendsto
          (fun n => c.sum fun i z => c.sum fun j w =>
            star z * A n i j * w)
          l
          (𝓝 (c.sum fun i z => c.sum fun j w =>
            star z * B i j * w)) := by
      simpa only [Finsupp.sum] using
        tendsto_finsetSum c.support (fun i _ =>
          tendsto_finsetSum c.support (fun j _ =>
            (tendsto_const_nhds.mul (hlim i j)).mul
              tendsto_const_nhds))
    exact ge_of_tendsto hquadratic
      (Eventually.of_forall fun n => (hA n).2 c)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def entrywiseExpPartial
    {I : Type*} (A : Matrix I I ℂ) (N : ℕ) :
    Matrix I I ℂ :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • entrywisePow A n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem entrywiseExpPartial_posSemidef
    {I : Type*} {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (N : ℕ) :
    (entrywiseExpPartial A N).PosSemidef := by
  apply weightedSum_posSemidef (Finset.range N)
    (fun n => entrywisePow A n) (fun n => (n.factorial : ℝ)⁻¹)
  · intro n hn
    exact entrywisePow_posSemidef hA n
  · intro n hn
    positivity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tendsto_entrywiseExpPartial
    {I : Type*} (A : Matrix I I ℂ) (i j : I) :
    Tendsto (fun N => entrywiseExpPartial A N i j)
      Filter.atTop (𝓝 (Complex.exp (A i j))) := by
  have hsum :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A i j)).tendsto_sum_nat
  simp only [entrywiseExpPartial, Matrix.sum_apply,
    Matrix.smul_apply, entrywisePow_apply]
  rw [Complex.exp_eq_exp_ℂ]
  exact hsum

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem entrywiseExp_posSemidef
    {I : Type*} {A : Matrix I I ℂ}
    (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => Complex.exp (A i j)) := by
  apply posSemidef_of_tendsto_entries Filter.atTop
    (entrywiseExpPartial A)
    (fun i j => Complex.exp (A i j))
  · intro N
    exact entrywiseExpPartial_posSemidef hA N
  · intro i j
    exact tendsto_entrywiseExpPartial A i j

end CornulierUltralimit

end

section

open ConnesRigidity
open scoped BigOperators ComplexOrder Matrix InnerProductSpace

universe u

variable {I V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gaussianKernel (v : I → V) (t : ℝ) : Matrix I I ℂ :=
  fun i j => (Real.exp (-t * ‖v i - v j‖ ^ 2) : ℂ)



omit [InnerProductSpace ℂ V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem gaussianKernel_diag
    (v : I → V) (t : ℝ) (i : I) :
    gaussianKernel v t i i = 1 := by
  simp only [gaussianKernel, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Real.exp_zero, Complex.ofReal_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gaussianSymmetricGram (v : I → V) (t : ℝ) : Matrix I I ℂ :=
  t • (Matrix.gram ℂ v + (Matrix.gram ℂ v)ᵀ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussianSymmetricGram_posSemidef
    (v : I → V) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianSymmetricGram v t).PosSemidef := by
  have hgram := CornulierUltralimit.gram_posSemidef_infinite v
  exact (hgram.add hgram.transpose).smul ht

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gaussianWeight (v : I → V) (t : ℝ) (i : I) : ℂ :=
  (Real.exp (-t * ‖v i‖ ^ 2) : ℂ)

omit [InnerProductSpace ℂ V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussianWeightGram_posSemidef
    (v : I → V) (t : ℝ) :
    (Matrix.gram ℂ (gaussianWeight v t)).PosSemidef :=
  CornulierUltralimit.gram_posSemidef_infinite (gaussianWeight v t)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussianSymmetricGram_apply
    (v : I → V) (t : ℝ) (i j : I) :
    gaussianSymmetricGram v t i j =
      (2 * t * (inner ℂ (v i) (v j)).re : ℝ) := by
  change (t : ℂ) *
    (inner ℂ (v i) (v j) + inner ℂ (v j) (v i)) =
      (2 * t * (inner ℂ (v i) (v j)).re : ℝ)
  rw [← inner_conj_symm (v j) (v i), Complex.add_conj]
  push_cast
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussianKernel_factor
    (v : I → V) (t : ℝ) (i j : I) :
    gaussianKernel v t i j =
      Complex.exp (gaussianSymmetricGram v t i j) *
        (Matrix.gram ℂ (gaussianWeight v t)) i j := by
  have hnorm := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
  change ‖v i - v j‖ ^ 2 =
    ‖v i‖ ^ 2 - 2 * (inner ℂ (v i) (v j)).re + ‖v j‖ ^ 2 at hnorm
  have hreal :
      -t * ‖v i - v j‖ ^ 2 =
        2 * t * (inner ℂ (v i) (v j)).re +
          (-t * ‖v i‖ ^ 2) + (-t * ‖v j‖ ^ 2) := by
    rw [hnorm]
    ring
  have hcomplex := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hcomplex
  change (Real.exp (-t * ‖v i - v j‖ ^ 2) : ℂ) =
    Complex.exp (gaussianSymmetricGram v t i j) *
      inner ℂ (gaussianWeight v t i) (gaussianWeight v t j)
  rw [Complex.ofReal_exp, gaussianSymmetricGram_apply]
  rw [RCLike.inner_apply']
  change Complex.exp (↑(-t * ‖v i - v j‖ ^ 2)) =
    Complex.exp (↑(2 * t * (inner ℂ (v i) (v j)).re)) *
      (star (gaussianWeight v t i) * gaussianWeight v t j)
  simp only [gaussianWeight, RCLike.star_def, Complex.conj_ofReal]
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  simpa only [neg_mul, add_assoc] using hcomplex

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gaussianKernel_posSemidef
    (v : I → V) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianKernel v t).PosSemidef := by
  have hexp : Matrix.PosSemidef
      ((fun i j => Complex.exp (gaussianSymmetricGram v t i j)) :
        Matrix I I ℂ) :=
    CornulierUltralimit.entrywiseExp_posSemidef
      (gaussianSymmetricGram_posSemidef v ht)
  have hweight := gaussianWeightGram_posSemidef v t
  have hfactor : gaussianKernel v t =
      ((fun i j => Complex.exp (gaussianSymmetricGram v t i j)) :
        Matrix I I ℂ) ⊙ Matrix.gram ℂ (gaussianWeight v t) := by
    ext i j
    exact gaussianKernel_factor v t i j
  rw [hfactor]
  exact hexp.hadamard hweight

section AffineActions

variable {G : Type u} [Group G] [CompleteSpace V]





end AffineActions

end

section

open ConnesRigidity
open scoped ComplexOrder InnerProductSpace

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasAffineGaussianRealization
    (G : CountableDiscreteGroup.{u}) : HasAffineGaussianRealization G := by
  intro V _ _ _ α x t ht
  let v : G → V := fun g ↦ α g x
  let K : Matrix G G ℂ := gaussianKernel v t
  have hK : K.PosSemidef := gaussianKernel_posSemidef v ht.le
  let : Fact (CornulierUltralimit.scalarOperatorKernel K).PosSemidef :=
    ⟨CornulierUltralimit.scalarOperatorKernel_posSemidef K hK⟩
  let ρ : G →* Equiv.Perm G :=
    { toFun := fun g ↦ Equiv.mulLeft g
      map_one' := by
        apply Equiv.ext
        intro h
        exact one_mul h
      map_mul' := by
        intro a b
        apply Equiv.ext
        intro h
        exact mul_assoc a b h }
  have hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j := by
    intro a i j
    change (Real.exp (-t * ‖α (a * i) x - α (a * j) x‖ ^ 2) : ℂ) =
      (Real.exp (-t * ‖α i x - α j x‖ ^ 2) : ℂ)
    have hd : ‖α (a * i) x - α (a * j) x‖ =
        ‖α i x - α j x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, map_mul, map_mul]
      exact (α a).isometry.dist_eq (α i x) (α j x)
    rw [hd]
  let W := RKHS.OfKernel (CornulierUltralimit.scalarOperatorKernel K)
  let representation :=
    CornulierUltralimit.actionKernelUnitaryRepresentation K ρ hinv
  let π : UnitaryRepresentation G W :=
    Unitary.linearIsometryEquiv.symm.toMonoidHom.comp representation
  let ξ : W := CornulierUltralimit.canonicalKernelVector K (1 : G)
  have hinner (g h : G) :
      ⟪CornulierUltralimit.canonicalKernelVector K g,
        CornulierUltralimit.canonicalKernelVector K h⟫_ℂ = K g h :=
    CornulierUltralimit.canonicalKernelVector_inner K hK g h
  have hnorm (g : G) :
      ‖CornulierUltralimit.canonicalKernelVector K g‖ = 1 := by
    have hsq : ‖CornulierUltralimit.canonicalKernelVector K g‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
      change (gaussianKernel v t g g).re = 1
      rw [gaussianKernel_diag]
      norm_num
    nlinarith [norm_nonneg
      (CornulierUltralimit.canonicalKernelVector K g)]
  refine ⟨W, inferInstance, inferInstance, inferInstance, π, ξ,
    hnorm 1, ?_⟩
  intro g
  have haction :
      (π g : W →L[ℂ] W) ξ =
        CornulierUltralimit.canonicalKernelVector K g := by
    change representation g
      (CornulierUltralimit.canonicalKernelVector K (1 : G)) =
        CornulierUltralimit.canonicalKernelVector K g
    simpa [ρ] using
      CornulierUltralimit.actionKernelUnitaryRepresentation_canonicalKernelVector
        K ρ hinv g (1 : G)
  rw [haction]
  change ‖CornulierUltralimit.canonicalKernelVector K g -
      CornulierUltralimit.canonicalKernelVector K (1 : G)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ), hinner]
  rw [hnorm, hnorm]
  change 1 ^ 2 - 2 *
      (Real.exp (-t * ‖α g x - α (1 : G) x‖ ^ 2) : ℂ).re +
      1 ^ 2 = 2 * (1 - Real.exp (-(t * ‖α g x - x‖ ^ 2)))
  have hxone : α (1 : G) x = x := by simp
  rw [hxone]
  simp only [Complex.ofReal_re, one_pow]
  rw [neg_mul]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierRelativeAffineFixed_of_uniform
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G)
    (huniform : HasUniformRelativeKazhdanDisplacement G N) :
    ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
      ∃ y : V, IsAffineFixed α N y :=
  gaussian_relativeAffineFixedPoint_of_uniform G N
    (hasAffineGaussianRealization G) huniform

end

section

open ConnesRigidity

universe u

variable {G : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_sup_of_elementwise_commute
    (N₁ N₂ : Subgroup G)
    (hcomm : ∀ g ∈ N₁, ∀ h ∈ N₂, Commute g h)
    (x : G) :
    x ∈ N₁ ⊔ N₂ ↔
      ∃ g ∈ N₁, ∃ h ∈ N₂, g * h = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact ⟨y, hy, 1, N₂.one_mem, by simp only [mul_one]⟩
        · exact ⟨1, N₁.one_mem, y, hy, by simp only [one_mul]⟩
    | one =>
        exact ⟨1, N₁.one_mem, 1, N₂.one_mem, by simp only [mul_one]⟩
    | mul y z hy hz ihy ihz =>
        obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := ihy
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := ihz
        refine ⟨y₁ * z₁, N₁.mul_mem hy₁ hz₁,
          y₂ * z₂, N₂.mul_mem hy₂ hz₂, ?_⟩
        have hswap : y₂ * z₁ = z₁ * y₂ :=
          (hcomm z₁ hz₁ y₂ hy₂).symm.eq
        calc
          (y₁ * z₁) * (y₂ * z₂) = y₁ * (z₁ * y₂) * z₂ := by group
          _ = y₁ * (y₂ * z₁) * z₂ := by rw [hswap]
          _ = (y₁ * y₂) * (z₁ * z₂) := by group
    | inv y hy ih =>
        obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := ih
        refine ⟨y₁⁻¹, N₁.inv_mem hy₁,
          y₂⁻¹, N₂.inv_mem hy₂, ?_⟩
        have hswap : y₁⁻¹ * y₂⁻¹ = y₂⁻¹ * y₁⁻¹ :=
          (hcomm y₁⁻¹ (N₁.inv_mem hy₁)
            y₂⁻¹ (N₂.inv_mem hy₂)).eq
        rw [mul_inv_rev]
        exact hswap
  · rintro ⟨g, hg, h, hh, rfl⟩
    exact Subgroup.mul_mem_sup hg hh

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitary_displacement_mul_le
    (π : UnitaryRepresentation G V)
    (g h : G) (ξ : V) :
    ‖(π (g * h) : V →L[ℂ] V) ξ - ξ‖ ≤
      ‖(π g : V →L[ℂ] V) ξ - ξ‖ +
        ‖(π h : V →L[ℂ] V) ξ - ξ‖ := by
  rw [map_mul]
  change
    ‖(π g : V →L[ℂ] V) ((π h : V →L[ℂ] V) ξ) - ξ‖ ≤ _
  calc
    ‖(π g : V →L[ℂ] V) ((π h : V →L[ℂ] V) ξ) - ξ‖ =
        ‖(π g : V →L[ℂ] V)
            ((π h : V →L[ℂ] V) ξ - ξ) +
          ((π g : V →L[ℂ] V) ξ - ξ)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖(π g : V →L[ℂ] V)
            ((π h : V →L[ℂ] V) ξ - ξ)‖ +
          ‖(π g : V →L[ℂ] V) ξ - ξ‖ := norm_add_le _ _
    _ = ‖(π g : V →L[ℂ] V) ξ - ξ‖ +
          ‖(π h : V →L[ℂ] V) ξ - ξ‖ := by
      rw [Unitary.norm_map]
      ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitary_displacement_sup_lt_of_elementwise_commute
    (π : UnitaryRepresentation G V)
    (N₁ N₂ : Subgroup G)
    (hcomm : ∀ g ∈ N₁, ∀ h ∈ N₂, Commute g h)
    (ξ : V) (ε₁ ε₂ : ℝ)
    (h₁ : ∀ g : N₁,
      ‖(π (g : G) : V →L[ℂ] V) ξ - ξ‖ < ε₁)
    (h₂ : ∀ h : N₂,
      ‖(π (h : G) : V →L[ℂ] V) ξ - ξ‖ < ε₂) :
    ∀ k : (N₁ ⊔ N₂ : Subgroup G),
      ‖(π (k : G) : V →L[ℂ] V) ξ - ξ‖ < ε₁ + ε₂ := by
  rintro ⟨k, hk⟩
  obtain ⟨g, hg, h, hh, hgh⟩ :=
    (mem_sup_of_elementwise_commute N₁ N₂ hcomm k).mp hk
  change ‖(π k : V →L[ℂ] V) ξ - ξ‖ < ε₁ + ε₂
  rw [← hgh]
  exact lt_of_le_of_lt (unitary_displacement_mul_le π g h ξ)
    (add_lt_add (h₁ ⟨g, hg⟩) (h₂ ⟨h, hh⟩))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem HasUniformRelativeKazhdanDisplacement.sup_of_elementwise_commute
    {N₁ N₂ : Subgroup G}
    (h₁ : HasUniformRelativeKazhdanDisplacement G N₁)
    (h₂ : HasUniformRelativeKazhdanDisplacement G N₂)
    (hcomm : ∀ g ∈ N₁, ∀ h ∈ N₂, Commute g h) :
    HasUniformRelativeKazhdanDisplacement G (N₁ ⊔ N₂) := by
  classical
  intro ε hε
  obtain ⟨F₁, δ₁, hδ₁, hbound₁⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨F₂, δ₂, hδ₂, hbound₂⟩ := h₂ (ε / 2) (by positivity)
  refine ⟨F₁ ∪ F₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro W _ _ _ π ξ hunit hξ
  have hξ₁ : ∀ g ∈ F₁,
      ‖(π g : W →L[ℂ] W) ξ - ξ‖ < δ₁ := by
    intro g hg
    exact lt_of_lt_of_le
      (hξ g (Finset.mem_union_left F₂ hg)) (min_le_left _ _)
  have hξ₂ : ∀ g ∈ F₂,
      ‖(π g : W →L[ℂ] W) ξ - ξ‖ < δ₂ := by
    intro g hg
    exact lt_of_lt_of_le
      (hξ g (Finset.mem_union_right F₁ hg)) (min_le_right _ _)
  have hone := hbound₁ W inferInstance inferInstance inferInstance π ξ hunit hξ₁
  have htwo := hbound₂ W inferInstance inferInstance inferInstance π ξ hunit hξ₂
  intro k
  have hjoin := unitary_displacement_sup_lt_of_elementwise_commute
    π N₁ N₂ hcomm ξ (ε / 2) (ε / 2) hone htwo k
  linarith

public
theorem HasUniformRelativeKazhdanDisplacement.mono
    {N M : Subgroup G}
    (hN : HasUniformRelativeKazhdanDisplacement G N)
    (hMN : M ≤ N) :
    HasUniformRelativeKazhdanDisplacement G M := by
  intro ε hε
  obtain ⟨F, δ, hδ, hbound⟩ := hN ε hε
  refine ⟨F, δ, hδ, ?_⟩
  intro W _ _ _ π ξ hunit hξ m
  exact hbound W inferInstance inferInstance inferInstance π ξ hunit hξ
    ⟨m, hMN m.property⟩

end

section

open ConnesRigidity

universe u

section ActualParabolicEmbedding

open Matrix

variable {A : Type} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwoPlusTwo_symm_zero :
    (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) =
      Sum.inl (0 : Fin 2) := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwoPlusTwo_symm_one :
    (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) =
      Sum.inl (1 : Fin 2) := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwoPlusTwo_symm_two :
    (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) =
      Sum.inr (0 : Fin 2) := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwoPlusTwo_symm_three :
    (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) =
      Sum.inr (1 : Fin 2) := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def rankTwoColumnBlock (v : Fin 2 → A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => if j = (1 : Fin 2) then v i else 0

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem rankTwoColumnBlock_add (v w : Fin 2 → A) :
    rankTwoColumnBlock (v + w) =
      rankTwoColumnBlock v + rankTwoColumnBlock w := by
  ext i j
  by_cases hj : j = (1 : Fin 2) <;>
    simp [rankTwoColumnBlock, hj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem rankTwoColumnBlock_zero :
    rankTwoColumnBlock (0 : Fin 2 → A) = 0 := by
  ext i j
  simp only [rankTwoColumnBlock, Fin.isValue, Pi.zero_apply, ite_self, Matrix.zero_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem rankTwoColumnBlock_mul
    (g : Matrix.SpecialLinearGroup (Fin 2) A) (v : Fin 2 → A) :
    (g : Matrix (Fin 2) (Fin 2) A) * rankTwoColumnBlock v =
      rankTwoColumnBlock (g • v) := by
  ext i j
  by_cases hj : j = (1 : Fin 2)
  · subst j
    simp only [Fin.isValue, Matrix.mul_apply, rankTwoColumnBlock, ↓reduceIte, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec, mulVec, dotProduct]
  · simp only [Matrix.mul_apply, rankTwoColumnBlock, Fin.isValue, hj, ↓reduceIte, mul_zero,
      Finset.sum_const_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def rankTwoParabolicMatrix (x : ElementaryRankTwoSemidirect A) :
    Matrix (Fin 4) (Fin 4) A :=
  Matrix.reindex (finSumFinEquiv (m := 2) (n := 2))
    (finSumFinEquiv (m := 2) (n := 2))
    (Matrix.fromBlocks
      ((x.right : Matrix.SpecialLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A)
      (rankTwoColumnBlock (Multiplicative.toAdd x.left)) 0 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem rankTwoParabolicMatrix_det (x : ElementaryRankTwoSemidirect A) :
    (rankTwoParabolicMatrix x).det = 1 := by
  unfold rankTwoParabolicMatrix
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]
  exact (x.right : Matrix.SpecialLinearGroup (Fin 2) A).property

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def rankTwoParabolicSpecialLinear :
    ElementaryRankTwoSemidirect A →* Matrix.SpecialLinearGroup (Fin 4) A where
  toFun x := ⟨rankTwoParabolicMatrix x, rankTwoParabolicMatrix_det x⟩
  map_one' := by
    apply Subtype.ext
    change rankTwoParabolicMatrix 1 = 1
    unfold rankTwoParabolicMatrix
    rw [show (1 : ElementaryRankTwoSemidirect A).right = 1 by rfl]
    change Matrix.reindex _ _ (Matrix.fromBlocks 1 _ 0 1) = 1
    rw [show rankTwoColumnBlock
      (Multiplicative.toAdd (1 : ElementaryRankTwoSemidirect A).left) = 0 by
        apply rankTwoColumnBlock_zero]
    rw [Matrix.fromBlocks_one]
    exact map_one (Matrix.reindexAlgEquiv A A
      (finSumFinEquiv (m := 2) (n := 2)))
  map_mul' x y := by
    apply Subtype.ext
    change rankTwoParabolicMatrix (x * y) =
      rankTwoParabolicMatrix x * rankTwoParabolicMatrix y
    unfold rankTwoParabolicMatrix
    change (Matrix.reindexAlgEquiv A A
      (finSumFinEquiv (m := 2) (n := 2)))
      (Matrix.fromBlocks _ _ 0 1) =
      (Matrix.reindexAlgEquiv A A
        (finSumFinEquiv (m := 2) (n := 2)))
        (Matrix.fromBlocks _ _ 0 1) *
      (Matrix.reindexAlgEquiv A A
        (finSumFinEquiv (m := 2) (n := 2)))
        (Matrix.fromBlocks _ _ 0 1)
    rw [← map_mul, Matrix.fromBlocks_multiply]
    apply congrArg (Matrix.reindexAlgEquiv A A
      (finSumFinEquiv (m := 2) (n := 2)))
    congr 1
    · simp only [SemidirectProduct.mul_right, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        mul_zero, add_zero]
    · simp only [Matrix.mul_one, SemidirectProduct.mul_left,
          toAdd_mul, elementaryRankTwoAction_toAdd]
      rw [rankTwoColumnBlock_add, rankTwoColumnBlock_mul]
      exact add_comm _ _
    · simp only [zero_mul, mul_zero, add_zero]
    · simp only [zero_mul, mul_one, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem rankTwoParabolicSpecialLinear_inl
    (v : Fin 2 → A) :
    rankTwoParabolicSpecialLinear
        (SemidirectProduct.inl (Multiplicative.ofAdd v) :
          ElementaryRankTwoSemidirect A) =
      Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 4) ≠ 3 by decide) (v 0) *
      Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 4) ≠ 3 by decide) (v 1) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change rankTwoParabolicMatrix
    (SemidirectProduct.inl (Multiplicative.ofAdd v) :
      ElementaryRankTwoSemidirect A) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoParabolicMatrix,
      rankTwoColumnBlock, Matrix.reindex_apply, Matrix.fromBlocks,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem rankTwoParabolicSpecialLinear_inr_root
    {i j : Fin 2} (hij : i ≠ j) (a : A) :
    rankTwoParabolicSpecialLinear
        (SemidirectProduct.inr (elementaryRankTwoRoot hij a) :
          ElementaryRankTwoSemidirect A) =
      Matrix.SpecialLinearGroup.transvection
        (show Fin.castAdd 2 i ≠ Fin.castAdd 2 j from
          fun h => hij (Fin.castAdd_inj.mp h)) a := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  change rankTwoParabolicMatrix
    (SemidirectProduct.inr (elementaryRankTwoRoot hij a) :
      ElementaryRankTwoSemidirect A) k l = _
  fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
    simp_all [rankTwoParabolicMatrix,
      Matrix.reindex_apply, Matrix.fromBlocks, elementaryRankTwoRoot,
      Matrix.SpecialLinearGroup.transvection_coe]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rankTwoParabolicSpecialLinear_inr_mem_integral
    (g : Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial)
    (hg : g ∈ elementaryRankTwo IntegralPolynomial) :
    rankTwoParabolicSpecialLinear
      (SemidirectProduct.inr
        (⟨g, hg⟩ : elementaryRankTwo IntegralPolynomial) :
          ElementaryRankTwoSemidirect IntegralPolynomial) ∈
      integralElementarySubgroup := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      change rankTwoParabolicSpecialLinear
        (SemidirectProduct.inr (elementaryRankTwoRoot hij a) :
          ElementaryRankTwoSemidirect IntegralPolynomial) ∈
        integralElementarySubgroup
      rw [rankTwoParabolicSpecialLinear_inr_root]
      exact Subgroup.subset_closure
        ⟨Fin.castAdd 2 i, Fin.castAdd 2 j, _, a, rfl⟩
  | one =>
      change rankTwoParabolicSpecialLinear
        (SemidirectProduct.inr
          (1 : elementaryRankTwo IntegralPolynomial) :
          ElementaryRankTwoSemidirect IntegralPolynomial) ∈
        integralElementarySubgroup
      simp only [map_one, one_mem]
  | mul x y hx hy ihx ihy =>
      have hxy :
          (⟨x * y, Subgroup.mul_mem _ hx hy⟩ :
            elementaryRankTwo IntegralPolynomial) =
            (⟨x, hx⟩ : elementaryRankTwo IntegralPolynomial) *
            (⟨y, hy⟩ : elementaryRankTwo IntegralPolynomial) := rfl
      change rankTwoParabolicSpecialLinear
        (SemidirectProduct.inr
          (⟨x * y, Subgroup.mul_mem _ hx hy⟩ :
            elementaryRankTwo IntegralPolynomial) :
          ElementaryRankTwoSemidirect IntegralPolynomial) ∈
        integralElementarySubgroup
      rw [hxy, map_mul, map_mul]
      exact integralElementarySubgroup.mul_mem ihx ihy
  | inv x hx ihx =>
      have hinv :
          (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ :
            elementaryRankTwo IntegralPolynomial) =
            (⟨x, hx⟩ : elementaryRankTwo IntegralPolynomial)⁻¹ := rfl
      change rankTwoParabolicSpecialLinear
        (SemidirectProduct.inr
          (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ :
            elementaryRankTwo IntegralPolynomial) :
          ElementaryRankTwoSemidirect IntegralPolynomial) ∈
        integralElementarySubgroup
      rw [hinv, map_inv, map_inv]
      exact integralElementarySubgroup.inv_mem ihx

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem rankTwoParabolicSpecialLinear_mem_integral
    (x : ElementaryRankTwoSemidirect IntegralPolynomial) :
    rankTwoParabolicSpecialLinear x ∈ integralElementarySubgroup := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul]
  apply integralElementarySubgroup.mul_mem
  · have hleft := rankTwoParabolicSpecialLinear_inl
      (Multiplicative.toAdd x.left)
    have hx : Multiplicative.ofAdd (Multiplicative.toAdd x.left) = x.left := rfl
    rw [hx] at hleft
    rw [hleft]
    apply integralElementarySubgroup.mul_mem <;>
      apply Subgroup.subset_closure
    · exact ⟨0, 3, by decide, _, rfl⟩
    · exact ⟨1, 3, by decide, _, rfl⟩
  · exact rankTwoParabolicSpecialLinear_inr_mem_integral
      (x.right : Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial)
      x.right.property

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralRankTwoColumnEmbedding :
    integralElementaryRankTwoGroup →* integralElementaryGroup where
  toFun x := ⟨rankTwoParabolicSpecialLinear x,
    rankTwoParabolicSpecialLinear_mem_integral x⟩
  map_one' := Subtype.ext (map_one rankTwoParabolicSpecialLinear)
  map_mul' x y := Subtype.ext (map_mul rankTwoParabolicSpecialLinear x y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralRankTwoColumnEmbedding_inl
    (v : Fin 2 → IntegralPolynomial) :
    integralRankTwoColumnEmbedding
      (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      cornulierRoot 0 3 (by decide) (v 0) *
      cornulierRoot 1 3 (by decide) (v 1) := by
  apply Subtype.ext
  exact rankTwoParabolicSpecialLinear_inl v

end ActualParabolicEmbedding

end

section

open Matrix

variable {A : Type} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def specialLinearReindexHom (e : Equiv.Perm (Fin 4)) :
    Matrix.SpecialLinearGroup (Fin 4) A →*
      Matrix.SpecialLinearGroup (Fin 4) A where
  toFun g := ⟨Matrix.reindex e e (g : Matrix (Fin 4) (Fin 4) A), by
    rw [Matrix.det_reindex_self]
    exact g.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.reindexAlgEquiv A A e)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (Matrix.reindexAlgEquiv A A e)
      (g : Matrix (Fin 4) (Fin 4) A) (h : Matrix (Fin 4) (Fin 4) A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem specialLinearReindexHom_transvection
    (e : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) (a : A) :
    specialLinearReindexHom e
      (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) a := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  change Matrix.reindex e e
    ((Matrix.SpecialLinearGroup.transvection hij a :
      Matrix.SpecialLinearGroup (Fin 4) A) : Matrix (Fin 4) (Fin 4) A) k l = _
  simp only [reindex_apply,
    SpecialLinearGroup.transvection_coe, submatrix_apply, Matrix.add_apply, Matrix.one_apply,
    Equiv.eq_symm_apply, Equiv.apply_symm_apply, single_apply, eq_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem specialLinearReindexHom_mem_integral
    (e : Equiv.Perm Index) :
    integralElementarySubgroup.map (specialLinearReindexHom e) ≤
      integralElementarySubgroup := by
  change (Subgroup.closure _).map _ ≤ _
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
  rw [specialLinearReindexHom_transvection]
  exact Subgroup.subset_closure ⟨e i, e j, _, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryReindexHom (e : Equiv.Perm Index) :
    integralElementaryGroup →* integralElementaryGroup where
  toFun g := ⟨specialLinearReindexHom e (g.val : IntegralSpecialLinearGroup),
    specialLinearReindexHom_mem_integral e
      ⟨(g.val : IntegralSpecialLinearGroup), g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (specialLinearReindexHom e))
  map_mul' g h := Subtype.ext
    (map_mul (specialLinearReindexHom e)
      (g.val : IntegralSpecialLinearGroup) (h.val : IntegralSpecialLinearGroup))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralElementaryReindexHom_root
    (e : Equiv.Perm Index) (i j : Index) (hij : i ≠ j)
    (a : IntegralPolynomial) :
    integralElementaryReindexHom e (cornulierRoot i j hij a) =
      cornulierRoot (e i) (e j) (e.injective.ne hij) a := by
  apply Subtype.ext
  exact specialLinearReindexHom_transvection e hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def specialLinearTransposeInverseHom :
    Matrix.SpecialLinearGroup (Fin 4) A →*
      Matrix.SpecialLinearGroup (Fin 4) A where
  toFun g := Matrix.SpecialLinearGroup.transpose g⁻¹
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [SpecialLinearGroup.transpose, inv_one, Matrix.SpecialLinearGroup.coe_one,
      transpose_one, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    change (((g * h)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) A) :
      Matrix (Fin 4) (Fin 4) A).transpose =
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) A) :
        Matrix (Fin 4) (Fin 4) A).transpose) *
      (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 4) A) :
        Matrix (Fin 4) (Fin 4) A).transpose)
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 4) A) :
        Matrix (Fin 4) (Fin 4) A)
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) A) :
        Matrix (Fin 4) (Fin 4) A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem specialLinearTransposeInverseHom_transvection
    {i j : Fin 4} (hij : i ≠ j) (a : A) :
    specialLinearTransposeInverseHom
      (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij.symm (-a) := by
  change Matrix.SpecialLinearGroup.transpose
    (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ = _
  rw [Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1 + Matrix.single i j (-a)).transpose =
    1 + Matrix.single j i (-a)
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem specialLinearTransposeInverseHom_mem_integral :
    integralElementarySubgroup.map
      (specialLinearTransposeInverseHom (A := IntegralPolynomial)) ≤
        integralElementarySubgroup := by
  change (Subgroup.closure _).map _ ≤ _
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
  rw [specialLinearTransposeInverseHom_transvection]
  exact Subgroup.subset_closure ⟨j, i, hij.symm, -a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryTransposeInverseHom :
    integralElementaryGroup →* integralElementaryGroup where
  toFun g := ⟨specialLinearTransposeInverseHom
    (g.val : IntegralSpecialLinearGroup),
    specialLinearTransposeInverseHom_mem_integral
      ⟨(g.val : IntegralSpecialLinearGroup), g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one specialLinearTransposeInverseHom)
  map_mul' g h := Subtype.ext
    (map_mul specialLinearTransposeInverseHom
      (g.val : IntegralSpecialLinearGroup) (h.val : IntegralSpecialLinearGroup))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralElementaryTransposeInverseHom_root
    (i j : Index) (hij : i ≠ j)
    (a : IntegralPolynomial) :
    integralElementaryTransposeInverseHom (cornulierRoot i j hij a) =
      cornulierRoot j i hij.symm (-a) := by
  apply Subtype.ext
  exact specialLinearTransposeInverseHom_transvection hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralRankTwoColumnEmbedding12 :
    integralElementaryRankTwoGroup →* integralElementaryGroup :=
  (integralElementaryReindexHom
    (Equiv.swap (0 : Index) 2)).comp integralRankTwoColumnEmbedding

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralRankTwoRowEmbedding01 :
    integralElementaryRankTwoGroup →* integralElementaryGroup :=
  integralElementaryTransposeInverseHom.comp integralRankTwoColumnEmbedding

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralRankTwoRowEmbedding12 :
    integralElementaryRankTwoGroup →* integralElementaryGroup :=
  integralElementaryTransposeInverseHom.comp integralRankTwoColumnEmbedding12

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralRankTwoColumnEmbedding12_inl
    (v : Fin 2 → IntegralPolynomial) :
    integralRankTwoColumnEmbedding12
      (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      cornulierRoot 2 3 (by decide) (v 0) *
      cornulierRoot 1 3 (by decide) (v 1) := by
  change integralElementaryReindexHom (Equiv.swap (0 : Index) 2)
      (integralRankTwoColumnEmbedding
        (SemidirectProduct.inl (Multiplicative.ofAdd v))) = _
  rw [integralRankTwoColumnEmbedding_inl, map_mul,
    integralElementaryReindexHom_root,
    integralElementaryReindexHom_root]
  have hzero : (Equiv.swap (0 : Index) 2) 0 = 2 := by decide
  have hfirst : (Equiv.swap (0 : Index) 2) 1 = 1 := by decide
  have hlast : (Equiv.swap (0 : Index) 2) 3 = 3 := by decide
  simp only [hzero, hfirst, hlast]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralRankTwoRowEmbedding01_inl
    (v : Fin 2 → IntegralPolynomial) :
    integralRankTwoRowEmbedding01
      (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      cornulierRoot 3 0 (by decide) (-(v 0)) *
      cornulierRoot 3 1 (by decide) (-(v 1)) := by
  change integralElementaryTransposeInverseHom
      (integralRankTwoColumnEmbedding
        (SemidirectProduct.inl (Multiplicative.ofAdd v))) = _
  rw [integralRankTwoColumnEmbedding_inl, map_mul,
    integralElementaryTransposeInverseHom_root,
    integralElementaryTransposeInverseHom_root]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integralRankTwoRowEmbedding12_inl
    (v : Fin 2 → IntegralPolynomial) :
    integralRankTwoRowEmbedding12
      (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      cornulierRoot 3 2 (by decide) (-(v 0)) *
      cornulierRoot 3 1 (by decide) (-(v 1)) := by
  change integralElementaryTransposeInverseHom
      (integralRankTwoColumnEmbedding12
        (SemidirectProduct.inl (Multiplicative.ofAdd v))) = _
  rw [integralRankTwoColumnEmbedding12_inl, map_mul,
    integralElementaryTransposeInverseHom_root,
    integralElementaryTransposeInverseHom_root]

end

section

open Matrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnRoot_commute
    (i j : Index) (hi : i ≠ cornulierLast)
    (hj : j ≠ cornulierLast) (a b : IntegralPolynomial) :
    Commute (cornulierRoot i cornulierLast hi a)
      (cornulierRoot j cornulierLast hj b) := by
  apply Subtype.ext
  change
    Matrix.SpecialLinearGroup.transvection hi a *
        Matrix.SpecialLinearGroup.transvection hj b =
      Matrix.SpecialLinearGroup.transvection hj b *
        Matrix.SpecialLinearGroup.transvection hi a
  apply Matrix.SpecialLinearGroup.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, add_comm,
    Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hj.symm, one_mul,
    add_zero, mul_one, Matrix.add_apply, add_left_comm,
    Matrix.single_mul_single_of_ne _ _ _ _ hi.symm, implies_true]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowRoot_commute
    (i j : Index) (hi : cornulierLast ≠ i)
    (hj : cornulierLast ≠ j) (a b : IntegralPolynomial) :
    Commute (cornulierRoot cornulierLast i hi a)
      (cornulierRoot cornulierLast j hj b) := by
  apply Subtype.ext
  change
    Matrix.SpecialLinearGroup.transvection hi a *
        Matrix.SpecialLinearGroup.transvection hj b =
      Matrix.SpecialLinearGroup.transvection hj b *
        Matrix.SpecialLinearGroup.transvection hi a
  apply Matrix.SpecialLinearGroup.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, add_comm,
    Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hi.symm, one_mul,
    add_zero, mul_one, Matrix.add_apply, add_left_comm,
    Matrix.single_mul_single_of_ne _ _ _ _ hj.symm, implies_true]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierK₁_isMulCommutative : IsMulCommutative cornulierK₁ := by
  unfold cornulierK₁
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨i, hi, a, rfl⟩ _ ⟨j, hj, b, rfl⟩
  exact (cornulierColumnRoot_commute i j hi hj a b).eq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierK₂_isMulCommutative : IsMulCommutative cornulierK₂ := by
  unfold cornulierK₂
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨i, hi, a, rfl⟩ _ ⟨j, hj, b, rfl⟩
  exact (cornulierRowRoot_commute i j hi hj a b).eq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierColumnPlane01 : Subgroup integralElementaryGroup :=
  integralElementaryRankTwoTranslationSubgroup.map
    integralRankTwoColumnEmbedding

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnPlane01_le_K₁ :
    cornulierColumnPlane01 ≤ cornulierK₁ := by
  rintro _ ⟨g, ⟨v, hv⟩, rfl⟩
  subst g
  let w := Multiplicative.toAdd v
  have hw : v = Multiplicative.ofAdd w := rfl
  rw [hw, integralRankTwoColumnEmbedding_inl]
  exact cornulierK₁.mul_mem
    (cornulierRoot_mem_K₁ 0 (by decide) (w 0))
    (cornulierRoot_mem_K₁ 1 (by decide) (w 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem cornulierRoot_zero
    (i j : Index) (hij : i ≠ j) :
    cornulierRoot i j hij 0 = 1 := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.transvection hij
    (0 : IntegralPolynomial) =
      (1 : Matrix.SpecialLinearGroup Index IntegralPolynomial)
  exact Matrix.SpecialLinearGroup.transvection_coeff_zero hij

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnPlane01_root_zero (a : IntegralPolynomial) :
    cornulierRoot 0 3 (by decide) a ∈ cornulierColumnPlane01 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 0 a
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoColumnEmbedding_inl]
  simp only [Fin.isValue, Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, cornulierRoot_zero, mul_one, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnPlane01_root_one (a : IntegralPolynomial) :
    cornulierRoot 1 3 (by decide) a ∈ cornulierColumnPlane01 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 1 a
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoColumnEmbedding_inl]
  simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
    cornulierRoot_zero, Pi.single_eq_same, one_mul, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierColumnPlane12 : Subgroup integralElementaryGroup :=
  integralElementaryRankTwoTranslationSubgroup.map
    integralRankTwoColumnEmbedding12

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnPlane12_le_K₁ :
    cornulierColumnPlane12 ≤ cornulierK₁ := by
  rintro _ ⟨g, ⟨v, hv⟩, rfl⟩
  subst g
  let w := Multiplicative.toAdd v
  have hw : v = Multiplicative.ofAdd w := rfl
  rw [hw, integralRankTwoColumnEmbedding12_inl]
  exact cornulierK₁.mul_mem
    (cornulierRoot_mem_K₁ 2 (by decide) (w 0))
    (cornulierRoot_mem_K₁ 1 (by decide) (w 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnPlane12_root_two (a : IntegralPolynomial) :
    cornulierRoot 2 3 (by decide) a ∈ cornulierColumnPlane12 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 0 a
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoColumnEmbedding12_inl]
  simp only [Fin.isValue, Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, cornulierRoot_zero, mul_one, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierRowPlane01 : Subgroup integralElementaryGroup :=
  integralElementaryRankTwoTranslationSubgroup.map
    integralRankTwoRowEmbedding01

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowPlane01_le_K₂ :
    cornulierRowPlane01 ≤ cornulierK₂ := by
  rintro _ ⟨g, ⟨v, hv⟩, rfl⟩
  subst g
  let w := Multiplicative.toAdd v
  have hw : v = Multiplicative.ofAdd w := rfl
  rw [hw, integralRankTwoRowEmbedding01_inl]
  exact cornulierK₂.mul_mem
    (cornulierRoot_mem_K₂ 0 (by decide) (-(w 0)))
    (cornulierRoot_mem_K₂ 1 (by decide) (-(w 1)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowPlane01_root_zero (a : IntegralPolynomial) :
    cornulierRoot 3 0 (by decide) a ∈ cornulierRowPlane01 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 0 (-a)
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoRowEmbedding01_inl]
  simp only [Fin.isValue, Pi.single_eq_same, neg_neg, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, neg_zero, cornulierRoot_zero, mul_one, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowPlane01_root_one (a : IntegralPolynomial) :
    cornulierRoot 3 1 (by decide) a ∈ cornulierRowPlane01 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 1 (-a)
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoRowEmbedding01_inl]
  simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, neg_zero,
    cornulierRoot_zero, Pi.single_eq_same, neg_neg, one_mul, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierRowPlane12 : Subgroup integralElementaryGroup :=
  integralElementaryRankTwoTranslationSubgroup.map
    integralRankTwoRowEmbedding12

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowPlane12_le_K₂ :
    cornulierRowPlane12 ≤ cornulierK₂ := by
  rintro _ ⟨g, ⟨v, hv⟩, rfl⟩
  subst g
  let w := Multiplicative.toAdd v
  have hw : v = Multiplicative.ofAdd w := rfl
  rw [hw, integralRankTwoRowEmbedding12_inl]
  exact cornulierK₂.mul_mem
    (cornulierRoot_mem_K₂ 2 (by decide) (-(w 0)))
    (cornulierRoot_mem_K₂ 1 (by decide) (-(w 1)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowPlane12_root_two (a : IntegralPolynomial) :
    cornulierRoot 3 2 (by decide) a ∈ cornulierRowPlane12 := by
  let v : Fin 2 → IntegralPolynomial := Pi.single 0 (-a)
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd v),
    ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
  rw [integralRankTwoRowEmbedding12_inl]
  simp only [Fin.isValue, Pi.single_eq_same, neg_neg, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, neg_zero, cornulierRoot_zero, mul_one, v]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierColumnPlanes_sup_eq_K₁ :
    cornulierColumnPlane01 ⊔ cornulierColumnPlane12 = cornulierK₁ := by
  apply le_antisymm
    (sup_le cornulierColumnPlane01_le_K₁ cornulierColumnPlane12_le_K₁)
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, a, rfl⟩
  fin_cases i
  · exact Subgroup.mem_sup_left (cornulierColumnPlane01_root_zero a)
  · exact Subgroup.mem_sup_left (cornulierColumnPlane01_root_one a)
  · exact Subgroup.mem_sup_right (cornulierColumnPlane12_root_two a)
  · exact (hi rfl).elim

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierRowPlanes_sup_eq_K₂ :
    cornulierRowPlane01 ⊔ cornulierRowPlane12 = cornulierK₂ := by
  apply le_antisymm
    (sup_le cornulierRowPlane01_le_K₂ cornulierRowPlane12_le_K₂)
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, a, rfl⟩
  fin_cases j
  · exact Subgroup.mem_sup_left (cornulierRowPlane01_root_zero a)
  · exact Subgroup.mem_sup_left (cornulierRowPlane01_root_one a)
  · exact Subgroup.mem_sup_right (cornulierRowPlane12_root_two a)
  · exact (hj rfl).elim

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierColumnPlanes_commute
    (g : integralElementaryGroup) (hg : g ∈ cornulierColumnPlane01)
    (h : integralElementaryGroup) (hh : h ∈ cornulierColumnPlane12) :
    Commute g h := by
  let : IsMulCommutative cornulierK₁ :=
    cornulierK₁_isMulCommutative
  exact setLike_mul_comm (cornulierColumnPlane01_le_K₁ hg)
    (cornulierColumnPlane12_le_K₁ hh)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierRowPlanes_commute
    (g : integralElementaryGroup) (hg : g ∈ cornulierRowPlane01)
    (h : integralElementaryGroup) (hh : h ∈ cornulierRowPlane12) :
    Commute g h := by
  let : IsMulCommutative cornulierK₂ :=
    cornulierK₂_isMulCommutative
  exact setLike_mul_comm (cornulierRowPlane01_le_K₂ hg)
    (cornulierRowPlane12_le_K₂ hh)

end

end ConnesRigidity

end
