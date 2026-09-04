/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.NonSoficGroup.Spectral
import all LeanPool.NonSoficGroup.Spectral
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Geometry.Group.Growth.LinearLowerBound
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

/-!
# Compression arguments for the non-sofic group construction

This file assembles the rooted finite-model and component-compression
arguments used by the final contradiction.
-/

noncomputable section

namespace SoficGroups

open MatchedComponentCompletion

namespace KunRootedWordPower

section

open Filter Topology
open KunRootedIndicatorCrossing
open KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise

universe u v

private theorem RootedIndicatorMarkovModel.IsRootedAtRadius.mono
    {G ι : Type u} [Group G]
    {X : RootedIndicatorMarkovModel G ι}
    {w : G → List ι} {r R : ℕ}
    (h : X.IsRootedAtRadius w R) (hr : r ≤ R) :
    X.IsRootedAtRadius w r :=
  ⟨fun a g hword => h.out a g (hword.trans hr)⟩

private theorem exists_rooted_word_radius_all_markov_iterate_contractions
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ j ≤ k,
        ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ ≤
          (kazhdanMarkovContractionFactor P S ^ j + ε) *
            ‖permutationMarkov X.generator
                (indicatorVector X.indicator) -
              indicatorVector X.indicator‖ := by
  classical
  have hexists : ∀ j : ℕ, ∃ r : ℕ,
      ∀ X : RootedIndicatorMarkovModel G ↥S,
        X.IsGenerated (fun i : ↥S => (i : G)) w →
        X.IsRootedAtRadius w r →
        ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ ≤
          (kazhdanMarkovContractionFactor P S ^ j + ε) *
            ‖permutationMarkov X.generator
                (indicatorVector X.indicator) -
              indicatorVector X.indicator‖ :=
    fun j => exists_rooted_word_radius_markov_iterate_contraction
      P S honeS hcover hsymmetric w j ε hε
  choose r hr using hexists
  let R := ∑ j ∈ Finset.range (k + 1), r j
  refine ⟨R, ?_⟩
  intro X hgenerated hroot j hj
  have hjmem : j ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
  have hrj : r j ≤ R := by
    exact Finset.single_le_sum
      (f := r) (fun i _ => Nat.zero_le _) hjmem
  exact hr j X hgenerated (hroot.mono hrj)

/-- The displacement of an iterate is bounded by its successive displacements. -/
public
theorem norm_iterate_sub_le_sum_successive
    {E : Type*} [NormedAddCommGroup E]
    (F : E → E) (x : E) (k : ℕ) :
    ‖(F^[k]) x - x‖ ≤
      ∑ j ∈ Finset.range k,
        ‖(F^[j + 1]) x - (F^[j]) x‖ := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, sub_self, norm_zero, Finset.range_zero,
    Function.iterate_succ,
              Function.comp_apply, Finset.sum_empty, Std.le_refl]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        ‖(F^[k + 1]) x - x‖ =
            ‖((F^[k]) x - x) +
              ((F^[k + 1]) x - (F^[k]) x)‖ := by
              congr 1
              abel
        _ ≤ ‖(F^[k]) x - x‖ +
              ‖(F^[k + 1]) x - (F^[k]) x‖ :=
          norm_add_le _ _
        _ ≤ (∑ j ∈ Finset.range k,
              ‖(F^[j + 1]) x - (F^[j]) x‖) +
              ‖(F^[k + 1]) x - (F^[k]) x‖ :=
          add_le_add ih (le_refl _)

private theorem sum_geometric_budget_le
    (q : ℝ) (hqzero : 0 ≤ q) (hqone : q < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      (q ^ j +
        (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹)) ≤
      2 / (1 - q) := by
  have hgap : 0 < 1 - q := sub_pos.mpr hqone
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hgeom :
      (∑ j ∈ Finset.range k, q ^ j) ≤ (1 - q)⁻¹ := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hqzero hqone)
  have hratio :
      (k : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hkpos).2
    rw [one_mul]
    exact_mod_cast Nat.le_succ k
  have hnoise :
      (k : ℝ) *
        (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ ≤
        (1 - q)⁻¹ := by
    calc
      (k : ℝ) *
          (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ =
        ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          (1 - q)⁻¹ := by
            field_simp
      _ ≤ 1 * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio
          (inv_nonneg.mpr hgap.le)
      _ = (1 - q)⁻¹ := one_mul _
  calc
    (∑ j ∈ Finset.range k,
      (q ^ j + (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹)) =
        (∑ j ∈ Finset.range k, q ^ j) +
          (k : ℝ) *
            (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ := by
              rw [Finset.sum_add_distrib]
              simp only [Nat.cast_add, Nat.cast_one, mul_inv_rev, Finset.sum_const,
                Finset.card_range, nsmul_eq_mul]
    _ ≤ (1 - q)⁻¹ + (1 - q)⁻¹ :=
      add_le_add hgeom hnoise
    _ = 2 / (1 - q) := by ring

private theorem exists_rooted_word_radius_geometric_markov_displacement
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector X.indicator) -
        indicatorVector X.indicator‖ ≤
      (2 / (1 - kazhdanMarkovContractionFactor P S)) *
        ‖permutationMarkov X.generator
            (indicatorVector X.indicator) -
          indicatorVector X.indicator‖ := by
  let q := kazhdanMarkovContractionFactor P S
  have hqzero : 0 ≤ q :=
    kazhdanMarkovContractionFactor_nonneg P S
  have hqone : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩
  let ε : ℝ := (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹
  have hε : 0 < ε :=
    inv_pos.mpr (mul_pos (by positivity) (sub_pos.mpr hqone))
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_all_markov_iterate_contractions
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨r, ?_⟩
  intro X hgenerated hroot
  let d : ℝ :=
    ‖permutationMarkov X.generator
        (indicatorVector X.indicator) -
      indicatorVector X.indicator‖
  have hsteps : ∀ j ∈ Finset.range k,
      ‖((permutationMarkov X.generator)^[j + 1])
          (indicatorVector X.indicator) -
        ((permutationMarkov X.generator)^[j])
          (indicatorVector X.indicator)‖ ≤
        (q ^ j + ε) * d := by
    intro j hj
    exact hr X hgenerated hroot j
      (Nat.le_of_lt (Finset.mem_range.mp hj))
  calc
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector X.indicator) -
      indicatorVector X.indicator‖ ≤
        ∑ j ∈ Finset.range k,
          ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ :=
      norm_iterate_sub_le_sum_successive
        (permutationMarkov X.generator)
        (indicatorVector X.indicator) k
    _ ≤ ∑ j ∈ Finset.range k, (q ^ j + ε) * d :=
      Finset.sum_le_sum hsteps
    _ = (∑ j ∈ Finset.range k, (q ^ j + ε)) * d := by
      rw [Finset.sum_mul]
    _ ≤ (2 / (1 - q)) * d :=
      mul_le_mul_of_nonneg_right
        (sum_geometric_budget_le q hqzero hqone k)
        (norm_nonneg _)
    _ = (2 / (1 - kazhdanMarkovContractionFactor P S)) *
        ‖permutationMarkov X.generator
            (indicatorVector X.indicator) -
          indicatorVector X.indicator‖ := by
      rfl

end

section

open Filter Topology
open KunRootedIndicatorCrossing
open KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise

universe u

private theorem rooted_realMarkov_eq_mass_realPermutationMarkov
    {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) :
    KunRealComplexMarkovBridge.realMarkov p =
      KunFinitePermutationMarkovMass.realPermutationMarkov p := by
  funext f x
  simp only [KunRealComplexMarkovBridge.realMarkov, div_eq_mul_inv, mul_comm,
    KunFinitePermutationMarkovMass.realPermutationMarkov]

private theorem rooted_markov_real_iterate_sq_error
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 =
      ∑ x : V,
        ((((KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T)) x -
          if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  have h :=
    KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_sq
      p (KunFinitePermutationMarkovMass.realIndicator T) k
  have hcomplex :
      KunRealComplexMarkovBridge.permutationMarkov p =
        KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      KunRealComplexMarkovBridge.indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T) =
        KunRootedIndicatorCrossing.indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T) := rfl
  rw [rooted_realMarkov_eq_mass_realPermutationMarkov] at h
  rw [hcomplex, hvector] at h
  simpa only [KunFinitePermutationMarkovMass.realIndicator] using h

private theorem rooted_indicator_defect_sq_le_boundary
    {ι V : Type*} [Fintype ι] [Nonempty ι]
    [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) :
    ‖permutationMarkov p
        (indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 ≤
      2 * (boundary p T : ℝ) /
        (Fintype.card ι : ℝ) := by
  have hcomplex :
      KunRealComplexMarkovBridge.permutationMarkov p =
        KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      KunRealComplexMarkovBridge.indicatorVector
          (KunDirectedIndicatorJensen.realIndicator T) =
        KunRootedIndicatorCrossing.indicatorVector
          (KunDirectedIndicatorJensen.realIndicator T) := rfl
  have hreal :
      KunRealComplexMarkovBridge.realMarkov p
          (KunDirectedIndicatorJensen.realIndicator T) =
        KunDirectedIndicatorJensen.realPermutationMarkov p
          (KunDirectedIndicatorJensen.realIndicator T) := rfl
  have henergy :=
    KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
      p (KunDirectedIndicatorJensen.realIndicator T)
  rw [hcomplex, hvector, hreal] at henergy
  have hindicator :
      KunFinitePermutationMarkovMass.realIndicator T =
        KunDirectedIndicatorJensen.realIndicator T := by
    funext x
    simp only [KunFinitePermutationMarkovMass.realIndicator,
      KunDirectedIndicatorJensen.realIndicator]
  rw [hindicator]
  calc
    ‖permutationMarkov p
        (indicatorVector
          (KunDirectedIndicatorJensen.realIndicator T)) -
        indicatorVector
          (KunDirectedIndicatorJensen.realIndicator T)‖ ^ 2 =
      ∑ x,
        (KunDirectedIndicatorJensen.realPermutationMarkov p
          (KunDirectedIndicatorJensen.realIndicator T) x -
            KunDirectedIndicatorJensen.realIndicator T x) ^ 2 := by
          exact henergy
    _ ≤ 2 * (boundary p T : ℝ) /
        (Fintype.card ι : ℝ) :=
      KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
        p T

end

end KunRootedWordPower

namespace KunActualRootedModelBridge

open KunActualSoficRootRadius
open KunRootedIndicatorCrossing
open KunRootedWordPower
open KunThomInvariantOrthogonal
open scoped BigOperators

universe u

private def sourceFiniteIndicator
    {V : Type*} [DecidableEq V] (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0

private def sourceRootedIndicatorMarkovModel
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (T : Finset (Fin (A.model n).size)) :
    RootedIndicatorMarkovModel G ↥S where
  carrier := Fin (A.model n).size
  fintype := inferInstance
  generator i := (A.model n).action (i : G)
  indicator := sourceFiniteIndicator T
  evaluation :=
    chosenWordEvaluation A (fun i : ↥S => (i : G))
      (symmetricGeneratorWord S hsymmetric hgenerates) n

private theorem sourceRootedIndicatorMarkovModel_isGenerated
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (T : Finset (Fin (A.model n).size)) :
    (sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T).IsGenerated
        (fun i : ↥S => (i : G))
        (symmetricGeneratorWord S hsymmetric hgenerates) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change sourceFiniteIndicator T x = 0 ∨
      sourceFiniteIndicator T x = 1
    by_cases hx : x ∈ T
    · right
      unfold sourceFiniteIndicator
      split
      · rfl
      · rename_i hnot
        exact (hnot hx).elim
    · left
      unfold sourceFiniteIndicator
      split
      · rename_i hmem
        exact (hx hmem).elim
      · rfl
  · intro g
    rfl
  · exact chosen_symmetric_wordEvaluation_one
      A S hsymmetric hgenerates n
  · intro i
    exact chosen_symmetric_wordEvaluation_generator
      A S hsymmetric hgenerates n i

private theorem sourceRootedIndicatorMarkovModel_isRootedAtRadius
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G) (hone : 1 ∈ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n r : ℕ) (T : Finset (Fin (A.model n).size))
    (hgood : Disjoint T
      (chosenCayleyRadiusBad A S
        (symmetricGeneratorWord S hsymmetric hgenerates) n r)) :
    (sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T).IsRootedAtRadius
        (symmetricGeneratorWord S hsymmetric hgenerates) r := by
  refine ⟨?_⟩
  intro a g hword x hx
  have hxreal : sourceFiniteIndicator T x ≠ 0 := by
    intro hzero
    apply hx
    change (sourceFiniteIndicator T x : ℂ) = 0
    exact_mod_cast hzero
  have hxT : x ∈ T := by
    by_contra hnot
    apply hxreal
    unfold sourceFiniteIndicator
    split
    · rename_i hmem
      exact (hnot hmem).elim
    · rfl
  have hxgood := Finset.disjoint_left.mp hgood hxT
  exact chosenCayleyRadiusBad_rooted
    A S hone (symmetricGeneratorWord S hsymmetric hgenerates)
    (symmetricGeneratorWord_prod S hsymmetric hgenerates)
    n r a g hword hxgood

end KunActualRootedModelBridge

namespace KunSharpThresholdCut

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

private def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun x => t < f x)

private def highCrossingProfile {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a t : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    (Finset.univ.filter (fun x : V => a < f x)).sum (fun x =>
      (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t))

private theorem highCrossingProfile_eq_boundary {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a t : ℝ)
    (hat : a < t) :
    highCrossingProfile σ f a t =
      (boundary σ (upperLevel f t) : ℝ) := by
  classical
  unfold highCrossingProfile boundary upperLevel
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mem_Ico, indicator,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  all_goals grind

private theorem integrableOn_crossingIndicator
    (a b c d : ℝ) :
    IntegrableOn ((Ico a b).indicator (fun _ => (1 : ℝ)))
      (Ioo c d) := by
  exact (integrableOn_const (μ := volume)
    (C := (1 : ℝ)) (s := Ioo c d)
    (by simp only [Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])).indicator
      measurableSet_Ico

private theorem integrableOn_highCrossingProfile {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    IntegrableOn (highCrossingProfile σ f a) (Ioo c d) := by
  unfold highCrossingProfile
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun x _ =>
      integrableOn_crossingIndicator (f (σ i x)) (f x) c d

private theorem setIntegral_crossingIndicator_le_abs
    (a b c d : ℝ) :
    (∫ t in Ioo c d,
      (Ico a b).indicator (fun _ => (1 : ℝ)) t) ≤ |b - a| := by
  calc
    (∫ t in Ioo c d,
        (Ico a b).indicator (fun _ => (1 : ℝ)) t) =
        (volume.restrict (Ioo c d)).real (Ico a b) := by
          exact integral_indicator_one (μ := volume.restrict (Ioo c d))
            measurableSet_Ico
    _ = volume.real (Ico a b ∩ Ioo c d) :=
      measureReal_restrict_apply measurableSet_Ico
    _ ≤ volume.real (Ico a b) :=
      measureReal_mono inter_subset_left
        (by simp only [Real.volume_Ico, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])
    _ = max (b - a) 0 := Real.volume_real_Ico
    _ ≤ |b - a| := max_le (le_abs_self _) (abs_nonneg _)

private theorem setIntegral_highCrossingProfile_le_variation {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    (∫ t in Ioo c d, highCrossingProfile σ f a t) ≤
      ∑ i : ι, ∑ x ∈ Finset.univ.filter (fun x : V => a < f x),
        |f (σ i x) - f x| := by
  classical
  let H : Finset V := Finset.univ.filter fun x : V => a < f x
  have hint (i : ι) (x : V) :
      Integrable
        ((Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)))
        (volume.restrict (Ioo c d)) :=
    integrableOn_crossingIndicator (f (σ i x)) (f x) c d
  calc
    (∫ t in Ioo c d, highCrossingProfile σ f a t) =
        ∑ i : ι, ∑ x ∈ H, (∫ t in Ioo c d,
          (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) := by
      unfold highCrossingProfile
      change (∫ t in Ioo c d, ∑ i : ι, ∑ x ∈ H,
        (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) = _
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum H
          (fun x _ => hint i x))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum H (fun x _ => hint i x)]
    _ ≤ ∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro x _
      calc
        (∫ t in Ioo c d,
          (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t) ≤
            |f x - f (σ i x)| :=
              setIntegral_crossingIndicator_le_abs
                (f (σ i x)) (f x) c d
        _ = |f (σ i x) - f x| := abs_sub_comm _ _
    _ = ∑ i : ι, ∑ x ∈ Finset.univ.filter
        (fun x : V => a < f x), |f (σ i x) - f x| := by
      rfl

private theorem card_symmDiff_upperLevel_le_nine_sq_error {V : Type*}
    [Fintype V] [DecidableEq V]
    (T : Finset V) (f : V → ℝ) (t : ℝ)
    (hlow : (1 / 3 : ℝ) ≤ t) (hhigh : t ≤ (2 / 3 : ℝ)) :
    (((upperLevel f t ∆ T).card : ℝ)) ≤
      9 * ∑ x : V, (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  classical
  let D : Finset V := upperLevel f t ∆ T
  have hpoint (x : V) (hx : x ∈ D) :
      (1 : ℝ) ≤
        9 * (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
    rcases (Finset.mem_symmDiff.mp hx) with hx | hx
    · obtain ⟨hxlevel, hxT⟩ := hx
      have hfx : t < f x := (Finset.mem_filter.mp hxlevel).2
      simp only [ite_eq_right hxT]
      nlinarith [sq_nonneg (3 * f x - 1)]
    · obtain ⟨hxT, hxlevel⟩ := hx
      have hfx : f x ≤ t := by
        apply le_of_not_gt
        intro h
        exact hxlevel
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      simp only [ite_eq_left hxT]
      nlinarith [sq_nonneg (3 * f x - 2)]
  have hcard :
      (D.card : ℝ) = ∑ x : V, if x ∈ D then (1 : ℝ) else 0 := by
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  change (D.card : ℝ) ≤ _
  rw [hcard]
  calc
    (∑ x : V, if x ∈ D then (1 : ℝ) else 0) ≤
        ∑ x : V,
          9 * (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ D
      · simpa only [ite_eq_left hx] using hpoint x hx
      · simp only [ite_eq_right hx]
        positivity
    _ = 9 * ∑ x : V,
        (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
      rw [Finset.mul_sum]

private theorem exists_upperLevel_boundary_and_symmDiff_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ) :
    ∃ t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
      (boundary σ (upperLevel f t) : ℝ) ≤
          3 * ∑ i : ι,
            ∑ x ∈ Finset.univ.filter
              (fun x : V => (1 / 3 : ℝ) < f x),
                |f (σ i x) - f x| ∧
        (((upperLevel f t ∆ T).card : ℝ)) ≤
          9 * ∑ x : V,
            (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  have hpos : volume (Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) ≠ 0 := by
    norm_num [Real.volume_Ioo]
  have hfin : volume (Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) ≠ ∞ := by
    simp only [one_div, Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  obtain ⟨t, ht, hmean⟩ :=
    exists_le_setAverage (μ := volume)
      (s := Ioo (1 / 3 : ℝ) (2 / 3 : ℝ))
      hpos hfin
      (integrableOn_highCrossingProfile σ f (1 / 3) _ _)
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← highCrossingProfile_eq_boundary σ f (1 / 3) t ht.1]
    calc
      highCrossingProfile σ f (1 / 3) t ≤
          ⨍ u in Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
            highCrossingProfile σ f (1 / 3) u := hmean
      _ = 3 * (∫ u in Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
            highCrossingProfile σ f (1 / 3) u) := by
        rw [setAverage_eq, Real.volume_real_Ioo]
        norm_num
      _ ≤ 3 * ∑ i : ι,
          ∑ x ∈ Finset.univ.filter
            (fun x : V => (1 / 3 : ℝ) < f x),
              |f (σ i x) - f x| :=
        mul_le_mul_of_nonneg_left
          (setIntegral_highCrossingProfile_le_variation
            σ f (1 / 3) (1 / 3) (2 / 3)) (by norm_num)
  · exact card_symmDiff_upperLevel_le_nine_sq_error
      T f t ht.1.le ht.2.le

end KunSharpThresholdCut

namespace KunActualFinalRestrictedVariation

open scoped BigOperators

private def realMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i : ι, f ((σ i).symm x)) / (Fintype.card ι : ℝ)

private theorem sum_permutation_mul_eq_sum_inverse_mul
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, f (p x) * f x) =
      ∑ x : V, f x * f (p.symm x) := by
  calc
    (∑ x : V, f (p x) * f x) =
        ∑ x : V, f (p (p.symm x)) * f (p.symm x) :=
      (Equiv.sum_comp p.symm
        (fun x : V => f (p x) * f x)).symm
    _ = ∑ x : V, f x * f (p.symm x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [p.apply_symm_apply]

private theorem sum_sq_displacement_eq_twice_inverse_residual
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, (f (p x) - f x) ^ 2) =
      2 * ∑ x : V, f x * (f x - f (p.symm x)) := by
  have hsquare :
      (∑ x : V, f (p x) ^ 2) = ∑ x : V, f x ^ 2 :=
    Equiv.sum_comp p (fun x : V => f x ^ 2)
  have hcross := sum_permutation_mul_eq_sum_inverse_mul p f
  calc
    (∑ x : V, (f (p x) - f x) ^ 2) =
        (∑ x : V, f (p x) ^ 2) +
          (∑ x : V, f x ^ 2) -
            2 * ∑ x : V, f (p x) * f x := by
      calc
        (∑ x : V, (f (p x) - f x) ^ 2) =
            ∑ x : V,
              (f (p x) ^ 2 + f x ^ 2 -
                2 * (f (p x) * f x)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
    _ = 2 * ∑ x : V, f x * (f x - f (p.symm x)) := by
      rw [hsquare, hcross]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring_nf

private theorem sum_sum_sq_displacement_eq_twice_card_mul_realMarkov_residual
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) =
      2 * (Fintype.card ι : ℝ) *
        ∑ x : V, f x * (f x - realMarkov σ f x) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  calc
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) =
        2 * ∑ x : V, ∑ i : ι,
          f x * (f x - f ((σ i).symm x)) := by
      simp_rw [sum_sq_displacement_eq_twice_inverse_residual]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 2 * (Fintype.card ι : ℝ) *
        ∑ x : V, f x * (f x - realMarkov σ f x) := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      unfold realMarkov
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      field_simp

private theorem sum_sq_le_card_of_unit_interval_mass
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ x : V, f x ^ 2) ≤ (T.card : ℝ) := by
  calc
    (∑ x : V, f x ^ 2) ≤ ∑ x : V, f x := by
      apply Finset.sum_le_sum
      intro x _
      nlinarith [mul_nonneg (hfzero x)
        (sub_nonneg.mpr (hfone x))]
    _ = (T.card : ℝ) := hmass

private theorem realMarkov_residual_pairing_le_sqrt_card_mul_residual
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ x : V, f x * (f x - realMarkov σ f x)) ≤
      Real.sqrt (T.card : ℝ) *
        Real.sqrt (∑ x : V,
          (realMarkov σ f x - f x) ^ 2) := by
  have hsquare := sum_sq_le_card_of_unit_interval_mass
    T f hfzero hfone hmass
  calc
    (∑ x : V, f x * (f x - realMarkov σ f x)) ≤
        Real.sqrt (∑ x : V, f x ^ 2) *
          Real.sqrt (∑ x : V,
            (f x - realMarkov σ f x) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f
        (fun x => f x - realMarkov σ f x)
    _ ≤ Real.sqrt (T.card : ℝ) *
          Real.sqrt (∑ x : V,
            (f x - realMarkov σ f x) ^ 2) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsquare)
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (T.card : ℝ) *
          Real.sqrt (∑ x : V,
            (realMarkov σ f x - f x) ^ 2) := by
      congr 2
      apply Finset.sum_congr rfl
      intro x _
      ring

private theorem sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) * Real.sqrt (T.card : ℝ) *
        Real.sqrt (∑ x : V,
          (realMarkov σ f x - f x) ^ 2) := by
  rw [sum_sum_sq_displacement_eq_twice_card_mul_realMarkov_residual]
  have hpair := realMarkov_residual_pairing_le_sqrt_card_mul_residual
    σ T f hfzero hfone hmass
  have hfactor : 0 ≤ 2 * (Fintype.card ι : ℝ) := by positivity
  nlinarith [mul_nonneg hfactor
    (sub_nonneg.mpr hpair)]

private theorem card_highSupport_le_three_card
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (((Finset.univ.filter fun x : V =>
      (1 / 3 : ℝ) < f x).card : ℝ)) ≤ 3 * (T.card : ℝ) := by
  classical
  let H : Finset V :=
    Finset.univ.filter fun x : V => (1 / 3 : ℝ) < f x
  have hpoint (x : V) (hx : x ∈ H) :
      (1 : ℝ) ≤ 3 * f x := by
    have hx' : (1 / 3 : ℝ) < f x :=
      (Finset.mem_filter.mp hx).2
    linarith
  have hhigh : (H.card : ℝ) ≤ 3 * ∑ x ∈ H, f x := by
    calc
      (H.card : ℝ) = ∑ _x ∈ H, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ x ∈ H, 3 * f x :=
        Finset.sum_le_sum fun x hx => hpoint x hx
      _ = 3 * ∑ x ∈ H, f x := by rw [Finset.mul_sum]
  have hsum : (∑ x ∈ H, f x) ≤ ∑ x : V, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ H)
    intro x _ _
    exact hfzero x
  change (H.card : ℝ) ≤ 3 * (T.card : ℝ)
  calc
    (H.card : ℝ) ≤ 3 * ∑ x ∈ H, f x := hhigh
    _ ≤ 3 * ∑ x : V, f x :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 3 * (T.card : ℝ) := by rw [hmass]

private theorem filtered_variation_sq_le_card_mul_filtered_energy
    {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (H : Finset V) :
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
      (Fintype.card ι : ℝ) * (H.card : ℝ) *
        ∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product H)
    (fun _ : ι × V => (1 : ℝ))
    (fun z : ι × V => |f (σ z.1 z.2) - f z.2|)
  simpa only [mul_assoc, ge_iff_le, Finset.product_eq_sprod, one_mul, Finset.sum_product, one_pow,
    Finset.sum_const, Finset.card_product, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, mul_one,
      sq_abs] using hcs

private theorem filtered_variation_sq_le_card_mul_energy
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (H : Finset V) :
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
      (Fintype.card ι : ℝ) * (H.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
  classical
  have henergy :
      (∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2) ≤
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ H)
    intro x _ _
    exact sq_nonneg _
  calc
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
        (Fintype.card ι : ℝ) * (H.card : ℝ) *
          ∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2 :=
      filtered_variation_sq_le_card_mul_filtered_energy σ f H
    _ ≤ (Fintype.card ι : ℝ) * (H.card : ℝ) *
          ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem highSupport_variation_sq_le_three_mul_reference_energy
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (T : Finset V)
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ)) :
    (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ^ 2 ≤
      3 * (Fintype.card ι : ℝ) * (T.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
  have henergy :
      0 ≤ ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun x _ => sq_nonneg _
  calc
    (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ((Finset.univ.filter
            (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) *
          ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      filtered_variation_sq_le_card_mul_energy σ f
        (Finset.univ.filter fun x : V => (1 / 3 : ℝ) < f x)
    _ ≤ (Fintype.card ι : ℝ) * (3 * (T.card : ℝ)) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhigh (Nat.cast_nonneg _)) henergy
    _ = 3 * (Fintype.card ι : ℝ) * (T.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
      ring

private theorem high_variation_le_of_markov_square_bounds
    {d t α η b r E H : ℝ}
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ t)
    (hresidual : r ≤ η * b)
    (henergy : E ≤ 2 * d * Real.sqrt t * r)
    (hcauchy : H ^ 2 ≤ 3 * d * t * E)
    (hsmall : 486 * d ^ 2 * η ≤ 4 * α ^ 2) :
    9 * H ≤ 2 * α * t := by
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hb_sqrt : b ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hbase
  have hr_sqrt : r ≤ η * Real.sqrt t :=
    hresidual.trans (mul_le_mul_of_nonneg_left hb_sqrt hη)
  have henergy' : E ≤ 2 * d * η * t := by
    calc
      E ≤ 2 * d * Real.sqrt t * r := henergy
      _ ≤ 2 * d * Real.sqrt t * (η * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hr_sqrt
          (mul_nonneg (mul_nonneg (by norm_num) hd) hsqrt)
      _ = 2 * d * η * (Real.sqrt t) ^ 2 := by ring
      _ = 2 * d * η * t := by rw [hsqrt_sq]
  have hcauchy' : H ^ 2 ≤ 6 * d ^ 2 * η * t ^ 2 := by
    calc
      H ^ 2 ≤ 3 * d * t * E := hcauchy
      _ ≤ 3 * d * t * (2 * d * η * t) :=
        mul_le_mul_of_nonneg_left henergy'
          (mul_nonneg (mul_nonneg (by norm_num) hd) ht)
      _ = 6 * d ^ 2 * η * t ^ 2 := by ring
  have hsquare : (9 * H) ^ 2 ≤ (2 * α * t) ^ 2 := by
    have hsmall' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
    linarith only [hcauchy', hsmall']
  nlinarith only [hsquare, mul_nonneg hα ht]

private theorem highSupport_variation_le_of_realMarkov_residual_and_highSupport
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (α η b : ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ))
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ))
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ (T.card : ℝ))
    (hresidual :
      Real.sqrt (∑ x : V,
        (realMarkov σ f x - f x) ^ 2) ≤ η * b)
    (hsmall :
      486 * (Fintype.card ι : ℝ) ^ 2 * η ≤ 4 * α ^ 2) :
    9 * (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ≤ 2 * α * (T.card : ℝ) := by
  exact high_variation_le_of_markov_square_bounds
    (d := (Fintype.card ι : ℝ))
    (t := (T.card : ℝ))
    (α := α) (η := η) (b := b)
    (r := Real.sqrt (∑ x : V,
      (realMarkov σ f x - f x) ^ 2))
    (E := ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2)
    (H := ∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hα hη hbase hresidual
    (sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
      σ T f hfzero hfone hmass)
    (highSupport_variation_sq_le_three_mul_reference_energy
      σ f T hhigh)
    hsmall

private theorem highSupport_variation_le_of_realMarkov_residual
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (α η b : ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ))
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ (T.card : ℝ))
    (hresidual :
      Real.sqrt (∑ x : V,
        (realMarkov σ f x - f x) ^ 2) ≤ η * b)
    (hsmall :
      486 * (Fintype.card ι : ℝ) ^ 2 * η ≤ 4 * α ^ 2) :
    9 * (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ≤ 2 * α * (T.card : ℝ) := by
  exact highSupport_variation_le_of_realMarkov_residual_and_highSupport
    σ T f α η b hfzero hfone hmass
    (card_highSupport_le_three_card T f hfzero hmass)
    hα hη hbase hresidual hsmall

end KunActualFinalRestrictedVariation

namespace MatchedFirstStageWordRadiusTransfer

open Filter Topology
open scoped BigOperators

private theorem card_completed_sourceWordTestBad_le_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (P : Finset V) :
    (MatchedComponentExitBudget.sourceWordTestBad
      (fun i => MatchedComponentCompletion.completedRestriction
        (σ i) P)
      (fun j => MatchedComponentCompletion.completedRestriction
        (p j) P)
      F).card ≤
      (MatchedComponentCompletion.sourceCompletionBad
        σ p F P).card := by
  classical
  let σP : ι → Equiv.Perm {x : V // x ∈ P} := fun i =>
    MatchedComponentCompletion.completedRestriction (σ i) P
  let pP : J → Equiv.Perm {x : V // x ∈ P} := fun j =>
    MatchedComponentCompletion.completedRestriction (p j) P
  let W : Finset {x : V // x ∈ P} :=
    MatchedComponentExitBudget.sourceWordTestBad σP pP F
  have hσP :
      ∀ i (x : V) (hx : x ∈ P) (_hi : σ i x ∈ P),
        ((σP i ⟨x, hx⟩ : {x : V // x ∈ P}) : V) = σ i x := by
    intro i x hx hi
    exact MatchedComponentCompletion.completedRestriction_apply_of_mem
      (σ i) P x hx hi
  have hinject :
      W.map (Function.Embedding.subtype (fun x : V => x ∈ P)) ⊆
        MatchedComponentCompletion.sourceCompletionBad
          σ p F P := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    by_contra hnot
    have hwords : z ∈ W := hz
    simp only [MatchedComponentExitBudget.sourceWordTestBad, ne_eq, Finset.univ_eq_attach,
      Finset.union_assoc,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, Finset.mem_attach,
        true_and, W, pP,
      σP] at hwords
    rcases hwords with hcomm | hmul | hsep
    · obtain ⟨i, j, hj, hfailure⟩ := hcomm
      exact hfailure
        (MatchedComponentCompletion.completedRestriction_commute_of_not_mem_sourceCompletionBad
          σ p F P σP hσP hj i z hnot)
    · obtain ⟨j, hj, k, hk, hfailure⟩ := hmul
      apply hfailure
      simpa only [Equiv.Perm.mul_apply] using
        completedRestriction_mul_of_not_mem_sourceCompletionBad σ p F P hj hk z hnot
    · obtain ⟨j, hj, k, hk, hne, heq⟩ := hsep
      exact
        (MatchedComponentCompletion.completedRestriction_ne_of_not_mem_sourceCompletionBad
          σ p F P hj hk hne z hnot) heq
  change W.card ≤ _
  calc
    W.card =
        (W.map (Function.Embedding.subtype (fun x : V => x ∈ P))).card :=
      (Finset.card_map _).symm
    _ ≤ (MatchedComponentCompletion.sourceCompletionBad
          σ p F P).card := Finset.card_le_card hinject

private theorem completed_sourceWordTestBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (P E : (n : ℕ) → Finset (V n))
    (hcapture : ∀ n,
      MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆ P n ∩ E n)
    (hradius : Tendsto
      (fun n => (((P n ∩ E n).card : ℝ) / (P n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((MatchedComponentExitBudget.sourceWordTestBad
          (fun i => MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card : ℝ) / (P n).card)
      atTop (nhds 0) := by
  have hupper (n : ℕ) :
      ((MatchedComponentExitBudget.sourceWordTestBad
        (fun i => MatchedComponentCompletion.completedRestriction
          (σ n i) (P n))
        (fun j => MatchedComponentCompletion.completedRestriction
          (p n j) (P n))
        F).card : ℝ) / (P n).card ≤
          (((P n ∩ E n).card : ℝ) / (P n).card) := by
    have hfirst := card_completed_sourceWordTestBad_le_sourceCompletionBad
      (σ n) (p n) F (P n)
    have hsecond := Finset.card_le_card (hcapture n)
    have hcard :
        (MatchedComponentExitBudget.sourceWordTestBad
          (fun i => MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card ≤ (P n ∩ E n).card := hfirst.trans hsecond
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcard
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    (Filter.Eventually.of_forall hupper)
    hradius

private theorem completed_sourceWordTestBad_density_tendsto_zero_of_matchedRadius
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι κ J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (U P : (n : ℕ) → Finset (V n))
    (Q : (n : ℕ) → Finpartition (U n))
    (I : ℕ → Finset κ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (r : ℕ → ℕ)
    (B : (n : ℕ) → ℕ → Finset (V n))
    (hcapture : ∀ n,
      MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆
          P n ∩ matchedRadiusBad
            (Q n) (I (r n)) (w n) (B n (r n)))
    (hradius : Tendsto
      (fun n =>
        (((P n ∩ matchedRadiusBad
          (Q n) (I (r n)) (w n) (B n (r n))).card : ℝ) / (P n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((MatchedComponentExitBudget.sourceWordTestBad
          (fun i => MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card : ℝ) / (P n).card)
      atTop (nhds 0) := by
  exact completed_sourceWordTestBad_density_tendsto_zero
    V σ p F P
    (fun n => matchedRadiusBad
      (Q n) (I (r n)) (w n) (B n (r n)))
    hcapture hradius

public
theorem pruned_sourceCompletionBad_density_tendsto_zero_of_matchedRadius
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι κ J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (U P : (n : ℕ) → Finset (V n))
    (Q : (n : ℕ) → Finpartition (U n))
    (I : ℕ → Finset κ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (r : ℕ → ℕ)
    (B : (n : ℕ) → ℕ → Finset (V n))
    (D : (n : ℕ) → Finset {x : V n // x ∈ P n})
    (hcapture : ∀ n,
      MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆
          P n ∩ matchedRadiusBad
            (Q n) (I (r n)) (w n) (B n (r n)))
    (hradius : Tendsto
      (fun n =>
        (((P n ∩ matchedRadiusBad
          (Q n) (I (r n)) (w n) (B n (r n))).card : ℝ) / (P n).card))
      atTop (nhds 0))
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (P n).card)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((MatchedComponentCompletion.sourceCompletionBad
          (fun i => MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F (Finset.univ \ D n)).card : ℝ) /
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}).card)
      atTop (nhds 0) := by
  have hword :=
    completed_sourceWordTestBad_density_tendsto_zero_of_matchedRadius
      V σ p F U P Q I w r B hcapture hradius
  apply MatchedComponentExitBudget.sourceCompletionBad_surviving_density_tendsto_zero
      (fun n => {x : V n // x ∈ P n})
      (fun n i =>
        MatchedComponentCompletion.completedRestriction
          (σ n i) (P n))
      (fun n j =>
        MatchedComponentCompletion.completedRestriction
          (p n j) (P n))
      F D hZ
  · simpa only [Fintype.card_coe] using hdeleted
  · simpa only [Fintype.card_coe] using hword

end MatchedFirstStageWordRadiusTransfer

namespace SourceCompressionMatching

open Filter Topology
open scoped BigOperators symmDiff

private theorem lt_exp_mul_of_equal_log_floor
    {x y H r : ℝ} (hx : 0 < x) (hy : 0 < y) (hH : 0 < H)
    (hrank :
      ⌊(Real.log x + r) / H⌋ = ⌊(Real.log y + r) / H⌋) :
    y < Real.exp H * x := by
  have hyfloor := Int.lt_floor_add_one ((Real.log y + r) / H)
  rw [← hrank] at hyfloor
  have hxloor := Int.floor_le ((Real.log x + r) / H)
  have hratio :
      (Real.log y + r) / H < (Real.log x + r) / H + 1 :=
    hyfloor.trans_le (by
      simpa only [add_comm, add_le_add_iff_left] using (add_le_add_right hxloor 1))
  have hscaled := mul_lt_mul_of_pos_right hratio hH
  have hcancel :
      ((Real.log x + r) / H + 1) * H =
        Real.log x + r + H := by
    rw [add_mul, div_mul_cancel₀ _ hH.ne', one_mul]
  have hlog : Real.log y < Real.log x + H := by
    rw [div_mul_cancel₀ _ hH.ne', hcancel] at hscaled
    linarith
  have hexp := (Real.exp_lt_exp).2 hlog
  rw [Real.exp_log hy, Real.exp_add, Real.exp_log hx] at hexp
  simpa only [mul_comm, gt_iff_lt] using hexp

public
theorem transported_maximumOverlapPart_card_lt_exp_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (H r : ℝ) (hH : 0 < H) (x : V) (hx : x ∈ C)
    (hTx : T x ∈ maximumOverlapPart Q
      (C.map T.toEmbedding))
    (hrank :
      MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (partitionComponentSize Q z : ℝ))
          H r (T x) =
        MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (partitionComponentSize Q z : ℝ))
          H r x) :
    ((maximumOverlapPart Q
      (C.map T.toEmbedding)).card : ℝ) <
        Real.exp H * (C.card : ℝ) := by
  let D := maximumOverlapPart Q (C.map T.toEmbedding)
  have hCne : C.Nonempty := Q.nonempty_of_mem_parts hC
  have hD : D ∈ Q.parts :=
    maximumOverlapPart_mem Q (C.map T.toEmbedding)
      ((Finset.map_nonempty).2 hCne) (Finset.subset_univ _)
  have hsource : partitionComponentSize Q x = C.card :=
    partitionComponentSize_eq_card_of_mem Q C hC x hx
  have htarget : partitionComponentSize Q (T x) = D.card :=
    partitionComponentSize_eq_card_of_mem
      Q D hD (T x) hTx
  have hfloor :
      ⌊(Real.log (C.card : ℝ) + r) / H⌋ =
        ⌊(Real.log (D.card : ℝ) + r) / H⌋ := by
    simpa only [MidrankPermutationEnergy.offsetFloorRank, hsource, htarget] using hrank.symm
  have hxpos : (0 : ℝ) < C.card := by
    exact_mod_cast hCne.card_pos
  have hypos : (0 : ℝ) < D.card := by
    exact_mod_cast (Q.nonempty_of_mem_parts hD).card_pos
  exact lt_exp_mul_of_equal_log_floor hxpos hypos hH hfloor

private theorem card_symmDiff_add_twice_inter
    {V : Type*} [DecidableEq V] (C D : Finset V) :
    (C ∆ D).card + 2 * (C ∩ D).card = C.card + D.card := by
  have hdis : Disjoint (C \ D) (D \ C) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (C ∆ D).card = (C \ D).card + (D \ C).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have hC := Finset.card_sdiff_add_card_inter C D
  have hD := Finset.card_sdiff_add_card_inter D C
  rw [Finset.inter_comm D C] at hD
  omega

public
theorem symmDiff_card_lt_of_overlap_and_exp_card
    {V : Type*} [DecidableEq V]
    (C D : Finset V) (H eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤ ((C ∩ D).card : ℝ))
    (hcard : (D.card : ℝ) < Real.exp H * (C.card : ℝ)) :
    ((C ∆ D).card : ℝ) <
      (Real.exp H - 1 + 2 * eta) * (C.card : ℝ) := by
  have hexact :
      ((C ∆ D).card : ℝ) + 2 * ((C ∩ D).card : ℝ) =
        (C.card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast card_symmDiff_add_twice_inter C D
  nlinarith

public
theorem target_majority_of_overlap_and_exp_card
    {V : Type*} [DecidableEq V]
    (C D : Finset V) (hC : C.Nonempty) (H eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤ ((C ∩ D).card : ℝ))
    (hcard : (D.card : ℝ) < Real.exp H * (C.card : ℝ))
    (hsmall : 2 * (Real.exp H - 1 + 2 * eta) < 1) :
    D.card < 2 * (C ∩ D).card := by
  have hbound :=
    symmDiff_card_lt_of_overlap_and_exp_card C D H eta hoverlap hcard
  have hpositive : (0 : ℝ) < C.card := by
    exact_mod_cast hC.card_pos
  have hreal :
      (2 : ℝ) * ((C ∆ D).card : ℝ) < (C.card : ℝ) := by
    calc
      (2 : ℝ) * ((C ∆ D).card : ℝ) <
          2 * ((Real.exp H - 1 + 2 * eta) * (C.card : ℝ)) :=
        mul_lt_mul_of_pos_left hbound (by norm_num)
      _ = (2 * (Real.exp H - 1 + 2 * eta)) * (C.card : ℝ) := by
        ring
      _ < 1 * (C.card : ℝ) :=
        mul_lt_mul_of_pos_right hsmall hpositive
      _ = (C.card : ℝ) := one_mul _
  have hnat : 2 * (C ∆ D).card < C.card := by
    exact_mod_cast hreal
  exact target_majority_of_small_symmDiff C D hnat

public
theorem symmDiff_density_tendsto_zero_of_log_rank_bounds
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (H eta : ℕ → ℝ)
    (hH : ∀ n, 0 ≤ H n) (heta : ∀ n, 0 ≤ eta n)
    (hHzero : Tendsto H atTop (nhds 0))
    (hetazero : Tendsto eta atTop (nhds 0))
    (hbound : ∀ n C, C ∈ R n →
      ((C ∆ D n C).card : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ)) :
    Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (nhds 0) := by
  have hcoeff : Tendsto
      (fun n => Real.exp (H n) - 1 + 2 * eta n)
      atTop (nhds 0) := by
    have hexp : Tendsto (fun n => Real.exp (H n)) atTop (nhds 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto (0 : ℝ)).comp
        hHzero
    have hfirst : Tendsto
        (fun n => Real.exp (H n) - 1) atTop (nhds 0) := by
      simpa only [sub_self] using hexp.sub_const 1
    have hsecond : Tendsto
        (fun n => (2 : ℝ) * eta n) atTop (nhds 0) := by
      simpa only [mul_zero] using hetazero.const_mul 2
    simpa only [zero_add] using hfirst.add hsecond
  refine squeeze_zero (fun n => by positivity) ?_ hcoeff
  intro n
  have hpos : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hexp : 1 ≤ Real.exp (H n) := by
    simpa only [Real.one_le_exp_iff, Real.exp_zero] using (Real.exp_le_exp.mpr (hH n))
  have hnonneg : 0 ≤ Real.exp (H n) - 1 + 2 * eta n := by
    nlinarith [heta n]
  have hmassnat :
      (∑ C ∈ R n, C.card) ≤ (U n).card := by
    calc
      (∑ C ∈ R n, C.card) =
          (matchedRetainedSupport (R n)).card :=
        (matchedRetainedSupport_card
          (P n) (R n) (hR n)).symm
      _ ≤ (U n).card :=
        Finset.card_le_card
          (matchedRetainedSupport_subset
            (P n) (R n) (hR n))
  have hmass :
      (∑ C ∈ R n, (C.card : ℝ)) ≤ (U n).card := by
    exact_mod_cast hmassnat
  have hsum :
      ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ)) := by
    calc
      ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) =
          ∑ C ∈ R n, ((C ∆ D n C).card : ℝ) := by
            simp only [Nat.cast_sum]
      _ ≤ ∑ C ∈ R n,
          (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ) := by
            exact Finset.sum_le_sum fun C hC => hbound n C hC
      _ = (Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ)) := by
            rw [Finset.mul_sum]
  calc
    ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card ≤
        ((Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ))) / (U n).card :=
      (div_le_div_iff_of_pos_right hpos).2 hsum
    _ ≤ ((Real.exp (H n) - 1 + 2 * eta n) *
          (U n).card) / (U n).card := by
      apply (div_le_div_iff_of_pos_right hpos).2
      exact mul_le_mul_of_nonneg_left hmass hnonneg
    _ = Real.exp (H n) - 1 + 2 * eta n := by
      field_simp

end SourceCompressionMatching

namespace SourceCompressionTransportCrossing

open Filter Topology
open scoped BigOperators

private theorem mem_partitionWordCrossing_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (x : V) :
    x ∈ partitionWordCrossing Q p ↔
      Q.part x ≠ Q.part (p x) := by
  simp only [partitionWordCrossing, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Q.mem_part_iff_part_eq_part (Finset.mem_univ _)
    (Finset.mem_univ _)]
  simp only [eq_comm, ne_eq]

private theorem card_partitionWordCrossing_le_add_distance
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p q : Equiv.Perm V) :
    (partitionWordCrossing Q p).card ≤
      (partitionWordCrossing Q q).card +
        permutationDistance p q := by
  classical
  have hsub :
      partitionWordCrossing Q p ⊆
        partitionWordCrossing Q q ∪
          Finset.univ.filter (fun x : V => p x ≠ q x) := by
    intro x hx
    by_cases heq : p x = q x
    · apply Finset.mem_union_left
      apply (mem_partitionWordCrossing_univ Q q x).2
      have hp := (mem_partitionWordCrossing_univ Q p x).1 hx
      simpa only [ne_eq, heq] using hp
    · apply Finset.mem_union_right
      exact Finset.mem_filter.2 ⟨Finset.mem_univ x, heq⟩
  calc
    (partitionWordCrossing Q p).card ≤
        (partitionWordCrossing Q q ∪
          Finset.univ.filter (fun x : V => p x ≠ q x)).card :=
      Finset.card_le_card hsub
    _ ≤ (partitionWordCrossing Q q).card +
        (Finset.univ.filter (fun x : V => p x ≠ q x)).card :=
      Finset.card_union_le _ _
    _ = (partitionWordCrossing Q q).card +
        permutationDistance p q := by
      simp only [ne_eq, permutationDistance, hammingDist]

private theorem tendsto_action_inverse
    {G : Type*} [Group G] (A : SoficApproximation G)
    (u : G) :
    Tendsto
      (fun n => normalizedHamming
        (((A.model n).action u)⁻¹)
        ((A.model n).action (u⁻¹)))
      atTop (nhds 0) := by
  have heq :
      (fun n => normalizedHamming
        (((A.model n).action u)⁻¹)
        ((A.model n).action (u⁻¹))) =
      (fun n => normalizedHamming
        ((A.model n).action (u * u⁻¹))
        ((A.model n).action u * (A.model n).action (u⁻¹))) := by
    funext n
    calc
      normalizedHamming
          (((A.model n).action u)⁻¹)
          ((A.model n).action (u⁻¹)) =
        normalizedHamming
          ((A.model n).action u * ((A.model n).action u)⁻¹)
          ((A.model n).action u * (A.model n).action (u⁻¹)) :=
        (normalizedHamming_mul_left
          ((A.model n).action u)
          (((A.model n).action u)⁻¹)
          ((A.model n).action (u⁻¹))).symm
      _ = normalizedHamming
          ((A.model n).action (u * u⁻¹))
          ((A.model n).action u * (A.model n).action (u⁻¹)) := by
        simp only [mul_inv_cancel, (A.model n).map_one]
  rw [heq]
  exact A.multiplicative u (u⁻¹)

public
theorem tendsto_action_conjugate
    {G : Type*} [Group G] (A : SoficApproximation G)
    (u g : G) :
    Tendsto
      (fun n => normalizedHamming
        ((A.model n).action (u * g * u⁻¹))
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹))
      atTop (nhds 0) := by
  have hbound : ∀ n,
      normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) ≤
        normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (normalizedHamming
          ((A.model n).action (u * g))
          ((A.model n).action u * (A.model n).action g) +
          normalizedHamming
            ((A.model n).action (u⁻¹))
            (((A.model n).action u)⁻¹)) := by
    intro n
    calc
      normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) ≤
        normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        normalizedHamming
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) :=
        normalizedHamming_triangle _ _ _
      _ ≤ normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (normalizedHamming
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹))
          (((A.model n).action u * (A.model n).action g) *
            (A.model n).action (u⁻¹)) +
          normalizedHamming
            (((A.model n).action u * (A.model n).action g) *
              (A.model n).action (u⁻¹))
            (((A.model n).action u * (A.model n).action g) *
              ((A.model n).action u)⁻¹)) := by
        gcongr
        exact normalizedHamming_triangle _ _ _
      _ = normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (normalizedHamming
          ((A.model n).action (u * g))
          ((A.model n).action u * (A.model n).action g) +
          normalizedHamming
            ((A.model n).action (u⁻¹))
            (((A.model n).action u)⁻¹)) := by
        rw [normalizedHamming_mul_right,
          normalizedHamming_mul_left]
  apply squeeze_zero
    (fun n => normalizedHamming_nonneg _ _) hbound
  convert (A.multiplicative (u * g) (u⁻¹)).add
    ((A.multiplicative u g).add
      (tendsto_action_inverse A u)) using 1
  · funext n
    rw [normalizedHamming_comm
      ((A.model n).action (u⁻¹))
      (((A.model n).action u)⁻¹)]
  · norm_num

public
theorem conjugated_word_crossing_density_tendsto_zero
    {G : Type*} [Group G] (A : SoficApproximation G)
    (u g : G)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hword : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
  have hdist : Tendsto
      (fun n => normalizedHamming
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)))
      atTop (nhds 0) := by
    have heq :
        (fun n => normalizedHamming
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)
          ((A.model n).action (u * g * u⁻¹))) =
        (fun n => normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)) := by
      funext n
      exact normalizedHamming_comm _ _
    rw [heq]
    exact tendsto_action_conjugate A u g
  have hupper : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
            (A.model n).size +
        normalizedHamming
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)
          ((A.model n).action (u * g * u⁻¹)))
      atTop (nhds 0) := by
    simpa only [add_zero] using hword.add hdist
  refine squeeze_zero (fun n => by positivity) ?_ hupper
  intro n
  have hnat := card_partitionWordCrossing_le_add_distance (Q n)
    ((A.model n).action u * (A.model n).action g *
      ((A.model n).action u)⁻¹)
    ((A.model n).action (u * g * u⁻¹))
  have hreal :
      ((partitionWordCrossing (Q n)
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)).card : ℝ) ≤
      ((partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) +
      (permutationDistance
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((partitionWordCrossing (Q n)
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)).card : ℝ) /
        (A.model n).size ≤
      (((partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) +
      (permutationDistance
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) : ℝ)) /
          (A.model n).size :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((partitionWordCrossing (Q n)
        ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
          (A.model n).size +
      normalizedHamming
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹)
        ((A.model n).action (u * g * u⁻¹)) := by
      simp only [permutationDistance, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv, Function.comp_apply,
        add_div,
        normalizedHamming, Fintype.card_fin]

end SourceCompressionTransportCrossing

namespace KunResidualRetainedSelection

open Filter Topology
open scoped BigOperators Pointwise symmDiff

private theorem exists_matchedRetained_part_boundary_and_bad_density_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) (B : Finset V) :
    ∃ C ∈ R,
      (boundary σ C : ℝ) / C.card ≤
        ((∑ D ∈ R, (boundary σ D : ℝ)) +
          ((matchedRetainedSupport R ∩ B).card : ℝ)) /
            (matchedRetainedSupport R).card ∧
      ((C ∩ B).card : ℝ) / C.card ≤
        ((∑ D ∈ R, (boundary σ D : ℝ)) +
          ((matchedRetainedSupport R ∩ B).card : ℝ)) /
            (matchedRetainedSupport R).card := by
  let PR := matchedRetainedFinpartition P R hR
  have hweight : ∀ C ∈ R, 0 < (C.card : ℝ) := by
    intro C hC
    exact_mod_cast (P.nonempty_of_mem_parts (hR hC)).card_pos
  obtain ⟨C, hC, haverage⟩ :=
    matched_exists_le_weighted_average R hRne
      (fun C : Finset V => (C.card : ℝ))
      (fun C : Finset V => (boundary σ C : ℝ) +
        ((C ∩ B).card : ℝ)) hweight
  have hbad :
      (∑ D ∈ R, ((D ∩ B).card : ℝ)) =
        ((matchedRetainedSupport R ∩ B).card : ℝ) := by
    have h := matched_sum_card_inter_partition PR B
    exact_mod_cast h
  have hmass :
      (∑ D ∈ R, (D.card : ℝ)) =
        ((matchedRetainedSupport R).card : ℝ) := by
    exact_mod_cast (matchedRetainedSupport_card P R hR).symm
  have haverage' :
      ((boundary σ C : ℝ) + ((C ∩ B).card : ℝ)) /
          C.card ≤
        ((∑ D ∈ R, (boundary σ D : ℝ)) +
          ((matchedRetainedSupport R ∩ B).card : ℝ)) /
            (matchedRetainedSupport R).card := by
    simpa only [Finset.sum_add_distrib, hbad, hmass] using haverage
  have hden : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  refine ⟨C, hC, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg (C ∩ B).card)) hden).trans
        haverage'
  · exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_left
        (Nat.cast_nonneg (boundary σ C))) hden).trans
        haverage'

private theorem matchedRetained_boundary_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ R n, (boundary (σ n) C : ℝ)) /
          (matchedRetainedSupport (R n)).card)
      atTop (𝓝 0) := by
  have hcover := matchedRetainedSupport_cover_density_tendsto_one
    U hU P R hR hdiscard
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤
        ((matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  have htwice : Tendsto
      (fun n =>
        (2 : ℝ) *
          ((∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) / (U n).card))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hboundary :
        Tendsto
          (fun n =>
            (2 : ℝ) *
              ((∑ C ∈ (P n).parts,
                (boundary (σ n) C : ℝ)) / (U n).card))
          atTop (𝓝 ((2 : ℝ) * 0)))
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ htwice
  filter_upwards [hhalf] with n hn
  have hucard : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hrcard :
      (0 : ℝ) < (matchedRetainedSupport (R n)).card := by
    exact_mod_cast
      (matchedRetainedSupport_nonempty
        (P n) (R n) (hR n) (hRne n)).card_pos
  have hmass :
      ((U n).card : ℝ) ≤
        2 * (matchedRetainedSupport (R n)).card := by
    have h := (le_div_iff₀ hucard).1 hn
    linarith
  have hsum :
      (∑ C ∈ R n, (boundary (σ n) C : ℝ)) ≤
        ∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (hR n)
    intro C _ _
    positivity
  calc
    (∑ C ∈ R n, (boundary (σ n) C : ℝ)) /
        (matchedRetainedSupport (R n)).card ≤
      (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
        (matchedRetainedSupport (R n)).card :=
          div_le_div_of_nonneg_right hsum hrcard.le
    _ ≤ 2 *
      ((∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
        (U n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hrcard hucard).2
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hmass (Finset.sum_nonneg fun C _ => Nat.cast_nonneg
          (boundary (σ n) C)))

private theorem exists_matchedRetained_parts_with_vanishing_boundary_and_bad_density
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (B : ∀ n, Finset (V n))
    (hbad : Tendsto
      (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0)) :
    ∃ C : ∀ n, Finset (V n),
      (∀ n, C n ∈ R n) ∧
        Tendsto
          (fun n => (boundary (σ n) (C n) : ℝ) / (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
          atTop (𝓝 0) := by
  have hretboundary := matchedRetained_boundary_density_tendsto_zero
    σ U hU P R hR hRne hdiscard hboundary
  have hretbad := matchedRetained_bad_density_tendsto_zero
    U hU P R hR hRne hdiscard B hbad
  have hcombined : Tendsto
      (fun n =>
        ((∑ D ∈ R n, (boundary (σ n) D : ℝ)) +
          ((matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (matchedRetainedSupport (R n)).card)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hretboundary.add hretbad
  have hchoose (n : ℕ) :=
    exists_matchedRetained_part_boundary_and_bad_density_le
      (σ n) (P n) (R n) (hR n) (hRne n) (B n)
  let C : ∀ n, Finset (V n) := fun n => (hchoose n).choose
  have hC (n : ℕ) : C n ∈ R n := (hchoose n).choose_spec.1
  have hCb (n : ℕ) :
      (boundary (σ n) (C n) : ℝ) / (C n).card ≤
        ((∑ D ∈ R n, (boundary (σ n) D : ℝ)) +
          ((matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (matchedRetainedSupport (R n)).card :=
    (hchoose n).choose_spec.2.1
  have hCe (n : ℕ) :
      ((C n ∩ B n).card : ℝ) / (C n).card ≤
        ((∑ D ∈ R n, (boundary (σ n) D : ℝ)) +
          ((matchedRetainedSupport (R n) ∩ B n).card : ℝ)) /
            (matchedRetainedSupport (R n)).card :=
    (hchoose n).choose_spec.2.2
  exact ⟨C, hC,
    squeeze_zero (fun n => by positivity) hCb hcombined,
    squeeze_zero (fun n => by positivity) hCe hcombined⟩

private theorem exists_matched_slow_diagonal_large_components_with_vanishing_boundary
    {K : Type*} [Group K] [Infinite K] [DecidableEq K]
    (S : Finset K) (hS : 1 ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤)
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) :
            ℝ) / (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0))
    (hrealize : ∀ n k (C : Finset (V n)), C ∈ R n →
      ∀ x ∈ C,
        x ∉ matchedRadiusBad
          (P n) (I k) (w n) (B n k) →
          ∃ f : K → V n,
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K) (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K)) :
    ∃ (r : ℕ → ℕ) (C : ∀ n, Finset (V n)),
      Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R n) ∧
        Tendsto
          (fun n =>
            (boundary (σ n) (C n) : ℝ) / (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              matchedRadiusBad
                (P n) (I (r n)) (w n) (B n (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by
  obtain ⟨r, hr, herror⟩ :=
    exists_matched_slow_diagonal_word_errors
      U P Q R hR D hD hmajor hdiscard hsymm I w hword B hbad
  let B' : ∀ n, Finset (V n) := fun n =>
    matchedRadiusBad (P n) (I (r n)) (w n) (B n (r n))
  have hB' : Tendsto
      (fun n => (((U n ∩ B' n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) ?_ herror
    intro n
    have hcard :
        ((U n ∩ B' n).card : ℝ) ≤
          ((∑ i ∈ I (r n),
            (partitionWordCrossing
              (P n) (w n i)).card : ℕ) : ℝ) +
            ((U n ∩ B n (r n)).card : ℝ) := by
      have h := matchedRadiusBad_card_le
        (P n) (I (r n)) (w n) (B n (r n))
      have h' :
          (U n ∩
            matchedRadiusBad
              (P n) (I (r n)) (w n) (B n (r n))).card ≤
                (∑ i ∈ I (r n),
                  (partitionWordCrossing
                    (P n) (w n i)).card) +
                  (U n ∩ B n (r n)).card := by
        omega
      dsimp [B']
      exact_mod_cast h'
    exact div_le_div_of_nonneg_right hcard (by positivity)
  obtain ⟨C, hC, hCboundary, hCerror⟩ :=
    exists_matchedRetained_parts_with_vanishing_boundary_and_bad_density
      σ U hU P R hR hRne hdiscard B' hB' hboundary
  have hCnonempty (n : ℕ) : (C n).Nonempty :=
    (P n).nonempty_of_mem_parts (hR n (hC n))
  have hgood : ∀ᶠ n in atTop, ∃ x ∈ C n, x ∉ B' n :=
    matched_eventually_exists_good_vertex
      C B' hCnonempty hCerror
  have hhalf : Tendsto (fun n => r n / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hr
  have hclosure :
      (Subgroup.closure (S : Set K) : Set K).Infinite := by
    simpa only [hgen, Subgroup.coe_top] using (Set.infinite_univ (α := K))
  have hlarge : Tendsto (fun n => (C n).card) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [hgood] with n hn
    obtain ⟨x, hx, hx'⟩ := hn
    obtain ⟨f, hf, hfinj⟩ :=
      hrealize n (r n) (C n) (hC n) x hx hx'
    exact (Nat.le_succ (r n / 2)).trans
      ((Finset.add_one_le_card_pow hS hclosure (r n / 2)).trans
        (Finset.card_le_card_of_injOn f hf hfinj))
  exact ⟨r, C, hr, hC, hCboundary, hCerror, hlarge⟩

private theorem matchedRetained_parts_eventually_nonempty_of_discard
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (R : ∀ n, Finset (Finset (V n)))
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (R n).Nonempty := by
  filter_upwards [hdiscard.eventually (gt_mem_nhds zero_lt_one)] with n hn
  by_contra hR
  have hrempty : R n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
  have hucard : ((U n).card : ℝ) ≠ 0 := by
    exact_mod_cast (hU n).card_pos.ne'
  have hsupport : matchedRetainedSupport (R n) = ∅ := by
    simp only [matchedRetainedSupport, hrempty, Finset.biUnion_empty]
  simp only [hsupport, Finset.sdiff_empty] at hn
  rw [div_self hucard] at hn
  exact (lt_irrefl (1 : ℝ)) hn

private theorem exists_matched_slow_diagonal_large_components_on_guarded_tail
    {K : Type*} [Group K] [Infinite K] [DecidableEq K]
    (S : Finset K) (hS : 1 ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤)
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (guard : ℕ → Prop)
    (hguard : ∀ᶠ n in atTop, guard n)
    (hmajor : ∀ n, guard n → ∀ C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card :
            ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0))
    (hrealize : ∀ n k (C : Finset (V n)), C ∈ R n →
      ∀ x ∈ C,
        x ∉ matchedRadiusBad
          (P n) (I k) (w n) (B n k) →
          ∃ f : K → V n,
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K)
              (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (V (n + N))),
      N₀ ≤ N ∧
        (∀ n, guard (n + N)) ∧
        Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R (n + N)) ∧
        Tendsto
          (fun n =>
            (boundary (σ (n + N)) (C n) : ℝ) /
              (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              matchedRadiusBad
                (P (n + N)) (I (r n)) (w (n + N))
                (B (n + N) (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by
  have hretained :=
    matchedRetained_parts_eventually_nonempty_of_discard
      U hU R hdiscard
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.1 (hretained.and hguard)
  let N : ℕ := max N₀ N₁
  have htail (n : ℕ) :
      (R (n + N)).Nonempty ∧ guard (n + N) :=
    hN₁ (n + N) (by dsimp [N]; omega)
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have hdiscard' : Tendsto
      (fun n =>
        (((U (n + N) \
          matchedRetainedSupport (R (n + N))).card : ℝ) /
            (U (n + N)).card))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hdiscard.comp hshift
  have hsymm' : Tendsto
      (fun n =>
        ((∑ C ∈ R (n + N),
          (C ∆ D (n + N) C).card : ℕ) : ℝ) /
            (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hsymm.comp hshift
  have hword' (k : ℕ) : Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing
            (Q (n + N)) (w (n + N) i)).card : ℕ) : ℝ) /
              (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (hword k).comp hshift
  have hbad' (k : ℕ) : Tendsto
      (fun n =>
        (((U (n + N) ∩ B (n + N) k).card : ℝ) /
          (U (n + N)).card))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (hbad k).comp hshift
  have hboundary' : Tendsto
      (fun n =>
        (∑ C ∈ (P (n + N)).parts,
          (boundary (σ (n + N)) C : ℝ)) /
            (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hboundary.comp hshift
  obtain ⟨r, C, hr, hC, hCboundary, hCbad, hClarge⟩ :=
    exists_matched_slow_diagonal_large_components_with_vanishing_boundary
      S hS hgen
      (fun n => σ (n + N))
      (fun n => U (n + N))
      (fun n => hU (n + N))
      (fun n => P (n + N))
      (fun n => Q (n + N))
      (fun n => R (n + N))
      (fun n => hR (n + N))
      (fun n => (htail n).1)
      (fun n C => D (n + N) C)
      (fun n C hC => hD (n + N) C hC)
      (fun n C hC => hmajor (n + N) (htail n).2 C hC)
      hdiscard' hsymm' I
      (fun n => w (n + N))
      hword'
      (fun n k => B (n + N) k)
      hbad' hboundary'
      (fun n k C hC x hx hx' =>
        hrealize (n + N) k C hC x hx hx')
  refine ⟨N, r, C, ?_, (fun n => (htail n).2), hr, hC,
    hCboundary, hCbad, hClarge⟩
  exact le_max_left _ _

private theorem source_compression_scale_guard_eventually
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      eta n ≤ (1 : ℝ) / 2 ∧
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 := by
  have hhalf : ∀ᶠ n in atTop, eta n ≤ (1 : ℝ) / 2 :=
    (heta.eventually (gt_mem_nhds (by norm_num :
      (0 : ℝ) < (1 : ℝ) / 2))).mono fun _ h => h.le
  have hexp : Tendsto
      (fun n => Real.exp (H n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp hH
  have hinner : Tendsto
      (fun n => Real.exp (H n) - 1 + 2 * eta n)
      atTop (𝓝 0) := by
    have htwo : Tendsto
        (fun n => (2 : ℝ) * eta n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul heta)
    have hone : Tendsto
        (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [sub_self, add_zero] using (hexp.sub hone).add htwo
  have hsmallLimit : Tendsto
      (fun n => (2 : ℝ) * (Real.exp (H n) - 1 + 2 * eta n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hinner)
  exact hhalf.and
    (hsmallLimit.eventually (gt_mem_nhds zero_lt_one))

public
theorem exists_matched_slow_diagonal_large_components_on_source_scale_tail
    {K : Type*} [Group K] [Infinite K] [DecidableEq K]
    (S : Finset K) (hS : 1 ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤)
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (hmajor : ∀ n,
      eta n ≤ (1 : ℝ) / 2 →
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        ∀ C, C ∈ R n →
          (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card :
            ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0))
    (hrealize : ∀ n k (C : Finset (V n)), C ∈ R n →
      ∀ x ∈ C,
        x ∉ matchedRadiusBad
          (P n) (I k) (w n) (B n k) →
          ∃ f : K → V n,
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K)
              (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (V (n + N))),
      N₀ ≤ N ∧
        (∀ n, eta (n + N) ≤ (1 : ℝ) / 2) ∧
        (∀ n,
          2 * (Real.exp (H (n + N)) - 1 +
            2 * eta (n + N)) < 1) ∧
        Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R (n + N)) ∧
        Tendsto
          (fun n =>
            (boundary (σ (n + N)) (C n) : ℝ) /
              (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              matchedRadiusBad
                (P (n + N)) (I (r n)) (w (n + N))
                (B (n + N) (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by
  let guard : ℕ → Prop := fun n =>
    eta n ≤ (1 : ℝ) / 2 ∧
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1
  have hguard : ∀ᶠ n in atTop, guard n :=
    source_compression_scale_guard_eventually H eta hH heta
  obtain ⟨N, r, C, hN, hg, hr, hC, hCboundary, hCbad, hClarge⟩ :=
    exists_matched_slow_diagonal_large_components_on_guarded_tail
      S hS hgen σ U hU P Q R hR D hD guard hguard
      (fun n hn C hC => hmajor n hn.1 hn.2 C hC)
      hdiscard hsymm I w hword B hbad hboundary hrealize N₀
  exact ⟨N, r, C, hN,
    (fun n => (hg n).1), (fun n => (hg n).2),
    hr, hC, hCboundary, hCbad, hClarge⟩

end KunResidualRetainedSelection

namespace KunUniversalGoodRootReferenceCuts

open scoped symmDiff

private theorem reference_difference_le_symmDiff_add_missing
    {α : Type*} [DecidableEq α]
    (U T W : Finset α) (hsub : T ⊆ W) :
    (U \ W).card + (W \ U).card ≤
      (U ∆ T).card + (W \ T).card := by
  have hdisjoint : Disjoint (U \ W) (W \ U) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset
      Finset.sdiff_disjoint
  have htw : (T ∆ W).card = (W \ T).card := by
    rw [Finset.symmDiff_def,
      Finset.sdiff_eq_empty_iff_subset.mpr hsub,
      Finset.empty_union]
  calc
    (U \ W).card + (W \ U).card = (U ∆ W).card := by
      rw [Finset.symmDiff_def,
        Finset.card_union_of_disjoint hdisjoint]
    _ ≤ ((U ∆ T) ∪ (T ∆ W)).card :=
      Finset.card_le_card (symmDiff_triangle U T W)
    _ ≤ (U ∆ T).card + (T ∆ W).card :=
      Finset.card_union_le _ _
    _ = (U ∆ T).card + (W \ T).card := by rw [htw]

private theorem reference_difference_le_of_good_root_threshold
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V)
    (B : Finset V) (T U : Finset (V × V))
    (t : ℕ) (q : ℝ) (hq : q < 1)
    (hsub : T ⊆ permutationGraph p)
    (hmissing :
      (permutationGraph p \ T).card ≤ 2 * B.card)
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤ (t : ℝ))
    (hdefect : permutationCommutationDefect σ p ≤ 2 * t)
    (hboundary :
      boundary (fun i => (σ i).prodCongr (σ i)) T ≤
        permutationCommutationDefect σ p +
          2 * Fintype.card ι * B.card)
    (hthreshold :
      ((U ∆ T).card : ℝ) ≤
        72 * (boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) /
            ((Fintype.card ι : ℝ) * (1 - q) ^ 2)) :
    (((U \ permutationGraph p).card +
      (permutationGraph p \ U).card : ℕ) : ℝ) ≤
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ)) * (t : ℝ) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hden : 0 < (Fintype.card ι : ℝ) * (1 - q) ^ 2 :=
    mul_pos hd (sq_pos_of_pos (sub_pos.mpr hq))
  have hdefect_real :
      (permutationCommutationDefect σ p : ℝ) ≤
        2 * (t : ℝ) := by
    exact_mod_cast hdefect
  have hboundary_real :
      (boundary
        (fun i => (σ i).prodCongr (σ i)) T : ℝ) ≤
          3 * (t : ℝ) := by
    have hbound :
        (boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) ≤
            (permutationCommutationDefect σ p : ℝ) +
              2 * (Fintype.card ι : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hboundary
    linarith
  have hmissing_real :
      ((permutationGraph p \ T).card : ℝ) ≤
        (t : ℝ) / (Fintype.card ι : ℝ) := by
    have hm :
        ((permutationGraph p \ T).card : ℝ) ≤
          2 * (B.card : ℝ) := by
      exact_mod_cast hmissing
    apply (le_div_iff₀ hd).2
    nlinarith
  have htransfer :
      (((U \ permutationGraph p).card +
        (permutationGraph p \ U).card : ℕ) : ℝ) ≤
          ((U ∆ T).card : ℝ) +
            ((permutationGraph p \ T).card : ℝ) := by
    exact_mod_cast reference_difference_le_symmDiff_add_missing
      U T (permutationGraph p) hsub
  calc
    (((U \ permutationGraph p).card +
      (permutationGraph p \ U).card : ℕ) : ℝ) ≤
        ((U ∆ T).card : ℝ) +
          ((permutationGraph p \ T).card : ℝ) := htransfer
    _ ≤ 72 * (boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) /
            ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          (t : ℝ) / (Fintype.card ι : ℝ) :=
      add_le_add hthreshold hmissing_real
    _ ≤ 72 * (3 * (t : ℝ)) /
          ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          (t : ℝ) / (Fintype.card ι : ℝ) := by
      gcongr
    _ = (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ)) * (t : ℝ) := by
      ring

private theorem rooted_reference_cut_bounds_of_slow_tolerance
    {h d C t N Δ u e : ℝ}
    (hh : 0 < h) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hN : 0 < N)
    (hdifference : Δ ≤ C * t)
    (hcard : u ≤ N + Δ)
    (hboundary : e ≤ (h * t / (2 * (h + 8 * d) * N)) * u)
    (hslow : 5 * (4 + h * C) * t ≤ h * N) :
    2 * Δ ≤ N ∧
      (h + 8 * d) * e ≤ h * t ∧
      5 * (4 * e + h * Δ) ≤ h * N := by
  have hden : 0 < h + 8 * d := by linarith
  have hCt : 5 * (C * t) ≤ N := by
    have hscaled : h * (5 * (C * t)) ≤ h * N := by
      linarith only [hslow, ht]
    exact le_of_mul_le_mul_left hscaled hh
  have hCtzero : 0 ≤ C * t := mul_nonneg hC ht
  have hnear : 2 * Δ ≤ N := by linarith only [hdifference, hCt, hCtzero]
  have hu : u ≤ 2 * N := by linarith only [hcard, hnear, hN]
  have hcoefficient : 0 ≤ h * t / (2 * (h + 8 * d) * N) := by
    positivity
  have he : e ≤ h * t / (h + 8 * d) := by
    calc
      e ≤ (h * t / (2 * (h + 8 * d) * N)) * u := hboundary
      _ ≤ (h * t / (2 * (h + 8 * d) * N)) * (2 * N) :=
        mul_le_mul_of_nonneg_left hu hcoefficient
      _ = h * t / (h + 8 * d) := by field_simp
  have himprovement : (h + 8 * d) * e ≤ h * t := by
    have he' := (le_div_iff₀ hden).mp he
    linarith only [he']
  have het : e ≤ t := by
    calc
      e ≤ h * t / (h + 8 * d) := he
      _ ≤ t := (div_le_iff₀ hden).2 (by linarith only [mul_nonneg hd ht])
  refine ⟨hnear, himprovement, ?_⟩
  calc
    5 * (4 * e + h * Δ) ≤ 5 * (4 * t + h * (C * t)) := by
      gcongr
    _ = 5 * (4 + h * C) * t := by ring
    _ ≤ h * N := hslow

private theorem hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
    {V ι : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h q : ℝ) (hpositive : 0 < h) (hq : q < 1)
    (B : Finset V)
    (good : Equiv.Perm V → Finset (V × V))
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤
        (tolerance : ℝ))
    (hgood_subset : ∀ p : Equiv.Perm V,
      good p ⊆ permutationGraph p)
    (hgood_missing : ∀ p : Equiv.Perm V,
      (permutationGraph p \ good p).card ≤
        2 * B.card)
    (hgood_boundary : ∀ p : Equiv.Perm V,
      boundary
        (fun i => (σ i).prodCongr (σ i)) (good p) ≤
          permutationCommutationDefect σ p +
            2 * Fintype.card ι * B.card)
    (hslow :
      5 * (4 + h *
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ))) * (tolerance : ℝ) ≤
            h * (Fintype.card V : ℝ))
    (hthreshold : ∀ p : Equiv.Perm V,
      permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          ((U ∆ good p).card : ℝ) ≤
            72 * (boundary
              (fun i => (σ i).prodCongr (σ i)) (good p) : ℝ) /
                ((Fintype.card ι : ℝ) * (1 - q) ^ 2) ∧
          (boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
              (h * (tolerance : ℝ) /
                (2 * (h + 8 * (Fintype.card ι : ℝ)) *
                  (Fintype.card V : ℝ))) * (U.card : ℝ)) :
    HasAlmostCentralizerImprovement σ tolerance := by
  let d : ℝ := Fintype.card ι
  let C : ℝ := 216 / (d * (1 - q) ^ 2) + 1 / d
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
    σ tolerance h hpositive hexp
  intro p hp
  obtain ⟨U, hnear_good, hboundary⟩ := hthreshold p hp
  have hdifference :
      (((U \ permutationGraph p).card +
        (permutationGraph p \ U).card : ℕ) : ℝ) ≤
          C * (tolerance : ℝ) := by
    simpa only [C, d] using
      reference_difference_le_of_good_root_threshold
        σ p B (good p) U tolerance q hq
        (hgood_subset p) (hgood_missing p)
        hbad hp (hgood_boundary p) hnear_good
  have hN : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty V)
  have hcardnat :
      U.card ≤ Fintype.card V +
        ((U \ permutationGraph p).card +
          (permutationGraph p \ U).card) := by
    have hinter := Finset.card_sdiff_add_card_inter
      U (permutationGraph p)
    have hsubset :
        (U ∩ permutationGraph p).card ≤
          (permutationGraph p).card :=
      Finset.card_le_card Finset.inter_subset_right
    have hgraph := KunThomFiberCoarea.permutationGraph_card p
    omega
  have hcard :
      (U.card : ℝ) ≤ (Fintype.card V : ℝ) +
        (((U \ permutationGraph p).card +
          (permutationGraph p \ U).card : ℕ) : ℝ) := by
    exact_mod_cast hcardnat
  have hslow' :
      5 * (4 + h * C) * (tolerance : ℝ) ≤
        h * (Fintype.card V : ℝ) := by
    simpa only [C, d] using hslow
  have hboundary' :
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
        (h * (tolerance : ℝ) /
          (2 * (h + 8 * d) * (Fintype.card V : ℝ))) *
            (U.card : ℝ) := by
    simpa only [d] using hboundary
  obtain ⟨hnear, himprovement, hdistance⟩ :=
    rooted_reference_cut_bounds_of_slow_tolerance
      hpositive hd.le hC (Nat.cast_nonneg tolerance) hN
      hdifference hcard hboundary' hslow'
  refine ⟨U, ?_, ?_, ?_⟩
  · exact_mod_cast hnear
  · simpa only [d] using himprovement
  · have hleft :
        ((U \ permutationGraph p).card : ℝ) ≤
          (((U \ permutationGraph p).card +
            (permutationGraph p \ U).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right
        (U \ permutationGraph p).card
        (permutationGraph p \ U).card
    linarith only [hdistance, mul_nonneg hpositive.le
      (sub_nonneg.mpr hleft)]

end KunUniversalGoodRootReferenceCuts

open KunUniversalGoodRootReferenceCuts

namespace KunRootedWordPower

open Filter Topology
open KunRootedIndicatorCrossing
open KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff

universe u

private instance rootedSparseModelDecidableEq
    {G ι : Type u} (X : RootedIndicatorMarkovModel G ι) :
    DecidableEq X.carrier :=
  Classical.decEq X.carrier

private theorem exists_rooted_word_radius_real_markov_sq_error_le_boundary
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ T : Finset X.carrier,
        (∀ x : X.carrier,
          X.indicator x = if x ∈ T then (1 : ℝ) else 0) →
        (∑ x : X.carrier,
          ((((KunFinitePermutationMarkovMass.realPermutationMarkov
              X.generator)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T)) x -
              if x ∈ T then (1 : ℝ) else 0) ^ 2) ≤
          8 * (boundary X.generator T : ℝ) /
            ((S.card : ℝ) *
              (1 - kazhdanMarkovContractionFactor P S) ^ 2) := by
  let : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let q := kazhdanMarkovContractionFactor P S
  have hgap : 0 < 1 - q :=
    sub_pos.mpr
      (kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩)
  have hdegree : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_geometric_markov_displacement
      P S honeS hcover hsymmetric w k
  refine ⟨r, ?_⟩
  intro X hgenerated hroot T hindicator
  let χ : X.carrier → ℝ :=
    KunFinitePermutationMarkovMass.realIndicator T
  have hχ : X.indicator = χ := by
    funext x
    simpa [χ,
      KunFinitePermutationMarkovMass.realIndicator]
      using hindicator x
  have hgeo := hr X hgenerated hroot
  rw [hχ] at hgeo
  have hjensen :
      ‖permutationMarkov X.generator (indicatorVector χ) -
        indicatorVector χ‖ ^ 2 ≤
        2 * (boundary X.generator T : ℝ) /
          (S.card : ℝ) := by
    simpa only [Fintype.card_coe] using rooted_indicator_defect_sq_le_boundary X.generator T
  have hcoef : 0 ≤ 2 / (1 - q) :=
    div_nonneg (by norm_num) hgap.le
  have hsquare :
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
        (2 / (1 - q)) ^ 2 *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖ ^ 2 := by
    calc
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
        ((2 / (1 - q)) *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hcoef (norm_nonneg _))).mpr hgeo
      _ = (2 / (1 - q)) ^ 2 *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖ ^ 2 := by
        rw [mul_pow]
  rw [← rooted_markov_real_iterate_sq_error X.generator T k]
  change
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
      8 * (boundary X.generator T : ℝ) /
        ((S.card : ℝ) * (1 - q) ^ 2)
  calc
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
      (2 / (1 - q)) ^ 2 *
        ‖permutationMarkov X.generator (indicatorVector χ) -
          indicatorVector χ‖ ^ 2 := hsquare
    _ ≤ (2 / (1 - q)) ^ 2 *
        (2 * (boundary X.generator T : ℝ) /
          (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hjensen (sq_nonneg _)
    _ = 8 * (boundary X.generator T : ℝ) /
        ((S.card : ℝ) * (1 - q) ^ 2) := by
      field_simp
      ring

private theorem rooted_final_realMarkov_eq_mass_realPermutationMarkov
    {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) :
    KunActualFinalRestrictedVariation.realMarkov p =
      KunFinitePermutationMarkovMass.realPermutationMarkov p := by
  funext f x
  simp only [KunActualFinalRestrictedVariation.realMarkov, div_eq_mul_inv, mul_comm,
    KunFinitePermutationMarkovMass.realPermutationMarkov]

private theorem rooted_real_markov_iterate_residual_sqrt_eq
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    Real.sqrt
      (∑ x : V,
        (KunActualFinalRestrictedVariation.realMarkov p
          ((((KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T))) x -
          ((((KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T)) x)) ^ 2) =
      ‖((permutationMarkov p)^[k + 1])
          (indicatorVector
            (KunFinitePermutationMarkovMass.realIndicator T)) -
        ((permutationMarkov p)^[k])
          (indicatorVector
            (KunFinitePermutationMarkovMass.realIndicator T))‖ := by
  have hcomplex :
      KunRealComplexMarkovBridge.permutationMarkov p =
        KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      KunRealComplexMarkovBridge.indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T) =
        KunRootedIndicatorCrossing.indicatorVector
          (KunFinitePermutationMarkovMass.realIndicator T) := rfl
  have henergy :=
    KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
      p (KunFinitePermutationMarkovMass.realIndicator T) k
  rw [hcomplex, hvector,
    rooted_realMarkov_eq_mass_realPermutationMarkov] at henergy
  have hfinal := rooted_final_realMarkov_eq_mass_realPermutationMarkov p
  have hsum :
      (∑ x : V,
        (KunActualFinalRestrictedVariation.realMarkov p
          ((((KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T))) x -
          ((((KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (KunFinitePermutationMarkovMass.realIndicator T)) x)) ^ 2) =
      ‖((permutationMarkov p)^[k + 1])
          (indicatorVector
            (KunFinitePermutationMarkovMass.realIndicator T)) -
        ((permutationMarkov p)^[k])
          (indicatorVector
            (KunFinitePermutationMarkovMass.realIndicator T))‖ ^ 2 := by
    rw [hfinal]
    simpa only [Function.iterate_succ_apply'] using henergy.symm
  rw [hsum, Real.sqrt_sq (norm_nonneg _)]

private theorem close_and_large_of_symmDiff_bound
    {V : Type*} [DecidableEq V] (U T : Finset V)
    (boundaryValue denominator : ℝ)
    (hdenominator : 0 < denominator)
    (hdistance :
      (((U ∆ T).card : ℝ)) ≤
        72 * boundaryValue / denominator)
    (hscaled :
      216 * boundaryValue < denominator * (T.card : ℝ)) :
    3 * (U ∆ T).card < T.card ∧
      2 * (T.card : ℝ) ≤ 3 * (U.card : ℝ) := by
  have hcloseReal :
      (3 : ℝ) * (((U ∆ T).card : ℝ)) < (T.card : ℝ) := by
    calc
      (3 : ℝ) * (((U ∆ T).card : ℝ)) ≤
          216 * boundaryValue / denominator := by
        calc
          (3 : ℝ) * (((U ∆ T).card : ℝ)) ≤
              3 * (72 * boundaryValue / denominator) :=
            mul_le_mul_of_nonneg_left hdistance (by norm_num)
          _ = 216 * boundaryValue / denominator := by ring
      _ < (T.card : ℝ) :=
        (div_lt_iff₀ hdenominator).2 (by nlinarith only [hscaled])
  have hclose : 3 * (U ∆ T).card < T.card := by
    exact_mod_cast hcloseReal
  have hsub : T ⊆ U ∪ (U ∆ T) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union.mpr (Or.inl hxU)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_symmDiff.mpr (Or.inr ⟨hx, hxU⟩)))
  have hcard : T.card ≤ U.card + (U ∆ T).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le U (U ∆ T))
  have hcardReal :
      (T.card : ℝ) ≤ (U.card : ℝ) + (((U ∆ T).card : ℝ)) := by
    exact_mod_cast hcard
  exact ⟨hclose, by linarith only [hcardReal, hcloseReal]⟩

private theorem exists_rooted_word_radius_sparse_cut_of_boundary
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (γ α : ℝ) (_hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ (k r : ℕ), ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ T : Finset X.carrier,
        T.Nonempty →
        (∀ x : X.carrier,
          X.indicator x = if x ∈ T then (1 : ℝ) else 0) →
        (boundary X.generator T : ℝ) <
          γ * (T.card : ℝ) →
        ∃ U : Finset X.carrier,
          (((U ∆ T).card : ℝ)) ≤
            9 * (∑ x : X.carrier,
              ((((KunFinitePermutationMarkovMass.realPermutationMarkov
                X.generator)^[k])
                  (KunFinitePermutationMarkovMass.realIndicator T)) x -
                if x ∈ T then (1 : ℝ) else 0) ^ 2) ∧
          (((U ∆ T).card : ℝ)) ≤
            72 * (boundary X.generator T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
          3 * (U ∆ T).card < T.card ∧
          (boundary X.generator U : ℝ) ≤
            α * (U.card : ℝ) := by
  classical
  let : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let q := kazhdanMarkovContractionFactor P S
  have hqzero : 0 ≤ q :=
    kazhdanMarkovContractionFactor_nonneg P S
  have hqone : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩
  have hgap : 0 < 1 - q := sub_pos.mpr hqone
  have hdegree : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  let η : ℝ := 4 * α ^ 2 / (486 * (S.card : ℝ) ^ 2)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hη hqone
  let ε : ℝ := (η - q ^ k) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨rnear, hnear⟩ :=
    exists_rooted_word_radius_real_markov_sq_error_le_boundary
      P S honeS hcover hsymmetric w k
  obtain ⟨rfinal, hfinal⟩ :=
    exists_rooted_word_radius_markov_iterate_contraction
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨k, max rnear rfinal, ?_⟩
  intro X hgenerated hroot T hT hindicator hboundary
  have hrootnear := hroot.mono (le_max_left rnear rfinal)
  have hrootfinal := hroot.mono (le_max_right rnear rfinal)
  let χ : X.carrier → ℝ :=
    KunFinitePermutationMarkovMass.realIndicator T
  let f : X.carrier → ℝ :=
    ((KunFinitePermutationMarkovMass.realPermutationMarkov
      X.generator)^[k]) χ
  let b : ℝ :=
    ‖permutationMarkov X.generator (indicatorVector χ) -
      indicatorVector χ‖
  have hχ : X.indicator = χ := by
    funext x
    simpa [χ,
      KunFinitePermutationMarkovMass.realIndicator]
      using hindicator x
  have hD :
      (∑ x : X.carrier,
        (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2) ≤
        8 * (boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by
    simpa only using hnear X hgenerated hrootnear T hindicator
  have hstep := hfinal X hgenerated hrootfinal
  rw [hχ] at hstep
  have hresidual :
      Real.sqrt
        (∑ x : X.carrier,
          (KunActualFinalRestrictedVariation.realMarkov
            X.generator f x - f x) ^ 2) ≤ η * b := by
    calc
      Real.sqrt
          (∑ x : X.carrier,
            (KunActualFinalRestrictedVariation.realMarkov
              X.generator f x - f x) ^ 2) =
          ‖((permutationMarkov X.generator)^[k + 1])
              (indicatorVector χ) -
            ((permutationMarkov X.generator)^[k])
              (indicatorVector χ)‖ := by
            simpa only [Function.iterate_succ, Function.comp_apply, f, χ] using
              rooted_real_markov_iterate_residual_sqrt_eq X.generator T k
      _ ≤ (q ^ k + ε) * b := hstep
      _ ≤ η * b := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [ε]
        linarith
  have hfzero : ∀ x : X.carrier, 0 ≤ f x := by
    intro x
    exact
      (KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
      X.generator T k x).1
  have hfone : ∀ x : X.carrier, f x ≤ 1 := by
    intro x
    exact
      (KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
      X.generator T k x).2
  have hmass : (∑ x : X.carrier, f x) = (T.card : ℝ) :=
    KunFinitePermutationMarkovMass.sum_realPermutationMarkov_iterate_indicator
      X.generator T k
  have hjensen :
      b ^ 2 ≤
        2 * (boundary X.generator T : ℝ) /
          (S.card : ℝ) := by
    simpa only [Fintype.card_coe] using rooted_indicator_defect_sq_le_boundary X.generator T
  have hgaple : 1 - q ≤ 1 := by linarith
  have hgapzero : 0 ≤ 1 - q := hgap.le
  have hgap_sq_le_one : (1 - q) ^ 2 ≤ 1 :=
    pow_le_one₀ hgapzero hgaple
  have hgamma_degree : 2 * γ ≤ (S.card : ℝ) := by
    have hsmalldegree :
        (S.card : ℝ) * (1 - q) ^ 2 ≤ (S.card : ℝ) :=
      mul_le_of_le_one_right hdegree.le hgap_sq_le_one
    change 216 * γ < (S.card : ℝ) * (1 - q) ^ 2
      at hγsmall
    linarith only [hγsmall, hsmalldegree, _hγ]
  have hbase : b ^ 2 ≤ (T.card : ℝ) := by
    refine hjensen.trans ?_
    apply (div_le_iff₀ hdegree).2
    have hscaled :=
      mul_le_mul_of_nonneg_right hgamma_degree
        (Nat.cast_nonneg T.card)
    have hboundary' :=
      mul_le_mul_of_nonneg_left hboundary.le
        (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hscaled, hboundary']
  have hsmall :
      486 * (Fintype.card (↥S) : ℝ) ^ 2 * η ≤
        4 * α ^ 2 := by
    have hne : (486 : ℝ) * (S.card : ℝ) ^ 2 ≠ 0 := by positivity
    rw [Fintype.card_coe]
    change 486 * (S.card : ℝ) ^ 2 * (4 * α ^ 2 / (486 * (S.card : ℝ) ^ 2)) ≤ _
    rw [mul_div_cancel₀ _ hne]
  have hvariation :=
    KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual
      X.generator T f α η b hfzero hfone hmass
        hα.le hη.le hbase hresidual hsmall
  obtain ⟨t, _ht, hcut, hdistance⟩ :=
    KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le
      X.generator T f
  let U : Finset X.carrier :=
    KunSharpThresholdCut.upperLevel f t
  have hquant :
      (((U ∆ T).card : ℝ)) ≤
        72 * (boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by
    calc
      (((U ∆ T).card : ℝ)) ≤
          9 * ∑ x : X.carrier,
            (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 :=
        hdistance
      _ ≤ 9 *
          (8 * (boundary X.generator T : ℝ) /
            ((S.card : ℝ) * (1 - q) ^ 2)) :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = 72 * (boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by ring
  have hTpos : 0 < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hdenom :
      0 < (S.card : ℝ) * (1 - q) ^ 2 :=
    mul_pos hdegree (sq_pos_of_pos hgap)
  have hscaled :
      216 * (boundary X.generator T : ℝ) <
        ((S.card : ℝ) * (1 - q) ^ 2) * (T.card : ℝ) := by
    calc
      216 * (boundary X.generator T : ℝ) <
        216 * (γ * (T.card : ℝ)) :=
        mul_lt_mul_of_pos_left hboundary (by norm_num)
      _ = (216 * γ) * (T.card : ℝ) := by ring
      _ < ((S.card : ℝ) * (1 - q) ^ 2) * (T.card : ℝ) :=
        mul_lt_mul_of_pos_right hγsmall hTpos
  obtain ⟨hclose, hlarge⟩ :=
    close_and_large_of_symmDiff_bound U T
      (boundary X.generator T)
      ((S.card : ℝ) * (1 - q) ^ 2)
      hdenom hquant hscaled
  have hscaledlarge :=
    mul_le_mul_of_nonneg_left hlarge hα.le
  have hboundaryU :
      (boundary X.generator U : ℝ) ≤
        α * (U.card : ℝ) := by
    change
      (boundary X.generator
        (KunSharpThresholdCut.upperLevel f t) : ℝ) ≤ _
    nlinarith only [hcut, hvariation, hscaledlarge]
  exact ⟨U, by simpa only [f, χ] using hdistance,
    by simpa only [q] using hquant, hclose, hboundaryU⟩

end KunRootedWordPower

namespace SourceCompressionRetainedDiscard

open Filter Topology
open scoped BigOperators symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def witnesslessComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    Finset (Finset V) :=
  (P.parts \ insufficientOverlapComponents P Q eta).filter
    (fun C => ∀ y ∈ C ∩ maximumOverlapPart Q C,
      b (T.symm y) ≠ b y)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def retainedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    Finset (Finset V) :=
  P.parts \ (insufficientOverlapComponents P Q eta ∪
    witnesslessComponents P Q T b eta)

private theorem witnesslessComponents_subset_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    witnesslessComponents P Q T b eta ⊆ P.parts := by
  intro C hC
  exact (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hC).1).1

private theorem overlapBad_disjoint_witnesslessComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    Disjoint (insufficientOverlapComponents P Q eta)
      (witnesslessComponents P Q T b eta) := by
  apply Finset.disjoint_left.mpr
  intro C hbad hwitnessless
  exact (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hwitnessless).1).2 hbad

public
theorem retainedComponents_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ)
    (C : Finset V)
    (hC : C ∈ retainedComponents P Q T b eta) :
    C ∈ P.parts ∧
      maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ maximumOverlapPart Q C).card : ℝ) ∧
      ∃ y ∈ C ∩ maximumOverlapPart Q C,
        b (T.symm y) = b y := by
  have hmem := Finset.mem_sdiff.mp hC
  have hpart : C ∈ P.parts := hmem.1
  have hnotbad : C ∉ insufficientOverlapComponents P Q eta :=
    fun h => hmem.2 (Finset.mem_union_left _ h)
  have hnotwitnessless : C ∉ witnesslessComponents P Q T b eta :=
    fun h => hmem.2 (Finset.mem_union_right _ h)
  have htarget : maximumOverlapPart Q C ∈ Q.parts :=
    maximumOverlapPart_mem Q C
      (P.nonempty_of_mem_parts hpart) (P.subset hpart)
  have hoverlap :=
    maximumOverlapPart_overlap_of_not_mem_insufficient
      P Q eta C hpart hnotbad
  refine ⟨hpart, htarget, hoverlap, ?_⟩
  by_contra hnone
  push Not at hnone
  apply hnotwitnessless
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hpart, hnotbad⟩, hnone⟩

private theorem witnessless_component_card_le_twice_rankChanging
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2)
    (C : Finset V)
    (hC : C ∈ witnesslessComponents P Q T b eta) :
    C.card ≤
      2 * (C ∩ RankArcCharging.rankChangingArc
        (Finset.univ : Finset V) b T.symm).card := by
  have hfilter := Finset.mem_filter.mp hC
  have hgood := Finset.mem_sdiff.mp hfilter.1
  have hpart : C ∈ P.parts := hgood.1
  have hnotbad : C ∉ insufficientOverlapComponents P Q eta :=
    hgood.2
  have hoverlap :=
    maximumOverlapPart_overlap_of_not_mem_insufficient
      P Q eta C hpart hnotbad
  have hsubset :
      C ∩ maximumOverlapPart Q C ⊆
        C ∩ RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm := by
    intro y hy
    have hy' := Finset.mem_inter.mp hy
    refine Finset.mem_inter.mpr ⟨hy'.1, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ y, hfilter.2 y hy⟩
  have hcard :
      ((C ∩ maximumOverlapPart Q C).card : ℝ) ≤
        ((C ∩ RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hhalf :
      (1 / 2 : ℝ) * (C.card : ℝ) ≤
        (1 - eta) * (C.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hreal :
      (C.card : ℝ) ≤
        2 * ((C ∩ RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card : ℝ) := by
    linarith
  exact_mod_cast hreal

private theorem witnesslessComponents_mass_le_twice_rankChanging
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2) :
    (∑ C ∈ witnesslessComponents P Q T b eta, C.card) ≤
      2 * (RankArcCharging.rankChangingArc
        (Finset.univ : Finset V) b T.symm).card := by
  let B := RankArcCharging.rankChangingArc
    (Finset.univ : Finset V) b T.symm
  have hsum :
      (∑ C ∈ witnesslessComponents P Q T b eta, (C ∩ B).card) ≤
        ∑ C ∈ P.parts, (C ∩ B).card := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (witnesslessComponents_subset_parts P Q T b eta)
      (fun _ _ _ => Nat.zero_le _)
  have hpartition :
      (∑ C ∈ P.parts, (C ∩ B).card) = B.card := by
    simpa only [Finset.univ_inter] using matched_sum_card_inter_partition P B
  calc
    (∑ C ∈ witnesslessComponents P Q T b eta, C.card) ≤
        ∑ C ∈ witnesslessComponents P Q T b eta,
          2 * (C ∩ B).card := by
      exact Finset.sum_le_sum fun C hC =>
        witnessless_component_card_le_twice_rankChanging
          P Q T b eta heta C hC
    _ = 2 * (∑ C ∈ witnesslessComponents P Q T b eta,
          (C ∩ B).card) := by
      simp only [Finset.mul_sum]
    _ ≤ 2 * (∑ C ∈ P.parts, (C ∩ B).card) :=
      Nat.mul_le_mul_left 2 hsum
    _ = 2 * B.card := by rw [hpartition]

private theorem retained_missing_card_le_overlap_add_twice_rankChanging
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2) :
    ((Finset.univ : Finset V) \
      matchedRetainedSupport
        (retainedComponents P Q T b eta)).card ≤
      (∑ C ∈ insufficientOverlapComponents P Q eta, C.card) +
        2 * (RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card := by
  let O := insufficientOverlapComponents P Q eta
  let W := witnesslessComponents P Q T b eta
  let R := retainedComponents P Q T b eta
  let B := RankArcCharging.rankChangingArc
    (Finset.univ : Finset V) b T.symm
  have hR : R ⊆ P.parts := Finset.sdiff_subset
  have hmiss :
      ((Finset.univ : Finset V) \
        matchedRetainedSupport R).card =
          ∑ C ∈ P.parts \ R, C.card := by
    have hsplit :
        (∑ C ∈ P.parts \ R, C.card) +
          (∑ C ∈ R, C.card) =
            ∑ C ∈ P.parts, C.card :=
      Finset.sum_sdiff hR
    have hcover := P.sum_card_parts
    have hret := matchedRetainedSupport_card P R hR
    have hcard := Finset.card_sdiff_add_card_eq_card
      (matchedRetainedSupport_subset P R hR)
    omega
  have hsubset : P.parts \ R ⊆ O ∪ W := by
    intro C hC
    have hC' := Finset.mem_sdiff.mp hC
    by_contra hbad
    apply hC'.2
    change C ∈ P.parts \ (O ∪ W)
    exact Finset.mem_sdiff.mpr ⟨hC'.1, hbad⟩
  have hsum :
      (∑ C ∈ P.parts \ R, C.card) ≤
        ∑ C ∈ O ∪ W, C.card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hdis : Disjoint O W :=
    overlapBad_disjoint_witnesslessComponents P Q T b eta
  have hunion :
      (∑ C ∈ O ∪ W, C.card) =
        (∑ C ∈ O, C.card) + (∑ C ∈ W, C.card) :=
    Finset.sum_union hdis
  have hwitness : (∑ C ∈ W, C.card) ≤ 2 * B.card :=
    witnesslessComponents_mass_le_twice_rankChanging
      P Q T b eta heta
  change
    ((Finset.univ : Finset V) \
      matchedRetainedSupport R).card ≤
        (∑ C ∈ O, C.card) + 2 * B.card
  omega

public
theorem retained_missing_density_tendsto_zero
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ) (eta : ℕ → ℝ)
    (heta : Tendsto eta atTop (nhds 0))
    (hoverlap : Tendsto
      (fun n =>
        ((∑ C ∈ insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        ((RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ : Finset (V n)) \
          matchedRetainedSupport
            (retainedComponents (P n) (Q n) (T n) (b n)
              (eta n))).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by
  have hhalf : ∀ᶠ n in atTop, eta n < (1 : ℝ) / 2 :=
    heta.eventually (gt_mem_nhds (by norm_num))
  have htwice : Tendsto
      (fun n => (2 : ℝ) *
        (((RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
            Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hrank.const_mul 2
  have hupper : Tendsto
      (fun n =>
        ((∑ C ∈ insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n) +
          (2 : ℝ) *
            (((RankArcCharging.rankChangingArc
              (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
                Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [zero_add] using hoverlap.add htwice
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ hupper
  filter_upwards [hhalf] with n hn
  have hnat := retained_missing_card_le_overlap_add_twice_rankChanging
    (P n) (Q n) (T n) (b n) (eta n) hn.le
  have hreal :
      (((Finset.univ : Finset (V n)) \
        matchedRetainedSupport
          (retainedComponents (P n) (Q n) (T n) (b n)
            (eta n))).card : ℝ) ≤
        ((∑ C ∈ insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) +
          2 * ((RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (((Finset.univ : Finset (V n)) \
      matchedRetainedSupport
        (retainedComponents (P n) (Q n) (T n) (b n)
          (eta n))).card : ℝ) / Fintype.card (V n) ≤
        (((∑ C ∈ insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) +
          2 * ((RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ)) /
            Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((∑ C ∈ insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n) +
          (2 : ℝ) *
            (((RankArcCharging.rankChangingArc
              (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
                Fintype.card (V n)) := by
      ring

end SourceCompressionRetainedDiscard

namespace SourceGeneratedWordCrossing

open Filter Topology
open scoped BigOperators



private theorem card_partitionWordCrossing_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p q : Equiv.Perm V) :
    (partitionWordCrossing Q (p * q)).card ≤
      (partitionWordCrossing Q p).card +
        (partitionWordCrossing Q q).card := by
  classical
  have hsub :
      partitionWordCrossing Q (p * q) ⊆
        partitionWordCrossing Q q ∪
          (partitionWordCrossing Q p).map
            q.symm.toEmbedding := by
    intro x hx
    have hpq := (SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ Q (p * q) x).1 hx
    by_cases hq : Q.part x ≠ Q.part (q x)
    · exact Finset.mem_union_left _
        ((SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ Q q x).2 hq)
    · apply Finset.mem_union_right
      apply Finset.mem_map.2
      refine ⟨q x, (SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ Q p (q x)).2
        ?_,
        by simp only [Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]⟩
      intro heq
      apply hpq
      have hpart : Q.part x = Q.part (q x) := not_ne_iff.mp hq
      simpa only [Equiv.Perm.mul_apply] using hpart.trans heq
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le
      (partitionWordCrossing Q q)
      ((partitionWordCrossing Q p).map
        q.symm.toEmbedding))
  simpa only [ge_iff_le, Finset.card_map, Nat.add_comm] using hcard

public
theorem sum_generator_crossing_eq_sum_partition_boundary
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) :
    (∑ i : ι, (partitionWordCrossing Q (σ i)).card) =
      ∑ C ∈ Q.parts, boundary σ C := by
  classical
  have hpart (i : ι) (C : Finset V) (hC : C ∈ Q.parts) :
      C ∩ partitionWordCrossing Q (σ i) =
        C.filter (fun x => σ i x ∉ C) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter,
      partitionWordCrossing, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hcross⟩
      refine ⟨hx, ?_⟩
      simpa only [Q.part_eq_of_mem hC hx] using hcross
    · rintro ⟨hx, hcross⟩
      refine ⟨hx, ?_⟩
      simpa only [Q.part_eq_of_mem hC hx] using hcross
  calc
    (∑ i : ι, (partitionWordCrossing Q (σ i)).card) =
      ∑ i : ι, ∑ C ∈ Q.parts,
        (C.filter (fun x => σ i x ∉ C)).card := by
      apply Finset.sum_congr rfl
      intro i _
      have hsum := sum_card_inter_partition Q
        (partitionWordCrossing Q (σ i))
      simp only [Finset.univ_inter] at hsum
      calc
        (partitionWordCrossing Q (σ i)).card =
            ∑ C ∈ Q.parts,
              (C ∩ partitionWordCrossing Q (σ i)).card :=
          hsum.symm
        _ = ∑ C ∈ Q.parts,
              (C.filter (fun x => σ i x ∉ C)).card := by
          apply Finset.sum_congr rfl
          intro C hC
          rw [hpart i C hC]
    _ = ∑ C ∈ Q.parts,
        ∑ i : ι, (C.filter (fun x => σ i x ∉ C)).card := by
      rw [Finset.sum_comm]
    _ = ∑ C ∈ Q.parts, boundary σ C := by
      simp only [boundary]

public
theorem generator_crossing_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (i : ι) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          (σ n i)).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hboundary
  intro n
  have hsingle :
      (partitionWordCrossing (Q n) (σ n i)).card ≤
        ∑ j : ι,
          (partitionWordCrossing (Q n) (σ n j)).card := by
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le
        (partitionWordCrossing (Q n) (σ n j)).card)
      (Finset.mem_univ i)
  have hsum := sum_generator_crossing_eq_sum_partition_boundary
    (Q n) (σ n)
  have hreal :
      ((partitionWordCrossing (Q n) (σ n i)).card : ℝ) ≤
        ∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ) := by
    exact_mod_cast hsingle.trans (le_of_eq hsum)
  exact div_le_div_of_nonneg_right hreal (by positivity)

private theorem list_generator_crossing_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*}
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hgenerator : ∀ i : ι, Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          (σ n i)).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (l : List ι) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((l.map (σ n)).prod)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp only [partitionWordCrossing, List.map_nil, List.prod_nil, Equiv.Perm.coe_one, id_eq,
        Finpartition.mem_part_self, Finset.mem_univ, not_true_eq_false, Finset.filter_false,
          Finset.card_empty,
        CharP.cast_eq_zero, zero_div, tendsto_const_nhds_iff]
  | cons i l ih =>
      have hupper : Tendsto
          (fun n =>
            ((partitionWordCrossing (Q n)
              (σ n i)).card : ℝ) / Fintype.card (V n) +
            ((partitionWordCrossing (Q n)
              ((l.map (σ n)).prod)).card : ℝ) /
                Fintype.card (V n))
          atTop (nhds 0) := by
        simpa only [add_zero] using (hgenerator i).add ih
      refine squeeze_zero (fun n => by positivity) ?_ hupper
      intro n
      have hnat := card_partitionWordCrossing_mul_le (Q n)
        (σ n i) ((l.map (σ n)).prod)
      have hreal :
          ((partitionWordCrossing (Q n)
            (σ n i * (l.map (σ n)).prod)).card : ℝ) ≤
          ((partitionWordCrossing (Q n)
            (σ n i)).card : ℝ) +
          ((partitionWordCrossing (Q n)
            ((l.map (σ n)).prod)).card : ℝ) := by
        exact_mod_cast hnat
      simpa only [List.map_cons, List.prod_cons, ge_iff_le, add_div] using
        (div_le_div_of_nonneg_right hreal (by positivity : (0 : ℝ) ≤ Fintype.card (V n)))

private theorem action_list_prod_tendsto
    {G : Type*} [Group G]
    (A : SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp only [List.prod_nil, PermutationModel.map_one, List.map_nil, normalizedHamming_self,
        tendsto_const_nhds_iff]
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            normalizedHamming
                ((A.model n).action (g * l.prod))
                ((A.model n).action g * (A.model n).action l.prod) +
              normalizedHamming
                ((A.model n).action l.prod)
                ((l.map (A.model n).action).prod))
          atTop (nhds 0) := by
        simpa only [add_zero] using (A.multiplicative g l.prod).add ih
      refine squeeze_zero
        (fun n => normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      have htriangle := normalizedHamming_triangle
        ((A.model n).action (g * l.prod))
        ((A.model n).action g * (A.model n).action l.prod)
        ((A.model n).action g *
          (l.map (A.model n).action).prod)
      rw [normalizedHamming_mul_left] at htriangle
      exact htriangle

private theorem exists_word_of_symmetric_generators
    {H : Type*} [Group H]
    (S : Finset H)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set H) = ⊤)
    (g : H) :
    ∃ l : List ↥S,
      ((l.map fun i : ↥S => (i : H)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set H) := by
    rw [hgenerates]
    simp only [Subgroup.mem_top]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]⟩
  | one =>
      exact ⟨[], by simp only [List.map_nil, List.prod_nil]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : H)⁻¹, hsymmetric (i : H) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : H)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : H)⁻¹) =
            (l.map (fun i : ↥S => (i : H))).map
              (fun z : H => z⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]

public
theorem crossing_density_tendsto_zero_of_normalizedHamming
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (p q : ∀ n, Equiv.Perm (V n))
    (hq : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n) (q n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0))
    (hdist : Tendsto
      (fun n => normalizedHamming (p n) (q n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n) (p n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n) (q n)).card : ℝ) /
            Fintype.card (V n) +
          normalizedHamming (p n) (q n))
      atTop (nhds 0) := by
    simpa only [add_zero] using hq.add hdist
  refine squeeze_zero (fun n => by positivity) ?_ hupper
  intro n
  have hnat := SourceCompressionTransportCrossing.card_partitionWordCrossing_le_add_distance
    (Q n) (p n) (q n)
  have hreal :
      ((partitionWordCrossing (Q n) (p n)).card : ℝ) ≤
      ((partitionWordCrossing (Q n) (q n)).card : ℝ) +
        (permutationDistance (p n) (q n) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((partitionWordCrossing (Q n) (p n)).card : ℝ) /
        Fintype.card (V n) ≤
      (((partitionWordCrossing (Q n) (q n)).card : ℝ) +
        (permutationDistance (p n) (q n) : ℝ)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((partitionWordCrossing (Q n) (q n)).card : ℝ) /
          Fintype.card (V n) +
        normalizedHamming (p n) (q n) := by
      simp only [permutationDistance, add_div, normalizedHamming]

public
theorem fixed_generated_word_crossing_density_tendsto_zero
    {G H : Type*} [Group G] [Group H]
    (A : SoficApproximation G)
    (φ : H →* G) (S : Finset H)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set H) = ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S => (A.model n).action (φ (i : H))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0))
    (g : H) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action (φ g))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  classical
  obtain ⟨l, hl⟩ :=
    exists_word_of_symmetric_generators S hsymmetric hgenerates g
  have hgenerator (i : ↥S) : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action (φ (i : H)))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
    simpa only [Fintype.card_fin] using
      generator_crossing_density_tendsto_zero
        (V := fun n => Fin (A.model n).size)
        Q (fun n (j : ↥S) => (A.model n).action (φ (j : H)))
        (by simpa only [Fintype.card_fin] using hboundary) i
  have hlist : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((l.map fun i : ↥S =>
            (A.model n).action (φ (i : H))).prod)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
    simpa only [Fintype.card_fin] using
      list_generator_crossing_density_tendsto_zero
        (V := fun n => Fin (A.model n).size)
        Q (fun n (i : ↥S) => (A.model n).action (φ (i : H)))
        (fun i => by
          simpa only [Fintype.card_fin] using hgenerator i)
        l
  have hprod :
      ((l.map fun i : ↥S => φ (i : H)).prod) = φ g := by
    calc
      ((l.map fun i : ↥S => φ (i : H)).prod) =
          φ ((l.map fun i : ↥S => (i : H)).prod) := by
        simpa only [List.map_subtype, List.map_id_fun', id_eq] using
          (map_list_prod φ (l.map fun i : ↥S => (i : H))).symm
      _ = φ g := by rw [hl]
  have hdist : Tendsto
      (fun n => normalizedHamming
        ((A.model n).action (φ g))
        ((l.map fun i : ↥S =>
          (A.model n).action (φ (i : H))).prod))
      atTop (nhds 0) := by
    have h := action_list_prod_tendsto A
      (l.map fun i : ↥S => φ (i : H))
    rw [hprod] at h
    simpa only [List.map_subtype, List.map_map, Function.comp_def] using h
  simpa only [Fintype.card_fin] using
    crossing_density_tendsto_zero_of_normalizedHamming
      (V := fun n => Fin (A.model n).size)
      Q (fun n => (A.model n).action (φ g))
      (fun n =>
        (l.map fun i : ↥S => (A.model n).action (φ (i : H))).prod)
      (by simpa only [Fintype.card_fin] using hlist)
      hdist

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceAlphaInclusion :
    prefixElementaryGroup alphaPrefixCode →*
      prefixElementaryGroup ninePrefixCode where
  toFun g :=
    ⟨g.val,
      SourceGeneration.alphaPrefixElementaryGroup_le_nine
        g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

public
theorem source_alpha_word_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup alphaPrefixCode)) = ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action (sourceAlphaInclusion i)) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0))
    (g : prefixElementaryGroup alphaPrefixCode) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action (sourceAlphaInclusion g))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) :=
  fixed_generated_word_crossing_density_tendsto_zero
    A sourceAlphaInclusion S hsymmetric hgenerates Q hboundary g

end SourceGeneratedWordCrossing

namespace KunRootedUniversalToleranceNumerics

private theorem rooted_graph_boundary_lt_of_slow_tolerance
    {h d q t N b c e : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hq : q < 1)
    (ht : 0 < t)
    (hbad : 2 * d * b ≤ t)
    (hmissing : N - 2 * b ≤ c)
    (hboundary : e ≤ 3 * t)
    (hslow :
      5 * (4 + h *
        (216 / (d * (1 - q) ^ 2) + 1 / d)) * t ≤ h * N) :
    e < (d * (1 - q) ^ 2 / 288) * c := by
  let δ : ℝ := d * (1 - q) ^ 2
  let γ : ℝ := δ / 288
  let C : ℝ := 216 / δ + 1 / d
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hslowCscaled : h * (5 * C * t) ≤ h * N := by
    have hslow' : 5 * (4 + h * C) * t ≤ h * N := by
      simpa only [C, δ] using hslow
    linarith only [hslow', ht]
  have hslowC : 5 * C * t ≤ N :=
    le_of_mul_le_mul_left hslowCscaled hh
  have hb : 2 * b ≤ t / d := by
    apply (le_div_iff₀ hd).2
    linarith only [hbad]
  have hgraph : N - t / d ≤ c := by
    linarith
  have hgraphscaled : γ * (N - t / d) ≤ γ * c :=
    mul_le_mul_of_nonneg_left hgraph hγ.le
  have hNscaled : γ * (5 * C * t) ≤ γ * N :=
    mul_le_mul_of_nonneg_left hslowC hγ.le
  have hγC : γ * C = (3 / 4 : ℝ) + γ / d := by
    change
      (δ / 288) * (216 / δ + 1 / d) =
        (3 / 4 : ℝ) + (δ / 288) / d
    field_simp [ne_of_gt hδ, ne_of_gt hd]
    ring
  have hidentity :
      γ * (5 * C * t) - γ * (t / d) =
        (15 / 4 : ℝ) * t + 4 * (γ / d) * t := by
    calc
      γ * (5 * C * t) - γ * (t / d) =
          5 * (γ * C) * t - (γ / d) * t := by ring
      _ = 5 * ((3 / 4 : ℝ) + γ / d) * t -
          (γ / d) * t := by rw [hγC]
      _ = (15 / 4 : ℝ) * t + 4 * (γ / d) * t := by ring
  have hpositive : 0 ≤ 4 * (γ / d) * t := by
    positivity
  have hstrict : 3 * t < γ * c := by
    linarith only [hgraphscaled, hNscaled, hidentity, hpositive, ht]
  simpa only [γ, δ] using lt_of_le_of_lt hboundary hstrict

private theorem rooted_graph_coefficient_small
    {d q : ℝ} (hd : 0 < d) (hq : q < 1) :
    0 < d * (1 - q) ^ 2 / 288 ∧
      216 * (d * (1 - q) ^ 2 / 288) < d * (1 - q) ^ 2 := by
  have hgap : 0 < d * (1 - q) ^ 2 := by
    positivity
  constructor
  · positivity
  · nlinarith

end KunRootedUniversalToleranceNumerics

namespace SourceBothCompressionNormalization

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressionUElement :
    prefixElementaryGroup ninePrefixCode :=
  ⟨compressionU,
    compressionU_mem_ninePrefixElementaryGroup⟩

private def sourceCompressionVElement :
    prefixElementaryGroup ninePrefixCode :=
  ⟨compressionV,
    compressionV_mem_ninePrefixElementaryGroup⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceAlphaElement
    (g : prefixElementaryGroup alphaPrefixCode) :
    prefixElementaryGroup ninePrefixCode :=
  ⟨g.val,
    SourceGeneration.alphaPrefixElementaryGroup_le_nine
      g.property⟩

private def sourceConjugatedAlphaUElement
    (g : prefixElementaryGroup alphaPrefixCode) :
    prefixElementaryGroup alphaPrefixCode := by
  refine ⟨compressionU * g.val *
    compressionU⁻¹, ?_⟩
  apply alphaZero_prefixElementaryGroup_le
  rw [← compressionU_map_alphaPrefixElementaryGroup]
  refine ⟨g.val, g.property, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]

private def sourceConjugatedAlphaVElement
    (g : prefixElementaryGroup alphaPrefixCode) :
    prefixElementaryGroup alphaPrefixCode := by
  refine ⟨compressionV * g.val *
    compressionV⁻¹, ?_⟩
  apply alphaZero_prefixElementaryGroup_le
  rw [← compressionV_map_alphaPrefixElementaryGroup]
  refine ⟨g.val, g.property, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]

private theorem sourceCompressionUElement_conjugates_alpha
    (g : prefixElementaryGroup alphaPrefixCode) :
    sourceCompressionUElement * sourceAlphaElement g *
        sourceCompressionUElement⁻¹ =
      sourceAlphaElement (sourceConjugatedAlphaUElement g) := by
  apply Subtype.ext
  rfl

private theorem sourceCompressionVElement_conjugates_alpha
    (g : prefixElementaryGroup alphaPrefixCode) :
    sourceCompressionVElement * sourceAlphaElement g *
        sourceCompressionVElement⁻¹ =
      sourceAlphaElement (sourceConjugatedAlphaVElement g) := by
  apply Subtype.ext
  rfl

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressionTable :
    Fin 2 → prefixElementaryGroup ninePrefixCode :=
  ![sourceCompressionUElement, sourceCompressionVElement]

public
theorem sourceCompressionTable_conjugates_alpha
    (i : Fin 2)
    (g : prefixElementaryGroup alphaPrefixCode) :
    ∃ k : prefixElementaryGroup alphaPrefixCode,
      sourceCompressionTable i * sourceAlphaElement g *
          (sourceCompressionTable i)⁻¹ =
        sourceAlphaElement k := by
  fin_cases i
  · exact ⟨sourceConjugatedAlphaUElement g,
      sourceCompressionUElement_conjugates_alpha g⟩
  · exact ⟨sourceConjugatedAlphaVElement g,
      sourceCompressionVElement_conjugates_alpha g⟩

end SourceBothCompressionNormalization

namespace KunCompletedProductDiagonalSparseCut

open KunDiagonalGoodRootGraphLoss
open KunRootedIndicatorCrossing
open KunRootedWordPower
open KunThomInvariantOrthogonal
open scoped BigOperators symmDiff

universe u

private def completedDiagonalPermutationHom {V : Type*} :
    Equiv.Perm V →* Equiv.Perm (V × V) where
  toFun p := p.prodCongr p
  map_one' := by
    ext z <;> rfl
  map_mul' := by
    intro p q
    ext z <;> rfl

private def completedGoodPermutationGraphIndicator
    {V : Type*} [DecidableEq V]
    (T : Finset (V × V)) (z : V × V) : ℝ :=
  if z ∈ T then 1 else 0

private def completedGoodPermutationGraphRootedModel
    {G ι V : Type u} [Fintype V] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (φ : G → Equiv.Perm V)
    (p : Equiv.Perm V) (B : Finset V) :
    RootedIndicatorMarkovModel G ι where
  carrier := V × V
  fintype := inferInstance
  generator i := completedDiagonalPermutationHom (σ i)
  indicator := completedGoodPermutationGraphIndicator
    (goodPermutationGraph p B)
  evaluation g := completedDiagonalPermutationHom (φ g)

private theorem completedGoodPermutationGraphRootedModel_isGenerated
    {G ι V : Type u} [Group G] [Fintype ι]
    [Fintype V] [DecidableEq V]
    (s : ι → G) (w : G → List ι)
    (σ : ι → Equiv.Perm V) (φ : G → Equiv.Perm V)
    (hword : ∀ g : G, φ g = ((w g).map σ).prod)
    (hone : φ 1 = 1)
    (hgenerator : ∀ i : ι, φ (s i) = σ i)
    (p : Equiv.Perm V) (B : Finset V) :
    (completedGoodPermutationGraphRootedModel σ φ p B).IsGenerated s w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    change
      completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 0 ∨
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 1
    unfold completedGoodPermutationGraphIndicator
    by_cases hz : z ∈ goodPermutationGraph p B
    · exact Or.inr (ite_eq_left hz)
    · exact Or.inl (ite_eq_right hz)
  · intro g
    change
      completedDiagonalPermutationHom (φ g) =
        ((w g).map
          fun i : ι => completedDiagonalPermutationHom (σ i)).prod
    rw [hword g, map_list_prod, List.map_map]
    rfl
  · change
      completedDiagonalPermutationHom (φ 1) =
        (1 : Equiv.Perm (V × V))
    rw [hone, map_one]
  · intro i
    change
      completedDiagonalPermutationHom (φ (s i)) =
        completedDiagonalPermutationHom (σ i)
    rw [hgenerator i]

private theorem completedGoodPermutationGraphRootedModel_isRootedAtRadius
    {G ι V : Type u} [Group G]
    [Fintype V] [DecidableEq V]
    (w : G → List ι) (σ : ι → Equiv.Perm V)
    (φ : G → Equiv.Perm V)
    (p : Equiv.Perm V) (B : Finset V) (r : ℕ)
    (hroot : ∀ a g : G,
      (w a).length + (w g).length + (w (a * g)).length ≤ r →
        ∀ x : V, x ∉ B →
          φ (a * g) x = (φ a * φ g) x) :
    (completedGoodPermutationGraphRootedModel
      σ φ p B).IsRootedAtRadius w r := by
  refine ⟨?_⟩
  intro a g hword z hz
  have hzreal :
      completedGoodPermutationGraphIndicator
        (goodPermutationGraph p B) z ≠ 0 := by
    intro hzero
    apply hz
    change
      (completedGoodPermutationGraphIndicator
        (goodPermutationGraph p B) z : ℂ) = 0
    exact_mod_cast hzero
  have hzgraph : z ∈ goodPermutationGraph p B := by
    by_contra hnot
    apply hzreal
    exact ite_eq_right hnot
  have hgood : z.1 ∉ B ∧ z.2 ∉ B :=
    (Finset.mem_filter.mp hzgraph).2
  apply Prod.ext
  · exact hroot a g hword z.1 hgood.1
  · exact hroot a g hword z.2 hgood.2

private theorem exists_completed_goodPermutationGraph_sparse_cut
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      ∀ (p : Equiv.Perm V) (B : Finset V),
      (∀ a g : G,
        (w a).length + (w g).length + (w (a * g)).length ≤ r →
          ∀ x : V, x ∉ B →
            φ (a * g) x = (φ a * φ g) x) →
      let T := goodPermutationGraph p B
      T.Nonempty →
      (boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (V × V),
        (((U ∆ T).card : ℝ)) ≤
          72 * (boundary
            (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
        3 * (U ∆ T).card < T.card ∧
        (boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) U : ℝ) ≤
            α * (U.card : ℝ) := by
  classical
  obtain ⟨k, r, hr⟩ :=
    exists_rooted_word_radius_sparse_cut_of_boundary
      P S honeS hcover hsymmetric w γ α hγ hα hγsmall
  refine ⟨r, ?_⟩
  intro V _ _ σ φ hword hone hgenerator p B hroot
  have hproductInstance :
      (instDecidableEqProd : DecidableEq (V × V)) =
        Classical.decEq (V × V) :=
    Subsingleton.elim _ _
  let : DecidableEq (V × V) := Classical.decEq (V × V)
  dsimp only
  intro hT hboundary
  rw [hproductInstance] at hboundary ⊢
  let X : RootedIndicatorMarkovModel G ↥S :=
    completedGoodPermutationGraphRootedModel σ φ p B
  let T : Finset X.carrier := goodPermutationGraph p B
  have hgenerated : X.IsGenerated (fun i : ↥S => (i : G)) w :=
    completedGoodPermutationGraphRootedModel_isGenerated
      (fun i : ↥S => (i : G)) w σ φ
        hword hone hgenerator p B
  have hrooted : X.IsRootedAtRadius w r :=
    completedGoodPermutationGraphRootedModel_isRootedAtRadius
      w σ φ p B r hroot
  have hindicator : ∀ z : X.carrier,
      X.indicator z = if z ∈ T then (1 : ℝ) else 0 := by
    intro z
    by_cases hz : z ∈ goodPermutationGraph p B
    · have hzT : z ∈ T := hz
      rw [ite_eq_left hzT]
      change
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 1
      exact ite_eq_left hz
    · have hzT : z ∉ T := hz
      rw [ite_eq_right hzT]
      change
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 0
      exact ite_eq_right hz
  have hT' : T.Nonempty := hT
  have hboundary' :
      (boundary X.generator T : ℝ) <
        γ * (T.card : ℝ) := by
    change
      (boundary
        (fun i : ↥S => (σ i).prodCongr (σ i))
        (goodPermutationGraph p B) : ℝ) <
          γ * ((goodPermutationGraph p B).card : ℝ)
    exact hboundary
  obtain ⟨U, _hmarkov, hdistance, hclose, hcut⟩ :=
    hr X hgenerated hrooted T hT' hindicator hboundary'
  refine ⟨U, ?_, ?_, ?_⟩
  · exact hdistance
  · exact hclose
  · exact hcut

end KunCompletedProductDiagonalSparseCut

namespace KunTransportedAmbientOverlap

open Filter Topology
open scoped BigOperators symmDiff

private theorem intersection_generator_exit_subset_union
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (C D : Finset V) :
    ((C ∩ D).filter fun x => p x ∉ C ∩ D) ⊆
      ((C.filter fun x => p x ∉ C) ∩ D) ∪
        ((D.filter fun x => p x ∉ D) ∩ C) := by
  intro x hx
  obtain ⟨hxCD, hout⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hxCD
  by_cases hpC : p x ∈ C
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hxD, ?_⟩, hxC⟩
    intro hpD
    exact hout (Finset.mem_inter.mpr ⟨hpC, hpD⟩)
  · apply Finset.mem_union_left
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨hxC, hpC⟩, hxD⟩

private theorem sum_intersection_generator_exit_card_le
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P Q : Finpartition U)
    (p : Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card) ≤
      (∑ C ∈ P.parts,
        (C.filter fun x => p x ∉ C).card) +
      (∑ D ∈ Q.parts,
        (D.filter fun x => p x ∉ D).card) := by
  classical
  have hcell (C D : Finset V) :
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card ≤
        (((C.filter fun x => p x ∉ C) ∩ D).card) +
          (((D.filter fun x => p x ∉ D) ∩ C).card) :=
    (Finset.card_le_card
      (intersection_generator_exit_subset_union p C D)).trans
        (Finset.card_union_le _ _)
  have hfirst (C : Finset V) (hC : C ∈ P.parts) :
      (∑ D ∈ Q.parts,
        ((C.filter fun x => p x ∉ C) ∩ D).card) =
        (C.filter fun x => p x ∉ C).card := by
    have h := sum_card_inter_partition Q
      (C.filter fun x => p x ∉ C)
    have hsub :
        (C.filter fun x => p x ∉ C) ⊆ U :=
      (Finset.filter_subset _ _).trans (P.subset hC)
    simpa only [Finset.inter_comm, Finset.inter_eq_right.mpr hsub] using h
  have hsecond (D : Finset V) (hD : D ∈ Q.parts) :
      (∑ C ∈ P.parts,
        ((D.filter fun x => p x ∉ D) ∩ C).card) =
        (D.filter fun x => p x ∉ D).card := by
    have h := sum_card_inter_partition P
      (D.filter fun x => p x ∉ D)
    have hsub :
        (D.filter fun x => p x ∉ D) ⊆ U :=
      (Finset.filter_subset _ _).trans (Q.subset hD)
    simpa only [Finset.inter_comm, Finset.inter_eq_right.mpr hsub] using h
  calc
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card) ≤
        ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          ((((C.filter fun x => p x ∉ C) ∩ D).card) +
            (((D.filter fun x => p x ∉ D) ∩ C).card)) := by
      apply Finset.sum_le_sum
      intro C _
      apply Finset.sum_le_sum
      intro D _
      exact hcell C D
    _ = (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          ((C.filter fun x => p x ∉ C) ∩ D).card) +
        (∑ D ∈ Q.parts, ∑ C ∈ P.parts,
          ((D.filter fun x => p x ∉ D) ∩ C).card) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ C ∈ P.parts,
          (C.filter fun x => p x ∉ C).card) +
        (∑ D ∈ Q.parts,
          (D.filter fun x => p x ∉ D).card) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro C hC
        exact hfirst C hC
      · apply Finset.sum_congr rfl
        intro D hD
        exact hsecond D hD

private theorem sum_intersection_boundary_le_partition_boundaries
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {U : Finset V} (P Q : Finpartition U)
    (σ : ι → Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      boundary σ (C ∩ D)) ≤
      (∑ C ∈ P.parts, boundary σ C) +
        (∑ D ∈ Q.parts, boundary σ D) := by
  classical
  calc
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      boundary σ (C ∩ D)) =
      ∑ i : ι, ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
        ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
      simp_rw [boundary]
      calc
        (∑ C ∈ P.parts, ∑ D ∈ Q.parts, ∑ i : ι,
          ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card) =
            ∑ C ∈ P.parts, ∑ i : ι, ∑ D ∈ Q.parts,
              ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
          apply Finset.sum_congr rfl
          intro C _
          rw [Finset.sum_comm]
        _ = ∑ i : ι, ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
              ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
          rw [Finset.sum_comm]
    _ ≤ ∑ i : ι,
      ((∑ C ∈ P.parts, (C.filter fun x => σ i x ∉ C).card) +
        (∑ D ∈ Q.parts, (D.filter fun x => σ i x ∉ D).card)) := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_intersection_generator_exit_card_le P Q (σ i)
    _ = (∑ C ∈ P.parts, boundary σ C) +
        (∑ D ∈ Q.parts, boundary σ D) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [boundary]
        rw [Finset.sum_comm]
      · simp_rw [boundary]
        rw [Finset.sum_comm]

private theorem dominant_component_loss_le_ambient_intersection_boundaries
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {U : Finset V} (P Q : Finpartition U)
    (σ : ι → Equiv.Perm V) (gamma : ℝ)
    (hexp : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (boundary σ E : ℝ))
    (C : Finset V) (hC : C ∈ P.parts) :
    gamma *
        ((C.card : ℝ) -
          ((C ∩ maximumOverlapPart Q C).card : ℝ)) ≤
      ∑ E ∈ Q.parts,
        (boundary σ (C ∩ E) : ℝ) := by
  classical
  let D : Finset V := maximumOverlapPart Q C
  have hCU : C ⊆ U := P.subset hC
  have hD : D ∈ Q.parts :=
    maximumOverlapPart_mem Q C
      (P.nonempty_of_mem_parts hC) hCU
  have hmax : ∀ E ∈ Q.parts, (C ∩ E).card ≤ (C ∩ D).card :=
    maximumOverlapPart_maximal Q C
      (P.nonempty_of_mem_parts hC) hCU
  have hsmall (E : Finset V) (hE : E ∈ Q.parts.erase D) :
      gamma * ((C ∩ E).card : ℝ) ≤
        (boundary σ (C ∩ E) : ℝ) := by
    obtain ⟨hne, hEmem⟩ := Finset.mem_erase.mp hE
    have hdisj : Disjoint (C ∩ E) (C ∩ D) :=
      (Q.disjoint hEmem hD hne).mono
        Finset.inter_subset_right Finset.inter_subset_right
    have hunion : (C ∩ E) ∪ (C ∩ D) ⊆ C :=
      Finset.union_subset Finset.inter_subset_left
        Finset.inter_subset_left
    have hcard :
        (C ∩ E).card + (C ∩ D).card ≤ C.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hunion
    have hhalf : 2 * (C ∩ E).card ≤ C.card := by
      have hmaximum := hmax E hEmem
      omega
    exact hexp C hC (C ∩ E) Finset.inter_subset_left hhalf
  have hsum :
      (∑ E ∈ Q.parts, ((C ∩ E).card : ℝ)) =
        (C.card : ℝ) := by
    exact_mod_cast
      sum_card_component_inter_partition Q C hCU
  have herase :
      (∑ E ∈ Q.parts.erase D, ((C ∩ E).card : ℝ)) =
        (C.card : ℝ) - ((C ∩ D).card : ℝ) := by
    have hsplit := Finset.add_sum_erase Q.parts
      (fun E : Finset V => ((C ∩ E).card : ℝ)) hD
    linarith
  change gamma * ((C.card : ℝ) - ((C ∩ D).card : ℝ)) ≤ _
  calc
    gamma * ((C.card : ℝ) - ((C ∩ D).card : ℝ)) =
        ∑ E ∈ Q.parts.erase D,
          gamma * ((C ∩ E).card : ℝ) := by
      rw [← Finset.mul_sum, herase]
    _ ≤ ∑ E ∈ Q.parts.erase D,
          (boundary σ (C ∩ E) : ℝ) :=
      Finset.sum_le_sum hsmall
    _ ≤ ∑ E ∈ Q.parts,
          (boundary σ (C ∩ E) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _)
      intro E _ _
      exact Nat.cast_nonneg _

private theorem sum_dominant_component_losses_le_partition_boundaries
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {U : Finset V} (P Q : Finpartition U)
    (σ : ι → Equiv.Perm V) (gamma : ℝ)
    (hexp : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (boundary σ E : ℝ)) :
    gamma *
        (∑ C ∈ P.parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart Q C).card : ℝ))) ≤
      (∑ C ∈ P.parts, (boundary σ C : ℝ)) +
        (∑ D ∈ Q.parts, (boundary σ D : ℝ)) := by
  classical
  calc
    gamma *
        (∑ C ∈ P.parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart Q C).card : ℝ))) =
      ∑ C ∈ P.parts,
        gamma * ((C.card : ℝ) -
          ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          (boundary σ (C ∩ D) : ℝ) := by
        apply Finset.sum_le_sum
        intro C hC
        exact dominant_component_loss_le_ambient_intersection_boundaries
          P Q σ gamma hexp C hC
    _ ≤ (∑ C ∈ P.parts, (boundary σ C : ℝ)) +
        (∑ D ∈ Q.parts, (boundary σ D : ℝ)) := by
      exact_mod_cast
        sum_intersection_boundary_le_partition_boundaries P Q σ

public
theorem dominant_component_loss_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (P Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (P n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (boundary (σ n) D : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n => (1 / gamma) *
        ((∑ C ∈ (P n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (V n) +
          (∑ D ∈ (Q n).parts,
            (boundary (σ n) D : ℝ)) /
              Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / gamma : ℝ))
          atTop (nhds (1 / gamma))).mul (hsource.add htarget))
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hupper
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro C _
      apply sub_nonneg.mpr
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_left :
          C ∩ maximumOverlapPart (Q n) C ⊆ C)
    · exact Nat.cast_nonneg _
  · have hcard : (0 : ℝ) < Fintype.card (V n) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hbound :=
      sum_dominant_component_losses_le_partition_boundaries
        (P n) (Q n) (σ n) gamma (hexp n)
    have hdivide :
        (∑ C ∈ (P n).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) ≤
          ((∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) +
            (∑ D ∈ (Q n).parts,
              (boundary (σ n) D : ℝ))) / gamma := by
      apply (le_div_iff₀ hgamma).2
      simpa only [Finset.sum_sub_distrib, mul_comm] using hbound
    calc
      (∑ C ∈ (P n).parts,
        ((C.card : ℝ) -
          ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
            Fintype.card (V n) ≤
        (((∑ C ∈ (P n).parts,
          (boundary (σ n) C : ℝ)) +
          (∑ D ∈ (Q n).parts,
            (boundary (σ n) D : ℝ))) / gamma) /
              Fintype.card (V n) :=
        div_le_div_of_nonneg_right hdivide hcard.le
      _ = (1 / gamma) *
          ((∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) /
              Fintype.card (V n) +
            (∑ D ∈ (Q n).parts,
              (boundary (σ n) D : ℝ)) /
                Fintype.card (V n)) := by
        ring

private theorem boundary_conjugate_map
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (C : Finset V) :
    boundary
      (fun i => T * σ i * T⁻¹)
      (C.map T.toEmbedding) =
        boundary σ C := by
  classical
  unfold boundary
  apply Finset.sum_congr rfl
  intro i _
  have hfilter :
      ((C.map T.toEmbedding).filter fun y =>
        (T * σ i * T⁻¹) y ∉ C.map T.toEmbedding) =
      (C.filter fun x => σ i x ∉ C).map T.toEmbedding := by
    ext y
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Finset.mem_map_mk, Finset.mem_filter,
      Finset.mem_map_equiv]
  rw [hfilter, Finset.card_map]

public
theorem transportedUnivFinpartition_half_expansion
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (gamma : ℝ)
    (hexp : ∀ C ∈ Q.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (boundary σ E : ℝ)) :
    ∀ C ∈ (transportedUnivFinpartition Q T).parts,
      ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary
              (fun i => T * σ i * T⁻¹) E : ℝ) := by
  classical
  intro C hC
  rw [transportedUnivFinpartition_parts] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  intro E hE hhalf
  let E₀ : Finset V := E.map T.symm.toEmbedding
  have hrecovery : E₀.map T.toEmbedding = E := by
    simp only [Finset.map_map, Function.Embedding.mk_trans_mk, Equiv.self_comp_symm,
      Function.Embedding.mk_id,
      Finset.map_refl, E₀]
  have hsub : E₀ ⊆ C₀ := by
    apply (Finset.map_subset_map (f := T.toEmbedding)).mp
    simpa only [hrecovery] using hE
  have hhalf₀ : 2 * E₀.card ≤ C₀.card := by
    simpa [E₀] using hhalf
  have hsource := hexp C₀ hC₀ E₀ hsub hhalf₀
  have hboundary :=
    boundary_conjugate_map σ T E₀
  calc
    gamma * (E.card : ℝ) = gamma * (E₀.card : ℝ) := by
      simp only [Finset.card_map, E₀]
    _ ≤ (boundary σ E₀ : ℝ) := hsource
    _ = (boundary
      (fun i => T * σ i * T⁻¹)
        (E₀.map T.toEmbedding) : ℝ) := by
      exact_mod_cast hboundary.symm
    _ = (boundary
      (fun i => T * σ i * T⁻¹) E : ℝ) := by
      rw [hrecovery]

private theorem sum_boundary_transportedUnivFinpartition
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V) :
    (∑ C ∈ (transportedUnivFinpartition Q T).parts,
      boundary
        (fun i => T * σ i * T⁻¹) C) =
      ∑ C ∈ Q.parts, boundary σ C := by
  classical
  rw [transportedUnivFinpartition_parts]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro C _
    exact boundary_conjugate_map σ T C
  · intro C hC D hD heq
    exact T.finsetCongr.injective heq

public
theorem transported_partition_boundary_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition (Q n) (T n)).parts,
            (boundary
              (fun i => T n * σ n i * (T n)⁻¹) C : ℝ)) /
                Fintype.card (V n))
      atTop (nhds 0) := by
  have hsum (n : ℕ) :
      (∑ C ∈
        (transportedUnivFinpartition (Q n) (T n)).parts,
          (boundary
            (fun i => T n * σ n i * (T n)⁻¹) C : ℝ)) =
        ∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ) := by
    exact_mod_cast
      sum_boundary_transportedUnivFinpartition (Q n) (σ n) (T n)
  simpa only [hsum] using hboundary

public
theorem exists_common_slow_overlap_scales_for_transported_partitions
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : ∀ j : κ, Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (boundary
            (fun i => T n j * σ n i * (T n j)⁻¹) D : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
        Antitone eta ∧
        Tendsto eta atTop (nhds 0) ∧
        (∀ n, 0 < H n) ∧
        Antitone H ∧
        Tendsto H atTop (nhds 0) ∧
        Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
        ∀ j : κ, Tendsto
          (fun n =>
            (∑ C ∈ insufficientOverlapComponents
              (transportedUnivFinpartition
                (Q n) (T n j))
              (Q n) (eta n), (C.card : ℝ)) /
                Fintype.card (V n))
          atTop (nhds 0) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let L : κ → ℕ → ℝ := fun j n =>
    (∑ C ∈
      (transportedUnivFinpartition
        (Q n) (T n j)).parts,
      ((C.card : ℝ) -
        ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
          Fintype.card (V n)
  have hLnonneg (j : κ) (n : ℕ) : 0 ≤ L j n := by
    dsimp [L]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro C _
      apply sub_nonneg.mpr
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_left :
          C ∩ maximumOverlapPart (Q n) C ⊆ C)
    · exact Nat.cast_nonneg _
  have hLlimit (j : κ) :
      Tendsto (L j) atTop (nhds 0) := by
    apply dominant_component_loss_density_tendsto_zero
      (fun n =>
        transportedUnivFinpartition (Q n) (T n j))
      Q
      (fun n i => T n j * σ n i * (T n j)⁻¹)
      gamma hgamma
    · intro n
      exact transportedUnivFinpartition_half_expansion
        (Q n) (σ n) (T n j) gamma (hexp n)
    · exact transported_partition_boundary_density_tendsto_zero
        Q σ (fun n => T n j) hsource
    · exact htarget j
  let e : ℕ → ℝ := fun n => ∑ j : κ, L j n
  have henonneg (n : ℕ) : 0 ≤ e n := by
    exact Finset.sum_nonneg fun j _ => hLnonneg j n
  have helimit : Tendsto e atTop (nhds 0) := by
    dsimp [e]
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hLlimit j)
  obtain ⟨eta, H, heta, hetaanti, hetalimit,
    hH, hHanti, hHlimit, hslow, hratio⟩ :=
    exists_positive_antitone_slow_overlap_scales
      e henonneg helimit
  refine ⟨eta, H, heta, hetaanti, hetalimit,
    hH, hHanti, hHlimit, hratio, ?_⟩
  intro j
  refine squeeze_zero (fun n =>
    div_nonneg (Finset.sum_nonneg fun C _ => Nat.cast_nonneg C.card)
      (Nat.cast_nonneg _)) ?_ hslow
  intro n
  let P : Finpartition (Finset.univ : Finset (V n)) :=
    transportedUnivFinpartition (Q n) (T n j)
  have hmass :=
    insufficientOverlapComponents_mass_le_loss
      P (Q n) (eta n)
  have hdivide :
      (∑ C ∈ insufficientOverlapComponents
        P (Q n) (eta n), (C.card : ℝ)) ≤
          (∑ C ∈ P.parts,
            ((C.card : ℝ) -
              ((C ∩ maximumOverlapPart (Q n) C).card :
                ℝ))) / eta n := by
    apply (le_div_iff₀ (heta n)).2
    simpa only [mul_comm, Finset.sum_sub_distrib] using hmass
  have hcard : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsingle : L j n ≤ e n := by
    exact Finset.single_le_sum
      (fun k _ => hLnonneg k n)
      (Finset.mem_univ j)
  change
    (∑ C ∈ insufficientOverlapComponents
      P (Q n) (eta n), (C.card : ℝ)) /
        Fintype.card (V n) ≤ e n / eta n
  calc
    (∑ C ∈ insufficientOverlapComponents
      P (Q n) (eta n), (C.card : ℝ)) /
        Fintype.card (V n) ≤
      ((∑ C ∈ P.parts,
        ((C.card : ℝ) -
          ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
            eta n) / Fintype.card (V n) :=
      div_le_div_of_nonneg_right hdivide hcard.le
    _ = L j n / eta n := by
      dsimp [L, P]
      ring
    _ ≤ e n / eta n :=
      div_le_div_of_nonneg_right hsingle (heta n).le

end KunTransportedAmbientOverlap

namespace KunUniformCompletedRootRadiusImprovement

open KunDiagonalGoodRootGraphLoss
open KunThomInvariantOrthogonal
open scoped BigOperators symmDiff

universe u

public
theorem exists_uniform_radius_hasAlmostCentralizerImprovement
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (h α : ℝ) (hpositive : 0 < h) (hα : 0 < α) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [Nonempty V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V)
        (tolerance : ℕ) (B : Finset V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      (∀ A : Finset V,
        h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
            (boundary σ A : ℝ)) →
      (5 * (4 + h *
        (216 / ((S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) +
            1 / (S.card : ℝ))) * (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ)) →
      (tolerance = 0 ∨
        (0 < (tolerance : ℝ) ∧
          α ≤ h * (tolerance : ℝ) /
            (2 * (h + 8 * (S.card : ℝ)) *
              (Fintype.card V : ℝ)) ∧
          2 * (S.card : ℝ) * (B.card : ℝ) ≤
            (tolerance : ℝ) ∧
          ∀ a g : G,
            (w a).length + (w g).length +
                (w (a * g)).length ≤ r →
              ∀ x : V, x ∉ B →
                φ (a * g) x = (φ a * φ g) x)) →
      HasAlmostCentralizerImprovement σ tolerance := by
  classical
  let : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let d : ℝ := S.card
  let q : ℝ := kazhdanMarkovContractionFactor P S
  let γ : ℝ := d * (1 - q) ^ 2 / 288
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  have hq : q < 1 := by
    exact kazhdanMarkovContractionFactor_lt_one
      P S ⟨1, honeS⟩
  have hγpair :=
    KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
      hd hq
  have hγ : 0 < γ := by
    simpa only [γ] using hγpair.1
  have hγsmall :
      216 * γ < (S.card : ℝ) * (1 - q) ^ 2 := by
    simpa only [γ, d] using hγpair.2
  obtain ⟨r, hspectral⟩ :=
    KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
      P S honeS hcover hsymmetric w γ α hγ hα
        (by simpa only [q] using hγsmall)
  refine ⟨r, ?_⟩
  intro V _ _ _ σ φ tolerance B hword hone hgenerator
    hexp hslow hcase
  rcases hcase with htzero | ⟨ht, htarget, hbadS, hlocal⟩
  · subst tolerance
    exact KunCompletedPrunedComponent.hasAlmostCentralizerImprovement_zero σ
  have hbad :
      2 * (Fintype.card (↥S) : ℝ) * (B.card : ℝ) ≤
        (tolerance : ℝ) := by
    simpa only [Fintype.card_coe] using hbadS
  have hslowq :
      5 * (4 + h *
        (216 / ((Fintype.card (↥S) : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card (↥S) : ℝ))) *
            (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ) := by
    simpa only [Fintype.card_coe, q] using hslow
  apply
    hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
      σ tolerance h q hpositive hq B
      (fun p => goodPermutationGraph p B) hexp
      hbad
      (fun p => goodPermutationGraph_subset p B)
      (fun p => card_permutationGraph_sdiff_goodPermutationGraph_le p B)
      (fun p =>
        boundary_goodPermutationGraph_le_commutationDefect_add σ p B)
      hslowq
  intro p hp
  let T : Finset (V × V) := goodPermutationGraph p B
  have hcard :
      (Fintype.card V : ℝ) - 2 * (B.card : ℝ) ≤
        (T.card : ℝ) := by
    exact card_goodPermutationGraph_ge_card_sub_twice_bad p B
  have hboundary :
      (boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) ≤
          3 * (tolerance : ℝ) := by
    have hbound :=
      boundary_goodPermutationGraph_le_commutationDefect_add σ p B
    have hbound_real :
        (boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) ≤
          (permutationCommutationDefect σ p : ℝ) +
            2 * (Fintype.card (↥S) : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hbound
    have hp_real :
        (permutationCommutationDefect σ p : ℝ) ≤
          2 * (tolerance : ℝ) := by
      exact_mod_cast hp
    linarith
  have hsparse :
      (boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) <
          γ * (T.card : ℝ) := by
    have hslowS :
        5 * (4 + h *
          (216 / (d * (1 - q) ^ 2) + 1 / d)) *
            (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ) := by
      simpa only [d, q] using hslow
    have hbad' :
        2 * d * (B.card : ℝ) ≤ (tolerance : ℝ) := by
      simpa only [d] using hbadS
    have hs :=
      KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
        hpositive hd hq ht hbad' hcard hboundary hslowS
    simpa only [γ] using hs
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    have hnonnegative :
        0 ≤ (boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) := by
      positivity
    have hpositiveT : 0 < (T.card : ℝ) :=
      (mul_pos_iff_of_pos_left hγ).mp
        (lt_of_le_of_lt hnonnegative hsparse)
    exact_mod_cast hpositiveT
  obtain ⟨U, hreference, _hclose, hcut⟩ :=
    hspectral V σ φ hword hone hgenerator p B hlocal hT hsparse
  refine ⟨U, ?_, ?_⟩
  · simpa only [T, q, Fintype.card_coe] using hreference
  · calc
      (boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) U : ℝ) ≤
          α * (U.card : ℝ) := hcut
      _ ≤ (h * (tolerance : ℝ) /
          (2 * (h + 8 * (Fintype.card (↥S) : ℝ)) *
            (Fintype.card V : ℝ))) * (U.card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [Fintype.card_coe] using htarget

end KunUniformCompletedRootRadiusImprovement

namespace CompletedChosenWordLocalRoot

open Filter Topology
open scoped BigOperators


private theorem list_permutation_hamming_tendsto
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*}
    (σ τ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => normalizedHamming (σ n i) (τ n i))
        atTop (nhds 0))
    (l : List ι) :
    Tendsto
      (fun n => normalizedHamming
        ((l.map (σ n)).prod) ((l.map (τ n)).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, normalizedHamming_self, tendsto_const_nhds_iff]
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            normalizedHamming (σ n i) (τ n i) +
              normalizedHamming
                ((l.map (σ n)).prod) ((l.map (τ n)).prod))
          atTop (nhds 0) := by
        simpa only [add_zero] using (hletter i).add ih
      refine squeeze_zero
        (fun n => normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      exact KunActualSoficRootRadius.normalizedHamming_mul_le
        (σ n i) (τ n i)
        ((l.map (σ n)).prod) ((l.map (τ n)).prod)

private theorem approximate_action_list_prod_tendsto
    {G : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (l : List G) :
    Tendsto
      (fun n => normalizedHamming
        (p n l.prod) ((l.map (p n)).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp only [List.prod_nil, hone, List.map_nil, normalizedHamming_self, tendsto_const_nhds_iff]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            normalizedHamming
                (p n (a * l.prod)) (p n a * p n l.prod) +
              normalizedHamming
                (p n l.prod) ((l.map (p n)).prod))
          atTop (nhds 0) := by
        simpa only [add_zero] using (hmul a l.prod).add ih
      refine squeeze_zero
        (fun n => normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      have h := normalizedHamming_triangle
        (p n (a * l.prod))
        (p n a * p n l.prod)
        (p n a * (l.map (p n)).prod)
      rw [normalizedHamming_mul_left] at h
      exact h

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def chosenWordEvaluation
    {G ι V : Type*}
    (σ : ι → Equiv.Perm V) (w : G → List ι) (g : G) :
    Equiv.Perm V :=
  ((w g).map σ).prod

private theorem chosenWordEvaluation_tendsto_action
    {G ι : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g : G, ((w g).map s).prod = g)
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => normalizedHamming
          (σ n i) (p n (s i)))
        atTop (nhds 0))
    (g : G) :
    Tendsto
      (fun n => normalizedHamming
        (chosenWordEvaluation (σ n) w g) (p n g))
      atTop (nhds 0) := by
  have hσ : Tendsto
      (fun n => normalizedHamming
        (chosenWordEvaluation (σ n) w g)
        (((w g).map fun i => p n (s i)).prod))
      atTop (nhds 0) := by
    exact list_permutation_hamming_tendsto V
      σ (fun n i => p n (s i)) hletter (w g)
  have hp : Tendsto
      (fun n => normalizedHamming
        (p n g) (((w g).map fun i => p n (s i)).prod))
      atTop (nhds 0) := by
    have h := approximate_action_list_prod_tendsto
      V p hone hmul ((w g).map s)
    simpa only [hw g, List.map_map, Function.comp_def] using h
  have hp' : Tendsto
      (fun n => normalizedHamming
        (((w g).map fun i => p n (s i)).prod) (p n g))
      atTop (nhds 0) := by
    have heq :
        (fun n => normalizedHamming
          (((w g).map fun i => p n (s i)).prod) (p n g)) =
        (fun n => normalizedHamming
          (p n g) (((w g).map fun i => p n (s i)).prod)) := by
      funext n
      exact normalizedHamming_comm _ _
    rw [heq]
    exact hp
  have hupper : Tendsto
      (fun n =>
        normalizedHamming
          (chosenWordEvaluation (σ n) w g)
          (((w g).map fun i => p n (s i)).prod) +
        normalizedHamming
          (((w g).map fun i => p n (s i)).prod) (p n g))
      atTop (nhds 0) := by
    simpa only [add_zero] using hσ.add hp'
  exact squeeze_zero
    (fun n => normalizedHamming_nonneg _ _)
    (fun n => normalizedHamming_triangle _ _ _)
    hupper

public
theorem chosenWordEvaluation_multiplicative_tendsto
    {G ι : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g : G, ((w g).map s).prod = g)
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => normalizedHamming
          (σ n i) (p n (s i)))
        atTop (nhds 0))
    (a g : G) :
    Tendsto
      (fun n => normalizedHamming
        (chosenWordEvaluation (σ n) w (a * g))
        (chosenWordEvaluation (σ n) w a *
          chosenWordEvaluation (σ n) w g))
      atTop (nhds 0) := by
  let φ : ∀ n, G → Equiv.Perm (V n) :=
    fun n k => chosenWordEvaluation (σ n) w k
  have hφ (k : G) : Tendsto
      (fun n => normalizedHamming (φ n k) (p n k))
      atTop (nhds 0) :=
    chosenWordEvaluation_tendsto_action
      V p hone hmul s w hw σ hletter k
  have hpa : Tendsto
      (fun n => normalizedHamming (p n a) (φ n a))
      atTop (nhds 0) := by
    have heq :
        (fun n => normalizedHamming (p n a) (φ n a)) =
        (fun n => normalizedHamming (φ n a) (p n a)) := by
      funext n
      exact normalizedHamming_comm _ _
    rw [heq]
    exact hφ a
  have hpg : Tendsto
      (fun n => normalizedHamming (p n g) (φ n g))
      atTop (nhds 0) := by
    have heq :
        (fun n => normalizedHamming (p n g) (φ n g)) =
        (fun n => normalizedHamming (φ n g) (p n g)) := by
      funext n
      exact normalizedHamming_comm _ _
    rw [heq]
    exact hφ g
  have hupper : Tendsto
      (fun n =>
        normalizedHamming
          (φ n (a * g)) (p n (a * g)) +
        (normalizedHamming
          (p n (a * g)) (p n a * p n g) +
        (normalizedHamming (p n a) (φ n a) +
          normalizedHamming (p n g) (φ n g))))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hφ (a * g)).add ((hmul a g).add (hpa.add hpg))
  change Tendsto
    (fun n => normalizedHamming
      (φ n (a * g)) (φ n a * φ n g)) atTop (nhds 0)
  refine squeeze_zero
    (fun n => normalizedHamming_nonneg _ _) ?_ hupper
  intro n
  calc
    normalizedHamming
        (φ n (a * g)) (φ n a * φ n g) ≤
      normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      normalizedHamming
        (p n (a * g)) (φ n a * φ n g) :=
      normalizedHamming_triangle _ _ _
    _ ≤ normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      (normalizedHamming
        (p n (a * g)) (p n a * p n g) +
        normalizedHamming
          (p n a * p n g) (φ n a * φ n g)) := by
      gcongr
      exact normalizedHamming_triangle _ _ _
    _ ≤ normalizedHamming
        (φ n (a * g)) (p n (a * g)) +
      (normalizedHamming
        (p n (a * g)) (p n a * p n g) +
        (normalizedHamming (p n a) (φ n a) +
          normalizedHamming (p n g) (φ n g))) := by
      gcongr
      exact KunActualSoficRootRadius.normalizedHamming_mul_le
        (p n a) (φ n a) (p n g) (φ n g)

end CompletedChosenWordLocalRoot

namespace CompletedSourceChosenWordRestrictionTransfer

open Filter Topology
open MatchedComponentCompletion
open MatchedComponentExitBudget
open MatchedFirstStageWordRadiusTransfer
open scoped BigOperators

private theorem completedGenerator_permutationDistance_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (Z : Finset V)
    (τ : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      σ (x : V) ∈ Z →
        ((τ x : {x : V // x ∈ Z}) : V) = σ (x : V)) :
    permutationDistance
      τ (completedRestriction σ Z) ≤
        (Finset.univ \ Z).card := by
  let E : Finset V := Z.filter fun x => σ x ∉ Z
  have hpoint : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → τ x = completedRestriction σ Z x := by
    intro x hx
    have hinside : σ (x : V) ∈ Z := by
      by_contra hout
      apply hx
      exact Finset.mem_filter.mpr ⟨x.property, hout⟩
    apply Subtype.ext
    calc
      ((τ x : {x : V // x ∈ Z}) : V) =
          σ (x : V) := hagrees x hinside
      _ = ((completedRestriction σ Z x :
          {x : V // x ∈ Z}) : V) := by
        symm
        exact completedRestriction_apply_of_mem
          σ Z x x.property hinside
  calc
    permutationDistance
        τ (completedRestriction σ Z) ≤
      (subtypeBad Z E).card :=
        permutationDistance_le_subtypeBad Z E
          τ (completedRestriction σ Z) hpoint
    _ = (Z ∩ E).card := card_subtypeBad Z E
    _ ≤ E.card := Finset.card_le_card Finset.inter_subset_right
    _ ≤ (Finset.univ \ Z).card := by
      simpa only [E] using
        card_permutation_exit_le_deleted σ Z

private theorem completedGenerator_normalizedHamming_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (Z : Finset V)
    (τ : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      σ (x : V) ∈ Z →
        ((τ x : {x : V // x ∈ Z}) : V) = σ (x : V)) :
    normalizedHamming
      τ (completedRestriction σ Z) ≤
        (((Finset.univ \ Z).card : ℝ) / Z.card) := by
  have hnat :=
    completedGenerator_permutationDistance_le_deleted
      σ Z τ hagrees
  have hreal :
      (permutationDistance
        τ (completedRestriction σ Z) : ℝ) ≤
          (Finset.univ \ Z).card := by
    exact_mod_cast hnat
  have hdiv := div_le_div_of_nonneg_right hreal
    (show (0 : ℝ) ≤ (Z.card : ℝ) by positivity)
  simpa only [normalizedHamming,
    permutationDistance, Fintype.card_coe] using hdiv

private theorem completedGenerator_normalizedHamming_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → Equiv.Perm (V n))
    (Z : (n : ℕ) → Finset (V n))
    (τ : (n : ℕ) → Equiv.Perm {x : V n // x ∈ Z n})
    (hagrees : ∀ n, ∀ x : {x : V n // x ∈ Z n},
      σ n (x : V n) ∈ Z n →
        ((τ n x : {x : V n // x ∈ Z n}) : V n) =
          σ n (x : V n))
    (hdeleted : Tendsto
      (fun n => (((Finset.univ \ Z n).card : ℝ) / (Z n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        normalizedHamming
          (τ n) (completedRestriction (σ n) (Z n)))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      normalizedHamming_nonneg
        (τ n) (completedRestriction (σ n) (Z n)))
    (Filter.Eventually.of_forall fun n =>
      completedGenerator_normalizedHamming_le_deleted
        (σ n) (Z n) (τ n) (hagrees n))
    hdeleted

end CompletedSourceChosenWordRestrictionTransfer

namespace CompletedSourceFinalGeneratorTransfer

open Filter Topology
open MatchedComponentCompletion
open CompletedSourceChosenWordRestrictionTransfer

public
theorem surviving_card_ratio_tendsto_one
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n)))
      atTop (nhds 1) := by
  have hbase : Tendsto
      (fun n => (1 : ℝ) -
        ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hdeleted
  convert hbase using 1
  funext n
  have hU : (Finset.univ : Finset (V n)).Nonempty := by
    obtain ⟨x, _⟩ := hZ n
    exact ⟨x, Finset.mem_univ x⟩
  have hcard : Fintype.card (V n) ≠ 0 := by
    exact Finset.card_ne_zero.mpr hU
  rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (D n)),
    Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ (D n))]
  field_simp

public
theorem deleted_density_relative_survivors
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((D n).card : ℝ) /
          (Finset.univ \ D n : Finset (V n)).card)
      atTop (nhds 0) := by
  have hcover :=
    surviving_card_ratio_tendsto_one V D hZ hdeleted
  have hquotient : Tendsto
      ((fun n => ((D n).card : ℝ) / Fintype.card (V n)) /
        (fun n =>
          ((Finset.univ \ D n : Finset (V n)).card : ℝ) /
            Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [zero_div] using
      hdeleted.div hcover (by norm_num : (1 : ℝ) ≠ 0)
  convert hquotient using 1
  funext n
  have hN : Fintype.card (V n) ≠ 0 := by
    obtain ⟨x, _⟩ := hZ n
    exact Finset.card_ne_zero.mpr
      (show (Finset.univ : Finset (V n)).Nonempty from
        ⟨x, Finset.mem_univ x⟩)
  have hNreal : (Fintype.card (V n) : ℝ) ≠ 0 := by
    exact_mod_cast hN
  have hZreal :
      ((Finset.univ \ D n : Finset (V n)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (hZ n)
  change
    ((D n).card : ℝ) /
        (Finset.univ \ D n : Finset (V n)).card =
      (((D n).card : ℝ) / Fintype.card (V n)) /
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n))
  field_simp [hNreal, hZreal]

public
theorem twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*}
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (s : ι → J)
    (P : (n : ℕ) → Finset (V n))
    (D : (n : ℕ) → Finset {x : V n // x ∈ P n})
    (τ : (n : ℕ) → (i : ι) →
      Equiv.Perm
        {x : {x : V n // x ∈ P n} //
          x ∈ (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})})
    (hsource : ∀ n i, σ n i = p n (s i))
    (hagrees : ∀ n i,
      ∀ x : {x : {x : V n // x ∈ P n} //
        x ∈ (Finset.univ \ D n :
          Finset {x : V n // x ∈ P n})},
        completedRestriction (σ n i) (P n) x.val ∈
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}) →
        (τ n i x).val =
          completedRestriction (σ n i) (P n) x.val)
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (P n).card)
      atTop (nhds 0)) :
    ∀ i : ι,
      Tendsto
        (fun n =>
          normalizedHamming
            (τ n i)
            (completedRestriction
              (completedRestriction (p n (s i)) (P n))
              (Finset.univ \ D n)))
        atTop (nhds 0) := by
  intro i
  have hdeletedbase : Tendsto
      (fun n =>
        ((D n).card : ℝ) /
          Fintype.card {x : V n // x ∈ P n})
      atTop (nhds 0) := by
    simpa only [Fintype.card_coe] using hdeleted
  have hsurvivors :=
    deleted_density_relative_survivors
      (fun n => {x : V n // x ∈ P n}) D hZ hdeletedbase
  have hdeletedfinal : Tendsto
      (fun n =>
        (((Finset.univ \
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})).card : ℝ) /
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}).card))
      atTop (nhds 0) := by
    convert hsurvivors using 1
    funext n
    have hset :
        (Finset.univ \
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})) = D n := by
      ext x
      simp only [Finset.univ_eq_attach, sdiff_sdiff_right_self, Finset.inf_eq_inter',
        Finset.mem_inter,
        Finset.mem_attach, true_and]
    rw [hset]
  have hletter :=
    completedGenerator_normalizedHamming_tendsto_zero
      (fun n => {x : V n // x ∈ P n})
      (fun n => completedRestriction (σ n i) (P n))
      (fun n => (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}))
      (fun n => τ n i)
      (fun n => hagrees n i)
      hdeletedfinal
  convert hletter using 1
  funext n
  rw [hsource n i]

end CompletedSourceFinalGeneratorTransfer

namespace CompletedPrescribedSpectralRadiusSchedule

open Filter Topology
open scoped Pointwise

private theorem mem_generator_pow_of_chosen_word_length
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    {a : G} {r : ℕ} (ha : (w a).length ≤ r) :
    a ∈ S ^ r := by
  have hprod : ∀ l : List ↥S,
      ((l.map fun i : ↥S => (i : G)).prod) ∈ S ^ l.length := by
    intro l
    induction l with
    | nil => simp only [List.length_nil, pow_zero, List.map_nil, List.prod_nil, Finset.mem_one]
    | cons i l ih =>
        simpa only [List.length_cons, pow_succ', List.map_cons, List.map_subtype, List.map_id_fun',
          id_eq,
          List.prod_cons] using (Finset.mul_mem_mul i.property ih)
  apply Finset.pow_subset_pow_right hone ha
  simpa only [hw a] using hprod (w a)

private def multiplicationBad
    {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
    (φ : G → Equiv.Perm V) (a g : G) : Finset V :=
  Finset.univ.filter (fun x => φ (a * g) x ≠ (φ a * φ g) x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def fixedRadiusRootBad
    {G V : Type*} [Group G] [DecidableEq G]
    [Fintype V] [DecidableEq V]
    (φ : G → Equiv.Perm V) (S : Finset G) (r : ℕ) : Finset V :=
  ((S ^ r).product (S ^ r)).biUnion fun ag =>
    multiplicationBad φ ag.1 ag.2

public
theorem fixedRadiusRootBad_rooted
    {G V : Type*} [Group G] [DecidableEq G]
    [Fintype V] [DecidableEq V]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    (φ : G → Equiv.Perm V) (r : ℕ)
    (a g : G)
    (hr : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    (x : V) (hx : x ∉ fixedRadiusRootBad φ S r) :
    φ (a * g) x = (φ a * φ g) x := by
  have ha : a ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw (by omega)
  have hg : g ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw (by omega)
  by_contra hfailure
  apply hx
  unfold fixedRadiusRootBad
  apply Finset.mem_biUnion.mpr
  refine ⟨(a, g), Finset.mem_product.mpr ⟨ha, hg⟩, ?_⟩
  unfold multiplicationBad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfailure⟩

public
theorem fixedRadiusRootBad_density_tendsto_zero
    {G : Type*} [Group G] [DecidableEq G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (φ : ∀ n, G → Equiv.Perm (V n))
    (S : Finset G)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => normalizedHamming
          (φ n (a * g)) (φ n a * φ n g))
        atTop (𝓝 0))
    (r : ℕ) :
    Tendsto
      (fun n =>
        ((fixedRadiusRootBad (φ n) S r).card : ℝ) /
          Fintype.card (V n))
      atTop (𝓝 0) := by
  classical
  have hpair : ∀ ag ∈ (S ^ r).product (S ^ r),
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) ∩
            multiplicationBad (φ n) ag.1 ag.2).card : ℝ) /
              (Finset.univ : Finset (V n)).card)
        atTop (𝓝 0) := by
    intro ag _
    simpa only [multiplicationBad, Equiv.Perm.coe_mul, Function.comp_apply, ne_eq,
      Finset.univ_inter,
      Finset.card_univ, normalizedHamming, hammingDist] using hmul ag.1 ag.2
  have h := finite_union_bad_density_tendsto_zero
    ((S ^ r).product (S ^ r))
    (fun n => (Finset.univ : Finset (V n)))
    (fun n ag => multiplicationBad (φ n) ag.1 ag.2)
    hpair
  simpa only [fixedRadiusRootBad, Finset.product_eq_sprod, Finset.product_biUnion,
    Finset.univ_inter,
    Finset.card_univ] using h

end CompletedPrescribedSpectralRadiusSchedule

namespace KunSourceUnconditionalFullDecomposition

section

open Filter Topology
open KunActualSoficRootRadius
open KunActualRootedModelBridge
open KunRootedWordPower
open KunThomInvariantOrthogonal
open scoped BigOperators symmDiff

private theorem exists_source_sparse_cut_at_radius
    {G : Type} [Group G] [DecidableEq G]
    (P : KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (A : SoficApproximation G) (n : ℕ)
        (T : Finset (Fin (A.model n).size)),
      Disjoint T
        (chosenCayleyRadiusBad A S
          (symmetricGeneratorWord S hsymmetric hgenerates) n r) →
      (boundary
        (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (Fin (A.model n).size),
        3 * (U ∆ T).card < T.card ∧
          (boundary
            (fun i : ↥S => (A.model n).action (i : G)) U : ℝ) ≤
              α * (U.card : ℝ) := by
  classical
  obtain ⟨k, r, hr⟩ :=
    exists_rooted_word_radius_sparse_cut_of_boundary
      P S hone hcover hsymmetric
      (symmetricGeneratorWord S hsymmetric hgenerates)
      γ α hγ hα hsmall
  refine ⟨r, ?_⟩
  intro A n T hgood hboundary
  have hvertexInstance :
      (instDecidableEqFin (A.model n).size :
        DecidableEq (Fin (A.model n).size)) =
          Classical.decEq (Fin (A.model n).size) :=
    Subsingleton.elim _ _
  let : DecidableEq (Fin (A.model n).size) :=
    Classical.decEq (Fin (A.model n).size)
  rw [hvertexInstance] at hboundary ⊢
  have hT : T.Nonempty := by
    by_contra hnot
    have hempty : T = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    subst T
    simp only [
      boundary,
      Finset.univ_eq_attach,
      Finset.notMem_empty,
      not_false_eq_true,
      Finset.filter_empty,
      Finset.card_empty,
      Finset.sum_const_zero,
      CharP.cast_eq_zero,
      mul_zero,
      lt_self_iff_false
    ] at hboundary
  let X :=
    sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T
  have hgenerated :
      X.IsGenerated (fun i : ↥S => (i : G))
        (symmetricGeneratorWord S hsymmetric hgenerates) :=
    sourceRootedIndicatorMarkovModel_isGenerated
      A S hsymmetric hgenerates n T
  have hrooted :
      X.IsRootedAtRadius
        (symmetricGeneratorWord S hsymmetric hgenerates) r :=
    sourceRootedIndicatorMarkovModel_isRootedAtRadius
      A S hone hsymmetric hgenerates n r T hgood
  have hboundary' :
      (boundary X.generator T : ℝ) <
        γ * (T.card : ℝ) := by
    change
      (boundary
        (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
          γ * (T.card : ℝ)
    exact hboundary
  obtain ⟨U, _hmarkov, _hreference, hclose, hcut⟩ :=
    hr X hgenerated hrooted T hT
      (by
        intro x
        dsimp only [X, sourceRootedIndicatorMarkovModel,
          sourceFiniteIndicator]
        split
        next hleft =>
          split
          next => rfl
          next hright =>
            exfalso
            apply hright
            exact Finset.mem_def.mpr (Finset.mem_def.mp hleft)
        next hleft =>
          split
          next hright =>
            exfalso
            apply hleft
            exact Finset.mem_def.mpr (Finset.mem_def.mp hright)
          next => rfl)
      hboundary'
  exact ⟨U, hclose, hcut⟩

private theorem exists_source_full_finpartition_sequence_of_kazhdan
    {G : Type} [Group G]
    (A : SoficApproximation G)
    (P : KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    ∃ (γ : ℝ)
      (Q : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γ ∧
        (∀ n, ∀ C ∈ (Q n).parts,
          ∀ E : Finset (Fin (A.model n).size),
            E ⊆ C →
            2 * E.card ≤ C.card →
            γ * (E.card : ℝ) ≤
              (boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) E : ℝ)) ∧
        Tendsto
          (fun n =>
            (∑ C ∈ (Q n).parts,
              (boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) C : ℝ)) /
                  (A.model n).size)
          atTop (𝓝 0) := by
  classical
  let : Nonempty (↥S) := ⟨⟨1, hone⟩⟩
  let q : ℝ := kazhdanMarkovContractionFactor P S
  let γ : ℝ := (S.card : ℝ) * (1 - q) ^ 2 / 288
  have hq : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, hone⟩
  have hd : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  have hsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2 := by
    have hgap : 0 < (S.card : ℝ) * (1 - q) ^ 2 := by
      positivity
    dsimp [γ, q]
    nlinarith
  let α : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hα (j : ℕ) : 0 < α j := by
    dsimp [α]
    positivity
  have hαzero : Tendsto α atTop (𝓝 0) := by
    simpa [α] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsparse (j : ℕ) :=
    exists_source_sparse_cut_at_radius
      P S hone hcover hsymmetric hgenerates
      γ (α j) hγ (hα j) hsmall
  let radius : ℕ → ℕ := fun j => (hsparse j).choose
  let w : G → List ↥S :=
    symmetricGeneratorWord S hsymmetric hgenerates
  have hw : ∀ g : G,
      ((w g).map fun i : ↥S => (i : G)).prod = g := by
    intro g
    exact symmetricGeneratorWord_prod S hsymmetric hgenerates g
  let e : ℕ → ℕ → ℝ := fun n j =>
    ((chosenCayleyRadiusBad A S w n (radius j)).card : ℝ) /
      (A.model n).size
  have henonnegative : ∀ n j, 0 ≤ e n j := by
    intro n j
    dsimp [e]
    positivity
  have hezero (j : ℕ) :
      Tendsto (fun n => e n j) atTop (𝓝 0) := by
    simpa only [e] using
      chosenCayleyRadiusBad_density_tendsto_zero
        A S w hw (radius j)
  obtain ⟨m, hm, he⟩ :=
    exists_diverging_radius_with_vanishing_diagonal_error
      e henonnegative hezero
  let B : (n : ℕ) → Finset (Fin (A.model n).size) :=
    fun n => chosenCayleyRadiusBad A S w n (radius (m n))
  let a : ℕ → ℝ := fun n => α (m n)
  let σ : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n i => (A.model n).action (i : G)
  let (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    ⟨⟨0, (A.model n).size_pos⟩⟩
  have hazero : Tendsto a atTop (𝓝 0) := by
    exact hαzero.comp hm
  have hbad :
      Tendsto
        (fun n =>
          ((B n).card : ℝ) /
            Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    simpa only [B, e, Fintype.card_fin] using he
  have himprove :
      ∀ n (T : Finset (Fin (A.model n).size)),
        T ⊆ Finset.univ \ B n →
        (boundary (σ n) T : ℝ) <
          γ * (T.card : ℝ) →
        ∃ U : Finset (Fin (A.model n).size),
          3 * (U ∆ T).card < T.card ∧
            (boundary (σ n) U : ℝ) ≤
              a n * (U.card : ℝ) := by
    intro n T hT hboundary
    have hdisjoint : Disjoint T (B n) := by
      apply Finset.disjoint_left.mpr
      intro x hx hbadx
      exact (Finset.mem_sdiff.mp (hT hx)).2 hbadx
    have hgood :
        Disjoint T
          (chosenCayleyRadiusBad A S
            (symmetricGeneratorWord S hsymmetric hgenerates)
            n ((hsparse (m n)).choose)) := by
      simpa only [B, w, radius] using hdisjoint
    have hboundary' :
        (boundary
          (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
            γ * (T.card : ℝ) := by
      simpa only [σ] using hboundary
    obtain ⟨U, hclose, hcut⟩ :=
      (hsparse (m n)).choose_spec A n T hgood hboundary'
    refine ⟨U, hclose, ?_⟩
    simpa only [σ, a] using hcut
  obtain ⟨Q, hγ', hQ, hbudget⟩ :=
    KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
        (↥S) (fun n => Fin (A.model n).size)
        σ B γ hγ a
        (fun n => (hα (m n)).le)
        hazero hbad himprove
  refine ⟨γ, Q, hγ', ?_, ?_⟩
  · simpa only [σ] using hQ
  · simpa only [σ, Fintype.card_fin] using hbudget

end

section

open Filter Topology

public
theorem exists_source_subgroup_and_ambient_full_finpartition_sequences
    {G Γ : Type} [Group G] [Group Γ]
    (A : SoficApproximation G)
    (f : Γ →* G) (hf : Function.Injective f)
    (PΓ : KazhdanPair.{0, 0} Γ)
    (PG : KazhdanPair.{0, 0} G)
    (SΓ : Finset Γ) (SG : Finset G)
    (honeΓ : 1 ∈ SΓ) (honeG : 1 ∈ SG)
    (hcoverΓ : PΓ.generators ⊆ SΓ)
    (hcoverG : PG.generators ⊆ SG)
    (hsymmetricΓ : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesΓ : Subgroup.closure (SΓ : Set Γ) = ⊤)
    (hgeneratesG : Subgroup.closure (SG : Set G) = ⊤) :
    ∃ (γΓ γG : ℝ)
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by
  classical
  obtain ⟨γΓ, QΓ, hγΓ, hexpΓ, hbudgetΓ⟩ :=
    exists_source_full_finpartition_sequence_of_kazhdan
      (pullbackSoficApproximation f hf A)
      PΓ SΓ honeΓ hcoverΓ hsymmetricΓ hgeneratesΓ
  obtain ⟨γG, QG, hγG, hexpG, hbudgetG⟩ :=
    exists_source_full_finpartition_sequence_of_kazhdan
      A PG SG honeG hcoverG hsymmetricG hgeneratesG
  refine ⟨γΓ, γG, QΓ, QG, hγΓ, hγG, ?_, hexpG, ?_,
    hbudgetG⟩
  · exact hexpΓ
  · exact hbudgetΓ

end

end KunSourceUnconditionalFullDecomposition

namespace KunActualCompressedSourceGroupFoundations

universe v

public
theorem alphaZeroPrefixElementaryGroup_infinite :
    Infinite
      (prefixElementaryGroup alphaZeroPrefixCode) := by
  let : Infinite (binaryLeavittElementaryGroup 3) :=
    binaryLeavittEL3_infinite
  exact Infinite.of_injective
    (binaryPrefixElementaryGroupEquiv
      alphaZeroPrefixCode)
    (binaryPrefixElementaryGroupEquiv
      alphaZeroPrefixCode).injective

end KunActualCompressedSourceGroupFoundations

namespace KunExactKazhdanGeneratorChange

universe u v

private theorem unitary_word_displacement_le
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (ξ : H) (l : List G) (δ : ℝ)
    (hletters : ∀ g ∈ l, ‖π g ξ - ξ‖ ≤ δ) :
    ‖π l.prod ξ - ξ‖ ≤ (l.length : ℝ) * δ := by
  induction l with
  | nil =>
      simp only [List.prod_nil, map_one, LinearIsometryEquiv.coe_one, id_eq, sub_self, norm_zero,
        List.length_nil,
        CharP.cast_eq_zero, zero_mul, Std.le_refl]
  | cons g l ih =>
      have hg : ‖π g ξ - ξ‖ ≤ δ :=
        hletters g (by simp only [List.mem_cons, true_or])
      have htail :
          ∀ a ∈ l, ‖π a ξ - ξ‖ ≤ δ := by
        intro a ha
        exact hletters a (by simp only [List.mem_cons, ha, or_true])
      have hword := ih htail
      calc
        ‖π (g :: l).prod ξ - ξ‖ =
            ‖π g (π l.prod ξ - ξ) + (π g ξ - ξ)‖ := by
              congr 1
              simp only [List.prod_cons, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
                map_sub,
                sub_add_sub_cancel]
        _ ≤ ‖π g (π l.prod ξ - ξ)‖ +
              ‖π g ξ - ξ‖ := norm_add_le _ _
        _ = ‖π l.prod ξ - ξ‖ + ‖π g ξ - ξ‖ := by
              rw [LinearIsometryEquiv.norm_map]
        _ ≤ (l.length : ℝ) * δ + δ := by linarith
        _ = ((g :: l).length : ℝ) * δ := by
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
              ring

private theorem exists_word_of_symmetric_generating_finset
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ l : List ↥S, ((l.map fun i : ↥S => (i : G)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgenerates]
    simp only [Subgroup.mem_top]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]⟩
  | one =>
      exact ⟨[], by simp only [List.map_nil, List.prod_nil]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : G)⁻¹, hsymmetric (i : G) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : G)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : G)⁻¹) =
            (l.map fun i : ↥S => (i : G)).map
              (fun z : G => z⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]

private def symmetricGeneratingWord
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    List ↥S :=
  (exists_word_of_symmetric_generating_finset
    S hsymmetric hgenerates g).choose

private theorem symmetricGeneratingWord_prod
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    (((symmetricGeneratingWord S hsymmetric hgenerates g).map
      fun i : ↥S => (i : G)).prod) = g :=
  (exists_word_of_symmetric_generating_finset
    S hsymmetric hgenerates g).choose_spec

private def kazhdanPairOnSymmetricGeneratingFinset
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, v} G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    KazhdanPair.{u, v} G := by
  classical
  let w : G → List ↥S :=
    symmetricGeneratingWord S hsymmetric hgenerates
  let L : ℕ := 1 + ∑ g ∈ P.generators, (w g).length
  have hL : 0 < L := by
    dsimp [L]
    omega
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL
  refine
    { generators := S
      kazhdanConstant := P.kazhdanConstant / (L : ℝ)
      positive := div_pos P.positive hLreal
      invariant := ?_ }
  intro H _ _ _ π ξ hξ hS
  apply P.invariant H π ξ hξ
  intro g hg
  have hlength :
      (w g).length < L := by
    have hsingle :
        (w g).length ≤
          ∑ a ∈ P.generators, (w a).length :=
      Finset.single_le_sum
        (fun a _ => Nat.zero_le (w a).length) hg
    dsimp [L]
    omega
  have hlengthreal :
      ((w g).length : ℝ) < (L : ℝ) := by
    exact_mod_cast hlength
  have hδ : 0 < P.kazhdanConstant / (L : ℝ) :=
    div_pos P.positive hLreal
  have hword :
      ‖π (((w g).map fun i : ↥S => (i : G)).prod) ξ - ξ‖ ≤
        ((w g).length : ℝ) *
          (P.kazhdanConstant / (L : ℝ)) := by
    have hbound :=
      unitary_word_displacement_le π ξ
        ((w g).map fun i : ↥S => (i : G))
        (P.kazhdanConstant / (L : ℝ))
        (by
          intro a ha
          obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp ha
          exact (hS (i : G) i.property).le)
    simpa only [List.length_map] using hbound
  calc
    ‖π g ξ - ξ‖ =
        ‖π (((w g).map fun i : ↥S => (i : G)).prod) ξ - ξ‖ := by
          rw [show
            (((w g).map fun i : ↥S => (i : G)).prod) = g from
              symmetricGeneratingWord_prod
                S hsymmetric hgenerates g]
    _ ≤ ((w g).length : ℝ) *
          (P.kazhdanConstant / (L : ℝ)) := hword
    _ < (L : ℝ) * (P.kazhdanConstant / (L : ℝ)) :=
      mul_lt_mul_of_pos_right hlengthreal hδ
    _ = P.kazhdanConstant := by
      field_simp [Nat.cast_ne_zero.mpr hL.ne']

private theorem kazhdanPairOnSymmetricGeneratingFinset_generators
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, v} G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    (kazhdanPairOnSymmetricGeneratingFinset
      P S hsymmetric hgenerates).generators = S := by
  rfl

public
theorem exists_kazhdanPair_with_exact_symmetric_generators
    {G : Type u} [Group G]
    [HasPropertyT.{u, v} G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    ∃ P : KazhdanPair.{u, v} G,
      P.generators = S := by
  obtain ⟨P⟩ :=
    HasPropertyT.exists_kazhdanPair (G := G)
  exact ⟨kazhdanPairOnSymmetricGeneratingFinset
    P S hsymmetric hgenerates,
    kazhdanPairOnSymmetricGeneratingFinset_generators
      P S hsymmetric hgenerates⟩

end KunExactKazhdanGeneratorChange

namespace KunExactActualSourceAmbientGenerators

section

open KunExactKazhdanGeneratorChange

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceAlphaInclusion :
    prefixElementaryGroup alphaPrefixCode →*
      prefixElementaryGroup ninePrefixCode where
  toFun g :=
    ⟨g.val,
      SourceGeneration.alphaPrefixElementaryGroup_le_nine
        g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem sourceAlphaInclusion_injective :
    Function.Injective sourceAlphaInclusion := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z :
      prefixElementaryGroup ninePrefixCode =>
        z.val) hxy

private def sourceCompressionU :
    prefixElementaryGroup ninePrefixCode :=
  ⟨compressionU,
    compressionU_mem_ninePrefixElementaryGroup⟩

private def sourceCompressionV :
    prefixElementaryGroup ninePrefixCode :=
  ⟨compressionV,
    compressionV_mem_ninePrefixElementaryGroup⟩

private noncomputable def sourcePositiveGenerators
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    Finset
      (prefixElementaryGroup ninePrefixCode) := by
  classical
  exact SΓ.image sourceAlphaInclusion ∪
    {sourceCompressionU, sourceCompressionV}

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def sourceAmbientSymmetricGenerators
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    Finset
      (prefixElementaryGroup ninePrefixCode) := by
  classical
  exact insert 1
    (sourcePositiveGenerators SΓ ∪
      (sourcePositiveGenerators SΓ).image fun g => g⁻¹)

private theorem one_mem_sourceAmbientSymmetricGenerators
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    1 ∈ sourceAmbientSymmetricGenerators SΓ := by
  classical
  simp only [sourceAmbientSymmetricGenerators, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image,
    inv_eq_one, exists_eq_right, or_self, true_or]

private theorem sourceAmbientSymmetricGenerators_inv_mem
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (g : prefixElementaryGroup ninePrefixCode)
    (hg : g ∈ sourceAmbientSymmetricGenerators SΓ) :
    g⁻¹ ∈ sourceAmbientSymmetricGenerators SΓ := by
  classical
  have hcases :
      g = 1 ∨
        g ∈ sourcePositiveGenerators SΓ ∨
        ∃ y ∈ sourcePositiveGenerators SΓ, y⁻¹ = g := by
    simpa only [Subtype.exists, sourceAmbientSymmetricGenerators, Finset.mem_insert,
      Finset.mem_union,
      Finset.mem_image] using hg
  rcases hcases with rfl | hgpos | ⟨y, hy, rfl⟩
  · simp only [sourceAmbientSymmetricGenerators, inv_one, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image,
      inv_eq_one, exists_eq_right, or_self, true_or]
  · have hinv :
        g⁻¹ ∈ (sourcePositiveGenerators SΓ).image
          (fun x => x⁻¹) :=
      Finset.mem_image.mpr ⟨g, hgpos, rfl⟩
    simp only [sourceAmbientSymmetricGenerators, Finset.mem_insert, inv_eq_one, Finset.mem_union,
      hinv, or_true]
  · simp only [sourceAmbientSymmetricGenerators, inv_inv, Finset.mem_insert, Finset.mem_union, hy,
      Finset.mem_image, Subtype.exists, true_or, or_true]

private theorem sourceAmbientSymmetricGenerators_generate
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤) :
    Subgroup.closure
      (sourceAmbientSymmetricGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode)) = ⊤ := by
  classical
  let K : Subgroup
      (prefixElementaryGroup ninePrefixCode) :=
    Subgroup.closure
      (sourceAmbientSymmetricGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode))
  have hpositive :
      ∀ x ∈ sourcePositiveGenerators SΓ, x ∈ K := by
    intro x hx
    apply Subgroup.subset_closure
    change x ∈ sourceAmbientSymmetricGenerators SΓ
    simp only [sourceAmbientSymmetricGenerators, Finset.mem_insert, Finset.mem_union, hx,
      Finset.mem_image,
      Subtype.exists, true_or, or_true]
  have hcorner :
      ∀ g :
        prefixElementaryGroup alphaPrefixCode,
        sourceAlphaInclusion g ∈ K := by
    intro g
    have hsub :
        Subgroup.closure
          (SΓ : Set
            (prefixElementaryGroup
              alphaPrefixCode)) ≤
            K.comap sourceAlphaInclusion := by
      rw [Subgroup.closure_le]
      intro x hx
      change sourceAlphaInclusion x ∈ K
      apply hpositive
      change sourceAlphaInclusion x ∈
        SΓ.image sourceAlphaInclusion ∪
          {sourceCompressionU, sourceCompressionV}
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    apply hsub
    rw [hgeneratesΓ]
    simp only [Subgroup.mem_top]
  let U : Subgroup BinaryLeavittˣ :=
    K.map
      (prefixElementaryGroup
        ninePrefixCode).subtype
  have hsource :
      SourceGeneration.sourceGeneratedGroup ≤ U := by
    rw [SourceGeneration.sourceGeneratedGroup,
      Subgroup.closure_le]
    intro x hx
    rcases hx with hα | htables
    · let a :
          prefixElementaryGroup
            alphaPrefixCode := ⟨x, hα⟩
      exact ⟨sourceAlphaInclusion a, hcorner a, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htables
      rcases htables with rfl | rfl
      · exact ⟨sourceCompressionU,
          hpositive sourceCompressionU
            (by simp only [sourcePositiveGenerators, Finset.union_insert, Finset.union_singleton,
              Finset.mem_insert,
                  Finset.mem_image, Subtype.exists, true_or]), rfl⟩
      · exact ⟨sourceCompressionV,
          hpositive sourceCompressionV
            (by simp only [sourcePositiveGenerators, Finset.union_insert, Finset.union_singleton,
              Finset.mem_insert,
                  Finset.mem_image, Subtype.exists, true_or, or_true]), rfl⟩
  have htop :
      (⊤ : Subgroup
        (prefixElementaryGroup
          ninePrefixCode)) ≤ K := by
    intro x _hx
    have hxin :
        (x.val : BinaryLeavittˣ) ∈
          SourceGeneration.sourceGeneratedGroup := by
      rw [sourceGeneratedGroup_eq_nine]
      exact x.property
    obtain ⟨y, hy, hval⟩ := hsource hxin
    have heq : y = x := by
      apply Subtype.ext
      exact hval
    simpa only [← heq, SetLike.mem_coe] using hy
  exact top_unique htop

private theorem exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤)
    [HasPropertyT.{0, 0}
      (prefixElementaryGroup
        ninePrefixCode)] :
    ∃ P : KazhdanPair.{0, 0}
        (prefixElementaryGroup
          ninePrefixCode),
      P.generators = sourceAmbientSymmetricGenerators SΓ := by
  exact exists_kazhdanPair_with_exact_symmetric_generators
    (sourceAmbientSymmetricGenerators SΓ)
    (sourceAmbientSymmetricGenerators_inv_mem SΓ)
    (sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ)

end

section

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressionTable :
    Fin 2 →
      prefixElementaryGroup ninePrefixCode :=
  ![sourceCompressionU, sourceCompressionV]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourcePositiveGeneratorMap
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    (↥SΓ ⊕ Fin 2) →
      prefixElementaryGroup ninePrefixCode :=
  Sum.elim (fun i : ↥SΓ => sourceAlphaInclusion (i :
    prefixElementaryGroup alphaPrefixCode))
    sourceCompressionTable

private theorem range_sourcePositiveGeneratorMap
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    Set.range (sourcePositiveGeneratorMap SΓ) =
      (sourcePositiveGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode)) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with i | i
    · change
        sourceAlphaInclusion
          (i :
            prefixElementaryGroup
              alphaPrefixCode) ∈
            sourcePositiveGenerators SΓ
      change
        sourceAlphaInclusion
          (i :
            prefixElementaryGroup
              alphaPrefixCode) ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨(i :
          prefixElementaryGroup
            alphaPrefixCode), i.property, rfl⟩
    · fin_cases i
      · change sourceCompressionU ∈
          sourcePositiveGenerators SΓ
        change sourceCompressionU ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
        exact Finset.mem_union_right _ (by simp only [Finset.mem_insert, Finset.mem_singleton,
          true_or])
      · change sourceCompressionV ∈
          sourcePositiveGenerators SΓ
        change sourceCompressionV ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
        exact Finset.mem_union_right _ (by simp only [Finset.mem_insert, Finset.mem_singleton,
          or_true])
  · intro hx
    change
      x ∈ SΓ.image sourceAlphaInclusion ∪
        {sourceCompressionU, sourceCompressionV} at hx
    rcases Finset.mem_union.mp hx with hcorner | htables
    · obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp hcorner
      refine ⟨Sum.inl ⟨g, hg⟩, ?_⟩
      exact heq
    · simp only [Finset.mem_insert, Finset.mem_singleton] at htables
      rcases htables with rfl | rfl
      · refine ⟨Sum.inr (0 : Fin 2), ?_⟩
        rfl
      · refine ⟨Sum.inr (1 : Fin 2), ?_⟩
        rfl

private theorem sourcePositiveGenerators_generate
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤) :
    Subgroup.closure
      (sourcePositiveGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode)) = ⊤ := by
  classical
  let K : Subgroup
      (prefixElementaryGroup ninePrefixCode) :=
    Subgroup.closure
      (sourcePositiveGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode))
  have hcontain :
      (sourceAmbientSymmetricGenerators SΓ : Set
        (prefixElementaryGroup
          ninePrefixCode)) ⊆
        (K : Set
          (prefixElementaryGroup
            ninePrefixCode)) := by
    intro x hx
    have hcases :
        x = 1 ∨
          x ∈ sourcePositiveGenerators SΓ ∨
          x⁻¹ ∈ sourcePositiveGenerators SΓ := by
      simpa only [sourceAmbientSymmetricGenerators, Finset.coe_insert, Finset.coe_union,
        Finset.coe_image,
        Set.image_inv_eq_inv, Set.mem_insert_iff, Set.mem_union, SetLike.mem_coe, Set.mem_inv] using
          hx
    rcases hcases with rfl | hxpositive | hxinverse
    · exact K.one_mem
    · exact Subgroup.subset_closure hxpositive
    · simpa only [SetLike.mem_coe, inv_inv] using K.inv_mem (Subgroup.subset_closure hxinverse)
  have hle :
      Subgroup.closure
        (sourceAmbientSymmetricGenerators SΓ : Set
          (prefixElementaryGroup
            ninePrefixCode)) ≤ K := by
    rw [Subgroup.closure_le]
    exact hcontain
  have htop :
      (⊤ : Subgroup
        (prefixElementaryGroup
          ninePrefixCode)) ≤ K := by
    rw [← sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ]
    exact hle
  exact top_unique htop

private theorem sourcePositiveGeneratorMap_range_generate
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤) :
    Subgroup.closure
      (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ := by
  rw [range_sourcePositiveGeneratorMap]
  exact sourcePositiveGenerators_generate SΓ hgeneratesΓ

end

end KunExactActualSourceAmbientGenerators

namespace KunUnconditionalActualSourceGeneratorData

open KunExactKazhdanGeneratorChange
open KunExactActualSourceAmbientGenerators

private theorem exists_symmetric_generating_finset_of_finitelyGenerated
    {G : Type*} [Group G]
    (hfg : Group.FG G) :
    ∃ S : Finset G,
      1 ∈ S ∧
        (∀ g ∈ S, g⁻¹ ∈ S) ∧
        Subgroup.closure (S : Set G) = ⊤ := by
  classical
  obtain ⟨_, T, _, hT⟩ := (Group.fg_iff').1 hfg
  let S : Finset G := insert 1 (T ∪ T.image fun g => g⁻¹)
  refine ⟨S, by simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, inv_eq_one,
    exists_eq_right, or_self,
                  true_or, S], ?_, ?_⟩
  · intro g hg
    have hcases :
        g = 1 ∨ g ∈ T ∨
          ∃ y ∈ T, y⁻¹ = g := by
      simpa [S, Finset.mem_image] using hg
    rcases hcases with rfl | hgT | ⟨y, hy, rfl⟩
    · simp only [inv_one, Finset.mem_insert, Finset.mem_union, Finset.mem_image, inv_eq_one,
      exists_eq_right,
        or_self, true_or, S]
    · have hmem :
          g⁻¹ ∈ T.image fun z => z⁻¹ :=
        Finset.mem_image.mpr ⟨g, hgT, rfl⟩
      simp only [Finset.mem_insert, inv_eq_one, Finset.mem_union, hmem, or_true, S]
    · simp only [inv_inv, Finset.mem_insert, Finset.mem_union, hy, Finset.mem_image, true_or,
      or_true, S]
  · have hsubset : (T : Set G) ⊆ (S : Set G) := by
      intro g hg
      change g ∈ T at hg
      change g ∈ S
      simp only [Finset.mem_insert, Finset.mem_union, hg, Finset.mem_image, true_or, or_true, S]
    apply top_unique
    rw [← hT]
    exact Subgroup.closure_mono hsubset

private theorem exists_actual_source_alpha_symmetric_generators :
    ∃ SΓ : Finset
        (prefixElementaryGroup
          alphaPrefixCode),
      1 ∈ SΓ ∧
        (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
        Subgroup.closure
          (SΓ : Set
            (prefixElementaryGroup
              alphaPrefixCode)) = ⊤ :=
  exists_symmetric_generating_finset_of_finitelyGenerated
    alphaPrefixElementaryGroup_finitelyGenerated

public
theorem exists_unconditional_actual_source_generator_data :
    ∃ (SΓ : Finset
          (prefixElementaryGroup
            alphaPrefixCode))
      (PΓ : KazhdanPair.{0, 0}
        (prefixElementaryGroup
          alphaPrefixCode))
      (PG : KazhdanPair.{0, 0}
        (prefixElementaryGroup
          ninePrefixCode)),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤ ∧
      PΓ.generators = SΓ ∧
      1 ∈ sourceAmbientSymmetricGenerators SΓ ∧
      (∀ g ∈ sourceAmbientSymmetricGenerators SΓ,
        g⁻¹ ∈ sourceAmbientSymmetricGenerators SΓ) ∧
      Subgroup.closure
        (sourceAmbientSymmetricGenerators SΓ : Set
          (prefixElementaryGroup
            ninePrefixCode)) = ⊤ ∧
      PG.generators = sourceAmbientSymmetricGenerators SΓ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ := by
  let : HasPropertyT.{0, 0}
      (prefixElementaryGroup
        alphaPrefixCode) :=
    alphaPrefixElementaryGroup_hasPropertyT_unconditional
  let : HasPropertyT.{0, 0}
      (prefixElementaryGroup
        ninePrefixCode) :=
    ninePrefixElementaryGroup_hasPropertyT_unconditional
  obtain ⟨SΓ, honeΓ, hsymmetricΓ, hgeneratesΓ⟩ :=
    exists_actual_source_alpha_symmetric_generators
  obtain ⟨PΓ, hPΓ⟩ :=
    exists_kazhdanPair_with_exact_symmetric_generators
      SΓ hsymmetricΓ hgeneratesΓ
  obtain ⟨PG, hPG⟩ :=
    exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
      SΓ hgeneratesΓ
  refine ⟨SΓ, PΓ, PG, honeΓ, hsymmetricΓ, hgeneratesΓ,
    hPΓ, one_mem_sourceAmbientSymmetricGenerators SΓ,
    sourceAmbientSymmetricGenerators_inv_mem SΓ,
    sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ,
    hPG, sourceAlphaInclusion_injective, ?_⟩
  exact sourcePositiveGeneratorMap_range_generate SΓ hgeneratesΓ

end KunUnconditionalActualSourceGeneratorData

namespace SourceCommonComponentComparisonBad

open Filter Topology
open scoped BigOperators

private noncomputable def comparisonBad
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (eta : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ¬ (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (p x) : ℝ)

private noncomputable def familyComparisonBad
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) : Finset (ι × V) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ (1 - eta) * (partitionComponentSize Q e.2 : ℝ) ≤
      (partitionComponentSize Q (p e.1 e.2) : ℝ)

private theorem familyComparisonBad_card
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) :
    (familyComparisonBad Q p eta).card =
      ∑ i : ι, (comparisonBad Q (p i) eta).card := by
  classical
  unfold familyComparisonBad
  rw [Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  unfold comparisonBad
  rw [Finset.card_filter]

private theorem comparisonBad_subset_partitionWordCrossing
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (eta : ℝ) (heta : 0 ≤ eta) :
    comparisonBad Q p eta ⊆ partitionWordCrossing Q p := by
  classical
  intro x hx
  unfold comparisonBad at hx
  have hbad := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hsame
  apply hbad
  have hpart : Q.part (p x) = Q.part x :=
    Q.part_eq_of_mem (Q.part_mem.mpr (Finset.mem_univ x)) hsame
  have hsize : partitionComponentSize Q (p x) =
      partitionComponentSize Q x := by
    unfold partitionComponentSize
    rw [hpart]
  rw [hsize]
  have hnonneg : (0 : ℝ) ≤
      (partitionComponentSize Q x : ℝ) := by
    positivity
  nlinarith

private noncomputable def overlapRetainedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) : Finset (Finset V) :=
  (transportedUnivFinpartition Q T).parts \
    insufficientOverlapComponents
      (transportedUnivFinpartition Q T) Q eta

private theorem comparisonBad_subset_matchedWordPreimageBad
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    comparisonBad Q T eta ⊆
      matchedWordPreimageBad
        (Finset.univ : Finset V)
        (overlapRetainedComponents Q T eta)
        (maximumOverlapPart Q) T := by
  classical
  intro x hx
  have hbad : ¬ (1 - eta) *
        (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by
    unfold comparisonBad at hx
    exact (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ (T x), ?_⟩⟩
  intro hcore
  obtain ⟨C, hC, hy⟩ := Finset.mem_biUnion.mp hcore
  have hparts : C ∈
      (transportedUnivFinpartition Q T).parts :=
    (Finset.mem_sdiff.mp hC).1
  have hret : C ∉ insufficientOverlapComponents
      (transportedUnivFinpartition Q T) Q eta :=
    (Finset.mem_sdiff.mp hC).2
  have hyC : T x ∈ C := (Finset.mem_inter.mp hy).1
  have hyD : T x ∈ maximumOverlapPart Q C :=
    (Finset.mem_inter.mp hy).2
  have hxpart : Q.part x ∈ Q.parts :=
    Q.part_mem.mpr (Finset.mem_univ x)
  have hmap : (Q.part x).map T.toEmbedding ∈
      (transportedUnivFinpartition Q T).parts := by
    rw [transportedUnivFinpartition_parts]
    exact Finset.mem_image_of_mem
      (fun D : Finset V => D.map T.toEmbedding) hxpart
  have hyMap : T x ∈ (Q.part x).map T.toEmbedding :=
    Finset.mem_map.mpr
      ⟨x, Q.mem_part (Finset.mem_univ x), rfl⟩
  have heq : (Q.part x).map T.toEmbedding = C := by
    have hfirst :=
      (transportedUnivFinpartition Q T).part_eq_of_mem
        hmap hyMap
    have hsecond :=
      (transportedUnivFinpartition Q T).part_eq_of_mem
        hparts hyC
    exact hfirst.symm.trans hsecond
  apply hbad
  apply partitionComponentSize_transport_lower_of_retained
    Q T (Q.part x) hxpart eta
  · simpa only [heq] using hret
  · exact Q.mem_part (Finset.mem_univ x)
  · simpa only [heq] using hyD

private theorem matchedCore_missing_card_le_overlap_and_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    ((Finset.univ : Finset V) \
      matchedCore
        (overlapRetainedComponents Q T eta)
        (maximumOverlapPart Q)).card ≤
      (∑ C ∈ insufficientOverlapComponents
        (transportedUnivFinpartition Q T) Q eta,
          C.card) +
      ∑ C ∈ (transportedUnivFinpartition Q T).parts,
        (C \
          maximumOverlapPart Q C).card := by
  classical
  let P := transportedUnivFinpartition Q T
  let O := insufficientOverlapComponents P Q eta
  let R := P.parts \
    insufficientOverlapComponents P Q eta
  have hR : R ⊆ P.parts := Finset.sdiff_subset
  have hO : O ⊆ P.parts :=
    insufficientOverlapComponents_subset P Q eta
  have hparts : P.parts \ R = O := by
    ext C
    constructor
    · intro h
      obtain ⟨hCP, hnot⟩ := Finset.mem_sdiff.mp h
      by_contra hCO
      exact hnot (Finset.mem_sdiff.mpr ⟨hCP, hCO⟩)
    · intro h
      exact Finset.mem_sdiff.mpr
        ⟨hO h, fun hR' => (Finset.mem_sdiff.mp hR').2 h⟩
  have hmissing :
      ((Finset.univ : Finset V) \
        matchedRetainedSupport R).card =
        ∑ C ∈ O, C.card := by
    have hsplit := Finset.sum_sdiff hR (f := fun C : Finset V => C.card)
    rw [hparts] at hsplit
    have hfull := P.sum_card_parts
    have hret := matchedRetainedSupport_card P R hR
    have hcard := Finset.card_sdiff_add_card_eq_card
      (matchedRetainedSupport_subset P R hR)
    omega
  change
    ((Finset.univ : Finset V) \
      matchedCore R
        (maximumOverlapPart Q)).card ≤
      (∑ C ∈ O, C.card) +
        ∑ C ∈ P.parts,
          (C \ maximumOverlapPart Q C).card
  rw [matchedCore_missing_card P R hR
    (maximumOverlapPart Q), hmissing]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum_of_subset_of_nonneg hR
    (fun _ _ _ => Nat.zero_le _)

private theorem comparisonBad_card_le_overlap_and_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    (comparisonBad Q T eta).card ≤
      (∑ C ∈ insufficientOverlapComponents
        (transportedUnivFinpartition Q T) Q eta,
          C.card) +
      ∑ C ∈ (transportedUnivFinpartition Q T).parts,
        (C \
          maximumOverlapPart Q C).card := by
  calc
    (comparisonBad Q T eta).card ≤
        (matchedWordPreimageBad
          (Finset.univ : Finset V)
          (overlapRetainedComponents Q T eta)
          (maximumOverlapPart Q) T).card :=
      Finset.card_le_card
        (comparisonBad_subset_matchedWordPreimageBad Q T eta)
    _ ≤ ((Finset.univ : Finset V) \
          matchedCore
            (overlapRetainedComponents Q T eta)
            (maximumOverlapPart Q)).card :=
      matchedWordPreimageBad_card_le
        (Finset.univ : Finset V)
        (overlapRetainedComponents Q T eta)
        (maximumOverlapPart Q) T
    _ ≤ _ := matchedCore_missing_card_le_overlap_and_loss Q T eta

private theorem cast_card_sdiff_eq_sub_card_inter
    {V : Type*} [DecidableEq V] (C D : Finset V) :
    ((C \ D).card : ℝ) =
      (C.card : ℝ) - ((C ∩ D).card : ℝ) := by
  have hnat := Finset.card_sdiff_add_card_inter C D
  have hreal : ((C \ D).card : ℝ) +
      ((C ∩ D).card : ℝ) = (C.card : ℝ) := by
    exact_mod_cast hnat
  linarith

private theorem subgroup_comparisonBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → Equiv.Perm (V n))
    (eta : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n)
    (hcross : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n) (p n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((comparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hcross
  intro n
  have hnat := Finset.card_le_card
    (comparisonBad_subset_partitionWordCrossing
      (Q n) (p n) (eta n) (heta n))
  have hreal :
      ((comparisonBad (Q n) (p n) (eta n)).card : ℝ) ≤
        ((partitionWordCrossing
          (Q n) (p n)).card : ℝ) := by
    exact_mod_cast hnat
  exact div_le_div_of_nonneg_right hreal (by positivity)

private theorem transported_comparisonBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (eta : ℕ → ℝ)
    (hoverlap : Tendsto
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hloss : Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) /
            Fintype.card (V n) +
        (∑ C ∈
          (transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [zero_add] using hoverlap.add hloss
  refine squeeze_zero (fun n => by positivity) ?_ hlimit
  intro n
  have hnat := comparisonBad_card_le_overlap_and_loss
    (Q n) (T n) (eta n)
  have hreal :
      ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) ≤
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) +
        ∑ C ∈
          (transportedUnivFinpartition (Q n) (T n)).parts,
          ((C \ maximumOverlapPart (Q n) C).card : ℝ) := by
    exact_mod_cast hnat
  simp_rw [cast_card_sdiff_eq_sub_card_inter] at hreal
  calc
    ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) /
        Fintype.card (V n) ≤
      ((∑ C ∈ insufficientOverlapComponents
        (transportedUnivFinpartition (Q n) (T n))
        (Q n) (eta n), (C.card : ℝ)) +
        ∑ C ∈
          (transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = _ := by ring

private theorem combined_positive_comparisonBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (eta : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n)
    (hcross : ∀ i : ι, Tendsto
      (fun n =>
        ((partitionWordCrossing
          (Q n) (σ n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition
            (Q n) (T n j)) (Q n) (eta n), (C.card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hloss : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((familyComparisonBad (Q n)
          (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  classical
  have hsingle (i : ι ⊕ κ) : Tendsto
      (fun n =>
        ((comparisonBad (Q n)
          (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    cases i with
    | inl i =>
        exact subgroup_comparisonBad_density_tendsto_zero
          V Q (fun n => σ n i) eta heta (hcross i)
    | inr j =>
        exact transported_comparisonBad_density_tendsto_zero
          V Q (fun n => T n j) eta (hoverlap j) (hloss j)
  have hsum : Tendsto
      (fun n => ∑ i : ι ⊕ κ,
        ((comparisonBad (Q n)
          (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hsingle i)
  have hrewrite (n : ℕ) :
      ((familyComparisonBad (Q n)
        (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
          Fintype.card (V n) =
        ∑ i : ι ⊕ κ,
          ((comparisonBad (Q n)
            (Sum.elim (σ n) (T n) i) (eta n)).card : ℝ) /
              Fintype.card (V n) := by
    rw [familyComparisonBad_card]
    push_cast
    rw [Finset.sum_div]
  simpa only [hrewrite] using hsum

end SourceCommonComponentComparisonBad

namespace SourceCommonOffsetMidrankEnergy

open Filter Topology
open scoped BigOperators

private noncomputable def realComponentSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V)) (x : V) : ℝ :=
  (partitionComponentSize Q x : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def componentLogRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (H r : ℝ) : V → ℤ :=
  MidrankPermutationEnergy.offsetFloorRank
    (fun x => Real.log (realComponentSize Q x)) H r

private noncomputable def componentSizeComparisonBad
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) : Finset (ι × V) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ (1 - eta) * realComponentSize Q e.2 ≤
      realComponentSize Q (p e.1 e.2)

private theorem componentSizeComparison_of_not_mem
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ)
    (i : ι) (x : V)
    (hx : (i, x) ∉ componentSizeComparisonBad Q p eta) :
    (1 - eta) * realComponentSize Q x ≤
      realComponentSize Q (p i x) := by
  classical
  by_contra h
  apply hx
  unfold componentSizeComparisonBad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

private theorem exists_common_component_log_rank_with_vanishing_drops
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → ι → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hbad : Tendsto
      (fun n =>
        ((componentSizeComparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι,
            ((MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (componentLogRank (Q n) (H n) (r n))
              (p n i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  classical
  let B : (n : ℕ) → Finset (ι × V n) :=
    fun n => componentSizeComparisonBad (Q n) (p n) (eta n)
  let E : (n : ℕ) → Finset (ι × V n) :=
    fun n => Finset.univ \ B n
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hpositive (n : ℕ) (e : ι × V n) (_he : e ∈ E n) :
      0 < realComponentSize (Q n) e.2 := by
    have hpart : (Q n).part e.2 ∈ (Q n).parts :=
      (Q n).part_mem.mpr (Finset.mem_univ e.2)
    have hnonempty := (Q n).nonempty_of_mem_parts hpart
    unfold realComponentSize partitionComponentSize
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hcard (n : ℕ) :
      ((E n).card : ℝ) ≤
        (Fintype.card ι : ℝ) * (Fintype.card (V n) : ℝ) := by
    have hnat : (E n).card ≤ Fintype.card ι * Fintype.card (V n) := by
      simpa only [Fintype.card_prod] using
        (Finset.card_le_univ (E n))
    exact_mod_cast hnat
  have hcomparison (n : ℕ) (e : ι × V n) (he : e ∈ E n) :
      (1 - eta n) * realComponentSize (Q n) e.2 ≤
        realComponentSize (Q n) (p n e.1 e.2) := by
    apply componentSizeComparison_of_not_mem (Q n) (p n) (eta n)
      e.1 e.2
    exact (Finset.mem_sdiff.mp he).2
  have hexceptions : Tendsto
      (fun n =>
        (((Finset.univ : Finset (ι × V n)) \ E n).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
    simpa [E, B] using hbad
  obtain ⟨r, hr, hdrop⟩ :=
    ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
        (fun n => ι × V n) E
        (fun n e => realComponentSize (Q n) e.2)
        (fun n e => realComponentSize (Q n) (p n e.1 e.2))
        eta H (fun n => (Fintype.card (V n) : ℝ))
        (Fintype.card ι : ℝ)
        hpositive heta0 heta1 hH hN hcard hcomparison
        heta hratio hexceptions
  have hrewrite (n : ℕ) :
      rankDropCount
        (fun e : ι × V n => Real.log (realComponentSize (Q n) e.2))
        (fun e : ι × V n =>
          Real.log (realComponentSize (Q n) (p n e.1 e.2)))
        (H n) (r n) =
        ∑ i : ι,
          ((MidrankPermutationEnergy.rankDecreasingVertices
            Finset.univ (componentLogRank (Q n) (H n) (r n))
            (p n i)).card : ℝ) := by
    simpa only [componentLogRank] using
      (MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
        (fun x : V n => Real.log (realComponentSize (Q n) x))
        (p n) (H n) (r n))
  refine ⟨r, hr, ?_⟩
  simpa only [hrewrite] using hdrop

private theorem exists_common_component_log_rank_with_vanishing_midrank_energy
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (Q A : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → ι → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hbad : Tendsto
      (fun n =>
        ((componentSizeComparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0))
    (hcross : Tendsto
      (fun n =>
        (∑ i : ι,
          ((partitionWordCrossing (A n) (p n i)).card : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι,
            ((MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (componentLogRank (Q n) (H n) (r n))
              (p n i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (∑ i : ι, ∑ x : V n,
            (MidrankPermutationEnergy.partitionVertexMidrank
              (A n) (componentLogRank (Q n) (H n) (r n)) (p n i x) -
             MidrankPermutationEnergy.partitionVertexMidrank
              (A n) (componentLogRank (Q n) (H n) (r n)) x) ^ 2) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  obtain ⟨r, hr, hdrop⟩ :=
    exists_common_component_log_rank_with_vanishing_drops
      V ι Q p eta H heta0 heta1 hH heta hratio hbad
  refine ⟨r, hr, hdrop, ?_⟩
  apply MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
      V (fun _ => ι) A
      (fun n => componentLogRank (Q n) (H n) (r n)) p
      (fun n => (Fintype.card (V n) : ℝ))
  · intro n
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  · exact hcross
  · exact hdrop

end SourceCommonOffsetMidrankEnergy

namespace SourceCommonComponentRankNoBad

open Filter Topology
open scoped BigOperators

public
theorem exists_common_positive_component_log_rank_with_vanishing_midrank_energy
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (Q A : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hcrossQ : ∀ i : ι, Tendsto
      (fun n =>
        ((partitionWordCrossing
          (Q n) (σ n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition
            (Q n) (T n j)) (Q n) (eta n), (C.card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hloss : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hcrossA : Tendsto
      (fun n =>
        (∑ i : ι ⊕ κ,
          ((partitionWordCrossing
            (A n) (Sum.elim (σ n) (T n) i)).card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι ⊕ κ,
            ((MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n))
              (Sum.elim (σ n) (T n) i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (∑ i : ι ⊕ κ, ∑ x : V n,
            (MidrankPermutationEnergy.partitionVertexMidrank
              (A n)
              (SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n))
              (Sum.elim (σ n) (T n) i x) -
             MidrankPermutationEnergy.partitionVertexMidrank
              (A n)
              (SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n)) x) ^ 2) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  have hsource :=
    SourceCommonComponentComparisonBad.combined_positive_comparisonBad_density_tendsto_zero
        V ι κ Q σ T eta heta0 hcrossQ hoverlap hloss
  have hsets (n : ℕ) :
      SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
        (Q n) (Sum.elim (σ n) (T n)) (eta n) =
      SourceCommonComponentComparisonBad.familyComparisonBad
        (Q n) (Sum.elim (σ n) (T n)) (eta n) := by
    classical
    ext e
    constructor
    · intro he
      unfold
        SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
        at he
      have hfail := (Finset.mem_filter.mp he).2
      unfold SourceCommonComponentComparisonBad.familyComparisonBad
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only
        [SourceCommonOffsetMidrankEnergy.realComponentSize]
        using hfail
    · intro he
      unfold
        SourceCommonComponentComparisonBad.familyComparisonBad
        at he
      have hfail := (Finset.mem_filter.mp he).2
      unfold
        SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only
        [SourceCommonOffsetMidrankEnergy.realComponentSize]
        using hfail
  have hbad : Tendsto
      (fun n =>
        ((SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
          (Q n) (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [hsets] using hsource
  exact
    SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_midrank_energy
        V (ι ⊕ κ) Q A (fun n => Sum.elim (σ n) (T n))
        eta H heta0 heta1 hH heta hratio hbad hcrossA

end SourceCommonComponentRankNoBad

namespace KunPositiveWordMidrankEnergy

open Filter Topology
open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def squaredPermutationEnergy
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) : ℝ :=
  ∑ x : V, (f (p x) - f x) ^ 2

private theorem squaredPermutationEnergy_nonneg
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) :
    0 ≤ squaredPermutationEnergy f p := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem squaredPermutationEnergy_inv
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) :
    squaredPermutationEnergy f p⁻¹ = squaredPermutationEnergy f p := by
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f (p⁻¹ x) - f x) ^ 2) =
        ∑ x : V, (f x - f (p x)) ^ 2 := by
          simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using
            (Equiv.sum_comp p (fun x : V => (f (p⁻¹ x) - f x) ^ 2)).symm
    _ = ∑ x : V, (f (p x) - f x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      ring

private theorem squaredPermutationEnergy_mul_le
    {V : Type*} [Fintype V]
    (f : V → ℝ) (p q : Equiv.Perm V) :
    squaredPermutationEnergy f (p * q) ≤
      2 * squaredPermutationEnergy f p +
        2 * squaredPermutationEnergy f q := by
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f ((p * q) x) - f x) ^ 2) ≤
        ∑ x : V,
          (2 * (f (p (q x)) - f (q x)) ^ 2 +
           2 * (f (q x) - f x) ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      simp only [Equiv.Perm.mul_apply]
      nlinarith [sq_nonneg
        ((f (p (q x)) - f (q x)) - (f (q x) - f x))]
    _ = 2 * (∑ x : V, (f (p x) - f x) ^ 2) +
          2 * (∑ x : V, (f (q x) - f x) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Equiv.sum_comp q (fun x : V => (f (p x) - f x) ^ 2)]

private theorem squaredPermutationEnergy_le_add_hammingDist
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (p q : Equiv.Perm V) :
    squaredPermutationEnergy f p ≤
      squaredPermutationEnergy f q +
        (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
  classical
  have hpoint (x : V) :
      (f (p x) - f x) ^ 2 ≤
        (f (q x) - f x) ^ 2 +
          if p x = q x then 0 else 1 := by
    split_ifs with hx
    · simp only [hx, add_zero, le_refl]
    · have hp0 := hf0 (p x)
      have hp1 := hf1 (p x)
      have hx0 := hf0 x
      have hx1 := hf1 x
      nlinarith [sq_nonneg (f (q x) - f x),
        mul_nonneg
          (show 0 ≤ 1 - (f (p x) - f x) by linarith)
          (show 0 ≤ 1 + (f (p x) - f x) by linarith)]
  have hindicator :
      (∑ x : V, if p x = q x then (0 : ℝ) else 1) =
        (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
    have hswitch (x : V) :
        (if p x = q x then (0 : ℝ) else 1) =
          if p x ≠ q x then 1 else 0 := by
      split_ifs <;> simp_all
    simp_rw [hswitch]
    simpa only [ne_eq, ite_not, hammingDist] using
      (Finset.sum_boole (fun x : V => p x ≠ q x) (Finset.univ : Finset V))
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f (p x) - f x) ^ 2) ≤
        ∑ x : V,
          ((f (q x) - f x) ^ 2 +
            if p x = q x then 0 else 1) :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x : V, (f (q x) - f x) ^ 2) +
          (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
      rw [Finset.sum_add_distrib, hindicator]

private theorem squaredPermutationEnergy_tendsto_of_normalizedHamming
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hd : Tendsto
      (fun n => normalizedHamming (p n) (q n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n) +
          normalizedHamming (p n) (q n))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hq.add hd
  refine squeeze_zero (fun n =>
    div_nonneg (squaredPermutationEnergy_nonneg (f n) (p n))
      (Nat.cast_nonneg _)) ?_ hupper
  intro n
  have he := squaredPermutationEnergy_le_add_hammingDist
    (f n) (hf0 n) (hf1 n) (p n) (q n)
  calc
    squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n) ≤
      (squaredPermutationEnergy (f n) (q n) +
        (hammingDist (fun x => p n x) (fun x => q n x) : ℝ)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right he (Nat.cast_nonneg _)
    _ = squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n) +
        normalizedHamming (p n) (q n) := by
      rw [add_div]
      rfl

private theorem squaredPermutationEnergy_mul_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hp : Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n * q n) /
        Fintype.card (V n)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n =>
        2 * (squaredPermutationEnergy (f n) (p n) /
          Fintype.card (V n)) +
        2 * (squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (Filter.Tendsto.const_mul (2 : ℝ) hp).add (Filter.Tendsto.const_mul (2 : ℝ) hq)
  refine squeeze_zero (fun n =>
    div_nonneg (squaredPermutationEnergy_nonneg (f n) (p n * q n))
      (Nat.cast_nonneg _)) ?_ hupper
  intro n
  calc
    squaredPermutationEnergy (f n) (p n * q n) /
        Fintype.card (V n) ≤
      (2 * squaredPermutationEnergy (f n) (p n) +
        2 * squaredPermutationEnergy (f n) (q n)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right
        (squaredPermutationEnergy_mul_le (f n) (p n) (q n))
        (Nat.cast_nonneg _)
    _ = 2 * (squaredPermutationEnergy (f n) (p n) /
          Fintype.card (V n)) +
        2 * (squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n)) := by ring

private theorem sofic_action_inverse_normalizedHamming_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (g : G) :
    Tendsto
      (fun n =>
        normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)))
      atTop (𝓝 0) := by
  have heq :
      (fun n =>
        normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))) =
        (fun n =>
          normalizedHamming
            ((A.model n).action (g * g⁻¹))
            ((A.model n).action g *
              (A.model n).action (g⁻¹))) := by
    funext n
    calc
      normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)) =
        normalizedHamming
          ((A.model n).action g *
            ((A.model n).action g)⁻¹)
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) :=
        (normalizedHamming_mul_left
          ((A.model n).action g)
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))).symm
      _ = normalizedHamming
          ((A.model n).action (g * g⁻¹))
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) := by
        simp only [mul_inv_cancel, (A.model n).map_one]
  rw [heq]
  exact A.multiplicative g (g⁻¹)

private theorem sofic_action_squared_energy_mul
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (g h : G)
    (hg : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action g) /
          (A.model n).size) atTop (𝓝 0))
    (hh : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action h) /
          (A.model n).size) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action (g * h)) /
          (A.model n).size) atTop (𝓝 0) := by
  have hproduct : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n)
          ((A.model n).action g * (A.model n).action h) /
          (A.model n).size) atTop (𝓝 0) := by
    simpa only [Fintype.card_fin] using
      (squaredPermutationEnergy_mul_tendsto_zero
        (fun n => Fin (A.model n).size) f
        (fun n => (A.model n).action g)
        (fun n => (A.model n).action h)
        (by simpa only [Fintype.card_fin] using hg)
        (by simpa only [Fintype.card_fin] using hh))
  simpa only [Fintype.card_fin] using
    (squaredPermutationEnergy_tendsto_of_normalizedHamming
      (fun n => Fin (A.model n).size) f hf0 hf1
      (fun n => (A.model n).action (g * h))
      (fun n => (A.model n).action g * (A.model n).action h)
      (by simpa only [Fintype.card_fin] using hproduct)
      (A.multiplicative g h))

private theorem sofic_action_squared_energy_inv
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (g : G)
    (hg : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action g) /
          (A.model n).size) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action (g⁻¹)) /
          (A.model n).size) atTop (𝓝 0) := by
  have htrue : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) (((A.model n).action g)⁻¹) /
          (A.model n).size) atTop (𝓝 0) := by
    simpa only [squaredPermutationEnergy_inv] using hg
  have hd : Tendsto
      (fun n =>
        normalizedHamming
          ((A.model n).action (g⁻¹))
          (((A.model n).action g)⁻¹)) atTop (𝓝 0) := by
    have heq :
        (fun n =>
          normalizedHamming
            ((A.model n).action (g⁻¹))
            (((A.model n).action g)⁻¹)) =
          (fun n =>
            normalizedHamming
              (((A.model n).action g)⁻¹)
              ((A.model n).action (g⁻¹))) := by
      funext n
      exact normalizedHamming_comm _ _
    rw [heq]
    exact sofic_action_inverse_normalizedHamming_tendsto_zero A g
  simpa only [Fintype.card_fin] using
    (squaredPermutationEnergy_tendsto_of_normalizedHamming
      (fun n => Fin (A.model n).size) f hf0 hf1
      (fun n => (A.model n).action (g⁻¹))
      (fun n => ((A.model n).action g)⁻¹)
      (by simpa only [Fintype.card_fin] using htrue) hd)

private theorem action_energy_tendsto_zero_of_positive_generator_sum
    {G ι : Type*} [Group G] [Fintype ι]
    (A : SoficApproximation G)
    (s : ι → G)
    (hgenerate : Subgroup.closure (Set.range s) = ⊤)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (hpositive : Tendsto
      (fun n =>
        (∑ i : ι,
          squaredPermutationEnergy (f n)
            ((A.model n).action (s i))) /
          (A.model n).size) atTop (𝓝 0)) :
    ∀ g : G,
      Tendsto
        (fun n =>
          squaredPermutationEnergy (f n) ((A.model n).action g) /
            (A.model n).size) atTop (𝓝 0) := by
  classical
  have hsingle (i : ι) :
      Tendsto
        (fun n =>
          squaredPermutationEnergy (f n) ((A.model n).action (s i)) /
            (A.model n).size) atTop (𝓝 0) := by
    refine squeeze_zero (fun n =>
      div_nonneg
        (squaredPermutationEnergy_nonneg (f n)
          ((A.model n).action (s i)))
        (Nat.cast_nonneg _)) ?_ hpositive
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.single_le_sum
      (fun j _ => squaredPermutationEnergy_nonneg
        (f n) ((A.model n).action (s j)))
      (Finset.mem_univ i)
  intro g
  have hg : g ∈ Subgroup.closure (Set.range s) := by
    rw [hgenerate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hsingle i
  | one =>
      have heq :
          (fun n =>
            squaredPermutationEnergy (f n) ((A.model n).action 1) /
              (A.model n).size) =
            (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        simp only [squaredPermutationEnergy, (A.model n).map_one, Equiv.Perm.coe_one, id_eq,
          sub_self, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_div]
      rw [heq]
      exact tendsto_const_nhds
  | mul x y _ _ hx hy =>
      exact sofic_action_squared_energy_mul A f hf0 hf1 x y hx hy
  | inv x _ hx =>
      exact sofic_action_squared_energy_inv A f hf0 hf1 x hx

public
theorem sum_action_energy_tendsto_zero_of_positive_generator_sum
    {G ι : Type*} [Group G] [Fintype ι]
    (A : SoficApproximation G)
    (s : ι → G)
    (hgenerate : Subgroup.closure (Set.range s) = ⊤)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (hpositive : Tendsto
      (fun n =>
        (∑ i : ι,
          squaredPermutationEnergy (f n)
            ((A.model n).action (s i))) /
          (A.model n).size) atTop (𝓝 0))
    (S : Finset G) :
    Tendsto
      (fun n =>
        (∑ g ∈ S,
          squaredPermutationEnergy (f n) ((A.model n).action g)) /
          (A.model n).size) atTop (𝓝 0) := by
  have hall := action_energy_tendsto_zero_of_positive_generator_sum
    A s hgenerate f hf0 hf1 hpositive
  have hsum : Tendsto
      (fun n =>
        ∑ g ∈ S,
          squaredPermutationEnergy (f n) ((A.model n).action g) /
            (A.model n).size) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum S (fun g _ => hall g)
  simpa only [Finset.sum_div] using hsum

end KunPositiveWordMidrankEnergy

namespace KunAdditiveMedianPoincare

open CheegerPoincare
open Filter Topology
open scoped BigOperators

private def permutationRealVariation
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) : ℝ :=
  ∑ i : ι, ∑ x : V, |f (σ i x) - f x|

private theorem sum_indicator_real_eq_mul_card
    {V : Type*} (A : Finset V)
    (q : V → Prop) [DecidablePred q] (m : ℝ) :
    (∑ x ∈ A, if q x then m else 0) =
      m * (A.filter q).card := by
  calc
    (∑ x ∈ A, if q x then m else 0) =
        m * (∑ x ∈ A, if q x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = m * (A.filter q).card := by
          congr 1
          exact Finset.sum_boole (R := ℝ) q A

private theorem permutationRealVariation_subtract_layer
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (A : Finset V) (m : ℝ) (hm : 0 ≤ m)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationRealVariation σ f =
      permutationRealVariation σ
        (fun x => if x ∈ A then f x - m else 0) +
        2 * m * (boundary σ A : ℝ) := by
  classical
  let g : V → ℝ := fun x => if x ∈ A then f x - m else 0
  have hpair (i : ι) (x : V) :
      |f (σ i x) - f x| =
        |g (σ i x) - g x| +
          (if x ∈ A ∧ σ i x ∉ A then m else 0) +
          (if x ∉ A ∧ σ i x ∈ A then m else 0) := by
    by_cases hx : x ∈ A
    · by_cases hy : σ i x ∈ A
      · simp only [hy, ↓reduceIte, hx, sub_sub_sub_cancel_right, not_true_eq_false, and_false,
        add_zero, and_true, g]
      · have hyzero := houtside (σ i x) hy
        have hxnonnegative : 0 ≤ f x := hm.trans (hinside x hx)
        simp only [hyzero, zero_sub, abs_neg, abs_of_nonneg hxnonnegative, hy, ↓reduceIte, hx,
          neg_sub,
          abs_of_nonpos (sub_nonpos.mpr (hinside x hx)), not_false_eq_true, and_self,
            sub_add_cancel, not_true_eq_false,
          add_zero, g]
    · by_cases hy : σ i x ∈ A
      · have hxzero := houtside x hx
        have hynonnegative : 0 ≤ f (σ i x) :=
          hm.trans (hinside (σ i x) hy)
        have hysub : 0 ≤ f (σ i x) - m :=
          sub_nonneg.mpr (hinside (σ i x) hy)
        simp only [hxzero, sub_zero, abs_of_nonneg hynonnegative, hy, ↓reduceIte, hx, abs_of_nonneg
          hysub,
          not_true_eq_false, and_self, add_zero, not_false_eq_true, sub_add_cancel, g]
      · simp only [houtside (σ i x) hy, houtside x hx, sub_self, abs_zero, hy, ↓reduceIte, hx,
        not_false_eq_true,
          and_true, add_zero, and_false, g]
  have hone (i : ι) :
      (∑ x : V, |f (σ i x) - f x|) =
        (∑ x : V, |g (σ i x) - g x|) +
          2 * m * (A.filter fun x => σ i x ∉ A).card := by
    have hexit :
        (∑ x : V, if x ∈ A ∧ σ i x ∉ A then m else 0) =
          m * (A.filter fun x => σ i x ∉ A).card := by
      have hset :
          Finset.univ.filter
            (fun x : V => x ∈ A ∧ σ i x ∉ A) =
              A.filter fun x => σ i x ∉ A := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hset] using
        sum_indicator_real_eq_mul_card Finset.univ
          (fun x : V => x ∈ A ∧ σ i x ∉ A) m
    have henter :
        (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) =
          m * (Finset.univ.filter fun x =>
            x ∉ A ∧ σ i x ∈ A).card :=
      sum_indicator_real_eq_mul_card
        Finset.univ (fun x => x ∉ A ∧ σ i x ∈ A) m
    calc
      (∑ x : V, |f (σ i x) - f x|) =
          ∑ x : V,
            (|g (σ i x) - g x| +
              (if x ∈ A ∧ σ i x ∉ A then m else 0) +
              (if x ∉ A ∧ σ i x ∈ A then m else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hpair i x
      _ = (∑ x : V, |g (σ i x) - g x|) +
            (∑ x : V,
              if x ∈ A ∧ σ i x ∉ A then m else 0) +
            (∑ x : V,
              if x ∉ A ∧ σ i x ∈ A then m else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ x : V, |g (σ i x) - g x|) +
            m * (A.filter fun x => σ i x ∉ A).card +
            m * (Finset.univ.filter fun x =>
              x ∉ A ∧ σ i x ∈ A).card := by
            rw [hexit, henter]
      _ = (∑ x : V, |g (σ i x) - g x|) +
            2 * m * (A.filter fun x => σ i x ∉ A).card := by
            have hcross :
                (Finset.univ.filter fun x =>
                  x ∉ A ∧ σ i x ∈ A).card =
                  (A.filter fun x => σ i x ∉ A).card :=
              KunThomFiberCoarea.card_entering_eq_card_exiting
                (σ i) A
            rw [hcross]
            ring
  unfold permutationRealVariation boundary
  calc
    (∑ i : ι, ∑ x : V, |f (σ i x) - f x|) =
        ∑ i : ι,
          ((∑ x : V, |g (σ i x) - g x|) +
            2 * m * (A.filter fun x => σ i x ∉ A).card) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hone i
    _ = (∑ i : ι, ∑ x : V, |g (σ i x) - g x|) +
          2 * m *
            (∑ i : ι, (A.filter fun x => σ i x ∉ A).card) := by
          push_cast
          simp only [Finset.sum_add_distrib, Finset.mul_sum]

private theorem additive_permutation_small_support_coarea
    {V ι : Type*} [Fintype V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ) + ε)
    (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ M)
    (hhalf :
      2 * (CheegerPoincare.positiveSupport f).card ≤
        Fintype.card V) :
    2 * γ * (∑ x : V, f x) ≤
      permutationRealVariation σ f + 2 * ε * M := by
  classical
  generalize hn :
    (CheegerPoincare.positiveSupport f).card = n
  induction n using Nat.strong_induction_on generalizing f M with
  | h n ih =>
    by_cases hnonempty :
        (CheegerPoincare.positiveSupport f).Nonempty
    · let A : Finset V :=
        CheegerPoincare.positiveSupport f
      have hA : A.Nonempty := hnonempty
      have himage : (A.image f).Nonempty :=
        Finset.image_nonempty.mpr hA
      let m : ℝ := (A.image f).min' himage
      have hmem : m ∈ A.image f := Finset.min'_mem _ _
      obtain ⟨z, hzA, hzm⟩ := Finset.mem_image.mp hmem
      have hmpos : 0 < m := by
        rw [← hzm]
        exact
          (CheegerPoincare.mem_positiveSupport f z).mp hzA
      have hmle : ∀ x ∈ A, m ≤ f x := by
        intro x hx
        exact Finset.min'_le (A.image f) (f x)
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hmM : m ≤ M := by
        rw [← hzm]
        exact hfM z
      let g : V → ℝ := fun x =>
        if x ∈ A then f x - m else 0
      have hgnonnegative : ∀ x, 0 ≤ g x := by
        intro x
        by_cases hx : x ∈ A
        · simpa [g, hx] using sub_nonneg.mpr (hmle x hx)
        · simp only [hx, ↓reduceIte, Std.le_refl, g]
      have hgupper : ∀ x, g x ≤ M - m := by
        intro x
        by_cases hx : x ∈ A
        · simp only [g, ite_eq_left hx]
          linarith [hfM x]
        · simp only [g, ite_eq_right hx]
          linarith
      have hgsub :
          CheegerPoincare.positiveSupport g ⊆ A := by
        intro x hx
        have hpositive :=
          (CheegerPoincare.mem_positiveSupport g x).mp hx
        by_contra hxA
        simp only [hxA, ↓reduceIte, lt_self_iff_false, g] at hpositive
      have hznot :
          z ∉ CheegerPoincare.positiveSupport g := by
        intro hz
        have hpositive :=
          (CheegerPoincare.mem_positiveSupport g z).mp hz
        have hzero : g z = 0 := by
          simp only [hzA, ↓reduceIte, hzm, sub_self, g]
        simp only [hzero, lt_self_iff_false] at hpositive
      have hstrict :
          CheegerPoincare.positiveSupport g ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hgsub, ?_⟩
        intro heq
        exact hznot (heq.symm ▸ hzA)
      have hgcard :
          (CheegerPoincare.positiveSupport g).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hstrict
      have hghalf :
          2 * (CheegerPoincare.positiveSupport g).card ≤
            Fintype.card V :=
        (Nat.mul_le_mul_left 2 (Finset.card_le_card hgsub)).trans hhalf
      have hgbound :
          2 * γ * (∑ x : V, g x) ≤
            permutationRealVariation σ g + 2 * ε * (M - m) :=
        ih (CheegerPoincare.positiveSupport g).card
          hgcard g (M - m) (sub_nonneg.mpr hmM)
          hgnonnegative hgupper hghalf rfl
      have hhalfre : (2 : ℝ) * A.card ≤ Fintype.card V := by
        exact_mod_cast hhalf
      have hmin :
          (A.card : ℝ) ≤ (Fintype.card V : ℝ) - A.card := by
        linarith
      have hcut :
          γ * (A.card : ℝ) ≤
            (boundary σ A : ℝ) + ε := by
        simpa only [min_eq_left hmin] using hexp A
      have houtside : ∀ x, x ∉ A → f x = 0 := by
        intro x hx
        have hnot : ¬ 0 < f x := by
          intro hpositive
          exact hx
            ((CheegerPoincare.mem_positiveSupport f x).mpr
              hpositive)
        exact le_antisymm (le_of_not_gt hnot) (hf x)
      have hsumindicator :
          (∑ x : V, if x ∈ A then m else 0) =
            m * (A.card : ℝ) := by
        simpa only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
          Finset.subset_univ,
          Finset.filter_mem_eq_of_subset] using sum_indicator_real_eq_mul_card Finset.univ (fun x :
            V => x ∈ A) m
      have hsum :
          (∑ x : V, f x) =
            (∑ x : V, g x) + m * (A.card : ℝ) := by
        calc
          (∑ x : V, f x) =
              ∑ x : V,
                (g x + if x ∈ A then m else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x ∈ A
              · simp only [hx, ↓reduceIte, sub_add_cancel, g]
              · simp only [houtside x hx, hx, ↓reduceIte, add_zero, g]
          _ = (∑ x : V, g x) +
              (∑ x : V, if x ∈ A then m else 0) := by
              rw [Finset.sum_add_distrib]
          _ = (∑ x : V, g x) + m * (A.card : ℝ) := by
              rw [hsumindicator]
      have hvariation :
          permutationRealVariation σ f =
            permutationRealVariation σ g +
              2 * m * (boundary σ A : ℝ) :=
        permutationRealVariation_subtract_layer
          σ f A m hmpos.le hmle houtside
      have hscaled :=
        mul_le_mul_of_nonneg_left hcut
          (show 0 ≤ 2 * m by positivity)
      rw [hsum, hvariation]
      linarith only [hgbound, hscaled]
    · have hzero : ∀ x, f x = 0 := by
        intro x
        have hx : ¬ 0 < f x := by
          intro hpositive
          apply hnonempty
          exact ⟨x,
            (CheegerPoincare.mem_positiveSupport f x).mpr
              hpositive⟩
        exact le_antisymm (le_of_not_gt hx) (hf x)
      simp only [hzero, Finset.sum_const_zero, mul_zero, permutationRealVariation, sub_self,
        abs_zero, zero_add,
        ge_iff_le]
      positivity

private theorem positive_negative_abs_eq (a b : ℝ) :
    |max a 0 - max b 0| +
      |max (-a) 0 - max (-b) 0| = |a - b| := by
  rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
    simp only [max_eq_left, max_eq_right, ha, hb, neg_nonneg, neg_nonpos,
      sub_zero, zero_sub, sub_self, abs_zero, add_zero, zero_add, abs_neg,
      neg_sub_neg]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    ring
  · rw [abs_of_nonneg hb, abs_of_nonpos ha,
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring
  · exact abs_sub_comm b a

private theorem permutationRealVariation_positive_negative
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (m : ℝ) :
    permutationRealVariation σ (fun x => max (f x - m) 0) +
      permutationRealVariation σ (fun x => max (m - f x) 0) =
        permutationRealVariation σ f := by
  unfold permutationRealVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hx : m - f x = -(f x - m) := by ring
  have hy : m - f (σ i x) = -(f (σ i x) - m) := by ring
  have hxy :
      (f (σ i x) - m) - (f x - m) = f (σ i x) - f x := by
    ring
  simpa only [hx, hy, hxy] using
    positive_negative_abs_eq (f (σ i x) - m) (f x - m)

private theorem exists_bounded_finite_real_median
    {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      2 * (CheegerPoincare.lowerLevel f m).card ≤
          Fintype.card V ∧
      2 * (CheegerPoincare.upperLevel f m).card ≤
          Fintype.card V := by
  classical
  obtain ⟨m, hbelow, habove⟩ :=
    CheegerPoincare.exists_finite_real_median f
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr
    (inferInstance : Nonempty V)
  have hm_nonnegative : 0 ≤ m := by
    by_contra hnot
    have hm_negative : m < 0 := lt_of_not_ge hnot
    have hupper :
        CheegerPoincare.upperLevel f m =
          (Finset.univ : Finset V) := by
      ext x
      simp only [CheegerPoincare.mem_upperLevel,
        Finset.mem_univ, iff_true]
      exact hm_negative.trans_le (hf x)
    rw [hupper, Finset.card_univ] at habove
    omega
  have hm_one : m ≤ 1 := by
    by_contra hnot
    have hm_greater : 1 < m := lt_of_not_ge hnot
    have hlower :
        CheegerPoincare.lowerLevel f m =
          (Finset.univ : Finset V) := by
      ext x
      simp only [CheegerPoincare.mem_lowerLevel,
        Finset.mem_univ, iff_true]
      exact (hf_one x).trans_lt hm_greater
    rw [hlower, Finset.card_univ] at hbelow
    omega
  exact ⟨m, hm_nonnegative, hm_one, hbelow, habove⟩

private theorem additive_permutation_median_absolute_deviation
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      2 * γ * (∑ x : V, |f x - m|) ≤
        permutationRealVariation σ f + 4 * ε := by
  classical
  obtain ⟨m, hm_nonnegative, hm_one, hbelow, habove⟩ :=
    exists_bounded_finite_real_median f hf hf_one
  let p : V → ℝ := fun x => max (f x - m) 0
  let q : V → ℝ := fun x => max (m - f x) 0
  have hp_nonnegative : ∀ x, 0 ≤ p x := by
    intro x
    exact le_max_right _ _
  have hq_nonnegative : ∀ x, 0 ≤ q x := by
    intro x
    exact le_max_right _ _
  have hp_one : ∀ x, p x ≤ 1 := by
    intro x
    apply max_le
    · linarith [hf_one x]
    · norm_num
  have hq_one : ∀ x, q x ≤ 1 := by
    intro x
    apply max_le
    · linarith [hf x]
    · norm_num
  have hp_half :
      2 * (CheegerPoincare.positiveSupport p).card ≤
        Fintype.card V := by
    simpa only [p, CheegerPoincare.positiveSupport_max_sub]
      using habove
  have hq_half :
      2 * (CheegerPoincare.positiveSupport q).card ≤
        Fintype.card V := by
    simpa only [q,
      CheegerPoincare.positiveSupport_max_sub_reverse]
      using hbelow
  have hp_coarea := additive_permutation_small_support_coarea
    σ γ ε hε hexp p 1 (by norm_num) hp_nonnegative hp_one hp_half
  have hq_coarea := additive_permutation_small_support_coarea
    σ γ ε hε hexp q 1 (by norm_num) hq_nonnegative hq_one hq_half
  have hvariation :
      permutationRealVariation σ p +
        permutationRealVariation σ q =
          permutationRealVariation σ f := by
    simpa only [p, q] using
      permutationRealVariation_positive_negative σ f m
  have hpoint (x : V) : p x + q x = |f x - m| := by
    dsimp [p, q]
    rcases le_total m (f x) with hx | hx
    · rw [max_eq_left (sub_nonneg.mpr hx),
        max_eq_right (sub_nonpos.mpr hx),
        abs_of_nonneg (sub_nonneg.mpr hx)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr hx),
        max_eq_left (sub_nonneg.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr hx)]
      ring
  have hmass :
      (∑ x : V, p x) + (∑ x : V, q x) =
        ∑ x : V, |f x - m| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact hpoint x
  refine ⟨m, hm_nonnegative, hm_one, ?_⟩
  rw [← hmass, ← hvariation]
  nlinarith [hp_coarea, hq_coarea]

private theorem additive_permutation_median_variance
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    2 * γ *
        (∑ x : V,
          (f x - CheegerPoincare.finiteMean f) ^ 2) ≤
      permutationRealVariation σ f + 4 * ε := by
  obtain ⟨m, hm_nonnegative, hm_one, hmedian⟩ :=
    additive_permutation_median_absolute_deviation
      σ γ ε hε hexp f hf hf_one
  have hpoint (x : V) : (f x - m) ^ 2 ≤ |f x - m| := by
    have hlower : -1 ≤ f x - m := by
      linarith [hf x]
    have hupper : f x - m ≤ 1 := by
      linarith [hf_one x]
    rcases le_total 0 (f x - m) with hx | hx
    · rw [abs_of_nonneg hx]
      nlinarith
    · rw [abs_of_nonpos hx]
      nlinarith
  have hsq :
      (∑ x : V, (f x - m) ^ 2) ≤
        ∑ x : V, |f x - m| := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hmean :=
    CheegerPoincare.sum_sq_sub_finiteMean_le f m
  have hfactor : 0 ≤ 2 * γ := mul_nonneg (by norm_num) hγ
  calc
    2 * γ *
        (∑ x : V,
          (f x - CheegerPoincare.finiteMean f) ^ 2) ≤
        2 * γ * (∑ x : V, (f x - m) ^ 2) :=
      mul_le_mul_of_nonneg_left hmean hfactor
    _ ≤ 2 * γ * (∑ x : V, |f x - m|) :=
      mul_le_mul_of_nonneg_left hsq hfactor
    _ ≤ permutationRealVariation σ f + 4 * ε := hmedian

private theorem additive_permutation_finiteVariance
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    2 * γ * (Fintype.card V : ℝ) *
        CheegerPoincare.finiteVariance f ≤
      permutationRealVariation σ f + 4 * ε := by
  have hvariance := additive_permutation_median_variance
    σ γ ε hγ hε hexp f hf hf_one
  rw [← CheegerPoincare.card_mul_finiteVariance f]
    at hvariance
  nlinarith

end KunAdditiveMedianPoincare

namespace KunCompletedComponentMidrankVariation

open Filter Topology
open scoped BigOperators

private def permutationRealVariation
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) : ℝ :=
  ∑ i : ι, ∑ x : V, |f (σ i x) - f x|

private theorem permutationRealVariation_sq_le_card_mul_energy
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    permutationRealVariation σ f ^ 2 ≤
      ((Fintype.card ι : ℝ) * Fintype.card V) *
        (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (ι × V))
    (fun _ : ι × V => (1 : ℝ))
    (fun z : ι × V => |f (σ z.1 z.2) - f z.2|)
  simpa only [one_mul, one_pow, sq_abs,
    ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_const_zero, Finset.sum_const, Finset.card_product,
    Finset.card_univ, Nat.cast_mul, nsmul_eq_mul, mul_one,
    permutationRealVariation] using h

private theorem normalized_permutationRealVariation_tendsto_zero_of_energy
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (ι : Type*) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (f : (n : ℕ) → V n → ℝ)
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (f n (σ n i x) - f n x) ^ 2) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        permutationRealVariation (σ n) (f n) /
          (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hupper (n : ℕ) :
      permutationRealVariation (σ n) (f n) /
          (Fintype.card (V n) : ℝ) ≤
        Real.sqrt
          ((Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    calc
      (permutationRealVariation (σ n) (f n) /
        (Fintype.card (V n) : ℝ)) ^ 2 =
          permutationRealVariation (σ n) (f n) ^ 2 /
            (Fintype.card (V n) : ℝ) ^ 2 := by
              ring
      _ ≤
          (((Fintype.card ι : ℝ) * Fintype.card (V n)) *
            (∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2)) /
            (Fintype.card (V n) : ℝ) ^ 2 := by
              exact div_le_div_of_nonneg_right
                (permutationRealVariation_sq_le_card_mul_energy
                  (σ n) (f n))
                (sq_nonneg (Fintype.card (V n) : ℝ))
      _ = (Fintype.card ι : ℝ) *
          ((∑ i : ι, ∑ x : V n,
            (f n (σ n i x) - f n x) ^ 2) /
              (Fintype.card (V n) : ℝ)) := by
            field_simp [ne_of_gt (hN n)]
  have hroot : Tendsto
      (fun n =>
        Real.sqrt
          ((Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ))))
      atTop (nhds 0) := by
    have hscaled : Tendsto
        (fun n =>
          (Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using henergy.const_mul (Fintype.card ι : ℝ)
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hscaled
  apply squeeze_zero'
    (Eventually.of_forall (fun n => ?_))
    (Eventually.of_forall hupper)
    hroot
  apply div_nonneg _ (hN n).le
  unfold permutationRealVariation
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem sum_partition_parts_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) (f : V → ℝ) :
    (∑ C ∈ P.parts, ∑ x ∈ C, f x) = ∑ x : V, f x := by
  classical
  calc
    (∑ C ∈ P.parts, ∑ x ∈ C, f x) =
        ∑ x ∈ P.parts.biUnion id, f x := by
          symm
          exact Finset.sum_biUnion P.disjoint
    _ = ∑ x : V, f x := by rw [P.biUnion_parts]

private theorem completed_component_real_variation_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V)
    (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    permutationRealVariation τ (fun x => f (x : V)) ≤
      (∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
        (boundary σ C : ℝ) := by
  classical
  have hunit (x y : V) : |f x - f y| ≤ (1 : ℝ) := by
    apply (abs_le).2
    constructor <;> linarith [hf0 x, hf0 y, hf1 x, hf1 y]
  have hpoint (i : ι) (x : {x : V // x ∈ C}) :
      |f ((τ i x : {x : V // x ∈ C}) : V) - f (x : V)| ≤
        |f (σ i (x : V)) - f (x : V)| +
          if σ i (x : V) ∈ C then 0 else 1 := by
    by_cases hinside : σ i (x : V) ∈ C
    · simp only [ite_eq_left hinside, add_zero]
      rw [hτ i (x : V) x.property hinside]
    · simp only [ite_eq_right hinside]
      linarith [hunit
        ((τ i x : {x : V // x ∈ C}) : V) (x : V),
        abs_nonneg (f (σ i (x : V)) - f (x : V))]
  calc
    permutationRealVariation τ (fun x => f (x : V)) ≤
        ∑ i : ι, ∑ x : {x : V // x ∈ C},
          (|f (σ i (x : V)) - f (x : V)| +
            if σ i (x : V) ∈ C then 0 else 1) := by
          unfold permutationRealVariation
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro x _
          exact hpoint i x
    _ = ∑ i : ι,
          ((∑ x ∈ C, |f (σ i x) - f x|) +
            ((C.filter fun x => σ i x ∉ C).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib]
          have horiginal :
              (∑ x : {x : V // x ∈ C},
                |f (σ i (x : V)) - f (x : V)|) =
                ∑ x ∈ C, |f (σ i x) - f x| :=
            (Finset.sum_subtype C (fun _ => Iff.rfl)
              (fun x : V => |f (σ i x) - f x|)).symm
          have hmiss :
              (∑ x : {x : V // x ∈ C},
                if σ i (x : V) ∈ C then (0 : ℝ) else 1) =
                ((C.filter fun x => σ i x ∉ C).card : ℝ) := by
            calc
              (∑ x : {x : V // x ∈ C},
                if σ i (x : V) ∈ C then (0 : ℝ) else 1) =
                  ∑ x ∈ C,
                    if σ i x ∈ C then (0 : ℝ) else 1 :=
                (Finset.sum_subtype C (fun _ => Iff.rfl)
                  (fun x : V => if σ i x ∈ C then (0 : ℝ) else 1)).symm
              _ = ((C.filter fun x => σ i x ∉ C).card : ℝ) := by
                simpa only [ite_not] using
                  (Finset.sum_boole (R := ℝ)
                    (fun x : V => σ i x ∉ C) C)
          rw [horiginal, hmiss]
    _ = (∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
          (boundary σ C : ℝ) := by
          simp only [Finset.sum_add_distrib, boundary, Nat.cast_sum]

private theorem sum_completed_component_real_variation_le
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    (∑ C ∈ P.parts,
      permutationRealVariation (τ C) (fun x => f (x : V))) ≤
      permutationRealVariation σ f +
        ∑ C ∈ P.parts, (boundary σ C : ℝ) := by
  classical
  have hparts :
      (∑ C ∈ P.parts, ∑ i : ι, ∑ x ∈ C,
        |f (σ i x) - f x|) =
        permutationRealVariation σ f := by
    unfold permutationRealVariation
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_partition_parts_eq P
      (fun x : V => |f (σ i x) - f x|)
  calc
    (∑ C ∈ P.parts,
      permutationRealVariation (τ C) (fun x => f (x : V))) ≤
        ∑ C ∈ P.parts,
          ((∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
            (boundary σ C : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          exact completed_component_real_variation_le
            σ C (τ C) (hτ C hC) f hf0 hf1
    _ = permutationRealVariation σ f +
          ∑ C ∈ P.parts, (boundary σ C : ℝ) := by
          rw [Finset.sum_add_distrib, hparts]

end KunCompletedComponentMidrankVariation

open KunCompletedComponentMidrankVariation

namespace KunGlobalActualAdditiveMidrankVariance

open Filter Topology
open scoped BigOperators

private theorem weighted_component_midrankVariance_additive_bound
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (hexpand : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary σ E : ℝ))
    (b : V → ℤ) :
    2 * γ *
        (∑ C ∈ P.parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C b)) ≤
      KunCompletedComponentMidrankVariation.permutationRealVariation
        σ (MidrankPermutationEnergy.partitionVertexMidrank P b) +
        5 * (∑ C ∈ P.parts, (boundary σ C : ℝ)) := by
  classical
  let f : V → ℝ :=
    MidrankPermutationEnergy.partitionVertexMidrank P b
  have hf0 (x : V) : 0 ≤ f x :=
    componentVertexMidrank_nonneg (P.part x) b x
  have hf1 (x : V) : f x ≤ 1 :=
    componentVertexMidrank_le_one (P.part x) b x
  have hcomponent (C : Finset V) (hC : C ∈ P.parts) :
      2 * γ * (C.card : ℝ) *
          midrankVariance
            (componentRankMassList C b) ≤
        KunCompletedComponentMidrankVariation.permutationRealVariation
          (τ C) (fun x : {x : V // x ∈ C} => f (x : V)) +
          4 * (boundary σ C : ℝ) := by
    have hCne : C.Nonempty := P.nonempty_of_mem_parts hC
    let : Nonempty {x : V // x ∈ C} :=
      ⟨⟨hCne.choose, hCne.choose_spec⟩⟩
    have hrestrict :
        (fun x : {x : V // x ∈ C} => f (x : V)) =
          (fun x : {x : V // x ∈ C} =>
            componentVertexMidrank C b (x : V)) := by
      funext x
      change
        componentVertexMidrank (P.part (x : V)) b (x : V) =
          componentVertexMidrank C b (x : V)
      rw [P.part_eq_of_mem hC x.property]
    have hcut (E : Finset {x : V // x ∈ C}) :
        γ * min (E.card : ℝ)
            ((Fintype.card {x : V // x ∈ C} : ℝ) - E.card) ≤
          (boundary (τ C) E : ℝ) +
            (boundary σ C : ℝ) := by
      have h :=
        KunResidualExpanderDecomposition.completed_component_additive_expansion
          σ C (τ C) (hτ C hC) γ (hexpand C hC) E
      have h' :
          γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) ≤
            (boundary (τ C) E : ℝ) +
              (boundary σ C : ℝ) := by
        linarith
      simpa only [Fintype.card_coe] using h'
    have hp :=
      KunAdditiveMedianPoincare.additive_permutation_finiteVariance
        (τ C) γ (boundary σ C : ℝ)
        hγ (Nat.cast_nonneg _) hcut
        (fun x : {x : V // x ∈ C} =>
          componentVertexMidrank C b (x : V))
        (fun x => componentVertexMidrank_nonneg C b (x : V))
        (fun x => componentVertexMidrank_le_one C b (x : V))
    rw [Fintype.card_coe,
      ComponentMidrankVariance.componentVertexMidrank_finiteVariance_eq
        C b hCne] at hp
    rw [← hrestrict] at hp
    simpa only
      [KunAdditiveMedianPoincare.permutationRealVariation,
       KunCompletedComponentMidrankVariation.permutationRealVariation]
      using hp
  have hsummed :
      2 * γ *
          (∑ C ∈ P.parts,
            (C.card : ℝ) *
              midrankVariance
                (componentRankMassList C b)) ≤
        (∑ C ∈ P.parts,
          KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V))) +
          4 * (∑ C ∈ P.parts, (boundary σ C : ℝ)) := by
    calc
      2 * γ *
          (∑ C ∈ P.parts,
            (C.card : ℝ) *
              midrankVariance
                (componentRankMassList C b)) =
        ∑ C ∈ P.parts,
          2 * γ * (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C b) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C _
              ring
      _ ≤ ∑ C ∈ P.parts,
          (KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V)) +
            4 * (boundary σ C : ℝ)) := by
              apply Finset.sum_le_sum
              intro C hC
              exact hcomponent C hC
      _ = (∑ C ∈ P.parts,
          KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V))) +
          4 * (∑ C ∈ P.parts, (boundary σ C : ℝ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcompletion :=
    KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
      P σ τ hτ f hf0 hf1
  change
    2 * γ *
        (∑ C ∈ P.parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C b)) ≤
      KunCompletedComponentMidrankVariation.permutationRealVariation
        σ f +
        5 * (∑ C ∈ P.parts, (boundary σ C : ℝ))
  linarith

private theorem weighted_component_midrankVariance_tendsto_zero_of_additive_expansion
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (τ : (n : ℕ) → (C : Finset (V n)) →
      ι → Equiv.Perm {x : V n // x ∈ C})
    (b : (n : ℕ) → V n → ℤ)
    (γ : ℝ) (hγ : 0 < γ)
    (hτ : ∀ n C, C ∈ (P n).parts → ∀ i (x : V n)
      (hx : x ∈ C) (_hy : σ n i x ∈ C),
      ((τ n C i ⟨x, hx⟩ : {x : V n // x ∈ C}) : V n) =
        σ n i x)
    (hexpand : ∀ n C, C ∈ (P n).parts → ∀ E : Finset (V n),
      E ⊆ C → 2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary (σ n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (boundary (σ n) C : ℝ)) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0))
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) (σ n i x) -
           MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) x) ^ 2) /
              (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
  classical
  let f : (n : ℕ) → V n → ℝ :=
    fun n =>
      MidrankPermutationEnergy.partitionVertexMidrank
        (P n) (b n)
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hvariation : Tendsto
      (fun n =>
        KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
    apply
      normalized_permutationRealVariation_tendsto_zero_of_energy
      V ι σ f
    exact henergy
  have hnonnegative : ∀ n,
      0 ≤
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ) := by
    intro n
    apply div_nonneg _ (hN n).le
    apply Finset.sum_nonneg
    intro C hC
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [← ComponentMidrankVariance.componentVertexMidrank_finiteVariance_eq
      C (b n) ((P n).nonempty_of_mem_parts hC)]
    exact CheegerPoincare.finiteVariance_nonneg _
  have hupper (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          midrankVariance
            (componentRankMassList C (b n))) /
              (Fintype.card (V n) : ℝ) ≤
        (KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ) +
          5 * ((∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) /
              (Fintype.card (V n) : ℝ))) / (2 * γ) := by
    have hfinite :=
      weighted_component_midrankVariance_additive_bound
        (P n) (σ n) (τ n) γ hγ.le (hτ n)
          (hexpand n) (b n)
    have hfinite' :=
      (div_le_div_iff_of_pos_right (hN n)).2 hfinite
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hγ)).2
    calc
      ((∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          midrankVariance
            (componentRankMassList C (b n))) /
              (Fintype.card (V n) : ℝ)) * (2 * γ) =
          (2 * γ *
            (∑ C ∈ (P n).parts,
              (C.card : ℝ) *
                midrankVariance
                  (componentRankMassList C (b n)))) /
                    (Fintype.card (V n) : ℝ) := by ring
      _ ≤
          (KunCompletedComponentMidrankVariation.permutationRealVariation
            (σ n) (f n) +
            5 * (∑ C ∈ (P n).parts,
              (boundary (σ n) C : ℝ))) /
                (Fintype.card (V n) : ℝ) := hfinite'
      _ =
          KunCompletedComponentMidrankVariation.permutationRealVariation
            (σ n) (f n) / (Fintype.card (V n) : ℝ) +
            5 * ((∑ C ∈ (P n).parts,
              (boundary (σ n) C : ℝ)) /
                (Fintype.card (V n) : ℝ)) := by ring
  have hlimit : Tendsto
      (fun n =>
        (KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ) +
          5 * ((∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) /
              (Fintype.card (V n) : ℝ))) / (2 * γ))
      atTop (nhds 0) := by
    have hsum := hvariation.add (hboundary.const_mul (5 : ℝ))
    have hscaled := hsum.mul_const ((2 * γ)⁻¹)
    simpa only [div_eq_mul_inv, zero_add, zero_mul, mul_zero] using hscaled
  exact squeeze_zero'
    (Eventually.of_forall hnonnegative)
    (Eventually.of_forall hupper)
    hlimit

public
theorem weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ)
    (γ : ℝ) (hγ : 0 < γ)
    (hexpand : ∀ n C, C ∈ (P n).parts → ∀ E : Finset (V n),
      E ⊆ C → 2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary (σ n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (boundary (σ n) C : ℝ)) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0))
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) (σ n i x) -
           MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) x) ^ 2) /
              (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
  classical
  let τ : (n : ℕ) → (C : Finset (V n)) →
      ι → Equiv.Perm {x : V n // x ∈ C} :=
    fun n C i =>
      Classical.choose
        (exists_completion_of_internal_permutation
          (σ n i) C)
  have hτ (n : ℕ) (C : Finset (V n)) (_hC : C ∈ (P n).parts)
      (i : ι) (x : V n) (hx : x ∈ C) (hy : σ n i x ∈ C) :
      ((τ n C i ⟨x, hx⟩ : {x : V n // x ∈ C}) : V n) =
        σ n i x := by
    exact Classical.choose_spec
      (exists_completion_of_internal_permutation
        (σ n i) C) x hx hy
  exact weighted_component_midrankVariance_tendsto_zero_of_additive_expansion
    V ι P σ τ b γ hγ hτ hexpand hboundary henergy

end KunGlobalActualAdditiveMidrankVariance

namespace KunCommonRankArcInvariance

open Filter Topology
open scoped BigOperators

private theorem exists_maximizing_partition_ranks
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ) :
    ∃ j : (n : ℕ) → Finset (V n) → ℤ,
      ∀ n C, C ∈ (P n).parts →
        j n C ∈ C.image (b n) ∧
          ∀ k ∈ C.image (b n),
            componentRankMass C (b n) k ≤
              componentRankMass C (b n) (j n C) := by
  classical
  let j : (n : ℕ) → Finset (V n) → ℤ := fun n C =>
    if h : C.Nonempty then
      (exists_maximal_componentRankMass
        C (b n) h).choose
    else 0
  refine ⟨j, ?_⟩
  intro n C hC
  have hn : C.Nonempty := (P n).nonempty_of_mem_parts hC
  have h := (exists_maximal_componentRankMass
    C (b n) hn).choose_spec
  simpa only [j, dite_eq_left hn] using h

private theorem maximizing_partition_rank_omitted_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (hmax : ∀ n C, C ∈ (P n).parts →
      ∀ k ∈ C.image (b n),
        componentRankMass C (b n) k ≤
          componentRankMass C (b n) (j n C))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0) := by
  classical
  have hupper : Tendsto
      (fun n =>
        (12 : ℝ) *
          ((∑ C ∈ (P n).parts,
            (C.card : ℝ) *
              midrankVariance
                (componentRankMassList C (b n))) /
                  Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).mul
          hvariance)
  refine squeeze_zero (fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hupper
  intro n
  have hfinite :=
    actual_weighted_midrank_dominant_mass_le
      (P n).parts (fun C : Finset (V n) => C) (b n) (j n)
      (fun C hC => (P n).nonempty_of_mem_parts hC)
      (fun C hC => hmax n C hC)
  have hcard :=
    RankArcCharging.card_sdiff_selectedRankSupport
      (P n) (b n) (j n)
  have hcast :
      ((((Finset.univ : Finset (V n)) \
        RankArcCharging.selectedRankSupport
          (P n) (b n) (j n)).card : ℕ) : ℝ) =
        ∑ C ∈ (P n).parts,
          (((C.card -
            (C.filter fun x => b n x = j n C).card : ℕ) : ℝ)) := by
    exact_mod_cast hcard
  calc
    ((((Finset.univ : Finset (V n)) \
      RankArcCharging.selectedRankSupport
        (P n) (b n) (j n)).card : ℝ) /
          Fintype.card (V n)) ≤
      (12 * (∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          midrankVariance
            (componentRankMassList C (b n)))) /
              Fintype.card (V n) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [hcast]
      exact hfinite
    _ = (12 : ℝ) *
        ((∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                Fintype.card (V n)) := by
      ring

private theorem rankChangingArc_density_tendsto_zero_of_selected_support
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {κ : Type*}
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (homitted : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((partitionWordCrossing
          (P n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ, Tendsto
      (fun n =>
        ((RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n))
          (b n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  intro i
  exact RankArcCharging.rankChangingArc_density_tendsto_zero
    V (fun n => (Finset.univ : Finset (V n)))
    P b j (fun n => w n i)
    (fun n => (Fintype.card (V n) : ℝ))
    (fun n => by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
    (hcross i) homitted

public
theorem exists_common_rank_invariance_of_midrank_variance
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {κ : Type*}
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C (b n))) /
                Fintype.card (V n))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((partitionWordCrossing
          (P n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ j : (n : ℕ) → Finset (V n) → ℤ,
      (∀ n C, C ∈ (P n).parts →
        j n C ∈ C.image (b n) ∧
          ∀ k ∈ C.image (b n),
            componentRankMass C (b n) k ≤
              componentRankMass C (b n) (j n C)) ∧
      Tendsto
        (fun n =>
          ((((Finset.univ : Finset (V n)) \
            RankArcCharging.selectedRankSupport
              (P n) (b n) (j n)).card : ℝ) /
                Fintype.card (V n)))
        atTop (nhds 0) ∧
      ∀ i : κ, Tendsto
        (fun n =>
          ((RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n))
            (b n) (w n i)).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) := by
  obtain ⟨j, hj⟩ := exists_maximizing_partition_ranks P b
  have homitted :=
    maximizing_partition_rank_omitted_density_tendsto_zero
      P b j (fun n C hC => (hj n C hC).2) hvariance
  exact ⟨j, hj, homitted,
    rankChangingArc_density_tendsto_zero_of_selected_support
      P b j w homitted hcross⟩

public
theorem sofic_action_inverse_normalizedHamming_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (g : G) :
    Tendsto
      (fun n =>
        normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)))
      atTop (nhds 0) := by
  have heq :
      (fun n =>
        normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))) =
        (fun n =>
          normalizedHamming
            ((A.model n).action (g * g⁻¹))
            ((A.model n).action g *
              (A.model n).action (g⁻¹))) := by
    funext n
    calc
      normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)) =
        normalizedHamming
          ((A.model n).action g *
            ((A.model n).action g)⁻¹)
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) :=
        (normalizedHamming_mul_left
          ((A.model n).action g)
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))).symm
      _ = normalizedHamming
          ((A.model n).action (g * g⁻¹))
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) := by
        simp only [mul_inv_cancel, (A.model n).map_one]
  rw [heq]
  exact A.multiplicative g (g⁻¹)

end KunCommonRankArcInvariance

namespace ChosenCayleyMatchedComponentRealization

open Filter Topology
open KunActualSoficRootRadius
open KunResidualRetainedSelection
open scoped BigOperators Pointwise symmDiff

private def sourceFirstFactorApproximation
    {K J : Type*} [Group K] [Group J]
    (A : SoficApproximation (K × J)) :
    SoficApproximation K :=
  pullbackSoficApproximation
    (MonoidHom.inl K J)
    (fun _ _ h => congrArg Prod.fst h)
    A

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceFirstFactorCayleyRadiusBad
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (n k : ℕ) : Finset (Fin (A.model n).size) :=
  chosenCayleyRadiusBad
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates) n k

private theorem sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  exact chosenCayleyRadiusBad_density_tendsto_zero
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates)
    (symmetricGeneratorWord_prod S hsymmetric hgenerates) k

private theorem sourceFirstFactor_injective_ball
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (n k : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ sourceFirstFactorCayleyRadiusBad
      A S hsymmetric hgenerates n k) :
    Set.InjOn
      (fun g : K => (A.model n).action (g, 1) x)
      (↑(S ^ k) : Set K) := by
  exact chosenCayleyRadiusBad_injective_ball
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates)
    n k hx

end ChosenCayleyMatchedComponentRealization

namespace CanonicalProductRadiusBadMatchedCapture

open Filter Topology
open KunActualSoficRootRadius
open ChosenCayleyMatchedComponentRealization
open MatchedComponentCompletion
open MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ) :
    Finset (K × J) :=
  ((S ^ k).image fun a : K => (a, (1 : J))) ∪
    (((CompressionCriterion.productTrackedTable F).image
      fun j : J => ((1 : K), j)) ∪
      (S.biUnion fun a =>
        (CompressionCriterion.productTrackedTable F).image
          fun j : J => (a, j)))

public
theorem firstFactor_mem_sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ)
    {a : K} (ha : a ∈ S ^ k) :
    (a, (1 : J)) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

private theorem secondFactor_mem_sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ)
    {j : J}
    (hj : j ∈ CompressionCriterion.productTrackedTable F) :
    ((1 : K), j) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

private theorem composite_mem_sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ)
    {a : K} (ha : a ∈ S)
    {j : J}
    (hj : j ∈ CompressionCriterion.productTrackedTable F) :
    (a, j) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨a, ha, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩

private theorem generator_mem_sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ)
    {a : K} (ha : a ∈ S) :
    (a, (1 : J)) ∈ sourceProductRadiusLabels S F k :=
  composite_mem_sourceProductRadiusLabels S F k ha
    (CompressionCriterion.one_mem_productTrackedTable F)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def canonicalProductRadiusBad
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ) :
    Finset (Fin (A.model n).size) :=
  sourceFirstFactorCayleyRadiusBad
    A S hsymmetric hgenerates n k ∪
      finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k)

public
theorem canonicalProductRadiusBad_density_tendsto_zero
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (k : ℕ) :
    Tendsto
      (fun n =>
        ((canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  have hfactor :=
    sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
      A S hsymmetric hgenerates k
  have hproduct :=
    finiteRootBad_density_tendsto_zero
      A (sourceProductRadiusLabels S F k)
  have hsum : Tendsto
      (fun n =>
        ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
    simpa only [add_zero] using hfactor.add hproduct
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((canonicalProductRadiusBad
        A S hsymmetric hgenerates F n k).card : ℝ) ≤
        (sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card +
        (finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card := by
    exact_mod_cast Finset.card_union_le
      (sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k)
      (finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k))
  calc
    ((canonicalProductRadiusBad
      A S hsymmetric hgenerates F n k).card : ℝ) /
        (A.model n).size ≤
      (((sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k).card : ℝ) +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ)) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ) /
            (A.model n).size := by
      rw [add_div]

private theorem sourceWordTestBad_subset_finiteProductRootBad
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K) (F : Finset J) (n k : ℕ) :
    sourceWordTestBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F ⊆
        finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k) := by
  classical
  intro x hx
  by_contra hxroot
  simp only [sourceWordTestBad, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx
  rcases hx with (hcomm | hmul) | hsep
  · obtain ⟨i, j, hj, hfailure⟩ := hcomm
    have hfirst :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hj)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        hxroot
    have hsecond :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hj)
        hxroot
    apply hfailure
    calc
      (A.model n).action (1, j)
          ((A.model n).action ((i : K), 1) x) =
        (A.model n).action ((1, j) * ((i : K), 1)) x := by
          simpa only [Prod.mk_mul_mk, one_mul, mul_one, Equiv.Perm.mul_apply] using hfirst.symm
      _ = (A.model n).action
          (((i : K), 1) * (1, j)) x := by simp only [Prod.mk_mul_mk, one_mul, mul_one]
      _ = (A.model n).action ((i : K), 1)
          ((A.model n).action (1, j) x) := by
          simpa only [Prod.mk_mul_mk, mul_one, one_mul, Equiv.Perm.mul_apply] using hsecond
  · obtain ⟨j, hj, l, hl, hfailure⟩ := hmul
    have hjT :=
      CompressionCriterion.mem_productTrackedTable hj
    have hlT :=
      CompressionCriterion.mem_productTrackedTable hl
    have hproduct :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hjT)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hlT)
        hxroot
    apply hfailure
    simpa only [Prod.mk_mul_mk, mul_one, Equiv.Perm.mul_apply] using hproduct
  · obtain ⟨j, hj, l, hl, hne, heq⟩ := hsep
    have hjT :=
      CompressionCriterion.mem_productTrackedTable hj
    have hlT :=
      CompressionCriterion.mem_productTrackedTable hl
    have hne' : ((1 : K), j) ≠ ((1 : K), l) := by
      intro h
      exact hne (congrArg Prod.snd h)
    exact finiteRootBad_separated
      (A.model n) (sourceProductRadiusLabels S F k)
      (secondFactor_mem_sourceProductRadiusLabels S F k hjT)
      (secondFactor_mem_sourceProductRadiusLabels S F k hlT)
      hne' hxroot heq

public
theorem component_exit_mem_partitionWordCrossing
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U)
    (C : Finset V) (hC : C ∈ P.parts)
    (p : Equiv.Perm V) {x : V}
    (hx : x ∈ C) (hout : p x ∉ C) :
    x ∈ partitionWordCrossing P p := by
  have hxU : x ∈ U := P.subset hC hx
  change x ∈ U.filter fun y => p y ∉ P.part y
  apply Finset.mem_filter.mpr
  refine ⟨hxU, ?_⟩
  rwa [P.part_eq_of_mem hC hx]

public
theorem sourceCompletionBad_subset_canonical_matchedRadiusBad
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts) :
    sourceCompletionBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C ⊆
      C ∩ matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k) := by
  classical
  intro x hx
  have hxC : x ∈ C :=
    sourceCompletionBad_subset
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C hx
  refine Finset.mem_inter.mpr ⟨hxC, ?_⟩
  by_contra hnot
  have hnotbad :
      x ∉ canonicalProductRadiusBad
        A S hsymmetric hgenerates F n k := by
    intro hbad
    apply hnot
    exact Finset.mem_union_left _ hbad
  have hroot :
      x ∉ finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k) := by
    intro hbad
    exact hnotbad (Finset.mem_union_right _ hbad)
  have hnotcross :
      ∀ q ∈ sourceProductRadiusLabels S F k,
        x ∉ partitionWordCrossing
          P ((A.model n).action q) := by
    intro q hq hcross
    apply hnot
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨q, hq, hcross⟩
  have hcovered :=
    sourceCompletionBad_subset_exit_union_wordBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C hx
  simp only [Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and] at hcovered
  rcases hcovered with ((hgen | hfactor) | hcomposite) | hword
  · obtain ⟨i, hx', hout⟩ := hgen
    apply hnotcross
      ((i : K), 1)
      (generator_mem_sourceProductRadiusLabels
        S F k i.property)
    exact component_exit_mem_partitionWordCrossing
      P C hC _ hx' hout
  · obtain ⟨j, hj, hx', hout⟩ := hfactor
    apply hnotcross
      ((1 : K), j)
      (secondFactor_mem_sourceProductRadiusLabels S F k hj)
    exact component_exit_mem_partitionWordCrossing
      P C hC _ hx' hout
  · obtain ⟨i, j, hj, hx', hout⟩ := hcomposite
    have hpair :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels S F k hj)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        hroot
    have hvalue :
        (A.model n).action ((i : K), j) x =
          (A.model n).action (1, j)
            ((A.model n).action ((i : K), 1) x) := by
      simpa only [Prod.mk_mul_mk, one_mul, mul_one, Equiv.Perm.mul_apply] using hpair
    apply hnotcross
      ((i : K), j)
      (composite_mem_sourceProductRadiusLabels
        S F k i.property hj)
    apply component_exit_mem_partitionWordCrossing
      P C hC _ hx'
    rw [hvalue]
    exact hout
  · apply hroot
    exact sourceWordTestBad_subset_finiteProductRootBad
      A S F n k hword

public
theorem canonical_source_matched_component_cayley_ball_realization
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K) (honeS : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts)
    (x : Fin (A.model n).size) (hx : x ∈ C)
    (hgood : x ∉
      matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k)) :
    ∃ f : K → Fin (A.model n).size,
      Set.MapsTo f
        (↑(S ^ (k / 2)) : Set K)
        (↑C : Set (Fin (A.model n).size)) ∧
      Set.InjOn f (↑(S ^ (k / 2)) : Set K) := by
  have hxsource :
      x ∉ sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k := by
    intro hbad
    apply hgood
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ hbad
  have hroot :=
    sourceFirstFactor_injective_ball
      A S hsymmetric hgenerates n k hxsource
  refine ⟨fun a => (A.model n).action (a, 1) x, ?_, ?_⟩
  · intro a ha
    have hak : a ∈ S ^ k :=
      Finset.pow_subset_pow_right honeS
        (Nat.div_le_self k 2) ha
    have halabel :=
      firstFactor_mem_sourceProductRadiusLabels S F k hak
    have hnotcross :
        x ∉ partitionWordCrossing
          P ((A.model n).action (a, 1)) := by
      intro hcross
      apply hgood
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨(a, 1), halabel, hcross⟩
    have himage : (A.model n).action (a, 1) x ∈ C := by
      by_contra hout
      apply hnotcross
      exact component_exit_mem_partitionWordCrossing
        P C hC _ hx hout
    exact himage
  · apply hroot.mono
    intro a ha
    exact Finset.pow_subset_pow_right honeS
      (Nat.div_le_self k 2) ha

end CanonicalProductRadiusBadMatchedCapture

namespace CompletedSelectedCentralizerPairwiseSource

open Filter Topology
open MatchedComponentCompletion
open MatchedFirstStageWordRadiusTransfer
open CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise

private theorem eventually_five_mul_sourceCompletionBad_le_of_density
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      5 * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card ≤ (Z n).card := by
  have hsmall : ∀ᶠ n in atTop,
      ((sourceCompletionBad
        (σ n) (p n) F (Z n)).card : ℝ) /
          (Z n).card < (1 / 5 : ℝ) :=
    hbad.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  have hpositive : (0 : ℝ) < (Z n).card := by
    exact_mod_cast (hZ n).card_pos
  have hreal := (div_lt_iff₀ hpositive).mp hn
  have hstrict :
      5 * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card < (Z n).card := by
    exact_mod_cast (show
      (5 : ℝ) * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card < (Z n).card by
          linarith)
  exact hstrict.le

public
theorem eventually_completed_sourceCentralizer_table_of_bad_density
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) /
            (Z n).card)
      atTop (nhds 0))
    (σZ : (n : ℕ) → ι →
      Equiv.Perm {x : V n // x ∈ Z n})
    (hσZ : ∀ n i (x : V n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((σZ n i ⟨x, hx⟩ :
          {x : V n // x ∈ Z n}) : V n) = σ n i x)
    (t : ℕ → ℕ)
    (ht : ∀ n,
      2 * Fintype.card ι *
        (sourceCompletionBad
          (σ n) (p n) F (Z n)).card ≤ t n) :
    ∀ᶠ n in atTop,
      (∀ a ∈ F, ∀ b ∈ F,
        5 * permutationDistance
          (completedRestriction (p n (a * b)) (Z n))
          (completedRestriction (p n a) (Z n) *
            completedRestriction (p n b) (Z n)) ≤
          Fintype.card {x : V n // x ∈ Z n}) ∧
      (∀ a ∈ F, ∀ b ∈ F, a ≠ b →
        Fintype.card {x : V n // x ∈ Z n} <
          5 * permutationDistance
            (completedRestriction (p n a) (Z n))
            (completedRestriction (p n b) (Z n))) ∧
      (∀ a ∈ CompressionCriterion.productTrackedTable F,
        permutationCommutationDefect
          (σZ n) (completedRestriction (p n a) (Z n)) ≤
            t n) := by
  have hevent :=
    eventually_five_mul_sourceCompletionBad_le_of_density
      V σ p F Z hZ hbad
  filter_upwards [hevent] with n hn
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    have hdist :=
      completedRestriction_mul_distance_le_sourceCompletionBad
        (σ n) (p n) F (Z n) ha hb
    simpa only [Fintype.card_coe] using
      (Nat.mul_le_mul_left 5 hdist).trans hn
  · intro a ha b hb hab
    exact completedRestriction_separated_of_sourceCompletionBad
      (σ n) (p n) F (Z n) (hZ n) hn ha hb hab
  · intro a ha
    have hdef :=
      completedRestriction_commutationDefect_le_sourceCompletionBad
        (σ n) (p n) F (Z n)
        (σZ n) (hσZ n) ha
    have hscale :
        Fintype.card ι *
          (sourceCompletionBad
            (σ n) (p n) F (Z n)).card ≤ t n := by
      have hdegree : Fintype.card ι ≤ 2 * Fintype.card ι := by
        omega
      exact (Nat.mul_le_mul_right
        (sourceCompletionBad
          (σ n) (p n) F (Z n)).card hdegree).trans (ht n)
    exact hdef.trans hscale

end CompletedSelectedCentralizerPairwiseSource

namespace KunActualSelectedCentralizerFiniteModel

open Filter Topology

private noncomputable def trackedCompletedAlmostCentralizer
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ CompressionCriterion.productTrackedTable F,
      permutationCommutationDefect σ (p j) ≤ t) :
    J → AlmostCentralizerElement σ t := by
  classical
  intro j
  by_cases hj : j ∈ CompressionCriterion.productTrackedTable F
  · exact ⟨p j, hdefect j hj⟩
  · exact ⟨1, by simp only [permutationCommutationDefect_one, zero_le]⟩

private theorem trackedCompletedAlmostCentralizer_permutation_of_mem
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ CompressionCriterion.productTrackedTable F,
      permutationCommutationDefect σ (p j) ≤ t)
    {j : J}
    (hj : j ∈ CompressionCriterion.productTrackedTable F) :
    (trackedCompletedAlmostCentralizer σ p F t hdefect j).permutation =
      p j := by
  classical
  simp only [trackedCompletedAlmostCentralizer, hj, ↓reduceDIte]

private theorem trackedCompletedAlmostCentralizer_map_one
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (hp : p 1 = 1)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ CompressionCriterion.productTrackedTable F,
      permutationCommutationDefect σ (p j) ≤ t) :
    (trackedCompletedAlmostCentralizer σ p F t hdefect 1).permutation = 1 := by
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (CompressionCriterion.one_mem_productTrackedTable F), hp]

private theorem trackedCompletedAlmostCentralizer_multiplicative
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ CompressionCriterion.productTrackedTable F,
      permutationCommutationDefect σ (p j) ≤ t)
    (hmul : ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance
        (p (x * y)) (p x * p y) ≤ Fintype.card V) :
    ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance
        (trackedCompletedAlmostCentralizer
          σ p F t hdefect (x * y)).permutation
        ((trackedCompletedAlmostCentralizer
          σ p F t hdefect x).permutation *
         (trackedCompletedAlmostCentralizer
          σ p F t hdefect y).permutation) ≤ Fintype.card V := by
  intro x hx y hy
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (CompressionCriterion.mul_mem_productTrackedTable hx hy),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (CompressionCriterion.mem_productTrackedTable hx),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (CompressionCriterion.mem_productTrackedTable hy)]
  exact hmul x hx y hy

private theorem trackedCompletedAlmostCentralizer_separated
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ CompressionCriterion.productTrackedTable F,
      permutationCommutationDefect σ (p j) ≤ t)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * permutationDistance (p x) (p y)) :
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V <
        5 * permutationDistance
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect x).permutation
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect y).permutation := by
  intro x hx y hy hxy
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (CompressionCriterion.mem_productTrackedTable hx),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (CompressionCriterion.mem_productTrackedTable hy)]
  exact hsep x hx y hy hxy

public
theorem nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
    {J : Type} [Group J] (F : Finset J)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (ι : Type) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (hp : ∀ n, p n 1 = 1)
    (t : ℕ → ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hdefect : ∀ᶠ n in atTop,
      ∀ j ∈ CompressionCriterion.productTrackedTable F,
        permutationCommutationDefect
          (σ n) (p n j) ≤ t n)
    (hexp : ∀ᶠ n in atTop, ∀ E : Finset (V n),
      h * min (E.card : ℝ)
        ((Fintype.card (V n) : ℝ) - E.card) ≤
          (boundary (σ n) E : ℝ))
    (hsmall : ∀ᶠ n in atTop,
      (10 : ℝ) * t n < h * Fintype.card (V n))
    (himprove : ∀ᶠ n in atTop,
      HasAlmostCentralizerImprovement (σ n) (t n))
    (hmul : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance
        (p n (x * y)) (p n x * p n y) ≤ Fintype.card (V n))
    (hsep : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card (V n) <
        5 * permutationDistance (p n x) (p n y)) :
    Nonempty (ExpandingCentralizerFiniteModel J F) := by
  have hgood := hdefect.and
    (hexp.and (hsmall.and (himprove.and (hmul.and hsep))))
  obtain ⟨n, hn⟩ := hgood.exists
  obtain ⟨hdefect_n, hexp_n, hsmall_n,
    himprove_n, hmul_n, hsep_n⟩ := hn
  let f := trackedCompletedAlmostCentralizer
    (σ n) (p n) F (t n) hdefect_n
  refine ⟨expandingCentralizerFiniteModelOfImprovement
    F (σ n) (t n) h hpositive hexp_n hsmall_n himprove_n
      f ?_ ?_ ?_⟩
  · exact trackedCompletedAlmostCentralizer_map_one
      (σ n) (p n) (hp n) F (t n) hdefect_n
  · exact trackedCompletedAlmostCentralizer_multiplicative
      (σ n) (p n) F (t n) hdefect_n hmul_n
  · exact trackedCompletedAlmostCentralizer_separated
      (σ n) (p n) F (t n) hdefect_n hsep_n

end KunActualSelectedCentralizerFiniteModel

namespace SourceTopLevelCompression

open Filter

public
theorem sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
    (hmodels :
      ∀ A : SoficApproximation
          (prefixElementaryGroup ninePrefixCode),
        Tendsto (fun n => (A.model n).size) atTop atTop →
          ∀ F : Finset
              (ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  [0, 0, 0, 1]),
            Nonempty (ExpandingCentralizerFiniteModel
              (ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  [0, 0, 0, 1]) F))
    (hsource : Sofic
      (prefixElementaryGroup ninePrefixCode)) :
    LEF
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]) := by
  let : Sofic
      (prefixElementaryGroup ninePrefixCode) :=
    hsource
  let : Countable
      (prefixElementaryGroup ninePrefixCode) :=
    ninePrefixElementaryGroup_countable
  obtain ⟨A, hA⟩ := exists_soficApproximation_size_tendsto
    (prefixElementaryGroup ninePrefixCode)
  exact lef_of_expanding_centralizer_models (hmodels A hA)

end SourceTopLevelCompression


end SoficGroups

end
