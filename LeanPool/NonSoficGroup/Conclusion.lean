/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.NonSoficGroup.Compression
import all LeanPool.NonSoficGroup.Compression

noncomputable section

namespace SoficGroups

open CanonicalProductRadiusBadMatchedCapture
open CompletedSelectedCentralizerPairwiseSource
open CompletedSourceFinalGeneratorTransfer
open KunActualSelectedCentralizerFiniteModel
open KunGlobalActualAdditiveMidrankVariance
open MatchedFirstStageWordRadiusTransfer
open SourceCommonComponentRankNoBad

namespace ThompsonFFiniteQuotient

variable {G : Type*} [Group G]

/-- The conjugate of `b` by the `n`th power of `a`. -/
public def conjugateTerm (a b : G) (n : ℕ) : G :=
  (a ^ n)⁻¹ * b * a ^ n

theorem conjugateTerm_succ (a b : G) (n : ℕ) :
    conjugateTerm a b (n + 1) =
      a⁻¹ * conjugateTerm a b n * a := by
  simp only [conjugateTerm, pow_succ, mul_inv_rev]
  group

theorem conjugation_shift (a u v w : G)
    (h : u⁻¹ * v * u = w) :
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) *
        (a⁻¹ * u * a) = a⁻¹ * w * a := by
  calc
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) *
        (a⁻¹ * u * a) = a⁻¹ * (u⁻¹ * v * u) * a := by
      group
    _ = a⁻¹ * w * a := by rw [h]

theorem conjugacy_relation_of_commute (a b : G) (n : ℕ)
    (h : Commute (a * b⁻¹) (conjugateTerm a b n)) :
    b⁻¹ * conjugateTerm a b n * b =
      conjugateTerm a b (n + 1) := by
  rw [conjugateTerm_succ]
  calc
    b⁻¹ * conjugateTerm a b n * b =
        a⁻¹ * ((a * b⁻¹) * conjugateTerm a b n) * b := by
      group
    _ = a⁻¹ * (conjugateTerm a b n * (a * b⁻¹)) * b := by
      rw [h.eq]
    _ = a⁻¹ * conjugateTerm a b n * a := by
      group

theorem conjugacy_relation_shift (a b u : G) (n : ℕ)
    (h : u⁻¹ * conjugateTerm a b n * u =
      conjugateTerm a b (n + 1)) :
    (a⁻¹ * u * a)⁻¹ * conjugateTerm a b (n + 1) *
        (a⁻¹ * u * a) = conjugateTerm a b (n + 2) := by
  rw [conjugateTerm_succ a b n,
    conjugateTerm_succ a b (n + 1)]
  exact conjugation_shift a u
    (conjugateTerm a b n) (conjugateTerm a b (n + 1)) h

theorem conjugacy_relation_step (a b : G) (n : ℕ)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2)
    (hprevious : b⁻¹ * conjugateTerm a b n * b =
      conjugateTerm a b (n + 1))
    (hcurrent : b⁻¹ * conjugateTerm a b (n + 1) * b =
      conjugateTerm a b (n + 2)) :
    b⁻¹ * conjugateTerm a b (n + 2) * b =
      conjugateTerm a b (n + 3) := by
  have hone : conjugateTerm a b 1 = a⁻¹ * b * a := by
    simp only [conjugateTerm, pow_one]
  have hshift :
      (conjugateTerm a b 1)⁻¹ *
          conjugateTerm a b (n + 1) *
          conjugateTerm a b 1 =
        conjugateTerm a b (n + 2) := by
    rw [hone]
    exact conjugacy_relation_shift a b b n hprevious
  have hdouble :
      (conjugateTerm a b 2)⁻¹ *
          conjugateTerm a b (n + 2) *
          conjugateTerm a b 2 =
        conjugateTerm a b (n + 3) := by
    rw [conjugateTerm_succ a b 1]
    exact conjugacy_relation_shift a b
      (conjugateTerm a b 1) (n + 1) hshift
  calc
    b⁻¹ * conjugateTerm a b (n + 2) * b =
        (b⁻¹ * conjugateTerm a b 1 * b)⁻¹ *
          (b⁻¹ * conjugateTerm a b (n + 1) * b) *
          (b⁻¹ * conjugateTerm a b 1 * b) := by
      rw [← hshift]
      group
    _ = (conjugateTerm a b 2)⁻¹ *
          conjugateTerm a b (n + 2) *
          conjugateTerm a b 2 := by
      rw [hfirst, hcurrent]
    _ = conjugateTerm a b (n + 3) := hdouble

theorem conjugacy_relation_all (a b : G)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2)
    (hsecond : b⁻¹ * conjugateTerm a b 2 * b =
      conjugateTerm a b 3) (n : ℕ) :
    b⁻¹ * conjugateTerm a b (n + 1) * b =
      conjugateTerm a b (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => exact hfirst
  | one => exact hsecond
  | more n hprevious hcurrent =>
      simpa only [Nat.add_assoc, Nat.reduceAdd] using conjugacy_relation_step a b (n + 1) hfirst
        hprevious hcurrent

theorem finite_group_commute_of_thompsonF_two_relations
    {G : Type*} [Group G] [Finite G] (a b : G)
    (hfirst : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (hsecond : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2)) :
    Commute a b := by
  have hfirst' : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2 := by
    apply conjugacy_relation_of_commute a b 1
    simpa only [conjugateTerm, pow_one] using hfirst
  have hsecond' : b⁻¹ * conjugateTerm a b 2 * b =
      conjugateTerm a b 3 := by
    apply conjugacy_relation_of_commute a b 2
    simpa only [conjugateTerm] using hsecond
  have hpositive : 0 < orderOf a := orderOf_pos a
  have hindex : orderOf a - 1 + 1 = orderOf a :=
    Nat.sub_add_cancel hpositive
  have hnext : orderOf a - 1 + 2 = orderOf a + 1 := by
    omega
  have hperiod : conjugateTerm a b (orderOf a) = b := by
    simp only [conjugateTerm, pow_orderOf_eq_one, inv_one, one_mul, mul_one]
  have hconjugate :
      conjugateTerm a b (orderOf a + 1) = a⁻¹ * b * a := by
    rw [conjugateTerm_succ, hperiod]
  have hrelation := conjugacy_relation_all a b hfirst' hsecond'
    (orderOf a - 1)
  rw [hindex, hnext, hperiod, hconjugate] at hrelation
  have heq : b = a⁻¹ * b * a := by
    simpa only [inv_mul_cancel, one_mul] using hrelation
  change a * b = b * a
  calc
    a * b = a * (a⁻¹ * b * a) := congrArg (fun z : G => a * z) heq
    _ = b * a := by group

end ThompsonFFiniteQuotient

namespace ThompsonFTwoRelatorLEF

open scoped commutatorElement

def thompsonFRelator (n : ℕ) : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2) * (FreeGroup.of (1 : Fin 2))⁻¹,
    ((FreeGroup.of (0 : Fin 2)) ^ n)⁻¹ *
      FreeGroup.of (1 : Fin 2) * (FreeGroup.of (0 : Fin 2)) ^ n⁆

def thompsonFGeneratorCommutator : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆

theorem not_lef_of_thompsonF_two_relations
    {G : Type*} [Group G] (a b : G)
    (h₁ : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (h₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2))
    (hne : ¬ Commute a b)
    (hfinite : ∀ (n : ℕ) (x y : Equiv.Perm (Fin n)),
      Commute (x * y⁻¹) (x⁻¹ * y * x) →
      Commute (x * y⁻¹) ((x ^ 2)⁻¹ * y * x ^ 2) →
      Commute x y) :
    ¬ LEF G := by
  classical
  intro hlef
  let φ : FreeGroup (Fin 2) →* G := FreeGroup.lift ![a, b]
  let r₁ : FreeGroup (Fin 2) := thompsonFRelator 1
  let r₂ : FreeGroup (Fin 2) := thompsonFRelator 2
  let w : FreeGroup (Fin 2) := thompsonFGeneratorCommutator
  let tracked : Finset (FreeGroup (Fin 2)) := {r₁, r₂, w}
  let controls : FreeGroup (Fin 2) → Finset G :=
    fun q => Classical.choose (exists_local_word_control φ q)
  have hcontrols (q : FreeGroup (Fin 2)) :
      ∀ (H : Type) [Group H] (f : G → H),
        LocalMultiplicativeOn (controls q) f →
          FreeGroup.lift (fun i => f (φ (FreeGroup.of i))) q = f (φ q) :=
    Classical.choose_spec (exists_local_word_control φ q)
  let support : Finset G :=
    insert 1 (insert (φ w) (tracked.biUnion controls))
  obtain ⟨n, f, hf_inj, hf_local⟩ := hlef.approximate support
  let ψ : FreeGroup (Fin 2) →* Equiv.Perm (Fin n) :=
    FreeGroup.lift (fun i => f (φ (FreeGroup.of i)))
  have hword (q : FreeGroup (Fin 2)) (hq : q ∈ tracked) :
      ψ q = f (φ q) := by
    apply hcontrols q (Equiv.Perm (Fin n)) f
    apply hf_local.mono
    intro z hz
    simp only [support, Finset.mem_insert, Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨q, hq, hz⟩)
  have hφ₁ : φ r₁ = 1 := by
    simpa [φ, r₁, thompsonFRelator] using h₁.commutator_eq
  have hφ₂ : φ r₂ = 1 := by
    simpa [φ, r₂, thompsonFRelator] using h₂.commutator_eq
  have hψ₁ : ψ r₁ = 1 := by
    calc
      ψ r₁ = f (φ r₁) := hword r₁ (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or,
        tracked])
      _ = 1 := by rw [hφ₁, hf_local.map_one]
  have hψ₂ : ψ r₂ = 1 := by
    calc
      ψ r₂ = f (φ r₂) := hword r₂ (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or,
        or_true, tracked])
      _ = 1 := by rw [hφ₂, hf_local.map_one]
  have hf₁ :
      Commute (f a * (f b)⁻¹) ((f a)⁻¹ * f b * f a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [ψ, φ, r₁, thompsonFRelator] using hψ₁
  have hf₂ :
      Commute (f a * (f b)⁻¹)
        (((f a) ^ 2)⁻¹ * f b * (f a) ^ 2) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [ψ, φ, r₂, thompsonFRelator] using hψ₂
  have hψw : ψ w = 1 := by
    simpa [ψ, φ, w, thompsonFGeneratorCommutator] using
      (hfinite n (f a) (f b) hf₁ hf₂).commutator_eq
  have hφw : φ w ≠ 1 := by
    intro hz
    apply hne
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [φ, w, thompsonFGeneratorCommutator] using hz
  apply hφw
  apply hf_inj
  · simp only [Finset.coe_insert, Finset.coe_biUnion, SetLike.mem_coe, Set.mem_insert_iff,
    Set.mem_iUnion,
      exists_prop, true_or, or_true, support]
  · simp only [Finset.coe_insert, Finset.coe_biUnion, SetLike.mem_coe, Set.mem_insert_iff,
    Set.mem_iUnion,
      exists_prop, true_or, support]
  calc
    f (φ w) = ψ w := (hword w (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true,
      tracked])).symm
    _ = 1 := hψw
    _ = f 1 := hf_local.map_one.symm

end ThompsonFTwoRelatorLEF

namespace ThompsonFLocalWitness

open ThompsonPrefixInsertion

theorem prefixWordAction_inv {g : BinaryLeavittˣ}
    {a b : List (Fin 2)} (h : PrefixWordAction g a b) :
    PrefixWordAction g⁻¹ b a := by
  have hunit : (↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt) = 1 := by
    simp only [Units.inv_mul]
  constructor
  · calc
      (↑g⁻¹ : BinaryLeavitt) * leavittWordS b =
          (↑g⁻¹ : BinaryLeavitt) *
            ((g : BinaryLeavitt) * leavittWordS a) := by
              rw [h.prefixing]
      _ = ((↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt)) *
          leavittWordS a := by rw [mul_assoc]
      _ = leavittWordS a := by rw [hunit, one_mul]
  · change leavittWordT b * (g : BinaryLeavitt) = leavittWordT a
    calc
      leavittWordT b * (g : BinaryLeavitt) =
          (leavittWordT a * (↑g⁻¹ : BinaryLeavitt)) *
            (g : BinaryLeavitt) := by rw [h.deletion]
      _ = leavittWordT a *
          ((↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt)) := by
            rw [mul_assoc]
      _ = leavittWordT a := by rw [hunit, mul_one]

theorem prefixWordAction_prefixInsertion {g : BinaryLeavittˣ}
    {a b : List (Fin 2)} (l : List (Fin 2))
    (h : PrefixWordAction g a b) :
    PrefixWordAction (prefixInsertionHom l g) (l ++ a) (l ++ b) := by
  have hl := leavittWordT_mul_wordS_self l
  have hl' (x : BinaryLeavitt) :
      leavittWordT l * (leavittWordS l * x) = x := by
    rw [← mul_assoc, hl, one_mul]
  constructor
  · rw [prefixInsertionHom_val, leavittWordS_append,
      leavittWordS_append]
    simp only [leavittCylinder]
    noncomm_ring [hl, hl', h.prefixing]
  · have hinv :
        (prefixInsertionHom l g)⁻¹ = prefixInsertionHom l g⁻¹ :=
      ((prefixInsertionHom l).map_inv g).symm
    rw [hinv, prefixInsertionHom_val, leavittWordT_append,
      leavittWordT_append]
    simp only [leavittCylinder]
    noncomm_ring [hl, hl', h.deletion]
    rw [← mul_assoc, h.deletion]

def rootRotation : BinaryLeavittˣ :=
  cylinderSwap [0] [1, 0] (by decide) (by decide) *
    cylinderSwap [0] [1, 1] (by decide) (by decide) *
    cylinderSwap [0] [1] (by decide) (by decide)

def rightRotation : BinaryLeavittˣ :=
  prefixInsertionHom [1] rootRotation

theorem rootRotation_action_zero_zero :
    PrefixWordAction rootRotation [0, 0] [0] := by
  unfold rootRotation
  rw [mul_assoc]
  refine prefixWordAction_mul (b := [1, 0]) ?_ ?_
  · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
      (by decide) (by decide) (by decide)
  · refine prefixWordAction_mul (b := [1, 0]) ?_ ?_
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)

theorem rootRotation_action_zero_one :
    PrefixWordAction rootRotation [0, 1] [1, 0] := by
  unfold rootRotation
  rw [mul_assoc]
  refine prefixWordAction_mul (b := [0]) ?_ ?_
  · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
      (by decide) (by decide) (by decide)
  · refine prefixWordAction_mul (b := [1, 1]) ?_ ?_
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)

theorem rootRotation_action_one :
    PrefixWordAction rootRotation [1] [1, 1] := by
  unfold rootRotation
  rw [mul_assoc]
  refine prefixWordAction_mul (b := [1, 1]) ?_ ?_
  · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
      (by decide) (by decide) (by decide)
  · refine prefixWordAction_mul (b := [0]) ?_ ?_
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)

theorem generatorB_eq_prefixInsertion :
    rightRotation⁻¹ = prefixInsertionHom [1] rootRotation⁻¹ := by
  change
    (prefixInsertionHom [1] rootRotation)⁻¹ =
      prefixInsertionHom [1] rootRotation⁻¹
  exact ((prefixInsertionHom [1]).map_inv rootRotation).symm

theorem generator_two_eq_prefixInsertion :
    rootRotation⁻¹⁻¹ * rightRotation⁻¹ * rootRotation⁻¹ =
      prefixInsertionHom [1, 1] rootRotation⁻¹ := by
  calc
    rootRotation⁻¹⁻¹ * rightRotation⁻¹ * rootRotation⁻¹ =
        rootRotation * prefixInsertionHom [1] rootRotation⁻¹ *
          rootRotation⁻¹ := by
            rw [generatorB_eq_prefixInsertion]
            simp only [inv_inv, Fin.isValue, map_inv]
    _ = prefixInsertionHom [1, 1] rootRotation⁻¹ :=
      prefixInsertionHom_conjugate_of_prefixWordAction
        rootRotation [1] [1, 1] rootRotation_action_one rootRotation⁻¹

theorem generator_three_eq_prefixInsertion :
    (rootRotation⁻¹ ^ 2)⁻¹ * rightRotation⁻¹ * rootRotation⁻¹ ^ 2 =
      prefixInsertionHom [1, 1, 1] rootRotation⁻¹ := by
  have hrotation :
      PrefixWordAction rootRotation [1, 1] [1, 1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      prefixWordAction_append rootRotation_action_one [1]
  calc
    (rootRotation⁻¹ ^ 2)⁻¹ * rightRotation⁻¹ * rootRotation⁻¹ ^ 2 =
        rootRotation *
          (rootRotation⁻¹⁻¹ * rightRotation⁻¹ * rootRotation⁻¹) *
          rootRotation⁻¹ := by
            simp only [pow_two, mul_inv_rev, inv_inv, mul_assoc]
    _ = rootRotation * prefixInsertionHom [1, 1] rootRotation⁻¹ *
          rootRotation⁻¹ := by rw [generator_two_eq_prefixInsertion]
    _ = prefixInsertionHom [1, 1, 1] rootRotation⁻¹ :=
      prefixInsertionHom_conjugate_of_prefixWordAction
        rootRotation [1, 1] [1, 1, 1] hrotation rootRotation⁻¹

theorem generator_difference_action_one_one :
    PrefixWordAction (rootRotation⁻¹ * rightRotation⁻¹⁻¹) [1, 1] [1, 1] := by
  have hrotation :
      PrefixWordAction rootRotation [1, 1] [1, 1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      prefixWordAction_append rootRotation_action_one [1]
  have hright :
      PrefixWordAction rightRotation [1, 1] [1, 1, 1] := by
    unfold rightRotation
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      prefixWordAction_prefixInsertion [1] rootRotation_action_one
  change
    PrefixWordAction
      (rootRotation⁻¹ * (rightRotation⁻¹)⁻¹) [1, 1] [1, 1]
  simp only [inv_inv]
  exact prefixWordAction_mul (prefixWordAction_inv hrotation) hright

theorem commute_prefixInsertion_of_prefixWordAction_fixed
    (g : BinaryLeavittˣ) (w : List (Fin 2))
    (h : PrefixWordAction g w w) (u : BinaryLeavittˣ) :
    Commute g (prefixInsertionHom w u) := by
  have hconjugate :=
    prefixInsertionHom_conjugate_of_prefixWordAction g w w h u
  apply (commute_iff_eq _ _).2
  calc
    g * prefixInsertionHom w u =
        (g * prefixInsertionHom w u * g⁻¹) * g := by group
    _ = prefixInsertionHom w u * g := by rw [hconjugate]

theorem relator_one :
    Commute (rootRotation⁻¹ * rightRotation⁻¹⁻¹)
      (rootRotation⁻¹⁻¹ * rightRotation⁻¹ * rootRotation⁻¹) := by
  rw [generator_two_eq_prefixInsertion]
  exact commute_prefixInsertion_of_prefixWordAction_fixed
    (rootRotation⁻¹ * rightRotation⁻¹⁻¹) [1, 1]
    generator_difference_action_one_one rootRotation⁻¹

theorem relator_two :
    Commute (rootRotation⁻¹ * rightRotation⁻¹⁻¹)
      ((rootRotation⁻¹ ^ 2)⁻¹ * rightRotation⁻¹ * rootRotation⁻¹ ^ 2) := by
  rw [generator_three_eq_prefixInsertion]
  apply commute_prefixInsertion_of_prefixWordAction_fixed
    (rootRotation⁻¹ * rightRotation⁻¹⁻¹) [1, 1, 1] _ rootRotation⁻¹
  simpa only [Fin.isValue, List.cons_append, List.nil_append] using
    prefixWordAction_append generator_difference_action_one_one [1]

theorem cylinderSwap_mem_binaryPrefixTranspositionGroup
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    cylinderSwap a b hab hba ∈ binaryPrefixTranspositionGroup :=
  Subgroup.subset_closure ⟨a, b, hab, hba, rfl⟩

theorem rootRotation_mem_binaryPrefixTranspositionGroup :
    rootRotation ∈ binaryPrefixTranspositionGroup := by
  unfold rootRotation
  exact binaryPrefixTranspositionGroup.mul_mem
    (binaryPrefixTranspositionGroup.mul_mem
      (cylinderSwap_mem_binaryPrefixTranspositionGroup
        [0] [1, 0] (by decide) (by decide))
      (cylinderSwap_mem_binaryPrefixTranspositionGroup
        [0] [1, 1] (by decide) (by decide)))
    (cylinderSwap_mem_binaryPrefixTranspositionGroup
      [0] [1] (by decide) (by decide))

theorem generatorA_mem_binaryPrefixTranspositionGroup :
    rootRotation⁻¹ ∈ binaryPrefixTranspositionGroup :=
  binaryPrefixTranspositionGroup.inv_mem
    rootRotation_mem_binaryPrefixTranspositionGroup

theorem generatorB_mem_binaryPrefixTranspositionGroup :
    rightRotation⁻¹ ∈ binaryPrefixTranspositionGroup := by
  rw [generatorB_eq_prefixInsertion]
  exact prefixInsertionHom_mem_binaryPrefixTranspositionGroup
    [1] rootRotation⁻¹ generatorA_mem_binaryPrefixTranspositionGroup

theorem generators_not_commute : ¬ Commute rootRotation⁻¹ rightRotation⁻¹ := by
  have ha_zero_one :
      PrefixWordAction rootRotation⁻¹ [1, 0] [0, 1] :=
    prefixWordAction_inv rootRotation_action_zero_one
  have ha_one :
      PrefixWordAction rootRotation⁻¹ [1, 1] [1] :=
    prefixWordAction_inv rootRotation_action_one
  have hb_one_one_zero :
      PrefixWordAction rightRotation⁻¹ [1, 1, 0] [1, 0, 1] := by
    apply prefixWordAction_inv
    unfold rightRotation
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      prefixWordAction_prefixInsertion [1] rootRotation_action_zero_one
  have hb_one_zero :
      PrefixWordAction rightRotation⁻¹ [1, 0] [1, 0, 0] := by
    apply prefixWordAction_inv
    unfold rightRotation
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      prefixWordAction_prefixInsertion [1] rootRotation_action_zero_zero
  have hab :
      PrefixWordAction (rootRotation⁻¹ * rightRotation⁻¹)
        [1, 1, 0] [0, 1, 1] :=
    prefixWordAction_mul
      (by
        simpa only [Fin.isValue, List.cons_append, List.nil_append] using
          prefixWordAction_append ha_zero_one [1])
      hb_one_one_zero
  have hba :
      PrefixWordAction (rightRotation⁻¹ * rootRotation⁻¹)
        [1, 1, 0] [1, 0, 0] :=
    prefixWordAction_mul hb_one_zero
      (by
        simpa only [Fin.isValue, List.cons_append, List.nil_append] using
          prefixWordAction_append ha_one [0])
  intro hcommute
  have hwords :
      leavittWordS [0, 1, 1] = leavittWordS [1, 0, 0] := by
    calc
      leavittWordS [0, 1, 1] =
          (↑(rootRotation⁻¹ * rightRotation⁻¹) : BinaryLeavitt) *
            leavittWordS [1, 1, 0] := hab.prefixing.symm
      _ = (↑(rightRotation⁻¹ * rootRotation⁻¹) : BinaryLeavitt) *
            leavittWordS [1, 1, 0] := by rw [hcommute.eq]
      _ = leavittWordS [1, 0, 0] := hba.prefixing
  apply (one_ne_zero : (1 : BinaryLeavitt) ≠ 0)
  calc
    (1 : BinaryLeavitt) =
        leavittWordT [0, 1, 1] * leavittWordS [0, 1, 1] :=
      (leavittWordT_mul_wordS_self [0, 1, 1]).symm
    _ = leavittWordT [0, 1, 1] * leavittWordS [1, 0, 0] := by
      rw [hwords]
    _ = 0 := leavittWordT_mul_wordS_of_incomparable
      [0, 1, 1] [1, 0, 0] (by decide) (by decide)

def sourceGeneratorA :
    localPrefixTranspositionGroup [0, 0, 0, 1] :=
  ⟨prefixInsertionHom [0, 0, 0, 1] rootRotation⁻¹,
    ⟨rootRotation⁻¹, generatorA_mem_binaryPrefixTranspositionGroup, rfl⟩⟩

def sourceGeneratorB :
    localPrefixTranspositionGroup [0, 0, 0, 1] :=
  ⟨prefixInsertionHom [0, 0, 0, 1] rightRotation⁻¹,
    ⟨rightRotation⁻¹, generatorB_mem_binaryPrefixTranspositionGroup, rfl⟩⟩

theorem source_relator_one :
    Commute (sourceGeneratorA * sourceGeneratorB⁻¹)
      (sourceGeneratorA⁻¹ * sourceGeneratorB * sourceGeneratorA) := by
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  simpa only [sourceGeneratorA, sourceGeneratorB,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using
    (relator_one.map
      (prefixInsertionHom [0, 0, 0, 1])).eq

theorem source_relator_two :
    Commute (sourceGeneratorA * sourceGeneratorB⁻¹)
      ((sourceGeneratorA ^ 2)⁻¹ * sourceGeneratorB *
        sourceGeneratorA ^ 2) := by
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  simpa only [sourceGeneratorA, sourceGeneratorB,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
    map_mul, map_inv, map_pow] using
    (relator_two.map
      (prefixInsertionHom [0, 0, 0, 1])).eq

theorem source_generators_not_commute :
    ¬ Commute sourceGeneratorA sourceGeneratorB := by
  intro hcommute
  apply generators_not_commute
  apply Commute.of_map
    (prefixInsertionHom_injective [0, 0, 0, 1])
  apply (commute_iff_eq _ _).2
  have heq := congrArg
    (fun x :
      localPrefixTranspositionGroup [0, 0, 0, 1] =>
      (x : BinaryLeavittˣ)) hcommute.eq
  simpa only [sourceGeneratorA, sourceGeneratorB, Subgroup.coe_mul]
    using heq

end ThompsonFLocalWitness

section

theorem sourceLocalPrefixTranspositionGroup_notLEF :
    ¬ LEF
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]) := by
  apply ThompsonFTwoRelatorLEF.not_lef_of_thompsonF_two_relations
    ThompsonFLocalWitness.sourceGeneratorA
    ThompsonFLocalWitness.sourceGeneratorB
    ThompsonFLocalWitness.source_relator_one
    ThompsonFLocalWitness.source_relator_two
    ThompsonFLocalWitness.source_generators_not_commute
  intro n x y hfirst hsecond
  exact ThompsonFFiniteQuotient.finite_group_commute_of_thompsonF_two_relations
    x y hfirst hsecond

end

namespace KunUnconditionalActualSourceDecomposition

open Filter Topology
open KunSourceUnconditionalFullDecomposition
open KunExactActualSourceAmbientGenerators
open KunUnconditionalActualSourceGeneratorData

theorem exists_unconditional_actual_source_dual_finpartition_sequences
    (A : SoficApproximation
      (prefixElementaryGroup
        ninePrefixCode)) :
    ∃ (SΓ : Finset
          (prefixElementaryGroup
            alphaPrefixCode))
      (SG : Finset
          (prefixElementaryGroup
            ninePrefixCode))
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ γG : ℝ),
      SG = sourceAmbientSymmetricGenerators SΓ ∧
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤ ∧
      1 ∈ SG ∧
      (∀ g ∈ SG, g⁻¹ ∈ SG) ∧
      Subgroup.closure
        (SG : Set
          (prefixElementaryGroup
            ninePrefixCode)) = ⊤ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ ∧
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    prefixElementaryGroup
                      alphaPrefixCode))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  prefixElementaryGroup
                    ninePrefixCode)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    prefixElementaryGroup
                      alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  prefixElementaryGroup
                    ninePrefixCode)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by
  classical
  obtain ⟨SΓ, PΓ, PG, honeΓ, hsymmetricΓ, hgeneratesΓ,
    hPΓ, honeG, hsymmetricG, hgeneratesG, hPG,
    hfaithful, hpositive⟩ :=
      exists_unconditional_actual_source_generator_data
  let SG := sourceAmbientSymmetricGenerators SΓ
  have hcoverΓ : PΓ.generators ⊆ SΓ := by
    rw [hPΓ]
  have hcoverG : PG.generators ⊆ SG := by
    dsimp [SG]
    rw [hPG]
  obtain ⟨γΓ, γG, QΓ, QG, hγΓ, hγG, hexpΓ,
    hexpG, hboundaryΓ, hboundaryG⟩ :=
      exists_source_subgroup_and_ambient_full_finpartition_sequences
        A sourceAlphaInclusion hfaithful
        PΓ PG SΓ SG honeΓ honeG hcoverΓ hcoverG
        hsymmetricΓ hsymmetricG hgeneratesΓ hgeneratesG
  exact ⟨SΓ, SG, QΓ, QG, γΓ, γG, rfl,
    honeΓ, hsymmetricΓ, hgeneratesΓ,
    honeG, hsymmetricG, hgeneratesG, hfaithful,
    hpositive, hγΓ, hγG, hexpΓ, hexpG,
    hboundaryΓ, hboundaryG⟩

end KunUnconditionalActualSourceDecomposition

open KunUnconditionalActualSourceDecomposition

namespace KunCombinedPrescribedRootSourceTolerance

open Filter Topology

theorem eventually_scaled_tolerance_lt
    (N t : ℕ → ℕ)
    (hN : ∀ n, 0 < N n)
    (ht : Tendsto (fun n => (t n : ℝ) / (N n : ℝ)) atTop (𝓝 0))
    (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell) :
    ∀ᶠ n in atTop, c * (t n : ℝ) < ell * (N n : ℝ) := by
  have hthreshold : 0 < ell / c := div_pos hell hc
  filter_upwards [ht.eventually (gt_mem_nhds hthreshold)] with n hn
  have hNreal : (0 : ℝ) < N n := by
    exact_mod_cast hN n
  have hratio : (t n : ℝ) < (ell / c) * (N n : ℝ) :=
    (div_lt_iff₀ hNreal).mp hn
  calc
    c * (t n : ℝ) < c * ((ell / c) * (N n : ℝ)) :=
      mul_lt_mul_of_pos_left hratio hc
    _ = ell * (N n : ℝ) := by
      field_simp

theorem exists_prescribed_radius_union_source_completed_tolerance
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hVpositive : ∀ n, 0 < Fintype.card (V n))
    (hV : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (root : (n : ℕ) → ℕ → Finset (V n))
    (source : (n : ℕ) → Finset (V n))
    (hroot : ∀ r : ℕ,
      Tendsto
        (fun n => ((root n r).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0))
    (hsource : Tendsto
      (fun n => ((source n).card : ℝ) / Fintype.card (V n))
      atTop (𝓝 0))
    (δ : ℕ → ℝ)
    (hδpositive : ∀ j, 0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (R : ℕ → ℕ) (hR : ∀ j, j ≤ R j)
    (d : ℕ) (hd : 0 < d)
    (ell q : ℝ) (hell : 0 < ell) (hq : q < 1) :
    ∃ m rootError t : ℕ → ℕ,
      Tendsto m atTop atTop ∧
      Tendsto (fun n => R (m n)) atTop atTop ∧
      Tendsto (fun n => δ (m n)) atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((root n (R (m n)) ∪ source n).card : ℝ) /
            (δ (m n) * (Fintype.card (V n) : ℝ))))
        atTop (𝓝 0) ∧
      (∀ n,
        rootError n =
          Nat.ceil (δ (m n) * (Fintype.card (V n) : ℝ))) ∧
      (∀ n,
        δ (m n) ≤
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ)) ∧
      Tendsto
        (fun n =>
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        t n =
          2 * d * (root n (R (m n)) ∪ source n).card +
            rootError n + 1) ∧
      (∀ n, 0 < t n) ∧
      (∀ n,
        2 * d * (root n (R (m n))).card ≤ t n) ∧
      (∀ n,
        2 * d * (source n).card ≤ t n) ∧
      (∀ n, rootError n ≤ t n) ∧
      Tendsto
        (fun n =>
          (t n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
          ell * (t n : ℝ) /
            (2 * (ell + 8 * (d : ℝ)) *
              (Fintype.card (V n) : ℝ))) ∧
      (∀ᶠ n in atTop,
        (10 : ℝ) * (t n : ℝ) <
          ell * (Fintype.card (V n) : ℝ)) ∧
      (∀ᶠ n in atTop,
        (5 : ℝ) *
            (4 + ell *
              (216 / ((d : ℝ) * (1 - q) ^ 2) +
                1 / (d : ℝ))) * (t n : ℝ) ≤
          ell * (Fintype.card (V n) : ℝ)) := by
  classical
  let N : ℕ → ℕ := fun n => Fintype.card (V n)
  let B : (n : ℕ) → ℕ → Finset (V n) :=
    fun n j => root n (R j) ∪ source n
  have hNpositive (n : ℕ) : (0 : ℝ) < N n := by
    exact_mod_cast hVpositive n
  have hunion (j : ℕ) :
      Tendsto
        (fun n => ((B n j).card : ℝ) / (N n : ℝ))
        atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n =>
          ((root n (R j)).card : ℝ) / Fintype.card (V n) +
            ((source n).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
      simpa only [zero_add] using (hroot (R j)).add hsource
    refine squeeze_zero (fun n => by positivity) ?_ hsum
    intro n
    have hcard :
        ((B n j).card : ℝ) ≤
          ((root n (R j)).card : ℝ) +
            ((source n).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (root n (R j)) (source n)
    calc
      ((B n j).card : ℝ) / (N n : ℝ) ≤
          (((root n (R j)).card : ℝ) +
            ((source n).card : ℝ)) / (N n : ℝ) :=
        div_le_div_of_nonneg_right hcard (hNpositive n).le
      _ = ((root n (R j)).card : ℝ) / Fintype.card (V n) +
            ((source n).card : ℝ) / Fintype.card (V n) := by
        dsimp [N]
        ring
  let e : ℕ → ℕ → ℝ := fun n j =>
    (((B n j).card : ℝ) / (N n : ℝ)) / δ j
  have hepositive (n j : ℕ) : 0 ≤ e n j := by
    dsimp [e]
    exact div_nonneg
      (div_nonneg (Nat.cast_nonneg _) (hNpositive n).le)
      (hδpositive j).le
  have hevanishes (j : ℕ) :
      Tendsto (fun n => e n j) atTop (𝓝 0) := by
    simpa only [zero_div] using (hunion j).div_const (δ j)
  obtain ⟨m, hm, herror⟩ :=
    exists_diverging_radius_with_vanishing_diagonal_error
      e hepositive hevanishes
  have hδm : Tendsto (fun n => δ (m n)) atTop (𝓝 0) :=
    hδ.comp hm
  have hRm : Tendsto (fun n => R (m n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hR (m n)) hm
  have hrelative : Tendsto
      (fun n =>
        ((B n (m n)).card : ℝ) /
          (δ (m n) * (N n : ℝ)))
      atTop (𝓝 0) := by
    convert herror using 1
    funext n
    dsimp [e]
    ring
  have hbadselected : Tendsto
      (fun n => ((B n (m n)).card : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hp := hrelative.mul hδm
    convert hp using 1
    · funext n
      have hne : δ (m n) ≠ 0 := (hδpositive (m n)).ne'
      rw [div_mul_eq_mul_div, mul_comm _ (δ (m n)),
        mul_div_mul_left _ _ hne]
    · norm_num
  have honeover : Tendsto
      (fun n => (1 : ℝ) / (N n : ℝ))
      atTop (𝓝 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hV
  let rootError : ℕ → ℕ :=
    fun n => Nat.ceil (δ (m n) * (N n : ℝ))
  have hrootlower (n : ℕ) :
      δ (m n) ≤ (rootError n : ℝ) / (N n : ℝ) := by
    apply (le_div_iff₀ (hNpositive n)).2
    exact Nat.le_ceil _
  have hrootupper (n : ℕ) :
      (rootError n : ℝ) / (N n : ℝ) ≤
        δ (m n) + 1 / (N n : ℝ) := by
    apply (div_le_iff₀ (hNpositive n)).2
    have hceil :=
      (Nat.ceil_lt_add_one
        (mul_nonneg (hδpositive (m n)).le
          (hNpositive n).le)).le
    have hone : (1 / (N n : ℝ)) * (N n : ℝ) = 1 := by
      field_simp [ne_of_gt (hNpositive n)]
    change (rootError n : ℝ) ≤ _
    dsimp [rootError] at hceil ⊢
    linarith only [hceil, hone]
  have hrootlimit : Tendsto
      (fun n => (rootError n : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun n => δ (m n) + 1 / (N n : ℝ))
        atTop (𝓝 0) := by
      simpa only [one_div, add_zero] using hδm.add honeover
    exact squeeze_zero (fun n => by positivity) hrootupper hupper
  let t : ℕ → ℕ :=
    fun n => 2 * d * (B n (m n)).card + rootError n + 1
  have htpositive (n : ℕ) : 0 < t n := by
    dsimp [t]
    omega
  have hrootbudget (n : ℕ) :
      2 * d * (root n (R (m n))).card ≤ t n := by
    have hsub :
        root n (R (m n)) ⊆ B n (m n) := by
      dsimp [B]
      exact Finset.subset_union_left
    have hcard := Finset.card_le_card hsub
    have hmul :
        2 * d * (root n (R (m n))).card ≤
          2 * d * (B n (m n)).card :=
      Nat.mul_le_mul_left (2 * d) hcard
    dsimp [t]
    omega
  have hsourcebudget (n : ℕ) :
      2 * d * (source n).card ≤ t n := by
    have hsub : source n ⊆ B n (m n) := by
      dsimp [B]
      exact Finset.subset_union_right
    have hcard := Finset.card_le_card hsub
    have hmul :
        2 * d * (source n).card ≤
          2 * d * (B n (m n)).card :=
      Nat.mul_le_mul_left (2 * d) hcard
    dsimp [t]
    omega
  have hrooterrorbudget (n : ℕ) : rootError n ≤ t n := by
    dsimp [t]
    omega
  have htzero : Tendsto
      (fun n => (t n : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n =>
          ((2 * d : ℕ) : ℝ) *
            (((B n (m n)).card : ℝ) / (N n : ℝ)))
        atTop (𝓝 0) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_zero] using hbadselected.const_mul ((2 * d : ℕ)
        : ℝ)
    have hsum := (hscaled.add hrootlimit).add honeover
    convert hsum using 1
    · funext n
      dsimp [t]
      push_cast
      ring
    · norm_num
  have hdreal : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hden : 0 < (2 : ℝ) * (ell + 8 * (d : ℝ)) := by
    positivity
  have htarget (n : ℕ) :
      ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
        ell * (t n : ℝ) /
          (2 * (ell + 8 * (d : ℝ)) * (N n : ℝ)) := by
    have hratio : δ (m n) ≤ (t n : ℝ) / (N n : ℝ) := by
      calc
        δ (m n) ≤ (rootError n : ℝ) / (N n : ℝ) :=
          hrootlower n
        _ ≤ (t n : ℝ) / (N n : ℝ) := by
          apply div_le_div_of_nonneg_right
            (by exact_mod_cast hrooterrorbudget n)
            (hNpositive n).le
    calc
      ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
          ell * ((t n : ℝ) / (N n : ℝ)) /
            (2 * (ell + 8 * (d : ℝ))) := by
        apply div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hell.le) hden.le
      _ = ell * (t n : ℝ) /
            (2 * (ell + 8 * (d : ℝ)) * (N n : ℝ)) := by
        field_simp [ne_of_gt (hNpositive n), ne_of_gt hden]
  have hten :
      ∀ᶠ n in atTop,
        (10 : ℝ) * (t n : ℝ) < ell * (N n : ℝ) :=
    eventually_scaled_tolerance_lt
      N t (fun n => hVpositive n) htzero
      10 ell (by norm_num) hell
  let c : ℝ :=
    5 * (4 + ell *
      (216 / ((d : ℝ) * (1 - q) ^ 2) + 1 / (d : ℝ)))
  have hdiff : 0 < 1 - q := sub_pos.mpr hq
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hspectral :
      ∀ᶠ n in atTop,
        c * (t n : ℝ) ≤ ell * (N n : ℝ) :=
    (eventually_scaled_tolerance_lt
      N t (fun n => hVpositive n) htzero c ell hc hell).mono
      fun _ h => h.le
  refine ⟨m, rootError, t, hm, hRm, hδm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [B, N] using hrelative
  · intro n
    rfl
  · simpa only [N] using hrootlower
  · simpa only [N] using hrootlimit
  · intro n
    rfl
  · exact htpositive
  · exact hrootbudget
  · exact hsourcebudget
  · exact hrooterrorbudget
  · simpa only [N] using htzero
  · simpa only [N] using htarget
  · simpa only [N] using hten
  · simpa only [N, c] using hspectral

end KunCombinedPrescribedRootSourceTolerance

open KunCombinedPrescribedRootSourceTolerance

namespace KunLiteralSourceSelectedComponents

open Filter Topology
open scoped BigOperators Pointwise

def sourceConjugacyDisagreementBad
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    (u g : G) (n : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  exact Finset.univ.filter fun x =>
    (A.model n).action (u * g * u⁻¹) x ≠
      ((A.model n).action u * (A.model n).action g *
        ((A.model n).action u)⁻¹) x

theorem sourceConjugacyDisagreementBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    (u g : G) :
    Tendsto
      (fun n =>
        ((sourceConjugacyDisagreementBad A u g n).card : ℝ) /
          (A.model n).size)
      atTop (nhds 0) := by
  classical
  simpa only [sourceConjugacyDisagreementBad, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
    Function.comp_apply,
    ne_eq, normalizedHamming, hammingDist, Fintype.card_fin] using
    SourceCompressionTransportCrossing.tendsto_action_conjugate A u g

end KunLiteralSourceSelectedComponents

namespace KunActualBothTransportedOverlapScales

open Filter Topology
open scoped BigOperators

theorem source_both_transported_generator_boundary_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                  (SourceBothCompressionNormalization.sourceCompressionTable j) *
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode)) *
                ((A.model n).action
                  (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
            C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0) := by
  classical
  have hsource' : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  (i : prefixElementaryGroup
                    alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0) := by
    exact hsource
  intro j
  have hcross (i : ↥S) : Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j) *
            (A.model n).action
              (SourceBothCompressionNormalization.sourceAlphaElement
                (i : prefixElementaryGroup
                  alphaPrefixCode)) *
            ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card :
                ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
    obtain ⟨k, hk⟩ :=
      SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
        j (i : prefixElementaryGroup
          alphaPrefixCode)
    have hword :=
      SourceGeneratedWordCrossing.source_alpha_word_crossing_density_tendsto_zero
        A S hsymmetric hgenerates Q hsource' k
    have hword' : Tendsto
        (fun n =>
          ((partitionWordCrossing (Q n)
            ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j *
                SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode) *
                (SourceBothCompressionNormalization.sourceCompressionTable j)⁻¹))).card
                  : ℝ) /
                (A.model n).size)
        atTop (nhds 0) := by
      rw [hk]
      exact hword
    exact
      SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
        A
        (SourceBothCompressionNormalization.sourceCompressionTable j)
        (SourceBothCompressionNormalization.sourceAlphaElement
          (i : prefixElementaryGroup
            alphaPrefixCode))
        Q hword'
  have hsum : Tendsto
      (fun n =>
        ∑ i : ↥S,
          ((partitionWordCrossing (Q n)
            ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card
                  : ℝ) /
                (A.model n).size)
      atTop (nhds 0) := by
    simpa only [Finset.univ_eq_attach, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hcross i)
  have hidentity (n : ℕ) :
      (∑ C ∈ (Q n).parts,
        (boundary
          (fun i : ↥S =>
            (A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
          C : ℝ)) / (A.model n).size =
        ∑ i : ↥S,
          ((partitionWordCrossing (Q n)
            ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card
                  : ℝ) /
                (A.model n).size := by
    have hnat :=
      SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
        (Q n)
        (fun i : ↥S =>
          (A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j) *
            (A.model n).action
              (SourceBothCompressionNormalization.sourceAlphaElement
                (i : prefixElementaryGroup
                  alphaPrefixCode)) *
            ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
    have hreal :
        (∑ i : ↥S,
          ((partitionWordCrossing (Q n)
            ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card
                  : ℝ)) =
          ∑ C ∈ (Q n).parts,
            (boundary
              (fun i : ↥S =>
                (A.model n).action
                    (SourceBothCompressionNormalization.sourceCompressionTable j) *
                  (A.model n).action
                    (SourceBothCompressionNormalization.sourceAlphaElement
                      (i : prefixElementaryGroup
                        alphaPrefixCode)) *
                  ((A.model n).action
                    (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
              C : ℝ) := by
      exact_mod_cast hnat
    rw [← hreal, Finset.sum_div]
  rw [show
    (fun n =>
      (∑ C ∈ (Q n).parts,
        (boundary
          (fun i : ↥S =>
            (A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
          C : ℝ)) / (A.model n).size) =
      (fun n =>
        ∑ i : ↥S,
          ((partitionWordCrossing (Q n)
            ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode)) *
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card
                  : ℝ) /
                (A.model n).size) from funext hidentity]
  exact hsum

theorem exists_source_both_common_slow_overlap_scales
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexpand : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
      Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧
      Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ insufficientOverlapComponents
            (transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j)))
            (Q n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (nhds 0)) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))).parts,
            ((C.card : ℝ) -
              ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
                (A.model n).size)
        atTop (nhds 0)) ∧
      ∃ N : ℕ, ∀ n : ℕ, eta (n + N) < 1 := by
  classical
  have hnonempty (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let : ∀ n, Nonempty (Fin (A.model n).size) := hnonempty
  let σ : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n i =>
      (A.model n).action
        (SourceBothCompressionNormalization.sourceAlphaElement
          (i : prefixElementaryGroup
            alphaPrefixCode))
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (SourceBothCompressionNormalization.sourceCompressionTable j)
  have hsource' : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary (σ n) C : ℝ)) /
            Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    simpa only [σ, Fintype.card_fin] using hsource
  have htarget : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i => T n j * σ n i * (T n j)⁻¹) C : ℝ)) /
              Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    intro j
    simpa only [σ, T, Fintype.card_fin] using
      source_both_transported_generator_boundary_density_tendsto_zero
        A S hsymmetric hgenerates Q hsource j
  obtain ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, hoverlap⟩ :=
    KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
      Q σ T gamma hgamma
      (by
        intro n C hC E hE hhalf
        simpa only [σ] using hexpand n C hC E hE hhalf)
      hsource' htarget
  have hloss : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    intro j
    apply
      KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
        (fun n =>
          transportedUnivFinpartition (Q n) (T n j))
        Q (fun n i => T n j * σ n i * (T n j)⁻¹)
        gamma hgamma
    · intro n
      exact
        KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
          (Q n) (σ n) (T n j) gamma
          (fun C hC E hE hhalf =>
            by simpa only [σ] using hexpand n C hC E hE hhalf)
    · exact
        KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
          Q σ (fun n => T n j) hsource'
    · exact htarget j
  have htail : ∃ N : ℕ, ∀ n : ℕ, eta (n + N) < 1 := by
    have heventually : ∀ᶠ n in atTop, eta n < 1 :=
      heta0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
    refine ⟨N, ?_⟩
    intro n
    apply hN
    omega
  refine ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, ?_, ?_, htail⟩
  · intro j
    simpa only [T, Fintype.card_fin] using hoverlap j
  · intro j
    simpa only [T, Fintype.card_fin] using hloss j

end KunActualBothTransportedOverlapScales
namespace SourceProductThroughAlpha

open Filter Topology
open scoped BigOperators

universe v

def sourceCompressionUAlphaHom :
    prefixElementaryGroup alphaPrefixCode →*
      prefixElementaryGroup alphaZeroPrefixCode :=
  ((MulAut.conj compressionU).toMonoidHom.comp
    (prefixElementaryGroup
      alphaPrefixCode).subtype).codRestrict
        (prefixElementaryGroup
          alphaZeroPrefixCode)
        (by
          intro g
          rw [← compressionU_map_alphaPrefixElementaryGroup]
          exact ⟨g.val, g.property, rfl⟩)

noncomputable def sourceCompressionUAlphaEquiv :
    prefixElementaryGroup alphaPrefixCode ≃*
      prefixElementaryGroup alphaZeroPrefixCode := by
  apply MulEquiv.ofBijective sourceCompressionUAlphaHom
  constructor
  · intro g g' heq
    apply Subtype.ext
    apply (MulAut.conj compressionU).injective
    exact congrArg
      (fun k : prefixElementaryGroup
          alphaZeroPrefixCode =>
        (k : BinaryLeavittˣ)) heq
  · intro k
    have hk :
        (k : BinaryLeavittˣ) ∈
          (prefixElementaryGroup
            alphaPrefixCode).map
              (MulAut.conj compressionU).toMonoidHom := by
      rw [compressionU_map_alphaPrefixElementaryGroup]
      exact k.property
    obtain ⟨g, hg, heq⟩ := hk
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact heq

noncomputable def sourceCompressedGeneratingFinset
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    Finset
      (prefixElementaryGroup alphaZeroPrefixCode) := by
  classical
  exact SΓ.image sourceCompressionUAlphaEquiv

theorem sourceCompressedGeneratingFinset_one_mem
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hone : 1 ∈ SΓ) :
    1 ∈ sourceCompressedGeneratingFinset SΓ := by
  classical
  change 1 ∈ SΓ.image sourceCompressionUAlphaEquiv
  exact Finset.mem_image.mpr
    ⟨1, hone, map_one sourceCompressionUAlphaEquiv⟩

theorem sourceCompressedGeneratingFinset_inv_mem
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (k : prefixElementaryGroup
      alphaZeroPrefixCode)
    (hk : k ∈ sourceCompressedGeneratingFinset SΓ) :
    k⁻¹ ∈ sourceCompressedGeneratingFinset SΓ := by
  classical
  change k ∈ SΓ.image sourceCompressionUAlphaEquiv at hk
  change k⁻¹ ∈ SΓ.image sourceCompressionUAlphaEquiv
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hk
  exact Finset.mem_image.mpr
    ⟨g⁻¹, hsymmetric g hg,
      map_inv sourceCompressionUAlphaEquiv g⟩

theorem sourceCompressedGeneratingFinset_closure
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤) :
    Subgroup.closure
      (sourceCompressedGeneratingFinset SΓ : Set
        (prefixElementaryGroup
          alphaZeroPrefixCode)) = ⊤ := by
  classical
  change Subgroup.closure
    ((SΓ.image sourceCompressionUAlphaEquiv : Finset
      (prefixElementaryGroup
        alphaZeroPrefixCode)) : Set
          (prefixElementaryGroup
            alphaZeroPrefixCode)) = ⊤
  rw [Finset.coe_image]
  change
    Subgroup.closure
      (sourceCompressionUAlphaEquiv.toMonoidHom ''
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode))) = ⊤
  rw [← MonoidHom.map_closure, hgenerates,
    Subgroup.map_top_of_surjective
      sourceCompressionUAlphaEquiv.toMonoidHom
      sourceCompressionUAlphaEquiv.surjective]

theorem exists_sourceCompressedKazhdanPair_with_same_generators
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤) :
    ∃ P : KazhdanPair.{0, v}
        (prefixElementaryGroup
          alphaZeroPrefixCode),
      P.generators = sourceCompressedGeneratingFinset SΓ := by
  let : HasPropertyT.{0, v}
      (prefixElementaryGroup
        alphaZeroPrefixCode) :=
    alphaZeroPrefixElementaryGroup_hasPropertyT_unconditional
  exact
    KunExactKazhdanGeneratorChange.exists_kazhdanPair_with_exact_symmetric_generators
      (sourceCompressedGeneratingFinset SΓ)
      (sourceCompressedGeneratingFinset_inv_mem SΓ hsymmetric)
      (sourceCompressedGeneratingFinset_closure SΓ hgenerates)

def sourceCompressedLocalProductToAlpha :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]) →*
      prefixElementaryGroup alphaPrefixCode :=
  ThompsonPrefixInsertion.sourceCompressedLocalProductHom.codRestrict
      (prefixElementaryGroup alphaPrefixCode)
      (by
        intro x
        change
          (x.1 : BinaryLeavittˣ) *
            (x.2 : BinaryLeavittˣ) ∈
              prefixElementaryGroup alphaPrefixCode
        exact
          (prefixElementaryGroup
            alphaPrefixCode).mul_mem
              (alphaZero_prefixElementaryGroup_le x.1.property)
              (ThompsonPrefixInsertion.sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord
                  x.2.property))

theorem sourceCompressedLocalProductEmbedding_factors_through_alpha :
    SourceGeneratedWordCrossing.sourceAlphaInclusion.comp
        sourceCompressedLocalProductToAlpha =
      ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem source_compressed_local_product_word_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (z : prefixElementaryGroup
          alphaZeroPrefixCode ×
        ThompsonPrefixInsertion.localPrefixTranspositionGroup
            [0, 0, 0, 1]) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action
            (ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
              z))).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hfactor :
      SourceGeneratedWordCrossing.sourceAlphaInclusion
          (sourceCompressedLocalProductToAlpha z) =
        ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
          z := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        sourceCompressedLocalProductEmbedding_factors_through_alpha z
  have hword :=
    SourceGeneratedWordCrossing.source_alpha_word_crossing_density_tendsto_zero
        A SΓ hsymmetric hgenerates Q hboundary
          (sourceCompressedLocalProductToAlpha z)
  simpa only [hfactor] using hword

theorem source_compressed_local_product_ball_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (I : ℕ → Finset
      (prefixElementaryGroup
          alphaZeroPrefixCode ×
        ThompsonPrefixInsertion.localPrefixTranspositionGroup
            [0, 0, 0, 1]))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((∑ z ∈ I k,
          (partitionWordCrossing (Q n)
            ((A.model n).action
              (ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                z))).card : ℕ) : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ∑ z ∈ I k,
            ((partitionWordCrossing (Q n)
              ((A.model n).action
                (ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                  z))).card : ℝ) /
                (A.model n).size)
        atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (I k)
        (fun z _ =>
          source_compressed_local_product_word_crossing_density_tendsto_zero A SΓ hsymmetric
            hgenerates Q hboundary z)
  simpa only [Nat.cast_sum, Finset.sum_div] using hsum

def sourceCompressedLocalProductApproximation
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode)) :
    SoficApproximation
      (prefixElementaryGroup
          alphaZeroPrefixCode ×
        ThompsonPrefixInsertion.localPrefixTranspositionGroup
            [0, 0, 0, 1]) :=
  pullbackSoficApproximation
    ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
    ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding_injective
    A

@[simp]
theorem sourceCompressedLocalProductApproximation_model_size
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (n : ℕ) :
    ((sourceCompressedLocalProductApproximation A).model n).size =
      (A.model n).size := by
  rfl

theorem source_canonical_product_radius_crossing_density_tendsto_zero
    [DecidableEq
      (prefixElementaryGroup
        alphaZeroPrefixCode)]
    [DecidableEq
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
          [0, 0, 0, 1])]
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
          [0, 0, 0, 1]))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((∑ z ∈
          CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (sourceCompressedGeneratingFinset SΓ) F k,
          (partitionWordCrossing (Q n)
            (((sourceCompressedLocalProductApproximation A).model n).action
              z)).card : ℕ) : ℝ) /
            ((sourceCompressedLocalProductApproximation A).model n).size)
      atTop (𝓝 0) := by
  change
    Tendsto
      (fun n =>
        ((∑ z ∈
          CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (sourceCompressedGeneratingFinset SΓ) F k,
          (partitionWordCrossing (Q n)
            ((A.model n).action
              (ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                z))).card : ℕ) : ℝ) /
              (A.model n).size)
      atTop (𝓝 0)
  exact
    source_compressed_local_product_ball_crossing_density_tendsto_zero
      A SΓ hsymmetric hgenerates Q hboundary
      (fun r =>
        CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
            (sourceCompressedGeneratingFinset SΓ) F r)
      k

end SourceProductThroughAlpha

namespace SourceRetainedActualMatching

open Filter Topology
open scoped BigOperators symmDiff

noncomputable def logarithmicComponentRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (H r : ℝ) : V → ℤ :=
  MidrankPermutationEnergy.offsetFloorRank
    (fun x => Real.log (partitionComponentSize Q x : ℝ))
    H r

noncomputable def retainedTransportedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (H r eta : ℝ) : Finset (Finset V) :=
  SourceCompressionRetainedDiscard.retainedComponents
    (transportedUnivFinpartition Q T) Q T
    (logarithmicComponentRank Q H r) eta

theorem retained_transport_component_matching_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V)
    (H r eta : ℝ) (hH : 0 < H)
    (C : Finset V)
    (hC : C ∈ retainedTransportedComponents Q T H r eta) :
    maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ maximumOverlapPart Q C).card : ℝ) ∧
      ((C ∆ maximumOverlapPart Q C).card : ℝ) <
        (Real.exp H - 1 + 2 * eta) * (C.card : ℝ) ∧
      (2 * (Real.exp H - 1 + 2 * eta) < 1 →
        (maximumOverlapPart Q C).card <
          2 * (C ∩ maximumOverlapPart Q C).card) := by
  classical
  have hret :
      C ∈ SourceCompressionRetainedDiscard.retainedComponents
        (transportedUnivFinpartition Q T) Q T
        (logarithmicComponentRank Q H r) eta := by
    exact hC
  obtain ⟨hpart, htarget, hoverlap, y, hy, hrank⟩ :=
    SourceCompressionRetainedDiscard.retainedComponents_spec
      (transportedUnivFinpartition Q T) Q T
      (logarithmicComponentRank Q H r) eta C hret
  have hpartImage := hpart
  rw [transportedUnivFinpartition_parts] at hpartImage
  obtain ⟨C₀, hC₀, hmap⟩ := Finset.mem_image.mp hpartImage
  have hyMap : y ∈ C₀.map T.toEmbedding := by
    rw [hmap]
    exact (Finset.mem_inter.mp hy).1
  obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hyMap
  have hxy' : T x = y := hxy
  have hTx :
      T x ∈ maximumOverlapPart Q
        (C₀.map T.toEmbedding) := by
    rw [hmap]
    simpa only [hxy'] using (Finset.mem_inter.mp hy).2
  have hfloor :
      MidrankPermutationEnergy.offsetFloorRank
        (fun z : V =>
          Real.log (partitionComponentSize Q z : ℝ))
        H r (T x) =
      MidrankPermutationEnergy.offsetFloorRank
        (fun z : V =>
          Real.log (partitionComponentSize Q z : ℝ))
        H r x := by
    have heq :
        logarithmicComponentRank Q H r (T x) =
          logarithmicComponentRank Q H r x := by
      calc
        logarithmicComponentRank Q H r (T x) =
            logarithmicComponentRank Q H r y :=
          congrArg (logarithmicComponentRank Q H r) hxy'
        _ = logarithmicComponentRank Q H r (T.symm y) :=
          hrank.symm
        _ = logarithmicComponentRank Q H r x := by
          rw [← hxy', Equiv.symm_apply_apply]
    exact heq
  have hsize :=
    SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
      Q T C₀ hC₀ H r hH x hx hTx hfloor
  rw [hmap] at hsize
  have hcard : C.card = C₀.card := by
    rw [← hmap, Finset.card_map]
  rw [← hcard] at hsize
  have hsymmetric :=
    SourceCompressionMatching.symmDiff_card_lt_of_overlap_and_exp_card
      C (maximumOverlapPart Q C) H eta
      hoverlap hsize
  refine ⟨htarget, hoverlap, hsymmetric, ?_⟩
  intro hsmall
  exact
    SourceCompressionMatching.target_majority_of_overlap_and_exp_card
      C (maximumOverlapPart Q C)
      ((transportedUnivFinpartition Q T).nonempty_of_mem_parts hpart)
      H eta hoverlap hsize hsmall

theorem retained_source_transport_matching_of_ambient_midrank_variance
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (κ : Type*)
    (Q A : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (H r eta : ℕ → ℝ)
    (hHpos : ∀ n, 0 < H n)
    (hHzero : Tendsto H atTop (nhds 0))
    (heta0 : ∀ n, 0 ≤ eta n)
    (hetazero : Tendsto eta atTop (nhds 0))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (A n).parts,
          (C.card : ℝ) *
            midrankVariance
              (componentRankMassList C
                (logarithmicComponentRank (Q n) (H n) (r n)))) /
                  Fintype.card (V n))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((partitionWordCrossing
          (A n) (T n i).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ i : κ, Tendsto
      (fun n =>
        ((∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition (Q n) (T n i))
          (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ,
      (∀ n, retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) ⊆
          (transportedUnivFinpartition
            (Q n) (T n i)).parts) ∧
      (∀ n C, C ∈ retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) →
          maximumOverlapPart (Q n) C ∈ (Q n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) →
              (maximumOverlapPart (Q n) C).card <
                2 * (C ∩ maximumOverlapPart
                  (Q n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) \
            matchedRetainedSupport
              (retainedTransportedComponents
                (Q n) (T n i) (H n) (r n) (eta n))).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n),
              (C ∆ maximumOverlapPart (Q n) C).card :
                ℕ) : ℝ) / Fintype.card (V n))
        atTop (nhds 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (maximumOverlapPart (Q n))
          ((retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) :
              Finset (Finset (V n))) :
                Set (Finset (V n)))) := by
  let b : (n : ℕ) → V n → ℤ :=
    fun n => logarithmicComponentRank (Q n) (H n) (r n)
  obtain ⟨_j, _hj, _homit, hrank⟩ :=
    KunCommonRankArcInvariance.exists_common_rank_invariance_of_midrank_variance
      A b (fun n i => (T n i).symm) hvariance hcross
  intro i
  let P : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)) :=
    fun n => transportedUnivFinpartition (Q n) (T n i)
  let R : (n : ℕ) → Finset (Finset (V n)) :=
    fun n => retainedTransportedComponents
      (Q n) (T n i) (H n) (r n) (eta n)
  have hparts (n : ℕ) : R n ⊆ (P n).parts := by
    exact Finset.sdiff_subset
  have htarget (n : ℕ) (C : Finset (V n)) (hC : C ∈ R n) :
      maximumOverlapPart (Q n) C ∈ (Q n).parts :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).1
  have hmajor (n : ℕ)
      (_heta : eta n ≤ (1 : ℝ) / 2)
      (hsmall : 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1)
      (C : Finset (V n)) (hC : C ∈ R n) :
      (maximumOverlapPart (Q n) C).card <
        2 * (C ∩ maximumOverlapPart (Q n) C).card :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).2.2.2 hsmall
  have hbound (n : ℕ) (C : Finset (V n)) (hC : C ∈ R n) :
      ((C ∆ maximumOverlapPart (Q n) C).card : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ) :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).2.2.1.le
  have hdiscard :
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) \
            matchedRetainedSupport (R n)).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) := by
    exact
      SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
        V P Q (fun n => T n i) b eta hetazero
        (hoverlap i) (hrank i)
  have hsymmetric :
      Tendsto
        (fun n =>
          ((∑ C ∈ R n,
            (C ∆ maximumOverlapPart (Q n) C).card :
              ℕ) : ℝ) / Fintype.card (V n))
        atTop (nhds 0) := by
    have hfull (n : ℕ) :
        (Finset.univ : Finset (V n)).Nonempty :=
      Finset.univ_nonempty
    simpa only [Finset.card_univ] using
      SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
        (V := V) (fun n => (Finset.univ : Finset (V n))) hfull
        P R hparts (fun n => maximumOverlapPart (Q n))
        H eta (fun n => (hHpos n).le) heta0 hHzero hetazero
        hbound
  refine ⟨hparts, htarget, hmajor, hdiscard, hsymmetric, ?_⟩
  intro n hsmall
  exact finpartition_dominant_matching_injOn
    (P n) (R n) (hparts n)
    (maximumOverlapPart (Q n))
    (fun C hC =>
      (retained_transport_component_matching_bounds
        (Q n) (T n i) (H n) (r n) (eta n)
        (hHpos n) C hC).2.2.2 hsmall)

end SourceRetainedActualMatching

namespace KunActualBothTransportedOverlapScales

open Filter Topology
open scoped BigOperators

theorem exists_source_both_capped_overlap_scales
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexpand : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (SourceBothCompressionNormalization.sourceAlphaElement
                  (i : prefixElementaryGroup
                    alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
      (∀ n, eta n < 1) ∧
      Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧
      Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ insufficientOverlapComponents
            (transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j)))
            (Q n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (nhds 0)) ∧
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SourceBothCompressionNormalization.sourceCompressionTable j))).parts,
            ((C.card : ℝ) -
              ((C ∩ maximumOverlapPart (Q n) C).card : ℝ))) /
                (A.model n).size)
        atTop (nhds 0) := by
  classical
  obtain ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, hoverlap, hloss, _htail⟩ :=
    exists_source_both_common_slow_overlap_scales
      A S hsymmetric hgenerates Q gamma hgamma hexpand hsource
  let capped : ℕ → ℝ := fun n => min (eta n) ((1 : ℝ) / 2)
  have heventually : ∀ᶠ n in atTop, eta n < (1 : ℝ) / 2 :=
    heta0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heq : capped =ᶠ[atTop] eta := by
    filter_upwards [heventually] with n hn
    exact min_eq_left hn.le
  have hcappedpositive (n : ℕ) : 0 < capped n := by
    exact lt_min (heta n) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcappedone (n : ℕ) : capped n < 1 := by
    have hhalf : capped n ≤ (1 : ℝ) / 2 :=
      min_le_right _ _
    linarith
  have hcappedanti : Antitone capped := by
    intro m n hmn
    exact min_le_min (hetaanti hmn) (le_refl ((1 : ℝ) / 2))
  have hcappedzero : Tendsto capped atTop (nhds 0) :=
    heta0.congr' heq.symm
  have hcappedratio : Tendsto
      (fun n => capped n / H n) atTop (nhds 0) := by
    have heqratio :
        (fun n => capped n / H n) =ᶠ[atTop]
          (fun n => eta n / H n) := by
      filter_upwards [heq] with n hn
      rw [hn]
    exact hratio.congr' heqratio.symm
  refine ⟨capped, H, hcappedpositive, hcappedone, hcappedanti,
    hcappedzero, hH, hHanti, hH0, hcappedratio, ?_, hloss⟩
  intro j
  have heqoverlap :
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j)))
          (Q n) (capped n), (C.card : ℝ)) /
            (A.model n).size) =ᶠ[atTop]
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              (SourceBothCompressionNormalization.sourceCompressionTable j)))
          (Q n) (eta n), (C.card : ℝ)) /
            (A.model n).size) := by
    filter_upwards [heq] with n hn
    rw [hn]
  exact (hoverlap j).congr' heqoverlap.symm

end KunActualBothTransportedOverlapScales

namespace KunLiteralNineSourceCompletedCentralizerModels

open Filter Topology
open scoped BigOperators

theorem sourceAmbientGeneratedWord_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup ninePrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup ninePrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (i : prefixElementaryGroup
                  ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (g : prefixElementaryGroup ninePrefixCode) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          ((A.model n).action g)).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  simpa only [MonoidHom.id_apply] using
    SourceGeneratedWordCrossing.fixed_generated_word_crossing_density_tendsto_zero
        A (MonoidHom.id _) S hsymmetric hgenerates Q hboundary g

theorem sourceAmbientFiniteFamily_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup ninePrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup ninePrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (i : prefixElementaryGroup
                  ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (ι : Type*) [Fintype ι]
    (g : ι →
      prefixElementaryGroup ninePrefixCode) :
    Tendsto
      (fun n =>
        (∑ i : ι,
          ((partitionWordCrossing (Q n)
            ((A.model n).action (g i))).card : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n =>
        ∑ i : ι,
          ((partitionWordCrossing (Q n)
            ((A.model n).action (g i))).card : ℝ) /
              (A.model n).size)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset ι)
        (fun i _ => sourceAmbientGeneratedWord_crossing_density_tendsto_zero A S hsymmetric
          hgenerates Q hboundary (g i))
  simpa only [Finset.sum_div] using hsum

theorem sourceAmbientActualInverse_crossing_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup ninePrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup ninePrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                (i : prefixElementaryGroup
                  ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (g : prefixElementaryGroup ninePrefixCode) :
    Tendsto
      (fun n =>
        ((partitionWordCrossing (Q n)
          (((A.model n).action g)⁻¹)).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hlabel :=
    sourceAmbientGeneratedWord_crossing_density_tendsto_zero
      A S hsymmetric hgenerates Q hboundary (g⁻¹)
  have hinverse :=
    KunCommonRankArcInvariance.sofic_action_inverse_normalizedHamming_tendsto_zero
      A g
  simpa only [Fintype.card_fin] using
    SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
        Q (fun n => ((A.model n).action g)⁻¹)
          (fun n => (A.model n).action (g⁻¹))
          (by simpa only [Fintype.card_fin] using hlabel)
          hinverse

theorem exists_source_common_log_rank_with_ambient_midrank_variance
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (SG : Finset
      (prefixElementaryGroup ninePrefixCode))
    (QΓ QG : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (γG : ℝ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesG : Subgroup.closure
      (SG : Set
        (prefixElementaryGroup ninePrefixCode)) =
          ⊤)
    (hpositive : Subgroup.closure
      (Set.range
        (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ)) = ⊤)
    (hγG : 0 < γG)
    (hexpandG : ∀ n C, C ∈ (QG n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SG =>
                (A.model n).action
                  (i : prefixElementaryGroup
                    ninePrefixCode)) E : ℝ))
    (hboundaryΓ : Tendsto
      (fun n =>
        (∑ C ∈ (QΓ n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (KunExactActualSourceAmbientGenerators.sourceAlphaInclusion
                  (i : prefixElementaryGroup
                    alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (hboundaryG : Tendsto
      (fun n =>
        (∑ C ∈ (QG n).parts,
          (boundary
            (fun i : ↥SG =>
              (A.model n).action
                (i : prefixElementaryGroup
                  ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (𝓝 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (𝓝 0))
    (hoverlap : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ insufficientOverlapComponents
          (transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j)))
          (QΓ n) (eta n), (C.card : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (hloss : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))).parts,
          ((C.card : ℝ) -
            ((C ∩ maximumOverlapPart (QΓ n) C).card : ℝ))) /
              (A.model n).size)
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (C.card : ℝ) *
              midrankVariance
                (componentRankMassList C
                  (SourceCommonOffsetMidrankEnergy.componentLogRank
                    (QΓ n) (H n) (r n)))) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          ((partitionWordCrossing (QG n)
            (((A.model n).action
              (KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))⁻¹)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0)) := by
  classical
  let : ∀ n, Nonempty (Fin (A.model n).size) :=
    fun n => Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let σ : (n : ℕ) → ↥SΓ → Equiv.Perm (Fin (A.model n).size) :=
    fun n i =>
      (A.model n).action
        (KunExactActualSourceAmbientGenerators.sourceAlphaInclusion
          (i : prefixElementaryGroup
            alphaPrefixCode))
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (KunExactActualSourceAmbientGenerators.sourceCompressionTable
          j)
  have hcrossΓ : ∀ i : ↥SΓ, Tendsto
      (fun n =>
        ((partitionWordCrossing (QΓ n)
          (σ n i)).card : ℝ) /
            Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    intro i
    exact
      SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
        QΓ σ
        (by simpa only [σ, Fintype.card_fin] using hboundaryΓ)
        i
  have haction (n : ℕ) (i : ↥SΓ ⊕ Fin 2) :
      (A.model n).action
        (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ i) =
        Sum.elim (σ n) (T n) i := by
    cases i <;> rfl
  have hcrossG : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          ((partitionWordCrossing
            (QG n) (Sum.elim (σ n) (T n) i)).card : ℝ)) /
              Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    simpa only [haction, Fintype.card_fin]
      using sourceAmbientFiniteFamily_crossing_density_tendsto_zero
        A SG hsymmetricG hgeneratesG QG hboundaryG
        (↥SΓ ⊕ Fin 2)
        (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ)
  obtain ⟨r, hr, _hdrop, hmidpoint⟩ :=
    exists_common_positive_component_log_rank_with_vanishing_midrank_energy
      (fun n => Fin (A.model n).size)
      (↥SΓ) (Fin 2) QΓ QG σ T eta H
      heta0 heta1 hH heta hratio hcrossΓ
      (by simpa only [T, Fintype.card_fin] using hoverlap)
      (by simpa only [T, Fintype.card_fin] using hloss)
      hcrossG
  let b : (n : ℕ) → Fin (A.model n).size → ℤ :=
    fun n =>
      SourceCommonOffsetMidrankEnergy.componentLogRank
        (QΓ n) (H n) (r n)
  let f : (n : ℕ) → Fin (A.model n).size → ℝ :=
    fun n =>
      MidrankPermutationEnergy.partitionVertexMidrank
        (QG n) (b n)
  have hf0 : ∀ n x, 0 ≤ f n x := by
    intro n x
    exact componentVertexMidrank_nonneg
      ((QG n).part x) (b n) x
  have hf1 : ∀ n x, f n x ≤ 1 := by
    intro n x
    exact componentVertexMidrank_le_one
      ((QG n).part x) (b n) x
  have hmidpoint' : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          ∑ x : Fin (A.model n).size,
            (f n (Sum.elim (σ n) (T n) i x) - f n x) ^ 2) /
              (A.model n).size)
      atTop (𝓝 0) := by
    simpa only [f, b, Fintype.card_fin] using hmidpoint
  have hpositiveEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          KunPositiveWordMidrankEnergy.squaredPermutationEnergy
            (f n)
            ((A.model n).action
              (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
                SΓ i))) /
              (A.model n).size)
      atTop (𝓝 0) := by
    have hpoint (n : ℕ) (i : ↥SΓ ⊕ Fin 2) :
        KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n)
          ((A.model n).action
            (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
              SΓ i)) =
          ∑ x : Fin (A.model n).size,
            (f n (Sum.elim (σ n) (T n) i x) - f n x) ^ 2 := by
      rw [haction n i]
      rfl
    simpa only [hpoint] using hmidpoint'
  have hgenerators :=
    KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
      A
      (KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
        SΓ)
      hpositive f hf0 hf1 hpositiveEnergy SG
  have hgeneratorSum (n : ℕ) :
      (∑ g ∈ SG,
        KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n) ((A.model n).action g)) =
      ∑ i : ↥SG,
        KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n)
          ((A.model n).action
            (i : prefixElementaryGroup
              ninePrefixCode)) := by
    rw [← Finset.sum_coe_sort SG]
  have hsubtypeEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SG,
          KunPositiveWordMidrankEnergy.squaredPermutationEnergy
            (f n)
            ((A.model n).action
              (i : prefixElementaryGroup
                ninePrefixCode))) /
                (A.model n).size)
      atTop (𝓝 0) := by
    simpa only [hgeneratorSum] using hgenerators
  have hgeneratorEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SG, ∑ x : Fin (A.model n).size,
          (f n ((A.model n).action
            (i : prefixElementaryGroup
              ninePrefixCode) x) - f n x) ^ 2) /
            Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    simpa only [Fintype.card_fin,
      KunPositiveWordMidrankEnergy.squaredPermutationEnergy]
      using hsubtypeEnergy
  have hvariance :=
    weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
      (fun n => Fin (A.model n).size) (↥SG) QG
      (fun n i =>
        (A.model n).action
          (i : prefixElementaryGroup
            ninePrefixCode))
      b γG hγG hexpandG
      (by simpa only [Fintype.card_fin] using hboundaryG)
      (by simpa only [f] using hgeneratorEnergy)
  refine ⟨r, hr, ?_, ?_⟩
  · simpa only [b, Fintype.card_fin] using hvariance
  · intro j
    exact sourceAmbientActualInverse_crossing_density_tendsto_zero
      A SG hsymmetricG hgeneratesG QG hboundaryG
      (KunExactActualSourceAmbientGenerators.sourceCompressionTable
        j)

end KunLiteralNineSourceCompletedCentralizerModels

open KunLiteralNineSourceCompletedCentralizerModels

namespace KunActualFirstStageReferenceExpansion

open Filter Topology
open scoped BigOperators

def componentGeneratorDisagreement
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V)
    (σref σact : ι → Equiv.Perm V) : ℕ :=
  ∑ i : ι, (C.filter fun x => σref i x ≠ σact i x).card

theorem componentGeneratorDisagreement_comm
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V)
    (σref σact : ι → Equiv.Perm V) :
    componentGeneratorDisagreement C σref σact =
      componentGeneratorDisagreement C σact σref := by
  classical
  unfold componentGeneratorDisagreement
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => ne_comm

theorem boundary_le_boundary_add_componentGeneratorDisagreement
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V)
    (C E : Finset V) (hEC : E ⊆ C) :
    boundary σref E ≤
      boundary σact E +
        componentGeneratorDisagreement C σref σact := by
  classical
  unfold boundary componentGeneratorDisagreement
  calc
    (∑ i : ι, (E.filter fun x => σref i x ∉ E).card) ≤
        ∑ i : ι,
          ((E.filter fun x => σact i x ∉ E).card +
            (C.filter fun x => σref i x ≠ σact i x).card) := by
          apply Finset.sum_le_sum
          intro i _
          have hsubset :
              (E.filter fun x => σref i x ∉ E) ⊆
                (E.filter fun x => σact i x ∉ E) ∪
                  (C.filter fun x => σref i x ≠ σact i x) := by
            intro x hx
            obtain ⟨hxE, href⟩ := Finset.mem_filter.mp hx
            by_cases hact : σact i x ∈ E
            · apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨hEC hxE, ?_⟩
              intro heq
              apply href
              rwa [heq]
            · apply Finset.mem_union_left
              exact Finset.mem_filter.mpr ⟨hxE, hact⟩
          exact (Finset.card_le_card hsubset).trans
            (Finset.card_union_le _ _)
    _ = (∑ i : ι, (E.filter fun x => σact i x ∉ E).card) +
          ∑ i : ι,
            (C.filter fun x => σref i x ≠ σact i x).card := by
          rw [Finset.sum_add_distrib]

theorem completed_actual_component_additive_expansion_of_reference
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σact i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σact i x)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary σref E : ℝ)) :
    ∀ E : Finset {x : V // x ∈ C},
      γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) -
        ((boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (boundary τ E : ℝ) := by
  classical
  have hhalf (E : Finset {x : V // x ∈ C})
      (hE : 2 * E.card ≤ C.card) :
      γ * (E.card : ℝ) -
        ((boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (boundary τ E : ℝ) := by
    let D : Finset V :=
      E.map (Function.Embedding.subtype (fun x : V => x ∈ C))
    have hDC : D ⊆ C := by
      intro x hx
      exact Finset.property_of_mem_map_subtype E hx
    have hcard : D.card = E.card := by
      dsimp [D]
      exact Finset.card_map _
    have hhalfD : 2 * D.card ≤ C.card := by
      simpa only [hcard] using hE
    have hreference := hexpand D hDC hhalfD
    rw [hcard] at hreference
    have hchanged :=
      boundary_le_boundary_add_componentGeneratorDisagreement
        σref σact C D hDC
    have hcompleted :=
      KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
        σact C τ hτ E
    have hcomponent :=
      boundary_le_boundary_add_componentGeneratorDisagreement
        σact σref C C (Finset.Subset.refl C)
    rw [componentGeneratorDisagreement_comm C σact σref] at hcomponent
    have hchangedR :
        (boundary σref D : ℝ) ≤
          (boundary σact D : ℝ) +
            (componentGeneratorDisagreement C σref σact : ℝ) := by
      exact_mod_cast hchanged
    have hcompletedR :
        (boundary σact D : ℝ) ≤
          (boundary τ E : ℝ) +
            (boundary σact C : ℝ) := by
      change
        ((boundary σact
          (E.map (Function.Embedding.subtype
            (fun x : V => x ∈ C))) : ℕ) : ℝ) ≤ _
      exact_mod_cast hcompleted
    have hcomponentR :
        (boundary σact C : ℝ) ≤
          (boundary σref C : ℝ) +
            (componentGeneratorDisagreement C σref σact : ℝ) := by
      exact_mod_cast hcomponent
    linarith
  intro E
  by_cases hE : 2 * E.card ≤ C.card
  · have hreal : (2 : ℝ) * (E.card : ℝ) ≤ (C.card : ℝ) := by
      exact_mod_cast hE
    rw [min_eq_left (by linarith)]
    exact hhalf E hE
  · let D : Finset {x : V // x ∈ C} := Finset.univ \ E
    have hcard : D.card + E.card = C.card := by
      dsimp [D]
      have h :=
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
      simpa only [Finset.univ_eq_attach, Finset.card_attach] using h
    have hhalfD : 2 * D.card ≤ C.card := by
      omega
    have hsmall := hhalf D hhalfD
    have hrealD : (D.card : ℝ) = (C.card : ℝ) - (E.card : ℝ) := by
      have hreal :
          (D.card : ℝ) + (E.card : ℝ) = (C.card : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hrealE : (C.card : ℝ) < 2 * (E.card : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hE
    rw [min_eq_right (by linarith)]
    rw [hrealD] at hsmall
    have hcomplement :
        boundary τ D = boundary τ E := by
      simpa only [D] using
        KunResidualExpanderDecomposition.boundary_complement τ E
    rw [hcomplement] at hsmall
    exact hsmall

theorem completedRestriction_additive_expansion_of_reference
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V) (C : Finset V)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary σref E : ℝ)) :
    ∀ E : Finset {x : V // x ∈ C},
      γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) -
        ((boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (boundary
          (fun i =>
            MatchedComponentCompletion.completedRestriction
              (σact i) C) E : ℝ) := by
  apply completed_actual_component_additive_expansion_of_reference
    σref σact C
    (fun i =>
      MatchedComponentCompletion.completedRestriction
        (σact i) C)
  · intro i x hx hy
    exact MatchedComponentCompletion.completedRestriction_apply_of_mem
      (σact i) C x hx hy
  · exact hexpand

def normalizedReferenceCompletionError
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V) (σref σact : ι → Equiv.Perm V) : ℝ :=
  ((boundary σref C : ℝ) +
    2 * (componentGeneratorDisagreement C σref σact : ℝ)) /
      (C.card : ℝ)

theorem normalizedReferenceCompletionError_tendsto_zero
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hdisagreement : Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        normalizedReferenceCompletionError (C n) (σref n) (σact n))
      atTop (nhds 0) := by
  have hsum :=
    hboundary.add (hdisagreement.const_mul (2 : ℝ))
  simpa only [normalizedReferenceCompletionError, add_div,
    mul_div_assoc, zero_add, mul_zero] using hsum

theorem exists_vanishing_completedRestriction_additive_expansion_of_reference
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C : (n : ℕ) → Finset (V n))
    (hC : ∀ n, (C n).Nonempty)
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (γ : ℝ)
    (hexpand : ∀ n, ∀ E : Finset (V n), E ⊆ C n →
      2 * E.card ≤ (C n).card →
        γ * (E.card : ℝ) ≤
          (boundary (σref n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hdisagreement : Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset {x : V n // x ∈ C n},
        γ * min (E.card : ℝ)
          ((Fintype.card {x : V n // x ∈ C n} : ℝ) - E.card) -
            a n * Fintype.card {x : V n // x ∈ C n} ≤
          (boundary
            (fun i =>
              MatchedComponentCompletion.completedRestriction
                (σact n i) (C n)) E : ℝ) := by
  let a : ℕ → ℝ :=
    fun n => normalizedReferenceCompletionError
      (C n) (σref n) (σact n)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro n
    unfold a normalizedReferenceCompletionError
    apply div_nonneg
    · positivity
    · exact Nat.cast_nonneg _
  · exact normalizedReferenceCompletionError_tendsto_zero
      V ι C σref σact hboundary hdisagreement
  · intro n E
    have hcard : ((C n).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (hC n)
    have h :=
      completedRestriction_additive_expansion_of_reference
        (σref n) (σact n) (C n) γ (hexpand n) E
    simpa only [a, normalizedReferenceCompletionError,
      Fintype.card_coe, div_mul_cancel₀ _ hcard] using h

theorem componentGeneratorDisagreement_le_card_mul_component_bad
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C B : Finset V)
    (σref σact : ι → Equiv.Perm V)
    (hbad : ∀ i (x : V), x ∈ C →
      σref i x ≠ σact i x → x ∈ B) :
    componentGeneratorDisagreement C σref σact ≤
      Fintype.card ι * (C ∩ B).card := by
  classical
  unfold componentGeneratorDisagreement
  calc
    (∑ i : ι, (C.filter fun x => σref i x ≠ σact i x).card) ≤
        ∑ _i : ι, (C ∩ B).card := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxC, hdisagree⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_inter.mpr
            ⟨hxC, hbad i x hxC hdisagree⟩
    _ = Fintype.card ι * (C ∩ B).card := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hdensity : Tendsto
      (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun n =>
        (Fintype.card ι : ℝ) *
          (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hdensity.const_mul (Fintype.card ι : ℝ)
  apply squeeze_zero'
    (Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))
    (Eventually.of_forall fun n => ?_)
    hlimit
  have hnat :=
    componentGeneratorDisagreement_le_card_mul_component_bad
      (C n) (B n) (σref n) (σact n) (hbad n)
  have hreal :
      (componentGeneratorDisagreement
        (C n) (σref n) (σact n) : ℝ) ≤
        (Fintype.card ι : ℝ) *
          ((C n ∩ B n).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (componentGeneratorDisagreement
      (C n) (σref n) (σact n) : ℝ) / (C n).card ≤
        ((Fintype.card ι : ℝ) *
          ((C n ∩ B n).card : ℝ)) / (C n).card :=
          div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = (Fintype.card ι : ℝ) *
          (((C n ∩ B n).card : ℝ) / (C n).card) := by ring

theorem exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (hC : ∀ n, (C n).Nonempty)
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (γ : ℝ)
    (hexpand : ∀ n, ∀ E : Finset (V n), E ⊆ C n →
      2 * E.card ≤ (C n).card →
        γ * (E.card : ℝ) ≤
          (boundary (σref n) E : ℝ))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hboundary : Tendsto
      (fun n =>
        (boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hbad_density : Tendsto
      (fun n =>
        (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset {x : V n // x ∈ C n},
        γ * min (E.card : ℝ)
          ((Fintype.card {x : V n // x ∈ C n} : ℝ) - E.card) -
            a n * Fintype.card {x : V n // x ∈ C n} ≤
          (boundary
            (fun i =>
              MatchedComponentCompletion.completedRestriction
                (σact n i) (C n)) E : ℝ) := by
  apply exists_vanishing_completedRestriction_additive_expansion_of_reference
    V ι C hC σref σact γ hexpand hboundary
  exact componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
    V ι C B σref σact hbad hbad_density

end KunActualFirstStageReferenceExpansion

open KunActualFirstStageReferenceExpansion

namespace SourceProductThroughAlpha

open Filter Topology
open scoped BigOperators

theorem source_u_conjugated_product_generator
    (g : prefixElementaryGroup
      alphaPrefixCode) :
    ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
        (sourceCompressionUAlphaEquiv g, 1) =
      SourceBothCompressionNormalization.sourceCompressionUElement *
        SourceGeneratedWordCrossing.sourceAlphaInclusion g *
          (SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹ := by
  apply Subtype.ext
  change
    (sourceCompressionUAlphaEquiv g : BinaryLeavittˣ) * 1 =
      compressionU *
        (g : BinaryLeavittˣ) *
          compressionU⁻¹
  rw [mul_one]
  change
    (MulAut.conj compressionU)
        (g : BinaryLeavittˣ) =
      compressionU *
        (g : BinaryLeavittˣ) *
          compressionU⁻¹
  rw [MulAut.conj_apply]

theorem source_u_transported_reference_half_expansion
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (QΓ : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ)
    (hexpand : ∀ n, ∀ C ∈ (QΓ n).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) E : ℝ)) :
    ∀ n, ∀ C ∈
      (transportedUnivFinpartition
        (QΓ n)
        ((A.model n).action
          SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                    SourceBothCompressionNormalization.sourceCompressionUElement *
                  (A.model n).action
                    (SourceGeneratedWordCrossing.sourceAlphaInclusion
                      i) *
                    ((A.model n).action
                      SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
              E : ℝ) := by
  intro n
  exact
    KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
      (QΓ n)
      (fun i : ↥SΓ =>
        (A.model n).action
          (SourceGeneratedWordCrossing.sourceAlphaInclusion i))
      ((A.model n).action
        SourceBothCompressionNormalization.sourceCompressionUElement)
      gamma (hexpand n)

theorem source_u_transported_reference_boundary_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (QΓ : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (QΓ n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈
          (transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                  SourceBothCompressionNormalization.sourceCompressionUElement *
                (A.model n).action
                  (SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i) *
                  ((A.model n).action
                    SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
            C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0) := by
  have h :=
    KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
      (V := fun n => Fin (A.model n).size)
      QΓ
      (fun n (i : ↥SΓ) =>
        (A.model n).action
          (SourceGeneratedWordCrossing.sourceAlphaInclusion i))
      (fun n =>
        (A.model n).action
          SourceBothCompressionNormalization.sourceCompressionUElement)
      (by simpa only [Fintype.card_fin] using hboundary)
  simpa only [Fintype.card_fin] using h

end SourceProductThroughAlpha

namespace KunLiteralSourceSelectedComponents

open Filter Topology
open CanonicalProductRadiusBadMatchedCapture
open SourceProductThroughAlpha
open scoped BigOperators Pointwise

def sourceCompressionPermutation
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (n : ℕ) : Equiv.Perm (Fin (A.model n).size) :=
  (A.model n).action
    SourceBothCompressionNormalization.sourceCompressionUElement

def sourceTransportedReferenceGenerators
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (n : ℕ) : ↥S → Equiv.Perm (Fin (A.model n).size) :=
  fun g => sourceCompressionPermutation A n *
    (A.model n).action
      (SourceGeneratedWordCrossing.sourceAlphaInclusion g) *
    (sourceCompressionPermutation A n)⁻¹

def sourceTransportedPartition
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (Q : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (n : ℕ) :
    Finpartition (Finset.univ : Finset (Fin (A.model n).size)) :=
  transportedUnivFinpartition
    (Q n) (sourceCompressionPermutation A n)

noncomputable def sourceGeneratorFamilyConjugacyBad
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (n : ℕ) : Finset (Fin (A.model n).size) :=
  S.biUnion fun g => sourceConjugacyDisagreementBad A
    SourceBothCompressionNormalization.sourceCompressionUElement
    (SourceGeneratedWordCrossing.sourceAlphaInclusion g) n

theorem sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    Tendsto
      (fun n =>
        ((sourceGeneratorFamilyConjugacyBad A S n).card : ℝ) /
          (A.model n).size)
      atTop (nhds 0) := by
  classical
  have h := finite_union_bad_density_tendsto_zero S
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n g => sourceConjugacyDisagreementBad A
      SourceBothCompressionNormalization.sourceCompressionUElement
      (SourceGeneratedWordCrossing.sourceAlphaInclusion g) n)
    (fun g _ => by
      simpa only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] using
        sourceConjugacyDisagreementBad_density_tendsto_zero A
          SourceBothCompressionNormalization.sourceCompressionUElement
          (SourceGeneratedWordCrossing.sourceAlphaInclusion g))
  simpa only [sourceGeneratorFamilyConjugacyBad, Finset.univ_inter, Finset.card_univ,
    Fintype.card_fin] using h

noncomputable def sourceSelectedRadiusBad
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup
          alphaPrefixCode)) = ⊤)
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]))
    (n k : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  let SK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset S
  let AP :=
    SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A
  exact
    CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
      AP SK
      (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
        S hsymmetric)
      (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
        S hgenerates)
      F n k ∪ sourceGeneratorFamilyConjugacyBad A S n

end KunLiteralSourceSelectedComponents

namespace SourceGuardedCanonicalSelection

open Filter Topology
open scoped BigOperators Pointwise symmDiff

abbrev SourceK :=
  prefixElementaryGroup alphaZeroPrefixCode

abbrev SourceJ :=
  ThompsonPrefixInsertion.localPrefixTranspositionGroup
    [0, 0, 0, 1]

noncomputable def guardedCanonicalProductRadiusBad
    [DecidableEq SourceK] [DecidableEq SourceJ]
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (F : Finset SourceJ)
    (E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size))
    (n k : ℕ) : Finset (Fin (A.model n).size) :=
  CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
    (SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A)
    (SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ)
    (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      SΓ hsymmetric)
    (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      SΓ hgenerates)
    F n k ∪ E n k

theorem exists_source_guarded_canonical_selected_components_of_retained_matching
    [DecidableEq SourceK] [DecidableEq SourceJ]
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hone : 1 ∈ SΓ)
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (prefixElementaryGroup alphaPrefixCode)) =
          ⊤)
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    {κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (Fin (A.model n).size))
    (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : (n : ℕ) → Finset (Fin (A.model n).size) →
      Finset (Fin (A.model n).size))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (nhds 0))
    (heta : Tendsto eta atTop (nhds 0))
    (hmajor : ∀ n,
      eta n ≤ (1 : ℝ) / 2 →
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        ∀ C, C ∈ R n →
          (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) \
          matchedRetainedSupport (R n)).card : ℝ) /
            (A.model n).size))
      atTop (nhds 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (A.model n).size)
      atTop (nhds 0))
    (F : Finset SourceJ)
    (E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size))
    (hE : ∀ k, Tendsto
      (fun n => ((E n k).card : ℝ) / (A.model n).size)
      atTop (nhds 0))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (nhds 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (A.model n).size)
      atTop (nhds 0))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
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
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ matchedRadiusBad
            (P (n + N))
            (CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ)
              F (r n))
            (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (guardedCanonicalProductRadiusBad
              A SΓ hsymmetric hgenerates F E (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (nhds 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by
  classical
  let : Infinite SourceK :=
    KunActualCompressedSourceGroupFoundations.alphaZeroPrefixElementaryGroup_infinite
  have hnonempty (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let : ∀ n, Nonempty (Fin (A.model n).size) := hnonempty
  let SK : Finset SourceK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ
  let Ap : SoficApproximation (SourceK × SourceJ) :=
    SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A
  let I : ℕ → Finset (SourceK × SourceJ) := fun k =>
    CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
      SK F k
  let w : (n : ℕ) → SourceK × SourceJ →
      Equiv.Perm (Fin (A.model n).size) :=
    fun n z => (Ap.model n).action z
  let B : (n : ℕ) → ℕ → Finset (Fin (A.model n).size) :=
    fun n k => guardedCanonicalProductRadiusBad
      A SΓ hsymmetric hgenerates F E n k
  have hSKone : 1 ∈ SK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_one_mem
      SΓ hone
  have hSKsym : ∀ g ∈ SK, g⁻¹ ∈ SK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      SΓ hsymmetric
  have hSKgen : Subgroup.closure (SK : Set SourceK) = ⊤ :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      SΓ hgenerates
  have hU (n : ℕ) :
      (Finset.univ : Finset (Fin (A.model n).size)).Nonempty :=
    Finset.univ_nonempty
  have hword (k : ℕ) : Tendsto
      (fun n =>
        ((∑ z ∈ I k,
          (partitionWordCrossing
            (Q n) (w n z)).card : ℕ) : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [I, w, Ap, SK, Finset.card_univ,
      Fintype.card_fin,
      SourceProductThroughAlpha.sourceCompressedLocalProductApproximation_model_size]
        using
      SourceProductThroughAlpha.source_canonical_product_radius_crossing_density_tendsto_zero
        A SΓ hsymmetric hgenerates Q hsource F k
  have hbad (k : ℕ) : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) ∩
          B n k).card : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card))
      atTop (nhds 0) := by
    have hcanonical :=
      CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
        Ap SK hSKsym hSKgen F k
    have hcanon' : Tendsto
        (fun n =>
          ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size)
        atTop (nhds 0) := by
      exact hcanonical
    have hlimit : Tendsto
        (fun n =>
          ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size +
            ((E n k).card : ℝ) / (A.model n).size)
        atTop (nhds 0) := by
      simpa only [add_zero] using hcanon'.add (hE k)
    refine squeeze_zero (fun n => by positivity) ?_ hlimit
    intro n
    have hnat := Finset.card_union_le
      (CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k) (E n k)
    have hreal :
        (((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℕ) : ℝ) ≤
        ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          Ap SK hSKsym hSKgen F n k).card : ℝ) +
          ((E n k).card : ℝ) := by
      exact_mod_cast hnat
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin]
    change
      ((B n k).card : ℝ) / (A.model n).size ≤ _
    change
      ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℝ) /
        (A.model n).size ≤ _
    calc
      ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
        Ap SK hSKsym hSKgen F n k ∪ E n k).card : ℝ) /
        (A.model n).size ≤
          (((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) +
            ((E n k).card : ℝ)) /
            (A.model n).size :=
              div_le_div_of_nonneg_right hreal (by positivity)
      _ = ((CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k).card : ℝ) /
              (A.model n).size +
            ((E n k).card : ℝ) / (A.model n).size := by ring
  have hrealize :
      ∀ n k (C : Finset (Fin (A.model n).size)), C ∈ R n →
        ∀ x ∈ C,
          x ∉ matchedRadiusBad
            (P n) (I k) (w n) (B n k) →
            ∃ f : SourceK → Fin (A.model n).size,
              Set.MapsTo f (↑(SK ^ (k / 2)) : Set SourceK)
                (↑C : Set (Fin (A.model n).size)) ∧
              Set.InjOn f (↑(SK ^ (k / 2)) : Set SourceK) := by
    intro n k C hCR x hx hgood
    have hgoodcanonical :
        x ∉ matchedRadiusBad
          (P n) (I k) (w n)
          (CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k) := by
      intro hxcan
      apply hgood
      unfold matchedRadiusBad at hxcan ⊢
      rcases Finset.mem_union.mp hxcan with hxB | hxW
      · apply Finset.mem_union_left
        change x ∈
          CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
            Ap SK hSKsym hSKgen F n k ∪ E n k
        exact Finset.mem_union_left _ hxB
      · exact Finset.mem_union_right _ hxW
    exact
      canonical_source_matched_component_cayley_ball_realization
        Ap SK hSKone hSKsym hSKgen F n k (P n) C
        (hR n hCR) x hx hgoodcanonical
  have hdiscard' : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) \
          matchedRetainedSupport (R n)).card : ℝ) /
            (Finset.univ : Finset (Fin (A.model n).size)).card))
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hdiscard
  have hsymm' : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hsymm
  have hboundary' : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (boundary (σ n) C : ℝ)) /
          (Finset.univ : Finset (Fin (A.model n).size)).card)
      atTop (nhds 0) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hboundary
  have hselected :=
    KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_source_scale_tail
      SK hSKone hSKgen σ
      (fun n => (Finset.univ : Finset (Fin (A.model n).size))) hU
      P Q R hR D hD H eta hH heta hmajor hdiscard' hsymm'
      I w hword B hbad hboundary' hrealize N₀
  simpa only [I, w, Ap, SK, B] using hselected

end SourceGuardedCanonicalSelection

open SourceGuardedCanonicalSelection

namespace KunActualSourceURetainedNoPremise

open Filter Topology
open scoped BigOperators symmDiff

theorem exists_actual_source_u_retained_matching
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode)) :
    ∃ (SΓ : Finset
          (prefixElementaryGroup
            alphaPrefixCode))
      (QΓ : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ : ℝ)
      (H eta r : ℕ → ℝ)
      (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size))),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤ ∧
      0 < γΓ ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 0 < H n) ∧
      Tendsto H atTop (𝓝 0) ∧
      (∀ n, 0 < eta n) ∧
      (∀ n, eta n < 1) ∧
      Tendsto eta atTop (𝓝 0) ∧
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      (∀ n,
        R n =
          SourceRetainedActualMatching.retainedTransportedComponents
            (QΓ n)
            ((A.model n).action
              SourceBothCompressionNormalization.sourceCompressionUElement)
            (H n) (r n) (eta n)) ∧
      (∀ n,
        R n ⊆
          (transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              SourceBothCompressionNormalization.sourceCompressionUElement)).parts) ∧
      (∀ n C, C ∈ R n →
        maximumOverlapPart (QΓ n) C ∈ (QΓ n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ R n →
            (maximumOverlapPart (QΓ n) C).card <
              2 * (C ∩ maximumOverlapPart
                (QΓ n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (Fin (A.model n).size)) \
            matchedRetainedSupport (R n)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ R n,
            (C ∆ maximumOverlapPart
              (QΓ n) C).card : ℕ) : ℝ) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (maximumOverlapPart (QΓ n))
          ((R n : Finset (Finset (Fin (A.model n).size))) :
            Set (Finset (Fin (A.model n).size)))) := by
  classical
  obtain ⟨SΓ, SG, QΓ, QG, γΓ, γG, _hSG,
      honeΓ, hsymmetricΓ, hgeneratesΓ,
      _honeG, hsymmetricG, hgeneratesG,
      _hfaithful, hpositive,
      hγΓ, hγG, hexpandΓ, hexpandG,
      hboundaryΓ, hboundaryG⟩ :=
    exists_unconditional_actual_source_dual_finpartition_sequences A
  have hexpandΓ' :
      ∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) E : ℝ) :=
    hexpandΓ
  have hboundaryΓ' :
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SourceBothCompressionNormalization.sourceAlphaElement
                    (i : prefixElementaryGroup
                      alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) :=
    hboundaryΓ
  obtain ⟨eta, H, hetapos, hetaone, _hetaanti, hetazero,
      hHpos, _hHanti, hHzero, hratio, hoverlap, hloss⟩ :=
    KunActualBothTransportedOverlapScales.exists_source_both_capped_overlap_scales
        A SΓ hsymmetricΓ hgeneratesΓ QΓ γΓ hγΓ
        hexpandΓ' hboundaryΓ'
  have hoverlap' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ insufficientOverlapComponents
            (transportedUnivFinpartition
              (QΓ n)
              ((A.model n).action
                (KunExactActualSourceAmbientGenerators.sourceCompressionTable
                  j)))
            (QΓ n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) :=
    hoverlap
  have hloss' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (transportedUnivFinpartition
              (QΓ n)
              ((A.model n).action
                (KunExactActualSourceAmbientGenerators.sourceCompressionTable
                  j))).parts,
            ((C.card : ℝ) -
              ((C ∩ maximumOverlapPart
                (QΓ n) C).card : ℝ))) /
                (A.model n).size)
        atTop (𝓝 0) :=
    hloss
  obtain ⟨r, hr, hvariance, hinverse⟩ :=
    exists_source_common_log_rank_with_ambient_midrank_variance
        A SΓ SG QΓ QG γG
        hsymmetricG hgeneratesG hpositive hγG hexpandG
        hboundaryΓ hboundaryG eta H
        (fun n => (hetapos n).le) hetaone hHpos
        hetazero hratio hoverlap' hloss'
  let : ∀ n, Nonempty (Fin (A.model n).size) :=
    fun n => Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (SourceBothCompressionNormalization.sourceCompressionTable j)
  have hvariance' :
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (C.card : ℝ) *
              midrankVariance
                (componentRankMassList C
                  (SourceRetainedActualMatching.logarithmicComponentRank
                    (QΓ n) (H n) (r n)))) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    simpa only [
      SourceRetainedActualMatching.logarithmicComponentRank,
      SourceCommonOffsetMidrankEnergy.componentLogRank,
      SourceCommonOffsetMidrankEnergy.realComponentSize,
      Fintype.card_fin] using hvariance
  have hinverse' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          ((partitionWordCrossing
            (QG n) (T n j).symm).card : ℝ) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    intro j
    simpa only [T, Fintype.card_fin, Equiv.Perm.inv_def,
      SourceBothCompressionNormalization.sourceCompressionTable,
      SourceBothCompressionNormalization.sourceCompressionUElement,
      SourceBothCompressionNormalization.sourceCompressionVElement,
      KunExactActualSourceAmbientGenerators.sourceCompressionTable,
      KunExactActualSourceAmbientGenerators.sourceCompressionU,
      KunExactActualSourceAmbientGenerators.sourceCompressionV]
      using hinverse j
  have hoverlapNat :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          ((∑ C ∈ insufficientOverlapComponents
            (transportedUnivFinpartition
              (QΓ n) (T n j))
            (QΓ n) (eta n), C.card : ℕ) : ℝ) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    intro j
    simpa only [T, Nat.cast_sum, Fintype.card_fin] using hoverlap j
  have hmatch :=
    SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
        (fun n => Fin (A.model n).size)
        (Fin 2) QΓ QG T H r eta hHpos hHzero
        (fun n => (hetapos n).le) hetazero
        hvariance' hinverse' hoverlapNat (0 : Fin 2)
  have hTzero (n : ℕ) :
      T n (0 : Fin 2) =
        (A.model n).action
          SourceBothCompressionNormalization.sourceCompressionUElement :=
    rfl
  let R : (n : ℕ) → Finset (Finset (Fin (A.model n).size)) :=
    fun n =>
      SourceRetainedActualMatching.retainedTransportedComponents
        (QΓ n)
        ((A.model n).action
          SourceBothCompressionNormalization.sourceCompressionUElement)
        (H n) (r n) (eta n)
  obtain ⟨hparts, htarget, hmajor, hdiscard, hsymmetric, hinjective⟩ :=
    hmatch
  refine ⟨SΓ, QΓ, γΓ, H, eta, r, R,
    honeΓ, hsymmetricΓ, hgeneratesΓ, hγΓ,
    hexpandΓ', hboundaryΓ', hHpos, hHzero,
    hetapos, hetaone, hetazero, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · simpa only [R, hTzero] using hparts
  · simpa only [R, hTzero] using htarget
  · simpa only [R, hTzero] using hmajor
  · simpa only [R, hTzero, Fintype.card_fin] using hdiscard
  · simpa only [R, hTzero, Fintype.card_fin] using hsymmetric
  · simpa only [R, hTzero] using hinjective

end KunActualSourceURetainedNoPremise

namespace KunLiteralSourceSelectedComponents

open Filter Topology
open scoped BigOperators Pointwise

noncomputable def sourceSelectedProductRadiusLabels
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]))
    (k : ℕ) :
    Finset
      (prefixElementaryGroup alphaZeroPrefixCode ×
        ThompsonPrefixInsertion.localPrefixTranspositionGroup
          [0, 0, 0, 1]) := by
  classical
  exact
    CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
      (SourceProductThroughAlpha.sourceCompressedGeneratingFinset S)
      F k

theorem exists_source_selected_components
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1])) :
    ∃ (S : Finset
          (prefixElementaryGroup alphaPrefixCode))
      (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
      (hgenerates : Subgroup.closure
        (S : Set
          (prefixElementaryGroup
            alphaPrefixCode)) = ⊤)
      (Q : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (gamma : ℝ) (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
      1 ∈ S ∧
      0 < gamma ∧
      Tendsto
        (fun n =>
          (∑ D ∈ (Q n).parts,
            (boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) D : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto r atTop atTop ∧
      (∀ n, C n ∈ (sourceTransportedPartition A Q (n + N)).parts) ∧
      (∀ n, (C n).Nonempty) ∧
      (∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
        D ⊆ C n → 2 * D.card ≤ (C n).card →
          gamma * (D.card : ℝ) ≤
            (boundary
              (sourceTransportedReferenceGenerators A S (n + N)) D : ℝ)) ∧
      Tendsto
        (fun n =>
          (boundary
            (sourceTransportedReferenceGenerators A S (n + N))
            (C n) : ℝ) / (C n).card)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ matchedRadiusBad
            (sourceTransportedPartition A Q (n + N))
            (sourceSelectedProductRadiusLabels S F (r n))
            (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (sourceSelectedRadiusBad A S
              hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (𝓝 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by
  classical
  obtain ⟨S, Q, gamma, H, eta, _offset, R,
      hone, hsymmetric, hgenerates, hgamma,
      hexpand, hsource, _hHpositive, hH,
      _hetapositive, _hetaone, heta, _hoffset, _hRdef,
      hR, htarget, hmajor, hdiscard, hsymm, _hinjective⟩ :=
    KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching A
  have hsource' :
      Tendsto
        (fun n =>
          (∑ D ∈ (Q n).parts,
            (boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) D : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) := by
    exact hsource
  let P : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)) :=
    fun n => sourceTransportedPartition A Q n
  let sigma : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n => sourceTransportedReferenceGenerators A S n
  let E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size) :=
    fun n _ => sourceGeneratorFamilyConjugacyBad A S n
  have hRP : ∀ n, R n ⊆ (P n).parts := by
    simpa only [P, sourceTransportedPartition,
      sourceCompressionPermutation] using hR
  have hE : ∀ k, Tendsto
      (fun n => ((E n k).card : ℝ) / (A.model n).size)
      atTop (𝓝 0) := by
    intro k
    simpa only [E] using
      sourceGeneratorFamilyConjugacyBad_density_tendsto_zero A S
  have hboundary : Tendsto
      (fun n =>
        (∑ D ∈ (P n).parts,
          (boundary (sigma n) D : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0) := by
    change Tendsto
      (fun n =>
        (∑ D ∈
          (transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
          (boundary
            (fun i : ↥S =>
              (A.model n).action
                  SourceBothCompressionNormalization.sourceCompressionUElement *
                (A.model n).action
                  (SourceGeneratedWordCrossing.sourceAlphaInclusion i) *
                ((A.model n).action
                  SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
            D : ℝ)) / (A.model n).size)
      atTop (𝓝 0)
    exact
      SourceProductThroughAlpha.source_u_transported_reference_boundary_density_tendsto_zero
        A S Q hsource'
  obtain ⟨N, r, C, _hN, _hetaguard, _hexpguard,
      hr, hCR, hCboundary, hCbad, hCgrowth⟩ :=
    exists_source_guarded_canonical_selected_components_of_retained_matching
        A S hone hsymmetric hgenerates
        P Q sigma R hRP
        (fun n D => maximumOverlapPart (Q n) D)
        htarget H eta hH heta hmajor hdiscard hsymm
        F E hE hsource' hboundary 0
  have hCpart (n : ℕ) :
      C n ∈ (sourceTransportedPartition A Q (n + N)).parts := by
    exact hRP (n + N) (hCR n)
  have hCnonempty (n : ℕ) : (C n).Nonempty :=
    (sourceTransportedPartition A Q (n + N)).nonempty_of_mem_parts
      (hCpart n)
  have hexpand' :
      ∀ n, ∀ D ∈ (Q n).parts,
        ∀ E₀ : Finset (Fin (A.model n).size), E₀ ⊆ D →
          2 * E₀.card ≤ D.card →
            gamma * (E₀.card : ℝ) ≤
              (boundary
                (fun i : ↥S =>
                  (A.model n).action
                    (SourceGeneratedWordCrossing.sourceAlphaInclusion
                      i)) E₀ : ℝ) := by
    exact hexpand
  have htransported :=
    SourceProductThroughAlpha.source_u_transported_reference_half_expansion
      A S Q gamma hexpand'
  refine ⟨S, hsymmetric, hgenerates, Q, gamma, N, r, C,
    hone, hgamma,
    hsource', hr, hCpart, hCnonempty, ?_, ?_, ?_, hCgrowth⟩
  · intro n D hDC hhalf
    change gamma * (D.card : ℝ) ≤
      (boundary
        (fun i : ↥S =>
          (A.model (n + N)).action
              SourceBothCompressionNormalization.sourceCompressionUElement *
            (A.model (n + N)).action
              (SourceGeneratedWordCrossing.sourceAlphaInclusion i) *
            ((A.model (n + N)).action
              SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
        D : ℝ)
    exact htransported (n + N) (C n) (hCpart n) D hDC hhalf
  · simpa only [sigma] using hCboundary
  · simpa only [P, E, sourceTransportedPartition,
      sourceCompressionPermutation, sourceSelectedProductRadiusLabels,
      SourceGuardedCanonicalSelection.guardedCanonicalProductRadiusBad,
      sourceSelectedRadiusBad] using hCbad

end KunLiteralSourceSelectedComponents

namespace SourceProductThroughAlpha

open scoped BigOperators

noncomputable def sourceCompressedGeneratorSubtypeEquiv
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode)) :
    (↥SΓ) ≃
      (↥(sourceCompressedGeneratingFinset SΓ)) := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    refine ⟨sourceCompressionUAlphaEquiv (g :
      prefixElementaryGroup alphaPrefixCode), ?_⟩
    change sourceCompressionUAlphaEquiv (g :
      prefixElementaryGroup alphaPrefixCode) ∈
        SΓ.image sourceCompressionUAlphaEquiv
    exact Finset.mem_image.mpr ⟨g, g.property, rfl⟩
  · intro k
    refine ⟨sourceCompressionUAlphaEquiv.symm (k :
      prefixElementaryGroup alphaZeroPrefixCode), ?_⟩
    have hk :
        (k : prefixElementaryGroup
          alphaZeroPrefixCode) ∈
          SΓ.image sourceCompressionUAlphaEquiv := by
      exact k.property
    obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp hk
    rw [← heq, sourceCompressionUAlphaEquiv.symm_apply_apply]
    exact hg
  · intro g
    apply Subtype.ext
    exact sourceCompressionUAlphaEquiv.symm_apply_apply _
  · intro k
    apply Subtype.ext
    exact sourceCompressionUAlphaEquiv.apply_symm_apply _

theorem boundary_sourceCompressedGeneratorSubtypeEquiv
    {V : Type*} [DecidableEq V]
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (σ : ↥(sourceCompressedGeneratingFinset SΓ) → Equiv.Perm V)
    (E : Finset V) :
    boundary
      (fun i : ↥SΓ =>
        σ (sourceCompressedGeneratorSubtypeEquiv SΓ i)) E =
      boundary σ E := by
  classical
  unfold boundary
  exact Equiv.sum_comp (sourceCompressedGeneratorSubtypeEquiv SΓ)
    (fun i : ↥(sourceCompressedGeneratingFinset SΓ) =>
      (E.filter fun x => σ i x ∉ E).card)

end SourceProductThroughAlpha

namespace KunGuardedCanonicalMatchedDensity

open Filter Topology

theorem matchedRadiusBad_mono_bad
    {V ι : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U)
    (I : Finset ι) (w : ι → Equiv.Perm V)
    {B B' : Finset V} (hB : B ⊆ B') :
    matchedRadiusBad P I w B ⊆
      matchedRadiusBad P I w B' := by
  intro x hx
  unfold matchedRadiusBad at hx ⊢
  rcases Finset.mem_union.mp hx with hxB | hxcross
  · exact Finset.mem_union_left _ (hB hxB)
  · exact Finset.mem_union_right _ hxcross

theorem canonical_matched_density_of_guarded
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : (n : ℕ) → Finset (V n))
    (P : (n : ℕ) → Finpartition (U n))
    {ι : Type*} (I : ℕ → Finset ι)
    (w : (n : ℕ) → ι → Equiv.Perm (V n))
    (B E C : (n : ℕ) → Finset (V n))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (P n) (I n) (w n) (B n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hguarded
  intro n
  have hsubset :
      C n ∩ matchedRadiusBad
          (P n) (I n) (w n) (B n) ⊆
        C n ∩ matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n) := by
    intro x hx
    obtain ⟨hxC, hxB⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨hxC, matchedRadiusBad_mono_bad
        (P n) (I n) (w n)
        (Finset.subset_union_left : B n ⊆ B n ∪ E n) hxB⟩
  have hcard :
      ((C n ∩ matchedRadiusBad
        (P n) (I n) (w n) (B n)).card : ℝ) ≤
        (C n ∩ matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n)).card := by
    exact_mod_cast Finset.card_le_card hsubset
  exact div_le_div_of_nonneg_right hcard (by positivity)

end KunGuardedCanonicalMatchedDensity

namespace KunActualCanonicalSelectedPruning

open Filter Topology
open MatchedComponentCompletion

theorem exists_actual_uniformly_expanding_pruned_selected_components
    {K J : Type*} [Group K] [Group J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ)
    (ha : Tendsto a atTop (nhds 0))
    (hadd : ∀ n,
      ∀ E : Finset {x : Fin (A.model (ν n)).size // x ∈ C n},
        γ * min (E.card : ℝ)
            ((Fintype.card
              {x : Fin (A.model (ν n)).size // x ∈ C n} : ℝ) -
                E.card) -
          a n * Fintype.card
            {x : Fin (A.model (ν n)).size // x ∈ C n} ≤
          (boundary
            (fun i : ↥S =>
              completedRestriction
                ((A.model (ν n)).action ((i : K), (1 : J)))
                (C n)) E : ℝ)) :
    ∃ (N : ℕ)
      (D : (n : ℕ) → Finset
        {x : Fin (A.model (ν (n + N))).size // x ∈ C (n + N)})
      (τ : (n : ℕ) → ↥S → Equiv.Perm
        {x : {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)} //
          x ∈ (Finset.univ \ D n :
            Finset {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)})}),
      (∀ n,
        (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).Nonempty) ∧
      Tendsto
        (fun n => ((D n).card : ℝ) / (C (n + N)).card)
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (Finset.univ \ D n :
            Finset {x : Fin (A.model (ν (n + N))).size //
              x ∈ C (n + N)}).card)
        atTop atTop ∧
      (∀ n (i : ↥S)
        (x : {y : Fin (A.model (ν (n + N))).size //
          y ∈ C (n + N)})
        (hx : x ∈ (Finset.univ \ D n :
          Finset {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}))
        (_hi : completedRestriction
          ((A.model (ν (n + N))).action ((i : K), (1 : J)))
          (C (n + N)) x ∈
            (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})),
        ((τ n i ⟨x, hx⟩ :
          {z : {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)} //
            z ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})}) :
          {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}) =
            completedRestriction
              ((A.model (ν (n + N))).action ((i : K), (1 : J)))
              (C (n + N)) x) ∧
      (∀ n,
        ∀ E : Finset
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})},
          (γ / 2) * min (E.card : ℝ)
            ((Fintype.card
              {x : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
                x ∈ (Finset.univ \ D n :
                  Finset {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)})} : ℝ) - E.card) ≤
            (boundary (τ n) E : ℝ)) := by
  classical
  let ell : ℝ := γ / 2
  have hgap : ell < γ := by
    dsimp [ell]
    linarith
  have hgapPositive : 0 < γ - ell := sub_pos.mpr hgap
  let c : ℝ :=
    2 * (2 * (γ - ell) + (Fintype.card ↥S : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    have hcard : (0 : ℝ) ≤ Fintype.card ↥S := by
      exact Nat.cast_nonneg _
    nlinarith
  have htarget : 0 < (γ - ell) ^ 2 / c :=
    div_pos (sq_pos_of_pos hgapPositive) hc
  have hsmallEvent : ∀ᶠ n in atTop,
      a n < (γ - ell) ^ 2 / c :=
    ha.eventually (gt_mem_nhds htarget)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEvent
  have hsmall (n : ℕ) :
      2 * a (n + N) *
          (2 * (γ - ell) + (Fintype.card ↥S : ℝ)) ≤
        (γ - ell) ^ 2 := by
    have hratio : a (n + N) < (γ - ell) ^ 2 / c :=
      hN (n + N) (by omega)
    have hbound : a (n + N) * c < (γ - ell) ^ 2 :=
      (lt_div_iff₀ hc).mp hratio
    calc
      2 * a (n + N) *
          (2 * (γ - ell) + (Fintype.card ↥S : ℝ)) =
        a (n + N) * c := by
          dsimp [c]
          ring
      _ ≤ (γ - ell) ^ 2 := hbound.le
  have hstage (n : ℕ) :
      ∃ (D : Finset
          {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)})
        (τ : ↥S → Equiv.Perm
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})}),
        2 * D.card ≤ (C (n + N)).card ∧
        (D.card : ℝ) ≤
          a (n + N) * (C (n + N)).card / (γ - ell) ∧
        (∀ (i : ↥S)
          (x : {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)})
          (hx : x ∈ (Finset.univ \ D :
            Finset {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)}))
          (_hi : completedRestriction
            ((A.model (ν (n + N))).action ((i : K), (1 : J)))
            (C (n + N)) x ∈
              (Finset.univ \ D :
                Finset {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)})),
          ((τ i ⟨x, hx⟩ :
            {z : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
              z ∈ (Finset.univ \ D :
                Finset {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)})}) :
            {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)}) =
              completedRestriction
                ((A.model (ν (n + N))).action ((i : K), (1 : J)))
                (C (n + N)) x) ∧
        (∀ E : Finset
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})},
          ell * min (E.card : ℝ)
            ((Fintype.card
              {x : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
                x ∈ (Finset.univ \ D :
                  Finset {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)})} : ℝ) - E.card) ≤
            (boundary τ E : ℝ)) := by
    simpa only [Fintype.card_coe] using
      KunCompletedPrunedComponent.exists_completed_pruned_expander
        (fun i : ↥S =>
          completedRestriction
            ((A.model (ν (n + N))).action ((i : K), (1 : J)))
            (C (n + N)))
        γ ell (a (n + N)) hgap (hadd (n + N)) (hsmall n)
  choose D τ hhalf hbound hagree hexpand using hstage
  have hnonempty (n : ℕ) :
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν (n + N))).size //
          x ∈ C (n + N)}).Nonempty := by
    have hCpositive : 0 < (C (n + N)).card :=
      ((Q (n + N)).nonempty_of_mem_parts (hC (n + N))).card_pos
    have hpositive :
        0 < (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ (D n)),
        Finset.card_univ, Fintype.card_coe]
      have hh := hhalf n
      omega
    exact Finset.card_pos.mp hpositive
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have haupper : Tendsto
      (fun n => a (n + N) / (γ - ell))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_div] using
      (ha.comp hshift).div_const (γ - ell)
  have hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C (n + N)).card)
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => by positivity)
      (fun n => ?_)
      haupper
    have hCpositive : (0 : ℝ) < (C (n + N)).card := by
      exact_mod_cast
        ((Q (n + N)).nonempty_of_mem_parts (hC (n + N))).card_pos
    calc
      ((D n).card : ℝ) / (C (n + N)).card ≤
        (a (n + N) * (C (n + N)).card /
          (γ - ell)) / (C (n + N)).card :=
          div_le_div_of_nonneg_right (hbound n) hCpositive.le
      _ = a (n + N) / (γ - ell) := by
          field_simp [hCpositive.ne', hgapPositive.ne']
  have hshiftlarge :
      Tendsto (fun n => (C (n + N)).card) atTop atTop := by
    simpa only [Function.comp_def] using hlarge.comp hshift
  have hzlarge : Tendsto
      (fun n =>
        (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).card)
      atTop atTop := by
    apply MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
      (fun n => {x : Fin (A.model (ν (n + N))).size //
        x ∈ C (n + N)}) D
    · simpa only [Fintype.card_coe] using hshiftlarge
    · simpa only [Fintype.card_coe] using hdeleted
  refine ⟨N, D, τ, hnonempty, hdeleted, hzlarge,
    hagree, ?_⟩
  simpa only [ell] using hexpand

end KunActualCanonicalSelectedPruning

namespace KunActualCanonicalPrunedSourceBadDensity

open Filter Topology
open MatchedComponentCompletion
open CanonicalProductRadiusBadMatchedCapture

theorem pruned_sourceCompletionBad_density_tendsto_zero_of_canonical_matched
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
          (C n).card))
      atTop (𝓝 0))
    (D : (n : ℕ) → Finset
      {x : Fin (A.model (ν n)).size // x ∈ C n})
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C n).card)
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        ((sourceCompletionBad
          (fun i : ↥S =>
            completedRestriction
              ((A.model (ν n)).action ((i : K), (1 : J))) (C n))
          (fun j : J =>
            completedRestriction
              ((A.model (ν n)).action ((1 : K), j)) (C n))
          F (Finset.univ \ D n)).card : ℝ) /
            (Finset.univ \ D n :
              Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).card)
      atTop (𝓝 0) := by
  apply
    pruned_sourceCompletionBad_density_tendsto_zero_of_matchedRadius
    (fun n => Fin (A.model (ν n)).size)
    (fun n (i : ↥S) => (A.model (ν n)).action ((i : K), (1 : J)))
    (fun n (j : J) => (A.model (ν n)).action ((1 : K), j))
    F
    (fun n => (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    C Q
    (fun k => sourceProductRadiusLabels S F k)
    (fun n => (A.model (ν n)).action)
    r
    (fun n k => canonicalProductRadiusBad
      A S hsymmetric hgenerates F (ν n) k)
    D
  · intro n
    exact sourceCompletionBad_subset_canonical_matchedRadiusBad
      A S hsymmetric hgenerates F (ν n) (r n)
      (Q n) (C n) (hC n)
  · exact hmatched
  · exact hZ
  · exact hdeleted

end KunActualCanonicalPrunedSourceBadDensity

open KunActualCanonicalPrunedSourceBadDensity

namespace KunActualTwicePrunedFirstFactorRootBad

open Filter Topology
open MatchedComponentCompletion
open MatchedComponentExitBudget
open KunActualSoficRootRadius
open CanonicalProductRadiusBadMatchedCapture
open CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise

noncomputable def restrictionMultiplicationBad
    {V : Type*} [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V) : Finset V :=
  Z.filter (fun x => q x ∉ Z ∨ r x ∉ Z ∨ r x ≠ p (q x))

theorem completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V)
    (x : {v : V // v ∈ Z})
    (hx : (x : V) ∉ restrictionMultiplicationBad p q r Z) :
    completedRestriction r Z x =
      (completedRestriction p Z * completedRestriction q Z) x := by
  classical
  have hgood : ¬ (q (x : V) ∉ Z ∨ r (x : V) ∉ Z ∨
      r (x : V) ≠ p (q (x : V))) := by
    intro h
    exact hx (Finset.mem_filter.mpr ⟨x.property, h⟩)
  have hq : q (x : V) ∈ Z := by
    by_contra hn
    exact hgood (Or.inl hn)
  have hr : r (x : V) ∈ Z := by
    by_contra hn
    exact hgood (Or.inr (Or.inl hn))
  have hmul : r (x : V) = p (q (x : V)) := by
    by_contra hn
    exact hgood (Or.inr (Or.inr hn))
  have hpq : p (q (x : V)) ∈ Z := hmul ▸ hr
  have hqvalue :
      ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) =
        q (x : V) :=
    completedRestriction_apply_of_mem q Z x x.property hq
  apply Subtype.ext
  change
    ((completedRestriction r Z x : {v : V // v ∈ Z}) : V) =
      ((completedRestriction p Z
        (completedRestriction q Z x) : {v : V // v ∈ Z}) : V)
  calc
    ((completedRestriction r Z x : {v : V // v ∈ Z}) : V) =
        r (x : V) :=
      completedRestriction_apply_of_mem r Z x x.property hr
    _ = p (q (x : V)) := hmul
    _ = p ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) := by
      rw [hqvalue]
    _ = ((completedRestriction p Z
          (completedRestriction q Z x) : {v : V // v ∈ Z}) : V) := by
      symm
      apply completedRestriction_apply_of_mem
      change p ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) ∈ Z
      rw [hqvalue]
      exact hpq

theorem completedRestriction_mul_distance_le_failure_add_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V) :
    permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤
      (Finset.univ.filter fun x : V => r x ≠ p (q x)).card +
        2 * (Finset.univ \ Z).card := by
  classical
  let B : Finset V := restrictionMultiplicationBad p q r Z
  let E₁ : Finset V := Z.filter fun x => q x ∉ Z
  let E₂ : Finset V := Z.filter fun x => r x ∉ Z
  let E₃ : Finset V := Finset.univ.filter fun x : V => r x ≠ p (q x)
  have hsubset : B ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    rcases hx'.2 with hq | hr | hmul
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hq⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx'.1, hr⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmul⟩)
  have hB :
      B.card ≤ E₁.card + E₂.card + E₃.card := by
    calc
      B.card ≤ (E₁ ∪ E₂ ∪ E₃).card := Finset.card_le_card hsubset
      _ ≤ (E₁ ∪ E₂).card + E₃.card := Finset.card_union_le _ _
      _ ≤ (E₁.card + E₂.card) + E₃.card := by
        gcongr
        exact Finset.card_union_le _ _
  have hdist :
      permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤ B.card := by
    calc
      permutationDistance
          (completedRestriction r Z)
          (completedRestriction p Z * completedRestriction q Z) ≤
          (subtypeBad Z B).card :=
        permutationDistance_le_subtypeBad Z B _ _
          (fun x hx =>
            completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
              p q r Z x hx)
      _ = (Z ∩ B).card := card_subtypeBad Z B
      _ ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have hE₁ : E₁.card ≤ (Finset.univ \ Z).card :=
    card_permutation_exit_le_deleted q Z
  have hE₂ : E₂.card ≤ (Finset.univ \ Z).card :=
    card_permutation_exit_le_deleted r Z
  change
    permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤
      E₃.card + 2 * (Finset.univ \ Z).card
  omega

theorem firstFactor_completed_mul_distance_le_canonical_matched
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (Q : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ Q.parts)
    (a g : K)
    (ha : a ∈ S ^ k) (hg : g ∈ S ^ k)
    (hag : a * g ∈ S ^ k) :
    permutationDistance
        (completedRestriction
          ((A.model n).action (a * g, (1 : J))) C)
        (completedRestriction
          ((A.model n).action (a, (1 : J))) C *
         completedRestriction
          ((A.model n).action (g, (1 : J))) C) ≤
      (C ∩ matchedRadiusBad
        Q (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)).card := by
  classical
  let B := matchedRadiusBad
    Q (sourceProductRadiusLabels S F k)
    ((A.model n).action)
    (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)
  calc
    permutationDistance
        (completedRestriction
          ((A.model n).action (a * g, (1 : J))) C)
        (completedRestriction
          ((A.model n).action (a, (1 : J))) C *
         completedRestriction
          ((A.model n).action (g, (1 : J))) C) ≤
        (subtypeBad C B).card := by
      apply permutationDistance_le_subtypeBad C B
      intro x hx
      apply completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
        ((A.model n).action (a, (1 : J)))
        ((A.model n).action (g, (1 : J)))
        ((A.model n).action (a * g, (1 : J))) C x
      intro hfailure
      have hbad := (Finset.mem_filter.mp hfailure).2
      have hnotcross (b : K) (hb : b ∈ S ^ k) :
          (x : Fin (A.model n).size) ∉
            partitionWordCrossing
              Q ((A.model n).action (b, (1 : J))) := by
        intro hcross
        apply hx
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨(b, (1 : J)),
            firstFactor_mem_sourceProductRadiusLabels S F k hb,
            hcross⟩
      rcases hbad with hq | hr | hmul
      · exact hnotcross g hg
          (component_exit_mem_partitionWordCrossing
            Q C hC ((A.model n).action (g, (1 : J)))
            x.property hq)
      · exact hnotcross (a * g) hag
          (component_exit_mem_partitionWordCrossing
            Q C hC ((A.model n).action (a * g, (1 : J)))
            x.property hr)
      · have hnotroot :
            (x : Fin (A.model n).size) ∉
              finiteRootBad (A.model n)
                (sourceProductRadiusLabels S F k) := by
          intro hroot
          apply hx
          apply Finset.mem_union_left
          exact Finset.mem_union_right _ hroot
        have hroot := finiteRootBad_multiplicative
          (A.model n) (sourceProductRadiusLabels S F k)
          (firstFactor_mem_sourceProductRadiusLabels S F k ha)
          (firstFactor_mem_sourceProductRadiusLabels S F k hg)
          hnotroot
        apply hmul
        simpa only [Prod.mk_mul_mk, mul_one, Equiv.Perm.mul_apply] using hroot
    _ = (C ∩ matchedRadiusBad
        Q (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)).card :=
      card_subtypeBad C B

theorem density_relative_survivors
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (b : ℕ → ℕ)
    (hb : Tendsto
      (fun n => (b n : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n => (b n : ℝ) /
        (Finset.univ \ D n : Finset (V n)).card)
      atTop (nhds 0) := by
  have hcover := surviving_card_ratio_tendsto_one V D hZ hdeleted
  have hquotient : Tendsto
      ((fun n => (b n : ℝ) / Fintype.card (V n)) /
        (fun n =>
          ((Finset.univ \ D n : Finset (V n)).card : ℝ) /
            Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [zero_div] using
      hb.div hcover (by norm_num : (1 : ℝ) ≠ 0)
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
    (b n : ℝ) / (Finset.univ \ D n : Finset (V n)).card =
      ((b n : ℝ) / Fintype.card (V n)) /
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n))
  field_simp [hNreal, hZreal]

theorem twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (S : Finset K) (hone : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (nhds 0))
    (D : (n : ℕ) → Finset
      {x : Fin (A.model (ν n)).size // x ∈ C n})
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C n).card)
      atTop (nhds 0))
    (a g : K) :
    Tendsto
      (fun n =>
        normalizedHamming
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a * g, (1 : J))) (C n))
            (Finset.univ \ D n))
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a, (1 : J))) (C n))
            (Finset.univ \ D n) *
           completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (g, (1 : J))) (C n))
            (Finset.univ \ D n)))
      atTop (nhds 0) := by
  classical
  let W : ℕ → Type := fun n =>
    {x : Fin (A.model (ν n)).size // x ∈ C n}
  let Z : (n : ℕ) → Finset (W n) := fun n => Finset.univ \ D n
  let B : ℕ → ℕ := fun n =>
    (C n ∩ matchedRadiusBad
      (Q n) (sourceProductRadiusLabels S F (r n))
      ((A.model (ν n)).action)
      (canonicalProductRadiusBad
        A S hsymmetric hgenerates F (ν n) (r n))).card
  have hdeletedW : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (W n))
      atTop (nhds 0) := by
    simpa only [W, Fintype.card_coe] using hdeleted
  have hBW : Tendsto
      (fun n => (B n : ℝ) / Fintype.card (W n))
      atTop (nhds 0) := by
    simpa only [B, W, Fintype.card_coe] using hmatched
  have hBfinal : Tendsto
      (fun n => (B n : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    exact density_relative_survivors W D hZ hdeletedW B hBW
  have hDfinal : Tendsto
      (fun n => ((D n).card : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    exact deleted_density_relative_survivors W D hZ hdeletedW
  have hupper : Tendsto
      (fun n => (B n : ℝ) / (Z n).card +
        2 * ((D n).card : ℝ) / (Z n).card)
      atTop (nhds 0) := by
    convert hBfinal.add (hDfinal.const_mul 2) using 1 <;>
      simp [mul_div_assoc]
  let w : K → List ↥S :=
    symmetricGeneratorWord S hsymmetric hgenerates
  have hw : ∀ b : K, ((w b).map fun i : ↥S => (i : K)).prod = b :=
    symmetricGeneratorWord_prod S hsymmetric hgenerates
  have hlarge : ∀ᶠ n in atTop,
      max (w a).length (max (w g).length (w (a * g)).length) ≤ r n :=
    Filter.tendsto_atTop.1 hr _
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      normalizedHamming_nonneg _ _)
    ?_ hupper
  filter_upwards [hlarge] with n hn
  have ha : a ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  have hg : g ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  have hag : a * g ∈ S ^ r n :=
    mem_generator_pow_of_chosen_word_length S hone w hw
      (by omega)
  let p : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (a, (1 : J))) (C n)
  let q : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (g, (1 : J))) (C n)
  let s : Equiv.Perm (W n) :=
    completedRestriction ((A.model (ν n)).action (a * g, (1 : J))) (C n)
  have hfirst :
      permutationDistance s (p * q) ≤ B n := by
    exact firstFactor_completed_mul_distance_le_canonical_matched
      A S hsymmetric hgenerates F (ν n) (r n)
      (Q n) (C n) (hC n) a g ha hg hag
  have hfailure :
      (Finset.univ.filter fun x : W n =>
        s x ≠ p (q x)).card ≤ B n := by
    calc
      (Finset.univ.filter fun x : W n =>
        s x ≠ p (q x)).card =
          permutationDistance s (p * q) := by
        unfold permutationDistance hammingDist
        congr 1
      _ ≤ B n := hfirst
  have hdist := completedRestriction_mul_distance_le_failure_add_deleted
    p q s (Z n)
  have hcomplement :
      (Finset.univ \ Z n : Finset (W n)) = D n := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Decidable.not_not, Z]
  have hnat :
      permutationDistance
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) ≤
        B n + 2 * (D n).card := by
    rw [hcomplement] at hdist
    omega
  have hreal :
      (permutationDistance
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) : ℝ) ≤
        (B n : ℝ) + 2 * (D n).card := by
    exact_mod_cast hnat
  have hnormalized := div_le_div_of_nonneg_right hreal
    (show (0 : ℝ) ≤ ((Z n).card : ℝ) by positivity)
  change
    normalizedHamming
        (completedRestriction s (Z n))
        (completedRestriction p (Z n) *
          completedRestriction q (Z n)) ≤
      (B n : ℝ) / (Z n).card +
        2 * ((D n).card : ℝ) / (Z n).card
  simpa only [normalizedHamming, Equiv.Perm.coe_mul, Function.comp_apply, Fintype.card_coe,
    mul_div_assoc,
    permutationDistance, add_div] using hnormalized

end KunActualTwicePrunedFirstFactorRootBad

open KunActualTwicePrunedFirstFactorRootBad

namespace KunActualSelectedPrunedSourceFiniteModelBridge

open Filter Topology
open MatchedComponentCompletion
open KunActualSoficRootRadius
open scoped BigOperators Pointwise

theorem completed_generator_one_of_internal_agreement
    {G : Type} [Group G] (S : Finset G)
    {W : Type}
    (σ : ↥S → Equiv.Perm W) (Z : Finset W)
    (τ : ↥S → Equiv.Perm {x : W // x ∈ Z})
    (hagrees : ∀ i (x : W) (hx : x ∈ Z)
      (_hi : σ i x ∈ Z),
        ((τ i ⟨x, hx⟩ : {x : W // x ∈ Z}) : W) = σ i x)
    (hidentity : ∀ i : ↥S, (i : G) = 1 → σ i = 1)
    (i : ↥S) (hi : (i : G) = 1) : τ i = 1 := by
  have hσ : σ i = 1 := hidentity i hi
  ext x
  have hinside : σ i (x : W) ∈ Z := by
    rw [hσ]
    exact x.property
  simpa only [Equiv.Perm.coe_one, id_eq, SetLike.coe_eq_coe, Subtype.coe_eta, hσ] using
    hagrees i (x : W) x.property hinside

theorem nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
    {G J : Type} [Group G] [Group J]
    (P : KazhdanPair.{0, 0} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (F : Finset J)
    (W : ℕ → Type)
    [∀ n, Finite (W n)] [∀ n, DecidableEq (W n)]
    (σ : (n : ℕ) → ↥S → Equiv.Perm (W n))
    (hσone : ∀ n (i : ↥S), (i : G) = 1 → σ n i = 1)
    (p : (n : ℕ) → J → Equiv.Perm (W n))
    (hp : ∀ n, p n 1 = 1)
    (Z : (n : ℕ) → Finset (W n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hlarge : Tendsto (fun n => (Z n).card) atTop atTop)
    (τ : (n : ℕ) → ↥S →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hτ : ∀ n i (x : W n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((τ n i ⟨x, hx⟩ :
          {x : W n // x ∈ Z n}) : W n) = σ n i x)
    (ρ : (n : ℕ) → G →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hρone : ∀ n, ρ n 1 = 1)
    (hρmul : ∀ a g : G,
      Tendsto
        (fun n => normalizedHamming
          (ρ n (a * g)) (ρ n a * ρ n g))
        atTop (𝓝 0))
    (hρgenerator : ∀ i : ↥S,
      Tendsto
        (fun n => normalizedHamming
          (τ n i) (ρ n (i : G)))
        atTop (𝓝 0))
    (ell : ℝ) (hell : 0 < ell)
    (hexp : ∀ n, ∀ E : Finset {x : W n // x ∈ Z n},
      ell * min (E.card : ℝ)
        ((Fintype.card {x : W n // x ∈ Z n} : ℝ) - E.card) ≤
          (boundary (τ n) E : ℝ))
    (hbad : Tendsto
      (fun n =>
        ((MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (𝓝 0)) :
    Nonempty (ExpandingCentralizerFiniteModel J F) := by
  classical
  let : ∀ n, Fintype (W n) := fun n => Fintype.ofFinite (W n)
  let V : ℕ → Type := fun n => {x : W n // x ∈ Z n}
  let (n : ℕ) : Nonempty (V n) :=
    ⟨⟨(hZ n).choose, (hZ n).choose_spec⟩⟩
  let w : G → List ↥S :=
    KunActualSoficRootRadius.symmetricGeneratorWord
      S hsymmetric hgenerates
  have hw (g : G) :
      ((w g).map fun i : ↥S => (i : G)).prod = g := by
    exact KunActualSoficRootRadius.symmetricGeneratorWord_prod
      S hsymmetric hgenerates g
  let φ : (n : ℕ) → G → Equiv.Perm (V n) :=
    fun n g => ((w g).map (τ n)).prod
  have hφone (n : ℕ) : φ n 1 = 1 := by
    simp only [symmetricGeneratorWord_one, List.map_nil, List.prod_nil, φ, w]
  have hφgenerator (n : ℕ) (i : ↥S) :
      φ n (i : G) = τ n i := by
    by_cases hi : (i : G) = 1
    · have hτone : τ n i = 1 :=
        completed_generator_one_of_internal_agreement
          S (σ n) (Z n) (τ n) (hτ n) (hσone n) i hi
      simp only [hi, symmetricGeneratorWord_one, List.map_nil, List.prod_nil, hτone, φ, w]
    · simp only [KunActualSoficRootRadius.symmetricGeneratorWord_generator S hsymmetric
      hgenerates i hi,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, φ, w]
  have hφmul (a g : G) :
      Tendsto
        (fun n => normalizedHamming
          (φ n (a * g)) (φ n a * φ n g))
        atTop (𝓝 0) := by
    simpa only [CompletedChosenWordLocalRoot.chosenWordEvaluation] using
      CompletedChosenWordLocalRoot.chosenWordEvaluation_multiplicative_tendsto V ρ hρone
        hρmul
        (fun i : ↥S => (i : G)) w hw τ hρgenerator a g
  let root : (n : ℕ) → ℕ → Finset (V n) :=
    fun n k =>
      CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad
        (φ n) S k
  have hroot (k : ℕ) :
      Tendsto
        (fun n => ((root n k).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
    exact
      CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
      V φ S hφmul k
  let source : (n : ℕ) → Finset (V n) :=
    fun n => MatchedComponentCompletion.subtypeBad
      (Z n)
      (MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Z n))
  have hsource :
      Tendsto
        (fun n => ((source n).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
    simpa [source, V,
      MatchedComponentCompletion.card_subtype_sourceCompletionBad,
      Fintype.card_coe] using hbad
  have hVpositive (n : ℕ) : 0 < Fintype.card (V n) := by
    simpa [V, Fintype.card_coe] using (hZ n).card_pos
  have hVlarge :
      Tendsto (fun n => Fintype.card (V n)) atTop atTop := by
    simpa [V, Fintype.card_coe] using hlarge
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδpositive (j : ℕ) : 0 < δ j := by
    dsimp [δ]
    positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let d : ℕ := S.card
  have hd : 0 < d := by
    dsimp [d]
    exact Finset.card_pos.mpr ⟨1, honeS⟩
  let q : ℝ :=
    KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor P S
  have hq : q < 1 := by
    exact KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
      P S ⟨1, honeS⟩
  let α : ℕ → ℝ :=
    fun j => ell * δ j / (2 * (ell + 8 * (d : ℝ)))
  have hα (j : ℕ) : 0 < α j := by
    dsimp [α]
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  let spectral (j : ℕ) :=
    KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
        P S honeS hcover hsymmetric w ell (α j) hell (hα j)
  let radius : ℕ → ℕ := fun j => (spectral j).choose
  have hspectral (j : ℕ) := (spectral j).choose_spec
  let R : ℕ → ℕ := fun j => max j (radius j)
  have hR (j : ℕ) : j ≤ R j := le_max_left _ _
  obtain ⟨m, rootError, t, hm, hRm, hδm, hrelative,
      hrootError, hrootlower, hrootlimit, htdef, htpositive,
      htroot, htsource, htrooterror, htlimit, htarget,
      hsmall, hslow⟩ :=
    exists_prescribed_radius_union_source_completed_tolerance
        V hVpositive hVlarge root source hroot hsource
        δ hδpositive hδ R hR d hd ell q hell hq
  let pZ : (n : ℕ) → J → Equiv.Perm (V n) :=
    fun n j => MatchedComponentCompletion.completedRestriction
      (p n j) (Z n)
  have hpZ (n : ℕ) : pZ n 1 = 1 := by
    dsimp [pZ]
    rw [hp n,
      MatchedComponentCompletion.completedRestriction_one]
  have hsourcebudget (n : ℕ) :
      2 * Fintype.card (↥S) *
        (MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Z n)).card ≤ t n := by
    have hbudget := htsource n
    change
      2 * S.card *
        (MatchedComponentCompletion.subtypeBad
          (Z n)
          (MatchedComponentCompletion.sourceCompletionBad
            (σ n) (p n) F (Z n))).card ≤ t n at hbudget
    rw [MatchedComponentCompletion.card_subtype_sourceCompletionBad]
      at hbudget
    simpa only [Fintype.card_coe] using hbudget
  have htable :=
    eventually_completed_sourceCentralizer_table_of_bad_density
        W σ p F Z hZ hbad τ hτ t hsourcebudget
  have hdefect : ∀ᶠ n in atTop,
      ∀ j ∈ CompressionCriterion.productTrackedTable F,
        permutationCommutationDefect
          (τ n) (pZ n j) ≤ t n := by
    filter_upwards [htable] with n hn
    simpa only using hn.2.2
  have hmulJ : ∀ᶠ n in atTop,
      ∀ a ∈ F, ∀ b ∈ F,
        5 * permutationDistance
          (pZ n (a * b)) (pZ n a * pZ n b) ≤
            Fintype.card (V n) := by
    filter_upwards [htable] with n hn
    simpa [pZ, V] using hn.1
  have hsepJ : ∀ᶠ n in atTop,
      ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
        Fintype.card (V n) <
          5 * permutationDistance (pZ n a) (pZ n b) := by
    filter_upwards [htable] with n hn
    simpa [pZ, V] using hn.2.1
  have himprove : ∀ᶠ n in atTop,
      HasAlmostCentralizerImprovement (τ n) (t n) := by
    filter_upwards [hslow] with n hn
    apply hspectral (m n) (V n) (τ n) (φ n) (t n)
      (root n (R (m n)) ∪ source n)
    · intro g
      rfl
    · exact hφone n
    · exact hφgenerator n
    · exact hexp n
    · simpa only [one_div] using hn
    · right
      refine ⟨by exact_mod_cast htpositive n, ?_, ?_, ?_⟩
      · simpa only using htarget n
      · have hbudget :
            2 * d * (root n (R (m n)) ∪ source n).card ≤ t n := by
          rw [htdef n]
          omega
        exact_mod_cast hbudget
      · intro a g hlength x hx
        have hxroot : x ∉ root n (R (m n)) := by
          intro hxroot
          exact hx (Finset.mem_union_left _ hxroot)
        have hradius : radius (m n) ≤ R (m n) := by
          exact le_max_right _ _
        exact
          CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
            S honeS w hw (φ n) (R (m n)) a g
            (hlength.trans hradius) x hxroot
  exact
    nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
      F V (↥S) τ pZ hpZ t ell hell hdefect
      (Filter.Eventually.of_forall hexp)
      hsmall himprove hmulJ hsepJ

end KunActualSelectedPrunedSourceFiniteModelBridge

open KunActualSelectedPrunedSourceFiniteModelBridge

namespace KunActualCanonicalSelectedFiniteModelComposition

open Filter Topology
open MatchedComponentCompletion
open CanonicalProductRadiusBadMatchedCapture

theorem nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
    {K J : Type} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficApproximation (K × J))
    (P : KazhdanPair.{0, 0} K)
    (S : Finset K) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (𝓝 0))
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hadd : ∀ n,
      ∀ E : Finset {x : Fin (A.model (ν n)).size // x ∈ C n},
        γ * min (E.card : ℝ)
            ((Fintype.card
              {x : Fin (A.model (ν n)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (ν n)).size // x ∈ C n} ≤
          (boundary
            (fun i : ↥S =>
              completedRestriction
                ((A.model (ν n)).action ((i : K), (1 : J)))
                (C n)) E : ℝ)) :
    Nonempty (ExpandingCentralizerFiniteModel J F) := by
  classical
  obtain ⟨N, D, τ, hZ, hdeleted, hZlarge, hagrees, hexp⟩ :=
    KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
      A S ν Q C hC hlarge γ hγ a ha hadd
  let ν' : ℕ → ℕ := fun n => ν (n + N)
  let Q' : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν' n)).size)) :=
    fun n => Q (n + N)
  let C' : (n : ℕ) → Finset (Fin (A.model (ν' n)).size) :=
    fun n => C (n + N)
  let r' : ℕ → ℕ := fun n => r (n + N)
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have hC' (n : ℕ) : C' n ∈ (Q' n).parts := hC (n + N)
  have hr' : Tendsto r' atTop atTop := by
    exact hr.comp hshift
  have hmatched' : Tendsto
      (fun n =>
        (((C' n ∩ matchedRadiusBad
          (Q' n) (sourceProductRadiusLabels S F (r' n))
          ((A.model (ν' n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν' n) (r' n))).card : ℝ) /
            (C' n).card))
      atTop (𝓝 0) := by
    exact hmatched.comp hshift
  let W : ℕ → Type :=
    fun n => {x : Fin (A.model (ν' n)).size // x ∈ C' n}
  let Z : (n : ℕ) → Finset (W n) :=
    fun n => Finset.univ \ D n
  let σ : (n : ℕ) → ↥S → Equiv.Perm (W n) :=
    fun n i => completedRestriction
      ((A.model (ν' n)).action ((i : K), (1 : J))) (C' n)
  let p : (n : ℕ) → J → Equiv.Perm (W n) :=
    fun n j => completedRestriction
      ((A.model (ν' n)).action ((1 : K), j)) (C' n)
  let ρ : (n : ℕ) → K →
      Equiv.Perm {x : W n // x ∈ Z n} :=
    fun n g => completedRestriction
      (completedRestriction
        ((A.model (ν' n)).action (g, (1 : J))) (C' n))
      (Z n)
  have hσone (n : ℕ) (i : ↥S) (hi : (i : K) = 1) :
      σ n i = 1 := by
    dsimp [σ]
    rw [hi]
    change completedRestriction
      ((A.model (ν' n)).action (1 : K × J)) (C' n) = 1
    rw [(A.model (ν' n)).map_one, completedRestriction_one]
  have hp (n : ℕ) : p n 1 = 1 := by
    dsimp [p]
    change completedRestriction
      ((A.model (ν' n)).action (1 : K × J)) (C' n) = 1
    rw [(A.model (ν' n)).map_one, completedRestriction_one]
  have hρone (n : ℕ) : ρ n 1 = 1 := by
    dsimp [ρ]
    change completedRestriction
      (completedRestriction
        ((A.model (ν' n)).action (1 : K × J)) (C' n))
      (Z n) = 1
    rw [(A.model (ν' n)).map_one,
      completedRestriction_one, completedRestriction_one]
  have hρmul (b g : K) :
      Tendsto
        (fun n => normalizedHamming
          (ρ n (b * g)) (ρ n b * ρ n g))
        atTop (𝓝 0) := by
    exact
      twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
      A S hone hsymmetric hgenerates F ν' Q' C' hC'
      r' hr' hmatched' D hZ hdeleted b g
  have hagrees' : ∀ n (i : ↥S)
      (x : {y : W n // y ∈ Z n}),
        completedRestriction
            ((A.model (ν' n)).action ((i : K), (1 : J)))
            (C' n) x.val ∈ Z n →
          (τ n i x).val =
            completedRestriction
              ((A.model (ν' n)).action ((i : K), (1 : J)))
              (C' n) x.val := by
    intro n i x hx
    exact hagrees n i x.val x.property hx
  have hρgenerator (i : ↥S) :
      Tendsto
        (fun n => normalizedHamming
          (τ n i) (ρ n (i : K)))
        atTop (𝓝 0) := by
    exact
      twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
      (fun n => Fin (A.model (ν' n)).size)
      (fun n (j : ↥S) =>
        (A.model (ν' n)).action ((j : K), (1 : J)))
      (fun n (g : K) =>
        (A.model (ν' n)).action (g, (1 : J)))
      (fun j : ↥S => (j : K)) C' D τ
      (fun _ _ => rfl) hagrees' hZ hdeleted i
  have hsource : Tendsto
      (fun n =>
        ((sourceCompletionBad (σ n) (p n) F (Z n)).card : ℝ) /
          (Z n).card)
      atTop (𝓝 0) := by
    exact
      pruned_sourceCompletionBad_density_tendsto_zero_of_canonical_matched
      A S hsymmetric hgenerates F ν' Q' C' hC'
      r' hmatched' D hZ hdeleted
  have hhalf : 0 < γ / 2 := by positivity
  exact
    nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
    P S hone hcover hsymmetric hgenerates F W σ hσone
    p hp Z hZ hZlarge τ hagrees ρ hρone hρmul hρgenerator
    (γ / 2) hhalf hexp hsource

end KunActualCanonicalSelectedFiniteModelComposition

open KunActualCanonicalSelectedFiniteModelComposition

namespace KunLiteralSourceSelectedComponents

theorem sourceTransportedReferenceGenerator_disagreement_mem
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (SΓ : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (n : ℕ) (i : ↥SΓ) (x : Fin (A.model n).size)
    (h : sourceTransportedReferenceGenerators A SΓ n i x ≠
      ((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A).model
        n).action
        (SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
          (i : prefixElementaryGroup alphaPrefixCode),
          1) x) :
    x ∈ sourceGeneratorFamilyConjugacyBad A SΓ n := by
  classical
  unfold sourceGeneratorFamilyConjugacyBad
  apply Finset.mem_biUnion.mpr
  refine ⟨(i : prefixElementaryGroup
    alphaPrefixCode), i.property, ?_⟩
  unfold sourceConjugacyDisagreementBad
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  change
    (A.model n).action
      (SourceBothCompressionNormalization.sourceCompressionUElement *
        SourceGeneratedWordCrossing.sourceAlphaInclusion
          (i : prefixElementaryGroup
            alphaPrefixCode) *
        SourceBothCompressionNormalization.sourceCompressionUElement⁻¹) x ≠
      sourceTransportedReferenceGenerators A SΓ n i x
  rw [← SourceProductThroughAlpha.source_u_conjugated_product_generator]
  exact Ne.symm h

end KunLiteralSourceSelectedComponents

namespace KunActualSourceSelectedCompletedGeneratorExpansion

open Filter Topology
open scoped BigOperators

theorem exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (S : Finset
      (prefixElementaryGroup alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (prefixElementaryGroup
          alphaPrefixCode)) = ⊤)
    (Q : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1]))
    (N : ℕ) (r : ℕ → ℕ)
    (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size))
    (gamma : ℝ)
    (hC : ∀ n, (C n).Nonempty)
    (hexpand : ∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
      D ⊆ C n → 2 * D.card ≤ (C n).card →
        gamma * (D.card : ℝ) ≤
          (boundary
            (KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
              A S (n + N)) D : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (boundary
          (KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
            A S (n + N)) (C n) : ℝ) / (C n).card)
      atTop (nhds 0))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ matchedRadiusBad
          (KunLiteralSourceSelectedComponents.sourceTransportedPartition
            A Q (n + N))
          (KunLiteralSourceSelectedComponents.sourceSelectedProductRadiusLabels
            S F (r n))
          (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
            A).model (n + N)).action)
          (KunLiteralSourceSelectedComponents.sourceSelectedRadiusBad
            A S hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
              (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset
        {x : Fin (A.model (n + N)).size // x ∈ C n},
        gamma * min (E.card : ℝ)
          ((Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} ≤
            (boundary
              (fun i :
                ↥(SourceProductThroughAlpha.sourceCompressedGeneratingFinset
                  S) =>
                MatchedComponentCompletion.completedRestriction
                  (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
                    A).model (n + N)).action
                    ((i : prefixElementaryGroup
                      alphaZeroPrefixCode), 1))
                  (C n)) E : ℝ) := by
  classical
  have hbad_density : Tendsto
      (fun n =>
        (((C n ∩
          KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
            A S (n + N)).card : ℝ) / (C n).card))
      atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hguarded
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (by
      intro x hx
      obtain ⟨hxC, hxE⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨hxC, ?_⟩
      unfold matchedRadiusBad
      apply Finset.mem_union_left
      change x ∈
        CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          (SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A)
          (SourceProductThroughAlpha.sourceCompressedGeneratingFinset S)
          (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
            S hsymmetric)
          (SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
            S hgenerates)
          F (n + N) (r n) ∪
          KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
            A S (n + N)
      exact Finset.mem_union_right _ hxE)
  obtain ⟨a, ha_nonnegative, ha_zero, ha_expand⟩ :=
    exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
      (fun n => Fin (A.model (n + N)).size)
      (↥S) C
      (fun n =>
        KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N))
      hC
      (fun n =>
        KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
          A S (n + N))
      (fun n (i : ↥S) =>
        ((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
          A).model (n + N)).action
            (SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
              (i : prefixElementaryGroup
                alphaPrefixCode), 1))
      gamma hexpand
      (fun n i x _hx hdis =>
        KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
          A S (n + N) i x hdis)
      hboundary hbad_density
  refine ⟨a, ha_nonnegative, ha_zero, ?_⟩
  intro n E
  have h := ha_expand n E
  have hreindex :
      boundary
        (fun i : ↥S =>
          MatchedComponentCompletion.completedRestriction
            (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action
              (SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
                (i : prefixElementaryGroup
                  alphaPrefixCode), 1))
            (C n)) E =
        boundary
          (fun i :
            ↥(SourceProductThroughAlpha.sourceCompressedGeneratingFinset
              S) =>
            MatchedComponentCompletion.completedRestriction
              (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
                A).model (n + N)).action
                ((i : prefixElementaryGroup
                  alphaZeroPrefixCode), 1))
              (C n)) E := by
    exact
      SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
        S
        (fun i :
          ↥(SourceProductThroughAlpha.sourceCompressedGeneratingFinset
            S) =>
          MatchedComponentCompletion.completedRestriction
            (((SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action
              ((i : prefixElementaryGroup
                alphaZeroPrefixCode), 1))
            (C n))
        E
  exact h.trans_eq (congrArg (fun t : ℕ => (t : ℝ)) hreindex)

end KunActualSourceSelectedCompletedGeneratorExpansion

open KunActualSourceSelectedCompletedGeneratorExpansion

namespace KunLiteralNineSourceFiniteModels

open Filter Topology
open CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise

theorem source_ambient_nonempty_expandingCentralizerFiniteModel
    (A : SoficApproximation
      (prefixElementaryGroup ninePrefixCode))
    (F : Finset
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        [0, 0, 0, 1])) :
    Nonempty
      (ExpandingCentralizerFiniteModel
        (ThompsonPrefixInsertion.localPrefixTranspositionGroup
          [0, 0, 0, 1]) F) := by
  classical
  obtain ⟨S, hsymmetric, hgenerates, Q, gamma, N, r, C,
      hone, hgamma, _hsource, hr, hC, hCnonempty,
      hexpand, hboundary, hguarded, hlarge⟩ :=
    KunLiteralSourceSelectedComponents.exists_source_selected_components
      A F
  let K : Type :=
    prefixElementaryGroup alphaZeroPrefixCode
  let J : Type :=
    ThompsonPrefixInsertion.localPrefixTranspositionGroup
      [0, 0, 0, 1]
  let AP : SoficApproximation (K × J) :=
    SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
      A
  let SK : Finset K :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset S
  have hSKone : 1 ∈ SK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_one_mem
      S hone
  have hSKsymmetric : ∀ k ∈ SK, k⁻¹ ∈ SK :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      S hsymmetric
  have hSKgenerates : Subgroup.closure (SK : Set K) = ⊤ :=
    SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      S hgenerates
  have hpair : ∃ P : KazhdanPair.{0, 0} K,
      P.generators = SK :=
    SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
      S hsymmetric hgenerates
  obtain ⟨PK, hPK⟩ := hpair
  have hcover : PK.generators ⊆ SK := by
    rw [hPK]
  let ν : ℕ → ℕ := fun n => n + N
  let QK : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (AP.model (ν n)).size)) :=
    fun n =>
      KunLiteralSourceSelectedComponents.sourceTransportedPartition
        A Q (n + N)
  have hCK (n : ℕ) : C n ∈ (QK n).parts := hC n
  have hbad_eq (n : ℕ) :
      KunLiteralSourceSelectedComponents.sourceSelectedRadiusBad
        A S hsymmetric hgenerates F (n + N) (r n) =
        canonicalProductRadiusBad
          AP SK hSKsymmetric hSKgenerates F (ν n) (r n) ∪
        KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N) := by
    rfl
  have hlabel_eq (n : ℕ) :
      KunLiteralSourceSelectedComponents.sourceSelectedProductRadiusLabels
        S F (r n) =
      sourceProductRadiusLabels SK F (r n) := by
    rfl
  have hguarded' :
      Tendsto
        (fun n =>
          (((C n ∩ matchedRadiusBad
            (QK n)
            (sourceProductRadiusLabels SK F (r n))
            ((AP.model (ν n)).action)
            (canonicalProductRadiusBad
              AP SK hSKsymmetric hSKgenerates F (ν n) (r n) ∪
              KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
                A S (n + N))).card : ℝ) /
              (C n).card))
        atTop (𝓝 0) := by
    have hguarded_eq := hguarded
    simp_rw [hbad_eq, hlabel_eq] at hguarded_eq
    convert hguarded_eq using 1
    funext n
    simp only [QK, AP, ν]
    congr 2
  have hcanonical :
      Tendsto
        (fun n =>
          (((C n ∩ matchedRadiusBad
            (QK n)
            (sourceProductRadiusLabels SK F (r n))
            ((AP.model (ν n)).action)
            (canonicalProductRadiusBad
              AP SK hSKsymmetric hSKgenerates F (ν n) (r n))).card : ℝ) /
              (C n).card))
        atTop (𝓝 0) := by
    exact KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
      (fun n => Fin (AP.model (ν n)).size)
      (fun n => (Finset.univ : Finset (Fin (AP.model (ν n)).size)))
      QK
      (fun n => sourceProductRadiusLabels SK F (r n))
      (fun n => (AP.model (ν n)).action)
      (fun n => canonicalProductRadiusBad
        AP SK hSKsymmetric hSKgenerates F (ν n) (r n))
      (fun n =>
        KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N))
      C hguarded'
  obtain ⟨a, _ha_nonnegative, ha, hadd⟩ :=
    exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
      A S hsymmetric hgenerates Q F N r C gamma
      hCnonempty hexpand hboundary hguarded
  exact
    nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
    AP PK SK hSKone hcover hSKsymmetric hSKgenerates F
    ν QK C hCK r hr hcanonical hlarge gamma hgamma a ha hadd

end KunLiteralNineSourceFiniteModels

namespace SourceTopLevelCompressionFinal

open SourceTopLevelCompression
open KunLiteralNineSourceFiniteModels

theorem sourceLocalPrefixTranspositionGroup_lef_of_sofic :
    Sofic
        (prefixElementaryGroup ninePrefixCode) →
      LEF
        (ThompsonPrefixInsertion.localPrefixTranspositionGroup
          [0, 0, 0, 1]) := by
  intro hsource
  exact sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
    (fun A _ F =>
      source_ambient_nonempty_expandingCentralizerFiniteModel A F)
    hsource

theorem ninePrefixElementaryGroup_not_sofic :
    ¬ Sofic
      (prefixElementaryGroup ninePrefixCode) := by
  intro hsource
  exact sourceLocalPrefixTranspositionGroup_notLEF
    (sourceLocalPrefixTranspositionGroup_lef_of_sofic hsource)

theorem binaryLeavittElementaryGroup_not_sofic :
    ¬ Sofic (binaryLeavittElementaryGroup 9) := by
  intro hsofic
  let : Sofic
    (binaryLeavittElementaryGroup 9) := hsofic
  exact ninePrefixElementaryGroup_not_sofic
    (sofic_of_injective
      ninePrefixElementaryGroupEquiv.symm.toMonoidHom
      ninePrefixElementaryGroupEquiv.symm.injective)

/-- There exists a finitely presented group that is not sofic. -/
public theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ Sofic G := by
  exact exists_finitelyPresented_not_sofic_of_not_sofic
    binaryLeavittElementaryGroup_not_sofic

end SourceTopLevelCompressionFinal

end SoficGroups

end
