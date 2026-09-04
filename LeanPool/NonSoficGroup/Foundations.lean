/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.RingQuot
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Foundations for the non-sofic group construction

This file develops the finite-permutation, property-T, Leavitt-algebra, and
prefix-action infrastructure used by the construction.
-/

noncomputable section

namespace SoficGroups

section

open Filter Topology

universe u v w

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev UnitaryRepresentation (G : Type u) (H : Type v) [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  G →* (H ≃ₗᵢ[ℂ] H)

open scoped Pointwise commutatorElement symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure KazhdanPair (G : Type u) [Group G] where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generators : Finset G
  /-- Internal interface connecting the split non-sofic proof modules. -/
  kazhdanConstant : ℝ
  positive : 0 < kazhdanConstant
  invariant :
    ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (π : UnitaryRepresentation G H) (ξ : H),
      ‖ξ‖ = 1 →
      (∀ g ∈ generators, ‖π g ξ - ξ‖ < kazhdanConstant) →
      ∃ η : H, η ≠ 0 ∧ ∀ g : G, π g η = η

/-- Internal interface connecting the split non-sofic proof modules. -/
public
class HasPropertyT (G : Type u) [Group G] : Prop where
  exists_kazhdanPair : Nonempty (KazhdanPair.{u, v} G)

public
theorem hasPropertyT_of_mulEquiv {G : Type u} {G' : Type w}
    [Group G] [Group G'] (e : G ≃* G')
    [HasPropertyT.{u, v} G] : HasPropertyT.{w, v} G' := by
  classical
  obtain ⟨P⟩ := HasPropertyT.exists_kazhdanPair (G := G)
  refine ⟨⟨{
    generators := P.generators.image e
    kazhdanConstant := P.kazhdanConstant
    positive := P.positive
    invariant := ?_
  }⟩⟩
  intro H _ _ _ π ξ hξ hξ'
  obtain ⟨η, hη, hη'⟩ := P.invariant H (π.comp e.toMonoidHom) ξ hξ (by
    intro g hg
    exact hξ' (e g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
  refine ⟨η, hη, ?_⟩
  intro g
  obtain ⟨g, rfl⟩ := e.surjective g
  exact hη' g

/-- The proportion of points on which two finite permutations differ. -/
public
def normalizedHamming {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : ℝ :=
  (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y

@[simp]
public
theorem normalizedHamming_self {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Equiv.Perm Y) : normalizedHamming p p = 0 := by
  simp only [normalizedHamming, hammingDist_self, CharP.cast_eq_zero, zero_div]

public
theorem normalizedHamming_comm {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : normalizedHamming p q = normalizedHamming q p := by
  simp only [normalizedHamming, hammingDist_comm]

public
theorem normalizedHamming_nonneg {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : 0 ≤ normalizedHamming p q := by
  unfold normalizedHamming
  positivity

public
theorem normalizedHamming_triangle {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q r : Equiv.Perm Y) :
    normalizedHamming p r ≤ normalizedHamming p q + normalizedHamming q r := by
  have h := hammingDist_triangle (fun y => p y) (fun y => q y) (fun y => r y)
  unfold normalizedHamming
  rw [← add_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · positivity

private theorem normalizedHamming_le_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : normalizedHamming p q ≤ 1 := by
  have hcard :
      hammingDist (fun y => p y) (fun y => q y) ≤ Fintype.card Y :=
    hammingDist_le_card_fintype
  unfold normalizedHamming
  calc
    (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y ≤
        (Fintype.card Y : ℝ) / Fintype.card Y := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ ≤ 1 := by
      by_cases h : Fintype.card Y = 0 <;> simp [h]

public
theorem normalizedHamming_mul_left {Y : Type*} [Fintype Y] [DecidableEq Y]
    (s p q : Equiv.Perm Y) :
    normalizedHamming (s * p) (s * q) = normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => s (p y)) (fun y => s (q y)) =
        hammingDist (fun y => p y) (fun y => q y) :=
    hammingDist_comp (fun (_ : Y) (z : Y) => s z) (fun _ => s.injective)
  simp only [normalizedHamming, Equiv.Perm.mul_apply, hdist]

public
theorem normalizedHamming_mul_right {Y : Type*} [Fintype Y] [DecidableEq Y]
    (s p q : Equiv.Perm Y) :
    normalizedHamming (p * s) (q * s) = normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => (p * s) y) (fun y => (q * s) y) =
        hammingDist (fun y => p y) (fun y => q y) := by
    unfold hammingDist
    apply Finset.card_bij (fun y _ => s y)
    · intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hy).2
    · intro y hy z hz h
      exact s.injective h
    · intro y hy
      refine ⟨s.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
        (Finset.mem_filter.mp hy).2
  unfold normalizedHamming
  exact congrArg
    (fun k : ℕ => (k : ℝ) / (Fintype.card Y : ℝ)) hdist

/-- A finite permutation-valued approximation to a group action. -/
public
structure PermutationModel (G : Type*) [Group G] where
  /-- The cardinality of the finite model. -/
  size : ℕ
  /-- The model is nonempty. -/
  size_pos : 0 < size
  /-- The permutation assigned to each group element. -/
  action : G → Equiv.Perm (Fin size)
  /-- The identity is assigned the identity permutation. -/
  map_one : action 1 = 1

/-- Multiplication and separation hold on a prescribed finite set. -/
public
structure GoodOn {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) (ε : ℝ) : Prop where
  /-- The model is approximately multiplicative on the prescribed set. -/
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    normalizedHamming (M.action (g * h)) (M.action g * M.action h) < ε
  /-- Nonidentity elements in the prescribed set stay far from the identity permutation. -/
  separated : ∀ g ∈ F, g ≠ 1 →
    1 - ε < normalizedHamming (M.action g) 1

private theorem GoodOn.mono {G : Type*} [Group G] {M : PermutationModel G}
    {F F' : Finset G} {ε : ℝ} (h : GoodOn M F' ε) (hF : F ⊆ F') :
    GoodOn M F ε where
  multiplicative g hg k hk := h.multiplicative g (hF hg) k (hF hk)
  separated g hg hne := h.separated g (hF hg) hne

/-- A group admitting arbitrarily accurate finite permutation models. -/
public
class Sofic (G : Type*) [Group G] : Prop where
  /-- Every finite set has a permutation model at every error strictly between zero and one. -/
  approximation : ∀ (F : Finset G) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ M : PermutationModel G, GoodOn M F ε

private theorem normalizedHamming_permCongr
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) (p q : Equiv.Perm X) :
    normalizedHamming (e.permCongr p) (e.permCongr q) =
      normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => e.permCongr p y) (fun y => e.permCongr q y) =
        hammingDist (fun x => p x) (fun x => q x) := by
    unfold hammingDist
    apply Finset.card_equiv e.symm
    intro y
    simp only [Equiv.permCongr_apply, ne_eq, e.injective.eq_iff, Finset.mem_filter, Finset.mem_univ,
      true_and]
  unfold normalizedHamming
  rw [hdist, ← Fintype.card_congr e]

private theorem hammingDist_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (p q : Equiv.Perm Y) :
    hammingDist
      (fun z : X × Y => ((Equiv.refl X).prodCongr p) z)
      (fun z : X × Y => ((Equiv.refl X).prodCongr q) z) =
      Fintype.card X * hammingDist (fun y => p y) (fun y => q y) := by
  classical
  change
    (Finset.univ.filter fun z : X × Y =>
      (z.1, p z.2) ≠ (z.1, q z.2)).card =
      Fintype.card X *
        (Finset.univ.filter fun y : Y => p y ≠ q y).card
  have hfilter :
      (Finset.univ.filter fun z : X × Y =>
        (z.1, p z.2) ≠ (z.1, q z.2)) =
        (Finset.univ : Finset X) ×ˢ
          (Finset.univ.filter fun y : Y => p y ≠ q y) := by
    ext z
    simp only [ne_eq, Prod.mk.injEq, true_and, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_product]
  rw [hfilter, Finset.card_product]
  rfl

private theorem normalizedHamming_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (hX : Fintype.card X ≠ 0)
    (p q : Equiv.Perm Y) :
    normalizedHamming
      ((Equiv.refl X).prodCongr p) ((Equiv.refl X).prodCongr q) =
      normalizedHamming p q := by
  unfold normalizedHamming
  rw [hammingDist_prodCongr_refl_left, Fintype.card_prod, Nat.cast_mul,
    Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast hX)

private def amplifyModel {G : Type*} [Group G]
    (M : PermutationModel G) (k : ℕ) (hk : 0 < k) : PermutationModel G where
  size := k * M.size
  size_pos := Nat.mul_pos hk M.size_pos
  action g := finProdFinEquiv.permCongr
    ((Equiv.refl (Fin k)).prodCongr (M.action g))
  map_one := by
    ext x
    simp only [Equiv.prodCongr, Equiv.coe_refl, M.map_one, Equiv.Perm.coe_one, Prod.map_id,
      Equiv.refl_symm,
      Equiv.permCongr_apply, finProdFinEquiv_symm_apply, Equiv.coe_fn_mk, id_eq,
        finProdFinEquiv_apply_val,
      Fin.coe_modNat, Fin.coe_divNat, Nat.mod_add_div]

private theorem amplifyModel_normalizedHamming
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming ((amplifyModel M k hk).action g)
        ((amplifyModel M k hk).action h) =
      normalizedHamming (M.action g) (M.action h) := by
  change normalizedHamming
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action g)))
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [normalizedHamming_permCongr]
  apply normalizedHamming_prodCongr_refl_left
  simpa only [Fintype.card_fin, ne_eq] using hk.ne'

private theorem amplifyModel_multiplicative_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming
      ((amplifyModel M k hk).action (g * h))
      ((amplifyModel M k hk).action g *
        (amplifyModel M k hk).action h) =
    normalizedHamming (M.action (g * h))
      (M.action g * M.action h) := by
  have hprod (p q : Equiv.Perm (Fin M.size)) :
      ((Equiv.refl (Fin k)).prodCongr p) *
        ((Equiv.refl (Fin k)).prodCongr q) =
      (Equiv.refl (Fin k)).prodCongr (p * q) := by
    apply Equiv.ext
    intro z
    exact Prod.ext rfl rfl
  change
    normalizedHamming
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action (g * h))))
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action g)) *
        finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [← Equiv.permCongr_mul, normalizedHamming_permCongr, hprod]
  apply normalizedHamming_prodCongr_refl_left
  simpa only [Fintype.card_fin, ne_eq] using hk.ne'

private theorem amplifyModel_separation_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g : G) :
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
      normalizedHamming (M.action g) 1 := by
  calc
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
        normalizedHamming ((amplifyModel M k hk).action g)
          ((amplifyModel M k hk).action 1) := by
            rw [PermutationModel.map_one]
    _ = normalizedHamming (M.action g) (M.action 1) :=
      amplifyModel_normalizedHamming M k hk g 1
    _ = normalizedHamming (M.action g) 1 := by rw [M.map_one]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure SoficApproximation (G : Type*) [Group G] where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  model : ℕ → PermutationModel G
  multiplicative : ∀ g h : G,
    Tendsto
      (fun n => normalizedHamming
        ((model n).action (g * h)) ((model n).action g * (model n).action h))
      atTop (𝓝 0)
  separated : ∀ g : G, g ≠ 1 →
    Tendsto
      (fun n => normalizedHamming ((model n).action g) 1)
      atTop (𝓝 1)

private def pullbackPermutationModel {G H : Type*} [Group G] [Group H]
    (f : H →* G) (M : PermutationModel G) : PermutationModel H where
  size := M.size
  size_pos := M.size_pos
  action h := M.action (f h)
  map_one := by simpa only [map_one] using M.map_one

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def pullbackSoficApproximation {G H : Type*} [Group G] [Group H]
    (f : H →* G) (hf : Function.Injective f)
    (A : SoficApproximation G) : SoficApproximation H where
  model n := pullbackPermutationModel f (A.model n)
  multiplicative g h := by
    convert A.multiplicative (f g) (f h) using 1
    funext n
    change
      normalizedHamming ((A.model n).action (f (g * h)))
        ((A.model n).action (f g) * (A.model n).action (f h)) =
      normalizedHamming ((A.model n).action (f g * f h))
        ((A.model n).action (f g) * (A.model n).action (f h))
    rw [map_mul]
  separated g hg := by
    have hfg : f g ≠ 1 := by
      intro he
      apply hg
      apply hf
      simpa only [map_one] using he
    convert A.separated (f g) hfg using 1
    funext n
    rfl

private theorem nonempty_soficApproximation_of_sofic
    (G : Type*) [Group G] [Countable G] [Sofic G] :
    Nonempty (SoficApproximation G) := by
  classical
  let K : Set.FiniteExhaustion (Set.univ : Set G) :=
    Set.countable_univ.finiteExhaustion
  let F : ℕ → Finset G := fun n => (K.finite n).toFinset
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hε_pos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hε_lt (n : ℕ) : ε n < 1 := by
    dsimp [ε]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_lt_one (by linarith : (0 : ℝ) < n + 2)]
    linarith
  have hε_lim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hmem (g : G) : ∀ᶠ n in atTop, g ∈ F n := by
    have hg : g ∈ ⋃ n, K n := by
      rw [K.iUnion_eq]
      exact Set.mem_univ g
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    filter_upwards [eventually_ge_atTop i] with n hn
    exact (K.finite n).mem_toFinset.mpr (K.mono hn hi)
  have hchoose (n : ℕ) : ∃ M : PermutationModel G, GoodOn M (F n) (ε n) :=
    Sofic.approximation (F n) (ε n) (hε_pos n) (hε_lt n)
  let M : ℕ → PermutationModel G := fun n => (hchoose n).choose
  have hgood (n : ℕ) : GoodOn (M n) (F n) (ε n) :=
    (hchoose n).choose_spec
  refine ⟨{
    model := M
    multiplicative := ?_
    separated := ?_
  }⟩
  · intro g h
    refine squeeze_zero' (Eventually.of_forall fun n =>
      normalizedHamming_nonneg _ _) ?_ hε_lim
    filter_upwards [hmem g, hmem h] with n hg hh
    exact (hgood n).multiplicative g hg h hh |>.le
  · intro g hg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using (tendsto_const_nhds.sub hε_lim))
      tendsto_const_nhds
    · filter_upwards [hmem g] with n hn
      exact ((hgood n).separated g hn hg).le
    · exact Eventually.of_forall fun n =>
        normalizedHamming_le_one _ _

private def amplifyApproximation {G : Type*} [Group G]
    (A : SoficApproximation G) : SoficApproximation G where
  model n := amplifyModel (A.model n) (n + 1) (Nat.zero_lt_succ n)
  multiplicative g h := by
    simpa only [amplifyModel_multiplicative_distance] using
      A.multiplicative g h
  separated g hg := by
    simpa only [amplifyModel_separation_distance] using
      A.separated g hg

private theorem amplifyApproximation_size_tendsto
    {G : Type*} [Group G] (A : SoficApproximation G) :
    Tendsto (fun n => (amplifyApproximation A).model n |>.size)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n + 1)
    (g := fun n => (amplifyApproximation A).model n |>.size)
  · intro n
    change n + 1 ≤ (n + 1) * (A.model n).size
    exact Nat.le_mul_of_pos_right _ (A.model n).size_pos
  · exact tendsto_add_atTop_nat 1

public
theorem exists_soficApproximation_size_tendsto
    (G : Type*) [Group G] [Countable G] [Sofic G] :
    ∃ A : SoficApproximation G,
      Tendsto (fun n => (A.model n).size) atTop atTop := by
  obtain ⟨A⟩ := nonempty_soficApproximation_of_sofic G
  exact ⟨amplifyApproximation A, amplifyApproximation_size_tendsto A⟩

public
theorem sofic_of_injective {G H : Type*} [Group G] [Group H]
    [Sofic G] (f : H →* G) (hf : Function.Injective f) : Sofic H := by
  classical
  constructor
  intro F ε hε hε'
  obtain ⟨M, hM⟩ := Sofic.approximation (F.image f) ε hε hε'
  let N : PermutationModel H :=
    { size := M.size
      size_pos := M.size_pos
      action := fun g => M.action (f g)
      map_one := by simpa only [map_one] using M.map_one }
  refine ⟨N, ?_⟩
  constructor
  · intro g hg h hh
    simpa [N] using hM.multiplicative
      (f g) (Finset.mem_image_of_mem f hg)
      (f h) (Finset.mem_image_of_mem f hh)
  · intro g hg hne
    apply hM.separated (f g) (Finset.mem_image_of_mem f hg)
    intro he
    apply hne
    apply hf
    simpa only [map_one] using he

private theorem exists_finite_obstruction {G : Type*} [Group G] (hG : ¬ Sofic G) :
    ∃ (F : Finset G) (ε : ℝ), 1 ∈ F ∧ 0 < ε ∧ ε < 1 ∧
      ∀ M : PermutationModel G, ¬ GoodOn M F ε := by
  classical
  have hex : ∃ (F : Finset G) (ε : ℝ), 0 < ε ∧ ε < 1 ∧
      ∀ M : PermutationModel G, ¬ GoodOn M F ε := by
    by_contra h
    apply hG
    constructor
    intro F ε hε hε'
    by_contra hmodel
    apply h
    exact ⟨F, ε, hε, hε', fun M hM => hmodel ⟨M, hM⟩⟩
  obtain ⟨F, ε, hε, hε', hF⟩ := hex
  refine ⟨insert 1 F, ε, Finset.mem_insert_self _ _, hε, hε', ?_⟩
  intro M hM
  exact hF M (hM.mono (Finset.subset_insert _ _))

private noncomputable def multiplicationTable {G : Type*} [Group G]
    (F : Finset G) : Finset G := by
  classical
  exact F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)

private theorem mem_multiplicationTable_of_mem {G : Type*} [Group G]
    {F : Finset G} {g : G} (hg : g ∈ F) : g ∈ multiplicationTable F := by
  classical
  simp only [multiplicationTable, Finset.product_eq_sprod, Finset.mem_union, hg, Finset.mem_image,
    Finset.mem_product, Prod.exists, true_or]

private theorem mul_mem_multiplicationTable {G : Type*} [Group G]
    {F : Finset G} {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    g * h ∈ multiplicationTable F := by
  classical
  change g * h ∈ F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩

private noncomputable def tableRelators {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Finset (FreeGroup ↥(multiplicationTable F)) := by
  classical
  let oneGenerator : ↥(multiplicationTable F) :=
    ⟨1, mem_multiplicationTable_of_mem h₁⟩
  let word (x : ↥F × ↥F) : FreeGroup ↥(multiplicationTable F) :=
    FreeGroup.of ⟨x.1.1, mem_multiplicationTable_of_mem x.1.2⟩ *
      FreeGroup.of ⟨x.2.1, mem_multiplicationTable_of_mem x.2.2⟩ *
      (FreeGroup.of
        ⟨x.1.1 * x.2.1, mul_mem_multiplicationTable x.1.2 x.2.2⟩)⁻¹
  exact {FreeGroup.of oneGenerator} ∪ (F.attach.product F.attach).image word

private abbrev tableGroup {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Type _ :=
  PresentedGroup (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F)))

private noncomputable def tableGenerator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableGroup F h₁ :=
  PresentedGroup.of g

private theorem tableGenerator_one {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    tableGenerator F h₁ ⟨1, mem_multiplicationTable_of_mem h₁⟩ = 1 := by
  classical
  change PresentedGroup.mk _ (FreeGroup.of _) = 1
  apply PresentedGroup.one_of_mem
  change FreeGroup.of _ ∈ tableRelators F h₁
  simp only [tableRelators, Finset.product_eq_sprod, Finset.singleton_union, Finset.mem_insert,
    Finset.mem_image, Finset.mem_product, Finset.mem_attach, and_self, true_and, Prod.exists,
      Subtype.exists, true_or]

private theorem tableGenerator_mul {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ *
      tableGenerator F h₁ ⟨h, mem_multiplicationTable_of_mem hh⟩ =
    tableGenerator F h₁ ⟨g * h, mul_mem_multiplicationTable hg hh⟩ := by
  classical
  have hrel :
      (FreeGroup.of ⟨g, mem_multiplicationTable_of_mem hg⟩ *
        FreeGroup.of ⟨h, mem_multiplicationTable_of_mem hh⟩) *
          (FreeGroup.of ⟨g * h, mul_mem_multiplicationTable hg hh⟩)⁻¹ ∈
        (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F))) := by
    change _ ∈ tableRelators F h₁
    rw [tableRelators]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(⟨g, hg⟩, ⟨h, hh⟩), ?_, rfl⟩
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_attach, and_self]
  simpa only [tableGenerator, PresentedGroup.of, map_mul] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem hrel

private noncomputable def tableEvaluation {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : tableGroup F h₁ →* G := by
  classical
  apply PresentedGroup.toGroup (f := fun g : ↥(multiplicationTable F) => g.1)
  intro r hr
  change r ∈ tableRelators F h₁ at hr
  simp only [tableRelators, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image] at hr
  rcases hr with rfl | ⟨⟨g, h⟩, _, rfl⟩
  · simp only [FreeGroup.lift_apply_of]
  · simp only [map_mul, FreeGroup.lift_apply_of, map_inv, mul_inv_rev, mul_mul_inv_mul_cancel,
    mul_inv_cancel]

@[simp]
private theorem tableEvaluation_generator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableEvaluation F h₁ (tableGenerator F h₁ g) = g.1 := by
  change PresentedGroup.toGroup _ (PresentedGroup.of g) = g.1
  exact PresentedGroup.toGroup.of _

private theorem tableGenerator_ne_one {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {g : G} (hg : g ∈ F) (hne : g ≠ 1) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ ≠ 1 := by
  intro h
  apply hne
  simpa only [tableEvaluation_generator, map_one] using congrArg (tableEvaluation F h₁) h

private theorem tableGroup_finitelyPresented {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Group.IsFinitelyPresented (tableGroup F h₁) :=
  inferInstance

private noncomputable def tableTestSet {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Finset (tableGroup F h₁) := by
  classical
  exact F.attach.image fun g =>
    tableGenerator F h₁ ⟨g.1, mem_multiplicationTable_of_mem g.2⟩

private theorem tableGenerator_mem_tableTestSet {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {g : G} (hg : g ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ ∈
      tableTestSet F h₁ := by
  classical
  change _ ∈ F.attach.image _
  exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩

private noncomputable def pullbackTableModel {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁)) : PermutationModel G := by
  classical
  refine
    { size := M.size
      size_pos := M.size_pos
      action := fun g => if hg : g ∈ multiplicationTable F then
        M.action (tableGenerator F h₁ ⟨g, hg⟩) else 1
      map_one := ?_ }
  simp only [mem_multiplicationTable_of_mem h₁, ↓reduceDIte, tableGenerator_one F h₁, M.map_one]

private theorem pullbackTableModel_action_of_mem {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁))
    {g : G} (hg : g ∈ multiplicationTable F) :
    (pullbackTableModel F h₁ M).action g =
      M.action (tableGenerator F h₁ ⟨g, hg⟩) := by
  classical
  simp only [pullbackTableModel, dite_eq_left hg]

private theorem goodOn_pullbackTableModel {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (M : PermutationModel (tableGroup F h₁))
    (hM : GoodOn M (tableTestSet F h₁) ε) :
    GoodOn (pullbackTableModel F h₁ M) F ε := by
  constructor
  · intro g hg h hh
    have htest := hM.multiplicative
      (tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩)
      (tableGenerator_mem_tableTestSet F h₁ hg)
      (tableGenerator F h₁ ⟨h, mem_multiplicationTable_of_mem hh⟩)
      (tableGenerator_mem_tableTestSet F h₁ hh)
    change normalizedHamming
      ((pullbackTableModel F h₁ M).action (g * h))
      ((pullbackTableModel F h₁ M).action g *
        (pullbackTableModel F h₁ M).action h) < ε
    rw [pullbackTableModel_action_of_mem F h₁ M
      (mul_mem_multiplicationTable hg hh),
      pullbackTableModel_action_of_mem F h₁ M
        (mem_multiplicationTable_of_mem hg),
      pullbackTableModel_action_of_mem F h₁ M
        (mem_multiplicationTable_of_mem hh),
      ← tableGenerator_mul F h₁ hg hh]
    exact htest
  · intro g hg hne
    have htest := hM.separated
      (tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩)
      (tableGenerator_mem_tableTestSet F h₁ hg)
      (tableGenerator_ne_one F h₁ hg hne)
    change 1 - ε < normalizedHamming
      ((pullbackTableModel F h₁ M).action g) 1
    rw [pullbackTableModel_action_of_mem F h₁ M
      (mem_multiplicationTable_of_mem hg)]
    exact htest

private theorem tableGroup_not_sofic_of_obstruction {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hbad : ∀ M : PermutationModel G, ¬ GoodOn M F ε) :
    ¬ Sofic (tableGroup F h₁) := by
  intro hsofic
  obtain ⟨M, hM⟩ := hsofic.approximation (tableTestSet F h₁) ε hε hε'
  exact hbad (pullbackTableModel F h₁ M)
    (goodOn_pullbackTableModel F h₁ M hM)

private theorem exists_nonsofic_finite_table {G : Type u} [Group G]
    (hG : ¬ Sofic G) :
    ∃ (F : Finset G) (h₁ : 1 ∈ F),
      Group.IsFinitelyPresented (tableGroup F h₁) ∧
        ¬ Sofic (tableGroup F h₁) := by
  obtain ⟨F, ε, h₁, hε, hε', hbad⟩ := exists_finite_obstruction hG
  exact ⟨F, h₁, tableGroup_finitelyPresented F h₁,
    tableGroup_not_sofic_of_obstruction F h₁ ε hε hε' hbad⟩

public
theorem exists_finitelyPresented_not_sofic_of_not_sofic
    {G : Type u} [Group G] (hG : ¬ Sofic G) :
    ∃ (H : Type u) (_ : Group H),
      Group.IsFinitelyPresented H ∧ ¬ Sofic H := by
  obtain ⟨F, h₁, hfp, hn⟩ := exists_nonsofic_finite_table hG
  exact ⟨tableGroup F h₁, inferInstance, hfp, hn⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure LocalMultiplicativeOn {G : Type u} {H : Type v}
    [Group G] [Group H] (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y

/-- Internal interface connecting the split non-sofic proof modules. -/
public
class LEF (G : Type u) [Group G] : Prop where
  approximate : ∀ s : Finset G, ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set G) ∧ LocalMultiplicativeOn s f

namespace LocalMultiplicativeOn

variable {G : Type u} {H : Type v} [Group G] [Group H]

public
theorem mono {s t : Finset G} {f : G → H}
    (h : LocalMultiplicativeOn t f) (hst : s ⊆ t) : LocalMultiplicativeOn s f where
  map_one := h.map_one
  map_mul x hx y hy := h.map_mul x (hst hx) y (hst hy)

private theorem map_inv_of_mem {s : Finset G} {f : G → H}
    (h : LocalMultiplicativeOn s f) {x : G} (hx : x ∈ s) (hi : x⁻¹ ∈ s) :
    f x⁻¹ = (f x)⁻¹ := by
  have hm := h.map_mul x hx x⁻¹ hi
  rw [mul_inv_cancel, h.map_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

end LocalMultiplicativeOn

public
theorem exists_local_word_control {α : Type u} {G : Type v} [Group G]
    (φ : FreeGroup α →* G) (z : FreeGroup α) :
    ∃ s : Finset G, ∀ (H : Type w) [Group H] (f : G → H),
      LocalMultiplicativeOn s f →
        FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) z = f (φ z) := by
  classical
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · refine ⟨∅, ?_⟩
    intro H _ f hf
    simp only [map_one, hf.map_one]
  · intro a
    refine ⟨∅, ?_⟩
    intro H _ f _
    simp only [FreeGroup.lift_apply_of]
  · intro a _
    refine ⟨{φ (FreeGroup.of a), (φ (FreeGroup.of a))⁻¹}, ?_⟩
    intro H _ f hf
    simp only [map_inv, FreeGroup.lift_apply_of]
    exact (hf.map_inv_of_mem (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or]) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).symm
  · intro x y hx hy
    obtain ⟨sx, hx⟩ := hx
    obtain ⟨sy, hy⟩ := hy
    refine ⟨insert (φ x) (insert (φ y) (sx ∪ sy)), ?_⟩
    intro H _ f hf
    have hsx : sx ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_union, ha, true_or, or_true]
    have hsy : sy ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_union, ha, or_true]
    calc
      FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) (x * y) =
          FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) x *
            FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) y := map_mul _ _ _
      _ = f (φ x) * f (φ y) :=
        congrArg₂ (· * ·) (hx H f (hf.mono hsx)) (hy H f (hf.mono hsy))
      _ = f (φ x * φ y) :=
        (hf.map_mul (φ x) (by simp only [Finset.mem_insert, Finset.mem_union, true_or]) (φ y) (by
          simp only [Finset.mem_insert, Finset.mem_union, true_or, or_true])).symm
      _ = f (φ (x * y)) := by rw [map_mul]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def boundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) : ℕ :=
  ∑ i : ι, (A.filter fun x => σ i x ∉ A).card

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def agreementSet {V : Type*} [Fintype V] [DecidableEq V]
    (c c' : Equiv.Perm V) : Finset V :=
  Finset.univ.filter (fun x => c x = c' x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationCommutationDefect {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) : ℕ :=
  ∑ i : ι, (Finset.univ.filter fun x => c (σ i x) ≠ σ i (c x)).card

public
theorem agreementSet_card_add_hammingDist {V : Type*}
    [Fintype V] [DecidableEq V] (c c' : Equiv.Perm V) :
    (agreementSet c c').card +
      hammingDist (fun x => c x) (fun x => c' x) = Fintype.card V := by
  simpa only [agreementSet, hammingDist, ne_eq, Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun x => c x = c' x))

private theorem boundary_agreementSet_le_commutationDefect {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c c' : Equiv.Perm V) :
    boundary σ (agreementSet c c') ≤
      permutationCommutationDefect σ c +
        permutationCommutationDefect σ c' := by
  classical
  unfold boundary permutationCommutationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let B : Finset V :=
    Finset.univ.filter fun x => c (σ i x) ≠ σ i (c x)
  let B' : Finset V :=
    Finset.univ.filter fun x => c' (σ i x) ≠ σ i (c' x)
  have hsub :
      (agreementSet c c').filter (fun x => σ i x ∉ agreementSet c c') ⊆
        B ∪ B' := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hagree : c x = c' x :=
      (Finset.mem_filter.mp hx'.1).2
    have hdisagree : c (σ i x) ≠ c' (σ i x) := by
      intro heq
      exact hx'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    by_cases hc : c (σ i x) = σ i (c x)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hc'
      apply hdisagree
      calc
        c (σ i x) = σ i (c x) := hc
        _ = σ i (c' x) := congrArg (σ i) hagree
        _ = c' (σ i x) := hc'.symm
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le B B')

private theorem hamming_dichotomy_of_expansion {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
        (boundary σ A : ℝ))
    (c c' : Equiv.Perm V) :
    h * (hammingDist (fun x => c x) (fun x => c' x) : ℝ) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) ∨
      h * ((Fintype.card V : ℝ) -
          hammingDist (fun x => c x) (fun x => c' x)) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) := by
  have hcard := agreementSet_card_add_hammingDist c c'
  have hcard' :
      ((agreementSet c c').card : ℝ) +
        (hammingDist (fun x => c x) (fun x => c' x) : ℝ) =
          Fintype.card V := by
    exact_mod_cast hcard
  have hboundary := boundary_agreementSet_le_commutationDefect σ c c'
  have hboundary' :
      (boundary σ (agreementSet c c') : ℝ) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) := by
    exact_mod_cast hboundary
  have hcut := (hexp (agreementSet c c')).trans hboundary'
  by_cases hhalf :
      ((agreementSet c c').card : ℝ) ≤
        (Fintype.card V : ℝ) - (agreementSet c c').card
  · right
    rw [min_eq_left hhalf] at hcut
    have hident :
        (Fintype.card V : ℝ) -
          hammingDist (fun x => c x) (fun x => c' x) =
            (agreementSet c c').card := by
      linarith [hcard']
    simpa only [hident, Nat.cast_add, ge_iff_le] using hcut
  · left
    rw [min_eq_right (le_of_not_ge hhalf)] at hcut
    have hident :
        (Fintype.card V : ℝ) - (agreementSet c c').card =
          hammingDist (fun x => c x) (fun x => c' x) := by
      linarith [hcard']
    simpa only [Nat.cast_add, ge_iff_le, hident] using hcut

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def inducedBoundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) : ℕ :=
  ∑ i : ι, (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card

private theorem boundary_union_le {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) :
    boundary σ (B ∪ E) ≤ boundary σ B + inducedBoundary σ B E := by
  classical
  unfold boundary inducedBoundary
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union] at hx ⊢
  rcases hx with ⟨hxB | hxE, hout⟩
  · exact Or.inl ⟨hxB, fun h => hout (Or.inl h)⟩
  · exact Or.inr
      ⟨hxE, fun h => hout (Or.inl h), fun h => hout (Or.inr h)⟩

private theorem boundary_le_induced_add_deleted {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) :
    boundary σ E ≤ inducedBoundary σ B E + Fintype.card ι * B.card := by
  classical
  unfold boundary inducedBoundary
  calc
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card)
        ≤ ∑ i : ι,
          ((E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card + B.card) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hpre : (E.filter fun x => σ i x ∈ B).card ≤ B.card := by
              rw [← Finset.card_map (σ i).toEmbedding]
              apply Finset.card_le_card
              intro y hy
              obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
              exact (Finset.mem_filter.mp hx).2
            have hsub :
                (E.filter fun x => σ i x ∉ E) ⊆
                  (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E) ∪
                    (E.filter fun x => σ i x ∈ B) := by
              intro x hx
              obtain ⟨hxE, hout⟩ := Finset.mem_filter.mp hx
              by_cases hB : σ i x ∈ B
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxE, hB⟩)
              · exact Finset.mem_union_left _
                  (Finset.mem_filter.mpr ⟨hxE, hB, hout⟩)
            exact (Finset.card_le_card hsub).trans
              ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hpre _))
    _ = (∑ i : ι, (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card) +
        Fintype.card ι * B.card := by simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ,
                                        smul_eq_mul]

private theorem maximal_bad_cut_induced_lower {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) (ell : ℝ)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hdisj : Disjoint B E) (hne : E.Nonempty)
    (hhalf : 2 * (B ∪ E).card ≤ Fintype.card V) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  by_contra h
  have hE : (inducedBoundary σ B E : ℝ) < ell * (E.card : ℝ) :=
    lt_of_not_ge h
  have hcut : (boundary σ (B ∪ E) : ℝ) ≤
      (boundary σ B : ℝ) + (inducedBoundary σ B E : ℝ) := by
    exact_mod_cast boundary_union_le σ B E
  have hcard : ((B ∪ E).card : ℝ) = (B.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  have hbad : (boundary σ (B ∪ E) : ℝ) < ell * ((B ∪ E).card : ℝ) := by
    rw [hcard]
    nlinarith
  have hsize := hmax (B ∪ E) hhalf hbad
  have hepos : 0 < E.card := Finset.card_pos.mpr hne
  have hnat := Finset.card_union_of_disjoint hdisj
  omega

private theorem bad_cut_card_bound {γ ell a : ℝ} {N b q : ℕ}
    (hgap : ell < γ)
    (hadd : γ * (b : ℝ) - a * (N : ℝ) ≤ (q : ℝ))
    (hbad : (q : ℝ) ≤ ell * (b : ℝ)) :
    (b : ℝ) ≤ a * (N : ℝ) / (γ - ell) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  nlinarith

private theorem large_cut_lower {γ ell a d N b e q : ℝ}
    (hgap : ell < γ) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hdeleted : (γ - ell) * b ≤ a * N)
    (hsmall : 2 * a * (2 * (γ - ell) + d) ≤ (γ - ell) ^ 2)
    (hlarge : N / 2 - b < e)
    (hcut : γ * e - a * N - d * b ≤ q) :
    ell * e ≤ q := by
  have hδ : 0 < γ - ell := sub_pos.mpr hgap
  have hδd : 0 ≤ (γ - ell) + d := by linarith
  have hscaledDeleted := mul_le_mul_of_nonneg_left hdeleted hδd
  have hscaledSmall := mul_le_mul_of_nonneg_right hsmall hN
  have hscaledLarge := mul_lt_mul_of_pos_left hlarge hδ
  nlinarith

private theorem prune_permutation_multigraph {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ) (B : Finset V)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ) ((Fintype.card V : ℝ) - (A.card : ℝ)) -
          a * (Fintype.card V : ℝ) ≤ (boundary σ A : ℝ))
    (hBhalf : 2 * B.card ≤ Fintype.card V)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤ (γ - ell) ^ 2)
    (E : Finset V) (hdisj : Disjoint B E)
    (hEhalf : 2 * E.card ≤ Fintype.card V - B.card) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, CharP.cast_eq_zero, mul_zero, inducedBoundary,
    Finset.notMem_empty,
      not_false_eq_true, and_true, Finset.filter_empty, Finset.sum_const_zero, Std.le_refl]
  by_cases hunion : 2 * (B ∪ E).card ≤ Fintype.card V
  · exact maximal_bad_cut_induced_lower σ B E ell hB hmax hdisj hne hunion
  have hBhalfReal :
      (B.card : ℝ) ≤ (Fintype.card V : ℝ) - (B.card : ℝ) := by
    have hcast : 2 * (B.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hBhalf
    linarith
  have haddB := hadd B
  rw [min_eq_left hBhalfReal] at haddB
  have hdeleted :
      (γ - ell) * (B.card : ℝ) ≤ a * (Fintype.card V : ℝ) := by
    linarith
  have hEhalfNat : 2 * E.card ≤ Fintype.card V :=
    hEhalf.trans (Nat.sub_le _ _)
  have hEhalfReal :
      (E.card : ℝ) ≤ (Fintype.card V : ℝ) - (E.card : ℝ) := by
    have hcast : 2 * (E.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hEhalfNat
    linarith
  have haddE := hadd E
  rw [min_eq_left hEhalfReal] at haddE
  have hremoval :
      (boundary σ E : ℝ) ≤ (inducedBoundary σ B E : ℝ) +
        (Fintype.card ι : ℝ) * (B.card : ℝ) := by
    exact_mod_cast boundary_le_induced_add_deleted σ B E
  have hcut :
      γ * (E.card : ℝ) - a * (Fintype.card V : ℝ) -
        (Fintype.card ι : ℝ) * (B.card : ℝ) ≤
        (inducedBoundary σ B E : ℝ) := by
    linarith
  have hcard := Finset.card_union_of_disjoint hdisj
  have hlargeNat : Fintype.card V < 2 * (B.card + E.card) := by
    simpa only [hcard] using Nat.lt_of_not_ge hunion
  have hlargeCast :
      (Fintype.card V : ℝ) < 2 * ((B.card : ℝ) + (E.card : ℝ)) := by
    exact_mod_cast hlargeNat
  have hlarge :
      (Fintype.card V : ℝ) / 2 - (B.card : ℝ) < (E.card : ℝ) := by
    linarith
  exact large_cut_lower hgap (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hdeleted hsmall hlarge hcut

private theorem exists_maximal_bad_cut {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (ell : ℝ) :
    ∃ B : Finset V,
      2 * B.card ≤ Fintype.card V ∧
      (boundary σ B : ℝ) ≤ ell * (B.card : ℝ) ∧
      ∀ A : Finset V,
        2 * A.card ≤ Fintype.card V →
        (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.powerset.filter fun A =>
      2 * A.card ≤ Fintype.card V ∧
        (boundary σ A : ℝ) < ell * (A.card : ℝ)
  by_cases hnonempty : candidates.Nonempty
  · obtain ⟨B, hBmem, hmax⟩ :=
      Finset.exists_max_image candidates Finset.card hnonempty
    have hprops :
        2 * B.card ≤ Fintype.card V ∧
          (boundary σ B : ℝ) < ell * (B.card : ℝ) := by
      have hmem : B ∈ Finset.univ.powerset.filter fun A =>
          2 * A.card ≤ Fintype.card V ∧
            (boundary σ A : ℝ) < ell * (A.card : ℝ) := by
        simpa only [candidates] using hBmem
      exact (Finset.mem_filter.mp hmem).2
    refine ⟨B, hprops.1, hprops.2.le, ?_⟩
    intro A hhalf hbad
    apply hmax A
    simp only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, hhalf, hbad, and_self,
      candidates]
  · refine ⟨∅, by simp only [Finset.card_empty, mul_zero, zero_le], by simp only [boundary,
    Finset.notMem_empty, not_false_eq_true, Finset.filter_empty, Finset.card_empty,
                             Finset.sum_const_zero, CharP.cast_eq_zero, mul_zero, Std.le_refl], ?_⟩
    intro A hhalf hbad
    exfalso
    apply hnonempty
    refine ⟨A, ?_⟩
    simp only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, hhalf, hbad, and_self,
      candidates]

public
theorem exists_pruned_expander {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ) ((Fintype.card V : ℝ) - (A.card : ℝ)) -
          a * (Fintype.card V : ℝ) ≤ (boundary σ A : ℝ))
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤ (γ - ell) ^ 2) :
    ∃ B : Finset V,
      2 * B.card ≤ Fintype.card V ∧
      (B.card : ℝ) ≤ a * (Fintype.card V : ℝ) / (γ - ell) ∧
      ∀ E : Finset V, Disjoint B E →
        2 * E.card ≤ Fintype.card V - B.card →
        ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  obtain ⟨B, hhalf, hB, hmax⟩ := exists_maximal_bad_cut σ ell
  refine ⟨B, hhalf, ?_, ?_⟩
  · have hhalfReal :
        (B.card : ℝ) ≤ (Fintype.card V : ℝ) - (B.card : ℝ) := by
      have hcast : 2 * (B.card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast hhalf
      linarith
    have hlow := hadd B
    rw [min_eq_left hhalfReal] at hlow
    exact bad_cut_card_bound hgap hlow hB
  · intro E hdisj hEhalf
    exact prune_permutation_multigraph σ γ ell a B hgap hadd hhalf hB
      hmax hsmall E hdisj hEhalf

private theorem disjoint_dominant_intersections_false {V : Type*} [DecidableEq V]
    (P Q D : Finset V) (hdisj : Disjoint P Q)
    (hP : D.card < 2 * (P ∩ D).card)
    (hQ : D.card < 2 * (Q ∩ D).card) : False := by
  have hparts : Disjoint (P ∩ D) (Q ∩ D) := by
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left) hdisj)
  have hsub : (P ∩ D) ∪ (Q ∩ D) ⊆ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hparts] at hcard
  omega

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRetainedSupport {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) : Finset V :=
  R.biUnion id

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedCore {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) : Finset V :=
  R.biUnion fun C => C ∩ D C

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def partitionWordCrossing {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∉ P.part x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedWordPreimageBad {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ matchedCore R D)

public
theorem finpartition_dominant_matching_injOn
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hmajor : ∀ C ∈ R, (D C).card < 2 * (C ∩ D C).card) :
    Set.InjOn D (R : Set (Finset V)) := by
  intro C hC E hE heq
  have hCR : C ∈ R := hC
  have hER : E ∈ R := hE
  by_contra hne
  exact disjoint_dominant_intersections_false C E (D C)
    (P.disjoint (hR hCR) (hR hER) hne)
    (hmajor C hCR)
    (by simpa only [heq] using hmajor E hER)

public
theorem matchedRetainedSupport_subset
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) :
    matchedRetainedSupport R ⊆ U := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact P.subset (hR hC) (by simpa only [id_eq] using hxC)

private theorem matchedCore_subset_retainedSupport
    {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) :
    matchedCore R D ⊆ matchedRetainedSupport R := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr
    ⟨C, hC, by simpa only [id_eq] using (Finset.mem_inter.mp hxC).1⟩

private theorem matchedCore_subset
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    matchedCore R D ⊆ U :=
  (matchedCore_subset_retainedSupport R D).trans
    (matchedRetainedSupport_subset P R hR)

public
theorem matchedRetainedSupport_card
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) :
    (matchedRetainedSupport R).card = ∑ C ∈ R, C.card := by
  unfold matchedRetainedSupport
  apply Finset.card_biUnion
  intro C hC E hE hne
  exact P.disjoint (hR hC) (hR hE) hne

private theorem matchedCore_card
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    (matchedCore R D).card = ∑ C ∈ R, (C ∩ D C).card := by
  unfold matchedCore
  apply Finset.card_biUnion
  intro C hC E hE hne
  exact (P.disjoint (hR hC) (hR hE) hne).mono
    Finset.inter_subset_left Finset.inter_subset_left

public
theorem matchedCore_missing_card
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    (U \ matchedCore R D).card =
      (U \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C \ D C).card := by
  have hcore := Finset.card_sdiff_add_card_eq_card
    (matchedCore_subset P R hR D)
  have hret := Finset.card_sdiff_add_card_eq_card
    (matchedRetainedSupport_subset P R hR)
  have hsplit :
      (∑ C ∈ R, (C \ D C).card) + (matchedCore R D).card =
        (matchedRetainedSupport R).card := by
    rw [matchedCore_card P R hR D, matchedRetainedSupport_card P R hR]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ =>
      Finset.card_sdiff_add_card_inter C (D C)
  omega

private theorem matchedCore_missing_card_le_symmDiff
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    (U \ matchedCore R D).card ≤
      (U \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C ∆ D C).card := by
  rw [matchedCore_missing_card P R hR D]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum fun C _ =>
      Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := C) (t := D C))) _

private theorem matched_partition_part_eq_of_target_part_eq
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    {x y : V} (hx : x ∈ matchedCore R D)
    (hy : y ∈ matchedCore R D)
    (hpart : Q.part x = Q.part y) :
    P.part x = P.part y := by
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨E, hE, hyE⟩ := Finset.mem_biUnion.mp hy
  have hxparts := Finset.mem_inter.mp hxC
  have hyparts := Finset.mem_inter.mp hyE
  have hQx : Q.part x = D C :=
    Q.part_eq_of_mem (hD C hC) hxparts.2
  have hQy : Q.part y = D E :=
    Q.part_eq_of_mem (hD E hE) hyparts.2
  have hCE : C = E := hinj hC hE (hQx.symm.trans (hpart.trans hQy))
  calc
    P.part x = C := P.part_eq_of_mem (hR hC) hxparts.1
    _ = E := hCE
    _ = P.part y := (P.part_eq_of_mem (hR hE) hyparts.1).symm

public
theorem matchedWordPreimageBad_card_le
    {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) :
    (matchedWordPreimageBad U R D w).card ≤
      (U \ matchedCore R D).card := by
  apply Finset.card_le_card_of_injOn w
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact w.injective hxy

private theorem partitionWordCrossing_subset_target_or_unmatched
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (w : Equiv.Perm V) :
    partitionWordCrossing P w ⊆
      partitionWordCrossing Q w ∪
        (U \ matchedCore R D) ∪ matchedWordPreimageBad U R D w := by
  intro x hx
  obtain ⟨hxU, hxP⟩ := Finset.mem_filter.mp hx
  by_cases hxcore : x ∈ matchedCore R D
  · by_cases hxQ : w x ∈ Q.part x
    · have hwU : w x ∈ U := Q.part_subset x hxQ
      by_cases hwcore : w x ∈ matchedCore R D
      · have hQpart : Q.part x = Q.part (w x) :=
          (Q.part_eq_of_mem (Q.part_mem.mpr hxU) hxQ).symm
        have hPpart := matched_partition_part_eq_of_target_part_eq
          P Q R hR D hD hinj hxcore hwcore hQpart
        exfalso
        apply hxP
        rw [hPpart]
        exact P.mem_part hwU
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hxU, Finset.mem_sdiff.mpr ⟨hwU, hwcore⟩⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxU, hxQ⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxU, hxcore⟩))

private theorem partitionWordCrossing_card_le_target_add_unmatched
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (w : Equiv.Perm V) :
    (partitionWordCrossing P w).card ≤
      (partitionWordCrossing Q w).card +
        2 * (U \ matchedCore R D).card := by
  have hsub := Finset.card_le_card
    (partitionWordCrossing_subset_target_or_unmatched
      P Q R hR D hD hinj w)
  have hfirst := Finset.card_union_le
    (partitionWordCrossing Q w) (U \ matchedCore R D)
  have hsecond := Finset.card_union_le
    (partitionWordCrossing Q w ∪ (U \ matchedCore R D))
    (matchedWordPreimageBad U R D w)
  have hpre := matchedWordPreimageBad_card_le U R D w
  omega

private theorem matchedCore_missing_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => (((U n \ matchedCore (R n) (D n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n =>
        ((U n \ matchedRetainedSupport (R n)).card : ℝ) / (U n).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hdiscard.add hsymm
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((U n \ matchedCore (R n) (D n)).card : ℝ) ≤
        (U n \ matchedRetainedSupport (R n)).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) := by
    exact_mod_cast matchedCore_missing_card_le_symmDiff
      (P n) (R n) (hR n) (D n)
  calc
    ((U n \ matchedCore (R n) (D n)).card : ℝ) / (U n).card ≤
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ)) / (U n).card :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((U n \ matchedRetainedSupport (R n)).card : ℝ) / (U n).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card := by
      ring

private theorem permutation_increment_sum_eq_zero
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ) :
    ∑ x, (f (p x) - f x) = 0 := by
  rw [Finset.sum_sub_distrib, Equiv.sum_comp p f]
  exact sub_self _

private theorem permutation_squared_increment_le_twice_decreasing
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    ∑ x, (f (p x) - f x) ^ 2 ≤
      2 * ((Finset.univ.filter fun x => f (p x) < f x).card : ℝ) := by
  classical
  let d : α → ℝ := fun x => f (p x) - f x
  let B : Finset α := Finset.univ.filter fun x => d x < 0
  let C : Finset α := Finset.univ.filter fun x => ¬ d x < 0
  have hsum : ∑ x, d x = 0 :=
    permutation_increment_sum_eq_zero p f
  have hlower (x : α) : -1 ≤ d x := by
    dsimp [d]
    linarith [hf_nonneg (p x), hf_le_one x]
  have hupper (x : α) : d x ≤ 1 := by
    dsimp [d]
    linarith [hf_le_one (p x), hf_nonneg x]
  have hsplit : B.sum d + C.sum d = 0 := by
    calc
      B.sum d + C.sum d = ∑ x, d x := by
        simpa only [not_lt, B, C] using Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : α
          => d x < 0) d
      _ = 0 := hsum
  have habs_bad : B.sum (fun x => |d x|) = -(B.sum d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hneg : d x < 0 := (Finset.mem_filter.mp hx).2
    exact abs_of_neg hneg
  have habs_good : C.sum (fun x => |d x|) = C.sum d := by
    apply Finset.sum_congr rfl
    intro x hx
    have hnonneg : 0 ≤ d x :=
      le_of_not_gt (Finset.mem_filter.mp hx).2
    exact abs_of_nonneg hnonneg
  have habs_split :
      B.sum (fun x => |d x|) + C.sum (fun x => |d x|) =
        ∑ x, |d x| := by
    simpa [B, C] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : α => d x < 0) (fun x => |d x|)
  have habs_total : (∑ x, |d x|) = -2 * B.sum d := by
    rw [← habs_split, habs_bad, habs_good]
    linarith
  have hbad : -(B.sum d) ≤ (B.card : ℝ) := by
    calc
      -(B.sum d) = B.sum (fun x => -d x) := by
        simp only [Finset.sum_neg_distrib]
      _ ≤ B.sum (fun _ => (1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro x _
        linarith [hlower x]
      _ = (B.card : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsquare : (∑ x, d x ^ 2) ≤ ∑ x, |d x| := by
    apply Finset.sum_le_sum
    intro x _
    by_cases h : 0 ≤ d x
    · rw [abs_of_nonneg h]
      nlinarith [hupper x]
    · have hneg : d x < 0 := lt_of_not_ge h
      rw [abs_of_neg hneg]
      nlinarith [hlower x]
  rw [habs_total] at hsquare
  have hfinal : (∑ x, d x ^ 2) ≤ 2 * (B.card : ℝ) := by
    linarith
  simpa [d, B, sub_neg] using hfinal

public
theorem exists_completion_of_internal_permutation {V : Type*}
    [Finite V]
    (p : Equiv.Perm V) (Z : Finset V) :
    ∃ q : Equiv.Perm {x : V // x ∈ Z},
      ∀ (x : V) (hx : x ∈ Z) (_hp : p x ∈ Z),
        (q ⟨x, hx⟩ : V) = p x := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let A := {x : V // x ∈ Z ∧ p x ∈ Z}
  let f : A → {x : V // x ∈ Z} := fun x => ⟨x.1, x.2.1⟩
  let g : A → {x : V // x ∈ Z} := fun x => ⟨p x.1, x.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact p.injective
      (congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h)
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨q, ?_⟩
  intro x hx hp
  have h := hq (⟨x, hx, hp⟩ : A)
  exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h

private def diagonalRadius (e : ℕ → ℕ → ℝ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => e n k < 1 / ((k : ℝ) + 1)) n

private theorem diagonalRadius_tendsto_atTop (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (diagonalRadius e) atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro k
  have htol : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by
    positivity
  have herr : ∀ᶠ n in atTop, e n k < 1 / ((k : ℝ) + 1) :=
    (he k).eventually (gt_mem_nhds htol)
  filter_upwards [eventually_ge_atTop k, herr] with n hn hn'
  exact Nat.le_findGreatest hn hn'

private theorem diagonalRadius_eventually_error_lt (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      e n (diagonalRadius e n) <
        1 / ((diagonalRadius e n : ℝ) + 1) := by
  classical
  have htol : (0 : ℝ) < 1 / ((0 : ℝ) + 1) := by
    norm_num
  have herr : ∀ᶠ n in atTop,
      e n 0 < 1 / ((0 : ℝ) + 1) :=
    (he 0).eventually (gt_mem_nhds htol)
  filter_upwards [herr] with n hn
  change
    (fun k : ℕ => e n k < 1 / ((k : ℝ) + 1))
      (Nat.findGreatest (fun k => e n k < 1 / ((k : ℝ) + 1)) n)
  exact Nat.findGreatest_spec
    (P := fun k => e n k < 1 / ((k : ℝ) + 1))
    (Nat.zero_le n) (by simpa only [CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, div_self] using hn)

private theorem diagonalRadius_error_tendsto_zero (e : ℕ → ℕ → ℝ)
    (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (fun n => e n (diagonalRadius e n)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      e n (diagonalRadius e n) ≤
        1 / ((diagonalRadius e n : ℝ) + 1) :=
    (diagonalRadius_eventually_error_lt e he).mono fun _ h => h.le
  have hlimit : Tendsto
      (fun n => 1 / ((diagonalRadius e n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (diagonalRadius_tendsto_atTop e he)
  exact squeeze_zero'
    (Eventually.of_forall fun n => hnonneg n (diagonalRadius e n))
    hbound hlimit

public
theorem exists_diverging_radius_with_vanishing_diagonal_error
    (e : ℕ → ℕ → ℝ) (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto (fun n => e n (r n)) atTop (𝓝 0) :=
  ⟨diagonalRadius e, diagonalRadius_tendsto_atTop e he,
    diagonalRadius_error_tendsto_zero e hnonneg he⟩

public
theorem finite_union_bad_density_tendsto_zero
    {α : ℕ → Type*} [∀ n, DecidableEq (α n)]
    {ι : Type*} (I : Finset ι)
    (V : ∀ n, Finset (α n)) (B : ∀ n, ι → Finset (α n))
    (hbad : ∀ i ∈ I, Tendsto
      (fun n => (((V n ∩ B n i).card : ℝ) / (V n).card))
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((V n ∩ I.biUnion (B n)).card : ℝ) / (V n).card))
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto
      (fun n =>
        ∑ i ∈ I, (((V n ∩ B n i).card : ℝ) / (V n).card))
      atTop (𝓝 0) := by
    induction I using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, tendsto_const_nhds_iff]
    | @insert i I hi ih =>
        have hfirst := hbad i (Finset.mem_insert_self i I)
        have hrest := ih (fun j hj =>
          hbad j (Finset.mem_insert_of_mem hj))
        simpa only [hi, not_false_eq_true, Finset.sum_insert, add_zero] using hfirst.add hrest
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((V n ∩ I.biUnion (B n)).card : ℝ) ≤
        ∑ i ∈ I, ((V n ∩ B n i).card : ℝ) := by
    rw [Finset.inter_biUnion]
    exact_mod_cast
      (Finset.card_biUnion_le
        (s := I) (t := fun i => V n ∩ B n i))
  calc
    ((V n ∩ I.biUnion (B n)).card : ℝ) / (V n).card ≤
        (∑ i ∈ I, ((V n ∩ B n i).card : ℝ)) / (V n).card :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ i ∈ I, (((V n ∩ B n i).card : ℝ) / (V n).card) :=
      Finset.sum_div _ _ _

public
theorem sum_card_inter_partition {α : Type*} [DecidableEq α]
    {U : Finset α} (P : Finpartition U) (B : Finset α) :
    ∑ C ∈ P.parts, (C ∩ B).card = (U ∩ B).card := by
  have hdis :
      (P.parts : Set (Finset α)).PairwiseDisjoint
        (fun C : Finset α => C ∩ B) := by
    intro C hC D hD hne
    exact (P.disjoint hC hD hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hunion :
      P.parts.biUnion (fun C => C ∩ B) = U ∩ B := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, ← P.biUnion_parts, id_eq]
    aesop
  calc
    ∑ C ∈ P.parts, (C ∩ B).card =
        (P.parts.biUnion fun C => C ∩ B).card :=
      (Finset.card_biUnion hdis).symm
    _ = (U ∩ B).card := congrArg Finset.card hunion

public
theorem retained_bad_density_tendsto_zero
    {α : ℕ → Type*} [∀ n, DecidableEq (α n)]
    (V U B : ∀ n, Finset (α n))
    (hV : ∀ n, (V n).Nonempty) (hU : ∀ n, (U n).Nonempty)
    (hUV : ∀ n, U n ⊆ V n)
    (hcover : Tendsto
      (fun n => ((U n).card : ℝ) / (V n).card) atTop (𝓝 1))
    (hbad : Tendsto
      (fun n => (((V n ∩ B n).card : ℝ) / (V n).card))
      atTop (𝓝 0)) :
    Tendsto (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ ((U n).card : ℝ) / (V n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (by simpa only [mul_zero] using
          (tendsto_const_nhds.mul hbad :
            Tendsto (fun n => (2 : ℝ) * (((V n ∩ B n).card : ℝ) / (V n).card)) atTop (𝓝 ((2 : ℝ) *
              0))))
  filter_upwards [hhalf] with n hn
  have hv : (0 : ℝ) < (V n).card := by
    exact_mod_cast (hV n).card_pos
  have hu : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hmass : ((V n).card : ℝ) ≤ 2 * (U n).card := by
    have h := (le_div_iff₀ hv).1 hn
    linarith
  have hbadcard :
      ((U n ∩ B n).card : ℝ) ≤ (V n ∩ B n).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter_right (hUV n) :
        U n ∩ B n ⊆ V n ∩ B n)
  calc
    ((U n ∩ B n).card : ℝ) / (U n).card ≤
        ((V n ∩ B n).card : ℝ) / (U n).card :=
      div_le_div_of_nonneg_right hbadcard hu.le
    _ ≤ 2 * (((V n ∩ B n).card : ℝ) / (V n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hu hv).2
      simpa only [mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) (V n ∩ B n).card))

/-- Internal interface connecting the split non-sofic proof modules. -/
public
inductive LeavittGenerator where
  | s : Fin 2 → LeavittGenerator
  | t : Fin 2 → LeavittGenerator
  deriving Fintype

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev LeavittFree : Type := FreeAlgebra (ZMod 2) LeavittGenerator

private instance leavittFreeCountable : Countable LeavittFree :=
  ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := LeavittGenerator)).toEquiv.trans
    (MonoidAlgebra.coeffEquiv
      (R := ZMod 2) (M := FreeMonoid LeavittGenerator))).injective.countable

/-- Internal interface connecting the split non-sofic proof modules. -/
public
inductive LeavittRelation : LeavittFree → LeavittFree → Prop where
  | inverse (i j : Fin 2) :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.t i) * FreeAlgebra.ι (ZMod 2) (.s j))
        (if i = j then 1 else 0)
  | partition :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.s 0) * FreeAlgebra.ι (ZMod 2) (.t 0) +
          FreeAlgebra.ι (ZMod 2) (.s 1) * FreeAlgebra.ι (ZMod 2) (.t 1))
        1

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev BinaryLeavitt : Type := RingQuot LeavittRelation

private instance binaryLeavittCountable : Countable BinaryLeavitt :=
  (RingQuot.mkAlgHom_surjective (ZMod 2) LeavittRelation).countable

private def leavittQuotient : LeavittFree →ₐ[ZMod 2] BinaryLeavitt :=
  RingQuot.mkAlgHom (ZMod 2) LeavittRelation

public
instance binaryLeavittFiniteType : Algebra.FiniteType (ZMod 2) BinaryLeavitt :=
  Algebra.FiniteType.of_surjective leavittQuotient
    (RingQuot.mkAlgHom_surjective (ZMod 2) LeavittRelation)

private def leavittS (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.s i))

private def leavittT (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.t i))

private theorem leavittT_mul_S (i j : Fin 2) :
    leavittT i * leavittS j = if i = j then 1 else 0 := by
  simpa only [leavittT, leavittQuotient, leavittS, map_mul, MonoidWithZeroHom.map_ite_one_zero]
    using
    RingQuot.mkAlgHom_rel (ZMod 2) (LeavittRelation.inverse i j)

private theorem leavitt_partition :
    leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1 = 1 := by
  simpa only [leavittS, leavittQuotient, Fin.isValue, leavittT, map_add, map_mul, map_one] using
    RingQuot.mkAlgHom_rel (ZMod 2) LeavittRelation.partition

private abbrev leavittSequence : Type := ℕ → ZMod 2

private def prefixOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := if n % 2 = i.val then x (n / 2) else 0
  map_add' x y := by
    ext n
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    ext n
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

private def deletionOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := x (2 * n + i.val)
  map_add' x y := by
    ext n
    rfl
  map_smul' a x := by
    ext n
    rfl

private theorem deletion_mul_prefix (i j : Fin 2) :
    deletionOperator i * prefixOperator j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> ext x n <;>
    simp [deletionOperator, prefixOperator, Module.End.mul_apply, Nat.add_mod]
  congr 1
  omega

private theorem prefix_deletion_partition :
    prefixOperator 0 * deletionOperator 0 +
      prefixOperator 1 * deletionOperator 1 = 1 := by
  ext x n
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  change
    (if n % 2 = 0 then x (2 * (n / 2)) else 0) +
      (if n % 2 = 1 then x (2 * (n / 2) + 1) else 0) = x n
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h] <;> congr 1 <;> omega

private def leavittGeneratorAction :
    LeavittGenerator → Module.End (ZMod 2) leavittSequence
  | .s i => prefixOperator i
  | .t i => deletionOperator i

private def leavittFreeRepresentation :
    LeavittFree →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  FreeAlgebra.lift (ZMod 2) leavittGeneratorAction

private theorem leavittFreeRepresentation_respects {x y : LeavittFree}
    (h : LeavittRelation x y) :
    leavittFreeRepresentation x = leavittFreeRepresentation y := by
  cases h with
  | inverse i j =>
      simp only [leavittFreeRepresentation, map_mul, FreeAlgebra.lift_ι_apply,
        leavittGeneratorAction,
        deletion_mul_prefix, MonoidWithZeroHom.map_ite_one_zero]
  | partition =>
      simpa only [leavittFreeRepresentation, Fin.isValue, map_add, map_mul,
        FreeAlgebra.lift_ι_apply,
        leavittGeneratorAction, map_one] using prefix_deletion_partition

private def leavittRepresentation :
    BinaryLeavitt →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  RingQuot.liftAlgHom (ZMod 2)
    ⟨leavittFreeRepresentation, fun _ _ h => leavittFreeRepresentation_respects h⟩

@[simp] private theorem leavittRepresentation_S (i : Fin 2) :
    leavittRepresentation (leavittS i) = prefixOperator i := by
  simp only [leavittRepresentation, leavittFreeRepresentation, leavittS, leavittQuotient,
    RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply, leavittGeneratorAction]

@[simp] private theorem leavittRepresentation_T (i : Fin 2) :
    leavittRepresentation (leavittT i) = deletionOperator i := by
  simp only [leavittRepresentation, leavittFreeRepresentation, leavittT, leavittQuotient,
    RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply, leavittGeneratorAction]

public
instance binaryLeavittNontrivial : Nontrivial BinaryLeavitt :=
  leavittRepresentation.toRingHom.domain_nontrivial

private theorem prefix_deletion_ne_one :
    prefixOperator 0 * deletionOperator 0 ≠ 1 := by
  intro h
  have h' := congrArg
    (fun f : Module.End (ZMod 2) leavittSequence => f (fun _ => 1) 1) h
  simp only [prefixOperator, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, deletionOperator,
    add_zero,
    Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Nat.mod_succ, one_ne_zero, ↓reduceIte,
      Module.End.one_apply,
    zero_ne_one] at h'

private theorem leavittS_mul_T_ne_one : leavittS 0 * leavittT 0 ≠ 1 := by
  intro h
  apply prefix_deletion_ne_one
  simpa only [Fin.isValue, map_mul, leavittRepresentation_S, leavittRepresentation_T, map_one] using
    congrArg leavittRepresentation h

private instance binaryLeavittInfinite : Infinite BinaryLeavitt where
  not_finite h := by
    let := h
    apply leavittS_mul_T_ne_one
    exact mul_eq_one_symm (by simpa only [Fin.isValue, ↓reduceIte] using leavittT_mul_S 0 0)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittWordS : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittS i * leavittWordS a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittWordT : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittWordT a * leavittT i

public
theorem leavittWordT_mul_wordS_self (a : List (Fin 2)) :
    leavittWordT a * leavittWordS a = 1 := by
  induction a with
  | nil => simp only [leavittWordT, leavittWordS, mul_one]
  | cons i a ih =>
      calc
        leavittWordT (i :: a) * leavittWordS (i :: a) =
            leavittWordT a *
              ((leavittT i * leavittS i) * leavittWordS a) := by
                simp only [leavittWordT, leavittWordS, mul_assoc]
        _ = 1 := by simp only [leavittT_mul_S, ↓reduceIte, one_mul, ih]

public
theorem leavittWordT_mul_wordS_of_incomparable
    (a b : List (Fin 2)) (hab : ¬a <+: b) (hba : ¬b <+: a) :
    leavittWordT a * leavittWordS b = 0 := by
  induction a generalizing b with
  | nil => exact (hab (by simp only [List.nil_prefix])).elim
  | cons i a ih =>
      cases b with
      | nil => exact (hba (by simp only [List.nil_prefix])).elim
      | cons j b =>
          by_cases hij : i = j
          · subst j
            have hab' : ¬a <+: b := by
              intro hp
              apply hab
              simpa only [List.cons_prefix_cons, true_and] using hp
            have hba' : ¬b <+: a := by
              intro hp
              apply hba
              simpa only [List.cons_prefix_cons, true_and] using hp
            calc
              leavittWordT (i :: a) * leavittWordS (i :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS i) * leavittWordS b) := by
                      simp only [leavittWordT, leavittWordS, mul_assoc]
              _ = leavittWordT a * leavittWordS b := by
                simp only [leavittT_mul_S, ↓reduceIte, one_mul]
              _ = 0 := ih b hab' hba'
          · calc
              leavittWordT (i :: a) * leavittWordS (j :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS j) * leavittWordS b) := by
                      simp only [leavittWordT, leavittWordS, mul_assoc]
              _ = 0 := by simp only [leavittT_mul_S, hij, ↓reduceIte, zero_mul, mul_zero]

public
theorem leavittWordS_append (a b : List (Fin 2)) :
    leavittWordS (a ++ b) = leavittWordS a * leavittWordS b := by
  induction a with
  | nil => simp only [List.nil_append, leavittWordS, one_mul]
  | cons i a ih => simp only [List.cons_append, leavittWordS, ih, mul_assoc]

public
theorem leavittWordT_append (a b : List (Fin 2)) :
    leavittWordT (a ++ b) = leavittWordT b * leavittWordT a := by
  induction a with
  | nil => simp only [List.nil_append, leavittWordT, mul_one]
  | cons i a ih => simp only [List.cons_append, leavittWordT, ih, mul_assoc]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittCylinder (a : List (Fin 2)) : BinaryLeavitt :=
  leavittWordS a * leavittWordT a

private theorem leavittCylinder_split (a : List (Fin 2)) :
    leavittCylinder a =
      leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
  calc
    leavittCylinder a =
        leavittWordS a *
          (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) *
          leavittWordT a := by
            rw [leavitt_partition]
            simp only [leavittCylinder, mul_one]
    _ = leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
      simp only [Fin.isValue, mul_add, add_mul, mul_assoc, leavittCylinder, leavittWordS_append,
        leavittWordS,
        mul_one, leavittWordT_append, leavittWordT, one_mul]

namespace MatrixCorner

variable {ι A : Type*} [Fintype ι] [Ring A]

private def codeIdempotent (s t : ι → A) : A := ∑ i, s i * t i

private def encode (s t : ι → A) (M : Matrix ι ι A) : A :=
  ∑ i, ∑ j, s i * M i j * t j

private def decode (s t : ι → A) (x : A) : Matrix ι ι A :=
  fun i j => t i * x * s j

private theorem decode_encode [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M : Matrix ι ι A) : decode s t (encode s t M) = M := by
  ext i j
  change t i * (∑ k, ∑ l, s k * M k l * t l) * s j = M i j
  calc
    t i * (∑ k, ∑ l, s k * M k l * t l) * s j =
        ∑ k, ∑ l, (t i * s k) * M k l * (t l * s j) := by
          simp only [mul_assoc, Finset.mul_sum, Finset.sum_mul]
    _ = M i j := by simp only [h, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ,
                      ↓reduceIte, Finset.sum_ite_eq]

private theorem encode_decode (s t : ι → A) (x : A) :
    encode s t (decode s t x) =
      codeIdempotent s t * x * codeIdempotent s t := by
  change
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
      (∑ i, s i * t i) * x * (∑ j, s j * t j)
  calc
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
        ∑ i, ∑ j, (s i * t i) * x * (s j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]
    _ = (∑ i, s i * t i) * x * (∑ j, s j * t j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

private theorem codeIdempotent_isIdempotent [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    IsIdempotentElem (codeIdempotent s t) := by
  change (∑ i, s i * t i) * (∑ i, s i * t i) = ∑ i, s i * t i
  calc
    (∑ i, s i * t i) * (∑ i, s i * t i) =
        ∑ i, ∑ j, s i * (t i * s j) * t j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]
    _ = ∑ i, s i * t i := by simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem encode_one [DecidableEq ι] (s t : ι → A) :
    encode s t (1 : Matrix ι ι A) = codeIdempotent s t := by
  simp only [encode, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, codeIdempotent]

private theorem encode_mul [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M N : Matrix ι ι A) :
    encode s t (M * N) = encode s t M * encode s t N := by
  symm
  calc
    encode s t M * encode s t N =
        ∑ i, ∑ j, ∑ k, ∑ l,
          s i * M i j * (t j * s k) * N k l * t l := by
            change
              (∑ i, ∑ j, s i * M i j * t j) *
                (∑ k, ∑ l, s k * N k l * t l) = _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            simp only [mul_assoc]
    _ = ∑ i, ∑ j, ∑ l, s i * M i j * N j l * t l := by
      simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = ∑ i, ∑ l, ∑ j, s i * M i j * N j l * t l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = encode s t (M * N) := by
      simp only [encode, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc]

private def ringEquiv [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    Matrix ι ι A ≃+* (codeIdempotent_isIdempotent s t h).Corner where
  toFun M :=
    ⟨encode s t M, ⟨encode s t M, by
      change
        codeIdempotent s t * encode s t M * codeIdempotent s t =
          encode s t M
      rw [← encode_decode, decode_encode s t h]⟩⟩
  invFun x := decode s t x.1
  left_inv M := decode_encode s t h M
  right_inv x := Subtype.ext <| by
    change encode s t (decode s t x.1) = x.1
    rw [encode_decode]
    have hx :=
      (Subsemigroup.mem_corner_iff
        (codeIdempotent_isIdempotent s t h)).mp x.property
    rw [hx.1, hx.2]
  map_mul' M N := Subtype.ext (encode_mul s t h M N)
  map_add' M N := Subtype.ext <| by
    change encode s t (M + N) = encode s t M + encode s t N
    simp only [encode, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

end MatrixCorner

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure BinaryPrefixCode (ι : Type*) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  word : ι → List (Fin 2)
  prefix_free : ∀ ⦃i j⦄, i ≠ j → ¬word i <+: word j

private theorem binaryPrefixCode_orthogonal {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) :
    leavittWordT (E.word i) * leavittWordS (E.word j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [leavittWordT_mul_wordS_self, ↓reduceIte]
  · simp only [hij, ↓reduceIte]
    exact leavittWordT_mul_wordS_of_incomparable _ _
      (E.prefix_free hij) (E.prefix_free (Ne.symm hij))

private def binaryPrefixCornerEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Matrix ι ι BinaryLeavitt ≃+*
      (MatrixCorner.codeIdempotent_isIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i))
        (binaryPrefixCode_orthogonal E)).Corner :=
  MatrixCorner.ringEquiv
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
    (binaryPrefixCode_orthogonal E)

private def prefixTable {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) : BinaryLeavitt :=
  ∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)

private theorem prefixTable_mul_reverse {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) :
    prefixTable source target * prefixTable target source =
      MatrixCorner.codeIdempotent
        (fun i => leavittWordS (target.word i))
        (fun i => leavittWordT (target.word i)) := by
  classical
  change
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
      ∑ i, leavittWordS (target.word i) * leavittWordT (target.word i)
  calc
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
        ∑ i, ∑ j,
          leavittWordS (target.word i) *
            (leavittWordT (source.word i) *
              leavittWordS (source.word j)) *
            leavittWordT (target.word j) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp only [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (target.word i) := by
      simp only [binaryPrefixCode_orthogonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]

private def prefixTableUnit {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι)
    (hsource : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (source.word i))
      (fun i => leavittWordT (source.word i)) = 1)
    (htarget : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (target.word i))
      (fun i => leavittWordT (target.word i)) = 1) : BinaryLeavittˣ where
  val := prefixTable source target
  inv := prefixTable target source
  val_inv := (prefixTable_mul_reverse source target).trans htarget
  inv_val := (prefixTable_mul_reverse target source).trans hsource

private def alphaWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0, 0]
  | 1 => [0, 0, 1]
  | _ => [0, 1]

private def betaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0, 0]
  | 1 => [1, 0, 0, 1]
  | _ => [1, 0, 1]

private def nuWord : Fin 3 → List (Fin 2)
  | 0 => [1, 1, 0, 0]
  | 1 => [1, 1, 0, 1]
  | _ => [1, 1, 1]

private def etaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0]
  | 1 => [1, 0, 1]
  | _ => [1, 1]

private def nineWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0
  | 1 => betaWord 0
  | 2 => nuWord 0
  | 3 => alphaWord 1
  | 4 => betaWord 1
  | 5 => nuWord 1
  | 6 => alphaWord 2
  | 7 => betaWord 2
  | _ => nuWord 2

private def uWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => alphaWord 0 ++ [1]
  | 2 => etaWord 0
  | 3 => alphaWord 1 ++ [0]
  | 4 => alphaWord 1 ++ [1]
  | 5 => etaWord 1
  | 6 => alphaWord 2 ++ [0]
  | 7 => alphaWord 2 ++ [1]
  | _ => etaWord 2

private def vWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => etaWord 0
  | 2 => alphaWord 0 ++ [1]
  | 3 => alphaWord 1 ++ [0]
  | 4 => etaWord 1
  | 5 => alphaWord 1 ++ [1]
  | 6 => alphaWord 2 ++ [0]
  | 7 => etaWord 2
  | _ => alphaWord 2 ++ [1]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def alphaPrefixCode : BinaryPrefixCode (Fin 3) where
  word := alphaWord
  prefix_free := by decide

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def ninePrefixCode : BinaryPrefixCode (Fin 9) where
  word := nineWord
  prefix_free := by decide

private def uPrefixCode : BinaryPrefixCode (Fin 9) where
  word := uWord
  prefix_free := by decide

private def vPrefixCode : BinaryPrefixCode (Fin 9) where
  word := vWord
  prefix_free := by decide

private theorem alpha_cylinders :
    leavittCylinder (alphaWord 0) +
        leavittCylinder (alphaWord 1) +
        leavittCylinder (alphaWord 2) =
      leavittCylinder [0] := by
  have h₀₀ :
      leavittCylinder [0, 0, 0] + leavittCylinder [0, 0, 1] =
        leavittCylinder [0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0,
      0]).symm
  have h₀ :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [0]).symm
  change
    leavittCylinder [0, 0, 0] +
        leavittCylinder [0, 0, 1] +
        leavittCylinder [0, 1] = leavittCylinder [0]
  rw [h₀₀, h₀]

private theorem beta_cylinders :
    leavittCylinder (betaWord 0) +
        leavittCylinder (betaWord 1) +
        leavittCylinder (betaWord 2) =
      leavittCylinder [1, 0] := by
  have h₁₀₀ :
      leavittCylinder [1, 0, 0, 0] + leavittCylinder [1, 0, 0, 1] =
        leavittCylinder [1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0]).symm
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      0]).symm
  change
    leavittCylinder [1, 0, 0, 0] +
        leavittCylinder [1, 0, 0, 1] +
        leavittCylinder [1, 0, 1] = leavittCylinder [1, 0]
  rw [h₁₀₀, h₁₀]

private theorem nu_cylinders :
    leavittCylinder (nuWord 0) +
        leavittCylinder (nuWord 1) +
        leavittCylinder (nuWord 2) =
      leavittCylinder [1, 1] := by
  have h₁₁₀ :
      leavittCylinder [1, 1, 0, 0] + leavittCylinder [1, 1, 0, 1] =
        leavittCylinder [1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      0]).symm
  have h₁₁ :
      leavittCylinder [1, 1, 0] + leavittCylinder [1, 1, 1] =
        leavittCylinder [1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      1]).symm
  change
    leavittCylinder [1, 1, 0, 0] +
        leavittCylinder [1, 1, 0, 1] +
        leavittCylinder [1, 1, 1] = leavittCylinder [1, 1]
  rw [h₁₁₀, h₁₁]

private theorem eta_cylinders :
    leavittCylinder (etaWord 0) +
        leavittCylinder (etaWord 1) +
        leavittCylinder (etaWord 2) =
      leavittCylinder [1] := by
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      0]).symm
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [1]).symm
  change
    leavittCylinder [1, 0, 0] +
        leavittCylinder [1, 0, 1] +
        leavittCylinder [1, 1] = leavittCylinder [1]
  rw [h₁₀, h₁]

private theorem ninePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (ninePrefixCode.word i))
      (fun i => leavittWordT (ninePrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (nineWord i)) = 1
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [1]).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (nineWord i)) =
        (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) +
        (leavittCylinder (betaWord 0) +
          leavittCylinder (betaWord 1) +
          leavittCylinder (betaWord 2)) +
        (leavittCylinder (nuWord 0) +
          leavittCylinder (nuWord 1) +
          leavittCylinder (nuWord 2)) := by
          simp only [nineWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton]
          ac_rfl
    _ = leavittCylinder [0] +
          leavittCylinder [1, 0] + leavittCylinder [1, 1] := by
      rw [alpha_cylinders, beta_cylinders, nu_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [add_assoc, h₁]
    _ = 1 := hroot

private theorem uPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (uPrefixCode.word i))
      (fun i => leavittWordT (uPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (uWord i)) = 1
  have h₀ :
      leavittCylinder (alphaWord 0 ++ [0]) +
          leavittCylinder (alphaWord 0 ++ [1]) =
        leavittCylinder (alphaWord 0) :=
    (leavittCylinder_split (alphaWord 0)).symm
  have h₁ :
      leavittCylinder (alphaWord 1 ++ [0]) +
          leavittCylinder (alphaWord 1 ++ [1]) =
        leavittCylinder (alphaWord 1) :=
    (leavittCylinder_split (alphaWord 1)).symm
  have h₂ :
      leavittCylinder (alphaWord 2 ++ [0]) +
          leavittCylinder (alphaWord 2 ++ [1]) =
        leavittCylinder (alphaWord 2) :=
    (leavittCylinder_split (alphaWord 2)).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (uWord i)) =
        ((leavittCylinder (alphaWord 0 ++ [0]) +
            leavittCylinder (alphaWord 0 ++ [1])) +
          (leavittCylinder (alphaWord 1 ++ [0]) +
            leavittCylinder (alphaWord 1 ++ [1])) +
          (leavittCylinder (alphaWord 2 ++ [0]) +
            leavittCylinder (alphaWord 2 ++ [1]))) +
        (leavittCylinder (etaWord 0) +
          leavittCylinder (etaWord 1) +
          leavittCylinder (etaWord 2)) := by
          simp only [uWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton]
          ac_rfl
    _ = (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) + leavittCylinder [1] := by
      rw [h₀, h₁, h₂, eta_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [alpha_cylinders]
    _ = 1 := hroot

private theorem vPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (vPrefixCode.word i))
      (fun i => leavittWordT (vPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (vWord i)) = 1
  calc
    (∑ i : Fin 9, leavittCylinder (vWord i)) =
        ∑ i : Fin 9, leavittCylinder (uWord i) := by
          simp only [vWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton, uWord,
            add_right_inj]
          ac_rfl
    _ = 1 := uPrefixCode_complete

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def compressionU : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode uPrefixCode
    ninePrefixCode_complete uPrefixCode_complete

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def compressionV : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode vPrefixCode
    ninePrefixCode_complete vPrefixCode_complete

private instance binaryLeavittCharP : CharP BinaryLeavitt 2 :=
  CharP.of_ringHom_of_ne_zero
    (algebraMap (ZMod 2) BinaryLeavitt) 2 (by decide)

private theorem matrixUnitTransport_root
    {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (sSource tSource sTarget tTarget : ι → A)
    (hsource : ∀ i j, tSource i * sSource j = if i = j then 1 else 0)
    (i j : ι) (a : A) :
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
      sTarget i * a * tTarget j := by
  have hleft :
      (∑ k, sTarget k * tSource k) * sSource i = sTarget i := by
    calc
      (∑ k, sTarget k * tSource k) * sSource i =
          ∑ k, sTarget k * (tSource k * sSource i) := by
            simp only [Finset.sum_mul, mul_assoc]
      _ = sTarget i := by simp only [hsource, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
  have hright :
      tSource j * (∑ k, sSource k * tTarget k) = tTarget j := by
    calc
      tSource j * (∑ k, sSource k * tTarget k) =
          ∑ k, (tSource j * sSource k) * tTarget k := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = tTarget j := by simp only [hsource, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
  calc
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
        ((∑ k, sTarget k * tSource k) * sSource i) * a *
          (tSource j * (∑ k, sSource k * tTarget k)) := by
            simp only [mul_assoc]
    _ = sTarget i * a * tTarget j := by rw [hleft, hright]

private theorem prefixTable_transport_root {ι : Type*}
    [Fintype ι]
    (source target : BinaryPrefixCode ι) (i j : ι)
    (a : BinaryLeavitt) :
    prefixTable source target *
        (leavittWordS (source.word i) * a *
          leavittWordT (source.word j)) *
        prefixTable target source =
      leavittWordS (target.word i) * a * leavittWordT (target.word j) := by
  classical
  exact matrixUnitTransport_root
    (fun k => leavittWordS (source.word k))
    (fun k => leavittWordT (source.word k))
    (fun k => leavittWordS (target.word k))
    (fun k => leavittWordT (target.word k))
    (binaryPrefixCode_orthogonal source) i j a

private theorem compressionU_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (uWord i) * a * leavittWordT (uWord j) := by
  exact prefixTable_transport_root ninePrefixCode uPrefixCode i j a

private theorem compressionV_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (vWord i) * a * leavittWordT (vWord j) := by
  exact prefixTable_transport_root ninePrefixCode vPrefixCode i j a

private def alphaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val, by omega⟩

@[simp]
private theorem nineWord_alphaNineIndex (i : Fin 3) :
    nineWord (alphaNineIndex i) = alphaWord i := by
  fin_cases i <;> rfl

@[simp]
private theorem uWord_alphaNineIndex (i : Fin 3) :
    uWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl

@[simp]
private theorem vWord_alphaNineIndex (i : Fin 3) :
    vWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl

private theorem compressionU_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, uWord_alphaNineIndex] using
    compressionU_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a

private theorem compressionV_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, vWord_alphaNineIndex] using
    compressionV_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def alphaZeroPrefixCode : BinaryPrefixCode (Fin 3) where
  word i := alphaWord i ++ [0]
  prefix_free := by decide

private def prefixElementaryUnit {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j)
    (a : BinaryLeavitt) : BinaryLeavittˣ := by
  let x := leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have hzero : leavittWordT (E.word j) * leavittWordS (E.word i) = 0 := by
    simpa only [hij.symm, ↓reduceIte] using binaryPrefixCode_orthogonal E j i
  have hx : x * x = 0 := by
    dsimp [x]
    calc
      (leavittWordS (E.word i) * a * leavittWordT (E.word j)) *
          (leavittWordS (E.word i) * a * leavittWordT (E.word j)) =
        leavittWordS (E.word i) * a *
          (leavittWordT (E.word j) * leavittWordS (E.word i)) *
          a * leavittWordT (E.word j) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hzero]; simp only [mul_zero, zero_mul]
  exact
    { val := 1 + x
      inv := 1 - x
      val_inv := by noncomm_ring [hx]
      inv_val := by noncomm_ring [hx] }

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def prefixElementaryGroup {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : BinaryLeavitt),
      prefixElementaryUnit E i j h a = z}

private theorem compressionU_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionU
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) := by
          simp only [mul_add, mul_one, add_mul, Units.mul_inv]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionU_conjugate_alpha_root]

private theorem compressionV_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionV
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) := by
          simp only [mul_add, mul_one, add_mul, Units.mul_inv]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionV_conjugate_alpha_root]

private theorem prefixElementaryGroup_map_conj
    {ι : Type*} [DecidableEq ι]
    (E E' : BinaryPrefixCode ι) (g : BinaryLeavittˣ)
    (hconj : ∀ (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt),
      MulAut.conj g (prefixElementaryUnit E i j hij a) =
        prefixElementaryUnit E' i j hij a) :
    (prefixElementaryGroup E).map (MulAut.conj g).toMonoidHom =
      prefixElementaryGroup E' := by
  unfold prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a, (hconj i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨prefixElementaryUnit E i j hij a,
      ⟨i, j, hij, a, rfl⟩, hconj i j hij a⟩

public
theorem compressionU_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionU).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionU compressionU_conjugate_alpha_elementaryUnit

public
theorem compressionV_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionV).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionV compressionV_conjugate_alpha_elementaryUnit

private theorem alphaZero_prefixElementaryUnit_eq
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaZeroPrefixCode i j hij a =
      prefixElementaryUnit alphaPrefixCode i j hij
        (leavittS 0 * a * leavittT 0) := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i ++ [0]) * a *
      leavittWordT (alphaWord j ++ [0]) =
    1 + leavittWordS (alphaWord i) *
      (leavittS 0 * a * leavittT 0) * leavittWordT (alphaWord j)
  simp only [Fin.isValue, leavittWordS_append, leavittWordS, mul_one, mul_assoc,
    leavittWordT_append,
    leavittWordT, one_mul]

public
theorem alphaZero_prefixElementaryGroup_le :
    prefixElementaryGroup alphaZeroPrefixCode ≤
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaZero_prefixElementaryUnit_eq]
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittS 0 * a * leavittT 0, rfl⟩

section NoncommutativeElementaryGroup

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

private theorem single_mul_self_eq_zero (i j : ι) (h : i ≠ j) (a : R) :
    Matrix.single i j a * Matrix.single i j a = 0 :=
  Matrix.single_mul_single_of_ne (c := a) i j i h.symm a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryUnit (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]
  inv_val := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]

@[simp] private theorem elementaryUnit_zero (i j : ι) (h : i ≠ j) :
    elementaryUnit (R := R) i j h 0 = 1 := by
  apply Units.ext
  simp only [elementaryUnit, Matrix.single_zero, add_zero, sub_zero, Units.val_one]

private theorem elementaryUnit_mul (i j : ι) (h : i ≠ j) (a b : R) :
    elementaryUnit i j h a * elementaryUnit i j h b =
      elementaryUnit i j h (a + b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single i j b) =
      1 + Matrix.single i j (a + b)
  have hab : Matrix.single i j a * Matrix.single i j b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i h.symm b
  rw [Matrix.single_add]
  noncomm_ring [hab]

private theorem elementaryUnit_injective (i j : ι) (h : i ≠ j) :
    Function.Injective (elementaryUnit (R := R) i j h) := by
  intro a b hab
  have he := congrArg (fun z : (Matrix ι ι R)ˣ => (z : Matrix ι ι R) i j) hab
  simpa only [elementaryUnit, Matrix.add_apply, ne_eq, h, not_false_eq_true, Matrix.one_apply_ne,
    Matrix.single_apply_same, zero_add] using he

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryGroup (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] :
    Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : R), elementaryUnit i j h a = z}

public
theorem elementaryUnit_mem (i j : ι) (h : i ≠ j) (a : R) :
    elementaryUnit i j h a ∈ elementaryGroup ι R :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryRootHom (i j : ι) (h : i ≠ j) :
    Multiplicative R →* elementaryGroup ι R where
  toFun a := ⟨elementaryUnit i j h a.toAdd, elementaryUnit_mem i j h a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact elementaryUnit_zero i j h
  map_mul' a b := by
    apply Subtype.ext
    exact (elementaryUnit_mul i j h a.toAdd b.toAdd).symm

private theorem elementaryGroup_infinite [Infinite R] (i j : ι) (h : i ≠ j) :
    Infinite (elementaryGroup ι R) := by
  apply Infinite.of_injective
    (fun a : R => (⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
      elementaryGroup ι R))
  intro a b hab
  exact elementaryUnit_injective i j h (congrArg Subtype.val hab)

private theorem cylinder_transposition_factorization [CharP R 2] (P Q : R)
    (hPP : P * P = 0) (hPQP : P * Q * P = P) :
    (1 + P) * (1 + Q) * (1 + P) =
      1 - P * Q - Q * P + P + Q := by
  simp only [CharTwo.sub_eq_add]
  have hthree : (3 : ℤ) • P = P := by
    rw [zsmul_eq_mul, CharTwo.intCast_eq_mod]
    norm_num
  noncomm_ring [hPP, hPQP]
  simp only [hthree]

public
theorem elementaryUnit_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
      elementaryUnit i k hik (a * b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
      (1 - Matrix.single i j a) * (1 - Matrix.single j k b) =
      1 + Matrix.single i k (a * b)
  have hxx := single_mul_self_eq_zero i j hij a
  have hyy := single_mul_self_eq_zero j k hjk b
  have hyx : Matrix.single j k b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k i hik.symm a
  have hxy : Matrix.single i j a * Matrix.single j k b =
      Matrix.single i k (a * b) :=
    Matrix.single_mul_single_same (c := a) i j k b
  have hzx : Matrix.single i k (a * b) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm a
  have hzy : Matrix.single i k (a * b) * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k j hjk.symm b
  have hzz := single_mul_self_eq_zero i k hik (a * b)
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz]

public
theorem elementaryUnit_mem_of_two_step
    (H : Subgroup (Matrix ι ι R)ˣ) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : R)
    (hleft : elementaryUnit i j hij a ∈ H)
    (hright : elementaryUnit j k hjk 1 ∈ H) :
    elementaryUnit i k hik a ∈ H := by
  have hc : ⁅elementaryUnit i j hij a, elementaryUnit j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [elementaryUnit_commutator i j k hij hjk hik a 1] at hc
  simpa only [mul_one] using hc

end NoncommutativeElementaryGroup

section FiniteGeneration

variable {R : Type*} [Ring R]

private noncomputable def finiteElementaryGenerators [DecidableEq R]
    (n : ℕ) (s : Finset R) : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
  Finset.univ.biUnion (fun i : Fin n =>
    Finset.univ.biUnion (fun j : Fin n =>
      if h : i ≠ j then (insert 1 s).image (elementaryUnit i j h) else ∅))

private theorem mem_finiteElementaryGenerators [DecidableEq R] (n : ℕ) (s : Finset R)
    (z : (Matrix (Fin n) (Fin n) R)ˣ) :
    z ∈ finiteElementaryGenerators n s ↔
      ∃ (i j : Fin n) (h : i ≠ j) (a : R),
        a ∈ insert 1 s ∧ elementaryUnit i j h a = z := by
  constructor
  · intro hz
    unfold finiteElementaryGenerators at hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : i ≠ j
    · rw [dite_eq_left h] at hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, j, h, a, ha, rfl⟩
    · rw [dite_eq_right h] at hj
      simp only [Finset.notMem_empty] at hj
  · rintro ⟨i, j, h, a, ha, rfl⟩
    unfold finiteElementaryGenerators
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [dite_eq_left h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

variable [Algebra (ZMod 2) R]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryCoefficientSubalgebra (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) :
    Subalgebra (ZMod 2) R where
  carrier :=
    {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hik : i ≠ k := hki.symm
    have hleft := ha i k hik
    have hright := hb k j hkj
    have hc : ⁅elementaryUnit i k hik a, elementaryUnit k j hkj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
        (H.inv_mem hright)
    rw [elementaryUnit_commutator i k j hik hkj hij a b] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, elementaryUnit_zero] using H.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij

private theorem elementaryGroup_finitelyGenerated
    [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ZMod 2) (A := R)
  let t : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
    finiteElementaryGenerators n s
  let H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
    Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ)
  have hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    change elementaryUnit i j hij (1 : R) ∈ finiteElementaryGenerators n s
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  let C : Subalgebra (ZMod 2) R :=
    elementaryCoefficientSubalgebra n hn H hunit
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    change elementaryUnit i j hij a ∈ finiteElementaryGenerators n s
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  have heq : H = elementaryGroup (Fin n) R := by
    apply le_antisymm
    · change Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ) ≤ _
      rw [Subgroup.closure_le]
      intro z hz
      change z ∈ finiteElementaryGenerators n s at hz
      obtain ⟨i, j, hij, a, _, rfl⟩ :=
        (mem_finiteElementaryGenerators n s z).mp hz
      exact elementaryUnit_mem i j hij a
    · rw [elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, a, rfl⟩
      have ha : a ∈ C := by simp only [hC, Algebra.mem_top]
      exact ha i j hij
  apply (Group.fg_iff_subgroup_fg (elementaryGroup (Fin n) R)).mpr
  exact ⟨t, heq⟩

private theorem elementaryGroup_three_finitelyGenerated
    [Algebra.FiniteType (ZMod 2) R] :
    Group.FG (elementaryGroup (Fin 3) R) :=
  elementaryGroup_finitelyGenerated 3 (by decide)

end FiniteGeneration

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev binaryLeavittElementaryGroup (n : ℕ) : Type :=
  elementaryGroup (Fin n) BinaryLeavitt

private def completePrefixMatrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    Matrix ι ι BinaryLeavitt ≃+* BinaryLeavitt where
  toFun := MatrixCorner.encode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  invFun := MatrixCorner.decode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  left_inv := MatrixCorner.decode_encode _ _ (binaryPrefixCode_orthogonal E)
  right_inv x := by
    rw [MatrixCorner.encode_decode, hcomplete]
    simp only [one_mul, mul_one]
  map_mul' := MatrixCorner.encode_mul _ _ (binaryPrefixCode_orthogonal E)
  map_add' M N := by
    simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private def completePrefixUnitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (Matrix ι ι BinaryLeavitt)ˣ ≃* BinaryLeavittˣ :=
  Units.mapEquiv (completePrefixMatrixEquiv E hcomplete).toMulEquiv

private theorem completePrefixUnitEquiv_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    completePrefixUnitEquiv E hcomplete (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) =
        1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have h₁ :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) = 1 := by
    rw [MatrixCorner.encode_one, hcomplete]
  calc
    MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) +
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (Matrix.single i j a) := by
          simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
            Finset.sum_add_distrib]
    _ = 1 + leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
      rw [h₁]
      simp only [MatrixCorner.encode, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul,
        zero_mul,
        Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]

private theorem completePrefixElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (elementaryGroup ι BinaryLeavitt).map
        (completePrefixUnitEquiv E hcomplete).toMonoidHom =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def ninePrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 9 ≃* prefixElementaryGroup ninePrefixCode :=
  ((completePrefixUnitEquiv ninePrefixCode ninePrefixCode_complete).subgroupMap
      (elementaryGroup (Fin 9) BinaryLeavitt)).trans
    (MulEquiv.subgroupCongr
      (completePrefixElementaryGroup_map ninePrefixCode ninePrefixCode_complete))

private def idempotentCornerUnitExtension {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : he.Cornerˣ →* Aˣ where
  toFun u :=
    { val := u.val.val + (1 - e)
      inv := u.inv.val + (1 - e)
      val_inv := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have huv : u.val.val * u.inv.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.val_inv
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, huv]
      inv_val := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have hvu : u.inv.val * u.val.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.inv_val
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, hvu] }
  map_one' := by
    apply Units.ext
    change e + (1 - e) = 1
    noncomm_ring
  map_mul' u v := by
    apply Units.ext
    have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
    have hv := (Subsemigroup.mem_corner_iff he).mp v.val.property
    change
      u.val.val * v.val.val + (1 - e) =
        (u.val.val + (1 - e)) * (v.val.val + (1 - e))
    noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2]

private theorem idempotentCornerUnitExtension_injective
    {A : Type*} [Ring A] {e : A} (he : IsIdempotentElem e) :
    Function.Injective (idempotentCornerUnitExtension he) := by
  intro u v huv
  apply Units.ext
  apply Subtype.ext
  have h := congrArg (fun z : Aˣ => (z : A)) huv
  change u.val.val + (1 - e) = v.val.val + (1 - e) at h
  exact add_right_cancel h

private def prefixCornerUnitHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (Matrix ι ι BinaryLeavitt)ˣ →* BinaryLeavittˣ :=
  (idempotentCornerUnitExtension
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).toMonoidHom

private theorem prefixCornerUnitHom_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Function.Injective (prefixCornerUnitHom E) := by
  exact (idempotentCornerUnitExtension_injective
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).injective

private theorem prefixCornerUnitHom_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixCornerUnitHom E (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) +
      (1 - MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))) =
      1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have henc :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k)) +
        leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
    calc
      MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 + Matrix.single i j a) =
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 : Matrix ι ι BinaryLeavitt) +
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (Matrix.single i j a) := by
            simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
              Finset.sum_add_distrib]
      _ = MatrixCorner.codeIdempotent
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k)) +
          leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
            rw [MatrixCorner.encode_one]
            simp only [MatrixCorner.encode, Matrix.single_apply, ite_and, mul_ite, mul_zero,
              ite_mul, zero_mul,
              Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
                Finset.sum_const_zero]
  rw [henc]
  noncomm_ring

private theorem prefixCornerElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (elementaryGroup ι BinaryLeavitt).map (prefixCornerUnitHom E) =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (prefixCornerUnitHom_elementaryUnit E i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      prefixCornerUnitHom_elementaryUnit E i j hij a⟩

private def alphaPrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 3 ≃* prefixElementaryGroup alphaPrefixCode :=
  ((elementaryGroup (Fin 3) BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom alphaPrefixCode)
      (prefixCornerUnitHom_injective alphaPrefixCode)).trans
    (MulEquiv.subgroupCongr
      (prefixCornerElementaryGroup_map alphaPrefixCode))

namespace SourceGeneration

open scoped commutatorElement

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceGeneratedGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    ((prefixElementaryGroup alphaPrefixCode : Set BinaryLeavittˣ) ∪
      {compressionU, compressionV})

private theorem alphaRoot_mem_sourceGenerated
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a ∈ sourceGeneratedGroup := by
  apply Subgroup.subset_closure
  apply Set.mem_union_left
  exact Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

private theorem compressionU_mem_sourceGenerated :
    compressionU ∈ sourceGeneratedGroup := by
  apply Subgroup.subset_closure
  apply Set.mem_union_right
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

private theorem compressionV_mem_sourceGenerated :
    compressionV ∈ sourceGeneratedGroup := by
  apply Subgroup.subset_closure
  apply Set.mem_union_right
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

private theorem prefixTable_mul_wordS {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    prefixTable source target * leavittWordS (source.word i) =
      leavittWordS (target.word i) := by
  classical
  calc
    prefixTable source target * leavittWordS (source.word i) =
        ∑ j, leavittWordS (target.word j) *
          (leavittWordT (source.word j) * leavittWordS (source.word i)) := by
            simp only [prefixTable, Finset.sum_mul, mul_assoc]
    _ = leavittWordS (target.word i) := by
      simp only [binaryPrefixCode_orthogonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ,
        ↓reduceIte]

private theorem wordT_mul_prefixTable {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    leavittWordT (target.word i) * prefixTable source target =
      leavittWordT (source.word i) := by
  classical
  calc
    leavittWordT (target.word i) * prefixTable source target =
        ∑ j, (leavittWordT (target.word i) *
          leavittWordS (target.word j)) * leavittWordT (source.word j) := by
            simp only [prefixTable, Finset.mul_sum, mul_assoc]
    _ = leavittWordT (source.word i) := by
      simp only [binaryPrefixCode_orthogonal, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ,
        ↓reduceIte]

private theorem leavittWordS_split (a : List (Fin 2)) :
    leavittWordS a =
      leavittWordS (a ++ [0]) * leavittT 0 +
        leavittWordS (a ++ [1]) * leavittT 1 := by
  calc
    leavittWordS a = leavittWordS a *
        (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) := by
          rw [leavitt_partition]
          simp only [mul_one]
    _ = leavittWordS (a ++ [0]) * leavittT 0 +
        leavittWordS (a ++ [1]) * leavittT 1 := by
          simp only [Fin.isValue, mul_add, leavittWordS_append, leavittWordS, mul_one, mul_assoc]

private theorem leavittWordT_split (a : List (Fin 2)) :
    leavittWordT a =
      leavittS 0 * leavittWordT (a ++ [0]) +
        leavittS 1 * leavittWordT (a ++ [1]) := by
  calc
    leavittWordT a =
        (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) *
          leavittWordT a := by
            rw [leavitt_partition]
            simp only [one_mul]
    _ = leavittS 0 * leavittWordT (a ++ [0]) +
        leavittS 1 * leavittWordT (a ++ [1]) := by
          simp only [Fin.isValue, add_mul, mul_assoc, leavittWordT_append, leavittWordT, one_mul]

private def betaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 1, by omega⟩

private def nuNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2, by omega⟩

@[simp] private theorem nineWord_betaNineIndex (i : Fin 3) :
    nineWord (betaNineIndex i) = betaWord i := by
  fin_cases i <;> rfl

@[simp] private theorem nineWord_nuNineIndex (i : Fin 3) :
    nineWord (nuNineIndex i) = nuWord i := by
  fin_cases i <;> rfl

@[simp] private theorem uWord_betaNineIndex (i : Fin 3) :
    uWord (betaNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl

@[simp] private theorem vWord_nuNineIndex (i : Fin 3) :
    vWord (nuNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl

private theorem compressionU_inv_mul_alphaWordS (i : Fin 3) :
    (↑(compressionU⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
      leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (betaWord i) * leavittT 1 := by
  calc
    (↑(compressionU⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
        (↑(compressionU⁻¹) : BinaryLeavitt) *
          (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
            leavittWordS (alphaWord i ++ [1]) * leavittT 1) :=
      congrArg ((↑(compressionU⁻¹) : BinaryLeavitt) * ·)
        (leavittWordS_split (alphaWord i))
    _ = (prefixTable uPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [0])) * leavittT 0 +
        (prefixTable uPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [1])) * leavittT 1 := by
            change
              prefixTable uPrefixCode ninePrefixCode *
                  (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
                    leavittWordS (alphaWord i ++ [1]) * leavittT 1) = _
            simp only [Fin.isValue, mul_add, mul_assoc]
    _ = leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (betaWord i) * leavittT 1 := by
          simpa only [ninePrefixCode, uPrefixCode, nineWord_alphaNineIndex,
            nineWord_betaNineIndex, uWord_alphaNineIndex, uWord_betaNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (· * leavittT 0)
                (prefixTable_mul_wordS uPrefixCode ninePrefixCode
                  (alphaNineIndex i)))
              (congrArg (· * leavittT 1)
                (prefixTable_mul_wordS uPrefixCode ninePrefixCode
                  (betaNineIndex i)))

private theorem alphaWordT_mul_compressionU (i : Fin 3) :
    leavittWordT (alphaWord i) * (compressionU : BinaryLeavitt) =
      leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (betaWord i) := by
  calc
    leavittWordT (alphaWord i) * (compressionU : BinaryLeavitt) =
        (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
          leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
          (compressionU : BinaryLeavitt) :=
      congrArg (· * (compressionU : BinaryLeavitt))
        (leavittWordT_split (alphaWord i))
    _ = leavittS 0 * (leavittWordT (alphaWord i ++ [0]) *
          prefixTable ninePrefixCode uPrefixCode) +
        leavittS 1 * (leavittWordT (alphaWord i ++ [1]) *
          prefixTable ninePrefixCode uPrefixCode) := by
            change
              (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
                leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
                prefixTable ninePrefixCode uPrefixCode = _
            simp only [Fin.isValue, add_mul, mul_assoc]
    _ = leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (betaWord i) := by
          simpa only [ninePrefixCode, uPrefixCode, nineWord_alphaNineIndex,
            nineWord_betaNineIndex, uWord_alphaNineIndex, uWord_betaNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (leavittS 0 * ·)
                (wordT_mul_prefixTable ninePrefixCode uPrefixCode
                  (alphaNineIndex i)))
              (congrArg (leavittS 1 * ·)
                (wordT_mul_prefixTable ninePrefixCode uPrefixCode
                  (betaNineIndex i)))

private def alphaBetaNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + p.val, by omega⟩

private theorem alphaBetaNineIndex_ne {i j : Fin 3} (hij : i ≠ j)
    (p q : Fin 2) : alphaBetaNineIndex p i ≠ alphaBetaNineIndex q j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + p.val = 3 * j.val + q.val at hv
  omega

@[simp] private theorem nineWord_alphaBetaNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaBetaNineIndex p i) =
      if p = 0 then alphaWord i else betaWord i := by
  fin_cases p <;> fin_cases i <;> rfl

private theorem binaryBlockSandwich
    (x₀ x₁ y₀ y₁ a : BinaryLeavitt) (p q : Fin 2) :
    (x₀ * leavittT 0 + x₁ * leavittT 1) *
        (leavittS p * a * leavittT q) *
        (leavittS 0 * y₀ + leavittS 1 * y₁) =
      (if p = 0 then x₀ else x₁) * a *
        (if q = 0 then y₀ else y₁) := by
  have hact (r s : Fin 2) (x : BinaryLeavitt) :
      leavittT r * (leavittS s * x) = if r = s then x else 0 := by
    rw [← mul_assoc, leavittT_mul_S]
    split <;> simp
  fin_cases p <;> fin_cases q <;>
    simp [add_mul, mul_add, mul_assoc, hact]

private theorem alphaBetaRoot_mem_sourceGenerated
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 2) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode
      (alphaBetaNineIndex p i) (alphaBetaNineIndex q j)
      (alphaBetaNineIndex_ne hij p q) a ∈ sourceGeneratedGroup := by
  have hα := alphaRoot_mem_sourceGenerated i j hij
    (leavittS p * a * leavittT q)
  have hU := compressionU_mem_sourceGenerated
  have hconj :
      compressionU⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionU ∈
        sourceGeneratedGroup :=
    sourceGeneratedGroup.mul_mem
      (sourceGeneratedGroup.mul_mem (sourceGeneratedGroup.inv_mem hU) hα) hU
  have heq :
      compressionU⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionU =
        prefixElementaryUnit ninePrefixCode
          (alphaBetaNineIndex p i) (alphaBetaNineIndex q j)
          (alphaBetaNineIndex_ne hij p q) a := by
    apply Units.ext
    change
      (↑(compressionU⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionU : BinaryLeavitt) =
        1 + leavittWordS (nineWord (alphaBetaNineIndex p i)) * a *
          leavittWordT (nineWord (alphaBetaNineIndex q j))
    calc
      (↑(compressionU⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionU : BinaryLeavitt) =
        1 + ((↑(compressionU⁻¹) : BinaryLeavitt) *
            leavittWordS (alphaWord i)) *
          (leavittS p * a * leavittT q) *
          (leavittWordT (alphaWord j) * (compressionU : BinaryLeavitt)) := by
            simp only [mul_assoc, mul_add, mul_one, add_mul, Units.inv_mul]
      _ = 1 +
          (leavittWordS (alphaWord i) * leavittT 0 +
            leavittWordS (betaWord i) * leavittT 1) *
          (leavittS p * a * leavittT q) *
          (leavittS 0 * leavittWordT (alphaWord j) +
            leavittS 1 * leavittWordT (betaWord j)) := by
              rw [compressionU_inv_mul_alphaWordS,
                alphaWordT_mul_compressionU]
      _ = 1 + leavittWordS (nineWord (alphaBetaNineIndex p i)) * a *
          leavittWordT (nineWord (alphaBetaNineIndex q j)) := by
            rw [binaryBlockSandwich]
            simp only [nineWord_alphaBetaNineIndex]
            split_ifs <;> rfl
  exact heq ▸ hconj

private def prefixElementaryEntry {ι : Type*} (E : BinaryPrefixCode ι)
    (i j : ι) (a : BinaryLeavitt) : BinaryLeavitt :=
  leavittWordS (E.word i) * a * leavittWordT (E.word j)

private theorem prefixElementaryEntry_mul {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j k l : ι)
    (a b : BinaryLeavitt) :
    prefixElementaryEntry E i j a * prefixElementaryEntry E k l b =
      if j = k then prefixElementaryEntry E i l (a * b) else 0 := by
  calc
    prefixElementaryEntry E i j a * prefixElementaryEntry E k l b =
        leavittWordS (E.word i) * a *
          (leavittWordT (E.word j) * leavittWordS (E.word k)) *
          b * leavittWordT (E.word l) := by
            simp only [prefixElementaryEntry, mul_assoc]
    _ = if j = k then prefixElementaryEntry E i l (a * b) else 0 := by
      rw [binaryPrefixCode_orthogonal E j k]
      split <;> simp [prefixElementaryEntry, mul_assoc]

private theorem prefixElementaryUnit_commutator {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : BinaryLeavitt) :
    ⁅prefixElementaryUnit E i j hij a,
      prefixElementaryUnit E j k hjk b⁆ =
      prefixElementaryUnit E i k hik (a * b) := by
  let x := prefixElementaryEntry E i j a
  let y := prefixElementaryEntry E j k b
  let z := prefixElementaryEntry E i k (a * b)
  have hxx : x * x = 0 := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hij.symm]
  have hyy : y * y = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E j k b = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hjk.symm]
  have hyx : y * x = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hik.symm]
  have hxy : x * y = z := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E j k b =
      prefixElementaryEntry E i k (a * b)
    rw [prefixElementaryEntry_mul, ite_eq_left rfl]
  have hzx : z * x = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E i j a = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hik.symm]
  have hzy : z * y = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E j k b = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hjk.symm]
  have hzz : z * z = 0 := by
    change prefixElementaryEntry E i k (a * b) *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hik.symm]
  have hxz : x * z = 0 := by
    change prefixElementaryEntry E i j a *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hij.symm]
  have hyz : y * z = 0 := by
    change prefixElementaryEntry E j k b *
      prefixElementaryEntry E i k (a * b) = 0
    rw [prefixElementaryEntry_mul, ite_eq_right hik.symm]
  apply Units.ext
  change (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + z
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz, hxz, hyz]

private theorem prefixElementaryUnit_mem_of_two_step
    {ι : Type*} [DecidableEq ι] (E : BinaryPrefixCode ι)
    (H : Subgroup BinaryLeavittˣ) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : BinaryLeavitt)
    (hleft : prefixElementaryUnit E i j hij a ∈ H)
    (hright : prefixElementaryUnit E j k hjk 1 ∈ H) :
    prefixElementaryUnit E i k hik a ∈ H := by
  have hc :
      ⁅prefixElementaryUnit E i j hij a,
        prefixElementaryUnit E j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem
      (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [prefixElementaryUnit_commutator E i j k hij hjk hik a 1] at hc
  simpa only [mul_one] using hc

private theorem prefixElementaryGroup_le_of_hub
    {ι : Type*} [DecidableEq ι] (E : BinaryPrefixCode ι)
    (H : Subgroup BinaryLeavittˣ) (k : ι)
    (hto : ∀ (i : ι) (h : i ≠ k) (a : BinaryLeavitt),
      prefixElementaryUnit E i k h a ∈ H)
    (hfrom : ∀ (j : ι) (h : k ≠ j) (a : BinaryLeavitt),
      prefixElementaryUnit E k j h a ∈ H) :
    prefixElementaryGroup E ≤ H := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  by_cases hi : i = k
  · subst k
    exact hfrom j hij a
  by_cases hj : j = k
  · subst k
    exact hto i hij a
  exact prefixElementaryUnit_mem_of_two_step E H i k j
    hi (Ne.symm hj) hij a (hto i hi a) (hfrom j (Ne.symm hj) 1)

private theorem compressionV_inv_mul_alphaWordS (i : Fin 3) :
    (↑(compressionV⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
      leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (nuWord i) * leavittT 1 := by
  calc
    (↑(compressionV⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
        (↑(compressionV⁻¹) : BinaryLeavitt) *
          (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
            leavittWordS (alphaWord i ++ [1]) * leavittT 1) :=
      congrArg ((↑(compressionV⁻¹) : BinaryLeavitt) * ·)
        (leavittWordS_split (alphaWord i))
    _ = (prefixTable vPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [0])) * leavittT 0 +
        (prefixTable vPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [1])) * leavittT 1 := by
            change
              prefixTable vPrefixCode ninePrefixCode *
                  (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
                    leavittWordS (alphaWord i ++ [1]) * leavittT 1) = _
            simp only [Fin.isValue, mul_add, mul_assoc]
    _ = leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (nuWord i) * leavittT 1 := by
          simpa only [ninePrefixCode, vPrefixCode, nineWord_alphaNineIndex,
            nineWord_nuNineIndex, vWord_alphaNineIndex, vWord_nuNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (· * leavittT 0)
                (prefixTable_mul_wordS vPrefixCode ninePrefixCode
                  (alphaNineIndex i)))
              (congrArg (· * leavittT 1)
                (prefixTable_mul_wordS vPrefixCode ninePrefixCode
                  (nuNineIndex i)))

private theorem alphaWordT_mul_compressionV (i : Fin 3) :
    leavittWordT (alphaWord i) * (compressionV : BinaryLeavitt) =
      leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (nuWord i) := by
  calc
    leavittWordT (alphaWord i) * (compressionV : BinaryLeavitt) =
        (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
          leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
          (compressionV : BinaryLeavitt) :=
      congrArg (· * (compressionV : BinaryLeavitt))
        (leavittWordT_split (alphaWord i))
    _ = leavittS 0 * (leavittWordT (alphaWord i ++ [0]) *
          prefixTable ninePrefixCode vPrefixCode) +
        leavittS 1 * (leavittWordT (alphaWord i ++ [1]) *
          prefixTable ninePrefixCode vPrefixCode) := by
            change
              (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
                leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
                prefixTable ninePrefixCode vPrefixCode = _
            simp only [Fin.isValue, add_mul, mul_assoc]
    _ = leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (nuWord i) := by
          simpa only [ninePrefixCode, vPrefixCode, nineWord_alphaNineIndex,
            nineWord_nuNineIndex, vWord_alphaNineIndex, vWord_nuNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (leavittS 0 * ·)
                (wordT_mul_prefixTable ninePrefixCode vPrefixCode
                  (alphaNineIndex i)))
              (congrArg (leavittS 1 * ·)
                (wordT_mul_prefixTable ninePrefixCode vPrefixCode
                  (nuNineIndex i)))

private def alphaNuNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2 * p.val, by omega⟩

private theorem alphaNuNineIndex_ne {i j : Fin 3} (hij : i ≠ j)
    (p q : Fin 2) : alphaNuNineIndex p i ≠ alphaNuNineIndex q j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 2 * p.val = 3 * j.val + 2 * q.val at hv
  omega

@[simp] private theorem nineWord_alphaNuNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaNuNineIndex p i) =
      if p = 0 then alphaWord i else nuWord i := by
  fin_cases p <;> fin_cases i <;> rfl

private theorem alphaNuRoot_mem_sourceGenerated
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 2) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode
      (alphaNuNineIndex p i) (alphaNuNineIndex q j)
      (alphaNuNineIndex_ne hij p q) a ∈ sourceGeneratedGroup := by
  have hα := alphaRoot_mem_sourceGenerated i j hij
    (leavittS p * a * leavittT q)
  have hV := compressionV_mem_sourceGenerated
  have hconj :
      compressionV⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionV ∈
        sourceGeneratedGroup :=
    sourceGeneratedGroup.mul_mem
      (sourceGeneratedGroup.mul_mem (sourceGeneratedGroup.inv_mem hV) hα) hV
  have heq :
      compressionV⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionV =
        prefixElementaryUnit ninePrefixCode
          (alphaNuNineIndex p i) (alphaNuNineIndex q j)
          (alphaNuNineIndex_ne hij p q) a := by
    apply Units.ext
    change
      (↑(compressionV⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionV : BinaryLeavitt) =
        1 + leavittWordS (nineWord (alphaNuNineIndex p i)) * a *
          leavittWordT (nineWord (alphaNuNineIndex q j))
    calc
      (↑(compressionV⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionV : BinaryLeavitt) =
        1 + ((↑(compressionV⁻¹) : BinaryLeavitt) *
            leavittWordS (alphaWord i)) *
          (leavittS p * a * leavittT q) *
          (leavittWordT (alphaWord j) * (compressionV : BinaryLeavitt)) := by
            simp only [mul_assoc, mul_add, mul_one, add_mul, Units.inv_mul]
      _ = 1 +
          (leavittWordS (alphaWord i) * leavittT 0 +
            leavittWordS (nuWord i) * leavittT 1) *
          (leavittS p * a * leavittT q) *
          (leavittS 0 * leavittWordT (alphaWord j) +
            leavittS 1 * leavittWordT (nuWord j)) := by
              rw [compressionV_inv_mul_alphaWordS,
                alphaWordT_mul_compressionV]
      _ = 1 + leavittWordS (nineWord (alphaNuNineIndex p i)) * a *
          leavittWordT (nineWord (alphaNuNineIndex q j)) := by
            rw [binaryBlockSandwich]
            simp only [nineWord_alphaNuNineIndex]
            split_ifs <;> rfl
  exact heq ▸ hconj

private theorem nineRoot_to_alphaHub_mem_sourceGenerated
    (i : Fin 9) (hi : i ≠ 0) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode i 0 hi a ∈ sourceGeneratedGroup := by
  fin_cases i
  · exact (hi rfl).elim
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 1 3 0
      (by decide) (by decide) hi a
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero,
          Nat.mod_succ,
          zero_add, Fin.mk_one, Nat.one_mod, mul_one, add_zero, Fin.reduceFinMk] using
          alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin
            2) a)
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.one_mod, mul_one,
          Nat.zero_mod,
          add_zero, Fin.reduceFinMk, mul_zero, Fin.zero_eta] using
          alphaBetaRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin
            2) (1 : BinaryLeavitt))
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 2 3 0
      (by decide) (by decide) hi a
      (by
        simpa only [Fin.isValue, alphaNuNineIndex, Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero,
          Nat.mod_succ,
          mul_one, zero_add, Fin.reduceFinMk, Nat.one_mod, add_zero] using
          alphaNuRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin
            2) a)
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.one_mod, mul_one,
          Nat.zero_mod,
          add_zero, Fin.reduceFinMk, mul_zero, Fin.zero_eta] using
          alphaBetaRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin
            2) (1 : BinaryLeavitt))
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.one_mod, mul_one, Nat.zero_mod, add_zero, mul_zero, Fin.zero_eta] using
      alphaBetaRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.one_mod, mul_one, Nat.mod_succ, Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta] using
      alphaBetaRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaNuNineIndex, Fin.coe_ofNat_eq_mod,
    Nat.one_mod,
      mul_one, Nat.mod_succ, Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta] using
      alphaNuRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin 2) a
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, Nat.reduceMul, Nat.zero_mod, add_zero, mul_zero, Fin.zero_eta] using
      alphaBetaRoot_mem_sourceGenerated (2 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, Nat.reduceMul, Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta] using
      alphaBetaRoot_mem_sourceGenerated (2 : Fin 3) (0 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, alphaNuNineIndex, Fin.coe_ofNat_eq_mod,
    Nat.mod_succ,
      Nat.reduceMul, mul_one, Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta] using
      alphaNuRoot_mem_sourceGenerated (2 : Fin 3) (0 : Fin 3) (by decide) (1 : Fin 2) (0 : Fin 2) a

private theorem nineRoot_from_alphaHub_mem_sourceGenerated
    (i : Fin 9) (hi : (0 : Fin 9) ≠ i) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode 0 i hi a ∈ sourceGeneratedGroup := by
  fin_cases i
  · exact (hi rfl).elim
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 0 3 1
      (by decide) (by decide) hi a
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero,
          add_zero,
          Fin.zero_eta, Nat.one_mod, mul_one, Fin.reduceFinMk] using
          alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin
            2) a)
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.one_mod, mul_one,
          Nat.zero_mod,
          add_zero, Fin.reduceFinMk, mul_zero, Nat.mod_succ, zero_add, Fin.mk_one] using
          alphaBetaRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin
            2) (1 : BinaryLeavitt))
  · exact prefixElementaryUnit_mem_of_two_step
      ninePrefixCode sourceGeneratedGroup 0 3 2
      (by decide) (by decide) hi a
      (by
        simpa only [Fin.isValue, alphaBetaNineIndex, Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero,
          add_zero,
          Fin.zero_eta, Nat.one_mod, mul_one, Fin.reduceFinMk] using
          alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin
            2) a)
      (by
        simpa only [Fin.isValue, alphaNuNineIndex, Fin.coe_ofNat_eq_mod, Nat.one_mod, mul_one,
          Nat.zero_mod, mul_zero,
          add_zero, Fin.reduceFinMk, Nat.mod_succ, zero_add] using
          alphaNuRoot_mem_sourceGenerated (1 : Fin 3) (0 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin
            2) (1 : BinaryLeavitt))
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta, Nat.one_mod, mul_one] using
      alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta, Nat.one_mod, mul_one, Nat.mod_succ] using
      alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin 2)
        a
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaNuNineIndex, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod,
      mul_zero, add_zero, Fin.zero_eta, Nat.one_mod, mul_one, Nat.mod_succ] using
      alphaNuRoot_mem_sourceGenerated (0 : Fin 3) (1 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin 2) a
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta, Nat.mod_succ, Nat.reduceMul] using
      alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (2 : Fin 3) (by decide) (0 : Fin 2) (0 : Fin 2)
        a
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaBetaNineIndex,
    Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, mul_zero, add_zero, Fin.zero_eta, Nat.mod_succ, Nat.reduceMul] using
      alphaBetaRoot_mem_sourceGenerated (0 : Fin 3) (2 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin 2)
        a
  · simpa only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, alphaNuNineIndex, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod,
      mul_zero, add_zero, Fin.zero_eta, Nat.mod_succ, Nat.reduceMul, mul_one] using
      alphaNuRoot_mem_sourceGenerated (0 : Fin 3) (2 : Fin 3) (by decide) (0 : Fin 2) (1 : Fin 2) a

private theorem ninePrefixElementaryGroup_le_sourceGenerated :
    prefixElementaryGroup ninePrefixCode ≤ sourceGeneratedGroup :=
  prefixElementaryGroup_le_of_hub ninePrefixCode sourceGeneratedGroup
    (0 : Fin 9) nineRoot_to_alphaHub_mem_sourceGenerated
    nineRoot_from_alphaHub_mem_sourceGenerated

private theorem alphaNineIndex_ne {i j : Fin 3} (hij : i ≠ j) :
    alphaNineIndex i ≠ alphaNineIndex j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val at hv
  omega

private theorem alphaPrefixElementaryUnit_eq_nine
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a =
      prefixElementaryUnit ninePrefixCode
        (alphaNineIndex i) (alphaNineIndex j)
        (alphaNineIndex_ne hij) a := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j) =
      1 + leavittWordS (nineWord (alphaNineIndex i)) * a *
        leavittWordT (nineWord (alphaNineIndex j))
  rw [nineWord_alphaNineIndex, nineWord_alphaNineIndex]

public
theorem alphaPrefixElementaryGroup_le_nine :
    prefixElementaryGroup alphaPrefixCode ≤
      prefixElementaryGroup ninePrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaPrefixElementaryUnit_eq_nine]
  exact Subgroup.subset_closure
    ⟨alphaNineIndex i, alphaNineIndex j, alphaNineIndex_ne hij, a, rfl⟩

private theorem sourceGeneratedGroup_le_nine_of_compressions
    (hu : compressionU ∈ prefixElementaryGroup ninePrefixCode)
    (hv : compressionV ∈ prefixElementaryGroup ninePrefixCode) :
    sourceGeneratedGroup ≤ prefixElementaryGroup ninePrefixCode := by
  rw [sourceGeneratedGroup, Subgroup.closure_le]
  intro z hz
  rcases hz with hz | hz
  · exact alphaPrefixElementaryGroup_le_nine hz
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv

private theorem sourceGeneratedGroup_eq_nine_of_compressions
    (hu : compressionU ∈ prefixElementaryGroup ninePrefixCode)
    (hv : compressionV ∈ prefixElementaryGroup ninePrefixCode) :
    sourceGeneratedGroup = prefixElementaryGroup ninePrefixCode :=
  le_antisymm (sourceGeneratedGroup_le_nine_of_compressions hu hv)
    ninePrefixElementaryGroup_le_sourceGenerated

end SourceGeneration

private theorem binaryLeavittMatrixUnitSubgroup_countable (n : ℕ)
    (H : Subgroup (Matrix (Fin n) (Fin n) BinaryLeavitt)ˣ) : Countable H := by
  let : Countable (Matrix (Fin n) (Fin n) BinaryLeavitt) :=
    Countable.of_equiv (Fin n → Fin n → BinaryLeavitt)
      (Matrix.of : (Fin n → Fin n → BinaryLeavitt) ≃
        Matrix (Fin n) (Fin n) BinaryLeavitt)
  have h : Function.Injective
      (fun x : H => (x.val.val : Matrix (Fin n) (Fin n) BinaryLeavitt)) := by
    intro x y hxy
    apply Subtype.ext
    exact Units.ext hxy
  exact h.countable

private instance binaryLeavittElementaryGroupCountable (n : ℕ) :
    Countable (binaryLeavittElementaryGroup n) :=
  binaryLeavittMatrixUnitSubgroup_countable n
    (elementaryGroup (Fin n) BinaryLeavitt)

private theorem binaryLeavittEL3_finitelyGenerated :
    Group.FG (binaryLeavittElementaryGroup 3) :=
  elementaryGroup_three_finitelyGenerated

public
theorem binaryLeavittEL3_infinite :
    Infinite (binaryLeavittElementaryGroup 3) :=
  elementaryGroup_infinite (R := BinaryLeavitt)
    (0 : Fin 3) (1 : Fin 3) (by decide)

public
theorem alphaPrefixElementaryGroup_finitelyGenerated :
    Group.FG (prefixElementaryGroup alphaPrefixCode) := by
  let : Group.FG (binaryLeavittElementaryGroup 3) :=
    binaryLeavittEL3_finitelyGenerated
  exact Group.fg_of_surjective
    (f := alphaPrefixElementaryGroupEquiv.toMonoidHom)
    alphaPrefixElementaryGroupEquiv.surjective

public
theorem ninePrefixElementaryGroup_countable :
    Countable (prefixElementaryGroup ninePrefixCode) :=
  ninePrefixElementaryGroupEquiv.symm.injective.countable

private noncomputable def midrankFirstMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) + midrankFirstMoment (a + p) ps

private noncomputable def midrankSecondMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) ^ 2 + midrankSecondMoment (a + p) ps

private theorem midrankFirstMoment_eq (a : ℝ) (ps : List ℝ) :
    midrankFirstMoment a ps = ((a + ps.sum) ^ 2 - a ^ 2) / 2 := by
  induction ps generalizing a with
  | nil => simp only [midrankFirstMoment, List.sum_nil, add_zero, sub_self, zero_div]
  | cons p ps ih =>
      simp only [midrankFirstMoment, List.sum_cons]
      rw [ih (a + p)]
      ring

private theorem midrankSecondMoment_eq (a : ℝ) (ps : List ℝ) :
    midrankSecondMoment a ps =
      ((a + ps.sum) ^ 3 - a ^ 3) / 3 -
        (ps.map fun p => p ^ 3).sum / 12 := by
  induction ps generalizing a with
  | nil => simp only [midrankSecondMoment, List.sum_nil, add_zero, sub_self, zero_div, List.map_nil]
  | cons p ps ih =>
      simp only [midrankSecondMoment, List.sum_cons, List.map_cons]
      rw [ih (a + p)]
      ring

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def midrankVariance (ps : List ℝ) : ℝ :=
  midrankSecondMoment 0 ps - (midrankFirstMoment 0 ps) ^ 2

private theorem midrankVariance_eq (ps : List ℝ) (hsum : ps.sum = 1) :
    midrankVariance ps = (1 - (ps.map fun p => p ^ 3).sum) / 12 := by
  unfold midrankVariance
  rw [midrankSecondMoment_eq, midrankFirstMoment_eq, hsum]
  ring

private theorem cubeSum_le_dominant_mul_sum (ps : List ℝ) (m : ℝ)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hone : ∀ p ∈ ps, p ≤ 1)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (ps.map fun p => p ^ 3).sum ≤ m * ps.sum := by
  induction ps with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, Std.le_refl]
  | cons p ps ih =>
      have hp : 0 ≤ p := hpos p (by simp only [List.mem_cons, true_or])
      have hpone : p ≤ 1 := hone p (by simp only [List.mem_cons, true_or])
      have hpm : p ≤ m := hdom p (by simp only [List.mem_cons, true_or])
      have hsq : p * p ≤ m := calc
        p * p ≤ p * 1 := mul_le_mul_of_nonneg_left hpone hp
        _ = p := by ring
        _ ≤ m := hpm
      have hcube : p ^ 3 ≤ m * p := calc
        p ^ 3 = (p * p) * p := by ring
        _ ≤ m * p := mul_le_mul_of_nonneg_right hsq hp
      have htailpos : ∀ q ∈ ps, 0 ≤ q := by
        intro q hq
        exact hpos q (by simp only [List.mem_cons, hq, or_true])
      have htailone : ∀ q ∈ ps, q ≤ 1 := by
        intro q hq
        exact hone q (by simp only [List.mem_cons, hq, or_true])
      have htaildom : ∀ q ∈ ps, q ≤ m := by
        intro q hq
        exact hdom q (by simp only [List.mem_cons, hq, or_true])
      have htail := ih htailpos htailone htaildom
      simpa only [List.map_cons, List.sum_cons, mul_add, ge_iff_le] using add_le_add hcube htail

private theorem cube_sum_le_dominant_mass (ps : List ℝ) (m : ℝ)
    (hsum : ps.sum = 1)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (ps.map fun p => p ^ 3).sum ≤ m := by
  have hone : ∀ p ∈ ps, p ≤ (1 : ℝ) := by
    intro p hp
    have hsub : List.Sublist [p] ps := List.singleton_sublist.mpr hp
    have hle : ([p] : List ℝ).sum ≤ ps.sum :=
      hsub.sum_le_sum hpos
    simpa only [ge_iff_le, List.sum_cons, List.sum_nil, add_zero, hsum] using hle
  have h := cubeSum_le_dominant_mul_sum ps m hpos hone hdom
  simpa only [ge_iff_le, hsum, mul_one] using h

private theorem midrankVariance_controls_dominant_mass
    (ps : List ℝ) (m : ℝ)
    (hsum : ps.sum = 1)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (1 - m) / 12 ≤ midrankVariance ps := by
  rw [midrankVariance_eq ps hsum]
  have hcube := cube_sum_le_dominant_mass ps m hsum hpos hdom
  linarith

private theorem weighted_midrank_dominant_mass_le {ι : Type*}
    (I : Finset ι) (weight : ι → ℝ)
    (q : ι → List ℝ) (m : ι → ℝ)
    (hweight : ∀ i ∈ I, 0 ≤ weight i)
    (hsum : ∀ i ∈ I, (q i).sum = 1)
    (hpositive : ∀ i ∈ I, ∀ x ∈ q i, 0 ≤ x)
    (hdominant : ∀ i ∈ I, ∀ x ∈ q i, x ≤ m i) :
    (∑ i ∈ I, weight i * (1 - m i)) ≤
      12 * ∑ i ∈ I, weight i * midrankVariance (q i) := by
  calc
    (∑ i ∈ I, weight i * (1 - m i)) ≤
        ∑ i ∈ I, 12 * (weight i * midrankVariance (q i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hvar := midrankVariance_controls_dominant_mass
        (q i) (m i) (hsum i hi) (hpositive i hi) (hdominant i hi)
      have hpoint : 1 - m i ≤ 12 * midrankVariance (q i) := by
        linarith
      calc
        weight i * (1 - m i) ≤
            weight i * (12 * midrankVariance (q i)) :=
          mul_le_mul_of_nonneg_left hpoint (hweight i hi)
        _ = 12 * (weight i * midrankVariance (q i)) := by ring
    _ = 12 * ∑ i ∈ I, weight i * midrankVariance (q i) := by
      rw [Finset.mul_sum]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentRankMass {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ) : ℝ :=
  ((C.filter fun x => b x = j).card : ℝ) / (C.card : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentVertexMidrank {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) : ℝ :=
  (((C.filter fun z => b z < b x).card : ℝ) +
      ((C.filter fun z => b z = b x).card : ℝ) / 2) /
    (C.card : ℝ)

private theorem componentVertexMidrank_eq_sum_componentRankMass
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x =
      (∑ j ∈ (C.image b).filter (fun j => j < b x),
        componentRankMass C b j) + componentRankMass C b (b x) / 2 := by
  classical
  let J : Finset ℤ := (C.image b).filter fun j => j < b x
  have hfilter :
      C.filter (fun z => b z ∈ J) =
        C.filter (fun z => b z < b x) := by
    ext z
    simp only [Finset.mem_filter]
    dsimp [J]
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  have hcard :
      (∑ j ∈ J, (C.filter fun z => b z = j).card) =
        (C.filter fun z => b z < b x).card := by
    calc
      (∑ j ∈ J, (C.filter fun z => b z = j).card) =
          (C.filter fun z => b z ∈ J).card :=
        Finset.sum_card_fiberwise_eq_card_filter C J b
      _ = (C.filter fun z => b z < b x).card :=
        congrArg Finset.card hfilter
  have hcard' :
      (∑ j ∈ J, ((C.filter fun z => b z = j).card : ℝ)) =
        ((C.filter fun z => b z < b x).card : ℝ) := by
    exact_mod_cast hcard
  simp only [componentVertexMidrank, componentRankMass, ← Finset.sum_div]
  rw [show
    (∑ j ∈ (C.image b).filter (fun j => j < b x),
      ((C.filter fun z => b z = j).card : ℝ)) =
        ((C.filter fun z => b z < b x).card : ℝ) from by
      simpa only [J] using hcard']
  ring

private theorem componentRankMass_nonneg {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ) :
    0 ≤ componentRankMass C b j := by
  unfold componentRankMass
  positivity

private theorem sum_componentRankMass {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ j ∈ C.image b, componentRankMass C b j) = 1 := by
  have hcard :
      (∑ j ∈ C.image b, ((C.filter fun x => b x = j).card : ℝ)) =
        (C.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image b C).symm
  have hne : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hC)
  simp only [componentRankMass, ← Finset.sum_div]
  rw [hcard, div_self hne]

public
theorem componentVertexMidrank_nonneg {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    0 ≤ componentVertexMidrank C b x := by
  unfold componentVertexMidrank
  positivity

private theorem component_lower_equal_disjoint
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    Disjoint (C.filter fun z => b z < b x)
      (C.filter fun z => b z = b x) := by
  apply Finset.disjoint_left.mpr
  intro z hzlow hzeq
  have hlow := (Finset.mem_filter.mp hzlow).2
  have heq := (Finset.mem_filter.mp hzeq).2
  omega

public
theorem componentVertexMidrank_le_one {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x ≤ 1 := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp only [componentVertexMidrank, Finset.filter_empty, Finset.card_empty, CharP.cast_eq_zero,
    zero_div,
      add_zero, div_zero, zero_le_one]
  · have hc : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hdisj := component_lower_equal_disjoint C b x
    have hsub :
        (C.filter fun z => b z < b x) ∪
          (C.filter fun z => b z = b x) ⊆ C := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have hcard' :
        ((C.filter fun z => b z < b x).card : ℝ) +
          ((C.filter fun z => b z = b x).card : ℝ) ≤
            (C.card : ℝ) := by
      exact_mod_cast hcard
    unfold componentVertexMidrank
    apply (div_le_one hc).2
    have heq : 0 ≤ ((C.filter fun z => b z = b x).card : ℝ) := by
      positivity
    linarith

private theorem componentVertexMidrank_mono {V : Type*}
    (C : Finset V) (b : V → ℤ) {x y : V}
    (hxy : b x ≤ b y) :
    componentVertexMidrank C b x ≤ componentVertexMidrank C b y := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp only [componentVertexMidrank, Finset.filter_empty, Finset.card_empty, CharP.cast_eq_zero,
    zero_div,
      add_zero, div_zero, Std.le_refl]
  · have hc : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    rcases hxy.eq_or_lt with heq | hlt
    · unfold componentVertexMidrank
      simp only [heq, Std.le_refl]
    · have hdisj := component_lower_equal_disjoint C b x
      have hsub :
          (C.filter fun z => b z < b x) ∪
            (C.filter fun z => b z = b x) ⊆
              C.filter fun z => b z < b y := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzC, lt_trans hzx hlt⟩
        · obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzC, hzx.symm ▸ hlt⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      have hcard' :
          ((C.filter fun z => b z < b x).card : ℝ) +
            ((C.filter fun z => b z = b x).card : ℝ) ≤
              ((C.filter fun z => b z < b y).card : ℝ) := by
        exact_mod_cast hcard
      have hex : 0 ≤ ((C.filter fun z => b z = b x).card : ℝ) := by
        positivity
      have hey : 0 ≤ ((C.filter fun z => b z = b y).card : ℝ) := by
        positivity
      unfold componentVertexMidrank
      apply (div_le_div_iff_of_pos_right hc).2
      linarith

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentRankMassList {V : Type*}
    (C : Finset V) (b : V → ℤ) : List ℝ :=
  ((C.image b).sort (· ≤ ·)).map (componentRankMass C b)

private theorem sum_map_sort_eq {α : Type*}
    [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ a ∈ s, f a := by
  change
    ((s.sort (· ≤ ·)).map f).sum =
      (s.val.map f).sum
  have h := congrArg
    (fun t : Multiset α => (t.map f).sum)
    (s.sort_eq (· ≤ ·))
  simpa only [Multiset.map_coe, Multiset.sum_coe] using h

private theorem componentRankMassList_sum {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (componentRankMassList C b).sum = 1 := by
  unfold componentRankMassList
  rw [sum_map_sort_eq]
  exact sum_componentRankMass C b hC

private theorem componentRankMassList_nonneg {V : Type*}
    (C : Finset V) (b : V → ℤ) :
    ∀ p ∈ componentRankMassList C b, 0 ≤ p := by
  intro p hp
  unfold componentRankMassList at hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact componentRankMass_nonneg C b j

private theorem componentRankMassList_le_max {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ)
    (hmax : ∀ k ∈ C.image b,
      componentRankMass C b k ≤ componentRankMass C b j) :
    ∀ p ∈ componentRankMassList C b,
      p ≤ componentRankMass C b j := by
  intro p hp
  unfold componentRankMassList at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact hmax k (((C.image b).mem_sort (· ≤ ·)).mp hk)

public
theorem exists_maximal_componentRankMass
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    ∃ j ∈ C.image b,
      ∀ k ∈ C.image b,
        componentRankMass C b k ≤ componentRankMass C b j := by
  have himage : (C.image b).Nonempty := hC.image b
  obtain ⟨j, hj, hmax⟩ :=
    Finset.exists_max_image (C.image b) (componentRankMass C b) himage
  exact ⟨j, hj, hmax⟩

private theorem component_omitted_rank_card_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ)
    (hC : C.Nonempty) :
    ((C.card - (C.filter fun x => b x = j).card : ℕ) : ℝ) =
      (C.card : ℝ) * (1 - componentRankMass C b j) := by
  have hsub : (C.filter fun x => b x = j).card ≤ C.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hne : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  rw [Nat.cast_sub hsub]
  unfold componentRankMass
  field_simp [hne]

public
theorem actual_weighted_midrank_dominant_mass_le
    {V ι : Type*}
    (I : Finset ι) (C : ι → Finset V) (b : V → ℤ) (j : ι → ℤ)
    (hC : ∀ i ∈ I, (C i).Nonempty)
    (hmax : ∀ i ∈ I, ∀ k ∈ (C i).image b,
      componentRankMass (C i) b k ≤ componentRankMass (C i) b (j i)) :
    (∑ i ∈ I,
      (((C i).card - ((C i).filter fun x => b x = j i).card : ℕ) : ℝ)) ≤
      12 * ∑ i ∈ I,
        ((C i).card : ℝ) *
          midrankVariance (componentRankMassList (C i) b) := by
  calc
    (∑ i ∈ I,
        (((C i).card - ((C i).filter fun x => b x = j i).card : ℕ) : ℝ)) =
      ∑ i ∈ I,
        ((C i).card : ℝ) *
          (1 - componentRankMass (C i) b (j i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact component_omitted_rank_card_eq (C i) b (j i) (hC i hi)
    _ ≤ 12 * ∑ i ∈ I,
        ((C i).card : ℝ) *
          midrankVariance (componentRankMassList (C i) b) := by
      apply weighted_midrank_dominant_mass_le
        I (fun i => ((C i).card : ℝ))
        (fun i => componentRankMassList (C i) b)
        (fun i => componentRankMass (C i) b (j i))
      · intro i hi
        positivity
      · intro i hi
        exact componentRankMassList_sum (C i) b (hC i hi)
      · intro i hi
        exact componentRankMassList_nonneg (C i) b
      · intro i hi
        exact componentRankMassList_le_max (C i) b (j i) (hmax i hi)

private theorem exists_maximum_overlap_component
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∃ D ∈ Q.parts,
      ∀ E ∈ Q.parts, (C ∩ E).card ≤ (C ∩ D).card := by
  classical
  have hU : U.Nonempty := hC.mono hCU
  exact Finset.exists_max_image Q.parts
    (fun D : Finset V => (C ∩ D).card)
    (Q.parts_nonempty hU.ne_empty)

public
theorem sum_card_component_inter_partition
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) (hCU : C ⊆ U) :
    ∑ D ∈ Q.parts, (C ∩ D).card = C.card := by
  have h := sum_card_inter_partition Q C
  simpa only [Finset.inter_comm, Finset.inter_eq_right.mpr hCU] using h

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def maximumOverlapPart
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) : Finset V := by
  classical
  exact if h : C.Nonempty ∧ C ⊆ U then
    (exists_maximum_overlap_component Q C h.1 h.2).choose else ∅

public
theorem maximumOverlapPart_mem
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    maximumOverlapPart Q C ∈ Q.parts := by
  classical
  have h : C.Nonempty ∧ C ⊆ U := ⟨hC, hCU⟩
  simpa only [maximumOverlapPart, dite_eq_left h] using
    (exists_maximum_overlap_component Q C hC hCU).choose_spec.1

public
theorem maximumOverlapPart_maximal
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∀ E ∈ Q.parts,
      (C ∩ E).card ≤ (C ∩ maximumOverlapPart Q C).card := by
  classical
  have h : C.Nonempty ∧ C ⊆ U := ⟨hC, hCU⟩
  simpa only [maximumOverlapPart, dite_eq_left h] using
    (exists_maximum_overlap_component Q C hC hCU).choose_spec.2

namespace PrefixCompressionU

open scoped BigOperators

private def sourceCrossRoot (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j h
    (leavittWordS a * leavittWordT b)

private theorem sourceCrossRoot_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossRoot i j h a b ∈ prefixElementaryGroup ninePrefixCode :=
  Subgroup.subset_closure ⟨i, j, h,
    leavittWordS a * leavittWordT b, rfl⟩

@[simp] private theorem sourceCrossRoot_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossRoot i j h a b) : BinaryLeavitt) =
      1 + leavittWordS (nineWord i ++ a) *
        leavittWordT (nineWord j ++ b) := by
  change
    1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) = _
  rw [leavittWordS_append, leavittWordT_append]
  noncomm_ring

private def sourceCrossSwap (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  sourceCrossRoot i j h a b *
    sourceCrossRoot j i h.symm b a *
    sourceCrossRoot i j h a b

private theorem sourceCrossSwap_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossSwap i j h a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (sourceCrossRoot_mem i j h a b)
      (sourceCrossRoot_mem j i h.symm b a))
    (sourceCrossRoot_mem i j h a b)

private theorem sourceRefinementOrthogonal (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hz : leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa only [ninePrefixCode, h, ↓reduceIte] using binaryPrefixCode_orthogonal ninePrefixCode i j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hz]; simp only [mul_zero, zero_mul]

private theorem sourceCrossSwap_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord i ++ a) -
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord i ++ a) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hba : leavittWordT B * leavittWordS A = 0 :=
    sourceRefinementOrthogonal j i h.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = 0 := by rw [hba]; simp only [mul_zero, zero_mul]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) =
        leavittWordS A * leavittWordT A
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) * leavittWordT A := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT A := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    change
      (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS B * leavittWordT B
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS B * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQP : P * Q * P = P := by
    rw [hPQ]
    change
      (leavittWordS A * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  change
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q
  calc
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
        (1 + P) * (1 + Q) * (1 + P) := by
          simp only [sourceCrossSwap, Units.val_mul, sourceCrossRoot_val]
          rfl
    _ = 1 - P * Q - Q * P + P + Q :=
      cylinder_transposition_factorization P Q hPP hPQP
    _ = 1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q := by rw [hPQ, hQP]

private def refinedSourceWord : Fin 19 → List (Fin 2)
  | 0 => [0, 0, 0, 0]
  | 1 => [0, 0, 0, 1]
  | 2 => [1, 0, 0, 0, 0]
  | 3 => [1, 0, 0, 0, 1]
  | 4 => [1, 1, 0, 0, 0]
  | 5 => [1, 1, 0, 0, 1]
  | 6 => [0, 0, 1]
  | 7 => [1, 0, 0, 1, 0]
  | 8 => [1, 0, 0, 1, 1]
  | 9 => [1, 1, 0, 1]
  | 10 => [0, 1, 0, 0]
  | 11 => [0, 1, 0, 1]
  | 12 => [0, 1, 1]
  | 13 => [1, 0, 1, 0, 0]
  | 14 => [1, 0, 1, 0, 1]
  | 15 => [1, 0, 1, 1]
  | 16 => [1, 1, 1, 0, 0]
  | 17 => [1, 1, 1, 0, 1]
  | _ => [1, 1, 1, 1]

private def refinedSourcePrefixCode : BinaryPrefixCode (Fin 19) where
  word := refinedSourceWord
  prefix_free := by decide

private theorem refinedSourcePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (refinedSourcePrefixCode.word i))
      (fun i => leavittWordT (refinedSourcePrefixCode.word i)) = 1 := by
  have h000 :
      leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1] =
        leavittCylinder [0, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0, 0,
      0]).symm
  have h1000 :
      leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1] =
        leavittCylinder [1, 0, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0, 0]).symm
  have h1100 :
      leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1] =
        leavittCylinder [1, 1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      0, 0]).symm
  have h1001 :
      leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1] =
        leavittCylinder [1, 0, 0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0, 1]).symm
  have h010 :
      leavittCylinder [0, 1, 0, 0] +
          leavittCylinder [0, 1, 0, 1] =
        leavittCylinder [0, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0, 1,
      0]).symm
  have h01 :
      leavittCylinder [0, 1, 0] +
          leavittCylinder [0, 1, 1] =
        leavittCylinder [0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0,
      1]).symm
  have h1010 :
      leavittCylinder [1, 0, 1, 0, 0] +
          leavittCylinder [1, 0, 1, 0, 1] =
        leavittCylinder [1, 0, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      1, 0]).symm
  have h101 :
      leavittCylinder [1, 0, 1, 0] +
          leavittCylinder [1, 0, 1, 1] =
        leavittCylinder [1, 0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      1]).symm
  have h1110 :
      leavittCylinder [1, 1, 1, 0, 0] +
          leavittCylinder [1, 1, 1, 0, 1] =
        leavittCylinder [1, 1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      1, 0]).symm
  have h111 :
      leavittCylinder [1, 1, 1, 0] +
          leavittCylinder [1, 1, 1, 1] =
        leavittCylinder [1, 1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      1]).symm
  change (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) = 1
  calc
    (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) =
        (leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1]) +
        (leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1]) +
        (leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1]) +
        leavittCylinder [0, 0, 1] +
        (leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1]) +
        leavittCylinder [1, 1, 0, 1] +
        ((leavittCylinder [0, 1, 0, 0] +
            leavittCylinder [0, 1, 0, 1]) +
          leavittCylinder [0, 1, 1]) +
        ((leavittCylinder [1, 0, 1, 0, 0] +
            leavittCylinder [1, 0, 1, 0, 1]) +
          leavittCylinder [1, 0, 1, 1]) +
        ((leavittCylinder [1, 1, 1, 0, 0] +
            leavittCylinder [1, 1, 1, 0, 1]) +
          leavittCylinder [1, 1, 1, 1]) := by
            simp only [refinedSourceWord, Fin.isValue, Fin.sum_univ_succ,
              Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one,
              Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
              Fin.default_eq_zero, Finset.sum_singleton]
            ac_rfl
    _ = leavittCylinder [0, 0, 0] +
          leavittCylinder [1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0] +
          leavittCylinder [0, 0, 1] +
          leavittCylinder [1, 0, 0, 1] +
          leavittCylinder [1, 1, 0, 1] +
          leavittCylinder [0, 1] +
          leavittCylinder [1, 0, 1] +
          leavittCylinder [1, 1, 1] := by
            rw [h000, h1000, h1100, h1001, h010, h01,
              h1010, h101, h1110, h111]
    _ = ∑ i : Fin 9, leavittCylinder (nineWord i) := by
      simp only [Fin.isValue, nineWord, alphaWord, betaWord, nuWord,
        Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton]
      ac_rfl
    _ = 1 := ninePrefixCode_complete

private theorem completePrefixWord_ext {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (x y : BinaryLeavitt)
    (haction : ∀ i : ι,
      x * leavittWordS (E.word i) =
        y * leavittWordS (E.word i)) :
    x = y := by
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by rw [hcomplete]
    _ = ∑ i : ι,
        (x * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc x _ _).symm
    _ = ∑ i : ι,
        (y * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [haction i]
    _ = y * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_assoc y _ _
    _ = y := by rw [hcomplete, mul_one]

private theorem prefixTable_mul_sourceWord {ι : Type*}
    [Fintype ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    prefixTable source target * leavittWordS (source.word i) =
      leavittWordS (target.word i) := by
  classical
  simp only [prefixTable, Finset.sum_mul, mul_assoc, binaryPrefixCode_orthogonal, mul_ite, mul_one,
    mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem compressionU_mul_nine_refinement
    (i : Fin 9) (r : List (Fin 2)) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (nineWord i ++ r) =
      leavittWordS (uWord i ++ r) := by
  rw [leavittWordS_append, leavittWordS_append]
  change
    prefixTable ninePrefixCode uPrefixCode *
        (leavittWordS (ninePrefixCode.word i) * leavittWordS r) =
      leavittWordS (uPrefixCode.word i) * leavittWordS r
  rw [← mul_assoc, prefixTable_mul_sourceWord]

private def refinedSourceParent : Fin 19 → Fin 9
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 4
  | 9 => 5
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 7
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | _ => 8

private def refinedSourceSuffix : Fin 19 → List (Fin 2)
  | 0 => [0]
  | 1 => [1]
  | 2 => [0]
  | 3 => [1]
  | 4 => [0]
  | 5 => [1]
  | 6 => []
  | 7 => [0]
  | 8 => [1]
  | 9 => []
  | 10 => [0, 0]
  | 11 => [0, 1]
  | 12 => [1]
  | 13 => [0, 0]
  | 14 => [0, 1]
  | 15 => [1]
  | 16 => [0, 0]
  | 17 => [0, 1]
  | _ => [1]

private def refinedTargetWord (i : Fin 19) : List (Fin 2) :=
  uWord (refinedSourceParent i) ++ refinedSourceSuffix i

private theorem refinedSourceWord_eq_parent_append (i : Fin 19) :
    refinedSourceWord i =
      nineWord (refinedSourceParent i) ++ refinedSourceSuffix i := by
  fin_cases i <;> decide

private theorem compressionU_mul_refinedSourceWord (i : Fin 19) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  rw [refinedSourceWord_eq_parent_append]
  exact compressionU_mul_nine_refinement
    (refinedSourceParent i) (refinedSourceSuffix i)

private def binaryWordCancellation (a b : List (Fin 2)) : BinaryLeavitt :=
  match a, b with
  | [], b => leavittWordS b
  | a, [] => leavittWordT a
  | i :: a, j :: b =>
      if i = j then binaryWordCancellation a b else 0

private theorem leavittWordT_mul_wordS_cancel (a b : List (Fin 2)) :
    leavittWordT a * leavittWordS b =
      binaryWordCancellation a b := by
  induction a generalizing b with
  | nil => simp only [leavittWordT, one_mul, binaryWordCancellation]
  | cons i a ih =>
      cases b with
      | nil => simp only [leavittWordS, mul_one, binaryWordCancellation]
      | cons j b =>
          by_cases hij : i = j
          · subst j
            change
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                if i = i then binaryWordCancellation a b else 0
            rw [ite_eq_left rfl]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS i) * leavittWordS b) := by
                    noncomm_ring
              _ = binaryWordCancellation a b := by
                rw [leavittT_mul_S]
                simpa only [↓reduceIte, one_mul] using ih b
          · change
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                if i = j then binaryWordCancellation a b else 0
            rw [ite_eq_right hij]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS j) * leavittWordS b) := by
                    noncomm_ring
              _ = 0 := by rw [leavittT_mul_S]; simp only [hij, ↓reduceIte, zero_mul, mul_zero]

private theorem leavittWordS_mul_wordS (a b : List (Fin 2)) :
    leavittWordS a * leavittWordS b = leavittWordS (a ++ b) :=
  (leavittWordS_append a b).symm

private theorem sourceCrossSwap_mul_leavittWordS
    (i j : Fin 9) (h : i ≠ j)
    (a b x : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) * leavittWordS x =
      leavittWordS x -
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord i ++ a) x -
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord i ++ a) x := by
  rw [sourceCrossSwap_val]
  simp only [sub_mul, add_mul, one_mul, mul_assoc,
    leavittWordT_mul_wordS_cancel]

private def sourceUChronologicalSwaps : List BinaryLeavittˣ :=
  [sourceCrossSwap 0 1 (by decide) [0] [],
   sourceCrossSwap 0 4 (by decide) [1] [],
   sourceCrossSwap 3 7 (by decide) [] [],
   sourceCrossSwap 6 2 (by decide) [0, 0] [],
   sourceCrossSwap 6 5 (by decide) [0, 1] [],
   sourceCrossSwap 6 8 (by decide) [1] [],
   sourceCrossSwap 3 6 (by decide) [] [0],
   sourceCrossSwap 1 0 (by decide) [] [0, 0],
   sourceCrossSwap 4 0 (by decide) [] [0, 1],
   sourceCrossSwap 1 0 (by decide) [] [1, 0],
   sourceCrossSwap 4 0 (by decide) [] [1, 1],
   sourceCrossSwap 3 1 (by decide) [0, 0] [],
   sourceCrossSwap 3 4 (by decide) [0, 1] [],
   sourceCrossSwap 7 3 (by decide) [] [0],
   sourceCrossSwap 7 3 (by decide) [] [1],
   sourceCrossSwap 2 6 (by decide) [] [0, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [0, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [0, 1],
   sourceCrossSwap 2 6 (by decide) [] [1, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [1, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [1, 1]]

private def elementaryCompressionU : BinaryLeavittˣ :=
  sourceUChronologicalSwaps.reverse.prod

private theorem elementaryCompressionU_mem :
    elementaryCompressionU ∈ prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [List.mem_reverse, sourceUChronologicalSwaps,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h <;>
    subst x <;> exact sourceCrossSwap_mem _ _ _ _ _

private theorem elementaryCompressionU_mul_refinedSourceWord (i : Fin 19) :
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  fin_cases i <;>
    simp [elementaryCompressionU, sourceUChronologicalSwaps,
      sourceCrossSwap_mul_leavittWordS,
      refinedSourceWord, refinedTargetWord,
      refinedSourceParent, refinedSourceSuffix,
      nineWord, uWord, alphaWord, betaWord, nuWord, etaWord,
      binaryWordCancellation, leavittWordS_mul_wordS,
      List.prod_cons, mul_assoc]

private theorem elementaryCompressionU_eq_compressionU :
    elementaryCompressionU = compressionU := by
  apply Units.ext
  apply completePrefixWord_ext refinedSourcePrefixCode
    refinedSourcePrefixCode_complete
  intro i
  change
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i)
  rw [elementaryCompressionU_mul_refinedSourceWord,
    compressionU_mul_refinedSourceWord]

private theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← elementaryCompressionU_eq_compressionU]
  exact elementaryCompressionU_mem

end PrefixCompressionU

public
theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompressionU.compressionU_mem_ninePrefixElementaryGroup

namespace PrefixCompression

open scoped BigOperators

private theorem prefixTable_compose {ι : Type*} [Fintype ι]
    (source middle target : BinaryPrefixCode ι) :
    prefixTable middle target * prefixTable source middle =
      prefixTable source target := by
  classical
  change
    (∑ i, leavittWordS (target.word i) *
      leavittWordT (middle.word i)) *
      (∑ j, leavittWordS (middle.word j) *
        leavittWordT (source.word j)) =
      ∑ i, leavittWordS (target.word i) *
        leavittWordT (source.word i)
  calc
    (∑ i, leavittWordS (target.word i) *
        leavittWordT (middle.word i)) *
        (∑ j, leavittWordS (middle.word j) *
          leavittWordT (source.word j)) =
      ∑ i, ∑ j,
        leavittWordS (target.word i) *
          (leavittWordT (middle.word i) *
            leavittWordS (middle.word j)) *
          leavittWordT (source.word j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp only [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (source.word i) := by
      simp only [binaryPrefixCode_orthogonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]

private def compressionTransition : BinaryLeavittˣ :=
  prefixTableUnit uPrefixCode vPrefixCode
    uPrefixCode_complete vPrefixCode_complete

private theorem compressionV_eq_transition_mul :
    compressionV = compressionTransition * compressionU := by
  apply Units.ext
  change
    prefixTable ninePrefixCode vPrefixCode =
      prefixTable uPrefixCode vPrefixCode *
        prefixTable ninePrefixCode uPrefixCode
  exact (prefixTable_compose ninePrefixCode uPrefixCode vPrefixCode).symm

private def nineCrossRoot (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j hij
    (leavittWordS a * leavittWordT b)

private theorem nineCrossRoot_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossRoot i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩

private def nineCrossSwap (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  nineCrossRoot i j hij a b *
    nineCrossRoot j i hij.symm b a *
    nineCrossRoot i j hij a b

private theorem nineCrossSwap_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossSwap i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (nineCrossRoot_mem i j hij a b)
      (nineCrossRoot_mem j i hij.symm b a))
    (nineCrossRoot_mem i j hij a b)

private def compressionTransitionCrossSwaps : List BinaryLeavittˣ :=
  [nineCrossSwap 0 1 (by decide) [1, 0] [],
   nineCrossSwap 0 4 (by decide) [1, 1] [],
   nineCrossSwap 3 7 (by decide) [1] [],
   nineCrossSwap 6 2 (by decide) [1, 0, 0] [],
   nineCrossSwap 6 5 (by decide) [1, 0, 1] [],
   nineCrossSwap 6 8 (by decide) [1, 1] []]

private theorem compressionTransitionCrossSwaps_prod_mem :
    compressionTransitionCrossSwaps.prod ∈
      prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [compressionTransitionCrossSwaps, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h <;>
    subst x <;> exact nineCrossSwap_mem _ _ _ _ _

private def transpositionValue {A : Type*} [Ring A]
    (sa ta sb tb : A) : A :=
  1 - sa * ta - sb * tb + sa * tb + sb * ta

private theorem transpositionValue_refine {A : Type*} [Ring A]
    (sa ta sb tb p₀ q₀ p₁ q₁ : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (h₀₀ : q₀ * p₀ = 1) (h₁₁ : q₁ * p₁ = 1)
    (h₀₁ : q₀ * p₁ = 0) (h₁₀ : q₁ * p₀ = 0)
    (hpartition : p₀ * q₀ + p₁ * q₁ = 1) :
    transpositionValue (sa * p₀) (q₀ * ta) (sb * p₀) (q₀ * tb) *
        transpositionValue (sa * p₁) (q₁ * ta) (sb * p₁) (q₁ * tb) =
      transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have h₀₀' (x : A) : q₀ * (p₀ * x) = x := by
    rw [← mul_assoc, h₀₀, one_mul]
  have h₁₁' (x : A) : q₁ * (p₁ * x) = x := by
    rw [← mul_assoc, h₁₁, one_mul]
  have h₀₁' (x : A) : q₀ * (p₁ * x) = 0 := by
    rw [← mul_assoc, h₀₁, zero_mul]
  have h₁₀' (x : A) : q₁ * (p₀ * x) = 0 := by
    rw [← mul_assoc, h₁₀, zero_mul]
  have hpartition' (x : A) :
      p₀ * (q₀ * x) + p₁ * (q₁ * x) = x := by
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hpartition, one_mul]
  have hpartition_left (z x : A) :
      z * (p₀ * (q₀ * x)) + z * (p₁ * (q₁ * x)) = z * x := by
    rw [← mul_add, hpartition']
  unfold transpositionValue
  calc
    _ = 1 -
          (sa * (p₀ * (q₀ * ta)) + sa * (p₁ * (q₁ * ta))) -
          (sb * (p₀ * (q₀ * tb)) + sb * (p₁ * (q₁ * tb))) +
          (sa * (p₀ * (q₀ * tb)) + sa * (p₁ * (q₁ * tb))) +
          (sb * (p₀ * (q₀ * ta)) + sb * (p₁ * (q₁ * ta))) := by
            noncomm_ring [haa, hbb, hab, hba, h₀₀, h₁₁, h₀₁, h₁₀,
              haa', hbb', hab', hba', h₀₀', h₁₁', h₀₁', h₁₀']
    _ = _ := by
      rw [hpartition_left sa ta, hpartition_left sb tb,
        hpartition_left sa tb, hpartition_left sb ta]

private theorem nineRefinement_orthogonal
    (i j : Fin 9) (hij : i ≠ j) (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hzero :
      leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa only [ninePrefixCode, hij, ↓reduceIte] using binaryPrefixCode_orthogonal ninePrefixCode i
      j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hzero]; simp only [mul_zero, zero_mul]

private theorem nineCrossSwap_val (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(nineCrossSwap i j hij a b) : BinaryLeavitt) =
      transpositionValue
        (leavittWordS (nineWord i ++ a))
        (leavittWordT (nineWord i ++ a))
        (leavittWordS (nineWord j ++ b))
        (leavittWordT (nineWord j ++ b)) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 :=
    nineRefinement_orthogonal j i hij.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp only [mul_zero, zero_mul]
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  change
    (1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) *
      (1 + leavittWordS (nineWord j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i)) *
      (1 + leavittWordS (nineWord i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) = _
  have hleft :
      leavittWordS (nineWord i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (nineWord j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl

private def wordSwapValue (a b : List (Fin 2)) : BinaryLeavitt :=
  transpositionValue (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)

private theorem wordSwapValue_refine (a b : List (Fin 2))
    (hab : leavittWordT a * leavittWordS b = 0)
    (hba : leavittWordT b * leavittWordS a = 0) :
    wordSwapValue (a ++ [0]) (b ++ [0]) *
        wordSwapValue (a ++ [1]) (b ++ [1]) =
      wordSwapValue a b := by
  unfold wordSwapValue
  simpa only [leavittWordS_append, leavittWordT_append,
    leavittWordS, leavittWordT, mul_one, one_mul] using
    transpositionValue_refine
      (leavittWordS a) (leavittWordT a)
      (leavittWordS b) (leavittWordT b)
      (leavittS 0) (leavittT 0)
      (leavittS 1) (leavittT 1)
      (leavittWordT_mul_wordS_self a)
      (leavittWordT_mul_wordS_self b)
      hab hba
      (by simpa only [Fin.isValue, ↓reduceIte] using leavittT_mul_S 0 0)
      (by simpa only [Fin.isValue, ↓reduceIte] using leavittT_mul_S 1 1)
      (by simpa only [Fin.isValue, zero_ne_one, ↓reduceIte] using leavittT_mul_S 0 1)
      (by simpa only [Fin.isValue, one_ne_zero, ↓reduceIte] using leavittT_mul_S 1 0)
      leavitt_partition

private theorem compressionTransitionCrossSwaps_prod_val :
    (↑compressionTransitionCrossSwaps.prod : BinaryLeavitt) =
      wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) := by
  have h₀ :
      wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] =
        wordSwapValue [0, 0, 0, 1] [1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 0, 0, 1] [1, 0, 0] (leavittWordT_mul_wordS_of_incomparable _ _ (by
        decide) (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂₀ :
      wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] =
        wordSwapValue [0, 1, 1, 0] [1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 1, 1, 0] [1, 1, 0] (leavittWordT_mul_wordS_of_incomparable _ _ (by
        decide) (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂ :
      wordSwapValue [0, 1, 1, 0] [1, 1, 0] *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1] =
        wordSwapValue [0, 1, 1] [1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 1, 1] [1, 1] (leavittWordT_mul_wordS_of_incomparable _ _ (by decide)
        (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  simp only [compressionTransitionCrossSwaps, List.prod_cons, List.prod_nil,
    Units.val_mul, nineCrossSwap_val, mul_one]
  change
    wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
      (wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] *
      (wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      (wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
      (wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] *
       wordSwapValue [0, 1, 1, 1] [1, 1, 1])))) =
    wordSwapValue [0, 0, 0, 1] [1, 0, 0] *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      wordSwapValue [0, 1, 1] [1, 1]
  calc
    _ =
      (wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1]) *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      ((wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1]) *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1]) := by
          noncomm_ring
    _ = _ := by rw [h₀, h₂₀, h₂]

private theorem transpositionValue_mul_codeWord {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j) (k : ι) :
    transpositionValue
        (leavittWordS (E.word i)) (leavittWordT (E.word i))
        (leavittWordS (E.word j)) (leavittWordT (E.word j)) *
        leavittWordS (E.word k) =
      if k = i then leavittWordS (E.word j)
      else if k = j then leavittWordS (E.word i)
      else leavittWordS (E.word k) := by
  by_cases hki : k = i
  · subst k
    simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      binaryPrefixCode_orthogonal, ↓reduceIte,
      mul_one, sub_self, hij.symm, mul_zero, add_zero, zero_add]
  · by_cases hkj : k = j
    · subst k
      simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
        binaryPrefixCode_orthogonal, hij,
        ↓reduceIte, mul_zero, sub_zero, mul_one, sub_self, zero_add, add_zero, hij.symm]
    · simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      binaryPrefixCode_orthogonal, Ne.symm hki,
        ↓reduceIte, mul_zero, sub_zero, Ne.symm hkj, add_zero, hki, hkj]

private theorem uSwap12_mul (k : Fin 9) :
    wordSwapValue (uWord 1) (uWord 2) * leavittWordS (uWord k) =
      if k = 1 then leavittWordS (uWord 2)
      else if k = 2 then leavittWordS (uWord 1)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 1 2 (by decide) k

private theorem uSwap45_mul (k : Fin 9) :
    wordSwapValue (uWord 4) (uWord 5) * leavittWordS (uWord k) =
      if k = 4 then leavittWordS (uWord 5)
      else if k = 5 then leavittWordS (uWord 4)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 4 5 (by decide) k

private theorem uSwap78_mul (k : Fin 9) :
    wordSwapValue (uWord 7) (uWord 8) * leavittWordS (uWord k) =
      if k = 7 then leavittWordS (uWord 8)
      else if k = 8 then leavittWordS (uWord 7)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 7 8 (by decide) k

private theorem compressionTransitionParentSwaps_mul_word (k : Fin 9) :
    (wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)) *
        leavittWordS (uWord k) = leavittWordS (vWord k) := by
  fin_cases k <;>
    simp [mul_assoc, uSwap12_mul, uSwap45_mul, uSwap78_mul] <;>
    rfl

private theorem compressionTransitionParentSwaps_eq_table :
    wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) =
      prefixTable uPrefixCode vPrefixCode := by
  let x : BinaryLeavitt :=
    wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)
  change x = prefixTable uPrefixCode vPrefixCode
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
          (fun i => leavittWordS (uPrefixCode.word i))
          (fun i => leavittWordT (uPrefixCode.word i)) := by
            rw [uPrefixCode_complete]
    _ = ∑ i : Fin 9,
          (x * leavittWordS (uWord i)) * leavittWordT (uWord i) := by
            simp only [MatrixCorner.codeIdempotent, uPrefixCode, Finset.mul_sum, mul_assoc]
    _ = ∑ i : Fin 9,
          leavittWordS (vWord i) * leavittWordT (uWord i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show x * leavittWordS (uWord i) =
              leavittWordS (vWord i) from
              compressionTransitionParentSwaps_mul_word i]
    _ = prefixTable uPrefixCode vPrefixCode := rfl

private theorem compressionTransitionCrossSwaps_prod_eq :
    compressionTransitionCrossSwaps.prod = compressionTransition := by
  apply Units.ext
  exact compressionTransitionCrossSwaps_prod_val.trans
    compressionTransitionParentSwaps_eq_table

private theorem compressionTransition_mem :
    compressionTransition ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← compressionTransitionCrossSwaps_prod_eq]
  exact compressionTransitionCrossSwaps_prod_mem

private theorem compressionV_mem_of_compressionU
    (hU : compressionU ∈ prefixElementaryGroup ninePrefixCode) :
    compressionV ∈ prefixElementaryGroup ninePrefixCode := by
  rw [compressionV_eq_transition_mul]
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    compressionTransition_mem hU

end PrefixCompression

public
theorem compressionV_mem_ninePrefixElementaryGroup :
    compressionV ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompression.compressionV_mem_of_compressionU
    compressionU_mem_ninePrefixElementaryGroup

public
theorem sourceGeneratedGroup_eq_nine :
    SourceGeneration.sourceGeneratedGroup =
      prefixElementaryGroup ninePrefixCode :=
  SourceGeneration.sourceGeneratedGroup_eq_nine_of_compressions
    compressionU_mem_ninePrefixElementaryGroup
    compressionV_mem_ninePrefixElementaryGroup

private theorem shifted_floor_drop_subset_two_intervals
    (u v H : ℝ) (hH : 0 < H) (k : ℤ) (hk : k = ⌊u / H⌋) :
    {r : ℝ | r ∈ Set.Ico 0 H ∧ ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ⊆
      Set.Ico ((k : ℝ) * H - u) ((k : ℝ) * H - v) ∪
        Set.Ico (((k + 1 : ℤ) : ℝ) * H - u)
          (((k + 1 : ℤ) : ℝ) * H - v) := by
  intro r hr
  rcases hr with ⟨⟨hr0, hrH⟩, hdrop⟩
  let j : ℤ := ⌊(u + r) / H⌋
  have hlow : k ≤ j := by
    rw [hk]
    apply Int.floor_mono
    apply (div_le_div_iff_of_pos_right hH).2
    linarith
  have hhigh : j < k + 2 := by
    apply Int.floor_lt.mpr
    have hu : u / H < (k : ℝ) + 1 := by
      rw [hk]
      exact Int.lt_floor_add_one (u / H)
    have hr' : r / H < 1 := (div_lt_one hH).mpr hrH
    calc
      (u + r) / H = u / H + r / H := by ring
      _ < ((k : ℝ) + 1) + 1 := add_lt_add hu hr'
      _ = ((k + 2 : ℤ) : ℝ) := by push_cast; ring
  have hcases : j = k ∨ j = k + 1 := by omega
  have hv : (v + r) / H < (j : ℝ) := by
    apply Int.floor_lt.mp
    exact hdrop
  have hu : (j : ℝ) ≤ (u + r) / H := Int.floor_le _
  have hv' : v + r < (j : ℝ) * H := (div_lt_iff₀ hH).mp hv
  have hu' : (j : ℝ) * H ≤ u + r := (le_div_iff₀ hH).mp hu
  rcases hcases with hcase | hcase
  · left
    rw [hcase] at hv' hu'
    exact ⟨by linarith, by linarith⟩
  · right
    rw [hcase] at hv' hu'
    exact ⟨by linarith, by linarith⟩

private theorem measurableSet_shifted_floor_drop (u v H : ℝ) :
    MeasurableSet
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} := by
  have hv : Measurable (fun r : ℝ => ⌊(v + r) / H⌋) := by
    fun_prop
  have hu : Measurable (fun r : ℝ => ⌊(u + r) / H⌋) := by
    fun_prop
  exact measurableSet_lt hv hu

private theorem exists_common_offset_below_average
    (H : ℝ) (hH : 0 < H) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f (Set.Ico 0 H)
      MeasureTheory.volume) :
    ∃ r ∈ Set.Ico 0 H,
      f r ≤ MeasureTheory.average
        (MeasureTheory.volume.restrict (Set.Ico 0 H)) f := by
  have hvolume : MeasureTheory.volume (Set.Ico (0 : ℝ) H) =
      ENNReal.ofReal H := by
    rw [Real.volume_Ico, sub_zero]
  have hnezero : MeasureTheory.volume (Set.Ico (0 : ℝ) H) ≠ 0 := by
    rw [hvolume]
    exact ENNReal.ofReal_ne_zero_iff.mpr hH
  have hnetop : MeasureTheory.volume (Set.Ico (0 : ℝ) H) ≠ ⊤ := by
    rw [hvolume]
    exact ENNReal.ofReal_ne_top
  exact MeasureTheory.exists_le_setAverage hnezero hnetop hf

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)

private theorem measurable_rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    Measurable (fun r : ℝ => rankDropCount u v H r) := by
  classical
  unfold rankDropCount
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite
    (measurableSet_shifted_floor_drop (u i) (v i) H)
    measurable_const measurable_const

private theorem rankDropCount_nonneg_and_le {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) :
    0 ≤ rankDropCount u v H r ∧
      rankDropCount u v H r ≤ (Fintype.card ι : ℝ) := by
  classical
  constructor
  · unfold rankDropCount
    exact Finset.sum_nonneg (fun i hi => by split_ifs <;> norm_num)
  · unfold rankDropCount
    calc
      (∑ i : ι, if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
        then (1 : ℝ) else 0) ≤ ∑ _i : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs <;> norm_num
      _ = (Fintype.card ι : ℝ) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]

private theorem integrableOn_rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => rankDropCount u v H r)
      (Set.Ico 0 H) MeasureTheory.volume := by
  have hfinite : MeasureTheory.volume (Set.Ico (0 : ℝ) H) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  refine ⟨(measurable_rankDropCount u v H).aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.restrict_of_bounded
    (Fintype.card ι : ℝ) hfinite
  filter_upwards [] with r
  rw [Real.norm_eq_abs, abs_of_nonneg
    (rankDropCount_nonneg_and_le u v H r).1]
  exact (rankDropCount_nonneg_and_le u v H r).2

private theorem integrable_rankDropIndicator
    (u v H : ℝ) :
    MeasureTheory.Integrable
      (fun r : ℝ =>
        if ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋ then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ico 0 H)) := by
  have hfinite : MeasureTheory.volume (Set.Ico (0 : ℝ) H) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hmeas : Measurable
      (fun r : ℝ =>
        if ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_shifted_floor_drop u v H)
      measurable_const measurable_const
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.restrict_of_bounded
    (1 : ℝ) hfinite
  filter_upwards [] with r
  split_ifs <;> norm_num

private theorem exists_common_rank_offset {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        MeasureTheory.average
          (MeasureTheory.volume.restrict (Set.Ico 0 H))
          (fun t : ℝ => rankDropCount u v H t) := by
  exact exists_common_offset_below_average H hH
    (fun t : ℝ => rankDropCount u v H t)
    (integrableOn_rankDropCount u v H)

private theorem rankDropCount_integral_eq {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    (∫ r, rankDropCount u v H r
      ∂(MeasureTheory.volume.restrict (Set.Ico 0 H))) =
      ∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
        {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋} := by
  classical
  unfold rankDropCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i hi => integrable_rankDropIndicator (u i) (v i) H)]
  apply Finset.sum_congr rfl
  intro i hi
  have hindicator :
      (fun r : ℝ =>
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
          then (1 : ℝ) else 0) =
        {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}.indicator
          (fun _ : ℝ => (1 : ℝ)) := by
    funext r
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [hindicator]
  exact MeasureTheory.integral_indicator_one
    (measurableSet_shifted_floor_drop (u i) (v i) H)

private theorem rankDropCount_average_eq {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H) :
    MeasureTheory.average
        (MeasureTheory.volume.restrict (Set.Ico 0 H))
        (fun r : ℝ => rankDropCount u v H r) =
      H⁻¹ * ∑ i : ι,
        (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋} := by
  rw [MeasureTheory.average_eq,
    MeasureTheory.measureReal_restrict_apply_univ,
    Real.volume_real_Ico_of_le hH.le, sub_zero,
    rankDropCount_integral_eq]
  exact smul_eq_mul _ _

private theorem rankDropCount_clamp_eq {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) (hH : 0 < H) :
    rankDropCount u v H r =
      rankDropCount u (fun i => min (v i) (u i)) H r := by
  classical
  unfold rankDropCount
  apply Finset.sum_congr rfl
  intro i hi
  change
    (if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
      then (1 : ℝ) else 0) =
      if ⌊(min (v i) (u i) + r) / H⌋ < ⌊(u i + r) / H⌋
        then (1 : ℝ) else 0
  by_cases hle : v i ≤ u i
  · rw [min_eq_left hle]
  · have hreverse : u i ≤ v i := le_of_not_ge hle
    have hfloor :
        ¬ ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ := by
      apply not_lt_of_ge
      apply Int.floor_mono
      apply (div_le_div_iff_of_pos_right hH).2
      linarith
    simp only [hfloor, ↓reduceIte, min_eq_right hreverse, lt_self_iff_false]

private theorem shifted_floor_drop_volume_bound_sharp
    (u v H : ℝ) (hH : 0 < H) (hvu : v ≤ u) :
    MeasureTheory.volume
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
      ENNReal.ofReal (u - v) := by
  let k : ℤ := ⌊u / H⌋
  let c : ℝ := (((k + 1 : ℤ) : ℝ) * H - u)
  let d : ℝ := u - v
  have hd : 0 ≤ d := sub_nonneg.mpr hvu
  have hklo : (k : ℝ) ≤ u / H := by
    dsimp [k]
    exact Int.floor_le _
  have hkhi : u / H < (k : ℝ) + 1 := by
    dsimp [k]
    exact Int.lt_floor_add_one _
  have hklo' : (k : ℝ) * H ≤ u := (le_div_iff₀ hH).mp hklo
  have hkhi' : u < ((k : ℝ) + 1) * H := (div_lt_iff₀ hH).mp hkhi
  have hc0 : 0 ≤ c := by
    dsimp [c]
    push_cast
    linarith
  have hcH : c ≤ H := by
    dsimp [c]
    push_cast
    linarith
  let A : Set ℝ := Set.Ico 0 (max 0 (c - H + d))
  let B : Set ℝ := Set.Ico c (min H (c + d))
  have hsubset :
      {r : ℝ | r ∈ Set.Ico 0 H ∧
        ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ⊆ A ∪ B := by
    intro r hr
    have htwo := shifted_floor_drop_subset_two_intervals u v H hH k rfl hr
    rcases htwo with hleft | hright
    · left
      change r ∈ Set.Ico 0 (max 0 (c - H + d))
      refine ⟨hr.1.1, ?_⟩
      apply lt_of_lt_of_le (b := c - H + d)
      · have hupper := hleft.2
        dsimp [c, d]
        push_cast
        linarith
      · exact le_max_right _ _
    · right
      change r ∈ Set.Ico c (min H (c + d))
      refine ⟨?_, lt_min hr.1.2 ?_⟩
      · have hlower := hright.1
        dsimp [c]
        exact hlower
      · have hupper := hright.2
        dsimp [c, d]
        push_cast at hupper ⊢
        linarith
  have hA : MeasureTheory.volume A =
      ENNReal.ofReal (max 0 (c - H + d)) := by
    dsimp [A]
    rw [Real.volume_Ico, sub_zero]
  have hB : MeasureTheory.volume B =
      ENNReal.ofReal (min H (c + d) - c) := by
    dsimp [B]
    rw [Real.volume_Ico]
  have hA0 : 0 ≤ max 0 (c - H + d) := le_max_left _ _
  have hB0 : 0 ≤ min H (c + d) - c := by
    apply sub_nonneg.mpr
    exact le_min hcH (by linarith)
  have hlength : max 0 (c - H + d) + (min H (c + d) - c) = d := by
    by_cases hshort : d ≤ H - c
    · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      ring
    · have hlong : H - c < d := lt_of_not_ge hshort
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
  calc
    MeasureTheory.volume
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
        MeasureTheory.volume (A ∪ B) :=
      MeasureTheory.measure_mono hsubset
    _ ≤ MeasureTheory.volume A + MeasureTheory.volume B :=
      MeasureTheory.measure_union_le A B
    _ = ENNReal.ofReal (max 0 (c - H + d)) +
        ENNReal.ofReal (min H (c + d) - c) := by rw [hA, hB]
    _ = ENNReal.ofReal d := by
      rw [← ENNReal.ofReal_add hA0 hB0, hlength]
    _ = ENNReal.ofReal (u - v) := by rfl

private theorem rankDrop_measureReal_bound_sharp
    (u v H : ℝ) (hH : 0 < H) (hvu : v ≤ u) :
    (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
      u - v := by
  rw [MeasureTheory.measureReal_restrict_apply
    (measurableSet_shifted_floor_drop u v H)]
  have heq :
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ∩ Set.Ico 0 H =
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, and_comm]
  rw [heq, MeasureTheory.measureReal_def]
  have hbound := shifted_floor_drop_volume_bound_sharp u v H hH hvu
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (sub_nonneg.mpr hvu)] at hreal

private theorem exists_common_rank_offset_bound_sharp {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H)
    (hvu : ∀ i : ι, v i ≤ u i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        (1 / H) * ∑ i : ι, (u i - v i) := by
  classical
  obtain ⟨r, hr, hmean⟩ := exists_common_rank_offset u v H hH
  refine ⟨r, hr, hmean.trans ?_⟩
  rw [rankDropCount_average_eq u v H hH]
  have hsum :
      (∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}) ≤
        ∑ i : ι, (u i - v i) := by
    exact Finset.sum_le_sum (fun i hi =>
      rankDrop_measureReal_bound_sharp (u i) (v i) H hH (hvu i))
  calc
    H⁻¹ *
        (∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}) ≤
      H⁻¹ * ∑ i : ι, (u i - v i) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hH.le)
    _ = (1 / H) * ∑ i : ι, (u i - v i) := by
      rw [one_div]

private theorem exists_common_rank_offset_one_sided_sharp
    {ι : Type*} [Fintype ι]
    (u v delta : ι → ℝ) (H : ℝ) (hH : 0 < H)
    (hdelta : ∀ i : ι, 0 ≤ delta i)
    (hone : ∀ i : ι, u i - delta i ≤ v i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        (1 / H) * ∑ i : ι, delta i := by
  classical
  obtain ⟨r, hr, hbound⟩ :=
    exists_common_rank_offset_bound_sharp
      u (fun i => min (v i) (u i))
      H hH (fun i => min_le_right (v i) (u i))
  refine ⟨r, hr, ?_⟩
  have hsum :
      (∑ i : ι, (u i - min (v i) (u i))) ≤
        ∑ i : ι, delta i := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hle : v i ≤ u i
    · rw [min_eq_left hle]
      linarith [hone i]
    · rw [min_eq_right (le_of_not_ge hle), sub_self]
      exact hdelta i
  calc
    rankDropCount u v H r =
      rankDropCount u (fun i => min (v i) (u i)) H r :=
        rankDropCount_clamp_eq u v H r hH
    _ ≤ (1 / H) * ∑ i : ι, (u i - min (v i) (u i)) := hbound
    _ ≤ (1 / H) * ∑ i : ι, delta i :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem log_one_sided_of_multiplicative
    (x y eta : ℝ) (hx : 0 < x)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hcomparison : (1 - eta) * x ≤ y) :
    Real.log x - |Real.log (1 - eta)| ≤ Real.log y := by
  have hfactor : 0 < 1 - eta := by linarith
  have hy : 0 < y :=
    lt_of_lt_of_le (mul_pos hfactor hx) hcomparison
  have hlog : Real.log ((1 - eta) * x) ≤ Real.log y :=
    (Real.log_le_log_iff (mul_pos hfactor hx) hy).2 hcomparison
  rw [Real.log_mul hfactor.ne' hx.ne'] at hlog
  have hnonpos : Real.log (1 - eta) ≤ 0 :=
    Real.log_nonpos hfactor.le (by linarith)
  rw [abs_of_nonpos hnonpos]
  linarith

private theorem exists_common_log_rank_offset {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (eta H : ℝ)
    (hx : ∀ i : ι, 0 < x i)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hH : 0 < H)
    (hcomparison : ∀ i : ι, (1 - eta) * x i ≤ y i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount (fun i => Real.log (x i))
          (fun i => Real.log (y i)) H r ≤
        (Fintype.card ι : ℝ) * |Real.log (1 - eta)| / H := by
  classical
  obtain ⟨r, hr, hbound⟩ :=
    exists_common_rank_offset_one_sided_sharp
      (fun i => Real.log (x i))
      (fun i => Real.log (y i))
      (fun _ : ι => |Real.log (1 - eta)|)
      H hH
      (fun _ => abs_nonneg _)
      (fun i => log_one_sided_of_multiplicative
        (x i) (y i) eta (hx i) heta0 heta1 (hcomparison i))
  refine ⟨r, hr, hbound.trans_eq ?_⟩
  simp only [one_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

private theorem abs_log_one_sub_le_two_mul
    (eta : ℝ) (heta0 : 0 ≤ eta) (hetaHalf : eta ≤ (1 : ℝ) / 2) :
    |Real.log (1 - eta)| ≤ 2 * eta := by
  have hfactor : 0 < 1 - eta := by linarith
  have hlog : Real.log (1 - eta) ≤ 0 :=
    Real.log_nonpos hfactor.le (by linarith)
  rw [abs_of_nonpos hlog]
  have hlower := Real.one_sub_inv_le_log_of_pos hfactor
  have hratio : eta / (1 - eta) ≤ 2 * eta := by
    apply (div_le_iff₀ hfactor).2
    nlinarith [mul_nonneg heta0 (by linarith : 0 ≤ 1 - 2 * eta)]
  have hidentity : (1 - eta)⁻¹ - 1 = eta / (1 - eta) := by
    field_simp
    ring
  linarith

private theorem abs_log_one_sub_div_tendsto_zero
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (hH : ∀ n, 0 < H n)
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0))
    (hratio : Filter.Tendsto
      (fun n => eta n / H n) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => |Real.log (1 - eta n)| / H n)
      Filter.atTop (nhds 0) := by
  have hsmall : ∀ᶠ n in Filter.atTop,
      eta n < (1 : ℝ) / 2 :=
    heta.eventually (gt_mem_nhds (by norm_num))
  have hupper : ∀ᶠ n in Filter.atTop,
      |Real.log (1 - eta n)| / H n ≤
        2 * (eta n / H n) := by
    filter_upwards [hsmall] with n hn
    calc
      |Real.log (1 - eta n)| / H n ≤
          (2 * eta n) / H n :=
        (div_le_div_iff_of_pos_right (hH n)).2
          (abs_log_one_sub_le_two_mul
            (eta n) (heta0 n) hn.le)
      _ = 2 * (eta n / H n) := by ring
  have hlimit : Filter.Tendsto
      (fun n => 2 * (eta n / H n)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (2 : ℝ) hratio
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (hH n).le)
    hupper hlimit

namespace CheegerPoincare

open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => 0 < f x

@[simp] public theorem mem_positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) (x : V) :
    x ∈ positiveSupport f ↔ 0 < f x := by
  classical
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def finiteMean {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, f x) / (Fintype.card V : ℝ)

private theorem sum_sub_finiteMean_eq_zero {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (∑ x : V, (f x - finiteMean f)) = 0 := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, finiteMean]
  field_simp
  ring

public
theorem sum_sq_sub_finiteMean_le {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (c : ℝ) :
    (∑ x : V, (f x - finiteMean f) ^ 2) ≤
      ∑ x : V, (f x - c) ^ 2 := by
  have hpoint (x : V) :
      (f x - c) ^ 2 =
        (f x - finiteMean f) ^ 2 +
          2 * (finiteMean f - c) * (f x - finiteMean f) +
          (finiteMean f - c) ^ 2 := by
    ring
  have hidentity :
      (∑ x : V, (f x - c) ^ 2) =
        (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
    calc
      (∑ x : V, (f x - c) ^ 2) =
          ∑ x : V,
            ((f x - finiteMean f) ^ 2 +
              2 * (finiteMean f - c) * (f x - finiteMean f) +
              (finiteMean f - c) ^ 2) :=
            Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          2 * (finiteMean f - c) *
            (∑ x : V, (f x - finiteMean f)) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            rw [sum_sub_finiteMean_eq_zero]
            ring
  rw [hidentity]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => f x < a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => a < f x

@[simp] public theorem mem_lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ lowerLevel f a ↔ f x < a := by
  classical
  simp only [lowerLevel, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] public theorem mem_upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ upperLevel f a ↔ a < f x := by
  classical
  simp only [upperLevel, Finset.mem_filter, Finset.mem_univ, true_and]

public
theorem exists_finite_real_median {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    ∃ m : ℝ,
      2 * (lowerLevel f m).card ≤ Fintype.card V ∧
      2 * (upperLevel f m).card ≤ Fintype.card V := by
  classical
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty V›
    refine ⟨f x, ?_⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  let a : ℝ := values.min' hvalues
  have ha_values : a ∈ values := Finset.min'_mem values hvalues
  have ha_lower : lowerLevel f a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_lt : f x < a := (mem_lowerLevel f a x).mp hx
    have hx_values : f x ∈ values :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    exact (not_lt_of_ge (Finset.min'_le values (f x) hx_values)) hx_lt
  let candidates : Finset ℝ :=
    values.filter fun c => 2 * (lowerLevel f c).card ≤ Fintype.card V
  have hcandidates : candidates.Nonempty := by
    refine ⟨a, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨ha_values, ?_⟩
    simp only [ha_lower, Finset.card_empty, mul_zero, zero_le]
  let m : ℝ := candidates.max' hcandidates
  have hm_candidates : m ∈ candidates :=
    Finset.max'_mem candidates hcandidates
  have hm_lower : 2 * (lowerLevel f m).card ≤ Fintype.card V :=
    (Finset.mem_filter.mp hm_candidates).2
  refine ⟨m, hm_lower, ?_⟩
  by_contra hu
  have hu_large : Fintype.card V < 2 * (upperLevel f m).card :=
    Nat.lt_of_not_ge hu
  have hu_nonempty : (upperLevel f m).Nonempty := by
    apply Finset.card_pos.mp
    omega
  let upperValues : Finset ℝ := (upperLevel f m).image f
  have hupperValues : upperValues.Nonempty :=
    Finset.image_nonempty.mpr hu_nonempty
  let b : ℝ := upperValues.min' hupperValues
  have hb_upperValues : b ∈ upperValues :=
    Finset.min'_mem upperValues hupperValues
  obtain ⟨z, hz_upper, hz_b⟩ := Finset.mem_image.mp hb_upperValues
  have hmb : m < b := by
    rw [← hz_b]
    exact (mem_upperLevel f m z).mp hz_upper
  have hdisjoint : Disjoint (lowerLevel f b) (upperLevel f m) := by
    apply Finset.disjoint_left.mpr
    intro x hx_lower hx_upper
    have hx_lt : f x < b := (mem_lowerLevel f b x).mp hx_lower
    have hx_image : f x ∈ upperValues :=
      Finset.mem_image.mpr ⟨x, hx_upper, rfl⟩
    have hb_le : b ≤ f x :=
      Finset.min'_le upperValues (f x) hx_image
    exact (not_lt_of_ge hb_le) hx_lt
  have hcard :
      (lowerLevel f b).card + (upperLevel f m).card ≤ Fintype.card V := by
    calc
      (lowerLevel f b).card + (upperLevel f m).card =
          ((lowerLevel f b) ∪ (upperLevel f m)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hb_lower : 2 * (lowerLevel f b).card ≤ Fintype.card V := by
    omega
  have hb_values : b ∈ values := by
    rw [← hz_b]
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hb_candidates : b ∈ candidates :=
    Finset.mem_filter.mpr ⟨hb_values, hb_lower⟩
  have hb_le_m : b ≤ m :=
    Finset.le_max' candidates b hb_candidates
  exact (not_le_of_gt hmb) hb_le_m

private theorem positive_max_iff (a : ℝ) : 0 < max a 0 ↔ 0 < a := by
  by_cases ha : 0 < a
  · rw [max_eq_left ha.le]
  · rw [max_eq_right (le_of_not_gt ha)]
    simp only [lt_self_iff_false, ha]

public
theorem positiveSupport_max_sub {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (f x - m) 0) = upperLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_upperLevel,
    positive_max_iff, sub_pos]

public
theorem positiveSupport_max_sub_reverse {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (m - f x) 0) = lowerLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_lowerLevel,
    positive_max_iff, sub_pos]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def finiteVariance {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, (f x - finiteMean f) ^ 2) / (Fintype.card V : ℝ)

public
theorem finiteVariance_nonneg {V : Type*} [Fintype V]
    (f : V → ℝ) : 0 ≤ finiteVariance f := by
  unfold finiteVariance
  exact div_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)

public
theorem card_mul_finiteVariance {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (Fintype.card V : ℝ) * finiteVariance f =
      ∑ x : V, (f x - finiteMean f) ^ 2 := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteVariance
  field_simp

end CheegerPoincare

namespace ThompsonPrefixLocal

open scoped BigOperators

private theorem idempotentCornerUnitExtensions_commute
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (u : he.Cornerˣ) (v : hf.Cornerˣ) :
    Commute
      (idempotentCornerUnitExtension he u)
      (idempotentCornerUnitExtension hf v) := by
  apply Units.ext
  have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
  have hv := (Subsemigroup.mem_corner_iff hf).mp v.val.property
  have huv : u.val.val * v.val.val = 0 := by
    calc
      u.val.val * v.val.val =
          (u.val.val * e) * (f * v.val.val) := by rw [hu.2, hv.1]
      _ = u.val.val * (e * f) * v.val.val := by noncomm_ring
      _ = 0 := by rw [hef]; simp only [mul_zero, zero_mul]
  have hvu : v.val.val * u.val.val = 0 := by
    calc
      v.val.val * u.val.val =
          (v.val.val * f) * (e * u.val.val) := by rw [hv.2, hu.1]
      _ = v.val.val * (f * e) * u.val.val := by noncomm_ring
      _ = 0 := by rw [hfe]; simp only [mul_zero, zero_mul]
  have hev : e * v.val.val = 0 := by
    calc
      e * v.val.val = e * (f * v.val.val) := by rw [hv.1]
      _ = (e * f) * v.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp only [zero_mul]
  have hve : v.val.val * e = 0 := by
    calc
      v.val.val * e = (v.val.val * f) * e := by rw [hv.2]
      _ = v.val.val * (f * e) := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp only [mul_zero]
  have huf : u.val.val * f = 0 := by
    calc
      u.val.val * f = (u.val.val * e) * f := by rw [hu.2]
      _ = u.val.val * (e * f) := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp only [mul_zero]
  have hfu : f * u.val.val = 0 := by
    calc
      f * u.val.val = f * (e * u.val.val) := by rw [hu.1]
      _ = (f * e) * u.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp only [zero_mul]
  change
    (u.val.val + (1 - e)) * (v.val.val + (1 - f)) =
      (v.val.val + (1 - f)) * (u.val.val + (1 - e))
  noncomm_ring [he.eq, hf.eq, hu.1, hu.2, hv.1, hv.2,
    hef, hfe, huv, hvu, hev, hve, huf, hfu]

private theorem idempotentCornerUnitExtensions_eq_one
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0)
    (u : he.Cornerˣ) (v : hf.Cornerˣ)
    (h : idempotentCornerUnitExtension he u =
      idempotentCornerUnitExtension hf v) :
    idempotentCornerUnitExtension he u = 1 := by
  have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
  have hv := (Subsemigroup.mem_corner_iff hf).mp v.val.property
  have hev : e * v.val.val = 0 := by
    calc
      e * v.val.val = e * (f * v.val.val) := by rw [hv.1]
      _ = (e * f) * v.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hef, zero_mul]
  have hval := congrArg (fun z : Aˣ => (z : A)) h
  change u.val.val + (1 - e) = v.val.val + (1 - f) at hval
  have hleft := congrArg (fun z : A => e * z) hval
  have hue : u.val.val = e := by
    simpa only [mul_add, hu.1, mul_sub, mul_one, he.eq, sub_self, add_zero, hev, hef, sub_zero,
      zero_add] using
      hleft
  apply Units.ext
  change u.val.val + (1 - e) = 1
  rw [hue]
  noncomm_ring

private def idempotentCornerGroup {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : Subgroup Aˣ :=
  (idempotentCornerUnitExtension he).range

private theorem idempotentCornerGroup_le_centralizer
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    idempotentCornerGroup hf ≤
      Subgroup.centralizer (idempotentCornerGroup he : Set Aˣ) := by
  intro z hz
  obtain ⟨v, rfl⟩ := hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  exact (idempotentCornerUnitExtensions_commute he hf hef hfe u v).eq

private theorem idempotentCornerGroup_inf_eq_bot
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) :
    idempotentCornerGroup he ⊓ idempotentCornerGroup hf = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hz
    have huv : idempotentCornerUnitExtension he u =
        idempotentCornerUnitExtension hf v := hu.trans hv.symm
    have hone := idempotentCornerUnitExtensions_eq_one he hf hef u v huv
    have hz : z = 1 := hu.symm.trans hone
    simp only [hz, one_mem]
  · exact bot_le

private theorem leavittCylinder_isIdempotent (a : List (Fin 2)) :
    IsIdempotentElem (leavittCylinder a) := by
  change
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a * leavittWordT a
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a *
        (leavittWordT a * leavittWordS a) * leavittWordT a := by
          noncomm_ring
    _ = leavittWordS a * leavittWordT a := by
      rw [leavittWordT_mul_wordS_self]
      simp only [mul_one]

private theorem leavittCylinder_mul_eq_zero_of_incomparable
    (a b : List (Fin 2)) (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    leavittCylinder a * leavittCylinder b = 0 := by
  change
    (leavittWordS a * leavittWordT a) *
      (leavittWordS b * leavittWordT b) = 0
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS b * leavittWordT b) =
      leavittWordS a *
        (leavittWordT a * leavittWordS b) * leavittWordT b := by
          noncomm_ring
    _ = 0 := by
      rw [leavittWordT_mul_wordS_of_incomparable a b hab hba]
      simp only [mul_zero, zero_mul]

private def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup (leavittCylinder_isIdempotent a)

private def prefixCodeIdempotent {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι) : BinaryLeavitt :=
  MatrixCorner.codeIdempotent
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))

private def prefixCodeCornerGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))

private theorem prefixElementaryGroup_le_corner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    prefixElementaryGroup E ≤ prefixCodeCornerGroup E := by
  rw [← prefixCornerElementaryGroup_map E]
  rintro _ ⟨u, _, rfl⟩
  exact ⟨(Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv) u, rfl⟩

private theorem alphaZeroWord_incomparable_local (i : Fin 3) :
    ¬ alphaZeroPrefixCode.word i <+: [0, 0, 0, 1] := by
  fin_cases i <;> decide

private theorem localWord_incomparable_alphaZero (i : Fin 3) :
    ¬ [0, 0, 0, 1] <+: alphaZeroPrefixCode.word i := by
  fin_cases i <;> decide

private theorem alphaZeroCode_mul_localCylinder :
    prefixCodeIdempotent alphaZeroPrefixCode *
        leavittCylinder [0, 0, 0, 1] = 0 := by
  change
    (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) *
        leavittCylinder [0, 0, 0, 1] = 0
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    (alphaZeroPrefixCode.word i) [0, 0, 0, 1]
    (alphaZeroWord_incomparable_local i)
    (localWord_incomparable_alphaZero i)

private theorem localCylinder_mul_alphaZeroCode :
    leavittCylinder [0, 0, 0, 1] *
        prefixCodeIdempotent alphaZeroPrefixCode = 0 := by
  change
    leavittCylinder [0, 0, 0, 1] *
        (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) = 0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    [0, 0, 0, 1] (alphaZeroPrefixCode.word i)
    (localWord_incomparable_alphaZero i)
    (alphaZeroWord_incomparable_local i)

private theorem localCylinderCorner_le_centralizer_alphaZero :
    cylinderCornerGroup [0, 0, 0, 1] ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) := by
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS (alphaZeroPrefixCode.word i))
    (fun i => leavittWordT (alphaZeroPrefixCode.word i))
    (binaryPrefixCode_orthogonal alphaZeroPrefixCode)
  let hf := leavittCylinder_isIdempotent [0, 0, 0, 1]
  have hef : prefixCodeIdempotent alphaZeroPrefixCode *
      leavittCylinder [0, 0, 0, 1] = 0 :=
    alphaZeroCode_mul_localCylinder
  have hfe : leavittCylinder [0, 0, 0, 1] *
      prefixCodeIdempotent alphaZeroPrefixCode = 0 :=
    localCylinder_mul_alphaZeroCode
  intro z hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx' := prefixElementaryGroup_le_corner alphaZeroPrefixCode hx
  have hz' : z ∈ idempotentCornerGroup hf := hz
  have hc := idempotentCornerGroup_le_centralizer he hf hef hfe hz'
  exact Subgroup.mem_centralizer_iff.mp hc x hx'

private theorem alphaZero_inf_localCylinderCorner_eq_bot :
    prefixElementaryGroup alphaZeroPrefixCode ⊓
        cylinderCornerGroup [0, 0, 0, 1] = ⊥ := by
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS (alphaZeroPrefixCode.word i))
    (fun i => leavittWordT (alphaZeroPrefixCode.word i))
    (binaryPrefixCode_orthogonal alphaZeroPrefixCode)
  let hf := leavittCylinder_isIdempotent [0, 0, 0, 1]
  have hzero := idempotentCornerGroup_inf_eq_bot he hf
    alphaZeroCode_mul_localCylinder
  apply le_antisymm
  · intro z hz
    have hx := prefixElementaryGroup_le_corner alphaZeroPrefixCode hz.1
    have hz' : z ∈ idempotentCornerGroup he ⊓ idempotentCornerGroup hf :=
      ⟨hx, hz.2⟩
    rw [hzero] at hz'
    exact hz'
  · exact bot_le

end ThompsonPrefixLocal

public
theorem target_majority_of_small_symmDiff
    {V : Type*} [DecidableEq V] (C D : Finset V)
    (hsmall : 2 * (C ∆ D).card < C.card) :
    D.card < 2 * (C ∩ D).card := by
  have hC := Finset.card_sdiff_add_card_inter C D
  have hD := Finset.card_sdiff_add_card_inter D C
  have hleft : (C \ D).card ≤ (C ∆ D).card :=
    Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := C) (t := D))
  have hright : (D \ C).card ≤ (C ∆ D).card :=
    Finset.card_le_card (Finset.symmDiff_subset_sdiff' (s := C) (t := D))
  rw [Finset.inter_comm D C] at hD
  omega

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRetainedFinpartition
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) : Finpartition (matchedRetainedSupport R) :=
  P.ofSubset hR (Finset.sup_eq_biUnion R id)

public
theorem matchedRetainedSupport_nonempty
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) :
    (matchedRetainedSupport R).Nonempty := by
  obtain ⟨C, hC⟩ := hRne
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts (hR hC)
  refine ⟨x, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨C, hC, by simpa only [id_eq] using hx⟩

private theorem partitionWordCrossing_indexed_sum_card_le_target_add_unmatched
    {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (I : Finset ι) (w : ι → Equiv.Perm V) :
    (∑ i ∈ I, (partitionWordCrossing P (w i)).card) ≤
      (∑ i ∈ I, (partitionWordCrossing Q (w i)).card) +
        2 * I.card * (U \ matchedCore R D).card := by
  calc
    (∑ i ∈ I, (partitionWordCrossing P (w i)).card) ≤
        ∑ i ∈ I,
          ((partitionWordCrossing Q (w i)).card +
            2 * (U \ matchedCore R D).card) :=
      Finset.sum_le_sum fun i _ =>
        partitionWordCrossing_card_le_target_add_unmatched
          P Q R hR D hD hinj (w i)
    _ = (∑ i ∈ I, (partitionWordCrossing Q (w i)).card) +
          2 * I.card * (U \ matchedCore R D).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, mul_assoc]

public
theorem matchedRetainedSupport_cover_density_tendsto_one
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0)) :
    Tendsto
      (fun n => ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card)
      atTop (𝓝 1) := by
  have hform (n : ℕ) :
      ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card =
        1 - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card) := by
    have hcard := Finset.card_sdiff_add_card_eq_card
      (matchedRetainedSupport_subset (P n) (R n) (hR n))
    have hreal :
        ((U n \ matchedRetainedSupport (R n)).card : ℝ) +
          (matchedRetainedSupport (R n)).card = (U n).card := by
      exact_mod_cast hcard
    have hden : ((U n).card : ℝ) ≠ 0 := by
      exact_mod_cast (hU n).card_pos.ne'
    field_simp
    linarith
  have hlimit : Tendsto
      (fun n =>
        (1 : ℝ) - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hdiscard :
        Tendsto
          (fun n =>
            (1 : ℝ) - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
              (U n).card))
          atTop (𝓝 ((1 : ℝ) - 0)))
  convert hlimit using 1
  funext n
  exact hform n

public
theorem exists_matched_slow_diagonal_word_errors
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)] {ι : Type*}
    (U : ∀ n, Finset (V n))
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
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
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto
          (fun n =>
            (((∑ i ∈ I (r n),
                (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) +
              (U n ∩ B n (r n)).card) / (U n).card)
          atTop (𝓝 0) := by
  have hmissing := matchedCore_missing_density_tendsto_zero
    U P R hR D hdiscard hsymm
  have hsource (k : ℕ) : Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n =>
          ((2 * (I k).card : ℕ) : ℝ) *
            (((U n \ matchedCore (R n) (D n)).card : ℝ) /
              (U n).card))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hmissing :
          Tendsto
            (fun n =>
              ((2 * (I k).card : ℕ) : ℝ) *
                (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                  (U n).card))
            atTop (𝓝 (((2 * (I k).card : ℕ) : ℝ) * 0)))
    have hupper : Tendsto
        (fun n =>
          ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
            (U n).card +
            ((2 * (I k).card : ℕ) : ℝ) *
              (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                (U n).card))
        atTop (𝓝 0) := by
      simpa only [add_zero] using (hword k).add hscaled
    refine squeeze_zero (fun n => by positivity) ?_ hupper
    intro n
    have hcard :
        ((∑ i ∈ I k,
          (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) ≤
          ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) +
            ((2 * (I k).card : ℕ) : ℝ) *
              ((U n \ matchedCore (R n) (D n)).card : ℝ) := by
      exact_mod_cast
        partitionWordCrossing_indexed_sum_card_le_target_add_unmatched
          (P n) (Q n) (R n) (hR n) (D n) (hD n)
          (finpartition_dominant_matching_injOn
            (P n) (R n) (hR n) (D n) (hmajor n))
          (I k) (w n)
    calc
      ((∑ i ∈ I k,
        (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
          (U n).card ≤
        (((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) +
          ((2 * (I k).card : ℕ) : ℝ) *
            ((U n \ matchedCore (R n) (D n)).card : ℝ)) /
              (U n).card :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
            (U n).card +
            ((2 * (I k).card : ℕ) : ℝ) *
              (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                (U n).card) := by
        ring
  let e : ℕ → ℕ → ℝ := fun n k =>
    (((∑ i ∈ I k,
        (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) +
      (U n ∩ B n k).card) / (U n).card
  have he_nonneg (n k : ℕ) : 0 ≤ e n k := by
    dsimp [e]
    positivity
  have he (k : ℕ) : Tendsto (fun n => e n k) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n =>
          ((∑ i ∈ I k,
            (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
              (U n).card +
            ((U n ∩ B n k).card : ℝ) / (U n).card)
        atTop (𝓝 0) := by
      simpa only [add_zero] using (hsource k).add (hbad k)
    convert hsum using 1
    funext n
    dsimp [e]
    ring
  obtain ⟨r, hr, her⟩ :=
    exists_diverging_radius_with_vanishing_diagonal_error e he_nonneg he
  exact ⟨r, hr, her⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRadiusBad {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) : Finset V :=
  B ∪ I.biUnion fun i => partitionWordCrossing P (w i)

public
theorem matchedRadiusBad_card_le
    {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) :
    (U ∩ matchedRadiusBad P I w B).card ≤
      (U ∩ B).card +
        ∑ i ∈ I, (partitionWordCrossing P (w i)).card := by
  have hsubset : U ∩ matchedRadiusBad P I w B ⊆
      (U ∩ B) ∪ I.biUnion (fun i => partitionWordCrossing P (w i)) := by
    intro x hx
    obtain ⟨hxU, hx⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hx with hxB | hxW
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hxB⟩)
    · exact Finset.mem_union_right _ hxW
  have hfirst := Finset.card_le_card hsubset
  have hsecond := Finset.card_union_le
    (U ∩ B) (I.biUnion fun i => partitionWordCrossing P (w i))
  have hthird := Finset.card_biUnion_le
    (s := I) (t := fun i => partitionWordCrossing P (w i))
  omega

public
theorem matched_exists_le_weighted_average {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (weight bad : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i) :
    ∃ i ∈ s,
      bad i / weight i ≤ (∑ j ∈ s, bad j) / (∑ j ∈ s, weight j) := by
  have hsum : 0 < ∑ j ∈ s, weight j := Finset.sum_pos hweight hs
  have havg :
      ∑ i ∈ s, bad i ≤
        ∑ i ∈ s,
          ((∑ j ∈ s, bad j) / (∑ j ∈ s, weight j)) * weight i := by
    rw [← Finset.mul_sum, div_mul_cancel₀ _ hsum.ne']
  obtain ⟨i, hi, hbound⟩ := Finset.exists_le_of_sum_le hs havg
  exact ⟨i, hi, (div_le_iff₀ (hweight i hi)).2 hbound⟩

public
theorem matched_sum_card_inter_partition
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (B : Finset V) :
    ∑ C ∈ P.parts, (C ∩ B).card = (U ∩ B).card := by
  have hdis :
      (P.parts : Set (Finset V)).PairwiseDisjoint
        (fun C : Finset V => C ∩ B) := by
    intro C hC D hD hne
    exact (P.disjoint hC hD hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hunion : P.parts.biUnion (fun C => C ∩ B) = U ∩ B := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, ← P.biUnion_parts, id_eq]
    aesop
  calc
    ∑ C ∈ P.parts, (C ∩ B).card =
        (P.parts.biUnion fun C => C ∩ B).card :=
      (Finset.card_biUnion hdis).symm
    _ = (U ∩ B).card := congrArg Finset.card hunion

public
theorem matchedRetained_bad_density_tendsto_zero
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
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
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((matchedRetainedSupport (R n) ∩ B n).card : ℝ) /
          (matchedRetainedSupport (R n)).card))
      atTop (𝓝 0) := by
  have hcover := matchedRetainedSupport_cover_density_tendsto_one
    U hU P R hR hdiscard
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤
        ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  have htwice : Tendsto
      (fun n =>
        (2 : ℝ) * (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hbad :
        Tendsto
          (fun n =>
            (2 : ℝ) * (((U n ∩ B n).card : ℝ) / (U n).card))
          atTop (𝓝 ((2 : ℝ) * 0)))
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ htwice
  filter_upwards [hhalf] with n hn
  have hucard : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hrcard : (0 : ℝ) < (matchedRetainedSupport (R n)).card := by
    exact_mod_cast
      (matchedRetainedSupport_nonempty (P n) (R n) (hR n) (hRne n)).card_pos
  have hmass :
      ((U n).card : ℝ) ≤ 2 * (matchedRetainedSupport (R n)).card := by
    have h := (le_div_iff₀ hucard).1 hn
    linarith
  have hbadcard :
      ((matchedRetainedSupport (R n) ∩ B n).card : ℝ) ≤
        (U n ∩ B n).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter_right
        (matchedRetainedSupport_subset (P n) (R n) (hR n)))
  calc
    ((matchedRetainedSupport (R n) ∩ B n).card : ℝ) /
        (matchedRetainedSupport (R n)).card ≤
      ((U n ∩ B n).card : ℝ) / (matchedRetainedSupport (R n)).card :=
        div_le_div_of_nonneg_right hbadcard hrcard.le
    _ ≤ 2 * (((U n ∩ B n).card : ℝ) / (U n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hrcard hucard).2
      simpa only [mul_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) (U n ∩ B n).card))

public
theorem matched_eventually_exists_good_vertex
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (C B : ∀ n, Finset (V n)) (hC : ∀ n, (C n).Nonempty)
    (hbad : Tendsto
      (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ x ∈ C n, x ∉ B n := by
  filter_upwards [hbad.eventually (gt_mem_nhds zero_lt_one)] with n hn
  by_contra h
  push Not at h
  have heq : C n ∩ B n = C n := Finset.inter_eq_left.2 h
  have hc : ((C n).card : ℝ) ≠ 0 := by
    exact_mod_cast (hC n).card_pos.ne'
  rw [heq, div_self hc] at hn
  exact (lt_irrefl (1 : ℝ)) hn

namespace ComponentMidrankVariance

open scoped BigOperators

private def lowerRankWeight (s : Finset ℤ) (w : ℤ → ℝ) (j : ℤ) : ℝ :=
  (s.filter (fun i => i < j)).sum w

private theorem sum_weighted_ordered_midpoints_sq (s : Finset ℤ) (w : ℤ → ℝ) :
    (∑ j ∈ s, w j * (lowerRankWeight s w j + w j / 2) ^ 2) =
      (∑ j ∈ s, w j) ^ 3 / 3 -
        (∑ j ∈ s, w j ^ 3) / 12 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp only [lowerRankWeight, Finset.filter_empty, Finset.sum_empty, zero_add, ne_eq,
    OfNat.ofNat_ne_zero,
               not_false_eq_true, zero_pow, zero_div, sub_self]
  | @insert a s hmax ih =>
      have ha : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (hmax a ha)
      have hfiltera :
          (insert a s).filter (fun i : ℤ => i < a) = s := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hi | hi, hia⟩
          · subst i
            exact (lt_irrefl _ hia).elim
          · exact hi
        · intro hi
          exact ⟨Or.inr hi, hmax i hi⟩
      have hprefixa :
          lowerRankWeight (insert a s) w a = ∑ i ∈ s, w i := by
        unfold lowerRankWeight
        rw [hfiltera]
      have hprefix (j : ℤ) (hj : j ∈ s) :
          lowerRankWeight (insert a s) w j = lowerRankWeight s w j := by
        unfold lowerRankWeight
        have hnot : ¬ a < j := not_lt_of_ge (le_of_lt (hmax j hj))
        rw [Finset.filter_insert, ite_eq_right hnot]
      calc
        (∑ j ∈ insert a s,
            w j * (lowerRankWeight (insert a s) w j + w j / 2) ^ 2) =
          w a * ((∑ i ∈ s, w i) + w a / 2) ^ 2 +
            ∑ j ∈ s, w j * (lowerRankWeight s w j + w j / 2) ^ 2 := by
              rw [Finset.sum_insert ha, hprefixa]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [hprefix j hj]
        _ = w a * ((∑ i ∈ s, w i) + w a / 2) ^ 2 +
            ((∑ j ∈ s, w j) ^ 3 / 3 -
              (∑ j ∈ s, w j ^ 3) / 12) := by rw [ih]
        _ = (∑ j ∈ insert a s, w j) ^ 3 / 3 -
            (∑ j ∈ insert a s, w j ^ 3) / 12 := by
              rw [Finset.sum_insert ha, Finset.sum_insert ha]
              ring

private theorem twice_lower_rank_pairs_add_equal_rank_pairs
    {V : Type*} (C : Finset V) (b : V → ℤ) :
    2 * (∑ x ∈ C, ((C.filter fun z => b z < b x).card : ℝ)) +
        (∑ x ∈ C, ((C.filter fun z => b z = b x).card : ℝ)) =
      (C.card : ℝ) ^ 2 := by
  classical
  let L : V → V → ℝ := fun x z => if b z < b x then 1 else 0
  let E : V → V → ℝ := fun x z => if b z = b x then 1 else 0
  have htri (x z : V) : L x z + L z x + E x z = 1 := by
    dsimp [L, E]
    split_ifs <;> norm_num <;> omega
  have hswap :
      (∑ x ∈ C, ∑ z ∈ C, L z x) =
        ∑ x ∈ C, ∑ z ∈ C, L x z := by
    rw [Finset.sum_comm]
  have hlower (x : V) :
      ((C.filter fun z => b z < b x).card : ℝ) =
        ∑ z ∈ C, L x z := by
    change ((C.filter fun z => b z < b x).card : ℝ) =
      ∑ z ∈ C, if b z < b x then 1 else 0
    exact (Finset.sum_boole (fun z : V => b z < b x) C).symm
  have hequal (x : V) :
      ((C.filter fun z => b z = b x).card : ℝ) =
        ∑ z ∈ C, E x z := by
    change ((C.filter fun z => b z = b x).card : ℝ) =
      ∑ z ∈ C, if b z = b x then 1 else 0
    exact (Finset.sum_boole (fun z : V => b z = b x) C).symm
  simp_rw [hlower, hequal]
  calc
    2 * (∑ x ∈ C, ∑ z ∈ C, L x z) +
        (∑ x ∈ C, ∑ z ∈ C, E x z) =
      ∑ x ∈ C, ∑ z ∈ C, (L x z + L z x + E x z) := by
        simp_rw [Finset.sum_add_distrib]
        rw [hswap]
        ring
    _ = ∑ x ∈ C, ∑ _z ∈ C, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      exact htri x z
    _ = (C.card : ℝ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, pow_two]

private theorem sum_componentVertexMidrank
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C, componentVertexMidrank C b x) =
      (C.card : ℝ) / 2 := by
  have hcard : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  have hpairs := twice_lower_rank_pairs_add_equal_rank_pairs C b
  unfold componentVertexMidrank
  rw [← Finset.sum_div]
  have hnum :
      (∑ x ∈ C,
        (((C.filter fun z => b z < b x).card : ℝ) +
          ((C.filter fun z => b z = b x).card : ℝ) / 2)) =
        (C.card : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    linarith
  rw [hnum]
  field_simp

private theorem componentVertexMidrank_eq_ordered_midpoint
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x =
      lowerRankWeight (C.image b) (componentRankMass C b) (b x) +
        componentRankMass C b (b x) / 2 := by
  simpa only [lowerRankWeight] using
    componentVertexMidrank_eq_sum_componentRankMass C b x

private theorem sum_componentVertexMidrank_sq_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C, componentVertexMidrank C b x ^ 2) =
      (C.card : ℝ) *
        ((1 : ℝ) / 3 -
          (∑ j ∈ C.image b, componentRankMass C b j ^ 3) / 12) := by
  classical
  have hcard : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := C) (t := C.image b) (g := b)
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun x => componentVertexMidrank C b x ^ 2)
  calc
    (∑ x ∈ C, componentVertexMidrank C b x ^ 2) =
        ∑ j ∈ C.image b,
          ∑ x ∈ C.filter (fun x => b x = j),
            componentVertexMidrank C b x ^ 2 := hfiber.symm
    _ = ∑ j ∈ C.image b,
          ((C.filter fun x => b x = j).card : ℝ) *
            (lowerRankWeight (C.image b) (componentRankMass C b) j +
              componentRankMass C b j / 2) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (∑ x ∈ C.filter (fun x => b x = j),
                componentVertexMidrank C b x ^ 2) =
              ∑ _x ∈ C.filter (fun x => b x = j),
                (lowerRankWeight (C.image b) (componentRankMass C b) j +
                  componentRankMass C b j / 2) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    have hbx : b x = j := (Finset.mem_filter.mp hx).2
                    rw [componentVertexMidrank_eq_ordered_midpoint C b x, hbx]
            _ = ((C.filter fun x => b x = j).card : ℝ) *
                (lowerRankWeight (C.image b) (componentRankMass C b) j +
                  componentRankMass C b j / 2) ^ 2 := by
                    simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (C.card : ℝ) *
          (∑ j ∈ C.image b,
            componentRankMass C b j *
              (lowerRankWeight (C.image b) (componentRankMass C b) j +
                componentRankMass C b j / 2) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hweight :
              ((C.filter fun x => b x = j).card : ℝ) =
                (C.card : ℝ) * componentRankMass C b j := by
            unfold componentRankMass
            field_simp
          rw [hweight]
          ring
    _ = (C.card : ℝ) *
          (((∑ j ∈ C.image b, componentRankMass C b j) ^ 3 / 3) -
            (∑ j ∈ C.image b, componentRankMass C b j ^ 3) / 12) := by
          rw [sum_weighted_ordered_midpoints_sq]
    _ = (C.card : ℝ) *
          ((1 : ℝ) / 3 -
            (∑ j ∈ C.image b, componentRankMass C b j ^ 3) / 12) := by
          rw [sum_componentRankMass C b hC]
          norm_num

private theorem componentRankMassList_cube_sum
    {V : Type*}
    (C : Finset V) (b : V → ℤ) :
    ((componentRankMassList C b).map fun p => p ^ 3).sum =
      ∑ j ∈ C.image b, componentRankMass C b j ^ 3 := by
  unfold componentRankMassList
  simp only [List.map_map]
  exact sum_map_sort_eq (C.image b)
    (fun j => componentRankMass C b j ^ 3)

private theorem componentVertexMidrank_variance_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C,
      (componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
      (C.card : ℝ) *
        midrankVariance (componentRankMassList C b) := by
  have hcenter :
      (∑ x ∈ C,
        (componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
        (∑ x ∈ C, componentVertexMidrank C b x ^ 2) -
          (∑ x ∈ C, componentVertexMidrank C b x) +
          (C.card : ℝ) / 4 := by
    calc
      (∑ x ∈ C,
        (componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
          ∑ x ∈ C,
            (componentVertexMidrank C b x ^ 2 -
              componentVertexMidrank C b x + (1 / 4 : ℝ)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
      _ = (∑ x ∈ C, componentVertexMidrank C b x ^ 2) -
          (∑ x ∈ C, componentVertexMidrank C b x) +
          (C.card : ℝ) / 4 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [div_eq_mul_inv, one_mul, Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ x ∈ C,
      (componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
        (C.card : ℝ) *
            ((1 : ℝ) / 3 -
              (∑ j ∈ C.image b,
                componentRankMass C b j ^ 3) / 12) -
          (C.card : ℝ) / 2 + (C.card : ℝ) / 4 := by
            rw [hcenter, sum_componentVertexMidrank_sq_eq C b hC,
              sum_componentVertexMidrank C b hC]
    _ = (C.card : ℝ) *
        midrankVariance (componentRankMassList C b) := by
          rw [midrankVariance_eq
            (componentRankMassList C b)
            (componentRankMassList_sum C b hC),
            componentRankMassList_cube_sum C b]
          ring

private theorem componentVertexMidrank_finiteMean_eq_half
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    CheegerPoincare.finiteMean
      (fun x : {x // x ∈ C} =>
        componentVertexMidrank C b x) =
      (1 / 2 : ℝ) := by
  have hc : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  unfold CheegerPoincare.finiteMean
  rw [← Finset.sum_subtype C (fun _ => Iff.rfl)
    (componentVertexMidrank C b),
    Fintype.card_coe,
    ComponentMidrankVariance.sum_componentVertexMidrank C b hC]
  field_simp

public
theorem componentVertexMidrank_finiteVariance_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    CheegerPoincare.finiteVariance
      (fun x : {x // x ∈ C} =>
        componentVertexMidrank C b x) =
      midrankVariance (componentRankMassList C b) := by
  have hc : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  unfold CheegerPoincare.finiteVariance
  rw [componentVertexMidrank_finiteMean_eq_half C b hC,
    ← Finset.sum_subtype C (fun _ => Iff.rfl)
      (fun x =>
        (componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2),
    Fintype.card_coe,
    ComponentMidrankVariance.componentVertexMidrank_variance_eq
      C b hC]
  field_simp

end ComponentMidrankVariance

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def insufficientOverlapComponents
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun C =>
    ((C ∩ maximumOverlapPart Q C).card : ℝ) <
      (1 - eta) * (C.card : ℝ)

public
theorem insufficientOverlapComponents_subset
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) :
    insufficientOverlapComponents P Q eta ⊆ P.parts := by
  classical
  exact Finset.filter_subset _ _

public
theorem insufficientOverlapComponents_mass_le_loss
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) :
    eta * (∑ C ∈ insufficientOverlapComponents P Q eta,
        (C.card : ℝ)) ≤
      ∑ C ∈ P.parts,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
  classical
  calc
    eta * (∑ C ∈ insufficientOverlapComponents P Q eta,
        (C.card : ℝ)) =
      ∑ C ∈ insufficientOverlapComponents P Q eta,
        eta * (C.card : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ C ∈ insufficientOverlapComponents P Q eta,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          have hbad :=
            (Finset.mem_filter.mp
              (show C ∈ P.parts.filter (fun C =>
                ((C ∩ maximumOverlapPart Q C).card : ℝ) <
                  (1 - eta) * (C.card : ℝ)) from hC)).2
          linarith
    _ ≤ ∑ C ∈ P.parts,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (insufficientOverlapComponents_subset P Q eta)
          intro C _ _
          exact sub_nonneg.mpr (by
            exact_mod_cast Finset.card_le_card
              (Finset.inter_subset_left :
                C ∩ maximumOverlapPart Q C ⊆ C))

private noncomputable def finsetPermutationOrderIso
    {V : Type u} (T : Equiv.Perm V) : Finset V ≃o Finset V where
  toEquiv := T.finsetCongr
  map_rel_iff' := by
    intro A B
    exact Finset.map_subset_map

private noncomputable def transportedFinpartition
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V) :
    Finpartition (U.map T.toEmbedding) :=
  Q.map (finsetPermutationOrderIso T)

@[simp]
private theorem transportedFinpartition_parts
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V) :
    (transportedFinpartition Q T).parts =
      Q.parts.image (fun C : Finset V => C.map T.toEmbedding) := by
  classical
  change Q.parts.map (finsetPermutationOrderIso T).toEmbedding =
    Q.parts.image (fun C : Finset V => C.map T.toEmbedding)
  exact Finset.map_eq_image (finsetPermutationOrderIso T).toEmbedding Q.parts

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def transportedUnivFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) : Finpartition (Finset.univ : Finset V) :=
  (transportedFinpartition Q T).copy (Finset.map_univ_equiv T)

@[simp]
public
theorem transportedUnivFinpartition_parts
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) :
    (transportedUnivFinpartition Q T).parts =
      Q.parts.image (fun C : Finset V => C.map T.toEmbedding) := by
  exact transportedFinpartition_parts Q T

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def partitionComponentSize
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (x : V) : ℕ :=
  (Q.part x).card

public
theorem partitionComponentSize_eq_card_of_mem
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) (hC : C ∈ Q.parts)
    (x : V) (hx : x ∈ C) :
    partitionComponentSize Q x = C.card := by
  unfold partitionComponentSize
  rw [Q.part_eq_of_mem hC hx]

private theorem partitionComponentSize_transport_lower_of_overlap
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V)
    (C D : Finset V) (hC : C ∈ Q.parts) (hD : D ∈ Q.parts)
    (eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤
        (((C.map T.toEmbedding) ∩ D).card : ℝ))
    (x : V) (hx : x ∈ C) (hTx : T x ∈ D) :
    (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by
  rw [partitionComponentSize_eq_card_of_mem Q C hC x hx,
    partitionComponentSize_eq_card_of_mem Q D hD (T x) hTx]
  calc
    (1 - eta) * (C.card : ℝ) ≤
      (((C.map T.toEmbedding) ∩ D).card : ℝ) := hoverlap
    _ ≤ (D.card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_right : (C.map T.toEmbedding) ∩ D ⊆ D)

public
theorem maximumOverlapPart_overlap_of_not_mem_insufficient
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) (C : Finset V)
    (hC : C ∈ P.parts)
    (hretained : C ∉ insufficientOverlapComponents P Q eta) :
    (1 - eta) * (C.card : ℝ) ≤
      ((C ∩ maximumOverlapPart Q C).card : ℝ) := by
  classical
  apply le_of_not_gt
  intro hbad
  apply hretained
  change C ∈ P.parts.filter (fun C =>
    ((C ∩ maximumOverlapPart Q C).card : ℝ) <
      (1 - eta) * (C.card : ℝ))
  exact Finset.mem_filter.mpr ⟨hC, hbad⟩

public
theorem partitionComponentSize_transport_lower_of_retained
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (eta : ℝ)
    (hretained : C.map T.toEmbedding ∉
      insufficientOverlapComponents
        (transportedUnivFinpartition Q T) Q eta)
    (x : V) (hx : x ∈ C)
    (hTx : T x ∈ maximumOverlapPart Q (C.map T.toEmbedding)) :
    (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by
  have htransport : C.map T.toEmbedding ∈
      (transportedUnivFinpartition Q T).parts := by
    rw [transportedUnivFinpartition_parts]
    exact Finset.mem_image_of_mem
      (fun C : Finset V => C.map T.toEmbedding) hC
  have hsize := maximumOverlapPart_overlap_of_not_mem_insufficient
    (transportedUnivFinpartition Q T) Q eta
    (C.map T.toEmbedding) htransport hretained
  have hsize' :
      (1 - eta) * (C.card : ℝ) ≤
        (((C.map T.toEmbedding) ∩
          maximumOverlapPart Q (C.map T.toEmbedding)).card : ℝ) := by
    simpa only [Finset.card_map] using hsize
  have htarget := maximumOverlapPart_mem Q
    (C.map T.toEmbedding)
    ((Finset.map_nonempty).2 (Q.nonempty_of_mem_parts hC))
    (Finset.subset_univ _)
  exact partitionComponentSize_transport_lower_of_overlap Q T C
    (maximumOverlapPart Q (C.map T.toEmbedding)) hC htarget
    eta hsize' x hx hTx

namespace ThompsonPrefixInsertion

open scoped BigOperators

private def singletonPrefixCode (a : List (Fin 2)) : BinaryPrefixCode (Fin 1) where
  word _ := a
  prefix_free := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

private theorem singletonPrefixCode_codeIdempotent (a : List (Fin 2)) :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)) =
      leavittCylinder a := by
  simp only [MatrixCorner.codeIdempotent, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    singletonPrefixCode, Finset.sum_const, Finset.card_singleton, one_smul, leavittCylinder]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def prefixInsertionHom (a : List (Fin 2)) :
    BinaryLeavittˣ →* BinaryLeavittˣ :=
  (prefixCornerUnitHom (singletonPrefixCode a)).comp
    (Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv).toMonoidHom

public
theorem prefixInsertionHom_injective (a : List (Fin 2)) :
    Function.Injective (prefixInsertionHom a) :=
  (prefixCornerUnitHom_injective (singletonPrefixCode a)).comp
    (Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv).injective


private def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  (idempotentCornerUnitExtension (ThompsonPrefixLocal.leavittCylinder_isIdempotent a)).range

private theorem cylinderCornerGroup_eq_source (a : List (Fin 2)) :
    cylinderCornerGroup a = ThompsonPrefixLocal.cylinderCornerGroup a := by
  rfl

private theorem prefixInsertionHom_mem_cylinderCorner
    (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    prefixInsertionHom a u ∈ cylinderCornerGroup a := by
  unfold cylinderCornerGroup
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS ((singletonPrefixCode a).word i))
    (fun i => leavittWordT ((singletonPrefixCode a).word i))
    (binaryPrefixCode_orthogonal (singletonPrefixCode a))
  have hidem :
      (⟨MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)), he⟩ :
          {e : BinaryLeavitt // IsIdempotentElem e}) =
        ⟨leavittCylinder a, ThompsonPrefixLocal.leavittCylinder_isIdempotent a⟩ :=
    Subtype.ext (singletonPrefixCode_codeIdempotent a)
  have hcorner := congrArg
    (fun p : {e : BinaryLeavitt // IsIdempotentElem e} =>
      (idempotentCornerUnitExtension p.property).range)
    hidem
  rw [← hcorner]
  refine ⟨(Units.mapEquiv
      (binaryPrefixCornerEquiv (singletonPrefixCode a)).toMulEquiv)
    ((Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv) u), ?_⟩
  rfl

public
theorem prefixInsertionHom_val (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    (↑(prefixInsertionHom a u) : BinaryLeavitt) =
      leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
        (1 - leavittCylinder a) := by
  change
    MatrixCorner.encode
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))
        ((Matrix.uniqueRingEquiv (m := Fin 1)
          (A := BinaryLeavitt)).symm (u : BinaryLeavitt)) +
      (1 - MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))) = _
  simp only [MatrixCorner.encode, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    singletonPrefixCode,
    Matrix.uniqueRingEquiv_symm_apply, Matrix.of_apply, Finset.sum_const, Finset.card_singleton,
      one_smul,
    MatrixCorner.codeIdempotent, leavittCylinder]

private theorem transpositionValue_mul_self {A : Type*} [Ring A]
    (sa ta sb tb : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0) :
    PrefixCompression.transpositionValue sa ta sb tb *
      PrefixCompression.transpositionValue sa ta sb tb = 1 := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hab, hba, haa', hbb', hab', hba']

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def cylinderSwap (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) : BinaryLeavittˣ where
  val := PrefixCompression.wordSwapValue a b
  inv := PrefixCompression.wordSwapValue a b
  val_inv := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)
  inv_val := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)

private theorem append_not_prefix_append (a b x y : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    ¬ a ++ x <+: b ++ y := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hle : a.length ≤ b.length
  · exact hab ((List.isPrefix_append_of_length hle).mp ha)
  · apply hba
    rw [List.prefix_iff_eq_take]
    have hea := List.prefix_iff_eq_take.mp ha
    rw [hea, List.take_take, Nat.min_eq_left (Nat.le_of_not_ge hle)]
    simp only [List.take_left']

private theorem prepend_not_prefix_prepend (l a b : List (Fin 2))
    (hab : ¬ a <+: b) :
    ¬ l ++ a <+: l ++ b := by
  intro h
  apply hab
  simpa only [List.prefix_append_right_inj] using h

private theorem prefixInsertionHom_cylinderSwap
    (l a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom l (cylinderSwap a b hab hba) =
      cylinderSwap (l ++ a) (l ++ b)
        (prepend_not_prefix_prepend l a b hab)
        (prepend_not_prefix_prepend l b a hba) := by
  apply Units.ext
  rw [prefixInsertionHom_val]
  change
    leavittWordS l *
        (1 - leavittWordS a * leavittWordT a -
          leavittWordS b * leavittWordT b +
          leavittWordS a * leavittWordT b +
          leavittWordS b * leavittWordT a) * leavittWordT l +
        (1 - leavittWordS l * leavittWordT l) =
      1 - leavittWordS (l ++ a) * leavittWordT (l ++ a) -
        leavittWordS (l ++ b) * leavittWordT (l ++ b) +
        leavittWordS (l ++ a) * leavittWordT (l ++ b) +
        leavittWordS (l ++ b) * leavittWordT (l ++ a)
  rw [leavittWordS_append, leavittWordT_append,
    leavittWordS_append, leavittWordT_append]
  simp only [CharTwo.sub_eq_add]
  noncomm_ring
  simp only [zsmul_eq_mul, Int.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add]

private theorem transpositionValue_braid {A : Type*} [Ring A]
    (sa ta sb tb sc tc : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1) (hcc : tc * sc = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (hac : ta * sc = 0) (hca : tc * sa = 0)
    (hbc : tb * sc = 0) (hcb : tc * sb = 0) :
    PrefixCompression.transpositionValue sa ta sc tc *
        PrefixCompression.transpositionValue sb tb sc tc *
        PrefixCompression.transpositionValue sa ta sc tc =
      PrefixCompression.transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hcc' (x : A) : tc * (sc * x) = x := by
    rw [← mul_assoc, hcc, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have hac' (x : A) : ta * (sc * x) = 0 := by
    rw [← mul_assoc, hac, zero_mul]
  have hca' (x : A) : tc * (sa * x) = 0 := by
    rw [← mul_assoc, hca, zero_mul]
  have hbc' (x : A) : tb * (sc * x) = 0 := by
    rw [← mul_assoc, hbc, zero_mul]
  have hcb' (x : A) : tc * (sb * x) = 0 := by
    rw [← mul_assoc, hcb, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hcc, hab, hba, hac, hca, hbc, hcb,
    haa', hbb', hcc', hab', hba', hac', hca', hbc', hcb']

private def prefixCrossRoot {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit E i j hij
    (leavittWordS a * leavittWordT b)

private theorem prefixCrossRoot_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossRoot E i j hij a b ∈ prefixElementaryGroup E :=
  Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩

private def prefixCrossSwap {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixCrossRoot E i j hij a b *
    prefixCrossRoot E j i hij.symm b a *
    prefixCrossRoot E i j hij a b

private theorem prefixCrossSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossSwap E i j hij a b ∈ prefixElementaryGroup E :=
  (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem
      (prefixCrossRoot_mem E i j hij a b)
      (prefixCrossRoot_mem E j i hij.symm b a))
    (prefixCrossRoot_mem E i j hij a b)

private theorem prefixCrossSwap_val {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    (↑(prefixCrossSwap E i j hij a b) : BinaryLeavitt) =
      PrefixCompression.wordSwapValue
        (E.word i ++ a) (E.word j ++ b) := by
  let A : List (Fin 2) := E.word i ++ a
  let B : List (Fin 2) := E.word j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 := by
    apply leavittWordT_mul_wordS_of_incomparable B A
    · exact append_not_prefix_append (E.word j) (E.word i)
        b a (E.prefix_free hij.symm) (E.prefix_free hij)
    · exact append_not_prefix_append (E.word i) (E.word j)
        a b (E.prefix_free hij) (E.prefix_free hij.symm)
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp only [mul_zero, zero_mul]
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  change
    (1 + leavittWordS (E.word i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) *
      (1 + leavittWordS (E.word j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (E.word i)) *
      (1 + leavittWordS (E.word i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) = _
  have hleft :
      leavittWordS (E.word i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (E.word j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (E.word j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (E.word i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl

private theorem samePrefixCylinderSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j)
    (a b c : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) ∈
      prefixElementaryGroup E := by
  let x := prefixCrossSwap E i j hij a c
  let y := prefixCrossSwap E i j hij b c
  have hx : x ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij a c
  have hy : y ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij b c
  have hfactor : x * y * x =
      cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) := by
    apply Units.ext
    change
      (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij b c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) =
        PrefixCompression.wordSwapValue (E.word i ++ a) (E.word i ++ b)
    rw [prefixCrossSwap_val, prefixCrossSwap_val]
    exact transpositionValue_braid
      (leavittWordS (E.word i ++ a))
      (leavittWordT (E.word i ++ a))
      (leavittWordS (E.word i ++ b))
      (leavittWordT (E.word i ++ b))
      (leavittWordS (E.word j ++ c))
      (leavittWordT (E.word j ++ c))
      (leavittWordT_mul_wordS_self (E.word i ++ a))
      (leavittWordT_mul_wordS_self (E.word i ++ b))
      (leavittWordT_mul_wordS_self (E.word j ++ c))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word i ++ a)
        (prepend_not_prefix_prepend (E.word i) b a hba)
        (prepend_not_prefix_prepend (E.word i) a b hab))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ a)
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ b)
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
  rw [← hfactor]
  exact (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem hx hy) hx

private theorem sourceLocal_cylinderSwap_mem_alpha
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom [0, 0, 0, 1] (cylinderSwap a b hab hba) ∈
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixInsertionHom_cylinderSwap]
  have h := samePrefixCylinderSwap_mem alphaPrefixCode
    (0 : Fin 3) (1 : Fin 3) (by decide)
    ([1] ++ a) ([1] ++ b) []
    (prepend_not_prefix_prepend [1] a b hab)
    (prepend_not_prefix_prepend [1] b a hba)
  simpa only [alphaPrefixCode, Fin.isValue, List.cons_append, List.nil_append, alphaWord] using h

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def binaryPrefixTranspositionGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (a b : List (Fin 2))
      (hab : ¬ a <+: b) (hba : ¬ b <+: a),
      cylinderSwap a b hab hba = z}

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def localPrefixTranspositionGroup
    (l : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  binaryPrefixTranspositionGroup.map (prefixInsertionHom l)

private theorem localPrefixTranspositionGroup_le_cylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤ cylinderCornerGroup l := by
  rintro _ ⟨u, _, rfl⟩
  exact prefixInsertionHom_mem_cylinderCorner l u

private theorem localPrefixTranspositionGroup_le_sourceCylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤
      ThompsonPrefixLocal.cylinderCornerGroup l := by
  rw [← cylinderCornerGroup_eq_source]
  exact localPrefixTranspositionGroup_le_cylinderCorner l

private theorem sourceLocalPrefixTranspositionGroup_le_alpha :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup alphaPrefixCode := by
  apply (Subgroup.map_le_iff_le_comap).2
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a, b, hab, hba, rfl⟩
  exact sourceLocal_cylinderSwap_mem_alpha a b hab hba

public
theorem sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup alphaPrefixCode := by
  exact sourceLocalPrefixTranspositionGroup_le_alpha

private theorem sourceLocalPrefixTranspositionGroup_le_nine :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup ninePrefixCode :=
  sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord.trans
    SourceGeneration.alphaPrefixElementaryGroup_le_nine

private theorem sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) :=
  (localPrefixTranspositionGroup_le_sourceCylinderCorner
    [0, 0, 0, 1]).trans
    ThompsonPrefixLocal.localCylinderCorner_le_centralizer_alphaZero

private theorem alphaZero_inf_sourceLocalPrefixTranspositionGroup_eq_bot :
    prefixElementaryGroup alphaZeroPrefixCode ⊓
        localPrefixTranspositionGroup [0, 0, 0, 1] = ⊥ := by
  apply le_antisymm
  · calc
      prefixElementaryGroup alphaZeroPrefixCode ⊓
          localPrefixTranspositionGroup [0, 0, 0, 1] ≤
        prefixElementaryGroup alphaZeroPrefixCode ⊓
          ThompsonPrefixLocal.cylinderCornerGroup
            [0, 0, 0, 1] :=
          inf_le_inf_left _
            (localPrefixTranspositionGroup_le_sourceCylinderCorner
              [0, 0, 0, 1])
      _ = ⊥ := ThompsonPrefixLocal.alphaZero_inf_localCylinderCorner_eq_bot
  · exact bot_le

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressedLocalProductHom :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup [0, 0, 0, 1]) →*
        BinaryLeavittˣ where
  toFun x := (x.1 : BinaryLeavittˣ) * (x.2 : BinaryLeavittˣ)
  map_one' := by simp only [Prod.fst_one, OneMemClass.coe_one, Prod.snd_one, mul_one]
  map_mul' p q := by
    have hcomm :
        (q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ) =
          (p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ) :=
      Subgroup.mem_centralizer_iff.mp
        (sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero
          p.2.property)
        (q.1 : BinaryLeavittˣ) q.1.property
    change
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ))
    calc
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        (p.1 : BinaryLeavittˣ) *
          (((q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by simp only [mul_assoc]
      _ = (p.1 : BinaryLeavittˣ) *
          (((p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by rw [hcomm]
      _ = ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) := by
            simp only [mul_assoc]

private theorem sourceCompressedLocalProductHom_injective :
    Function.Injective sourceCompressedLocalProductHom := by
  apply (injective_iff_map_eq_one sourceCompressedLocalProductHom).2
  rintro ⟨k, j⟩ hone
  change (k : BinaryLeavittˣ) * (j : BinaryLeavittˣ) = 1 at hone
  have hkinv : (k : BinaryLeavittˣ) = (j : BinaryLeavittˣ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hone
  have hkJ :
      (k : BinaryLeavittˣ) ∈
        localPrefixTranspositionGroup [0, 0, 0, 1] := by
    rw [hkinv]
    exact (localPrefixTranspositionGroup
      [0, 0, 0, 1]).inv_mem j.property
  have hkbot :
      (k : BinaryLeavittˣ) ∈
        prefixElementaryGroup alphaZeroPrefixCode ⊓
          localPrefixTranspositionGroup
            [0, 0, 0, 1] :=
    ⟨k.property, hkJ⟩
  rw [alphaZero_inf_sourceLocalPrefixTranspositionGroup_eq_bot] at hkbot
  have hkone : (k : BinaryLeavittˣ) = 1 := by
    simpa only [OneMemClass.coe_eq_one, Subgroup.mem_bot] using hkbot
  have hjone : (j : BinaryLeavittˣ) = 1 := by
    simpa only [OneMemClass.coe_eq_one, hkone, one_mul] using hone
  apply Prod.ext
  · exact Subtype.ext hkone
  · exact Subtype.ext hjone

private theorem sourceCompressedLocalProductHom_range_le_nine :
    sourceCompressedLocalProductHom.range ≤
      prefixElementaryGroup ninePrefixCode := by
  rintro _ ⟨⟨k, j⟩, rfl⟩
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    (SourceGeneration.alphaPrefixElementaryGroup_le_nine
      (alphaZero_prefixElementaryGroup_le k.property))
    (sourceLocalPrefixTranspositionGroup_le_nine j.property)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressedLocalProductEmbedding :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup [0, 0, 0, 1]) →*
        prefixElementaryGroup ninePrefixCode :=
  sourceCompressedLocalProductHom.codRestrict
    (prefixElementaryGroup ninePrefixCode)
    (fun x => sourceCompressedLocalProductHom_range_le_nine ⟨x, rfl⟩)

public
theorem sourceCompressedLocalProductEmbedding_injective :
    Function.Injective sourceCompressedLocalProductEmbedding := by
  intro x y hxy
  apply sourceCompressedLocalProductHom_injective
  exact congrArg Subtype.val hxy

end ThompsonPrefixInsertion

namespace MidrankPermutationEnergy

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def partitionVertexMidrank {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ) (x : V) : ℝ :=
  componentVertexMidrank (P.part x) b x

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def rankDecreasingVertices {V : Type*}
    (U : Finset V) (b : V → ℤ) (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (p x) < b x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def offsetFloorRank {V : Type*} (u : V → ℝ) (H r : ℝ) : V → ℤ :=
  fun x => ⌊(u x + r) / H⌋

public
theorem rankDropCount_eq_sum_rankDecreasingVertices
    {V ι : Type*} [Fintype V] [Fintype ι]
    (u : V → ℝ) (p : ι → Equiv.Perm V) (H r : ℝ) :
    rankDropCount
      (fun e : ι × V => u e.2)
      (fun e : ι × V => u (p e.1 e.2)) H r =
        ∑ i : ι,
          ((rankDecreasingVertices Finset.univ
            (offsetFloorRank u H r) (p i)).card : ℝ) := by
  classical
  unfold rankDropCount
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  unfold rankDecreasingVertices offsetFloorRank
  exact Finset.sum_boole
    (fun x : V =>
      ⌊(u (p i x) + r) / H⌋ < ⌊(u x + r) / H⌋)
    Finset.univ

private def midpointDecreasingVertices {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ)
    (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => partitionVertexMidrank P b (p x) <
    partitionVertexMidrank P b x)

private theorem midpointDecreasing_subset_crossing_union_rankDecreasing
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (p : Equiv.Perm V) :
    midpointDecreasingVertices P b p ⊆
      partitionWordCrossing P p ∪ rankDecreasingVertices U b p := by
  intro x hx
  have hxmem := (Finset.mem_filter.mp hx).1
  have hxdec := (Finset.mem_filter.mp hx).2
  by_cases hcross : p x ∈ P.part x
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hxmem, ?_⟩
    by_contra hnot
    have hrank : b x ≤ b (p x) := le_of_not_gt hnot
    have hpart : P.part x ∈ P.parts := P.part_mem.mpr hxmem
    have hsame : P.part (p x) = P.part x :=
      P.part_eq_of_mem hpart hcross
    have hmono := componentVertexMidrank_mono (P.part x) b hrank
    unfold partitionVertexMidrank at hxdec
    rw [hsame] at hxdec
    exact (not_lt_of_ge hmono) hxdec
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨hxmem, hcross⟩

private theorem partitionVertexMidrank_permutation_energy_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (b : V → ℤ) (p : Equiv.Perm V) :
    (∑ x : V,
      (partitionVertexMidrank P b (p x) -
        partitionVertexMidrank P b x) ^ 2) ≤
      2 * ((partitionWordCrossing P p).card : ℝ) +
        2 * ((rankDecreasingVertices Finset.univ b p).card : ℝ) := by
  have hbase := permutation_squared_increment_le_twice_decreasing
    p (partitionVertexMidrank P b)
    (fun x => componentVertexMidrank_nonneg (P.part x) b x)
    (fun x => componentVertexMidrank_le_one (P.part x) b x)
  have hsubset :
      (Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) < partitionVertexMidrank P b x) ⊆
        partitionWordCrossing P p ∪
          rankDecreasingVertices Finset.univ b p := by
    exact midpointDecreasing_subset_crossing_union_rankDecreasing P b p
  have hcard :
      (Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) <
          partitionVertexMidrank P b x).card ≤
        (partitionWordCrossing P p).card +
          (rankDecreasingVertices Finset.univ b p).card :=
    (Finset.card_le_card hsubset).trans
      (Finset.card_union_le _ _)
  have hcast :
      ((Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) <
          partitionVertexMidrank P b x).card : ℝ) ≤
        ((partitionWordCrossing P p).card : ℝ) +
          ((rankDecreasingVertices Finset.univ b p).card : ℝ) := by
    exact_mod_cast hcard
  nlinarith

private theorem sum_partitionVertexMidrank_permutation_energy_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι)
    (P : Finpartition (Finset.univ : Finset V))
    (b : V → ℤ) (p : ι → Equiv.Perm V) :
    (∑ i ∈ I, ∑ x : V,
      (partitionVertexMidrank P b (p i x) -
        partitionVertexMidrank P b x) ^ 2) ≤
      2 * (∑ i ∈ I, ((partitionWordCrossing P (p i)).card : ℝ)) +
        2 * (∑ i ∈ I,
          ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
  calc
    (∑ i ∈ I, ∑ x : V,
        (partitionVertexMidrank P b (p i x) -
          partitionVertexMidrank P b x) ^ 2) ≤
      ∑ i ∈ I,
        (2 * ((partitionWordCrossing P (p i)).card : ℝ) +
          2 * ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact partitionVertexMidrank_permutation_energy_le P b (p i)
    _ = 2 * (∑ i ∈ I, ((partitionWordCrossing P (p i)).card : ℝ)) +
          2 * (∑ i ∈ I,
            ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

public
theorem partitionVertexMidrank_permutation_energy_tendsto_zero
    (V ι : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    [∀ n, Fintype (ι n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (p : (n : ℕ) → ι n → Equiv.Perm (V n))
    (N : ℕ → ℝ)
    (hN : ∀ n, 0 < N n)
    (hcross : Tendsto
      (fun n =>
        (∑ i : ι n, ((partitionWordCrossing (P n) (p n i)).card : ℝ)) /
          N n)
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        (∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n)
      atTop (nhds 0) := by
  have hnonnegative : ∀ n,
      0 ≤ (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n := by
    intro n
    apply div_nonneg _ (hN n).le
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg fun x hx => sq_nonneg _
  have hupper : ∀ n,
      (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n ≤
        2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n) := by
    intro n
    have hfinite := sum_partitionVertexMidrank_permutation_energy_le
      (Finset.univ : Finset (ι n)) (P n) (b n) (p n)
    have hdiv := (div_le_div_iff_of_pos_right (hN n)).2 hfinite
    calc
      (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n ≤
        (2 * (∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) +
         2 * (∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ))) /
            N n := hdiv
      _ = 2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n) := by ring
  have hlimit : Tendsto
      (fun n =>
        2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (Filter.Tendsto.const_mul (2 : ℝ) hcross).add (Filter.Tendsto.const_mul (2 : ℝ) hrank)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit

end MidrankPermutationEnergy

namespace RankArcCharging

open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def selectedRankSupport
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) : Finset V :=
  P.parts.biUnion (fun C => C.filter (fun x => b x = j C))

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def rankChangingArc
    {V : Type*}
    (U : Finset V) (b : V → ℤ) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (w x) ≠ b x)

private def rankSupportPreimageBad
    {V : Type*} [DecidableEq V]
    (U S : Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ S)

private theorem selectedRankSupport_subset
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    selectedRankSupport P b j ⊆ U := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact P.subset hC (Finset.mem_filter.mp hxC).1

private theorem selectedRankSupport_card
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    (selectedRankSupport P b j).card =
      ∑ C ∈ P.parts, (C.filter fun x => b x = j C).card := by
  unfold selectedRankSupport
  apply Finset.card_biUnion
  intro C hC D hD hne
  exact (P.disjoint hC hD hne).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

public
theorem card_sdiff_selectedRankSupport
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    (U \ selectedRankSupport P b j).card =
      ∑ C ∈ P.parts,
        (C.card - (C.filter fun x => b x = j C).card) := by
  rw [Finset.card_sdiff_of_subset (selectedRankSupport_subset P b j),
    selectedRankSupport_card]
  rw [Finset.sum_tsub_distrib]
  · rw [P.sum_card_parts]
  · intro C hC
    exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem selectedRankSupport_rank_eq
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    {x : V} (hx : x ∈ selectedRankSupport P b j) :
    b x = j (P.part x) := by
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hxmem, hxrank⟩ := Finset.mem_filter.mp hxC
  have hpart : P.part x = C := P.part_eq_of_mem hC hxmem
  simpa only [hpart] using hxrank

private theorem rankSupportPreimageBad_card_le
    {V : Type*} [DecidableEq V]
    (U S : Finset V) (w : Equiv.Perm V) :
    (rankSupportPreimageBad U S w).card ≤ (U \ S).card := by
  apply Finset.card_le_card_of_injOn w
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact w.injective hxy

private theorem rankChangingArc_subset_crossing_or_unselected
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    (w : Equiv.Perm V) :
    rankChangingArc U b w ⊆
      partitionWordCrossing P w ∪
        (U \ selectedRankSupport P b j) ∪
          rankSupportPreimageBad U (selectedRankSupport P b j) w := by
  intro x hx
  obtain ⟨hxU, hxchange⟩ := Finset.mem_filter.mp hx
  by_cases hxselected : x ∈ selectedRankSupport P b j
  · by_cases hcross : w x ∈ P.part x
    · by_cases hwselected : w x ∈ selectedRankSupport P b j
      · exfalso
        apply hxchange
        have hpart : P.part (w x) = P.part x :=
          P.part_eq_of_mem (P.part_mem.mpr hxU) hcross
        rw [selectedRankSupport_rank_eq P b j hwselected,
          selectedRankSupport_rank_eq P b j hxselected, hpart]
      · have hwU : w x ∈ U := P.part_subset x hcross
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hxU, Finset.mem_sdiff.mpr ⟨hwU, hwselected⟩⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hxU, hcross⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hxU, hxselected⟩))

private theorem rankChangingArc_card_le_crossing_add_unselected
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    (w : Equiv.Perm V) :
    (rankChangingArc U b w).card ≤
      (partitionWordCrossing P w).card +
        2 * (U \ selectedRankSupport P b j).card := by
  have hsubset := Finset.card_le_card
    (rankChangingArc_subset_crossing_or_unselected P b j w)
  have hfirst := Finset.card_union_le
    (partitionWordCrossing P w) (U \ selectedRankSupport P b j)
  have hsecond := Finset.card_union_le
    (partitionWordCrossing P w ∪ (U \ selectedRankSupport P b j))
    (rankSupportPreimageBad U (selectedRankSupport P b j) w)
  have hpre := rankSupportPreimageBad_card_le
    U (selectedRankSupport P b j) w
  omega

public
theorem rankChangingArc_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n))
    (P : ∀ n, Finpartition (U n))
    (b : ∀ n, V n → ℤ)
    (j : ∀ n, Finset (V n) → ℤ)
    (w : ∀ n, Equiv.Perm (V n))
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hcross : Filter.Tendsto
      (fun n => ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0))
    (homit : Filter.Tendsto
      (fun n =>
        (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
          N n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0) := by
  have hnonnegative : ∀ n,
      0 ≤ ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (hN n).le
  have hupper : ∀ n,
      ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n ≤
        ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n) := by
    intro n
    have hnat := rankChangingArc_card_le_crossing_add_unselected
      (P n) (b n) (j n) (w n)
    have hreal :
        ((rankChangingArc (U n) (b n) (w n)).card : ℝ) ≤
          ((partitionWordCrossing (P n) (w n)).card : ℝ) +
            2 * ((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) := by
      exact_mod_cast hnat
    calc
      ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n ≤
          (((partitionWordCrossing (P n) (w n)).card : ℝ) +
            2 * ((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ)) /
              N n :=
        div_le_div_of_nonneg_right hreal (hN n).le
      _ = ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n) := by
        ring
  have hlimit : Filter.Tendsto
      (fun n =>
        ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hcross.add (Filter.Tendsto.const_mul (2 : ℝ) homit)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit

end RankArcCharging

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationDistance {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : ℕ :=
  hammingDist (fun x => p x) (fun x => q x)

@[simp]
public
theorem permutationDistance_self {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : permutationDistance p p = 0 := by
  simp only [permutationDistance, hammingDist_self]

private theorem permutationDistance_comm {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : permutationDistance p q = permutationDistance q p := by
  exact hammingDist_comm _ _

private theorem permutationDistance_triangle {V : Type*}
    [Fintype V] [DecidableEq V] (p q r : Equiv.Perm V) :
    permutationDistance p r ≤ permutationDistance p q + permutationDistance q r :=
  hammingDist_triangle _ _ _

private theorem permutationDistance_mul_left {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (s * p) (s * q) = permutationDistance p q := by
  have h := hammingDist_comp (fun (_ : V) (x : V) => s x)
    (x := fun x => p x) (y := fun x => q x) (fun _ => s.injective)
  simpa only [permutationDistance, Equiv.Perm.mul_apply] using h

private theorem permutationDistance_mul_right {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (p * s) (q * s) = permutationDistance p q := by
  unfold permutationDistance hammingDist
  apply Finset.card_bij (fun x _ => s x)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact s.injective h
  · intro y hy
    refine ⟨s.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp hy).2

private theorem permutationDistance_mul_le {V : Type*}
    [Fintype V] [DecidableEq V] (p p' q q' : Equiv.Perm V) :
    permutationDistance (p * q) (p' * q') ≤
      permutationDistance p p' + permutationDistance q q' := by
  calc
    permutationDistance (p * q) (p' * q') ≤
        permutationDistance (p * q) (p' * q) +
          permutationDistance (p' * q) (p' * q') :=
      permutationDistance_triangle _ _ _
    _ = permutationDistance p p' + permutationDistance q q' := by
      rw [permutationDistance_mul_right, permutationDistance_mul_left]

private theorem permutationDistance_inv {V : Type*}
    [Fintype V] [DecidableEq V] (p q : Equiv.Perm V) :
    permutationDistance p⁻¹ q⁻¹ = permutationDistance p q := by
  calc
    permutationDistance p⁻¹ q⁻¹ =
        permutationDistance (q * p⁻¹) (q * q⁻¹) :=
      (permutationDistance_mul_left q p⁻¹ q⁻¹).symm
    _ = permutationDistance (q * p⁻¹) 1 := by simp only [mul_inv_cancel]
    _ = permutationDistance ((q * p⁻¹) * p) (1 * p) :=
      (permutationDistance_mul_right p (q * p⁻¹) 1).symm
    _ = permutationDistance q p := by simp only [inv_mul_cancel_right, one_mul]
    _ = permutationDistance p q := permutationDistance_comm q p

@[simp]
public
theorem permutationCommutationDefect_one {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) :
    permutationCommutationDefect σ 1 = 0 := by
  simp only [permutationCommutationDefect, Equiv.Perm.coe_one, id_eq, ne_eq, not_true_eq_false,
    Finset.filter_false, Finset.card_empty, Finset.sum_const_zero]

private theorem permutationCommutationDefect_inv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) :
    permutationCommutationDefect σ c⁻¹ = permutationCommutationDefect σ c := by
  classical
  unfold permutationCommutationDefect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun x _ => c⁻¹ x)
  · intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    apply c.injective
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using heq.symm
  · intro x hx y hy heq
    exact (c⁻¹).injective heq
  · intro y hy
    have hbad := (Finset.mem_filter.mp hy).2
    refine ⟨c y, ?_, by simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    have heq' := congrArg c heq
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using heq'.symm

private theorem permutationCommutationDefect_mul_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p q : Equiv.Perm V) :
    permutationCommutationDefect σ (p * q) ≤
      permutationCommutationDefect σ p + permutationCommutationDefect σ q := by
  classical
  unfold permutationCommutationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let Bp : Finset V :=
    Finset.univ.filter fun x => p (σ i x) ≠ σ i (p x)
  let Bq : Finset V :=
    Finset.univ.filter fun x => q (σ i x) ≠ σ i (q x)
  let C : Finset V :=
    Finset.univ.filter fun x => q x ∈ Bp
  have hC : C.card = Bp.card := by
    apply Finset.card_bij (fun x _ => q x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact q.injective hxy
    · intro y hy
      refine ⟨q.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa only [Equiv.apply_symm_apply] using hy⟩
  have hsub :
      (Finset.univ.filter fun x =>
        (p * q) (σ i x) ≠ σ i ((p * q) x)) ⊆ Bq ∪ C := by
    intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    by_cases hq : q (σ i x) = σ i (q x)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hp
      apply hbad
      simpa only [Equiv.Perm.mul_apply, hq] using hp
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  calc
    (Finset.univ.filter fun x =>
      (p * q) (σ i x) ≠ σ i ((p * q) x)).card ≤
        (Bq ∪ C).card := Finset.card_le_card hsub
    _ ≤ Bq.card + C.card := Finset.card_union_le Bq C
    _ = Bp.card + Bq.card := by rw [hC, Nat.add_comm]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure AlmostCentralizerElement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  permutation : Equiv.Perm V
  defect_le : permutationCommutationDefect σ permutation ≤ tolerance

@[ext (iff := false)]
private theorem AlmostCentralizerElement.ext {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p q : AlmostCentralizerElement σ tolerance)
    (h : p.permutation = q.permutation) : p = q := by
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      cases h
      rfl

private instance almostCentralizerElementFinite {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) :
    Finite (AlmostCentralizerElement σ tolerance) :=
  Finite.of_injective (fun p => p.permutation)
    (fun p q hpq => AlmostCentralizerElement.ext p q hpq)

private structure AlmostCentralizerGap {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  dichotomy : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V ∨
      4 * Fintype.card V <
        5 * permutationDistance p.permutation q.permutation

private theorem almostCentralizerGap_of_expansion {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) (h : ℝ)
    (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤ (boundary σ A : ℝ))
    (hsmall : (10 : ℝ) * tolerance < h * Fintype.card V) :
    AlmostCentralizerGap σ tolerance := by
  constructor
  intro p q
  have hdef :
      ((permutationCommutationDefect σ p.permutation +
        permutationCommutationDefect σ q.permutation : ℕ) : ℝ) ≤
          2 * (tolerance : ℝ) := by
    have hnat : permutationCommutationDefect σ p.permutation +
        permutationCommutationDefect σ q.permutation ≤ 2 * tolerance := by
      have hp := p.defect_le
      have hq := q.defect_le
      omega
    exact_mod_cast hnat
  rcases hamming_dichotomy_of_expansion σ h hexp p.permutation q.permutation with
    hnear | hfar
  · left
    by_contra hnot
    have hlarge : Fintype.card V <
        5 * permutationDistance p.permutation q.permutation :=
      Nat.lt_of_not_ge hnot
    have hlarge' : (Fintype.card V : ℝ) <
        5 * (permutationDistance p.permutation q.permutation : ℝ) := by
      exact_mod_cast hlarge
    have hpos : 0 < h *
        (5 * (permutationDistance p.permutation q.permutation : ℝ) -
          Fintype.card V) :=
      mul_pos hpositive (sub_pos.mpr hlarge')
    change h * (permutationDistance p.permutation q.permutation : ℝ) ≤ _
      at hnear
    nlinarith
  · right
    by_contra hnot
    have hlarge :
        5 * permutationDistance p.permutation q.permutation ≤
          4 * Fintype.card V := Nat.le_of_not_gt hnot
    have hlarge' :
        5 * (permutationDistance p.permutation q.permutation : ℝ) ≤
          4 * (Fintype.card V : ℝ) := by
      exact_mod_cast hlarge
    have hpos : 0 ≤ h *
        (4 * (Fintype.card V : ℝ) -
          5 * (permutationDistance p.permutation q.permutation : ℝ)) :=
      mul_nonneg hpositive.le (sub_nonneg.mpr hlarge')
    change h * ((Fintype.card V : ℝ) -
      permutationDistance p.permutation q.permutation) ≤ _ at hfar
    nlinarith

private def almostCentralizerSetoid {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :
    Setoid (AlmostCentralizerElement σ tolerance) where
  r p q := 5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simp only [permutationDistance_self, mul_zero, zero_le]
    · intro p q hpq
      simpa only [permutationDistance_comm q.permutation p.permutation] using hpq
    · intro p q r hpq hqr
      rcases hgap.dichotomy p r with hclose | hfar
      · exact hclose
      · have htri := permutationDistance_triangle
          p.permutation q.permutation r.permutation
        omega

private abbrev AlmostCentralizerClusters {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :=
  Quotient (almostCentralizerSetoid σ tolerance hgap)

private def almostCentralizerCluster {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.mk (almostCentralizerSetoid σ tolerance hgap) p

private theorem almostCentralizerCluster_eq_iff {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    almostCentralizerCluster hgap p = almostCentralizerCluster hgap q ↔
      5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V := by
  exact Quotient.eq

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure AlmostCentralizerRepair {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  correct : Equiv.Perm V → Equiv.Perm V
  corrected_defect : ∀ p q : AlmostCentralizerElement σ tolerance,
    permutationCommutationDefect σ
      (correct (p.permutation * q.permutation)) ≤ tolerance
  corrected_distance : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance
      (correct (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure HasAlmostCentralizerImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  improve : ∀ p : Equiv.Perm V,
    permutationCommutationDefect σ p ≤ 2 * tolerance →
      ∃ q : Equiv.Perm V,
        permutationCommutationDefect σ q ≤ tolerance ∧
          5 * permutationDistance q p ≤ Fintype.card V

private def almostCentralizerRepairOfImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (h : HasAlmostCentralizerImprovement σ tolerance) :
    AlmostCentralizerRepair σ tolerance := by
  classical
  let correction : Equiv.Perm V → Equiv.Perm V := fun p =>
    if hp : permutationCommutationDefect σ p ≤ 2 * tolerance then
      (h.improve p hp).choose
    else p
  refine ⟨correction, ?_, ?_⟩
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change permutationCommutationDefect σ
      (correction (p.permutation * q.permutation)) ≤ tolerance
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.1
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change 5 * permutationDistance
      (correction (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.2

private def correctedAlmostCentralizerProduct {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (R : AlmostCentralizerRepair σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨R.correct (p.permutation * q.permutation), R.corrected_defect p q⟩

private theorem correctedAlmostCentralizerProduct_congr {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    {p p' q q' : AlmostCentralizerElement σ tolerance}
    (hp : 5 * permutationDistance p.permutation p'.permutation ≤
      Fintype.card V)
    (hq : 5 * permutationDistance q.permutation q'.permutation ≤
      Fintype.card V) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R p q).permutation
      (correctedAlmostCentralizerProduct R p' q').permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R p' q'
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance p' q'
  have hmul := permutationDistance_mul_le
    p.permutation p'.permutation q.permutation q'.permutation
  have htri₁ := permutationDistance_triangle a.permutation
    (p.permutation * q.permutation) b.permutation
  have htri₂ := permutationDistance_triangle
    (p.permutation * q.permutation)
    (p'.permutation * q'.permutation) b.permutation
  have hsym :
      permutationDistance (p'.permutation * q'.permutation) b.permutation =
        permutationDistance b.permutation
          (p'.permutation * q'.permutation) :=
    permutationDistance_comm _ _
  change 5 * permutationDistance a.permutation b.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy a b with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance a.permutation b.permutation at hfar
    change 5 * permutationDistance a.permutation
      (p.permutation * q.permutation) ≤ Fintype.card V at ha
    change 5 * permutationDistance b.permutation
      (p'.permutation * q'.permutation) ≤ Fintype.card V at hb
    omega

private def almostCentralizerClusterMul {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap →
        AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map₂ (correctedAlmostCentralizerProduct R)
    (fun _ _ hp _ _ hq =>
      correctedAlmostCentralizerProduct_congr hgap R hp hq)

private def almostCentralizerOne {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) :
    AlmostCentralizerElement σ tolerance :=
  ⟨1, by simp only [permutationCommutationDefect_one, zero_le]⟩

private def almostCentralizerInverse {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨p.permutation⁻¹, by
    rw [permutationCommutationDefect_inv]
    exact p.defect_le⟩

private def almostCentralizerClusterInv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map almostCentralizerInverse (by
    intro p q hpq
    change 5 * permutationDistance p.permutation⁻¹ q.permutation⁻¹ ≤
      Fintype.card V
    rwa [permutationDistance_inv])

private theorem correctedAlmostCentralizerProduct_assoc {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    (p q r : AlmostCentralizerElement σ tolerance) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R
        (correctedAlmostCentralizerProduct R p q) r).permutation
      (correctedAlmostCentralizerProduct R p
        (correctedAlmostCentralizerProduct R q r)).permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R q r
  let l := correctedAlmostCentralizerProduct R a r
  let t := correctedAlmostCentralizerProduct R p b
  have hl := R.corrected_distance a r
  have ht := R.corrected_distance p b
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance q r
  have ha' :
      5 * permutationDistance
        (a.permutation * r.permutation)
        ((p.permutation * q.permutation) * r.permutation) ≤
          Fintype.card V := by
    rw [permutationDistance_mul_right]
    exact ha
  have hb' :
      5 * permutationDistance
        ((p.permutation * q.permutation) * r.permutation)
        (p.permutation * b.permutation) ≤ Fintype.card V := by
    rw [mul_assoc, permutationDistance_mul_left,
      permutationDistance_comm]
    exact hb
  have ht' :
      5 * permutationDistance
        (p.permutation * b.permutation) t.permutation ≤
          Fintype.card V := by
    rw [permutationDistance_comm]
    exact ht
  have htri₁ := permutationDistance_triangle l.permutation
    (a.permutation * r.permutation) t.permutation
  have htri₂ := permutationDistance_triangle
    (a.permutation * r.permutation)
    ((p.permutation * q.permutation) * r.permutation) t.permutation
  have htri₃ := permutationDistance_triangle
    ((p.permutation * q.permutation) * r.permutation)
    (p.permutation * b.permutation) t.permutation
  change 5 * permutationDistance l.permutation t.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy l t with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance l.permutation t.permutation at hfar
    change 5 * permutationDistance l.permutation
      (a.permutation * r.permutation) ≤ Fintype.card V at hl
    omega

@[instance_reducible]
private def almostCentralizerClusterGroup {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    Group (AlmostCentralizerClusters σ tolerance hgap) := by
  letI : One (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerCluster hgap (almostCentralizerOne σ tolerance)⟩
  letI : Mul (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterMul hgap R⟩
  letI : Inv (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterInv hgap⟩
  apply Group.ofLeftAxioms
  · intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ p q r =>
      apply Quotient.sound
      exact correctedAlmostCentralizerProduct_assoc hgap R p q r
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (1 * p.permutation)) p.permutation ≤ Fintype.card V
      simpa only [one_mul, almostCentralizerOne] using R.corrected_distance (almostCentralizerOne σ
        tolerance) p
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (p.permutation⁻¹ * p.permutation)) 1 ≤ Fintype.card V
      simpa only [inv_mul_cancel, almostCentralizerInverse] using
        R.corrected_distance (almostCentralizerInverse p) p

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure ExpandingCentralizerFiniteModel (G : Type*) [Group G]
    (F : Finset G) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  vertices : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesFintype : Fintype vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesDecidableEq : DecidableEq vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generatorIndex : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [generatorFintype : Fintype generatorIndex]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generators : generatorIndex → Equiv.Perm vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  tolerance : ℕ
  /-- Internal interface connecting the split non-sofic proof modules. -/
  cheeger : ℝ
  cheeger_positive : 0 < cheeger
  expansion : ∀ A : Finset vertices,
    cheeger * min (A.card : ℝ)
        ((Fintype.card vertices : ℝ) - A.card) ≤
      (boundary generators A : ℝ)
  small : (10 : ℝ) * tolerance < cheeger * Fintype.card vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  repair : AlmostCentralizerRepair generators tolerance
  /-- Internal interface connecting the split non-sofic proof modules. -/
  approximation : G → AlmostCentralizerElement generators tolerance
  map_one : (approximation 1).permutation = 1
  multiplicative : ∀ x ∈ F, ∀ y ∈ F,
    5 * permutationDistance (approximation (x * y)).permutation
      ((approximation x).permutation * (approximation y).permutation) ≤
        Fintype.card vertices
  separated : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
    Fintype.card vertices <
      5 * permutationDistance
        (approximation x).permutation (approximation y).permutation

private instance expandingCentralizerFiniteModelVerticesFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.vertices :=
  M.verticesFintype

private instance expandingCentralizerFiniteModelVerticesDecidableEq
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : DecidableEq M.vertices :=
  M.verticesDecidableEq

private instance expandingCentralizerFiniteModelGeneratorFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.generatorIndex :=
  M.generatorFintype

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def expandingCentralizerFiniteModelOfImprovement
    {G : Type*} [Group G] (F : Finset G)
    {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) (h : ℝ)
    (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤ (boundary σ A : ℝ))
    (hsmall : (10 : ℝ) * tolerance < h * Fintype.card V)
    (himprove : HasAlmostCentralizerImprovement σ tolerance)
    (f : G → AlmostCentralizerElement σ tolerance)
    (hone : (f 1).permutation = 1)
    (hmul : ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance (f (x * y)).permutation
        ((f x).permutation * (f y).permutation) ≤ Fintype.card V)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * permutationDistance
        (f x).permutation (f y).permutation) :
    ExpandingCentralizerFiniteModel G F where
  vertices := V
  verticesFintype := inferInstance
  verticesDecidableEq := inferInstance
  generatorIndex := ι
  generatorFintype := inferInstance
  generators := σ
  tolerance := tolerance
  cheeger := h
  cheeger_positive := hpositive
  expansion := hexp
  small := hsmall
  repair := almostCentralizerRepairOfImprovement himprove
  approximation := f
  map_one := hone
  multiplicative := hmul
  separated := hsep

private theorem exists_finite_group_embedding_of_expanding_centralizer
    {G : Type*} [Group G] (F : Finset G)
    (M : ExpandingCentralizerFiniteModel G F) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G → H),
      Set.InjOn f (F : Set G) ∧ f 1 = 1 ∧
        ∀ x ∈ F, ∀ y ∈ F, f (x * y) = f x * f y := by
  let hgap : AlmostCentralizerGap M.generators M.tolerance :=
    almostCentralizerGap_of_expansion M.generators M.tolerance M.cheeger
      M.cheeger_positive M.expansion M.small
  let H := AlmostCentralizerClusters M.generators M.tolerance hgap
  let : Group H := almostCentralizerClusterGroup hgap M.repair
  let : Finite H := inferInstance
  let f : G → H := fun x => almostCentralizerCluster hgap (M.approximation x)
  refine ⟨H, inferInstance, inferInstance, f, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra hne
    have hclose :
        5 * permutationDistance
          (M.approximation x).permutation
          (M.approximation y).permutation ≤ Fintype.card M.vertices :=
      (almostCentralizerCluster_eq_iff hgap
        (M.approximation x) (M.approximation y)).mp hxy
    have hfar := M.separated x hx y hy hne
    omega
  · change almostCentralizerCluster hgap (M.approximation 1) =
      almostCentralizerCluster hgap
        (almostCentralizerOne M.generators M.tolerance)
    apply Quotient.sound
    change 5 * permutationDistance (M.approximation 1).permutation 1 ≤
      Fintype.card M.vertices
    simp only [M.map_one, permutationDistance_self, mul_zero, zero_le]
  · intro x hx y hy
    change almostCentralizerCluster hgap (M.approximation (x * y)) =
      almostCentralizerCluster hgap
        (correctedAlmostCentralizerProduct M.repair
          (M.approximation x) (M.approximation y))
    apply Quotient.sound
    let a := M.approximation (x * y)
    let b := correctedAlmostCentralizerProduct M.repair
      (M.approximation x) (M.approximation y)
    change 5 * permutationDistance a.permutation b.permutation ≤
      Fintype.card M.vertices
    rcases hgap.dichotomy a b with hclose | hfar
    · exact hclose
    · have hmul := M.multiplicative x hx y hy
      have hrepair := M.repair.corrected_distance
        (M.approximation x) (M.approximation y)
      have htri := permutationDistance_triangle a.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) b.permutation
      have hsym :
          permutationDistance
            ((M.approximation x).permutation *
              (M.approximation y).permutation) b.permutation =
            permutationDistance b.permutation
              ((M.approximation x).permutation *
                (M.approximation y).permutation) :=
        permutationDistance_comm _ _
      change 4 * Fintype.card M.vertices <
        5 * permutationDistance a.permutation b.permutation at hfar
      change 5 * permutationDistance a.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) ≤ Fintype.card M.vertices at hmul
      change 5 * permutationDistance b.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) ≤
            Fintype.card M.vertices at hrepair
      omega

private theorem exists_permutation_embedding_of_expanding_centralizer
    {G : Type*} [Group G] (F : Finset G)
    (M : ExpandingCentralizerFiniteModel G F) :
    ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
      Set.InjOn f (F : Set G) ∧ f 1 = 1 ∧
        ∀ x ∈ F, ∀ y ∈ F, f (x * y) = f x * f y := by
  obtain ⟨H, hgroup, hfinite, f, hinj, hone, hmul⟩ :=
    exists_finite_group_embedding_of_expanding_centralizer F M
  let : Group H := hgroup
  let : Finite H := hfinite
  let : Fintype H := Fintype.ofFinite H
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let ρ : H →* Equiv.Perm (Fin (Fintype.card H)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H H)
  have hρ : Function.Injective ρ :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  refine ⟨Fintype.card H, fun x => ρ (f x), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (hρ hxy)
  · simp only [hone, map_one]
  · intro x hx y hy
    change ρ (f (x * y)) = ρ (f x) * ρ (f y)
    rw [hmul x hx y hy, map_mul]

public
theorem lef_of_expanding_centralizer_models {G : Type*} [Group G]
    (hmodels : ∀ F : Finset G,
      Nonempty (ExpandingCentralizerFiniteModel G F)) : LEF G := by
  constructor
  intro F
  obtain ⟨M⟩ := hmodels F
  obtain ⟨n, f, hinj, hone, hmul⟩ :=
    exists_permutation_embedding_of_expanding_centralizer F M
  exact ⟨n, f, hinj, ⟨hone, hmul⟩⟩

private theorem exists_positive_antitone_slow_vanishing_threshold
    (e : ℕ → ℝ) (he_nonneg : ∀ n, 0 ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∃ eta : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧ Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      Tendsto (fun n => e n / eta n) atTop (nhds 0) := by
  have hrange : BddAbove (Set.range e) := he.bddAbove_range
  have htail_bdd (n : ℕ) : BddAbove (e '' Set.Ici n) := by
    apply hrange.mono
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, rfl⟩
  have htail_ne (n : ℕ) : (e '' Set.Ici n).Nonempty := by
    refine ⟨e n, ?_⟩
    exact ⟨n, Set.mem_Ici.mpr (le_refl n), rfl⟩
  let d : ℕ → ℝ := fun n => sSup (e '' Set.Ici n)
  have hd_dom (n : ℕ) : e n ≤ d n := by
    dsimp [d]
    apply le_csSup (htail_bdd n)
    exact ⟨n, Set.mem_Ici.mpr (le_refl n), rfl⟩
  have hd_nonneg (n : ℕ) : 0 ≤ d n :=
    (he_nonneg n).trans (hd_dom n)
  have hd_antitone : Antitone d := by
    intro a b hab
    change sSup (e '' Set.Ici b) ≤ sSup (e '' Set.Ici a)
    apply csSup_le_csSup (htail_bdd a) (htail_ne b)
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, Set.mem_Ici.mpr (hab.trans (Set.mem_Ici.mp hk)), rfl⟩
  have hd_zero : Tendsto d atTop (nhds 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (hd_nonneg n)
    · intro a ha
      have hev : ∀ᶠ k in atTop, e k < a / 2 :=
        he.eventually (gt_mem_nhds (half_pos ha))
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : d n ≤ a / 2 := by
        dsimp [d]
        apply csSup_le (htail_ne n)
        rintro y ⟨k, hk, rfl⟩
        exact (hN k (hn.trans (Set.mem_Ici.mp hk))).le
      exact hle.trans_lt (half_lt_self ha)
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq_pos (n : ℕ) : 0 < q n := by
    dsimp [q]
    positivity
  have hq_antitone : Antitone q := by
    intro a b hab
    dsimp [q]
    apply one_div_le_one_div_of_le (by positivity)
    have hab_real : (a : ℝ) ≤ b := by
      exact_mod_cast hab
    exact add_le_add hab_real (le_refl 1)
  have hq_zero : Tendsto q atTop (nhds 0) := by
    dsimp [q]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let eta : ℕ → ℝ := fun n => Real.sqrt (d n + q n)
  have heta_pos (n : ℕ) : 0 < eta n := by
    dsimp [eta]
    apply Real.sqrt_pos.2
    exact lt_of_lt_of_le (hq_pos n) (le_add_of_nonneg_left (hd_nonneg n))
  have heta_antitone : Antitone eta := by
    intro a b hab
    dsimp [eta]
    exact Real.sqrt_le_sqrt (add_le_add (hd_antitone hab) (hq_antitone hab))
  have hsum_zero : Tendsto (fun n => d n + q n) atTop (nhds 0) := by
    simpa only [add_zero] using hd_zero.add hq_zero
  have heta_zero : Tendsto eta atTop (nhds 0) := by
    simpa only [eta, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsum_zero
  have hratio_bound (n : ℕ) : e n / eta n ≤ eta n := by
    apply (div_le_iff₀ (heta_pos n)).2
    calc
      e n ≤ d n := hd_dom n
      _ ≤ d n + q n := le_add_of_nonneg_right (hq_pos n).le
      _ = eta n * eta n := by
        dsimp [eta]
        nlinarith [Real.sq_sqrt (add_nonneg (hd_nonneg n) (hq_pos n).le)]
  refine ⟨eta, heta_pos, heta_antitone, heta_zero, ?_⟩
  exact squeeze_zero (fun n => div_nonneg (he_nonneg n) (heta_pos n).le)
    hratio_bound heta_zero

public
theorem exists_positive_antitone_slow_overlap_scales
    (e : ℕ → ℝ) (he_nonneg : ∀ n, 0 ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧ Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧ Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => e n / eta n) atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) := by
  obtain ⟨eta, heta_pos, heta_antitone, heta_zero, herror_zero⟩ :=
    exists_positive_antitone_slow_vanishing_threshold e he_nonneg he
  let H : ℕ → ℝ := fun n => Real.sqrt (eta n)
  have hH_pos (n : ℕ) : 0 < H n := by
    exact Real.sqrt_pos.2 (heta_pos n)
  have hH_antitone : Antitone H := by
    intro a b hab
    exact Real.sqrt_le_sqrt (heta_antitone hab)
  have hH_zero : Tendsto H atTop (nhds 0) := by
    simpa only [H, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp heta_zero
  have hquot (n : ℕ) : eta n / H n = H n := by
    dsimp [H]
    apply (div_eq_iff (Real.sqrt_pos.2 (heta_pos n)).ne').2
    nlinarith [Real.sq_sqrt (heta_pos n).le]
  have hquot_zero : Tendsto (fun n => eta n / H n) atTop (nhds 0) := by
    have hfun : (fun n => eta n / H n) = H := funext hquot
    rw [hfun]
    exact hH_zero
  exact ⟨eta, H, heta_pos, heta_antitone, heta_zero,
    hH_pos, hH_antitone, hH_zero, herror_zero, hquot_zero⟩

namespace ExceptionalRankOffset

open Filter Topology
open scoped BigOperators

private theorem rankDropCount_goodSubtype_eq
    {ι : Type*}
    (G : Finset ι) (u v : ι → ℝ) (H r : ℝ) :
    rankDropCount
        (fun i : {i // i ∈ G} => u i.1)
        (fun i : {i // i ∈ G} => v i.1) H r =
      ∑ i ∈ G,
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0 := by
  classical
  unfold rankDropCount
  rw [Finset.univ_eq_attach]
  change
    (∑ i ∈ G.attach,
      if ⌊(v i.1 + r) / H⌋ < ⌊(u i.1 + r) / H⌋ then (1 : ℝ) else 0) =
      ∑ i ∈ G,
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0
  exact Finset.sum_attach G
    (fun i : ι =>
      if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)

private theorem rankDropCount_le_goodSubtype_add_exceptions
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (u v : ι → ℝ) (H r : ℝ) :
    rankDropCount u v H r ≤
      rankDropCount
          (fun i : {i // i ∈ G} => u i.1)
          (fun i : {i // i ∈ G} => v i.1) H r +
        (((Finset.univ : Finset ι) \ G).card : ℝ) := by
  classical
  let d : ι → ℝ := fun i =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then 1 else 0
  have hgood :
      rankDropCount
        (fun i : {i // i ∈ G} => u i.1)
        (fun i : {i // i ∈ G} => v i.1) H r =
        ∑ i ∈ G, d i := by
    exact rankDropCount_goodSubtype_eq G u v H r
  have hfull : rankDropCount u v H r = ∑ i : ι, d i := by
    rfl
  have hsplit :
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) +
        (∑ i ∈ G, d i) = ∑ i : ι, d i :=
    Finset.sum_sdiff (Finset.subset_univ G)
  have hbad :
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) ≤
        (((Finset.univ : Finset ι) \ G).card : ℝ) := by
    calc
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) ≤
        ∑ _i ∈ (Finset.univ : Finset ι) \ G, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          dsimp [d]
          split_ifs <;> norm_num
      _ = (((Finset.univ : Finset ι) \ G).card : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul,
        mul_one]
  rw [hfull, hgood]
  linarith

private theorem exists_common_log_rank_offset_except
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (x y : ι → ℝ) (eta H : ℝ)
    (hx : ∀ i ∈ G, 0 < x i)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hH : 0 < H)
    (hcomparison : ∀ i ∈ G, (1 - eta) * x i ≤ y i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount
          (fun i => Real.log (x i))
          (fun i => Real.log (y i)) H r ≤
        (G.card : ℝ) * |Real.log (1 - eta)| / H +
          (((Finset.univ : Finset ι) \ G).card : ℝ) := by
  obtain ⟨r, hr, hbound⟩ := exists_common_log_rank_offset
    (fun i : {i // i ∈ G} => x i.1)
    (fun i : {i // i ∈ G} => y i.1)
    eta H
    (fun i => hx i.1 i.2)
    heta0 heta1 hH
    (fun i => hcomparison i.1 i.2)
  have hbound' :
      rankDropCount
        (fun i : {i // i ∈ G} => Real.log (x i.1))
        (fun i : {i // i ∈ G} => Real.log (y i.1)) H r ≤
          (G.card : ℝ) * |Real.log (1 - eta)| / H := by
    simpa only [Fintype.card_coe] using hbound
  refine ⟨r, hr, ?_⟩
  calc
    rankDropCount
        (fun i => Real.log (x i))
        (fun i => Real.log (y i)) H r ≤
      rankDropCount
          (fun i : {i // i ∈ G} => Real.log (x i.1))
          (fun i : {i // i ∈ G} => Real.log (y i.1)) H r +
        (((Finset.univ : Finset ι) \ G).card : ℝ) :=
        rankDropCount_le_goodSubtype_add_exceptions G
          (fun i => Real.log (x i)) (fun i => Real.log (y i)) H r
    _ ≤ (G.card : ℝ) * |Real.log (1 - eta)| / H +
        (((Finset.univ : Finset ι) \ G).card : ℝ) :=
        add_le_add hbound' (le_refl _)

public
theorem exists_common_log_rank_offsets_tendsto_zero_except
    (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (G : (n : ℕ) → Finset (ι n))
    (x y : (n : ℕ) → ι n → ℝ)
    (eta H N : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n i, i ∈ G n → 0 < x n i)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (hN : ∀ n, 0 < N n)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ C * N n)
    (hcomparison : ∀ n i, i ∈ G n →
      (1 - eta n) * x n i ≤ y n i)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hexceptions : Tendsto
      (fun n =>
        (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n)
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
        Tendsto
          (fun n =>
            rankDropCount
              (fun i => Real.log (x n i))
              (fun i => Real.log (y n i)) (H n) (r n) / N n)
          atTop (nhds 0) := by
  have hwitness : ∀ n, ∃ r ∈ Set.Ico 0 (H n),
      rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) r ≤
        ((G n).card : ℝ) * |Real.log (1 - eta n)| / H n +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) := by
    intro n
    exact exists_common_log_rank_offset_except
      (G n) (x n) (y n) (eta n) (H n)
      (hx n) (heta0 n) (heta1 n) (hH n) (hcomparison n)
  choose r hr hbound using hwitness
  refine ⟨r, hr, ?_⟩
  have hlog := abs_log_one_sub_div_tendsto_zero
    eta H heta0 hH heta hratio
  have hscaled : Tendsto
      (fun n => C * (|Real.log (1 - eta n)| / H n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul C hlog
  have hlimit : Tendsto
      (fun n =>
        C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n)
      atTop (nhds 0) := by
    simpa only [add_zero] using hscaled.add hexceptions
  have hnonnegative : ∀ n,
      0 ≤ rankDropCount
        (fun i => Real.log (x n i))
        (fun i => Real.log (y n i)) (H n) (r n) / N n := by
    intro n
    exact div_nonneg
      (rankDropCount_nonneg_and_le
        (fun i => Real.log (x n i))
        (fun i => Real.log (y n i)) (H n) (r n)).1
      (hN n).le
  have hupper : ∀ n,
      rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) (r n) / N n ≤
        C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
    intro n
    calc
      rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) (r n) / N n ≤
        (((G n).card : ℝ) * |Real.log (1 - eta n)| / H n +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ)) / N n :=
          (div_le_div_iff_of_pos_right (hN n)).2 (hbound n)
      _ = (((G n).card : ℝ) / N n) *
            (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
            ring
      _ ≤ C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_right
                ((div_le_iff₀ (hN n)).2 (hcard n))
              exact div_nonneg (abs_nonneg _) (hH n).le
            · exact le_refl _
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit

end ExceptionalRankOffset

namespace ThompsonPrefixInsertion

private theorem cylinderSwap_mul_wordS_right
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    (↑(cylinderSwap a b hab hba) : BinaryLeavitt) *
        leavittWordS b = leavittWordS a := by
  change
    PrefixCompression.transpositionValue
        (leavittWordS a) (leavittWordT a)
        (leavittWordS b) (leavittWordT b) *
      leavittWordS b = leavittWordS a
  simp only [PrefixCompression.transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
    leavittWordT_mul_wordS_of_incomparable a b hab hba, mul_zero, sub_zero,
      leavittWordT_mul_wordS_self, mul_one,
    sub_self, zero_add, add_zero]

end ThompsonPrefixInsertion

universe u₁ u₂ u₃

section ElementaryRingQuotient

variable {ι : Type u₁} {R : Type u₂} {S : Type u₃}
  [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]

private def elementaryMatrixUnitMap (f : R →+* S) :
    (Matrix ι ι R)ˣ →* (Matrix ι ι S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom

private theorem elementaryMatrixUnitMap_elementaryUnit
    (f : R →+* S) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryMatrixUnitMap f (elementaryUnit i j hij a) =
      elementaryUnit i j hij (f a) := by
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single i j a) =
    1 + Matrix.single i j (f a)
  rw [map_add, map_one]
  congr 1
  ext k l
  change f (if i = k ∧ j = l then a else 0) =
    if i = k ∧ j = l then f a else 0
  split_ifs <;> simp

private theorem elementaryGroup_map_le (f : R →+* S) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) ≤
      elementaryGroup ι S := by
  rw [Subgroup.map_le_iff_le_comap, elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change elementaryMatrixUnitMap f (elementaryUnit i j hij a) ∈
    elementaryGroup ι S
  rw [elementaryMatrixUnitMap_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)

private theorem elementaryGroup_map_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) =
      elementaryGroup ι S := by
  apply le_antisymm (elementaryGroup_map_le f)
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, b, rfl⟩
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨elementaryUnit i j hij a,
    elementaryUnit_mem i j hij a, ?_⟩
  exact elementaryMatrixUnitMap_elementaryUnit f i j hij a

end ElementaryRingQuotient

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def binaryPrefixElementaryGroupEquiv
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    elementaryGroup ι BinaryLeavitt ≃* prefixElementaryGroup E :=
  ((elementaryGroup ι BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom E) (prefixCornerUnitHom_injective E)).trans
    (MulEquiv.subgroupCongr (prefixCornerElementaryGroup_map E))

namespace CompressionCriterion

open Filter Topology

public
theorem normalizedHamming_distinct_tendsto
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    {g h : G} (hne : g ≠ h) :
    Tendsto
      (fun n => normalizedHamming
        ((A.model n).action g) ((A.model n).action h))
      atTop (𝓝 1) := by
  have hdifference : g * h⁻¹ ≠ 1 := by
    intro he
    apply hne
    have := congrArg (fun x : G => x * h) he
    simpa only [inv_mul_cancel_right, one_mul] using this
  have hseparation := A.separated (g * h⁻¹) hdifference
  have hmultiplication := A.multiplicative (g * h⁻¹) h
  have hlower (n : ℕ) :
      normalizedHamming
        ((A.model n).action (g * h⁻¹)) 1 -
          normalizedHamming
            ((A.model n).action ((g * h⁻¹) * h))
            ((A.model n).action (g * h⁻¹) *
              (A.model n).action h) ≤
        normalizedHamming
          ((A.model n).action g) ((A.model n).action h) := by
    have htriangle := normalizedHamming_triangle
      ((A.model n).action (g * h⁻¹) * (A.model n).action h)
      ((A.model n).action g)
      ((A.model n).action h)
    have hright := normalizedHamming_mul_right
      ((A.model n).action h) ((A.model n).action (g * h⁻¹)) 1
    have hsym := normalizedHamming_comm
      ((A.model n).action g)
      ((A.model n).action (g * h⁻¹) * (A.model n).action h)
    have hword : (g * h⁻¹) * h = g := by simp only [inv_mul_cancel_right]
    rw [hword] at *
    simp only [one_mul] at hright
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto
      (fun n => normalizedHamming
        ((A.model n).action (g * h⁻¹)) 1 -
          normalizedHamming
            ((A.model n).action ((g * h⁻¹) * h))
            ((A.model n).action (g * h⁻¹) * (A.model n).action h))
      atTop (𝓝 1) by
        simpa only [inv_mul_cancel_right, sub_zero] using hseparation.sub hmultiplication)
    tendsto_const_nhds
  · exact hlower
  · intro n
    exact normalizedHamming_le_one _ _

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def productTrackedTable {J : Type*} [Group J]
    (F : Finset J) : Finset J := by
  classical
  exact multiplicationTable (insert 1 F)

public
theorem one_mem_productTrackedTable {J : Type*} [Group J]
    (F : Finset J) : 1 ∈ productTrackedTable F := by
  classical
  exact mem_multiplicationTable_of_mem
    (Finset.mem_insert_self 1 F)

public
theorem mem_productTrackedTable {J : Type*} [Group J]
    {F : Finset J} {j : J} (hj : j ∈ F) :
    j ∈ productTrackedTable F := by
  classical
  exact mem_multiplicationTable_of_mem
    (Finset.mem_insert_of_mem hj)

public
theorem mul_mem_productTrackedTable {J : Type*} [Group J]
    {F : Finset J} {x y : J} (hx : x ∈ F) (hy : y ∈ F) :
    x * y ∈ productTrackedTable F := by
  classical
  exact mul_mem_multiplicationTable
    (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)

end CompressionCriterion

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationGraph {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : Finset (V × V) :=
  Finset.univ.image fun x => (x, p x)

public
theorem mem_permutationGraph {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (x y : V) :
    (x, y) ∈ permutationGraph p ↔ y = p x := by
  simp only [permutationGraph, Finset.mem_image, Finset.mem_univ, eq_comm, Prod.mk.injEq, true_and,
    exists_eq_left']

public
theorem boundary_permutationGraph_eq_commutationDefect
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) :
    boundary (fun i => (σ i).prodCongr (σ i)) (permutationGraph p) =
      permutationCommutationDefect σ p := by
  classical
  unfold boundary permutationCommutationDefect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun z _ => z.1)
  · intro z hz
    obtain ⟨hzgraph, hzbad⟩ := Finset.mem_filter.mp hz
    have hzsecond : z.2 = p z.1 :=
      (mem_permutationGraph p z.1 z.2).mp hzgraph
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcommute
    apply hzbad
    apply (mem_permutationGraph p (σ i z.1) (σ i z.2)).mpr
    simpa only [hzsecond] using hcommute.symm
  · intro z hz w hw hfirst
    obtain ⟨hzgraph, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwgraph, _⟩ := Finset.mem_filter.mp hw
    have hzsecond := (mem_permutationGraph p z.1 z.2).mp hzgraph
    have hwsecond := (mem_permutationGraph p w.1 w.2).mp hwgraph
    apply Prod.ext hfirst
    simpa only [hzsecond, hwsecond, EmbeddingLike.apply_eq_iff_eq] using congrArg p hfirst
  · intro x hx
    obtain ⟨_, hbad⟩ := Finset.mem_filter.mp hx
    refine ⟨(x, p x), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_permutationGraph p x (p x)).mpr rfl, ?_⟩
    intro hgraph
    have hcommute :=
      (mem_permutationGraph p (σ i x) (σ i (p x))).mp hgraph
    exact hbad hcommute.symm

public
theorem kazhdan_generator_displacement
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (hfixed : ∀ η : H, (∀ g : G, π g η = η) → η = 0)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖ξ‖ ≤ ‖π g ξ - ξ‖ := by
  classical
  by_contra h
  push Not at h
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let z : ℂ := (‖ξ‖ : ℂ)⁻¹
  let ζ : H := z • ξ
  have hζ : ‖ζ‖ = 1 := by
    dsimp [ζ, z]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnorm]
    exact inv_mul_cancel₀ (ne_of_gt hnorm)
  have hζsmall : ∀ g ∈ P.generators,
      ‖π g ζ - ζ‖ < P.kazhdanConstant := by
    intro g hg
    have hscale :
        ‖π g ζ - ζ‖ = ‖ξ‖⁻¹ * ‖π g ξ - ξ‖ := by
      dsimp [ζ, z]
      rw [map_smul, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hnorm]
    rw [hscale]
    calc
      ‖ξ‖⁻¹ * ‖π g ξ - ξ‖ <
          ‖ξ‖⁻¹ * (P.kazhdanConstant * ‖ξ‖) :=
        mul_lt_mul_of_pos_left (h g hg) (inv_pos.mpr hnorm)
      _ = P.kazhdanConstant := by
        field_simp
  obtain ⟨η, hη, hηfixed⟩ := P.invariant H π ζ hζ hζsmall
  exact hη (hfixed η hηfixed)

namespace ThompsonPrefixInsertion

open scoped commutatorElement

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure PrefixWordAction (g : BinaryLeavittˣ)
    (a b : List (Fin 2)) : Prop where
  prefixing : (↑g : BinaryLeavitt) * leavittWordS a = leavittWordS b
  deletion :
    leavittWordT a * (↑(g⁻¹) : BinaryLeavitt) = leavittWordT b

public
theorem prefixWordAction_append
    {g : BinaryLeavittˣ} {a b : List (Fin 2)}
    (h : PrefixWordAction g a b) (r : List (Fin 2)) :
    PrefixWordAction g (a ++ r) (b ++ r) := by
  constructor
  · rw [leavittWordS_append, leavittWordS_append, ← mul_assoc, h.prefixing]
  · rw [leavittWordT_append, leavittWordT_append, mul_assoc, h.deletion]

public
theorem prefixWordAction_mul
    {g h : BinaryLeavittˣ} {a b c : List (Fin 2)}
    (hg : PrefixWordAction g b c)
    (hh : PrefixWordAction h a b) :
    PrefixWordAction (g * h) a c := by
  constructor
  · change
      ((g : BinaryLeavitt) * (h : BinaryLeavitt)) *
        leavittWordS a = leavittWordS c
    rw [mul_assoc, hh.prefixing, hg.prefixing]
  · change
      leavittWordT a *
        ((↑(h⁻¹) : BinaryLeavitt) *
          (↑(g⁻¹) : BinaryLeavitt)) = leavittWordT c
    rw [← mul_assoc, hh.deletion, hg.deletion]

private theorem cylinderSwap_prefixWordAction_left
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    PrefixWordAction (cylinderSwap a b hab hba) a b := by
  constructor
  · change
      PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) *
        leavittWordS a = leavittWordS b
    simp only [PrefixCompression.transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      leavittWordT_mul_wordS_self, mul_one, sub_self, leavittWordT_mul_wordS_of_incomparable b a hba
        hab, mul_zero,
      add_zero, zero_add]
  · change
      leavittWordT a *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT b
    have haa : leavittWordT a * leavittWordS a = 1 :=
      leavittWordT_mul_wordS_self a
    have hab' : leavittWordT a * leavittWordS b = 0 :=
      leavittWordT_mul_wordS_of_incomparable a b hab hba
    have haa' (z : BinaryLeavitt) :
        leavittWordT a * (leavittWordS a * z) = z := by
      rw [← mul_assoc, haa, one_mul]
    have hab'' (z : BinaryLeavitt) :
        leavittWordT a * (leavittWordS b * z) = 0 := by
      rw [← mul_assoc, hab', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [haa, hab', haa', hab'']

private theorem cylinderSwap_prefixWordAction_right
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    PrefixWordAction (cylinderSwap a b hab hba) b a := by
  constructor
  · exact cylinderSwap_mul_wordS_right a b hab hba
  · change
      leavittWordT b *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT a
    have hbb : leavittWordT b * leavittWordS b = 1 :=
      leavittWordT_mul_wordS_self b
    have hba' : leavittWordT b * leavittWordS a = 0 :=
      leavittWordT_mul_wordS_of_incomparable b a hba hab
    have hbb' (z : BinaryLeavitt) :
        leavittWordT b * (leavittWordS b * z) = z := by
      rw [← mul_assoc, hbb, one_mul]
    have hba'' (z : BinaryLeavitt) :
        leavittWordT b * (leavittWordS a * z) = 0 := by
      rw [← mul_assoc, hba', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [hbb, hba', hbb', hba'']

private theorem cylinderSwap_prefixWordAction_fixed
    (a b w : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (haw : ¬ a <+: w) (hwa : ¬ w <+: a)
    (hbw : ¬ b <+: w) (hwb : ¬ w <+: b) :
    PrefixWordAction (cylinderSwap a b hab hba) w w := by
  constructor
  · change
      PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) *
        leavittWordS w = leavittWordS w
    simp only [PrefixCompression.transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      leavittWordT_mul_wordS_of_incomparable a w haw hwa, mul_zero, sub_zero,
      leavittWordT_mul_wordS_of_incomparable b w hbw hwb, add_zero]
  · change
      leavittWordT w *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT w
    have hwa' : leavittWordT w * leavittWordS a = 0 :=
      leavittWordT_mul_wordS_of_incomparable w a hwa haw
    have hwb' : leavittWordT w * leavittWordS b = 0 :=
      leavittWordT_mul_wordS_of_incomparable w b hwb hbw
    have hwa'' (z : BinaryLeavitt) :
        leavittWordT w * (leavittWordS a * z) = 0 := by
      rw [← mul_assoc, hwa', zero_mul]
    have hwb'' (z : BinaryLeavitt) :
        leavittWordT w * (leavittWordS b * z) = 0 := by
      rw [← mul_assoc, hwb', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [hwa', hwb', hwa'', hwb'']

public
theorem prefixInsertionHom_conjugate_of_prefixWordAction
    (g : BinaryLeavittˣ) (a b : List (Fin 2))
    (h : PrefixWordAction g a b) (u : BinaryLeavittˣ) :
    g * prefixInsertionHom a u * g⁻¹ = prefixInsertionHom b u := by
  apply Units.ext
  change
    (g : BinaryLeavitt) *
        (↑(prefixInsertionHom a u) : BinaryLeavitt) *
          (↑(g⁻¹) : BinaryLeavitt) =
      (↑(prefixInsertionHom b u) : BinaryLeavitt)
  rw [prefixInsertionHom_val, prefixInsertionHom_val]
  change
    (g : BinaryLeavitt) *
        (leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
          (1 - leavittWordS a * leavittWordT a)) *
          (↑(g⁻¹) : BinaryLeavitt) =
      leavittWordS b * (u : BinaryLeavitt) * leavittWordT b +
        (1 - leavittWordS b * leavittWordT b)
  have hunit :
      (g : BinaryLeavitt) * (↑(g⁻¹) : BinaryLeavitt) = 1 :=
    g.val_inv
  calc
    (g : BinaryLeavitt) *
        (leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
          (1 - leavittWordS a * leavittWordT a)) *
          (↑(g⁻¹) : BinaryLeavitt) =
        ((g : BinaryLeavitt) * leavittWordS a) *
            (u : BinaryLeavitt) *
            (leavittWordT a * (↑(g⁻¹) : BinaryLeavitt)) +
          ((g : BinaryLeavitt) * (↑(g⁻¹) : BinaryLeavitt) -
            ((g : BinaryLeavitt) * leavittWordS a) *
              (leavittWordT a * (↑(g⁻¹) : BinaryLeavitt))) := by
          simp only [CharTwo.sub_eq_add]
          noncomm_ring
    _ = leavittWordS b * (u : BinaryLeavitt) * leavittWordT b +
          (1 - leavittWordS b * leavittWordT b) := by
          rw [h.prefixing, h.deletion, hunit]

public
theorem prefixInsertionHom_mem_binaryPrefixTranspositionGroup
    (a : List (Fin 2)) (u : BinaryLeavittˣ)
    (hu : u ∈ binaryPrefixTranspositionGroup) :
    prefixInsertionHom a u ∈ binaryPrefixTranspositionGroup := by
  have hle :
      binaryPrefixTranspositionGroup ≤
        binaryPrefixTranspositionGroup.comap (prefixInsertionHom a) := by
    change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).2
    rintro _ ⟨x, y, hxy, hyx, rfl⟩
    change prefixInsertionHom a (cylinderSwap x y hxy hyx) ∈
      binaryPrefixTranspositionGroup
    rw [prefixInsertionHom_cylinderSwap]
    exact Subgroup.subset_closure
      ⟨a ++ x, a ++ y,
        prepend_not_prefix_prepend a x y hxy,
        prepend_not_prefix_prepend a y x hyx, rfl⟩
  exact hle hu

end ThompsonPrefixInsertion

namespace LeavittElementaryMorita

open scoped BigOperators commutatorElement

section ElementaryBlockFlattening

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

private def elementaryBlockMatrixEquiv :
    Matrix ι ι (Matrix κ κ R) ≃+*
      Matrix (ι × κ) (ι × κ) R :=
  Matrix.compRingEquiv ι κ R

private def elementaryBlockUnitEquiv :
    (Matrix ι ι (Matrix κ κ R))ˣ ≃*
      (Matrix (ι × κ) (ι × κ) R)ˣ :=
  Units.mapEquiv (elementaryBlockMatrixEquiv (ι := ι)
    (κ := κ) (R := R)).toMulEquiv

private theorem elementaryBlockUnitEquiv_elementaryUnit_single
    (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij (Matrix.single k l a)) =
      elementaryUnit (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a := by
  apply Units.ext
  change
    elementaryBlockMatrixEquiv (ι := ι) (κ := κ) (R := R)
        (1 + Matrix.single i j (Matrix.single k l a)) =
      1 + Matrix.single (i, k) (j, l) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.comp_single_single i j k l a

private theorem elementaryBlockUnitEquiv_elementaryUnit_mem
    (i j : ι) (hij : i ≠ j) (A : Matrix κ κ R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij A) ∈
      elementaryGroup (ι × κ) R := by
  induction A using Matrix.induction_on' with
  | h_zero =>
      simp only [elementaryUnit_zero, map_one, one_mem]
  | h_add A B hA hB =>
      rw [← elementaryUnit_mul, map_mul]
      exact (elementaryGroup (ι × κ) R).mul_mem hA hB
  | h_std_basis k l a =>
      rw [elementaryBlockUnitEquiv_elementaryUnit_single i j hij k l a]
      exact elementaryUnit_mem (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a

private theorem elementaryBlockGroup_map [Nontrivial ι] :
    (elementaryGroup ι (Matrix κ κ R)).map
        (elementaryBlockUnitEquiv
          (ι := ι) (κ := κ) (R := R)).toMonoidHom =
      elementaryGroup (ι × κ) R := by
  let B : Subgroup (Matrix (ι × κ) (ι × κ) R)ˣ :=
    (elementaryGroup ι (Matrix κ κ R)).map
      (elementaryBlockUnitEquiv
        (ι := ι) (κ := κ) (R := R)).toMonoidHom
  have hcross (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
      elementaryUnit (i, k) (j, l)
          (fun h => hij (congrArg Prod.fst h)) a ∈ B := by
    refine ⟨elementaryUnit i j hij (Matrix.single k l a),
      elementaryUnit_mem i j hij (Matrix.single k l a), ?_⟩
    exact elementaryBlockUnitEquiv_elementaryUnit_single
      i j hij k l a
  change B = elementaryGroup (ι × κ) R
  apply le_antisymm
  · change
      (elementaryGroup ι (Matrix κ κ R)).map
          (elementaryBlockUnitEquiv
            (ι := ι) (κ := κ) (R := R)).toMonoidHom ≤
        elementaryGroup (ι × κ) R
    rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, A, rfl⟩, rfl⟩
    change
      elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
          (elementaryUnit i j hij A) ∈
        elementaryGroup (ι × κ) R
    exact elementaryBlockUnitEquiv_elementaryUnit_mem
      i j hij A
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, k⟩, ⟨j, l⟩, hne, a, rfl⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨j, hji⟩ := exists_ne i
      exact elementaryUnit_mem_of_two_step B
        (i, k) (j, k) (i, l)
        (fun h => hji (congrArg Prod.fst h).symm)
        (fun h => hji (congrArg Prod.fst h))
        hne a
        (hcross i j hji.symm k k a)
        (hcross j i hji k l 1)
    · exact hcross i j hij k l a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryBlockGroupEquiv [Nontrivial ι] :
    elementaryGroup ι (Matrix κ κ R) ≃*
      elementaryGroup (ι × κ) R :=
  ((elementaryBlockUnitEquiv
      (ι := ι) (κ := κ) (R := R)).subgroupMap
    (elementaryGroup ι (Matrix κ κ R))).trans
    (MulEquiv.subgroupCongr
      (elementaryBlockGroup_map (ι := ι) (κ := κ) (R := R)))

end ElementaryBlockFlattening

section ElementaryReindexing

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

private def elementaryReindexUnitEquiv (e : ι ≃ κ) :
    (Matrix ι ι R)ˣ ≃* (Matrix κ κ R)ˣ :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

private theorem elementaryReindexUnitEquiv_elementaryUnit
    (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryReindexUnitEquiv (R := R) e
        (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  change
    (Matrix.reindexRingEquiv R e)
        (1 + Matrix.single i j a) =
      1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  change
    Matrix.reindex e e (Matrix.single i j a) =
      Matrix.single (e i) (e j) a
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    (Matrix.submatrix_single_equiv e.symm e.symm i j a)

private theorem elementaryReindexGroup_map (e : ι ≃ κ) :
    (elementaryGroup ι R).map
        (elementaryReindexUnitEquiv (R := R) e).toMonoidHom =
      elementaryGroup κ R := by
  apply le_antisymm
  · rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    change
      elementaryReindexUnitEquiv (R := R) e
          (elementaryUnit i j hij a) ∈ elementaryGroup κ R
    rw [elementaryReindexUnitEquiv_elementaryUnit]
    exact elementaryUnit_mem (e i) (e j) (e.injective.ne hij) a
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨k, l, hkl, a, rfl⟩
    have hij : e.symm k ≠ e.symm l := e.symm.injective.ne hkl
    refine ⟨elementaryUnit (e.symm k) (e.symm l) hij a,
      elementaryUnit_mem (e.symm k) (e.symm l) hij a, ?_⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Equiv.apply_symm_apply] using
      elementaryReindexUnitEquiv_elementaryUnit e (e.symm k) (e.symm l) hij a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryReindexGroupEquiv (e : ι ≃ κ) :
    elementaryGroup ι R ≃* elementaryGroup κ R :=
  ((elementaryReindexUnitEquiv (R := R) e).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (elementaryReindexGroup_map e))

end ElementaryReindexing

section ElementaryCoefficientEquivalence

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]

private def elementaryCoefficientGroupEquiv (f : R ≃+* S) :
    elementaryGroup ι R ≃* elementaryGroup ι S :=
  ((Units.mapEquiv f.mapMatrix.toMulEquiv).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (by
      change
        (elementaryGroup ι R).map
          (elementaryMatrixUnitMap f.toRingHom) =
            elementaryGroup ι S
      exact elementaryGroup_map_eq_of_surjective
        f.toRingHom f.surjective))

end ElementaryCoefficientEquivalence

private def ternaryLeavittWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0]
  | 1 => [0, 1]
  | _ => [1]

private def ternaryLeavittPrefixCode : BinaryPrefixCode (Fin 3) where
  word := ternaryLeavittWord
  prefix_free := by decide

private theorem ternaryLeavittPrefixCode_complete :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS (ternaryLeavittPrefixCode.word i))
        (fun i => leavittWordT (ternaryLeavittPrefixCode.word i)) =
      1 := by
  have hzero :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [0]).symm
  have hroot :
      leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul,
      List.nil_append] using
      (leavittCylinder_split ([] : List (Fin 2))).symm
  have hsum :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] +
          leavittCylinder [1] = 1 := by
    rw [hzero]
    exact hroot
  simpa only [MatrixCorner.codeIdempotent, ternaryLeavittPrefixCode, ternaryLeavittWord,
    Fin.isValue,
    Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one, Finset.univ_unique,
      Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_one_eq_two, leavittCylinder, add_assoc] using hsum

private def binaryLeavittMatrixThreeEquiv :
    BinaryLeavitt ≃+* Matrix (Fin 3) (Fin 3) BinaryLeavitt :=
  (completePrefixMatrixEquiv ternaryLeavittPrefixCode
    ternaryLeavittPrefixCode_complete).symm

private def binaryLeavittElementaryThreeEquivNine :
    binaryLeavittElementaryGroup 3 ≃*
      binaryLeavittElementaryGroup 9 :=
  (elementaryCoefficientGroupEquiv
    (ι := Fin 3) binaryLeavittMatrixThreeEquiv).trans
    ((elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := BinaryLeavitt)).trans
      (elementaryReindexGroupEquiv
        (R := BinaryLeavitt) (finProdFinEquiv :
          Fin 3 × Fin 3 ≃ Fin 9)))

private theorem binaryLeavittElementaryThree_hasPropertyT_of_nine
    [HasPropertyT.{0, v} (binaryLeavittElementaryGroup 9)] :
    HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
  hasPropertyT_of_mulEquiv binaryLeavittElementaryThreeEquivNine.symm

public
theorem alphaPrefixElementaryGroup_hasPropertyT_of_nine
    [HasPropertyT.{0, v} (binaryLeavittElementaryGroup 9)] :
    HasPropertyT.{0, v} (prefixElementaryGroup alphaPrefixCode) := by
  let : HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
    binaryLeavittElementaryThree_hasPropertyT_of_nine
  exact hasPropertyT_of_mulEquiv alphaPrefixElementaryGroupEquiv

public
theorem alphaZeroPrefixElementaryGroup_hasPropertyT_of_nine
    [HasPropertyT.{0, v} (binaryLeavittElementaryGroup 9)] :
    HasPropertyT.{0, v} (prefixElementaryGroup alphaZeroPrefixCode) := by
  let : HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
    binaryLeavittElementaryThree_hasPropertyT_of_nine
  exact hasPropertyT_of_mulEquiv
    (binaryPrefixElementaryGroupEquiv alphaZeroPrefixCode)

end LeavittElementaryMorita

namespace ThompsonFiniteGeneration

open ThompsonPrefixInsertion

public
theorem cylinderSwap_prefixWordAction_of_cases
    {a b w v : List (Fin 2)}
    (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (hcase :
      (a <+: w ∧ v = b ++ w.drop a.length) ∨
      (b <+: w ∧ v = a ++ w.drop b.length) ∨
      (v = w ∧ ¬ a <+: w ∧ ¬ w <+: a ∧
        ¬ b <+: w ∧ ¬ w <+: b)) :
    PrefixWordAction (cylinderSwap a b hab hba) w v := by
  rcases hcase with h | h | h
  · obtain ⟨haw, rfl⟩ := h
    simpa only [(List.prefix_append_drop haw).symm] using
      prefixWordAction_append
        (cylinderSwap_prefixWordAction_left a b hab hba)
        (w.drop a.length)
  · obtain ⟨hbw, rfl⟩ := h
    simpa only [(List.prefix_append_drop hbw).symm] using
      prefixWordAction_append
        (cylinderSwap_prefixWordAction_right a b hab hba)
        (w.drop b.length)
  · obtain ⟨hv, haw, hwa, hbw, hwb⟩ := h
    subst v
    exact cylinderSwap_prefixWordAction_fixed
      a b w hab hba haw hwa hbw hwb

end ThompsonFiniteGeneration

end


end SoficGroups

end
