/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.BanLat.Substructures.Band.DisjointComplement

public import LeanPool.OrderClosures.OrderAdherence


/-!
# The Gao--Leung order-continuity characterization

This file proves Gao--Leung Theorem 2.7.  The reverse implication is obtained
by contrapositive: failure of order continuity supplies an order-bounded
disjoint sequence, which gives a lattice embedding of `ℓ∞(ℕ × ℕ)` into the
ambient Banach lattice.  The row-limit sublattice then separates uo-adherence
from order adherence.
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped BoundedContinuousFunction

universe u

section

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- Extracts an order-convergent subsequence from norm convergence; used to
identify order adherence with topological closure for order-continuous norms. -/
private theorem norm_tendsto_has_order_convergent_subsequence
    {z : ℕ → X} {x : X} (hz : Tendsto z atTop (nhds x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ OrderConvergesTo (z ∘ φ) x := by
  let V : ℕ → Set X := fun n ↦ Metric.closedBall x ((1 / 2 : ℝ) ^ n)
  have hV : ∀ n, V n ∈ nhds x := fun n ↦
    Metric.closedBall_mem_nhds x (by positivity)
  obtain ⟨φ, hφ, hzφ⟩ := hz.subseq_mem hV
  let v : ℕ → X := fun n ↦ |z (φ n) - x|
  have hv_norm : ∀ n, ‖v n‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    rw [norm_abs_eq_norm, ← dist_eq_norm]
    exact hzφ n
  have hv_sum : Summable v := by
    apply Summable.of_norm_bounded summable_geometric_two
    exact hv_norm
  let r : ℕ → X := fun k ↦ ∑' n, v (n + k)
  have hr_nonneg : ∀ k, 0 ≤ r k := fun k ↦
    tsum_nonneg fun n ↦ abs_nonneg _
  have hr_step : ∀ k, r k = v k + r (k + 1) := by
    intro k
    have hs := ((summable_nat_add_iff k).2 hv_sum).sum_add_tsum_nat_add 1
    simpa [r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.symm
  have hr_anti : Antitone r := antitone_nat_of_succ_le fun k ↦ by
    rw [hr_step k]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hv_norm_sum : Summable fun n ↦ ‖v n‖ := by
    apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hv_norm
      summable_geometric_two
  have hr_tendsto : Tendsto r atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro k
      change ‖∑' j, v (j + k)‖ ≤ ∑' j, ‖v (j + k)‖
      exact norm_tsum_le_tsum_norm
        ((summable_nat_add_iff (f := fun n ↦ ‖v n‖) k).2 hv_norm_sum)
    · exact tendsto_sum_nat_add (fun n ↦ ‖v n‖)
  refine ⟨φ, hφ, ?_⟩
  let K := ULift.{u} ℕ
  let rr : K → X := fun k ↦ r k.down
  have hrr_range : Set.range rr = Set.range r := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.down, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨ULift.up k, rfl⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, rr,
    fun _ _ h ↦ hr_anti h, fun k ↦ hr_nonneg k.down, ?_, ?_⟩
  · rw [hrr_range]
    exact isGLB_of_tendsto_atTop hr_anti hr_tendsto
  intro k
  apply eventually_atTop.mpr
  refine ⟨k.down, fun n hn ↦ ?_⟩
  have htail : Summable fun j ↦ v (j + k.down) :=
    (summable_nat_add_iff k.down).2 hv_sum
  have hterm : v (n - k.down + k.down) ≤ r k.down := by
    exact htail.le_tsum (n - k.down) (fun j _ ↦ abs_nonneg _)
  simpa [v, r, rr, Function.comp_apply, Nat.sub_add_cancel hn] using hterm

/-- Identifies order adherence with norm closure under order continuity; used
for the forward implications in the Gao--Leung characterization. -/
private theorem orderAdherence_eq_closure [IsOrderContinuousNorm X] (A : Set X) :
    orderAdherence A = closure A := by
  apply Set.Subset.antisymm
  · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    exact mem_closure_of_tendsto (tendsto_of_orderConvergesTo_of_isOrderContinuousNorm hfx)
      (Eventually.of_forall hf)
  · intro x hx
    obtain ⟨z, hzA, hzx⟩ := mem_closure_iff_seq_limit.mp hx
    obtain ⟨φ, hφ, hzφ⟩ := norm_tendsto_has_order_convergent_subsequence hzx
    let I := ULift.{u} ℕ
    refine ⟨I, inferInstance, inferInstance, inferInstance,
      fun i ↦ z (φ i.down), fun i ↦ hzA _, ?_⟩
    rcases hzφ with ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, hbound⟩
    refine ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, ?_⟩
    intro k
    obtain ⟨n, hn⟩ := eventually_atTop.mp (hbound k)
    apply eventually_atTop.mpr
    refine ⟨ULift.up n, fun i hi ↦ ?_⟩
    exact hn i.down hi

end

section DisjointEmbedding

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*}

/-- Propagates pairwise disjointness to a scalar multiple and a finite sum;
used in the finite disjoint-sum estimate below. -/
private lemma isVLDisjoint_smul_finset_sum
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (a : P → ℝ) {p : P} {F : Finset P} (hp : p ∉ F) :
    IsVLDisjoint (a p • x p) (∑ q ∈ F, a q • x q) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right (a p • x p)
  | @insert q F hq ih =>
      rw [Finset.sum_insert hq]
      have hp' : p ≠ q ∧ p ∉ F := by
        simpa only [Finset.mem_insert, not_or] using hp
      apply IsVLDisjoint.add_right
      · exact ((hx hp'.1).smul_left (a p)).smul_right (a q)
      · exact ih hp'.2

/-- Bounds a positive finite combination of disjoint vectors by one common
order bound; this supplies boundedness for the supremum defining the embedding. -/
private lemma finset_disjoint_sum_le
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ M) (F : Finset P) :
    ∑ p ∈ F, a p • x p ≤ M • b := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using smul_nonneg hM hb
  | @insert p F hp ih =>
      rw [Finset.sum_insert hp]
      have hterm : a p • x p ≤ M • b :=
        (smul_le_smul_of_nonneg_left (hxb p).2 (ha p).1).trans
          (smul_le_smul_of_nonneg_right (ha p).2 hb)
      have hterm0 : 0 ≤ a p • x p := smul_nonneg (ha p).1 (hxb p).1
      have hsum0 : 0 ≤ ∑ q ∈ F, a q • x q := by
        exact Finset.sum_nonneg fun q _ ↦ smul_nonneg (ha q).1 (hxb q).1
      have hdisj := isVLDisjoint_smul_finset_sum hx a hp
      have hadd : a p • x p + ∑ q ∈ F, a q • x q =
          a p • x p ⊔ ∑ q ∈ F, a q • x q := by
        simpa [abs_of_nonneg hterm0, abs_of_nonneg hsum0] using
          (sup_abs_eq_add_abs_of_isVLDisjoint hdisj).symm
      rw [hadd]
      exact sup_le hterm ih

end DisjointEmbedding

section DisjointEmbedding

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]

/-- Supplies the vector-lattice structure on bounded scalar functions required
as the domain of `disjointEmbedding`. -/
private noncomputable instance boundedContinuousFunctionVectorLattice :
    VectorLattice (P →ᵇ ℝ) where
  toModule := inferInstance
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h p
    exact mul_le_mul_of_nonneg_left (h p) ha

/-- The finite positive combinations approximating the disjoint embedding;
their supremum is defined separately as `disjointSup`. -/
private noncomputable def disjointFiniteSum (x : P → X)
    (a : P →ᵇ ℝ) (F : Finset P) : X :=
  ∑ p ∈ F, a p • x p

/-- The supremum of all finite coefficient sums; used as the positive-cone
map extended linearly in `disjointEmbedding`. -/
private noncomputable def disjointSup (x : P → X) (a : P →ᵇ ℝ) : X :=
  sSup (Set.range (disjointFiniteSum x a))

omit [DiscreteTopology P] in
/-- Packages the defining finite sums as a genuine least upper bound; reused
throughout the construction of `disjointEmbedding`. -/
private theorem disjointSup_isLUB
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P →ᵇ ℝ} (ha : 0 ≤ a) :
    IsLUB (Set.range (disjointFiniteSum x a)) (disjointSup x a) := by
  classical
  have ha' : ∀ p, 0 ≤ a p ∧ a p ≤ ‖a‖ := by
    intro p
    exact ⟨ha p, (le_abs_self (a p)).trans
      (by simpa [Real.norm_eq_abs] using a.norm_coe_le_norm p)⟩
  have hbound : BddAbove (Set.range (disjointFiniteSum x a)) := by
    refine ⟨‖a‖ • b, ?_⟩
    rintro _ ⟨F, rfl⟩
    exact finset_disjoint_sum_le hx hb hxb (norm_nonneg a) ha' F
  refine ⟨?_, ?_⟩
  · intro y hy
    exact SigmaConditionallyCompleteLattice.le_csSup _ _ (Set.countable_range _)
      hbound hy
  · intro y hy
    exact SigmaConditionallyCompleteLattice.csSup_le _ _ (Set.countable_range _)
      (Set.range_nonempty _) hy

omit [DiscreteTopology P] in
/-- Records positivity of `disjointSup`; needed by the positive linear
extension used to construct `disjointEmbedding`. -/
private theorem disjointSup_nonneg
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P →ᵇ ℝ} (ha : 0 ≤ a) :
    0 ≤ disjointSup x a := by
  apply (disjointSup_isLUB hx hb hxb ha).1
  exact ⟨∅, by simp [disjointFiniteSum]⟩

omit [DiscreteTopology P] in
/-- Proves additivity of `disjointSup` on the positive cone, the second input
to the positive linear extension defining `disjointEmbedding`. -/
private theorem disjointSup_add
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a c : P →ᵇ ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    disjointSup x (a + c) = disjointSup x a + disjointSup x c := by
  classical
  have hac : 0 ≤ a + c := add_nonneg ha hc
  have hA := disjointSup_isLUB hx hb hxb ha
  have hC := disjointSup_isLUB hx hb hxb hc
  have hAC := disjointSup_isLUB hx hb hxb hac
  apply le_antisymm
  · apply hAC.2
    rintro _ ⟨F, rfl⟩
    simp only [disjointFiniteSum, BoundedContinuousFunction.add_apply, add_smul,
      Finset.sum_add_distrib]
    exact add_le_add (hA.1 ⟨F, rfl⟩) (hC.1 ⟨F, rfl⟩)
  · rw [add_comm, ← le_sub_iff_add_le]
    apply hC.2
    rintro _ ⟨G, rfl⟩
    rw [le_sub_iff_add_le]
    rw [add_comm, ← le_sub_iff_add_le]
    apply hA.2
    rintro _ ⟨F, rfl⟩
    rw [le_sub_iff_add_le]
    let H := F ∪ G
    have hFa : disjointFiniteSum x a F ≤ disjointFiniteSum x a H := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      intro p _ _
      exact smul_nonneg (ha p) (hxb p).1
    have hGc : disjointFiniteSum x c G ≤ disjointFiniteSum x c H := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right)
      intro p _ _
      exact smul_nonneg (hc p) (hxb p).1
    calc
      disjointFiniteSum x a F + disjointFiniteSum x c G ≤
          disjointFiniteSum x a H + disjointFiniteSum x c H := add_le_add hFa hGc
      _ = disjointFiniteSum x (a + c) H := by
        simp only [disjointFiniteSum, BoundedContinuousFunction.add_apply, add_smul,
          Finset.sum_add_distrib]
      _ ≤ disjointSup x (a + c) := hAC.1 ⟨H, rfl⟩

/-- Converts disjoint scalar coefficients on one vector into disjoint scalar
multiples; used when comparing finite sums with disjoint coefficient functions. -/
private lemma isVLDisjoint_smul_same_of_inf_eq_zero
    {x : X} {a c : ℝ} (hac : a ⊓ c = 0) :
    IsVLDisjoint (a • x) (c • x) := by
  by_cases hle : a ≤ c
  · have ha0 : a = 0 := by simpa [inf_eq_left.mpr hle] using hac
    rw [ha0, zero_smul]
    exact isVLDisjoint_zero_left _
  · have hc0 : c = 0 := by
      simpa [inf_eq_right.mpr (le_of_not_ge hle)] using hac
    rw [hc0, zero_smul]
    exact isVLDisjoint_zero_right _

omit [DiscreteTopology P] [Countable P] in
/-- Extends coefficientwise disjointness from one summand to a finite sum;
used to prove disjointness of two finite approximating sums. -/
private lemma isVLDisjoint_smul_finset_sum_of_inf_eq_zero
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0)
    (p : P) (G : Finset P) :
    IsVLDisjoint (a p • x p) (disjointFiniteSum x c G) := by
  classical
  induction G using Finset.induction_on with
  | empty => simpa [disjointFiniteSum] using isVLDisjoint_zero_right (a p • x p)
  | @insert q G hq ih =>
      rw [disjointFiniteSum, Finset.sum_insert hq]
      apply IsVLDisjoint.add_right
      · by_cases hpq : p = q
        · subst q
          apply isVLDisjoint_smul_same_of_inf_eq_zero
          have hp := congrArg (fun f : P →ᵇ ℝ ↦ f p) hac
          simpa using hp
        · exact ((hx hpq).smul_left (a p)).smul_right (c q)
      · simpa [disjointFiniteSum] using ih

omit [DiscreteTopology P] [Countable P] in
/-- Shows that finite sums with disjoint coefficient functions are disjoint;
used to pass disjointness to their order suprema. -/
private lemma isVLDisjoint_finset_sums_of_inf_eq_zero
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0)
    (F G : Finset P) :
    IsVLDisjoint (disjointFiniteSum x a F) (disjointFiniteSum x c G) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa [disjointFiniteSum] using isVLDisjoint_zero_left (disjointFiniteSum x c G)
  | @insert p F hp ih =>
      rw [disjointFiniteSum, Finset.sum_insert hp]
      exact IsVLDisjoint.add_left
        (isVLDisjoint_smul_finset_sum_of_inf_eq_zero hx hac p G)
        (by simpa [disjointFiniteSum] using ih)

omit [DiscreteTopology P] in
/-- Passes disjointness of coefficient functions to the corresponding
`disjointSup` values; this proves that the eventual embedding is a lattice map. -/
private theorem disjointSup_disjoint
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0) :
    disjointSup x a ⊓ disjointSup x c = 0 := by
  have ha : 0 ≤ a := hac ▸ inf_le_left
  have hc : 0 ≤ c := hac ▸ inf_le_right
  have hA := disjointSup_isLUB hx hb hxb ha
  have hC := disjointSup_isLUB hx hb hxb hc
  let BC : Band X := Band.disjointComplement {disjointSup x c}
  have hfiniteA : Set.range (disjointFiniteSum x a) ⊆ (BC : Set X) := by
    rintro _ ⟨F, rfl⟩ _ hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    let BF : Band X := Band.disjointComplement {disjointFiniteSum x a F}
    have hfiniteC : Set.range (disjointFiniteSum x c) ⊆ (BF : Set X) := by
      rintro _ ⟨G, rfl⟩ _ hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      exact isVLDisjoint_comm.mp
        (isVLDisjoint_finset_sums_of_inf_eq_zero hx hac F G)
    have htauC : disjointSup x c ∈ BF :=
      BF.sSup_mem hfiniteC (Set.range_nonempty _) hC
    exact isVLDisjoint_comm.mp (htauC _ rfl)
  have htauA : disjointSup x a ∈ BC :=
    BC.sSup_mem hfiniteA (Set.range_nonempty _) hA
  exact inf_eq_zero_of_isVLDisjoint
    (disjointSup_nonneg hx hb hxb ha) (disjointSup_nonneg hx hb hxb hc)
    (htauA _ rfl)

/-- Embeds bounded coefficient functions along a disjoint family; this is the
main device used to transport the row-limit counterexample into `X`. -/
private noncomputable def disjointEmbedding
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b) :
    VecLatHom (P →ᵇ ℝ) X := by
  letI : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  let tau : (P →ᵇ ℝ) → X := disjointSup x
  have htau_nonneg : ∀ a, 0 ≤ a → 0 ≤ tau a :=
    fun _ ha ↦ disjointSup_nonneg hx hb hxb ha
  have htau_add : ∀ a c, 0 ≤ a → 0 ≤ c → tau (a + c) = tau a + tau c :=
    fun _ _ ha hc ↦ disjointSup_add hx hb hxb ha hc
  let T : (P →ᵇ ℝ) →ₗ[ℝ] X := Positive.extension htau_nonneg htau_add
  apply IsVecLatHom.mk' T
  apply IsVecLatHom.of_disjoint T.isLinear (Positive.extension_positive htau_nonneg htau_add)
  intro a c hac
  have ha : 0 ≤ a := hac ▸ inf_le_left
  have hc : 0 ≤ c := hac ▸ inf_le_right
  rw [Positive.extension_nonneg htau_nonneg htau_add ha,
    Positive.extension_nonneg htau_nonneg htau_add hc]
  exact disjointSup_disjoint hx hb hxb hac

omit [DiscreteTopology P] in
/-- Evaluates `disjointEmbedding` on the positive cone as `disjointSup`; used
for its order, norm, and band estimates. -/
private theorem disjointEmbedding_apply_nonneg
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    (a : P →ᵇ ℝ) (ha : 0 ≤ a) :
    disjointEmbedding x hx b hb hxb a = disjointSup x a := by
  rw [disjointEmbedding]
  exact Positive.extension_nonneg
    (fun _ ha ↦ disjointSup_nonneg hx hb hxb ha)
    (fun _ _ ha hc ↦ disjointSup_add hx hb hxb ha hc) ha

omit [DiscreteTopology P] in
/-- Controls each coordinate summand by the absolute value of its embedded
vector; used both for the lower norm estimate and coordinate convergence. -/
private theorem abs_apply_smul_le_abs_disjointEmbedding
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    (a : P →ᵇ ℝ) (p : P) :
    |a p| • x p ≤ |disjointEmbedding x hx b hb hxb a| := by
  rw [← (disjointEmbedding x hx b hb hxb).map_abs,
    disjointEmbedding_apply_nonneg x hx b hb hxb |a| (abs_nonneg a)]
  apply (disjointSup_isLUB hx hb hxb (abs_nonneg a)).1
  refine ⟨{p}, ?_⟩
  simp [disjointFiniteSum]

omit [DiscreteTopology P] in
/-- Gives the embedding a uniform lower norm bound from the disjoint sequence;
used to bound coefficient functions in the row-limit exclusion argument. -/
private theorem disjointEmbedding_lower_bound
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {ε : ℝ} (hε : 0 < ε) (hxnorm : ∀ p, ε ≤ ‖x p‖) (a : P →ᵇ ℝ) :
    ε * ‖a‖ ≤ ‖disjointEmbedding x hx b hb hxb a‖ := by
  have hcoord : ∀ p, ε * |a p| ≤ ‖disjointEmbedding x hx b hb hxb a‖ := by
    intro p
    have horder := abs_apply_smul_le_abs_disjointEmbedding x hx b hb hxb a p
    have hnorm : ‖|a p| • x p‖ ≤ ‖disjointEmbedding x hx b hb hxb a‖ := by
      rw [← norm_abs_eq_norm (disjointEmbedding x hx b hb hxb a)]
      apply norm_le_norm_of_abs_le_abs
      simpa [abs_of_nonneg (smul_nonneg (abs_nonneg _) (hxb p).1)] using horder
    calc
      ε * |a p| ≤ ‖x p‖ * |a p| := by gcongr; exact hxnorm p
      _ = ‖|a p| • x p‖ := by
        rw [norm_smul, Real.norm_of_nonneg (abs_nonneg _), mul_comm]
      _ ≤ _ := hnorm
  have hanorm : ‖a‖ ≤ ε⁻¹ * ‖disjointEmbedding x hx b hb hxb a‖ := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (inv_nonneg.mpr hε.le)
      (norm_nonneg _))).2
    intro p
    rw [Real.norm_eq_abs, le_inv_mul_iff₀ hε]
    simpa [mul_comm] using hcoord p
  calc
    ε * ‖a‖ ≤ ε * (ε⁻¹ * ‖disjointEmbedding x hx b hb hxb a‖) :=
      mul_le_mul_of_nonneg_left hanorm hε.le
    _ = ‖disjointEmbedding x hx b hb hxb a‖ := by field_simp

omit [DiscreteTopology P] in
/-- Places positive embedded functions in the band generated by the disjoint
family; used in the proof of coordinatewise uo-convergence. -/
private theorem disjointEmbedding_nonneg_mem_doubleDisjointComplement
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    (a : P →ᵇ ℝ) (ha : 0 ≤ a) :
    disjointEmbedding x hx b hb hxb a ∈ (Set.range x)ᵈᵈ := by
  let B : Band X := Band.disjointComplement ((Set.range x)ᵈ)
  rw [disjointEmbedding_apply_nonneg x hx b hb hxb a ha]
  apply B.sSup_mem (S := Set.range (disjointFiniteSum x a))
  · rintro _ ⟨F, rfl⟩
    apply B.toOrderIdeal.toSubmodule.sum_mem
    intro p hp
    apply B.toOrderIdeal.toSubmodule.smul_mem
    exact subset_disjointComplement_disjointComplement (Set.range x) ⟨p, rfl⟩
  · exact Set.range_nonempty _
  · exact disjointSup_isLUB hx hb hxb ha

omit [DiscreteTopology P] in
/-- A zero coefficient makes the embedded vector disjoint from that coordinate;
used to show that eventually vanishing coordinates converge uo. -/
private theorem isVLDisjoint_disjointEmbedding_of_apply_eq_zero
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    (a : P →ᵇ ℝ) (ha : 0 ≤ a) (p : P) (hap : a p = 0) :
    IsVLDisjoint (disjointEmbedding x hx b hb hxb a) (x p) := by
  classical
  let B : Band X := Band.disjointComplement {x p}
  rw [disjointEmbedding_apply_nonneg x hx b hb hxb a ha]
  have hfinite : Set.range (disjointFiniteSum x a) ⊆ (B : Set X) := by
    rintro _ ⟨F, rfl⟩
    change ∀ y ∈ ({x p} : Set X), IsVLDisjoint (disjointFiniteSum x a F) y
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    induction F using Finset.induction_on with
    | empty => simpa [disjointFiniteSum] using isVLDisjoint_zero_left (x p)
    | @insert q F hq ih =>
        rw [disjointFiniteSum, Finset.sum_insert hq]
        apply IsVLDisjoint.add_left
        · by_cases hqp : q = p
          · subst q
            rw [hap, zero_smul]
            exact isVLDisjoint_zero_left _
          · exact (hx hqp).smul_left (a q)
        · simpa [disjointFiniteSum] using ih
  have htau : disjointSup x a ∈ B :=
    B.sSup_mem hfinite (Set.range_nonempty _) (disjointSup_isLUB hx hb hxb ha)
  exact htau _ rfl

end DisjointEmbedding

section DisjointSequence

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- Extracts a positive order-bounded disjoint sequence with norms bounded away
from zero from failure of order continuity; this starts the reverse implication. -/
private theorem exists_orderBounded_disjoint_sequence_norm_bounded_away
    (hX : ¬ IsOrderContinuousNorm X) :
    ∃ (ε : ℝ) (b : X) (x : ℕ → X), 0 < ε ∧ 0 ≤ b ∧
      Pairwise (fun m n ↦ IsVLDisjoint (x m) (x n)) ∧
      ∀ n, 0 ≤ x n ∧ x n ≤ b ∧ ε ≤ ‖x n‖ := by
  classical
  rw [BanachLattice.isOrderContinuousNorm_iff_disjoint_tendsto_zero] at hX
  push Not at hX
  obtain ⟨z, hzdisj, hzbdd, hznot⟩ := hX
  rw [Metric.tendsto_atTop] at hznot
  push Not at hznot
  obtain ⟨ε, hε, hzlarge⟩ := hznot
  let S : Set ℕ := {n | ε ≤ ‖z n‖}
  have hSinf : S.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hnε⟩ := hzlarge (N + 1)
    have hnS : n ∈ S := by simpa [S, dist_zero_right] using hnε
    have := hN hnS
    omega
  let e : ℕ ↪ S := hSinf.natEmbedding S
  let φ : ℕ → ℕ := fun n ↦ (e n).1
  let x : ℕ → X := fun n ↦ |z (φ n)|
  obtain ⟨b, hb⟩ := hzbdd
  have hxb : ∀ n, x n ≤ b := fun n ↦ hb ⟨φ n, rfl⟩
  have hb0 : 0 ≤ b := (abs_nonneg (z (φ 0))).trans (hxb 0)
  refine ⟨ε, b, x, hε, hb0, ?_, ?_⟩
  · intro m n hmn
    have hφ : φ m ≠ φ n := by
      intro h
      apply hmn
      exact e.injective (Subtype.ext h)
    simpa [x, IsVLDisjoint] using hzdisj hφ
  · intro n
    refine ⟨abs_nonneg _, hxb n, ?_⟩
    have he : (e n).1 ∈ S := (e n).2
    change ε ≤ ‖z (φ n)‖ at he
    simpa [x, norm_abs_eq_norm] using he

end DisjointSequence

section RowLimitSublattice

/-- The two-dimensional coordinate set used by the row-limit example. -/
private abbrev PairIndex := ℕ × ℕ

/-- Bounded scalar functions on the row-limit coordinate set. -/
private abbrev PairLInfinity := PairIndex →ᵇ ℝ

/-- Functions whose row tails converge to the scaled row head; bundled first
as a submodule before adding lattice closure. -/
private def rowLimitSubmodule : Submodule ℝ PairLInfinity where
  carrier := {a | ∀ m : ℕ,
    Tendsto (fun n : ℕ ↦ a (m, n + 1)) atTop
      (nhds ((m + 1 : ℕ) * a (m, 0)))}
  zero_mem' := by simp
  add_mem' := by
    intro a c ha hc m
    simpa [mul_add] using (ha m).add (hc m)
  smul_mem' := by
    intro r a ha m
    simpa [mul_assoc, mul_left_comm, mul_comm] using (ha m).const_smul r

/-- The row-limit submodule as a vector sublattice; its image supplies the
sublattice separating order adherence from uo-adherence. -/
private noncomputable def rowLimitSublattice : VectorSublattice PairLInfinity :=
  VectorSublattice.ofAbsClosed rowLimitSubmodule fun a ha ↦ by
    intro m
    change Tendsto (fun k => |a (m, k + 1)|) atTop (𝓝 ((m + 1 : ℕ) * |a (m, 0)|))
    simpa only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ))]
      using (ha m).abs

/-- The limiting row-head function that belongs to uo-adherence but will be
excluded from order adherence. -/
private noncomputable def rowHead : PairLInfinity :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p : PairIndex ↦ if p.2 = 0 then 1 else 0) 1 (by
      intro p
      simp [Real.norm_eq_abs]
      split_ifs <;> norm_num)

/-- Finite row approximations to `rowHead`; these lie in `rowLimitSublattice`
and agree eventually at every coordinate. -/
private noncomputable def rowApprox (j : ℕ) : PairLInfinity :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p : PairIndex ↦
      if p.2 = 0 then
        if p.1 ≤ j then 1 else 0
      else if p.1 ≤ j ∧ j < p.2 then (p.1 + 1 : ℕ) else 0)
    (j + 1) (by
      intro p
      rw [Real.norm_eq_abs]
      by_cases hn : p.2 = 0
      · simp only [hn, ite_true]
        by_cases hm : p.1 ≤ j
        · rw [ite_eq_left hm, abs_one]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
        · rw [ite_eq_right hm, abs_zero]
          positivity
      · simp only [hn, ite_false]
        by_cases ht : p.1 ≤ j ∧ j < p.2
        · rw [ite_eq_left ht, abs_of_nonneg (by positivity)]
          exact_mod_cast Nat.succ_le_succ ht.1
        · rw [ite_eq_right ht, abs_zero]
          positivity)

/-- Verifies that every finite row approximation belongs to the row-limit
sublattice, so its image can witness uo-adherence. -/
private theorem rowApprox_mem (j : ℕ) : rowApprox j ∈ rowLimitSublattice := by
  intro m
  by_cases hm : m ≤ j
  · have heq :
        (fun n : ℕ ↦ rowApprox j (m, n + 1)) =ᶠ[atTop]
          (fun _ ↦ (m + 1 : ℕ)) := by
      apply eventually_atTop.mpr
      refine ⟨j, fun n hn ↦ ?_⟩
      simp [rowApprox, hm]
      omega
    have ht := tendsto_const_nhds.congr' heq.symm
    simpa [rowApprox, hm] using ht
  · have heq :
        (fun n : ℕ ↦ rowApprox j (m, n + 1)) =ᶠ[atTop]
          (fun _ ↦ 0) := by
      filter_upwards with n
      simp [rowApprox, hm]
    have ht := tendsto_const_nhds.congr' heq.symm
    simp [rowApprox, hm]

/-- Records eventual coordinatewise agreement of the row approximations with
`rowHead`; this is the input for their embedded uo-convergence. -/
private theorem rowApprox_eventually_apply_eq_rowHead (p : PairIndex) :
    ∀ᶠ j in atTop, rowApprox j p = rowHead p := by
  apply eventually_atTop.mpr
  refine ⟨max p.1 p.2, fun j hj ↦ ?_⟩
  by_cases hn : p.2 = 0
  · simp [rowApprox, rowHead, hn]
    omega
  · simp [rowApprox, rowHead, hn]
    omega

end RowLimitSublattice

section CoordinatewiseUO

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]

omit [DiscreteTopology P] [Countable P] in
/-- Turns eventual coordinatewise vanishing into order convergence after
clamping; used to establish uo-convergence of the disjoint embedding. -/
private theorem orderConvergesTo_inf_of_eventually_coordinate_zero
    (x : P → X) (T : VecLatHom (P →ᵇ ℝ) X) (d : ℕ → P →ᵇ ℝ)
    (hd0 : ∀ j, 0 ≤ d j)
    (hband : ∀ j, T (d j) ∈ (Set.range x)ᵈᵈ)
    (hdisj : ∀ j p, d j p = 0 → IsVLDisjoint (T (d j)) (x p))
    (hdzero : ∀ p, ∀ᶠ j in atTop, d j p = 0) (w : X) (hw : 0 ≤ w) :
    OrderConvergesTo (fun j ↦ T (d j) ⊓ w) 0 := by
  classical
  let z : ℕ → X := fun j ↦ T (d j) ⊓ w
  have hTd0 : ∀ j, 0 ≤ T (d j) := fun j ↦
    by simpa using T.monotone (hd0 j)
  have hz0 : ∀ j, 0 ≤ z j := fun j ↦ le_inf (hTd0 j) hw
  have hzw : ∀ j, z j ≤ w := fun _ ↦ inf_le_right
  let r : ℕ → X := fun k ↦ sSup (Set.range fun j ↦ z (j + k))
  have hrLUB : ∀ k, IsLUB (Set.range fun j ↦ z (j + k)) (r k) := by
    intro k
    refine ⟨?_, ?_⟩
    · intro y hy
      exact SigmaConditionallyCompleteLattice.le_csSup _ _ (Set.countable_range _)
        ⟨w, by rintro _ ⟨j, rfl⟩; exact hzw (j + k)⟩ hy
    · intro y hy
      exact SigmaConditionallyCompleteLattice.csSup_le _ _ (Set.countable_range _)
        (Set.range_nonempty _) hy
  have hr0 : ∀ k, 0 ≤ r k := fun k ↦
    (hz0 k).trans ((hrLUB k).1 ⟨0, by simp⟩)
  have hranti : Antitone r := antitone_nat_of_succ_le fun k ↦ by
    apply (hrLUB (k + 1)).2
    rintro _ ⟨j, rfl⟩
    apply (hrLUB k).1
    exact ⟨j + 1, congrArg z (by omega)⟩
  let q : X := sInf (Set.range r)
  have hqGLB : IsGLB (Set.range r) q := by
    refine ⟨?_, ?_⟩
    · intro y hy
      exact SigmaConditionallyCompleteLattice.csInf_le _ _ (Set.countable_range _)
        ⟨0, by rintro _ ⟨k, rfl⟩; exact hr0 k⟩ hy
    · intro y hy
      exact SigmaConditionallyCompleteLattice.le_csInf _ _ (Set.countable_range _)
        (Set.range_nonempty _) hy
  have hq0 : 0 ≤ q := hqGLB.2 (by rintro _ ⟨k, rfl⟩; exact hr0 k)
  let A : Set X := Set.range x
  let B : Band X := Band.disjointComplement Aᵈ
  have hzB : ∀ j, z j ∈ B := by
    intro j
    apply B.toOrderIdeal.solid (hband j) (hz0 j) inf_le_left
  have hrB : ∀ k, r k ∈ B := fun k ↦
    B.sSup_mem (by rintro _ ⟨j, rfl⟩; exact hzB (j + k))
      (Set.range_nonempty _) (hrLUB k)
  have hqB : q ∈ B :=
    B.toOrderIdeal.solid (hrB 0) hq0 (hqGLB.1 ⟨0, rfl⟩)
  have hq_disjoint : q ∈ Aᵈ := by
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hdzero p)
    let D : Band X := Band.disjointComplement {x p}
    have hzD : Set.range (fun j ↦ z (j + N)) ⊆ (D : Set X) := by
      rintro _ ⟨j, rfl⟩ _ hy'
      rw [Set.mem_singleton_iff] at hy'
      subst hy'
      have hTd := hdisj (j + N) p (hN (j + N) (by omega))
      apply hTd.mono_left
      rw [abs_of_nonneg (hz0 (j + N)), abs_of_nonneg (hTd0 (j + N))]
      exact inf_le_left
    have hrD : r N ∈ D :=
      D.sSup_mem hzD (Set.range_nonempty _) (hrLUB N)
    apply (hrD _ rfl).mono_left
    simp only [abs_of_nonneg hq0, abs_of_nonneg (hr0 N)]
    exact hqGLB.1 ⟨N, rfl⟩
  have hqeq : q = 0 := by
    apply Set.mem_singleton_iff.mp
    exact disjointComplement_inter_eq_zero Aᵈ ⟨hq_disjoint, hqB⟩
  have hrGLB : IsGLB (Set.range r) 0 := by simpa [hqeq] using hqGLB
  refine ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance,
    fun k ↦ r k.down, fun _ _ h ↦ hranti h, fun k ↦ hr0 k.down, ?_, ?_⟩
  · have hrange : Set.range (fun k : ULift.{u} ℕ ↦ r k.down) = Set.range r := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨k.down, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨ULift.up k, rfl⟩
    rw [hrange]
    exact hrGLB
  · intro k
    apply eventually_atTop.mpr
    refine ⟨k.down, fun j hj ↦ ?_⟩
    have hzle : z j ≤ r k.down := by
      apply (hrLUB k.down).1
      exact ⟨j - k.down, congrArg z (Nat.sub_add_cancel hj)⟩
    simpa [abs_of_nonneg (hz0 j), z] using hzle

omit [DiscreteTopology P] in
/-- Transfers eventual coordinatewise equality to uo-convergence through the
disjoint embedding; applied to `rowApprox` and `rowHead`. -/
private theorem disjointEmbedding_uoConverges_of_eventuallyEq
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    (a : ℕ → P →ᵇ ℝ) (e : P →ᵇ ℝ)
    (hae : ∀ p, ∀ᶠ j in atTop, a j p = e p) :
    UOConvergesTo (fun j ↦ disjointEmbedding x hx b hb hxb (a j))
      (disjointEmbedding x hx b hb hxb e) := by
  classical
  let T := disjointEmbedding x hx b hb hxb
  let d : ℕ → P →ᵇ ℝ := fun j ↦ |a j - e|
  have hd0 : ∀ j, 0 ≤ d j := fun _ ↦ abs_nonneg _
  intro w hw
  have hz := orderConvergesTo_inf_of_eventually_coordinate_zero x T d hd0
    (fun j ↦ disjointEmbedding_nonneg_mem_doubleDisjointComplement
      x hx b hb hxb (d j) (hd0 j))
    (fun j p hp ↦ isVLDisjoint_disjointEmbedding_of_apply_eq_zero
      x hx b hb hxb (d j) (hd0 j) p hp)
    (fun p ↦ (hae p).mono fun j hj ↦ by simp [d, hj]) w hw
  convert hz using 1
  ext j
  dsimp only [d]
  change |T (a j) - T e| ⊓ w = T |a j - e| ⊓ w
  apply congrArg (fun y : X ↦ y ⊓ w)
  calc
    |T (a j) - T e| = |T (a j - e)| := congrArg abs (map_sub T (a j) e).symm
    _ = T |a j - e| := (T.map_abs _).symm

end CoordinatewiseUO

section SublatticeImage

variable {E : Type*} {X : Type*}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]

/-- Bundles the image of a vector sublattice under a lattice homomorphism;
used to place the row-limit construction inside the ambient lattice. -/
private def vectorSublatticeImage (T : VecLatHom E X) (H : VectorSublattice E) :
    VectorSublattice X where
  carrier := T '' (H : Set E)
  zero_mem' := ⟨0, H.toSubmodule.zero_mem, map_zero T⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, H.toSubmodule.add_mem ha hc, map_add T a c⟩
  smul_mem' := by
    rintro r _ ⟨a, ha, rfl⟩
    exact ⟨r • a, H.toSubmodule.smul_mem r ha, map_smul T r a⟩
  sup_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a ⊔ c, H.sup_mem ha hc, T.map_sup' a c⟩

end SublatticeImage

section CoordinateConvergence

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]

omit [DiscreteTopology P] in
/-- Recovers convergence of each nonzero coordinate from order convergence of
embedded functions; used to exclude `rowHead` from order adherence. -/
private theorem tendsto_apply_of_disjointEmbedding_orderConvergesTo
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {I : Type*} [Preorder I]
    (c : I → P →ᵇ ℝ) (e : P →ᵇ ℝ)
    (hc : OrderConvergesTo
      (fun i ↦ disjointEmbedding x hx b hb hxb (c i))
      (disjointEmbedding x hx b hb hxb e)) (p : P) (hxp : x p ≠ 0) :
    Tendsto (fun i ↦ c i p) atTop (nhds (e p)) := by
  classical
  rw [Metric.tendsto_nhds]
  by_contra hnot
  push Not at hnot
  obtain ⟨δ, hδ, hfreq⟩ := hnot
  rcases hc with ⟨K, hpre, hdir, hne, r, hranti, hr0, hrglb, hbound⟩
  let : Preorder K := hpre
  let : IsDirected K (· ≤ ·) := hdir
  let : Nonempty K := hne
  have hlower : δ • x p ∈ lowerBounds (Set.range r) := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, hiδ, hibound⟩ := (hfreq.and_eventually (hbound k)).exists
    have hcoeff := abs_apply_smul_le_abs_disjointEmbedding
      x hx b hb hxb (c i - e) p
    have hscale : δ • x p ≤ |c i p - e p| • x p := by
      apply smul_le_smul_of_nonneg_right
      · simpa [Real.dist_eq] using hiδ
      · exact (hxb p).1
    calc
      δ • x p ≤ |c i p - e p| • x p := hscale
      _ ≤ |disjointEmbedding x hx b hb hxb (c i - e)| := by simpa using hcoeff
      _ = |disjointEmbedding x hx b hb hxb (c i) -
          disjointEmbedding x hx b hb hxb e| := by rw [map_sub]
      _ ≤ r k := hibound
  have hnonpos : δ • x p ≤ 0 := hrglb.2 hlower
  have hzero : δ • x p = 0 :=
    le_antisymm hnonpos (smul_nonneg hδ.le (hxb p).1)
  exact (smul_ne_zero hδ.ne' hxp) hzero

end CoordinateConvergence

section RowLimitExclusion

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- Shows that the embedded row head is not an order-adherence point of the
row-limit image, providing the strict separation needed in the counterexample. -/
private theorem rowHead_not_mem_orderAdherence_image
    (x : PairIndex → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {ε : ℝ} (hε : 0 < ε) (hxnorm : ∀ p, ε ≤ ‖x p‖) :
    disjointEmbedding x hx b hb hxb rowHead ∉
      orderAdherence (vectorSublatticeImage
        (disjointEmbedding x hx b hb hxb) rowLimitSublattice : Set X) := by
  classical
  let T := disjointEmbedding x hx b hb hxb
  let Y := vectorSublatticeImage T rowLimitSublattice
  rintro ⟨I, hpre, hdir, hne, f, hfY, hforder⟩
  let : Preorder I := hpre
  let : IsDirected I (· ≤ ·) := hdir
  let : Nonempty I := hne
  have hpreimage : ∀ i, ∃ c : PairLInfinity, c ∈ rowLimitSublattice ∧ T c = f i := by
    intro i
    exact hfY i
  choose c hcH hcT using hpreimage
  have hcorder : OrderConvergesTo (fun i ↦ T (c i)) (T rowHead) := by
    convert hforder using 1
    ext i
    exact hcT i
  have hcorder' := hcorder
  rcases hcorder' with ⟨K, hkpre, hkdir, hkne, r, hranti, hr0, hrglb, hbound⟩
  let : Preorder K := hkpre
  let : IsDirected K (· ≤ ·) := hkdir
  let : Nonempty K := hkne
  let k₀ : K := Classical.choice inferInstance
  let C : ℝ := ‖r k₀‖ + ‖T rowHead‖
  have hTbound : ∀ᶠ i in atTop, ‖T (c i)‖ ≤ C := by
    filter_upwards [hbound k₀] with i hi
    have hdiff : ‖T (c i) - T rowHead‖ ≤ ‖r k₀‖ := by
      apply norm_le_norm_of_abs_le_abs
      simpa [abs_of_nonneg (hr0 k₀)] using hi
    calc
      ‖T (c i)‖ = ‖(T (c i) - T rowHead) + T rowHead‖ := by
        congr 1
        abel
      _ ≤ ‖T (c i) - T rowHead‖ + ‖T rowHead‖ := norm_add_le _ _
      _ ≤ C := add_le_add hdiff le_rfl
  let M : ℝ := ε⁻¹ * C
  have hcbound : ∀ᶠ i in atTop, ‖c i‖ ≤ M := by
    filter_upwards [hTbound] with i hi
    have hlower := disjointEmbedding_lower_bound x hx b hb hxb hε hxnorm (c i)
    rw [le_inv_mul_iff₀ hε]
    exact hlower.trans hi
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M)
  have hmM : M < (m + 1 : ℕ) / 2 := by
    norm_num
    nlinarith
  have hxp : x (m, 0) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (hε.trans_le (hxnorm (m, 0)))
  have hcoord := tendsto_apply_of_disjointEmbedding_orderConvergesTo
    x hx b hb hxb c rowHead hcorder (m, 0) hxp
  have hhalf : ∀ᶠ i in atTop, (1 / 2 : ℝ) < c i (m, 0) := by
    apply hcoord
    exact Ioi_mem_nhds (show (1 / 2 : ℝ) < rowHead (m, 0) by simp [rowHead]; norm_num)
  obtain ⟨i, hic, hihalf⟩ := (hcbound.and hhalf).exists
  have hlimit_le : (m + 1 : ℕ) * c i (m, 0) ≤ M := by
    apply le_of_tendsto' (hcH i m)
    intro n
    calc
      c i (m, n + 1) ≤ |c i (m, n + 1)| := le_abs_self _
      _ = ‖c i (m, n + 1)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖c i‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ M := hic
  have hlimit_gt : M < (m + 1 : ℕ) * c i (m, 0) := by
    calc
      M < (m + 1 : ℕ) / 2 := hmM
      _ < (m + 1 : ℕ) * c i (m, 0) := by
        have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
        nlinarith
  exact (not_lt_of_ge hlimit_le) hlimit_gt

end RowLimitExclusion

section LiftConvergence

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

omit [IsOrderedAddMonoid X] in
/-- Reindexes sequential order convergence by `ULift ℕ`; used to match the
universe required by the definitions of adherence. -/
private theorem orderConvergesTo_uliftNat {f : ℕ → X} {x : X}
    (h : OrderConvergesTo f x) :
    OrderConvergesTo (fun i : ULift.{u} ℕ ↦ f i.down) x := by
  rcases h with ⟨K, hpre, hdir, hne, r, hranti, hr0, hrglb, hbound⟩
  refine ⟨K, hpre, hdir, hne, r, hranti, hr0, hrglb, ?_⟩
  intro k
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hbound k)
  apply eventually_atTop.mpr
  exact ⟨ULift.up n, fun i hi ↦ hn i.down hi⟩

omit [IsOrderedAddMonoid X] in
/-- Reindexes sequential uo-convergence by `ULift ℕ`; used when inserting the
row approximations into uo-adherence. -/
private theorem uoConvergesTo_uliftNat {f : ℕ → X} {x : X}
    (h : UOConvergesTo f x) :
    UOConvergesTo (fun i : ULift.{u} ℕ ↦ f i.down) x := by
  intro a ha
  exact orderConvergesTo_uliftNat (h a ha)

end LiftConvergence

section ReverseImplication

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- Derives order continuity from equality of order and uo-adherence on every
vector sublattice; this is the reverse step of the Gao--Leung cycle. -/
private theorem orderContinuousNorm_of_forall_orderAdherence_eq_uoAdherence
    (h : ∀ Y : VectorSublattice X,
      orderAdherence (Y : Set X) = uoAdherence (Y : Set X)) :
    IsOrderContinuousNorm X := by
  classical
  by_contra hX
  obtain ⟨ε, b, xn, hε, hb, hxpair, hxn⟩ :=
    exists_orderBounded_disjoint_sequence_norm_bounded_away hX
  let x : PairIndex → X := fun p ↦ xn (Nat.pairEquiv p)
  have hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q) := by
    intro p q hpq
    apply hxpair
    exact fun hp ↦ hpq (Nat.pairEquiv.injective hp)
  have hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b := fun p ↦ ⟨(hxn _).1, (hxn _).2.1⟩
  have hxnorm : ∀ p, ε ≤ ‖x p‖ := fun p ↦ (hxn _).2.2
  let T := disjointEmbedding x hx b hb hxb
  let Y := vectorSublatticeImage T rowLimitSublattice
  have huolim : UOConvergesTo (fun j ↦ T (rowApprox j)) (T rowHead) :=
    disjointEmbedding_uoConverges_of_eventuallyEq x hx b hb hxb rowApprox rowHead
      rowApprox_eventually_apply_eq_rowHead
  have huomem : T rowHead ∈ uoAdherence (Y : Set X) := by
    refine ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance,
      fun j ↦ T (rowApprox j.down), ?_,
      uoConvergesTo_uliftNat (f := fun j ↦ T (rowApprox j)) huolim⟩
    intro j
    exact ⟨rowApprox j.down, rowApprox_mem j.down, rfl⟩
  have hordmem : T rowHead ∈ orderAdherence (Y : Set X) := by
    rw [h Y]
    exact huomem
  exact rowHead_not_mem_orderAdherence_image x hx b hb hxb hε hxnorm hordmem

end ReverseImplication

section Characterization

variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- Gao--Leung, Theorem 2.7 (paper Theorem `ND`). -/
theorem gaoLeung_orderContinuous_characterization :
    ((∀ Y : VectorSublattice X, IsOrderClosed (orderAdherence (Y : Set X))) ↔
      (∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X))) ∧
    ((∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X)) ↔
      IsOrderContinuousNorm X) := by
  let A : Prop := ∀ Y : VectorSublattice X,
    IsOrderClosed (orderAdherence (Y : Set X))
  let B : Prop := ∀ Y : VectorSublattice X,
    orderAdherence (Y : Set X) = uoAdherence (Y : Set X)
  let C : Prop := IsOrderContinuousNorm X
  have hCA : C → A := by
    intro hC
    let : IsOrderContinuousNorm X := hC
    intro Y
    change orderAdherence (orderAdherence (Y : Set X)) ⊆ orderAdherence (Y : Set X)
    rw [orderAdherence_eq_closure, orderAdherence_eq_closure, closure_closure]
  have hAB : A → B := by
    intro hA Y
    apply Set.Subset.antisymm
    · exact (orderAdherence_subset_uoAdherence_subset (Y := Y)).1
    · intro x hx
      exact hA Y ((orderAdherence_subset_uoAdherence_subset (Y := Y)).2 hx)
  have hBC : B → C := by
    exact orderContinuousNorm_of_forall_orderAdherence_eq_uoAdherence
  exact ⟨⟨hAB, fun hB ↦ hCA (hBC hB)⟩, ⟨hBC, fun hC ↦ hAB (hCA hC)⟩⟩

end Characterization

end OrderClosures
