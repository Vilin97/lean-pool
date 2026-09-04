/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.MathlibFoundations
import LeanPool.Wallace.TriangularPreprocess

/-!
# Block-density filters for the Wallace construction

This file packages the density-one filter used in the paper.  The formulation is deliberately
abstract in the finite blocks: the later scheduling module only has to provide nonempty blocks
which eventually avoid every finite set and a deletion bound whose relative size tends to zero.
-/

open Filter Set Topology
open scoped Topology

namespace Wallace

noncomputable section

/-- Finite blocks which move to infinity. -/
structure BlockSystem where
  block : ℕ → Finset ℕ
  block_nonempty : ∀ l, (block l).Nonempty
  eventually_disjoint_finite :
    ∀ K : Finset ℕ, {l | Disjoint (block l) K} ∈ (atTop : Filter ℕ)

namespace BlockSystem

/-- The concrete block system supplied by the triangular preprocessing enumeration.  Its blocks
have the prescribed cardinalities and partition `ℕ`; in particular, every finite set of positions
meets only finitely many block labels. -/
def ofBlockPositions (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) : BlockSystem where
  block := TriangularPreprocess.blockPositions N hN
  block_nonempty := by
    intro l
    apply Finset.card_pos.mp
    simpa only [TriangularPreprocess.blockPositions_card] using hN l
  eventually_disjoint_finite := by
    intro K
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [
      (K.image (TriangularPreprocess.blockOf N hN)).finite_toSet.compl_mem_cofinite
    ] with l hl
    rw [Finset.disjoint_left]
    intro n hnblock hnK
    apply hl
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨n, hnK, (TriangularPreprocess.mem_blockPositions_iff N hN).mp hnblock⟩

@[simp]
theorem ofBlockPositions_block (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (l : ℕ) :
    (ofBlockPositions N hN).block l = TriangularPreprocess.blockPositions N hN l :=
  rfl

theorem ofBlockPositions_card (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (l : ℕ) :
    ((ofBlockPositions N hN).block l).card = N l :=
  TriangularPreprocess.blockPositions_card N hN l

/-- Proportion of a block missing from a set. -/
noncomputable def missingRatio (B : BlockSystem) (A : Set ℕ) (l : ℕ) : ℝ := by
  classical
  exact (((B.block l).filter fun n ↦ n ∉ A).card : ℝ) / ((B.block l).card : ℝ)

theorem missingRatio_nonneg (B : BlockSystem) (A : Set ℕ) (l : ℕ) :
    0 ≤ B.missingRatio A l := by
  unfold missingRatio
  positivity

@[simp]
theorem missingRatio_univ (B : BlockSystem) (l : ℕ) :
    B.missingRatio Set.univ l = 0 := by
  classical
  simp [missingRatio]

@[simp]
theorem missingRatio_empty (B : BlockSystem) (l : ℕ) :
    B.missingRatio ∅ l = 1 := by
  classical
  unfold missingRatio
  simp only [Set.mem_empty_iff_false, not_false_eq_true, Finset.filter_true]
  exact div_self (by
    exact_mod_cast (B.block_nonempty l).card_pos.ne')

theorem missingRatio_mono (B : BlockSystem) {A C : Set ℕ} (hAC : A ⊆ C) (l : ℕ) :
    B.missingRatio C l ≤ B.missingRatio A l := by
  classical
  unfold missingRatio
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hnA ↦ hn.2 (hAC hnA)⟩)

theorem missingRatio_inter_le (B : BlockSystem) (A C : Set ℕ) (l : ℕ) :
    B.missingRatio (A ∩ C) l ≤ B.missingRatio A l + B.missingRatio C l := by
  classical
  let (n : ℕ) : Decidable (n ∈ A ∩ C) := Classical.propDecidable _
  have hsubset :
      (B.block l).filter (fun n ↦ n ∉ A ∩ C) ⊆
        (B.block l).filter (fun n ↦ n ∉ A) ∪
          (B.block l).filter (fun n ↦ n ∉ C) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
    rcases hn with ⟨hnb, hnAC⟩
    by_cases hnA : n ∈ A
    · exact Or.inr ⟨hnb, fun hnC ↦ hnAC ⟨hnA, hnC⟩⟩
    · exact Or.inl ⟨hnb, hnA⟩
  have hcard :
      ((B.block l).filter (fun n ↦ n ∉ A ∩ C)).card ≤
        ((B.block l).filter (fun n ↦ n ∉ A)).card +
          ((B.block l).filter (fun n ↦ n ∉ C)).card := by
    exact (Finset.card_le_card hsubset).trans
      ((Finset.card_union_le _ _).trans_eq rfl)
  unfold missingRatio
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right (by
    exact_mod_cast (B.block_nonempty l).card_pos)).mpr
  norm_cast

/-- Sets having block density one along the labels in `a`. -/
def IsLarge (B : BlockSystem) (a A : Set ℕ) : Prop :=
  Tendsto (B.missingRatio A) (atTop ⊓ Filter.principal a) (nhds 0)

/-- The block-density-one sets form a filter. -/
def densityFilter (B : BlockSystem) (a : Set ℕ) : Filter ℕ where
  sets := {A | B.IsLarge a A}
  univ_sets := by
    exact tendsto_congr' (Eventually.of_forall (B.missingRatio_univ)) |>.mpr tendsto_const_nhds
  sets_of_superset := by
    intro A C hA hAC
    apply squeeze_zero' (Eventually.of_forall (B.missingRatio_nonneg C))
      (Eventually.of_forall fun l ↦ B.missingRatio_mono hAC l) hA
  inter_sets := by
    intro A C hA hC
    apply squeeze_zero' (Eventually.of_forall (B.missingRatio_nonneg (A ∩ C)))
      (Eventually.of_forall fun l ↦ B.missingRatio_inter_le A C l)
    simpa using hA.add hC

@[simp]
theorem mem_densityFilter_iff (B : BlockSystem) (a A : Set ℕ) :
    A ∈ B.densityFilter a ↔ B.IsLarge a A :=
  Iff.rfl

/-- Every cofinite set has block density one.  In mathlib's reverse-inclusion order on filters,
this says that the density filter lies below the cofinite filter. -/
theorem densityFilter_le_cofinite (B : BlockSystem) (a : Set ℕ) :
    B.densityFilter a ≤ cofinite := by
  classical
  rw [le_cofinite_iff_compl_singleton_mem]
  intro n
  let (k : ℕ) : Decidable (k ∈ ({n} : Set ℕ)ᶜ) := Classical.propDecidable _
  rw [mem_densityFilter_iff]
  unfold IsLarge
  apply tendsto_congr' ?_ |>.mpr tendsto_const_nhds
  have hdisjoint := B.eventually_disjoint_finite {n}
  filter_upwards [(inf_le_left : atTop ⊓ Filter.principal a ≤ atTop) hdisjoint] with l hl
  unfold missingRatio
  have hempty : (B.block l).filter (fun k ↦ k ∉ ({n} : Set ℕ)ᶜ) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k hkblock
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
    intro hkn
    subst k
    exact Finset.disjoint_left.mp hl hkblock (Finset.mem_singleton_self n)
  have hcardzero :
      ((B.block l).filter (fun k ↦ k ∉ ({n} : Set ℕ)ᶜ)).card = 0 :=
    Finset.card_eq_zero.mpr hempty
  have hcastzero :
      (((B.block l).filter (fun k ↦ k ∉ ({n} : Set ℕ)ᶜ)).card : ℝ) = 0 := by
    exact_mod_cast hcardzero
  rw [hcastzero]
  exact zero_div _

/-- If the label set is infinite, the block-density filter is proper. -/
theorem densityFilter_neBot (B : BlockSystem) {a : Set ℕ} (ha : a.Infinite) :
    (B.densityFilter a).NeBot := by
  rw [Filter.neBot_iff]
  intro hbot
  have hempty : (∅ : Set ℕ) ∈ B.densityFilter a := by
    rw [hbot]
    exact Filter.mem_bot
  rw [mem_densityFilter_iff] at hempty
  unfold IsLarge at hempty
  have : NeBot (atTop ⊓ Filter.principal a) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ha.cofinite_inf_principal_neBot
  have hone_tendsto :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) (atTop ⊓ Filter.principal a) (nhds 0) := by
    convert hempty using 1
    funext l
    exact (B.missingRatio_empty l).symm
  have hone : (1 : ℝ) = 0 := tendsto_const_nhds_iff.mp hone_tendsto
  exact one_ne_zero hone

/-- The density filter along an infinite almost-disjoint label set has a free ultrafilter
extension.  Both refinement inequalities are recorded explicitly. -/
theorem exists_free_ultrafilter_le_densityFilter
    (B : BlockSystem) {a : Set ℕ} (ha : a.Infinite) :
    ∃ p : Ultrafilter ℕ,
      (p : Filter ℕ) ≤ B.densityFilter a ∧ (p : Filter ℕ) ≤ cofinite := by
  let : (B.densityFilter a).NeBot := B.densityFilter_neBot ha
  exact exists_free_ultrafilter_le_filter (B.densityFilter a)
    (B.densityFilter_le_cofinite a)

end BlockSystem

namespace AlmostDisjoint

variable {ι α : Type*}

/-- The union of the members that occur strictly before `j` in an enumeration. -/
def earlierUnion [Preorder ι] (family : ι → Set α) (j : ι) : Set α :=
  ⋃ i ∈ Set.Iio j, family i

/-- The standard recursive disjointization from the paper:
`b_j = a_j \ \bigcup_{i<j} a_i`. -/
def disjointize [Preorder ι] (family : ι → Set α) (j : ι) : Set α :=
  family j \ earlierUnion family j

theorem disjointize_subset [Preorder ι] (family : ι → Set α) (j : ι) :
    disjointize family j ⊆ family j :=
  Set.sdiff_subset

/-- Disjointization makes any linearly enumerated family pairwise disjoint; no
almost-disjointness assumption is needed for this part. -/
theorem pairwise_disjoint_disjointize [LinearOrder ι] (family : ι → Set α) :
    Pairwise fun i j ↦ Disjoint (disjointize family i) (disjointize family j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    exact hxj.2 (Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem hij hxi.1)
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    exact hxi.2 (Set.mem_iUnion_of_mem j <| Set.mem_iUnion_of_mem hji hxj.1)

/-- If `a_j` has finite intersection with every predecessor and `j` has only finitely
many predecessors, then the disjointization removes only finitely many points. -/
theorem disjointize_loss_finite [LinearOrder ι] (family : ι → Set α)
    (had : Pairwise fun i j ↦ (family i ∩ family j).Finite) (j : ι)
    (hpred : (Set.Iio j).Finite) :
    (family j \ disjointize family j).Finite := by
  have hfiniteUnion : (⋃ i ∈ Set.Iio j, family j ∩ family i).Finite :=
    hpred.biUnion fun i hi ↦ had (ne_of_gt hi)
  refine hfiniteUnion.subset ?_
  intro x hx
  have hxj : x ∈ family j := hx.1
  have hxEarlier : x ∈ earlierUnion family j := by
    by_contra hxnot
    exact hx.2 ⟨hxj, hxnot⟩
  rcases Set.mem_iUnion.mp hxEarlier with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hxi with ⟨hi, hxFamily⟩
  exact Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem hi ⟨hxj, hxFamily⟩

end AlmostDisjoint

namespace BlockSystem

/-- The points retained after deleting `E l` from every block whose label belongs to `b`.
This is exactly the set `U_α` in equation (retained) of the paper. -/
def retainedBlocks (B : BlockSystem) (b : Set ℕ) (E : ℕ → Finset ℕ) : Set ℕ :=
  ⋃ l ∈ b, ↑(B.block l \ E l)

/-- On a retained label, every point missing from the retained union lies in the
corresponding deletion set. -/
theorem missingRatio_retainedBlocks_le (B : BlockSystem) (b : Set ℕ)
    (E : ℕ → Finset ℕ) {l : ℕ} (hlb : l ∈ b) :
    B.missingRatio (B.retainedBlocks b E) l ≤
      ((E l).card : ℝ) / ((B.block l).card : ℝ) := by
  classical
  unfold missingRatio
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn
  rcases hn with ⟨hnblock, hnmissing⟩
  by_contra hnE
  apply hnmissing
  exact Set.mem_iUnion_of_mem l <| Set.mem_iUnion_of_mem hlb <| by
    simp only [Finset.mem_coe, Finset.mem_sdiff]
    exact ⟨hnblock, hnE⟩

/-- The paper's quantitative estimate `deficit ≤ R_l / card(block_l)`. -/
theorem missingRatio_retainedBlocks_le_bound (B : BlockSystem) (b : Set ℕ)
    (E : ℕ → Finset ℕ) (R : ℕ → ℕ) {l : ℕ} (hlb : l ∈ b)
    (hcard : (E l).card ≤ R l) :
    B.missingRatio (B.retainedBlocks b E) l ≤
      (R l : ℝ) / ((B.block l).card : ℝ) := by
  refine (B.missingRatio_retainedBlocks_le b E hlb).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

/-- Bounded block deletions with vanishing relative bound are retained by the density
filter.  The hypothesis `a \ b` finite records `b =* a` together with `b ⊆ a`, which is
the precise direction needed for the limit along `a`. -/
theorem retainedBlocks_mem_densityFilter (B : BlockSystem) {a b : Set ℕ}
    (E : ℕ → Finset ℕ) (R : ℕ → ℕ)
    (hab : (a \ b).Finite) (_hE : ∀ l, E l ⊆ B.block l)
    (hcard : ∀ l ∈ b, (E l).card ≤ R l)
    (hratio : Tendsto (fun l ↦ (R l : ℝ) / ((B.block l).card : ℝ)) atTop (nhds 0)) :
    B.retainedBlocks b E ∈ B.densityFilter a := by
  rw [mem_densityFilter_iff]
  unfold IsLarge
  have havoidAtTop : ∀ᶠ l in atTop, l ∉ a \ b := by
    rw [← Nat.cofinite_eq_atTop]
    exact hab.compl_mem_cofinite
  have havoid : ∀ᶠ l in atTop ⊓ Filter.principal a, l ∉ a \ b :=
    (inf_le_left : atTop ⊓ Filter.principal a ≤ atTop) havoidAtTop
  have hina : ∀ᶠ l in atTop ⊓ Filter.principal a, l ∈ a :=
    (inf_le_right : atTop ⊓ Filter.principal a ≤ Filter.principal a) (by simp)
  have hinb : ∀ᶠ l in atTop ⊓ Filter.principal a, l ∈ b := by
    filter_upwards [hina, havoid] with l hla hlavoid
    exact Classical.byContradiction fun hlb ↦ hlavoid ⟨hla, hlb⟩
  apply squeeze_zero' (Eventually.of_forall fun l ↦
      B.missingRatio_nonneg (B.retainedBlocks b E) l) ?_
    (hratio.mono_left inf_le_left)
  filter_upwards [hinb] with l hlb
  exact B.missingRatio_retainedBlocks_le_bound b E R hlb (hcard l hlb)

/-- Concrete specialization to the triangular preprocessing blocks.  The denominator is now the
prescribed paper size `N l`, by `blockPositions_card`. -/
theorem retainedBlocks_mem_densityFilter_ofBlockPositions
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) {a b : Set ℕ}
    (E : ℕ → Finset ℕ) (R : ℕ → ℕ)
    (hab : (a \ b).Finite) (hE : ∀ l, E l ⊆ (ofBlockPositions N hN).block l)
    (hcard : ∀ l ∈ b, (E l).card ≤ R l)
    (hratio : Tendsto (fun l ↦ (R l : ℝ) / (N l : ℝ)) atTop (nhds 0)) :
    (ofBlockPositions N hN).retainedBlocks b E ∈
      (ofBlockPositions N hN).densityFilter a := by
  apply (ofBlockPositions N hN).retainedBlocks_mem_densityFilter E R hab hE hcard
  simpa only [ofBlockPositions_card] using hratio

end BlockSystem

end

end Wallace
