/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import Mathlib.Tactic.DeriveEncodable
public import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundDecomposition

/-!
# Dyadic stopping intervals for the Calderón--Zygmund decomposition

This module supplies an explicit global dyadic grid and proves the quantitative
parent/child facts behind the height-one stopping rule. In particular, a
child of a good parent has `‖f‖`-average at most two.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal BigOperators Function Topology

namespace QuadraticCarleson
namespace CalderonZygmundDyadicStopping


noncomputable
section

/-- Length of a depth-`n` cell in the dyadic grid with root length `L`. -/
def dyadicLength (L : ℝ) (n : ℕ) : ℝ := L / (2 : ℝ) ^ n

/-- The half-open dyadic cell with depth `n` and integer address `q`. -/
def dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) : Set ℝ :=
  Ico ((q : ℝ) * dyadicLength L n) (((q : ℝ) + 1) * dyadicLength L n)

theorem dyadicLength_pos {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < dyadicLength L n := by
  exact div_pos hL (by positivity)

theorem dyadicLength_succ (L : ℝ) (n : ℕ) :
    dyadicLength L (n + 1) = dyadicLength L n / 2 := by
  simp [dyadicLength, pow_succ]
  ring

@[simp] theorem volume_dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) :
    volume (dyadicInterval L n q) = ENNReal.ofReal (dyadicLength L n) := by
  rw [dyadicInterval, Real.volume_Ico]
  congr 1
  ring

theorem volumeReal_dyadicInterval {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    volume.real (dyadicInterval L n q) = dyadicLength L n := by
  rw [Measure.real, volume_dyadicInterval]
  exact ENNReal.toReal_ofReal (div_nonneg hL (by positivity))

theorem leftChild_subset {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    dyadicInterval L (n + 1) (2 * q) ⊆ dyadicInterval L n q := by
  intro x hx
  simp only [dyadicInterval, mem_Ico] at hx ⊢
  rw [dyadicLength_succ] at hx
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hx ⊢
  constructor <;> nlinarith

theorem rightChild_subset {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    dyadicInterval L (n + 1) (2 * q + 1) ⊆ dyadicInterval L n q := by
  intro x hx
  simp only [dyadicInterval, mem_Ico] at hx ⊢
  rw [dyadicLength_succ] at hx
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hx ⊢
  constructor <;> nlinarith

theorem left_right_children_disjoint {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    Disjoint (dyadicInterval L (n + 1) (2 * q))
      (dyadicInterval L (n + 1) (2 * q + 1)) := by
  apply Set.disjoint_left.2
  intro x hxleft hxright
  simp only [dyadicInterval, mem_Ico] at hxleft hxright
  rw [dyadicLength_succ] at hxleft hxright
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hxleft hxright
  linarith

/-- A coarse dyadic length is an integral power-of-two multiple of every
finer dyadic length. -/
theorem dyadicLength_eq_pow_mul {L : ℝ} {n m : ℕ} (hnm : n ≤ m) :
    dyadicLength L n = (2 : ℝ) ^ (m - n) * dyadicLength L m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold dyadicLength
  rw [Nat.add_sub_cancel_left]
  rw [pow_add]
  field_simp

/-- At different depths, a fine dyadic cell is either contained in a given
coarser cell or disjoint from it. This is the arithmetic laminarity property
of the half-open global dyadic grid. -/
theorem dyadicInterval_subset_or_disjoint_of_le {L : ℝ} (hL : 0 < L)
    {n m : ℕ} (hnm : n ≤ m) (q r : ℤ) :
    dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L m r) (dyadicInterval L n q) := by
  let D : ℤ := (2 : ℕ) ^ (m - n)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) (m - n))
  have hlen := dyadicLength_eq_pow_mul (L := L) hnm
  have hcastD : (D : ℝ) = (2 : ℝ) ^ (m - n) := by
    simp [D]
  have hdm : 0 < dyadicLength L m := dyadicLength_pos hL m
  by_cases hrange : q * D ≤ r ∧ r < (q + 1) * D
  · left
    intro x hx
    simp only [dyadicInterval, mem_Ico] at hx ⊢
    have hloZ : q * D ≤ r := hrange.1
    have hhiZ : r + 1 ≤ (q + 1) * D := by omega
    have hloR : ((q * D : ℤ) : ℝ) * dyadicLength L m ≤
        (r : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hloZ) hdm.le
    have hhiR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
        (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hhiZ) hdm.le
    rw [hlen, ← hcastD]
    push_cast at hloR hhiR ⊢
    constructor <;> nlinarith
  · right
    rw [not_and_or] at hrange
    rcases hrange with hlo | hhi
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : r + 1 ≤ q * D := by omega
      have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
          ((q * D : ℤ) : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : (q + 1) * D ≤ r := by omega
      have hzR : (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m ≤
          (r : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith

/-- Any two cells in the global dyadic grid are nested or disjoint. -/
theorem dyadicInterval_laminar {L : ℝ} (hL : 0 < L)
    (n : ℕ) (q : ℤ) (m : ℕ) (r : ℤ) :
    dyadicInterval L n q ⊆ dyadicInterval L m r ∨
      dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L n q) (dyadicInterval L m r) := by
  rcases le_total n m with hnm | hmn
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hnm q r with hsub | hdis
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hdis.symm)
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hmn r q with hsub | hdis
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hdis)

/-- Distinct cells at one fixed depth are disjoint. -/
theorem dyadicInterval_disjoint_of_sameDepth {L : ℝ} (hL : 0 < L)
    (n : ℕ) {q r : ℤ} (hqr : q ≠ r) :
    Disjoint (dyadicInterval L n q) (dyadicInterval L n r) := by
  apply Set.disjoint_left.2
  intro x hxq hxr
  simp only [dyadicInterval, mem_Ico] at hxq hxr
  have hd : 0 < dyadicLength L n := dyadicLength_pos hL n
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hz : q + 1 ≤ r := by omega
    have hzR : ((q + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (r : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith
  · have hz : r + 1 ≤ q := by omega
    have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (q : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith

theorem dyadicInterval_nonempty {L : ℝ} (hL : 0 < L) (n : ℕ) (q : ℤ) :
    (dyadicInterval L n q).Nonempty := by
  rw [dyadicInterval, nonempty_Ico]
  have hd := dyadicLength_pos hL n
  nlinarith

/-- The data-dependent root length. It is strictly larger than the global
`L¹` mass, so every depth-zero cell has average at most one. -/
def rootLength (f : ℝ → ℂ) : ℝ :=
  (∫ x, ‖f x‖) + 1

theorem rootLength_pos {f : ℝ → ℂ} : 0 < rootLength f := by
  have hmass : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (μ := volume)
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  unfold rootLength
  linarith

/-- The scalar `‖f‖` average on a dyadic cell. -/
def dyadicNormAverage (f : ℝ → ℂ) (L : ℝ) (n : ℕ) (q : ℤ) : ℝ :=
  ⨍ x in dyadicInterval L n q, ‖f x‖

theorem dyadicNormAverage_eq {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (n : ℕ) (q : ℤ) :
    dyadicNormAverage f L n q =
      (∫ x in dyadicInterval L n q, ‖f x‖) / dyadicLength L n := by
  rw [dyadicNormAverage, setAverage_eq, volumeReal_dyadicInterval hL.le]
  rw [div_eq_inv_mul]
  simp only [smul_eq_mul]

theorem root_dyadicNormAverage_le_one {f : ℝ → ℂ} (hf : Integrable f) (q : ℤ) :
    dyadicNormAverage f (rootLength f) 0 q ≤ 1 := by
  have hlocal : (∫ x in dyadicInterval (rootLength f) 0 q, ‖f x‖) ≤ ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  rw [dyadicNormAverage_eq rootLength_pos, dyadicLength]
  simp only [pow_zero, div_one]
  have hmass : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (μ := volume)
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  rw [div_le_one (by unfold rootLength; linarith)]
  exact hlocal.trans (by unfold rootLength; linarith)

private theorem child_integral_le_parent
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} {n : ℕ} {q child : ℤ}
    (hsub : dyadicInterval L (n + 1) child ⊆ dyadicInterval L n q) :
    (∫ x in dyadicInterval L (n + 1) child, ‖f x‖) ≤
      ∫ x in dyadicInterval L n q, ‖f x‖ := by
  apply setIntegral_mono_set hf.norm.integrableOn
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  exact Filter.Eventually.of_forall hsub

/-- Quantitative stopping lemma: the left child of a height-one good parent
has average at most two. -/
theorem leftChild_dyadicNormAverage_le_two
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    {n : ℕ} {q : ℤ} (hparent : dyadicNormAverage f L n q ≤ 1) :
    dyadicNormAverage f L (n + 1) (2 * q) ≤ 2 := by
  have hmono := child_integral_le_parent hf (leftChild_subset hL.le n q)
  rw [dyadicNormAverage_eq hL] at hparent
  rw [dyadicNormAverage_eq hL, dyadicLength_succ]
  have hlen : 0 < dyadicLength L n := dyadicLength_pos hL n
  rw [div_le_iff₀ (half_pos hlen)]
  rw [div_le_iff₀ hlen] at hparent
  nlinarith

/-- Quantitative stopping lemma for the right child. -/
theorem rightChild_dyadicNormAverage_le_two
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    {n : ℕ} {q : ℤ} (hparent : dyadicNormAverage f L n q ≤ 1) :
    dyadicNormAverage f L (n + 1) (2 * q + 1) ≤ 2 := by
  have hmono := child_integral_le_parent hf (rightChild_subset hL.le n q)
  rw [dyadicNormAverage_eq hL] at hparent
  rw [dyadicNormAverage_eq hL, dyadicLength_succ]
  have hlen : 0 < dyadicLength L n := dyadicLength_pos hL n
  rw [div_le_iff₀ (half_pos hlen)]
  rw [div_le_iff₀ hlen] at hparent
  nlinarith

/-! ## The intrinsic first-crossing stopping predicate -/

/-- An address in the global dyadic forest. Every tree starts at a depth-zero
cell, and `left`/`right` record successive bisections. -/
inductive DyadicNode where
  | root (q : ℤ)
  | left (parent : DyadicNode)
  | right (parent : DyadicNode)
  deriving DecidableEq, Encodable

/-- Depth of a dyadic node. -/
def DyadicNode.depth : DyadicNode → ℕ
  | .root _ => 0
  | .left p => p.depth + 1
  | .right p => p.depth + 1

/-- Integer address of a dyadic node in the global grid at its depth. -/
def DyadicNode.index : DyadicNode → ℤ
  | .root q => q
  | .left p => 2 * p.index
  | .right p => 2 * p.index + 1

theorem DyadicNode.depth_index_injective :
    Function.Injective (fun p : DyadicNode ↦ (p.depth, p.index)) := by
  intro p
  induction p with
  | root q =>
      intro r h
      cases r with
      | root s => simp only [depth, index, Prod.mk.injEq] at h; simp [h.2]
      | left r => simp [depth] at h
      | right r => simp [depth] at h
  | left p ih =>
      intro r h
      cases r with
      | root s => simp [depth] at h
      | left r =>
          simp only [depth, index, Prod.mk.injEq] at h
          have hindex : p.index = r.index :=
            mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h.2
          have hparent : p = r := ih (Prod.ext (Nat.add_right_cancel h.1) hindex)
          simp [hparent]
      | right r =>
          simp only [depth, index, Prod.mk.injEq] at h
          omega
  | right p ih =>
      intro r h
      cases r with
      | root s => simp [depth] at h
      | left r =>
          simp only [depth, index, Prod.mk.injEq] at h
          omega
      | right r =>
          simp only [depth, index, Prod.mk.injEq] at h
          have hmul : 2 * p.index = 2 * r.index := by omega
          have hindex : p.index = r.index :=
            mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hmul
          have hparent : p = r := ih (Prod.ext (Nat.add_right_cancel h.1) hindex)
          simp [hparent]

/-- The half-open interval represented by a node. -/
def DyadicNode.interval (L : ℝ) (p : DyadicNode) : Set ℝ :=
  dyadicInterval L p.depth p.index

/-- The scalar norm average on the interval represented by a node. -/
def DyadicNode.normAverage (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : ℝ :=
  dyadicNormAverage f L p.depth p.index

@[simp] theorem DyadicNode.interval_root (L : ℝ) (q : ℤ) :
    (DyadicNode.root q).interval L = dyadicInterval L 0 q := rfl

@[simp] theorem DyadicNode.interval_left (L : ℝ) (p : DyadicNode) :
    p.left.interval L =
      dyadicInterval L (p.depth + 1) (2 * p.index) := rfl

@[simp] theorem DyadicNode.interval_right (L : ℝ) (p : DyadicNode) :
    p.right.interval L =
      dyadicInterval L (p.depth + 1) (2 * p.index + 1) := rfl

theorem DyadicNode.left_interval_subset {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : p.left.interval L ⊆ p.interval L :=
  leftChild_subset hL p.depth p.index

theorem DyadicNode.right_interval_subset {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : p.right.interval L ⊆ p.interval L :=
  rightChild_subset hL p.depth p.index

theorem DyadicNode.children_disjoint {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : Disjoint (p.left.interval L) (p.right.interval L) :=
  left_right_children_disjoint hL p.depth p.index

/-- All strict dyadic ancestors of a node have height-one-good norm average.
This is stated intrinsically in terms of the global grid: every strictly
coarser cell containing the node's interval is good. -/
def ancestorsGood (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < p.depth →
    p.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1

/-- A first-crossing stopping node: its own norm average is above one, while
every strict ancestor has average at most one. -/
def IsStoppingNode (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ancestorsGood f L p ∧ 1 < p.normAverage f L

/-- The subtype of intrinsic stopping nodes for the data-dependent root
length. It is countable because the dyadic forest itself is encodable. -/
def stoppingNode (f : ℝ → ℂ) :=
  {p : DyadicNode // IsStoppingNode f (rootLength f) p}

instance stoppingNode_countable (f : ℝ → ℂ) : Countable (stoppingNode f) :=
  Subtype.val_injective.countable

theorem stoppingNode_lower_average {f : ℝ → ℂ} (p : stoppingNode f) :
    1 < p.1.normAverage f (rootLength f) := p.2.2

theorem root_not_stopping {f : ℝ → ℂ} (hf : Integrable f) (q : ℤ) :
    ¬ IsStoppingNode f (rootLength f) (.root q) := by
  intro h
  exact (not_lt_of_ge (root_dyadicNormAverage_le_one hf q)) h.2

/-- The parent of a stopping node is height-one good. -/
theorem stoppingNode_parent_good {f : ℝ → ℂ} (p : stoppingNode f) :
    match p.1 with
    | .root _ => True
    | .left parent => parent.normAverage f (rootLength f) ≤ 1
    | .right parent => parent.normAverage f (rootLength f) ≤ 1 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | root q => trivial
  | left parent =>
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.left_interval_subset rootLength_pos.le parent)
  | right parent =>
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.right_interval_subset rootLength_pos.le parent)

/-- Sharp upper-average estimate for every intrinsic first-crossing node.
The factor two is exactly the ratio between a parent and either child on the
line. -/
theorem stoppingNode_upper_average {f : ℝ → ℂ} (hf : Integrable f)
    (p : stoppingNode f) :
    p.1.normAverage f (rootLength f) ≤ 2 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | root q =>
      exact (root_dyadicNormAverage_le_one hf q).trans one_le_two
  | left parent =>
      apply leftChild_dyadicNormAverage_le_two hf rootLength_pos
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.left_interval_subset rootLength_pos.le parent)
  | right parent =>
      apply rightChild_dyadicNormAverage_le_two hf rootLength_pos
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.right_interval_subset rootLength_pos.le parent)

theorem stoppingNode_average_mem_Ioc {f : ℝ → ℂ} (hf : Integrable f)
    (p : stoppingNode f) :
    p.1.normAverage f (rootLength f) ∈ Set.Ioc 1 2 :=
  ⟨stoppingNode_lower_average p, stoppingNode_upper_average hf p⟩

/-- Distinct intrinsic first-crossing nodes represent disjoint half-open
intervals. -/
theorem stoppingNode_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Disjoint on fun p : stoppingNode f ↦
      p.1.interval (rootLength f)) := by
  intro p q hpq
  have reverse_of_subset {a b : DyadicNode} (hab : a.depth ≤ b.depth)
      (hsub : a.interval (rootLength f) ⊆ b.interval (rootLength f)) :
      b.interval (rootLength f) ⊆ a.interval (rootLength f) := by
    rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hab a.index b.index with
      hrev | hdis
    · exact hrev
    · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos a.depth a.index
      exact False.elim (Set.disjoint_left.1 hdis (hsub hx) hx)
  rcases dyadicInterval_laminar rootLength_pos p.1.depth p.1.index
      q.1.depth q.1.index with hpqsub | hqpsub | hdis
  · rcases lt_trichotomy p.1.depth q.1.depth with hlt | heq | hgt
    · have hrev := reverse_of_subset hlt.le hpqsub
      have hgood := q.2.1 p.1.depth p.1.index hlt hrev
      exact False.elim ((not_lt_of_ge hgood) p.2.2)
    · by_cases hindex : p.1.index = q.1.index
      · apply False.elim
        apply hpq
        apply Subtype.ext
        apply DyadicNode.depth_index_injective
        exact Prod.ext heq hindex
      · change Disjoint
          (dyadicInterval (rootLength f) p.1.depth p.1.index)
          (dyadicInterval (rootLength f) q.1.depth q.1.index)
        rw [← heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos p.1.depth hindex
    · have hgood := p.2.1 q.1.depth q.1.index hgt hpqsub
      exact False.elim ((not_lt_of_ge hgood) q.2.2)
  · rcases lt_trichotomy q.1.depth p.1.depth with hlt | heq | hgt
    · have hrev := reverse_of_subset hlt.le hqpsub
      have hgood := p.2.1 q.1.depth q.1.index hlt hrev
      exact False.elim ((not_lt_of_ge hgood) q.2.2)
    · by_cases hindex : p.1.index = q.1.index
      · apply False.elim
        apply hpq
        apply Subtype.ext
        apply DyadicNode.depth_index_injective
        exact Prod.ext heq.symm hindex
      · change Disjoint
          (dyadicInterval (rootLength f) p.1.depth p.1.index)
          (dyadicInterval (rootLength f) q.1.depth q.1.index)
        rw [heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos p.1.depth hindex
    · have hgood := q.2.1 p.1.depth p.1.index hgt hqpsub
      exact False.elim ((not_lt_of_ge hgood) p.2.2)
  · exact hdis

/-! ## Canonically indexed stopping cells

The following pair index has no redundant representations. It is used for
the actual selected family and its countable union. -/

/-- A canonical cell is its depth and global integer index. -/
structure DyadicCell where
  /-- The dyadic depth of the cell relative to the root scale. -/
  depth : ℕ
  /-- The global integer index locating the cell at its dyadic depth. -/
  index : ℤ
  deriving DecidableEq, Encodable

/-- The dyadic interval represented by the cell at root length `L`. -/
def DyadicCell.interval (L : ℝ) (c : DyadicCell) : Set ℝ :=
  dyadicInterval L c.depth c.index

/-- The average of the norm of `f` over the cell at root length `L`. -/
def DyadicCell.normAverage (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : ℝ :=
  dyadicNormAverage f L c.depth c.index

/-- Every strictly coarser dyadic cell containing `c` is good. -/
def cellAncestorsGood (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < c.depth →
    c.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1

/-- A first-crossing cell: its norm average exceeds one and every strictly coarser ancestor has
average at most one. -/
def IsStoppingCell (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  cellAncestorsGood f L c ∧ 1 < c.normAverage f L

/-- The canonical countable family of first-crossing cells. -/
def stoppingCell (f : ℝ → ℂ) :=
  {c : DyadicCell // IsStoppingCell f (rootLength f) c}

instance stoppingCell_countable (f : ℝ → ℂ) : Countable (stoppingCell f) :=
  Subtype.val_injective.countable

theorem stoppingCell_lower_average {f : ℝ → ℂ} (c : stoppingCell f) :
    1 < c.1.normAverage f (rootLength f) := c.2.2

/-- The parent argument gives the uniform upper average two on every
canonical first-crossing cell. -/
theorem stoppingCell_upper_average {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) : c.1.normAverage f (rootLength f) ≤ 2 := by
  rcases c with ⟨⟨n, q⟩, hc⟩
  cases n with
  | zero =>
      exact (root_dyadicNormAverage_le_one hf q).trans one_le_two
  | succ n =>
      rcases Int.even_or_odd' q with ⟨r, rfl | rfl⟩
      · apply leftChild_dyadicNormAverage_le_two hf rootLength_pos
        apply hc.1 n r (by simp)
        exact leftChild_subset rootLength_pos.le n r
      · apply rightChild_dyadicNormAverage_le_two hf rootLength_pos
        apply hc.1 n r (by simp)
        exact rightChild_subset rootLength_pos.le n r

theorem stoppingCell_average_mem_Ioc {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) :
    c.1.normAverage f (rootLength f) ∈ Set.Ioc 1 2 :=
  ⟨stoppingCell_lower_average c, stoppingCell_upper_average hf c⟩

/-- The canonical first-crossing intervals are exactly pairwise disjoint. -/
theorem stoppingCell_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Disjoint on fun c : stoppingCell f ↦
      c.1.interval (rootLength f)) := by
  intro c d hcd
  rcases dyadicInterval_laminar rootLength_pos c.1.depth c.1.index
      d.1.depth d.1.index with hsub | hsub | hdis
  · rcases lt_trichotomy c.1.depth d.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          c.1.index d.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (d.2.1 c.1.depth c.1.index hlt hrev)) c.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos c.1.depth c.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [← heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (c.2.1 d.1.depth d.1.index hgt hsub)) d.2.2)
  · rcases lt_trichotomy d.1.depth c.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          d.1.index c.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (c.2.1 d.1.depth d.1.index hlt hrev)) d.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos d.1.depth d.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (d.2.1 c.1.depth c.1.index hgt hsub)) c.2.2)
  · exact hdis

/-- The union of all canonical stopping intervals for `f`. -/
def stoppingBadUnion (f : ℝ → ℂ) : Set ℝ :=
  ⋃ c : stoppingCell f, c.1.interval (rootLength f)

theorem measurableSet_stoppingCell_interval {f : ℝ → ℂ} (c : stoppingCell f) :
    MeasurableSet (c.1.interval (rootLength f)) := measurableSet_Ico

theorem measurableSet_stoppingBadUnion (f : ℝ → ℂ) :
    MeasurableSet (stoppingBadUnion f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  exact MeasurableSet.iUnion measurableSet_stoppingCell_interval

theorem volume_stoppingCell_interval {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (c.1.interval (rootLength f)) =
      ENNReal.ofReal (dyadicLength (rootLength f) c.1.depth) :=
  volume_dyadicInterval _ _ _

theorem volume_stoppingCell_interval_lt_top {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (c.1.interval (rootLength f)) < ∞ := by
  rw [volume_stoppingCell_interval]
  exact ENNReal.ofReal_lt_top

/-- Total length of the canonical stopping cells is bounded by the global
`L¹` mass. -/
theorem tsum_volume_stoppingCell_le_lintegral_norm {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∑' c : stoppingCell f, volume (c.1.interval (rootLength f))) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  let _ := Encodable.ofCountable (stoppingCell f)
  have hlocal : ∀ c : stoppingCell f,
      volume (c.1.interval (rootLength f)) ≤
        ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ := by
    intro c
    have hfin : volume (c.1.interval (rootLength f)) ≠ ∞ :=
      (volume_stoppingCell_interval_lt_top c).ne
    have havg : 1 < ⨍ x in c.1.interval (rootLength f), ‖f x‖ := c.2.2
    have hmpos : 0 < volume.real (c.1.interval (rootLength f)) := by
      rw [Measure.real, volume_stoppingCell_interval,
        ENNReal.toReal_ofReal (dyadicLength_pos rootLength_pos c.1.depth).le]
      exact dyadicLength_pos rootLength_pos c.1.depth
    have hreal : volume.real (c.1.interval (rootLength f)) <
        ∫ x in c.1.interval (rootLength f), ‖f x‖ := by
      calc
        volume.real (c.1.interval (rootLength f)) =
            volume.real (c.1.interval (rootLength f)) * 1 := by ring
        _ < volume.real (c.1.interval (rootLength f)) *
            (⨍ x in c.1.interval (rootLength f), ‖f x‖) :=
          mul_lt_mul_of_pos_left havg hmpos
        _ = ∫ x in c.1.interval (rootLength f), ‖f x‖ := by
          simpa [smul_eq_mul] using
            (measure_smul_setAverage (f := fun x ↦ ‖f x‖) hfin)
    calc
      volume (c.1.interval (rootLength f)) =
          ENNReal.ofReal (volume.real (c.1.interval (rootLength f))) := by
        rw [Measure.real, ENNReal.ofReal_toReal hfin]
      _ ≤ ENNReal.ofReal (∫ x in c.1.interval (rootLength f), ‖f x‖) :=
        ENNReal.ofReal_le_ofReal hreal.le
      _ = ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ :=
        ofReal_integral_eq_lintegral_ofReal hf.norm.integrableOn
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  calc
    (∑' c : stoppingCell f, volume (c.1.interval (rootLength f))) ≤
        ∑' c : stoppingCell f,
          ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ :=
      ENNReal.tsum_le_tsum hlocal
    _ = ∫⁻ x in stoppingBadUnion f, ENNReal.ofReal ‖f x‖ := by
      rw [stoppingBadUnion,
        lintegral_iUnion measurableSet_stoppingCell_interval stoppingCell_pairwiseDisjoint]
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := volume) (f := fun x ↦ ENNReal.ofReal ‖f x‖)
          (subset_univ (stoppingBadUnion f)))

/-! ## Minimal-depth selection and coverage reduction -/

/-- At depth `n`, some dyadic cell containing `x` has norm average above
one. -/
def HasBadCellAtDepth (f : ℝ → ℂ) (x : ℝ) (n : ℕ) : Prop :=
  ∃ q : ℤ, x ∈ dyadicInterval (rootLength f) n q ∧
    1 < dyadicNormAverage f (rootLength f) n q

/-- A bad cell at some depth contains an intrinsic first-crossing stopping
cell containing the same point. The construction takes the least bad depth,
so no maximality or selection principle is assumed. -/
theorem exists_stoppingCell_mem_of_exists_badCell {f : ℝ → ℂ} {x : ℝ}
    (hx : ∃ n, HasBadCellAtDepth f x n) :
    ∃ c : stoppingCell f, x ∈ c.1.interval (rootLength f) := by
  classical
  let n := Nat.find hx
  have hn : HasBadCellAtDepth f x n := Nat.find_spec hx
  let q := hn.choose
  have hxq : x ∈ dyadicInterval (rootLength f) n q := hn.choose_spec.1
  have hqbad : 1 < dyadicNormAverage f (rootLength f) n q := hn.choose_spec.2
  let c : DyadicCell := ⟨n, q⟩
  have hcAnc : cellAncestorsGood f (rootLength f) c := by
    intro m r hm hsub
    by_contra hnot
    have hrbad : 1 < dyadicNormAverage f (rootLength f) m r := lt_of_not_ge hnot
    have hmBad : HasBadCellAtDepth f x m :=
      ⟨r, hsub hxq, hrbad⟩
    exact (Nat.not_lt_of_ge (Nat.find_min' hx hmBad)) hm
  exact ⟨⟨c, hcAnc, hqbad⟩, hxq⟩

theorem mem_stoppingBadUnion_of_exists_badCell {f : ℝ → ℂ} {x : ℝ}
    (hx : ∃ n, HasBadCellAtDepth f x n) : x ∈ stoppingBadUnion f := by
  rcases exists_stoppingCell_mem_of_exists_badCell hx with ⟨c, hc⟩
  exact mem_iUnion.2 ⟨c, hc⟩

/-! ## Dyadic differentiation -/

/-- The unique integer index of the half-open depth-`n` cell containing a
point. -/
def containingIndex (L : ℝ) (n : ℕ) (x : ℝ) : ℤ :=
  ⌊x / dyadicLength L n⌋

theorem mem_dyadicInterval_containingIndex {L : ℝ} (hL : 0 < L)
    (n : ℕ) (x : ℝ) :
    x ∈ dyadicInterval L n (containingIndex L n x) := by
  have hd := dyadicLength_pos hL n
  simp only [dyadicInterval, mem_Ico, containingIndex]
  constructor
  · exact (le_div_iff₀ hd).mp (Int.floor_le (x / dyadicLength L n))
  · exact (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (x / dyadicLength L n))

/-- The midpoint of the depth-`n` dyadic interval containing `x`. -/
def containingCenter (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((containingIndex L n x : ℝ) + 1 / 2) * dyadicLength L n

/-- Half the length of a depth-`n` dyadic interval at root scale `L`. -/
def containingRadius (L : ℝ) (n : ℕ) : ℝ :=
  dyadicLength L n / 2

theorem closedBall_containing_eq_Icc (L : ℝ) (n : ℕ) (x : ℝ) :
    Metric.closedBall (containingCenter L n x) (containingRadius L n) =
      Icc ((containingIndex L n x : ℝ) * dyadicLength L n)
        (((containingIndex L n x : ℝ) + 1) * dyadicLength L n) := by
  rw [Real.closedBall_eq_Icc]
  simp only [containingCenter, containingRadius]
  congr 1 <;> ring

theorem setAverage_dyadicInterval_eq_closedBall (g : ℝ → ℝ)
    (L : ℝ) (n : ℕ) (x : ℝ) :
    (⨍ y in dyadicInterval L n (containingIndex L n x), g y) =
      ⨍ y in Metric.closedBall (containingCenter L n x) (containingRadius L n), g y := by
  rw [closedBall_containing_eq_Icc, dyadicInterval, setAverage_eq, setAverage_eq]
  simp only [Measure.real, Real.volume_Icc, Real.volume_Ico]
  rw [integral_Icc_eq_integral_Ico]

theorem tendsto_containingRadius_nhdsGT_zero {L : ℝ} (hL : 0 < L) :
    Tendsto (containingRadius L) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hp : Tendsto (fun n : ℕ ↦ (((2 : ℝ)⁻¹) ^ n)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul := hp.const_mul (L / 2)
    convert hmul using 1
    · funext n
      simp only [containingRadius, dyadicLength, div_eq_mul_inv]
      norm_num
      rw [← inv_pow]
      norm_num
      ring
    · ring
  · exact Filter.Eventually.of_forall fun n ↦
      half_pos (dyadicLength_pos hL n)

theorem mem_closedBall_containing {L : ℝ} (hL : 0 < L) (n : ℕ) (x : ℝ) :
    x ∈ Metric.closedBall (containingCenter L n x) (containingRadius L n) := by
  rw [closedBall_containing_eq_Icc]
  exact ⟨(mem_dyadicInterval_containingIndex hL n x).1,
    (mem_dyadicInterval_containingIndex hL n x).2.le⟩

/-- Lebesgue differentiation along the unique half-open dyadic cells
containing a point. -/
theorem ae_tendsto_dyadicNormAverage {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun n ↦ dyadicNormAverage f (rootLength f) n
          (containingIndex (rootLength f) n x))
        atTop (𝓝 ‖f x‖) := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure ℝ) hf.norm.locallyIntegrable 1
  filter_upwards [hdiff] with x hx
  have hball := hx
    (containingCenter (rootLength f) · x)
    (containingRadius (rootLength f))
    (tendsto_containingRadius_nhdsGT_zero rootLength_pos)
    (Filter.Eventually.of_forall fun n ↦ by
      simpa using mem_closedBall_containing rootLength_pos n x)
  rw [show (fun n ↦
      ⨍ y in Metric.closedBall
        (containingCenter (rootLength f) n x)
        (containingRadius (rootLength f) n), ‖f y‖) =
      (fun n ↦ dyadicNormAverage f (rootLength f) n
        (containingIndex (rootLength f) n x)) by
    funext n
    exact (setAverage_dyadicInterval_eq_closedBall
      (fun y ↦ ‖f y‖) (rootLength f) n x).symm] at hball
  exact hball

/-- Almost every point whose value is above height one belongs to a bad
dyadic cell at some finite depth. -/
theorem ae_exists_badCell_of_high {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → ∃ n, HasBadCellAtDepth f x n := by
  filter_upwards [ae_tendsto_dyadicNormAverage hf] with x hxlim
  intro hxhigh
  have hev : ∀ᶠ n in atTop,
      1 < dyadicNormAverage f (rootLength f) n
        (containingIndex (rootLength f) n x) :=
    (tendsto_order.1 hxlim).1 1 hxhigh
  rcases hev.exists with ⟨n, hn⟩
  exact ⟨n, containingIndex (rootLength f) n x,
    mem_dyadicInterval_containingIndex rootLength_pos n x, hn⟩

/-- The intrinsic stopping intervals cover the height-one superlevel set
almost everywhere. -/
theorem ae_highPoint_mem_stoppingBadUnion {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → x ∈ stoppingBadUnion f := by
  filter_upwards [ae_exists_badCell_of_high hf] with x hx
  exact fun hhigh ↦ mem_stoppingBadUnion_of_exists_badCell (hx hhigh)

/-! ## The full good part -/

/-- The complex average of `f` over a canonical stopping interval. -/
def stoppingCellAverage (f : ℝ → ℂ) (c : stoppingCell f) : ℂ :=
  ⨍ y in c.1.interval (rootLength f), f y

theorem norm_stoppingCellAverage_le_normAverage {f : ℝ → ℂ}
    (c : stoppingCell f) :
    ‖stoppingCellAverage f c‖ ≤ c.1.normAverage f (rootLength f) := by
  have hmpos : 0 < volume.real (c.1.interval (rootLength f)) := by
    rw [Measure.real, volume_stoppingCell_interval,
      ENNReal.toReal_ofReal (dyadicLength_pos rootLength_pos c.1.depth).le]
    exact dyadicLength_pos rootLength_pos c.1.depth
  rw [stoppingCellAverage, DyadicCell.normAverage, dyadicNormAverage,
    setAverage_eq, setAverage_eq]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos,
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.2 hmpos.le)

theorem norm_stoppingCellAverage_le_two {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) : ‖stoppingCellAverage f c‖ ≤ 2 :=
  (norm_stoppingCellAverage_le_normAverage c).trans
    (stoppingCell_upper_average hf c)

/-- The usual Calderón--Zygmund good part: `f` off the stopping union and
the interval average on each stopping cell. The pointwise sum has at most
one nonzero term because the cells are pairwise disjoint. -/
def stoppingGoodPart (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (stoppingBadUnion f)ᶜ.indicator f x +
    ∑' c : stoppingCell f,
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x

private theorem tsum_stoppingPiece_eq_of_mem {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) :
    (∑' d : stoppingCell f,
      (d.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f d) x) = stoppingCellAverage f c := by
  classical
  rw [tsum_eq_single c]
  · simp [hx]
  · intro d hdc
    have hdis := stoppingCell_pairwiseDisjoint (f := f) hdc.symm
    have hxnot : x ∉ d.1.interval (rootLength f) :=
      fun hxd ↦ Set.disjoint_left.1 hdis hx hxd
    simp [hxnot]

private theorem tsum_stoppingPiece_eq_zero_of_notMem {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) :
    (∑' c : stoppingCell f,
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x) = 0 := by
  have hzero : (fun c : stoppingCell f ↦
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x) = 0 := by
    funext c
    have hxc : x ∉ c.1.interval (rootLength f) := fun hmem ↦
      hx (mem_iUnion.2 ⟨c, hmem⟩)
    simp [hxc]
  rw [hzero]
  exact tsum_zero

theorem stoppingGoodPart_eq_average_of_mem {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) :
    stoppingGoodPart f x = stoppingCellAverage f c := by
  have hxu : x ∈ stoppingBadUnion f := mem_iUnion.2 ⟨c, hx⟩
  have hxcomp : x ∉ (stoppingBadUnion f)ᶜ := by simpa
  rw [stoppingGoodPart, indicator_of_notMem hxcomp,
    tsum_stoppingPiece_eq_of_mem c hx, zero_add]

theorem stoppingGoodPart_eq_of_notMem {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) : stoppingGoodPart f x = f x := by
  rw [stoppingGoodPart, indicator_of_mem (mem_compl hx),
    tsum_stoppingPiece_eq_zero_of_notMem hx, add_zero]

/-- The full good part, including the averages on stopping intervals, has
the sharp height-two essential bound. -/
theorem ae_norm_stoppingGoodPart_le_two {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, ‖stoppingGoodPart f x‖ ≤ 2 := by
  filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
  by_cases hxu : x ∈ stoppingBadUnion f
  · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
    rw [stoppingGoodPart_eq_average_of_mem c hxc]
    exact norm_stoppingCellAverage_le_two hf c
  · rw [stoppingGoodPart_eq_of_notMem hxu]
    exact (le_of_not_gt (fun hhigh ↦ hxu (hxcover hhigh))).trans one_le_two

theorem volume_stoppingBadUnion_eq_tsum (f : ℝ → ℂ) :
    volume (stoppingBadUnion f) =
      ∑' c : stoppingCell f, volume (c.1.interval (rootLength f)) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  rw [stoppingBadUnion,
    measure_iUnion stoppingCell_pairwiseDisjoint measurableSet_stoppingCell_interval]

theorem volume_stoppingBadUnion_lt_top {f : ℝ → ℂ} (hf : Integrable f) :
    volume (stoppingBadUnion f) < ∞ := by
  rw [volume_stoppingBadUnion_eq_tsum]
  refine (tsum_volume_stoppingCell_le_lintegral_norm hf).trans_lt ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))]
  exact ENNReal.ofReal_lt_top

theorem volumeReal_stoppingBadUnion_le_integral_norm {f : ℝ → ℂ}
    (hf : Integrable f) :
    volume.real (stoppingBadUnion f) ≤ ∫ x, ‖f x‖ := by
  have hvol := tsum_volume_stoppingCell_le_lintegral_norm hf
  rw [← volume_stoppingBadUnion_eq_tsum] at hvol
  have hreal := ENNReal.toReal_mono
    (by
      rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))]
      exact ENNReal.ofReal_ne_top) hvol
  rw [Measure.real]
  simp only [ofReal_norm] at hreal
  exact hreal.trans_eq (integral_norm_eq_lintegral_enorm hf.1).symm

theorem aestronglyMeasurable_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    AEStronglyMeasurable (stoppingGoodPart f) volume := by
  let _ := Encodable.ofCountable (stoppingCell f)
  apply (hf.1.indicator (measurableSet_stoppingBadUnion f).compl).add
  apply AEStronglyMeasurable.tsum
  intro c
  exact (measurable_const.indicator
    (measurableSet_stoppingCell_interval (f := f) c)).aestronglyMeasurable

theorem integrable_sq_norm_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) := by
  let majorant : ℝ → ℝ := fun x ↦ ‖f x‖ +
    (stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ)) x
  have hconst : Integrable
      ((stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ))) :=
    (integrableOn_const (volume_stoppingBadUnion_lt_top hf).ne).integrable_indicator
      (measurableSet_stoppingBadUnion f)
  have hmajorant : Integrable majorant := hf.norm.add hconst
  apply Integrable.mono' hmajorant
  · exact AEMeasurable.aestronglyMeasurable
      ((aestronglyMeasurable_stoppingGoodPart hf).norm.aemeasurable.pow_const 2)
  · filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hxu : x ∈ stoppingBadUnion f
    · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
      rw [stoppingGoodPart_eq_average_of_mem c hxc]
      simp only [majorant, indicator_of_mem hxu]
      nlinarith [norm_nonneg (f x), norm_nonneg (stoppingCellAverage f c),
        norm_stoppingCellAverage_le_two hf c]
    · rw [stoppingGoodPart_eq_of_notMem hxu]
      simp only [majorant, indicator_of_notMem hxu, add_zero]
      have hnorm : ‖f x‖ ≤ 1 := le_of_not_gt fun hhigh ↦ hxu (hxcover hhigh)
      nlinarith [norm_nonneg (f x)]

/-- A global squared-`L²` estimate for the complete good part. The constant
five comes from the direct domination `‖g‖² ≤ ‖f‖ + 4⋅1_Ω`; it uses only
integrability of `f` and the stopping-family length bound. -/
theorem integral_sq_norm_stoppingGoodPart_le_five_l1 {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∫ x, ‖stoppingGoodPart f x‖ ^ 2) ≤ 5 * ∫ x, ‖f x‖ := by
  let majorant : ℝ → ℝ := fun x ↦ ‖f x‖ +
    (stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ)) x
  have hconst : Integrable
      ((stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ))) :=
    (integrableOn_const (volume_stoppingBadUnion_lt_top hf).ne).integrable_indicator
      (measurableSet_stoppingBadUnion f)
  have hmajorant : Integrable majorant := hf.norm.add hconst
  have hpoint : ∀ᵐ x ∂volume, ‖stoppingGoodPart f x‖ ^ 2 ≤ majorant x := by
    filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
    by_cases hxu : x ∈ stoppingBadUnion f
    · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
      rw [stoppingGoodPart_eq_average_of_mem c hxc]
      simp only [majorant, indicator_of_mem hxu]
      nlinarith [norm_nonneg (f x), norm_nonneg (stoppingCellAverage f c),
        norm_stoppingCellAverage_le_two hf c]
    · rw [stoppingGoodPart_eq_of_notMem hxu]
      simp only [majorant, indicator_of_notMem hxu, add_zero]
      have hnorm : ‖f x‖ ≤ 1 := le_of_not_gt fun hhigh ↦ hxu (hxcover hhigh)
      nlinarith [norm_nonneg (f x)]
  have hsqMeas : AEStronglyMeasurable
      (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) volume :=
    ((aestronglyMeasurable_stoppingGoodPart hf).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hsq : Integrable (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) := by
    apply Integrable.mono' hmajorant hsqMeas
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  calc
    (∫ x, ‖stoppingGoodPart f x‖ ^ 2) ≤ ∫ x, majorant x :=
      integral_mono_ae hsq hmajorant hpoint
    _ = (∫ x, ‖f x‖) + 4 * volume.real (stoppingBadUnion f) := by
      rw [integral_add hf.norm hconst, integral_indicator
        (measurableSet_stoppingBadUnion f), setIntegral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ 5 * ∫ x, ‖f x‖ := by
      have hmass : 0 ≤ ∫ x, ‖f x‖ :=
        integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
      nlinarith [volumeReal_stoppingBadUnion_le_integral_norm hf]


end
end CalderonZygmundDyadicStopping
end QuadraticCarleson
