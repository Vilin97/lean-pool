/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.Preliminaries
public import Mathlib.Analysis.Normed.Lp.ProdLp


/-!
# The attachment map for the protected extension

This module formalizes the metric input to the adjunction construction.  The
attachment set in `M ⊕₁ ℝ` is parametrized by `M ⊕ Unit`: the left summand is
the base hyperplane and the right summand is the single elevated point.
-/

@[expose] public section

namespace ScottishBook155

open ENNReal WithLp

universe u v

/-- The sum-norm product `M ⊕₁ ℝ`. -/
abbrev OneSum (M : Type u) := WithLp 1 (M × ℝ)

/-- Parametrization of the base hyperplane together with one elevated point. -/
noncomputable def attachmentPoint
    {M : Type u} (a : M) (H : ℝ) : M ⊕ Unit → OneSum M
  | Sum.inl m => toLp 1 (m, 0)
  | Sum.inr _ => toLp 1 (a, H)

/-- The attachment subset of the sum-norm product. -/
noncomputable def attachmentSet
    {M : Type u} (a : M) (H : ℝ) : Set (OneSum M) :=
  Set.range (attachmentPoint a H)

/-- The map prescribed on the attachment set before taking the metric
adjunction. -/
def attachmentMap {M : Type u} {N : Type v}
    (V : M → N) (y : N) : M ⊕ Unit → N
  | Sum.inl m => V m
  | Sum.inr _ => y

theorem dist_attachmentPoint_base_base
    {M : Type u} [NormedAddCommGroup M] (a m n : M) (H : ℝ) :
    dist (attachmentPoint a H (Sum.inl m)) (attachmentPoint a H (Sum.inl n)) =
      dist m n := by
  simp [attachmentPoint,
    WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]

theorem dist_attachmentPoint_base_top
    {M : Type u} [NormedAddCommGroup M] (a m : M) {H : ℝ} (hH : 0 ≤ H) :
    dist (attachmentPoint a H (Sum.inl m)) (attachmentPoint a H (Sum.inr ())) =
      dist m a + H := by
  simp [attachmentPoint,
    WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
    Real.dist_eq, abs_of_nonneg hH]

theorem attachmentSet_eq
    {M : Type u} (a : M) (H : ℝ) :
    attachmentSet a H =
      {x : OneSum M | x.snd = 0} ∪ {toLp 1 (a, H)} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    cases p with
    | inl m => exact Or.inl (by simp [attachmentPoint])
    | inr u => exact Or.inr (by simp [attachmentPoint])
  · rintro (hx | hx)
    · refine ⟨Sum.inl x.fst, ?_⟩
      rw [attachmentPoint, ← toLp_ofLp 1 x]
      congr 1
      exact Prod.ext rfl hx.symm
    · have hx' : x = toLp 1 (a, H) := by simpa using hx
      exact ⟨Sum.inr (), hx'.symm.trans (by simp)⟩

/-- The attachment set is closed in `M ⊕₁ ℝ`. -/
theorem isClosed_attachmentSet
    {M : Type u} [NormedAddCommGroup M] (a : M) (H : ℝ) :
    IsClosed (attachmentSet a H) := by
  rw [attachmentSet_eq]
  apply IsClosed.union
  · exact isClosed_eq (WithLp.continuous_snd 1 M ℝ) continuous_const
  · exact isClosed_singleton

theorem attachmentPoint_mem_attachmentSet
    {M : Type u} (a : M) (H : ℝ) (p : M ⊕ Unit) :
    attachmentPoint a H p ∈ attachmentSet a H :=
  ⟨p, rfl⟩

theorem dist_to_attachmentBase
    {M : Type u} [NormedAddCommGroup M] (a m : M) (H s : ℝ) :
    dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inl m)) = |s| := by
  simp [attachmentPoint,
    WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]

/-- The vertical route to the base hyperplane gives the elementary upper
bound on distance to the attachment set used in the collar argument. -/
theorem infDist_attachmentSet_le_abs
    {M : Type u} [NormedAddCommGroup M] (a m : M) (H s : ℝ) :
    Metric.infDist (toLp 1 (m, s) : OneSum M) (attachmentSet a H) ≤ |s| := by
  calc
    Metric.infDist (toLp 1 (m, s) : OneSum M) (attachmentSet a H) ≤
        dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inl m)) :=
      Metric.infDist_le_dist_of_mem (attachmentPoint_mem_attachmentSet a H (Sum.inl m))
    _ = |s| := dist_to_attachmentBase a m H s

/-- Exact distance from a point to the union of the base hyperplane and the
single elevated attachment point. -/
theorem infDist_attachmentSet_eq_min
    {M : Type u} [NormedAddCommGroup M] (a m : M) (H s : ℝ) :
    Metric.infDist (toLp 1 (m, s) : OneSum M) (attachmentSet a H) =
      min |s| (dist m a + |s - H|) := by
  have hne : (attachmentSet a H).Nonempty :=
    ⟨attachmentPoint a H (Sum.inr ()), attachmentPoint_mem_attachmentSet a H _⟩
  apply le_antisymm
  · apply le_min
    · exact infDist_attachmentSet_le_abs a m H s
    · calc
        Metric.infDist (toLp 1 (m, s) : OneSum M) (attachmentSet a H) ≤
            dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inr ())) :=
          Metric.infDist_le_dist_of_mem (attachmentPoint_mem_attachmentSet a H _)
        _ = dist m a + |s - H| := by
          simp [attachmentPoint,
            WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
            Real.dist_eq]
  · rw [Metric.le_infDist hne]
    intro z hz
    rcases hz with ⟨p, rfl⟩
    cases p with
    | inl v =>
        calc
          min |s| (dist m a + |s - H|) ≤ |s| := min_le_left _ _
          _ ≤ dist (toLp 1 (m, s) : OneSum M)
              (attachmentPoint a H (Sum.inl v)) := by
            simp [attachmentPoint,
              WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    | inr star =>
        calc
          min |s| (dist m a + |s - H|) ≤ dist m a + |s - H| := min_le_right _ _
          _ = dist (toLp 1 (m, s) : OneSum M)
              (attachmentPoint a H (Sum.inr star)) := by
            simp [attachmentPoint,
              WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
              Real.dist_eq]

/-- In the complementary two-point case, a height above `2r` forces both
nearest attachment routes to use the base hyperplane. -/
theorem abs_add_abs_lt_dist_of_infDist_add_lt
    {M : Type u} [NormedAddCommGroup M] (a m₀ m₁ : M) {H r s₀ s₁ : ℝ} (hr : 0 < r) (hH : 2 * r < H)
    (hd : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) ≤ r)
    (hfar : Metric.infDist (toLp 1 (m₀, s₀) : OneSum M) (attachmentSet a H) +
      Metric.infDist (toLp 1 (m₁, s₁) : OneSum M) (attachmentSet a H) <
        dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁))) :
    |s₀| + |s₁| <
      dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) := by
  have hdist : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) =
      dist m₀ m₁ + |s₀ - s₁| := by
    simp [WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
      Real.dist_eq]
  rw [infDist_attachmentSet_eq_min, infDist_attachmentSet_eq_min] at hfar
  have hHpos : 0 < H := by linarith
  rcases le_total |s₀| (dist m₀ a + |s₀ - H|) with h₀ | h₀ <;>
    rcases le_total |s₁| (dist m₁ a + |s₁ - H|) with h₁ | h₁
  · simpa [min_eq_left h₀, min_eq_left h₁] using hfar
  · rw [min_eq_left h₀, min_eq_right h₁] at hfar
    have habs₁ := abs_add_le (H - s₁) s₁
    rw [show H - s₁ + s₁ = H by ring, abs_of_pos hHpos] at habs₁
    have hs₁_le : |s₁| ≤ |s₀| + |s₀ - s₁| := by
      have := abs_add_le s₀ (s₁ - s₀)
      rw [show s₀ + (s₁ - s₀) = s₁ by ring, abs_sub_comm s₁ s₀] at this
      exact this
    rw [hdist] at hd hfar ⊢
    have hdist₁ : 0 ≤ dist m₁ a := dist_nonneg
    have hdist₀ : 0 ≤ dist m₀ m₁ := dist_nonneg
    have habs_symm : |H - s₁| = |s₁ - H| := abs_sub_comm H s₁
    rw [habs_symm] at habs₁
    exfalso
    linarith
  · rw [min_eq_right h₀, min_eq_left h₁] at hfar
    have habs₀ := abs_add_le (H - s₀) s₀
    rw [show H - s₀ + s₀ = H by ring, abs_of_pos hHpos] at habs₀
    have hs₀_le : |s₀| ≤ |s₁| + |s₀ - s₁| := by
      have := abs_add_le s₁ (s₀ - s₁)
      rw [show s₁ + (s₀ - s₁) = s₀ by ring] at this
      exact this
    rw [hdist] at hd hfar ⊢
    have hdist₀ : 0 ≤ dist m₀ a := dist_nonneg
    have hdist₁ : 0 ≤ dist m₀ m₁ := dist_nonneg
    have habs_symm : |H - s₀| = |s₀ - H| := abs_sub_comm H s₀
    rw [habs_symm] at habs₀
    exfalso
    linarith
  · rw [min_eq_right h₀, min_eq_right h₁] at hfar
    have htri := dist_triangle (toLp 1 (m₀, s₀) : OneSum M)
      (attachmentPoint a H (Sum.inr ())) (toLp 1 (m₁, s₁) : OneSum M)
    have htop₀ : dist (toLp 1 (m₀, s₀) : OneSum M)
        (attachmentPoint a H (Sum.inr ())) = dist m₀ a + |s₀ - H| := by
      simp [attachmentPoint,
        WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
        Real.dist_eq]
    have htop₁ : dist (attachmentPoint a H (Sum.inr ()) )
        (toLp 1 (m₁, s₁) : OneSum M) = dist m₁ a + |s₁ - H| := by
      rw [dist_comm]
      simp [attachmentPoint,
        WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
        Real.dist_eq]
    rw [htop₀, htop₁] at htri
    linarith

theorem abs_lt_of_infDist_add_lt
    {M : Type u} [NormedAddCommGroup M] (a m₀ m₁ : M) {H r s₀ s₁ : ℝ} (hr : 0 < r) (hH : 2 * r < H)
    (hd : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) ≤ r)
    (hfar : Metric.infDist (toLp 1 (m₀, s₀) : OneSum M) (attachmentSet a H) +
      Metric.infDist (toLp 1 (m₁, s₁) : OneSum M) (attachmentSet a H) <
        dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁))) :
    |s₀| < r ∧ |s₁| < r := by
  have hsum := abs_add_abs_lt_dist_of_infDist_add_lt a m₀ m₁ hr hH hd hfar
  constructor <;> linarith [abs_nonneg s₀, abs_nonneg s₁]

theorem attachmentPoint_injective
    {M : Type u} (a : M) {H : ℝ} (hH : H ≠ 0) :
    Function.Injective (attachmentPoint a H) := by
  intro p q hpq
  cases p with
  | inl m =>
      cases q with
      | inl n =>
          have hpair : (m, (0 : ℝ)) = (n, 0) := toLp_injective 1 hpq
          exact congrArg Sum.inl (congrArg Prod.fst hpair)
      | inr u =>
          exfalso
          have := congrArg WithLp.snd hpq
          simp only [attachmentPoint, toLp_snd] at this
          exact hH this.symm
  | inr u =>
      cases q with
      | inl n =>
          exfalso
          have := congrArg WithLp.snd hpq
          simp only [attachmentPoint, toLp_snd] at this
          exact hH this
      | inr v => simp

theorem attachmentMap_injective
    {M : Type u} {N : Type v} {V : M → N} {y : N}
    (hV : Function.Injective V) (hy : y ∉ Set.range V) :
    Function.Injective (attachmentMap V y) := by
  intro p q hpq
  cases p with
  | inl m =>
      cases q with
      | inl n => exact congrArg Sum.inl (hV hpq)
      | inr u =>
          change V m = y at hpq
          exact False.elim (hy ⟨m, hpq⟩)
  | inr u =>
      cases q with
      | inl n =>
          change y = V n at hpq
          exact False.elim (hy ⟨n, hpq.symm⟩)
      | inr v => simp

/-- The prescribed attachment map is nonexpansive with respect to the ambient
sum-norm distance on its parametrized attachment set. -/
theorem attachmentMap_dist_le
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    {V : M → N} (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (a : M) (y : N) {H : ℝ} (hgap : dist (V a) y < H) (p q : M ⊕ Unit) :
    dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q) := by
  have hH : 0 ≤ H := (dist_nonneg.trans_lt hgap).le
  cases p with
  | inl m =>
      cases q with
      | inl n => simpa [attachmentMap, dist_attachmentPoint_base_base] using hV m n
      | inr u =>
          rw [dist_attachmentPoint_base_top a m hH]
          calc
            dist (attachmentMap V y (Sum.inl m)) (attachmentMap V y (Sum.inr u)) =
                dist (V m) y := rfl
            _ ≤ dist (V m) (V a) + dist (V a) y := dist_triangle _ _ _
            _ ≤ dist m a + dist (V a) y := add_le_add (hV m a) le_rfl
            _ ≤ dist m a + H := add_le_add le_rfl hgap.le
  | inr u =>
      cases q with
      | inl n =>
          rw [dist_comm (attachmentMap V y (Sum.inr u)),
            dist_comm (attachmentPoint a H (Sum.inr u)),
            dist_attachmentPoint_base_top a n hH]
          calc
            dist (attachmentMap V y (Sum.inl n)) (attachmentMap V y (Sum.inr u)) =
                dist (V n) y := rfl
            _ ≤ dist (V n) (V a) + dist (V a) y := dist_triangle _ _ _
            _ ≤ dist n a + dist (V a) y := add_le_add (hV n a) le_rfl
            _ ≤ dist n a + H := add_le_add le_rfl hgap.le
      | inr v => simp

end ScottishBook155
