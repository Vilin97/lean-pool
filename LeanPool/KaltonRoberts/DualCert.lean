/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Dual certificate existence (Lemma 2.1)

This file proves the existence of a dual certificate for the best ℓ∞
approximation from the additive subspace, using the geometric Hahn–Banach
separation theorem.

**Reference**: Lemma 2.1 in Section 2 of the companion paper.
-/
import LeanPool.KaltonRoberts.Defs

/-!
# Dual certificate existence

Existence of a dual certificate for best `l∞` approximation from the additive
subspace, using geometric Hahn-Banach separation.
-/

namespace KaltonRoberts

open Finset BigOperators

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Indicator function and basic properties -/

/-- Indicator function of a finset as a vector in `U → ℝ`. -/
def _root_.Finset.indicator' (S : Finset U) : U → ℝ :=
  fun i => if i ∈ S then 1 else 0

omit [Fintype U] in
@[simp]
lemma _root_.Finset.indicator'_apply (S : Finset U) (i : U) :
    S.indicator' i = if i ∈ S then (1 : ℝ) else 0 := rfl

/-- A continuous linear map on `U → ℝ` decomposes via basis vectors. -/
lemma clm_decompose (Λ : (U → ℝ) →L[ℝ] ℝ) (h : U → ℝ) :
    Λ h = ∑ i : U, h i * Λ (Function.update (0 : U → ℝ) i 1) := by
  have key : ∀ i : U, Λ (Function.update (0 : U → ℝ) i (h i)) =
      h i * Λ (Function.update (0 : U → ℝ) i 1) := by
    intro i
    have : Function.update (0 : U → ℝ) i (h i) =
        h i • Function.update (0 : U → ℝ) i 1 := by
      ext j; simp [Function.update, Pi.smul_apply]
    rw [this, map_smul, smul_eq_mul]
  suffices h_eq : h = ∑ i : U, Function.update (0 : U → ℝ) i (h i) by
    calc Λ h = Λ (∑ i, Function.update (0 : U → ℝ) i (h i)) := by congr 1
      _ = ∑ i, Λ (Function.update (0 : U → ℝ) i (h i)) := map_sum Λ _ _
      _ = ∑ i, h i * Λ (Function.update (0 : U → ℝ) i 1) :=
        Finset.sum_congr rfl (fun i _ => key i)
  ext j; simp [Finset.sum_apply, Function.update]

omit [Fintype U] in
/-- Applying a CLinearMap to an indicator equals `additiveFunction`. -/
lemma clm_indicator'_eq_additiveFunction (Λ : (U → ℝ) →L[ℝ] ℝ) (S : Finset U) :
    Λ S.indicator' = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
  have : S.indicator' = ∑ i ∈ S, Function.update (0 : U → ℝ) i 1 := by
    ext j; simp [Finset.indicator', Finset.sum_apply, Function.update]
  rw [this, map_sum]; rfl

/-! ## M = 0 case -/

/-
When `M = 0`, every `f(S) = 0`, so `λ(∅) = 1` gives a valid certificate.
-/
lemma dual_cert_zero_case
    (f : Finset U → ℝ) (_hf : IsApproxAdditive f 1)
    (hMbound : ∀ S : Finset U, |f S| ≤ distToAdditive f)
    (hM0 : distToAdditive f = 0) :
    Nonempty (DualCertificate f (distToAdditive f)) := by
  have hzero : ∀ S : Finset U, f S = 0 := by
    simp_all
  refine ⟨⟨fun S => if S = ∅ then 1 else 0, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.sum_eq_single ∅] <;> simp
  · simp_all
  · simp_all
  · simp_all

/-! ## M > 0 case: the Hahn–Banach argument -/

/-- The set of "signed indicator generators" at active sets. -/
noncomputable def activeGenerators (f : Finset U → ℝ) (M : ℝ) : Set (U → ℝ) :=
  (fun S => S.indicator') '' {S : Finset U | f S = M} ∪
  (fun S => -S.indicator') '' {S : Finset U | f S = -M}

omit [Fintype U] in
lemma activeGenerators_finite [Finite U] (f : Finset U → ℝ) (M : ℝ) :
    (activeGenerators f M).Finite := by
  letI := Fintype.ofFinite U
  apply Set.Finite.union
  · exact Set.Finite.image _ (Set.Finite.ofFinset (Finset.univ.filter (f · = M))
      (by simp))
  · exact Set.Finite.image _ (Set.Finite.ofFinset (Finset.univ.filter (f · = -M))
      (by simp))

/-
Key separation lemma: 0 is in the convex hull of the active generators
when the best-approximation hypothesis holds with M > 0.

**Proof**: By contradiction using `geometric_hahn_banach_closed_point`.
If 0 ∉ conv(G), there exists Λ with Λ(c) < u < 0 for all c ∈ conv(G). Define
a(i) = -Λ(Function.update 0 i 1). Then for positive active S,
additiveFunction a S > 0, and for negative active S, additiveFunction a S < 0.
A small ε-perturbation gives ∀ S, |f(S) - εa(S)| < M, contradicting `hbest`.
-/
omit [Fintype U] in
lemma zero_mem_convexHull_of_best_approx [Finite U]
    (f : Finset U → ℝ) (M : ℝ) (hM_pos : 0 < M)
    (hMbound : ∀ S : Finset U, |f S| ≤ M)
    (hbest : ∀ a : U → ℝ, ∃ S : Finset U, |f S - additiveFunction a S| ≥ M) :
    (0 : U → ℝ) ∈ convexHull ℝ (activeGenerators f M) := by
  letI := Fintype.ofFinite U
  by_contra h_contra;
  obtain ⟨Λ, u, hΛ, hu⟩ : ∃ Λ : (U → ℝ) →L[ℝ] ℝ, ∃ u : ℝ, (∀ c ∈ convexHull ℝ (activeGenerators f
    M), Λ c < u) ∧ u < Λ 0 := by
    have h_closed_convex : IsClosed (convexHull ℝ (activeGenerators f M)) ∧ Convex ℝ (convexHull ℝ
      (activeGenerators f M)) := by
      exact ⟨ Set.Finite.isClosed_convexHull ℝ ( activeGenerators_finite f M ), convex_convexHull ℝ
        _ ⟩;
    have := @geometric_hahn_banach_closed_point;
    convert this h_closed_convex.2 h_closed_convex.1 h_contra;
  -- For every generator g ∈ activeGenerators f M, g is in the convex hull (subset_convexHull), so Λ
  -- g < u < 0.
  have hΛ_gen : ∀ S : Finset U, f S = M → Λ (S.indicator') < 0 := by
    intro S hS
    have hS_gen : S.indicator' ∈ activeGenerators f M := by
      exact Set.mem_union_left _ ( Set.mem_image_of_mem _ hS );
    exact lt_of_lt_of_le ( hΛ _ ( subset_convexHull ℝ _ hS_gen ) ) ( by simpa using hu.le )
  have hΛ_gen_neg : ∀ S : Finset U, f S = -M → Λ (-S.indicator') < 0 := by
    intro S hS_neg
    have hΛ_gen_neg : Λ (-S.indicator') < u := by
      exact hΛ _ ( subset_convexHull ℝ _ <| Set.mem_union_right _ <| Set.mem_image_of_mem _ hS_neg
        );
    linarith [ show Λ 0 = 0 by simp ];
  -- Define a : U → ℝ by a i = -(Λ (Function.update 0 i 1)).
  set a : U → ℝ := fun i => -(Λ (Function.update 0 i 1)) with ha_def;
  have h_additiveFunction_a_pos : ∀ S : Finset U, f S = M → additiveFunction a S > 0 := by
    intro S hS
    have hΛ_S : Λ (S.indicator') = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
      convert clm_indicator'_eq_additiveFunction Λ S using 1;
    simp_all +decide [ additiveFunction ];
    linarith [ hΛ_gen S hS ];
  have h_additiveFunction_a_neg : ∀ S : Finset U, f S = -M → additiveFunction a S < 0 := by
    intro S hS
    have hΛ_neg : Λ (-S.indicator') < 0 := hΛ_gen_neg S hS
    have h_additiveFunction_a_neg : additiveFunction a S = -Λ (S.indicator') := by
      rw [ clm_indicator'_eq_additiveFunction Λ S ]; ring_nf!;
      unfold additiveFunction; simp +decide [ Finset.sum_neg_distrib ];
    simp_all
  -- For ε > 0 sufficiently small, ∀ S : Finset U, |f S - additiveFunction (fun i => ε * a i) S| <
  -- M.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ S : Finset U, |f S - additiveFunction (fun i => ε * a i) S| <
    M := by
    -- For inactive S, |f S| < M, so |f S - ε · additiveFunction a S| < M for ε small by continuity.
    have h_inactive : ∀ S : Finset U, |f S| < M → ∃ ε > 0, ∀ ε' ∈ Set.Ioo 0 ε, |f S -
      additiveFunction (fun i => ε' * a i) S| < M := by
      intro S hS
      have h_cont : Filter.Tendsto (fun ε' => |f S - additiveFunction (fun i => ε' * a i) S|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (|f S|)) := by
        simp +decide only [additiveFunction]
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by
          simp +decide ) );
      have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( M - |f S| ) ( sub_pos.mpr hS );
      exact
        ⟨this.choose, this.choose_spec.1, fun ε' hε' => by
          linarith [
            abs_lt.mp
              (this.choose_spec.2 hε'.1 (by
                simpa [abs_of_pos hε'.1] using hε'.2))]⟩
    -- For active S, |f S| = M, so |f S - ε · additiveFunction a S| < M for ε small by continuity.
    have h_active : ∀ S : Finset U, |f S| = M → ∃ ε > 0, ∀ ε' ∈ Set.Ioo 0 ε, |f S - additiveFunction
      (fun i => ε' * a i) S| < M := by
      intro S hS
      by_cases hS_pos : f S = M;
      · simp_all +decide only [additiveFunction]
        simp_all +decide only [
          ge_iff_le,
          map_zero,
          map_neg,
          Left.neg_neg_iff,
          sum_neg_distrib,
          gt_iff_lt,
          Left.neg_pos_iff,
          Set.mem_Ioo,
          mul_neg,
          ← Finset.mul_sum _ _ _,
          sub_neg_eq_add,
          and_imp,
          abs_eq_self]
        exact
          ⟨M / (-∑ i ∈ S, Λ (Function.update 0 i 1)),
            div_pos hM_pos (neg_pos.mpr (h_additiveFunction_a_pos S hS_pos)),
            fun ε' hε'₁ hε'₂ =>
              abs_lt.mpr
                ⟨by
                  nlinarith [
                    mul_div_cancel₀ M
                      (ne_of_gt (neg_pos.mpr (h_additiveFunction_a_pos S hS_pos))),
                    h_additiveFunction_a_pos S hS_pos],
                  by
                  nlinarith [
                    mul_div_cancel₀ M
                      (ne_of_gt (neg_pos.mpr (h_additiveFunction_a_pos S hS_pos))),
                    h_additiveFunction_a_pos S hS_pos]⟩⟩
      · have hS_neg : f S = -M := by
          exact Or.resolve_left ( eq_or_eq_neg_of_abs_eq hS ) hS_pos;
        simp_all +decide only [additiveFunction]
        simp_all +decide only [
          ge_iff_le,
          map_zero,
          map_neg,
          Left.neg_neg_iff,
          sum_neg_distrib,
          gt_iff_lt,
          Left.neg_pos_iff,
          Set.mem_Ioo,
          mul_neg,
          ← Finset.mul_sum _ _ _,
          sub_neg_eq_add,
          and_imp,
          abs_neg,
          abs_eq_self]
        exact
          ⟨M / (∑ i ∈ S, Λ (Function.update 0 i 1)),
            div_pos hM_pos (h_additiveFunction_a_neg S hS_neg),
            fun ε' hε'₁ hε'₂ =>
              abs_lt.mpr
                ⟨by
                  simp_all,
                  by
                  nlinarith [
                    mul_div_cancel₀ M (ne_of_gt (h_additiveFunction_a_neg S hS_neg))]⟩⟩
    choose! ε hε_pos hε using fun S => if h : |f S| < M then h_inactive S h else h_active S (
      le_antisymm ( hMbound S ) ( not_lt.mp h ) );
    -- Choose ε as the minimum of the ε_S's.
    obtain ⟨ε_min, hε_min_pos, hε_min⟩ : ∃ ε_min > 0, ∀ S : Finset U, ε_min ≤ ε S := by
      by_cases h_empty : Finset.Nonempty (Finset.univ : Finset (Finset U));
      · have hne : (Finset.image ε Finset.univ).Nonempty :=
          ⟨ε h_empty.choose, Finset.mem_image_of_mem ε (Finset.mem_univ h_empty.choose)⟩
        refine ⟨Finset.min' (Finset.image ε Finset.univ) hne, ?_, ?_⟩
        · simp_all
        · intro S
          exact Finset.min'_le _ _ (Finset.mem_image_of_mem ε (Finset.mem_univ S))
      · simp_all +decide;
    exact ⟨ ε_min / 2, half_pos hε_min_pos, fun S => hε S ( ε_min / 2 ) ⟨ half_pos hε_min_pos, by
      linarith [ hε_min S ] ⟩ ⟩;
  exact absurd ( hbest ( fun i => ε * a i ) ) ( by push Not; exact hε )

omit [Fintype U] in
/-- `indicator'` is injective: different finsets give different indicator functions. -/
lemma indicator'_injective : Function.Injective (Finset.indicator' : Finset U → (U → ℝ)) := by
  intro S T hST
  ext i
  have h := congr_fun hST i
  simp [Finset.indicator'] at h
  by_cases hi : i ∈ S <;> by_cases hj : i ∈ T <;> simp_all

/-
Extract a `DualCertificate` from 0 ∈ convexHull of active generators.
-/
lemma dual_cert_from_convexHull
    (f : Finset U → ℝ) (M : ℝ) (hM_pos : 0 < M)
    (hMbound : ∀ S : Finset U, |f S| ≤ M)
    (h0 : (0 : U → ℝ) ∈ convexHull ℝ (activeGenerators f M)) :
    Nonempty (DualCertificate f M) := by
  -- By definition of convex hull, there exists a finite set of active generators $\{c_1, c_2,
  -- \ldots, c_n\}$ and positive weights $\{w_1, w_2, \ldots, w_n\}$ such that $\sum_{i=1}^n w_i c_i
  -- = 0$ and $\sum_{i=1}^n w_i = 1$.
  obtain ⟨c, w, hw_pos, hw_sum, hw_zero⟩ : ∃ (c : Finset (U → ℝ)) (w : (U → ℝ) → ℝ), (∀ v ∈ c, v ∈
    activeGenerators f M) ∧ (∀ v ∈ c, 0 < w v) ∧ (∑ v ∈ c, w v = 1) ∧ (∑ v ∈ c, w v • v = 0) := by
    rw [ mem_convexHull_iff_exists_fintype ] at h0;
    obtain ⟨ ι, x, w, z, hw₁, hw₂, hw₃, hw₄ ⟩ := h0;
    refine ⟨ Finset.image z ( Finset.univ.filter fun i => w i ≠ 0 ), fun v => ∑ i ∈
      Finset.univ.filter fun i => w i ≠ 0, if z i = v then w i else 0, ?_, ?_, ?_, ?_ ⟩ <;>
      simp_all +decide only [
        ne_eq, mem_image, mem_filter, mem_univ, true_and,
        sum_ite, sum_const_zero, add_zero, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, implies_true]
    · exact fun i hi => lt_of_lt_of_le ( lt_of_le_of_ne ( hw₁ i ) ( Ne.symm hi ) ) (
      Finset.single_le_sum ( fun i _ => hw₁ i ) ( by aesop ) );
    · rw [← hw₂]
      trans ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i
      · exact Finset.sum_image' (s := Finset.univ.filter fun i => w i ≠ 0) (g := z) (h := w)
          (by intro i hi; rfl)
      · exact Finset.sum_filter_of_ne (s := Finset.univ) (f := w) (p := fun i => w i ≠ 0)
          (by intro i _ hwi; exact hwi)
    · trans ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i • z i
      · exact Finset.sum_image' (s := Finset.univ.filter fun i => w i ≠ 0) (g := z)
          (h := fun i => w i • z i) (by
            intro i hi
            rw [Finset.sum_smul]
            exact Finset.sum_congr rfl fun j hj => by
              simp_all)
      · rw [Finset.sum_filter_of_ne]
        · exact hw₄
        · simp_all
  -- Define the weights for the finsets S such that their indicators are in c.
  obtain ⟨lam_pos, lam_neg, hw_pos_def, hw_neg_def⟩ : ∃ (lam_pos : Finset U → ℝ) (lam_neg : Finset U
    → ℝ),
    (∀ S : Finset U, 0 ≤ lam_pos S ∧ 0 ≤ lam_neg S) ∧
    (∀ S : Finset U, (lam_pos S > 0 → f S = M) ∧ (lam_neg S > 0 → f S = -M)) ∧
    (∑ S : Finset U, lam_pos S + ∑ S : Finset U, lam_neg S = 1) ∧
    (∑ S : Finset U, lam_pos S • S.indicator' - ∑ S : Finset U, lam_neg S • S.indicator' = 0) := by
      refine ⟨ fun S => if hS : f S = M then ∑ v ∈ c, if v = S.indicator' then w v else 0 else 0,
        fun S => if hS : f S = -M then ∑ v ∈ c, if v = -S.indicator' then w v else 0 else 0, ?_, ?_,
          ?_, ?_ ⟩ <;>
        simp_all +decide only [
          sum_ite_eq',
          dite_eq_ite,
          gt_iff_lt,
          ite_smul,
          zero_smul,
          sum_ite,
          sum_const_zero,
          add_zero]
      · intro S; split_ifs <;> simp +decide [ *, le_of_lt ];
      · grind;
      · convert hw_zero.1 using 1;
        rw [
          ← Finset.sum_subset
            (show
              Finset.image (fun S => S.indicator')
                  (Finset.filter (fun S => f S = M) Finset.univ |>
                    Finset.filter (fun S => S.indicator' ∈ c)) ∪
                Finset.image (fun S => -S.indicator')
                  (Finset.filter (fun S => f S = -M) Finset.univ |>
                    Finset.filter (fun S => -S.indicator' ∈ c)) ⊆ c from
              ?_)
          ];
        · rw [ Finset.sum_union ];
          · rw [Finset.sum_image, Finset.sum_image] <;>
              simp +contextual [indicator'_injective.eq_iff]
          · simp +contextual only [
              disjoint_left,
              mem_image,
              mem_filter,
              mem_univ,
              true_and,
              not_exists,
              not_and,
              and_imp,
              forall_exists_index]
            rintro _ S₁ hS₁ hS₁' rfl S₂ hS₂ hS₂'
            simp_all +decide only [
              funext_iff,
              Finset.sum_apply,
              Pi.smul_apply,
              smul_eq_mul,
              Pi.zero_apply,
              Pi.neg_apply,
              indicator',
              not_forall]
            contrapose! hM_pos;
            have h_empty : S₁ = ∅ := by
              grind;
            have := hMbound ∅; simp_all +decide [ abs_le ];
            rw [ show S₂ = ∅ by ext x; aesop ] at hS₂; linarith;
        · intro v hv hv'; specialize hw_pos v hv; simp_all +decide [ activeGenerators ];
          grind;
        · grind;
      · have h_sum_eq : ∑ v ∈ c, w v • v = ∑ S ∈ Finset.filter (fun S => f S = M) Finset.univ, ∑ v ∈
        c, (if v = S.indicator' then w v • v else 0) + ∑ S ∈ Finset.filter (fun S => f S = -M)
          Finset.univ, ∑ v ∈ c, (if v = -S.indicator' then w v • v else 0) := by
          have h_sum_eq : ∀ v ∈ c, v = ∑ S ∈ Finset.filter (fun S => f S = M) Finset.univ, (if v =
            S.indicator' then v else 0) + ∑ S ∈ Finset.filter (fun S => f S = -M) Finset.univ, (if v
              = -S.indicator' then v else 0) := by
            intro v hv
            specialize hw_pos v hv
            unfold activeGenerators at hw_pos
            simp_all +decide only [
              Set.mem_union,
              Set.mem_image,
              Set.mem_setOf_eq,
              sum_ite,
              sum_const_zero,
              add_zero,
              sum_neg_distrib]
            rcases hw_pos with (⟨S, hS₁, rfl⟩ | ⟨S, hS₁, rfl⟩) <;>
              simp +decide only [sum_filter]
            · rw [Finset.sum_eq_single S, Finset.sum_eq_zero] <;>
                simp +contextual only [
                  hS₁,
                  ↓reduceIte,
                  neg_zero,
                  add_zero,
                  mem_univ,
                  ite_eq_right_iff,
                  forall_const,
                  ne_eq,
                  indicator'_injective.eq_iff,
                  not_true_eq_false,
                  IsEmpty.forall_iff]
              · intro T hT₁ hT₂
                have := congr_fun hT₂
                simp_all +decide only [indicator', Pi.neg_apply]
                ext a; specialize this a; split_ifs at this <;> norm_num at this;
                simp +decide [ *, Finset.indicator' ];
              · aesop;
            · rw [Finset.sum_eq_zero, Finset.sum_eq_single S] <;>
                simp +contextual only [
                  hS₁,
                  ↓reduceIte,
                  zero_add,
                  mem_univ,
                  ne_eq,
                  neg_inj,
                  indicator'_injective.eq_iff,
                  ite_eq_right_iff,
                  forall_const,
                  not_true_eq_false,
                  IsEmpty.forall_iff]
              · aesop;
              · intro T hT₁ hT₂
                have := congr_fun hT₂
                simp_all +decide only [indicator', Pi.neg_apply]
                ext a
                specialize this a
                split_ifs at this <;> simp_all +decide [Finset.indicator']
                norm_num at this;
          have h_sum_eq : ∑ v ∈ c, w v • v = ∑ v ∈ c, w v • (∑ S ∈ Finset.filter (fun S => f S = M)
            Finset.univ, (if v = S.indicator' then v else 0) + ∑ S ∈ Finset.filter (fun S => f S =
              -M) Finset.univ, (if v = -S.indicator' then v else 0)) := by
            exact Finset.sum_congr rfl fun v hv => h_sum_eq v hv ▸ rfl;
          rw [ h_sum_eq, Finset.sum_congr rfl fun v hv => by rw [ smul_add ] ];
          simp +decide only [smul_sum, smul_ite, smul_zero, sum_add_distrib];
          exact congrArg₂ ( · + · ) ( Finset.sum_comm ) ( Finset.sum_comm );
        simp_all +decide only [
          sum_ite_eq',
          sum_ite,
          sum_const_zero,
          add_zero,
          smul_neg,
          sum_neg_distrib]
        exact eq_of_sub_eq_zero ( by simpa [ sub_eq_add_neg ] using hw_zero.2 );
  refine ⟨⟨fun S => lam_pos S - lam_neg S, ?_, ?_, ?_, ?_⟩⟩
  · have h_abs : ∀ S : Finset U, |lam_pos S - lam_neg S| = lam_pos S + lam_neg S := by
      grind;
    simp_all +decide [ Finset.sum_add_distrib ];
  · intro i
    replace hw_neg_def := congr_fun hw_neg_def.2.2 i
    have hdiff :
        ((∑ x : Finset U, if i ∈ x then lam_pos x else 0) -
          ∑ x : Finset U, if i ∈ x then lam_neg x else 0) = 0 := by
      simpa [Finset.indicator'] using hw_neg_def
    have hsum : (∑ x : Finset U, if i ∈ x then lam_pos x - lam_neg x else 0) = 0 := by
      calc
        (∑ x : Finset U, if i ∈ x then lam_pos x - lam_neg x else 0)
            = ∑ x : Finset U,
                ((if i ∈ x then lam_pos x else 0) - (if i ∈ x then lam_neg x else 0)) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : i ∈ x <;> simp [hx]
        _ = (∑ x : Finset U, if i ∈ x then lam_pos x else 0) -
              ∑ x : Finset U, if i ∈ x then lam_neg x else 0 := by
              rw [Finset.sum_sub_distrib]
        _ = 0 := hdiff
    simpa [Finset.sum_filter, sub_eq_add_neg] using hsum
  · grind +revert;
  · grind +qlia

/-- When `M > 0`, construct the dual certificate via Hahn–Banach. -/
lemma dual_cert_pos_case
    (f : Finset U → ℝ) (_hf : IsApproxAdditive f 1)
    (hMbound : ∀ S : Finset U, |f S| ≤ distToAdditive f)
    (hbest : ∀ a : U → ℝ, ∃ S : Finset U,
      |f S - additiveFunction a S| ≥ distToAdditive f)
    (hM_pos : 0 < distToAdditive f) :
    Nonempty (DualCertificate f (distToAdditive f)) :=
  dual_cert_from_convexHull f _ hM_pos hMbound
    (zero_mem_convexHull_of_best_approx f _ hM_pos hMbound hbest)

omit [Fintype U] in
/-- `distToAdditive f ≥ 0` for any function `f`. -/
lemma distToAdditive_nonneg (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (hM : ∀ S : Finset U, |f S| ≤ distToAdditive f) :
    0 ≤ distToAdditive f := by
  simpa only [hf.1, abs_zero] using hM ∅

/-- **Lemma 2.1** (Dual certificate existence).
Combines the M = 0 and M > 0 cases. -/
theorem dual_certificate_exists_proof
    (f : Finset U → ℝ)
    (hf : IsApproxAdditive f 1)
    (hM : ∀ S : Finset U, |f S| ≤ distToAdditive f)
    (hbest : ∀ a : U → ℝ, ∃ S : Finset U,
      |f S - additiveFunction a S| ≥ distToAdditive f) :
    Nonempty (DualCertificate f (distToAdditive f)) := by
  by_cases hM0 : distToAdditive f = 0
  · exact dual_cert_zero_case f hf hM hM0
  · exact dual_cert_pos_case f hf hM hbest
      (lt_of_le_of_ne (distToAdditive_nonneg f hf hM) (Ne.symm hM0))

end KaltonRoberts
