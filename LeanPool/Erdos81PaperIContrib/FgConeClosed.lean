/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Geometry.Convex.Cone.Simplicial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!

# Closedness of a finitely generated cone (Weyl)

The finitely generated cone `cone{v k} = {∑ k, c k • v k : c ≥ 0}` spanned by a finite
family `v : κ → E` in a real normed space is **closed**. This is the nontrivial half of
the Farkas–Minkowski–Weyl correspondence and the key topological input to the geometric
Farkas lemma / finite LP strong duality.

Mathlib has `ProperCone` (whose closedness is part of the structure) and geometric
hyperplane separation, but does not provide the closedness result proved here.

## Main results
* `LeanPool.Erdos81PaperIContrib.simplicial_cone_isClosed` — a simplicial cone is closed.
* `LeanPool.Erdos81PaperIContrib.conic_caratheodory` — conic Carathéodory reduction.
* `LeanPool.Erdos81PaperIContrib.fg_cone_isClosed` — a finitely generated cone is closed.

## Generalization vs. the source
The Paper I version was stated over `EuclideanSpace ℝ ι`. None of the three proofs uses the
inner product; they are ported here to an arbitrary real normed space `E`
(`[NormedAddCommGroup E] [NormedSpace ℝ E]`), which is the natural Mathlib generality.

-/

open scoped BigOperators

namespace LeanPool.Erdos81PaperIContrib

variable {κ ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **simplicial cone** — the nonnegative combinations of a linearly independent finite
family — is closed: it is the image of the closed nonnegative orthant under an injective
(hence closed-embedding) linear map from a finite-dimensional space. -/
lemma simplicial_cone_isClosed
    (v : κ → E) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : E |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
  classical
  set L : (s → ℝ) →ₗ[ℝ] E :=
    ∑ k : s, LinearMap.smulRight (LinearMap.proj k) (v k) with hL_def
  have hLval : ∀ c : s → ℝ, L c = ∑ k : s, c k • v k := by
    intro c
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [hLval] at hm
    funext k; exact Fintype.linearIndependent_iff.mp hli m hm k
  have hclosedmap : IsClosedMap L :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {c : s → ℝ | ∀ k, 0 ≤ c k} := by
    have : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext c; simp
    rw [this]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨c, hc0, hcoff, rfl⟩
    refine ⟨fun k : s => c k, fun k => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach s (fun j => c j • v j)]
    rfl
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro k hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach s (fun j => (if h : j ∈ s then c ⟨j, h⟩ else 0) • v j)]
      apply Finset.sum_congr rfl
      intro k _
      simp [k.2]

/-- **Conic Carathéodory.** Over any linearly ordered field, a nonnegative combination of a
finite family equals a nonnegative combination over a linearly independent subfamily with the
same value. This algebraic reduction requires no topology on the ambient module. -/
lemma conic_caratheodory {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup M] [Module R M] [Fintype κ]
    (v : κ → M) (c : κ → R) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → R) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn R v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset κ,
      (∃ d : κ → R, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
        (∑ k ∈ s, d k • v k = ∑ k, c k • v k)) ∧
      ∀ t : Finset κ, (∃ d : κ → R, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ t, d k = 0) ∧
        (∑ k ∈ t, d k • v k = ∑ k, c k • v k)) → s.card ≤ t.card := by
    apply_rules [Set.exists_min_image]
    · exact Set.toFinite _
    · exact ⟨Finset.univ, ⟨c, hc, fun k hk => False.elim <| hk <| Finset.mem_univ _, by
        simp⟩⟩
  by_cases h_lin_dep : ¬ LinearIndepOn R v s
  · obtain ⟨d, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨a, ha_nonzero, ha_support, ha_sum⟩ : ∃ a : κ → R,
        (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧
        (∑ k ∈ s, a k • v k = 0) ∧ (∃ k ∈ s, a k > 0) := by
      obtain ⟨a, ha_nonzero, ha_sum⟩ : ∃ a : κ → R,
          (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧
          (∑ k ∈ s, a k • v k = 0) := by
        rw [linearIndepOn_iff'] at h_lin_dep
        push Not at h_lin_dep
        obtain ⟨t, g, ht, hg, i, hi, hi'⟩ := h_lin_dep
        refine ⟨fun k => if k ∈ t then g k else 0, ⟨i, ht hi, by simpa [hi] using hi'⟩,
          fun k hk => by
            change (if k ∈ t then g k else 0) = 0
            split
            · rename_i hkt
              exact (hk (ht hkt)).elim
            · rfl, ?_⟩
        calc ∑ k ∈ s, (if k ∈ t then g k else 0) • v k
            = ∑ k ∈ s, if k ∈ t then g k • v k else 0 := by
              refine Finset.sum_congr rfl (fun k _ => ?_); rw [ite_smul, zero_smul]
          _ = ∑ k ∈ s ∩ t, g k • v k := Finset.sum_ite_mem s t _
          _ = ∑ k ∈ t, g k • v k := by rw [Finset.inter_eq_right.mpr ht]
          _ = 0 := hg
      by_cases h_neg : ∀ k ∈ s, a k ≤ 0
      · obtain ⟨k, hks, hk⟩ := ha_nonzero
        exact ⟨fun k => -a k, ⟨k, hks, neg_ne_zero.mpr hk⟩,
          fun k hk => by simp only [ha_sum.1 k hk, neg_zero],
          by simp [neg_smul, ha_sum.2],
          ⟨k, hks, neg_pos.mpr (lt_of_le_of_ne (h_neg k hks) hk)⟩⟩
      · exact ⟨a, ha_nonzero, ha_sum.1, ha_sum.2, by
          push Not at h_neg
          exact h_neg⟩
    obtain ⟨θ, hθ_min⟩ : ∃ θ,
        (∀ k ∈ s, d k - θ * a k ≥ 0) ∧ (∃ k ∈ s, d k - θ * a k = 0) := by
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ s, a k₀ > 0 ∧
          ∀ k ∈ s, a k > 0 → d k / a k ≥ d k₀ / a k₀ := by
        obtain ⟨kp, hkp⟩ := ha_sum.2
        obtain ⟨k₀, hk₀f, hk₀min⟩ :=
          Finset.exists_min_image (s.filter (fun k => a k > 0)) (fun k => d k / a k)
            ⟨kp, Finset.mem_filter.mpr hkp⟩
        obtain ⟨hk₀s, hk₀pos⟩ := Finset.mem_filter.mp hk₀f
        exact ⟨k₀, hk₀s, hk₀pos, fun k hk hk' =>
          hk₀min k (Finset.mem_filter.mpr ⟨hk, hk'⟩)⟩
      refine ⟨d k₀ / a k₀, ?_, k₀, hk₀.1, ?_⟩
      · intro k hk
        by_cases hk' : a k > 0
        · have hle : d k₀ / a k₀ * a k ≤ d k :=
            (le_div_iff₀ hk').1 (hk₀.2.2 k hk hk')
          linarith
        · have h2 : d k₀ / a k₀ * a k ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hd_nonneg _) hk₀.2.1.le)
              (le_of_not_gt hk')
          linarith [hd_nonneg k]
      · rw [div_mul_cancel₀ _ hk₀.2.1.ne', sub_self]
    set t := s.filter (fun k => d k - θ * a k ≠ 0) with ht_def
    have h_t_support : ∀ k, 0 ≤ d k - θ * a k := by
      exact fun k => if hk : k ∈ s then hθ_min.1 k hk else by
        simp [hd_zero k hk, ha_support k hk]
    have h_t_zero : ∀ k ∉ t, d k - θ * a k = 0 := by
      intro k hk
      by_cases hks : k ∈ s
      · by_contra hP
        exact hk (by rw [ht_def]; exact Finset.mem_filter.mpr ⟨hks, hP⟩)
      · rw [hd_zero k hks, ha_support k hks]
        ring
    have h_t_sum : ∑ k ∈ t, (d k - θ * a k) • v k = ∑ k, c k • v k := by
      convert congr_arg (fun x => x - θ • ∑ k ∈ s, a k • v k) hd_sum using 1
      · rw [Finset.sum_filter_of_ne]
        · simp [sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
        · exact fun k _ hk' hk'' => hk' <| by rw [hk'', zero_smul]
      · simp [ha_sum.1]
    contrapose! hs
    refine fun _ => ⟨t, ⟨fun k => d k - θ * a k, h_t_support, h_t_zero, h_t_sum⟩, ?_⟩
    refine Finset.card_lt_card ?_
    rw [ht_def]
    obtain ⟨k₁, hk₁s, hk₁0⟩ := hθ_min.2
    exact ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hk₁s)).2 hk₁0⟩
  · exact ⟨hs.1.choose, s, hs.1.choose_spec.1, hs.1.choose_spec.2.1,
      Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2⟩

/-- **Weyl.** The finitely generated cone `{∑ k, c k • v k : c ≥ 0}` is closed. -/
lemma fg_cone_isClosed [Fintype κ] (v : κ → E) :
    IsClosed {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by
  classical
  have hset : {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y}
      = ⋃ s : Finset κ, ⋃ (_ : LinearIndepOn ℝ v s),
          {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧
            ∑ k ∈ s, c k • v k = y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc0, rfl⟩
      obtain ⟨d, s, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory v c hc0
      exact ⟨s, hindep, d, hd0, hdoff, hsum⟩
    · rintro ⟨s, hindep, c, hc0, hcoff, rfl⟩
      refine ⟨c, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro k _ hks; rw [hcoff k hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed v s h

/-! ### Integration with the Mathlib `PointedCone` API

We restate closedness in Mathlib's cone vocabulary. `PointedCone ℝ E` is
`Submodule {c : ℝ // 0 ≤ c} E`; `PointedCone.hull ℝ s` is its conic hull. The bridge below
identifies the span (as a set) with the engine's explicit conic-combination set, handling
the `ℝ≥0`-vs-`ℝ` scalar action. -/

open scoped BigOperators

/-- The conic span of a finite set equals the engine's explicit nonnegative-combination
set indexed by the finite subtype. This is the `ℝ≥0`/`ℝ` bridge. -/
private lemma hull_eq_engine {s : Set E} [Fintype s] :
    (PointedCone.hull ℝ s : Set E)
      = {y : E | ∃ c : ↥s → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • (k : E) = y} := by
  classical
  apply Set.Subset.antisymm
  · -- span ⊆ engine set, by span induction
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
        refine ⟨fun k => if k = (⟨x, h⟩ : s) then (1 : ℝ) else 0, ?_, ?_⟩
        · intro k; dsimp only; split_ifs <;> norm_num
        · simp [Finset.sum_ite_eq']
    | zero => exact ⟨0, fun _ => le_refl 0, by simp⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨cx, hcx, rfl⟩ := ihx
        obtain ⟨cy, hcy, rfl⟩ := ihy
        exact ⟨fun k => cx k + cy k, fun k => add_nonneg (hcx k) (hcy k), by
          simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ ih =>
        obtain ⟨c, hc, rfl⟩ := ih
        refine ⟨fun k => (a : ℝ) * c k, fun k => mul_nonneg a.2 (hc k), ?_⟩
        have : (a • ∑ k, c k • (k : E)) = (a : ℝ) • ∑ k, c k • (k : E) := rfl
        rw [this, Finset.smul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [smul_smul])
  · -- engine set ⊆ span
    rintro x ⟨c, hc, rfl⟩
    refine sum_mem (fun k _ => ?_)
    have hk : (k : E) ∈ PointedCone.hull ℝ s := PointedCone.subset_hull k.2
    have hsm : c k • (k : E) = (⟨c k, hc k⟩ : {c : ℝ // 0 ≤ c}) • (k : E) := rfl
    rw [hsm]
    exact Submodule.smul_mem _ _ hk

/-- **A finitely generated pointed cone is closed** (Mathlib-API form). -/
theorem hull_isClosed_of_finite {s : Set E} (hs : s.Finite) :
    IsClosed (PointedCone.hull ℝ s : Set E) := by
  classical
  let _ : Fintype s := hs.fintype
  rw [hull_eq_engine]
  exact fg_cone_isClosed (fun k : s => (k : E))

/-- A finitely generated pointed cone in a real normed space is closed. -/
theorem PointedCone.FG.isClosed {C : PointedCone ℝ E} (hC : C.FG) :
    IsClosed (C : Set E) := by
  obtain ⟨s, rfl⟩ := hC
  exact hull_isClosed_of_finite s.finite_toSet

/-- **A simplicial pointed cone is closed** (Mathlib-API form). -/
theorem isSimplicial_isClosed {C : PointedCone ℝ E} (hC : C.IsSimplicial) :
    IsClosed (C : Set E) := by
  obtain ⟨s, hs, _, hspan⟩ := hC
  rw [← hspan]
  exact hull_isClosed_of_finite hs

end LeanPool.Erdos81PaperIContrib
