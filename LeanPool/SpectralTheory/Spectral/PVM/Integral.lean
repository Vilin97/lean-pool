/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.SpectralTheory.Spectral.PVM.Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini

/-!
# Bounded spectral integration

This file constructs the spectral integral first for complex-valued simple functions and then for
bounded measurable functions.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The spectral sum of a complex-valued simple function against a PVM. -/
noncomputable def PVM.simpleIntegral (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) : E →L[ℂ] E :=
  ∑ z ∈ f.range, z • E_pvm.proj (f ⁻¹' {z})

/-- The projections of finitely many fibers add to the projection of their union. -/
theorem PVM.sum_proj_preimage (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (s : Finset β) :
    ∑ y ∈ s, E_pvm.proj (f ⁻¹' {y}) = E_pvm.proj (f ⁻¹' (↑s : Set β)) := by
  classical
  have hmeas : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) :=
    fun y _ => f.measurableSet_fiber y
  have hpair : (↑s : Set β).PairwiseDisjoint (fun y => f ⁻¹' {y}) := by
    intro y hy z hz hyz
    change Disjoint (f ⁻¹' {y}) (f ⁻¹' {z})
    rw [Set.disjoint_left]
    intro t hty htz
    change f t = y at hty
    change f t = z at htz
    exact hyz (hty.symm.trans htz)
  have hunion : (⋃ y ∈ (↑s : Set β), f ⁻¹' {y}) = f ⁻¹' (↑s : Set β) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_iUnion] at ht
      obtain ⟨y, ht⟩ := ht
      rw [Set.mem_iUnion] at ht
      obtain ⟨hy, hty⟩ := ht
      change f t = y at hty
      change f t ∈ (↑s : Set β)
      exact hty.symm ▸ hy
    · intro ht
      change f t ∈ (↑s : Set β) at ht
      rw [Set.mem_iUnion]
      refine ⟨f t, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨ht, rfl⟩
  rw [← E_pvm.proj_biUnion_finset s (fun y => f ⁻¹' {y}) hmeas hpair, hunion]

/-- Reindexing a simple function groups the projections of fibers with the same new value. -/
theorem PVM.simpleIntegral_map (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (g : β → ℂ) :
    E_pvm.simpleIntegral (f.map g) =
      ∑ y ∈ f.range, g y • E_pvm.proj (f ⁻¹' {y}) := by
  classical
  rw [PVM.simpleIntegral, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun y hy => ?_
  rw [SimpleFunc.map_preimage_singleton, ← E_pvm.sum_proj_preimage,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [(Finset.mem_filter.mp hz).2]

/-- Simple spectral integration preserves addition. -/
theorem PVM.simpleIntegral_add (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f + g) = E_pvm.simpleIntegral f + E_pvm.simpleIntegral g := by
  calc
    E_pvm.simpleIntegral (f + g) =
        ∑ p ∈ (f.pair g).range,
          (p.1 + p.2) • E_pvm.proj (f.pair g ⁻¹' {p}) := by
      rw [SimpleFunc.add_eq_map₂, E_pvm.simpleIntegral_map]
    _ = (∑ p ∈ (f.pair g).range,
          p.1 • E_pvm.proj (f.pair g ⁻¹' {p})) +
        ∑ p ∈ (f.pair g).range,
          p.2 • E_pvm.proj (f.pair g ⁻¹' {p}) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [add_smul]
    _ = E_pvm.simpleIntegral ((f.pair g).map Prod.fst) +
        E_pvm.simpleIntegral ((f.pair g).map Prod.snd) := by
      rw [E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map]
    _ = E_pvm.simpleIntegral f + E_pvm.simpleIntegral g := by
      rw [SimpleFunc.map_fst_pair, SimpleFunc.map_snd_pair]

/-- Simple spectral integration preserves negation. -/
theorem PVM.simpleIntegral_neg (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (-f) = -E_pvm.simpleIntegral f := by
  change E_pvm.simpleIntegral (f.map Neg.neg) = -E_pvm.simpleIntegral f
  rw [E_pvm.simpleIntegral_map, PVM.simpleIntegral, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [neg_smul]

/-- Simple spectral integration preserves subtraction. -/
theorem PVM.simpleIntegral_sub (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f - g) = E_pvm.simpleIntegral f - E_pvm.simpleIntegral g := by
  rw [sub_eq_add_neg, E_pvm.simpleIntegral_add, E_pvm.simpleIntegral_neg]
  rw [sub_eq_add_neg]

/-- The projections of the fibers of a simple function sum to the identity. -/
theorem PVM.sum_proj_fiber_eq_one (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    (∑ z ∈ f.range, E_pvm.proj (f ⁻¹' {z})) = 1 := by
  have hpair : (↑f.range : Set ℂ).PairwiseDisjoint (fun z => f ⁻¹' {z}) := by
    intro z hz w hw hzw
    change Disjoint (f ⁻¹' {z}) (f ⁻¹' {w})
    rw [Set.disjoint_left]
    intro t htz htw
    exact hzw ((Set.mem_singleton_iff.mp htz).symm.trans (Set.mem_singleton_iff.mp htw))
  have hunion : (⋃ z ∈ (↑f.range : Set ℂ), f ⁻¹' {z}) = Set.univ := by
    ext t
    constructor
    · intro ht
      exact Set.mem_univ t
    · intro ht
      rw [Set.mem_iUnion]
      refine ⟨f t, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨f.mem_range_self t, rfl⟩
  have hmeas : ∀ z ∈ f.range, MeasurableSet (f ⁻¹' {z}) :=
    fun z _ => f.measurableSet_fiber z
  rw [← E_pvm.proj_biUnion_finset f.range (fun z => f ⁻¹' {z}) hmeas hpair,
    hunion, E_pvm.univ]

/-- Projections onto two distinct fibers of a simple function multiply to zero. -/
theorem PVM.proj_fiber_mul_proj_fiber (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ)
    {z w : ℂ} (hzw : z ≠ w) :
    E_pvm.proj (f ⁻¹' {z}) * E_pvm.proj (f ⁻¹' {w}) = 0 := by
  rw [← E_pvm.inter _ _ (f.measurableSet_fiber z) (f.measurableSet_fiber w)]
  have hinter : (f ⁻¹' {z}) ∩ (f ⁻¹' {w}) = ∅ := by
    ext t
    constructor
    · intro ht
      exact hzw ((Set.mem_singleton_iff.mp ht.1).symm.trans (Set.mem_singleton_iff.mp ht.2))
    · intro ht
      exact False.elim ht
  rw [hinter, E_pvm.empty]

/-- On a fixed simple partition, pointwise multiplication becomes operator multiplication. -/
theorem PVM.simpleIntegral_map_mul_map (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (a b : β → ℂ) :
    E_pvm.simpleIntegral (f.map a) * E_pvm.simpleIntegral (f.map b) =
      E_pvm.simpleIntegral (f.map fun z => a z * b z) := by
  classical
  rw [E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum, Finset.sum_eq_single z]
  · rw [smul_mul_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
      (f.measurableSet_fiber z)).2.eq]
  · intro w hw hwz
    have hzw : z ≠ w := Ne.symm hwz
    have hzero : E_pvm.proj (f ⁻¹' {z}) * E_pvm.proj (f ⁻¹' {w}) = 0 := by
      rw [← E_pvm.inter _ _ (f.measurableSet_fiber z) (f.measurableSet_fiber w)]
      have hinter : (f ⁻¹' {z}) ∩ (f ⁻¹' {w}) = ∅ := by
        ext t
        constructor
        · intro ht
          exact hzw ((Set.mem_singleton_iff.mp ht.1).symm.trans
            (Set.mem_singleton_iff.mp ht.2))
        · intro ht
          exact False.elim ht
      rw [hinter, E_pvm.empty]
    rw [smul_mul_smul, hzero, smul_zero]
  · intro hznot
    exact (hznot hz).elim

/-- Simple spectral integration preserves pointwise multiplication. -/
theorem PVM.simpleIntegral_mul (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f * g) = E_pvm.simpleIntegral f * E_pvm.simpleIntegral g := by
  rw [SimpleFunc.mul_eq_map₂]
  symm
  simpa only [SimpleFunc.map_fst_pair, SimpleFunc.map_snd_pair] using
    E_pvm.simpleIntegral_map_mul_map (f.pair g) Prod.fst Prod.snd

/-- Multiplying a simple spectral sum by its adjoint removes all cross-fiber terms. -/
theorem PVM.star_simpleIntegral_mul (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    star (E_pvm.simpleIntegral f) * E_pvm.simpleIntegral f =
      ∑ z ∈ f.range, (star z * z) • E_pvm.proj (f ⁻¹' {z}) := by
  classical
  rw [PVM.simpleIntegral, star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [star_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
    (f.measurableSet_fiber z)).1.star_eq, Finset.mul_sum]
  rw [Finset.sum_eq_single z]
  · rw [smul_mul_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
      (f.measurableSet_fiber z)).2.eq]
  · intro w hw hwz
    rw [smul_mul_smul, E_pvm.proj_fiber_mul_proj_fiber f (Ne.symm hwz), smul_zero]
  · intro hznot
    exact (hznot hz).elim

/-- The squared norm of a simple spectral sum is the weighted sum over its fibers. -/
theorem PVM.norm_sq_simpleIntegral (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) (x : E) :
    ‖E_pvm.simpleIntegral f x‖ ^ 2 =
      ∑ z ∈ f.range, ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  rw [← ContinuousLinearMap.star_eq_adjoint]
  change (@inner ℂ E _
    ((star (E_pvm.simpleIntegral f) * E_pvm.simpleIntegral f) x) x).re = _
  rw [E_pvm.star_simpleIntegral_mul f]
  rw [sum_apply, sum_inner]
  rw [Complex.re_sum]
  have hzstar (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hterm (z : ℂ) :
      (@inner ℂ E _ (((star z * z) • E_pvm.proj (f ⁻¹' {z})) x) x).re =
        ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
    rw [hzstar, smul_apply, inner_smul_left]
    have hrealstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [starRingEnd_apply, hrealstar]
    change ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re -
        0 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).im = _
    ring
  simpa only [] using
    (Finset.sum_congr (s₁ := f.range) (s₂ := f.range) rfl (fun z hz => hterm z))

/-- A uniform bound for a simple function bounds the norm of its spectral sum. -/
theorem PVM.norm_simpleIntegral_le (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t‖ ≤ C) : ‖E_pvm.simpleIntegral f‖ ≤ C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hbdd 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hweight_nonneg (z : ℂ) :
      0 ≤ (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
    exact
      ((ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z}) (f.measurableSet_fiber z)).2).mpr
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
          (f.measurableSet_fiber z)).1).re_inner_nonneg_left x
  have hsum_weight :
      ∑ z ∈ f.range, (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re = ‖x‖ ^ 2 := by
    have h := congrArg
      (fun A : E →L[ℂ] E => (@inner ℂ E _ (A x) x).re)
      (E_pvm.sum_proj_fiber_eq_one f)
    rw [sum_apply, sum_inner, Complex.re_sum] at h
    change (∑ z ∈ f.range,
      (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re) =
        (@inner ℂ E _ x x).re at h
    calc
      ∑ z ∈ f.range,
          (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re =
          (@inner ℂ E _ x x).re := h
      _ = ‖x‖ ^ 2 := by
        change RCLike.re (@inner ℂ E _ x x) = ‖x‖ ^ 2
        exact @inner_self_eq_norm_sq ℂ E _ _ _ x
  have hsquare : ‖E_pvm.simpleIntegral f x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [E_pvm.norm_sq_simpleIntegral f x]
    calc
      ∑ z ∈ f.range,
          ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re ≤
          ∑ z ∈ f.range,
            C ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_right _ (hweight_nonneg z)
        apply (sq_le_sq₀ (norm_nonneg z) hC).mpr
        rw [SimpleFunc.mem_range] at hz
        obtain ⟨t, rfl⟩ := hz
        exact hbdd t
      _ = C ^ 2 * ∑ z ∈ f.range,
          (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
        rw [Finset.mul_sum]
      _ = C ^ 2 * ‖x‖ ^ 2 := by rw [hsum_weight]
      _ = (C * ‖x‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp hsquare

/-- Uniform distance of simple functions controls the operator norm of their spectral sums. -/
theorem PVM.norm_simpleIntegral_sub_le (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t - g t‖ ≤ C) :
    ‖E_pvm.simpleIntegral f - E_pvm.simpleIntegral g‖ ≤ C := by
  rw [← E_pvm.simpleIntegral_sub]
  apply E_pvm.norm_simpleIntegral_le
  intro t
  exact hbdd t

/- The error of `nearestPt` is written recursively as a minimum so that its continuity is
visible to Dini's theorem, even though the chosen nearest point itself need not be continuous. -/
private noncomputable def nearestError (e : ℕ → ℂ) : ℕ → ℂ → ℝ
  | 0 => fun z => dist (e 0) z
  | n + 1 => fun z => min (dist (e (n + 1)) z) (nearestError e n z)

private theorem nearestError_continuous (e : ℕ → ℂ) :
    ∀ n, Continuous (nearestError e n)
  | 0 => continuous_const.dist continuous_id
  | n + 1 => (continuous_const.dist continuous_id).min (nearestError_continuous e n)

private theorem nearestError_eq (e : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    nearestError e n z = dist (SimpleFunc.nearestPt e n z) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change min (dist (e (n + 1)) z) (nearestError e n z) = _
      rw [ih]
      simp only [SimpleFunc.nearestPt, SimpleFunc.nearestPtInd_succ,
        SimpleFunc.map_apply]
      split_ifs with h
      · rw [min_eq_left]
        have hle := (h (SimpleFunc.nearestPtInd e n z)
          (SimpleFunc.nearestPtInd_le e n z)).le
        rw [edist_dist, edist_dist] at hle
        exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle
      · rw [min_eq_right]
        push Not at h
        obtain ⟨k, hk, hnew⟩ := h
        have hold := SimpleFunc.edist_nearestPt_le e z hk
        rw [edist_dist, edist_dist] at hold hnew
        exact ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hold).trans
          ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hnew)

private theorem nearestError_antitone (e : ℕ → ℂ) (z : ℂ) :
    Antitone (fun n => nearestError e n z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [nearestError]
  exact min_le_right _ _

private theorem nearestError_tendsto_of_nearestPt_tendsto (e : ℕ → ℂ) (z : ℂ)
    (h : Filter.Tendsto (fun n => SimpleFunc.nearestPt e n z) Filter.atTop (nhds z)) :
    Filter.Tendsto (fun n => nearestError e n z) Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => z) Filter.atTop (nhds z) :=
    tendsto_const_nhds
  have hdist := h.dist hconst
  simpa only [nearestError_eq, dist_self] using hdist

private theorem nearestPt_tendstoUniformlyOn (s : Set ℂ) (hs : IsCompact s)
    (y₀ : ℂ) (hy₀ : y₀ ∈ s) :
    TendstoUniformlyOn
      (fun n z => SimpleFunc.approxOn id measurable_id s y₀ hy₀ n z)
      id Filter.atTop s := by
  let _ : Nonempty s := ⟨⟨y₀, hy₀⟩⟩
  let e : ℕ → ℂ := fun k => Nat.casesOn k y₀
    (Subtype.val ∘ TopologicalSpace.denseSeq s)
  have hpoint (z : ℂ) (hz : z ∈ s) :
      Filter.Tendsto (fun n => nearestError e n z) Filter.atTop (nhds 0) := by
    apply nearestError_tendsto_of_nearestPt_tendsto
    have h := SimpleFunc.tendsto_approxOn (f := id) measurable_id hy₀ (subset_closure hz)
    change Filter.Tendsto (fun n => SimpleFunc.nearestPt e n z) Filter.atTop (nhds z) at h
    exact h
  have hDini : TendstoUniformlyOn (fun n => nearestError e n) (fun _ => 0)
      Filter.atTop s :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto hs
      (fun n => (nearestError_continuous e n).continuousOn)
      (fun z hz => nearestError_antitone e z) continuousOn_const hpoint
  rw [Metric.tendstoUniformlyOn_iff] at hDini ⊢
  intro ε hε
  filter_upwards [hDini ε hε] with n hn
  intro z hz
  have herr := hn z hz
  rw [dist_comm, Real.dist_0_eq_abs,
    abs_of_nonneg (by rw [nearestError_eq]; exact dist_nonneg)] at herr
  change dist z (SimpleFunc.nearestPt e n z) < ε
  rw [dist_comm, ← nearestError_eq]
  exact herr

private theorem bound_nonneg {f : ℝ → ℂ} {C : ℝ} (hbdd : ∀ t, ‖f t‖ ≤ C) : 0 ≤ C :=
  (norm_nonneg (f 0)).trans (hbdd 0)

/-- A uniformly bounded simple-function approximation used to construct the bounded spectral
integral. -/
noncomputable def boundedApprox (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) (n : ℕ) : SimpleFunc ℝ ℂ :=
  SimpleFunc.approxOn f hf (Metric.closedBall 0 C) 0
    (Metric.mem_closedBall.mpr (by rw [dist_self]; exact bound_nonneg hbdd)) n

private theorem boundedApprox_mem (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) (n : ℕ) (t : ℝ) :
    boundedApprox f hf C hbdd n t ∈ Metric.closedBall (0 : ℂ) C := by
  apply SimpleFunc.approxOn_mem

private theorem boundedApprox_norm_le (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) (n : ℕ) (t : ℝ) :
    ‖boundedApprox f hf C hbdd n t‖ ≤ C := by
  have h := boundedApprox_mem f hf C hbdd n t
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

private theorem boundedApprox_tendstoUniformly (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    TendstoUniformly (fun n t => boundedApprox f hf C hbdd n t) f Filter.atTop := by
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 C :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact bound_nonneg hbdd)
  have hU := nearestPt_tendstoUniformlyOn (Metric.closedBall (0 : ℂ) C)
    (ProperSpace.isCompact_closedBall 0 C) 0 hzero
  rw [Metric.tendstoUniformlyOn_iff] at hU
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hU ε hε] with n hn
  intro t
  have hft : f t ∈ Metric.closedBall (0 : ℂ) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbdd t
  have h := hn (f t) hft
  change dist (f t) (boundedApprox f hf C hbdd n t) < ε
  exact h

/-- A bounded measurable complex-valued function admits uniformly convergent simple
approximations obeying the same pointwise norm bound. -/
theorem exists_bounded_simpleFunc_tendstoUniformly (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc ℝ ℂ,
      TendstoUniformly (fun n t => s n t) f Filter.atTop ∧
        ∀ n t, ‖s n t‖ ≤ C := by
  exact ⟨boundedApprox f hf C hbdd,
    boundedApprox_tendstoUniformly f hf C hbdd,
    boundedApprox_norm_le f hf C hbdd⟩

private theorem simpleIntegral_boundedApprox_cauchy (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    CauchySeq (fun n => E_pvm.simpleIntegral (boundedApprox f hf C hbdd n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hU := boundedApprox_tendstoUniformly f hf C hbdd
  rw [Metric.tendstoUniformly_iff] at hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hU (ε / 4) (by linarith))
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hpoint : ∀ t,
      ‖boundedApprox f hf C hbdd m t - boundedApprox f hf C hbdd n t‖ ≤ ε / 2 := by
    intro t
    apply le_of_lt
    calc
      ‖boundedApprox f hf C hbdd m t - boundedApprox f hf C hbdd n t‖ =
          dist (boundedApprox f hf C hbdd m t) (boundedApprox f hf C hbdd n t) := by
        rw [dist_eq_norm]
      _ ≤ dist (boundedApprox f hf C hbdd m t) (f t) +
          dist (f t) (boundedApprox f hf C hbdd n t) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        apply add_lt_add
        · rw [dist_comm]
          exact hN m hm t
        · exact hN n hn t
      _ = ε / 2 := by ring
  have hop := E_pvm.norm_simpleIntegral_sub_le
    (boundedApprox f hf C hbdd m) (boundedApprox f hf C hbdd n)
    (C := ε / 2) hpoint
  exact hop.trans_lt (by linarith)

/-- The spectral sum of a constant simple function is the corresponding scalar operator. -/
theorem PVM.simpleIntegral_const (E_pvm : PVM E) (z : ℂ) :
    E_pvm.simpleIntegral (SimpleFunc.const ℝ z) = z • 1 := by
  rw [PVM.simpleIntegral, SimpleFunc.range_const, Finset.sum_singleton]
  have hpre : ((SimpleFunc.const ℝ z : SimpleFunc ℝ ℂ) ⁻¹' {z}) = Set.univ := by
    ext t
    simp only [SimpleFunc.const_apply, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ]
  rw [hpre, E_pvm.univ]

/-- The spectral sum of the zero simple function is zero. -/
@[simp]
theorem PVM.simpleIntegral_zero (E_pvm : PVM E) :
    E_pvm.simpleIntegral (0 : SimpleFunc ℝ ℂ) = 0 := by
  rw [show (0 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 0 by
    ext t
    rfl]
  rw [E_pvm.simpleIntegral_const, zero_smul]

/-- The spectral sum of the unit simple function is the identity operator. -/
@[simp]
theorem PVM.simpleIntegral_one (E_pvm : PVM E) :
    E_pvm.simpleIntegral (1 : SimpleFunc ℝ ℂ) = 1 := by
  rw [show (1 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 1 by
    ext t
    rfl]
  rw [E_pvm.simpleIntegral_const, one_smul]

/-- The spectral sum of `z` on a measurable set and zero off it is `z • E(S)`. -/
theorem PVM.simpleIntegral_piecewise_const (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S) (z : ℂ) :
    E_pvm.simpleIntegral
        (SimpleFunc.piecewise S hS (SimpleFunc.const ℝ z) (SimpleFunc.const ℝ 0)) =
      z • E_pvm.proj S := by
  classical
  by_cases hS_empty : S = ∅
  · subst S
    rw [SimpleFunc.piecewise_empty, E_pvm.simpleIntegral_const, zero_smul,
      E_pvm.empty, smul_zero]
  · by_cases hS_univ : S = Set.univ
    · subst S
      rw [SimpleFunc.piecewise_univ, E_pvm.simpleIntegral_const, E_pvm.univ]
    · by_cases hz : z = 0
      · subst z
        have hzero :
            SimpleFunc.piecewise S hS (SimpleFunc.const ℝ (0 : ℂ))
              (SimpleFunc.const ℝ 0) = 0 := by
          rw [show (0 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 0 by ext t; rfl]
          exact SimpleFunc.piecewise_same _ hS
        rw [hzero, E_pvm.simpleIntegral_zero, zero_smul]
      · rw [PVM.simpleIntegral,
          SimpleFunc.range_indicator hS (Set.nonempty_iff_ne_empty.mpr hS_empty) hS_univ z 0]
        rw [Finset.sum_insert (by
          intro hzmem
          exact hz (Finset.mem_singleton.mp hzmem)), Finset.sum_singleton]
        have hpre :
            (SimpleFunc.piecewise S hS (SimpleFunc.const ℝ z) (SimpleFunc.const ℝ 0) ⁻¹'
              {z}) = S := by
          ext t
          simp only [SimpleFunc.piecewise_apply, SimpleFunc.const_apply, Set.mem_preimage,
            Set.mem_singleton_iff]
          by_cases ht : t ∈ S
          · rw [ite_eq_left ht]
            exact iff_of_true rfl ht
          · rw [ite_eq_right ht]
            exact iff_of_false (Ne.symm hz) ht
        rw [hpre, zero_smul, add_zero]

/-- The bounded spectral integral of a measurable, uniformly bounded complex function. -/
noncomputable def PVM.integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    E →L[ℂ] E :=
  Filter.limUnder Filter.atTop (fun n => E_pvm.simpleIntegral
    (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n))

private theorem PVM.tendsto_integralApprox (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    Filter.Tendsto
      (fun n => E_pvm.simpleIntegral
        (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) := by
  rw [PVM.integral]
  exact (simpleIntegral_boundedApprox_cauchy E_pvm f hf
    (Classical.choose hbdd) (Classical.choose_spec hbdd)).tendsto_limUnder

/-- Spectral sums of any uniformly convergent simple approximation converge to the bounded
spectral integral. In particular, the limit is independent of the chosen bound and approximation
sequence. -/
theorem PVM.tendsto_simpleIntegral_of_tendstoUniformly (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (s : ℕ → SimpleFunc ℝ ℂ)
    (hs : TendstoUniformly (fun n t => s n t) f Filter.atTop) :
    Filter.Tendsto (fun n => E_pvm.simpleIntegral (s n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) := by
  apply (E_pvm.tendsto_integralApprox f hf hbdd).congr_dist
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hUchosen := boundedApprox_tendstoUniformly f hf
    (Classical.choose hbdd) (Classical.choose_spec hbdd)
  rw [Metric.tendstoUniformly_iff] at hUchosen hs
  filter_upwards [hUchosen (ε / 4) (by linarith), hs (ε / 4) (by linarith)]
    with n hnchosen hn
  rw [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
  have hpoint : ∀ t,
      ‖boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t -
          s n t‖ ≤ ε / 2 := by
    intro t
    apply le_of_lt
    calc
      ‖boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t -
          s n t‖ =
          dist (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t)
            (s n t) := by
        rw [dist_eq_norm]
      _ ≤ dist
          (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t) (f t) +
          dist (f t) (s n t) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        apply add_lt_add
        · rw [dist_comm]
          exact hnchosen t
        · exact hn t
      _ = ε / 2 := by ring
  exact (E_pvm.norm_simpleIntegral_sub_le
    (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n)
    (s n) hpoint).trans_lt (by linarith)

private theorem PVM.tendsto_simpleIntegral_boundedApprox (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (C : ℝ) (hbddC : ∀ t, ‖f t‖ ≤ C) :
    Filter.Tendsto (fun n => E_pvm.simpleIntegral (boundedApprox f hf C hbddC n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) :=
  E_pvm.tendsto_simpleIntegral_of_tendstoUniformly f hf hbdd
    (boundedApprox f hf C hbddC) (boundedApprox_tendstoUniformly f hf C hbddC)

/-- A pointwise bound on an integrand bounds the operator norm of its spectral integral. -/
theorem PVM.norm_integral_le (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) {C : ℝ} (hbdd : ∀ t, ‖f t‖ ≤ C) :
    ‖E_pvm.integral f hf ⟨C, hbdd⟩‖ ≤ C := by
  have hlim := (E_pvm.tendsto_simpleIntegral_boundedApprox
    f hf ⟨C, hbdd⟩ C hbdd).norm
  apply le_of_tendsto' hlim
  intro n
  exact E_pvm.norm_simpleIntegral_le (boundedApprox f hf C hbdd n)
    (boundedApprox_norm_le f hf C hbdd n)

private theorem boundedApprox_mul_tendstoUniformly
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hbddf : ∀ t, ‖f t‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g) (D : ℝ) (hbddg : ∀ t, ‖g t‖ ≤ D) :
    TendstoUniformly
      (fun n t => boundedApprox f hf C hbddf n t * boundedApprox g hg D hbddg n t)
      (f * g) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let K := C + D + 1
  let δ := ε / K
  have hC : 0 ≤ C := bound_nonneg hbddf
  have hD : 0 ≤ D := bound_nonneg hbddg
  have hK : 0 < K := by
    dsimp [K]
    linarith
  have hδ : 0 < δ := div_pos hε hK
  have hUf := boundedApprox_tendstoUniformly f hf C hbddf
  have hUg := boundedApprox_tendstoUniformly g hg D hbddg
  rw [Metric.tendstoUniformly_iff] at hUf hUg
  filter_upwards [hUf δ hδ, hUg δ hδ] with n hfn hgn
  intro t
  change dist (f t * g t)
    (boundedApprox f hf C hbddf n t * boundedApprox g hg D hbddg n t) < ε
  rw [dist_comm, dist_eq_norm]
  have hdiffF : ‖boundedApprox f hf C hbddf n t - f t‖ ≤ δ := by
    apply le_of_lt
    rw [← dist_eq_norm]
    exact (dist_comm _ _).trans_lt (hfn t)
  have hdiffG : ‖boundedApprox g hg D hbddg n t - g t‖ ≤ δ := by
    apply le_of_lt
    rw [← dist_eq_norm]
    exact (dist_comm _ _).trans_lt (hgn t)
  calc
    ‖boundedApprox f hf C hbddf n t * boundedApprox g hg D hbddg n t - f t * g t‖ =
        ‖boundedApprox f hf C hbddf n t *
            (boundedApprox g hg D hbddg n t - g t) +
          (boundedApprox f hf C hbddf n t - f t) * g t‖ := by
      congr 1
      ring
    _ ≤ ‖boundedApprox f hf C hbddf n t *
          (boundedApprox g hg D hbddg n t - g t)‖ +
        ‖(boundedApprox f hf C hbddf n t - f t) * g t‖ := norm_add_le _ _
    _ = ‖boundedApprox f hf C hbddf n t‖ *
          ‖boundedApprox g hg D hbddg n t - g t‖ +
        ‖boundedApprox f hf C hbddf n t - f t‖ * ‖g t‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ C * δ + δ * D := by
      apply add_le_add
      · calc
          ‖boundedApprox f hf C hbddf n t‖ *
              ‖boundedApprox g hg D hbddg n t - g t‖ ≤
              C * ‖boundedApprox g hg D hbddg n t - g t‖ :=
            mul_le_mul_of_nonneg_right
              (boundedApprox_norm_le f hf C hbddf n t) (norm_nonneg _)
          _ ≤ C * δ := mul_le_mul_of_nonneg_left hdiffG hC
      · calc
          ‖boundedApprox f hf C hbddf n t - f t‖ * ‖g t‖ ≤ δ * ‖g t‖ :=
            mul_le_mul_of_nonneg_right hdiffF (norm_nonneg _)
          _ ≤ δ * D := mul_le_mul_of_nonneg_left (hbddg t) hδ.le
    _ = δ * (C + D) := by ring
    _ < δ * K := by
      apply mul_lt_mul_of_pos_left _ hδ
      dsimp [K]
      linarith
    _ = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt hK)

/-- Bounded spectral integration preserves pointwise multiplication. -/
theorem PVM.integral_mul (E_pvm : PVM E)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hbddg : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (hbddfg : ∃ C, ∀ t, ‖(f * g) t‖ ≤ C) :
    E_pvm.integral (f * g) (hf.mul hg) hbddfg =
      E_pvm.integral f hf hbddf * E_pvm.integral g hg hbddg := by
  let sf := boundedApprox f hf (Classical.choose hbddf) (Classical.choose_spec hbddf)
  let sg := boundedApprox g hg (Classical.choose hbddg) (Classical.choose_spec hbddg)
  have hUniform : TendstoUniformly (fun n t => (sf n * sg n) t) (f * g) Filter.atTop := by
    simpa only [SimpleFunc.mul_apply] using boundedApprox_mul_tendstoUniformly
      f hf (Classical.choose hbddf) (Classical.choose_spec hbddf)
      g hg (Classical.choose hbddg) (Classical.choose_spec hbddg)
  have hfgLimit := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (f * g) (hf.mul hg) hbddfg (fun n => sf n * sg n) hUniform
  have hprodLimit : Filter.Tendsto (fun n => E_pvm.simpleIntegral (sf n * sg n))
      Filter.atTop
      (nhds (E_pvm.integral f hf hbddf * E_pvm.integral g hg hbddg)) := by
    simpa only [E_pvm.simpleIntegral_mul] using
      (E_pvm.tendsto_integralApprox f hf hbddf).mul
        (E_pvm.tendsto_integralApprox g hg hbddg)
  exact tendsto_nhds_unique hfgLimit hprodLimit

/-- Bounded spectral integration preserves pointwise subtraction, independently of the bound
witnesses used in the three integrals. -/
theorem PVM.integral_sub (E_pvm : PVM E)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hbddg : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (hbddsub : ∃ C, ∀ t, ‖(f - g) t‖ ≤ C) :
    E_pvm.integral (f - g) (hf.sub hg) hbddsub =
      E_pvm.integral f hf hbddf - E_pvm.integral g hg hbddg := by
  let sf := boundedApprox f hf (Classical.choose hbddf) (Classical.choose_spec hbddf)
  let sg := boundedApprox g hg (Classical.choose hbddg) (Classical.choose_spec hbddg)
  have hUniform : TendstoUniformly (fun n t => (sf n - sg n) t) (f - g) Filter.atTop := by
    have h := (boundedApprox_tendstoUniformly f hf
      (Classical.choose hbddf) (Classical.choose_spec hbddf)).sub
      (boundedApprox_tendstoUniformly g hg
        (Classical.choose hbddg) (Classical.choose_spec hbddg))
    exact h
  have hsubLimit := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (f - g) (hf.sub hg) hbddsub (fun n => sf n - sg n) hUniform
  have hrightLimit : Filter.Tendsto (fun n => E_pvm.simpleIntegral (sf n - sg n))
      Filter.atTop
      (nhds (E_pvm.integral f hf hbddf - E_pvm.integral g hg hbddg)) := by
    simpa only [E_pvm.simpleIntegral_sub] using
      (E_pvm.tendsto_integralApprox f hf hbddf).sub
        (E_pvm.tendsto_integralApprox g hg hbddg)
  exact tendsto_nhds_unique hsubLimit hrightLimit
