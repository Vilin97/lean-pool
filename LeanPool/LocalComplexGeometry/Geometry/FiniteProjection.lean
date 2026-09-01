/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Coordinates
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Main
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Geometric finite projection of a prepared hypersurface

This module packages the genuine local finite-map conclusion of Weierstrass
preparation.  The source is the actual zero locus in an open vertical tube,
and properness is asserted over the open base neighborhood itself.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/-! ## Coordinate and zero-locus definitions -/

/-- Projection to the first `n` standard complex coordinates. -/
def dropLastCLM (n : ℕ) :
    ComplexEuclidean (n + 1) →L[ℂ] ComplexEuclidean n :=
  baseProjectionCLM n

/-- Append a distinguished last coordinate. -/
def appendLastCLE (n : ℕ) :
    (ComplexEuclidean n × ℂ) ≃L[ℂ] ComplexEuclidean (n + 1) :=
  (wptAmbientEquiv n).symm

@[simp]
theorem dropLastCLM_appendLastCLE (n : ℕ)
    (z : ComplexEuclidean n) (w : ℂ) :
    dropLastCLM n (appendLastCLE n (z, w)) = z := by
  simp [dropLastCLM, appendLastCLE, baseProjectionCLM]

theorem lastCoordinateCLM_appendLastCLE (n : ℕ)
    (z : ComplexEuclidean n) (w : ℂ) :
    lastCoordinateCLM n (appendLastCLE n (z, w)) = w := by
  simp [lastCoordinateCLM, appendLastCLE]

theorem appendLastCLE_dropLast_lastCoordinate (n : ℕ)
    (x : ComplexEuclidean (n + 1)) :
    appendLastCLE n (dropLastCLM n x, lastCoordinateCLM n x) = x := by
  exact (wptAmbientEquiv n).symm_apply_apply x

theorem wptAmbientEquiv_eq_dropLast_lastCoordinate (n : ℕ)
    (x : ComplexEuclidean (n + 1)) :
    wptAmbientEquiv n x =
      (dropLastCLM n x, lastCoordinateCLM n x) := by
  rfl

/-- Evaluation of a monic prepared polynomial in its base and last variables. -/
def preparedValue {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (z : ComplexEuclidean n) (w : ℂ) : ℂ :=
  w ^ d + ∑ i, a i z * w ^ (i : ℕ)

@[simp]
theorem preparedValue_eq_preparedPolynomial {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (z : ComplexEuclidean n) (w : ℂ) :
    preparedValue a z w =
      ClassicalComplexWPT.preparedPolynomial d a (z, w) :=
  rfl

/-- The zero locus of `F` in the open vertical tube `U × {‖w‖ < R}`. -/
abbrev LocalHypersurface {n : ℕ}
    (F : ComplexEuclidean (n + 1) → ℂ)
    (U : Set (ComplexEuclidean n)) (R : ℝ) :=
  {x : ComplexEuclidean (n + 1) //
    dropLastCLM n x ∈ U ∧
    ‖lastCoordinateCLM n x‖ < R ∧ F x = 0}

/-- Projection of the local hypersurface to its open base. -/
def localProjection {n : ℕ}
    (F : ComplexEuclidean (n + 1) → ℂ)
    (U : Set (ComplexEuclidean n)) (R : ℝ) :
    LocalHypersurface F U R → U :=
  fun x ↦ ⟨dropLastCLM n x.1, x.2.1⟩

theorem continuous_localProjection {n : ℕ}
    (F : ComplexEuclidean (n + 1) → ℂ)
    (U : Set (ComplexEuclidean n)) (R : ℝ) :
    Continuous (localProjection F U R) := by
  apply Continuous.subtype_mk
  exact (dropLastCLM n).continuous.comp continuous_subtype_val

/-! ## Audited geometric finite-projection predicate -/

/--
An explicit local finite projection, including analytic preparation on a tube,
vertical boundary control, finite fibers, surjectivity, and genuine properness
over the open base `U`.
-/
def HasGeometricFiniteProjection {n : ℕ}
    (F : ComplexEuclidean (n + 1) → ℂ) (d : ℕ) : Prop :=
  ∃ (a : Fin d → ComplexEuclidean n → ℂ)
      (u : ComplexEuclidean (n + 1) → ℂ)
      (U : Set (ComplexEuclidean n)) (R : ℝ),
    IsOpen U ∧ 0 ∈ U ∧ IsPreconnected U ∧ 0 < R ∧
    AnalyticOnNhd ℂ F
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R} ∧
    (∀ i, AnalyticOnNhd ℂ (a i) U) ∧
    AnalyticOnNhd ℂ u
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R} ∧
    (∀ i, a i 0 = 0) ∧
    (∀ x, dropLastCLM n x ∈ U → ‖lastCoordinateCLM n x‖ < R →
      F x = u x * preparedValue a
        (dropLastCLM n x) (lastCoordinateCLM n x)) ∧
    (∀ x, dropLastCLM n x ∈ U → ‖lastCoordinateCLM n x‖ < R →
      u x ≠ 0) ∧
    (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R → preparedValue a z w ≠ 0) ∧
    (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
      F (appendLastCLE n (z, w)) ≠ 0) ∧
    (∀ z ∈ U, Set.Finite
      {w : ℂ | ‖w‖ < R ∧ F (appendLastCLE n (z, w)) = 0}) ∧
    (∀ z ∈ U, Set.ncard
      {w : ℂ | ‖w‖ < R ∧ F (appendLastCLE n (z, w)) = 0} ≤ d) ∧
    Function.Surjective (localProjection F U R) ∧
    IsProperMap (localProjection F U R)

/-! ## The polynomial associated to one vertical fiber -/

/-- The prepared value at `z`, regarded as a polynomial in the last variable. -/
def preparedPolynomialAt {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    Polynomial ℂ :=
  Polynomial.X ^ d +
    ∑ i : Fin d, Polynomial.C (a i z) * Polynomial.X ^ (i : ℕ)

@[simp]
theorem preparedPolynomialAt_eval {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) (w : ℂ) :
    (preparedPolynomialAt a z).eval w = preparedValue a z w := by
  change (Polynomial.evalRingHom w) (preparedPolynomialAt a z) =
    preparedValue a z w
  unfold preparedPolynomialAt preparedValue
  rw [map_add, map_pow, map_sum]
  simp

theorem preparedPolynomialAt_monic {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    (preparedPolynomialAt a z).Monic := by
  apply Polynomial.monic_X_pow_add
  exact Polynomial.degree_sum_fin_lt (fun i ↦ a i z)

@[simp]
theorem preparedPolynomialAt_natDegree {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    (preparedPolynomialAt a z).natDegree = d := by
  unfold preparedPolynomialAt
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt
    (by simpa [Polynomial.degree_X_pow] using
      Polynomial.degree_sum_fin_lt (fun i ↦ a i z)),
    Polynomial.natDegree_X_pow]

theorem preparedValue_zero_set_finite {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    Set.Finite {w : ℂ | preparedValue a z w = 0} := by
  have hset : {w : ℂ | preparedValue a z w = 0} =
      (preparedPolynomialAt a z).rootSet ℂ := by
    ext w
    rw [(preparedPolynomialAt_monic a z).mem_rootSet]
    simp [Polynomial.aeval_def, preparedPolynomialAt_eval]
  rw [hset]
  exact (preparedPolynomialAt a z).rootSet_finite ℂ

theorem preparedValue_zero_set_ncard_le {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    Set.ncard {w : ℂ | preparedValue a z w = 0} ≤ d := by
  have hset : {w : ℂ | preparedValue a z w = 0} =
      (preparedPolynomialAt a z).rootSet ℂ := by
    ext w
    rw [(preparedPolynomialAt_monic a z).mem_rootSet]
    simp [Polynomial.aeval_def, preparedPolynomialAt_eval]
  rw [hset]
  simpa using Polynomial.ncard_rootSet_le (preparedPolynomialAt a z) ℂ

theorem preparedValue_exists_zero {n d : ℕ} (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    ∃ w : ℂ, preparedValue a z w = 0 := by
  have hdegree : (preparedPolynomialAt a z).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree
      (preparedPolynomialAt_monic a z).ne_zero,
      preparedPolynomialAt_natDegree]
    exact_mod_cast hd.ne'
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (preparedPolynomialAt a z) hdegree
  exact ⟨w, by simpa [Polynomial.IsRoot, preparedPolynomialAt_eval] using hw⟩

/-- A quantitative root bound for a monic polynomial with sufficiently small
lower coefficients. -/
theorem norm_lt_of_monic_sum_eq_zero_of_coeff_bound {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr : 0 < r) (b : Fin d → ℂ) (w : ℂ)
    (hb : ∀ i, ‖b i‖ < r ^ (d - (i : ℕ)) / (2 * (d : ℝ)))
    (hzero : w ^ d + ∑ i : Fin d, b i * w ^ (i : ℕ) = 0) :
    ‖w‖ < r := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  by_contra hwr
  have hrw : r ≤ ‖w‖ := le_of_not_gt hwr
  have hwpos : 0 < ‖w‖ := hr.trans_le hrw
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hterm (i : Fin d) :
      ‖b i‖ * ‖w‖ ^ (i : ℕ) < ‖w‖ ^ d / (2 * (d : ℝ)) := by
    have hpow : r ^ (d - (i : ℕ)) ≤ ‖w‖ ^ (d - (i : ℕ)) :=
      pow_le_pow_left₀ hr.le hrw _
    have hmul :
        r ^ (d - (i : ℕ)) * ‖w‖ ^ (i : ℕ) ≤ ‖w‖ ^ d := by
      calc
        r ^ (d - (i : ℕ)) * ‖w‖ ^ (i : ℕ) ≤
            ‖w‖ ^ (d - (i : ℕ)) * ‖w‖ ^ (i : ℕ) :=
          mul_le_mul_of_nonneg_right hpow (pow_nonneg (norm_nonneg w) _)
        _ = ‖w‖ ^ d := by
          rw [← pow_add, Nat.sub_add_cancel i.is_lt.le]
    calc
      ‖b i‖ * ‖w‖ ^ (i : ℕ) <
          (r ^ (d - (i : ℕ)) / (2 * (d : ℝ))) *
            ‖w‖ ^ (i : ℕ) :=
        mul_lt_mul_of_pos_right (hb i) (pow_pos hwpos _)
      _ = (r ^ (d - (i : ℕ)) * ‖w‖ ^ (i : ℕ)) /
          (2 * (d : ℝ)) := by ring
      _ ≤ ‖w‖ ^ d / (2 * (d : ℝ)) := by
        exact div_le_div_of_nonneg_right hmul (by positivity)
  have hsumlt :
      (∑ i : Fin d, ‖b i‖ * ‖w‖ ^ (i : ℕ)) < ‖w‖ ^ d / 2 := by
    calc
      (∑ i : Fin d, ‖b i‖ * ‖w‖ ^ (i : ℕ)) <
          ∑ _i : Fin d, ‖w‖ ^ d / (2 * (d : ℝ)) := by
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun i _ ↦ hterm i)
      _ = ‖w‖ ^ d / 2 := by
        rw [Fin.sum_const, nsmul_eq_mul]
        field_simp
  have hpowle : ‖w‖ ^ d ≤
      ∑ i : Fin d, ‖b i‖ * ‖w‖ ^ (i : ℕ) := by
    have heq : w ^ d = -∑ i : Fin d, b i * w ^ (i : ℕ) :=
      eq_neg_of_add_eq_zero_left hzero
    calc
      ‖w‖ ^ d = ‖w ^ d‖ := by rw [norm_pow]
      _ = ‖∑ i : Fin d, b i * w ^ (i : ℕ)‖ := by rw [heq, norm_neg]
      _ ≤ ∑ i : Fin d, ‖b i * w ^ (i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ i : Fin d, ‖b i‖ * ‖w‖ ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, norm_pow]
  have hpnonneg : 0 ≤ ‖w‖ ^ d := pow_nonneg (norm_nonneg w) d
  linarith

/-! ## A compact-preimage criterion for the local projection -/

/--
If all zeros in the radius-`R` tube actually lie in a fixed smaller closed
disc, then projection of the zero locus to the open base is proper.
-/
theorem isProperMap_localProjection_of_inner_bound {n : ℕ}
    {F : ComplexEuclidean (n + 1) → ℂ}
    {U : Set (ComplexEuclidean n)} {r R : ℝ}
    (_hr : 0 ≤ r) (hrR : r < R)
    (hF : ContinuousOn F
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R})
    (hbound : ∀ x, dropLastCLM n x ∈ U →
      ‖lastCoordinateCLM n x‖ < R → F x = 0 →
      ‖lastCoordinateCLM n x‖ ≤ r) :
    IsProperMap (localProjection F U R) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_localProjection F U R, ?_⟩
  intro K hK
  let K₀ : Set (ComplexEuclidean n) := Subtype.val '' K
  let C : Set (ComplexEuclidean (n + 1)) :=
    appendLastCLE n '' (K₀ ×ˢ Metric.closedBall (0 : ℂ) r)
  have hK₀ : IsCompact K₀ := hK.image continuous_subtype_val
  have hC : IsCompact C :=
    (hK₀.prod (isCompact_closedBall (0 : ℂ) r)).image
      (appendLastCLE n).continuous
  have hC_mem (x : ComplexEuclidean (n + 1)) :
      x ∈ C ↔ dropLastCLM n x ∈ K₀ ∧ ‖lastCoordinateCLM n x‖ ≤ r := by
    constructor
    · rintro ⟨⟨z, w⟩, ⟨hpK, hpR⟩, rfl⟩
      have hpR' : ‖w‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hpR
      simpa only [dropLastCLM_appendLastCLE,
        lastCoordinateCLM_appendLastCLE] using ⟨hpK, hpR'⟩
    · rintro ⟨hxK, hxR⟩
      refine ⟨(dropLastCLM n x, lastCoordinateCLM n x), ?_, ?_⟩
      · exact ⟨hxK, by simpa [Metric.mem_closedBall, dist_zero_right] using hxR⟩
      · exact appendLastCLE_dropLast_lastCoordinate n x
  have hC_tube : C ⊆
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R} := by
    intro x hx
    obtain ⟨hxK, hxR⟩ := (hC_mem x).1 hx
    constructor
    · obtain ⟨z, hzK, hz⟩ := hxK
      rw [← hz]
      exact z.property
    · exact hxR.trans_lt hrR
  have hclosed : IsClosed (C ∩ F ⁻¹' {0}) :=
    (hF.mono hC_tube).preimage_isClosed_of_isClosed hC.isClosed
      isClosed_singleton
  have hD : IsCompact (C ∩ F ⁻¹' {0}) :=
    hC.of_isClosed_subset hclosed Set.inter_subset_left
  rw [Subtype.isCompact_iff]
  rw [show Subtype.val '' (localProjection F U R ⁻¹' K) =
      C ∩ F ⁻¹' {0} by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      have hyU := y.property.1
      have hyR := y.property.2.1
      have hyF := y.property.2.2
      have hyr := hbound y hyU hyR hyF
      constructor
      · apply (hC_mem y).2
        refine ⟨?_, hyr⟩
        exact ⟨localProjection F U R y, hyK, rfl⟩
      · exact hyF
    · rintro ⟨hxC, hxF⟩
      obtain ⟨hxK, hxr⟩ := (hC_mem x).1 hxC
      obtain ⟨z, hzK, hz⟩ := hxK
      have hxU : dropLastCLM n x ∈ U := hz ▸ z.property
      have hxR : ‖lastCoordinateCLM n x‖ < R := hxr.trans_lt hrR
      let y : LocalHypersurface F U R := ⟨x, hxU, hxR, hxF⟩
      refine ⟨y, ?_, rfl⟩
      change localProjection F U R y ∈ K
      have : localProjection F U R y = z := by
        apply Subtype.ext
        exact hz.symm
      simpa [this] using hzK]
  exact hD

/-! ## From an open preparation witness to finite projection -/

/--
A positive-degree preparation on an open neighborhood yields the full audited
geometric finite-projection predicate after shrinking to a product tube.
-/
theorem hasGeometricFiniteProjection_of_open_preparation {n d : ℕ}
    (hd : 0 < d) {f : ClassicalComplexWPT.Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (u : ClassicalComplexWPT.Ambient n → ℂ)
    (s : Set (ClassicalComplexWPT.Ambient n))
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hu : AnalyticAt ℂ u 0)
    (hs : IsOpen s) (hs0 : (0 : ClassicalComplexWPT.Ambient n) ∈ s)
    (hunit : ∀ x ∈ s, u x ≠ 0)
    (hfactor : ∀ x ∈ s,
      f x = u x * ClassicalComplexWPT.preparedPolynomial d a x) :
    HasGeometricFiniteProjection
      (fun x : ComplexEuclidean (n + 1) ↦ f (wptAmbientEquiv n x)) d := by
  let F : ComplexEuclidean (n + 1) → ℂ :=
    fun x ↦ f (wptAmbientEquiv n x)
  let u' : ComplexEuclidean (n + 1) → ℂ :=
    fun x ↦ u (wptAmbientEquiv n x)
  have hgood : {x : ClassicalComplexWPT.Ambient n |
      x ∈ s ∧ AnalyticAt ℂ f x ∧ AnalyticAt ℂ u x} ∈ 𝓝 0 := by
    filter_upwards [hs.mem_nhds hs0, hf.eventually_analyticAt,
      hu.eventually_analyticAt] with x hxs hfx hux
    exact ⟨hxs, hfx, hux⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := ε / 4
  let R : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : r < R := by dsimp [r, R]; linarith
  have hcoeffNear : {z : ComplexEuclidean n | ∀ i,
      AnalyticAt ℂ (a i) z ∧
      ‖a i z‖ < r ^ (d - (i : ℕ)) / (2 * (d : ℝ))} ∈ 𝓝 0 := by
    change ∀ᶠ z in 𝓝 0, ∀ i, AnalyticAt ℂ (a i) z ∧
      ‖a i z‖ < r ^ (d - (i : ℕ)) / (2 * (d : ℝ))
    apply Filter.eventually_all.mpr
    intro i
    have hc : ‖a i (0 : ComplexEuclidean n)‖ <
        r ^ (d - (i : ℕ)) / (2 * (d : ℝ)) := by
      rw [ha0 i, norm_zero]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    exact (ha i).eventually_analyticAt.and
      ((ha i).continuousAt.norm.eventually_lt continuousAt_const hc)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hcoeffNear
  let ρ : ℝ := min R δ
  let U : Set (ComplexEuclidean n) := Metric.ball 0 ρ
  have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hR hδ
  have hρR : ρ ≤ R := by dsimp [ρ]; exact min_le_left _ _
  have hρδ : ρ ≤ δ := by dsimp [ρ]; exact min_le_right _ _
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hU0 : (0 : ComplexEuclidean n) ∈ U := Metric.mem_ball_self hρ
  have hUpre : IsPreconnected U := (convex_ball (0 : ComplexEuclidean n) ρ).isPreconnected
  have hcoeff {z : ComplexEuclidean n} (hz : z ∈ U) (i : Fin d) :
      AnalyticAt ℂ (a i) z ∧
        ‖a i z‖ < r ^ (d - (i : ℕ)) / (2 * (d : ℝ)) := by
    apply hδsub
    have hzρ : dist z 0 < ρ := by simpa [U, Metric.mem_ball] using hz
    exact Metric.mem_ball.mpr (hzρ.trans_le hρδ)
  have htube_ball {x : ComplexEuclidean (n + 1)}
      (hxU : dropLastCLM n x ∈ U)
      (hxR : ‖lastCoordinateCLM n x‖ < R) :
      wptAmbientEquiv n x ∈ Metric.ball
        (0 : ClassicalComplexWPT.Ambient n) ε := by
    have hxbaseρ : ‖dropLastCLM n x‖ < ρ := by
      simpa [U, Metric.mem_ball, dist_zero_right] using hxU
    have hxbaseR : ‖dropLastCLM n x‖ < R := hxbaseρ.trans_le hρR
    have hRε : R < ε := by dsimp [R]; linarith
    simpa [Metric.mem_ball, dist_zero_right, Prod.norm_def, dropLastCLM,
      lastCoordinateCLM] using (max_lt hxbaseR hxR).trans hRε
  have hFanalytic : AnalyticOnNhd ℂ F
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R} := by
    intro x hx
    have hfx := (hεsub (htube_ball hx.1 hx.2)).2.1
    simpa [F, Function.comp_def] using hfx.compContinuousLinearMap
      (u := (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
        ClassicalComplexWPT.Ambient n)) (x := x)
  have huAnalytic : AnalyticOnNhd ℂ u'
      {x | dropLastCLM n x ∈ U ∧ ‖lastCoordinateCLM n x‖ < R} := by
    intro x hx
    have hux := (hεsub (htube_ball hx.1 hx.2)).2.2
    simpa [u', Function.comp_def] using hux.compContinuousLinearMap
      (u := (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
        ClassicalComplexWPT.Ambient n)) (x := x)
  have hfactor' (x : ComplexEuclidean (n + 1))
      (hxU : dropLastCLM n x ∈ U)
      (hxR : ‖lastCoordinateCLM n x‖ < R) :
      F x = u' x * preparedValue a
        (dropLastCLM n x) (lastCoordinateCLM n x) := by
    have hxs := (hεsub (htube_ball hxU hxR)).1
    change f (wptAmbientEquiv n x) = u (wptAmbientEquiv n x) *
      preparedValue a (dropLastCLM n x) (lastCoordinateCLM n x)
    rw [preparedValue_eq_preparedPolynomial]
    simpa only [wptAmbientEquiv_eq_dropLast_lastCoordinate] using
      hfactor (wptAmbientEquiv n x) hxs
  have hunit' (x : ComplexEuclidean (n + 1))
      (hxU : dropLastCLM n x ∈ U)
      (hxR : ‖lastCoordinateCLM n x‖ < R) : u' x ≠ 0 := by
    exact hunit (wptAmbientEquiv n x) (hεsub (htube_ball hxU hxR)).1
  have hroot (z : ComplexEuclidean n) (hz : z ∈ U) (w : ℂ)
      (hw : preparedValue a z w = 0) : ‖w‖ < r := by
    exact norm_lt_of_monic_sum_eq_zero_of_coeff_bound hd hr
      (fun i ↦ a i z) w (fun i ↦ (hcoeff hz i).2) hw
  have hfiberSubset (z : ComplexEuclidean n) (hz : z ∈ U) :
      {w : ℂ | ‖w‖ < R ∧ F (appendLastCLE n (z, w)) = 0} ⊆
        {w : ℂ | preparedValue a z w = 0} := by
    intro w hw
    have hbase : dropLastCLM n (appendLastCLE n (z, w)) ∈ U := by
      rw [dropLastCLM_appendLastCLE]
      exact hz
    have hlast : ‖lastCoordinateCLM n (appendLastCLE n (z, w))‖ < R := by
      rw [lastCoordinateCLM_appendLastCLE]
      exact hw.1
    have hfac := hfactor' (appendLastCLE n (z, w)) hbase hlast
    have hfac' : F (appendLastCLE n (z, w)) =
        u' (appendLastCLE n (z, w)) * preparedValue a z w := by
      simpa only [dropLastCLM_appendLastCLE,
        lastCoordinateCLM_appendLastCLE] using hfac
    have hmul : u' (appendLastCLE n (z, w)) * preparedValue a z w = 0 := by
      rw [← hfac']
      exact hw.2
    exact (mul_eq_zero.mp hmul).resolve_left
      (hunit' (appendLastCLE n (z, w)) hbase hlast)
  have hboundary : ∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
      preparedValue a z w ≠ 0 := by
    intro z hz w hwR hwzero
    have := hroot z hz w hwzero
    linarith
  have hFboundary : ∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
      F (appendLastCLE n (z, w)) ≠ 0 := by
    intro z hz w hwR hFzero
    have hzbaseρ : ‖z‖ < ρ := by
      simpa [U, Metric.mem_ball, dist_zero_right] using hz
    have hzbaseR : ‖z‖ < R := hzbaseρ.trans_le hρR
    have hRε : R < ε := by dsimp [R]; linarith
    have happ : wptAmbientEquiv n (appendLastCLE n (z, w)) = (z, w) :=
      (wptAmbientEquiv n).apply_symm_apply (z, w)
    have hboundaryBall : wptAmbientEquiv n (appendLastCLE n (z, w)) ∈
        Metric.ball (0 : ClassicalComplexWPT.Ambient n) ε := by
      rw [happ]
      simpa [Metric.mem_ball, dist_zero_right, Prod.norm_def, hwR] using
          (max_lt (hzbaseR.trans hRε) hRε)
    have hxs := (hεsub hboundaryBall).1
    have hfac := hfactor (wptAmbientEquiv n (appendLastCLE n (z, w))) hxs
    have hunitBoundary :=
      hunit (wptAmbientEquiv n (appendLastCLE n (z, w))) hxs
    have hfacBoundary : F (appendLastCLE n (z, w)) =
        u' (appendLastCLE n (z, w)) * preparedValue a z w := by
      change f (wptAmbientEquiv n (appendLastCLE n (z, w))) =
        u (wptAmbientEquiv n (appendLastCLE n (z, w))) * preparedValue a z w
      rw [preparedValue_eq_preparedPolynomial, happ]
      simpa only [happ] using hfac
    have hmul : u' (appendLastCLE n (z, w)) * preparedValue a z w = 0 := by
      rw [← hfacBoundary]
      exact hFzero
    exact hboundary z hz w hwR
      ((mul_eq_zero.mp hmul).resolve_left hunitBoundary)
  have hfiberFinite : ∀ z ∈ U, Set.Finite
      {w : ℂ | ‖w‖ < R ∧ F (appendLastCLE n (z, w)) = 0} := by
    intro z hz
    exact (preparedValue_zero_set_finite a z).subset (hfiberSubset z hz)
  have hfiberNcard : ∀ z ∈ U, Set.ncard
      {w : ℂ | ‖w‖ < R ∧ F (appendLastCLE n (z, w)) = 0} ≤ d := by
    intro z hz
    exact (Set.ncard_le_ncard (hfiberSubset z hz)
      (preparedValue_zero_set_finite a z)).trans
        (preparedValue_zero_set_ncard_le a z)
  have hsurj : Function.Surjective (localProjection F U R) := by
    intro z
    obtain ⟨w, hw⟩ := preparedValue_exists_zero hd a z
    have hwr : ‖w‖ < r := hroot z z.property w hw
    have hwR : ‖w‖ < R := hwr.trans hrR
    have hbase : dropLastCLM n (appendLastCLE n (z, w)) ∈ U := by
      rw [dropLastCLM_appendLastCLE]
      exact z.property
    have hlast : ‖lastCoordinateCLM n (appendLastCLE n (z, w))‖ < R := by
      rw [lastCoordinateCLM_appendLastCLE]
      exact hwR
    have hFzero : F (appendLastCLE n (z, w)) = 0 := by
      rw [hfactor' (appendLastCLE n (z, w)) hbase hlast]
      simp only [dropLastCLM_appendLastCLE,
        lastCoordinateCLM_appendLastCLE, hw, mul_zero]
    let x : LocalHypersurface F U R :=
      ⟨appendLastCLE n (z, w), hbase, hlast, hFzero⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simp [x, localProjection]
  have hinner : ∀ x, dropLastCLM n x ∈ U →
      ‖lastCoordinateCLM n x‖ < R → F x = 0 →
      ‖lastCoordinateCLM n x‖ ≤ r := by
    intro x hxU hxR hxF
    have hp : preparedValue a (dropLastCLM n x) (lastCoordinateCLM n x) = 0 := by
      have hmul : u' x * preparedValue a
          (dropLastCLM n x) (lastCoordinateCLM n x) = 0 := by
        rw [← hfactor' x hxU hxR]
        exact hxF
      exact (mul_eq_zero.mp hmul).resolve_left (hunit' x hxU hxR)
    exact (hroot (dropLastCLM n x) hxU (lastCoordinateCLM n x) hp).le
  have hproper : IsProperMap (localProjection F U R) :=
    isProperMap_localProjection_of_inner_bound hr.le hrR
      hFanalytic.continuousOn hinner
  change HasGeometricFiniteProjection F d
  exact ⟨a, u', U, R, hUopen, hU0, hUpre, hR,
    hFanalytic, (fun i z hz ↦ (hcoeff hz i).1), huAnalytic, ha0,
    hfactor', hunit', hboundary, hFboundary, hfiberFinite, hfiberNcard,
    hsurj, hproper⟩

/-- Positive exact order, through the pinned WPT theorem, gives a genuine
geometric finite projection in the standard coordinate model. -/
theorem hasGeometricFiniteProjection_of_exactOrder {n d : ℕ} (hd : 0 < d)
    {f : ClassicalComplexWPT.Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (horder : ClassicalComplexWPT.ExactOrderInLastVariable f d) :
    HasGeometricFiniteProjection
      (fun x : ComplexEuclidean (n + 1) ↦ f (wptAmbientEquiv n x)) d := by
  obtain ⟨a, u, s, hprep, hs, hs0, hunit, hfactor⟩ :=
    ClassicalComplexWPT.exists_open_preparation_neighborhood n d f hf horder
  exact hasGeometricFiniteProjection_of_open_preparation hd hf a u s
    hprep.1 hprep.2.1 hprep.2.2.1 hs hs0 hunit hfactor

end

end LocalComplexGeometry
