/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.PairCapture
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.AssemblyPieces
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ENNRealBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Constants
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.OverlapIntegral

/-!
# Gagliardo-to-Besov direction of the fractional comparison

This file proves the lower comparison: the `p`-th power of the fractional
Sobolev (Gagliardo) seminorm of `u` on a triadic cube `Q` is controlled, up
to a dimensional constant, by the supremum of the `p`-th powers of the
finite-depth overlapping Besov seminorms.

The proof decomposes the off-diagonal product cube into triadic distance
shells, captures each shell pair inside an overlapping center cube at the
matching depth (G3, `exists_centersAtDepth_pair_mem`), splits the difference
through the cube average (triangle inequality plus `L^p` bookkeeping), and
resums the shells into the depth seminorms.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory ScalarOverlap
open scoped ENNReal BigOperators

variable {d : ℕ}

/-- Constant for the Gagliardo-to-Besov direction; depends only on `d`.

Accounting (everything is measured per `pr := p.toReal ≥ 1`-th power):

* `2 ^ pr * 2 ≤ 4 ^ pr` from the triangle split through the cube average
  (two symmetric one-variable slots);
* `9 ^ (s·pr + d) ≤ 9 ^ pr * (9 ^ d) ^ pr` from comparing the shell radius
  `c_Q / 3 ^ (n+1)` with the depth side length `c_Q / 3 ^ j`, `n ≤ j + 1`
  (using `s ≤ 1`);
* `3 ^ d ≤ (3 ^ d) ^ pr` from the overlapping center count
  `card ≤ (3 ^ d) ^ (j + 1)` against the depth volume `3 ^ (j d)`;
* a final flat factor `2 ≤ 2 ^ pr` from the shell-to-depth reindexing
  `j = n - 1`.

Total: `(2 * (4 * 9 * 9 ^ d * 3 ^ d)) ^ pr = (2 ^ 3 * 3 ^ (3 d + 2)) ^ pr`. -/
noncomputable def gagliardoBesovLowerConstant (d : ℕ) : ℝ≥0∞ :=
  2 ^ 3 * 3 ^ (3 * d + 2)

/-- Diameter bound for the small triadic cube: two points of `cubeSet Q` are
at `sup`-distance at most the side length `cubeScaleFactor Q`. -/
theorem dist_le_cubeScaleFactor_of_mem_cubeSet {Q : TriadicCube d} {x y : Vec d}
    (hx : x ∈ Homogenization.cubeSet Q) (hy : y ∈ Homogenization.cubeSet Q) :
    dist x y ≤ cubeScaleFactor Q := by
  have hc : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  refine (dist_pi_le_iff hc.le).2 fun i => ?_
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hy1, hy2⟩ := hy i
  have hdiff : ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q -
      ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q = cubeScaleFactor Q := by
    ring
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- Triadic distance shell adapted to the cube `Q`: pairs at distance in
`(c_Q / 3 ^ (n+1), c_Q / 3 ^ n]`. -/
def shellSet (Q : TriadicCube d) (n : ℕ) : Set (Vec d × Vec d) :=
  {z | cubeScaleFactor Q / 3 ^ (n + 1) < dist z.1 z.2 ∧
    dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ n}

theorem measurableSet_shellSet (Q : TriadicCube d) (n : ℕ) :
    MeasurableSet (shellSet Q n) := by
  have h1 : IsOpen {z : Vec d × Vec d |
      cubeScaleFactor Q / 3 ^ (n + 1) < dist z.1 z.2} :=
    isOpen_lt continuous_const continuous_dist
  have h2 : IsClosed {z : Vec d × Vec d |
      dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ n} :=
    isClosed_le continuous_dist continuous_const
  exact h1.measurableSet.inter h2.measurableSet

/-- Every off-diagonal pair of `Q` lies in some shell. -/
theorem exists_mem_shellSet {Q : TriadicCube d} {z : Vec d × Vec d}
    (hz1 : z.1 ∈ Homogenization.cubeSet Q) (hz2 : z.2 ∈ Homogenization.cubeSet Q)
    (hne : z.1 ≠ z.2) : ∃ n : ℕ, z ∈ shellSet Q n := by
  classical
  have hc : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hd : (0 : ℝ) < dist z.1 z.2 := dist_pos.2 hne
  have hP : ∃ n : ℕ, cubeScaleFactor Q / 3 ^ (n + 1) < dist z.1 z.2 := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hd hc)
      (by norm_num : (1 / 3 : ℝ) < 1)
    refine ⟨m, ?_⟩
    have hpow : ((1 / 3 : ℝ)) ^ m * cubeScaleFactor Q =
        cubeScaleFactor Q / 3 ^ m := by
      rw [one_div, inv_pow]
      ring
    have hlt : cubeScaleFactor Q / 3 ^ m < dist z.1 z.2 := by
      calc cubeScaleFactor Q / 3 ^ m
          = (1 / 3 : ℝ) ^ m * cubeScaleFactor Q := hpow.symm
        _ < dist z.1 z.2 / cubeScaleFactor Q * cubeScaleFactor Q :=
            mul_lt_mul_of_pos_right hm hc
        _ = dist z.1 z.2 := div_mul_cancel₀ _ hc.ne'
    refine lt_of_le_of_lt ?_ hlt
    exact div_le_div_of_nonneg_left hc.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m))
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  cases h0 : Nat.find hP with
  | zero =>
      simpa using dist_le_cubeScaleFactor_of_mem_cubeSet hz1 hz2
  | succ m =>
      have hlt : m < Nat.find hP := by omega
      exact not_lt.1 (Nat.find_min hP hlt)

/-- The kernel integrand vanishes on the diagonal (junk value `0 ^ (-a) = 0`). -/
private theorem setLIntegral_diagonal_eq_zero {a : ℝ} (ha : a ≠ 0)
    (F : Vec d × Vec d → ℝ≥0∞) (ν : Measure (Vec d × Vec d)) :
    (∫⁻ z in {z : Vec d × Vec d | z.1 = z.2},
      ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z ∂ν) = 0 := by
  refine setLIntegral_eq_zero
    ((isClosed_eq continuous_fst continuous_snd).measurableSet) ?_
  intro z hz
  have hz' : z.1 = z.2 := hz
  simp [hz', Real.zero_rpow (neg_ne_zero.2 ha)]

/-- Shell decomposition: the kernel integral over `Q ×ˢ Q` is at most the sum
of its restrictions to the triadic shells (the diagonal contributes nothing). -/
private theorem setLIntegral_prodCube_le_tsum_shell {Q : TriadicCube d}
    {a : ℝ} (ha : a ≠ 0) (F : Vec d × Vec d → ℝ≥0∞) :
    (∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
        ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      ∑' n : ℕ,
        ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
            shellSet Q n,
          ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z
          ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  set ν : Measure (Vec d × Vec d) :=
    MeasureTheory.volume.prod MeasureTheory.volume
  set QQ : Set (Vec d × Vec d) :=
    Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q
  set g : Vec d × Vec d → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z
  have hsub : QQ ⊆ {z : Vec d × Vec d | z.1 = z.2} ∪ ⋃ n, QQ ∩ shellSet Q n := by
    intro z hz
    by_cases hdiag : z.1 = z.2
    · exact Or.inl hdiag
    · refine Or.inr (Set.mem_iUnion.2 ?_)
      obtain ⟨n, hn⟩ := exists_mem_shellSet hz.1 hz.2 hdiag
      exact ⟨n, hz, hn⟩
  calc (∫⁻ z in QQ, g z ∂ν)
      ≤ ∫⁻ z in {z : Vec d × Vec d | z.1 = z.2} ∪ ⋃ n, QQ ∩ shellSet Q n,
          g z ∂ν := lintegral_mono_set hsub
    _ ≤ (∫⁻ z in {z : Vec d × Vec d | z.1 = z.2}, g z ∂ν) +
          ∫⁻ z in ⋃ n, QQ ∩ shellSet Q n, g z ∂ν :=
        lintegral_union_le _ _ _
    _ ≤ 0 + ∑' n : ℕ, ∫⁻ z in QQ ∩ shellSet Q n, g z ∂ν :=
        add_le_add (le_of_eq (setLIntegral_diagonal_eq_zero ha F ν))
          (lintegral_iUnion_le _ _)
    _ = ∑' n : ℕ, ∫⁻ z in QQ ∩ shellSet Q n, g z ∂ν := zero_add _

/-- Step 1: the `p`-th power of the Gagliardo seminorm as a normalized kernel
integral over the product cube. -/
private theorem gagliardo_rpow_eq_lintegral {Q : TriadicCube d} {s : ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (u : Vec d → ℝ) :
    cubeGagliardoESeminorm Q s p u ^ p.toReal =
      ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
          ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
            ‖u z.1 - u z.2‖ₑ ^ p.toReal
          ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [Internal.cubeGagliardoESeminorm_eq_lintegral hp0 hpt,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one]
  rw [lintegral_gagliardoCubeMeasure_eq]
  congr 1
  exact lintegral_congr fun z => enorm_gagliardoKernel_rpow s hp0 hpt u z

/-- G3 packaging: each pair of the `n`-th shell of `Q ×ˢ Q` is captured by an
overlapping center cube at depth `n - 1`. -/
private theorem shell_capture {Q : TriadicCube d} {n : ℕ}
    {z : Vec d × Vec d}
    (hz : z ∈ (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
      shellSet Q n) :
    ∃ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
      z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S := by
  obtain ⟨hzQ, hzs⟩ := hz
  have hz1 : z.1 ∈ Homogenization.cubeSet Q := hzQ.1
  have hz2 : z.2 ∈ Homogenization.cubeSet Q := hzQ.2
  cases n with
  | zero =>
      refine ⟨middleChildCube Q, ?_, ?_, ?_⟩
      · rw [centersAtDepth_zero]
        exact Finset.mem_singleton_self _
      · rw [cubeSet_middleChildCube_eq_cubeSet]
        exact hz1
      · rw [cubeSet_middleChildCube_eq_cubeSet]
        exact hz2
  | succ m =>
      have hdist : dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ (m + 1) := hzs.2
      obtain ⟨S, hS, hxS, hyS⟩ :=
        exists_centersAtDepth_pair_mem hz1 hz2 hdist
      exact ⟨S, hS, hxS, hyS⟩

/-- The shell integral is at most the sum of the integrals over the products
of the capturing overlapping cubes at depth `n - 1`. -/
private theorem shell_setLIntegral_le_sum {Q : TriadicCube d} (n : ℕ)
    (F : Vec d × Vec d → ℝ≥0∞) :
    (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n,
      F z ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      ∑ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
        ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
          F z ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  set ν : Measure (Vec d × Vec d) :=
    MeasureTheory.volume.prod MeasureTheory.volume
  set C : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q (n - 1)
  have hsub : (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
      shellSet Q n ⊆
      ⋃ S : C, ScalarOverlap.cubeSet (S : TriadicCube d) ×ˢ
        ScalarOverlap.cubeSet (S : TriadicCube d) := by
    intro z hz
    obtain ⟨S, hS, hzS⟩ := shell_capture hz
    exact Set.mem_iUnion.2 ⟨⟨S, hS⟩, hzS⟩
  calc (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n, F z ∂ν)
      ≤ ∫⁻ z in ⋃ S : C, ScalarOverlap.cubeSet (S : TriadicCube d) ×ˢ
          ScalarOverlap.cubeSet (S : TriadicCube d), F z ∂ν :=
        lintegral_mono_set hsub
    _ ≤ ∑' S : C, ∫⁻ z in ScalarOverlap.cubeSet (S : TriadicCube d) ×ˢ
          ScalarOverlap.cubeSet (S : TriadicCube d), F z ∂ν :=
        lintegral_iUnion_le _ _
    _ = ∑ S ∈ C, ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
          F z ∂ν := by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort C (fun S =>
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, F z ∂ν)

/-- On the `n`-th shell the kernel weight is bounded by its value at the
inner shell radius, which can then be pulled out of the integral. -/
private theorem shell_setLIntegral_kernel_le {Q : TriadicCube d} {n : ℕ}
    {a : ℝ} (ha : 0 < a) {F : Vec d × Vec d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n,
      ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-a)) *
        ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
            shellSet Q n,
          F z ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hb : (0 : ℝ) < cubeScaleFactor Q / 3 ^ (n + 1) := by
    have := cubeScaleFactor_pos' Q
    positivity
  have hAn : MeasurableSet
      ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n) :=
    ((Homogenization.measurableSet_cubeSet Q).prod
      (Homogenization.measurableSet_cubeSet Q)).inter
      (measurableSet_shellSet Q n)
  have hmono : ∀ z ∈ (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
      shellSet Q n,
      ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z ≤
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-a)) * F z := by
    intro z hz
    have h1 : cubeScaleFactor Q / 3 ^ (n + 1) < dist z.1 z.2 := hz.2.1
    have h2 : dist z.1 z.2 ^ (-a) ≤ (cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hb h1.le (neg_nonpos.2 ha.le)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl
  calc (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n,
      ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * F z
      ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      ≤ ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
          shellSet Q n,
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-a)) * F z
        ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        setLIntegral_mono' hAn hmono
    _ = ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-a)) *
        ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
            shellSet Q n,
          F z ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        lintegral_const_mul _ hF

/-- Two-term power-mean inequality in `ℝ≥0∞`: `(A + B)^pr ≤ 2^pr (A^pr + B^pr)`. -/
private theorem rpow_add_le_two_rpow_mul {pr : ℝ} (hpr : 0 ≤ pr) (A B : ℝ≥0∞) :
    (A + B) ^ pr ≤ 2 ^ pr * (A ^ pr + B ^ pr) := by
  have hmax : A + B ≤ 2 * max A B := by
    rw [two_mul]
    exact add_le_add (le_max_left A B) (le_max_right A B)
  have hmaxpow : (max A B) ^ pr ≤ A ^ pr + B ^ pr := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]
      exact le_add_self
    · rw [max_eq_left h]
      exact le_self_add
  calc (A + B) ^ pr ≤ (2 * max A B) ^ pr := ENNReal.rpow_le_rpow hmax hpr
    _ = 2 ^ pr * (max A B) ^ pr := ENNReal.mul_rpow_of_nonneg _ _ hpr
    _ ≤ 2 ^ pr * (A ^ pr + B ^ pr) := by gcongr

/-- Pointwise triangle split of the difference power through a constant. -/
private theorem enorm_sub_rpow_le {pr : ℝ} (hpr : 0 ≤ pr) (u : Vec d → ℝ)
    (c : ℝ) (z : Vec d × Vec d) :
    ‖u z.1 - u z.2‖ₑ ^ pr ≤
      2 ^ pr * (‖u z.1 - c‖ₑ ^ pr + ‖u z.2 - c‖ₑ ^ pr) := by
  have hsplit : ‖u z.1 - u z.2‖ₑ ≤ ‖u z.1 - c‖ₑ + ‖u z.2 - c‖ₑ := by
    have hrw : u z.1 - u z.2 = (u z.1 - c) - (u z.2 - c) := by ring
    rw [hrw]
    exact enorm_sub_le
  calc ‖u z.1 - u z.2‖ₑ ^ pr
      ≤ (‖u z.1 - c‖ₑ + ‖u z.2 - c‖ₑ) ^ pr := ENNReal.rpow_le_rpow hsplit hpr
    _ ≤ 2 ^ pr * (‖u z.1 - c‖ₑ ^ pr + ‖u z.2 - c‖ₑ ^ pr) :=
        rpow_add_le_two_rpow_mul hpr _ _

/-- One-variable integrand over the product set, first slot. -/
private theorem lintegral_prod_fst_eq {E : Set (Vec d)} {g : Vec d → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ z in E ×ˢ E, g z.1
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) =
      MeasureTheory.volume E * ∫⁻ x in E, g x ∂MeasureTheory.volume := by
  rw [← Measure.prod_restrict]
  rw [lintegral_prod (fun z => g z.1) ((hg.comp measurable_fst).aemeasurable)]
  have hinner : ∀ x : Vec d,
      (∫⁻ _ : Vec d, g x ∂(MeasureTheory.volume.restrict E)) =
        g x * MeasureTheory.volume E := by
    intro x
    rw [lintegral_const, Measure.restrict_apply_univ]
  calc (∫⁻ x, ∫⁻ _, g x ∂(MeasureTheory.volume.restrict E)
        ∂(MeasureTheory.volume.restrict E))
      = ∫⁻ x, g x * MeasureTheory.volume E
          ∂(MeasureTheory.volume.restrict E) := lintegral_congr hinner
    _ = (∫⁻ x, g x ∂(MeasureTheory.volume.restrict E)) *
          MeasureTheory.volume E := lintegral_mul_const _ hg
    _ = MeasureTheory.volume E * ∫⁻ x in E, g x ∂MeasureTheory.volume :=
        mul_comm _ _

/-- One-variable integrand over the product set, second slot. -/
private theorem lintegral_prod_snd_eq {E : Set (Vec d)} {g : Vec d → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ z in E ×ˢ E, g z.2
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) =
      MeasureTheory.volume E * ∫⁻ x in E, g x ∂MeasureTheory.volume := by
  rw [← Measure.prod_restrict]
  rw [lintegral_prod (fun z => g z.2) ((hg.comp measurable_snd).aemeasurable)]
  dsimp only
  rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- Exact `ofReal` form of the oscillation power under `MemLp` (the equality
counterpart of `ofReal_oscillation_rpow_le`). -/
private theorem ofReal_oscillation_rpow_eq {S : TriadicCube d} {p : ℝ≥0∞}
    {u : Vec d → ℝ}
    (hu : MemLp u p (ScalarOverlap.normalizedCubeMeasure S)) :
    ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) =
      (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p
        (ScalarOverlap.normalizedCubeMeasure S)) ^ p.toReal := by
  have hsub : MemLp (fun x => u x - ScalarOverlap.cubeAverage S u) p
      (ScalarOverlap.normalizedCubeMeasure S) :=
    hu.sub (memLp_const _)
  have hfin : (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p
      (ScalarOverlap.normalizedCubeMeasure S)) ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hsub.eLpNorm_ne_top
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _ hsub.aestronglyMeasurable,
    ENNReal.toReal_rpow, ENNReal.ofReal_toReal hfin]

/-- The plain volume integral of the oscillation power equals the volume times
the `ofReal` of the normalized oscillation power. -/
private theorem lintegral_enorm_sub_average_eq {S : TriadicCube d} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ}
    (hu : MemLp u p (ScalarOverlap.normalizedCubeMeasure S)) :
    (∫⁻ x in ScalarOverlap.cubeSet S,
        ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (ScalarOverlap.cubeVolume S) *
        ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hvol : (0 : ℝ) < ScalarOverlap.cubeVolume S :=
    ScalarOverlap.cubeVolume_pos S
  set g : Vec d → ℝ≥0∞ :=
    fun x => ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal with hg
  have hμ : (∫⁻ x, g x ∂(ScalarOverlap.normalizedCubeMeasure S)) =
      ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume :=
    ScalarOverlap.lintegral_normalizedCubeMeasure_eq S g
  have hcancel : ENNReal.ofReal (ScalarOverlap.cubeVolume S) *
      ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hvol.le, mul_inv_cancel₀ hvol.ne',
      ENNReal.ofReal_one]
  have hLp : (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p
      (ScalarOverlap.normalizedCubeMeasure S)) ^ p.toReal =
      ∫⁻ x, g x ∂(ScalarOverlap.normalizedCubeMeasure S) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
      (f := fun x => u x - ScalarOverlap.cubeAverage S u)
      (hu.aestronglyMeasurable.sub aestronglyMeasurable_const), ← ENNReal.rpow_mul,
      one_div_mul_cancel hpr.ne', ENNReal.rpow_one]
  calc (∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume)
      = 1 * ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume :=
        (one_mul _).symm
    _ = ENNReal.ofReal (ScalarOverlap.cubeVolume S) *
          (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
            ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume) := by
        rw [← hcancel, mul_assoc]
    _ = ENNReal.ofReal (ScalarOverlap.cubeVolume S) *
          ∫⁻ x, g x ∂(ScalarOverlap.normalizedCubeMeasure S) := by
        rw [← hμ]
    _ = ENNReal.ofReal (ScalarOverlap.cubeVolume S) *
          ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
        rw [ofReal_oscillation_rpow_eq hu, hLp]

/-- Per-cube estimate: the doubled `L^p` difference integral over the product
of an overlapping cube is controlled by the volume squared times the
oscillation power. -/
private theorem setLIntegral_prod_overlap_le {S : TriadicCube d} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (ScalarOverlap.normalizedCubeMeasure S)) :
    (∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
        ‖u z.1 - u z.2‖ₑ ^ p.toReal
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      2 * 2 ^ p.toReal * ENNReal.ofReal (ScalarOverlap.cubeVolume S) ^ 2 *
        ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  set c : ℝ := ScalarOverlap.cubeAverage S u with hc
  set g : Vec d → ℝ≥0∞ := fun x => ‖u x - c‖ₑ ^ p.toReal with hgdef
  have hg : Measurable g :=
    (ENNReal.continuous_rpow_const.measurable).comp
      ((humeas.sub measurable_const).enorm)
  have hpoint : ∀ z : Vec d × Vec d,
      ‖u z.1 - u z.2‖ₑ ^ p.toReal ≤ 2 ^ p.toReal * (g z.1 + g z.2) :=
    fun z => enorm_sub_rpow_le hpr.le u c z
  have hvol : MeasureTheory.volume (ScalarOverlap.cubeSet S) =
      ENNReal.ofReal (ScalarOverlap.cubeVolume S) := by
    rw [← ScalarOverlap.cubeMeasure_apply_univ,
      ScalarOverlap.cubeMeasure_apply_univ_eq]
  calc (∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
        ‖u z.1 - u z.2‖ₑ ^ p.toReal
        ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      ≤ ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
          2 ^ p.toReal * (g z.1 + g z.2)
          ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        lintegral_mono fun z => hpoint z
    _ = 2 ^ p.toReal *
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
            (g z.1 + g z.2)
            ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        lintegral_const_mul _
          ((hg.comp measurable_fst).add (hg.comp measurable_snd))
    _ = 2 ^ p.toReal *
          ((∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
            g z.1 ∂(MeasureTheory.volume.prod MeasureTheory.volume)) +
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
            g z.2 ∂(MeasureTheory.volume.prod MeasureTheory.volume)) := by
        rw [lintegral_add_left (f := fun z : Vec d × Vec d => g z.1)
          (hg.comp measurable_fst)]
    _ = 2 ^ p.toReal *
          ((MeasureTheory.volume (ScalarOverlap.cubeSet S) *
            ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume) +
          MeasureTheory.volume (ScalarOverlap.cubeSet S) *
            ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume) := by
        rw [lintegral_prod_fst_eq hg, lintegral_prod_snd_eq hg]
    _ = 2 * 2 ^ p.toReal *
          (MeasureTheory.volume (ScalarOverlap.cubeSet S) *
            ∫⁻ x in ScalarOverlap.cubeSet S, g x ∂MeasureTheory.volume) := by
        ring
    _ = 2 * 2 ^ p.toReal * ENNReal.ofReal (ScalarOverlap.cubeVolume S) ^ 2 *
          ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
        rw [hvol, lintegral_enorm_sub_average_eq hp hpt hu]
        ring

/-- Inverting BR3: the sum of the oscillation powers over the centers is the
cardinality times the depth average. -/
private theorem sum_ofReal_oscillation_eq (Q : TriadicCube d) (j : ℕ)
    (p : ℝ≥0∞) (u : Vec d → ℝ) :
    (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal)) =
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞) *
        ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u j) := by
  rw [ofReal_depthAverage_eq, ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
  · exact_mod_cast ScalarOverlap.centersAtDepth_card_ne_zero Q j
  · exact ENNReal.natCast_ne_top _

/-- Real-side exponent bookkeeping for one shell: the kernel weight at the
inner shell radius, against the squared depth volume and the cube
normalization, reduces to the Besov depth weight power. -/
private theorem shell_coefficient_real_le {cQ : ℝ} (hc : 0 < cQ)
    {sr pr : ℝ} (hs0 : 0 ≤ sr) (hpr0 : 0 ≤ pr) (m : ℕ) {j n : ℕ}
    (hnj : n ≤ j + 1) :
    (cQ ^ m)⁻¹ * ((cQ / 3 ^ (n + 1)) ^ (-(sr * pr + (m : ℝ))) *
        ((cQ / 3 ^ j) ^ m) ^ 2) ≤
      (9 : ℝ) ^ (sr * pr + (m : ℝ)) * ((3 : ℝ) ^ (j * m))⁻¹ *
        (cQ / 3 ^ j) ^ (-(sr * pr)) := by
  set a : ℝ := sr * pr + (m : ℝ) with ha_def
  have ha0 : 0 ≤ a := by positivity
  set e : ℝ := cQ / 3 ^ j with he_def
  have he0 : 0 < e := div_pos hc (by positivity)
  have he9 : (0 : ℝ) < e / 9 := by positivity
  -- Step A: monotone comparison of the kernel weight
  have hle : e / 9 ≤ cQ / 3 ^ (n + 1) := by
    have h1 : e / 9 = cQ / 3 ^ (j + 2) := by
      rw [he_def, div_div, pow_add]
      norm_num
    rw [h1]
    exact div_le_div_of_nonneg_left hc.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hA : (cQ / 3 ^ (n + 1)) ^ (-a) ≤ (e / 9) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos he9 hle (neg_nonpos.2 ha0)
  -- Step B: split the inner radius weight
  have hB : (e / 9) ^ (-a) = e ^ (-a) * 9 ^ a := by
    rw [div_eq_mul_inv, Real.mul_rpow he0.le (by norm_num : (0:ℝ) ≤ (9:ℝ)⁻¹),
      Real.inv_rpow (by norm_num : (0:ℝ) ≤ (9:ℝ)),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ (9:ℝ)), inv_inv]
  -- Step C: merge the powers of `e`
  have h2m : ((e ^ m) ^ 2 : ℝ) = e ^ ((2 * m : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    ring
  have hC : e ^ (-a) * (e ^ m) ^ 2 = e ^ (-(sr * pr)) * e ^ ((m : ℕ) : ℝ) := by
    rw [h2m, ← Real.rpow_add he0, ← Real.rpow_add he0, ha_def]
    congr 1
    push_cast
    ring
  -- Step D: the leftover power of `e` cancels the cube normalization
  have hD : (cQ ^ m)⁻¹ * e ^ ((m : ℕ) : ℝ) = ((3 : ℝ) ^ (j * m))⁻¹ := by
    rw [Real.rpow_natCast]
    have hem : e ^ m = cQ ^ m / 3 ^ (j * m) := by
      rw [he_def, div_pow, ← pow_mul]
    rw [hem, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero m hc.ne'), one_mul]
  calc (cQ ^ m)⁻¹ * ((cQ / 3 ^ (n + 1)) ^ (-a) * (e ^ m) ^ 2)
      ≤ (cQ ^ m)⁻¹ * ((e / 9) ^ (-a) * (e ^ m) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hA (by positivity)
    _ = 9 ^ a * ((cQ ^ m)⁻¹ * (e ^ (-a) * (e ^ m) ^ 2)) := by
        rw [hB]
        ring
    _ = 9 ^ a * ((cQ ^ m)⁻¹ * (e ^ (-(sr * pr)) * e ^ ((m : ℕ) : ℝ))) := by
        rw [hC]
    _ = 9 ^ a * (e ^ (-(sr * pr)) * ((cQ ^ m)⁻¹ * e ^ ((m : ℕ) : ℝ))) := by
        ring
    _ = 9 ^ a * (e ^ (-(sr * pr)) * ((3 : ℝ) ^ (j * m))⁻¹) := by
        rw [hD]
    _ = 9 ^ a * ((3 : ℝ) ^ (j * m))⁻¹ * e ^ (-(sr * pr)) := by
        ring

/-- `ℝ≥0∞` coefficient collapse for one shell: every flat factor is absorbed
into a `pr`-th power of a dimensional constant. -/
private theorem shell_coefficient_ennreal_le {m : ℕ} {sr pr : ℝ}
    (hs1 : sr ≤ 1) (hpr : 1 ≤ pr) (j : ℕ) {card : ℕ}
    (hcard : card ≤ (3 ^ m) ^ (j + 1)) :
    (9 : ℝ≥0∞) ^ (sr * pr + (m : ℝ)) * ((3 : ℝ≥0∞) ^ (j * m))⁻¹ *
        (card : ℝ≥0∞) * (2 * 2 ^ pr) ≤
      ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * m + 2)) ^ pr := by
  have hpr0 : (0 : ℝ) ≤ pr := zero_le_one.trans hpr
  have hone9m : (1 : ℝ≥0∞) ≤ 9 ^ m := by
    simpa using pow_le_pow_left' (show (1 : ℝ≥0∞) ≤ 9 by norm_num) m
  have hone3m : (1 : ℝ≥0∞) ≤ 3 ^ m := by
    simpa using pow_le_pow_left' (show (1 : ℝ≥0∞) ≤ 3 by norm_num) m
  have hA : (9 : ℝ≥0∞) ^ (sr * pr + (m : ℝ)) ≤ ((9 : ℝ≥0∞) * 9 ^ m) ^ pr := by
    calc (9 : ℝ≥0∞) ^ (sr * pr + (m : ℝ))
        ≤ (9 : ℝ≥0∞) ^ (pr + (m : ℝ)) := by
          refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have : sr * pr ≤ 1 * pr := mul_le_mul_of_nonneg_right hs1 hpr0
          linarith
      _ = (9 : ℝ≥0∞) ^ pr * 9 ^ ((m : ℕ) : ℝ) :=
          ENNReal.rpow_add pr (m : ℝ) (by norm_num) (by norm_num)
      _ = (9 : ℝ≥0∞) ^ pr * 9 ^ m := by rw [ENNReal.rpow_natCast]
      _ ≤ (9 : ℝ≥0∞) ^ pr * ((9 : ℝ≥0∞) ^ m) ^ pr := by
          gcongr
          exact ENNReal.le_rpow_self_of_one_le hone9m hpr
      _ = ((9 : ℝ≥0∞) * 9 ^ m) ^ pr :=
          (ENNReal.mul_rpow_of_nonneg _ _ hpr0).symm
  have hB : ((3 : ℝ≥0∞) ^ (j * m))⁻¹ * (card : ℝ≥0∞) ≤
      ((3 : ℝ≥0∞) ^ m) ^ pr := by
    have hcard' : (card : ℝ≥0∞) ≤ (3 : ℝ≥0∞) ^ (j * m + m) := by
      calc (card : ℝ≥0∞) ≤ (((3 ^ m) ^ (j + 1) : ℕ) : ℝ≥0∞) :=
            Nat.cast_le.2 hcard
        _ = (3 : ℝ≥0∞) ^ (j * m + m) := by
            push_cast
            rw [← pow_mul]
            congr 1
            ring
    calc ((3 : ℝ≥0∞) ^ (j * m))⁻¹ * (card : ℝ≥0∞)
        ≤ ((3 : ℝ≥0∞) ^ (j * m))⁻¹ * (3 : ℝ≥0∞) ^ (j * m + m) := by
          gcongr
      _ = (3 : ℝ≥0∞) ^ m := by
          rw [pow_add, ← mul_assoc,
            ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num))
              (ENNReal.pow_ne_top (by norm_num)), one_mul]
      _ ≤ ((3 : ℝ≥0∞) ^ m) ^ pr :=
          ENNReal.le_rpow_self_of_one_le hone3m hpr
  have hC : (2 : ℝ≥0∞) * 2 ^ pr ≤ ((2 : ℝ≥0∞) * 2) ^ pr := by
    calc (2 : ℝ≥0∞) * 2 ^ pr ≤ 2 ^ pr * 2 ^ pr := by
          gcongr
          exact ENNReal.le_rpow_self_of_one_le (by norm_num) hpr
      _ = ((2 : ℝ≥0∞) * 2) ^ pr := (ENNReal.mul_rpow_of_nonneg _ _ hpr0).symm
  have hbase : ((9 : ℝ≥0∞) * 9 ^ m) * 3 ^ m * ((2 : ℝ≥0∞) * 2) =
      (2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * m + 2) := by
    have h9 : (9 : ℝ≥0∞) = 3 ^ 2 := by norm_num
    rw [h9, ← pow_mul, show 3 * m + 2 = 2 + (2 * m + m) from by ring,
      pow_add, pow_add]
    ring
  calc (9 : ℝ≥0∞) ^ (sr * pr + (m : ℝ)) * ((3 : ℝ≥0∞) ^ (j * m))⁻¹ *
        (card : ℝ≥0∞) * (2 * 2 ^ pr)
      = (9 : ℝ≥0∞) ^ (sr * pr + (m : ℝ)) *
          (((3 : ℝ≥0∞) ^ (j * m))⁻¹ * (card : ℝ≥0∞)) * (2 * 2 ^ pr) := by
        ring
    _ ≤ ((9 : ℝ≥0∞) * 9 ^ m) ^ pr * ((3 : ℝ≥0∞) ^ m) ^ pr *
          ((2 : ℝ≥0∞) * 2) ^ pr := mul_le_mul' (mul_le_mul' hA hB) hC
    _ = (((9 : ℝ≥0∞) * 9 ^ m) * 3 ^ m * ((2 : ℝ≥0∞) * 2)) ^ pr := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hpr0,
          ← ENNReal.mul_rpow_of_nonneg _ _ hpr0]
    _ = ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * m + 2)) ^ pr := by
        rw [hbase]

/-- Per-shell estimate: the shell integral of the kernel is controlled by the
inner shell weight, the squared depth volume, the center count, the triangle
factor, and the Besov depth average at depth `n - 1`. -/
private theorem shell_lintegral_le {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q))
    (ha : 0 < s * p.toReal + (d : ℝ)) (n : ℕ) :
    (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n,
      ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
        ‖u z.1 - u z.2‖ₑ ^ p.toReal
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      ENNReal.ofReal
          ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
        (2 * 2 ^ p.toReal *
            ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
          (((ScalarOverlap.centersAtDepth Q (n - 1)).card : ℝ≥0∞) *
            ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u (n - 1)))) := by
  have hF : Measurable fun z : Vec d × Vec d => ‖u z.1 - u z.2‖ₑ ^ p.toReal :=
    (ENNReal.continuous_rpow_const.measurable).comp
      (((humeas.comp measurable_fst).sub (humeas.comp measurable_snd)).enorm)
  have hvolS : ∀ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
      ScalarOverlap.cubeVolume S = (cubeScaleFactor Q / 3 ^ (n - 1)) ^ d := by
    intro S hS
    unfold ScalarOverlap.cubeVolume
    rw [scaleFactor_eq_cubeScaleFactor_div_pow_of_mem_centersAtDepth hS]
  calc (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
        shellSet Q n,
      ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
        ‖u z.1 - u z.2‖ₑ ^ p.toReal
      ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      ≤ ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
              shellSet Q n,
            ‖u z.1 - u z.2‖ₑ ^ p.toReal
            ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        shell_setLIntegral_kernel_le ha hF
    _ ≤ ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
            ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
              ‖u z.1 - u z.2‖ₑ ^ p.toReal
              ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        mul_le_mul_right (shell_setLIntegral_le_sum n _) _
    _ ≤ ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
            2 * 2 ^ p.toReal *
              ENNReal.ofReal (ScalarOverlap.cubeVolume S) ^ 2 *
              ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) :=
        mul_le_mul_right
          (Finset.sum_le_sum fun S hS =>
            setLIntegral_prod_overlap_le hp hpt humeas
              (memLp_overlap_of_memLp hu hS)) _
    _ = ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
            2 * 2 ^ p.toReal *
              ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
              ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
        congr 1
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [hvolS S hS]
    _ = ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          (2 * 2 ^ p.toReal *
              ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
            ∑ S ∈ ScalarOverlap.centersAtDepth Q (n - 1),
              ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal)) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
          (2 * 2 ^ p.toReal *
              ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
            (((ScalarOverlap.centersAtDepth Q (n - 1)).card : ℝ≥0∞) *
              ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u (n - 1)))) := by
        rw [sum_ofReal_oscillation_eq]

/-- `ofReal` form of the shell coefficient collapse. -/
private theorem shell_coefficient_ofReal_le {Q : TriadicCube d} {s pr : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hpr : 1 ≤ pr) {j n : ℕ} (hnj : n ≤ j + 1)
    {card : ℕ} (hcard : card ≤ (3 ^ d) ^ (j + 1)) :
    ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ENNReal.ofReal
          ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ)))) *
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2 *
        (card : ℝ≥0∞) * (2 * 2 ^ pr) ≤
      ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ pr *
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr))) := by
  have hc : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hpr0 : (0 : ℝ) ≤ pr := zero_le_one.trans hpr
  have hreal : (cubeVolume Q)⁻¹ *
      ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ))) *
        ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2) ≤
      (9 : ℝ) ^ (s * pr + (d : ℝ)) * ((3 : ℝ) ^ (j * d))⁻¹ *
        (cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr)) := by
    have h := shell_coefficient_real_le hc hs0 hpr0 d hnj
    have hvolQ : cubeVolume Q = cubeScaleFactor Q ^ d := rfl
    rw [hvolQ]
    exact h
  have h9 : ENNReal.ofReal ((9 : ℝ) ^ (s * pr + (d : ℝ))) =
      (9 : ℝ≥0∞) ^ (s * pr + (d : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 9)]
    norm_num
  have h3 : ENNReal.ofReal (((3 : ℝ) ^ (j * d))⁻¹) =
      ((3 : ℝ≥0∞) ^ (j * d))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hvol0 : (0 : ℝ) ≤ (cubeVolume Q)⁻¹ :=
    inv_nonneg.2 (cubeVolume_pos Q).le
  have hb0 : (0 : ℝ) ≤
      (cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ))) :=
    Real.rpow_nonneg (div_nonneg hc.le (by positivity)) _
  have he0 : (0 : ℝ) ≤ (cubeScaleFactor Q / 3 ^ j) ^ d :=
    pow_nonneg (div_nonneg hc.le (by positivity)) d
  have hsplit : ENNReal.ofReal ((cubeVolume Q)⁻¹ *
      ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ))) *
        ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2)) =
      ENNReal.ofReal (cubeVolume Q)⁻¹ *
        (ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ)))) *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2) := by
    rw [ENNReal.ofReal_mul hvol0, ENNReal.ofReal_mul hb0,
      ENNReal.ofReal_pow he0]
  calc ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ENNReal.ofReal
          ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ)))) *
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2 *
        (card : ℝ≥0∞) * (2 * 2 ^ pr)
      = ENNReal.ofReal ((cubeVolume Q)⁻¹ *
          ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * pr + (d : ℝ))) *
            ((cubeScaleFactor Q / 3 ^ j) ^ d) ^ 2)) *
          ((card : ℝ≥0∞) * (2 * 2 ^ pr)) := by
        rw [hsplit]
        ring
    _ ≤ ENNReal.ofReal ((9 : ℝ) ^ (s * pr + (d : ℝ)) *
          ((3 : ℝ) ^ (j * d))⁻¹ *
          (cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr))) *
          ((card : ℝ≥0∞) * (2 * 2 ^ pr)) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
    _ = ((9 : ℝ≥0∞) ^ (s * pr + (d : ℝ)) * ((3 : ℝ≥0∞) ^ (j * d))⁻¹ *
          (card : ℝ≥0∞) * (2 * 2 ^ pr)) *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr))) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), h9, h3]
        ring
    _ ≤ ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ pr *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr))) :=
        mul_le_mul_left (shell_coefficient_ennreal_le hs1 hpr j hcard) _

/-- Shell-to-depth collapse: each normalized shell term is bounded by the
`p`-th power of the Besov depth seminorm at depth `n - 1`. -/
private theorem shell_term_le {Q : TriadicCube d} [NeZero d] {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q)) (n : ℕ) :
    ENNReal.ofReal (cubeVolume Q)⁻¹ *
      (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
          shellSet Q n,
        ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
          ‖u z.1 - u z.2‖ₑ ^ p.toReal
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≤
      ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
        ENNReal.ofReal
          (cubeBesovOverlapDepthSeminorm Q s p u (n - 1) ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr1 : (1 : ℝ) ≤ p.toReal := by
    have h1 := ENNReal.toReal_mono hpt hp
    simpa using h1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have ha : 0 < s * p.toReal + (d : ℝ) := by
    have hsp : 0 ≤ s * p.toReal :=
      mul_nonneg hs0 (zero_le_one.trans hpr1)
    linarith
  have hc : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hnj : n ≤ (n - 1) + 1 := by omega
  have hcard := ScalarOverlap.centersAtDepth_card_le_pow Q (n - 1)
  have hw : cubeBesovOverlapDepthWeight Q s (n - 1) ^ p.toReal =
      (cubeScaleFactor Q / 3 ^ (n - 1)) ^ (-(s * p.toReal)) := by
    unfold cubeBesovOverlapDepthWeight cubeBesovDepthWeight
    rw [← Real.rpow_mul (le_of_lt (div_pos hc (by positivity))), neg_mul]
  calc ENNReal.ofReal (cubeVolume Q)⁻¹ *
      (∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
          shellSet Q n,
        ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
          ‖u z.1 - u z.2‖ₑ ^ p.toReal
        ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      ≤ ENNReal.ofReal (cubeVolume Q)⁻¹ *
          (ENNReal.ofReal
              ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + d))) *
            (2 * 2 ^ p.toReal *
                ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
              (((ScalarOverlap.centersAtDepth Q (n - 1)).card : ℝ≥0∞) *
                ENNReal.ofReal
                  (cubeBesovOverlapDepthAverage Q p u (n - 1))))) :=
        mul_le_mul_right (shell_lintegral_le hp hpt humeas hu ha n) _
    _ = (ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n + 1)) ^ (-(s * p.toReal + (d : ℝ)))) *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ d) ^ 2 *
          (((ScalarOverlap.centersAtDepth Q (n - 1)).card : ℝ≥0∞)) *
          (2 * 2 ^ p.toReal)) *
          ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u (n - 1)) := by
        ring
    _ ≤ (((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          ENNReal.ofReal
            ((cubeScaleFactor Q / 3 ^ (n - 1)) ^ (-(s * p.toReal)))) *
          ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u (n - 1)) :=
        mul_le_mul_left
          (shell_coefficient_ofReal_le hs0 hs1 hpr1 hnj hcard) _
    _ = ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          (ENNReal.ofReal
              (cubeBesovOverlapDepthWeight Q s (n - 1) ^ p.toReal) *
            ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u (n - 1))) := by
        rw [hw]
        ring
    _ = ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u (n - 1) ^ p.toReal) := by
        rw [← ofReal_depthSeminorm_rpow_eq Q s hp0 hpt u (n - 1)]

/-- **Gagliardo-to-Besov comparison.** The `p`-th power of the fractional
Sobolev seminorm on a triadic cube is controlled by the supremum of the
`p`-th powers of the finite-depth overlapping Besov seminorms, with a constant
depending only on the dimension. -/
theorem gagliardo_rpow_le_iSup_partialSeminorm {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q)) :
    cubeGagliardoESeminorm Q s p u ^ p.toReal ≤
      (gagliardoBesovLowerConstant d) ^ p.toReal *
        ⨆ N : ℕ, ENNReal.ofReal
          (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr1 : (1 : ℝ) ≤ p.toReal := by
    have h1 := ENNReal.toReal_mono hpt hp
    simpa using h1
  have hpr0 : (0 : ℝ) ≤ p.toReal := zero_le_one.trans hpr1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hane : s * p.toReal + (d : ℝ) ≠ 0 := by
    have hsp : 0 ≤ s * p.toReal := mul_nonneg hs hpr0
    intro hzero
    linarith
  -- shell-to-depth reindexing in the summation index
  have hreindex :
      (∑' n : ℕ, ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s p u (n - 1) ^ p.toReal)) ≤
      2 * ∑' j : ℕ, ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) := by
    set h : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
      (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) with hh
    have hsplit : (∑' n : ℕ, h (n - 1)) = h (0 - 1) + ∑' n : ℕ, h ((n + 1) - 1) :=
      tsum_eq_zero_add' ENNReal.summable
    calc (∑' n : ℕ, h (n - 1))
        = h (0 - 1) + ∑' n : ℕ, h ((n + 1) - 1) := hsplit
      _ = h 0 + ∑' n : ℕ, h n := by
          simp only [Nat.zero_sub, Nat.add_sub_cancel]
      _ ≤ (∑' n : ℕ, h n) + ∑' n : ℕ, h n :=
          add_le_add (ENNReal.le_tsum 0) le_rfl
      _ = 2 * ∑' n : ℕ, h n := (two_mul _).symm
  -- the depth series is the supremum of the partial seminorm powers
  have htsum_eq :
      (∑' j : ℕ, ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal)) =
      ⨆ N : ℕ, ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) := by
    rw [ENNReal.tsum_eq_iSup_nat' (N := fun i => i + 1) (Filter.tendsto_add_atTop_nat 1)]
    exact iSup_congr fun N =>
      (ofReal_partialSeminorm_rpow_eq Q s hp0 hpt N u).symm
  calc cubeGagliardoESeminorm Q s p u ^ p.toReal
      = ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
            ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
              ‖u z.1 - u z.2‖ₑ ^ p.toReal
            ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        gagliardo_rpow_eq_lintegral hp hpt u
    _ ≤ ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∑' n : ℕ,
            ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
                shellSet Q n,
              ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal
              ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        mul_le_mul_right (setLIntegral_prodCube_le_tsum_shell hane _) _
    _ = ∑' n : ℕ, ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ z in (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) ∩
              shellSet Q n,
            ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
              ‖u z.1 - u z.2‖ₑ ^ p.toReal
            ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' n : ℕ, ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u (n - 1) ^ p.toReal) :=
        ENNReal.tsum_le_tsum fun n =>
          shell_term_le hs hs1 hp hpt humeas hu n
    _ = ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          ∑' n : ℕ, ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u (n - 1) ^ p.toReal) :=
        ENNReal.tsum_mul_left
    _ ≤ ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal *
          (2 * ∑' j : ℕ, ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal)) :=
        mul_le_mul_right hreindex _
    _ = (2 * ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal) *
          ∑' j : ℕ, ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) := by
        ring
    _ ≤ ((2 : ℝ≥0∞) ^ p.toReal * ((2 : ℝ≥0∞) ^ 2 * 3 ^ (3 * d + 2)) ^ p.toReal) *
          ∑' j : ℕ, ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) :=
        mul_le_mul_left
          (mul_le_mul_left
            (ENNReal.le_rpow_self_of_one_le (by norm_num) hpr1) _) _
    _ = (gagliardoBesovLowerConstant d) ^ p.toReal *
          ∑' j : ℕ, ENNReal.ofReal
            (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hpr0]
        congr 2
        rw [gagliardoBesovLowerConstant]
        ring
    _ = (gagliardoBesovLowerConstant d) ^ p.toReal *
          ⨆ N : ℕ, ENNReal.ofReal
            (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) := by
        rw [htsum_eq]

end

end Gagliardo
end Homogenization
