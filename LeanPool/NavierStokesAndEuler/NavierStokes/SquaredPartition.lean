/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Concrete squared partitions on the line and on slow-coordinate grids

Integer translates of one compactly supported smooth bump are normalized by
the square root of their locally finite sum of squares. Every object below is
constructed; no partition-of-unity or derivative-bound hypothesis is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SquaredPartition

open Set Filter Function
open scoped Topology ContDiff BigOperators

/-- A smooth locally finite sum is smooth. This elementary version uses finite
sums on neighborhoods, so no uniform convergence premise is needed. -/
theorem contDiff_finsum_of_locallyFinite {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfin : LocallyFinite fun i => support (f i)) :
    ContDiff ℝ ∞ (fun x => ∑ᶠ i, f i x) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨U, hU, hfinite⟩ := hfin x
  have heq : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ hfinite.toFinset, f i y) := by
    filter_upwards [hU] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    exact hfinite.mem_toFinset.mpr ⟨y, hi, hy⟩
  exact (ContDiff.contDiffAt (ContDiff.sum fun i _ => hf i)).congr_of_eventuallyEq heq

/-- One fixed bump: equal to one on `[-1/2,1/2]`, positive on `(-1,1)`. -/
def bump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Translated bump, given by `bump (x - k)`. -/
def translatedBump (k : ℤ) (x : ℝ) : ℝ := bump (x - k)

theorem translatedBump_nonneg (k : ℤ) (x : ℝ) : 0 ≤ translatedBump k x := bump.nonneg

theorem translatedBump_smooth (k : ℤ) : ContDiff ℝ ∞ (translatedBump k) :=
  bump.contDiff.comp (contDiff_id.sub contDiff_const)

theorem translatedBump_support (k : ℤ) :
    support (translatedBump k) = Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := by
  ext x
  change bump (x - k) ≠ 0 ↔ _
  rw [← mem_support, bump.support_eq]
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, bump, abs_lt, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem integer_intervals_locallyFinite :
    LocallyFinite fun k : ℤ => Icc ((k : ℝ) - 1) ((k : ℝ) + 1) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (Set.finite_Icc (⌊x⌋ - 2) (⌊x⌋ + 3)).subset
  rintro k ⟨y, hy, hyx⟩
  have hfloor := Int.floor_le x
  have hfloor' := Int.lt_floor_add_one x
  have hlo : ((⌊x⌋ - 2 : ℤ) : ℝ) ≤ k := by
    push_cast
    linarith [hy.2, hyx.1]
  have hhi : (k : ℝ) ≤ ((⌊x⌋ + 3 : ℤ) : ℝ) := by
    push_cast
    linarith [hy.1, hyx.2]
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem translatedBump_locallyFinite : LocallyFinite fun k => support (translatedBump k) := by
  apply integer_intervals_locallyFinite.subset
  intro k
  rw [translatedBump_support]
  exact Ioo_subset_Icc_self

theorem squaredBump_locallyFinite :
    LocallyFinite fun k : ℤ => support (fun x => translatedBump k x ^ 2) := by
  apply translatedBump_locallyFinite.subset
  intro k x hx
  change translatedBump k x ≠ 0
  intro h
  exact hx (by simp [h])

/-- Denominator squared, given by `∑ᶠ k : ℤ, translatedBump k x ^ 2`. -/
def denominatorSquared (x : ℝ) : ℝ := ∑ᶠ k : ℤ, translatedBump k x ^ 2

theorem denominatorSquared_pos (x : ℝ) : 0 < denominatorSquared x := by
  apply finsum_pos (fun k => sq_nonneg (translatedBump k x))
  · refine ⟨⌊x⌋, pow_pos ?_ 2⟩
    apply bump.pos_of_mem_ball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, bump, abs_lt]
    constructor
    · linarith [Int.floor_le x]
    · linarith [Int.lt_floor_add_one x]
  · exact squaredBump_locallyFinite.point_finite x

theorem denominatorSquared_smooth : ContDiff ℝ ∞ denominatorSquared :=
  contDiff_finsum_of_locallyFinite (fun k => (translatedBump_smooth k).pow 2)
    squaredBump_locallyFinite

/-- Line mask, given by `translatedBump k x / Real.sqrt (denominatorSquared x)`. -/
def lineMask (k : ℤ) (x : ℝ) : ℝ :=
  translatedBump k x / Real.sqrt (denominatorSquared x)

theorem lineMask_nonneg (k : ℤ) (x : ℝ) : 0 ≤ lineMask k x :=
  div_nonneg (translatedBump_nonneg k x) (Real.sqrt_nonneg _)

theorem lineMask_smooth (k : ℤ) : ContDiff ℝ ∞ (lineMask k) :=
  (translatedBump_smooth k).div
    (denominatorSquared_smooth.sqrt (fun x => (denominatorSquared_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (denominatorSquared_pos x)).ne')

theorem lineMask_support (k : ℤ) :
    support (lineMask k) = Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := by
  ext x
  rw [← translatedBump_support]
  change translatedBump k x / Real.sqrt (denominatorSquared x) ≠ 0 ↔
    translatedBump k x ≠ 0
  rw [div_ne_zero_iff]
  exact and_iff_left (Real.sqrt_pos.mpr (denominatorSquared_pos x)).ne'

theorem lineMask_tsupport (k : ℤ) :
    tsupport (lineMask k) = Icc ((k : ℝ) - 1) ((k : ℝ) + 1) := by
  rw [tsupport, lineMask_support, closure_Ioo (by linarith : (k : ℝ) - 1 ≠ k + 1)]

theorem lineMask_compactSupport (k : ℤ) : HasCompactSupport (lineMask k) := by
  rw [HasCompactSupport, lineMask_tsupport]
  exact isCompact_Icc

theorem lineMask_locallyFinite : LocallyFinite fun k => tsupport (lineMask k) := by
  simpa only [lineMask_tsupport] using integer_intervals_locallyFinite

theorem lineMask_sum_sq (x : ℝ) : (∑ᶠ k : ℤ, lineMask k x ^ 2) = 1 := by
  simp only [lineMask, div_pow, Real.sq_sqrt (denominatorSquared_pos x).le]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul _ _]
  exact mul_inv_cancel₀ (denominatorSquared_pos x).ne'

theorem denominatorSquared_add_int (k : ℤ) (x : ℝ) :
    denominatorSquared (x + k) = denominatorSquared x := by
  unfold denominatorSquared
  apply finsum_eq_of_bijective (fun j : ℤ => j - k)
  · constructor
    · intro a b hab
      change a - k = b - k at hab
      omega
    · intro b
      exact ⟨b + k, by change b + k - k = b; omega⟩
  · intro j
    unfold translatedBump
    congr 2
    push_cast
    ring

theorem denominatorSquared_sub_int (k : ℤ) (x : ℝ) :
    denominatorSquared (x - k) = denominatorSquared x := by
  simpa only [Int.cast_neg, sub_eq_add_neg] using denominatorSquared_add_int (-k) x

/-- All masks are translates of a single normalized profile. -/
theorem lineMask_eq_translate (k : ℤ) (x : ℝ) :
    lineMask k x = lineMask 0 (x - k) := by
  simp only [lineMask, translatedBump, Int.cast_zero, sub_zero, denominatorSquared_sub_int]

/-- Grid mask, given by `lineMask k (x / δ)`. -/
def gridMask (δ : ℝ) (k : ℤ) (x : ℝ) : ℝ := lineMask k (x / δ)

theorem gridMask_nonneg (δ : ℝ) (k : ℤ) (x : ℝ) : 0 ≤ gridMask δ k x :=
  lineMask_nonneg _ _

theorem gridMask_smooth (δ : ℝ) (k : ℤ) : ContDiff ℝ ∞ (gridMask δ k) :=
  (lineMask_smooth k).comp (contDiff_id.div_const δ)

theorem gridMask_sum_sq (δ : ℝ) (x : ℝ) : (∑ᶠ k : ℤ, gridMask δ k x ^ 2) = 1 :=
  lineMask_sum_sq (x / δ)

theorem gridMask_support (δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    support (gridMask δ k) = Ioo (δ * k - δ) (δ * k + δ) := by
  ext x
  change x / δ ∈ support (lineMask k) ↔ _
  rw [lineMask_support]
  simp only [mem_Ioo]
  rw [lt_div_iff₀ hδ, div_lt_iff₀ hδ]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem gridMask_tsupport (δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    tsupport (gridMask δ k) = Icc (δ * k - δ) (δ * k + δ) := by
  rw [tsupport, gridMask_support δ hδ, closure_Ioo (by linarith : δ * k - δ ≠ δ * k + δ)]

theorem gridMask_compactSupport (δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    HasCompactSupport (gridMask δ k) := by
  rw [HasCompactSupport, gridMask_tsupport δ hδ]
  exact isCompact_Icc

theorem gridMask_locallyFinite (δ : ℝ) :
    LocallyFinite fun k => support (gridMask δ k) := by
  have hl : LocallyFinite fun k => support (lineMask k) :=
    lineMask_locallyFinite.subset fun k => subset_closure
  change LocallyFinite fun k => (fun x : ℝ => x / δ) ⁻¹' support (lineMask k)
  exact hl.preimage_continuous (continuous_id.div_const δ)

/-- A finite product of locally finite families is locally finite, with the
whole tuple as index. -/
theorem locallyFinite_iInter {ι κ X : Type*} [Finite ι] [TopologicalSpace X]
    {U : ι → κ → Set X} (h : ∀ i, LocallyFinite (U i)) :
    LocallyFinite fun k : ι → κ => ⋂ i, U i (k i) := by
  classical
  intro x
  choose V hV hfinite using fun i => h i x
  refine ⟨⋂ i, V i, Filter.iInter_mem.mpr hV, (Set.Finite.pi' hfinite).subset ?_⟩
  rintro k ⟨y, hy, hyV⟩ i
  exact ⟨y, mem_iInter.mp hy i, mem_iInter.mp hyV i⟩

/-- Product mask, given by `∏ j, gridMask δ (k j) (x j)`. -/
def productMask {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, gridMask δ (k j) (x j)

theorem productMask_nonneg {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    0 ≤ productMask δ k x :=
  Finset.prod_nonneg fun _ _ => gridMask_nonneg _ _ _

theorem productMask_smooth {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) :
    ContDiff ℝ ∞ (productMask δ k) := by
  apply contDiff_prod
  intro j _
  exact (gridMask_smooth δ (k j)).comp (contDiff_apply ℝ ℝ j)

theorem productMask_support {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) :
    support (productMask δ k) = ⋂ j, (fun x => x j) ⁻¹' support (gridMask δ (k j)) := by
  ext x
  simp [mem_support, productMask, Finset.prod_ne_zero_iff]

theorem productMask_locallyFinite {d : ℕ} (δ : ℝ) :
    LocallyFinite fun k : Fin d → ℤ => support (productMask δ k) := by
  simp_rw [productMask_support]
  refine locallyFinite_iInter (U := fun j k =>
    (fun x : Fin d → ℝ => x j) ⁻¹' support (gridMask δ k)) ?_
  intro j
  exact (gridMask_locallyFinite δ).preimage_continuous (continuous_apply j)

theorem productMask_tsupport_subset {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (k : Fin d → ℤ) :
    tsupport (productMask δ k) ⊆
      Set.pi univ (fun j => Icc (δ * k j - δ) (δ * k j + δ)) := by
  apply closure_minimal
  · intro x hx j _
    have hxj := mem_iInter.mp ((productMask_support δ k) ▸ hx) j
    change x j ∈ support (gridMask δ (k j)) at hxj
    have hc := subset_closure hxj
    change x j ∈ tsupport (gridMask δ (k j)) at hc
    simpa only [gridMask_tsupport δ hδ] using hc
  · exact (isCompact_univ_pi fun _ => isCompact_Icc).isClosed

theorem productMask_compactSupport {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (k : Fin d → ℤ) :
    HasCompactSupport (productMask δ k) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_closure
    (productMask_tsupport_subset δ hδ k)

theorem productMask_sum_sq {d : ℕ} (δ : ℝ) (x : Fin d → ℝ) :
    (∑ᶠ k : Fin d → ℤ, productMask δ k x ^ 2) = 1 := by
  classical
  let F : Fin d → Finset ℤ := fun j => ((gridMask_locallyFinite δ).point_finite (x j)).toFinset
  have hF (j : Fin d) : support (fun k : ℤ => gridMask δ k (x j) ^ 2) ⊆ F j := by
    intro k hk
    apply ((gridMask_locallyFinite δ).point_finite (x j)).mem_toFinset.mpr
    change gridMask δ k (x j) ≠ 0
    intro hz
    exact hk (by simp [hz])
  have hP : support (fun k : Fin d → ℤ => productMask δ k x ^ 2) ⊆
      Fintype.piFinset F := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro j
    apply hF j
    change gridMask δ (k j) (x j) ^ 2 ≠ 0
    have hp : productMask δ k x ≠ 0 := fun hz => hk (by simp [hz])
    exact pow_ne_zero 2 ((Finset.prod_ne_zero_iff.mp hp) j (Finset.mem_univ j))
  rw [finsum_eq_sum_of_support_subset _ hP]
  simp only [productMask, ← Finset.prod_pow]
  rw [← Finset.prod_univ_sum F (fun j k => gridMask δ k (x j) ^ 2)]
  have hsum (j : Fin d) : (∑ k ∈ F j, gridMask δ k (x j) ^ 2) = 1 := by
    rw [← finsum_eq_sum_of_support_subset _ (hF j)]
    exact gridMask_sum_sq δ (x j)
  simp_rw [hsum]
  exact Finset.prod_const_one

/-- Compact smooth profiles have a finite bound at every fixed derivative order. -/
theorem exists_uniform_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  have hb : BddAbove (range fun x => ‖iteratedFDeriv ℝ m f x‖) := by
    apply (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
    exact (hc.iteratedFDeriv m).comp_left norm_zero
  obtain ⟨B, hB⟩ := hb
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x => (hB (mem_range_self x)).trans (le_max_left _ _)⟩

/-- Full Fréchet jets of a translated rescaling cost one inverse scale per
derivative, with no dependence on the translation. -/
theorem rescale_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {m : ℕ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) (a : ℝ) (c x : E) :
    ‖iteratedFDeriv ℝ m (fun y => f (a • y - c)) x‖ ≤ C * |a| ^ m := by
  let g : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hg : ‖g‖ ≤ |a| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
    intro y
    simp [g, norm_smul, Real.norm_eq_abs]
  have hs : ContDiff ℝ ∞ (fun y => f (y - c)) := hf.comp (contDiff_id.sub contDiff_const)
  change ‖iteratedFDeriv ℝ m ((fun y => f (y - c)) ∘ g) x‖ ≤ _
  rw [g.iteratedFDeriv_comp_right hs x (mod_cast le_top)]
  calc
    ‖(iteratedFDeriv ℝ m (fun y => f (y - c)) (g x)).compContinuousLinearMap (fun _ => g)‖
        ≤ ‖iteratedFDeriv ℝ m (fun y => f (y - c)) (g x)‖ * ∏ _ : Fin m, ‖g‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ m f (g x - c)‖ * ‖g‖ ^ m := by
      rw [iteratedFDeriv_comp_sub]
      simp
    _ ≤ C * |a| ^ m :=
      mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg g) hg m)
        (pow_nonneg (norm_nonneg g) _) ((norm_nonneg _).trans (hC x))

theorem gridMask_all_jet_bounds (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → ∀ (k : ℤ) (x : ℝ),
      ‖iteratedFDeriv ℝ m (gridMask δ k) x‖ ≤ C / δ ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_jet_bound (lineMask_smooth 0) (lineMask_compactSupport
      0) m
  refine ⟨C, hC, fun δ hδ k x => ?_⟩
  have heq : gridMask δ k = fun y => lineMask 0 (δ⁻¹ • y - (k : ℝ)) := by
    funext y
    rw [gridMask, lineMask_eq_translate]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa [abs_inv, abs_of_pos hδ, div_eq_mul_inv] using
    rescale_jet_bound (lineMask_smooth 0) hbound δ⁻¹ (k : ℝ) x

theorem productMask_eq_rescale {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    productMask δ k x = productMask 1 0 (δ⁻¹ • x - fun j => (k j : ℝ)) := by
  unfold productMask gridMask
  apply Finset.prod_congr rfl
  intro j _
  rw [lineMask_eq_translate]
  simp [div_eq_mul_inv, mul_comm]

theorem productMask_all_jet_bounds (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → ∀ (k : Fin d → ℤ) (x : Fin d → ℝ),
      ‖iteratedFDeriv ℝ m (productMask δ k) x‖ ≤ C / δ ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_jet_bound (productMask_smooth (d := d) 1 0)
    (productMask_compactSupport 1 zero_lt_one 0) m
  refine ⟨C, hC, fun δ hδ k x => ?_⟩
  have heq : productMask δ k = fun y => productMask 1 0 (δ⁻¹ • y - fun j => (k j : ℝ)) :=
    funext (productMask_eq_rescale δ k)
  rw [heq]
  simpa [abs_inv, abs_of_pos hδ, div_eq_mul_inv] using
    rescale_jet_bound (productMask_smooth 1 0) hbound δ⁻¹ (fun j => (k j : ℝ)) x

/-- Log coordinate, given by `-Real.log q / Real.log 2`. -/
def logCoordinate (q : ℝ) : ℝ := -Real.log q / Real.log 2

theorem logCoordinate_window {q : ℝ} (hq : 0 < q) :
    logCoordinate q ∈ Ioo (-1 : ℝ) 1 ↔ q ∈ Ioo (1 / 2 : ℝ) 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  change (-1 < -Real.log q / Real.log 2 ∧ -Real.log q / Real.log 2 < 1) ↔ _
  rw [lt_div_iff₀ h2, div_lt_iff₀ h2]
  constructor
  · intro h
    constructor
    · apply (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 1 / 2) hq).mp
      rw [hhalf]
      linarith [h.2]
    · apply (Real.log_lt_log_iff hq (by norm_num : (0 : ℝ) < 2)).mp
      linarith [h.1]
  · intro h
    have hl := (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 1 / 2) hq).mpr h.1
    have hu := (Real.log_lt_log_iff hq (by norm_num : (0 : ℝ) < 2)).mpr h.2
    rw [hhalf] at hl
    constructor <;> linarith

/-- A single compact annular profile; its zero extension is smooth at zero. -/
def dyadicProfile (q : ℝ) : ℝ := if 0 < q then lineMask 0 (logCoordinate q) else 0

theorem dyadicProfile_nonneg (q : ℝ) : 0 ≤ dyadicProfile q := by
  unfold dyadicProfile
  split_ifs <;> first | exact lineMask_nonneg _ _ | exact le_rfl

theorem dyadicProfile_support : support dyadicProfile = Ioo (1 / 2 : ℝ) 2 := by
  ext q
  by_cases hq : 0 < q
  · change (if 0 < q then lineMask 0 (logCoordinate q) else 0) ≠ 0 ↔ _
    rw [ite_eq_left hq, ← mem_support, lineMask_support]
    simpa using logCoordinate_window hq
  · simp only [mem_support, dyadicProfile, ite_eq_right hq, ne_eq, not_true_eq_false, mem_Ioo,
      false_iff, not_and]
    intro hl
    exact (hq (by linarith : 0 < q)).elim

theorem dyadicProfile_zero_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : dyadicProfile q = 0 := by
  by_contra h
  have hm : q ∈ support dyadicProfile := h
  rw [dyadicProfile_support] at hm
  exact (not_lt_of_ge hq) hm.1

theorem dyadicProfile_smooth : ContDiff ℝ ∞ dyadicProfile := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 0 < q
  · have heq : dyadicProfile =ᶠ[𝓝 q] fun y => lineMask 0 (logCoordinate y) := by
      filter_upwards [Ioi_mem_nhds hq] with y hy
      exact ite_eq_left hy
    exact ((lineMask_smooth 0).contDiffAt.comp q
      (((Real.contDiffAt_log.mpr hq.ne').neg).div_const (Real.log 2))).congr_of_eventuallyEq heq
  · have heq : dyadicProfile =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show q < (1 / 2 : ℝ) by linarith)] with y hy
      exact dyadicProfile_zero_of_le_half hy.le
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem dyadicProfile_tsupport : tsupport dyadicProfile = Icc (1 / 2 : ℝ) 2 := by
  rw [tsupport, dyadicProfile_support, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 2)]

theorem dyadicProfile_compactSupport : HasCompactSupport dyadicProfile := by
  rw [HasCompactSupport, dyadicProfile_tsupport]
  exact isCompact_Icc

/-- Integer Q, given by `(2 : ℝ) ^ (-(n : ℝ))`. -/
def integerQ (n : ℤ) : ℝ := (2 : ℝ) ^ (-(n : ℝ))

theorem integerQ_pos (n : ℤ) : 0 < integerQ n := Real.rpow_pos_of_pos (by norm_num) _

theorem log_integerQ (n : ℤ) : Real.log (integerQ n) = -(n : ℝ) * Real.log 2 :=
  Real.log_rpow (by norm_num) _

theorem integerQ_nat (n : ℕ) : integerQ (n : ℤ) = ChartScales.Q n := by
  simp [integerQ, ChartScales.Q, SlotColoring.dyadicQ]

/-- Dyadic mask, given by `dyadicProfile (q / integerQ n)`. -/
def dyadicMask (n : ℤ) (q : ℝ) : ℝ := dyadicProfile (q / integerQ n)

theorem dyadicMask_nonneg (n : ℤ) (q : ℝ) : 0 ≤ dyadicMask n q := dyadicProfile_nonneg _

theorem dyadicMask_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicMask n) :=
  dyadicProfile_smooth.comp (contDiff_id.div_const _)

theorem dyadicMask_eq_line (n : ℤ) {q : ℝ} (hq : 0 < q) :
    dyadicMask n q = lineMask n (logCoordinate q) := by
  have hcoord : logCoordinate (q / integerQ n) = logCoordinate q - (n : ℝ) := by
    unfold logCoordinate
    rw [Real.log_div hq.ne' (integerQ_pos n).ne', log_integerQ]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]; ring
  unfold dyadicMask dyadicProfile
  rw [ite_eq_left (div_pos hq (integerQ_pos n)), hcoord, ← lineMask_eq_translate]

theorem dyadicMask_support (n : ℤ) :
    support (dyadicMask n) = Ioo (integerQ n / 2) (2 * integerQ n) := by
  ext q
  change q / integerQ n ∈ support dyadicProfile ↔ _
  rw [dyadicProfile_support]
  simp only [mem_Ioo]
  rw [lt_div_iff₀ (integerQ_pos n), div_lt_iff₀ (integerQ_pos n)]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem dyadicMask_tsupport (n : ℤ) :
    tsupport (dyadicMask n) = Icc (integerQ n / 2) (2 * integerQ n) := by
  rw [tsupport, dyadicMask_support, closure_Ioo (by linarith [integerQ_pos n] :
    integerQ n / 2 ≠ 2 * integerQ n)]

theorem dyadicMask_compactSupport (n : ℤ) : HasCompactSupport (dyadicMask n) := by
  rw [HasCompactSupport, dyadicMask_tsupport]
  exact isCompact_Icc

theorem dyadicMask_sum_sq {q : ℝ} (hq : 0 < q) : (∑ᶠ n : ℤ, dyadicMask n q ^ 2) = 1 := by
  simp_rw [dyadicMask_eq_line _ hq]
  exact lineMask_sum_sq _

/-- Dyadic local finiteness holds on the positive `q` domain. The supports
accumulate at zero, so no global local-finiteness claim is made there. -/
theorem dyadicMask_locallyFinite :
    LocallyFinite fun n : ℤ => support (fun q : Ioi (0 : ℝ) => dyadicMask n q) := by
  have hc : Continuous (fun q : Ioi (0 : ℝ) => logCoordinate q) :=
    ((continuous_subtype_val.log (fun q => q.property.ne')).neg).div_const (Real.log 2)
  have hl : LocallyFinite fun n => support (lineMask n) :=
    lineMask_locallyFinite.subset fun _ => subset_closure
  have h := hl.preimage_continuous hc
  convert! h using 1
  funext n
  ext q
  change dyadicMask n q ≠ 0 ↔ lineMask n (logCoordinate q) ≠ 0
  rw [dyadicMask_eq_line n q.property]

theorem dyadicMask_all_jet_bounds (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (q : ℝ),
      ‖iteratedFDeriv ℝ m (dyadicMask n) q‖ ≤ C / integerQ n ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_jet_bound dyadicProfile_smooth
      dyadicProfile_compactSupport m
  refine ⟨C, hC, fun n q => ?_⟩
  have heq : dyadicMask n = fun y => dyadicProfile ((integerQ n)⁻¹ • y - 0) := by
    funext y
    simp [dyadicMask, div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa [abs_inv, abs_of_pos (integerQ_pos n), div_eq_mul_inv] using
    rescale_jet_bound dyadicProfile_smooth hbound (integerQ n)⁻¹ (0 : ℝ) q

theorem dyadicMask_zero_of_neg {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {n : ℤ} (hn : n < 0) : dyadicMask n q = 0 := by
  rw [dyadicMask_eq_line n hq]
  by_contra h
  have hm : logCoordinate q ∈ support (lineMask n) := h
  rw [lineMask_support] at hm
  have hl : logCoordinate q ≥ 0 := by
    unfold logCoordinate
    apply div_nonneg
    · exact neg_nonneg.mpr (Real.log_nonpos hq.le hq1)
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
  linarith [hm.2]

/-- Natural bands already form a partition on `0<q≤1`. -/
theorem dyadicMask_nat_sum_sq {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ᶠ n : ℕ, dyadicMask (n : ℤ) q ^ 2) = 1 := by
  let f : ℤ → ℝ := fun n => dyadicMask n q ^ 2
  have hrange : ∀ n ∈ support f, n ∈ range (fun j : ℕ => (j : ℤ)) := by
    intro n hn
    have hnonneg : 0 ≤ n := by
      by_contra h
      have hz := dyadicMask_zero_of_neg hq hq1 (lt_of_not_ge h)
      exact hn (by simp [f, hz])
    exact ⟨n.toNat, Int.toNat_of_nonneg hnonneg⟩
  calc
    (∑ᶠ n : ℕ, dyadicMask (n : ℤ) q ^ 2) = ∑ᶠ n ∈ range (fun j : ℕ => (j : ℤ)), f n :=
      (finsum_mem_range (f := f) (g := fun j : ℕ => (j : ℤ)) Int.ofNat_injective).symm
    _ = ∑ᶠ n ∈ (univ : Set ℤ), f n := by
      apply finsum_mem_inter_support_eq'
      intro n hn
      exact ⟨fun _ => mem_univ _, fun _ => hrange n hn⟩
    _ = 1 := by rw [finsum_mem_univ]; exact dyadicMask_sum_sq hq

theorem integerQ_add (n m : ℤ) : integerQ (n + m) = integerQ n * integerQ m := by
  simp only [integerQ, Int.cast_add, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

theorem dyadicMask_add (n m : ℤ) (q : ℝ) :
    dyadicMask (n + m) q = dyadicMask n (q / integerQ m) := by
  simp only [dyadicMask, integerQ_add, div_div, mul_comm]

/-- After any chosen starting band, the retained bands partition the smaller
active range `0<q≤Q_N`. In particular one can retain only `n≥4`. -/
theorem dyadicMask_tail_sum_sq (N : ℕ) {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) :
    (∑ᶠ n : ℕ, dyadicMask ((n + N : ℕ) : ℤ) q ^ 2) = 1 := by
  have hq' : 0 < q / integerQ (N : ℤ) := div_pos hq (integerQ_pos _)
  have hq1' : q / integerQ (N : ℤ) ≤ 1 := by
    apply (div_le_one (integerQ_pos _)).mpr
    simpa only [integerQ_nat] using hqN
  have heq : (fun n : ℕ => dyadicMask ((n + N : ℕ) : ℤ) q ^ 2) =
      fun n : ℕ => dyadicMask (n : ℤ) (q / integerQ (N : ℤ)) ^ 2 := by
    funext n
    rw [Nat.cast_add, dyadicMask_add]
  rw [heq]
  exact dyadicMask_nat_sum_sq hq' hq1'

/-- Native spacing, given by `(ChartScales.S n ^ 3)⁻¹`. -/
def nativeSpacing (n : ℕ) : ℝ := (ChartScales.S n ^ 3)⁻¹

theorem nativeSpacing_pos {n : ℕ} (hn : 1 ≤ n) : 0 < nativeSpacing n :=
  inv_pos.mpr (pow_pos (ChartScales.S_pos hn) _)

/-- The actual three-coordinate partition at slow mesh `S_n^(-3)`. -/
def slowMask (n : ℕ) (k : SlotColoring.Grid) (x : SlotColoring.Position) : ℝ :=
  productMask (nativeSpacing n) k x

theorem slowMask_nonneg (n : ℕ) (k : SlotColoring.Grid) (x : SlotColoring.Position) :
    0 ≤ slowMask n k x := productMask_nonneg _ _ _

theorem slowMask_smooth (n : ℕ) (k : SlotColoring.Grid) : ContDiff ℝ ∞ (slowMask n k) :=
  productMask_smooth _ _

theorem slowMask_sum_sq (n : ℕ) (x : SlotColoring.Position) :
    (∑ᶠ k : SlotColoring.Grid, slowMask n k x ^ 2) = 1 := productMask_sum_sq _ _

theorem slowMask_locallyFinite (n : ℕ) :
    LocallyFinite fun k : SlotColoring.Grid => tsupport (slowMask n k) :=
  (productMask_locallyFinite _).closure

theorem slowMask_compactSupport {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    HasCompactSupport (slowMask n k) := productMask_compactSupport _ (nativeSpacing_pos hn) _

theorem slowMask_tsupport_subset {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    tsupport (slowMask n k) ⊆ Set.pi univ (fun j =>
      Icc (nativeSpacing n * k j - nativeSpacing n) (nativeSpacing n * k j + nativeSpacing n)) :=
  productMask_tsupport_subset _ (nativeSpacing_pos hn) _

theorem slowMask_jet_tsupport_subset {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (slowMask n k)) ⊆ Set.pi univ (fun j =>
      Icc (nativeSpacing n * k j - nativeSpacing n) (nativeSpacing n * k j + nativeSpacing n)) :=
  (tsupport_iteratedFDeriv_subset m).trans (slowMask_tsupport_subset hn k)

/-- Every fixed jet costs the fixed power `S^(3m)`, uniformly in all grid nodes. -/
theorem slowMask_all_jet_bounds (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ (k : SlotColoring.Grid) (x : SlotColoring.Position),
      ‖iteratedFDeriv ℝ m (slowMask n k) x‖ ≤ C * ChartScales.S n ^ (3 * m) := by
  obtain ⟨C, hC, hb⟩ := productMask_all_jet_bounds 3 m
  refine ⟨C, hC, fun n hn k x => ?_⟩
  have h := hb (nativeSpacing n) (nativeSpacing_pos hn) k x
  unfold slowMask
  simpa [nativeSpacing, div_eq_mul_inv, ← pow_mul] using h

/-- The manuscript's three physical-to-slow coordinate rescalings. -/
def slowCoordinates (D : ℝ) (n : ℕ) (x : SlotColoring.Position) : SlotColoring.Position :=
  fun j => x j / ChartScales.Q n ^ SlotColoring.axisExponent D j

theorem slowCoordinates_smooth (D : ℝ) (n : ℕ) : ContDiff ℝ ∞ (slowCoordinates D n) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℝ ℝ j).div_const _

/-- Physical slow mask, given by `slowMask n k (slowCoordinates D n x)`. -/
def physicalSlowMask (D : ℝ) (n : ℕ) (k : SlotColoring.Grid) (x : SlotColoring.Position) : ℝ :=
  slowMask n k (slowCoordinates D n x)

theorem physicalSlowMask_smooth (D : ℝ) (n : ℕ) (k : SlotColoring.Grid) :
    ContDiff ℝ ∞ (physicalSlowMask D n k) :=
  (slowMask_smooth n k).comp (slowCoordinates_smooth D n)

theorem physicalSlowMask_sum_sq (D : ℝ) (n : ℕ) (x : SlotColoring.Position) :
    (∑ᶠ k : SlotColoring.Grid, physicalSlowMask D n k x ^ 2) = 1 :=
  slowMask_sum_sq n _

theorem physicalSlowMask_locallyFinite (D : ℝ) (n : ℕ) :
    LocallyFinite fun k => support (physicalSlowMask D n k) := by
  have hl : LocallyFinite fun k => support (slowMask n k) :=
    (slowMask_locallyFinite n).subset fun _ => subset_closure
  exact hl.preimage_continuous (slowCoordinates_smooth D n).continuous

theorem physicalSlowMask_tsupport_smallBox (D : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (k : SlotColoring.Grid) :
    tsupport (physicalSlowMask D n k) ⊆ Set.pi univ (fun j =>
      Icc (SlotColoring.width D j n * k j - SlotColoring.width D j n)
        (SlotColoring.width D j n * k j + SlotColoring.width D j n)) := by
  apply closure_minimal
  · intro x hx j _
    have hs : slowCoordinates D n x ∈ support (productMask (nativeSpacing n) k) := hx
    rw [productMask_support] at hs
    have hj := mem_iInter.mp hs j
    change x j / ChartScales.Q n ^ SlotColoring.axisExponent D j ∈
      support (gridMask (nativeSpacing n) (k j)) at hj
    rw [gridMask_support _ (nativeSpacing_pos hn)] at hj
    have hp : 0 < ChartScales.Q n ^ SlotColoring.axisExponent D j :=
      Real.rpow_pos_of_pos (ChartScales.Q_pos n) _
    have hlo := (lt_div_iff₀ hp).mp hj.1
    have hhi := (div_lt_iff₀ hp).mp hj.2
    have hw : SlotColoring.width D j n =
        ChartScales.Q n ^ SlotColoring.axisExponent D j * nativeSpacing n := by
      unfold SlotColoring.width
      rw [SlotColoring.spacing_eq_scaled_mesh]
      simp only [ChartScales.Q, nativeSpacing, ChartScales.S, one_div]
    change x j ∈ Icc (SlotColoring.width D j n * k j - SlotColoring.width D j n)
      (SlotColoring.width D j n * k j + SlotColoring.width D j n)
    rw [hw]
    constructor <;> nlinarith
  · exact (isCompact_univ_pi fun _ => isCompact_Icc).isClosed

theorem physicalSlowMask_compactSupport (D : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (k : SlotColoring.Grid) : HasCompactSupport (physicalSlowMask D n k) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_closure
    (physicalSlowMask_tsupport_smallBox D hn k)

/-- The constructed masks fit inside the exact enlarged boxes already colored
in `SlotColoring`, for either pulse sign. -/
theorem physicalSlowMask_tsupport_subset_physicalBox (D : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (k : SlotColoring.Grid) (sign : Bool) :
    tsupport (physicalSlowMask D n k) ⊆ SlotColoring.physicalBox D (n, k, sign) := by
  intro x hx j
  have hj := physicalSlowMask_tsupport_smallBox D hn k hx j (mem_univ j)
  have hp := SlotColoring.width_pos D j hn
  change |x j - SlotColoring.width D j n * (k j : ℝ)| ≤ 2 * SlotColoring.width D j n
  rw [abs_le]
  constructor <;> linarith [hj.1, hj.2]

theorem physicalSlowMask_jet_tsupport_subset_physicalBox (D : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (k : SlotColoring.Grid) (sign : Bool) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (physicalSlowMask D n k)) ⊆
      SlotColoring.physicalBox D (n, k, sign) :=
  (tsupport_iteratedFDeriv_subset m).trans (physicalSlowMask_tsupport_subset_physicalBox D hn k
      sign)

/-- Label mask, given by `dyadicMask (n : ℤ) p.1 * slowMask n k p.2`. -/
def labelMask (n : ℕ) (k : SlotColoring.Grid) (p : ℝ × SlotColoring.Position) : ℝ :=
  dyadicMask (n : ℤ) p.1 * slowMask n k p.2

theorem labelMask_nonneg (n : ℕ) (k : SlotColoring.Grid) (p : ℝ × SlotColoring.Position) :
    0 ≤ labelMask n k p := mul_nonneg (dyadicMask_nonneg _ _) (slowMask_nonneg _ _ _)

theorem labelMask_smooth (n : ℕ) (k : SlotColoring.Grid) : ContDiff ℝ ∞ (labelMask n k) :=
  ((dyadicMask_smooth _).comp contDiff_fst).mul ((slowMask_smooth _ _).comp contDiff_snd)

theorem labelMask_compactSupport {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    HasCompactSupport (labelMask n k) := by
  have hc : IsCompact (tsupport (dyadicMask (n : ℤ)) ×ˢ tsupport (slowMask n k)) :=
    (dyadicMask_compactSupport _).prod (slowMask_compactSupport hn k)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro p hp
  have h := mul_ne_zero_iff.mp hp
  exact ⟨subset_closure h.1, subset_closure h.2⟩

theorem locallyFinite_pair_inter {ι κ X : Type*} [TopologicalSpace X]
    {U : ι → Set X} {V : ι → κ → Set X}
    (hU : LocallyFinite U) (hV : ∀ i, LocallyFinite (V i)) :
    LocallyFinite fun p : ι × κ => U p.1 ∩ V p.1 p.2 := by
  classical
  intro x
  obtain ⟨B, hB, hfB⟩ := hU x
  choose W hW hfW using fun i => hV i x
  let F : Finset ι := hfB.toFinset
  let P : Finset (ι × κ) := F.biUnion fun i => (hfW i).toFinset.image fun k => (i, k)
  refine ⟨B ∩ ⋂ i ∈ F, W i, inter_mem hB ((biInter_finset_mem F).mpr (fun i _ => hW i)),
    P.finite_toSet.subset ?_⟩
  rintro ⟨i, k⟩ ⟨y, ⟨hyU, hyV⟩, hyB, hyW⟩
  have hi : i ∈ F := hfB.mem_toFinset.mpr ⟨y, hyU, hyB⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, Finset.mem_image.mpr ⟨k, ?_, rfl⟩⟩
  exact (hfW i).mem_toFinset.mpr ⟨y, hyV, mem_iInter₂.mp hyW i hi⟩

theorem labelMask_locallyFinite :
    LocallyFinite fun p : ℕ × SlotColoring.Grid =>
      support (fun z : Ioi (0 : ℝ) × SlotColoring.Position => labelMask p.1 p.2 (z.1, z.2)) := by
  have hnat : LocallyFinite fun n : ℕ =>
      support (fun q : Ioi (0 : ℝ) => dyadicMask (n : ℤ) q) :=
    dyadicMask_locallyFinite.comp_injective Int.ofNat_injective
  have houter := hnat.preimage_continuous
    (continuous_fst : Continuous (Prod.fst : Ioi (0 : ℝ) × SlotColoring.Position → Ioi (0 : ℝ)))
  have hinner (n : ℕ) : LocallyFinite fun k : SlotColoring.Grid =>
      (Prod.snd : Ioi (0 : ℝ) × SlotColoring.Position → SlotColoring.Position) ⁻¹'
        support (slowMask n k) :=
    ((slowMask_locallyFinite n).subset fun _ => subset_closure).preimage_continuous continuous_snd
  have h := locallyFinite_pair_inter houter hinner
  convert! h using 1
  funext p
  ext z
  simp only [mem_support, labelMask, mul_ne_zero_iff, mem_inter_iff, mem_preimage]

/-- Finite support makes an ordinary sum over pairs equal its iterated sum. -/
theorem finsum_pair_eq {ι κ : Type*} {f : ι × κ → ℝ} (hf : (support f).Finite) :
    (∑ᶠ p, f p) = ∑ᶠ i, ∑ᶠ k, f (i, k) := by
  classical
  let A : Finset ι := hf.toFinset.image Prod.fst
  let B : Finset κ := hf.toFinset.image Prod.snd
  have hA {i k} (h : f (i, k) ≠ 0) : i ∈ A :=
    Finset.mem_image.mpr ⟨(i, k), hf.mem_toFinset.mpr h, rfl⟩
  have hB {i k} (h : f (i, k) ≠ 0) : k ∈ B :=
    Finset.mem_image.mpr ⟨(i, k), hf.mem_toFinset.mpr h, rfl⟩
  have hp : support f ⊆ (A.product B : Finset (ι × κ)) :=
    fun p hp => Finset.mem_product.mpr ⟨hA hp, hB hp⟩
  have hi : support (fun i => ∑ᶠ k, f (i, k)) ⊆ (A : Set ι) := by
    intro i hi
    by_cases hmem : i ∈ A
    · exact hmem
    · exfalso
      apply hi
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      by_contra h
      exact hmem (hA h)
  rw [finsum_eq_sum_of_support_subset _ hp, finsum_eq_sum_of_support_subset _ hi]
  apply (Finset.sum_product A B f).trans
  apply Finset.sum_congr rfl
  intro i _
  exact (finsum_eq_sum_of_support_subset _ (fun k hk => hB hk)).symm

/-- The exact normalized squared partition obtained by multiplying dyadic and
slow-grid masks; any lower band cutoff can be imposed by shrinking `q`. -/
theorem labelMask_tail_sum_sq (N : ℕ) {p : ℝ × SlotColoring.Position}
    (hq : 0 < p.1) (hqN : p.1 ≤ ChartScales.Q N) :
    (∑ᶠ n : ℕ, ∑ᶠ k : SlotColoring.Grid, labelMask (n + N) k p ^ 2) = 1 := by
  have hs (n : ℕ) : (∑ᶠ k : SlotColoring.Grid, labelMask n k p ^ 2) = dyadicMask (n : ℤ) p.1 ^ 2 :=
      by
    have hfinite : (support (fun k : SlotColoring.Grid => slowMask n k p.2 ^ 2)).Finite := by
      apply ((productMask_locallyFinite (nativeSpacing n)).point_finite p.2).subset
      intro k hk hz
      exact hk (by simp [slowMask, hz])
    simp only [labelMask, mul_pow]
    rw [← mul_finsum _ _, slowMask_sum_sq, mul_one]
  simp_rw [hs]
  exact dyadicMask_tail_sum_sq N hq hqN

theorem labelMask_tail_total_sum_sq (N : ℕ) {p : ℝ × SlotColoring.Position}
    (hq : 0 < p.1) (hqN : p.1 ≤ ChartScales.Q N) :
    (∑ᶠ a : ℕ × SlotColoring.Grid, labelMask (a.1 + N) a.2 p ^ 2) = 1 := by
  have hf : (support (fun a : ℕ × SlotColoring.Grid => labelMask a.1 a.2 p)).Finite :=
    labelMask_locallyFinite.point_finite (⟨p.1, hq⟩, p.2)
  have hinj : Function.Injective (fun a : ℕ × SlotColoring.Grid => (a.1 + N, a.2)) := by
    intro a b h
    apply Prod.ext
    · have he := congrArg Prod.fst h
      exact Nat.add_right_cancel he
    · simpa only [] using congrArg (fun z : ℕ × SlotColoring.Grid => z.2) h
  have hp := hf.preimage hinj.injOn
  have hs : (support (fun a : ℕ × SlotColoring.Grid => labelMask (a.1 + N) a.2 p ^ 2)).Finite := by
    apply hp.subset
    intro a ha hzero
    change labelMask (a.1 + N) a.2 p = 0 at hzero
    exact ha (by change labelMask (a.1 + N) a.2 p ^ 2 = 0; rw [hzero]; norm_num)
  rw [finsum_pair_eq hs]
  exact labelMask_tail_sum_sq N hq hqN

end NavierStokes.SquaredPartition
