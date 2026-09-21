/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Complex.Analytic
public import LeanPool.CarlsonFunctions.Dirichlet.Polynomial
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Smooth
public import LeanPool.CarlsonFunctions.Dirichlet.IntegrationByParts
public import LeanPool.CarlsonFunctions.Pochhammer.IncompleteMellin
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The Dirichlet or Simplex Mellin transform

By the regularized Dirichlet transform we understand the transformation from a complex-valued
function $f$ on the standard simplex $E^{k-1}$ (embedded in $ℝ^k$) to an analytic function of
$b∈ℂ^k$ that is the analytic continuation of `regDirichletIntegral b f`.

Terminology here is provisional. We are using the name (regularized) Dirichlet transform
because it is the central transform in Carlson's theory of Dirichlet averages. However,
the name (regularized) simplex Mellin transform is also appropriate.

## Main definitions and results

* `dirichletConvergenceRegion`: the parameter region `re (b i) > -N`.
* `exists_regDirichletContinuation_of_contDiffNear`: `(card ι - 1) * N` derivatives give
  analytic continuation to the region `re (b i) > -N`.
* `exists_entire_regDirichletContinuation_of_contDiffNear`: smoothness to every finite order
  gives an entire continuation.

Polynomial transforms are developed in `Dirichlet.Polynomial`; smooth simplex functions,
tangential derivatives, and face restrictions are developed in `StdSimplexMeasure.Smooth`.
`Dirichlet.Transform.Parametric` retains holomorphic auxiliary parameters throughout the
finite-shift construction and gluing. The shared shift-region and power-partition lemmas
are exported here for that construction.

## References
[Carl77] Carlson, Bille Chandler. "Special functions of applied mathematics." Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory MeasureTheory.Measure Set
open scoped Classical Topology

@[expose] public noncomputable section DirichletTransform

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-! ## Finite-order analytic continuation -/

/-- The region of Dirichlet parameters satisfying `-N < re (b i)` in every coordinate. -/
def dirichletConvergenceRegion (N : ℕ) : Set (ι → ℂ) :=
  {b | ∀ i, -(N : ℝ) < (b i).re}

/-- Dirichlet convergence regions are open. -/
theorem isOpen_dirichletConvergenceRegion (N : ℕ) :
    IsOpen (dirichletConvergenceRegion (ι := ι) N) := by
  rw [show dirichletConvergenceRegion (ι := ι) N =
      ⋂ i, {b : ι → ℂ | -(N : ℝ) < (b i).re} by
    ext b
    simp [dirichletConvergenceRegion]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt (continuous_const : Continuous fun _ : ι → ℂ ↦ -(N : ℝ))
      (Complex.continuous_re.comp (continuous_apply i : Continuous fun b : ι → ℂ ↦ b i))

omit [Fintype ι] in
/-- The order-zero convergence region is the ordinary domain of absolute convergence. -/
@[simp] theorem dirichletConvergenceRegion_zero :
    dirichletConvergenceRegion (ι := ι) 0 = mvBetaConvergent := by
  ext b
  simp [dirichletConvergenceRegion, mvBetaConvergent]

omit [Fintype ι] in
/-- Increasing the available regularity enlarges the corresponding convergence region. -/
theorem dirichletConvergenceRegion_mono {N M : ℕ} (hNM : N ≤ M) :
    dirichletConvergenceRegion (ι := ι) N ⊆ dirichletConvergenceRegion M := by
  intro b hb i
  exact (neg_le_neg (Nat.cast_le.mpr hNM)).trans_lt (hb i)

omit [Fintype ι] in
/-- The ordinary convergence region is contained in every finite-order continuation region. -/
theorem mvBetaConvergent_subset_dirichletConvergenceRegion (N : ℕ) :
    mvBetaConvergent ⊆ dirichletConvergenceRegion (ι := ι) N := by
  rw [← dirichletConvergenceRegion_zero (ι := ι)]
  exact dirichletConvergenceRegion_mono (Nat.zero_le N)

/-- On a singleton index type the regularized Dirichlet integral is `f 1 / Gamma b`, hence
entire in the Dirichlet parameter. -/
theorem exists_regDirichletContinuation_of_unique [Unique ι]
    {f : (ι → ℝ) → ℂ} (_hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  let ones : ι → ℝ := fun _ => 1
  refine ⟨fun b => f ones * (Gamma (b default))⁻¹, ?_, ?_⟩
  · intro b _
    have hproj : AnalyticAt ℂ (fun c : ι → ℂ => c default) b :=
      (ContinuousLinearMap.proj (default : ι) : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    have hG : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) (b default) :=
      differentiable_one_div_Gamma.analyticAt _
    exact (analyticAt_const.mul (hG.comp_of_eq hproj rfl)).analyticWithinAt
  · intro b hb
    have hdirac : Measure.stdSimplexMeasure (ι := ι) = Measure.dirac ones :=
      Measure.stdSimplexMeasure_unique
    have hones : ones ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
      simp [ones, Convexity.StdSimplex.coordinateSet]
    change f ones * (Gamma (b default))⁻¹ =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, regDirichletDensity b u * f u ∂Measure.stdSimplexMeasure
    rw [hdirac]
    have hinter : ones ∈ stdSimplexInterior :=
      ⟨hones, fun _ => by simp [ones]⟩
    rw [MeasureTheory.setIntegral_dirac]
    simp [regDirichletDensity, hinter, ones, Unique.eq_default, mul_comm, hones]

/-- The empty-index integral is identically zero, hence entire. -/
theorem exists_regDirichletContinuation_of_isEmpty [IsEmpty ι]
    (f : (ι → ℝ) → ℂ) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  refine ⟨fun _ => 0, analyticOn_const, ?_⟩
  intro b _
  simp [regDirichletIntegral, MeasureTheory.Measure.stdSimplexMeasure_empty]

/-- At order zero, the native regularized Dirichlet integral itself supplies the analytic
function on the ordinary convergence region. -/
theorem exists_regDirichletContinuation_zero {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex 0 f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion 0) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  refine ⟨fun b ↦ regDirichletIntegral b f, ?_, fun _ _ ↦ rfl⟩
  simpa using regDirichletIntegral_analyticOn hf.continuousOn

omit [Fintype ι] in
/-- Dirichlet continuation regions are convex, hence preconnected. -/
theorem isPreconnected_dirichletConvergenceRegion (N : ℕ) :
    IsPreconnected (dirichletConvergenceRegion (ι := ι) N) := by
  have hconv : Convex ℝ (dirichletConvergenceRegion (ι := ι) N) := by
    intro x hx y hy a b ha hb hab i
    have hx' := hx i
    have hy' := hy i
    have hre :
        ((a • x + b • y) i).re = a * (x i).re + b * (y i).re := by
      simp [Pi.add_apply, Pi.smul_apply, add_re, real_smul, mul_re, ofReal_re]
    rw [hre]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have : b = 1 := by linarith
      simpa [this]
    · have hsum : a * (-(N : ℝ)) + b * (-(N : ℝ)) = -(N : ℝ) := by
        rw [← add_mul, hab, one_mul]
      have hlt :
          a * (-(N : ℝ)) + b * (-(N : ℝ)) < a * (x i).re + b * (y i).re :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx' ha')
          (mul_le_mul_of_nonneg_left (le_of_lt hy') hb)
      rw [hsum] at hlt
      exact hlt
  exact hconv.isPreconnected

/-- Two analytic continuations to a Dirichlet convergence region that agree on the ordinary
convergence region agree everywhere on the continuation region. -/
theorem eqOn_dirichletContinuation {N : ℕ} {F G : (ι → ℂ) → ℂ}
    (hF : AnalyticOn ℂ F (dirichletConvergenceRegion N))
    (hG : AnalyticOn ℂ G (dirichletConvergenceRegion N))
    (hEq : EqOn F G mvBetaConvergent) :
    EqOn F G (dirichletConvergenceRegion N) := by
  have hopen := isOpen_dirichletConvergenceRegion (ι := ι) N
  have hF' := (hopen.analyticOn_iff_analyticOnNhd).1 hF
  have hG' := (hopen.analyticOn_iff_analyticOnNhd).1 hG
  have hz0 : (fun _ : ι => (1 : ℂ)) ∈ dirichletConvergenceRegion (ι := ι) N := by
    intro i
    change -(N : ℝ) < (1 : ℂ).re
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp [one_re]
    linarith
  have hz0β : (fun _ : ι => (1 : ℂ)) ∈ mvBetaConvergent (ι := ι) := by
    intro _
    simp
  have hnhds : mvBetaConvergent (ι := ι) ∈ 𝓝 (fun _ : ι => (1 : ℂ)) :=
    isOpen_mvBetaConvergent.mem_nhds hz0β
  have hev : F =ᶠ[𝓝 (fun _ : ι => (1 : ℂ))] G :=
    (hEq.eventuallyEq_of_mem hnhds)
  exact hF'.eqOn_of_preconnected_of_eventuallyEq hG'
    (isPreconnected_dirichletConvergenceRegion N) hz0 hev

/-- Jacobian identity for the complementary-coordinate exponent in a simplex slice. -/
theorem slice_jacobian_exponent (i : ι) [Nontrivial ι] (b : ι → ℂ) :
    ((Fintype.card ι - 2 : ℕ) : ℂ) + ∑ q : {j : ι // j ≠ i}, (b q - 1) =
      ∑ q : {j : ι // j ≠ i}, b q - 1 := by
  have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
  have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℂ) = (Fintype.card ι : ℂ) - 1 := by
    rw [hcard_rest, Nat.cast_sub (by omega)]
    norm_num
  have hcast_two : ((Fintype.card ι - 2 : ℕ) : ℂ) = (Fintype.card ι : ℂ) - 2 := by
    rw [Nat.cast_sub hcard_two]
    norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hcast_rest, hcast_two]
  ring

/-- Native slice formula: a regularized Dirichlet integral is an incomplete Mellin transform
in one coordinate of a complementary regularized Dirichlet integral on the opposite face. -/
theorem regDirichletIntegral_split_at [Nontrivial ι] (i : ι)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ} (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral b f =
      regIncompleteMellin (b i) 1 (fun t =>
        (1 - (t : ℂ)) ^ (∑ q : {j : ι // j ≠ i}, b q - 1) *
          regDirichletIntegral (fun q : {j : ι // j ≠ i} => b q)
            (stdSimplexSlice i t f)) := by
  classical
  let b' : {j : ι // j ≠ i} → ℂ := fun q ↦ b q
  let c : ℂ := ∑ q : {j : ι // j ≠ i}, b q
  have hb' : b' ∈ mvBetaConvergent := fun q ↦ hb q
  have hint : IntegrableOn
      (fun u : ι → ℝ ↦ (∏ j, (u j : ℂ) ^ (b j - 1)) * f u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure :=
    (Complex.integrableOn_mvBetaMonomial b hb).mul_continuousOn hf
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
  rw [regDirichletIntegral_eq_prod_invGamma_mul,
    integral_stdSimplex_split_at i _ hint]
  have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      (∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
        ((∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
          (b k - 1)) * f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)))
          ∂stdSimplexMeasure) =
        ((t : ℂ) ^ (b i - 1) *
          (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
          ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
            (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
              ∂stdSimplexMeasure := by
    intro t ht
    calc
      _ = ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
          ((t : ℂ) ^ (b i - 1) *
            (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
              ((∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v)
            ∂stdSimplexMeasure := by
          apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
          intro v hv
          change
            (∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
                (b k - 1)) * f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) = _
          rw [prod_cpow_stdSimplexCoordMap_scale i b ht hv]
          simp only [stdSimplexSlice]
          ring
      _ = _ := by rw [integral_const_mul]
  have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ((1 - t) ^ (Fintype.card ι - 2)) •
          (∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
            ((∏ k, ((stdSimplexCoordMap i
              (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^ (b k - 1)) *
                f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)))
              ∂stdSimplexMeasure) =
        (t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1) *
          ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
            (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
              ∂stdSimplexMeasure := by
    filter_upwards [ae_restrict_of_ae
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
    have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
    rw [hinner t ht]
    have hbase : (1 - (t : ℂ)) ≠ 0 := by
      intro hz
      apply ht.2.ne
      exact_mod_cast (sub_eq_zero.mp hz).symm
    rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.cpow_natCast]
    push_cast
    calc
      (1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
          (((t : ℂ) ^ (b i - 1) *
            (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
              ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
                  ∂stdSimplexMeasure) =
          (t : ℂ) ^ (b i - 1) *
            ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
              (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                  (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
                    ∂stdSimplexMeasure := by ring
      _ = _ := by
        rw [← Complex.cpow_add _ _ hbase, slice_jacobian_exponent i b]
  rw [integral_congr_ae houter]
  unfold regIncompleteMellin
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  rw [mul_assoc]
  apply congrArg ((Gamma (b i))⁻¹ * ·)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [regDirichletIntegral_eq_prod_invGamma_mul]
  dsimp only [c, b']
  ring

/-! ### Continuation by tangential integration by parts -/

/-- Iterated parameter shifts. Each step raises a free parameter and either lowers the
omitted parameter or takes one tangential derivative of the integrand. -/
private def shiftedDirichletIntegral (i : ι) :
    List {j : ι // j ≠ i} → (ι → ℂ) → ((ι → ℝ) → ℂ) → ℂ
  | [], b, f => regDirichletIntegral b f
  | j :: l, b, f =>
      shiftedDirichletIntegral i l (b + Pi.single (j : ι) 1 - Pi.single i 1) f -
        shiftedDirichletIntegral i l (b + Pi.single (j : ι) 1)
          (stdSimplexTangentDeriv j i f)

/-- Convergence region for a finite list of tangential parameter shifts. -/
def shiftRegion (i : ι) (l : List {j : ι // j ≠ i}) : Set (ι → ℂ) :=
  {b | (l.length : ℝ) < (b i).re ∧ ∀ j : {j : ι // j ≠ i},
    0 < (b j).re + (l.count j : ℝ)}

omit [Fintype ι] in
theorem shiftRegion_cons (i : ι) (j : {j : ι // j ≠ i})
    (l : List {j : ι // j ≠ i}) {b : ι → ℂ} (hb : b ∈ shiftRegion i (j :: l)) :
    (b + Pi.single (j : ι) 1 - Pi.single i 1) ∈ shiftRegion i l ∧
      (b + Pi.single (j : ι) 1) ∈ shiftRegion i l := by
  have hi : (l.length : ℝ) + 1 < (b i).re := by simpa [shiftRegion] using hb.1
  have hrest (k : {j : ι // j ≠ i}) :
      0 < ((b + Pi.single (j : ι) 1 : ι → ℂ) k).re + (l.count k : ℝ) := by
    have hk := hb.2 k
    by_cases hkj : k = j
    · subst k
      simpa [List.count_cons, add_assoc, add_left_comm, add_comm] using hk
    · have hval : (k : ι) ≠ j := fun h => hkj (Subtype.ext h)
      simpa [List.count_cons, hkj, hval, Ne.symm hkj] using hk
  constructor
  · constructor
    · simpa [Pi.single_eq_of_ne j.property.symm] using (lt_sub_iff_add_lt.mpr hi)
    · intro k
      simpa [Pi.single_eq_of_ne k.property] using hrest k
  · constructor
    · simpa [Pi.single_eq_of_ne j.property.symm] using (lt_trans (lt_add_one _) hi)
    · exact hrest

private theorem analyticOnNhd_shiftedDirichletIntegral (i : ι)
    (l : List {j : ι // j ≠ i}) {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex l.length f) :
    AnalyticOnNhd ℂ (fun b => shiftedDirichletIntegral i l b f) (shiftRegion i l) := by
  induction l generalizing f with
  | nil =>
      intro b hb
      have hb' : b ∈ mvBetaConvergent := by
        intro j
        by_cases hji : j = i
        · subst j; simpa [shiftRegion] using hb.1
        · simpa using hb.2 ⟨j, hji⟩
      exact (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
        (regDirichletIntegral_analyticOn hf.continuousOn)) b hb'
  | cons j l ih =>
      have hf' : ContDiffNearStdSimplex (l.length + 1) f := hf
      have h0 := ih (hf'.of_le (Nat.le_succ _))
      have h1 := ih (hf'.tangentDeriv j i)
      intro b hb
      obtain ⟨hb0, hb1⟩ := shiftRegion_cons i j l hb
      exact ((h0 _ hb0).comp_of_eq
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const) rfl).sub
        ((h1 _ hb1).comp_of_eq (analyticAt_id.add analyticAt_const) rfl)

private theorem shiftedDirichletIntegral_eq (i : ι) (l : List {j : ι // j ≠ i})
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex l.length f)
    {b : ι → ℂ} (hb : ∀ k, (l.length : ℝ) + 2 < (b k).re) :
    shiftedDirichletIntegral i l b f = regDirichletIntegral b f := by
  induction l generalizing f b with
  | nil => rfl
  | cons j l ih =>
      have hf' : ContDiffNearStdSimplex (l.length + 1) f := hf
      have hdf := hf'.tangentDeriv j i
      have hshift (k : ι) : (l.length : ℝ) + 2 < ((b + Pi.single (j : ι) 1 : ι → ℂ) k).re := by
        have hk := hb k
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
        by_cases hkj : k = j
        · subst k; simp; linarith
        · simpa [Pi.single_eq_of_ne hkj] using (by linarith : (l.length : ℝ) + 2 < (b k).re)
      have hshift' (k : ι) :
          (l.length : ℝ) + 2 < ((b + Pi.single (j : ι) 1 - Pi.single i 1 : ι → ℂ) k).re := by
        by_cases hki : k = i
        · subst k
          have hk := hb i
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
          simp [Pi.single_eq_of_ne j.property.symm]
          linarith
        · simpa [Pi.single_eq_of_ne hki] using hshift k
      rw [shiftedDirichletIntegral, ih (hf'.of_le (Nat.le_succ _)) hshift', ih hdf hshift]
      have hdiff : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, DifferentiableAt ℝ f u := by
        obtain ⟨U, hU, hsub, hfU⟩ := hf'
        intro u hu
        exact (hfU.contDiffAt (hU.mem_nhds (hsub hu))).differentiableAt (by simp)
      have H := regDirichletIntegral_tangent_ibp i j (b + Pi.single (j : ι) 1)
        (fun k => lt_of_le_of_lt
          (by have := Nat.cast_nonneg (α := ℝ) l.length; linarith : (2 : ℝ) ≤ l.length + 2)
          (hshift k)) hdiff hdf.continuousOn
      rw [add_sub_cancel_right] at H
      change regDirichletIntegral (b + Pi.single (j : ι) 1 - Pi.single i 1) f -
        regDirichletIntegral (b + Pi.single (j : ι) 1)
          (fun u => fderiv ℝ f u (Pi.single (j : ι) 1 - Pi.single i 1)) = _
      rw [H]
      ring

/-- Each free coordinate is shifted `N` times. -/
def shiftList (i : ι) (N : ℕ) : List {j : ι // j ≠ i} :=
  (List.replicate N (Finset.univ.toList : List {j : ι // j ≠ i})).flatten

theorem shiftList_length (i : ι) (N : ℕ) :
    (shiftList i N).length = (Fintype.card ι - 1) * N := by
  have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [shiftList, List.length_flatten, hcard, mul_comm]

theorem shiftList_count (i : ι) (N : ℕ) (j : {j : ι // j ≠ i}) :
    (shiftList i N).count j = N := by
  have hc : (Finset.univ.toList : List {j : ι // j ≠ i}).count j = 1 :=
    List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)
  simp [shiftList, List.count_flatten, hc]

theorem regDirichletIntegral_power_partition {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) (M : ℕ) :
    regDirichletIntegral b f =
      ∑ i, (ascPochhammer ℂ M).eval (b i) *
        regDirichletIntegral (b + Pi.single i (M : ℂ))
          (fun u => f u / powerPartitionDenom M u) := by
  let g := fun u => f u / powerPartitionDenom M u
  have hgc : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hf.div (by unfold powerPartitionDenom; fun_prop)
      (fun u hu => powerPartitionDenom_ne_zero M hu)
  have hsplit : regDirichletIntegral b f =
      ∑ i, regDirichletIntegral b (fun u => (u i : ℂ) ^ M * g u) := by
    have hint (i : ι) : IntegrableOn
        (fun u => regDirichletDensity b u * ((u i : ℂ) ^ M * g u))
        (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
      exact integrableOn_regDirichletDensity_mul b hb
        ((by fun_prop : ContinuousOn (fun u : ι → ℝ => (u i : ℂ) ^ M)
          (Convexity.StdSimplex.coordinateSet ℝ ι)).mul hgc)
    unfold regDirichletIntegral
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    dsimp only
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    change regDirichletDensity b u * f u =
      regDirichletDensity b u * (powerPartitionDenom M u * (f u / powerPartitionDenom M u))
    rw [mul_div_cancel₀ _ (powerPartitionDenom_ne_zero M hu)]
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro i _
  have h := regDirichletIntegral_monomial_mul hb (Pi.single i M) g
  simpa [mvPochhammer, Pi.single_apply, apply_ite, Pi.add_def, add_ite, g] using! h

/-- If `f` has `(card ι - 1) * N` continuous derivatives near the closed simplex,
its regularized Dirichlet integral continues to `-N < re (b i)` for every `i`.

The dimension factor is essential: the former statement with only `N` derivatives was
false at intersecting faces. The proof uses `N` tangential integrations by parts in
each of the `card ι - 1` free coordinates. -/
theorem exists_regDirichletContinuation_of_contDiffNear {N : ℕ}
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex ((Fintype.card ι - 1) * N) f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion N) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      obtain ⟨F, hF, hEq⟩ := exists_regDirichletContinuation_of_isEmpty f
      exact ⟨F, hF.mono fun _ _ => trivial, hEq⟩
  | inr _ =>
      let L := (Fintype.card ι - 1) * N
      let M := L + N
      let g := fun u => f u / powerPartitionDenom M u
      have hg : ContDiffNearStdSimplex L g := contDiffNear_div_powerPartitionDenom hf M
      have hgl (i : ι) : ContDiffNearStdSimplex (shiftList i N).length g := by
        simpa [shiftList_length, L] using hg
      let F := fun b : ι → ℂ => ∑ i, (ascPochhammer ℂ M).eval (b i) *
        shiftedDirichletIntegral i (shiftList i N) (b + Pi.single i (M : ℂ)) g
      have hF : AnalyticOnNhd ℂ F (dirichletConvergenceRegion N) := by
        intro b hb
        apply Finset.analyticAt_fun_sum
        intro i _
        have hbi : b + Pi.single i (M : ℂ) ∈ shiftRegion i (shiftList i N) := by
          constructor
          · simp only [shiftList_length, Pi.add_apply, Pi.single_eq_same, add_re, natCast_re]
            have hi := hb i
            dsimp [M, L]
            push_cast
            linarith
          · intro j
            simp only [Pi.add_apply, Pi.single_eq_of_ne j.property, add_zero, shiftList_count]
            have hj := hb j
            linarith
        have hp : AnalyticAt ℂ (fun b : ι → ℂ => (ascPochhammer ℂ M).eval (b i)) b :=
          ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ M)) (b i) (mem_univ _)).comp_of_eq
            ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) rfl
        exact hp.mul (((analyticOnNhd_shiftedDirichletIntegral i (shiftList i N) (hgl i))
          _ hbi).comp_of_eq (analyticAt_id.add analyticAt_const) rfl)
      refine ⟨F, hF.analyticOn, ?_⟩
      have hFb : AnalyticOnNhd ℂ F mvBetaConvergent :=
        hF.mono (mvBetaConvergent_subset_dirichletConvergenceRegion N)
      have hnative := isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
        (regDirichletIntegral_analyticOn hf.continuousOn)
      let b₀ : ι → ℂ := fun _ => (L + 3 : ℕ)
      have hb₀ : b₀ ∈ mvBetaConvergent := by
        intro i
        simp [b₀]
        positivity
      apply hFb.eqOn_of_preconnected_of_eventuallyEq hnative
        (by simpa using isPreconnected_dirichletConvergenceRegion (ι := ι) 0) hb₀
      have hev : ∀ᶠ b : ι → ℂ in 𝓝 b₀, ∀ i, (L : ℝ) + 2 < (b i).re := by
        apply Filter.eventually_all.mpr
        intro i
        apply (isOpen_lt (continuous_const : Continuous fun _ : ι → ℂ => (L : ℝ) + 2)
          (Complex.continuous_re.comp (continuous_apply i))).eventually_mem
        dsimp [b₀]
        simp only [Nat.cast_add, Nat.cast_ofNat]
        linarith
      filter_upwards [hev] with b hb
      have hbpos : b ∈ mvBetaConvergent := by
        intro i
        have := hb i
        have := Nat.cast_nonneg (α := ℝ) L
        linarith
      change (∑ i, (ascPochhammer ℂ M).eval (b i) *
        shiftedDirichletIntegral i (shiftList i N) (b + Pi.single i (M : ℂ)) g) = _
      rw [regDirichletIntegral_power_partition hbpos hf.continuousOn M]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply shiftedDirichletIntegral_eq i (shiftList i N) (hgl i)
      intro k
      rw [shiftList_length]
      by_cases hki : k = i
      · subst k
        simp only [Pi.add_apply, Pi.single_eq_same, add_re, natCast_re]
        have := hb i
        have := Nat.cast_nonneg (α := ℝ) M
        change (L : ℝ) + 2 < (b i).re + M
        linarith
      · simpa only [Pi.add_apply, Pi.single_eq_of_ne hki, add_zero] using hb k

/-- If a simplex function has every finite order of differentiability on a neighborhood of
the simplex, its compatible finite-order regularized continuations glue to an entire function
of all Dirichlet parameters. -/
theorem exists_entire_regDirichletContinuation_of_contDiffNear
    {f : (ι → ℝ) → ℂ} (hf : ∀ N, ContDiffNearStdSimplex N f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOnNhd ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  choose Φ hΦ using fun N ↦
    exists_regDirichletContinuation_of_contDiffNear (N := N) (hf ((Fintype.card ι - 1) * N))
  have hexists (b : ι → ℂ) : ∃ N, b ∈ dirichletConvergenceRegion N := by
    choose n hn using fun i ↦ exists_nat_gt (-(b i).re)
    refine ⟨∑ i, n i, fun i ↦ ?_⟩
    have hni : (n i : ℝ) ≤ (∑ j, n j : ℕ) := by
      exact_mod_cast Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j))
        (Finset.mem_univ i)
    have hlt : -(n i : ℝ) < (b i).re := by linarith [hn i]
    linarith
  let order : (ι → ℂ) → ℕ := fun b ↦ Nat.find (hexists b)
  have horder (b : ι → ℂ) : b ∈ dirichletConvergenceRegion (order b) :=
    Nat.find_spec (hexists b)
  let F : (ι → ℂ) → ℂ := fun b ↦ Φ (order b) b
  refine ⟨F, ?_, ?_⟩
  · intro b _
    let N := order b
    have hbN : b ∈ dirichletConvergenceRegion N := horder b
    have hΦN : AnalyticAt ℂ (Φ N) b :=
      ((isOpen_dirichletConvergenceRegion N).analyticOn_iff_analyticOnNhd.mp
        (hΦ N).1) b hbN
    apply hΦN.congr
    filter_upwards [(isOpen_dirichletConvergenceRegion N).eventually_mem hbN] with x hxN
    let m := min N (order x)
    have hxm : x ∈ dirichletConvergenceRegion m := by
      change x ∈ dirichletConvergenceRegion (min N (order x))
      by_cases hle : N ≤ order x
      · rw [Nat.min_eq_left hle]
        exact hxN
      · rw [Nat.min_eq_right (Nat.le_of_not_ge hle)]
        exact horder x
    have hΦN_m : AnalyticOn ℂ (Φ N) (dirichletConvergenceRegion m) :=
      (hΦ N).1.mono (dirichletConvergenceRegion_mono (Nat.min_le_left _ _))
    have hΦx_m : AnalyticOn ℂ (Φ (order x)) (dirichletConvergenceRegion m) :=
      (hΦ (order x)).1.mono
        (dirichletConvergenceRegion_mono (Nat.min_le_right _ _))
    have heq : Set.EqOn (Φ N) (Φ (order x))
        (dirichletConvergenceRegion m) := by
      apply eqOn_dirichletContinuation hΦN_m hΦx_m
      intro c hc
      exact (hΦ N).2 hc |>.trans ((hΦ (order x)).2 hc).symm
    exact heq hxm
  · intro b hb
    exact (hΦ (order b)).2 hb

end DirichletTransform

end DirichletTransform
