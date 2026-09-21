/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Deriv
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.SimplexFTC

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Newton--Taylor formulas from Carlson's Dirichlet averages

This file develops Carlson's Section 5.5. The unweighted Dirichlet average is isolated first,
and divided differences are defined from averages of iterated derivatives. Canonical finite
index types are used for lists of interpolation nodes; permutation invariance can subsequently
remove any dependence on their chosen ordering.

Carlson's Lemma 5.5-1 follows from the fundamental theorem of calculus on the last
free-coordinate slices of a simplex. A second slicing and dilation formula proves the
repeated-integral identity. Both arguments allow coincident nodes.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.5,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonNewtonTaylor

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's unweighted Dirichlet average, obtained by setting every Dirichlet parameter
equal to one. -/
def carlsonUnweightedAverage (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  realCarlsonDirichletAverage (fun _ ↦ 1) z f

omit [Fintype ι] in
/-- The unweighted Dirichlet parameters belong to the positive real parameter domain. -/
theorem one_mem_mvRealBetaDomain : (fun _ : ι ↦ (1 : ℝ)) ∈ mvRealBetaDomain := by
  intro i
  simp

/-- Averaging at a constant vector of nodes is evaluation at that node. -/
theorem carlsonUnweightedAverage_const [Nonempty ι] (f : ℂ → ℂ) (w : ℂ) :
    carlsonUnweightedAverage (fun _ : ι ↦ w) f = f w := by
  let b : ι → ℝ := fun _ ↦ 1
  let _ : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure one_mem_mvRealBetaDomain
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  change (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) = f w
  have hrestrict := dirichletMeasure_restrict b
  have hmem : ∀ᵐ u ∂dirichletMeasure b, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
    rw [← hrestrict]
    exact self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  calc
    (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) =
        ∫ _, f w ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [hmem] with u hu
      rw [carlsonAffineForm_const hu]
    _ = f w := by simp

/-- Permuting the nodes does not change the unweighted Carlson average. -/
theorem carlsonUnweightedAverage_perm (z : ι → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm ι) :
    carlsonUnweightedAverage (z ∘ σ) f = carlsonUnweightedAverage z f := by
  let b : ι → ℝ := fun _ ↦ 1
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun u := u ∘ σ.symm
    invFun u := u ∘ σ
    left_inv u := by funext i; simp
    right_inv u := by funext i; simp
    measurable_toFun := continuous_pi (fun i ↦ continuous_apply (σ.symm i)) |>.measurable
    measurable_invFun := continuous_pi (fun i ↦ continuous_apply (σ i)) |>.measurable
  }
  have hg : MeasurePreserving g (dirichletMeasure b) (dirichletMeasure b) := by
    convert measurePreserving_dirichletMeasure_perm b σ.symm using 1
    simp [b, Function.comp_def]
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  rw [← hg.integral_comp' (fun u ↦ f (carlsonAffineForm z u))]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  simpa [g, Function.comp_def] using
    (carlsonAffineForm_perm (z ∘ σ) σ.symm u).symm

/-- The node vector obtained by placing `x` before a vector of `n` nodes. -/
def prependNewtonNode (x : ℂ) (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons x z

/-- The node vector obtained by placing `x` and `y` before a vector of `n` nodes. -/
def prependTwoNewtonNodes (x y : ℂ) (z : Fin n → ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons x (Fin.cons y z)

/-- A divided difference of order `n`, expressed as Carlson's unweighted average of the
`n`th derivative divided by `n!`; this is formula (5.5-6). -/
def carlsonDividedDifference (n : ℕ) (f : ℂ → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  carlsonUnweightedAverage z (iteratedDeriv n f) / (n.factorial : ℂ)

/-- Unweighted probability normalization in finite coordinates. -/
theorem carlsonUnweightedAverage_eq_factorial_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    carlsonUnweightedAverage z f = (n.factorial : ℂ) *
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)), f (carlsonAffineForm z u)
        ∂Measure.stdSimplexMeasure := by
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  change (∫ u, f (carlsonAffineForm z u) ∂dirichletMeasureUniform 1) = _
  rw [dirichletMeasureUniform_one, integral_smul_measure]
  simp [Complex.real_smul]

/-- The factorial in the divided difference cancels the probability normalization. -/
theorem carlsonDividedDifference_eq_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    carlsonDividedDifference n f z =
      ∫ v in posSimplexFin n 1, iteratedDeriv n f (carlsonAffineForm z (finSimplexPoint v)) := by
  rw [carlsonDividedDifference, carlsonUnweightedAverage_eq_factorial_integral]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast n.factorial_ne_zero)]
  exact integral_stdSimplex_fin _

private lemma carlsonAffineForm_finSimplexPoint_snoc (z : Fin n → ℂ) (x : ℂ) (v : Fin n → ℝ) :
    carlsonAffineForm (Fin.snoc z x) (finSimplexPoint v) =
      (∑ k, (v k : ℂ) * z k) + ((1 - ∑ k, v k : ℝ) : ℂ) * x := by
  simp [carlsonAffineForm, finSimplexPoint, Fin.sum_univ_castSucc]

private lemma carlsonAffineForm_finSimplexPoint_snoc_snoc
    (z : Fin n → ℂ) (x y : ℂ) (v : Fin n → ℝ) (t : ℝ) :
    carlsonAffineForm (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint (Fin.snoc v t)) =
      carlsonAffineForm (Fin.snoc z y) (finSimplexPoint v) + (t : ℂ) * (x - y) := by
  simp [carlsonAffineForm_finSimplexPoint_snoc, Fin.sum_univ_castSucc]
  ring

private lemma continuousOn_carlson_finSimplex
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {z : Fin (n + 1) → ℂ} (hz : Set.range z ⊆ Ω) :
    ContinuousOn (fun v => f (carlsonAffineForm z (finSimplexPoint v))) (posSimplexFin n 1) :=
  hf.comp ((continuous_carlsonAffineForm z).comp continuous_finSimplexPoint).continuousOn
    (fun _ hv => convexHull_min hz hΩconv
      (carlsonAffineForm_mem_convexHull z (finSimplexPoint_mem hv)))

private lemma range_snoc_subset {Ω : Set ℂ} {z : Fin n → ℂ}
    (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) : Set.range (Fin.snoc z x) ⊆ Ω := by
  rintro _ ⟨k, rfl⟩
  refine Fin.lastCases ?_ (fun l => ?_) k
  · simpa using hx
  · simpa using hz ⟨l, rfl⟩

/-- The simplex fundamental theorem of calculus for a holomorphic kernel. -/
theorem carlson_simplex_integral_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    (∫ v in posSimplexFin n 1, f (carlsonAffineForm (Fin.snoc z x) (finSimplexPoint v))) -
      (∫ v in posSimplexFin n 1, f (carlsonAffineForm (Fin.snoc z y) (finSimplexPoint v))) =
      (x - y) * ∫ v in posSimplexFin (n + 1) 1,
        deriv f (carlsonAffineForm (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)) := by
  have hzx := range_snoc_subset hz hx
  have hzy := range_snoc_subset hz hy
  have hzxy := range_snoc_subset hzx hy
  have hcx := continuousOn_carlson_finSimplex hΩconv hf.continuousOn hzx
  have hcy := continuousOn_carlson_finSimplex hΩconv hf.continuousOn hzy
  have hcd := continuousOn_carlson_finSimplex hΩconv hf.deriv.continuousOn hzxy
  have hix := hcx.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one n)
  have hiy := hcy.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one n)
  have hid : IntegrableOn (fun v => (x - y) *
      deriv f (carlsonAffineForm (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)))
      (posSimplexFin (n + 1) 1) :=
    (continuousOn_const (c := x - y) |>.mul hcd).integrableOn_compact
      (isCompact_posSimplexFin_one (n + 1))
  rw [← integral_sub hix hiy, ← integral_const_mul,
    integral_posSimplexFin_snoc _ hid]
  apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
  intro v hv
  dsimp only
  let r : ℝ := 1 - ∑ k, v k
  have hr : 0 ≤ r := sub_nonneg.mpr hv.2
  let A : ℂ := carlsonAffineForm (Fin.snoc z y) (finSimplexPoint v)
  have hmem {t : ℝ} (ht : t ∈ Set.Icc 0 r) : A + (t : ℂ) * (x - y) ∈ Ω := by
    rw [← carlsonAffineForm_finSimplexPoint_snoc_snoc]
    apply convexHull_min hzxy hΩconv
    apply carlsonAffineForm_mem_convexHull _ (finSimplexPoint_mem ?_)
    constructor
    · intro k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv.1, ht.1]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      dsimp [r] at ht
      linarith [ht.2]
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 r) :
      HasDerivAt (fun t : ℝ => f (A + (t : ℂ) * (x - y)))
        ((x - y) * deriv f (A + (t : ℂ) * (x - y))) t := by
    have hline : HasDerivAt (fun t : ℝ => A + (t : ℂ) * (x - y)) (x - y) t := by
      simpa using! ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (x - y)).const_add A
    simpa [mul_comm] using! ((hf _ (hmem ht)).differentiableAt.hasDerivAt.comp t hline)
  have hint : IntervalIntegrable (fun t : ℝ => (x - y) * deriv f (A + (t : ℂ) * (x - y)))
      volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hr]
    exact continuousOn_const.mul (hf.deriv.continuousOn.comp (by fun_prop) (fun t ht => hmem ht))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa [Set.uIcc_of_le hr] using ht)) hint
  rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc] at H
  simp only [carlsonAffineForm_finSimplexPoint_snoc_snoc]
  change f (carlsonAffineForm (Fin.snoc z x) (finSimplexPoint v)) - f A = _
  rw [H]
  simp only [ofReal_zero, zero_mul, add_zero]
  congr 2
  simp only [A, r, carlsonAffineForm_finSimplexPoint_snoc]
  ring

/-- Divided differences are invariant under permutations of their nodes. -/
theorem carlsonDividedDifference_perm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    carlsonDividedDifference n f (z ∘ σ) = carlsonDividedDifference n f z := by
  rw [carlsonDividedDifference, carlsonDividedDifference,
    carlsonUnweightedAverage_perm]

/-- Exchanging the final two nodes does not change a divided difference. -/
theorem carlsonDividedDifference_snoc_snoc_comm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin n → ℂ) (x y : ℂ) :
    carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) =
      carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z y) x) := by
  let i : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let j : Fin (n + 2) := Fin.last (n + 1)
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i j
  rw [← carlsonDividedDifference_perm (n + 1) f
    (Fin.snoc (Fin.snoc z x) y) σ]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [σ, i, j]
  · by_cases hkj : k = j
    · subst k
      simp [σ, i, j]
    · have hklt : k.val < n := by
        simp only [i, j, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at hki hkj
        omega
      have hkle : k.val ≤ n := Nat.le_of_lt hklt
      simp [Function.comp_apply, σ, Equiv.swap_apply_of_ne_of_ne hki hkj,
        Fin.snoc, hklt, hkle]

/-- A divided difference of order zero is evaluation at its unique node. -/
@[simp] theorem carlsonDividedDifference_zero (f : ℂ → ℂ) (z : Fin 1 → ℂ) :
    carlsonDividedDifference 0 f z = f (z 0) := by
  have hz : z = fun _ ↦ z 0 := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  rw [hz]
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- If all nodes coincide, Carlson's divided difference is the corresponding Taylor
coefficient. -/
theorem carlsonDividedDifference_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    carlsonDividedDifference n f (fun _ ↦ w) =
      iteratedDeriv n f w / (n.factorial : ℂ) := by
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- The Newton basis polynomial associated to a finite vector of preceding nodes. -/
def newtonBasis (z : Fin n → ℂ) (x : ℂ) : ℂ :=
  ∏ i, (x - z i)

/-- The empty Newton basis is one. -/
@[simp] theorem newtonBasis_zero (z : Fin 0 → ℂ) (x : ℂ) :
    newtonBasis z x = 1 := by
  simp [newtonBasis]

/-- Prepending a node adds the corresponding linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_prepend (z : Fin n → ℂ) (a x : ℂ) :
    newtonBasis (prependNewtonNode a z) x = (x - a) * newtonBasis z x := by
  simp [newtonBasis, prependNewtonNode, Fin.prod_univ_succ]

/-- Appending a node adds its linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_snoc (z : Fin n → ℂ) (a x : ℂ) :
    newtonBasis (Fin.snoc z a) x = newtonBasis z x * (x - a) := by
  simp [newtonBasis, Fin.prod_univ_castSucc]

/-- The nodes preceding the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrecedingNodes {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin n → ℂ :=
  fun i => z ⟨i, lt_trans i.isLt n.isLt⟩

/-- The nodes through the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrefix {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin (n + 1) → ℂ :=
  fun i => z ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_iff.mpr n.isLt)⟩

@[simp] theorem newtonPrecedingNodes_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrecedingNodes z n.castSucc =
      newtonPrecedingNodes (Fin.init z) n := by
  rfl

@[simp] theorem newtonPrefix_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrefix z n.castSucc = newtonPrefix (Fin.init z) n := by
  rfl

@[simp] theorem newtonPrecedingNodes_last (z : Fin (p + 1) → ℂ) :
    newtonPrecedingNodes z (Fin.last p) = Fin.init z := by
  rfl

@[simp] theorem newtonPrefix_last (z : Fin (p + 1) → ℂ) :
    newtonPrefix z (Fin.last p) = z := by
  funext i
  rfl

/-- **Carlson 5.5-1.** Divided differences defined by unweighted Dirichlet averages satisfy
the usual first-order recurrence, including at coincident nodes. -/
theorem carlsonDividedDifference_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    carlsonDividedDifference n f (Fin.snoc z x) -
        carlsonDividedDifference n f (Fin.snoc z y) =
      (x - y) * carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) := by
  have hfiter : AnalyticOnNhd ℂ (iteratedDeriv n f) Ω := by
    simpa [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
  simp only [carlsonDividedDifference_eq_integral, iteratedDeriv_succ]
  exact carlson_simplex_integral_sub hΩconv hfiter z hz hx hy

/-- **Carlson 5.5-2.** The finite Newton expansion with its Dirichlet-average remainder. -/
theorem newtonTaylor_sum_add_remainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin p → ℂ) (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) :
    f x =
      (∑ n : Fin p, carlsonDividedDifference n f (newtonPrefix z n) *
        newtonBasis (newtonPrecedingNodes z n) x) +
      carlsonDividedDifference p f (Fin.snoc z x) * newtonBasis z x := by
  induction p with
  | zero =>
      simp [newtonBasis, carlsonDividedDifference_zero, Fin.snoc]
  | succ p ih =>
      let z₀ : Fin p → ℂ := Fin.init z
      let a : ℂ := z (Fin.last p)
      have hza : z = Fin.snoc z₀ a := by
        simp [z₀, a]
      have hz₀ : Set.range z₀ ⊆ Ω := by
        rintro w ⟨i, rfl⟩
        exact hz ⟨Fin.castSucc i, rfl⟩
      have ha : a ∈ Ω := hz ⟨Fin.last p, rfl⟩
      have hih := ih z₀ hz₀
      rw [hza]
      rw [hih]
      rw [Fin.sum_univ_castSucc]
      simp only [newtonPrefix_init_castSucc, newtonPrecedingNodes_init_castSucc,
        newtonPrefix_last, newtonPrecedingNodes_last, Fin.init_snoc,
        Fin.val_castSucc, Fin.val_last]
      rw [newtonBasis_snoc]
      have hrec := carlsonDividedDifference_sub hΩconv hf z₀ hz₀ hx ha
      rw [carlsonDividedDifference_snoc_snoc_comm] at hrec
      linear_combination newtonBasis z₀ x * hrec

/-- Taylor's formula with Carlson's unweighted-average remainder, obtained from the
Newton--Taylor formula by coalescing all interpolation nodes. -/
theorem taylor_sum_add_carlsonRemainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (p : ℕ) :
    f x =
      (∑ n : Fin p, iteratedDeriv n.val f a / (n.val.factorial : ℂ) * (x - a) ^ n.val) +
      carlsonDividedDifference p f (Fin.snoc (fun _ : Fin p => a) x) * (x - a) ^ p := by
  have hz : Set.range (fun _ : Fin p => a) ⊆ Ω := by
    rintro y ⟨i, rfl⟩
    exact ha
  have h := newtonTaylor_sum_add_remainder hΩconv hf
    (fun _ : Fin p => a) hz hx
  have hprefix (n : Fin p) : newtonPrefix (fun _ : Fin p => a) n = fun _ => a := by
    funext i
    rfl
  simp_rw [hprefix, carlsonDividedDifference_const] at h
  simpa [newtonPrecedingNodes, newtonBasis] using h

/-! ## Repeated integrals -/

/-- Integration of a complex-valued function along the oriented segment from `a` to `x`. -/
def carlsonSegmentIntegral (a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  (x - a) * ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (x - a))

/-- Carlson's repeated integration operator based at `a`, defined recursively by segment
integration. This is the operator in equations 5.5(9) and 5.5(12). -/
def carlsonRepeatedIntegral : ℕ → ℂ → (ℂ → ℂ) → ℂ → ℂ
  | 0, _, f, x => f x
  | n + 1, a, f, x => carlsonSegmentIntegral a x (carlsonRepeatedIntegral n a f)

/-- The zeroth repeated integral is the original function. -/
@[simp] theorem carlsonRepeatedIntegral_zero (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    carlsonRepeatedIntegral 0 a f x = f x := rfl

/-- The successor step for Carlson's repeated integration operator. -/
@[simp] theorem carlsonRepeatedIntegral_succ (n : ℕ) (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    carlsonRepeatedIntegral (n + 1) a f x =
      carlsonSegmentIntegral a x (carlsonRepeatedIntegral n a f) := rfl

/-- The unnormalized simplex integral with all base nodes coalesced at `a`. -/
private def coalescedSimplexIntegral (n : ℕ) (a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ v in posSimplexFin n 1, f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * (x - a))

private lemma carlsonAffineForm_coalesced (n : ℕ) (a x : ℂ) (v : Fin n → ℝ) :
    carlsonAffineForm (Fin.snoc (fun _ : Fin n => a) x) (finSimplexPoint v) =
      a + ((1 - ∑ k, v k : ℝ) : ℂ) * (x - a) := by
  rw [carlsonAffineForm_finSimplexPoint_snoc]
  simp only [← Finset.sum_mul, ofReal_sub, ofReal_one, ofReal_sum]
  ring

private lemma carlsonUnweightedAverage_coalesced (n : ℕ) (a x : ℂ) (f : ℂ → ℂ) :
    carlsonUnweightedAverage (Fin.snoc (fun _ : Fin n => a) x) f =
      (n.factorial : ℂ) * coalescedSimplexIntegral n a x f := by
  rw [carlsonUnweightedAverage_eq_factorial_integral, integral_stdSimplex_fin]
  simp only [carlsonAffineForm_coalesced, coalescedSimplexIntegral]

private lemma coalescedSimplexIntegral_succ
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    coalescedSimplexIntegral (n + 1) a x f =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ n * coalescedSimplexIntegral n a (a + (t : ℂ) * (x - a)) f := by
  have hz : Set.range (Fin.snoc (fun _ : Fin (n + 1) => a) x) ⊆ Ω :=
    range_snoc_subset (by rintro _ ⟨k, rfl⟩; exact ha) hx
  have hc := continuousOn_carlson_finSimplex hΩconv hf hz
  simp only [carlsonAffineForm_coalesced] at hc
  have hi := hc.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one (n + 1))
  unfold coalescedSimplexIntegral at ⊢
  rw [integral_posSimplexFin_snoc_outer _ hi]
  have hs : (∫ t in Set.Icc (0 : ℝ) 1,
      ∫ v in posSimplexFin n (1 - t),
        f (a + ((1 - ∑ k, Fin.snoc v t k : ℝ) : ℂ) * (x - a))) =
      ∫ t in Set.Icc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) ^ n *
        ∫ v in posSimplexFin n 1,
          f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * ((a + ((1 - t : ℝ) : ℂ) * (x - a)) - a)) := by
    rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
    apply setIntegral_congr_fun measurableSet_Ico
    intro t ht
    dsimp only
    rw [integral_posSimplexFin_scale _ (sub_pos.mpr ht.2)]
    simp only [Complex.real_smul, ofReal_pow]
    congr 1
    apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
    intro v _
    dsimp only
    congr 1
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum, ofReal_sub, ofReal_one, ofReal_add, ofReal_mul]
    ring
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤
    1)]
  have H := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (t : ℂ) ^ n * ∫ v in posSimplexFin n 1,
      f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * ((a + (t : ℂ) * (x - a)) - a))) 1
    (a := (0 : ℝ)) (b := 1)
  simpa using H

private lemma carlsonRepeatedIntegral_eq_coalesced
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    carlsonRepeatedIntegral n a f x = (x - a) ^ n * coalescedSimplexIntegral n a x f := by
  induction n generalizing x with
  | zero =>
      simp only [carlsonRepeatedIntegral_zero, pow_zero, one_mul, coalescedSimplexIntegral]
      rw [Measure.volume_pi_eq_dirac]
      simp [posSimplexFin]
  | succ n ih =>
      rw [carlsonRepeatedIntegral_succ, carlsonSegmentIntegral, coalescedSimplexIntegral_succ
        hΩconv hf ha hx]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have hy : a + (t : ℂ) * (x - a) ∈ Ω := by
        have H := hΩconv ha hx (sub_nonneg.mpr ht'.2) ht'.1 (by ring : 1 - t + t = 1)
        convert H using 1
        simp only [Complex.real_smul, ofReal_sub, ofReal_one]
        ring
      rw [ih hy]
      simp only [add_sub_cancel_left, mul_pow, pow_succ]
      ring

/-- Carlson's equation 5.5(10): an `n`-fold repeated integral is an unweighted Dirichlet
average with `n` nodes coalesced at the base point and one node at the endpoint. -/
theorem carlsonRepeatedIntegral_eq_unweightedAverage
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    carlsonRepeatedIntegral n a f x =
      (x - a) ^ n / (n.factorial : ℂ) *
        carlsonUnweightedAverage (Fin.snoc (fun _ : Fin n => a) x) f := by
  rw [carlsonRepeatedIntegral_eq_coalesced hΩconv hf.continuousOn ha hx,
    carlsonUnweightedAverage_coalesced]
  field_simp [Nat.factorial_ne_zero]

end DirichletTransform

end CarlsonNewtonTaylor
