/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalScale
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A constructed compactly supported Taylor–Borel extension

The input is an arbitrary sequence in a real Banach space. We choose increasing
integer cutoff scales and sum actual cutoff monomials. All derivative bounds,
convergence, smoothness, support, and prescribed derivatives at zero are proved.
-/

@[expose] public section


noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.BorelExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

/-- Monomial, given by `(s ^ j / (j.factorial : ℝ)) • v`. -/
def monomial (j : ℕ) (v : E) (s : ℝ) : E := (s ^ j / (j.factorial : ℝ)) • v

theorem monomial_contDiff (j : ℕ) (v : E) : ContDiff ℝ ∞ (monomial j v) := by
  exact ((contDiff_id.pow j).div_const _).smul contDiff_const

theorem deriv_monomial_succ (j : ℕ) (v : E) :
    deriv (monomial (j + 1) v) = monomial j v := by
  funext s
  have h := (((hasDerivAt_pow (j + 1) s).div_const
    ((j + 1).factorial : ℝ)).smul_const v).deriv
  change deriv (fun x : ℝ => (x ^ (j + 1) / ((j + 1).factorial : ℝ)) • v) s = _
  rw [h]
  unfold monomial
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [Nat.add_sub_cancel]
  field_simp

private theorem iteratedDeriv_zero_curve (n : ℕ) :
    iteratedDeriv n (fun _ : ℝ => (0 : E)) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      simp

theorem iteratedDeriv_monomial_zero (n j : ℕ) (v : E) :
    iteratedDeriv n (monomial j v) 0 = if n = j then v else 0 := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp [monomial]
      | succ j => simp [monomial]
  | succ n ih =>
      cases j with
      | zero =>
          rw [iteratedDeriv_succ']
          have h : deriv (monomial 0 v) = fun _ => 0 := by
            have hm : monomial 0 v = fun _ : ℝ => v := by
              funext x
              simp [monomial]
            rw [hm]
            ext x
            exact deriv_const x v
          rw [h, iteratedDeriv_zero_curve]
          simp
      | succ j =>
          rw [iteratedDeriv_succ', deriv_monomial_succ, ih]
          simp

/-- The actual summand, with no smooth extension supplied as an input. -/
def term (b : ℝ) (j : ℕ) (v : E) (s : ℝ) : E :=
  SmoothCutoffs.cutoff (b * s) • monomial j v s

/-- Template, given by `SmoothCutoffs.cutoff s • monomial j v s`. -/
def template (j : ℕ) (v : E) (s : ℝ) : E :=
  SmoothCutoffs.cutoff s • monomial j v s

theorem term_contDiff (b : ℝ) (j : ℕ) (v : E) : ContDiff ℝ ∞ (term b j v) :=
  (SmoothCutoffs.scaledCutoff_contDiff b).smul (monomial_contDiff j v)

theorem template_contDiff (j : ℕ) (v : E) : ContDiff ℝ ∞ (template j v) :=
  SmoothCutoffs.cutoff_contDiff.smul (monomial_contDiff j v)

theorem template_hasCompactSupport (j : ℕ) (v : E) :
    HasCompactSupport (template j v) :=
  SmoothCutoffs.cutoff_hasCompactSupport.smul_right

theorem template_iteratedDeriv_hasCompactSupport (j k : ℕ) (v : E) :
    HasCompactSupport (iteratedDeriv k (template j v)) := by
  induction k with
  | zero => simpa using template_hasCompactSupport j v
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem exists_template_bound (j k : ℕ) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖iteratedDeriv k (template j v) s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (template_iteratedDeriv_hasCompactSupport j k v).exists_bound_of_continuous
    ((template_contDiff j v).continuous_iteratedDeriv k (nat_le_infty k))
  exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩

/-- Template bound, given by `Classical.choose (exists_template_bound j k v)`. -/
def templateBound (j k : ℕ) (v : E) : ℝ :=
  Classical.choose (exists_template_bound j k v)

theorem templateBound_nonneg (j k : ℕ) (v : E) : 0 ≤ templateBound j k v :=
  (Classical.choose_spec (exists_template_bound j k v)).1

theorem norm_template_iteratedDeriv_le (j k : ℕ) (v : E) (s : ℝ) :
    ‖iteratedDeriv k (template j v) s‖ ≤ templateBound j k v :=
  (Classical.choose_spec (exists_template_bound j k v)).2 s

theorem term_eq_scaled_template {b : ℝ} (hb : b ≠ 0) (j : ℕ) (v : E) :
    term b j v = fun s => (b ^ j)⁻¹ • template j v (b * s) := by
  funext s
  simp only [term, template, monomial, smul_smul, mul_pow]
  congr 1
  field_simp

theorem iteratedDeriv_term {b : ℝ} (hb : b ≠ 0) (j k : ℕ) (v : E) (s : ℝ) :
    iteratedDeriv k (term b j v) s =
      (b ^ k / b ^ j) • iteratedDeriv k (template j v) (b * s) := by
  rw [term_eq_scaled_template hb]
  have ht : ContDiff ℝ (k : WithTop ℕ∞) (template j v) :=
    (template_contDiff j v).of_le (nat_le_infty k)
  have hc : ContDiff ℝ (k : WithTop ℕ∞) (fun x : ℝ => template j v (b * x)) :=
    ht.comp (contDiff_const.mul contDiff_id)
  change iteratedDeriv k ((b ^ j)⁻¹ • (fun x : ℝ => template j v (b * x))) s = _
  rw [iteratedDeriv_const_smul hc.contDiffAt, iteratedDeriv_comp_const_smul ht]
  simp only [smul_smul]
  congr 1
  ring

theorem iteratedDeriv_term_zero (b : ℝ) (j k : ℕ) (v : E) :
    iteratedDeriv k (term b j v) 0 = if k = j then v else 0 := by
  have heq : term b j v =ᶠ[𝓝 0] monomial j v := by
    filter_upwards [SmoothCutoffs.scaledCutoff_eventually_one_at_zero b] with s hs
    change SmoothCutoffs.cutoff (b * s) = 1 at hs
    simp only [term, hs, one_smul]
  rw [heq.iteratedDeriv_eq, iteratedDeriv_monomial_zero]

theorem norm_iteratedDeriv_term_le {b : ℝ} (hb : 0 < b)
    (j k : ℕ) (v : E) (s : ℝ) :
    ‖iteratedDeriv k (term b j v) s‖ ≤
      (b ^ k / b ^ j) * templateBound j k v := by
  rw [iteratedDeriv_term (ne_of_gt hb), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ b ^ k / b ^ j)]
  exact mul_le_mul_of_nonneg_left (norm_template_iteratedDeriv_le j k v (b * s))
    (by positivity)

private theorem power_ratio_le {b : ℝ} (hb : 1 ≤ b) {k j : ℕ} (hkj : k < j) :
    b ^ k / b ^ j ≤ 1 / b := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  apply (le_div_iff₀ hbpos).2
  calc
    (b ^ k / b ^ j) * b = b ^ (k + 1) / b ^ j := by rw [pow_succ]; ring
    _ ≤ 1 := (div_le_one (pow_pos hbpos j)).2
      (pow_le_pow_right₀ hb (Nat.succ_le_of_lt hkj))

/-- A finite collection of bounds controls every derivative below the degree. -/
def boundSum (j : ℕ) (v : E) : ℝ :=
  ∑ k ∈ Finset.range j, templateBound j k v

theorem boundSum_nonneg (j : ℕ) (v : E) : 0 ≤ boundSum j v :=
  Finset.sum_nonneg fun k _ => templateBound_nonneg j k v

theorem templateBound_le_boundSum {j k : ℕ} (hkj : k < j) (v : E) :
    templateBound j k v ≤ boundSum j v := by
  exact Finset.single_le_sum (fun i _ => templateBound_nonneg j i v)
    (Finset.mem_range.mpr hkj)

/-- Local scale, given by `Classical.choose (exists_nat_gt ((2 : ℝ) ^ j * boundSum j (a j)))`. -/
def localScale (a : ℕ → E) (j : ℕ) : ℕ :=
  Classical.choose (exists_nat_gt ((2 : ℝ) ^ j * boundSum j (a j)))

theorem localScale_bound (a : ℕ → E) (j : ℕ) :
    (2 : ℝ) ^ j * boundSum j (a j) < localScale a j :=
  Classical.choose_spec (exists_nat_gt ((2 : ℝ) ^ j * boundSum j (a j)))

/-- Increasing positive integer scales; they are selected from proved finite bounds. -/
def scale (a : ℕ → E) : ℕ → ℕ := DiagonalScale.doublingEnvelope (localScale a)

theorem scale_pos (a : ℕ → E) (j : ℕ) : 0 < scale a j :=
  DiagonalScale.doublingEnvelope_pos (localScale a) j

theorem scale_strictMono (a : ℕ → E) : StrictMono (scale a) :=
  DiagonalScale.doublingEnvelope_strictMono (localScale a)

theorem scale_doubling (a : ℕ → E) (j : ℕ) : 2 * scale a j ≤ scale a (j + 1) :=
  DiagonalScale.doublingEnvelope_growth (localScale a) j

theorem scale_ge_one (a : ℕ → E) (j : ℕ) : (1 : ℝ) ≤ scale a j := by
  exact_mod_cast scale_pos a j

theorem boundSum_le_scale (a : ℕ → E) (j : ℕ) :
    boundSum j (a j) ≤ (1 / 2 : ℝ) ^ j * scale a j := by
  have hscale : (2 : ℝ) ^ j * boundSum j (a j) ≤ scale a j := by
    exact (localScale_bound a j).le.trans
      (by exact_mod_cast DiagonalScale.doublingEnvelope_ge (localScale a) j)
  calc
    boundSum j (a j) = (1 / 2 : ℝ) ^ j * ((2 : ℝ) ^ j * boundSum j (a j)) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 2 : ℝ) ^ j * scale a j :=
      mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The all-order diagonal estimate: for each fixed derivative order the tail
is bounded uniformly on the whole real line by a geometric series. -/
theorem term_derivative_tail_bound (a : ℕ → E) {j k : ℕ} (hkj : k < j) (s : ℝ) :
    ‖iteratedDeriv k (term (scale a j) j (a j)) s‖ ≤ (1 / 2 : ℝ) ^ j := by
  have hb : (1 : ℝ) ≤ scale a j := scale_ge_one a j
  have hbpos : (0 : ℝ) < scale a j := lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ (((scale a j : ℝ) ^ k) / (scale a j : ℝ) ^ j) * templateBound j k (a j) :=
      norm_iteratedDeriv_term_le hbpos j k (a j) s
    _ ≤ (1 / (scale a j : ℝ)) * boundSum j (a j) :=
      mul_le_mul (power_ratio_le hb hkj) (templateBound_le_boundSum hkj (a j))
        (templateBound_nonneg j k (a j)) (by positivity)
    _ ≤ (1 / (scale a j : ℝ)) * ((1 / 2 : ℝ) ^ j * scale a j) :=
      mul_le_mul_of_nonneg_left (boundSum_le_scale a j) (by positivity)
    _ = (1 / 2 : ℝ) ^ j := by field_simp

/-- The finitely many early terms retain their actual derivative bounds. -/
def majorant (a : ℕ → E) (k j : ℕ) : ℝ :=
  if k < j then (1 / 2 : ℝ) ^ j
  else (((scale a j : ℝ) ^ k) / (scale a j : ℝ) ^ j) * templateBound j k (a j)

theorem majorant_summable (a : ℕ → E) (k : ℕ) : Summable (majorant a k) := by
  apply summable_geometric_two.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop k] with j hj
  simp only [majorant, ite_eq_left hj]

theorem norm_iteratedDeriv_term_le_majorant (a : ℕ → E) (k j : ℕ) (s : ℝ) :
    ‖iteratedDeriv k (term (scale a j) j (a j)) s‖ ≤ majorant a k j := by
  unfold majorant
  split_ifs with hkj
  · exact term_derivative_tail_bound a hkj s
  · exact norm_iteratedDeriv_term_le
      (by exact_mod_cast scale_pos a j) j k (a j) s

section Complete

variable [CompleteSpace E]

/-- An actual series of compactly supported cutoff monomials. -/
def extension (a : ℕ → E) (s : ℝ) : E :=
  ∑' j : ℕ, term (scale a j) j (a j) s

omit [CompleteSpace E] in
theorem extension_eq_series (a : ℕ → E) (s : ℝ) :
    extension a s = ∑' j : ℕ,
      (SmoothCutoffs.cutoff ((scale a j : ℝ) * s) * (s ^ j / (j.factorial : ℝ))) • a j := by
  simp only [extension, term, monomial, smul_smul]

theorem summable_iteratedDeriv_terms (a : ℕ → E) (k : ℕ) (s : ℝ) :
    Summable (fun j : ℕ => iteratedDeriv k (term (scale a j) j (a j)) s) :=
  .of_norm_bounded (majorant_summable a k)
    (fun j => norm_iteratedDeriv_term_le_majorant a k j s)

theorem extension_contDiff (a : ℕ → E) : ContDiff ℝ ∞ (extension a) := by
  apply contDiff_tsum (N := ⊤) (v := majorant a)
    (fun j => term_contDiff (scale a j) j (a j))
    (fun k _ => majorant_summable a k)
  intro k j s _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_term_le_majorant a k j s

theorem iteratedDeriv_extension (a : ℕ → E) (k : ℕ) (s : ℝ) :
    iteratedDeriv k (extension a) s =
      ∑' j : ℕ, iteratedDeriv k (term (scale a j) j (a j)) s := by
  have hF := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := ⊤) (v := majorant a)
    (fun j => term_contDiff (scale a j) j (a j))
    (fun n _ => majorant_summable a n)
    (fun n j x _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact norm_iteratedDeriv_term_le_majorant a n j x)
    (k := k) le_top s
  simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
  change (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm
      (iteratedFDeriv ℝ k (fun x => ∑' j : ℕ, term (scale a j) j (a j) x) s) = _
  rw [hF]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm.toContinuousLinearEquiv.map_tsum

/-- Every prescribed jet is attained, including the zeroth jet. -/
theorem extension_jets (a : ℕ → E) (k : ℕ) :
    iteratedDeriv k (extension a) 0 = a k := by
  rw [iteratedDeriv_extension]
  simp only [iteratedDeriv_term_zero]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    simp [Ne.symm hj]

omit [CompleteSpace E] in
theorem extension_zero_of_one_le_abs (a : ℕ → E) {s : ℝ} (hs : 1 ≤ |s|) :
    extension a s = 0 := by
  calc
    extension a s = ∑' _ : ℕ, (0 : E) := by
      apply tsum_congr
      intro j
      have hb := scale_ge_one a j
      have harg : 1 ≤ |(scale a j : ℝ) * s| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact one_le_mul_of_one_le_of_one_le hb hs
      simp only [term, SmoothCutoffs.cutoff_zero_of_one_le_abs harg, zero_smul]
    _ = 0 := tsum_zero

omit [CompleteSpace E] in
theorem extension_support (a : ℕ → E) : support (extension a) ⊆ Ioo (-1 : ℝ) 1 := by
  intro s hs
  have habs : |s| < 1 := lt_of_not_ge fun h => hs (extension_zero_of_one_le_abs a h)
  exact abs_lt.mp habs

omit [CompleteSpace E] in
theorem extension_tsupport (a : ℕ → E) : tsupport (extension a) ⊆ Icc (-1 : ℝ) 1 :=
  closure_minimal ((extension_support a).trans Ioo_subset_Icc_self) isClosed_Icc

omit [CompleteSpace E] in
theorem extension_hasCompactSupport (a : ℕ → E) : HasCompactSupport (extension a) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (extension_tsupport a)

/-- The right endpoint jets used by the one-sided gluing theorem are the same
prescribed jets as the ordinary derivatives. -/
theorem extension_right_jets (a : ℕ → E) (k : ℕ) :
    iteratedDerivWithin k (extension a) (Ici 0) 0 = a k := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0)
      ((extension_contDiff a).of_le (nat_le_infty k)).contDiffAt (mem_Ici.mpr le_rfl)]
  exact extension_jets a k

/-- Translate the constructed extension to any joining time. -/
def rightExtension (T : ℝ) (a : ℕ → E) (t : ℝ) : E := extension a (t - T)

theorem rightExtension_contDiff (T : ℝ) (a : ℕ → E) :
    ContDiff ℝ ∞ (rightExtension T a) :=
  (extension_contDiff a).comp (contDiff_id.sub contDiff_const)

theorem rightExtension_jets (T : ℝ) (a : ℕ → E) (k : ℕ) :
    iteratedDeriv k (rightExtension T a) T = a k := by
  unfold rightExtension
  simp only [sub_eq_add_neg, iteratedDeriv_comp_add_const, add_neg_cancel]
  exact extension_jets a k

theorem rightExtension_right_jets (T : ℝ) (a : ℕ → E) (k : ℕ) :
    iteratedDerivWithin k (rightExtension T a) (Ici T) T = a k := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici T)
      ((rightExtension_contDiff T a).of_le (nat_le_infty k)).contDiffAt
      (mem_Ici.mpr le_rfl)]
  exact rightExtension_jets T a k

omit [CompleteSpace E] in
theorem rightExtension_zero_from (T : ℝ) (a : ℕ → E) {t : ℝ} (ht : T + 1 ≤ t) :
    rightExtension T a t = 0 := by
  apply extension_zero_of_one_le_abs
  exact le_trans (by linarith : 1 ≤ t - T) (le_abs_self _)

/-- Borel's jet realization theorem with a fixed compact support, constructed
from the cutoff series rather than assumed as an extension principle. -/
theorem exists_smooth_compact_extension (a : ℕ → E) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ tsupport f ⊆ Icc (-1 : ℝ) 1 ∧
      (∀ k : ℕ, iteratedDeriv k f 0 = a k) :=
  ⟨extension a, extension_contDiff a, extension_tsupport a, extension_jets a⟩

/-- The interface for gluing to left endpoint limits at an arbitrary time. -/
theorem exists_smooth_right_extension (T : ℝ) (a : ℕ → E) :
    ∃ f : ℝ → E, ContDiffOn ℝ ∞ f (Ici T) ∧
      (∀ k : ℕ, iteratedDerivWithin k f (Ici T) T = a k) ∧
      (∀ t : ℝ, T + 1 ≤ t → f t = 0) :=
  ⟨rightExtension T a, (rightExtension_contDiff T a).contDiffOn,
    rightExtension_right_jets T a, fun _ ht => rightExtension_zero_from T a ht⟩

end Complete

end NavierStokes.BorelExtension
