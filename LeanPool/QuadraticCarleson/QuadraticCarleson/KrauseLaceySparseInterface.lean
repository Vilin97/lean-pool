/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.Bohr

/-!
# Interface to the Krause--Lacey sparse theorem

The result cited as `KL18`, Theorem 1.1, in the endpoint paper is Ben Krause
and Michael T. Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms*, Studia Math. 242 (2018), 217--229, arXiv:1609.01564.  In the
arXiv version the main statement is Theorem 1.6: for `d ≥ 2` the maximal
truncation with phase `exp (2 π i y^d)` has sparse `(1,r)` norm
`O(1 / (r - 1))`, for `1 < r ≤ 2`.

That theorem is not present in Mathlib.  Its proof uses oscillatory `TT*`, a
three-shift dyadic localization, a Calderón--Zygmund stopping recursion,
Carleson packing, John--Nirenberg, and Rademacher--Menshov.  This file begins
the missing branch with the exact project-facing pieces that can be proved
without postulating the analytic theorem:

* identification of the source's `1/4` sparseness convention with the
  project's approved `1/4` convention;
* the exact comparison `1/(p-1) ≤ p' ≤ 2/(p-1)` on `1 < p ≤ 2`;
* the algebraic dilation which reduces every nonzero quadratic modulation to
  one of the two signs occurring in the degree-two source theorem;
* linearity and sublinearity of every fixed quadratic Hilbert truncation on
  the project's test-function space, and its finite truncation maxima.

The sparseness conventions now agree exactly; no splitting or refinement is
required.  The remaining genuine adapter gap is that the full pointwise
supremum is naturally extended-real-valued until almost-everywhere finiteness
is established, while `TestOperator` is a total complex-valued function.
Fixed truncations avoid that issue.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate ENNReal Pointwise

namespace QuadraticCarleson


/-- The sparseness parameter used explicitly by Krause--Lacey. -/
def IsKrauseLaceySparse (S : Set RealInterval) : Prop :=
  IsSparse (1 / 4) S

/-- Sparseness is monotone when its density parameter is decreased. -/
theorem IsSparse.mono_parameter {η η' : ℝ} {S : Set RealInterval}
    (hS : IsSparse η S) (hη' : 0 < η') (hη'η : η' ≤ η) :
    IsSparse η' S := by
  rcases hS with ⟨hη, hη1, E, hEmeas, hEsub, hEdisj, hEmass⟩
  refine ⟨hη', hη'η.trans_lt hη1, E, hEmeas, hEsub, hEdisj, ?_⟩
  intro I
  exact (mul_le_mul_of_nonneg_right hη'η I.1.length_pos.le).trans (hEmass I)

/-- The Krause--Lacey convention and the project's approved sparse-family
convention are definitionally identical. -/
theorem isKrauseLaceySparse_iff {S : Set RealInterval} :
    IsKrauseLaceySparse S ↔ IsSparse (1 / 4) S := Iff.rfl

/-- With the approved parameter, the project's sparse-bound interface is
literally the Krause--Lacey convention; there is no constant loss or family
refinement hidden in this adapter. -/
theorem hasSparseOnePBound_iff_krauseLacey (C p : ℝ) (T : TestOperator) :
    HasSparseOnePBound C p T ↔
      ∀ f g : L0Infinity,
        ∃ S : Set RealInterval, IsKrauseLaceySparse S ∧
          ENNReal.ofReal ‖operatorPairing T f g‖ ≤
            ENNReal.ofReal C * sparseForm p f g S := Iff.rfl

/-- Krause--Lacey's quantitative factor, written literally. -/
noncomputable def krauseLaceyFactor (p : ℝ) : ℝ :=
  1 / (p - 1)

theorem krauseLaceyFactor_pos {p : ℝ} (hp : 1 < p) :
    0 < krauseLaceyFactor p := by
  exact one_div_pos.mpr (sub_pos.mpr hp)

/-- On the range used by the endpoint paper, the cited factor is bounded by
the project's Hölder conjugate `p' = p/(p-1)`. -/
theorem krauseLaceyFactor_le_holderConjugate {p : ℝ} (hp : 1 < p) :
    krauseLaceyFactor p ≤ holderConjugate p := by
  rw [krauseLaceyFactor, holderConjugate]
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr hp)).2 (by linarith)

/-- Conversely `p'` differs from the source's `1/(p-1)` by at most a factor
two when `p ≤ 2`. -/
theorem holderConjugate_le_two_mul_krauseLaceyFactor
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    holderConjugate p ≤ 2 * krauseLaceyFactor p := by
  rw [krauseLaceyFactor, holderConjugate]
  apply (div_le_iff₀ (sub_pos.mpr hp)).2
  field_simp [ne_of_gt (sub_pos.mpr hp)]
  nlinarith

/-- The kernel phase is unchanged when a positive scale is moved from the
modulation into the spatial variable.  This is the algebraic core of the
dilation reduction used immediately after Corollary
`c:finitemodulationsweak11` in the paper. -/
theorem quadratic_phase_scale (sigma a t : ℝ) :
    phase ((sigma * a ^ 2) * t ^ 2) = phase (sigma * (a * t) ^ 2) := by
  congr 1
  ring

/-- The corresponding identity for the singular kernel density.  The factor
`a` is precisely the Jacobian which cancels under the change of variables
`u = a t`.  Division at `t = 0` follows Lean's usual zero convention, so the
identity is genuinely pointwise. -/
theorem quadratic_kernel_density_scale (sigma a t : ℝ) (ha : a ≠ 0) :
    phase ((sigma * a ^ 2) * t ^ 2) / (t : ℂ) =
      (a : ℂ) * (phase (sigma * (a * t) ^ 2) / ((a * t : ℝ) : ℂ)) := by
  rw [quadratic_phase_scale]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [ha, ht]
    push_cast
    ring

/-- Every nonzero real modulation is a signed square, with scale
`sqrt |lambda|`.  Thus the degree-two Krause--Lacey theorem at phase `+t²`
(and its conjugate at `-t²`) covers exactly the nonzero convention fixed by
the endpoint paper. -/
theorem nonzero_modulation_eq_signed_sqrt_square {lam : ℝ} (hlam : lam ≠ 0) :
    lam = (if lam < 0 then (-1 : ℝ) else 1) * (Real.sqrt |lam|) ^ 2 := by
  rw [Real.sq_sqrt (abs_nonneg lam)]
  by_cases hneg : lam < 0
  · simp [hneg, abs_of_neg hneg]
  · have hpos : 0 < lam := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hlam)
    simp [hneg, abs_of_pos hpos]

/-- Pointwise normalization of the singular density for an arbitrary
nonzero modulation.  This makes the paper's exclusion of `lambda = 0`
explicit: no scale selector is defined at zero. -/
theorem quadratic_kernel_density_normalize_nonzero {lam : ℝ} (hlam : lam ≠ 0)
    (t : ℝ) :
    phase (lam * t ^ 2) / (t : ℂ) =
      (Real.sqrt |lam| : ℂ) *
        (phase ((if lam < 0 then (-1 : ℝ) else 1) *
          (Real.sqrt |lam| * t) ^ 2) /
            ((Real.sqrt |lam| * t : ℝ) : ℂ)) := by
  let a : ℝ := Real.sqrt |lam|
  let sigma : ℝ := if lam < 0 then -1 else 1
  have hsqrt : a ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 hlam))
  have hdecomp : lam = sigma * a ^ 2 :=
    nonzero_modulation_eq_signed_sqrt_square hlam
  change phase (lam * t ^ 2) / (t : ℂ) =
    (a : ℂ) * (phase (sigma * (a * t) ^ 2) / ((a * t : ℝ) : ℂ))
  rw [hdecomp]
  exact quadratic_kernel_density_scale sigma a t hsqrt

/-- Exact dilation invariance of a fixed quadratic Hilbert truncation.
Changing variables `u = a t` moves a positive spatial scale from the
modulation to the input, the evaluation point, and the truncation radius.
This is the precise integral identity behind the paper's reduction to unit
absolute modulation. -/
theorem quadraticHilbertTrunc_scale (sigma : ℝ) {a : ℝ} (ha : 0 < a) (ε : ℝ)
    (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertTrunc (sigma * a ^ 2) ε f x =
      quadraticHilbertTrunc sigma (a * ε) (fun u ↦ f (u / a)) (a * x) := by
  unfold quadraticHilbertTrunc
  let s : Set ℝ := {t : ℝ | ε < |t|}
  let s' : Set ℝ := {u : ℝ | a * ε < |u|}
  let F : ℝ → ℂ := fun u ↦
    f ((a * x - u) / a) * phase (sigma * u ^ 2) / (u : ℂ)
  have hset : a • s = s' := by
    ext u
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨t, ht, rfl⟩
      change a * ε < |a • t|
      simp only [smul_eq_mul, abs_mul, abs_of_pos ha]
      exact mul_lt_mul_of_pos_left ht ha
    · intro hu
      change a * ε < |u| at hu
      refine ⟨a⁻¹ * u, ?_, ?_⟩
      · change ε < |a⁻¹ * u|
        rw [abs_mul, abs_inv, abs_of_pos ha]
        exact (lt_inv_mul_iff₀ ha).2 (by simpa [mul_comm] using hu)
      · simp only [smul_eq_mul]
        field_simp [ha.ne']
  have hcv := Measure.setIntegral_comp_smul_of_pos volume F s ha
  rw [hset, Module.finrank_self, pow_one] at hcv
  have hcv' : (∫ t in s, F (a * t)) = a⁻¹ • ∫ u in s', F u := by
    simpa only [smul_eq_mul] using hcv
  change (∫ t in s, f (x - t) * phase (sigma * a ^ 2 * t ^ 2) / (t : ℂ)) =
    ∫ u in s', F u
  calc
    (∫ t in s, f (x - t) * phase (sigma * a ^ 2 * t ^ 2) / (t : ℂ)) =
        (a : ℂ) * ∫ t in s, F (a * t) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t ↦ by
            dsimp [F]
            have harg : (a * x - a * t) / a = x - t := by
              field_simp [ha.ne']
            rw [harg]
            have hk := quadratic_kernel_density_scale sigma a t ha.ne'
            calc
              f (x - t) * phase (sigma * a ^ 2 * t ^ 2) / (t : ℂ) =
                  f (x - t) *
                    (phase (sigma * a ^ 2 * t ^ 2) / (t : ℂ)) := by ring
              _ = f (x - t) * ((a : ℂ) *
                    (phase (sigma * (a * t) ^ 2) / ((a * t : ℝ) : ℂ))) := by rw [hk]
              _ = (a : ℂ) *
                  (f (x - t) * phase (sigma * (a * t) ^ 2) /
                    ((a * t : ℝ) : ℂ)) := by ring)
    _ = (a : ℂ) * ((a ^ (1 : ℕ))⁻¹ • ∫ u in s', F u) := by
      rw [hcv']
      simp only [pow_one]
    _ = ∫ u in s', F u := by
      rw [pow_one]
      simp [ha.ne']

/-- Paper-facing form of dilation invariance: each nonzero modulation is
reduced exactly to sign `+1` or `-1`, with no definition at modulation zero. -/
theorem quadraticHilbertTrunc_normalize_nonzero {lam : ℝ} (hlam : lam ≠ 0)
    (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x =
      quadraticHilbertTrunc (if lam < 0 then (-1 : ℝ) else 1)
        (Real.sqrt |lam| * ε) (fun u ↦ f (u / Real.sqrt |lam|))
        (Real.sqrt |lam| * x) := by
  let a : ℝ := Real.sqrt |lam|
  let sigma : ℝ := if lam < 0 then -1 else 1
  have ha : 0 < a := Real.sqrt_pos.2 (abs_pos.2 hlam)
  have hdecomp : lam = sigma * a ^ 2 :=
    nonzero_modulation_eq_signed_sqrt_square hlam
  change quadraticHilbertTrunc lam ε f x =
    quadraticHilbertTrunc sigma (a * ε) (fun u ↦ f (u / a)) (a * x)
  rw [hdecomp]
  exact quadraticHilbertTrunc_scale sigma ha ε f x

/-- Reversing the sign of the real phase conjugates the unit complex
oscillation. -/
theorem phase_neg_eq_conj (s : ℝ) : phase (-s) = conj (phase s) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The negative unit quadratic truncation is obtained from the positive
one by conjugating both the input and output.  Consequently the even-degree
Krause--Lacey estimate for its displayed `+t²` phase also controls the `-t²`
case with the identical constant. -/
theorem quadraticHilbertTrunc_neg_one_eq_conj (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertTrunc (-1) ε f x =
      conj (quadraticHilbertTrunc 1 ε (fun y ↦ conj (f y)) x) := by
  unfold quadraticHilbertTrunc
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    change f (x - t) * phase (-1 * t ^ 2) / (t : ℂ) =
      conj (conj (f (x - t)) * phase (1 * t ^ 2) / (t : ℂ))
    rw [map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← phase_neg_eq_conj]
    congr 2
    ring_nf)

/-- A fixed truncation, represented in the project's complex-valued operator
type.  Unlike the full supremum this is everywhere finite on `L₀∞`. -/
noncomputable def quadraticHilbertTruncTestOperator
    (lam ε : ℝ) : TestOperator :=
  fun f x ↦ quadraticHilbertTrunc lam ε f x

private theorem L0Infinity.integrable_for_truncation
    (f : L0Infinity) : Integrable f := by
  have hcompact : IsCompact (tsupport f) := f.hasCompactSupport_toFun
  have hfinite : volume (tsupport f) < ∞ := hcompact.measure_lt_top
  rcases f.bounded_toFun with ⟨C, hC⟩
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  exact IntegrableOn.of_bound hfinite
    f.measurable_toFun.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall hC)

private theorem integrableOn_quadraticHilbertTrunc_integrand
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (f : L0Infinity) (x : ℝ) :
    IntegrableOn
      (fun t ↦ f (x - t) * phase (lam * t ^ 2) / (t : ℂ))
      {t : ℝ | ε < |t|} := by
  let s : Set ℝ := {t : ℝ | ε < |t|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_id.abs
  have hf : Integrable (fun t ↦ f (x - t)) :=
    f.integrable_for_truncation.comp_sub_left x
  have hm : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2) / (t : ℂ)) := by
    apply Measurable.div
    · unfold phase
      fun_prop
    · exact Complex.measurable_ofReal.comp measurable_id
  have hbound : ∀ᵐ t ∂volume.restrict s,
      ‖phase (lam * t ^ 2) / (t : ℂ)‖ ≤ 1 / ε := by
    filter_upwards [ae_restrict_mem hs] with t ht
    have ht' : ε < |t| := ht
    rw [norm_div, norm_phase, Complex.norm_real, Real.norm_eq_abs]
    exact one_div_le_one_div_of_le hε ht'.le
  have hi := hf.integrableOn.bdd_mul hm.aestronglyMeasurable.restrict hbound
  change Integrable
    (fun t ↦ f (x - t) * phase (lam * t ^ 2) / (t : ℂ))
    (volume.restrict {t : ℝ | ε < |t|})
  simpa only [s, mul_comm, div_eq_mul_inv, mul_left_comm, mul_assoc] using hi

theorem quadraticHilbertTrunc_add
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (f g : L0Infinity) (x : ℝ) :
    quadraticHilbertTruncTestOperator lam ε (L0Infinity.add f g) x =
      quadraticHilbertTruncTestOperator lam ε f x +
        quadraticHilbertTruncTestOperator lam ε g x := by
  have hf := integrableOn_quadraticHilbertTrunc_integrand lam hε f x
  have hg := integrableOn_quadraticHilbertTrunc_integrand lam hε g x
  change quadraticHilbertTrunc lam ε (L0Infinity.add f g) x =
    quadraticHilbertTrunc lam ε f x + quadraticHilbertTrunc lam ε g x
  unfold quadraticHilbertTrunc
  rw [← integral_add hf hg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    change (f (x - t) + g (x - t)) * phase (lam * t ^ 2) / (t : ℂ) = _
    ring)

theorem quadraticHilbertTrunc_smul
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    quadraticHilbertTruncTestOperator lam ε (L0Infinity.smul c f) x =
      c * quadraticHilbertTruncTestOperator lam ε f x := by
  have hf := integrableOn_quadraticHilbertTrunc_integrand lam hε f x
  change quadraticHilbertTrunc lam ε (L0Infinity.smul c f) x =
    c * quadraticHilbertTrunc lam ε f x
  unfold quadraticHilbertTrunc
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    change (c * f (x - t)) * phase (lam * t ^ 2) / (t : ℂ) = _
    ring)

/-- Every positive fixed truncation has the sublinearity required by the
project's sparse framework. -/
theorem quadraticHilbertTruncTestOperator_isSublinear
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsSublinear (quadraticHilbertTruncTestOperator lam ε) := by
  constructor
  · intro f g x
    rw [quadraticHilbertTrunc_add lam hε]
    exact norm_add_le _ _
  · intro c f x
    rw [quadraticHilbertTrunc_smul lam hε, norm_mul]

/-- A finite maximum over positive truncation parameters.  This is an
everywhere-finite surrogate for the full maximal truncation and therefore
fits the project's real-valued finite-maximal framework without choosing an
almost-everywhere representative. -/
noncomputable def finiteQuadraticHilbertTruncationMax {N : ℕ}
    (lam : ℝ) (eps : Fin N → ℝ) : L0Infinity → ℝ → ℝ :=
  finiteMax (fun j ↦ quadraticHilbertTruncTestOperator lam (eps j))

theorem quadraticHilbertTrunc_norm_le_finiteTruncationMax {N : ℕ}
    (lam : ℝ) (eps : Fin N → ℝ) (j : Fin N) (f : L0Infinity) (x : ℝ) :
    ‖quadraticHilbertTrunc lam (eps j) f x‖ ≤
      finiteQuadraticHilbertTruncationMax lam eps f x := by
  exact le_finiteMax (fun i ↦ quadraticHilbertTruncTestOperator lam (eps i)) f x j

end QuadraticCarleson
