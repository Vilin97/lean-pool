/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.OrbitAction
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Fourier.HaagerupZsido.Kernel
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite Fourier interpolation of the reciprocal

Seam 2 of 4: the harmonic analysis.  For separated real arrays `α` and `β` the
reciprocal `(α i - β j)⁻¹` is represented by finitely many Fourier atoms with
controlled coefficient mass, which is what turns the orbit algebra of
`…ReciprocalMultiplier.OrbitAction` into an interpolation certificate.

* `exists_finite_average_approximation`, the finite quadrature step: an integral
  average is a finite convex combination up to `ε`;
* `exists_finite_fourier_interpolation` and its mass-bounded refinement, proved by
  Lagrange interpolation against the Haagerup--Zsidó kernel;
* the interpolation predicates `HasFiniteReciprocalFourierInterpolation`,
  `HasApproximateFiniteReciprocalFourierInterpolation`,
  `HasDoubledRealReciprocalOrbitInterpolation`, `HasReciprocalOrbitInterpolation`
  and the kernel hypothesis `HasIntegrableReciprocalFourierKernel`;
* `hasIntegrableReciprocalFourierKernel_pi_div_two`, the `π / 2` mass, and the
  transfer theorems that pass from an integrable kernel to an approximate finite
  interpolation, from approximate to exact, and from normalized gap to general.

## Provenance

*Split, not restated.*  This module was part of
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Internal/ReciprocalMultiplier.lean`
before that 2887-line file was divided — the largest in
the library, and nearly 3x Tau Ceti's stated 1000-line limit for a new file
(`ForTauCeti/README.md` §4) — along its four mathematical seams.  **No statement,
signature, proof, attribute or declaration name changed**; the split is a file
boundary plus the imports it forces.  The file itself had carried
`set_option linter.style.longFile 2900` and a note saying a split "is not a
migration lane's business"; SPLIT-1K is the lane whose business it is, and the
option is gone from all four parts.

That file in turn was
`DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean`
before the sin-Θ closure moved into the staging layer.

Literature bridge for the group as a whole:
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.
-/

public section

namespace TauCeti

open TauCeti
open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The average of an integrable function for a nonzero finite measure can be
approximated by a finite convex combination of actual values of the function.

This is the finite quadrature step used to turn an integrable scalar Fourier
kernel into finitely many Fourier atoms.  It is stated for a general real
normed space so the coefficient mass can later be included as one additional
coordinate of the integrand. -/
theorem exists_finite_average_approximation
    {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ] [NeZero μ]
    (g : Ω → V) (hg : MeasureTheory.Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ z : Fin q → Ω,
      (∀ r, 0 ≤ w r) ∧
      ∑ r, w r = 1 ∧
      dist (∑ r, w r • g (z r)) (⨍ x, g x ∂μ) < ε := by
  classical
  have havg : (⨍ x, g x ∂μ) ∈
      closedConvexHull ℝ (Set.range g) := by
    exact convex_closedConvexHull.average_mem isClosed_closedConvexHull
      (Filter.Eventually.of_forall fun x => subset_closedConvexHull (Set.mem_range_self x)) hg
  rw [closedConvexHull_eq_closure_convexHull] at havg
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp havg ε hε
  rcases mem_convexHull_iff_exists_fintype.mp hy with
    ⟨ι, hι, w, v, hw₀, hw₁, hv, hvsum⟩
  let : Fintype ι := hι
  let z : ι → Ω := fun i => Classical.choose (hv i)
  have hz (i : ι) : g (z i) = v i := Classical.choose_spec (hv i)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, w ∘ e.symm, z ∘ e.symm, ?_, ?_, ?_⟩
  · intro r
    exact hw₀ (e.symm r)
  · simpa only [Function.comp_apply] using (e.symm.sum_comp w).trans hw₁
  · have hsum : ∑ i, w i • g (z i) = y := by
      calc
        ∑ i, w i • g (z i) = ∑ i, w i • v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hz i]
        _ = y := hvsum
    have hreindex :
        (∑ r : Fin (Fintype.card ι),
          (w ∘ e.symm) r • g ((z ∘ e.symm) r)) =
        ∑ i : ι, w i • g (z i) := by
      simpa only [Function.comp_apply] using
        e.symm.sum_comp (fun i => w i • g (z i))
    rw [hreindex, hsum, dist_comm]
    exact hdist

/-- Any finite set of reals can be rescaled into an arc shorter than a full
turn, on which `Circle.exp` is injective.

The scale `τ = (1 + ∑ |x|)⁻¹` sends `s` into `Icc (-1) 1`, whose length `2` is
less than `2π`; injectivity of the rescaled exponential then follows from
`Circle.exp_injOn_Icc`.  This is what lets a Lagrange interpolation be set up on
the nodes `exp (τ x)`. -/
private theorem exists_pos_injOn_circle_exp (s : Finset ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ Set.InjOn (fun x : ℝ => (Circle.exp (τ * x) : ℂ)) s := by
  classical
  let R : ℝ := ∑ x ∈ s, |x|
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(1 + R)⁻¹, by positivity, ?_⟩
  set τ : ℝ := (1 + R)⁻¹ with hτdef
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have harg (x : ℝ) (hx : x ∈ s) : τ * x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hxR : |x| ≤ R := Finset.single_le_sum (fun z _ => abs_nonneg z) hx
    have hden : 0 < 1 + R := by linarith
    have habs : |τ * x| < 1 := by
      rw [abs_mul, abs_of_pos hτ, hτdef, inv_mul_eq_div, div_lt_one hden]
      linarith
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  intro x hx x' hx' hzx
  have harc : (1 : ℝ) - (-1) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hphase : τ * x = τ * x' :=
    Circle.exp_injOn_Icc harc (harg x hx) (harg x' hx') (Subtype.ext hzx)
  exact mul_left_cancel₀ (ne_of_gt hτ) hphase

/-- **A polynomial evaluated at `Circle.exp (τ x)` is a finite Fourier sum in
`x`**, with the polynomial's coefficients as Fourier coefficients and the
frequencies `r τ` for `r` below any bound `q` on the degree.

This is the step that turns Lagrange interpolation — an algebraic statement
about a polynomial at distinct nodes — into the analytic statement wanted here,
and it is pure bookkeeping: `zʳ = exp (r τ x i)` because `z = exp (τ x i)`.
Stated separately because the two interpolation theorems below differ in how
they bound the degree (`natDegree + 1` for one, `s.card + 1` for the other) and
in nothing else, so this is exactly their common part. -/
private theorem eval_circle_exp_eq_fourier_sum {q : ℕ} (τ : ℝ) (p : Polynomial ℂ)
    (hp : p.natDegree < q) (x : ℝ) :
    p.eval ((Circle.exp (τ * x) : ℂ)) =
      ∑ r : Fin q, p.coeff r *
        Complex.exp (((((r : ℕ) : ℝ) * τ * x : ℝ) : ℂ) * Complex.I) := by
  rw [Polynomial.eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp only [Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Arbitrary complex values on a finite set of real frequencies admit an
exact finite Fourier interpolation.

The proof places the finitely many frequencies in an arc shorter than a full
circle, applies Lagrange interpolation to their distinct complex phases, and
reads the polynomial coefficients as Fourier coefficients.  This is the
algebraic correction mechanism needed when a reciprocal Fourier integral is
first approximated by a finite sum. -/
theorem exists_finite_fourier_interpolation
    (s : Finset ℝ) (y : ℝ → ℂ) :
    ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
      ∀ x ∈ s, y x = ∑ r, a r * Complex.exp
        ((((t r * x) : ℝ) : ℂ) * Complex.I) := by
  classical
  obtain ⟨τ, -, hzinj⟩ := exists_pos_injOn_circle_exp s
  let p : Polynomial ℂ := Lagrange.interpolate s (fun x => (Circle.exp (τ * x) : ℂ)) y
  refine ⟨p.natDegree + 1, fun r => p.coeff r, fun r => (r : ℕ) * τ, fun x hx => ?_⟩
  rw [← Lagrange.eval_interpolate_at_node y hzinj hx]
  exact eval_circle_exp_eq_fourier_sum τ p (Nat.lt_succ_self _) x

/-- The finite Fourier interpolation map can be chosen with coefficient mass
bounded linearly by the `ℓ1` mass of the prescribed values.

For a fixed finite frequency set the constant is allowed to depend on that
set.  This is exactly the stability needed to correct a uniformly vanishing
finite error vector without changing the limiting Fourier mass. -/
theorem exists_finite_fourier_interpolation_with_mass_bound
    (s : Finset ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ → ℂ,
      ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
        (∀ x ∈ s, y x = ∑ r, a r * Complex.exp
          ((((t r * x) : ℝ) : ℂ) * Complex.I)) ∧
        ∑ r, ‖a r‖ ≤ K * ∑ x ∈ s, ‖y x‖ := by
  classical
  obtain ⟨τ, hτ, hinj⟩ := exists_pos_injOn_circle_exp s
  let z : ℝ → ℂ := fun x => (Circle.exp (τ * x) : ℂ)
  have hzinj : Set.InjOn z s := hinj
  let q : ℕ := s.card + 1
  let K : ℝ := ∑ n : Fin q, ∑ x ∈ s,
    ‖(Lagrange.basis s z x).coeff (n : ℕ)‖
  refine ⟨K, Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro y
  let p : Polynomial ℂ := Lagrange.interpolate s z y
  have hpdeg : p.natDegree < q := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_le_of_degree_le
    exact (Lagrange.degree_interpolate_le y hzinj).trans (by
      exact_mod_cast Nat.sub_le s.card 1)
  refine ⟨q, fun n => p.coeff n, fun n => (n : ℕ) * τ, ?_, ?_⟩
  · intro x hx
    rw [← Lagrange.eval_interpolate_at_node y hzinj hx]
    exact eval_circle_exp_eq_fourier_sum τ p hpdeg x
  · have hcoeff (n : ℕ) :
        p.coeff n = ∑ x ∈ s, y x * (Lagrange.basis s z x).coeff n := by
      simp [p, Lagrange.interpolate_apply]
    calc
      ∑ n : Fin q, ‖p.coeff n‖ ≤
          ∑ n : Fin q, ∑ x ∈ s,
            ‖y x‖ * ‖(Lagrange.basis s z x).coeff (n : ℕ)‖ := by
        apply Finset.sum_le_sum
        intro n _
        rw [hcoeff]
        simpa only [norm_mul] using
          norm_sum_le s (fun x => y x * (Lagrange.basis s z x).coeff (n : ℕ))
      _ ≤ ∑ n : Fin q, (∑ x ∈ s, ‖y x‖) *
          (∑ x ∈ s, ‖(Lagrange.basis s z x).coeff (n : ℕ)‖) := by
        apply Finset.sum_le_sum
        intro n _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        gcongr
        exact Finset.single_le_sum (fun u hu => norm_nonneg (y u)) hx
      _ = K * ∑ x ∈ s, ‖y x‖ := by
        simp only [K]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        ring

/-- A finite scalar Fourier interpolation of the reciprocal function on two
finite real frequency arrays.

The certificate is deliberately independent of Hilbert spaces, matrix units,
singular values, and norms on operators.  Its coefficient mass is the finite
analogue of the total variation of the classical reciprocal Fourier measure. -/
@[expose]
def HasFiniteReciprocalFourierInterpolation
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (δ mass : ℝ) : Prop :=
  ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
    (∀ i j,
      (δ : ℂ) = (((α i - β j : ℝ) : ℂ)) *
        ∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)) ∧
    ∑ r, ‖a r‖ ≤ mass

/-- A finite Fourier sum that approximates the reciprocal function on two
finite real frequency arrays.  Unlike the exact certificate, the error is
measured before multiplication by the frequency difference. -/
def HasApproximateFiniteReciprocalFourierInterpolation
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (mass tolerance : ℝ) : Prop :=
  ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
    (∀ i j,
      ‖(1 : ℂ) / (((α i - β j : ℝ) : ℂ)) -
        ∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)‖ ≤ tolerance) ∧
    ∑ r, ‖a r‖ ≤ mass

/-- A reciprocal interpolation on real coordinate matrix units after doubling
both Hilbert spaces.  Complex Fourier coefficients have been replaced by real
weights and coordinatewise orthogonal rotations. -/
@[expose]
def HasDoubledRealReciprocalOrbitInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    (delta mass : ℝ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ,
    ∃ U : Fin q → WithLp 2 (FR × FR) ≃ₗᵢ[ℝ] WithLp 2 (FR × FR),
      ∃ V : Fin q → WithLp 2 (ER × ER) ≃ₗᵢ[ℝ] WithLp 2 (ER × ER),
        (∀ i j,
          delta • UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
            (alpha i - beta j) •
              ((∑ r, w r • unitaryOrbitAction (U r) (V r))
                (UnitarilyInvariantSeminorm.orthogonalBlockSum
                  (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)))) ∧
        ∑ r, |w r| ≤ mass

/-- An integrable scalar Fourier kernel representing the reciprocal function
outside the unit interval, with controlled `L¹` mass. -/
def HasIntegrableReciprocalFourierKernel (mass : ℝ) : Prop :=
  ∃ f : ℝ → ℂ,
    Measurable f ∧
    MeasureTheory.Integrable f ∧
    (∀ x : ℝ, 1 ≤ |x| →
      (∫ t, f t * Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        (1 : ℂ) / (x : ℂ)) ∧
    (∫ t, ‖f t‖) ≤ mass

/-- **The sharp reciprocal kernel exists.**  The explicit Haagerup--Zsidó
`α = 0` kernel is measurable and integrable, represents `1 / x` on the whole
exterior region `1 ≤ |x|`, and has `L¹` mass exactly `π / 2`. -/
theorem hasIntegrableReciprocalFourierKernel_pi_div_two :
    HasIntegrableReciprocalFourierKernel (Real.pi / 2) :=
  ⟨HaagerupZsido.reciprocalKernel,
    HaagerupZsido.measurable_reciprocalKernel,
    HaagerupZsido.integrable_reciprocalKernel,
    fun x hx => HaagerupZsido.reciprocalKernel_fourier x hx,
    HaagerupZsido.integral_norm_reciprocalKernel.le⟩

/-- The pointwise phase of a complex-valued function: `f t / ‖f t‖` off the zero
set, and `0` on it.  Total by construction, so no integrability or non-vanishing
hypothesis is needed to form it. -/
private noncomputable def phaseOf (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  if f t = 0 then 0 else f t / (‖f t‖ : ℂ)

private theorem measurable_phaseOf {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (phaseOf f) :=
  Measurable.ite
    (measurableSet_eq_fun hf measurable_const)
    measurable_const (by fun_prop)

private theorem norm_phaseOf_le_one (f : ℝ → ℂ) (t : ℝ) : ‖phaseOf f t‖ ≤ 1 := by
  by_cases ht : f t = 0
  · simp [phaseOf, ht]
  · simp [phaseOf, ht]

/-- The phase recovers the function from its modulus. -/
private theorem norm_mul_phaseOf (f : ℝ → ℂ) (t : ℝ) :
    (‖f t‖ : ℂ) * phaseOf f t = f t := by
  by_cases ht : f t = 0
  · simp [phaseOf, ht]
  · simp only [phaseOf, ite_eq_right ht]
    field_simp [norm_ne_zero_iff.mpr ht]

/-- **The `‖f‖`-weighted measure has real total mass `∫ ‖f‖`.**  A general fact
about `volume.withDensity (fun t => ENNReal.ofReal ‖f t‖)` for integrable `f`,
with no Fourier content; it was inlined in the interpolation proof below. -/
private theorem measureReal_univ_withDensity_ofReal_norm
    {f : ℝ → ℂ} (hfint : MeasureTheory.Integrable f) :
    (MeasureTheory.volume.withDensity
        (fun t => ENNReal.ofReal ‖f t‖)).real Set.univ = ∫ t, ‖f t‖ := by
  rw [MeasureTheory.measureReal_def]
  simp only [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    MeasureTheory.setLIntegral_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint.norm
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
  exact ENNReal.toReal_ofReal
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)

/-- **A reciprocal Fourier kernel has total variation at least `‖1/d‖`.**  If
`∫ f t · exp (i t d) = 1/d` whenever `1 ≤ |d|`, then `‖1/d‖ ≤ ∫ ‖f t‖`: the
triangle inequality for the integral, and `‖exp (i t d)‖ = 1` pointwise.

Inlined in the interpolation proof below as the step that makes the weighted
measure nonzero. -/
private theorem norm_inv_le_integral_norm_of_reciprocalFourier
    {f : ℝ → ℂ}
    (hfourier : ∀ d : ℝ, 1 ≤ |d| →
      ∫ t, f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I)) = 1 / (d : ℂ))
    {d : ℝ} (hd : 1 ≤ |d|) :
    ‖(1 : ℂ) / (d : ℂ)‖ ≤ ∫ t, ‖f t‖ := by
  rw [← hfourier d hd]
  have hexpnorm (t : ℝ) :
      ‖Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  calc
    ‖∫ t, f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))‖ ≤
        ∫ t, ‖f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t, ‖f t‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul, hexpnorm t, mul_one]

/-- **The frequency-atom family is measurable and pointwise bounded by one.**
`atom t ij = phaseOf f t · exp (i t (α i - β j))` has every coordinate of modulus
at most one, since `phaseOf` does and the exponential has modulus exactly one.

Stated on an arbitrary measurable phase of modulus at most one rather than on
`phaseOf f`, because that is all the bound uses. -/
private theorem measurable_and_norm_le_one_frequencyAtom
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {phase : ℝ → ℂ} (hphase_meas : Measurable phase)
    (hphase_norm : ∀ t, ‖phase t‖ ≤ 1) :
    Measurable (fun t ij => phase t * Complex.exp
        ((((t * (α (Prod.fst ij) - β (Prod.snd ij)) : ℝ) : ℂ) * Complex.I)) :
      ℝ → (Fin m × Fin n → ℂ)) ∧
    ∀ t, ‖(fun ij => phase t * Complex.exp
        ((((t * (α (Prod.fst ij) - β (Prod.snd ij)) : ℝ) : ℂ) * Complex.I)) :
      Fin m × Fin n → ℂ)‖ ≤ 1 := by
  constructor
  · apply measurable_pi_lambda
    intro ij
    fun_prop
  · intro t
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro ij
    have hexpnorm :
        ‖Complex.exp
          ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I))‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    simp only [norm_mul, hexpnorm, mul_one]
    exact hphase_norm t

/-- **The weighted integral of a frequency atom is the reciprocal it interpolates.**
Against `volume.withDensity (ofReal ∘ norm ∘ f)`, the atom
`phaseOf f t · exp (i t d)` integrates to `1/d` whenever `f` reciprocal-interpolates
at `d`, because the density cancels the phase: `‖f t‖ · phaseOf f t = f t`. -/
private theorem integral_withDensity_frequencyAtom
    {f : ℝ → ℂ} (hfmeas : Measurable f)
    (hfourier : ∀ d : ℝ, 1 ≤ |d| →
      ∫ t, f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I)) = 1 / (d : ℂ))
    {d : ℝ} (hd : 1 ≤ |d|) :
    (∫ t, phaseOf f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))
        ∂(MeasureTheory.volume.withDensity fun t => ENNReal.ofReal ‖f t‖)) =
      (1 : ℂ) / (d : ℂ) := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← hfourier d hd]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  simp only [ENNReal.toReal_ofReal (norm_nonneg _)]
  calc
    ‖f t‖ • (phaseOf f t * Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))) =
        ((‖f t‖ : ℂ) * phaseOf f t) *
          Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I)) := by
      rw [RCLike.real_smul_eq_coe_mul, ← mul_assoc]
      rfl
    _ = _ := congrArg (fun u : ℂ => u *
      Complex.exp ((((t * d : ℝ) : ℂ) * Complex.I))) (norm_mul_phaseOf f t)

/-- An integrable reciprocal Fourier kernel yields finite Fourier sums of no
greater mass which uniformly approximate any prescribed finite frequency
array. -/
theorem hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {mass tolerance : ℝ}
    (hgap : ∀ i j, 1 ≤ |α i - β j|) (htolerance : 0 < tolerance)
    (hkernel : HasIntegrableReciprocalFourierKernel mass) :
    HasApproximateFiniteReciprocalFourierInterpolation
      α β mass tolerance := by
  classical
  rcases hkernel with ⟨f, hfmeas, hfint, hfourier, hmass⟩
  have hmass_nonneg : 0 ≤ mass :=
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _).trans hmass
  cases isEmpty_or_nonempty (Fin m) with
  | inl hm =>
      let := hm
      exact ⟨0, Fin.elim0, Fin.elim0, (fun i => isEmptyElim i), by simpa⟩
  | inr hm =>
    let := hm
    cases isEmpty_or_nonempty (Fin n) with
    | inl hn =>
        let := hn
        exact ⟨0, Fin.elim0, Fin.elim0,
          (fun _i j => isEmptyElim j), by simpa⟩
    | inr hn =>
      let := hn
      let M : ℝ := ∫ t, ‖f t‖
      let density : ℝ → ENNReal := fun t => ENNReal.ofReal ‖f t‖
      let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.withDensity density
      have : MeasureTheory.IsFiniteMeasure μ := by
        dsimp only [μ, density]
        exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hfint.norm.2
      let i₀ : Fin m := Classical.choice inferInstance
      let j₀ : Fin n := Classical.choice inferInstance
      let d₀ : ℝ := α i₀ - β j₀
      have hd₀ : d₀ ≠ 0 := by
        intro hd
        have := hgap i₀ j₀
        simp only [d₀, hd, abs_zero] at this
        norm_num at this
      have hMpos : 0 < M :=
        lt_of_lt_of_le
          (norm_pos_iff.mpr (div_ne_zero one_ne_zero (by exact_mod_cast hd₀)))
          (norm_inv_le_integral_norm_of_reciprocalFourier hfourier (hgap i₀ j₀))
      have hMnonneg : 0 ≤ M := hMpos.le
      have hμreal : μ.real Set.univ = M :=
        measureReal_univ_withDensity_ofReal_norm hfint
      have hμne : μ ≠ 0 := by
        intro hzero
        have : μ.real Set.univ = 0 := by simp [hzero]
        rw [hμreal] at this
        linarith
      let : NeZero μ := ⟨hμne⟩
      let phase : ℝ → ℂ := phaseOf f
      have hphase_meas : Measurable phase := measurable_phaseOf hfmeas
      have hphase_norm (t : ℝ) : ‖phase t‖ ≤ 1 := norm_phaseOf_le_one f t
      have hnorm_mul_phase (t : ℝ) : (‖f t‖ : ℂ) * phase t = f t :=
        norm_mul_phaseOf f t
      let atom : ℝ → (Fin m × Fin n → ℂ) := fun t ij =>
        phase t * Complex.exp
          ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I))
      obtain ⟨hatom_meas, hatom_norm⟩ :=
        measurable_and_norm_le_one_frequencyAtom α β hphase_meas hphase_norm
      have hatom_int : MeasureTheory.Integrable atom μ :=
        MeasureTheory.Integrable.of_bound hatom_meas.aestronglyMeasurable 1
          (Filter.Eventually.of_forall hatom_norm)
      have htolM : 0 < tolerance / M := div_pos htolerance hMpos
      rcases exists_finite_average_approximation μ atom hatom_int htolM with
        ⟨q, w, z, hw_nonneg, hw_sum, hquad⟩
      have hmoment (ij : Fin m × Fin n) :
          (∫ t, atom t ij ∂μ) =
            (1 : ℂ) / ((α ij.1 - β ij.2 : ℝ) : ℂ) :=
        integral_withDensity_frequencyAtom hfmeas hfourier (hgap ij.1 ij.2)
      let A : Fin m × Fin n → ℂ := ⨍ t, atom t ∂μ
      let Q : Fin m × Fin n → ℂ := ∑ r, w r • atom (z r)
      have hMA : M • A = ∫ t, atom t ∂μ := by
        dsimp only [A]
        rw [MeasureTheory.average_eq, hμreal, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hMpos), one_smul]
      have hA_moment (ij : Fin m × Fin n) :
          (M : ℂ) * A ij =
            (1 : ℂ) / ((α ij.1 - β ij.2 : ℝ) : ℂ) := by
        calc
          (M : ℂ) * A ij = (M • A) ij := by
            -- states the goal with the definition unfolded, in the shape the next step needs;
            -- there is no `_apply` lemma to rewrite with here.
            change (M : ℂ) * A ij = M • A ij
            exact (RCLike.real_smul_eq_coe_mul M (A ij)).symm
          _ = (∫ t, atom t ∂μ) ij := congrFun hMA ij
          _ = ∫ t, atom t ij ∂μ := by
            exact MeasureTheory.eval_integral
              (fun ij => hatom_int.eval ij) ij
          _ = _ := hmoment ij
      have hQ : dist Q A < tolerance / M := by
        exact hquad
      rw [dist_eq_norm] at hQ
      have hcoord (ij : Fin m × Fin n) :
          ‖Q ij - A ij‖ < tolerance / M := by
        exact (pi_norm_lt_iff htolM).mp hQ ij
      let a : Fin q → ℂ := fun r =>
        ((M * w r : ℝ) : ℂ) * phase (z r)
      have hsum (ij : Fin m × Fin n) :
          ∑ r, a r * Complex.exp
              ((((z r * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I)) =
            (M : ℂ) * Q ij := by
        simp only [a, Q, Finset.sum_apply, Pi.smul_apply,
          RCLike.real_smul_eq_coe_mul, atom]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        push_cast
        ac_rfl
      refine ⟨q, a, z, ?_, ?_⟩
      · intro i j
        rw [hsum (i, j), ← hA_moment (i, j)]
        calc
          ‖(M : ℂ) * A (i, j) - (M : ℂ) * Q (i, j)‖ =
              M * ‖A (i, j) - Q (i, j)‖ := by
            rw [← mul_sub, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg hMnonneg]
          _ ≤ M * (tolerance / M) := by
            apply (mul_lt_mul_of_pos_left _ hMpos).le
            simpa only [norm_sub_rev] using hcoord (i, j)
          _ = tolerance := by field_simp [ne_of_gt hMpos]
      · calc
          ∑ r, ‖a r‖ ≤ ∑ r, M * w r := by
            apply Finset.sum_le_sum
            intro r _
            simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hMnonneg, abs_of_nonneg (hw_nonneg r)]
            calc
              M * w r * ‖phase (z r)‖ ≤ M * w r * 1 := by
                exact mul_le_mul_of_nonneg_left (hphase_norm (z r))
                  (mul_nonneg hMnonneg (hw_nonneg r))
              _ = M * w r := mul_one _
          _ = M := by rw [← Finset.mul_sum, hw_sum, mul_one]
          _ ≤ mass := hmass

/-- Uniformly accurate finite reciprocal Fourier sums can be corrected to an
exact finite interpolation with arbitrarily small additional coefficient
mass.

The correction uses the fixed linear mass bound from
`exists_finite_fourier_interpolation_with_mass_bound` on the finite set of
distinct frequency differences. -/
theorem hasFiniteReciprocalFourierInterpolation_of_approximate
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {mass ε : ℝ}
    (hgap : ∀ i j, 1 ≤ |α i - β j|) (hε : 0 < ε)
    (happrox : ∀ η : ℝ, 0 < η →
      HasApproximateFiniteReciprocalFourierInterpolation α β mass η) :
    HasFiniteReciprocalFourierInterpolation α β 1 (mass + ε) := by
  classical
  let d : Fin m × Fin n → ℝ := fun ij => α ij.1 - β ij.2
  let s : Finset ℝ := (Finset.univ ×ˢ Finset.univ).image d
  obtain ⟨K, hK, hcorrect⟩ :=
    exists_finite_fourier_interpolation_with_mass_bound s
  let c : ℝ := s.card
  let η : ℝ := ε / ((K + 1) * (c + 1))
  have hc : 0 ≤ c := by positivity
  have hden : 0 < (K + 1) * (c + 1) :=
    mul_pos (by linarith) (by linarith)
  have hη : 0 < η := div_pos hε hden
  rcases happrox η hη with ⟨q₀, a₀, t₀, happ, hmass₀⟩
  let base : ℝ → ℂ := fun x => ∑ r, a₀ r * Complex.exp
    ((((t₀ r * x) : ℝ) : ℂ) * Complex.I)
  let y : ℝ → ℂ := fun x => (1 : ℂ) / (x : ℂ) - base x
  have hy (x : ℝ) (hx : x ∈ s) : ‖y x‖ ≤ η := by
    rcases Finset.mem_image.mp hx with ⟨⟨i, j⟩, _, rfl⟩
    simpa only [y, base, d] using happ i j
  have hysum : ∑ x ∈ s, ‖y x‖ ≤ c * η := by
    calc
      ∑ x ∈ s, ‖y x‖ ≤ ∑ _x ∈ s, η := by
        exact Finset.sum_le_sum fun x hx => hy x hx
      _ = c * η := by simp [c]
  rcases hcorrect y with ⟨q₁, a₁, t₁, hexact₁, hmass₁⟩
  have hsmall : K * (∑ x ∈ s, ‖y x‖) < ε := by
    have hnum : K * c < (K + 1) * (c + 1) := by nlinarith
    have hfrac : K * c / ((K + 1) * (c + 1)) < 1 :=
      (div_lt_one hden).2 hnum
    calc
      K * (∑ x ∈ s, ‖y x‖) ≤ K * (c * η) := by
        exact mul_le_mul_of_nonneg_left hysum hK
      _ = ε * (K * c / ((K + 1) * (c + 1))) := by
        dsimp only [η]
        field_simp
      _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one _
  refine ⟨q₀ + q₁, Fin.append a₀ a₁, Fin.append t₀ t₁, ?_, ?_⟩
  · intro i j
    let x : ℝ := α i - β j
    have hx : x ∈ s := by
      exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
    have hx₀ : x ≠ 0 := by
      intro hxz
      have := hgap i j
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change 1 ≤ |x| at this
      rw [hxz, abs_zero] at this
      norm_num at this
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx₀
    have hsum :
        (∑ r : Fin (q₀ + q₁),
          Fin.append a₀ a₁ r * Complex.exp
            (((Fin.append t₀ t₁ r * x : ℝ) : ℂ) * Complex.I)) =
          base x + ∑ r : Fin q₁, a₁ r * Complex.exp
            ((((t₁ r * x) : ℝ) : ℂ) * Complex.I) := by
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, base]
    have hrecip :
        (1 : ℂ) / (x : ℂ) = base x +
          ∑ r : Fin q₁, a₁ r * Complex.exp
            ((((t₁ r * x) : ℝ) : ℂ) * Complex.I) := by
      rw [← hexact₁ x hx]
      simp only [y]
      ring
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (1 : ℂ) = (x : ℂ) * ∑ r : Fin (q₀ + q₁),
      Fin.append a₀ a₁ r * Complex.exp
        (((Fin.append t₀ t₁ r * x : ℝ) : ℂ) * Complex.I)
    rw [hsum, ← hrecip]
    field_simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    calc
      ∑ r, ‖a₀ r‖ + ∑ r, ‖a₁ r‖ ≤
          mass + K * (∑ x ∈ s, ‖y x‖) := add_le_add hmass₀ hmass₁
      _ ≤ mass + ε := by
        simpa only [add_comm] using (add_lt_add_left hsmall mass).le

/-- Approximate reciprocal Fourier sums with masses tending to `π / 2`
produce the exact normalized finite interpolation with mass `π / 2 + ε`.
All exact finite compression is discharged here; the remaining analytic input
only has to provide uniformly accurate finite sums. -/
theorem hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_approximate
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hgap : ∀ i j, 1 ≤ |α i - β j|) {ε : ℝ} (hε : 0 < ε)
    (happrox : ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η →
      HasApproximateFiniteReciprocalFourierInterpolation
        α β (Real.pi / 2 + μ) η) :
    HasFiniteReciprocalFourierInterpolation α β 1 (Real.pi / 2 + ε) := by
  have hhalf : 0 < ε / 2 := by positivity
  have h := hasFiniteReciprocalFourierInterpolation_of_approximate
    α β hgap hhalf (happrox (ε / 2) hhalf)
  convert h using 1
  ring

/-- A sharp integrable reciprocal kernel gives exact finite interpolation on
every separated finite frequency array, with arbitrarily small excess mass.

The kernel is first compressed to an approximate finite Fourier sum by
`hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel`.
The finite interpolation correction then removes every moment error exactly;
its coefficient cost tends to zero with the quadrature tolerance. -/
theorem hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hgap : ∀ i j, 1 ≤ |α i - β j|) {eps : ℝ} (heps : 0 < eps)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2)) :
    HasFiniteReciprocalFourierInterpolation
      α β 1 (Real.pi / 2 + eps) := by
  exact hasFiniteReciprocalFourierInterpolation_of_approximate
    α β hgap heps fun tolerance htolerance =>
      hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel
        α β hgap htolerance hkernel

/-- Rescale a unit-gap finite Fourier interpolation to an arbitrary positive
gap.  The coefficient mass is unchanged and the Fourier frequencies are
divided by the gap. -/
theorem hasFiniteReciprocalFourierInterpolation_of_normalized
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {δ mass : ℝ} (hδ : 0 < δ)
    (h : HasFiniteReciprocalFourierInterpolation
      (fun i => α i / δ) (fun j => β j / δ) 1 mass) :
    HasFiniteReciprocalFourierInterpolation α β δ mass := by
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  refine ⟨q, a, fun r => t r / δ, ?_, hmass⟩
  intro i j
  have harg (r : Fin q) :
      (t r / δ) * (α i - β j) =
        t r * (α i / δ - β j / δ) := by
    field_simp [ne_of_gt hδ]
  simp_rw [harg]
  let S : ℂ := ∑ r, a r * Complex.exp
    ((((t r * (α i / δ - β j / δ)) : ℝ) : ℂ) * Complex.I)
  have hs : (1 : ℂ) =
      (((α i / δ - β j / δ : ℝ) : ℂ)) * S := by
    simpa [S] using hscalar i j
  calc
    (δ : ℂ) = (δ : ℂ) * 1 := by ring
    _ = (δ : ℂ) *
        ((((α i / δ - β j / δ : ℝ) : ℂ)) * S) := by rw [hs]
    _ = (((α i - β j : ℝ) : ℂ)) * S := by
      push_cast
      field_simp [ne_of_gt hδ]

/-- A simultaneous finite orbit interpolation of the reciprocal coordinate
multiplier.

The same coefficients and unitary factors must work for every coordinate
matrix unit.  The displayed identity is written without division: multiplying
the orbit average by the coordinate difference gives `δ` times the matrix
unit.  Positive separation guarantees that this is equivalent to reciprocal
interpolation, while the division-free form is substantially more robust in
the downstream finite algebra. -/
@[expose]
def HasReciprocalOrbitInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    (δ mass : ℝ) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → 𝕜,
    ∃ U : Fin n → F ≃ₗᵢ[𝕜] F,
      ∃ V : Fin n → E ≃ₗᵢ[𝕜] E,
        (∀ i j,
          ((δ : 𝕜)) • basisMatrixUnit eF eE i j =
            ((((α i - β j : ℝ) : 𝕜)) •
              ((∑ r, a r • unitaryOrbitAction (U r) (V r))
                (basisMatrixUnit eF eE i j)))) ∧
        ∑ r, ‖a r‖ ≤ mass

/-- A finite scalar reciprocal Fourier interpolation produces the exact
simultaneous complex unitary-orbit interpolation.  All matrix-unit transport
is supplied by `complexUnitaryOrbitAction_basisMatrixUnit_exp_sub`; the input
certificate contains the whole remaining analytic content. -/
theorem hasReciprocalOrbitInterpolation_of_finiteFourierInterpolation
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    {δ mass : ℝ}
    (h : HasFiniteReciprocalFourierInterpolation α β δ mass) :
    HasReciprocalOrbitInterpolation eF eE α β δ mass := by
  classical
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  let U : Fin q → FC ≃ₗᵢ[ℂ] FC := fun r =>
    basisDiagonalUnitary eF fun i => complexFourierPhase (t r * α i)
  let V : Fin q → EC ≃ₗᵢ[ℂ] EC := fun r =>
    basisDiagonalUnitary eE fun j => complexFourierPhase (-(t r * β j))
  refine ⟨q, a, U, V, ?_, hmass⟩
  intro i j
  have horbit :
      ((∑ r, a r • unitaryOrbitAction (U r) (V r))
          (basisMatrixUnit eF eE i j)) =
        (∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)) •
            basisMatrixUnit eF eE i j := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, U, V,
      complexUnitaryOrbitAction_basisMatrixUnit_exp_sub, smul_smul]
    rw [Finset.sum_smul]
  rw [horbit, smul_smul]
  exact congrArg (fun z : ℂ => z • basisMatrixUnit eF eE i j)
    (hscalar i j)

/-- A finite complex Fourier interpolation descends exactly to doubled real
coordinate spaces.  The complex coefficient norm is the real orbit weight and
its argument is absorbed into the left coordinate rotation. -/
theorem hasDoubledRealReciprocalOrbitInterpolation_of_finiteFourierInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {delta mass : ℝ}
    (h : HasFiniteReciprocalFourierInterpolation alpha beta delta mass) :
    HasDoubledRealReciprocalOrbitInterpolation
      eF eE alpha beta delta mass := by
  classical
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  let w : Fin q → ℝ := fun r => ‖a r‖
  let U : Fin q → WithLp 2 (FR × FR) ≃ₗᵢ[ℝ] WithLp 2 (FR × FR) := fun r =>
    basisDoubledRealRotation eF fun i => Complex.arg (a r) + t r * alpha i
  let V : Fin q → WithLp 2 (ER × ER) ≃ₗᵢ[ℝ] WithLp 2 (ER × ER) := fun r =>
    basisDoubledRealRotation eE fun j => -(t r * beta j)
  refine ⟨q, w, U, V, ?_, ?_⟩
  · intro i j
    let T : ER →ₗ[ℝ] FR := basisMatrixUnit eF eE i j
    let d : ℝ := alpha i - beta j
    have horbit :
        ((∑ r, w r • unitaryOrbitAction (U r) (V r))
            (UnitarilyInvariantSeminorm.orthogonalBlockSum T T)) =
          doubledComplexScalarAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
      calc
        ((∑ r, w r • unitaryOrbitAction (U r) (V r))
            (UnitarilyInvariantSeminorm.orthogonalBlockSum T T)) =
            ∑ r, ‖a r‖ •
              doubledPhaseAction (Complex.arg (a r) + t r * d) T := by
                simp only [LinearMap.sum_apply, LinearMap.smul_apply, w]
                apply Finset.sum_congr rfl
                intro r _
                rw [unitaryOrbitAction_apply]
                -- names the application so the norm bound applies to it directly.
                change ‖a r‖ •
                    ((basisDoubledRealRotation eF
                        (fun i => Complex.arg (a r) + t r * alpha i)).toLinearMap ∘ₗ
                      UnitarilyInvariantSeminorm.orthogonalBlockSum T T ∘ₗ
                        (basisDoubledRealRotation eE
                          (fun j => -(t r * beta j))).toLinearMap) = _
                rw [show T = basisMatrixUnit eF eE i j by rfl,
                  basisDoubledRealRotation_comp_basisMatrixUnit]
                congr 2
                dsimp only [d]
                ring
        _ = doubledComplexScalarAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
              exact sum_norm_smul_doubledPhaseAction_arg_add
                a (fun r => t r * d) T
    rw [← doubledComplexScalarAction_ofReal delta T, horbit,
      doubledComplexScalarAction_real_smul]
    congr 1
    exact hscalar i j
  · simpa only [w, abs_of_nonneg (norm_nonneg _)] using hmass

end TauCeti
