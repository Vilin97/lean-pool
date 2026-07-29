/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib

/-!
# `n`-dimensional Poisson summation for the Gaussian class  (SP1-AGP, leaf P.2)

Mathlib has one-dimensional Poisson summation (`Real.tsum_eq_tsum_fourier`) and the
multivariate **torus Fourier series** (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`),
but **no** `n`-dimensional / lattice Poisson summation formula. This file builds it for the
standard lattice `ℤ^ι ⊂ EuclideanSpace ℝ ι`, in the shape needed for the Hecke theta
transformation: `∑_{n∈ℤ^ι} g(n) = ∑_{m∈ℤ^ι} 𝓕g(m)`.

The engine mirrors the one-dimensional proof in mathlib's `PoissonSummation.lean`: the
genuinely new lemma is that the `m`-th coefficient of the torus-periodization of `g` is the
value of the Fourier transform `𝓕g` at the lattice point `m`
(`mFourierCoeff_torusPeriodizationFun`, the analogue of `Real.fourierCoeff_tsum_comp_add`).
Poisson then falls out of the multivariate torus Fourier series evaluated at `0`.

## Main results (this file)
* `DedekindResidue.tsum_eq_tsum_fourier_zpoint` — **`n`-dimensional Poisson summation over
  `ℤ^ι`**: `∑' n, g (zpoint n) = ∑' m, 𝓕 g (zpoint m)` for continuous `g` with locally
  summable lattice translates and summable Fourier values.
* `DedekindResidue.mFourierCoeff_torusPeriodizationFun` — the key coefficient identity.
* `DedekindResidue.integral_eq_tsum_integral_iocBox` — box tiling of `ℝ^ι` (+ `lintegral` twin).
* `DedekindResidue.summable_gaussian_zlattice` — the Gaussian `x ↦ exp(-a‖x‖²)` (`a > 0`) is
  summable over any `ℤ`-lattice in `EuclideanSpace ℝ ι` (dominated by a summable power via
  `ZLattice.summable_norm_rpow`). This drives the Gaussian instantiation downstream (AGΘ).
* `DedekindResidue.zpoint` — the standard embedding `ℤ^ι ↪ EuclideanSpace ℝ ι`;
  `torusPeriodizationFun` — the genuine descent of the periodization to the torus.

See `.mathlib-quality/substrate-api.md` §C/§E for the torus-Fourier footholds.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped Real FourierTransform

variable {ι : Type*} [Fintype ι]

/-- The standard embedding of the integer lattice `ℤ^ι` into `EuclideanSpace ℝ ι`. -/
noncomputable def zpoint (n : ι → ℤ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => (n i : ℝ))

omit [Fintype ι] in
/-- `zpoint` is additive: it is the restriction of a linear map to the integer lattice. -/
theorem zpoint_add (m n : ι → ℤ) : zpoint (m + n) = zpoint m + zpoint n := by
  ext i
  simp only [zpoint, PiLp.add_apply, Pi.add_apply, WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  push_cast; ring

/-- The torus monomial `mFourier (-m)` is the Fourier character `x ↦ exp(-2πi⟨m,x⟩)` of the
integer point `m`, written through the coordinatewise quotient `ℝ → AddCircle 1`. -/
theorem mFourier_neg_coe (m : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-m) (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (m i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring

/-- The integer points `ℤ^ι` are exactly the `ℤ`-span of the standard basis of `ι → ℝ`: the
equivalence sending an integer vector to itself, with inverse extracted by
`Submodule.span_induction` (every element of the span has integer coordinates). The forward
coercion is definitionally the integer vector (`intEquivSpanBasisFun_coe`). -/
noncomputable def intEquivSpanBasisFun :
    (ι → ℤ) ≃ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) :=
  Equiv.ofBijective
    (fun n => ⟨fun i => (n i : ℝ), by
      classical
      have : (fun i => (n i : ℝ)) = ∑ i, (n i : ℤ) • (Pi.basisFun ℝ ι i) := by
        ext j
        simp [Pi.basisFun_apply, Finset.sum_apply, Pi.single_apply, mul_ite]
      rw [this]
      exact Submodule.sum_mem _ (fun i _ =>
        Submodule.smul_mem _ (n i) (Submodule.subset_span ⟨i, rfl⟩))⟩)
    ⟨fun a b hab => by
      funext i
      have h2 : (a i : ℝ) = (b i : ℝ) := congrFun (congrArg Subtype.val hab) i
      exact_mod_cast h2,
     fun v => by
      classical
      have hcoords : ∀ i, ∃ n : ℤ, (v : ι → ℝ) i = n := by
        intro i
        refine Submodule.span_induction ?_ ?_ ?_ ?_ v.2
        · rintro x ⟨j, rfl⟩
          by_cases h : i = j
          · exact ⟨1, by simp [Pi.basisFun_apply, h]⟩
          · exact ⟨0, by simp [Pi.basisFun_apply, h]⟩
        · exact ⟨0, by simp⟩
        · rintro x y _ _ ⟨nx, hx⟩ ⟨ny, hy⟩
          exact ⟨nx + ny, by simp [hx, hy]⟩
        · rintro c x _ ⟨nx, hx⟩
          exact ⟨c * nx, by simp [Pi.smul_apply, hx, zsmul_eq_mul]⟩
      choose k hk using hcoords
      exact ⟨k, Subtype.ext (funext (fun i => (hk i).symm))⟩⟩

theorem intEquivSpanBasisFun_coe (n : ι → ℤ) :
    ((intEquivSpanBasisFun n : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) : ι → ℝ)
      = fun i => (n i : ℝ) := rfl

/-- A coordinate hyperplane `{x | x i = c}` in `ι → ℝ` is Lebesgue-null: it is a translate of
the kernel of the `i`-th coordinate projection, a proper subspace. -/
theorem volume_pi_hyperplane (i : ι) (c : ℝ) :
    (volume : Measure (ι → ℝ)) {x | x i = c} = 0 := by
  classical
  have h0 : (volume : Measure (ι → ℝ)) {x | x i = 0} = 0 := by
    have hker : {x : ι → ℝ | x i = 0}
        = (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) : Set (ι → ℝ)) := by
      ext x; simp [LinearMap.mem_ker]
    rw [hker]
    refine Measure.addHaar_submodule _ _ (fun htop => ?_)
    have h1 : (Pi.single i 1 : ι → ℝ)
        ∈ LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker] at h1
    simp [LinearMap.proj_apply] at h1
  have hshift : {x : ι → ℝ | x i = c}
      = (fun x : ι → ℝ => x + (Pi.single i (-c) : ι → ℝ)) ⁻¹' {x | x i = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.add_apply, Pi.single_eq_same]
    constructor <;> intro h <;> linarith
  rw [hshift, measure_preimage_add_right]
  exact h0

/-- The half-open boxes `(0,1]^ι` and `[0,1)^ι` agree up to Lebesgue-null sets: their
symmetric difference lies in the union of the coordinate hyperplanes `{x i = 0}`, `{x i = 1}`. -/
theorem iocBox_ae_icoBox :
    ({x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1} : Set (ι → ℝ))
      =ᵐ[(volume : Measure (ι → ℝ))] {x : ι → ℝ | ∀ i, x i ∈ Set.Ico (0:ℝ) 1} := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null (fun i => volume_pi_hyperplane i 1))
    obtain ⟨hs, ht⟩ := hx
    simp only [Set.mem_setOf_eq, not_forall] at ht
    obtain ⟨i, hi⟩ := ht
    have h1 := hs i
    rw [Set.mem_Ioc] at h1
    rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hi
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_setOf_eq]
    rcases hi with h | h
    · linarith
    · linarith
  · refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null (fun i => volume_pi_hyperplane i 0))
    obtain ⟨hs, ht⟩ := hx
    simp only [Set.mem_setOf_eq, not_forall] at ht
    obtain ⟨i, hi⟩ := ht
    have h1 := hs i
    rw [Set.mem_Ico] at h1
    rw [Set.mem_Ioc, not_and_or, not_le, not_lt] at hi
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_setOf_eq]
    rcases hi with h | h
    · linarith
    · linarith

/-- The `ZSpan` fundamental domain of the standard basis of `ι → ℝ` is the half-open box
`[0,1)^ι` (coordinates are the basis representation). -/
theorem fundamentalDomain_basisFun_eq :
    ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)
      = {x : ι → ℝ | ∀ i, x i ∈ Set.Ico (0:ℝ) 1} := by
  ext x
  simp [ZSpan.fundamentalDomain, Pi.basisFun_repr]

private theorem neg_intEquivSpanBasisFun_add (n : ι → ℤ) (x : ι → ℝ) :
    -((intEquivSpanBasisFun (-n) : ι → ℝ)) + x = x + fun i => (n i : ℝ) := by
  rw [intEquivSpanBasisFun_coe]
  funext i
  simp only [Pi.add_apply, Pi.neg_apply]
  push_cast
  ring

/-- **Box tiling of `ℝ^ι`.** For an integrable `f`, the integral over `ι → ℝ` is the sum over
integer translates of the integral over the half-open box `(0,1]^ι` — the fundamental-domain
decomposition for the standard integer lattice, in the `Ioc` normalisation used by the torus
Fourier coefficients. -/
theorem integral_eq_tsum_integral_iocBox (f : (ι → ℝ) → ℂ) (hf : Integrable f) :
    ∫ x, f x = ∑' n : ι → ℤ, ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
      f (x + fun i => (n i : ℝ)) := by
  classical
  have : VAddInvariantMeasure
      (↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))) (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup (ι → ℝ) volume)
  have h1 := (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι)
    (volume : Measure (ι → ℝ))).integral_eq_tsum' f hf
  rw [h1, ← ((Equiv.neg (ι → ℤ)).trans intEquivSpanBasisFun).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [fundamentalDomain_basisFun_eq, setIntegral_congr_set iocBox_ae_icoBox]
  refine setIntegral_congr_fun ?_ (fun x _ => ?_)
  · exact measurableSet_setOf.mpr (by measurability)
  · congr 1
    exact neg_intEquivSpanBasisFun_add n x

/-- **Box tiling of `ℝ^ι`, `lintegral` form.** No integrability needed: the lower integral over
`ι → ℝ` is the sum over integer translates of the lower integral over the box `(0,1]^ι`. -/
theorem lintegral_eq_tsum_lintegral_iocBox (f : (ι → ℝ) → ENNReal) :
    ∫⁻ x, f x = ∑' n : ι → ℤ, ∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
      f (x + fun i => (n i : ℝ)) := by
  classical
  have : VAddInvariantMeasure
      (↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))) (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup (ι → ℝ) volume)
  have h1 := (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι)
    (volume : Measure (ι → ℝ))).lintegral_eq_tsum' f
  rw [h1, ← ((Equiv.neg (ι → ℤ)).trans intEquivSpanBasisFun).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [fundamentalDomain_basisFun_eq, setLIntegral_congr iocBox_ae_icoBox]
  refine lintegral_congr (fun x => ?_)
  congr 1
  exact neg_intEquivSpanBasisFun_add n x

/-- The torus monomials have pointwise norm `1` (each factor lies on the circle). -/
theorem norm_mFourier_apply (n : ι → ℤ) (q : UnitAddTorus ι) :
    ‖UnitAddTorus.mFourier n q‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod]
  refine Finset.prod_eq_one (fun i _ => ?_)
  simp [fourier_apply]

/-- The half-open box `(0,1]^ι` has volume `1`. -/
theorem volume_iocBox :
    (volume : Measure (ι → ℝ)) {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1} = 1 := by
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1}
      = Set.pi Set.univ (fun _ => Set.Ioc (0:ℝ) 1) := by
    ext x; simp [Set.mem_pi]
  rw [hset, volume_pi_pi]
  simp [Real.volume_Ioc]

/-- The closed unit box in `EuclideanSpace ℝ ι`, as a compact set: the reference compact for
all sup-norm estimates on the fundamental box. -/
noncomputable def unitBoxCompacts : Compacts (EuclideanSpace ℝ ι) :=
  ⟨WithLp.toLp 2 '' {y : ι → ℝ | ∀ i, y i ∈ Set.Icc (0:ℝ) 1}, by
    have hbox : IsCompact {y : ι → ℝ | ∀ i, y i ∈ Set.Icc (0:ℝ) 1} := by
      have : {y : ι → ℝ | ∀ i, y i ∈ Set.Icc (0:ℝ) 1}
          = Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) := by
        ext y; simp [Pi.le_def, forall_and]
      rw [this]
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
    exact hbox.image (PiLp.continuous_toLp 2 _)⟩

omit [Fintype ι] in
/-- `toLp` sends an integer shift in `ι → ℝ` to a `zpoint` shift in `EuclideanSpace ℝ ι`. -/
theorem toLp_add_intCast (x : ι → ℝ) (n : ι → ℤ) :
    WithLp.toLp 2 (x + fun i => (n i : ℝ)) = WithLp.toLp 2 x + zpoint n := by
  ext i
  simp only [zpoint, PiLp.add_apply, Pi.add_apply, WithLp.equiv_symm_apply]

/-- **Central sup-norm estimate.** On the closed unit box, the `n`-translate of `g` is bounded
by the sup-norm of its restriction to `unitBoxCompacts` — the quantity `h_norm` sums. -/
theorem norm_apply_le_restrict_unitBox (g : C(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) :
    ‖g (WithLp.toLp 2 x + zpoint n)‖
      ≤ ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
          (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ := by
  have hmem : WithLp.toLp 2 x ∈ (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι)) :=
    ⟨x, hx, rfl⟩
  exact ContinuousMap.norm_coe_le_norm
    ((g.comp (ContinuousMap.addRight (zpoint n))).restrict
      (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))) ⟨_, hmem⟩

/-- **Integrability of the twisted function.** Under local summability of the lattice
translates, `y ↦ mFourier (-m) (π y) • g (toLp y)` is integrable on `ι → ℝ`: its `lintegral`
tiles into box pieces, each bounded by the corresponding translate's sup-norm on the closed
unit box, and those sup-norms are summable by `h_norm`. -/
theorem integrable_mFourier_smul_comp_toLp (g : C(EuclideanSpace ℝ ι, ℂ)) (m : ι → ℤ)
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
      Summable fun n : ι → ℤ => ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖) :
    Integrable (fun y : ι → ℝ =>
      UnitAddTorus.mFourier (-m) (fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))
        • g (WithLp.toLp 2 y)) := by
  have hchar : Continuous (fun y : ι → ℝ =>
      UnitAddTorus.mFourier (-m) (fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))) :=
    (map_continuous (UnitAddTorus.mFourier (-m))).comp
      (continuous_pi (fun i => continuous_quotient_mk'.comp (continuous_apply i)))
  have hcont : Continuous (fun y : ι → ℝ =>
      UnitAddTorus.mFourier (-m) (fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))
        • g (WithLp.toLp 2 y)) :=
    hchar.smul ((map_continuous g).comp (PiLp.continuous_toLp 2 _))
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_eq_tsum_lintegral_iocBox]
  have hbound : ∀ n : ι → ℤ,
      (∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖UnitAddTorus.mFourier (-m)
            (fun i => (((x + fun i => (n i : ℝ)) i : ℝ) : AddCircle (1 : ℝ)))
          • g (WithLp.toLp 2 (x + fun i => (n i : ℝ)))‖ₑ)
      ≤ ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
          (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ := by
    intro n
    have hle : ∀ x ∈ {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖UnitAddTorus.mFourier (-m)
            (fun i => (((x + fun i => (n i : ℝ)) i : ℝ) : AddCircle (1 : ℝ)))
          • g (WithLp.toLp 2 (x + fun i => (n i : ℝ)))‖ₑ
        ≤ ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
            (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ := by
      intro x hx
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, norm_mFourier_apply, one_mul, toLp_add_intCast]
      exact norm_apply_le_restrict_unitBox g n (fun i => ⟨(hx i).1.le, (hx i).2⟩)
    calc ∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖UnitAddTorus.mFourier (-m)
            (fun i => (((x + fun i => (n i : ℝ)) i : ℝ) : AddCircle (1 : ℝ)))
          • g (WithLp.toLp 2 (x + fun i => (n i : ℝ)))‖ₑ
        ≤ ∫⁻ _x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
          ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
            (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ :=
        setLIntegral_mono measurable_const hle
      _ = _ := by rw [setLIntegral_const, volume_iocBox, mul_one]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (h_norm _)]
  exact ENNReal.ofReal_lt_top

/-- **`𝓕` bridge.** The Fourier transform of `g` at the lattice point `m`, an integral over the
inner-product space `EuclideanSpace ℝ ι`, rewrites as an integral over `ι → ℝ` of the torus
character `mFourier (-m)` against `g` — via the measure-preserving `WithLp` identification and
`mFourier_neg_coe`. This is the analytic content connecting `𝓕` to the torus Fourier coefficient. -/
theorem fourierIntegral_zpoint_eq (g : EuclideanSpace ℝ ι → ℂ) (m : ι → ℤ) :
    𝓕 g (zpoint m) = ∫ x : ι → ℝ,
      UnitAddTorus.mFourier (-m) (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))
        • g ((WithLp.equiv 2 (ι → ℝ)).symm x) := by
  rw [Real.fourier_eq', ← (PiLp.volume_preserving_toLp (ι := ι)).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [mFourier_neg_coe]
  refine congr_arg₂ (· • ·) ?_ rfl
  have hinner : (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (zpoint m)) = ∑ i, x i * (m i : ℝ) := by
    simp only [zpoint, PiLp.inner_apply, WithLp.equiv_symm_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hs : (∑ i, (x i : ℂ) * (m i : ℂ)) = ∑ i, (m i : ℂ) * (x i : ℂ) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hinner]; push_cast; rw [hs]; congr 1; ring

/-- The **torus periodization** of `g`: the `ℤ^ι`-periodic function `x ↦ ∑_{n} g(x + n)`, the
object whose `m`-th Fourier coefficient is `𝓕g(m)`. -/
noncomputable def periodization (g : EuclideanSpace ℝ ι → ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∑' n : ι → ℤ, g (x + zpoint n)

omit [Fintype ι] in
/-- The periodization is `ℤ^ι`-periodic: shifting by a lattice point reindexes the sum. -/
theorem periodization_add_zpoint (g : EuclideanSpace ℝ ι → ℂ) (x : EuclideanSpace ℝ ι)
    (k : ι → ℤ) : periodization g (x + zpoint k) = periodization g x := by
  unfold periodization
  rw [← (Equiv.addLeft k).tsum_eq (fun n => g (x + zpoint n))]
  refine tsum_congr (fun n => ?_)
  rw [Equiv.coe_addLeft, zpoint_add, add_assoc]

/-- **Gaussian summability over a lattice.** For `a > 0`, the Gaussian `x ↦ exp(-a‖x‖²)` is
summable over any `ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι`. Proof: it is eventually dominated (as
`‖x‖ → ∞`, which happens cofinitely on the lattice since sub-level sets are finite) by
`‖x‖^{-d-1}`, which is summable by `ZLattice.summable_norm_rpow`. -/
theorem summable_gaussian_zlattice (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    Summable (fun z : L => Real.exp (-a * ‖(z : EuclideanSpace ℝ ι)‖ ^ 2)) := by
  classical
  have hfin : Module.finrank ℤ (↥L) = Fintype.card ι := by
    rw [ZLattice.rank ℝ L, finrank_euclideanSpace]
  have hrlt : (-(Fintype.card ι : ℝ) - 1) < -(Module.finrank ℤ (↥L) : ℝ) := by
    rw [hfin]; linarith
  have hpow := ZLattice.summable_norm_rpow L (-(Fintype.card ι : ℝ) - 1) hrlt
  -- Gaussian is `o(t^{-d-1})` at infinity, so eventually `≤` it.
  have hbound : ∀ᶠ t : ℝ in atTop,
      Real.exp (-a * t ^ 2) ≤ t ^ (-(Fintype.card ι : ℝ) - 1) := by
    have h := rexp_neg_quadratic_isLittleO_rpow_atTop (a := -a) (by linarith) 0
      (-(Fintype.card ι : ℝ) - 1)
    simp only [neg_mul, zero_mul, add_zero] at h
    filter_upwards [h.eventuallyLE, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    calc Real.exp (-a * t ^ 2) = ‖Real.exp (-(a * t ^ 2))‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring_nf
      _ ≤ ‖t ^ (-(Fintype.card ι : ℝ) - 1)‖ := ht
      _ = t ^ (-(Fintype.card ι : ℝ) - 1) := by
            rw [Real.norm_rpow_of_nonneg htpos.le, Real.norm_eq_abs, abs_of_pos htpos]
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound
  -- Sub-level set `{z : L | ‖z‖ ≤ R}` is finite (lattice ∩ ball, proper space).
  have hcl : IsClosed (L : Set (EuclideanSpace ℝ ι)) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hlevel : {z : L | ‖(z : EuclideanSpace ℝ ι)‖ ≤ R}.Finite := by
    have hfb : (Metric.closedBall 0 R ∩ (L : Set (EuclideanSpace ℝ ι))).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall hcl
    refine Set.Finite.of_finite_image (hfb.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by simpa using hz, z.2⟩
  refine Summable.of_norm_bounded_eventually hpow ?_
  rw [Filter.eventually_cofinite]
  refine hlevel.subset (fun z hz => ?_)
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  rw [not_le] at hlt
  exact hz (by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hR _ hlt.le)

/-- Evaluation of the `C(·,·)`-valued periodization: under local summability of the lattice
translates, the tsum of translates in `C(EuclideanSpace ℝ ι, ℂ)` evaluates pointwise to
`periodization g`. -/
theorem coe_tsum_comp_addRight_zpoint (g : C(EuclideanSpace ℝ ι, ℂ))
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
      Summable fun n : ι → ℤ => ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖)
    (x : EuclideanSpace ℝ ι) :
    (∑' n : ι → ℤ, g.comp (ContinuousMap.addRight (zpoint n))) x = periodization (⇑g) x := by
  rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm h_norm)]
  exact tsum_congr (fun n => rfl)

omit [Fintype ι] in
/-- **Descent well-definedness**: the periodization takes equal values at points of `ι → ℝ`
with the same image on the torus (they differ by an integer vector, and the periodization is
`ℤ^ι`-periodic). -/
theorem periodization_toLp_congr (g : EuclideanSpace ℝ ι → ℂ) {x y : ι → ℝ}
    (h : ∀ i, ((x i : ℝ) : AddCircle (1 : ℝ)) = (y i : ℝ)) :
    periodization g (WithLp.toLp 2 x) = periodization g (WithLp.toLp 2 y) := by
  have hi : ∀ i, ∃ n : ℤ, x i - y i = n := by
    intro i
    have h2 := h i
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨-n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    push_cast
    linarith
  choose k hk using hi
  have hxy : x = y + (fun i => (k i : ℝ)) := funext fun i => by
    have := hk i; simp only [Pi.add_apply]; linarith
  have hadd : WithLp.toLp 2 (y + fun i => (k i : ℝ)) = WithLp.toLp 2 y + zpoint k := by
    ext i
    simp only [zpoint, PiLp.add_apply, Pi.add_apply, WithLp.equiv_symm_apply]
  rw [hxy, hadd, periodization_add_zpoint]

/-- The **torus periodization** as a function on `UnitAddTorus ι`: the value of
`periodization g` at the canonical `Ioc (0,1]` representative. By
`torusPeriodizationFun_coe` this is the genuine descent of `periodization g` along the
quotient `(ι → ℝ) → UnitAddTorus ι` (independent of the choice of representative). -/
noncomputable def torusPeriodizationFun (g : EuclideanSpace ℝ ι → ℂ) (q : UnitAddTorus ι) : ℂ :=
  periodization g (WithLp.toLp 2 (fun i => ((AddCircle.equivIoc 1 0 (q i) : ℝ))))

omit [Fintype ι] in
/-- The torus periodization descends the periodization: precomposed with the quotient map it
is `periodization g ∘ toLp`. -/
theorem torusPeriodizationFun_coe (g : EuclideanSpace ℝ ι → ℂ) (x : ι → ℝ) :
    torusPeriodizationFun g (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))
      = periodization g (WithLp.toLp 2 x) :=
  periodization_toLp_congr g (fun _ => AddCircle.coe_equivIoc)

/-- Under local summability of the lattice translates, the torus periodization is continuous:
its composite with the (open quotient) projection `(ι → ℝ) → UnitAddTorus ι` is the continuous
`C(·,·)`-valued tsum of translates. -/
theorem continuous_torusPeriodizationFun (g : C(EuclideanSpace ℝ ι, ℂ))
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
      Summable fun n : ι → ℤ => ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖) :
    Continuous (torusPeriodizationFun ⇑g) := by
  have hq : IsOpenQuotientMap
      (fun (x : ι → ℝ) => ((fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) : UnitAddTorus ι)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  rw [hq.isQuotientMap.continuous_iff]
  have heq : (torusPeriodizationFun ⇑g)
      ∘ (fun (x : ι → ℝ) => ((fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) : UnitAddTorus ι))
      = ⇑(∑' n : ι → ℤ, g.comp (ContinuousMap.addRight (zpoint n))) ∘ (WithLp.toLp 2) := by
    funext x
    simp only [Function.comp_apply]
    rw [coe_tsum_comp_addRight_zpoint g h_norm, torusPeriodizationFun_coe]
  rw [heq]
  exact (map_continuous _).comp (PiLp.continuous_toLp 2 _)

omit [Fintype ι] in
/-- The coordinatewise quotient to the torus kills integer shifts. -/
theorem coe_add_intCast_eq (x : ι → ℝ) (n : ι → ℤ) :
    (fun i => (((x + fun i => (n i : ℝ)) i : ℝ) : AddCircle (1 : ℝ)))
      = (fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) := by
  funext i
  simp only [Pi.add_apply]
  rw [QuotientAddGroup.eq]
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-(n i), ?_⟩
  simp [zsmul_eq_mul]

/-- **The key coefficient identity** (n-dim analogue of `Real.fourierCoeff_tsum_comp_add`):
the `m`-th torus Fourier coefficient of the periodization of `g` is the Fourier transform of
`g` at the lattice point `m`. Proof: write the coefficient as a box integral, descend the
periodization, swap sum and integral (dominated by the translate sup-norms), absorb the
character into each translate by shift-invariance, reassemble the box tiling into `∫_{ℝ^ι}`,
and identify the result via the `𝓕` bridge. -/
theorem mFourierCoeff_torusPeriodizationFun (g : C(EuclideanSpace ℝ ι, ℂ)) (m : ι → ℤ)
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
      Summable fun n : ι → ℤ => ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖) :
    UnitAddTorus.mFourierCoeff (torusPeriodizationFun ⇑g) m = 𝓕 (⇑g) (zpoint m) := by
  classical
  have hmeas : MeasurableSet {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1} :=
    measurableSet_setOf.mpr (by measurability)
  have hchar : Continuous (fun x : ι → ℝ =>
      UnitAddTorus.mFourier (-m) (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))) :=
    (map_continuous (UnitAddTorus.mFourier (-m))).comp
      (continuous_pi (fun i => continuous_quotient_mk'.comp (continuous_apply i)))
  have haesm : ∀ n : ι → ℤ, AEStronglyMeasurable
      (fun x : ι → ℝ => (UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
        • g (WithLp.toLp 2 x + zpoint n))
      ((volume : Measure (ι → ℝ)).restrict {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1}) :=
    fun n => (Continuous.aestronglyMeasurable (hchar.smul
      (((map_continuous g).comp (continuous_add_const (zpoint n))).comp
        (PiLp.continuous_toLp 2 _)))).restrict
  have hlintbound : ∀ n : ι → ℤ,
      (∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖(UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • g (WithLp.toLp 2 x + zpoint n)‖ₑ)
      ≤ ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
          (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ := by
    intro n
    have hle : ∀ x ∈ {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖(UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • g (WithLp.toLp 2 x + zpoint n)‖ₑ
        ≤ ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
            (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ := by
      intro x hx
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, norm_mFourier_apply, one_mul]
      exact norm_apply_le_restrict_unitBox g n (fun i => ⟨(hx i).1.le, (hx i).2⟩)
    calc (∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
          ‖(UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
            • g (WithLp.toLp 2 x + zpoint n)‖ₑ)
        ≤ ∫⁻ _x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
            ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict
              (unitBoxCompacts (ι := ι) : Set (EuclideanSpace ℝ ι))‖ :=
          setLIntegral_mono measurable_const hle
      _ = _ := by rw [setLIntegral_const, volume_iocBox, mul_one]
  have hlint : (∑' n : ι → ℤ,
      ∫⁻ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        ‖(UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • g (WithLp.toLp 2 x + zpoint n)‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlintbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _)
      (h_norm (unitBoxCompacts (ι := ι)))]
    exact ENNReal.ofReal_lt_top.ne
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusPeriodizationFun ⇑g) m (fun _ => 0)]
  simp only [zero_add]
  rw [setIntegral_congr_fun hmeas (g := fun x : ι → ℝ =>
      ∑' n : ι → ℤ, (UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
        • g (WithLp.toLp 2 x + zpoint n))
    (fun x _ => by
      rw [torusPeriodizationFun_coe]
      show (UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • ∑' n : ι → ℤ, g (WithLp.toLp 2 x + zpoint n) = _
      rw [smul_eq_mul, ← tsum_mul_left]
      rfl)]
  rw [MeasureTheory.integral_tsum haesm hlint]
  have hterm : ∀ n : ι → ℤ,
      (∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
        (UnitAddTorus.mFourier (-m) fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • g (WithLp.toLp 2 x + zpoint n))
      = ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1},
          (fun y : ι → ℝ => (UnitAddTorus.mFourier (-m) fun i => ((y i : ℝ) : AddCircle (1:ℝ)))
            • g (WithLp.toLp 2 y)) (x + fun i => (n i : ℝ)) := by
    intro n
    refine setIntegral_congr_fun hmeas (fun x _ => ?_)
    show _ = (UnitAddTorus.mFourier (-m) fun i =>
        (((x + fun i => (n i : ℝ)) i : ℝ) : AddCircle (1:ℝ)))
      • g (WithLp.toLp 2 (x + fun i => (n i : ℝ)))
    rw [coe_add_intCast_eq, toLp_add_intCast]
  rw [tsum_congr hterm,
    ← integral_eq_tsum_integral_iocBox _ (integrable_mFourier_smul_comp_toLp g m h_norm)]
  rw [fourierIntegral_zpoint_eq]
  rfl

/-- **`n`-dimensional Poisson summation over `ℤ^ι`** (SP1-AGP P.2). For a continuous `g` on
`EuclideanSpace ℝ ι` whose lattice translates are locally summable and whose Fourier transform
is summable over `ℤ^ι`, `∑_{n} g(n) = ∑_{m} 𝓕g(m)`. Assembled from the multivariate torus
Fourier series and `mFourierCoeff_periodization`. -/
theorem tsum_eq_tsum_fourier_zpoint {g : C(EuclideanSpace ℝ ι, ℂ)}
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
        Summable fun n : ι → ℤ =>
          ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖)
    (h_sum : Summable fun m : ι → ℤ => 𝓕 (⇑g) (zpoint m)) :
    ∑' n : ι → ℤ, g (zpoint n) = ∑' m : ι → ℤ, 𝓕 (⇑g) (zpoint m) := by
  classical
  set G : C(UnitAddTorus ι, ℂ) :=
    ⟨torusPeriodizationFun ⇑g, continuous_torusPeriodizationFun g h_norm⟩ with hG
  have hcoeff : ∀ m : ι → ℤ, UnitAddTorus.mFourierCoeff (⇑G) m = 𝓕 (⇑g) (zpoint m) :=
    fun m => mFourierCoeff_torusPeriodizationFun g m h_norm
  have hsummable : Summable (UnitAddTorus.mFourierCoeff (⇑G)) :=
    h_sum.congr (fun m => (hcoeff m).symm)
  have hone : ∀ m : ι → ℤ, UnitAddTorus.mFourier m (0 : UnitAddTorus ι) = 1 := by
    intro m
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
    refine Finset.prod_eq_one (fun i _ => ?_)
    show fourier (m i) ((0 : UnitAddTorus ι) i) = 1
    rw [Pi.zero_apply, fourier_eval_zero]
  have hG0 : G (0 : UnitAddTorus ι) = ∑' n : ι → ℤ, g (zpoint n) := by
    have h0 : (0 : UnitAddTorus ι) = (fun i => (((0 : ι → ℝ) i : ℝ) : AddCircle (1:ℝ))) := by
      funext i
      simp
    show torusPeriodizationFun ⇑g (0 : UnitAddTorus ι) = _
    rw [h0, torusPeriodizationFun_coe]
    unfold periodization
    have htl : WithLp.toLp 2 (0 : ι → ℝ) = (0 : EuclideanSpace ℝ ι) := by
      ext i; simp
    rw [htl]
    exact tsum_congr (fun n => by rw [zero_add])
  have hhs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsummable
    (0 : UnitAddTorus ι)
  have heq : (fun m : ι → ℤ =>
      UnitAddTorus.mFourierCoeff (⇑G) m • UnitAddTorus.mFourier m (0 : UnitAddTorus ι))
      = fun m => 𝓕 (⇑g) (zpoint m) :=
    funext (fun m => by rw [hcoeff, hone, smul_eq_mul, mul_one])
  rw [heq, hG0] at hhs
  exact hhs.tsum_eq.symm

end

end DedekindResidue
