/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Evaluation of restricted power series at power-bounded tuples

The universal property of `E⟨T_1,…,T_m⟩` ([WP] §2, lines 176–181: "The Tate variables
are power-bounded, so the same presentation records the rational inequalities
`|f_i| ≤ |g|`"; Huber's universal property, [Huber94] (1.2)/Prop 1.3): a continuous
ring homomorphism `φ : E → B` into a complete Hausdorff nonarchimedean topological
ring together with a power-bounded tuple `b : Fin m → B` extends uniquely to
`E⟨T⟩ → B`, `T_i ↦ b_i`, by `F ↦ ∑_t φ(c_t)·b^t` — the series converges because the
coefficients are null and the monomials `b^t` range in a bounded set.

This is the `rev`-direction engine for every identification of a `presheafValue` with
a concrete model in this campaign (the `chartRev`/`chartEval` pattern of
`FJP/Over/Chart.lean:1124`, done once generically).  Search first: pieces may exist in
`WedhornCechAcyclicity.lean` (the 828b quotient-presentation machinery) and in
mathlib's `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean`.
-/

@[expose] public section

namespace WeightedParity

open FiniteJet.GraphKoszul TopologicalRing Filter Topology

/-- Cofinitely-null families are summable in a complete Hausdorff nonarchimedean
group (search first: `Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`). -/
theorem summable_of_tendsto_cofinite_nonarch {ι : Type*} {B : Type*} [AddCommGroup B]
    [UniformSpace B] [IsUniformAddGroup B] [CompleteSpace B] [T2Space B]
    [NonarchimedeanAddGroup B] (f : ι → B) (hf : Tendsto f cofinite (𝓝 0)) :
    Summable f :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f).mpr hf

section Eval

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}
variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [NonarchimedeanRing B]

/-- The monomial set of a power-bounded tuple is bounded (finite products of
power-bounded elements live in the bounded subring they generate). -/
theorem isBounded_range_monomials (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) :
    IsBounded (Set.range fun t : Fin m →₀ ℕ => ∏ i, b i ^ t i) := by
  classical
  refine IsBounded.subset (isBounded_closure_finset_of_isPowerBounded
    (T := Finset.image b Finset.univ) ?_) ?_
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hb i
  · rintro _ ⟨t, rfl⟩
    refine Subring.prod_mem _ fun i _ => Subring.pow_mem _ ?_ _
    refine Subring.subset_closure ?_
    rw [Finset.coe_image]
    exact Set.mem_image_of_mem b (Finset.mem_coe.mpr (Finset.mem_univ i))

/-- The evaluation family of a restricted series at a power-bounded tuple is
summable: the coefficients are null and the monomials range in a bounded set. -/
theorem summable_evalFamily (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (F : P E m) :
    Summable fun t : Fin m →₀ ℕ =>
      φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i := by
  classical
  apply summable_of_tendsto_cofinite_nonarch
  have hnorm : Tendsto (fun t : Fin m →₀ ℕ => ‖MvPowerSeries.coeff t F.1‖)
      cofinite (𝓝 0) :=
    F.2.congr fun t => by rw [FiniteJet.finsupp_prod_one, mul_one]
  have hc : Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t F.1)
      cofinite (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hφc : Tendsto (fun t : Fin m →₀ ℕ => φ (MvPowerSeries.coeff t F.1))
      cofinite (𝓝 0) := by
    have h1 := (hφ.tendsto 0).comp hc
    rwa [map_zero] at h1
  refine Filter.tendsto_def.mpr fun U hU => ?_
  obtain ⟨V, hV, hMV⟩ := isBounded_range_monomials b hb U hU
  refine Filter.mem_of_superset (Filter.tendsto_def.mp hφc V hV) fun t ht => ?_
  rw [Set.mem_preimage] at ht ⊢
  rw [mul_comm]
  exact hMV (Set.mul_mem_mul ⟨t, rfl⟩ ht)

/-- The raw evaluation `F ↦ ∑_t φ(c_t)·b^t`. -/
noncomputable def evalFun (φ : E →+* B) (b : Fin m → B) (F : P E m) : B :=
  ∑' t : Fin m →₀ ℕ, φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i

theorem evalFun_zero (φ : E →+* B) (b : Fin m → B) :
    evalFun φ b (0 : P E m) = 0 := by
  unfold evalFun
  rw [show (∑' t : Fin m →₀ ℕ, φ (MvPowerSeries.coeff t (0 : P E m).1) *
      ∏ i, b i ^ t i) = ∑' _ : Fin m →₀ ℕ, (0 : B) from
    tsum_congr fun t => by
      rw [show ((0 : P E m)).1 = (0 : MvPowerSeries (Fin m) E) from rfl, map_zero,
        map_zero, zero_mul]]
  exact tsum_zero

theorem evalFun_one (φ : E →+* B) (b : Fin m → B) :
    evalFun φ b (1 : P E m) = 1 := by
  classical
  unfold evalFun
  rw [tsum_eq_single (0 : Fin m →₀ ℕ) ?_]
  · rw [show ((1 : P E m)).1 = (1 : MvPowerSeries (Fin m) E) from rfl,
      MvPowerSeries.coeff_zero_one, map_one, one_mul]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero]
  · intro t ht
    rw [show ((1 : P E m)).1 = (1 : MvPowerSeries (Fin m) E) from rfl,
      MvPowerSeries.coeff_one, if_neg ht, map_zero, zero_mul]

theorem evalFun_add (φ : E →+* B) (hφ : Continuous φ) (b : Fin m → B)
    (hb : ∀ i, IsPowerBounded (b i)) (F G : P E m) :
    evalFun φ b (F + G) = evalFun φ b F + evalFun φ b G := by
  unfold evalFun
  rw [tsum_congr (f := fun t : Fin m →₀ ℕ =>
      φ (MvPowerSeries.coeff t (F + G).1) * ∏ i, b i ^ t i)
    (g := fun t : Fin m →₀ ℕ =>
      φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i +
        φ (MvPowerSeries.coeff t G.1) * ∏ i, b i ^ t i)
    (fun t => by
      rw [show ((F + G) : P E m).1 = F.1 + G.1 from rfl, map_add, map_add,
        add_mul])]
  exact Summable.tsum_add (summable_evalFamily φ hφ b hb F)
    (summable_evalFamily φ hφ b hb G)

/-- The sigma-antidiagonal parametrization of pairs of exponents. -/
noncomputable def sigmaAntidiagEquiv (m : ℕ) :
    (Σ t : Fin m →₀ ℕ, ↥(Finset.HasAntidiagonal.antidiagonal t)) ≃
      (Fin m →₀ ℕ) × (Fin m →₀ ℕ) where
  toFun x := x.2.1
  invFun p := ⟨p.1 + p.2, ⟨p, Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩⟩
  left_inv x := by
    obtain ⟨t, ⟨p, hp⟩⟩ := x
    have ht : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst ht
    rfl
  right_inv p := rfl

theorem evalFun_mul (φ : E →+* B) (hφ : Continuous φ) (b : Fin m → B)
    (hb : ∀ i, IsPowerBounded (b i)) (F G : P E m) :
    evalFun φ b (F * G) = evalFun φ b F * evalFun φ b G := by
  classical
  unfold evalFun
  rw [tsum_mul_tsum_of_nonarchimedean (summable_evalFamily φ hφ b hb F)
    (summable_evalFamily φ hφ b hb G)]
  set pairfn : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) → B := fun p =>
    (φ (MvPowerSeries.coeff p.1 F.1) * ∏ i, b i ^ p.1 i) *
      (φ (MvPowerSeries.coeff p.2 G.1) * ∏ i, b i ^ p.2 i) with hpairfn
  have hsum : Summable pairfn :=
    (summable_evalFamily φ hφ b hb F).mul_of_nonarchimedean
      (summable_evalFamily φ hφ b hb G)
  have hterm : ∀ t : Fin m →₀ ℕ,
      φ (MvPowerSeries.coeff t (F * G).1) * ∏ i, b i ^ t i =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, pairfn p := by
    intro t
    rw [show ((F * G) : P E m).1 = F.1 * G.1 from rfl, MvPowerSeries.coeff_mul,
      map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpt : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hbt : (∏ i, b i ^ t i) = (∏ i, b i ^ p.1 i) * ∏ i, b i ^ p.2 i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← Finsupp.add_apply, hpt]
    rw [map_mul, hbt, hpairfn]
    ring
  rw [tsum_congr hterm]
  have hkey : (∑' p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ), pairfn p) =
      ∑' t : Fin m →₀ ℕ, ∑' c : ↥(Finset.HasAntidiagonal.antidiagonal t),
        pairfn c.1 := by
    rw [← Equiv.tsum_eq (sigmaAntidiagEquiv m) pairfn]
    exact Summable.tsum_sigma
      ((Equiv.summable_iff (sigmaAntidiagEquiv m)).mpr hsum)
  rw [hkey]
  exact tsum_congr fun t => (Finset.tsum_subtype _ _).symm

/-- **Evaluation of restricted power series at a power-bounded tuple**: the universal
property of `E⟨T_1,…,T_m⟩` (Huber's (1.2); the generic form of the `chartEval`
construction, `FJP/Over/Chart.lean`).  Requires the coefficient images to be null and
the target monoid `{b^t}` bounded — both from `hb` and continuity of `φ`.
(2026-07-29: the skeleton's extra bounded-image hypothesis on `φ` was dropped —
Huber (1.2) needs only continuity and power-boundedness, and the construction
never used it.) -/
noncomputable def restrictedEval (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) :
    P E m →+* B where
  toFun := evalFun φ b
  map_one' := evalFun_one φ b
  map_mul' := evalFun_mul φ hφ b hb
  map_zero' := evalFun_zero φ b
  map_add' := evalFun_add φ hφ b hb

theorem restrictedEval_apply (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (F : P E m) :
    restrictedEval φ hφ b hb F =
      ∑' t : Fin m →₀ ℕ, φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i := rfl

@[simp] theorem restrictedEval_C (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (x : E) :
    restrictedEval φ hφ b hb (polyToP (MvPolynomial.C x)) = φ x := by
  classical
  rw [restrictedEval_apply, tsum_eq_single (0 : Fin m →₀ ℕ) ?_]
  · rw [coeff_polyToP, MvPolynomial.coeff_C, if_pos rfl,
      Finset.prod_eq_one fun i _ => by
        rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero], mul_one]
  · intro t ht
    rw [coeff_polyToP, MvPolynomial.coeff_C, if_neg fun h => ht h.symm, map_zero,
      zero_mul]

@[simp] theorem restrictedEval_X (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (i : Fin m) :
    restrictedEval φ hφ b hb (polyToP (MvPolynomial.X i)) = b i := by
  classical
  rw [restrictedEval_apply, tsum_eq_single (Finsupp.single i 1) ?_]
  · rw [coeff_polyToP, MvPolynomial.coeff_X', if_pos rfl, map_one, one_mul,
      Finset.prod_eq_single i
        (fun j _ hji => by
          rw [Finsupp.single_apply, if_neg fun h => hji h.symm, pow_zero])
        (fun h => absurd (Finset.mem_univ i) h),
      Finsupp.single_apply, if_pos rfl, pow_one]
  · intro t ht
    rw [coeff_polyToP, MvPolynomial.coeff_X', if_neg fun h => ht h.symm, map_zero,
      zero_mul]

theorem restrictedEval_continuous (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) :
    Continuous (restrictedEval φ hφ b hb) := by
  classical
  refine continuous_of_continuousAt_zero (restrictedEval φ hφ b hb).toAddMonoidHom ?_
  show Tendsto _ (𝓝 0) (𝓝 _)
  rw [show (restrictedEval φ hφ b hb).toAddMonoidHom (0 : P E m) = 0 from
    map_zero _]
  refine Filter.tendsto_def.mpr fun U hU => ?_
  obtain ⟨U₀, hU₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V₁, hV₁, hMV₁⟩ := isBounded_range_monomials b hb U₀
    (U₀.isOpen.mem_nhds U₀.zero_mem)
  have hpre : φ ⁻¹' V₁ ∈ 𝓝 (0 : E) := by
    have h1 := hφ.tendsto 0
    rw [map_zero] at h1
    exact h1 hV₁
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0) fun F hF => ?_
  rw [Set.mem_preimage]
  refine hU₀ ?_
  have hFnorm : ‖F‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hF
  have hterm : ∀ t : Fin m →₀ ℕ,
      φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i ∈ (U₀ : Set B) := by
    intro t
    have hc : φ (MvPowerSeries.coeff t F.1) ∈ V₁ := hball (by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (norm_coeff_le_gauss F t) hFnorm)
    have hin := hMV₁ (Set.mul_mem_mul ⟨t, rfl⟩ hc)
    rwa [mul_comm] at hin
  have hHasSum := (summable_evalFamily φ hφ b hb F).hasSum
  exact U₀.isClosed.mem_of_tendsto hHasSum
    (Filter.Eventually.of_forall fun s => sum_mem fun t _ => hterm t)

/-- Polynomials are dense in `E⟨T⟩` (truncate below any coefficient-norm level;
the general-`E` form of `FiniteJetFunctoriality.polyToP_denseRange`). -/
theorem denseRange_polyToP :
    DenseRange (polyToP : MvPolynomial (Fin m) E → P E m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le)
    (half_lt_self hε)
  rw [FiniteJet.finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : P E m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p
        (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : P E m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        E)).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
  by_cases hs : ε / 2 ≤ ‖MvPowerSeries.coeff s p.1‖
  · rw [Finset.sum_eq_single s
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun hns => absurd ((finite_setOf_le_norm_coeff p
        (half_pos hε)).mem_toFinset.mpr hs) hns),
      MvPolynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hs).le
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      subst h
      exact hs ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mp hb)

/-- Uniqueness of the evaluation extension on the closure of the polynomial subring
(the polynomials are dense in `E⟨T⟩`, [FJP] (4.4)). -/
theorem restrictedEval_unique (φ : E →+* B) (hφ : Continuous φ)
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i))
    (ψ : P E m →+* B) (hψ : Continuous ψ)
    (hψC : ∀ x : E, ψ (polyToP (MvPolynomial.C x)) = φ x)
    (hψX : ∀ i, ψ (polyToP (MvPolynomial.X i)) = b i) :
    ψ = restrictedEval φ hφ b hb := by
  have hpoly : ∀ Q : MvPolynomial (Fin m) E,
      ψ (polyToP Q) = restrictedEval φ hφ b hb (polyToP Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => rw [hψC, restrictedEval_C]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, hψX, restrictedEval_X]
  have hfun : ⇑ψ = ⇑(restrictedEval φ hφ b hb) :=
    denseRange_polyToP.equalizer hψ (restrictedEval_continuous φ hφ b hb)
      (funext hpoly)
  exact RingHom.ext fun F => congrFun hfun F

end Eval

end WeightedParity
