/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import LeanPool.SeveralComplexVariables.SeveralComplexVariables

/-!
# Several complex variables: principal statements (`Solution.lean`)

This file states the principal results of the `SeveralComplexVariables` library in terms of Mathlib
alone. It follows the project's catalogue of main theorems, `SCVMainTheorems.md`: the number in each
docstring is the item of that catalogue, and the sections A–K are its sections. The subject is
classical function theory on open subsets of finite-dimensional complex normed spaces `E`, in
particular of `ℂ^ι = ι → ℂ` for a finite index type `ι`, with values in a complex Banach space `F`.

## Conventions

* *Holomorphic* is `DifferentiableOn ℂ f U` and *analytic* is `AnalyticOnNhd ℂ f U`. On open subsets
  of `E` the two agree (item 3), and the statements use whichever the library proves directly.
* `ι → ℂ` carries the supremum norm, so that `Metric.ball` is a polydisc with equal radii; a
  polydisc with separate radii is `Set.pi univ fun i => Metric.ball (c i) (r i)`. Dimension zero and
  empty index types are included unless a hypothesis excludes them.
* Domains are not assumed connected or nonempty; such hypotheses are stated where they are needed.
* Hulls are defined through all real upper bounds rather than suprema. Subharmonic and
  plurisubharmonic functions are real valued, so the value `-∞` is not admitted.
* The definitions below restate those of the library and are kept few. Where a notion is used
  once, it is written out in the statement instead.

## Scope

Of the 65 items of the catalogue, all are represented except items 42 and 43 (factors of
distinguished polynomials, and the comparison of polynomials over the germ ring with germs), which
are algebraic steps towards items 44 and 45. An item with several assertions is represented by its
principal assertion. The sources are the texts of Boas, Fritzsche–Grauert, Hörmander,
Jakóbczak–Jarnicki, Korevaar–Wiegerinck, Range, Scheidemann, Shabat and Suwa listed in
`formalization.yaml`; none of the results is new. The proofs use only the axioms `propext`,
`Quot.sound` and `Classical.choice`.

## Related formalizations

The development builds on Mathlib. Two results were formalized independently, and earlier, by
Bochao Kong in the Palomar registry: the analytic Weierstrass preparation theorem (item 41; entry
PALOMAR-2026-08-29-000010) and Rückert's basis theorem, that the ring of analytic germs is
Noetherian (item 44; entry PALOMAR-2026-08-30-000001, which also contains the local analytic
Nullstellensatz, not treated here). Neither is used here. Mathlib's Weierstrass preparation
theorem concerns formal power series over complete local rings and is likewise not used.
-/


open Complex Filter Function MeasureTheory Metric Set
open scoped Real Topology

namespace SCV

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι]

/-! ## A. Local analysis and differential calculus -/

/-- The derivative in the coordinate `i`, the other coordinates being fixed. -/
noncomputable def partialDeriv [DecidableEq ι] (i : ι) (f : (ι → ℂ) → F) (z : ι → ℂ) : F :=
  deriv (fun w => f (update z i w)) (z i)

/-- The iterated coordinate derivative along a list of coordinates; the leftmost acts last. -/
noncomputable def iteratedPartialDeriv [DecidableEq ι] : List ι → ((ι → ℂ) → F) → (ι → ℂ) → F
  | [], f => f
  | i :: is, f => partialDeriv i (iteratedPartialDeriv is f)

-- BEGIN SOLUTION ONLY
omit [CompleteSpace F] [Fintype ι] in
/-- The submission and library definitions of iterated coordinate derivatives agree. -/
private theorem iteratedPartialDeriv_eq [DecidableEq ι] (is : List ι) (f : (ι → ℂ) → F) :
    iteratedPartialDeriv is f = SeveralComplexVariables.iteratedPartialDeriv is f := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [iteratedPartialDeriv, SeveralComplexVariables.iteratedPartialDeriv, ih]; rfl
-- END SOLUTION ONLY

/-- **1. Cauchy's integral formula on a polydisc**, for a function continuous on the closed polydisc
and analytic in each variable separately. -/
theorem cauchy_formula_polydisc {n : ℕ} {f : (Fin n → ℂ) → F} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ i, 0 < R i) (hw : ∀ i, ‖w i - c i‖ < R i)
    (hfc : ContinuousOn f (Set.pi univ fun i => closedBall (c i) (R i)))
    (hfa : ∀ z ∈ Set.pi univ fun i => closedBall (c i) (R i), ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ((2 * π * I : ℂ) ^ n)⁻¹ • torusIntegral (fun z => (∏ i, (z i - w i)⁻¹) • f z) c R = f w := by
  exact SeveralComplexVariables.two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul hR hw hfc hfa

/-- **2. Osgood's lemma**: a continuous, separately analytic function is jointly analytic. -/
theorem osgood [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F} (hU : IsOpen U)
    (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  exact SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU hfc hf

/-- **3. Holomorphic is analytic** on open subsets of a finite-dimensional space, for Banach-valued
maps. -/
theorem differentiableOn_iff_analyticOnNhd {U : Set E} {f : E → F} (hU : IsOpen U) :
    DifferentiableOn ℂ f U ↔ AnalyticOnNhd ℂ f U := by
  exact differentiableOn_iff_analyticOnNhd_of_finiteDimensional hU

/-- **4. Cauchy–Riemann equations**: holomorphy is real differentiability together with the
coordinate Cauchy–Riemann equations. -/
theorem analyticOnNhd_iff_cauchyRiemann [DecidableEq ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → F} :
    AnalyticOnNhd ℂ f U ↔ (∀ z ∈ U, DifferentiableAt ℝ f z) ∧
      ∀ z ∈ U, ∀ i, fderiv ℝ f z (Pi.single i I) = I • fderiv ℝ f z (Pi.single i 1) := by
  exact SeveralComplexVariables.analyticOnNhd_iff_differentiableAt_real_cauchyRiemann hU

/-- **6. Identity theorem**: holomorphic maps on a connected open set that agree on a nonempty open
subset agree everywhere. -/
theorem identity_theorem {U V : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hV : IsOpen V) (hne : V.Nonempty)
    (hVU : V ⊆ U) (heq : EqOn f g V) : EqOn f g U := by
  exact DifferentiableOn.eqOn_of_preconnected_of_eqOn hU hconn hf hg hV hne hVU heq

/-- **7. Maximum modulus principle**, for maps into a strictly convex Banach space, in particular
for scalar functions. -/
theorem maximum_modulus [StrictConvexSpace ℝ F] {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f : E → F} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U)
    (hmax : IsLocalMax (norm ∘ f) a) : EqOn f (const E (f a)) U := by
  exact SeveralComplexVariables.eqOn_const_of_holomorphic_of_isLocalMax_norm hU hconn hf ha hmax

/-- **9. Cauchy–Pompeiu identity** for a compactly supported `C¹` function, with
the antiholomorphic derivative `(∂φ/∂x + i ∂φ/∂y) / 2` written via the real derivative. -/
theorem cauchy_pompeiu {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ) :
    ∫ w, w⁻¹ • ((2 : ℂ)⁻¹ • (fderiv ℝ φ w 1 + I • fderiv ℝ φ w I)) = -((π : ℂ) • φ 0) := by
  have h := SeveralComplexVariables.integral_inv_smul_dbarAlong_fderiv hφ hsupp
  simpa [SeveralComplexVariables.dbarAlong] using h

/-- The Taylor series at `c` of a function of `n` complex variables: the coefficient of `zᵐ` is
`∂ᵐ f (c) / m!`, the mixed derivative being taken coordinate by coordinate. -/
noncomputable def taylorSeries {n : ℕ} (f : (Fin n → ℂ) → F) (c : Fin n → ℂ) :
    MvPowerSeries (Fin n) F :=
  fun m => (∏ i, (m i).factorial : ℂ)⁻¹ •
    iteratedPartialDeriv (List.ofFn fun i => List.replicate (m i) i).flatten f c

-- BEGIN SOLUTION ONLY
omit [CompleteSpace F] in
/-- The submission Taylor series equals the library holomorphic Taylor series. -/
private theorem taylorSeries_eq {n : ℕ} (f : (Fin n → ℂ) → F) (c : Fin n → ℂ) :
    taylorSeries f c = SeveralComplexVariables.holomorphicTaylorSeries f c := by
  funext m
  simp only [taylorSeries, SeveralComplexVariables.holomorphicTaylorSeries,
    SeveralComplexVariables.multiIndexDeriv, SeveralComplexVariables.multiIndexList,
    iteratedPartialDeriv_eq]
-- END SOLUTION ONLY

/-- **5. Cauchy estimates** for the Taylor coefficients of a function holomorphic near a closed
polydisc and bounded by `M` on it. -/
theorem cauchy_estimates {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {f : (Fin n → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) {c : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) {M : ℝ}
    (hsub : (Set.pi univ fun i => closedBall (c i) (R i)) ⊆ U)
    (hM : ∀ z ∈ Set.pi univ fun i => closedBall (c i) (R i), ‖f z‖ ≤ M) (m : Fin n →₀ ℕ) :
    ‖taylorSeries f c m‖ ≤ M * ∏ i, (R i)⁻¹ ^ m i := by
  have hfa := hf.analyticOnNhd_of_finiteDimensional hU
  have h := SeveralComplexVariables.norm_multiIndexDeriv_le (f := f) (c := c) hR
    (hfa.continuousOn.mono hsub) (fun z hz i => hfa.analyticAt_update (hsub hz) i) hM m
  have hpos : (0 : ℝ) < ∏ i, ((m i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hn : ‖(∏ i, (m i).factorial : ℂ)‖ = ∏ i, ((m i).factorial : ℝ) := by
    simp [norm_prod]
  rw [taylorSeries_eq, SeveralComplexVariables.holomorphicTaylorSeries, norm_smul, norm_inv, hn,
    inv_mul_le_iff₀ hpos]
  exact h

/-- **8. Holomorphic dependence of integrals on parameters**, under a locally integrable bound. -/
theorem analyticOnNhd_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set E}
    {G : E → α → F} (hU : IsOpen U) (hmeas : ∀ x ∈ U, AEStronglyMeasurable (G x) μ)
    (hderivmeas : ∀ x ∈ U, AEStronglyMeasurable (fun a => fderiv ℂ (G · a) x) μ)
    (hhol : ∀ᵐ a ∂μ, AnalyticOnNhd ℂ (G · a) U)
    (hdom : ∀ x ∈ U, ∃ (s : Set E) (bound : α → ℝ), s ∈ 𝓝 x ∧ Integrable bound μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ s, ‖G y a‖ ≤ bound a) :
    AnalyticOnNhd ℂ (fun x => ∫ a, G x a ∂μ) U := by
  exact analyticOnNhd_integral_of_locally_dominated hU hmeas hderivmeas hhol hdom

/-! ## B. Convergence and spaces of holomorphic functions -/

/-- **10. Weierstrass convergence theorem**: a locally uniform limit of holomorphic maps is
holomorphic, and the derivatives converge locally uniformly. -/
theorem weierstrass_convergence {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {g : E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U) (hlim : TendstoLocallyUniformlyOn f g atTop U) :
    DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℂ (f n)) (fderiv ℂ g) atTop U := by
  have hfa : ∀ᶠ n in atTop, AnalyticOnNhd ℂ (f n) U :=
    .of_forall fun n => (hf n).analyticOnNhd_of_finiteDimensional hU
  exact ⟨(hlim.analyticOnNhd_of_finiteDimensional hfa hU).differentiableOn,
    hlim.fderiv_of_finiteDimensional hfa hU⟩

/-- The continuous maps on an open set `U` that are restrictions of holomorphic maps. -/
def holomorphicMaps (U : TopologicalSpace.Opens E) (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℂ F] : Set C(U, F) :=
  {f | ∃ g : E → F, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z}

/-- **11. Holomorphic function spaces**: the holomorphic maps form a closed subset of `C(U, F)` in
the compact-open topology. -/
theorem isClosed_holomorphicMaps (U : TopologicalSpace.Opens E) :
    IsClosed (holomorphicMaps U F) := by
  have h : holomorphicMaps U F =
      (SeveralComplexVariables.holomorphicSubmodule (F := F) U : Set C(U, F)) := by
    ext f
    constructor
    · rintro ⟨g, hg, hgf⟩
      refine ((hg.analyticOnNhd_of_finiteDimensional U.isOpen).congr U.isOpen ?_ :
        AnalyticOnNhd ℂ (SeveralComplexVariables.openExtension U f) U)
      intro z hz
      rw [SeveralComplexVariables.openExtension_apply U f hz]
      exact hgf ⟨z, hz⟩
    · intro hf
      exact ⟨_, (show AnalyticOnNhd ℂ (SeveralComplexVariables.openExtension U f) U from
        hf).differentiableOn, fun z => SeveralComplexVariables.openExtension_coe U f z⟩
  rw [h]
  exact SeveralComplexVariables.isClosed_holomorphicSubmodule U

/-- **12. Montel's theorem**: a uniformly bounded sequence of holomorphic maps with values in a
finite-dimensional space has a locally uniformly convergent subsequence with holomorphic limit. -/
theorem montel [FiniteDimensional ℂ F] {U : Set E} (hU : IsOpen U) {f : ℕ → E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U) {M : ℝ} (hM : ∀ n, ∀ z ∈ U, ‖f n z‖ ≤ M) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  obtain ⟨g, φ, hφ, hg, hlim⟩ :=
    SeveralComplexVariables.exists_subseq_tendstoLocallyUniformlyOn_of_uniform_bound hU
      (fun n => (hf n).analyticOnNhd_of_finiteDimensional hU) (fun n z hz => hM n z hz)
  exact ⟨g, φ, hφ, hg.differentiableOn, hlim⟩

/-- **13. Vitali's theorem**: a locally bounded sequence of holomorphic maps on a connected open set
that converges pointwise on a nonempty open subset converges locally uniformly. -/
theorem vitali [FiniteDimensional ℂ F] {D V : Set E} (hD : IsOpen D) (hconn : IsPreconnected D)
    {f : ℕ → E → F} (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) (hV : IsOpen V)
    (hne : V.Nonempty) (hVD : V ⊆ D)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y)) :
    ∃ g : E → F, DifferentiableOn ℂ g D ∧ TendstoLocallyUniformlyOn f g atTop D := by
  exact SeveralComplexVariables.exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto hD hconn
    hf hb hV hne hVD hp

/-- **14. Holomorphic `Lᵖ` spaces**: on compact subsets, a holomorphic representative of an `Lᵖ`
class is bounded by a constant times the `Lᵖ` norm, for `1 ≤ p ≤ ∞`. -/
theorem holomorphic_Lp_bound (U : TopologicalSpace.Opens (ι → ℂ)) (p : ENNReal) [Fact (1 ≤ p)]
    {K : Set (ι → ℂ)} (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp F p (volume.restrict (U : Set (ι → ℂ)))) (f : (ι → ℂ) → F),
      DifferentiableOn ℂ f U → f =ᵐ[volume.restrict (U : Set (ι → ℂ))] u →
        ∀ z ∈ K, ‖f z‖ ≤ C * ‖u‖ := by
  exact SeveralComplexVariables.exists_norm_le_mul_Lp_norm U p hKU hK

/-! ## C. Local holomorphic mappings -/

/-- **15. Holomorphic inverse mapping theorem**: a holomorphic map with invertible derivative at `a`
is near `a` a homeomorphism between open sets that is holomorphic in both directions. -/
theorem inverse_mapping {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {U : Set E} (hU : IsOpen U) {f : E → G}
    (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U) (hinv : (fderiv ℂ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E G, DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target ∧ a ∈ e.source ∧ e.source ⊆ U ∧ (e : E → G) = f ∧
      fderiv ℂ e.symm (f a) = (fderiv ℂ f a).inverse := by
  obtain ⟨e, he, hae, heU, hef⟩ :=
    SeveralComplexVariables.exists_biholomorphic_of_isInvertible_fderiv hU hf ha hinv
  refine ⟨e, he.1, he.2, hae, heU, hef, ?_⟩
  rw [← hef]
  exact he.fderiv_symm hae

/-- **16. Holomorphic implicit mapping theorem**, with the derivative of the implicit map. -/
theorem implicit_mapping {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup R] [NormedSpace ℂ R]
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] [CompleteSpace R] {D : Set (P × Q)}
    (hD : IsOpen D) {f : P × Q → R} (hf : DifferentiableOn ℂ f D) {a : P} {b : Q}
    (hab : (a, b) ∈ D)
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q) (g : P → Q), IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      DifferentiableOn ℂ g U ∧ MapsTo g U V ∧ g a = b ∧
      HasFDerivAt g (-((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).inverse |>.comp
        ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inl ℂ P Q))) a ∧
      ∀ x ∈ U, ∀ y ∈ V, f (x, y) = f (a, b) ↔ y = g x := by
  exact SeveralComplexVariables.exists_holomorphic_implicit_mapping hD hf hab hi

/-! ## D. Reinhardt geometry, power series, and continuation -/

/-- A set is Reinhardt if it is invariant under independent rotations of the coordinates. -/
def IsReinhardt (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ = ‖z i‖) → w ∈ U

/-- A set is complete Reinhardt if it is closed under decreasing the coordinate moduli. -/
def IsCompleteReinhardt (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ ≤ ‖z i‖) → w ∈ U

/-- Logarithmic convexity: the image of the points without zero coordinates under
`z ↦ (log |z₁|, …, log |zₙ|)` is convex. -/
def IsLogarithmicallyConvex (U : Set (ι → ℂ)) : Prop :=
  Convex ℝ {x : ι → ℝ | (fun i => (Real.exp (x i) : ℂ)) ∈ U}

/-- The convergence domain of a power series: the interior of its set of absolute convergence. -/
def convergenceDomain {G : Type*} [NormedAddCommGroup G] (c : MvPowerSeries ι G) : Set (ι → ℂ) :=
  interior {z | Summable fun m : ι →₀ ℕ => ‖c m‖ * ∏ i, ‖z i‖ ^ m i}

omit [Fintype ι] in
/-- **17. Complete Reinhardt geometry**: a complete Reinhardt set is Reinhardt and, when nonempty,
path connected. -/
theorem IsCompleteReinhardt.isReinhardt_and_isPathConnected {U : Set (ι → ℂ)}
    (hU : IsCompleteReinhardt U) : IsReinhardt U ∧ (U.Nonempty → IsPathConnected U) := by
  have h : SeveralComplexVariables.IsCompleteReinhardt U := hU
  exact ⟨h.isReinhardt, fun hne => h.isPathConnected hne⟩

omit [Fintype ι] in
/-- **18. Logarithmic convexity including zero coordinates**: for an open complete Reinhardt set,
logarithmic convexity is closure under weighted geometric means of the coordinate moduli, with the
convention `0 ^ 0 = 1`. -/
theorem isLogarithmicallyConvex_iff_geometric [Finite ι] {U : Set (ι → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) :
    IsLogarithmicallyConvex U ↔ ∀ z ∈ U, ∀ w ∈ U, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ v : ι → ℂ, (∀ i, ‖v i‖ = ‖z i‖ ^ a * ‖w i‖ ^ b) → v ∈ U := by
  classical
  let := Fintype.ofFinite ι
  have hc' : SeveralComplexVariables.IsCompleteReinhardt U := hc
  rw [show IsLogarithmicallyConvex U ↔ SeveralComplexVariables.IsLogarithmicallyConvex U from
    Iff.rfl, ← SeveralComplexVariables.hasGeometricallyConvexModuli_iff ho hc']
  constructor
  · intro h z hz w hw a b ha hb hab v hv
    obtain ⟨u, hu, hue⟩ := h ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩ ha hb hab
    refine hc'.isReinhardt hu fun i => ?_
    have hi := congrArg NNReal.toReal (congrFun hue i)
    simp only [SeveralComplexVariables.geometricCombination, NNReal.coe_mul, NNReal.coe_rpow,
      coe_nnnorm] at hi
    rw [hv i, hi]
  · rintro h _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
    let u : ι → ℂ := fun i => ((‖z i‖ ^ a * ‖w i‖ ^ b : ℝ) : ℂ)
    have hnn (i : ι) : 0 ≤ ‖z i‖ ^ a * ‖w i‖ ^ b := by positivity
    have hu : u ∈ U := h z hz w hw a b ha hb hab u fun i => by
      simp only [u, Complex.norm_real, Real.norm_of_nonneg (hnn i)]
    refine ⟨u, hu, funext fun i => NNReal.eq ?_⟩
    simp only [u, SeveralComplexVariables.geometricCombination, coe_nnnorm, Complex.norm_real,
      Real.norm_of_nonneg (hnn i), NNReal.coe_mul, NNReal.coe_rpow]

/-- **19. Convergence domains of power series** are complete Reinhardt and logarithmically convex,
and the sum of the series is holomorphic there. -/
theorem convergenceDomain_properties (c : MvPowerSeries ι F) :
    IsCompleteReinhardt (convergenceDomain c) ∧ IsLogarithmicallyConvex (convergenceDomain c) ∧
      AnalyticOnNhd ℂ (fun z => ∑' m : ι →₀ ℕ, (∏ i, z i ^ m i) • c m) (convergenceDomain c) := by
  exact ⟨SeveralComplexVariables.isCompleteReinhardt_powerSeriesConvergenceDomain c,
    SeveralComplexVariables.isLogarithmicallyConvex_powerSeriesConvergenceDomain c,
    SeveralComplexVariables.analyticOnNhd_powerSeriesSum c⟩

/-- **20. Taylor representation on complete Reinhardt sets**: a holomorphic function on an open
complete Reinhardt set is the sum of one power series on the whole set. -/
theorem exists_powerSeries_eqOn_of_isCompleteReinhardt {n : ℕ} {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) :
    ∃ c : MvPowerSeries (Fin n) F, U ⊆ convergenceDomain c ∧
      EqOn (fun z => ∑' m : Fin n →₀ ℕ, (∏ i, z i ^ m i) • c m) f U := by
  exact ⟨_,
    SeveralComplexVariables.IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum
      ho hc hf⟩

/-- **21. Characterization of convergence domains**: every nonempty open complete logarithmically
convex Reinhardt set is the convergence domain of a scalar power series. -/
theorem exists_convergenceDomain_eq {U : Set (ι → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U) :
    ∃ c : MvPowerSeries ι ℂ, convergenceDomain c = U := by
  exact SeveralComplexVariables.exists_powerSeriesConvergenceDomain_eq hU hne hc hl

/-- **22. Laurent expansion on Reinhardt domains**: a holomorphic function on a nonempty connected
open Reinhardt set has a unique locally uniformly convergent Laurent expansion. -/
theorem existsUnique_laurent_expansion {n : ℕ} {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsPreconnected U) (hne : U.Nonempty) (hR : IsReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) :
    ∃! c : (Fin n → ℤ) → F,
      HasSumLocallyUniformlyOn (fun m z => (∏ i, z i ^ m i) • c m) f U := by
  obtain ⟨z, hz⟩ := hne
  have hR' : SeveralComplexVariables.IsReinhardt U := hR
  obtain ⟨r, hrU, hr⟩ := hR'.exists_strict_modulus_majorant ho hz
  have h := SeveralComplexVariables.multivariableLaurent_expansion ho hc hR' hf
    (r := fun i => (r i : ℝ)) (fun i => lt_of_le_of_lt (NNReal.coe_nonneg _) (hr i)) hrU
  exact ⟨_, h.1, fun c hc' => h.2.2.2.2 c hc'⟩

/-- **23. Continuation from Reinhardt domains**: a holomorphic function on a connected open
Reinhardt set containing the origin extends to the complete Reinhardt hull. -/
theorem exists_extension_completeReinhardtHull {n : ℕ} {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsConnected U) (hR : IsReinhardt U) (hzero : 0 ∈ U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g {w | ∃ z ∈ U, ∀ i, ‖w i‖ ≤ ‖z i‖} ∧ EqOn g f U := by
  exact SeveralComplexVariables.exists_extension_completeReinhardtHull ho hc hR hzero hf

/-- **24. Continuation from circular domains**: a holomorphic function on a connected open set
invariant under `z ↦ e^{iθ} z` and containing the origin extends to the balanced hull. -/
theorem exists_extension_balancedHull {U : Set E} (ho : IsOpen U) (hc : IsPreconnected U)
    (hrot : ∀ ⦃z⦄, z ∈ U → ∀ ⦃c : ℂ⦄, ‖c‖ = 1 → c • z ∈ U) (hzero : (0 : E) ∈ U) {f : E → F}
    (hf : AnalyticOnNhd ℂ f U) : ∃ g, AnalyticOnNhd ℂ g (balancedHull ℂ U) ∧ EqOn g f U := by
  exact SeveralComplexVariables.exists_extension_balancedHull ho hc hrot hzero hf

/-! ## E. Hartogs phenomena and removable singularities -/

/-- **25. Hartogs–Taylor expansion**: on an open set `U ⊆ E × ℂ` whose fibres are closed under
decreasing `|w|`, a holomorphic function is the locally uniform sum of its fibre Taylor series,
whose coefficients are holomorphic on the projection of `U`. -/
theorem hartogs_taylor_expansion {U : Set (E × ℂ)} (hU : IsOpen U)
    (hH : ∀ ⦃z w⦄, (z, w) ∈ U → ∀ ⦃v : ℂ⦄, ‖v‖ ≤ ‖w‖ → (z, v) ∈ U) {f : E × ℂ → F}
    (hf : DifferentiableOn ℂ f U) :
    (∀ k : ℕ, DifferentiableOn ℂ
      (fun z => ((k.factorial : ℂ)⁻¹) • iteratedDeriv k (fun w => f (z, w)) 0) (Prod.fst '' U)) ∧
    HasSumLocallyUniformlyOn (fun (k : ℕ) (p : E × ℂ) =>
      p.2 ^ k • (((k.factorial : ℂ)⁻¹) • iteratedDeriv k (fun w => f (p.1, w)) 0)) f U := by
  exact SeveralComplexVariables.differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn
    hU hH hf

/-- **26. Hartogs' continuity theorem**: a holomorphic function on the union of an annular cylinder
over a connected base `D` and a full cylinder over a nonempty open `D₀ ⊆ D` extends to the full
cylinder over `D`. -/
theorem hartogs_cylinder_extension {D D₀ : Set E} (hD : IsOpen D) (hc : IsPreconnected D)
    (hD₀ : IsOpen D₀) (hne : D₀.Nonempty) (hsub : D₀ ⊆ D) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {f : E × ℂ → F}
    (hf : AnalyticOnNhd ℂ f ((D ×ˢ (ball 0 R \ closedBall 0 ρ)) ∪ (D₀ ×ˢ ball 0 R))) :
    ∃ g, AnalyticOnNhd ℂ g (D ×ˢ ball 0 R) ∧
      EqOn g f ((D ×ˢ (ball 0 R \ closedBall 0 ρ)) ∪ (D₀ ×ˢ ball 0 R)) := by
  exact SeveralComplexVariables.exists_extension_hartogsCylinder hD hc hD₀ hne hsub hρ hρR hf

/-- **27. Hartogs' theorem on separate analyticity**: a function on an open subset of `ℂ^ι` that is
analytic in each variable separately is analytic, with no continuity or boundedness hypothesis. -/
theorem hartogs_separate_analyticity [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U) (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  exact SeveralComplexVariables.analyticOnNhd_of_separately_analytic hU hf

/-- **28. Isolated singularities are removable** in dimension at least two. -/
theorem exists_extension_diff_singleton (hdim : 2 ≤ Module.finrank ℂ E) {U : Set E}
    (ho : IsOpen U) {a : E} (ha : a ∈ U) {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ {a})) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {a}) := by
  exact SeveralComplexVariables.exists_analyticOnNhd_extension_diff_singleton hdim ho ha hf

/-- **29. Zeros are not isolated** in dimension at least two. -/
theorem frequently_zero_punctured (hdim : 2 ≤ Module.finrank ℂ E) {f : E → ℂ} {a : E}
    (hf : AnalyticAt ℂ f a) (ha : f a = 0) : ∃ᶠ z in 𝓝[≠] a, f z = 0 := by
  exact SeveralComplexVariables.frequently_zero_punctured_of_analyticAt hdim hf ha

/-- **30. First Riemann extension theorem**: a holomorphic function on the complement of the zero
set of a nonzero holomorphic function `g` on a connected open set, locally bounded near that zero
set, extends holomorphically. -/
theorem riemann_extension_first {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) {g : E → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hne : ∃ z ∈ U, g z ≠ 0) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    (hb : ∀ a ∈ U, g a = 0 → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ ball a r ∩ (U \ g ⁻¹' {0}),
      ‖f z‖ ≤ C) :
    ∃ f' : E → F, AnalyticOnNhd ℂ f' U ∧ EqOn f' f (U \ g ⁻¹' {0}) := by
  exact SeveralComplexVariables.exists_analyticOnNhd_extension_across_zeroSet hU hconn hg hne hf hb

/-- **31. Hartogs' extension theorem (compact holes)**: in dimension at least two, a holomorphic
function on `U \ K`, with `K ⊆ U` compact and `U \ K` connected, extends to `U`. -/
theorem hartogs_compact_hole (hdim : 2 ≤ Module.finrank ℂ E) {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hcompl : IsPreconnected (U \ K)) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (U \ K)) : ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ K) := by
  exact SeveralComplexVariables.exists_analyticOnNhd_extension_of_isCompact hdim hU hK hKU hcompl hf

/-! ## F. Elementary analytic sets -/

/-- `A` is an analytic subset of `U`: near every point of `U` it is the common zero set of finitely
many holomorphic functions. -/
def IsAnalyticSet (U A : Set E) : Prop :=
  A ⊆ U ∧ ∀ a ∈ U, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
    ∃ s : Finset (E → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f V) ∧
      ∀ z ∈ V, z ∈ A ↔ ∀ f ∈ s, f z = 0

/-- `a` is a regular point of `A` of codimension `q`: a local biholomorphic change of coordinates
carries `A` to a complex linear subspace of codimension `q`. -/
def IsRegularAnalyticSetAt (A : Set E) (a : E) (q : ℕ) : Prop :=
  a ∈ A ∧ ∃ (e : OpenPartialHomeomorph E E) (L : E →L[ℂ] (Fin q → ℂ)),
    (DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target) ∧ a ∈ e.source ∧
      Function.Surjective L ∧ ∀ z ∈ e.source, z ∈ A ↔ L (e z) = 0

/-- **32. Analytic sets are thin**: a proper analytic subset of a connected open set has empty
interior and connected complement. -/
theorem IsAnalyticSet.interior_eq_empty_and_isConnected_sdiff {U A : Set E}
    (hA : IsAnalyticSet U A) (hc : IsConnected U) (hp : A ≠ U) :
    interior A = ∅ ∧ IsConnected (U \ A) := by
  have h : SeveralComplexVariables.IsAnalyticSet U A := hA
  exact ⟨h.interior_eq_empty hc.isPreconnected hp, h.isConnected_sdiff hc hp⟩

/-- **33. Regular points and full-rank equations**: `a` is a regular point of codimension `q`
exactly when `A` is near `a` the zero set of `q` holomorphic equations of full rank at `a`. -/
theorem isRegularAnalyticSetAt_iff_exists_equations {A : Set E} {a : E} {q : ℕ} :
    IsRegularAnalyticSetAt A a q ↔ a ∈ A ∧ ∃ (V : Set E) (f : E → (Fin q → ℂ)),
      IsOpen V ∧ a ∈ V ∧ AnalyticOnNhd ℂ f V ∧ (∀ z ∈ V, z ∈ A ↔ f z = 0) ∧
        Function.Surjective (fderiv ℂ f a) := by
  exact SeveralComplexVariables.isRegularAnalyticSetAt_iff_exists_equations

/-- **34. Removal of a coordinate plane of codimension two**. -/
theorem exists_extension_across_coordinatePlane {U : Set ((E × ℂ) × ℂ)} (hU : IsOpen U)
    {f : ((E × ℂ) × ℂ) → F} (hf : AnalyticOnNhd ℂ f (U \ {z | z.1.2 = 0 ∧ z.2 = 0})) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {z | z.1.2 = 0 ∧ z.2 = 0}) := by
  exact SeveralComplexVariables.exists_extension_across_coordinatePlane hU hf

/-- **35. Second Riemann extension theorem**: holomorphic functions extend across an analytic subset
through each point of which some complex affine plane meets it only at that point, locally. -/
theorem riemann_extension_second {U A : Set E} (hA : IsAnalyticSet U A)
    (hcodim : ∀ a ∈ A, ∃ L : (Fin 2 → ℂ) →L[ℂ] E, Function.Injective L ∧
      ∀ᶠ z in 𝓝 (0 : Fin 2 → ℂ), a + L z ∈ A → z = 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ A)) : ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ A) := by
  have h : SeveralComplexVariables.IsAnalyticSet U A := hA
  exact h.exists_extension_of_codimension_two hcodim hf

/-! ## G. Germs, Weierstrass theory, and elementary local algebra -/

/-- The ring `𝒪ₓ` of germs at `x` of scalar analytic functions, as a subring of all germs. -/
def analyticGermRing (x : E) : Subring (Germ (𝓝 x) ℂ) where
  carrier := {φ | ∃ f : E → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝 x) ℂ) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩

/-- The germ at `x` of a function analytic at `x`. -/
def germ {x : E} (f : E → ℂ) (hf : AnalyticAt ℂ f x) : analyticGermRing x := ⟨f, f, hf, rfl⟩

/-- A remainder of degree less than `d` in the last variable, with coefficient functions `a j`. -/
def weierstrassRemainder {d : ℕ} (a : Fin d → E → ℂ) (z : E × ℂ) : ℂ :=
  ∑ j : Fin d, a j z.1 * z.2 ^ (j : ℕ)

/-- Weierstrass division at the origin: `g = q f + r` as germs, with `r` a polynomial of degree
less than `d` in the last variable. -/
def IsWeierstrassDivisionAt {d : ℕ} (f g q : E × ℂ → ℂ) (a : Fin d → E → ℂ) : Prop :=
  AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
    g =ᶠ[𝓝 0] fun z => q z * f z + weierstrassRemainder a z

/-- Weierstrass preparation at the origin: `f = u W` as germs, with `u` a unit and `W` a
distinguished polynomial of degree `d` in the last variable. -/
def IsWeierstrassPreparationAt {d : ℕ} (f u : E × ℂ → ℂ) (a : Fin d → E → ℂ) : Prop :=
  AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧ (∀ j, a j 0 = 0) ∧
    f =ᶠ[𝓝 0] fun z => u z * (z.2 ^ d + weierstrassRemainder a z)

-- BEGIN SOLUTION ONLY
omit [FiniteDimensional ℂ E] in
/-- The submission ring of analytic germs is the library analytic germ subring. -/
private theorem analyticGermRing_eq (x : E) :
    analyticGermRing x = SeveralComplexVariables.analyticGermSubring ℂ x := rfl

omit [FiniteDimensional ℂ E] in
/-- The submission and library predicates for Weierstrass division are equivalent. -/
private theorem isWeierstrassDivisionAt_iff {d : ℕ} {f g q : E × ℂ → ℂ} {a : Fin d → E → ℂ} :
    IsWeierstrassDivisionAt f g q a ↔ SeveralComplexVariables.IsWeierstrassDivisionAt f g q a :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

omit [FiniteDimensional ℂ E] in
/-- The submission and library predicates for Weierstrass preparation are equivalent. -/
private theorem isWeierstrassPreparationAt_iff {d : ℕ} {f u : E × ℂ → ℂ} {a : Fin d → E → ℂ} :
    IsWeierstrassPreparationAt f u a ↔ SeveralComplexVariables.IsWeierstrassPreparationAt f u a :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩
-- END SOLUTION ONLY

omit [FiniteDimensional ℂ E] in
/-- **36. The ring of analytic germs is a local integral domain**, and a germ is a unit exactly when
it does not vanish at the base point. -/
theorem analyticGermRing_isDomain_isLocalRing (x : E) :
    IsDomain (analyticGermRing x) ∧ IsLocalRing (analyticGermRing x) ∧
      ∀ (f : E → ℂ) (hf : AnalyticAt ℂ f x), IsUnit (germ f hf) ↔ f x ≠ 0 := by
  refine ⟨inferInstanceAs (IsDomain (SeveralComplexVariables.AnalyticGerm ℂ x)),
    inferInstanceAs (IsLocalRing (SeveralComplexVariables.AnalyticGerm ℂ x)), fun f hf => ?_⟩
  exact SeveralComplexVariables.AnalyticGerm.isUnit_iff
    (SeveralComplexVariables.AnalyticGerm.ofAnalyticAt f hf)

/-- **37. Coordinate normalization**: after a linear change of coordinates, a nonzero germ has
finite order in the last variable. -/
theorem exists_regular_coordinate_change {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hne : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ (L : (E × ℂ) ≃L[ℂ] (E × ℂ)) (d : ℕ), analyticOrderAt (fun w : ℂ => f (L (0, w))) 0 = d := by
  exact SeveralComplexVariables.exists_regular_coordinate_change hf hne

/-- **38. Taylor series determine germs** and are multiplicative. -/
theorem taylorSeries_mul_and_eq_zero_iff {n : ℕ} {x : Fin n → ℂ} {f g : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    taylorSeries (f * g) x = taylorSeries f x * taylorSeries g x ∧
      (taylorSeries f x = 0 ↔ f =ᶠ[𝓝 x] 0) := by
  open SeveralComplexVariables.AnalyticGerm in
  refine ⟨?_, ?_⟩
  · have h := taylorSeries_mul (ofAnalyticAt f hf) (ofAnalyticAt g hg)
    rwa [← ofAnalyticAt_mul, taylorSeries_ofAnalyticAt, taylorSeries_ofAnalyticAt,
      taylorSeries_ofAnalyticAt, ← taylorSeries_eq, ← taylorSeries_eq, ← taylorSeries_eq] at h
  · have h := taylorSeries_eq_zero_iff (ofAnalyticAt f hf)
    rw [taylorSeries_ofAnalyticAt, ← taylorSeries_eq, ← ofAnalyticAt_zero,
      ofAnalyticAt_eq_iff] at h
    exact h

omit [Fintype ι] in
/-- **39. Division by a power of the last coordinate** on a product of a polydisc `P` and a disc,
with a bound for the quotient. -/
theorem coordinatePower_division [Finite ι] (d : ℕ) {r : ι → ℝ} {R : ℝ} (hR : 0 < R)
    {P : Set (ι → ℂ)}
    (hP : P = Set.pi univ fun i => ball (0 : ℂ) (r i)) {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (P ×ˢ ball 0 R)) :
    ∃ (q : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ), DifferentiableOn ℂ q (P ×ˢ ball 0 R) ∧
      (∀ j, DifferentiableOn ℂ (a j) P) ∧
      EqOn g (fun z => q z * z.2 ^ d + weierstrassRemainder a z) (P ×ˢ ball 0 R) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ z ∈ P ×ˢ ball (0 : ℂ) R, ‖g z‖ ≤ M) →
        ∀ z ∈ P ×ˢ ball (0 : ℂ) R, ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * M := by
  classical
  let := Fintype.ofFinite ι
  subst hP
  obtain ⟨q, a, hdiv, hb, -⟩ := SeveralComplexVariables.coordinatePower_division d (r := r) hR hg
  exact ⟨q, a, hdiv.1, hdiv.2, hdiv.3, hb⟩

/-- **40. Weierstrass division theorem**, with uniqueness of quotient and remainder as germs. -/
theorem weierstrass_division {d : ℕ} {f g : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (q : E × ℂ → ℂ) (a : Fin d → E → ℂ), IsWeierstrassDivisionAt f g q a ∧
      ∀ q' a', IsWeierstrassDivisionAt f g q' a' → q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  obtain ⟨q, a, h, hu⟩ :=
    SeveralComplexVariables.exists_isWeierstrassDivisionAt_of_finiteDimensional hf hg horder
  exact ⟨q, a, isWeierstrassDivisionAt_iff.mpr h,
    fun q' a' h' => hu q' a' (isWeierstrassDivisionAt_iff.mp h')⟩

/-- **41. Weierstrass preparation theorem**, with uniqueness of the unit and the polynomial. -/
theorem weierstrass_preparation {d : ℕ} {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (u : E × ℂ → ℂ) (a : Fin d → E → ℂ), IsWeierstrassPreparationAt f u a ∧
      ∀ v b, IsWeierstrassPreparationAt f v b → u =ᶠ[𝓝 0] v ∧ ∀ j, a j =ᶠ[𝓝 0] b j := by
  obtain ⟨u, a, h, hu⟩ :=
    SeveralComplexVariables.exists_isWeierstrassPreparationAt_of_finiteDimensional hf horder
  exact ⟨u, a, isWeierstrassPreparationAt_iff.mpr h,
    fun v b h' => hu v b (isWeierstrassPreparationAt_iff.mp h')⟩

/-- **44–45. The ring of analytic germs is Noetherian and factorial.** -/
theorem analyticGermRing_isNoetherianRing_ufd (x : E) :
    IsNoetherianRing (analyticGermRing x) ∧ UniqueFactorizationMonoid (analyticGermRing x) := by
  exact ⟨inferInstanceAs (IsNoetherianRing (SeveralComplexVariables.AnalyticGerm ℂ x)),
    inferInstanceAs (UniqueFactorizationMonoid (SeveralComplexVariables.AnalyticGerm ℂ x))⟩

/-- **45. Relative primality persists**: the set of points at which the germs of two functions are
analytic and relatively prime is open. -/
theorem isOpen_isRelPrime_locus (f g : E → ℂ) :
    IsOpen {x | ∃ (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x),
      IsRelPrime (germ f hf) (germ g hg)} := by
  exact SeveralComplexVariables.AnalyticGerm.isOpen_isRelPrime_locus f g

/-! ## H. Zero-set geometry and biholomorphic rigidity -/

/-- **46. Regular points of hypersurfaces**: the zero set of a holomorphic function on a connected
open set, if nonempty and proper, contains a regular point of codimension one. -/
theorem exists_regularPoint_zeroSet {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ b ∈ U, f b ≠ 0) (hz : ∃ a ∈ U, f a = 0) :
    ∃ a, IsRegularAnalyticSetAt (U ∩ f ⁻¹' {0}) a 1 := by
  exact SeveralComplexVariables.exists_regularPoint_zeroSet hU hc hf hne hz

/-- **47. Injective holomorphic maps in equal dimensions are biholomorphic** onto their open
image. -/
theorem injOn_biholomorphic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] (hdim : Module.finrank ℂ E = Module.finrank ℂ G) {U : Set E}
    (hU : IsOpen U) {f : E → G} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ∃ e : OpenPartialHomeomorph E G, DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target ∧ e.source = U ∧ e.target = f '' U ∧ (e : E → G) = f := by
  obtain ⟨e, he, h⟩ := SeveralComplexVariables.exists_biholomorphic_of_injOn hdim hU hf hi
  exact ⟨e, he.1, he.2, h⟩

/-- **48. Cartan's uniqueness theorem**: a holomorphic self-map of a bounded connected open set
fixing a point with identity derivative there is the identity. -/
theorem cartan_uniqueness {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hb : Bornology.IsBounded U) {f : E → E} (hf : AnalyticOnNhd ℂ f U) (hmaps : MapsTo f U U)
    {a : E} (ha : a ∈ U) (hfix : f a = a) (hderiv : fderiv ℂ f a = ContinuousLinearMap.id ℂ E) :
    EqOn f id U := by
  exact SeveralComplexVariables.eqOn_id_of_mapsTo_of_fderiv_eq_id hU hconn hb hf hmaps ha hfix
    hderiv

/-- **49. Biholomorphisms of circular domains fixing the origin are linear**, when the source is
bounded and connected. -/
theorem biholomorphic_circular_linear {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {e : OpenPartialHomeomorph E G} (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) (hc : IsPreconnected e.source)
    (hb : Bornology.IsBounded e.source)
    (hrot : ∀ ⦃z⦄, z ∈ e.source → ∀ ⦃c : ℂ⦄, ‖c‖ = 1 → c • z ∈ e.source)
    (hrot' : ∀ ⦃z⦄, z ∈ e.target → ∀ ⦃c : ℂ⦄, ‖c‖ = 1 → c • z ∈ e.target)
    (hzero : (0 : E) ∈ e.source) (hfix : e 0 = 0) : ∃ L : E ≃L[ℂ] G, EqOn e L e.source := by
  have h : SeveralComplexVariables.IsBiholomorphic e := ⟨he, he'⟩
  exact h.exists_linearEquiv_of_circular hc hb hrot hrot' hzero hfix

/-- **50. The automorphisms of the unit ball of a complex inner product space act transitively.** -/
theorem exists_ball_automorphism {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {a b : H} (ha : a ∈ ball (0 : H) 1) (hb : b ∈ ball (0 : H) 1) :
    ∃ e : OpenPartialHomeomorph H H, DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target ∧ e.source = ball 0 1 ∧ e.target = ball 0 1 ∧
      e a = b := by
  obtain ⟨e, he, h⟩ := SeveralComplexVariables.exists_ball_automorphism ha hb
  exact ⟨e, he.1, he.2, h⟩

/-- **50. The unit polydisc and the Euclidean unit ball are not biholomorphic** in dimension at
least two. -/
theorem not_biholomorphic_polydisc_ball (hdim : 2 ≤ Fintype.card ι) :
    ¬ ∃ e : OpenPartialHomeomorph (ι → ℂ) (EuclideanSpace ℂ ι), DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target ∧ e.source = ball 0 1 ∧ e.target = ball 0 1 := by
  rintro ⟨e, h1, h2, h⟩
  exact SeveralComplexVariables.not_exists_isBiholomorphic_polydisc_ball hdim ⟨e, ⟨h1, h2⟩, h⟩

/-! ## I. Common extensions, holomorphic convexity, Cartan–Thullen, and Bochner's tube theorem -/

/-- The holomorphic hull of `K` relative to `U`: the points of `U` at which every holomorphic
function on `U` is bounded by each of its bounds on `K`. -/
def holomorphicHull (U K : Set E) : Set E :=
  {z | z ∈ U ∧ ∀ f : E → ℂ, AnalyticOnNhd ℂ f U → ∀ M : ℝ, (∀ w ∈ K, ‖f w‖ ≤ M) → ‖f z‖ ≤ M}

/-- `U` is holomorphically convex: hulls of compact subsets are compact. -/
def IsHolomorphicallyConvex (U : Set E) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → IsCompact (holomorphicHull U K)

/-- The generalized domain-of-holomorphy continuation property for a set `U`: there is no connected
open set `V ⊄ U` with a nonempty open `W ⊆ U ∩ V` such that every holomorphic function on `U`
agrees on `W` with one on `V`.

Openness, connectedness, and nonemptiness of `U` are separate hypotheses. This predicate is
automatically satisfied when `interior U = ∅`, because no nonempty open overlap exists. -/
def IsDomainOfHolomorphy (U : Set E) : Prop :=
  ∀ V W : Set E, IsOpen V → IsConnected V → IsOpen W → W.Nonempty → W ⊆ U → W ⊆ V →
    (∀ f : E → ℂ, AnalyticOnNhd ℂ f U → ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧ EqOn g f W) → V ⊆ U

/-- `U` is the domain of existence of `f`: `f` is holomorphic on `U` and has no continuation in the
above sense. -/
def IsDomainOfExistence (U : Set E) (f : E → ℂ) : Prop :=
  AnalyticOnNhd ℂ f U ∧
    ∀ V W : Set E, IsOpen V → IsConnected V → IsOpen W → W.Nonempty → W ⊆ U → W ⊆ V →
      (∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f W) → V ⊆ U

omit [FiniteDimensional ℂ E] in
/-- **51. Common extension domains**: if every holomorphic function on a nonempty open `U` extends
to the connected set `V ⊇ U`, then `V` lies in the convex hull of `U` and holomorphic functions on
`V` take no new values. -/
theorem common_extension {U V : Set E} (hUV : U ⊆ V)
    (hext : ∀ f : E → ℂ, AnalyticOnNhd ℂ f U → ∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f U)
    (ho : IsOpen U) (hne : U.Nonempty) (hc : IsPreconnected V) :
    V ⊆ convexHull ℝ U ∧ ∀ f : E → ℂ, AnalyticOnNhd ℂ f V → f '' V = f '' U := by
  have h := SeveralComplexVariables.isCommonAnalyticExtension_of_forall hUV hext
  exact ⟨h.subset_convexHull ho hne hc, fun f hf => h.image_eq ho hne hc hf⟩

/-- **52. Holomorphic hulls** are idempotent, and hulls of bounded sets are bounded. -/
theorem holomorphicHull_idem_and_isBounded (U : Set (ι → ℂ)) {K : Set (ι → ℂ)} :
    holomorphicHull U (holomorphicHull U K) = holomorphicHull U K ∧
      (Bornology.IsBounded K → Bornology.IsBounded (holomorphicHull U K)) := by
  exact ⟨SeveralComplexVariables.holomorphicHull_idem U K,
    SeveralComplexVariables.isBounded_holomorphicHull U⟩

/-- **52. Open complete logarithmically convex Reinhardt sets are holomorphically convex.** -/
theorem isHolomorphicallyConvex_of_completeReinhardt {U : Set (ι → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U) : IsHolomorphicallyConvex U := by
  exact SeveralComplexVariables.isHolomorphicallyConvex_of_completeReinhardt ho hc hl

omit [FiniteDimensional ℂ E] in
/-- **53. Elementary continuation obstructions.** Convex open sets and finite products of arbitrary
plane sets satisfy `IsDomainOfHolomorphy`, the continuation-obstruction predicate defined above.
This predicate does not require openness, connectedness, or nonemptiness. It holds vacuously
whenever the set has empty interior, because no nonempty open overlap exists. For nonempty
connected open plane factors, the product assertion recovers the classical theorem that their
product is a domain of holomorphy. -/
theorem isDomainOfHolomorphy_of_convex_and_pi :
    (∀ U : Set E, Convex ℝ U → IsOpen U → IsDomainOfHolomorphy U) ∧
      ∀ S : ι → Set ℂ, IsDomainOfHolomorphy (Set.pi univ S) := by
  exact ⟨fun _ hU ho => SeveralComplexVariables.isDomainOfHolomorphy_of_convex hU ho,
    fun S => SeveralComplexVariables.isDomainOfHolomorphy_pi S⟩

/-- **54. Escaping sequences**: an open set is holomorphically convex exactly when every sequence
leaving all its compact subsets is unbounded under some holomorphic function. -/
theorem isHolomorphicallyConvex_iff_escaping {U : Set E} (ho : IsOpen U) :
    IsHolomorphicallyConvex U ↔ ∀ p : ℕ → E, (∀ j, p j ∈ U) →
      (∀ K : Set E, IsCompact K → K ⊆ U → ∀ᶠ j in atTop, p j ∉ K) →
      ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ ¬ BddAbove (Set.range fun j => ‖f (p j)‖) := by
  exact SeveralComplexVariables.isHolomorphicallyConvex_iff_unbounded_on_escaping_sequences ho

/-- **55. Thullen's lemma, as a characterization**: an open subset of `ℂ^ι` with the supremum norm
is a domain of holomorphy exactly when polydisc radii available on a compact set remain available
on its holomorphic hull. -/
theorem isDomainOfHolomorphy_iff_hull_radius {n : ℕ} {U : Set (Fin n → ℂ)} (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ ∀ K, IsCompact K → K ⊆ U → ∀ r : ℝ, 0 < r →
      (∀ x ∈ K, ball x r ⊆ U) → ∀ a ∈ holomorphicHull U K, ball a r ⊆ U := by
  exact SeveralComplexVariables.isDomainOfHolomorphy_iff_hasHolomorphicHullRadiusProperty ho

/-- **56. Cartan–Thullen theorem**: for an open set, being a domain of holomorphy, holomorphic
convexity, and being the domain of existence of one function are equivalent. -/
theorem cartan_thullen {U : Set E} (ho : IsOpen U) :
    (IsDomainOfHolomorphy U ↔ IsHolomorphicallyConvex U) ∧
      (IsDomainOfHolomorphy U ↔ ∃ f : E → ℂ, IsDomainOfExistence U f) := by
  exact ⟨SeveralComplexVariables.isDomainOfHolomorphy_iff_isHolomorphicallyConvex ho,
    SeveralComplexVariables.isDomainOfHolomorphy_iff_exists_domainOfExistence ho⟩

/-- **57. Bochner's tube theorem**: a holomorphic function on the tube over a connected open base
`Ω ⊆ ℝ^ι` extends to the tube over the convex hull of `Ω`, and the tube is a domain of holomorphy
exactly when `Ω` is convex. -/
theorem bochner_tube {Ω : Set (ι → ℝ)} (ho : IsOpen Ω) (hc : IsPreconnected Ω) :
    (∀ f : (ι → ℂ) → F, AnalyticOnNhd ℂ f {z | (fun i => (z i).re) ∈ Ω} →
      ∃ g : (ι → ℂ) → F, AnalyticOnNhd ℂ g {z | (fun i => (z i).re) ∈ convexHull ℝ Ω} ∧
        EqOn g f {z | (fun i => (z i).re) ∈ Ω}) ∧
      (IsDomainOfHolomorphy {z : ι → ℂ | (fun i => (z i).re) ∈ Ω} ↔ Convex ℝ Ω) := by
  exact ⟨fun f hf => SeveralComplexVariables.exists_extension_tubeDomain_convexHull ho hc hf,
    SeveralComplexVariables.isDomainOfHolomorphy_tubeDomain_iff ho hc⟩

/-! ## J. Plurisubharmonic functions, the Levi form, and pseudoconvexity -/

/-- The local submean property of `u` at `a`: on all small circles around `a`, `u` is integrable
and `u a` is at most its average. -/
def HasSubmeanAt (u : ℂ → ℝ) (a : ℂ) : Prop :=
  ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable u a r ∧ u a ≤ Real.circleAverage u a r

/-- `u` is subharmonic on `U`: upper semicontinuous with the local submean property. -/
def SubharmonicOn (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  UpperSemicontinuousOn u U ∧ ∀ a ∈ U, HasSubmeanAt u a

/-- `f` is plurisubharmonic on `U`: upper semicontinuous, and subharmonic on every complex line. -/
def PlurisubharmonicOn (f : E → ℝ) (U : Set E) : Prop :=
  UpperSemicontinuousOn f U ∧
    ∀ a ∈ U, ∀ w : E, SubharmonicOn (fun t : ℂ => f (a + t • w)) {t | a + t • w ∈ U}

/-- The Levi form of `f` at `a` in the direction `w`, through the real second derivative. -/
noncomputable def leviForm (f : E → ℝ) (a w : E) : ℝ :=
  (iteratedFDeriv ℝ 2 f a ![w, w] + iteratedFDeriv ℝ 2 f a ![I • w, I • w]) / 4

/-- `U` is pseudoconvex: open, with a continuous plurisubharmonic exhaustion function. -/
def IsPseudoconvex (U : Set E) : Prop :=
  IsOpen U ∧ ∃ φ : E → ℝ, ContinuousOn φ U ∧ PlurisubharmonicOn φ U ∧
    ∀ c : ℝ, IsCompact {z ∈ U | φ z ≤ c}

/-- `ρ` is a local `C²` defining function of `U` on the neighbourhood `V` of the point `p`. -/
def IsLocalDefiningFunction (U : Set E) (p : E) (ρ : E → ℝ) (V : Set E) : Prop :=
  IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 ρ V ∧ ρ p = 0 ∧ fderiv ℝ ρ p ≠ 0 ∧ U ∩ V = {z | ρ z < 0} ∩ V

/-- `w` is a complex tangent vector at `p` of the level set of `ρ`. -/
def IsComplexTangent (ρ : E → ℝ) (p w : E) : Prop :=
  fderiv ℝ ρ p w = 0 ∧ fderiv ℝ ρ p (I • w) = 0

/-- The Levi condition at `p`: for every local defining function, the Levi form is positive
semidefinite on the complex tangent space. -/
def IsLeviPseudoconvexAt (U : Set E) (p : E) : Prop :=
  ∀ (ρ : E → ℝ) (V : Set E), IsLocalDefiningFunction U p ρ V →
    ∀ w, IsComplexTangent ρ p w → 0 ≤ leviForm ρ p w

-- BEGIN SOLUTION ONLY
omit [FiniteDimensional ℂ E] in
/-- The submission and library predicates for local defining functions are equivalent. -/
private theorem isLocalDefiningFunction_iff {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E} :
    IsLocalDefiningFunction U p ρ V ↔ SeveralComplexVariables.IsLocalDefiningFunction U p ρ V :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩⟩

omit [FiniteDimensional ℂ E] in
/-- The submission and library predicates for Levi pseudoconvexity are equivalent. -/
private theorem isLeviPseudoconvexAt_iff {U : Set E} {p : E} :
    IsLeviPseudoconvexAt U p ↔ SeveralComplexVariables.IsLeviPseudoconvexAt U p :=
  ⟨fun h ρ V hρ => h ρ V (isLocalDefiningFunction_iff.mpr hρ),
    fun h ρ V hρ => h ρ V (isLocalDefiningFunction_iff.mp hρ)⟩
-- END SOLUTION ONLY

/-- **58. Maximum principle for subharmonic functions.** -/
theorem SubharmonicOn.eqOn_const_of_isMaxOn {u : ℂ → ℝ} {U : Set ℂ} {a : ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hu : SubharmonicOn u U) (ha : a ∈ U) (hmax : ∀ z ∈ U, u z ≤ u a) :
    ∀ z ∈ U, u z = u a := by
  have h : SeveralComplexVariables.SubharmonicOn u U := hu
  exact h.eqOn_const_of_isMaxOn hU hc ha hmax

/-- **59. Laplacian criterion**: a `C²` function on an open subset of `ℂ` is subharmonic exactly
when its Laplacian is nonnegative. -/
theorem subharmonicOn_iff_laplacian_nonneg {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) : SubharmonicOn g U ↔ ∀ t ∈ U, 0 ≤ Laplacian.laplacian g t := by
  refine ⟨fun h t ht => ?_,
    fun h => SeveralComplexVariables.subharmonicOn_of_laplacian_nonneg hU hg h⟩
  exact SeveralComplexVariables.HasSubmeanAt.laplacian_nonneg (hg.contDiffAt (hU.mem_nhds ht))
    (h.2 t ht)

omit [FiniteDimensional ℂ E] in
/-- **60. Levi-form criterion**: a `C²` function is plurisubharmonic exactly when its Levi form is
positive semidefinite. -/
theorem plurisubharmonicOn_iff_leviForm_nonneg {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) :
    PlurisubharmonicOn f U ↔ ∀ a ∈ U, ∀ w : E, 0 ≤ leviForm f a w := by
  exact SeveralComplexVariables.plurisubharmonicOn_iff_leviForm_nonneg hU hf

/-- **61. Domains of holomorphy are pseudoconvex.** -/
theorem IsDomainOfHolomorphy.isPseudoconvex {U : Set E} (hU : IsDomainOfHolomorphy U)
    (ho : IsOpen U) : IsPseudoconvex U := by
  have h : SeveralComplexVariables.IsDomainOfHolomorphy U := hU
  exact h.isPseudoconvex ho

omit [FiniteDimensional ℂ E] in
/-- **61. Pseudoconvex sets satisfy the continuity principle** for continuous families of affine
analytic discs. -/
theorem IsPseudoconvex.continuity_principle {U : Set E} (h : IsPseudoconvex U) (a b : ℝ → E)
    (ha : Continuous a) (hb : Continuous b)
    (hbdry : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ sphere (0 : ℂ) 1, a t + ζ • b t ∈ U)
    (hinit : ∀ ζ ∈ closedBall (0 : ℂ) 1, a 0 + ζ • b 0 ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ closedBall (0 : ℂ) 1, a t + ζ • b t ∈ U := by
  have h' : SeveralComplexVariables.IsPseudoconvex U := h
  exact h'.satisfiesContinuityPrinciple a b ha hb hbdry hinit

/-- **62. Levi's theorem**: a domain of holomorphy satisfies the Levi condition at every boundary
point admitting a local `C²` defining function. -/
theorem IsDomainOfHolomorphy.isLeviPseudoconvexAt {U : Set E} (hU : IsDomainOfHolomorphy U)
    (ho : IsOpen U) {p : E} (hp : p ∈ frontier U) : IsLeviPseudoconvexAt U p := by
  have h : SeveralComplexVariables.IsDomainOfHolomorphy U := hU
  exact isLeviPseudoconvexAt_iff.mpr (h.isLeviPseudoconvex ho p hp)

omit [FiniteDimensional ℂ E] in
/-- **63. The Levi form under holomorphic maps.** -/
theorem leviForm_comp_analytic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {g : G → ℝ}
    {Φ : E → G} {a : E} (hg : ContDiffAt ℝ 2 g (Φ a)) (hΦ : AnalyticAt ℂ Φ a) (w : E) :
    leviForm (g ∘ Φ) a w = leviForm g (Φ a) (fderiv ℂ Φ a w) := by
  exact SeveralComplexVariables.leviForm_comp_analytic hg hΦ w

omit [FiniteDimensional ℂ E] in
/-- **64. Independence of the defining function**: the Levi condition may be tested on one local
defining function. -/
theorem isLeviPseudoconvexAt_iff_of_defining {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}
    (h : IsLocalDefiningFunction U p ρ V) :
    IsLeviPseudoconvexAt U p ↔ ∀ w, IsComplexTangent ρ p w → 0 ≤ leviForm ρ p w := by
  rw [isLeviPseudoconvexAt_iff]
  exact SeveralComplexVariables.isLeviPseudoconvexAt_iff_of_defining
    (isLocalDefiningFunction_iff.mp h)

/-- **64. Local peak functions** at strictly Levi pseudoconvex boundary points. -/
theorem exists_local_peak_function {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}
    (h : IsLocalDefiningFunction U p ρ V)
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ W ∈ 𝓝 p, ∃ f : E → ℂ, AnalyticOnNhd ℂ f univ ∧ f p = 1 ∧
      ∀ z ∈ W, z ≠ p → ρ z ≤ 0 → ‖f z‖ < 1 := by
  exact (isLocalDefiningFunction_iff.mp h).exists_peak hstrict

/-! ## K. Runge domains and polynomial hulls -/

/-- The polynomial hull of `K`. -/
def polynomialHull {n : ℕ} (K : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | ∀ P : MvPolynomial (Fin n) ℂ, ∀ M : ℝ,
    (∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M) → ‖MvPolynomial.eval z P‖ ≤ M}

/-- `U` is a Runge domain: holomorphic functions on `U` are approximated by polynomials, uniformly
on compact subsets. -/
def IsRungeDomain {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  ∀ f : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ f U → ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ U →
    ∀ ε > 0, ∃ P : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z P‖ < ε

/-- **65. Runge domains**: open complete Reinhardt sets are Runge domains, and in a Runge domain the
polynomial hull of a compact subset meets the domain in its holomorphic hull. -/
theorem runge_domains {n : ℕ} {U : Set (Fin n → ℂ)} (ho : IsOpen U) :
    (IsCompleteReinhardt U → IsRungeDomain U) ∧
      (IsRungeDomain U → ∀ K, IsCompact K → K ⊆ U →
        polynomialHull K ∩ U = holomorphicHull U K) := by
  refine ⟨fun hc => SeveralComplexVariables.IsCompleteReinhardt.isRungeDomain ho hc,
    fun h K hK hKU => ?_⟩
  have h' : SeveralComplexVariables.IsRungeDomain U := h
  exact h'.polynomialHull_inter hK hKU

end SCV

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
