/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.KoszulRestrictedExactness
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetGraphKoszul

/-!
# Strictness, closed images, and the loss-of-precision inclusions (9)/(10)

Source: [FJP] Lemma 5.1 (clauses 1–3) and the displayed inclusions (9), (10).  This file
sits on top of K5's all-degree exactness `GraphKoszul.koszulGraph_restricted_exact`
(paper Lemma 5.1 clause 1) and delivers the two remaining clauses plus the two
loss-of-precision inclusions:

* **Clause 2 (closed images).** `isClosed_range_koszulDifferential` — every Koszul
  differential of the graph datum over `P_E = E⟨T₁,…,T_m⟩` has closed image.  In positive
  degree this is `im d_{q+1} = ker d_q` (exactness) closed as the preimage of `{0}` under
  the continuous `d_q`; the bottom image `im d_0` is the graph ideal `J_E`, closed by
  `GraphKoszul.isClosed_graphIdeal` transported along the degree-`0` conjugation.
* **Clause 2 (strictness).** `koszulDifferential_isStrict` — every differential is strict
  (`IsStrictLinearMap`): supplied from the controlled lift
  `koszulDifferential_exists_lift` through the bounded-lift criterion
  `isStrictLinearMap_of_lift`.
* **Headline.** `koszulGraph_exact_strict_closed` bundles clauses 1–3 of [FJP] Lemma 5.1:
  all-degree exactness, all-degree strictness, and all-degree closed images.
* **Equation (9).** `exists_d1_lift_pow` (∃-`h` norm form) and
  `pow_smul_graphIdeal_inter_unitBall_subset` (the displayed lattice inclusion
  `ϖ^h (J_E ∩ P_{E,0}) ⊆ d_{1,E}(P_{E,0}^m)`).
* **Equation (10).** `exists_d2_lift_pow` (∃-`z` norm form) and
  `pow_smul_ker_d1_inter_subset` (the displayed lattice inclusion
  `ϖ^z (ker d_{1} ∩ P_{E,0}^m) ⊆ d_{2}(⋀² P_{E,0}^m)`), generic in the qualifying vertex
  `E` (specialised to `D` downstream).

The scaling element playing the role of the uniformizer `ϖ` inside `P_E` is
`polyToP (MvPolynomial.C t)` (the image of the pseudo-uniformizer `t : E`), abbreviated
`tP` in the proofs.  The constants `h`/`z` are datum-dependent and merely asserted to
exist ([FJP] §6 caution 2: no effectivity); (9) is about the *algebraic* image `J_E`, not
its closure ([FJP] §6 caution 1).  All statements degenerate correctly when an index type
`KoszulIndex m q` is empty (`q > m`): the sup norm of the empty tuple is `0`, so no
`Nonempty` hypothesis is required.
-/

@[expose] public section

open Filter Topology

namespace FiniteJet

/-! ### A bounded-lift criterion for strictness

An `R`-linear map between seminormed modules whose image admits a norm-bounded lift
(there is `c > 0` with every `y` in the image lifting to some `u`, `‖u‖ ≤ c ‖y‖`) is
strict: the induced map onto its range is open.  This is the elementary half of the open
mapping theorem — no Baire input — packaged for the project's `IsStrictLinearMap`
predicate. -/

/-- **Bounded-lift ⇒ strict.** A linear map `L` with a norm-bounded set-theoretic right
inverse on its image is strict (open onto its range). -/
theorem isStrictLinearMap_of_lift {R M N : Type*} [Semiring R]
    [SeminormedAddCommGroup M] [SeminormedAddCommGroup N] [Module R M] [Module R N]
    (L : M →ₗ[R] N) {c : ℝ} (hc : 0 < c)
    (hlift : ∀ y ∈ Set.range L, ∃ u, L u = y ∧ ‖u‖ ≤ c * ‖y‖) :
    IsStrictLinearMap L := by
  show IsOpenMap (Set.rangeFactorization (⇑L))
  intro U hU
  rw [Metric.isOpen_iff]
  rintro p ⟨x₀, hx₀U, rfl⟩
  obtain ⟨δ, hδ0, hδU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀U
  refine ⟨δ / c, by positivity, fun z hz => ?_⟩
  have hzd : dist (z : N) (L x₀) < δ / c := by
    rw [Metric.mem_ball, Subtype.dist_eq] at hz
    exact hz
  have hzsub : (z : N) - L x₀ ∈ Set.range (⇑L) := by
    obtain ⟨a, ha⟩ := z.2
    exact ⟨a - x₀, by rw [map_sub, ha]⟩
  obtain ⟨w, hw, hwn⟩ := hlift _ hzsub
  have hwδ : ‖w‖ < δ := by
    calc ‖w‖ ≤ c * ‖(z : N) - L x₀‖ := hwn
      _ = c * dist (z : N) (L x₀) := by rw [dist_eq_norm]
      _ < c * (δ / c) := mul_lt_mul_of_pos_left hzd hc
      _ = δ := by field_simp
  refine ⟨x₀ + w, hδU ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hwδ
  · apply Subtype.ext
    show L (x₀ + w) = (z : N)
    rw [map_add, hw]
    abel

namespace GraphKoszul

open KoszulFree

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

/-! ### The range of `d₁` is the graph ideal (eq. (2) as a set) -/

omit [NormOneClass E] [CompleteSpace E] in
/-- The set-theoretic image of the first graph differential `d₁` is exactly the graph
ideal `J_E = (r₁,…,r_m)` ([FJP] eq. (2)). -/
theorem range_d1 (r : Fin m → P E m) :
    Set.range (d1 r) = (Ideal.span (Set.range r) : Set (P E m)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    show ∑ i, u i * r i ∈ Ideal.span (Set.range r)
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
    exact ⟨c, hc⟩

/-! ### Closed images in every degree ([FJP] Lemma 5.1 clause 2/3) -/

/-- **Every Koszul image is closed** ([FJP] Lemma 5.1 clause 2, closedness; clause 3 is
the `q = 0` case).  In positive degree `im d_{n+1} = ker d_n` is closed as the preimage of
`{0}` under the continuous differential `d_n` (`koszulGraph_restricted_exact` +
`koszulDifferential_continuous` + `T2`); the bottom image `im d_0 = J_E` is closed by
`isClosed_graphIdeal`, transported along the degree-`0` conjugation
`koszulDifferential_zero_eq_d1` and the set identity `range_d1`. -/
theorem isClosed_range_koszulDifferential [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (q : ℕ) :
    IsClosed (Set.range (koszulDifferential r q)) := by
  cases q with
  | zero =>
    have hcont0 : Continuous (koszulTermZeroEquiv (R := P E m) (m := m)) := by
      have hfun : (⇑(koszulTermZeroEquiv (R := P E m) (m := m))) =
          fun x => x ⟨∅, Finset.card_empty⟩ := funext koszulTermZeroEquiv_apply
      rw [hfun]
      exact continuous_apply _
    have hpre : Set.range (koszulDifferential r 0) =
        (koszulTermZeroEquiv (R := P E m) (m := m)) ⁻¹' Set.range (d1 r) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨koszulTermOneEquiv x, (koszulDifferential_zero_eq_d1 r x).symm⟩
      · rintro ⟨u, hu⟩
        refine ⟨koszulTermOneEquiv.symm u, ?_⟩
        apply (koszulTermZeroEquiv (R := P E m) (m := m)).injective
        rw [koszulDifferential_zero_eq_d1, LinearEquiv.apply_symm_apply]
        exact hu
    rw [hpre, range_d1]
    exact (isClosed_graphIdeal t htu ht1 ht0 hscale hE₀P r).preimage hcont0
  | succ n =>
    have hex := koszulGraph_restricted_exact hE₀ t htu ht1 ht0 hscale g f hunit r hr n
    have hpre : Set.range (koszulDifferential r (n + 1)) =
        (koszulDifferential r n) ⁻¹' {0} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (hex y).symm
    rw [hpre]
    exact isClosed_singleton.preimage (koszulDifferential_continuous r n)

/-! ### The all-degree controlled lift and strictness ([FJP] Lemma 5.1 clause 2) -/

/-- **The all-degree controlled lift** ([FJP] Lemma 5.1 clause 2, quantitative form): for
every `q` there is a constant `h ≥ 1` such that every element `y` of the closed image of
`koszulDifferential r q` lifts to some `u` with `‖u‖ ≤ h ‖y‖`.  Route: the
`tP`-equivariant additive differential has closed range (`isClosed_range_koszulDifferential`)
and continuous action, so the ultrametric open mapping theorem with constants
`exists_lift_norm_le_of_closed_range` applies. -/
theorem koszulDifferential_exists_lift [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (q : ℕ) :
    ∃ h : ℝ, 1 ≤ h ∧ ∀ y ∈ Set.range (koszulDifferential r q),
      ∃ u, koszulDifferential r q u = y ∧ ‖u‖ ≤ h * ‖y‖ := by
  set tP : P E m := polyToP (MvPolynomial.C t) with htP
  have htPu : IsUnit tP := isUnit_tP t htu
  have htP1 : ‖tP‖ < 1 := by rw [htP, norm_tP t hscale]; exact ht1
  have htP0 : 0 < ‖tP‖ := by rw [htP, norm_tP t hscale]; exact ht0
  have htPs : ∀ G : P E m, ‖tP * G‖ = ‖tP‖ * ‖G‖ := fun G => by
    rw [htP, norm_tP t hscale]; exact norm_tP_mul t hscale G
  have hequiv : ∀ u, (koszulDifferential r q).toAddMonoidHom (fun i => tP * u i) =
      fun k => tP * (koszulDifferential r q).toAddMonoidHom u k := by
    intro u
    show koszulDifferential r q (fun i => tP * u i) = fun k => tP * koszulDifferential r q u k
    have h1 : (fun i => tP * u i) = tP • u := funext fun i => (smul_eq_mul tP (u i)).symm
    rw [h1, map_smul]
    funext k
    show (tP • koszulDifferential r q u) k = tP * koszulDifferential r q u k
    rw [Pi.smul_apply, smul_eq_mul]
  have hclosed : IsClosed (Set.range (koszulDifferential r q).toAddMonoidHom) := by
    have heq : Set.range (koszulDifferential r q).toAddMonoidHom =
        Set.range (koszulDifferential r q) := rfl
    rw [heq]
    exact isClosed_range_koszulDifferential hE₀ t htu ht1 ht0 hscale hE₀P g f hunit r hr q
  obtain ⟨h, hh1, hlift⟩ := exists_lift_norm_le_of_closed_range htPu htP1 htP0 htPs
    (koszulDifferential r q).toAddMonoidHom (koszulDifferential_continuous r q) hequiv hclosed
  exact ⟨h, hh1, hlift⟩

/-- **Every differential is strict** ([FJP] Lemma 5.1 clause 2): the controlled lift
`koszulDifferential_exists_lift` feeds the bounded-lift strictness criterion
`isStrictLinearMap_of_lift`. -/
theorem koszulDifferential_isStrict [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (q : ℕ) :
    IsStrictLinearMap (koszulDifferential r q) := by
  obtain ⟨h, hh1, hlift⟩ :=
    koszulDifferential_exists_lift hE₀ t htu ht1 ht0 hscale hE₀P g f hunit r hr q
  exact isStrictLinearMap_of_lift (koszulDifferential r q) (lt_of_lt_of_le one_pos hh1) hlift

/-! ### The headline: exact, strict, closed in all degrees ([FJP] Lemma 5.1 clauses 1–3) -/

/-- **[FJP] Lemma 5.1, clauses 1–3**, for the graph datum over a noetherian Tate vertex
`E`: the graph Koszul complex over `P_E = E⟨T₁,…,T_m⟩` is (i) exact in every positive
degree, (ii) strict in every degree, and (iii) has closed image in every degree.  The
loss-of-precision inclusions (9)/(10) are the separate theorems `exists_d1_lift_pow`,
`pow_smul_graphIdeal_inter_unitBall_subset`, `exists_d2_lift_pow`,
`pow_smul_ker_d1_inter_subset` below (this theorem does not assert full Lemma 5.1). -/
theorem koszulGraph_exact_strict_closed [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    (∀ q, Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q)) ∧
      (∀ q, IsStrictLinearMap (koszulDifferential r q)) ∧
      (∀ q, IsClosed (Set.range (koszulDifferential r q))) :=
  ⟨fun q => koszulGraph_restricted_exact hE₀ t htu ht1 ht0 hscale g f hunit r hr q,
   fun q => koszulDifferential_isStrict hE₀ t htu ht1 ht0 hscale hE₀P g f hunit r hr q,
   fun q => isClosed_range_koszulDifferential hE₀ t htu ht1 ht0 hscale hE₀P g f hunit r hr q⟩

/-! ### Equation (9): the degree-1 loss-of-precision inclusion -/

/-- **Equation (9), ∃-`h` norm form** ([FJP] Lemma 5.1): there is `h ∈ ℕ` such that every
`x` in the graph ideal `J_E = (r₁,…,r_m)` with `‖x‖ ≤ 1` (i.e. `x ∈ P_{E,0}`) has an
integral lift `u ∈ P_{E,0}^m` of `ϖ^h x` — `d₁ u = tP^h x`, `‖u‖ ≤ 1`, where
`tP = polyToP (C t)` is the image of the pseudo-uniformizer.  Derived from the
strictness constant `C` of `exists_d1_lift` by choosing `h` with `‖t‖^h C < 1` and scaling
the lift.  This is about the *algebraic* image `J_E`, stated for an arbitrary sequence
`r`. -/
theorem exists_d1_lift_pow [IsNoetherianRing (P E m)]
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (r : Fin m → P E m) :
    ∃ h : ℕ, ∀ x ∈ Ideal.span (Set.range r), ‖x‖ ≤ 1 →
      ∃ u : Fin m → P E m, ‖u‖ ≤ 1 ∧ d1 r u = polyToP (MvPolynomial.C t) ^ h * x := by
  set tP : P E m := polyToP (MvPolynomial.C t) with htP
  obtain ⟨C, hC1, hlift⟩ := exists_d1_lift t htu ht1 ht0 hscale hE₀P r
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) ht1
  have htPs : ∀ G : P E m, ‖tP * G‖ = ‖tP‖ * ‖G‖ := fun G => by
    rw [htP, norm_tP t hscale]; exact norm_tP_mul t hscale G
  have htPn : ‖tP‖ = ‖t‖ := by rw [htP]; exact norm_tP t hscale
  refine ⟨h, fun x hx hx1 => ?_⟩
  have hmem : tP ^ h * x ∈ Ideal.span (Set.range r) := Ideal.mul_mem_left _ _ hx
  obtain ⟨u, hu, hun⟩ := hlift _ hmem
  refine ⟨u, ?_, hu⟩
  calc ‖u‖ ≤ C * ‖tP ^ h * x‖ := hun
    _ = C * (‖t‖ ^ h * ‖x‖) := by rw [norm_pow_mul_of_scale (E := P E m) htPs h x, htPn]
    _ ≤ C * (‖t‖ ^ h * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hCpos.le
        exact mul_le_mul_of_nonneg_left hx1 (pow_nonneg (norm_nonneg t) h)
    _ = ‖t‖ ^ h * C := by ring
    _ ≤ 1 := by
        have hlt : ‖t‖ ^ h * C < 1 := by
          have hmul := mul_lt_mul_of_pos_right hh hCpos
          rwa [inv_mul_cancel₀ (ne_of_gt hCpos)] at hmul
        linarith

/-- **Equation (9), lattice-inclusion form** ([FJP] Lemma 5.1): literally
`ϖ^h (J_E ∩ P_{E,0}) ⊆ d_{1,E}(P_{E,0}^m)`.  Here `P_{E,0} = {x | ‖x‖ ≤ 1}` is the unit
ball of `P_E` (via `mem_unitBall_iff`), `P_{E,0}^m = {u | ‖u‖ ≤ 1}` is the sup-norm unit
ball of `P_E^m`, `J_E = Ideal.span (Set.range r)`, and `ϖ = tP = polyToP (C t)`. -/
theorem pow_smul_graphIdeal_inter_unitBall_subset [IsNoetherianRing (P E m)]
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (r : Fin m → P E m) :
    ∃ h : ℕ, (fun x => polyToP (MvPolynomial.C t) ^ h * x) ''
        ((Ideal.span (Set.range r) : Set (P E m)) ∩ {x | ‖x‖ ≤ 1}) ⊆
      (fun u => d1 r u) '' {u : Fin m → P E m | ‖u‖ ≤ 1} := by
  obtain ⟨h, hh⟩ := exists_d1_lift_pow t htu ht1 ht0 hscale hE₀P r
  refine ⟨h, ?_⟩
  rintro _ ⟨x, ⟨hxJ, hx1⟩, rfl⟩
  obtain ⟨u, hu1, hud⟩ := hh x hxJ hx1
  exact ⟨u, hu1, hud⟩

/-! ### Equation (10): the degree-2 loss-of-precision inclusion -/

/-- **Equation (10), ∃-`z` norm form** ([FJP] Lemma 5.1, generic vertex `E`): there is
`z ∈ ℕ` such that every `u ∈ ker d₁ ∩ P_{E,0}^m` has an integral lift `v ∈ ⋀² P_{E,0}^m`
of `ϖ^z u` — `d₂ v = ϖ^z u`, `‖v‖ ≤ 1`, where `ϖ = tP = polyToP (C t)`.  Derived from the
strictness constant `C` of `exists_d2_lift` (whose kernel hypothesis `d₁ u = 0` is matched
verbatim) by choosing `z` with `‖t‖^z C < 1` and scaling.  Proved generically; downstream
[FJP] uses it at `E = D`. -/
theorem exists_d2_lift_pow [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    ∃ z : ℕ, ∀ u : Fin m → P E m, d1 r u = 0 → ‖u‖ ≤ 1 →
      ∃ v : Pairs m → P E m, ‖v‖ ≤ 1 ∧
        d2 r v = fun i => polyToP (MvPolynomial.C t) ^ z * u i := by
  set tP : P E m := polyToP (MvPolynomial.C t) with htP
  obtain ⟨C, hC1, hlift⟩ := exists_d2_lift hE₀ t htu ht1 ht0 hscale g f hunit r hr
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨z, hz⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) ht1
  have htPs : ∀ G : P E m, ‖tP * G‖ = ‖tP‖ * ‖G‖ := fun G => by
    rw [htP, norm_tP t hscale]; exact norm_tP_mul t hscale G
  have htPn : ‖tP‖ = ‖t‖ := by rw [htP]; exact norm_tP t hscale
  have htPzn : ‖(tP ^ z : P E m)‖ = ‖t‖ ^ z := by
    have h := norm_pow_mul_of_scale (E := P E m) htPs z 1
    rw [mul_one, norm_one, mul_one, htPn] at h
    exact h
  refine ⟨z, fun u hu hu1 => ?_⟩
  have hd1 : d1 r (fun i => tP ^ z * u i) = 0 := by
    have hstep : d1 r (fun i => tP ^ z * u i) = tP ^ z * d1 r u := by
      show ∑ i, tP ^ z * u i * r i = tP ^ z * ∑ i, u i * r i
      rw [show tP ^ z * ∑ i, u i * r i = ∑ i, tP ^ z * (u i * r i) from Finset.mul_sum _ _ _]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    rw [hstep, hu, mul_zero]
  obtain ⟨v, hv, hvn⟩ := hlift (fun i => tP ^ z * u i) hd1
  refine ⟨v, ?_, hv⟩
  have hc : ∀ x : P E m, ‖tP ^ z * x‖ = ‖tP ^ z‖ * ‖x‖ := fun x => by
    rw [norm_pow_mul_of_scale (E := P E m) htPs z x, htPzn, htPn]
  have hnorm : ‖(fun i => tP ^ z * u i)‖ = ‖t‖ ^ z * ‖u‖ := by
    rw [pi_norm_scale hc u, htPzn]
  calc ‖v‖ ≤ C * ‖(fun i => tP ^ z * u i)‖ := hvn
    _ = C * (‖t‖ ^ z * ‖u‖) := by rw [hnorm]
    _ ≤ C * (‖t‖ ^ z * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hCpos.le
        exact mul_le_mul_of_nonneg_left hu1 (pow_nonneg (norm_nonneg t) z)
    _ = ‖t‖ ^ z * C := by ring
    _ ≤ 1 := by
        have hlt : ‖t‖ ^ z * C < 1 := by
          have hmul := mul_lt_mul_of_pos_right hz hCpos
          rwa [inv_mul_cancel₀ (ne_of_gt hCpos)] at hmul
        linarith

/-- **Equation (10), lattice-inclusion form** ([FJP] Lemma 5.1, generic vertex `E`):
literally `ϖ^z (ker d_{1} ∩ P_{E,0}^m) ⊆ d_{2}(⋀² P_{E,0}^m)`.  Here `ker d₁ = {u | d₁ u = 0}`,
`P_{E,0}^m = {u | ‖u‖ ≤ 1}`, and the second exterior power `⋀² P_{E,0}^m` is modelled as
the sup-norm unit ball `{v : Pairs m → P E m | ‖v‖ ≤ 1}` of `P_E^{⊕binom m 2}` under the
campaign's ordered-pair `d₂` model; `ϖ = tP = polyToP (C t)`. -/
theorem pow_smul_ker_d1_inter_subset [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    ∃ z : ℕ, (fun u : Fin m → P E m => fun i => polyToP (MvPolynomial.C t) ^ z * u i) ''
        ({u : Fin m → P E m | d1 r u = 0} ∩ {u | ‖u‖ ≤ 1}) ⊆
      (fun v : Pairs m → P E m => d2 r v) '' {v | ‖v‖ ≤ 1} := by
  obtain ⟨z, hz⟩ := exists_d2_lift_pow hE₀ t htu ht1 ht0 hscale g f hunit r hr
  refine ⟨z, ?_⟩
  rintro _ ⟨u, ⟨hker, hu1⟩, rfl⟩
  obtain ⟨v, hv1, hvd⟩ := hz u hker hu1
  exact ⟨v, hv1, hvd⟩

end Restricted

end GraphKoszul

end FiniteJet
