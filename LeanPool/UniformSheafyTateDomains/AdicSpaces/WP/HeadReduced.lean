/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.CoeffLocalization
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Reduced
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Head-localization reducedness — the BGR 7.3.2/10 sub-campaign

Discharges the quarantined `HeadLocsReduced` hypothesis of the reducedness
endpoints: every rational localization of every affinoid head of the
weighted-parity algebra is reduced.  Classical source: [BGR, Corollary 7.3.2/10]
via completed-local comparison and analytic unramifiedness; the head-specific
route follows the 2026-07-28 plan review
(`.mathlib-quality/wp-reduced/chatgpt-review-2026-07-28.md` and
`hrw-decomposition.md`):

* `isReduced_of_forall_completedLocal_reduced` (L2, mathlib-grade): a noetherian
  ring whose completed local rings at all maximal ideals are reduced is reduced
  (Krull intersection + locality of vanishing);
* `headToQ` and `qHead_completedLocal_comparison` (L1): the completed local rings
  of the graph model `QHead` agree with those of the head at contracted primes
  (finite-level graph evaluation + inverse limits);
* `head_completedLocal_reduced` (L3, the frontier), split into the `W ∉ 𝔭`
  Z-elimination case (reduces to Tate-algebra completed locals) and the `W ∈ 𝔭`
  quadratic-tower case;
* `headLocsReduced` (L4): assembly through `headLocEquiv`.
-/

@[expose] public section


namespace WeightedParity

open ValuationSpectrum FiniteJetOver IsLocalRing

/-! ### L2 — reducedness from reduced completed local rings (mathlib-grade) -/

/-- The completed local ring of `R` at a prime `𝔭`: the maximal-adic completion of
the localization. -/
noncomputable abbrev completedLocal (R : Type*) [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] : Type _ :=
  AdicCompletion (maximalIdeal (Localization.AtPrime 𝔭)) (Localization.AtPrime 𝔭)

/-- **L2**: a noetherian commutative ring whose completed local rings at all maximal
ideals are reduced is reduced ([hrw-decomposition] L2: Krull intersection makes
`R_𝔪 → (R_𝔪)^` injective; vanishing at all maximal localizations is vanishing). -/
theorem isReduced_of_forall_completedLocal_reduced (R : Type*) [CommRing R]
    [IsNoetherianRing R]
    (h : ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal), IsReduced (completedLocal R 𝔪)) :
    IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  have hloc : ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
      algebraMap R (Localization.AtPrime 𝔪) x = 0 := by
    intro 𝔪 h𝔪
    haveI := h𝔪
    haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
      IsLocalization.isNoetherianRing 𝔪.primeCompl (Localization.AtPrime 𝔪)
        inferInstance
    set L := Localization.AtPrime 𝔪 with hL
    set I : Ideal L := maximalIdeal L with hI
    set y : L := algebraMap R L x with hy_def
    have hy : IsNilpotent y := hx.map (algebraMap R L)
    have hz : IsNilpotent (algebraMap L (AdicCompletion I L) y) :=
      hy.map (algebraMap L (AdicCompletion I L))
    haveI := h 𝔪 h𝔪
    have hz0 : algebraMap L (AdicCompletion I L) y = 0 := hz.eq_zero
    have hmem : y ∈ (⊥ : Submodule L L) := by
      rw [← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := I) (M := L)
        (IsLocalRing.maximalIdeal.isMaximal L).ne_top]
      rw [Submodule.mem_iInf]
      intro n
      have hev := congrArg (AdicCompletion.eval I L n) hz0
      rw [show algebraMap L (AdicCompletion I L) y = AdicCompletion.of I L y from rfl,
        AdicCompletion.eval_of, map_zero] at hev
      exact (Submodule.Quotient.mk_eq_zero _).mp hev
    simpa using hmem
  have hbot : x ∈ (⊥ : Ideal R) := by
    refine Ideal.mem_of_localization_maximal fun P hP => ?_
    rw [Ideal.map_bot, Ideal.mem_bot]
    exact hloc P hP
  simpa using hbot

/-! ### L1 — the completed-local comparison for the graph model -/

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

variable {K w N} in
/-- The canonical homomorphism from the head into its graph model (constants into
`𝒜_N⟨T⟩`, then the quotient). -/
noncomputable def headToQ (DH : RationalLocData (WPHead K w N)) :
    WPHead K w N →+* QHead DH :=
  (Ideal.Quotient.mk _).comp
    ((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N) (m := DH.T.card)).comp
      MvPolynomial.C)

variable {K w} in
/-- **HRW-5(i)**: weight monotonicity of the head support — the zero-weight head
is the FULL restricted Tate algebra `K⟨W, U_{≤N}⟩`, and every weighted head sits
inside it as a subring ([hrw-decomposition] "subring-coding simplification":
the paper's finite embedding `Y_i ↦ W^{wᵢ}U_i, Z_i ↦ U_i²` is, in the ambient
support coding, literally this inclusion). -/
theorem wpHeadSupport_le_zero_weight (N : ℕ) :
    wpHeadSupport K w N ≤ wpHeadSupport K (fun _ => 0) N := by
  intro f hf t ht
  refine hf t fun hh => ht ⟨?_, hh.2⟩
  show WPMem (fun _ => 0) t
  simp [WPMem, wpWeight]

/-! ### HRW-5(ii) — the parity module decomposition of the zero-weight head

`K⟨W,U⟩ = ⊕_{E ⊆ {1,…,N}} 𝒜_N·U^E` ([WP] lem:finite-stage-normal-form at both
weights; [hrw-decomposition] "subring-coding simplification"): the zero-weight
head is module-finite over every weighted head through the square-free parity
monomials.  This is the finiteness half of the semilocal reduction. -/

section ParityDecomposition

variable {K w} (N : ℕ)

/-- The square-free exponent of a parity pattern `E ⊆ {1,…,N}`. -/
noncomputable def parityExp (E : Finset ℕ) : ℕ →₀ ℕ :=
  Finsupp.indicator E fun _ _ => 1

theorem parityExp_apply (E : Finset ℕ) (n : ℕ) :
    parityExp E n = if n ∈ E then 1 else 0 := by
  classical
  rw [parityExp, Finsupp.indicator_apply]
  split_ifs <;> rfl

/-- The square-free parity monomial `U^E` in the zero-weight head. -/
noncomputable def parityMonomialZ (E : Finset ℕ)
    (hE : E ⊆ Finset.Icc 1 N) : WPHead K (fun _ => 0) N :=
  ⟨⟨MvPowerSeries.monomial (parityExp E) (1 : K),
      MvPowerSeries.isRestrictedGauss_monomial _ _ _⟩, fun t ht => by
    show MvPowerSeries.coeff t
      (MvPowerSeries.monomial (parityExp E) (1 : K)) = 0
    classical
    rw [MvPowerSeries.coeff_monomial, if_neg]
    rintro rfl
    refine ht ⟨by simp [WPMem, wpWeight], fun n hn => ?_⟩
    rw [parityExp_apply, if_neg]
    intro hnE
    exact absurd (Finset.mem_Icc.mp (hE hnE)).2 (by omega)⟩

/-- The `E`-slice of a zero-weight head element: the even-off-`0` coefficients
shifted by the parity exponent, as a weighted-head element (even exponents have
parity weight zero). -/
noncomputable def paritySlice (E : Finset ℕ)
    (q : WPHead K (fun _ => 0) N) : WPHead K w N := by
  classical
  refine ⟨⟨(fun s : ℕ →₀ ℕ =>
    if (∀ n, n ≠ 0 → s n % 2 = 0) ∧ (∀ n, N < n → s n = 0) then
      MvPowerSeries.coeff (s + parityExp E) q.1.1 else 0 :
      MvPowerSeries ℕ K), ?_⟩, ?_⟩
  · -- restrictedness: a dominated, injectively reindexed subfamily
    have hw1 : ∀ u : ℕ →₀ ℕ, (u.prod fun _ e => (1 : ℝ) ^ e) = 1 := fun u => by
      simp [Finsupp.prod]
    have hq2 : Filter.Tendsto (fun t : ℕ →₀ ℕ =>
        ‖MvPowerSeries.coeff t q.1.1‖ * t.prod fun _ e => (1 : ℝ) ^ e)
        Filter.cofinite (nhds 0) := q.1.2
    have hinj : Function.Injective (fun s : ℕ →₀ ℕ => s + parityExp E) :=
      fun s₁ s₂ h => by simpa using congrArg (fun u => u - parityExp E) h
    have hcomp := hq2.comp hinj.tendsto_cofinite
    show Filter.Tendsto _ Filter.cofinite (nhds 0)
    refine squeeze_zero
      (fun s => mul_nonneg (norm_nonneg _) (by rw [hw1 s]; norm_num))
      (fun s => ?_) hcomp
    show ‖(if (∀ n, n ≠ 0 → s n % 2 = 0) ∧ (∀ n, N < n → s n = 0) then
        MvPowerSeries.coeff (s + parityExp E) q.1.1 else 0 : K)‖ *
        (s.prod fun _ e => (1 : ℝ) ^ e) ≤
      ‖MvPowerSeries.coeff (s + parityExp E) q.1.1‖ *
        ((s + parityExp E).prod fun _ e => (1 : ℝ) ^ e)
    rw [hw1, hw1, mul_one, mul_one]
    split_ifs with hcond
    · exact le_of_eq rfl
    · simp
  · -- head support at the weight `w`
    intro t ht
    show (if (∀ n, n ≠ 0 → t n % 2 = 0) ∧ (∀ n, N < n → t n = 0) then
      MvPowerSeries.coeff (t + parityExp E) q.1.1 else 0) = 0
    rw [if_neg]
    rintro ⟨heven, hbdd⟩
    refine ht ⟨?_, fun n hn => hbdd n hn⟩
    show wpWeight w t ≤ t 0
    rw [wpWeight_eq_zero_of_even heven]
    omega

open scoped Classical in
/-- The double-projection to the ambient series ring, as a ring hom (the
`Restricted`/support subtype coercions are definitionally transparent). -/
def headSeries : WPHead K (fun _ => 0) N →+* MvPowerSeries ℕ K where
  toFun x := x.1.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

open scoped Classical in
/-- **The parity reconstruction** ([WP] lem:finite-stage-normal-form): every
zero-weight head element is the sum, over square-free parity patterns, of its
slices (weighted-head elements) times the parity monomials. -/
theorem parity_decomposition (q : WPHead K (fun _ => 0) N) :
    q = ∑ E ∈ (Finset.Icc 1 N).powerset.attach,
      Subring.inclusion (wpHeadSupport_le_zero_weight (K := K) (w := w) N)
          (paritySlice N E.1 q) *
        parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2) := by
  classical
  have hser : Function.Injective (headSeries (K := K) N) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  refine hser ?_
  rw [map_sum (headSeries (K := K) N)]
  refine MvPowerSeries.ext fun t => ?_
  rw [map_sum (MvPowerSeries.coeff t)]
  have hterm : ∀ E ∈ (Finset.Icc 1 N).powerset.attach,
      MvPowerSeries.coeff t (headSeries (K := K) N
        (Subring.inclusion
            (wpHeadSupport_le_zero_weight (K := K) (w := w) N)
              (paritySlice N E.1 q) *
          parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2))) =
      (if parityExp E.1 ≤ t ∧
          (∀ n, n ≠ 0 → (t - parityExp E.1) n % 2 = 0) ∧
          (∀ n, N < n → (t - parityExp E.1) n = 0) then 1 else 0) *
        MvPowerSeries.coeff t q.1.1 := by
    intro E _
    have hmul : headSeries (K := K) N
        (Subring.inclusion
            (wpHeadSupport_le_zero_weight (K := K) (w := w) N)
              (paritySlice N E.1 q) *
          parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2)) =
        (paritySlice (w := w) N E.1 q).1.1 *
          MvPowerSeries.monomial (parityExp E.1) (1 : K) := rfl
    rw [hmul, MvPowerSeries.coeff_mul_monomial]
    by_cases hle : parityExp E.1 ≤ t
    · rw [if_pos hle]
      have hsl : MvPowerSeries.coeff (t - parityExp E.1)
          (paritySlice (w := w) N E.1 q).1.1 =
          if (∀ n, n ≠ 0 → (t - parityExp E.1) n % 2 = 0) ∧
             (∀ n, N < n → (t - parityExp E.1) n = 0) then
            MvPowerSeries.coeff t q.1.1 else 0 := by
        show (if (∀ n, n ≠ 0 → (t - parityExp E.1) n % 2 = 0) ∧
            (∀ n, N < n → (t - parityExp E.1) n = 0) then
          MvPowerSeries.coeff ((t - parityExp E.1) + parityExp E.1) q.1.1
          else 0) = _
        rw [tsub_add_cancel_of_le hle]
      rw [hsl, mul_one]
      by_cases hcond : (∀ n, n ≠ 0 → (t - parityExp E.1) n % 2 = 0) ∧
          (∀ n, N < n → (t - parityExp E.1) n = 0)
      · rw [if_pos hcond, if_pos ⟨hle, hcond⟩, one_mul]
      · rw [if_neg hcond, if_neg (by tauto), zero_mul]
    · rw [if_neg hle, if_neg (by tauto), zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  show MvPowerSeries.coeff t q.1.1 = _
  by_cases hq0 : MvPowerSeries.coeff t q.1.1 = 0
  · rw [hq0, mul_zero]
  · have hhead : HeadMem (fun _ => 0) N t := by
      by_contra hc
      exact hq0 (q.2 t hc)
    set Et : Finset ℕ :=
      t.support.filter (fun n => n ≠ 0 ∧ t n % 2 = 1) with hEt
    have hmemEt : ∀ n, n ∈ Et ↔ (t n ≠ 0 ∧ n ≠ 0 ∧ t n % 2 = 1) := by
      intro n
      rw [hEt, Finset.mem_filter, Finsupp.mem_support_iff]
    have hEtIcc : Et ∈ (Finset.Icc 1 N).powerset := by
      rw [Finset.mem_powerset]
      intro n hn
      obtain ⟨hne, hn0, -⟩ := (hmemEt n).mp hn
      refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      by_contra hgt
      exact hne (hhead.2 n (by omega))
    rw [Finset.sum_eq_single_of_mem (⟨Et, hEtIcc⟩ :
        {x // x ∈ (Finset.Icc 1 N).powerset}) (Finset.mem_attach _ _)]
    · rw [if_pos, one_mul]
      refine ⟨?_, ?_, ?_⟩
      · intro n
        rw [parityExp_apply]
        split_ifs with hn
        · have := ((hmemEt n).mp hn).2.2
          omega
        · omega
      · intro n hn0
        rw [Finsupp.tsub_apply, parityExp_apply]
        by_cases hmem : n ∈ Et
        · rw [if_pos hmem]
          have := ((hmemEt n).mp hmem).2.2
          omega
        · rw [if_neg hmem]
          have hcon : ¬ (t n ≠ 0 ∧ n ≠ 0 ∧ t n % 2 = 1) :=
            fun hc => hmem ((hmemEt n).mpr hc)
          push_neg at hcon
          rcases eq_or_ne (t n) 0 with h0 | h0
          · omega
          · have := hcon h0 hn0
            omega
      · intro n hn
        rw [Finsupp.tsub_apply, parityExp_apply, hhead.2 n hn,
          if_neg (fun hmem => ((hmemEt n).mp hmem).1 (hhead.2 n hn))]
    · rintro ⟨E, hE⟩ - hne
      rw [if_neg]
      rintro ⟨hle, heven, -⟩
      refine hne (Subtype.ext ?_)
      show E = Et
      refine Finset.ext fun n => ?_
      constructor
      · intro hnE
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp
          (Finset.mem_powerset.mp hE hnE)).1
        have hεn : parityExp E n = 1 := by
          rw [parityExp_apply, if_pos hnE]
        have htn : 1 ≤ t n := le_trans (le_of_eq hεn.symm) (hle n)
        have hpar := heven n (by omega)
        rw [Finsupp.tsub_apply, hεn] at hpar
        exact (hmemEt n).mpr ⟨by omega, by omega, by omega⟩
      · intro hnEt
        obtain ⟨hne0, hn0, hodd⟩ := (hmemEt n).mp hnEt
        by_contra hnE
        have hpar := heven n hn0
        rw [Finsupp.tsub_apply, parityExp_apply, if_neg hnE] at hpar
        omega

open scoped Classical in
/-- **HRW-5(ii)**: the zero-weight head (the full Tate algebra `K⟨W,U_{≤N}⟩`)
is module-finite over the weighted head through the inclusion, generated by
the square-free parity monomials. -/
theorem module_finite_zero_head :
    letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
      (Subring.inclusion
        (wpHeadSupport_le_zero_weight (K := K) (w := w) N)).toAlgebra
    Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (Subring.inclusion
      (wpHeadSupport_le_zero_weight (K := K) (w := w) N)).toAlgebra
  refine ⟨⟨(Finset.Icc 1 N).powerset.attach.image
    (fun E => parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2)), ?_⟩⟩
  rw [eq_top_iff]
  intro q _
  rw [parity_decomposition (w := w) N q]
  refine Submodule.sum_mem _ fun E hE => ?_
  have hsmul : Subring.inclusion
      (wpHeadSupport_le_zero_weight (K := K) (w := w) N)
        (paritySlice N E.1 q) *
      parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2) =
      paritySlice N E.1 q •
        parityMonomialZ N E.1 (Finset.mem_powerset.mp E.2) :=
    (Algebra.smul_def _ _).symm
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE)))

end ParityDecomposition

variable {K w N} in
/-- `headToQ` is the model's constant embedding (definitional identification with
the W15 layer). -/
theorem headToQ_eq_headConst (DH : RationalLocData (WPHead K w N)) :
    headToQ DH = headConst DH := rfl

variable {K w N} in
/-- **L1.a** ([hrw-decomposition], HRW-2): the denominator's image in the graph
model is a unit — the canonical-map unit transported along `headLocEquiv`
(the W16 law `headLocEquiv ∘ canonicalMap = headConst`). -/
theorem isUnit_headToQ_s (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    IsUnit (headToQ DH DH.s) := by
  haveI : HasLocLiftPowerBounded (WPHead K w N) := hasLocLiftPowerBounded_faithful
  have h1 : headToQ DH DH.s =
      headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap DH.s) := by
    rw [show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap DH.s) =
      headLocFwd ϖ DH hDH (DH.canonicalMap DH.s) from rfl,
      show DH.canonicalMap DH.s = DH.coeRingHom
        (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) from rfl,
      headLocFwd_coe, headLocFwdAlg_algebraMap]
    rfl
  rw [h1]
  exact (isUnit_canonicalMap_s DH DH (subset_refl _)).map
    (headLocEquiv ϖ hK₀ DH hDH)

variable {K w N} in
/-- **L1.a** (HRW-2): the denominator avoids the contraction of every proper
prime of the graph model — the fibre of the contraction lies in the localization
locus (the adversarial-note-safe primality form; maximality of the contraction
is deliberately NOT claimed). -/
theorem s_notMem_comap_headToQ (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsPrime) :
    DH.s ∉ 𝔮.comap (headToQ DH) := by
  intro hmem
  rw [Ideal.mem_comap] at hmem
  exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    (isUnit_headToQ_s ϖ hK₀ DH hDH))

variable {K w N} in
/-- **L1** ([hrw-decomposition]): for a maximal ideal `𝔮` of the graph model, the
completed local ring of the head at the contraction agrees with that of the model
at `𝔮`.  (Finite-level: mod every power of `𝔮` the graph variables evaluate
uniquely since the denominator is a unit; then pass to inverse limits.) -/
theorem qHead_completedLocal_comparison (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    haveI : (𝔮.comap (headToQ DH)).IsPrime := 𝔮.comap_isPrime (headToQ DH)
    Nonempty
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH)) ≃+*
        completedLocal (QHead DH) 𝔮) := by sorry

/-! ### L3 — reducedness of the head's completed local rings (the frontier) -/

variable {K w N} in
/-- **L3.a** (`W` invertible — the smooth chart): after inverting `W` the `Z`'s are
eliminated (`Z_i = W^{−2wᵢ}Y_i²`) and the head agrees with the full Tate algebra
`K⟨W, U_{≤N}⟩`; its completed local rings are reduced (classical Tate-algebra
regularity — its own sub-decomposition when reached). -/
theorem head_completedLocal_reduced_of_wa_notMem (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) (hW : WaHead K w N ∉ 𝔭) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by sorry

variable {K w N} in
/-- **L3.b** (`W ∈ 𝔭` — the singular point): all `Y_i ∈ 𝔭`, and the completed
quadratic tower must be analyzed through the formal relations directly
(characteristic-free; the deepest leaf of the campaign — see
[hrw-decomposition] L3.b for the planned Φ-style formal-domain embedding). -/
theorem head_completedLocal_reduced_of_wa_mem (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) (hW : WaHead K w N ∈ 𝔭) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by sorry

variable {K w N} in
/-- **L3**: every completed local ring of the head at a prime is reduced. -/
theorem head_completedLocal_reduced (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  by_cases hW : WaHead K w N ∈ 𝔭
  · exact head_completedLocal_reduced_of_wa_mem ϖ hK₀ 𝔭 h𝔭 hW
  · exact head_completedLocal_reduced_of_wa_notMem ϖ hK₀ 𝔭 h𝔭 hW

/-! ### L4 — assembly -/

variable {K w} in
/-- L4-prep: the graph model is noetherian (transport of the faithful
strongly-noetherian localization along `headLocEquiv`). -/
theorem isNoetherianRing_qHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) {N : ℕ}
    {DH : RationalLocData (WPHead K w N)} (hDH : DH.IsRational) :
    IsNoetherianRing (QHead DH) := by
  haveI := isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  haveI : IsNoetherianRing (WPHead K w N) :=
    IsStronglyNoetherian.isNoetherianRing (WPHead K w N)
  haveI : IsNoetherianRing (presheafValue DH) :=
    presheafValue_isNoetherianRing_faithful DH
  exact isNoetherianRing_of_surjective (presheafValue DH) (QHead DH)
    (headLocEquiv ϖ hK₀ DH hDH).toRingHom
    (headLocEquiv ϖ hK₀ DH hDH).surjective

variable {K} in
theorem headLocsReduced (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    HeadLocsReduced K w := by
  intro N DH hDH
  haveI hQnoeth : IsNoetherianRing (QHead DH) :=
    isNoetherianRing_qHead ϖ hK₀ hDH
  suffices h : IsReduced (QHead DH) by
    exact isReduced_of_injective
      (headLocEquiv ϖ hK₀ DH hDH).toRingHom
      (headLocEquiv ϖ hK₀ DH hDH).injective
  refine isReduced_of_forall_completedLocal_reduced _ ?_
  intro 𝔮 h𝔮
  haveI := h𝔮.isPrime
  haveI hcp : (𝔮.comap (headToQ DH)).IsPrime :=
    𝔮.comap_isPrime (headToQ DH)
  obtain ⟨e⟩ := qHead_completedLocal_comparison ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI : IsReduced
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH))) :=
    head_completedLocal_reduced ϖ hK₀ _ hcp
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end WeightedParity
