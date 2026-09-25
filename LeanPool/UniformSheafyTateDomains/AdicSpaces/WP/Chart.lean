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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.CoeffLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Reduced
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetChart

/-!
# The bad chart `ℬ = 𝒜⟨W/ϖ⟩` ([WP] §6.2)

The chart datum is `(W; ϖ)` — a genuine rational datum since `ϖ` is a unit
([WP] line 838).  Its entries lie in the `N = 0` head `𝒜_0 = K⟨W⟩`, so the chart is
the `N = 0` instance of the coefficientwise localization: `ℬ ≅ TailC0` over the head
localization `Q₀ = K⟨W⟩⟨X⟩/(ϖX − W) ≅ K⟨X⟩` with twist element `ρ = ϖX`.  In these
twisted coordinates the paper's weighted model ([WP] eq:weighted-chart-lattice /
eq:weighted-chart-norm) is EXACTLY the plain sup-norm `TailC0` — e.g.
`T_n = X^n U_n = ϖ^{−w n}·e_{δ_n}` is the single family with coefficient `ϖ^{−w n}`,
of norm `|ϖ|^{−w n}` (eq:Tn-power-norms).

Endpoints here ([WP] prop:weighted-chart-identification,
prop:weighted-chart-domain-nonuniform, prop-analogue of not-stable-uniformity):
`ℬ` is an integral domain (via the `Φ`-embedding into `MvPowerSeries` over the
domain `K⟨X⟩` — no classical input needed), `ℬ` is NOT uniform (the unbounded
power-bounded family `(T_n)`, needs the weight unbounded), and hence `𝒜` is not
stably uniform ([WP] thm 6.2 (4)).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver TopologicalRing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
open scoped Classical in
/-- The span of the chart pair is the unit ideal (`ϖ` is a unit; [WP] line 838:
"It is a genuine rational datum: the ideal `(ϖ,W)` is open"). -/
theorem span_chartPair_eq_top (ϖ : Uniformizer K) :
    Ideal.span (({WaHead K w 0, piHead ϖ} : Finset (WPHead K w 0)) :
      Set (WPHead K w 0)) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ?_) (isUnit_piHead ϖ)
  rw [Finset.coe_insert, Finset.coe_singleton]
  exact Set.mem_insert_of_mem _ rfl

variable {K w} in
open scoped Classical in
/-- The head chart datum `(W; ϖ)` on the `N = 0` head `K⟨W⟩`
([WP] §6.2: "the datum `(W;ϖ)`"; project convention `s ∈ T`). -/
noncomputable def chartHeadDatum (ϖ : Uniformizer K) :
    RationalLocData (WPHead K w 0) :=
  genPieceDatum
    (FiniteJet.unitBallPod (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
      (norm_piHead_pos ϖ) (norm_piHead_mul ϖ))
    {WaHead K w 0, piHead ϖ} (piHead ϖ) (span_chartPair_eq_top ϖ)

variable {K w} in
open scoped Classical in
theorem chartHeadDatum_T (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).T = {WaHead K w 0, piHead ϖ} := rfl

variable {K w} in
theorem chartHeadDatum_s (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).s = piHead ϖ := rfl

variable {K w} in
/-- The chart datum is rational (`ϖ` is a unit, so `span {W, ϖ} = ⊤`;
[WP]: "It is a genuine rational datum: the ideal `(ϖ,W)` is open"). -/
theorem chartHeadDatum_isRational (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).IsRational := by
  classical
  refine RationalLocData.isRational_of_span_eq_top ?_
  rw [chartHeadDatum_T]
  exact span_chartPair_eq_top ϖ

variable {K w} in
/-- The chart datum on `𝒜` — the lift of the head chart datum
(entries `W, ϖ`; [WP] §6.2). -/
noncomputable def chartDatum (ϖ : Uniformizer K) : RationalLocData (WPA K w) :=
  liftDatum (chartHeadDatum ϖ) (chartHeadDatum_isRational ϖ)

variable {K w} in
theorem chartDatum_isRational (ϖ : Uniformizer K) :
    (chartDatum (w := w) ϖ).IsRational :=
  liftDatum_isRational _ (chartHeadDatum_isRational ϖ)

/-! ### The chart head localization is `K⟨X⟩` -/

variable {K w} in
/-- At stage `0` the head support IS the even support (no odd generators, so the
evenness condition is vacuous). -/
theorem wpHeadSupport_zero_eq_even :
    wpHeadSupport K w 0 = wpEvenSupport K w 0 := by
  refine SetLike.ext fun f => ?_
  constructor
  · intro hf
    have hf' : ∀ t : ℕ →₀ ℕ, ¬ HeadMem w 0 t →
        MvPowerSeries.coeff t f.1 = 0 := hf
    show ∀ t : ℕ →₀ ℕ, ¬ EvenHeadMem w 0 t → MvPowerSeries.coeff t f.1 = 0
    intro t ht
    refine hf' t fun hh => ht ⟨hh, fun n hn => by
      rw [hh.2 n (Nat.pos_of_ne_zero hn)]⟩
  · intro hf
    have hf' : ∀ t : ℕ →₀ ℕ, ¬ EvenHeadMem w 0 t →
        MvPowerSeries.coeff t f.1 = 0 := hf
    show ∀ t : ℕ →₀ ℕ, ¬ HeadMem w 0 t → MvPowerSeries.coeff t f.1 = 0
    intro t ht
    exact hf' t fun he => ht he.1

variable {K w} in
/-- The `N = 0` head is the one-variable Tate algebra (`evenSupportEquiv` at the
degenerate stage). -/
noncomputable def headZeroEquiv : WPHead K w 0 ≃+* FiniteJet.GraphKoszul.P K 1 :=
  (RingEquiv.subringCongr (wpHeadSupport_zero_eq_even (K := K) (w := w))).trans
    (evenSupportEquiv K w 0)

variable {K w} in
theorem norm_headZeroEquiv (x : WPHead K w 0) :
    ‖headZeroEquiv (K := K) (w := w) x‖ = ‖x‖ := by
  rw [headZeroEquiv, RingEquiv.trans_apply, norm_evenSupportEquiv]
  rfl

variable {K} in
/-- `K⟨X⟩` is an integral domain (multiplicative Gauss norm). -/
theorem isDomain_P_one : IsDomain (FiniteJet.GraphKoszul.P K 1) := by
  have hmul : ∀ f g : FiniteJet.GraphKoszul.P K 1, ‖f * g‖ = ‖f‖ * ‖g‖ :=
    fun f g => norm_restricted_mul_general (fun a b => norm_mul a b) f g
  haveI : Nontrivial (FiniteJet.GraphKoszul.P K 1) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun z : FiniteJet.GraphKoszul.P K 1 => ‖z‖) h
    rw [show ‖(0 : FiniteJet.GraphKoszul.P K 1)‖ = 0 from norm_zero,
      show ‖(1 : FiniteJet.GraphKoszul.P K 1)‖ = 1 from norm_one] at h1
    linarith
  haveI : NoZeroDivisors (FiniteJet.GraphKoszul.P K 1) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hcon
    push_neg at hcon
    have h1 : ‖a * b‖ = 0 := by rw [hab, norm_zero]
    rw [hmul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact hcon.1 (norm_eq_zero.mp h)
    · exact hcon.2 (norm_eq_zero.mp h)
  exact NoZeroDivisors.to_isDomain _

variable {K w} in
theorem WaHead_ne_piHead (ϖ : Uniformizer K) :
    WaHead K w 0 ≠ piHead (w := w) (N := 0) ϖ := by
  intro h
  have h1 := congrArg (fun z : WPHead K w 0 => ‖z‖) h
  rw [show ‖WaHead K w 0‖ = 1 from norm_WaHead,
    show ‖piHead (w := w) (N := 0) ϖ‖ = ‖ϖ.val‖ from norm_piHead ϖ] at h1
  have h2 := ϖ.norm_val_lt_one
  rw [← h1] at h2
  exact lt_irrefl 1 h2

variable {K w} in
/-- `headZeroEquiv` sends the head variable `W` to the Tate variable `X`. -/
theorem headZeroEquiv_WaHead :
    headZeroEquiv (K := K) (w := w) (WaHead K w 0) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0) := by
  classical
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  rw [FiniteJet.GraphKoszul.coeff_polyToP]
  show MvPowerSeries.coeff (unhalve 0 s)
      (MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K)) =
    MvPolynomial.coeff s (MvPolynomial.X 0)
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_X']
  have hiff : unhalve 0 s = Finsupp.single 0 1 ↔ Finsupp.single 0 1 = s := by
    constructor
    · intro h
      have h0 : s 0 = 1 := by
        have h2 := congrArg (fun u : ℕ →₀ ℕ => u 0) h
        rwa [unhalve_apply, if_pos rfl, Finsupp.single_apply, if_pos rfl] at h2
      refine (Finsupp.ext fun i => ?_).symm
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [h0, Finsupp.single_apply, if_pos rfl]
    · intro h
      rw [← h]
      refine Finsupp.ext fun n => ?_
      rw [unhalve_apply]
      rcases eq_or_ne n 0 with rfl | hn
      · rw [if_pos rfl, Finsupp.single_apply, if_pos rfl,
          Finsupp.single_apply, if_pos rfl]
      · rw [if_neg hn, dif_neg (by omega), Finsupp.single_apply,
          if_neg fun hc => hn hc.symm]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

variable {K w} in
/-- `headZeroEquiv` fixes constants. -/
theorem headZeroEquiv_constHead (x : K) :
    headZeroEquiv (K := K) (w := w) (constHead K w 0 x) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C x) := by
  classical
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  rw [FiniteJet.GraphKoszul.coeff_polyToP]
  show MvPowerSeries.coeff (unhalve 0 s) (MvPowerSeries.C (σ := ℕ) x) =
    MvPolynomial.coeff s (MvPolynomial.C x)
  rw [MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
  have hiff : unhalve 0 s = 0 ↔ s = 0 := by
    constructor
    · intro h
      have h0 : s 0 = 0 := by
        have h2 := congrArg (fun u : ℕ →₀ ℕ => u 0) h
        rwa [unhalve_apply, if_pos rfl, Finsupp.zero_apply] at h2
      refine Finsupp.ext fun i => ?_
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [Finsupp.zero_apply]
      exact h0
    · intro h
      rw [h]
      refine Finsupp.ext fun n => ?_
      rw [unhalve_apply]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [if_neg hn]
        split_ifs with h1
        · simp
        · simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) (fun hc => h2 hc.symm)
  · exact absurd (hiff.mpr h2.symm) h1
  · rfl

variable {K w} in
theorem headZeroEquiv_continuous :
    Continuous (headZeroEquiv (K := K) (w := w)) :=
  AddMonoidHomClass.continuous_of_bound (headZeroEquiv (K := K) (w := w)) 1
    fun x => by rw [one_mul]; exact le_of_eq (norm_headZeroEquiv x)

variable {K w} in
theorem headZeroEquiv_symm_continuous :
    Continuous (headZeroEquiv (K := K) (w := w)).symm :=
  AddMonoidHomClass.continuous_of_bound (headZeroEquiv (K := K) (w := w)).symm 1
    fun y => by
      rw [one_mul]
      refine le_of_eq ?_
      rw [← norm_headZeroEquiv ((headZeroEquiv (K := K) (w := w)).symm y),
        RingEquiv.apply_symm_apply]

variable {K} in
theorem norm_polyToP_X1 :
    ‖(FiniteJet.GraphKoszul.polyToP (MvPolynomial.X (0 : Fin 1)) :
      FiniteJet.GraphKoszul.P K 1)‖ = 1 := by
  rw [← headZeroEquiv_WaHead (K := K) (w := fun _ => 0), norm_headZeroEquiv]
  exact norm_WaHead

variable {K} in
/-- The `X ↦ ϖX` rescaling of `K⟨X⟩` (a `restrictedEval` instance at the
power-bounded tuple `(ϖX)`; [WP] §6.2's `W ↦ ϖX` normalization). -/
noncomputable def chartRescale (ϖ : Uniformizer K) :
    FiniteJet.GraphKoszul.P K 1 →+* FiniteJet.GraphKoszul.P K 1 :=
  restrictedEval
    ((FiniteJet.GraphKoszul.polyToP).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin 1) K))
    (AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
      rw [one_mul, RingHom.comp_apply]
      exact le_of_eq
        (FiniteJet.GraphKoszul.norm_tP x fun y => norm_mul x y))
    (fun _ : Fin 1 => FiniteJet.GraphKoszul.polyToP
      (MvPolynomial.C ϖ.val * MvPolynomial.X 0))
    (fun _ => FiniteJet.isPowerBounded_of_norm_le_one (by
      rw [map_mul, FiniteJet.GraphKoszul.norm_tP_mul ϖ.val
        (fun y => norm_mul ϖ.val y), norm_polyToP_X1 (K := K), mul_one]
      exact ϖ.norm_val_lt_one.le))

variable {K} in
theorem chartRescale_C (ϖ : Uniformizer K) (x : K) :
    chartRescale (K := K) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C x)) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C x) :=
  restrictedEval_C _ _ _ _ x

variable {K} in
theorem chartRescale_X (ϖ : Uniformizer K) :
    chartRescale (K := K) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0)) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C ϖ.val * MvPolynomial.X 0) :=
  restrictedEval_X _ _ _ _ 0

variable {K} in
theorem chartRescale_continuous (ϖ : Uniformizer K) :
    Continuous (chartRescale (K := K) ϖ) :=
  restrictedEval_continuous _ _ _ _

variable {K w} in
/-- The coefficient hom of the chart model: `K⟨W⟩ → K⟨X⟩`, `W ↦ ϖX`. -/
noncomputable def chartCoeff (ϖ : Uniformizer K) :
    WPHead K w 0 →+* FiniteJet.GraphKoszul.P K 1 :=
  (chartRescale (K := K) ϖ).comp
    (headZeroEquiv (K := K) (w := w)).toRingHom

variable {K w} in
theorem chartCoeff_WaHead (ϖ : Uniformizer K) :
    chartCoeff (K := K) (w := w) ϖ (WaHead K w 0) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C ϖ.val * MvPolynomial.X 0) := by
  rw [chartCoeff, RingHom.comp_apply,
    show (headZeroEquiv (K := K) (w := w)).toRingHom (WaHead K w 0) =
      headZeroEquiv (K := K) (w := w) (WaHead K w 0) from rfl,
    headZeroEquiv_WaHead, chartRescale_X]

variable {K w} in
theorem chartCoeff_constHead (ϖ : Uniformizer K) (x : K) :
    chartCoeff (K := K) (w := w) ϖ (constHead K w 0 x) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C x) := by
  rw [chartCoeff, RingHom.comp_apply,
    show (headZeroEquiv (K := K) (w := w)).toRingHom (constHead K w 0 x) =
      headZeroEquiv (K := K) (w := w) (constHead K w 0 x) from rfl,
    headZeroEquiv_constHead, chartRescale_C]

variable {K w} in
theorem chartCoeff_piHead (ϖ : Uniformizer K) :
    chartCoeff (K := K) (w := w) ϖ (piHead ϖ) =
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C ϖ.val) := by
  rw [show piHead (w := w) (N := 0) ϖ = constHead K w 0 ϖ.val from rfl]
  exact chartCoeff_constHead ϖ ϖ.val

variable {K w} in
theorem chartCoeff_continuous (ϖ : Uniformizer K) :
    Continuous (chartCoeff (K := K) (w := w) ϖ) := by
  rw [chartCoeff, RingHom.coe_comp]
  exact (chartRescale_continuous ϖ).comp
    (headZeroEquiv_continuous (K := K) (w := w))

variable {K w} in
open scoped Classical in
/-- The forward chart evaluation on the polynomial model: coefficients through
`chartCoeff`, `X_i ↦ X` at the `W`-entry and `X_i ↦ 1` at the `ϖ`-entry. -/
noncomputable def chartFwdP (ϖ : Uniformizer K) :
    FiniteJet.GraphKoszul.P (WPHead K w 0) (chartHeadDatum (w := w) ϖ).T.card →+*
      FiniteJet.GraphKoszul.P K 1 :=
  restrictedEval (chartCoeff (K := K) (w := w) ϖ) (chartCoeff_continuous ϖ)
    (fun i => if ((datumEnum (chartHeadDatum (w := w) ϖ) i :
        ↥(chartHeadDatum (w := w) ϖ).T) : WPHead K w 0) = WaHead K w 0 then
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0) else 1)
    (fun i => by
      split_ifs
      · exact FiniteJet.isPowerBounded_of_norm_le_one
          (le_of_eq (norm_polyToP_X1 (K := K)))
      · exact FiniteJet.isPowerBounded_of_norm_le_one (le_of_eq norm_one))

variable {K w} in
open scoped Classical in
theorem chartFwdP_C (ϖ : Uniformizer K) (x : WPHead K w 0) :
    chartFwdP (K := K) (w := w) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C x)) =
      chartCoeff (K := K) (w := w) ϖ x :=
  restrictedEval_C _ _ _ _ x

variable {K w} in
open scoped Classical in
theorem chartFwdP_X (ϖ : Uniformizer K)
    (i : Fin (chartHeadDatum (w := w) ϖ).T.card) :
    chartFwdP (K := K) (w := w) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X i)) =
      (if ((datumEnum (chartHeadDatum (w := w) ϖ) i :
          ↥(chartHeadDatum (w := w) ϖ).T) : WPHead K w 0) = WaHead K w 0 then
        FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0) else 1) :=
  restrictedEval_X _ _ _ _ i

variable {K w} in
theorem chartFwdP_continuous (ϖ : Uniformizer K) :
    Continuous (chartFwdP (K := K) (w := w) ϖ) :=
  restrictedEval_continuous _ _ _ _

variable {K w} in
open scoped Classical in
/-- The forward evaluation kills the graph relations (`ϖ·X − ϖX = 0` at the
`W`-entry, `ϖ·1 − ϖ = 0` at the `ϖ`-entry). -/
theorem chartFwdP_graphRel (ϖ : Uniformizer K)
    (i : Fin (chartHeadDatum (w := w) ϖ).T.card) :
    chartFwdP (K := K) (w := w) ϖ
      (headGraphRel (chartHeadDatum (w := w) ϖ) i) = 0 := by
  rw [headGraphRel, map_sub, map_mul, map_sub, map_mul, chartFwdP_C, chartFwdP_C,
    chartFwdP_X]
  rw [show (chartHeadDatum (w := w) ϖ).s = piHead ϖ from rfl, chartCoeff_piHead]
  rcases Finset.mem_insert.mp
    (datumEnum (chartHeadDatum (w := w) ϖ) i).2 with h | h
  · rw [h, chartCoeff_WaHead, if_pos rfl, ← map_mul, sub_self]
  · rw [Finset.mem_singleton] at h
    rw [h, chartCoeff_piHead,
      if_neg fun hc => WaHead_ne_piHead ϖ hc.symm, mul_one, sub_self]

variable {K w} in
open scoped Classical in
theorem chartGraphIdeal_le_ker (ϖ : Uniformizer K) :
    headGraphIdeal (chartHeadDatum (w := w) ϖ) ≤
      RingHom.ker (chartFwdP (K := K) (w := w) ϖ) := by
  have hker_closed : IsClosed ((RingHom.ker (chartFwdP (K := K) (w := w) ϖ) :
      Ideal (FiniteJet.GraphKoszul.P (WPHead K w 0)
        (chartHeadDatum (w := w) ϖ).T.card)) :
      Set (FiniteJet.GraphKoszul.P (WPHead K w 0)
        (chartHeadDatum (w := w) ϖ).T.card)) := by
    have hset : ((RingHom.ker (chartFwdP (K := K) (w := w) ϖ) :
        Ideal (FiniteJet.GraphKoszul.P (WPHead K w 0)
          (chartHeadDatum (w := w) ϖ).T.card)) :
        Set (FiniteJet.GraphKoszul.P (WPHead K w 0)
          (chartHeadDatum (w := w) ϖ).T.card)) =
        chartFwdP (K := K) (w := w) ϖ ⁻¹' {0} := by
      ext y
      simp [RingHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage (chartFwdP_continuous ϖ) isClosed_singleton
  have hspan : (Ideal.span (Set.range (headGraphRel
      (chartHeadDatum (w := w) ϖ))) : Set _) ⊆
      ((RingHom.ker (chartFwdP (K := K) (w := w) ϖ) :
        Ideal (FiniteJet.GraphKoszul.P (WPHead K w 0)
          (chartHeadDatum (w := w) ϖ).T.card)) :
        Set (FiniteJet.GraphKoszul.P (WPHead K w 0)
          (chartHeadDatum (w := w) ϖ).T.card)) := by
    have h1 : Ideal.span (Set.range (headGraphRel (chartHeadDatum (w := w) ϖ))) ≤
        RingHom.ker (chartFwdP (K := K) (w := w) ϖ) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (chartFwdP_graphRel ϖ i)
    exact fun x hx => h1 hx
  intro x hx
  have hx' : x ∈ closure ((Ideal.span (Set.range (headGraphRel
      (chartHeadDatum (w := w) ϖ))) :
      Ideal (FiniteJet.GraphKoszul.P (WPHead K w 0)
        (chartHeadDatum (w := w) ϖ).T.card)) :
      Set (FiniteJet.GraphKoszul.P (WPHead K w 0)
        (chartHeadDatum (w := w) ϖ).T.card)) := by
    rw [← Ideal.coe_closure]
    exact hx
  exact closure_minimal hspan hker_closed hx'

variable {K w} in
/-- The forward chart model map on the graph quotient. -/
noncomputable def chartFwd (ϖ : Uniformizer K) :
    QHead (chartHeadDatum (w := w) ϖ) →+* FiniteJet.GraphKoszul.P K 1 :=
  Ideal.Quotient.lift (headGraphIdeal (chartHeadDatum (w := w) ϖ))
    (chartFwdP (K := K) (w := w) ϖ)
    (fun a ha => RingHom.mem_ker.mp (chartGraphIdeal_le_ker ϖ ha))

variable {K w} in
theorem chartFwd_mk (ϖ : Uniformizer K)
    (G : FiniteJet.GraphKoszul.P (WPHead K w 0)
      (chartHeadDatum (w := w) ϖ).T.card) :
    chartFwd (K := K) (w := w) ϖ
      (Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ)) G) =
      chartFwdP (K := K) (w := w) ϖ G :=
  rfl

variable {K w} in
theorem chartFwd_continuous (ϖ : Uniformizer K) :
    Continuous (chartFwd (K := K) (w := w) ϖ) := by
  refine continuous_of_continuousAt_zero (chartFwd (K := K) (w := w) ϖ).toAddMonoidHom ?_
  show Filter.Tendsto _ (nhds 0) (nhds _)
  rw [show (chartFwd (K := K) (w := w) ϖ).toAddMonoidHom
    (0 : QHead (chartHeadDatum (w := w) ϖ)) = 0 from map_zero _]
  refine Filter.tendsto_def.mpr fun U hU => ?_
  have hfwdP := (chartFwdP_continuous (K := K) (w := w) ϖ).tendsto 0
  rw [show chartFwdP (K := K) (w := w) ϖ 0 = 0 from map_zero _] at hfwdP
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp (hfwdP hU)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0) fun q hq => ?_
  rw [Set.mem_preimage]
  rw [Metric.mem_ball, dist_zero_right] at hq
  obtain ⟨G, hG, hGn⟩ := Ideal.Quotient.norm_mk_lt q
    (show (0 : ℝ) < δ - ‖q‖ by linarith)
  have hq' : chartFwd (K := K) (w := w) ϖ q =
      chartFwdP (K := K) (w := w) ϖ G := by
    rw [← hG, chartFwd_mk]
  show chartFwd (K := K) (w := w) ϖ q ∈ U
  rw [hq']
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖G‖ < ‖q‖ + (δ - ‖q‖) := hGn
    _ = δ := by rw [add_sub_cancel]

variable {K w} in
open scoped Classical in
theorem WaHead_mem_chartT (ϖ : Uniformizer K) :
    WaHead K w 0 ∈ (chartHeadDatum (w := w) ϖ).T := by
  rw [chartHeadDatum_T]
  exact Finset.mem_insert_self _ _

variable {K w} in
/-- The reverse chart model map: `X ↦ [X_W]`, constants through `headConst`. -/
noncomputable def chartRev (ϖ : Uniformizer K) :
    FiniteJet.GraphKoszul.P K 1 →+* QHead (chartHeadDatum (w := w) ϖ) :=
  restrictedEval
    ((headConst (chartHeadDatum (w := w) ϖ)).comp (constHead K w 0))
    (AddMonoidHomClass.continuous_of_bound _ 1 fun a => by
      rw [one_mul, RingHom.comp_apply]
      exact le_trans (norm_headConst_le _ _) (le_of_eq (by rw [norm_constHead])))
    (fun _ : Fin 1 => qX (chartHeadDatum (w := w) ϖ)
      ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
        ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩))
    (fun _ => FiniteJet.isPowerBounded_of_norm_le_one (norm_qX_le_one _ _))

variable {K w} in
theorem chartRev_C (ϖ : Uniformizer K) (a : K) :
    chartRev (K := K) (w := w) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C a)) =
      headConst (chartHeadDatum (w := w) ϖ) (constHead K w 0 a) :=
  restrictedEval_C _ _ _ _ a

variable {K w} in
theorem chartRev_X (ϖ : Uniformizer K) :
    chartRev (K := K) (w := w) ϖ
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0)) =
      qX (chartHeadDatum (w := w) ϖ)
        ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
          ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩) :=
  restrictedEval_X _ _ _ _ 0

variable {K w} in
theorem chartRev_continuous (ϖ : Uniformizer K) :
    Continuous (chartRev (K := K) (w := w) ϖ) :=
  restrictedEval_continuous _ _ _ _

variable {K w} in
/-- Forward after reverse is the identity on `K⟨X⟩`. -/
theorem chartFwd_chartRev (ϖ : Uniformizer K)
    (y : FiniteJet.GraphKoszul.P K 1) :
    chartFwd (K := K) (w := w) ϖ (chartRev (K := K) (w := w) ϖ y) = y := by
  classical
  have h1 : ⇑((chartFwd (K := K) (w := w) ϖ).comp
      (chartRev (K := K) (w := w) ϖ)) =
      (id : FiniteJet.GraphKoszul.P K 1 → FiniteJet.GraphKoszul.P K 1) := by
    refine denseRange_polyToP.equalizer
      ((chartFwd_continuous ϖ).comp (chartRev_continuous ϖ)) continuous_id ?_
    funext Q
    show chartFwd (K := K) (w := w) ϖ
      (chartRev (K := K) (w := w) ϖ (FiniteJet.GraphKoszul.polyToP Q)) =
      FiniteJet.GraphKoszul.polyToP Q
    induction Q using MvPolynomial.induction_on with
    | C a =>
      rw [chartRev_C, show headConst (chartHeadDatum (w := w) ϖ)
          (constHead K w 0 a) =
        Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
          (FiniteJet.GraphKoszul.polyToP
            (MvPolynomial.C (constHead K w 0 a))) from rfl,
        chartFwd_mk, chartFwdP_C, chartCoeff_constHead]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [map_mul, map_mul, map_mul, hp, chartRev_X,
        show qX (chartHeadDatum (w := w) ϖ)
          ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
            ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩) =
        Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
          (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X
            ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
              ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩))) from rfl,
        chartFwd_mk, chartFwdP_X, Equiv.apply_symm_apply, if_pos rfl, ← map_mul]
  exact congrFun h1 y

variable {K w} in
/-- The reverse map undoes the coefficient hom (density of polynomials in `K⟨W⟩`
through `headZeroEquiv`). -/
theorem chartRev_chartCoeff (ϖ : Uniformizer K) (x : WPHead K w 0) :
    chartRev (K := K) (w := w) ϖ (chartCoeff (K := K) (w := w) ϖ x) =
      headConst (chartHeadDatum (w := w) ϖ) x := by
  classical
  have hdense : DenseRange (⇑(headZeroEquiv (K := K) (w := w)).symm ∘
      ⇑(FiniteJet.GraphKoszul.polyToP (E := K) (m := 1))) :=
    DenseRange.comp (Function.Surjective.denseRange
      (headZeroEquiv (K := K) (w := w)).symm.surjective) denseRange_polyToP
      (headZeroEquiv_symm_continuous (K := K) (w := w))
  have h1 : ⇑((chartRev (K := K) (w := w) ϖ).comp
      (chartCoeff (K := K) (w := w) ϖ)) =
      ⇑(headConst (chartHeadDatum (w := w) ϖ)) := by
    refine hdense.equalizer
      ((chartRev_continuous ϖ).comp (chartCoeff_continuous ϖ))
      (AddMonoidHomClass.continuous_of_bound
        (headConst (chartHeadDatum (w := w) ϖ)) 1
        fun q => by rw [one_mul]; exact norm_headConst_le _ q) ?_
    funext Q
    show chartRev (K := K) (w := w) ϖ (chartCoeff (K := K) (w := w) ϖ
      ((headZeroEquiv (K := K) (w := w)).symm
        (FiniteJet.GraphKoszul.polyToP Q))) =
      headConst (chartHeadDatum (w := w) ϖ)
        ((headZeroEquiv (K := K) (w := w)).symm
          (FiniteJet.GraphKoszul.polyToP Q))
    rw [show chartCoeff (K := K) (w := w) ϖ
        ((headZeroEquiv (K := K) (w := w)).symm
          (FiniteJet.GraphKoszul.polyToP Q)) =
      chartRescale (K := K) ϖ (FiniteJet.GraphKoszul.polyToP Q) from by
        rw [chartCoeff, RingHom.comp_apply,
          show (headZeroEquiv (K := K) (w := w)).toRingHom
            ((headZeroEquiv (K := K) (w := w)).symm
              (FiniteJet.GraphKoszul.polyToP Q)) =
          headZeroEquiv (K := K) (w := w)
            ((headZeroEquiv (K := K) (w := w)).symm
              (FiniteJet.GraphKoszul.polyToP Q)) from rfl,
          RingEquiv.apply_symm_apply]]
    induction Q using MvPolynomial.induction_on with
    | C a =>
      rw [chartRescale_C, chartRev_C,
        show (headZeroEquiv (K := K) (w := w)).symm
          (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C a)) =
        constHead K w 0 a from by
          rw [← headZeroEquiv_constHead (K := K) (w := w) a,
            RingEquiv.symm_apply_apply]]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [map_mul, map_mul, map_mul, hp, chartRescale_X, map_mul, map_mul,
        chartRev_C, chartRev_X]
      have hrel := headConst_datumEnum (chartHeadDatum (w := w) ϖ)
        ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
          ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩)
      rw [Equiv.apply_symm_apply] at hrel
      rw [show constHead K w 0 ϖ.val = (chartHeadDatum (w := w) ϖ).s from rfl,
        ← hrel,
        show ((⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩ :
          ↥(chartHeadDatum (w := w) ϖ).T) : WPHead K w 0) = WaHead K w 0 from rfl,
        show (headZeroEquiv (K := K) (w := w)).symm
          (FiniteJet.GraphKoszul.polyToP p *
            FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0)) =
        (headZeroEquiv (K := K) (w := w)).symm
            (FiniteJet.GraphKoszul.polyToP p) *
          (headZeroEquiv (K := K) (w := w)).symm
            (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0)) from map_mul _ _ _,
        show (headZeroEquiv (K := K) (w := w)).symm
          (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X 0)) =
        WaHead K w 0 from by
          rw [← headZeroEquiv_WaHead (K := K) (w := w),
            RingEquiv.symm_apply_apply], map_mul]
  exact congrFun h1 x

variable {K w} in
/-- Reverse after forward is the identity on the graph quotient. -/
theorem chartRev_chartFwd (ϖ : Uniformizer K)
    (q : QHead (chartHeadDatum (w := w) ϖ)) :
    chartRev (K := K) (w := w) ϖ (chartFwd (K := K) (w := w) ϖ q) = q := by
  classical
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := headGraphIdeal (chartHeadDatum (w := w) ϖ)) q
  rw [chartFwd_mk]
  have hpoly : ∀ Q : MvPolynomial
      (Fin (chartHeadDatum (w := w) ϖ).T.card) (WPHead K w 0),
      chartRev (K := K) (w := w) ϖ (chartFwdP (K := K) (w := w) ϖ
        (FiniteJet.GraphKoszul.polyToP Q)) =
        Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
          (FiniteJet.GraphKoszul.polyToP Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x =>
      rw [chartFwdP_C, chartRev_chartCoeff]
      rfl
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      rfl
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp, chartFwdP_X]
      rcases Finset.mem_insert.mp
        (datumEnum (chartHeadDatum (w := w) ϖ) i).2 with h | h
      · rw [if_pos h, chartRev_X]
        have hi : ((datumEnum (chartHeadDatum (w := w) ϖ)).symm
            ⟨WaHead K w 0, WaHead_mem_chartT ϖ⟩) = i := by
          rw [← Equiv.symm_apply_apply
            (datumEnum (chartHeadDatum (w := w) ϖ)) i]
          congr 1
          exact Subtype.ext h.symm
        rw [hi]
        rfl
      · rw [Finset.mem_singleton] at h
        rw [if_neg (by rw [h]; exact fun hc => WaHead_ne_piHead ϖ hc.symm),
          map_one]
        have hrel := headConst_datumEnum (chartHeadDatum (w := w) ϖ) i
        rw [show ((datumEnum (chartHeadDatum (w := w) ϖ) i :
            ↥(chartHeadDatum (w := w) ϖ).T) : WPHead K w 0) = piHead ϖ from h,
          show (chartHeadDatum (w := w) ϖ).s = piHead ϖ from rfl] at hrel
        have hu : IsUnit (headConst (chartHeadDatum (w := w) ϖ) (piHead ϖ)) := by
          have h0 := isUnit_headConst_s ϖ (chartHeadDatum (w := w) ϖ)
            (chartHeadDatum_isRational ϖ)
          rwa [show (chartHeadDatum (w := w) ϖ).s = piHead ϖ from rfl] at h0
        have hqX1 : qX (chartHeadDatum (w := w) ϖ) i = 1 := by
          refine hu.mul_left_cancel ?_
          rw [mul_one, ← hrel]
        rw [show Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
            (FiniteJet.GraphKoszul.polyToP p *
              FiniteJet.GraphKoszul.polyToP (MvPolynomial.X i)) =
          Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
              (FiniteJet.GraphKoszul.polyToP p) *
            Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
              (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X i))
            from map_mul _ _ _,
          show Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
            (FiniteJet.GraphKoszul.polyToP (MvPolynomial.X i)) =
          qX (chartHeadDatum (w := w) ϖ) i from rfl, hqX1]
        rfl
  have h1 : ⇑((chartRev (K := K) (w := w) ϖ).comp
      (chartFwdP (K := K) (w := w) ϖ)) =
      ⇑(Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))) := by
    refine denseRange_polyToP.equalizer
      ((chartRev_continuous ϖ).comp (chartFwdP_continuous ϖ))
      (continuous_mk_headGraphIdeal (chartHeadDatum (w := w) ϖ)) ?_
    funext Q
    exact hpoly Q
  exact congrFun h1 G

variable {K w} in
/-- The chart head model: `K⟨W⟩⟨X⟩/(ϖX − W) ≅ K⟨X⟩` via `W ↦ ϖX` (the classical
smooth chart; the univariate rescaling of `FJP/FiniteJetChart.lean:82`). -/
noncomputable def chartQHeadEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    QHead (chartHeadDatum (w := w) ϖ) ≃+* FiniteJet.GraphKoszul.P K 1 :=
  { toFun := chartFwd (K := K) (w := w) ϖ
    invFun := chartRev (K := K) (w := w) ϖ
    left_inv := chartRev_chartFwd ϖ
    right_inv := chartFwd_chartRev ϖ
    map_mul' := map_mul _
    map_add' := map_add _ }

section NormBound

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E]
variable {B : Type*} [NormedCommRing B] [IsUltrametricDist B] [CompleteSpace B]
variable {m : ℕ}

/-- The evaluation is nonexpansive when the coefficient hom is and the tuple lies
in the unit ball (each Cauchy term is bounded by the Gauss norm; ultrametric
partial sums stay in the closed ball). -/
theorem norm_restrictedEval_le (φ : E →+* B) (hφ : Continuous φ)
    (hφ1 : ∀ x, ‖φ x‖ ≤ ‖x‖) (b : Fin m → B)
    (hb : ∀ i, TopologicalRing.IsPowerBounded (b i))
    (hb1 : ∀ i, ‖b i‖ ≤ 1) (hone : ‖(1 : B)‖ ≤ 1)
    (F : FiniteJet.GraphKoszul.P E m) :
    ‖restrictedEval φ hφ b hb F‖ ≤ ‖F‖ := by
  classical
  have hterm : ∀ t : Fin m →₀ ℕ,
      ‖φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i‖ ≤ ‖F‖ := by
    intro t
    have hprod : ‖∏ i, b i ^ t i‖ ≤ 1 := by
      refine Finset.prod_induction _ (fun x => ‖x‖ ≤ 1)
        (fun x y hx hy => le_trans (norm_mul_le x y)
          (mul_le_one₀ hx (norm_nonneg y) hy)) hone (fun i _ => ?_)
      have hb' : ∀ n : ℕ, ‖b i ^ n‖ ≤ 1 := by
        intro n
        cases n with
        | zero => rw [pow_zero]; exact hone
        | succ k =>
            exact le_trans (norm_pow_le' (b i) k.succ_pos)
              (pow_le_one₀ (norm_nonneg _) (hb1 i))
      exact hb' (t i)
    calc ‖φ (MvPowerSeries.coeff t F.1) * ∏ i, b i ^ t i‖
        ≤ ‖φ (MvPowerSeries.coeff t F.1)‖ * ‖∏ i, b i ^ t i‖ := norm_mul_le _ _
      _ ≤ ‖MvPowerSeries.coeff t F.1‖ * 1 :=
          mul_le_mul (hφ1 _) hprod (norm_nonneg _) (norm_nonneg _)
      _ = ‖MvPowerSeries.coeff t F.1‖ := mul_one _
      _ ≤ ‖F‖ := FiniteJet.GraphKoszul.norm_coeff_le_gauss F t
  have hHasSum := (summable_evalFamily φ hφ b hb F).hasSum
  have hball : IsClosed {x : B | ‖x‖ ≤ ‖F‖} :=
    isClosed_le continuous_norm continuous_const
  exact hball.mem_of_tendsto hHasSum (Filter.Eventually.of_forall fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg F)
      fun t _ => hterm t)

end NormBound

variable {K w} in
theorem norm_chartRescale_le (ϖ : Uniformizer K)
    (y : FiniteJet.GraphKoszul.P K 1) :
    ‖chartRescale (K := K) ϖ y‖ ≤ ‖y‖ := by
  refine norm_restrictedEval_le (E := K) (B := FiniteJet.GraphKoszul.P K 1)
    _ _ (fun x => ?_) _ _ (fun i => ?_) (le_of_eq norm_one) y
  · rw [RingHom.comp_apply]
    exact le_of_eq (FiniteJet.GraphKoszul.norm_tP x fun z => norm_mul x z)
  · rw [map_mul, FiniteJet.GraphKoszul.norm_tP_mul ϖ.val
      (fun z => norm_mul ϖ.val z), norm_polyToP_X1 (K := K), mul_one]
    exact ϖ.norm_val_lt_one.le

variable {K w} in
theorem norm_chartCoeff_le (ϖ : Uniformizer K) (x : WPHead K w 0) :
    ‖chartCoeff (K := K) (w := w) ϖ x‖ ≤ ‖x‖ := by
  rw [chartCoeff, RingHom.comp_apply]
  refine le_trans (norm_chartRescale_le ϖ _) ?_
  exact le_of_eq (norm_headZeroEquiv x)

variable {K w} in
theorem norm_chartFwdP_le (ϖ : Uniformizer K)
    (G : FiniteJet.GraphKoszul.P (WPHead K w 0)
      (chartHeadDatum (w := w) ϖ).T.card) :
    ‖chartFwdP (K := K) (w := w) ϖ G‖ ≤ ‖G‖ := by
  classical
  refine norm_restrictedEval_le (E := WPHead K w 0)
    (B := FiniteJet.GraphKoszul.P K 1) _ _ (norm_chartCoeff_le ϖ) _ _
    (fun i => ?_) (le_of_eq norm_one) G
  split_ifs
  · exact le_of_eq (norm_polyToP_X1 (K := K))
  · exact le_of_eq norm_one

variable {K w} in
theorem norm_chartRev_le (ϖ : Uniformizer K)
    (y : FiniteJet.GraphKoszul.P K 1) :
    ‖chartRev (K := K) (w := w) ϖ y‖ ≤ ‖y‖ := by
  have hone : ‖(1 : QHead (chartHeadDatum (w := w) ϖ))‖ ≤ 1 := by
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    exact le_of_eq norm_one
  refine norm_restrictedEval_le (E := K)
    (B := QHead (chartHeadDatum (w := w) ϖ)) _ _ (fun a => ?_) _ _
    (fun i => norm_qX_le_one _ _) hone y
  rw [RingHom.comp_apply]
  exact le_trans (norm_headConst_le _ _) (le_of_eq (by rw [norm_constHead]))

variable {K w} in
theorem chartQHeadEquiv_norm (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (x : QHead (chartHeadDatum (w := w) ϖ)) :
    ‖chartQHeadEquiv ϖ hK₀ x‖ = ‖x‖ := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨G, hG, hGn⟩ := Ideal.Quotient.norm_mk_lt x hε
    calc ‖chartQHeadEquiv ϖ hK₀ x‖
        = ‖chartFwdP (K := K) (w := w) ϖ G‖ := by
          rw [show chartQHeadEquiv ϖ hK₀ x = chartFwd (K := K) (w := w) ϖ x
            from rfl, ← hG, chartFwd_mk]
      _ ≤ ‖G‖ := norm_chartFwdP_le ϖ G
      _ ≤ ‖x‖ + ε := hGn.le
  · have h1 : ‖x‖ = ‖chartRev (K := K) (w := w) ϖ
        (chartFwd (K := K) (w := w) ϖ x)‖ := by
      rw [chartRev_chartFwd]
    rw [h1]
    exact norm_chartRev_le ϖ _

variable {K w} in
/-- The chart head localization is an integral domain (transport from `K⟨X⟩`, whose
Gauss norm is multiplicative). -/
theorem isDomain_chartQHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDomain (QHead (chartHeadDatum (w := w) ϖ)) := by
  haveI := isDomain_P_one (K := K)
  exact Function.Injective.isDomain (chartQHeadEquiv ϖ hK₀).toRingHom
    (chartQHeadEquiv ϖ hK₀).injective

/-! ### `ℬ` is a domain ([WP] prop:weighted-chart-domain-nonuniform, first half) -/

variable {K w} in
/-- **The bad chart is an integral domain** ([WP]
prop:weighted-chart-domain-nonuniform: "coefficientwise inclusion gives an injective
homomorphism `ℬ ↪ k⟨X,U_1,U_2,…⟩`; the target is a domain … therefore `ℬ` is a
domain" — realized through the `Φ`-embedding of the `TailC0` model into
`MvPowerSeries` over the domain `K⟨X⟩`). -/
theorem isDomain_chart (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDomain (presheafValue (chartDatum (w := w) ϖ)) := by
  haveI hQ : IsDomain (QHead (chartHeadDatum (w := w) ϖ)) :=
    isDomain_chartQHead ϖ hK₀
  have hρ0 : (rhoQ (chartHeadDatum (w := w) ϖ)).val ≠ 0 := by
    intro h0
    have h1 := congrArg (chartFwd (K := K) (w := w) ϖ) h0
    rw [map_zero] at h1
    rw [show (rhoQ (chartHeadDatum (w := w) ϖ)).val =
      headConst (chartHeadDatum (w := w) ϖ) (WaHead K w 0) from rfl,
      show headConst (chartHeadDatum (w := w) ϖ) (WaHead K w 0) =
        Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
          (FiniteJet.GraphKoszul.polyToP
            (MvPolynomial.C (WaHead K w 0))) from rfl,
      chartFwd_mk, chartFwdP_C, chartCoeff_WaHead] at h1
    have h2 := congrArg (fun z : FiniteJet.GraphKoszul.P K 1 => ‖z‖) h1
    rw [show ‖FiniteJet.GraphKoszul.polyToP
        (MvPolynomial.C ϖ.val * MvPolynomial.X (0 : Fin 1))‖ =
      ‖ϖ.val‖ * ‖FiniteJet.GraphKoszul.polyToP
        (MvPolynomial.X (0 : Fin 1))‖ from by
        rw [map_mul]
        exact FiniteJet.GraphKoszul.norm_tP_mul ϖ.val
          (fun z => norm_mul ϖ.val z) _,
      norm_polyToP_X1 (K := K), mul_one, norm_zero] at h2
    exact absurd h2.symm (ne_of_lt ϖ.norm_val_pos)
  haveI hT : IsDomain (TailC0 w 0 (QHead (chartHeadDatum (w := w) ϖ))
      (rhoQ (chartHeadDatum (w := w) ϖ))) := by
    refine isDomain_tailC0 w 0 _ fun x hx => ?_
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h hρ0
    · exact h
  exact Function.Injective.isDomain
    (coeffLocEquiv ϖ hK₀ (chartHeadDatum (w := w) ϖ)
      (chartHeadDatum_isRational ϖ)).toRingHom
    (coeffLocEquiv ϖ hK₀ (chartHeadDatum (w := w) ϖ)
      (chartHeadDatum_isRational ϖ)).injective

/-! ### `ℬ` is not uniform ([WP] prop:weighted-chart-domain-nonuniform, second half) -/

variable {K w} in
/-- The tail generator `δ_n = U_n` at stage `0` (`n ≥ 1`). -/
noncomputable def tailDelta (n : ℕ) (hn : 1 ≤ n) : TailIdx 0 :=
  ⟨Finsupp.single n 1, fun m hm => by
    rw [Finsupp.single_apply, if_neg (by omega)]⟩

/-- Power-boundedness from a uniform norm bound on all powers. -/
theorem isPowerBounded_of_forall_norm_le {R : Type*} [SeminormedCommRing R]
    {x : R} {C : ℝ} (hC : 0 < C) (h : ∀ n : ℕ, ‖x ^ n‖ ≤ C) :
    TopologicalRing.IsPowerBounded x := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / C), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro z ⟨s, ⟨n, rfl⟩, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖x ^ n * y‖ ≤ ‖x ^ n‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ C * ‖y‖ := mul_le_mul_of_nonneg_right (h n) (norm_nonneg y)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hy hC
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hC)

variable {K w} in
/-- Norms in the chart head model are computed in `K⟨X⟩`. -/
theorem norm_qHead_eq (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (x : QHead (chartHeadDatum (w := w) ϖ)) :
    ‖x‖ = ‖chartFwd (K := K) (w := w) ϖ x‖ :=
  (chartQHeadEquiv_norm ϖ hK₀ x).symm

variable {K w} in
/-- The chart head model has multiplicative norm (transport of the Gauss norm). -/
theorem norm_qHead_mul (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (x y : QHead (chartHeadDatum (w := w) ϖ)) :
    ‖x * y‖ = ‖x‖ * ‖y‖ := by
  rw [norm_qHead_eq ϖ hK₀, norm_qHead_eq ϖ hK₀ x, norm_qHead_eq ϖ hK₀ y, map_mul]
  exact norm_restricted_mul_general (fun a b => norm_mul a b) _ _

variable {K w} in
theorem norm_qHead_one (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ‖(1 : QHead (chartHeadDatum (w := w) ϖ))‖ = 1 := by
  rw [norm_qHead_eq ϖ hK₀, map_one]
  exact norm_one

variable {K w} in
theorem norm_qHead_pow (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (x : QHead (chartHeadDatum (w := w) ϖ)) (e : ℕ) :
    ‖x ^ e‖ = ‖x‖ ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact norm_qHead_one ϖ hK₀
  | succ k ih => rw [pow_succ, pow_succ, norm_qHead_mul ϖ hK₀, ih]

variable {K w} in
theorem norm_qHeadConst (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (a : K) :
    ‖headConst (chartHeadDatum (w := w) ϖ) (constHead K w 0 a)‖ = ‖a‖ := by
  rw [norm_qHead_eq ϖ hK₀,
    show headConst (chartHeadDatum (w := w) ϖ) (constHead K w 0 a) =
      Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
        (FiniteJet.GraphKoszul.polyToP
          (MvPolynomial.C (constHead K w 0 a))) from rfl,
    chartFwd_mk, chartFwdP_C, chartCoeff_constHead]
  exact FiniteJet.GraphKoszul.norm_tP a (fun z => norm_mul a z)

variable {K w} in
theorem norm_rhoQVal (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ‖(rhoQ (chartHeadDatum (w := w) ϖ)).val‖ = ‖ϖ.val‖ := by
  rw [norm_qHead_eq ϖ hK₀,
    show (rhoQ (chartHeadDatum (w := w) ϖ)).val =
      Ideal.Quotient.mk (headGraphIdeal (chartHeadDatum (w := w) ϖ))
        (FiniteJet.GraphKoszul.polyToP
          (MvPolynomial.C (WaHead K w 0))) from rfl,
    chartFwd_mk, chartFwdP_C, chartCoeff_WaHead, map_mul,
    FiniteJet.GraphKoszul.norm_tP_mul ϖ.val (fun z => norm_mul ϖ.val z),
    norm_polyToP_X1 (K := K), mul_one]

variable {K w} in
theorem norm_one_tailC0_le (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ‖(1 : TailC0 w 0 (QHead (chartHeadDatum (w := w) ϖ))
      (rhoQ (chartHeadDatum (w := w) ϖ)))‖ ≤ 1 := by
  rw [TailC0.norm_eq_iSup_coeff]
  refine ciSup_le fun τ => ?_
  rw [show TailC0.coeff τ (1 : TailC0 w 0 (QHead (chartHeadDatum (w := w) ϖ))
    (rhoQ (chartHeadDatum (w := w) ϖ))) =
    (if τ = 0 then 1 else 0) from TailC0.one_val τ]
  split_ifs
  · exact le_of_eq (norm_qHead_one ϖ hK₀)
  · rw [norm_zero]
    exact zero_le_one

variable {K w} in
/-- The `T_n` family is power-bounded but unbounded in the `TailC0` chart model
([WP] eq:Tn-power-norms: `‖T_n^{2r}‖ = 1`, `‖T_n^{2r+1}‖ = |ϖ|^{−n}`; "The family
`(T_n)` is not bounded: if `ϖ^N T_n ∈ ℬ₀` then … `N ≥ n`").  Requires the weight
unbounded on the tail (`hwu`). -/
theorem not_isUniform_chartModel (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsUniform
      (TailC0 w 0 (QHead (chartHeadDatum (w := w) ϖ))
        (rhoQ (chartHeadDatum ϖ))) := by
  classical
  intro hU
  obtain ⟨V, hV, hSV⟩ := hU.isBounded_powerBounded (Metric.ball 0 1)
    (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hc0, hcδ⟩ := NormedField.exists_norm_lt (α := K) hδ0
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hc0 ϖ.norm_val_lt_one
  obtain ⟨n, hn1, hnw⟩ := hwu m₀
  set qc := headConst (chartHeadDatum (w := w) ϖ) (constHead K w 0 c) with hqc
  set an := headConst (chartHeadDatum (w := w) ϖ)
    (constHead K w 0 ((ϖ.val ^ w n)⁻¹)) with han
  set Tn := TailC0.single (w := w) (ρ := rhoQ (chartHeadDatum (w := w) ϖ))
    (tailDelta n hn1) an with hTn
  have hδ1 : (tailDelta n hn1).1 = Finsupp.single n 1 := rfl
  have hδ2 : (tailDelta n hn1 + tailDelta n hn1).1 = Finsupp.single n 2 := by
    rw [TailIdx.add_val, hδ1, ← Finsupp.single_add]
  have hE : wpWeight w (tailDelta n hn1).1 + wpWeight w (tailDelta n hn1).1 -
      wpWeight w (tailDelta n hn1 + tailDelta n hn1).1 = 2 * w n := by
    rw [hδ1, hδ2, wpWeight_single, wpWeight_single,
      if_pos ⟨by omega, by omega⟩, if_neg (fun hc => absurd hc.1 (by decide))]
    omega
  have hT2 : Tn * Tn = TailC0.single (tailDelta n hn1 + tailDelta n hn1)
      ((rhoQ (chartHeadDatum (w := w) ϖ)).val ^
        (wpWeight w (tailDelta n hn1).1 + wpWeight w (tailDelta n hn1).1 -
          wpWeight w (tailDelta n hn1 + tailDelta n hn1).1) * (an * an)) := by
    rw [hTn, TailC0.single_mul_single]
  have hT2norm : ‖Tn * Tn‖ = 1 := by
    rw [hT2, TailC0.norm_single, norm_qHead_mul ϖ hK₀, norm_qHead_pow ϖ hK₀,
      norm_rhoQVal ϖ hK₀, hE, norm_qHead_mul ϖ hK₀, han,
      norm_qHeadConst ϖ hK₀, norm_inv, norm_pow]
    have hne : ‖ϖ.val‖ ^ w n ≠ 0 := ne_of_gt (pow_pos ϖ.norm_val_pos _)
    field_simp
    ring
  have hTnnorm : ‖Tn‖ = (‖ϖ.val‖ ^ w n)⁻¹ := by
    rw [hTn, TailC0.norm_single, han, norm_qHeadConst ϖ hK₀, norm_inv, norm_pow]
  have hTnpow : ∀ k : ℕ, ‖Tn ^ k‖ ≤ max 1 ((‖ϖ.val‖ ^ w n)⁻¹) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => rw [pow_zero]; exact le_max_of_le_left (norm_one_tailC0_le ϖ hK₀)
    | one => rw [pow_one]; exact le_max_of_le_right (le_of_eq hTnnorm)
    | more k ih _ =>
        rw [pow_succ, pow_succ, mul_assoc]
        refine le_trans (norm_mul_le _ _) ?_
        rw [hT2norm, mul_one]
        exact ih
  have hTnpb : Tn ∈ powerBoundedSubring (TailC0 w 0
      (QHead (chartHeadDatum (w := w) ϖ)) (rhoQ (chartHeadDatum (w := w) ϖ))) :=
    isPowerBounded_of_forall_norm_le
      (lt_of_lt_of_le one_pos (le_max_left _ _)) hTnpow
  set v := TailC0.ofHead (w := w) (ρ := rhoQ (chartHeadDatum (w := w) ϖ)) qc
    with hv
  have hvV : v ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, hv, TailC0.norm_ofHead, hqc,
      norm_qHeadConst ϖ hK₀]
    exact hcδ
  have hmem := hSV (Set.mul_mem_mul hTnpb hvV)
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hprod : Tn * v = TailC0.single (tailDelta n hn1) (an * qc) := by
    rw [hTn, hv, show TailC0.ofHead (w := w)
        (ρ := rhoQ (chartHeadDatum (w := w) ϖ)) qc =
      TailC0.single 0 qc from rfl, TailC0.single_mul_single,
      show tailDelta n hn1 + 0 = tailDelta n hn1 from add_zero _,
      show wpWeight w (tailDelta n hn1).1 + wpWeight w (0 : TailIdx 0).1 -
        wpWeight w (tailDelta n hn1).1 = 0 from by
          rw [TailIdx.zero_val, wpWeight_zero]; omega, pow_zero, one_mul]
  have hnorm : ‖Tn * v‖ = (‖ϖ.val‖ ^ w n)⁻¹ * ‖c‖ := by
    rw [hprod, TailC0.norm_single, norm_qHead_mul ϖ hK₀, han,
      norm_qHeadConst ϖ hK₀, hqc, norm_qHeadConst ϖ hK₀, norm_inv, norm_pow]
  rw [hnorm] at hmem
  have hle : ‖ϖ.val‖ ^ w n ≤ ‖c‖ :=
    le_trans (pow_le_pow_of_le_one ϖ.norm_val_pos.le
      ϖ.norm_val_lt_one.le hnw) hm₀.le
  have hge : (1 : ℝ) ≤ (‖ϖ.val‖ ^ w n)⁻¹ * ‖c‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ (pow_pos ϖ.norm_val_pos _), one_mul]
    exact hle
  linarith

variable {K w} in
/-- **The bad chart is not uniform** ([WP] prop:weighted-chart-domain-nonuniform:
"Hence `ℬ°` is unbounded and `ℬ` is not uniform"; transported along the
coefficientwise-localization model, the `not_isUniform_chart` pattern of
`FJP/Over/Chart.lean:1459`). -/
theorem not_isUniform_chart (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsUniform (presheafValue (chartDatum (w := w) ϖ)) := fun h =>
  not_isUniform_chartModel hwu ϖ hK₀
    (FiniteJet.isUniform_of_ringEquiv
      (coeffLocEquiv ϖ hK₀ (chartHeadDatum (w := w) ϖ)
        (chartHeadDatum_isRational ϖ))
      (coeffLocEquiv_continuous ϖ hK₀ (chartHeadDatum (w := w) ϖ)
        (chartHeadDatum_isRational ϖ))
      (coeffLocEquiv_symm_continuous ϖ hK₀ (chartHeadDatum (w := w) ϖ)
        (chartHeadDatum_isRational ϖ)) h)

variable {K w} in
/-- **`𝒜` is not stably uniform** ([WP] thm 6.2, "In particular, failure of stable
uniformity need not be caused by a nilpotent in the bad rational localization"; the
`not_isStablyUniform_JetA` assembly, `FJP/Over/Chart.lean:1469`). -/
theorem not_isStablyUniform_WPA (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsStablyUniform (WPA K w) := fun h =>
  not_isUniform_chart hwu ϖ hK₀
    ⟨h.presheafValue_isUniform (chartDatum ϖ) (chartDatum_isRational ϖ)⟩

variable {K w} in
/-- The bad chart is reduced — with NO classical input (a domain is reduced).  The
contrast with the FJP example ([WP] rem:second-example-relation: "Its bad chart
remains a domain"). -/
theorem isReduced_chart (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsReduced (presheafValue (chartDatum (w := w) ϖ)) := by
  haveI := isDomain_chart (w := w) ϖ hK₀
  infer_instance

end WeightedParity
