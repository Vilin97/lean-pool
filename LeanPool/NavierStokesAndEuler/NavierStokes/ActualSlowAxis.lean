/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowRecursion
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActivationHolomorphic
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransitionRamp

/-!
# The actual natural/ACT base in the all-order local axis recursion

The finite base functions below are the constructed holomorphic natural/ACT
functions. Every regularity field required by `SlowRecursion` is derived
from those functions. In particular the angular slow coefficient is `C*f`.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSlowAxis

open Set Filter
open scoped Topology ContDiff
open ActivationHolomorphic (InitialTube CField signedSquare)
open SlowRecursion (AxisFunction Coefficient)

/-- A conjugation-invariant open neighborhood whose real points remain in
the real profile domain. It retains the entire closed physical window. -/
noncomputable def parameterDomain (Ω : Set ℂ) : Set ℂ :=
  Ω ∩ (starRingEnd ℂ) ⁻¹' Ω ∩ Complex.re ⁻¹' ReferencePath.parameterInterval

theorem parameterDomain_open {Ω : Set ℂ} (hΩ : IsOpen Ω) : IsOpen (parameterDomain Ω) :=
  (hΩ.inter (hΩ.preimage Complex.continuous_conj)).inter
    (ReferencePath.parameterInterval_open.preimage Complex.continuous_re)

theorem parameterDomain_subset (Ω : Set ℂ) : parameterDomain Ω ⊆ Ω := fun _ hz => hz.1.1

theorem parameterDomain_conjugate {Ω : Set ℂ} {z : ℂ} (hz : z ∈ parameterDomain Ω) :
    starRingEnd ℂ z ∈ parameterDomain Ω := by
  exact ⟨⟨hz.1.2, by simpa using hz.1.1⟩, by simpa using hz.2⟩

theorem parameterDomain_real {Ω : Set ℂ}
    (hreal : ∀ eta ∈ Icc (-1 : ℝ) 1, (eta : ℂ) ∈ Ω)
    {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) : (eta : ℂ) ∈ parameterDomain Ω := by
  refine ⟨⟨hreal eta heta, ?_⟩, ?_⟩
  · simpa using hreal eta heta
  · exact NaturalAxisCoefficients.original_interval_interior heta

theorem parameterDomain_real_interval {Ω : Set ℂ} {eta : ℝ}
    (heta : (eta : ℂ) ∈ parameterDomain Ω) : eta ∈ ReferencePath.parameterInterval := heta.2

theorem parameterTube_conjugate (J : AxisCoefficientSpace.Window) {ρ : ℝ} {z : ℂ}
    (hz : z ∈ AxisHolomorphic.parameterTube J ρ) :
    starRingEnd ℂ z ∈ AxisHolomorphic.parameterTube J ρ := by
  rcases hz with ⟨x, hx, hd⟩
  refine ⟨x, hx, ?_⟩
  simpa only [Complex.dist_conj_comm, Complex.conj_ofReal] using hd

theorem smallTube_subset_domain {ρ τ : ℝ} (hτρ : τ ≤ ρ) (hτ : τ ≤ 1 / 40) :
    AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow τ ⊆
      parameterDomain (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ) := by
  intro z hz
  rcases hz with ⟨x, hx, hd⟩
  have hzρ : z ∈ AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ :=
    ⟨x, hx, lt_of_lt_of_le hd hτρ⟩
  refine ⟨⟨hzρ, parameterTube_conjugate _ hzρ⟩, ?_⟩
  have hre : |z.re - x| ≤ dist z (x : ℂ) := by
    simpa only [dist_eq_norm, Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (z - (x : ℂ))
  have hb := abs_lt.mp (lt_of_le_of_lt hre hd)
  change -21 / 20 ≤ x ∧ x ≤ 21 / 20 at hx
  change -11 / 10 < z.re ∧ z.re < 11 / 10
  constructor <;> linarith [hx.1, hx.2, hb.1, hb.2]

theorem histories_congr_below {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    {X eta : ℝ} (hX : 0 ≤ X) (hP0 : P.pressure0 eta = Q.pressure0 eta)
    (hf : ∀ Y ∈ Icc (0 : ℝ) X, P.f (Y, eta) = Q.f (Y, eta))
    (hu : ∀ Y ∈ Icc (0 : ℝ) X, P.U (Y, eta) = Q.U (Y, eta)) :
    P.Ubar (X, eta) = Q.Ubar (X, eta) ∧ P.pressure (X, eta) = Q.pressure (X, eta) := by
  constructor
  · unfold ProfileHistories.Profiles.Ubar ProfileHistories.average
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    exact hu (t * X) ⟨mul_nonneg ht'.1 hX, mul_le_of_le_one_left hX ht'.2⟩
  · unfold ProfileHistories.Profiles.pressure
    rw [hP0]
    congr 1
    unfold ProfileHistories.primitive
    apply intervalIntegral.integral_congr
    intro Y hY
    have hY' : Y ∈ Icc (0 : ℝ) X := by simpa only [uIcc_of_le hX] using hY
    change P.f (Y, eta) ^ 2 = Q.f (Y, eta) ^ 2
    rw [hf Y hY']

section ActualBase

variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
variable (E : InitialTube N h P0 R Ω)

include E in
theorem domain {S : ℝ} (hS : 0 < S) : SlowRecursion.Domain S (parameterDomain Ω) h where
  positive := hS
  open_set := parameterDomain_open E.isOpen
  conjugate := fun _ hz => parameterDomain_conjugate hz
  denominator := fun z hz => E.elliptic_ne_zero z hz.1.1

/-- Fields, given by `![E.f T κ δ, E.U T κ δ, E.Ubar T κ δ, E.Pi T κ δ]`. -/
noncomputable def fields (T κ δ : ℝ) : Fin 4 → CField :=
  ![E.f T κ δ, E.U T κ δ, E.Ubar T κ δ, E.Pi T κ δ]

/-- Real fields, given by `let P := StressActivation.FromReference.histories N hT hδ hδT κ P0
hP0 ![P.f, P.U, P.Ubar, P.pressure]`. -/
noncomputable def realFields {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) :
    Fin 4 → ProfileHistories.Field :=
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  ![P.f, P.U, P.Ubar, P.pressure]

theorem fields_regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (i : Fin 4) :
    ActivationHolomorphic.Regular univ Ω (signedSquare (fields E T κ δ i)) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.signed_regular hT hδ hδT κ
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

theorem fields_real {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (i : Fin 4) (x : ℝ) {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval) :
    fields E T κ δ i (x, (eta : ℂ)) = (realFields (N := N) hT hδ hδT κ hP0 i (x, eta) : ℂ) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.real_profiles hT hδ hδT κ hP0 x heta
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

/-- Each base component is an actual member of the compatible function
algebra; no separate jet data or extension hypothesis is supplied. -/
noncomputable def element {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) : AxisFunction S (parameterDomain Ω) :=
  ⟨signedSquare (fields E T κ δ i), {
    smooth := (fields_regular E hT hδ hδT κ i).smooth.mono
      (Set.prod_mono (subset_univ _) (parameterDomain_subset Ω))
    holomorphic := fun r _ => ((fields_regular E hT hδ hδT κ i).holomorphic r (mem_univ r)).mono
      (parameterDomain_subset Ω)
    even := fun z _ r _ => ActivationHolomorphic.signedSquare_even _ z r
    real := by
      intro r _ eta heta
      change (fields E T κ δ i (r ^ 2, (eta : ℂ))).im = 0
      rw [fields_real E hT hδ hδT κ hP0 i _ (parameterDomain_real_interval heta)]
      rfl }⟩

theorem element_complexProfile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    SlowRecursion.complexProfile (element E hT hδ hδT κ hP0 S i) (X, z) = fields E T κ δ i (X, z)
        := by
  change fields E T κ δ i (Real.sqrt X ^ 2, z) = _
  rw [Real.sq_sqrt hX]

theorem element_profile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (X, eta) =
      realFields (N := N) hT hδ hδT κ hP0 i (X, eta) := by
  have hc := (element_complexProfile E hT hδ hδT κ hP0 S i hX (eta : ℂ)).trans
    (fields_real E hT hδ hδT κ hP0 i X heta)
  exact congrArg Complex.re hc

theorem realFields_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (i : Fin 4) : ContDiffOn ℝ ∞ (realFields (N := N) hT hδ hδT κ hP0 i) N.radialDomain.carrier :=
        by
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  fin_cases i
  · exact P.f_smooth
  · exact P.U_smooth
  · exact P.Ubar_smooth
  · exact P.pressure_smooth

theorem real_domain_mem (N : ReferencePath.Input) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) : (X, eta) ∈ N.radialDomain.carrier := by
  refine ⟨?_, heta⟩
  have := mul_nonneg N.scale_pos.le hX
  linarith

/-- The canonical right jets agree with the actual smooth ACT jets at the
axis as well as at every positive radius. -/
theorem element_right_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) (k : ℕ) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    iteratedDerivWithin k (fun Y => SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (Y, eta))
        (Ici 0) X =
      iteratedDeriv k (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) X := by
  have he : EqOn (fun Y => SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (Y, eta))
      (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) (Ici 0) :=
    fun Y hY => element_profile E hT hδ hδT κ hP0 S i hY heta
  rw [iteratedDerivWithin_congr he hX]
  have hs : ContDiffAt ℝ ∞ (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) X :=
    ((realFields_smooth hT hδ hδT κ hP0 i).contDiffAt
      (N.radialDomain.isOpen.mem_nhds (real_domain_mem N hX heta))).comp X
      (contDiffAt_id.prodMk contDiffAt_const)
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0)
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)) hX]

theorem element_profile_germ {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 < X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) =ᶠ[𝓝 (X, eta)]
      realFields (N := N) hT hδ hδT κ hP0 i := by
  filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
    (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from ⟨hX, heta⟩)] with p hp
  exact element_profile E hT hδ hδT κ hP0 S i hp.1.le hp.2

/-- Base, constructed using `SlowRecursion.makeBase`. -/
noncomputable def base {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) : Coefficient S (parameterDomain Ω) :=
  SlowRecursion.makeBase (domain E hS)
    (SlowRecursion.realConstant S (parameterDomain Ω) C * element E hT hδ hδT κ hP0 S 0)
    (element E hT hδ hδT κ hP0 S 1) (element E hT hδ hδT κ hP0 S 2)
    (element E hT hδ hδT κ hP0 S 3)

theorem base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := base E hT hδ hδT κ hP0 C hS
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A 3) (X, eta) = P.pressure (X, eta) := by
  have hv (i : Fin 4) := element_profile E hT hδ hδT κ hP0 S i hX heta
  refine ⟨?_, hv 1, ?_, hv 3⟩
  · change ((C : ℂ) * element E hT hδ hδT κ hP0 S 0 (Real.sqrt X, (eta : ℂ))).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (C * ·) (hv 0)
  · change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt X, (eta : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt X, (eta : ℂ))).re = _
    exact congrArg₂ (· - ·) (hv 2) (hv 1)

theorem base_beta_value {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2))
    (heta : (eta : ℂ) ∈ parameterDomain Ω) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (base E hT hδ hδT κ hP0 C hS 4) (X, eta) =
      SlowDivergence.radialFlux h 0 P.U (X, eta) / X := by
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  let u := element E hT hδ hδT κ hP0 S 1
  let k := element E hT hδ hδT κ hP0 S 2 - u
  have hu : SlowRecursion.profile u =ᶠ[𝓝 (X, eta)] P.U :=
    element_profile_germ E hT hδ hδT κ hP0 S 1 hX.1 (parameterDomain_real_interval heta)
  have hk : SlowRecursion.profile k =ᶠ[𝓝 (X, eta)] PositiveAxisSystem.averageDefect P.U := by
    filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
      (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from
        ⟨hX.1, parameterDomain_real_interval heta⟩)] with q hq
    change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt q.1, (q.2 : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt q.1, (q.2 : ℂ))).re = _
    exact congrArg₂ (· - ·)
      (element_profile E hT hδ hδT κ hP0 S 2 hq.1.le hq.2)
      (element_profile E hT hδ hδT κ hP0 S 1 hq.1.le hq.2)
  have hb := congrArg Complex.re (SlowRecursion.betaOperator_value (domain E hS) 0 u k hX heta)
  have hcompare : PositiveAxisExistence.newBeta h 0 (SlowRecursion.profile u)
      (SlowRecursion.profile k) (X, eta) =
      PositiveAxisSystem.betaValue h 0 eta (PositiveAxisSystem.actualJet P.U (X, eta))
        (PositiveAxisSystem.actualJet (PositiveAxisSystem.averageDefect P.U) (X, eta)) := by
    simp only [PositiveAxisExistence.newBeta, PositiveAxisSystem.slowPower, Nat.cast_zero,
        mul_zero, zero_mul,
      PositiveAxisSystem.betaValue, PositiveAxisSystem.actualJet, hu.eq_of_nhds, hk.eq_of_nhds,
      SimilarityProfile.partialEta, hu.fderiv_eq, hk.fderiv_eq]
  exact hb.trans (hcompare.trans (PositiveAxisSystem.betaValue_averageDefect N.radialDomain
      P.U_smooth h 0
    (real_domain_mem N hX.1.le (parameterDomain_real_interval heta)) hX.1.ne'))

/-- A fixed radial rectangle strictly containing the entire initial collar. -/
noncomputable def axisRadius (N : ReferencePath.Input) (δ : ℝ) : ℝ :=
  Real.sqrt (N.endpoint * Real.exp δ) + 1

theorem axisRadius_pos (N : ReferencePath.Input) (δ : ℝ) : 0 < axisRadius N δ := by
  unfold axisRadius
  positivity

theorem collar_lt_square (N : ReferencePath.Input) (δ : ℝ) :
    N.endpoint * Real.exp δ < axisRadius N δ ^ 2 := by
  have hp : 0 ≤ N.endpoint * Real.exp δ := mul_nonneg N.endpoint_pos.le (Real.exp_pos δ).le
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (N.endpoint * Real.exp δ)
  unfold axisRadius
  nlinarith

/-- Hierarchy used in actual slow axis. -/
noncomputable def hierarchy {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) (C : ℝ) :=
  let hc := axisRadius_pos N δ
  let c := domain E (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0)
  SlowRecursion.buildLocalHierarchy c hc zero_lt_one C
    (base E hT hδ hδT κ hP0 C (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0))

theorem hierarchy_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := hierarchy E hT hδ hδT κ hP0 C
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) := by
  dsimp only
  simp only [(hierarchy E hT hδ hδT κ hP0 C).starts]
  exact base_values E hT hδ hδT κ hP0 C _ hX heta

theorem hierarchy_physical_swirl {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    {C : ℝ} (hC : C ≠ 0) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := hierarchy E hT hδ hδT κ hP0 C
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    Real.sqrt (2 * X) * SlowRecursion.profile (A.coefficients 0 0) (X, eta) / C = P.E (X, eta) := by
  have hv := (hierarchy_base_values E hT hδ hδT κ hP0 C hX heta).1
  dsimp only
  rw [hv]
  unfold ProfileHistories.Profiles.E
  field_simp

theorem hierarchy_on_collar {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) (C : ℝ)
    {n : ℕ} (hn : 0 < n) {X eta : ℝ} (hX : 0 < X)
    (hcollar : X ≤ N.endpoint * Real.exp δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    SlowRecursion.OrderEquations h C (hierarchy E hT hδ hδT κ hP0 C).coefficients n (X, eta) :=
  (hierarchy E hT hδ hδT κ hP0 C).equations n hn X
    ⟨hX, lt_of_le_of_lt hcollar (collar_lt_square N δ)⟩ eta (parameterDomain_real E.real_mem heta)

end ActualBase

section NaturalConstruction

variable {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ} {P0 : ℝ → ℝ}
variable (hp : PressureDatum.Admissible g a cap) (hP0 : P0 = PressureDatum.pressure g a)
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

include hp hP0 hsmall hσ in
theorem exists_tube_of_pressure_eq :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 / Λ)
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ)) := by
  subst P0
  exact ActivationHolomorphic.exists_initialTube hp F hΛ hsmall hσ

/-- Tube width, given by `Classical.choose (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)`. -/
noncomputable def tubeWidth : ℝ := Classical.choose (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall
    hσ)

theorem tubeWidth_pos : 0 < tubeWidth hp hP0 F hΛ hsmall hσ :=
  (Classical.choose_spec (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)).1

/-- This witness is obtained from the actual coefficient-space natural
solution and the proved pressure integral, not supplied by the caller. -/
noncomputable def constructedTube : InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 /
    Λ)
    (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F hΛ
        hsmall hσ)) :=
  Classical.choice (Classical.choose_spec (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)).2

include hp hP0 in
theorem actualPressure_smooth : ContDiff ℝ ∞ P0 := by
  rw [hP0]
  exact PressureDatum.pressure_contDiff hp

/-- From natural, given by `hierarchy (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
(actualPressure_smooth hp hP0) C`. -/
noncomputable def fromNatural {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :=
  hierarchy (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ (actualPressure_smooth hp hP0) C

theorem fromNatural_window {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (eta : ℂ) ∈ parameterDomain
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F hΛ
          hsmall hσ)) :=
  parameterDomain_real (constructedTube hp hP0 F hΛ hsmall hσ).real_mem heta

theorem fromNatural_uniform_tube :
    ∃ τ : ℝ, 0 < τ ∧
      AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow τ ⊆
        parameterDomain (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
          (tubeWidth hp hP0 F hΛ hsmall hσ)) := by
  exact ⟨min (tubeWidth hp hP0 F hΛ hsmall hσ) (1 / 40),
    lt_min (tubeWidth_pos hp hP0 F hΛ hsmall hσ) (by norm_num),
    smallTube_subset_domain (min_le_left _ _) (min_le_right _ _)⟩

theorem fromNatural_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let P := StressActivation.FromReference.histories (ReferenceJetBounds.referenceInput F hΛ)
      hT hδ hδT κ P0 (actualPressure_smooth hp hP0)
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) :=
  hierarchy_base_values (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
    (actualPressure_smooth hp hP0) C hX heta

theorem fromNatural_positive_order {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : 0 < X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    SlowRecursion.OrderEquations h C
      (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n (X, eta) :=
  hierarchy_on_collar (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
    (actualPressure_smooth hp hP0) C hn hX hcollar heta

theorem fromNatural_initial {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {X eta : ℝ}
    (hX : 0 ≤ X) (hinitial : X ≤ 4 / Λ) (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * F.family.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = F.family.U (X, eta) := by
  have hv := fromNatural_base_values hp hP0 F hΛ hsmall hσ hT hδ hδT κ hX heta
  have he : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint := hinitial
  dsimp only at hv ⊢
  refine ⟨hv.1.trans ?_, hv.2.1.trans ?_⟩
  · change C * StressActivation.FromReference.f _ T κ δ (X, eta) = _
    rw [StressActivation.FromReference.f_eq_reference _ T κ δ he,
      ReferencePath.Input.refF_eq_natural_initial _ δ he]
    rfl
  · change StressActivation.FromReference.U _ T κ δ (X, eta) = _
    rw [StressActivation.FromReference.U_eq_reference _ T κ δ he,
      ReferencePath.Input.refU_eq_natural_initial _ δ he]
    rfl

theorem fromNatural_stock_prefix {T δ κ w₁ w₂ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit)
    (hb : δ ≤ (TransitionRamp.ofNatural F.family hΛ hsmall hδ hδT (actualPressure_smooth hp
        hP0)).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {X eta : ℝ} (hX : 0 ≤ X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * Q.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = Q.Ubar (X, eta) - Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = Q.pressure (X, eta) := by
  let P := StressActivation.FromReference.histories (ReferenceJetBounds.referenceInput F hΛ)
    hT hδ hδT κ P0 (actualPressure_smooth hp hP0)
  let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
    (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
  have he (Y : ℝ) (hY : Y ≤ X) : Q.f (Y, eta) = P.f (Y, eta) ∧ Q.U (Y, eta) = P.U (Y, eta) :=
    TransitionRamp.physical_fields_eq_activation F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) hT hb hw₁ hw₂ heta (le_trans hY hcollar)
  have hhist := histories_congr_below Q P hX rfl
    (fun Y hY => (he Y hY.2).1) (fun Y hY => (he Y hY.2).2)
  have hv := fromNatural_base_values hp hP0 F hΛ hsmall hσ hT hδ hδT κ hX heta
  dsimp only at hv ⊢
  exact ⟨hv.1.trans (congrArg (C * ·) (he X le_rfl).1.symm),
    hv.2.1.trans (he X le_rfl).2.symm,
    hv.2.2.1.trans (congrArg₂ (· - ·) hhist.1.symm (he X le_rfl).2.symm),
    hv.2.2.2.trans hhist.2.symm⟩

theorem fromNatural_stock_fields {T δ κ w₁ w₂ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (hC : C ≠ 0)
    (hb : δ ≤ (TransitionRamp.ofNatural F.family hΛ hsmall hδ hδT (actualPressure_smooth hp
        hP0)).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {X eta : ℝ} (hX : 0 ≤ X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
    Real.sqrt (2 * X) * SlowRecursion.profile (A.coefficients 0 0) (X, eta) / C = Q.E (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = Q.pressure (X, eta) := by
  have hv := fromNatural_stock_prefix hp hP0 F hΛ hsmall hσ (κ := κ) hT hδ hδT hb hw₁ hw₂ hX
      hcollar heta
  refine ⟨?_, hv.2.1, hv.2.2.2⟩
  rw [hv.1]
  unfold ProfileHistories.Profiles.E
  field_simp

theorem fromNatural_profiles_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞
      (SlowRecursion.profile ((fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n i))
      (Ico (0 : ℝ) (axisRadius (ReferenceJetBounds.referenceInput F hΛ) δ ^ 2) ×ˢ
        PositiveAxisExistence.realParameterDomain (parameterDomain
          (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F
              hΛ hsmall hσ)))) :=
  (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).profiles_smooth (axisRadius_pos _ _)
    (parameterDomain_open (constructedTube hp hP0 F hΛ hsmall hσ).isOpen) n i

theorem fromNatural_zero_axis {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {n : ℕ} (hn : 0 < n)
    (i : Fin 5) {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n i (0, (eta : ℂ)) = 0 :=
  (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).zero_axis n hn i (eta : ℂ)
    (fromNatural_window hp hP0 F hΛ hsmall hσ heta)

theorem fromNatural_axis_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (n : ℕ) (i : Fin 5) (k : ℕ)
    {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    iteratedDerivWithin k (fun X => SlowRecursion.profile (A.coefficients n i) (X, eta)) (Ici 0) 0 =
      ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
        iteratedDeriv (2 * k) (fun r => (A.coefficients n i (r, (eta : ℂ))).re) 0 :=
  SlowRecursion.profile_axis_jet (axisRadius_pos _ _) _
    (fromNatural_window hp hP0 F hΛ hsmall hσ heta) k

end NaturalConstruction

end NavierStokes.ActualSlowAxis
