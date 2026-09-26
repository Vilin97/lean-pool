/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportProduct
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The divergence-free condition on time slices

This file formalizes the Fubini reduction behind `lem:divfree-slice` and `eq:divfree-ae`
of `paper/ckn.tex`.  Clause (S2) of `def:sws` pairs the solution against the space-time
test functions `∫ Σᵢ uᵢ ∂ᵢψ`.  Testing with a product `ψ₀(x)θ(t)` of a spatial test
function `ψ₀ ∈ C_c^∞(Ω)` and a time cutoff `θ ∈ C_c^∞(I)`, then applying Fubini,
separates the time variable and shows that

  `∫_Ω Σᵢ uᵢ(x,s) ∂ᵢψ₀(x) dx = 0`

for almost every `s ∈ I`.  The null set a priori depends on `ψ₀`; obtaining one common
null set requires a countable `C¹`-dense family of test functions and is not formalized
here.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! ## The product test function -/

/-- The topological support computed with the parabolic topology agrees with the one
computed with the product topology, through the homeomorphism `parabolicHomeomorph`. -/
private theorem tsupport_parabolic_eq (f : ParabolicPoint → ℝ) :
    tsupport f = parabolicHomeomorph ⁻¹' (tsupport fun q : Vec3 × ℝ => f q) := by
  have hsupp : Function.support f
      = parabolicHomeomorph ⁻¹' (Function.support fun q : Vec3 × ℝ => f q) := by
    ext z
    rw [Set.mem_preimage, Function.mem_support, Function.mem_support]
    exact Iff.rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

/-- The spatial partial derivative of a product `ψ(x)θ(t)`. -/
private theorem spatialPartial_mul (ψ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun z : ParabolicPoint => ψ z.1 * θ z.2) i z
      = θ z.2 * (fderiv ℝ ψ z.1) (basisVec i) := by
  have hd : DifferentiableAt ℝ ψ z.1 := (hψ.differentiable (by simp)) z.1
  unfold spatialPartial
  rw [show (fun x : Vec3 => (fun z : ParabolicPoint => ψ z.1 * θ z.2) (x, z.2))
        = (fun x : Vec3 => ψ x * θ z.2) from rfl,
    fderiv_mul_const hd (θ z.2), _root_.smul_apply, smul_eq_mul]

/-- A smooth spatial function supported in `Ω` has vanishing derivative outside `Ω`. -/
private theorem fderiv_eq_zero_of_tsupport_subset {ψ : Vec3 → ℝ} {Ω : Set Vec3}
    (h : tsupport ψ ⊆ Ω) {x : Vec3} (hx : x ∉ Ω) : fderiv ℝ ψ x = 0 := by
  have hx' : x ∉ tsupport ψ := fun hmem => hx (h hmem)
  have hev : ψ =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) :=
    Filter.eventually_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx')
      (fun y hy => by
        by_contra hne
        exact hy (subset_tsupport ψ (Function.mem_support.mpr hne)))
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const_apply]

/-- The product of a spatial test function and a time cutoff is a space-time test
function, with support contained in the product of the two supports. -/
private theorem mul_mem_spaceTimeTestFunction {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 → ℝ}
    {θ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ I) :
    (fun z : Vec3 × ℝ => ψ z.1 * θ z.2) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  have hts : tsupport (fun z : Vec3 × ℝ => ψ z.1 * θ z.2) = tsupport ψ ×ˢ tsupport θ :=
    CKN.tsupport_mul_prod_eq ψ θ
  refine ⟨?_, ?_, ?_⟩
  · exact (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  · have hcomp : IsCompact (tsupport (fun z : Vec3 × ℝ => ψ z.1 * θ z.2)) := by
      rw [hts]
      exact IsCompact.prod hψc hθc
    exact hcomp
  · have hsub : tsupport ψ ×ˢ tsupport θ ⊆ Ω ×ˢ I := Set.prod_mono hψΩ hθI
    rw [hts]
    exact hsub

/-- The integrand `Σᵢ uᵢ ∂ᵢ(ψ·θ)` vanishes outside `supp ψ × supp θ`: if the spatial
point is outside `supp ψ` the spatial derivative vanishes, and if the time is outside
`supp θ` the time cutoff vanishes. -/
private theorem support_integrand_subset {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u : ParabolicPoint → Vec3) :
    Function.support
        (fun z : ParabolicPoint =>
          ∑ i, u z i * spatialPartial (fun z : ParabolicPoint => ψ z.1 * θ z.2) i z)
      ⊆ parabolicHomeomorph ⁻¹' (tsupport ψ ×ˢ tsupport θ) := by
  intro z hz
  simp only [Set.mem_preimage, parabolicHomeomorph_apply, Set.mem_prod]
  by_contra hcon
  simp only [not_and_or] at hcon
  have hz0 : (fun z : ParabolicPoint => ∑ i, u z i *
      spatialPartial (fun z : ParabolicPoint => ψ z.1 * θ z.2) i z) z = 0 := by
    simp only
    apply Finset.sum_eq_zero
    intro i _
    rw [spatialPartial_mul ψ θ hψ i z]
    rcases hcon with h1 | h2
    · rw [fderiv_eq_zero_of_tsupport_subset (subset_refl (tsupport ψ)) h1]
      simp only [zero_apply, mul_zero]
    · have hθ0 : θ z.2 = 0 := by
        by_contra hne
        exact h2 (subset_tsupport θ (by simpa only [Function.mem_support] using hne))
      rw [hθ0, zero_mul, mul_zero]
  exact (Function.mem_support.mp hz) hz0

/-! ## The slice integral -/

/-- Pointwise identification of the spatial integrand: the derivative of the product
`ψ(x)φ(t)` splits off the time factor. -/
private theorem integrand_slice_eq {u : ParabolicPoint → Vec3} {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (φ : ℝ → ℝ) (t : ℝ) (x : Vec3) :
    (∑ i, u (x, t) i * spatialPartial (fun z : ParabolicPoint => ψ z.1 * φ z.2) i (x, t))
      = φ t * (∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [spatialPartial_mul ψ φ hψ i (x, t)]
  ring

/-- The spatial integral of the space-time integrand equals the time factor times the
slice functional. -/
private theorem integral_slice_eq {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψΩ : tsupport ψ ⊆ Ω) (φ : ℝ → ℝ) (t : ℝ) :
    ∫ x, (∑ i, u (x, t) i * spatialPartial (fun z : ParabolicPoint => ψ z.1 * φ z.2) i (x, t))
      = φ t * (∫ x in Ω, ∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) := by
  have hpt : ∀ x : Vec3,
      (∑ i, u (x, t) i * spatialPartial (fun z : ParabolicPoint => ψ z.1 * φ z.2) i (x, t))
        = φ t * (∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) :=
    fun x => integrand_slice_eq hψ φ t x
  have hset : ∀ x ∉ Ω, (∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro i _
    rw [fderiv_eq_zero_of_tsupport_subset hψΩ hx]
    simp only [zero_apply, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    setIntegral_eq_integral_of_forall_compl_eq_zero hset]

/-- Applying clause (S2) to the product `ψ(x)θ(t)` and Fubini shows that the time
integral `∫_I θ(s) F(s) ds` of the slice functional vanishes.  This is the reduction
behind `eq:divfree-ae`. -/
private theorem sliceIntegral_time_eq_zero {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    ∫ t, θ t * (∫ x in Ω, ∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) = 0 := by
  let Ψ : ParabolicPoint → ℝ := fun z => ψ z.1 * θ z.2
  let g : ParabolicPoint → ℝ := fun z => ∑ i, u z i * spatialPartial Ψ i z
  have hΨmem : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    mul_mem_spaceTimeTestFunction hψ hψc hψΩ hθ hθc hθI
  obtain ⟨hgint, hgzero⟩ := hS2 Ψ hΨmem
  have hsuppΨ : Function.support g ⊆ tsupport Ψ := by
    rw [tsupport_parabolic_eq Ψ]
    rw [show tsupport (fun q : Vec3 × ℝ => Ψ q) = tsupport ψ ×ˢ tsupport θ from
      CKN.tsupport_mul_prod_eq ψ θ]
    exact support_integrand_subset hψ u
  have hgInt : Integrable g volume :=
    (integrableOn_iff_integrable_of_support_subset hsuppΨ).mp hgint
  have hgInt' : Integrable g ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hgInt
  have hoff : ∀ z ∉ spaceTimeSet Ω I, g z = 0 := by
    intro z hz
    have hbridge : tsupport Ψ ⊆ spaceTimeSet Ω I := by
      rw [tsupport_parabolic_eq Ψ, parabolicHomeomorph_preimage]
      exact hΨmem.2.2
    have hz' : z ∉ tsupport Ψ := fun hmem => hz (hbridge hmem)
    exact not_not.mp (fun hne => hz' (hsuppΨ (Function.mem_support.mpr hne)))
  have hfull : ∫ z, g z ∂volume = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
    exact hgzero
  have hFubini : ∫ z, g z ∂volume = ∫ t, ∫ x, g (x, t) := integral_prod_symm g hgInt'
  have hmain : ∫ t, ∫ x, g (x, t)
      = ∫ t, θ t * (∫ x in Ω, ∑ i, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [g, Ψ]
    exact integral_slice_eq hψ hψΩ θ t
  rw [← hfull, hFubini, hmain]

/-! ## Local integrability of the slice functional -/

/-- The slice functional `s ↦ ∫_Ω Σᵢ uᵢ(x,s) ∂ᵢψ(x) dx` is locally integrable on `I`.
Around each interior time a smooth bump equal to `1` there turns the space-time
integrand into the slice integrand, which clause (S2) makes integrable. -/
private theorem locallyIntegrableOn_sliceIntegral {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) (hI : IsOpen I) :
    LocallyIntegrableOn
      (fun s => ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i)) I volume := by
  intro s₀ hs₀
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs₀)
  let c : ContDiffBump s₀ := ⟨ε / 4, ε / 2, by linarith only [hεpos], by linarith only [hεpos]⟩
  let f : ℝ → ℝ := ⇑c
  have hf_cd : ContDiff ℝ (⊤ : ℕ∞) f := c.contDiff
  have hf_cs : HasCompactSupport f := c.hasCompactSupport
  have hf_ts : tsupport f ⊆ I := by
    rw [show tsupport f = closedBall s₀ (ε / 2) from c.tsupport_eq]
    exact (closedBall_subset_ball (by linarith only [hεpos])).trans hεsub
  have hf_one : ∀ y ∈ closedBall s₀ (ε / 4), f y = 1 := fun y hy =>
    c.one_of_mem_closedBall hy
  let Ψ : ParabolicPoint → ℝ := fun z => ψ z.1 * f z.2
  let g : ParabolicPoint → ℝ := fun z => ∑ i, u z i * spatialPartial Ψ i z
  have hΨmem : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    mul_mem_spaceTimeTestFunction hψ hψc hψΩ hf_cd hf_cs hf_ts
  obtain ⟨hgint, -⟩ := hS2 Ψ hΨmem
  have hsuppΨ : Function.support g ⊆ tsupport Ψ := by
    rw [tsupport_parabolic_eq Ψ]
    rw [show tsupport (fun q : Vec3 × ℝ => Ψ q) = tsupport ψ ×ˢ tsupport f from
      CKN.tsupport_mul_prod_eq ψ f]
    exact support_integrand_subset hψ u
  have hgInt : Integrable g volume :=
    (integrableOn_iff_integrable_of_support_subset hsuppΨ).mp hgint
  have hgInt' : Integrable g ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hgInt
  have hH : Integrable (fun s => ∫ x, g (x, s) ∂volume) volume := hgInt'.integral_prod_right
  have hH_on : IntegrableOn (fun s => ∫ x, g (x, s) ∂volume) (ball s₀ (ε / 4)) volume :=
    hH.integrableOn
  refine ⟨ball s₀ (ε / 4), mem_nhdsWithin.mpr
    ⟨ball s₀ (ε / 4), isOpen_ball, mem_ball_self (by linarith only [hεpos]),
      fun y hy => hy.1⟩, ?_⟩
  refine hH_on.congr ?_
  filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with s hs
  simp only [g, Ψ]
  rw [integral_slice_eq hψ hψΩ f s, hf_one s (ball_subset_closedBall hs), one_mul]

/-! ## The main statements -/

/-- The weak divergence-free condition for the spatial slice at time `s`: the slice
`u(·,s)` is divergence-free against every compactly supported smooth spatial test
function contained in `Ω`, as in `eq:divfree-common` of `paper/ckn.tex`. -/
def SliceDivergenceFree (Ω : Set Vec3) (u : ParabolicPoint → Vec3) (s : ℝ) : Prop :=
  ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0

/-- The Fubini reduction of `lem:divfree-slice` and `eq:divfree-ae`: if the space-time
test pairing (S2) of `def:sws` vanishes, then for each spatial test function `ψ₀` the
slice pairing vanishes for almost every time in `I`.  The null set may depend on `ψ₀`. -/
theorem divfree_slice_weak {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    (hI : IsOpen I) :
    ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
  intro ψ hψ hψc hψΩ
  have hFint : LocallyIntegrableOn
      (fun s => ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i)) I volume :=
    locallyIntegrableOn_sliceIntegral hS2 hψ hψc hψΩ hI
  have hzero : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ I →
      ∫ x, θ x • (∫ y in Ω, ∑ i, u (y, x) i * (fderiv ℝ ψ y) (basisVec i)) ∂volume = 0 := by
    intro θ hθ hθc hθI
    simpa only [smul_eq_mul] using
      sliceIntegral_time_eq_zero hS2 hψ hψc hψΩ hθ hθc hθI
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hI hFint hzero
  exact (ae_restrict_iff' hI.measurableSet).mpr hae

/-- The divergence-free slice conclusion read off from the suitable weak solution class
of `def:sws`: for each spatial test function `ψ₀` the slice pairing vanishes for almost
every time in `I`. -/
theorem divfree_slice_weak_of_suitable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) :
    ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 :=
  divfree_slice_weak h.2.2.2.2.2.2.1 h.2.1

end CKN
