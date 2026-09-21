/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import LeanPool.Malliavin.Malliavin.Simplex
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Iterated-integral Hilbert laws

Rung 2 of the Clark--Ocone ladder: operators `Jₙ(fₙ)` with the Hilbert-space laws of iterated
Itô integrals.

We axiomatize the second-moment behaviour of a Wiener process (centered, with
covariance function `min s t`) as `IsWienerCov`, define the stochastic
integral of finitary step functions against such a process, and prove:

* linearity of the step integral (`stepIntegral_add`, `stepIntegral_smul`),
* vanishing expectation (`integral_stepIntegral`),
* the Itô isometry on step functions (`ito_isometry`).

The finite-sum calculation is followed by `IteratedIntegralFamily`, the downstream-facing
continuous-linear-map interface on `L²((ℝ≥0)ⁿ)`.  It records the simplex isometry, centering,
and orthogonality between different orders.  These laws alone do not characterize stochastic
integration on ordered boxes; the later `IteratedIntegralFamily.IsBrownian` predicate records that
additional link.  The selected law-level family assembles all positive simplex kernels into one
Hilbert sum.  The construction selects its onto branch only when process-measurable `L²` exhausts
the separable ambient space, so unrelated ambient randomness is never absorbed into the tower.
-/

namespace Malliavin

open MeasureTheory
open scoped NNReal

universe u_1 u_2 u_3 u_4 u_7 u_8

recall MeasureTheory.trim_eq_map {α : Type u_1} {m m0 : MeasurableSpace α}
    {μ : @Measure α m0} (hm : m ≤ m0) :
    μ.trim hm = @Measure.map α α m0 m id μ

recall MeasureTheory.trim_measurableSet_eq {α : Type u_1} {m m0 : MeasurableSpace α}
    {μ : @Measure α m0} {s : Set α} (hm : m ≤ m0)
    (hs : @MeasurableSet α m s) :
    (μ.trim hm) s = μ s

recall MeasureTheory.Lp.compMeasurePreservingₗᵢ {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    {β : Type u_7} [MeasurableSpace β] {μb : Measure β} (𝕜 : Type u_8)
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (f : α → β) (hf : MeasurePreserving f μ μb) : Lp E p μb →ₗᵢ[𝕜] Lp E p μ

recall MeasureTheory.Lp.compMeasurePreserving_comp_apply {α : Type u_1}
    {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] {β : Type u_7} [MeasurableSpace β] {μb : Measure β}
    {γ : Type u_8} {mγ : MeasurableSpace γ} {μc : Measure γ} (g : Lp E p μc)
    {f : β → γ} (hf : MeasurePreserving f μb μc) {f' : α → β}
    (hf' : MeasurePreserving f' μ μb) :
    (Lp.compMeasurePreserving (f ∘ f') (hf.comp hf')) g =
      (Lp.compMeasurePreserving f' hf') ((Lp.compMeasurePreserving f hf) g)

recall MeasureTheory.Lp.compMeasurePreserving_id_apply {E : Type u_4} {p : ENNReal}
    [NormedAddCommGroup E] {β : Type u_7} [MeasurableSpace β] {μb : Measure β}
    (g : Lp E p μb) : Lp.compMeasurePreserving id (MeasurePreserving.id μb) g = g

recall measurable_id'' {α : Type u_1} {m mα : MeasurableSpace α} (hm : m ≤ mα) :
    @Measurable α α mα m id

recall Submodule.mem_orthogonal_singleton_iff_inner_right {𝕜 : Type u_1}
    {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ inner 𝕜 u v = 0

recall lp.hasSum_single {α : Type u_3} {E : α → Type u_4} {p : ENNReal}
    [(i : α) → NormedAddCommGroup (E i)] [DecidableEq α] [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (f : lp E p) : HasSum (fun i ↦ lp.single p i (f i)) f

recall nonempty_equiv_of_countable {α : Type u_1} {β : Type u_2}
    [Countable α] [Infinite α] [Countable β] [Infinite β] : Nonempty (α ≃ β)

recall Orthonormal.exists_hilbertBasis_extension {𝕜 : Type u_2} [RCLike 𝕜]
    {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {s : Set E} (hs : Orthonormal 𝕜 ((↑) : s → E)) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = Subtype.val

recall HilbertBasis.mkOfOrthogonalEqBot {ι : Type u_1} {𝕜 : Type u_2}
    [RCLike 𝕜] {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E

recall MeasureTheory.memLp_indicator_iff_restrict {α : Type u_1}
    {m0 : MeasurableSpace α} {p : ENNReal} {μ : Measure α} {ε : Type u_7}
    [TopologicalSpace ε] [ESeminormedAddMonoid ε] {s : Set α} {f : α → ε}
    (hs : MeasurableSet s) : MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)

universe u₁ u₂ u₃ u₄ u₅

recall MeasureTheory.MemLp.coeFn_toLp {α : Type u₁} {E : Type u₂}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : MemLp f p μ) :
    ↑↑(MemLp.toLp f hf) =ᵐ[μ] f

recall MeasureTheory.Lp.ext {α : Type u₁} {E : Type u₂}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] {f g : Lp E p μ}
    (h : (f : α → E) =ᵐ[μ] (g : α → E)) : f = g

recall MeasureTheory.Lp.coeFn_smul {α : Type u₁} {𝕜 : Type u₂} {E : Type u₃}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c : 𝕜) (f : Lp E p μ) :
    ((c • f : Lp E p μ) : α → E) =ᵐ[μ] c • (f : α → E)

recall MeasureTheory.ae_restrict_mem {α : Type u₁} {m : MeasurableSpace α}
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ.restrict s, x ∈ s

recall MeasureTheory.ae_restrict_of_ae {α : Type u₁} {m : MeasurableSpace α}
    {μ : Measure α} {s : Set α} {q : α → Prop}
    (h : ∀ᵐ x ∂μ, q x) : ∀ᵐ x ∂μ.restrict s, q x

recall MeasureTheory.Measure.pi_pi {ι : Type u₁} {α : ι → Type u₂}
    [Fintype ι] [(i : ι) → MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (s : (i : ι) → Set (α i)) :
    Measure.pi μ (Set.univ.pi s) = ∏ i, μ i (s i)

recall MeasureTheory.Measure.restrict_apply {α : Type u₁} {m : MeasurableSpace α}
    {μ : Measure α} {s t : Set α} (ht : MeasurableSet t) :
    (μ.restrict s) t = μ (t ∩ s)

recall lp.inner_single_left {ι : Type u₁} {𝕜 : Type u₂} [RCLike 𝕜]
    {G : ι → Type u₃} [(i : ι) → NormedAddCommGroup (G i)]
    [(i : ι) → InnerProductSpace 𝕜 (G i)] [DecidableEq ι]
    (i : ι) (a : G i) (f : lp G 2) :
    inner 𝕜 (lp.single 2 i a) f = inner 𝕜 a (f i)

recall lp.eq_zero_iff_coeFn_eq_zero {α : Type u₁} {E : α → Type u₂}
    {p : ENNReal} [(i : α) → NormedAddCommGroup (E i)] {f : lp E p} :
    f = 0 ↔ (f : (i : α) → E i) = 0

recall memℓp_gen_iff {α : Type u₁} {E : α → Type u₂} {p : ENNReal}
    [(i : α) → NormedAddCommGroup (E i)] (hp : 0 < p.toReal)
    {f : (i : α) → E i} :
    Memℓp f p ↔ Summable fun i ↦ ‖f i‖ ^ p.toReal

recall lp.norm_eq_tsum_rpow {α : Type u₁} {E : α → Type u₂} {p : ENNReal}
    [(i : α) → NormedAddCommGroup (E i)] (hp : 0 < p.toReal)
    (f : lp E p) :
    ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

recall ContinuousLinearMap.hasSum {ι : Type u₁} {R : Type u₂} {R₂ : Type u₃}
    {M : Type u₄} {M₂ : Type u₅} [Semiring R] [Semiring R₂]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
    [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂}
    {L : SummationFilter ι} {f : ι → M} (φ : M →SL[σ] M₂)
    {x : M} (hf : HasSum f x L) : HasSum (fun b ↦ φ (f b)) (φ x) L

variable {Ω : Type*} [MeasureSpace Ω]

/-- Second-moment axiomatization of a centered process with the covariance
function of Brownian motion: `E[W s * W t] = min s t`. -/
structure IsWienerCov (W : ℝ≥0 → Ω → ℝ) : Prop where
  integrable_W : ∀ t, Integrable (W t)
  integrable_prod : ∀ s t, Integrable fun x => W s x * W t x
  mean_zero : ∀ t, ∫ x, W t x = 0
  covariance : ∀ s t, ∫ x, W s x * W t x = min s t

/-- Mathlib's pre-Brownian process supplies the finite second-moment interface used by the
elementary step-integral calculation below. -/
theorem isWienerCov_of_isPreBrownianReal {W : ℝ≥0 → Ω → ℝ}
    (hW : ProbabilityTheory.IsPreBrownianReal W volume) : IsWienerCov W where
  integrable_W := hW.integrable_eval
  integrable_prod := fun s t =>
    (hW.isGaussianProcess.hasGaussianLaw_eval s).memLp_two.integrable_mul
      (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  mean_zero := hW.integral_eval
  covariance := by
    let _ : IsProbabilityMeasure (volume : Measure Ω) :=
      hW.isGaussianProcess.isProbabilityMeasure
    intro s t
    have hs := (hW.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have ht := (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hcov := hW.covariance_eval s t
    rw [ProbabilityTheory.covariance_eq_sub hs ht, hW.integral_eval, hW.integral_eval,
      mul_zero, sub_zero] at hcov
    exact hcov

section Step

variable {W : ℝ≥0 → Ω → ℝ}

/-- An increasing sequence of `n + 1` times starting at `0`. -/
structure Partition (n : ℕ) where
  /-- The partition times `t 0 < t 1 < ⋯ < t n`. -/
  t : Fin (n + 1) → ℝ≥0
  /-- The partition starts at time `0`. -/
  start : t 0 = 0
  /-- The partition times are strictly increasing. -/
  mono : StrictMono t

omit [MeasureSpace Ω] in
/-- Stochastic integral of the step function taking the value `a i` on the
time interval `[P.t i, P.t (i+1)]`. -/
def stepIntegral (W : ℝ≥0 → Ω → ℝ) {n : ℕ} (P : Partition n) (a : Fin n → ℝ) : Ω → ℝ :=
  fun x => ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)

/-- Expansion of the covariance of two increments via bilinearity. -/
lemma integral_cov_sub (hW : IsWienerCov W) (u v x y : ℝ≥0) :
    ∫ z, (W v z - W u z) * (W y z - W x z)
        = min v y - min v x - min u y + min u x := by
  have hint : ∀ s t : ℝ≥0, Integrable fun z => W s z * W t z := hW.integrable_prod
  have hintAB : Integrable fun z => W v z * W y z - W v z * W x z :=
    (hint _ _).sub (hint _ _)
  have hintCD : Integrable fun z => W u z * W y z - W u z * W x z :=
    (hint _ _).sub (hint _ _)
  have hfun : (fun z => (W v z - W u z) * (W y z - W x z))
      = fun z => (W v z * W y z - W v z * W x z) - (W u z * W y z - W u z * W x z) :=
    funext fun z => by ring
  have hsplit1 : ∫ z, (W v z * W y z - W v z * W x z) - (W u z * W y z - W u z * W x z)
      = (∫ z, W v z * W y z - W v z * W x z) - (∫ z, W u z * W y z - W u z * W x z) :=
    integral_sub hintAB hintCD
  have hsplit2 : ∫ z, W v z * W y z - W v z * W x z
      = (∫ z, W v z * W y z) - (∫ z, W v z * W x z) :=
    integral_sub (hint _ _) (hint _ _)
  have hsplit3 : ∫ z, W u z * W y z - W u z * W x z
      = (∫ z, W u z * W y z) - (∫ z, W u z * W x z) :=
    integral_sub (hint _ _) (hint _ _)
  rw [hfun, hsplit1, hsplit2, hsplit3,
    hW.covariance v y, hW.covariance v x, hW.covariance u y, hW.covariance u x]
  ring

/-- Increments over disjoint intervals (second interval first) are
uncorrelated. -/
lemma integral_cov_incr_before (hW : IsWienerCov W) {u v x y : ℝ≥0}
    (hyu : y ≤ u) (huv : u ≤ v) (hxy : x ≤ y) :
    ∫ z, (W v z - W u z) * (W y z - W x z) = 0 := by
  have hyv : y ≤ v := hyu.trans huv
  have hxv : x ≤ v := hxy.trans hyv
  have hxu : x ≤ u := hxy.trans hyu
  rw [integral_cov_sub hW, min_eq_right hyv, min_eq_right hxv, min_eq_right hyu,
    min_eq_right hxu]
  ring

/-- Increments over disjoint intervals (first interval first) are
uncorrelated. -/
lemma integral_cov_incr_after (hW : IsWienerCov W) {u v x y : ℝ≥0}
    (huv : u ≤ v) (hvx : v ≤ x) (hxy : x ≤ y) :
    ∫ z, (W v z - W u z) * (W y z - W x z) = 0 := by
  have hyv : v ≤ y := hvx.trans hxy
  have huy : u ≤ y := huv.trans hyv
  have hux : u ≤ x := huv.trans hvx
  rw [integral_cov_sub hW, min_eq_left hyv, min_eq_left hvx, min_eq_left huy,
    min_eq_left hux]
  ring

/-- Itô isometry for a single increment: `E[(W v - W u)²] = v - u`. -/
lemma integral_cov_incr_self (hW : IsWienerCov W) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ z, (W v z - W u z) * (W v z - W u z) = (v : ℝ) - (u : ℝ) := by
  rw [integral_cov_sub hW]
  simp only [min_self, min_eq_left huv, min_eq_right huv]
  ring

omit [MeasureSpace Ω] in
lemma partition_succ_le_castSucc {n : ℕ} (P : Partition n) {i j : Fin n} (h : i < j) :
    P.t i.succ ≤ P.t j.castSucc := by
  have hval : ((i.succ : Fin (n + 1)) : ℕ) ≤ ((j.castSucc : Fin (n + 1)) : ℕ) :=
    Nat.succ_le_of_lt h
  exact P.mono.monotone (Fin.le_iff_val_le_val.mpr hval)

/-- Covariance of increments along a partition: the diagonal carries the
interval length, off-diagonal terms vanish. -/
lemma integral_cov_partition (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (i j : Fin n) :
    ∫ z, (W (P.t i.succ) z - W (P.t i.castSucc) z) *
          (W (P.t j.succ) z - W (P.t j.castSucc) z)
      = if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0 := by
  have hci : P.t i.castSucc ≤ P.t i.succ := P.mono.monotone (Fin.castSucc_le_succ i)
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact integral_cov_incr_self hW hci
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact integral_cov_incr_after hW hci (partition_succ_le_castSucc P hlt)
        (P.mono.monotone (Fin.castSucc_le_succ j))
    · exact integral_cov_incr_before hW (partition_succ_le_castSucc P hgt) hci
        (P.mono.monotone (Fin.castSucc_le_succ j))

omit [MeasureSpace Ω] in
@[simp] lemma stepIntegral_add {n : ℕ} (P : Partition n) (a b : Fin n → ℝ) :
    stepIntegral W P (a + b) = stepIntegral W P a + stepIntegral W P b := by
  funext x
  change ∑ i : Fin n, (a i + b i) * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        + ∑ i : Fin n, b i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
  have hterm : ∀ i : Fin n, (a i + b i) * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        + b i * (W (P.t i.succ) x - W (P.t i.castSucc) x) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]

omit [MeasureSpace Ω] in
@[simp] lemma stepIntegral_smul {n : ℕ} (P : Partition n) (c : ℝ) (a : Fin n → ℝ) :
    stepIntegral W P (c • a) = c • stepIntegral W P a := by
  funext x
  change ∑ i : Fin n, c * a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = c * ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
  calc ∑ i : Fin n, c * a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = ∑ i : Fin n, c * (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = c * ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
        (Finset.mul_sum _ _ _).symm

/-- Step integrals have zero expectation. -/
theorem integral_stepIntegral (hW : IsWienerCov W) {n : ℕ} (P : Partition n)
    (a : Fin n → ℝ) :
    ∫ x, stepIntegral W P a x = 0 := by
  have hint2 : ∀ i : Fin n,
      Integrable fun x => W (P.t i.succ) x - W (P.t i.castSucc) x :=
    fun i => (hW.integrable_W _).sub (hW.integrable_W _)
  have hsub : ∀ i : Fin n,
      ∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x = 0 := by
    intro i
    have hs : Integrable fun x => W (P.t i.succ) x := hW.integrable_W _
    have hc : Integrable fun x => W (P.t i.castSucc) x := hW.integrable_W _
    have key : ∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x
        = (∫ x, W (P.t i.succ) x) - (∫ x, W (P.t i.castSucc) x) :=
      integral_sub hs hc
    rw [key, hW.mean_zero, hW.mean_zero, sub_self]
  have hint : ∀ i : Fin n,
      Integrable fun x => a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
    fun i => (hint2 i).const_mul _
  have hf : (fun x => stepIntegral W P a x)
      = fun x => ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
    funext fun _ => rfl
  have hsplit : ∫ x, stepIntegral W P a x
      = ∑ i : Fin n, ∫ x, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) := by
    rw [hf]
    exact integral_finsetSum Finset.univ (fun i _ => hint i)
  rw [hsplit]
  exact Finset.sum_eq_zero fun i _ => by
    have hcm : ∫ x, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        = a i * (∫ x, W (P.t i.succ) x - W (P.t i.castSucc) x) :=
      integral_const_mul _ _
    rw [hcm, hsub i, mul_zero]

/-- **Itô isometry** for step integrals:
`E[I a * I b] = ∑ aᵢ bᵢ (t_{i+1} - t_i)`. -/
theorem ito_isometry (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (a b : Fin n → ℝ) :
    ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, a i * b i * ((P.t i.succ : ℝ) - (P.t i.castSucc : ℝ)) := by
  have hΔint : ∀ i j : Fin n,
      Integrable fun x : Ω => (W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x) := by
    intro i j
    have hfun : (fun x => (W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = fun x => (W (P.t i.succ) x * W (P.t j.succ) x
              - W (P.t i.succ) x * W (P.t j.castSucc) x)
            - (W (P.t i.castSucc) x * W (P.t j.succ) x
              - W (P.t i.castSucc) x * W (P.t j.castSucc) x) :=
      funext fun x => by ring
    rw [hfun]
    exact Integrable.sub ((hW.integrable_prod _ _).sub (hW.integrable_prod _ _))
      ((hW.integrable_prod _ _).sub (hW.integrable_prod _ _))
  have hint : ∀ i j : Fin n,
      Integrable fun x : Ω => (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
    fun i j => (hΔint i j).const_mul _
  have hdouble : ∀ f : Fin n → Fin n → Ω → ℝ, (∀ i j, Integrable (f i j)) →
      ∫ x, ∑ i, ∑ j, f i j x = ∑ i, ∑ j, ∫ x, f i j x := by
    intro f hf
    rw [integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hf i j))]
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum Finset.univ (fun j _ => hf i j)
  have hexpandf : (fun x => stepIntegral W P a x * stepIntegral W P b x)
      = fun x => ∑ i : Fin n, ∑ j : Fin n,
          (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := by
    funext x
    change (∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
         (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x))
       = ∑ i : Fin n, ∑ j : Fin n,
          (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x))
    calc (∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
         (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = ∑ i : Fin n, (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
            (∑ j : Fin n, b j * (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_mul _ _ _
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) *
            (b j * (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
              (W (P.t j.succ) x - W (P.t j.castSucc) x)) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := by
    rw [hexpandf]
    exact hdouble _ hint
  have hconst : ∀ i j : Fin n,
      ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = a i * b j *
            (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) := by
    intro i j
    have key : ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
        (W (P.t j.succ) x - W (P.t j.castSucc) x))
        = a i * b j * ∫ x, (W (P.t i.succ) x - W (P.t i.castSucc) x) *
          (W (P.t j.succ) x - W (P.t j.castSucc) x) :=
      integral_const_mul _ _
    rw [key, integral_cov_partition hW P]
  calc ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x, (a i * b j) * ((W (P.t i.succ) x - W (P.t i.castSucc) x) *
            (W (P.t j.succ) x - W (P.t j.castSucc) x)) := hsplit
    _ = ∑ i : Fin n, ∑ j : Fin n,
          a i * b j *
            (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hconst i j
    _ = ∑ i : Fin n, a i * b i * ((P.t i.succ : ℝ) - (P.t i.castSucc : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        have h0 : ∀ j : Fin n, j ≠ i →
            a i * b j *
              (if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0) = 0 := by
          intro j hj
          rw [if_neg (Ne.symm hj), mul_zero]
        have hsingle := Finset.sum_eq_single i (fun j _ hj => h0 j hj)
          (fun hni => absurd (Finset.mem_univ i) hni)
        rw [hsingle, if_pos rfl]

end Step

/-- Product of increments along a chain `u 0 ≤ v 0 ≤ u 1 ≤ v 1 ≤ …`: the intended
ordered-box value in a Brownian-linked iterated-integral family. -/
def chainIntegral {n : ℕ} (W : ℝ≥0 → Ω → ℝ) (u v : Fin n → ℝ≥0) : Ω → ℝ :=
  fun x => ∏ i, (W (v i) x - W (u i) x)

/-! ### The continuous iterated-integral tower

The preceding calculation motivates the laws in the interface below; it is not used here to prove
ordered-box compatibility for the selected continuous operators.  The time axis and
Brownian hypothesis are Mathlib's native ones.  Each `Jₙ` is defined on the full product
`L²((ℝ≥0)ⁿ)` and only sees its restriction to the ordered simplex.  This convention makes
the next rung's formula
`Iₙ(f) = n! • Jₙ(symmetrizeL f)` type-correct without introducing a bespoke subtype of kernels.
-/

section ContinuousTower

open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp

variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}

/-- The coercion from nonnegative reals to reals is a measurable embedding. -/
lemma measurableEmbedding_nnrealCoe_iterated :
    MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding

/-- Lebesgue measure on `ℝ≥0`, obtained by pulling real Lebesgue measure back along coercion. -/
noncomputable def nonnegativeLebesgueMeasure : Measure ℝ≥0 :=
  Measure.comap ((↑) : ℝ≥0 → ℝ) (volume : Measure ℝ)

/-- The nonnegative Lebesgue measure of `(a, b]` is its real length. -/
theorem nonnegativeLebesgueMeasure_Ioc (a b : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
  have himage : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc a b = Set.Ioc (a : ℝ) b := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨by exact_mod_cast hay, by exact_mod_cast hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx0 : 0 ≤ x := le_trans a.coe_nonneg hax.le
      exact ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hax, by exact_mod_cast hxb⟩, rfl⟩
  rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply,
    himage, Real.volume_Ioc]

instance nonnegativeLebesgueMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts nonnegativeLebesgueMeasure :=
  IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ) NNReal.continuous_coe
    measurableEmbedding_nnrealCoe_iterated

instance nonnegativeLebesgueMeasure_sigmaFinite :
    SigmaFinite nonnegativeLebesgueMeasure := inferInstance

instance nonnegativeLebesgueMeasure_nullSingletonClass :
    NullSingletonClass nonnegativeLebesgueMeasure where
  measure_singleton x := by
    rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply,
      Set.image_singleton, Real.volume_singleton]

/-- Lebesgue measure on the `n`-fold nonnegative time axis.  This is an abbreviation so that
downstream typeclass search sees the product measure's `SigmaFinite` instance. -/
noncomputable abbrev iteratedKernelMeasure (n : ℕ) : Measure (Fin n → ℝ≥0) :=
  Measure.pi fun _ : Fin n => nonnegativeLebesgueMeasure

/-- Deterministic square-integrable kernels of order `n`. -/
noncomputable abbrev IteratedKernel (n : ℕ) := Lp ℝ 2 (iteratedKernelMeasure n)

/-- Square-integrable real random variables under `P`. -/
abbrev RandomL2 (P : Measure Ω') := Lp ℝ 2 P

/-- The measurable space generated by all coordinates of a process. -/
abbrev processMeasurableSpace (B : ℝ≥0 → Ω' → ℝ) : MeasurableSpace Ω' :=
  ⨆ t : ℝ≥0, MeasurableSpace.comap (B t) (borel ℝ)

/-- Exact sigma-algebra generation by a process.  This is the no-extra-randomness formulation
used by downstream ambient-`L²` results; equality modulo null sets would be a weaker
alternative. -/
def IsWienerGenerated (B : ℝ≥0 → Ω' → ℝ) : Prop :=
  processMeasurableSpace B = ‹MeasurableSpace Ω'›

/-- Every coordinate is measurable when the process generates the ambient sigma-algebra. -/
theorem IsWienerGenerated.measurable (hgen : IsWienerGenerated B) (t : ℝ≥0) :
    Measurable (B t) := by
  apply Measurable.of_comap_le
  rw [← hgen]
  exact le_iSup (fun s : ℝ≥0 ↦ MeasurableSpace.comap (B s) (borel ℝ)) t

/-- A coordinatewise measurable process generates a sub-sigma-algebra of the ambient one. -/
theorem processMeasurableSpace_le_of_measurable
    (hmeas : ∀ t, Measurable (B t)) :
    processMeasurableSpace B ≤ mΩ' :=
  iSup_le fun t ↦ (hmeas t).comap_le

/-- The ambient measure restricted to the sigma-algebra generated by a measurable process. -/
noncomputable abbrev processTrimMeasure
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t)) :
    @Measure Ω' (processMeasurableSpace B) :=
  P.trim (processMeasurableSpace_le_of_measurable hmeas)

private theorem measurePreserving_id_processTrim
    (hmeas : ∀ t, Measurable (B t)) :
    @MeasurePreserving Ω' Ω' mΩ' (processMeasurableSpace B) id P
      (processTrimMeasure P B hmeas) := by
  let hm : processMeasurableSpace B ≤ mΩ' :=
    processMeasurableSpace_le_of_measurable hmeas
  have hid : @Measurable Ω' Ω' mΩ' (processMeasurableSpace B) id :=
    @measurable_id'' Ω' (processMeasurableSpace B) mΩ' hm
  exact @MeasurePreserving.mk Ω' Ω' mΩ' (processMeasurableSpace B)
    id P (processTrimMeasure P B hmeas) hid (trim_eq_map hm).symm

private theorem measurePreserving_id_processTrim_symm
    (hmeas : ∀ t, Measurable (B t))
    (hgen : processMeasurableSpace B = mΩ') :
    @MeasurePreserving Ω' Ω' (processMeasurableSpace B) mΩ' id
      (processTrimMeasure P B hmeas) P := by
  let hm : processMeasurableSpace B ≤ mΩ' :=
    processMeasurableSpace_le_of_measurable hmeas
  have hm' : mΩ' ≤ processMeasurableSpace B := by rw [hgen]
  have hid : @Measurable Ω' Ω' (processMeasurableSpace B) mΩ' id :=
    @measurable_id'' Ω' mΩ' (processMeasurableSpace B) hm'
  apply @MeasurePreserving.mk Ω' Ω' (processMeasurableSpace B) mΩ' id
    (processTrimMeasure P B hmeas) P hid
  ext s hs
  have hsB : @MeasurableSet Ω' (processMeasurableSpace B) s := hm' s hs
  rw [Measure.map_apply hid hs, Set.preimage_id]
  exact trim_measurableSet_eq hm hsB

/-- Pull process-measurable `L²` representatives into ambient `L²` along the identity. -/
noncomputable def processLpEmbedding
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t)) :
    (@Lp Ω' ℝ (processMeasurableSpace B) inferInstance 2
      (processTrimMeasure P B hmeas)) →ₗᵢ[ℝ] RandomL2 P := by
  exact @Lp.compMeasurePreservingₗᵢ Ω' ℝ mΩ' 2 P _ Ω'
    (processMeasurableSpace B) (processTrimMeasure P B hmeas) ℝ _ _ _ _ id
    (measurePreserving_id_processTrim hmeas)

/-- If the process sigma-algebra is ambient, its `L²` embedding is onto. -/
theorem processLpEmbedding_surjective
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t))
    (hgen : processMeasurableSpace B = mΩ') :
    Function.Surjective (processLpEmbedding P B hmeas) := by
  let hforward := measurePreserving_id_processTrim (P := P) hmeas
  let hreverse := measurePreserving_id_processTrim_symm (P := P) hmeas hgen
  let reverse : RandomL2 P →ₗᵢ[ℝ]
      (@Lp Ω' ℝ (processMeasurableSpace B) inferInstance 2
        (processTrimMeasure P B hmeas)) :=
    @Lp.compMeasurePreservingₗᵢ Ω' ℝ (processMeasurableSpace B) 2
      (processTrimMeasure P B hmeas) _ Ω' mΩ' P ℝ _ _ _ _ id hreverse
  intro f
  refine ⟨reverse f, ?_⟩
  change
    (@Lp.compMeasurePreserving Ω' ℝ mΩ' 2 P _ Ω'
      (processMeasurableSpace B) (processTrimMeasure P B hmeas) id hforward)
        ((@Lp.compMeasurePreserving Ω' ℝ (processMeasurableSpace B) 2
          (processTrimMeasure P B hmeas) _ Ω' mΩ' P id hreverse) f) = f
  have hcomp := @Lp.compMeasurePreserving_comp_apply Ω' ℝ mΩ' 2 P _ Ω'
    (processMeasurableSpace B) (processTrimMeasure P B hmeas) Ω'
    mΩ' P f id hreverse id hforward
  simpa only [Function.id_comp, Lp.compMeasurePreserving_id_apply] using hcomp.symm

/-- An all-orders family of operators satisfying the iterated-integral Hilbert-space laws.

`sameOrder` is the simplex isometry, `differentOrder` records cross-order orthogonality, and
`centered` is stated separately because it is needed before the chaos decomposition.  This
structure intentionally does not assert the Brownian ordered-box link. -/
structure IteratedIntegralFamily (P : Measure Ω') where
  /-- The order-`n` operator `Jₙ`. -/
  integral : (n : ℕ) → IteratedKernel n →L[ℝ] RandomL2 P
  /-- Polarized simplex isometry. -/
  sameOrder : ∀ (n : ℕ) (f g : IteratedKernel n),
    inner ℝ (integral n f) (integral n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n
  /-- Positive-order operators have centered output. -/
  centered : ∀ (n : ℕ), 0 < n → ∀ f : IteratedKernel n,
    ∫ ω, integral n f ω ∂P = 0
  /-- The zeroth-order integral is the constant represented by its kernel. -/
  zeroOrder : ∀ f : IteratedKernel 0,
    (fun ω => integral 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0
  /-- Outputs of different orders are orthogonal. -/
  differentOrder : ∀ {m n : ℕ}, m ≠ n → ∀ (f : IteratedKernel m) (g : IteratedKernel n),
    inner ℝ (integral m f) (integral n g) = 0
  /-- Restriction to the simplex is contractive, hence so is `Jₙ`. -/
  norm_integral_le : ∀ (n : ℕ) (f : IteratedKernel n), ‖integral n f‖ ≤ ‖f‖

namespace IteratedIntegralConstruction

/-! The construction below uses only the Hilbert-space laws exposed by the public interface.
Positive-order simplex spaces are assembled into a single external Hilbert sum and embedded in
the centered subspace.  Unit Brownian increments provide an explicit fallback embedding, while
separability together with exhaustion by process-measurable classes permits an onto choice. -/

section HilbertBasisCountability

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

omit [CompleteSpace E] in
private lemma countable_hilbertBasis_index {ι : Type*} (b : HilbertBasis ι ℝ E) :
    Countable ι := by
  let s : Set E := Set.range b
  have hs_orth : Orthonormal ℝ ((↑) : s → E) := b.orthonormal.toSubtypeRange
  have hs_discrete : DiscreteTopology s := by
    apply DiscreteTopology.of_forall_le_dist (r := 1) zero_lt_one
    intro x y hxy
    have hinner : inner ℝ (x : E) (y : E) = 0 := hs_orth.inner_eq_zero hxy
    have hsq : ‖(x : E) - (y : E)‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℝ)]
      norm_num [hs_orth.norm_eq_one, hinner]
    have hnorm : 1 ≤ ‖(x : E) - (y : E)‖ := by
      nlinarith [norm_nonneg ((x : E) - (y : E))]
    simpa only [Subtype.dist_eq, dist_eq_norm] using hnorm
  let _ : DiscreteTopology s := hs_discrete
  let _ : Countable s := countable_of_Lindelof_of_discrete
  exact (Equiv.ofInjective b b.orthonormal.linearIndependent.injective).injective.countable


end HilbertBasisCountability

end IteratedIntegralConstruction

namespace IteratedIntegralConstruction

/-- Square-integrable kernels on the strict ordered simplex of order `n`. -/
noncomputable abbrev SimplexKernel (n : ℕ) :=
  Lp ℝ 2 ((iteratedKernelMeasure n).restrict (simplex ℝ≥0 n))

private lemma restrictedSimplexMeasure_le (n : ℕ) :
    (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤
      (1 : ℝ≥0∞) • iteratedKernelMeasure n := by
  simpa only [one_smul] using
    (Measure.restrict_le_self :
      (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤ iteratedKernelMeasure n)

private noncomputable def restrictToSimplex (n : ℕ) :
    IteratedKernel n →L[ℝ] SimplexKernel n := by
  exact Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n)

private lemma restrictToSimplex_ae (n : ℕ) (f : IteratedKernel n) :
    restrictToSimplex n f =ᵐ[(iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)] f := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n) f

private lemma inner_restrictToSimplex (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (restrictToSimplex n f) (restrictToSimplex n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictToSimplex_ae n f, restrictToSimplex_ae n g] with t hft hgt
  rw [hft, hgt]

private lemma norm_restrictToSimplex_le (n : ℕ) (f : IteratedKernel n) :
    ‖restrictToSimplex n f‖ ≤ ‖f‖ := by
  have hop : ‖restrictToSimplex n‖ ≤ 1 := by
    simpa only [restrictToSimplex, ENNReal.toReal_one, Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le
        (E := ℝ) (p := (2 : ℝ≥0∞)) (c := 1)
        (by norm_num) (restrictedSimplexMeasure_le n))
  calc
    ‖restrictToSimplex n f‖ ≤ ‖restrictToSimplex n‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm (restrictToSimplex n) f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-! Symmetric product kernels realize every simplex kernel.  This is the deterministic bridge
needed to identify the range of each selected multiple operator with its simplex-order summand. -/

private lemma symmetrize_factorial_indicator_on_simplex
    (n : ℕ) (g : (Fin n → ℝ≥0) → ℝ) {t : Fin n → ℝ≥0}
    (ht : t ∈ simplex ℝ≥0 n) :
    symmetrize n ((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g) t = g t := by
  classical
  rw [symmetrize_apply]
  have hsum :
      ∑ σ : Equiv.Perm (Fin n),
          (((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g) (t ∘ σ)) =
        (n.factorial : ℝ) • g t := by
    calc
      _ = (((n.factorial : ℝ) • (simplex ℝ≥0 n).indicator g)
          (t ∘ (1 : Equiv.Perm (Fin n)))) := by
        apply Finset.sum_eq_single 1
        · intro σ _ hσ
          have hnot : t ∘ σ ∉ simplex ℝ≥0 n := by
            intro hσ_mem
            have hEq : σ = 1 :=
              perm_eq_of_strictMono_comp (mem_simplex.mp ht).injective
                (mem_simplex.mp hσ_mem) (by
                  have ht_one : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
                    funext i
                    rfl
                  rw [ht_one]
                  exact mem_simplex.mp ht)
            exact hσ hEq
          simp only [Pi.smul_apply, Set.indicator_of_notMem hnot, smul_zero]
        · intro h
          exact (h (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).elim
      _ = (n.factorial : ℝ) • g t := by
        have hone : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
          funext i
          rfl
        rw [hone]
        simp only [Pi.smul_apply, Set.indicator_of_mem ht]
  rw [hsum, smul_smul, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]

private lemma memLp_zeroExtension (n : ℕ) (g : SimplexKernel n) :
    MemLp ((simplex ℝ≥0 n).indicator (fun t ↦ g t)) (2 : ℝ≥0∞)
      (iteratedKernelMeasure n) := by
  rw [memLp_indicator_iff_restrict (measurableSet_simplex n)]
  exact Lp.memLp g

private noncomputable def zeroExtendSimplex (n : ℕ) (g : SimplexKernel n) :
    IteratedKernel n :=
  (memLp_zeroExtension n g).toLp ((simplex ℝ≥0 n).indicator (fun t ↦ g t))

private lemma coeFn_zeroExtendSimplex (n : ℕ) (g : SimplexKernel n) :
    ⇑(zeroExtendSimplex n g) =ᵐ[iteratedKernelMeasure n]
      (simplex ℝ≥0 n).indicator (fun t ↦ g t) :=
  MemLp.coeFn_toLp (memLp_zeroExtension n g)

/-- Symmetrize a product kernel and then restrict it to the strict simplex. -/
noncomputable def symmetrizeRestrict (n : ℕ) :
    IteratedKernel n →L[ℝ] SimplexKernel n := by
  exact (restrictToSimplex n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)

private lemma restrict_symmetrize_factorial_zeroExtend (n : ℕ) (g : SimplexKernel n) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          ((n.factorial : ℝ) • zeroExtendSimplex n g)) = g := by
  apply Lp.ext
  have hinput :
      ⇑((n.factorial : ℝ) • zeroExtendSimplex n g) =ᵐ[iteratedKernelMeasure n]
        (n.factorial : ℝ) • (simplex ℝ≥0 n).indicator (fun t ↦ g t) := by
    filter_upwards [Lp.coeFn_smul (n.factorial : ℝ) (zeroExtendSimplex n g),
      coeFn_zeroExtendSimplex n g] with t ht₁ ht₂
    simp only [Pi.smul_apply] at ht₁ ⊢
    exact ht₁.trans (congrArg ((n.factorial : ℝ) • ·) ht₂)
  have hsymm :
      ⇑(symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          ((n.factorial : ℝ) • zeroExtendSimplex n g)) =ᵐ[iteratedKernelMeasure n]
        symmetrize n ((n.factorial : ℝ) •
          (simplex ℝ≥0 n).indicator (fun t ↦ g t)) :=
    (coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2
      ((n.factorial : ℝ) • zeroExtendSimplex n g)).trans
      (symmetrize_congr_ae (μ := nonnegativeLebesgueMeasure) hinput)
  have hpoint :
      symmetrize n ((n.factorial : ℝ) •
          (simplex ℝ≥0 n).indicator (fun t ↦ g t)) =ᵐ[
            (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)] ⇑g := by
    filter_upwards [ae_restrict_mem (measurableSet_simplex n)] with t ht
    exact symmetrize_factorial_indicator_on_simplex n (fun t ↦ g t) ht
  filter_upwards [restrictToSimplex_ae n _, ae_restrict_of_ae hsymm, hpoint]
    with t ht₁ ht₂ ht₃
  exact ht₁.trans (ht₂.trans ht₃)

private noncomputable def symmetrizedRightInverse (n : ℕ) :
    SimplexKernel n → IteratedKernel n := by
  exact fun g ↦ (n.factorial : ℝ) •
    symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (zeroExtendSimplex n g)

private lemma symmetrizeRestrict_rightInverse (n : ℕ) (g : SimplexKernel n) :
    symmetrizeRestrict n (symmetrizedRightInverse n g) = g := by
  change restrictToSimplex n
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
      ((n.factorial : ℝ) •
        symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (zeroExtendSimplex n g))) = g
  simpa only [map_smul, symmetrizeL_symmetrizeL] using
    restrict_symmetrize_factorial_zeroExtend n g

/-- Every square-integrable simplex kernel is the simplex restriction of a symmetric product
kernel. -/
theorem symmetrizeRestrict_surjective (n : ℕ) :
    Function.Surjective (symmetrizeRestrict n) :=
  fun g ↦ ⟨symmetrizedRightInverse n g, symmetrizeRestrict_rightInverse n g⟩

private lemma iteratedKernelMeasure_zero :
    iteratedKernelMeasure 0 = Measure.dirac (0 : Fin 0 → ℝ≥0) := by
  simpa only [iteratedKernelMeasure] using
    (Measure.pi_of_empty (fun _ : Fin 0 ↦ nonnegativeLebesgueMeasure)
      (0 : Fin 0 → ℝ≥0))

private lemma simplex_zero : simplex ℝ≥0 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  change StrictMono t
  intro i
  exact Fin.elim0 i

private instance iteratedKernelMeasure_zero_isProbability :
    IsProbabilityMeasure (iteratedKernelMeasure 0) := by
  rw [iteratedKernelMeasure_zero]
  infer_instance

private theorem integral_iteratedKernelMeasure_zero (φ : (Fin 0 → ℝ≥0) → ℝ) :
    ∫ t, φ t ∂iteratedKernelMeasure 0 = φ 0 := by
  rw [iteratedKernelMeasure_zero]
  exact integral_dirac _ _

private theorem setIntegral_simplex_zero (φ : (Fin 0 → ℝ≥0) → ℝ) :
    ∫ t in simplex ℝ≥0 0, φ t ∂iteratedKernelMeasure 0 = φ 0 := by
  rw [simplex_zero, Measure.restrict_univ]
  exact integral_iteratedKernelMeasure_zero φ

private noncomputable def zeroKernelOne : IteratedKernel 0 :=
  Lp.const 2 (iteratedKernelMeasure 0) (1 : ℝ)

private noncomputable def zeroKernelIntegral : IteratedKernel 0 →L[ℝ] ℝ :=
  innerSL ℝ zeroKernelOne

private theorem zeroKernelIntegral_apply (f : IteratedKernel 0) :
    zeroKernelIntegral f = ∫ t, f t ∂iteratedKernelMeasure 0 := by
  rw [zeroKernelIntegral, innerSL_apply_apply, zeroKernelOne, ← indicatorConstLp_univ,
    L2.inner_indicatorConstLp_one MeasurableSet.univ
      (measure_ne_top (iteratedKernelMeasure 0) Set.univ), Measure.restrict_univ]

private noncomputable def probabilityConstL (hB : IsPreBrownianReal B P) :
    ℝ →L[ℝ] RandomL2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact Lp.constL 2 P ℝ

private theorem probabilityConstL_coe (hB : IsPreBrownianReal B P) (c : ℝ) :
    (fun ω ↦ probabilityConstL hB c ω) =ᵐ[P] fun _ ↦ c := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := P) c
  filter_upwards [h] with ω hω
  exact hω

private noncomputable def zeroIntegralCLM (hB : IsPreBrownianReal B P) :
    IteratedKernel 0 →L[ℝ] RandomL2 P :=
  (probabilityConstL hB).comp zeroKernelIntegral

private theorem zeroIntegralCLM_coe (hB : IsPreBrownianReal B P) (f : IteratedKernel 0) :
    (fun ω ↦ zeroIntegralCLM hB f ω) =ᵐ[P]
      fun _ ↦ ∫ t, f t ∂iteratedKernelMeasure 0 := by
  simpa only [zeroIntegralCLM, ContinuousLinearMap.comp_apply, zeroKernelIntegral_apply] using
    probabilityConstL_coe hB (zeroKernelIntegral f)

private theorem zeroIntegralCLM_sameOrder (hB : IsPreBrownianReal B P)
    (f g : IteratedKernel 0) :
    inner ℝ (zeroIntegralCLM hB f) (zeroIntegralCLM hB g) =
      ∫ t in simplex ℝ≥0 0, inner ℝ (f t) (g t) ∂iteratedKernelMeasure 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [zeroIntegralCLM_coe hB f, zeroIntegralCLM_coe hB g]
      with ω hf hg
    rw [hf, hg])]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_iteratedKernelMeasure_zero (fun t ↦ f t),
    integral_iteratedKernelMeasure_zero (fun t ↦ g t),
    setIntegral_simplex_zero (fun t ↦ inner ℝ (f t) (g t))]

private theorem zeroIntegralCLM_inner_centered (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) (X : RandomL2 P) (hX : ∫ ω, X ω ∂P = 0) :
    inner ℝ (zeroIntegralCLM hB f) X = 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [L2.inner_def]
  calc
    ∫ ω, inner ℝ (zeroIntegralCLM hB f ω) (X ω) ∂P =
        ∫ ω, (∫ t, f t ∂iteratedKernelMeasure 0) * X ω ∂P := by
          apply integral_congr_ae
          filter_upwards [zeroIntegralCLM_coe hB f] with ω hω
          rw [hω]
          exact Real.inner_apply _ _
    _ = (∫ t, f t ∂iteratedKernelMeasure 0) * ∫ ω, X ω ∂P :=
      integral_const_mul _ _
    _ = 0 := by rw [hX, mul_zero]

private theorem zeroIntegralCLM_norm_le (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) : ‖zeroIntegralCLM hB f‖ ≤ ‖f‖ := by
  have hsq : ‖zeroIntegralCLM hB f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← @real_inner_self_eq_norm_sq _ _ _ (zeroIntegralCLM hB f),
      ← @real_inner_self_eq_norm_sq _ _ _ f,
      zeroIntegralCLM_sameOrder hB f f, L2.inner_def, simplex_zero,
      Measure.restrict_univ]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).le

end IteratedIntegralConstruction

namespace IteratedIntegralConstruction

private def unitIncrement (B : ℝ≥0 → Ω' → ℝ) (k : ℕ) : Ω' → ℝ :=
  fun ω => B (k + 1) ω - B k ω

private theorem unitIncrement_memLp (hB : IsPreBrownianReal B P) (k : ℕ) :
    MemLp (unitIncrement B k) 2 P :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

private theorem integral_unitIncrement (hB : IsPreBrownianReal B P) (k : ℕ) :
    ∫ ω, unitIncrement B k ω ∂P = 0 := by
  change ∫ ω, B (k + 1) ω - B k ω ∂P = 0
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_zero]

private theorem integral_unitIncrement_sq (hB : IsPreBrownianReal B P) (k : ℕ) :
    ∫ ω, unitIncrement B k ω * unitIncrement B k ω ∂P = 1 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm := unitIncrement_memLp hB k
  have hc := covariance_eq_sub hm hm
  rw [integral_unitIncrement hB, mul_zero, sub_zero] at hc
  calc
    ∫ ω, unitIncrement B k ω * unitIncrement B k ω ∂P =
        ∫ ω, (unitIncrement B k * unitIncrement B k) ω ∂P := rfl
    _ = cov[unitIncrement B k, unitIncrement B k; P] := hc.symm
    _ = Var[unitIncrement B k; P] := covariance_self hm.aemeasurable
    _ = Var[id; gaussianReal 0 (nndist ((k + 1 : ℝ≥0) : ℝ) ((k : ℝ≥0) : ℝ))] :=
      (hB.hasLaw_sub (k + 1) k).variance_eq
    _ = 1 := by
      rw [variance_id_gaussianReal]
      norm_num [nndist]
      rfl

private theorem iIndepFun_unitIncrement (hB : IsPreBrownianReal B P) :
    iIndepFun (unitIncrement B) P := by
  unfold unitIncrement
  have h := hB.hasIndepIncrements.nat
    (t := fun k : ℕ => (k : ℝ≥0)) (fun _ _ hab => Nat.cast_le.mpr hab)
  simpa only [Nat.cast_add, Nat.cast_one] using h

private theorem integral_unitIncrement_mul_of_ne (hB : IsPreBrownianReal B P)
    {k l : ℕ} (hkl : k ≠ l) :
    ∫ ω, unitIncrement B k ω * unitIncrement B l ω ∂P = 0 := by
  have hi := (iIndepFun_unitIncrement hB).indepFun hkl
  rw [hi.integral_fun_mul_eq_mul_integral
    (unitIncrement_memLp hB k).aestronglyMeasurable
    (unitIncrement_memLp hB l).aestronglyMeasurable,
    integral_unitIncrement hB, zero_mul]

private noncomputable def unitIncrementL2 (hB : IsPreBrownianReal B P) (k : ℕ) :
    RandomL2 P :=
  (unitIncrement_memLp hB k).toLp (unitIncrement B k)

private theorem unitIncrementL2_orthonormal (hB : IsPreBrownianReal B P) :
    Orthonormal ℝ (unitIncrementL2 hB) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  change ∫ a, unitIncrementL2 hB k a * unitIncrementL2 hB l a ∂P = _
  have hk := MemLp.coeFn_toLp (unitIncrement_memLp hB k)
  have hl := MemLp.coeFn_toLp (unitIncrement_memLp hB l)
  have hcoe : (fun a => unitIncrementL2 hB k a * unitIncrementL2 hB l a) =ᵐ[P]
      fun a => unitIncrement B k a * unitIncrement B l a := by
    filter_upwards [hk, hl] with a hka hla
    exact congrArg₂ (· * ·) hka hla
  rw [integral_congr_ae hcoe]
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    exact integral_unitIncrement_sq hB k
  · rw [if_neg hkl]
    exact integral_unitIncrement_mul_of_ne hB hkl


local instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-! The positive orders are assembled into one external Hilbert sum.  A single isometry out of
this sum permits an onto branch; the selector uses it only when ambient `L²` is second-countable
and process-generated `L²` exhausts it. -/

/-- The external Hilbert sum of all positive-order simplex kernel spaces. -/
noncomputable abbrev PositiveKernelSum :=
  lp (fun n : ℕ ↦ SimplexKernel (n + 1)) 2

private def orderedBoxLeft {n : ℕ} (i : Fin (n + 1)) : ℝ≥0 :=
  2 * (i.1 : ℝ≥0)

private def orderedUnitBox (n : ℕ) : Set (Fin (n + 1) → ℝ≥0) :=
  Set.univ.pi fun i ↦ Set.Ioc (orderedBoxLeft i) (orderedBoxLeft i + 1)

private theorem measurableSet_orderedUnitBox (n : ℕ) :
    MeasurableSet (orderedUnitBox n) :=
  MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ioc

private theorem orderedUnitBox_subset_simplex (n : ℕ) :
    orderedUnitBox n ⊆ simplex ℝ≥0 (n + 1) := by
  intro t ht
  rw [mem_simplex]
  intro i j hij
  have hit := (Set.mem_pi.mp ht) i (Set.mem_univ i)
  have hjt := (Set.mem_pi.mp ht) j (Set.mem_univ j)
  have hij' : i.1 + 1 ≤ j.1 := by omega
  have hij'' : (i.1 : ℝ≥0) + 1 ≤ (j.1 : ℝ≥0) := by exact_mod_cast hij'
  have hsep : orderedBoxLeft i + 1 < orderedBoxLeft j := by
    dsimp only [orderedBoxLeft]
    calc
      2 * (i.1 : ℝ≥0) + 1 < 2 * (i.1 : ℝ≥0) + 2 := by norm_num
      _ = 2 * ((i.1 : ℝ≥0) + 1) := by ring
      _ ≤ 2 * (j.1 : ℝ≥0) := by gcongr
  exact lt_of_le_of_lt hit.2 (hsep.trans hjt.1)

private theorem measure_orderedUnitBox (n : ℕ) :
    iteratedKernelMeasure (n + 1) (orderedUnitBox n) = 1 := by
  change (Measure.pi fun _ : Fin (n + 1) ↦ nonnegativeLebesgueMeasure)
      (Set.univ.pi fun i ↦ Set.Ioc (orderedBoxLeft i) (orderedBoxLeft i + 1)) = 1
  rw [Measure.pi_pi]
  simp only [orderedBoxLeft, nonnegativeLebesgueMeasure_Ioc, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_one, add_sub_cancel_left, ENNReal.ofReal_one,
    Finset.prod_const_one]

private theorem restrict_measure_orderedUnitBox (n : ℕ) :
    ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
        (orderedUnitBox n) = 1 := by
  rw [Measure.restrict_apply (measurableSet_orderedUnitBox n),
    Set.inter_eq_left.mpr (orderedUnitBox_subset_simplex n)]
  exact measure_orderedUnitBox n

private noncomputable def simplexUnitBoxIndicator (n : ℕ) : SimplexKernel (n + 1) :=
  indicatorConstLp 2 (measurableSet_orderedUnitBox n)
    (by rw [restrict_measure_orderedUnitBox n]; norm_num) (1 : ℝ)

private theorem norm_simplexUnitBoxIndicator (n : ℕ) : ‖simplexUnitBoxIndicator n‖ = 1 := by
  rw [simplexUnitBoxIndicator, norm_indicatorConstLp (by norm_num) (by norm_num),
    measureReal_def, restrict_measure_orderedUnitBox]
  norm_num

private noncomputable def simplexBasisSet (n : ℕ) : Set (SimplexKernel (n + 1)) :=
  Classical.choose (exists_hilbertBasis ℝ (SimplexKernel (n + 1)))

private noncomputable abbrev simplexBasisIndex (n : ℕ) : Type :=
  simplexBasisSet n

private noncomputable def simplexBasis (n : ℕ) :
    HilbertBasis (simplexBasisIndex n) ℝ (SimplexKernel (n + 1)) :=
  Classical.choose (show ∃ b : HilbertBasis (simplexBasisIndex n) ℝ
      (SimplexKernel (n + 1)), ⇑b = Subtype.val from
    Classical.choose_spec (exists_hilbertBasis ℝ (SimplexKernel (n + 1))))

private noncomputable local instance simplexBasisIndex_countable (n : ℕ) :
    Countable (simplexBasisIndex n) := by
  exact countable_hilbertBasis_index (simplexBasis n)

private theorem simplexBasisIndex_nonempty (n : ℕ) : Nonempty (simplexBasisIndex n) := by
  by_contra h
  have hz : (simplexBasis n).repr (simplexUnitBoxIndicator n) = 0 := by
    ext i
    exact (h ⟨i⟩).elim
  have hu : simplexUnitBoxIndicator n = 0 :=
    (simplexBasis n).repr.injective (by simpa only [map_zero] using hz)
  have hnorm := norm_simplexUnitBoxIndicator n
  rw [hu, norm_zero] at hnorm
  norm_num at hnorm

private noncomputable def globalBasisIndexPoint (n : ℕ) :
    Σ k : ℕ, simplexBasisIndex k :=
  ⟨n, Classical.choice (simplexBasisIndex_nonempty n)⟩

private theorem globalBasisIndexPoint_injective :
    Function.Injective globalBasisIndexPoint := by
  intro i j hij
  exact congrArg Sigma.fst hij

private noncomputable local instance globalBasisIndex_infinite :
    Infinite (Σ n : ℕ, simplexBasisIndex n) :=
  Infinite.of_injective globalBasisIndexPoint globalBasisIndexPoint_injective

private noncomputable def globalBasisVector
    (a : Σ n : ℕ, simplexBasisIndex n) : PositiveKernelSum :=
  lp.single 2 a.1 (simplexBasis a.1 a.2)

private theorem globalBasisVector_orthonormal : Orthonormal ℝ globalBasisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, i⟩ ⟨m, j⟩
  change inner ℝ
      (lp.single 2 n (simplexBasis n i) : PositiveKernelSum)
      (lp.single 2 m (simplexBasis m j) : PositiveKernelSum) = _
  rw [lp.inner_single_left]
  by_cases hnm : n = m
  · subst m
    rw [lp.single_apply_self (E := fun k : ℕ ↦ SimplexKernel (k + 1))]
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using
      (orthonormal_iff_ite.mp (simplexBasis n).orthonormal i j)
  · rw [lp.single_apply_ne (E := fun k : ℕ ↦ SimplexKernel (k + 1)) 2 m
      (simplexBasis m j) hnm]
    simp only [inner_zero_right, Sigma.mk.injEq, hnm, false_and, ↓reduceIte]

private theorem globalBasisVector_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range globalBasisVector))ᗮ = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [lp.eq_zero_iff_coeFn_eq_zero]
  funext n
  apply (simplexBasis n).repr.injective
  ext i
  rw [(simplexBasis n).repr_apply_apply]
  have hinner := (Submodule.mem_orthogonal' _ _).mp hx
    (globalBasisVector ⟨n, i⟩)
    (Submodule.subset_span ⟨⟨n, i⟩, rfl⟩)
  change inner ℝ x (lp.single 2 n (simplexBasis n i)) = 0 at hinner
  rw [lp.inner_single_right] at hinner
  simpa only [real_inner_comm, Pi.zero_apply, map_zero, ZeroMemClass.coe_zero,
    PreLp.zero_apply] using hinner

private noncomputable def positiveKernelHilbertBasis :
    HilbertBasis (Σ n : ℕ, simplexBasisIndex n) ℝ PositiveKernelSum :=
  HilbertBasis.mkOfOrthogonalEqBot globalBasisVector_orthonormal
    globalBasisVector_orthogonal_eq_bot

private noncomputable def l2CongrLeft {ι κ : Type*} (e : ι ≃ κ) :
    ℓ²(ι, ℝ) ≃ₗᵢ[ℝ] ℓ²(κ, ℝ) where
  toFun f := ⟨fun j ↦ f (e.symm j), by
    change Memℓp (fun j : κ ↦ f (e.symm j)) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
    exact e.symm.summable_iff.mpr
      ((memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp f))⟩
  invFun g := ⟨fun i ↦ g (e i), by
    change Memℓp (fun i : ι ↦ g (e i)) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
    exact e.summable_iff.mpr
      ((memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp g))⟩
  left_inv f := by ext i; simp only [Equiv.symm_apply_apply]
  right_inv g := by ext j; simp only [Equiv.apply_symm_apply]
  map_add' f g := by ext j; rfl
  map_smul' c f := by ext j; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num),
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)]
    congr 1
    simpa only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs,
      ENNReal.toReal_ofNat, Real.rpow_ofNat, sq_abs] using
      (e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal))

/-- The constant-one vector in `L²(P)` for the probability measure supplied by `hB`. -/
noncomputable def probabilityOne (hB : IsPreBrownianReal B P) : RandomL2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ)

@[simp] theorem norm_probabilityOne (hB : IsPreBrownianReal B P) :
    ‖probabilityOne hB‖ = 1 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [probabilityOne, norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def]
  rw [measure_univ]
  norm_num

/-- The centered subspace of `L²(P)`, realized as the orthogonal complement of constants. -/
noncomputable abbrev CenteredRandomL2 (hB : IsPreBrownianReal B P) :=
  (ℝ ∙ probabilityOne hB)ᗮ

private noncomputable def centeredUnitIncrement (hB : IsPreBrownianReal B P) (k : ℕ) :
    CenteredRandomL2 hB := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨unitIncrementL2 hB k, ?_⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change inner ℝ
    (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ))
    (unitIncrementL2 hB k) = 0
  rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
  unfold unitIncrementL2
  rw [integral_congr_ae (MemLp.coeFn_toLp (unitIncrement_memLp hB k))]
  exact integral_unitIncrement hB k

private theorem centeredUnitIncrement_orthonormal (hB : IsPreBrownianReal B P) :
    Orthonormal ℝ (centeredUnitIncrement hB) := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (unitIncrementL2 hB i) (unitIncrementL2 hB j) = _
  exact orthonormal_iff_ite.mp (unitIncrementL2_orthonormal hB) i j

private theorem nonempty_positiveKernelSum_equiv_centered
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (CenteredRandomL2 hB)] :
    Nonempty (PositiveKernelSum ≃ₗᵢ[ℝ] CenteredRandomL2 hB) := by
  have hw := centeredUnitIncrement_orthonormal hB
  have hw_range : Orthonormal ℝ ((↑) : Set.range (centeredUnitIncrement hB) →
      CenteredRandomL2 hB) := hw.toSubtypeRange
  obtain ⟨sF, bF, hw_sub, _hbF⟩ := hw_range.exists_hilbertBasis_extension
  let _ : Countable sF := countable_hilbertBasis_index bF
  have hsF_inf : sF.Infinite :=
    (Set.infinite_range_of_injective hw.linearIndependent.injective).mono hw_sub
  let _ : Infinite sF := Set.infinite_coe_iff.mpr hsF_inf
  let e : (Σ n : ℕ, simplexBasisIndex n) ≃ sF := nonempty_equiv_of_countable.some
  exact ⟨positiveKernelHilbertBasis.repr.trans ((l2CongrLeft e).trans bF.repr.symm)⟩

private noncomputable def positiveKernelEmbeddingCentered
    (hB : IsPreBrownianReal B P) : PositiveKernelSum →ₗᵢ[ℝ] CenteredRandomL2 hB := by
  let hex := exists_injective_nat (Σ n : ℕ, simplexBasisIndex n)
  let e := Classical.choose hex
  have he : Function.Injective e := Classical.choose_spec hex
  exact (((centeredUnitIncrement_orthonormal hB).comp e he).orthogonalFamily.linearIsometry).comp
    positiveKernelHilbertBasis.repr.toLinearIsometry

private def processMeasurableL2Exhausts (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) : Prop :=
  ∃ hmeas : ∀ t, Measurable (B t), Function.Surjective (processLpEmbedding P B hmeas)

/-- A single isometry from the positive kernel sum into centered `L²(P)`.  It is selected to be
onto only when ambient `L²` is second-countable and every ambient class has a representative
measurable for the process-generated sigma-algebra.  Otherwise the explicit Brownian increment
sequence supplies a generated embedding satisfying all order-by-order Hilbert laws.  Neither
choice by itself asserts compatibility with ordered-box products. -/
noncomputable def positiveIteratedTowerLI (hB : IsPreBrownianReal B P) :
    PositiveKernelSum →ₗᵢ[ℝ] CenteredRandomL2 hB := by
  classical
  exact if h : Nonempty (SecondCountableTopology (CenteredRandomL2 hB)) ∧
      processMeasurableL2Exhausts P B then
      let _ : SecondCountableTopology (CenteredRandomL2 hB) := Classical.choice h.1
      (Classical.choice (nonempty_positiveKernelSum_equiv_centered hB)).toLinearIsometry
    else
      positiveKernelEmbeddingCentered hB

/-- The selected positive tower is onto whenever process-measurable `L²` exhausts a
second-countable ambient `L²` space. -/
theorem positiveIteratedTowerLI_surjective_of_processLpEmbedding
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hmeas : ∀ t, Measurable (B t))
    (hexhausts : Function.Surjective (processLpEmbedding P B hmeas)) :
    Function.Surjective (positiveIteratedTowerLI hB) := by
  classical
  have hcondition : processMeasurableL2Exhausts P B := ⟨hmeas, hexhausts⟩
  rw [positiveIteratedTowerLI, dif_pos ⟨⟨inferInstance⟩, hcondition⟩]
  exact (Classical.choice (nonempty_positiveKernelSum_equiv_centered hB)).surjective

/-- If the Brownian coordinates generate a second-countable ambient `L²` space, the selected
law-level tower exhausts its centered part. -/
theorem positiveIteratedTowerLI_surjective_of_generated
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hgen : IsWienerGenerated B) :
    Function.Surjective (positiveIteratedTowerLI hB) := by
  let hmeas : ∀ t, Measurable (B t) := hgen.measurable
  exact positiveIteratedTowerLI_surjective_of_processLpEmbedding hB hmeas
    (processLpEmbedding_surjective P B hmeas hgen)

-- Compiles at default 200k heartbeats (override removed).
private noncomputable def singleKernelLI (n : ℕ) :
    SimplexKernel (n + 1) →ₗᵢ[ℝ] PositiveKernelSum where
  toLinearMap := lp.lsingle (𝕜 := ℝ)
    (E := fun k : ℕ ↦ SimplexKernel (k + 1)) (2 : ℝ≥0∞) n
  norm_map' f := lp.norm_single (E := fun k : ℕ ↦ SimplexKernel (k + 1))
    (p := (2 : ℝ≥0∞)) (by norm_num) n f

/-- The isometric inclusion of one positive simplex order into ambient `L²(P)`. -/
noncomputable def simplexIntegralLI (hB : IsPreBrownianReal B P) (n : ℕ) :
    SimplexKernel (n + 1) →ₗᵢ[ℝ] RandomL2 P :=
  (CenteredRandomL2 hB).subtypeₗᵢ.comp
    ((positiveIteratedTowerLI hB).comp (singleKernelLI n))

@[simp] theorem simplexIntegralLI_apply (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : SimplexKernel (n + 1)) :
    simplexIntegralLI hB n f =
      ((positiveIteratedTowerLI hB (lp.single 2 n f) : CenteredRandomL2 hB) :
        RandomL2 P) :=
  rfl

/-- A vector in the positive kernel Hilbert sum is the sum of its orderwise selected simplex
images. -/
theorem hasSum_simplexIntegralLI (hB : IsPreBrownianReal B P) (f : PositiveKernelSum) :
    HasSum (fun n ↦ simplexIntegralLI hB n (f n))
      ((positiveIteratedTowerLI hB f : CenteredRandomL2 hB) : RandomL2 P) := by
  have hsum := lp.hasSum_single (E := fun n : ℕ ↦ SimplexKernel (n + 1))
    (p := (2 : ℝ≥0∞)) (by norm_num) f
  have himage := ((CenteredRandomL2 hB).subtypeₗᵢ.comp
    (positiveIteratedTowerLI hB)).toContinuousLinearMap.hasSum hsum
  convert himage using 1
  · funext n
    rw [simplexIntegralLI_apply]
    rfl
  · rfl

private noncomputable def positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel (n + 1) →L[ℝ] RandomL2 P :=
  (simplexIntegralLI hB n).toContinuousLinearMap.comp (restrictToSimplex (n + 1))

private theorem inner_positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB n f) (positiveIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 (n + 1), inner ℝ (f t) (g t)
        ∂iteratedKernelMeasure (n + 1) := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change inner ℝ (simplexIntegralLI hB n (restrictToSimplex (n + 1) f))
    (simplexIntegralLI hB n (restrictToSimplex (n + 1) g)) = _
  rw [LinearIsometry.inner_map_map]
  exact inner_restrictToSimplex (n + 1) f g

private theorem integral_positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) :
    ∫ ω, positiveIntegralCLM hB n f ω ∂P = 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmem : simplexIntegralLI hB n (restrictToSimplex (n + 1) f) ∈
      (ℝ ∙ probabilityOne hB)ᗮ := by
    simpa only [simplexIntegralLI_apply] using
      (positiveIteratedTowerLI hB
        (lp.single 2 n (restrictToSimplex (n + 1) f))).property
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  change inner ℝ
    (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ))
    (simplexIntegralLI hB n (restrictToSimplex (n + 1) f)) = 0 at hi
  rwa [L2.inner_indicatorConstLp_one, setIntegral_univ] at hi

private theorem inner_positiveIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel (m + 1)) (g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB m f) (positiveIntegralCLM hB n g) = 0 := by
  change inner ℝ
    ((CenteredRandomL2 hB).subtypeₗᵢ
      (positiveIteratedTowerLI hB
        (lp.single 2 m (restrictToSimplex (m + 1) f))))
    ((CenteredRandomL2 hB).subtypeₗᵢ
      (positiveIteratedTowerLI hB
        (lp.single 2 n (restrictToSimplex (n + 1) g)))) = 0
  rw [LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]
  change inner ℝ
    (lp.single 2 m (restrictToSimplex (m + 1) f) : PositiveKernelSum)
    (lp.single 2 n (restrictToSimplex (n + 1) g) : PositiveKernelSum) = 0
  rw [lp.inner_single_left,
    lp.single_apply_ne (E := fun k : ℕ ↦ SimplexKernel (k + 1)) 2 n
      (restrictToSimplex (n + 1) g) hmn]
  exact inner_zero_right _

private theorem norm_positiveIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) : ‖positiveIntegralCLM hB n f‖ ≤ ‖f‖ := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply]
  change ‖simplexIntegralLI hB n (restrictToSimplex (n + 1) f)‖ ≤ ‖f‖
  rw [LinearIsometry.norm_map]
  exact norm_restrictToSimplex_le (n + 1) f

private noncomputable def integralCLM (hB : IsPreBrownianReal B P) :
    (n : ℕ) → IteratedKernel n →L[ℝ] RandomL2 P
  | 0 => zeroIntegralCLM hB
  | n + 1 => positiveIntegralCLM hB n

private theorem integralCLM_sameOrder (hB : IsPreBrownianReal B P)
    (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (integralCLM hB n f) (integralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  cases n with
  | zero => exact zeroIntegralCLM_sameOrder hB f g
  | succ n => exact inner_positiveIntegralCLM hB n f g

private theorem integralCLM_centered (hB : IsPreBrownianReal B P)
    (n : ℕ) (hn : 0 < n) (f : IteratedKernel n) :
    ∫ ω, integralCLM hB n f ω ∂P = 0 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact integral_positiveIntegralCLM hB n f

private theorem integralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => integralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 :=
  zeroIntegralCLM_coe hB f

private theorem integralCLM_differentOrder (hB : IsPreBrownianReal B P)
    {m n : ℕ} (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (integralCLM hB m f) (integralCLM hB n g) = 0 := by
  cases m with
  | zero =>
      cases n with
      | zero => exact False.elim (hmn rfl)
      | succ n =>
          exact zeroIntegralCLM_inner_centered hB f (positiveIntegralCLM hB n g)
            (integral_positiveIntegralCLM hB n g)
  | succ m =>
      cases n with
      | zero =>
          rw [real_inner_comm]
          exact zeroIntegralCLM_inner_centered hB g (positiveIntegralCLM hB m f)
            (integral_positiveIntegralCLM hB m f)
      | succ n =>
          have hmn' : m ≠ n := fun h => hmn (congrArg Nat.succ h)
          exact inner_positiveIntegralCLM_ne hB hmn' f g

private theorem integralCLM_norm_le (hB : IsPreBrownianReal B P)
    (n : ℕ) (f : IteratedKernel n) : ‖integralCLM hB n f‖ ≤ ‖f‖ := by
  cases n with
  | zero => exact zeroIntegralCLM_norm_le hB f
  | succ n => exact norm_positiveIntegralCLM_le hB n f

/-- A law-level iterated-integral family obtained from the global positive kernel tower. -/
noncomputable def family (hB : IsPreBrownianReal B P) : IteratedIntegralFamily P where
  integral := integralCLM hB
  sameOrder := integralCLM_sameOrder hB
  centered := integralCLM_centered hB
  zeroOrder := integralCLM_zeroOrder hB
  differentOrder := integralCLM_differentOrder hB
  norm_integral_le := integralCLM_norm_le hB

end IteratedIntegralConstruction

/-- Construction of a law-level family satisfying the iterated-integral Hilbert-space laws.

Restriction to each simplex is a contraction.  The external sum of all positive orders embeds
isometrically in centered `L²(P)`.  It is selected to be onto only when process-measurable `L²`
exhausts a separable ambient space; order zero is the constant embedding. -/
noncomputable def iteratedIntegralFamily
    (hB : IsPreBrownianReal B P) : IteratedIntegralFamily P :=
  IteratedIntegralConstruction.family hB

/-- `Jₙ`, the selected order-`n` law-level operator, as a continuous linear map. -/
noncomputable def iteratedIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (iteratedIntegralFamily hB).integral n

/-- On a symmetrized positive-order kernel, `Jₙ₊₁` is the corresponding simplex summand
of the global positive tower. -/
theorem iteratedIntegralCLM_symmetrized (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) :
    iteratedIntegralCLM hB (n + 1)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2 f) =
      IteratedIntegralConstruction.simplexIntegralLI hB n
        (IteratedIntegralConstruction.symmetrizeRestrict (n + 1) f) :=
  rfl

/-- The polarized simplex isometry for two kernels of the same order. -/
theorem inner_iteratedIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB n f) (iteratedIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n :=
  (iteratedIntegralFamily hB).sameOrder n f g

/-- Positive-order operators in the selected family have expectation zero. -/
theorem integral_iteratedIntegralCLM (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, iteratedIntegralCLM hB n f ω ∂P = 0 :=
  (iteratedIntegralFamily hB).centered n hn f

/-- `J₀` identifies the one-dimensional zeroth kernel space with constant random variables. -/
theorem iteratedIntegralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => iteratedIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 :=
  (iteratedIntegralFamily hB).zeroOrder f

/-- Different orders in the selected tower are orthogonal in `L²(P)`. -/
theorem inner_iteratedIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB m f) (iteratedIntegralCLM hB n g) = 0 :=
  (iteratedIntegralFamily hB).differentOrder hmn f g

/-- The full-product-domain operator `Jₙ` is a contraction. -/
theorem norm_iteratedIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖iteratedIntegralCLM hB n f‖ ≤ ‖f‖ :=
  (iteratedIntegralFamily hB).norm_integral_le n f

end ContinuousTower

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
