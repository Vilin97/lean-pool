/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Jcut
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Amnr
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.QMNR
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureEnergyIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DriftCommutatorExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TensorNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceSmallnessThreshold
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source-scale reduction for the remainder index.  The corrected
indexing fixes the remainder at `Jcut β`; the estimates below retain that exact exponent. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4

/-- The actual tensor remainder at the corrected index `Jcut`. -/
def dmFrozenTailTerm {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ)
    (z : ℝ × Vec 2) : Vec 2 := fun i =>
      ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
          I.qMNR κ m n (AVenhance.Jcut β) z.1 j k

/-- `d_m` source split with its first vector term left explicit.  The
first term is `(Jhat_m - J_m) Σ_l xihat_l (∇X_l∘X_l⁻¹)∇T`; the second is
the literal `A_{m,n,Jcut} q_{m,n,Jcut}` remainder. -/
def dmFrozenSource {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (first : ℝ × Vec 2 → Vec 2) (z : ℝ × Vec 2) : Vec 2 :=
  first z + ∑ n ∈ Finset.range (AVenhance.Nstar β),
    dmFrozenTailTerm I hΦ m κ T n z

/-- The `Jhat_m - J_m` first term of `d_m`:
`Σ_l ξ̂_l F_lᵀ (JHat - 𝒥) F_l ∇T`, with the flow Jacobian `F_l` on both sides of
the flux gap (§9.4). -/
def dmFrozenFluxFirst {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (z : ℝ × Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l z.1 •
    ((I.flowGrad hΦ m l z.1 z.2).transpose.mulVec
      ((I.Jhat κ m z.1 - I.flux κ m z.1).mulVec
        ((I.flowGrad hΦ m l z.1 z.2).mulVec (AVenhance.spaceGrad (T z.1) z.2))))

/-- In two dimensions, the elementwise matrix supremum norm controls its
action on vectors equipped with the `Vec 2` supremum norm. -/
theorem matrix_mulVec_norm_le_two {M : Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2}
    (F : ℝ) (hF : 0 ≤ F) (hM : ‖M‖ ≤ F) :
    ‖M.mulVec v‖ ≤ 2 * F * ‖v‖ := by
  change ‖fun i => ∑ j : Fin 2, M i j * v j‖ ≤ 2 * F * ‖v‖
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * F * ‖v‖)).2
  intro i
  change |∑ j : Fin 2, M i j * v j| ≤ 2 * F * ‖v‖
  calc
    |∑ j : Fin 2, M i j * v j| ≤
        ∑ j : Fin 2, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 2, F * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hentry : |M i j| ≤ F := by
        have hrow : ‖M i‖ ≤ ‖M‖ := norm_le_pi_norm M i
        have hcol : |M i j| ≤ ‖M i‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (M i) j
        exact hcol.trans (hrow.trans hM)
      have hv : |v j| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
      calc
        |M i j| * |v j| ≤ F * |v j| :=
          mul_le_mul_of_nonneg_right hentry (abs_nonneg _)
        _ ≤ F * ‖v‖ := mul_le_mul_of_nonneg_left hv hF
    _ = 2 * F * ‖v‖ := by simp; ring

/-- Convexity of the cutoff average for vector-valued summands. -/
theorem hatXiML_average_norm_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (f : ℤ → Vec 2) {B : ℝ}
    (hb : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ‖f l‖ ≤ B) :
    ‖∑' l : ℤ, I.hatXiML m l t • f l‖ ≤ B := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  have hz (l : ℤ) (hl : l ∉ S) : I.hatXiML m l t = 0 := by
    by_contra hne
    exact hl ((Set.Finite.mem_toFinset _).2 hne)
  have hsum : (∑' l : ℤ, I.hatXiML m l t • f l) =
      ∑ l ∈ S, I.hatXiML m l t • f l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_smul])
  have hweights : ∑ l ∈ S, I.hatXiML m l t = 1 := by
    have hh : (∑' l : ℤ, I.hatXiML m l t) = ∑ l ∈ S, I.hatXiML m l t :=
      tsum_eq_sum (fun l hl => hz l hl)
    rw [← hh]
    exact AVenhance.Infra.Ingredients.hatXiML_partition I hm t
  rw [hsum]
  calc
    ‖∑ l ∈ S, I.hatXiML m l t • f l‖ ≤
        ∑ l ∈ S, ‖I.hatXiML m l t • f l‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ S, I.hatXiML m l t * B := by
      apply Finset.sum_le_sum
      intro l _
      have hw := (AVenhance.Infra.Ingredients.hatXiML_mem_Icc I hm l t).1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      by_cases h0 : I.hatXiML m l t = 0
      · simp [h0]
      · exact mul_le_mul_of_nonneg_left (hb l h0) hw
    _ = B := by rw [← Finset.sum_mul, hweights, one_mul]

/-- Pointwise bound on the first summand from an active-window flow bound
and a uniform flux-gap bound. -/
theorem dmFrozenFluxFirst_norm_le {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ L)
    {F : ℝ} (hF : 0 ≤ F)
    (hgap : ∀ t, ‖I.Jhat κ m t - I.flux κ m t‖ ≤ F) (z : ℝ × Vec 2) :
    ‖dmFrozenFluxFirst I hΦ m κ T z‖ ≤
      2 * F * (4 * L ^ 2) * ‖AVenhance.spaceGrad (T z.1) z.2‖ := by
  unfold dmFrozenFluxFirst
  refine hatXiML_average_norm_le I hm z.1 _ ?_
  intro l hl
  have hFl := hflow z l hl
  have hFlT : ‖(I.flowGrad hΦ m l z.1 z.2).transpose‖ ≤ L := by
    rwa [Matrix.norm_transpose]
  have h1 := matrix_mulVec_norm_le_two (M := I.flowGrad hΦ m l z.1 z.2)
    (v := AVenhance.spaceGrad (T z.1) z.2) L hL hFl
  have h2 := matrix_mulVec_norm_le_two (M := I.Jhat κ m z.1 - I.flux κ m z.1)
    (v := (I.flowGrad hΦ m l z.1 z.2).mulVec (AVenhance.spaceGrad (T z.1) z.2))
    F hF (hgap z.1)
  have h3 := matrix_mulVec_norm_le_two
    (M := (I.flowGrad hΦ m l z.1 z.2).transpose)
    (v := (I.Jhat κ m z.1 - I.flux κ m z.1).mulVec
      ((I.flowGrad hΦ m l z.1 z.2).mulVec (AVenhance.spaceGrad (T z.1) z.2)))
    L hL hFlT
  have hg := norm_nonneg (AVenhance.spaceGrad (T z.1) z.2)
  calc
    _ ≤ 2 * L * ‖(I.Jhat κ m z.1 - I.flux κ m z.1).mulVec
        ((I.flowGrad hΦ m l z.1 z.2).mulVec
          (AVenhance.spaceGrad (T z.1) z.2))‖ := h3
    _ ≤ 2 * L * (2 * F * ‖(I.flowGrad hΦ m l z.1 z.2).mulVec
          (AVenhance.spaceGrad (T z.1) z.2)‖) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * L * (2 * F * (2 * L * ‖AVenhance.spaceGrad (T z.1) z.2‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
    _ = 2 * F * (4 * L ^ 2) * ‖AVenhance.spaceGrad (T z.1) z.2‖ := by ring

/-- The first term has the Piola-conjugated flux gap as multiplier.  Its
analytic inputs are a pointwise bound `L` on the active flow Jacobians and the
source `L²` bound for the temperature gradient; the flux gap is supplied by the
corrected Section 3 `Jhat` estimate. -/
theorem dm_frozenFluxFirst_eLpNorm_le {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hfirstMeas : AEStronglyMeasurable (dmFrozenFluxFirst I hΦ m κ T)
      (volume.restrict AVenhance.timeCube))
    {L : ℝ} (hL : 0 ≤ L)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ L)
    {G₀ : ℝ}
    (hTgrad : eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal G₀)
    {F : ℝ} (hF : 0 ≤ F)
    (hgap : ∀ t, ‖I.Jhat κ m t - I.flux κ m t‖ ≤ F)
    (hm : 1 ≤ m) :
    eLpNorm (dmFrozenFluxFirst I hΦ m κ T) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal (2 * F * (4 * L ^ 2 * G₀)) := by
  set C : ℝ := 2 * F * (4 * L ^ 2) with hC
  have hCnn : 0 ≤ C := by positivity
  have hpoint : ∀ z : ℝ × Vec 2,
      ‖dmFrozenFluxFirst I hΦ m κ T z‖ ≤
        ‖C • AVenhance.spaceGrad (T z.1) z.2‖ := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hCnn]
    exact dmFrozenFluxFirst_norm_le I hΦ m hm κ T hL hflow hF hgap z
  have hmono := eLpNorm_mono_ae hfirstMeas (Filter.Eventually.of_forall hpoint) (p := 2)
  have hsmulFun : (fun z : ℝ × Vec 2 => C • AVenhance.spaceGrad (T z.1) z.2) =
      C • (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) := rfl
  have hscale :
      eLpNorm (fun z : ℝ × Vec 2 => C • AVenhance.spaceGrad (T z.1) z.2) 2
        (volume.restrict AVenhance.timeCube) =
      ENNReal.ofReal C *
        eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
          (volume.restrict AVenhance.timeCube) := by
    rw [hsmulFun, eLpNorm_const_smul, Real.enorm_of_nonneg hCnn]
  rw [hscale] at hmono
  calc
    eLpNorm (dmFrozenFluxFirst I hΦ m κ T) 2
        (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal C *
        eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
          (volume.restrict AVenhance.timeCube) := hmono
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal G₀ :=
      mul_le_mul_of_nonneg_left hTgrad (by positivity)
    _ = ENNReal.ofReal (2 * F * (4 * L ^ 2 * G₀)) := by
      rw [← ENNReal.ofReal_mul hCnn, hC]
      congr 1
      ring

/-- Specialization of the preceding first-term estimate to the actual Section 3 coefficients.  The
    paper's `J_m` is the flux, so the corrected
`flux_sub_Jhat_norm_le` estimate bounds the matrix multiplier directly. -/
theorem dm_frozenFluxFirst_eLpNorm_le_of_section3 {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {G : ℝ} (hfirstMeas : AEStronglyMeasurable
      (dmFrozenFluxFirst I hΦ m κ T) (volume.restrict AVenhance.timeCube))
    {L : ℝ} (hL : 0 ≤ L)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ L)
    {G₀ : ℝ}
    (hTgrad : eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal G₀)
    (hGL : 4 * L ^ 2 * G₀ ≤ G)
    (hm : 1 ≤ m) (hκ : 0 < κ) :
    eLpNorm (dmFrozenFluxFirst I hΦ m κ T) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal (2 *
        ((4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
            2 ^ AVenhance.Nstar β) *
          (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
          (AVenhance.epsilon β I.Λ m ^ 2 /
            (κ * AVenhance.tau β I.Λ m)) ^ AVenhance.Nstar β) * G) := by
  let F := (4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
      2 ^ AVenhance.Nstar β) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
    (AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m)) ^ AVenhance.Nstar β
  have hflux (t : ℝ) : ‖I.flux κ m t - I.Jhat κ m t‖ ≤ F := by
    simpa only [F] using AVenhance.Infra.Section3.flux_sub_Jhat_norm_le I hm hκ t
  have hF : 0 ≤ F := le_trans (norm_nonneg _) (hflux 0)
  have hgap : ∀ t, ‖I.Jhat κ m t - I.flux κ m t‖ ≤ F := by
    intro t
    simpa only [norm_sub_rev] using hflux t
  have hbase := dm_frozenFluxFirst_eLpNorm_le I hΦ m κ T
    hfirstMeas hL hflow hTgrad hF hgap hm
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2F : 0 ≤ 2 * F := by positivity
  simpa only [F] using mul_le_mul_of_nonneg_left hGL h2F

/-- One coordinate summand in the `A_{m,n,Jcut} q_{m,n,Jcut}`
vector tail. -/
def dmFrozenTailCoordinateTerm {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ)
    (i j k : Fin 2) (z : ℝ × Vec 2) : Vec 2 := fun p =>
      if i = p then
        I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
          I.qMNR κ m n (AVenhance.Jcut β) z.1 j k
      else 0

/-- L² multiplication by a scalar bounded in absolute value. -/
theorem eLpNorm_mul_right_le_of_abs_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {f g : α → ℝ} {A Q : ℝ} (hQ : 0 ≤ Q)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hbound : ∀ x, |g x| ≤ Q)
    (hLp : eLpNorm f 2 μ ≤ ENNReal.ofReal A) :
    eLpNorm (fun x => f x * g x) 2 μ ≤ ENNReal.ofReal (Q * A) := by
  have hfun : (fun x => Q • f x) = Q • f := rfl
  have hpoint : ∀ x, ‖f x * g x‖ ≤ ‖Q • f x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hQ]
    calc
      |f x| * |g x| ≤ |f x| * Q :=
        mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg (f x))
      _ = Q * |f x| := by ring
  have hmono := eLpNorm_mono_ae (hf.mul hg)
    (Filter.Eventually.of_forall hpoint) (p := 2)
  rw [hfun, eLpNorm_const_smul, Real.enorm_of_nonneg hQ] at hmono
  calc
    eLpNorm (fun x => f x * g x) 2 μ ≤
      ENNReal.ofReal Q * eLpNorm f 2 μ := hmono
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal A :=
      mul_le_mul_of_nonneg_left hLp (by positivity)
    _ = ENNReal.ofReal (Q * A) := (ENNReal.ofReal_mul hQ).symm

/-- Decomposition of the vector tail into its eight single-coordinate
products. -/
theorem dmFrozenTailTerm_eq_coordinate_sum {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ) (z : ℝ × Vec 2) :
    dmFrozenTailTerm I hΦ m κ T n z =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        dmFrozenTailCoordinateTerm I hΦ m κ T n i j k z := by
  funext i
  change (∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
        I.qMNR κ m n (AVenhance.Jcut β) z.1 j k) =
    ∑ i' : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      (if i' = i then
        I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i' j k *
          I.qMNR κ m n (AVenhance.Jcut β) z.1 j k
      else 0)
  simp [Finset.sum_ite_eq']

/-- Actual tail estimate from the `(k,ell)=(0,0)` instance of the
source `p.Amnr.bounds` and the corrected geometric qMNR bound.  The
AMNR input is the tensor-valued source estimate; only its finite coordinate
projections are used here. -/
theorem dmFrozenTailTerm_eLpNorm_le_of_pAmnr_qMNR {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ)
    {μ : Measure (ℝ × Vec 2)}
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hAmnr : eLpNorm
      (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
        z.1 z.2) 2 μ ≤ ENNReal.ofReal A)
    (hAentryMeas : ∀ i j k : Fin 2,
      AEStronglyMeasurable
        (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
          z.1 z.2 i j k) μ)
    (hCoordinateMeas : ∀ i j k : Fin 2,
      AEStronglyMeasurable (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) μ)
    (hn : n ≤ AVenhance.Nstar β) :
    eLpNorm (dmFrozenTailTerm I hΦ m κ T n) 2 μ ≤
      ENNReal.ofReal (8 * A *
        ((4 * Real.pi ^ 2 * C₀) *
          (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
          (AVenhance.epsilon β I.Λ m ^ 2 /
            (κ * AVenhance.tau β I.Λ m)) ^ n *
          (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β)) := by
  let Q := (4 * Real.pi ^ 2 * C₀) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
    (AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m)) ^ n *
    (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β
  have hqmatrix (t : ℝ) : ‖I.qMNR κ m n (AVenhance.Jcut β) t‖ ≤ Q := by
    simpa only [Q] using
      AVenhance.Infra.Section3.qMNR_norm_paper_bound I hcutoff hm hκ hn
        (AVenhance.Jcut β) t
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg _) (hqmatrix 0)
  have hqentry (t : ℝ) (j k : Fin 2) :
      |I.qMNR κ m n (AVenhance.Jcut β) t j k| ≤ Q := by
    have hrow : ‖I.qMNR κ m n (AVenhance.Jcut β) t j‖ ≤
        ‖I.qMNR κ m n (AVenhance.Jcut β) t‖ :=
      norm_le_pi_norm (I.qMNR κ m n (AVenhance.Jcut β) t) j
    have hentry : |I.qMNR κ m n (AVenhance.Jcut β) t j k| ≤
        ‖I.qMNR κ m n (AVenhance.Jcut β) t j‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (I.qMNR κ m n (AVenhance.Jcut β) t j) k
    exact hentry.trans (hrow.trans (hqmatrix t))
  have hAentryLp (i j k : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T
        (AVenhance.Jcut β) z.1 z.2 i j k) 2 μ ≤ ENNReal.ofReal A := by
    have hmono := eLpNorm_mono_ae (hAentryMeas i j k)
      (Filter.Eventually.of_forall fun z => by
        have hi : ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i j k‖ ≤ ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i j‖ := norm_le_pi_norm _ _
        have hj : ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i j‖ ≤ ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i‖ := norm_le_pi_norm _ _
        have hk : ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i‖ ≤ ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2‖ := norm_le_pi_norm _ _
        exact (hi.trans (hj.trans hk))) (p := 2)
    exact hmono.trans hAmnr
  have hprod (i j k : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 =>
        I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
          I.qMNR κ m n (AVenhance.Jcut β) (z.1) j k) 2 μ ≤
        ENNReal.ofReal (Q * A) := by
    apply eLpNorm_mul_right_le_of_abs_bound hQ0
      (hAentryMeas i j k)
    · have hcont := AVenhance.Infra.Section3.qMNR_entry_continuous
        I κ m n (AVenhance.Jcut β) j k
      exact (hcont.comp continuous_fst).aestronglyMeasurable
    · intro z
      exact hqentry z.1 j k
    · exact hAentryLp i j k
  have hcoordLp (i j k : Fin 2) :
      eLpNorm (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) 2 μ ≤
        ENNReal.ofReal (Q * A) := by
    have hpoint (z : ℝ × Vec 2) :
        ‖dmFrozenTailCoordinateTerm I hΦ m κ T n i j k z‖ ≤
          |I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
            I.qMNR κ m n (AVenhance.Jcut β) z.1 j k| := by
      change ‖fun p : Fin 2 =>
        if i = p then
          I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
            I.qMNR κ m n (AVenhance.Jcut β) z.1 j k
        else 0‖ ≤ _
      apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
      intro p
      by_cases hp : i = p
      · simp [hp]
      · simp only [hp, ↓reduceIte, norm_zero, abs_mul]
        positivity
    have hmono := eLpNorm_mono_ae (hCoordinateMeas i j k)
      (Filter.Eventually.of_forall fun z => by
        change ‖dmFrozenTailCoordinateTerm I hΦ m κ T n i j k z‖ ≤
          ‖I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
            I.qMNR κ m n (AVenhance.Jcut β) z.1 j k‖
        calc
          _ ≤ |I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k *
                I.qMNR κ m n (AVenhance.Jcut β) z.1 j k| := hpoint z
          _ = _ := (Real.norm_eq_abs _).symm) (p := 2)
    have hprod' := hprod i j k
    simpa only [Real.norm_eq_abs] using hmono.trans hprod'
  have hdecomp : (fun z : ℝ × Vec 2 => dmFrozenTailTerm I hΦ m κ T n z) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        dmFrozenTailCoordinateTerm I hΦ m κ T n i j k := by
    funext z
    exact dmFrozenTailTerm_eq_coordinate_sum I hΦ m κ T n z
  change eLpNorm (fun z : ℝ × Vec 2 => dmFrozenTailTerm I hΦ m κ T n z) 2 μ ≤ _
  rw [hdecomp]
  calc
    eLpNorm (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) 2 μ ≤
      ∑ i : Fin 2, eLpNorm (∑ j : Fin 2, ∑ k : Fin 2,
        dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) 2 μ :=
      eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, eLpNorm
        (∑ k : Fin 2, dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) 2 μ := by
      apply Finset.sum_le_sum
      intro i _
      exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        eLpNorm (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k) 2 μ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, ∑ _k : Fin 2,
        ENNReal.ofReal (Q * A) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact hcoordLp i j k
    _ = ENNReal.ofReal (8 * A * Q) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      calc
        _ = 8 * ENNReal.ofReal (Q * A) := by ring
        _ = ENNReal.ofReal 8 * ENNReal.ofReal (Q * A) := by
          norm_num
        _ = ENNReal.ofReal (8 * (Q * A)) :=
          (ENNReal.ofReal_mul (show 0 ≤ (8 : ℝ) by norm_num)).symm
        _ = ENNReal.ofReal (8 * A * Q) := by congr 1; ring

/-- L² triangle estimate for the `d_m` split. -/
theorem dm_frozenSource_eLpNorm_le_of_term_bounds {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (first : ℝ × Vec 2 → Vec 2) {Bfirst Btail : ℝ}
    (hBfirst : 0 ≤ Bfirst) (hBtail : 0 ≤ Btail)
    (hfirst : eLpNorm first 2 (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal Bfirst)
    (htail : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm (dmFrozenTailTerm I hΦ m κ T n) 2
        (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Btail) :
    eLpNorm (dmFrozenSource I hΦ m κ T first) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal (Bfirst + (AVenhance.Nstar β : ℝ) * Btail) := by
  have hsum : eLpNorm (fun z : ℝ × Vec 2 =>
      ∑ n ∈ Finset.range (AVenhance.Nstar β), dmFrozenTailTerm I hΦ m κ T n z) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal ((AVenhance.Nstar β : ℝ) * Btail) := by
    have hsumFun : (fun z : ℝ × Vec 2 =>
        ∑ n ∈ Finset.range (AVenhance.Nstar β), dmFrozenTailTerm I hΦ m κ T n z) =
        ∑ n ∈ Finset.range (AVenhance.Nstar β), dmFrozenTailTerm I hΦ m κ T n := by
      funext z
      simp
    rw [hsumFun]
    calc
      _ ≤ ∑ n ∈ Finset.range (AVenhance.Nstar β),
          eLpNorm (dmFrozenTailTerm I hΦ m κ T n) 2
            (volume.restrict AVenhance.timeCube) :=
        eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ∑ _n ∈ Finset.range (AVenhance.Nstar β), ENNReal.ofReal Btail :=
        Finset.sum_le_sum fun n hn => htail n hn
      _ = ENNReal.ofReal ((AVenhance.Nstar β : ℝ) * Btail) := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul, ENNReal.ofReal_mul hBtail, mul_comm]
  change eLpNorm (fun z : ℝ × Vec 2 => first z +
      ∑ n ∈ Finset.range (AVenhance.Nstar β), dmFrozenTailTerm I hΦ m κ T n z) 2
      (volume.restrict AVenhance.timeCube) ≤ _
  calc
    _ ≤ eLpNorm first 2 (volume.restrict AVenhance.timeCube) +
        eLpNorm (fun z : ℝ × Vec 2 =>
          ∑ n ∈ Finset.range (AVenhance.Nstar β), dmFrozenTailTerm I hΦ m κ T n z) 2
          (volume.restrict AVenhance.timeCube) :=
      eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ENNReal.ofReal Bfirst + ENNReal.ofReal ((AVenhance.Nstar β : ℝ) * Btail) :=
      add_le_add hfirst hsum
    _ = ENNReal.ofReal (Bfirst + (AVenhance.Nstar β : ℝ) * Btail) := by
      have hNtail : 0 ≤ (AVenhance.Nstar β : ℝ) * Btail := by positivity
      rw [← ENNReal.ofReal_add hBfirst hNtail]

/-- Complete `d_m` source estimate after inserting the actual `J_m`
flux first term, the corrected Section 3 flux gap, and the `(0,0)` `p.Amnr`
source bound for every tail mode.  The ratio hypothesis is the Section 3
smallness input used to discard the remaining mode factor `R^n ≤ 1`. -/
theorem dm_frozenSource_eLpNorm_le_of_section3_pAmnr {β C₀ A G : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m) ≤ 1)
    (hfirstMeas : AEStronglyMeasurable
      (dmFrozenFluxFirst I hΦ m κ T) (volume.restrict AVenhance.timeCube))
    {L : ℝ} (hL : 0 ≤ L)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ L)
    {G₀ : ℝ}
    (hTgrad : eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal G₀)
    (hGL : 4 * L ^ 2 * G₀ ≤ G)
    (hAmnr : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm
        (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
          z.1 z.2) 2 (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal A)
    (hAentryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i j k) (volume.restrict AVenhance.timeCube))
    (hCoordinateMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable
          (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k)
          (volume.restrict AVenhance.timeCube)) :
    eLpNorm (dmFrozenSource I hΦ m κ T
      (dmFrozenFluxFirst I hΦ m κ T)) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        (2 *
            ((4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
                2 ^ AVenhance.Nstar β) *
              (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
              (AVenhance.epsilon β I.Λ m ^ 2 /
                (κ * AVenhance.tau β I.Λ m)) ^ AVenhance.Nstar β) * G +
          (AVenhance.Nstar β : ℝ) *
            (8 * A *
              ((4 * Real.pi ^ 2 * C₀) *
                (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
                (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β))) := by
  let R := AVenhance.epsilon β I.Λ m ^ 2 /
    (κ * AVenhance.tau β I.Λ m)
  let Q := (4 * Real.pi ^ 2 * C₀) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
    (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β
  have hτ := I.tau_pos' m
  have hε := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hcutoff]
    positivity
  have hfirst := dm_frozenFluxFirst_eLpNorm_le_of_section3 I hΦ m κ T
    hfirstMeas hL hflow hTgrad hGL hm hκ
  have htail (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) :
      eLpNorm (dmFrozenTailTerm I hΦ m κ T n)
        2 (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal (8 * A * Q) := by
    have hnle : n ≤ AVenhance.Nstar β := (Finset.mem_range.mp hn).le
    have htail' := dmFrozenTailTerm_eLpNorm_le_of_pAmnr_qMNR I hΦ m κ T n
      hcutoff hm hκ (hAmnr n hn) (hAentryMeas n hn)
      (hCoordinateMeas n hn) hnle
    have hpow : R ^ n ≤ 1 := pow_le_one₀ hR0 hratio
    have hmul : 8 * A * (Q * R ^ n) ≤ 8 * A * Q := by
      calc
        _ = (8 * A * Q) * R ^ n := by ring
        _ ≤ (8 * A * Q) * 1 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = _ := by ring
    have htail'' : eLpNorm (dmFrozenTailTerm I hΦ m κ T n)
        2 (volume.restrict AVenhance.timeCube) ≤
          ENNReal.ofReal (8 * A * (Q * R ^ n)) := by
      refine htail'.trans ?_
      apply ENNReal.ofReal_le_ofReal
      dsimp [R, Q]
      ring_nf
      exact le_rfl
    calc
      _ ≤ ENNReal.ofReal (8 * A * (Q * R ^ n)) := htail''
      _ ≤ ENNReal.ofReal (8 * A * Q) := ENNReal.ofReal_le_ofReal hmul
  have hfirstNonneg : 0 ≤
      2 *
        ((4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
            2 ^ AVenhance.Nstar β) *
          (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
          R ^ AVenhance.Nstar β) * G := by
    have hCzeta : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
    positivity
  have htailNonneg : 0 ≤ (AVenhance.Nstar β : ℝ) * (8 * A * Q) := by
    positivity
  have htailBaseNonneg : 0 ≤ 8 * A * Q := by positivity
  have hassembled := dm_frozenSource_eLpNorm_le_of_term_bounds I hΦ m κ T
    (dmFrozenFluxFirst I hΦ m κ T) hfirstNonneg htailBaseNonneg hfirst htail
  simpa only [R, Q] using hassembled

/-- Arithmetic consequences of for the cutoff. -/
theorem jcut_source_budget {β : ℝ} (hJ : 2 ≤ AVenhance.Jcut β) :
    1 ≤ AVenhance.Jcut β ∧ AVenhance.Jcut β ≤ AVenhance.Nstar β ∧
      AVenhance.Nstar β ≤ 3 * AVenhance.Jcut β ∧
      AVenhance.Jcut β ≤ 4 * AVenhance.Nstar β := by
  have hN : 1 ≤ AVenhance.Nstar β := by
    exact le_trans (by omega) (AVenhance.Infra.Section4.Jcut_le_iteration_budget β)
  have hlow := AVenhance.Infra.Section4.Jcut_budget hN
  have hhi : AVenhance.Nstar β ≤ 2 * AVenhance.Jcut β + 2 := by
    have hdiv := Nat.lt_mul_div_succ (AVenhance.Nstar β - 1) (by norm_num : 0 < 2)
    unfold AVenhance.Jcut at hdiv ⊢
    omega
  refine ⟨by omega, AVenhance.Infra.Section4.Jcut_le_iteration_budget β, ?_, ?_⟩
  · omega
  · omega

/-- Transfer of the first `d_m` term from the corrected `4δ` exprat scale
to the `Jcut` exponent.  The proof uses `N ≤ 3J` and `J ≤ 4N`, which hold
for the large cutoff once `Jcut ≥ 2`. -/
theorem dm_first_term_four_delta_to_Jcut {N J : ℕ}
    {Cexpr Couter x Khalf F : ℝ}
    (hCexpr : 1 ≤ Cexpr) (hCouter : 0 ≤ Couter)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hK : 0 ≤ Khalf)
    (hN : N ≤ 3 * J) (hJ : J ≤ 4 * N)
    (hfirst : F ≤ Couter * Khalf * (Cexpr * x ^ 4) ^ N) :
    F ≤ Couter * Khalf * (Cexpr ^ 3 * x) ^ J := by
  have hpowC : Cexpr ^ N ≤ (Cexpr ^ 3) ^ J := by
    calc
      Cexpr ^ N ≤ Cexpr ^ (3 * J) := pow_le_pow_right₀ hCexpr hN
      _ = (Cexpr ^ 3) ^ J := by rw [pow_mul]
  have hrest : x ^ (4 * N - J) ≤ 1 := pow_le_one₀ hx0 hx1
  have hpowx : x ^ (4 * N) ≤ x ^ J := by
    calc
      x ^ (4 * N) = x ^ (J + (4 * N - J)) := by congr 1; omega
      _ = x ^ J * x ^ (4 * N - J) := by rw [pow_add]
      _ ≤ x ^ J := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hrest (pow_nonneg hx0 _)
  have hpow : (Cexpr * x ^ 4) ^ N ≤ (Cexpr ^ 3 * x) ^ J := by
    calc
      (Cexpr * x ^ 4) ^ N = Cexpr ^ N * x ^ (4 * N) := by rw [mul_pow, pow_mul]
      _ ≤ (Cexpr ^ 3) ^ J * x ^ J :=
        mul_le_mul hpowC hpowx (pow_nonneg hx0 _) (by positivity)
      _ = (Cexpr ^ 3 * x) ^ J := by rw [mul_pow, ← pow_mul]
  exact hfirst.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCouter hK))

/-- Assembly of the corrected first-term transfer and the Jcut remainder
sum.  This is the scalar source split used before the spacetime L² triangle
inequality for the vector-valued `d_m`. -/
theorem dm_source_split_scale {N J : ℕ}
    {Cexpr Couter Afac CA x Khalf F Tail : ℝ}
    (hCexpr : 1 ≤ Cexpr) (hCouter : 0 ≤ Couter) (hAfac : 0 ≤ Afac)
    (hCA : 0 ≤ CA) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hK : 0 ≤ Khalf)
    (hN : N ≤ 3 * J) (hJ : J ≤ 4 * N)
    (hfirst : F ≤ Couter * Khalf * (Cexpr * x ^ 4) ^ N)
    (htail : Tail ≤ (N : ℝ) * CA * Khalf * (Afac * x) ^ J) :
    F + Tail ≤ (Couter + (N : ℝ) * CA) * Khalf *
      ((Cexpr ^ 3 + Afac + 1) * x) ^ J := by
  have hfirst' := dm_first_term_four_delta_to_Jcut hCexpr hCouter
    hx0 hx1 hK hN hJ hfirst
  have hscale : 0 ≤ Cexpr ^ 3 + Afac + 1 := by positivity
  have hbase₁ : Cexpr ^ 3 * x ≤ (Cexpr ^ 3 + Afac + 1) * x := by
    exact mul_le_mul_of_nonneg_right (by linarith) hx0
  have hbase₂ : Afac * x ≤ (Cexpr ^ 3 + Afac + 1) * x := by
    have hcub : 0 ≤ Cexpr ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) hx0
  have hpow₁ := pow_le_pow_left₀ (by positivity : 0 ≤ Cexpr ^ 3 * x) hbase₁ J
  have hpow₂ := pow_le_pow_left₀ (mul_nonneg hAfac hx0) hbase₂ J
  have hfirst'' : F ≤ Couter * Khalf *
      ((Cexpr ^ 3 + Afac + 1) * x) ^ J := by
    exact hfirst'.trans (mul_le_mul_of_nonneg_left hpow₁
      (mul_nonneg hCouter hK))
  have htail' : Tail ≤ (N : ℝ) * CA * Khalf *
      ((Cexpr ^ 3 + Afac + 1) * x) ^ J := by
    exact htail.trans (mul_le_mul_of_nonneg_left hpow₂
      (by positivity))
  calc
    F + Tail ≤ Couter * Khalf * ((Cexpr ^ 3 + Afac + 1) * x) ^ J +
        (N : ℝ) * CA * Khalf * ((Cexpr ^ 3 + Afac + 1) * x) ^ J :=
      add_le_add hfirst'' htail'
    _ = _ := by ring

/-- `p.dm.bounds` after the source parameter inequalities are supplied.
The first scalar premise is the four-delta flux transfer; the second is
the `p.Amnr`/`qMNR` scale for the Jcut tail.  The actual L² estimate
and its `J_m = flux` identification are proved by
`dm_frozenSource_eLpNorm_le_of_section3_pAmnr` above. -/
theorem dm_frozenSource_paper_scale {β C₀ A G Cexpr Couter Afac CA x Khalf : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m) ≤ 1)
    (hfirstMeas : AEStronglyMeasurable
      (dmFrozenFluxFirst I hΦ m κ T) (volume.restrict AVenhance.timeCube))
    {L : ℝ} (hL : 0 ≤ L)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ L)
    {G₀ : ℝ}
    (hTgrad : eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal G₀)
    (hGL : 4 * L ^ 2 * G₀ ≤ G)
    (hAmnr : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm
        (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
          z.1 z.2) 2 (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal A)
    (hAentryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => I.Amnr hΦ m κ n T (AVenhance.Jcut β)
            z.1 z.2 i j k) (volume.restrict AVenhance.timeCube))
    (hCoordinateMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable
          (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k)
          (volume.restrict AVenhance.timeCube))
    (hCexpr : 1 ≤ Cexpr) (hCouter : 0 ≤ Couter) (hAfac : 0 ≤ Afac)
    (hCA : 0 ≤ CA) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hK : 0 ≤ Khalf)
    (hcut : 2 ≤ AVenhance.Jcut β)
    (hfirstScale :
      2 *
          ((4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
              2 ^ AVenhance.Nstar β) *
            (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
            (AVenhance.epsilon β I.Λ m ^ 2 /
              (κ * AVenhance.tau β I.Λ m)) ^ AVenhance.Nstar β) * G ≤
        Couter * Khalf * (Cexpr * x ^ 4) ^ AVenhance.Nstar β)
    (htailScale :
      (AVenhance.Nstar β : ℝ) *
          (8 * A *
            ((4 * Real.pi ^ 2 * C₀) *
              (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
              (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β)) ≤
        (AVenhance.Nstar β : ℝ) * CA * Khalf *
          (Afac * x) ^ AVenhance.Jcut β) :
    eLpNorm (dmFrozenSource I hΦ m κ T (dmFrozenFluxFirst I hΦ m κ T)) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        ((Couter + (AVenhance.Nstar β : ℝ) * CA) * Khalf *
          ((Cexpr ^ 3 + Afac + 1) * x) ^ AVenhance.Jcut β) := by
  let F := 2 *
    ((4 * Real.pi ^ 2 * I.Czeta * AVenhance.Nstar β *
        2 ^ AVenhance.Nstar β) *
      (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κ) *
      (AVenhance.epsilon β I.Λ m ^ 2 /
        (κ * AVenhance.tau β I.Λ m)) ^ AVenhance.Nstar β) * G
  let Tail := (AVenhance.Nstar β : ℝ) *
    (8 * A *
      ((4 * Real.pi ^ 2 * C₀) *
        (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
        (8 * AVenhance.tau β I.Λ m) ^ AVenhance.Jcut β))
  have hactual := dm_frozenSource_eLpNorm_le_of_section3_pAmnr I hΦ m κ T
    hcutoff hm hκ hA hG hratio hfirstMeas hL hflow hTgrad hGL hAmnr hAentryMeas hCoordinateMeas
  have hactual' : eLpNorm
      (dmFrozenSource I hΦ m κ T (dmFrozenFluxFirst I hΦ m κ T)) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal (F + Tail) := by
    simpa only [F, Tail] using hactual
  have hbudget := jcut_source_budget hcut
  have hscalar := dm_source_split_scale hCexpr hCouter hAfac hCA hx0 hx1 hK
    hbudget.2.2.1 hbudget.2.2.2 hfirstScale htailScale
  exact hactual'.trans (ENNReal.ofReal_le_ofReal hscalar)

end AVenhance.Infra.Section4
