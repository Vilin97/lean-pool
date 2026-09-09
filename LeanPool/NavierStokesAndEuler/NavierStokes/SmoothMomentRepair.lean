/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MomentRepair
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Smooth dependence of quadratic moment repair

The coefficients of a quadratic moment map are included among the variables
of a universal polynomial map. Its derivative at zero correction is a proved
product equivalence. The smooth inverse-function theorem constructs a local
solver; no solution branch or its regularity is assumed.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace NavierStokes.SmoothMomentRepair

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev QuadraticCoefficients := (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)
abbrev RepairData := QuadraticCoefficients E × E

variable {E}

/-- The same type holds an unknown correction on input and a moment debt on output. -/
def forward (z : RepairData E) : RepairData E :=
  (z.1, z.1.1 z.2 + z.1.2 z.2 z.2)

def base (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) : RepairData E :=
  ((B.toContinuousLinearMap, A), 0)

theorem forward_base (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) :
    forward (base B A) = base B A := by
  simp [forward, base]

/-- This universal coefficient map is polynomial, hence analytic. -/
theorem forward_contDiff : ContDiff ℝ ⊤ (forward : RepairData E → RepairData E) :=
  contDiff_fst.prodMk ((contDiff_fst.fst.clm_apply contDiff_snd).add
    ((contDiff_fst.snd.clm_apply contDiff_snd).clm_apply contDiff_snd))

/-- Invertibility of the full product derivative is derived from the linear part alone. -/
theorem forward_hasFDerivAt (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) :
    HasFDerivAt forward
      (((ContinuousLinearEquiv.refl ℝ (QuadraticCoefficients E)).prodCongr B).toContinuousLinearMap)
      (base B A) := by
  have hp := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := RepairData E) (F := QuadraticCoefficients E)
    (ContinuousLinearMap.fst ℝ (QuadraticCoefficients E) E) (x := base B A)
  have hc := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := RepairData E) (F := E)
    (ContinuousLinearMap.snd ℝ (QuadraticCoefficients E) E) (x := base B A)
  simp only [ContinuousLinearMap.coe_fst'] at hp
  simp only [ContinuousLinearMap.coe_snd'] at hc
  have hB := HasFDerivAt.fst (𝕜 := ℝ) (E := RepairData E)
    (F := E →L[ℝ] E) (G := E →L[ℝ] E →L[ℝ] E) hp
  have hA := HasFDerivAt.snd (𝕜 := ℝ) (E := RepairData E)
    (F := E →L[ℝ] E) (G := E →L[ℝ] E →L[ℝ] E) hp
  have hBc := HasFDerivAt.clm_apply (𝕜 := ℝ) (E := RepairData E) (G := E) (H := E) hB hc
  have hAc := HasFDerivAt.clm_apply (𝕜 := ℝ) (E := RepairData E)
    (G := E) (H := E →L[ℝ] E) hA hc
  have hAcc := HasFDerivAt.clm_apply (𝕜 := ℝ) (E := RepairData E) (G := E) (H := E) hAc hc
  have hsum := HasFDerivAt.fun_add (𝕜 := ℝ) (E := RepairData E) (F := E) hBc hAcc
  convert! HasFDerivAt.prodMk (𝕜 := ℝ) (E := RepairData E)
    (F := QuadraticCoefficients E) (G := E) hp hsum using 1
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · change B z.2 = B z.2 + z.1.1 0 + ((A 0) z.2 + (A z.2 + z.1.2 0) 0)
    simp only [map_zero, zero_apply, add_zero]

/-- A common open neighborhood supports an analytic solution in all coefficients and the debt. -/
theorem exists_local_analytic_solver [CompleteSpace E]
    (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) :
    ∃ (g : RepairData E → E) (U : Set (RepairData E)),
      IsOpen U ∧ base B A ∈ U ∧ ContDiffOn ℝ ⊤ g U ∧ g (base B A) = 0 ∧
      ∀ z ∈ U, z.1.1 (g z) + z.1.2 (g z) (g z) = z.2 := by
  have hF : ContDiffAt ℝ ⊤ forward (base B A) := forward_contDiff.contDiffAt
  have hDF := forward_hasFDerivAt B A
  let inv : RepairData E → RepairData E := hF.localInverse hDF (by simp)
  have hcont : ContDiffAt ℝ ⊤ inv (base B A) := by
    simpa only [forward_base] using hF.to_localInverse hDF (by simp)
  have hinv0 : inv (base B A) = base B A := by
    simpa only [forward_base] using hF.localInverse_apply_image hDF (by simp)
  have hinv : ∀ᶠ z in 𝓝 (base B A), forward (inv z) = z := by
    have h := HasStrictFDerivAt.eventually_right_inverse
      (f' := (ContinuousLinearEquiv.refl ℝ (QuadraticCoefficients E)).prodCongr B)
      (hF.hasStrictFDerivAt' hDF (by simp))
    change ∀ᶠ z in 𝓝 (forward (base B A)), forward (inv z) = z at h
    simpa only [forward_base] using h
  have hsm := hcont.eventually (by simp)
  obtain ⟨U, hUsub, hUopen, hUbase⟩ := mem_nhds_iff.mp (hsm.and hinv)
  refine ⟨(fun z => (inv z).2), U, hUopen, hUbase, ?_, ?_, ?_⟩
  · intro z hz
    exact ((hUsub hz).1.snd).contDiffWithinAt
  · exact congrArg Prod.snd hinv0
  · intro z hz
    have heq := (hUsub hz).2
    have hp := congrArg (Prod.fst : RepairData E → QuadraticCoefficients E) heq
    change (inv z).1 = z.1 at hp
    have hc := congrArg (Prod.snd : RepairData E → E) heq
    change (inv z).1.1 (inv z).2 + (inv z).1.2 (inv z).2 (inv z).2 = z.2 at hc
    simpa only [hp] using hc

/-- A quantitative bound derived by absorbing both the linear perturbation and
the quadratic term. -/
theorem solution_norm_bound (B₀ : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (A : E →L[ℝ] E →L[ℝ] E) (c d : E) (β δ K r : ℝ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hinv : ∀ x, ‖B₀.symm x‖ ≤ β * ‖x‖)
    (hB : ‖B - B₀.toContinuousLinearMap‖ ≤ δ) (hA : ‖A‖ ≤ K)
    (hc : ‖c‖ ≤ r) (hsmall : β * (δ + K * r) ≤ 1 / 2)
    (heq : B c + A c c = d) : ‖c‖ ≤ 2 * β * ‖d‖ := by
  have hlin : ‖(B - B₀.toContinuousLinearMap) c‖ ≤ δ * ‖c‖ :=
    ((B - B₀.toContinuousLinearMap).le_opNorm c).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg c))
  have hquad : ‖A c c‖ ≤ K * r * ‖c‖ :=
    (A.le_opNorm₂ c c).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hA hc (norm_nonneg c) hK) (norm_nonneg c))
  have hrem : ‖(B - B₀.toContinuousLinearMap) c + A c c‖ ≤ (δ + K * r) * ‖c‖ := by
    calc
      _ ≤ ‖(B - B₀.toContinuousLinearMap) c‖ + ‖A c c‖ := norm_add_le _ _
      _ ≤ δ * ‖c‖ + K * r * ‖c‖ := add_le_add hlin hquad
      _ = _ := by ring
  have hid : B₀ c = d - ((B - B₀.toContinuousLinearMap) c + A c c) := by
    rw [← heq, sub_apply]
    change B₀ c = (B c + A c c) - (B c - B₀ c + A c c)
    abel
  have hbound : ‖c‖ ≤ β * ‖d‖ + (1 / 2 : ℝ) * ‖c‖ := by
    calc
      ‖c‖ = ‖B₀.symm (B₀ c)‖ := by rw [B₀.symm_apply_apply]
      _ ≤ β * ‖B₀ c‖ := hinv _
      _ = β * ‖d - ((B - B₀.toContinuousLinearMap) c + A c c)‖ := by rw [hid]
      _ ≤ β * (‖d‖ + ‖(B - B₀.toContinuousLinearMap) c + A c c‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hβ
      _ ≤ β * (‖d‖ + (δ + K * r) * ‖c‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hrem _) hβ
      _ = β * ‖d‖ + (β * (δ + K * r)) * ‖c‖ := by ring
      _ ≤ β * ‖d‖ + (1 / 2 : ℝ) * ‖c‖ :=
        add_le_add_right (mul_le_mul_of_nonneg_right hsmall (norm_nonneg c)) _
  linarith

/-- The analytic solver has a uniform linear-in-debt bound on one common open neighborhood. -/
theorem exists_local_bounded_analytic_solver [CompleteSpace E]
    (B₀ : E ≃L[ℝ] E) (A₀ : E →L[ℝ] E →L[ℝ] E) :
    ∃ (g : RepairData E → E) (U : Set (RepairData E)) (C : ℝ),
      IsOpen U ∧ base B₀ A₀ ∈ U ∧ 0 < C ∧ ContDiffOn ℝ ⊤ g U ∧
      g (base B₀ A₀) = 0 ∧ ∀ z ∈ U,
        z.1.1 (g z) + z.1.2 (g z) (g z) = z.2 ∧ ‖g z‖ ≤ C * ‖z.2‖ := by
  obtain ⟨g, U, hUopen, hUbase, hg, hgbase, hgeq⟩ := exists_local_analytic_solver B₀ A₀
  let β : ℝ := ‖B₀.symm.toContinuousLinearMap‖ + 1
  let K : ℝ := ‖A₀‖ + 1
  let δ : ℝ := 1 / (4 * β)
  let r : ℝ := 1 / (4 * β * K)
  have hβ : 0 < β := by change 0 < ‖B₀.symm.toContinuousLinearMap‖ + 1; positivity
  have hK : 0 < K := by change 0 < ‖A₀‖ + 1; positivity
  have hδ : 0 < δ := by change 0 < 1 / (4 * β); positivity
  have hr : 0 < r := by change 0 < 1 / (4 * β * K); positivity
  have hsmall : β * (δ + K * r) ≤ 1 / 2 := by
    change β * (1 / (4 * β) + K * (1 / (4 * β * K))) ≤ 1 / 2
    apply le_of_eq
    field_simp; ring
  have hgin : ContinuousAt g (base B₀ A₀) :=
    hg.continuousOn.continuousAt (hUopen.mem_nhds hUbase)
  have hgsmall : ∀ᶠ z in 𝓝 (base B₀ A₀), ‖g z‖ < r :=
    hgin.norm.eventually (eventually_lt_nhds (by simpa only [hgbase, norm_zero] using hr))
  have hBcont : ContinuousAt
      (fun z : RepairData E => ‖z.1.1 - B₀.toContinuousLinearMap‖) (base B₀ A₀) :=
    ((continuous_fst.fst.sub continuous_const).norm).continuousAt
  have hBsmall : ∀ᶠ z in 𝓝 (base B₀ A₀), ‖z.1.1 - B₀.toContinuousLinearMap‖ < δ :=
    hBcont.eventually (eventually_lt_nhds (by simpa [base] using hδ))
  have hAproj : Continuous (fun z : RepairData E => z.1.2) :=
    (continuous_snd : Continuous (Prod.snd : QuadraticCoefficients E → (E →L[ℝ] E →L[ℝ] E))).comp
      (continuous_fst : Continuous (Prod.fst : RepairData E → QuadraticCoefficients E))
  have hAnorm : Continuous (norm : (E →L[ℝ] E →L[ℝ] E) → ℝ) :=
    continuous_norm (E := E →L[ℝ] E →L[ℝ] E)
  have hAcont : ContinuousAt (fun z : RepairData E => ‖z.1.2‖) (base B₀ A₀) :=
    (hAnorm.comp hAproj).continuousAt
  have hAsmall : ∀ᶠ z in 𝓝 (base B₀ A₀), ‖z.1.2‖ < K :=
    hAcont.eventually (eventually_lt_nhds (by change ‖A₀‖ < ‖A₀‖ + 1; linarith))
  have hall : ∀ᶠ z in 𝓝 (base B₀ A₀), z ∈ U ∧
      ‖z.1.1 - B₀.toContinuousLinearMap‖ < δ ∧ ‖z.1.2‖ < K ∧ ‖g z‖ < r := by
    filter_upwards [hUopen.mem_nhds hUbase, hBsmall, hAsmall, hgsmall] with z hz hB hA hgz
    exact ⟨hz, hB, hA, hgz⟩
  obtain ⟨V, hVsub, hVopen, hVbase⟩ := mem_nhds_iff.mp hall
  refine ⟨g, V, 2 * β, hVopen, hVbase, by positivity,
    hg.mono (fun z hz => (hVsub hz).1), hgbase, ?_⟩
  intro z hz
  have hs := hVsub hz
  refine ⟨hgeq z hs.1, ?_⟩
  apply solution_norm_bound B₀ z.1.1 z.1.2 (g z) z.2 β δ K r hβ.le hK.le
  · intro x
    apply (B₀.symm.toContinuousLinearMap.le_opNorm x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    change ‖B₀.symm.toContinuousLinearMap‖ ≤ ‖B₀.symm.toContinuousLinearMap‖ + 1
    linarith
  · exact hs.2.1.le
  · exact hs.2.2.1.le
  · exact hs.2.2.2.le
  · exact hsmall
  · exact hgeq z hs.1

/-- Smooth coefficient and debt families produce a genuinely smooth exact small branch. -/
theorem exists_smooth_parameter_branch [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (p₀ : P) (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E) (d : P → E)
    (hB : ContDiff ℝ ∞ B) (hA : ContDiff ℝ ∞ A) (hd : ContDiff ℝ ∞ d)
    (B₀ : E ≃L[ℝ] E) (hB₀ : B p₀ = B₀.toContinuousLinearMap) (hd₀ : d p₀ = 0) :
    ∃ (c : P → E) (U : Set P) (C : ℝ), IsOpen U ∧ p₀ ∈ U ∧ 0 < C ∧
      ContDiffOn ℝ ∞ c U ∧ c p₀ = 0 ∧
      ∀ p ∈ U, B p (c p) + A p (c p) (c p) = d p ∧ ‖c p‖ ≤ C * ‖d p‖ := by
  obtain ⟨g, V, C, hVopen, hVbase, hC, hg, hgbase, hgeq⟩ :=
    exists_local_bounded_analytic_solver B₀ (A p₀)
  let data : P → RepairData E := fun p => ((B p, A p), d p)
  have hdata : ContDiff ℝ ∞ data := (hB.prodMk hA).prodMk hd
  have hbase : data p₀ = base B₀ (A p₀) := by simp [data, base, hB₀, hd₀]
  refine ⟨g ∘ data, data ⁻¹' V, C, hVopen.preimage hdata.continuous, ?_, hC, ?_, ?_, ?_⟩
  · change data p₀ ∈ V
    rwa [hbase]
  · exact (hg.of_le le_top).comp hdata.contDiffOn (fun p hp => hp)
  · change g (data p₀) = 0
    rw [hbase, hgbase]
  · intro p hp
    exact hgeq (data p) hp

/-- The quadratic growth constant is the actual norm of the bilinear coefficient. -/
theorem quadratic_norm_le (A : E →L[ℝ] E →L[ℝ] E) (c : E) :
    ‖A c c‖ ≤ ‖A‖ * ‖c‖ ^ 2 := by
  calc
    _ ≤ ‖A‖ * ‖c‖ * ‖c‖ := A.le_opNorm₂ c c
    _ = _ := by ring

/-- The two-point quadratic estimate follows from bilinearity. -/
theorem quadratic_sub_le (A : E →L[ℝ] E →L[ℝ] E) (c e : E) :
    ‖A c c - A e e‖ ≤ ‖A‖ * (‖c‖ + ‖e‖) * ‖c - e‖ := by
  have hid : A c c - A e e = A (c - e) c + A e (c - e) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hid]
  calc
    _ ≤ ‖A (c - e) c‖ + ‖A e (c - e)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖c - e‖ * ‖c‖ + ‖A‖ * ‖e‖ * ‖c - e‖ :=
      add_le_add (A.le_opNorm₂ (c - e) c) (A.le_opNorm₂ e (c - e))
    _ = _ := by ring

/-- The existing contraction theorem gives uniqueness in the quantitative
correction ball, with all quadratic estimates proved from the supplied coefficients. -/
theorem exists_unique_quadratic_correction [CompleteSpace E]
    (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (d : E) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : 4 * ‖B.symm.toContinuousLinearMap‖ * ‖A‖ * r ≤ 1)
    (hd : 2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖ ≤ r) :
    ∃! c : E, ‖c‖ ≤ r ∧ B c + A c c = d := by
  apply MomentRepair.exists_unique_small_correction B (fun c => A c c) d
    ‖B.symm.toContinuousLinearMap‖ ‖A‖ r
    (norm_nonneg B.symm.toContinuousLinearMap) (norm_nonneg A) hr
  · exact fun x => B.symm.toContinuousLinearMap.le_opNorm x
  · exact fun c _ => quadratic_norm_le A c
  · exact fun c _ e _ => quadratic_sub_le A c e
  · exact hsmall
  · exact hd

/-- Compactness supplies genuine uniform bounds on the inverse linear part and
the quadratic coefficient; these bounds are not additional hypotheses. -/
theorem compact_inverse_quadratic_bounds [CompleteSpace E]
    {P : Type*} [TopologicalSpace P] (S : Set P) (hS : IsCompact S)
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E)
    (hB : ContinuousOn B S) (hA : ContinuousOn A S)
    (hinv : ∀ p ∈ S, (B p).IsInvertible) :
    ∃ β K : ℝ, 0 < β ∧ 0 < K ∧
      ∀ p ∈ S, ‖(B p).inverse‖ ≤ β ∧ ‖A p‖ ≤ K := by
  have hcontinuous : ContinuousOn (fun p => (B p).inverse) S := by
    intro p hp
    have hi : ContinuousAt
        (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) (B p) :=
      ((hinv p hp).contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)).continuousAt
    exact hi.comp_continuousWithinAt (hB p hp)
  obtain ⟨β₀, hβ₀⟩ := hS.exists_bound_of_continuousOn hcontinuous
  obtain ⟨K₀, hK₀⟩ := hS.exists_bound_of_continuousOn (E := E →L[ℝ] E →L[ℝ] E) (f := A) hA
  refine ⟨max β₀ 1, max K₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp
  exact ⟨(hβ₀ p hp).trans (le_max_left _ _), (hK₀ p hp).trans (le_max_left _ _)⟩

/-- A common positive discrepancy threshold and linear correction bound exist
for every continuous invertible quadratic family on a compact parameter set. -/
theorem compact_uniform_small_correction [CompleteSpace E]
    {P : Type*} [TopologicalSpace P] (S : Set P) (hS : IsCompact S)
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E)
    (hB : ContinuousOn B S) (hA : ContinuousOn A S)
    (hinv : ∀ p ∈ S, (B p).IsInvertible) :
    ∃ β ε : ℝ, 0 < β ∧ 0 < ε ∧ ∀ p ∈ S, ∀ d : E, ‖d‖ ≤ ε →
      ∃! c : E, ‖c‖ ≤ 2 * β * ‖d‖ ∧ B p c + A p c c = d := by
  obtain ⟨β, K, hβ, hK, hbound⟩ := compact_inverse_quadratic_bounds S hS B A hB hA hinv
  let r : ℝ := 1 / (4 * β * K)
  let ε : ℝ := r / (2 * β)
  have hr : 0 < r := by change 0 < 1 / (4 * β * K); positivity
  have hε : 0 < ε := by change 0 < r / (2 * β); positivity
  have hsmall : 4 * β * K * r ≤ 1 := by
    change 4 * β * K * (1 / (4 * β * K)) ≤ 1
    apply le_of_eq
    field_simp
  refine ⟨β, ε, hβ, hε, ?_⟩
  intro p hp d hd
  have hradius : 2 * β * ‖d‖ ≤ r := by
    calc
      _ ≤ 2 * β * ε := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = r := by change 2 * β * (r / (2 * β)) = r; field_simp
  have hsmall' : 4 * β * K * (2 * β * ‖d‖) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hradius (by positivity)).trans hsmall
  obtain ⟨e, he⟩ := hinv p hp
  have heinv : ‖e.symm.toContinuousLinearMap‖ ≤ β := by
    have h := (hbound p hp).1
    rwa [← he, ContinuousLinearMap.inverse_equiv] at h
  have hsolve : ∃! c : E, ‖c‖ ≤ 2 * β * ‖d‖ ∧ e c + A p c c = d := by
    apply MomentRepair.exists_unique_small_correction e (fun c => A p c c) d β K
      (2 * β * ‖d‖) hβ.le hK.le (by positivity)
    · intro x
      exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right heinv (norm_nonneg x))
    · intro c _
      exact (quadratic_norm_le (A p) c).trans
        (mul_le_mul_of_nonneg_right (hbound p hp).2 (sq_nonneg ‖c‖))
    · intro c _ f _
      apply (quadratic_sub_le (A p) c f).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (c - f))
      exact mul_le_mul_of_nonneg_right (hbound p hp).2
        (add_nonneg (norm_nonneg c) (norm_nonneg f))
    · exact hsmall'
    · exact le_rfl
  simpa only [← he, ContinuousLinearEquiv.coe_coe] using hsolve

end NavierStokes.SmoothMomentRepair
