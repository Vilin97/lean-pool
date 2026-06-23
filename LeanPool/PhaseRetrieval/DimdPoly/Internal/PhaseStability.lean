/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.OrthogonalCoercivity
import LeanPool.PhaseRetrieval.DimdPoly.Internal.OrthogonalReduction.OrthogonalReduction

/-! # PhaseStability -/


open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace DimdPolyLEAN

/-!
# Phase-stable polynomial recovery

This file adds the phase-optimized layer on top of the existing orthogonal
coercivity theorem.  The proof works inside the concrete polynomial subspace
of `L²(gammaD d)`, so the public statement remains about finite coefficient
arrays.
-/

/-- The Gaussian `L²` modulus defect between two finite Hermite-Fock polynomials. -/
def modulusDefect {d : Nat} (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) : ℝ :=
  Real.sqrt <| ∫ z, (‖evalPkappa kappa Q z‖ - ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d

/-- The coefficient distance after applying a chosen global phase to `Q`. -/
def phasedCoeffDistance {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa)
    (phase : ℂ) : ℝ :=
  ‖phase • Q - F‖

private theorem pkappa_ne_zero_of_norm_eq_one
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1) :
    F ≠ 0 := by
  intro hF_zero
  subst F
  have hzero : ‖(0 : Pkappa d kappa)‖ = 0 := by
    change
      Real.sqrt
          (Finset.sum (0 : Pkappa d kappa).support
            (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
    simp
  rw [hzero] at hF_norm
  norm_num at hF_norm

theorem pkappaInner_smul_left
    {d : Nat} {kappa : MultiIndex d} (c : ℂ)
    (Q F : Pkappa d kappa) :
    pkappaInner (c • Q) F = c * pkappaInner Q F := by
  by_cases hc : c = 0
  · subst c
    simp [pkappaInner]
  · unfold pkappaInner
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simp [Finsupp.smul_apply, mul_assoc]

theorem exists_phase_positivePhaseGauge
    {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧ positivePhaseGauge F (phase • Q) := by
  let β : ℂ := pkappaInner Q F
  rcases Complex.exists_norm_eq_mul_self β with ⟨phase, hphase, hphaseβ⟩
  refine ⟨phase, hphase, ?_⟩
  have hinner : pkappaInner (phase • Q) F = ((‖β‖ : ℝ) : ℂ) := by
    rw [pkappaInner_smul_left, hphaseβ]
  constructor
  · rw [hinner]
    simp
  · rw [hinner]
    simp

/-- The polynomial subspace of the concrete Gaussian `L²` space. -/
def polyL2Submodule {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Submodule ℂ (L2Tensor d) where
  carrier := Set.range (evalPkappaL2 kappa)
  zero_mem' := ⟨0, evalPkappaL2_zero hd kappa⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨F, rfl⟩
    rcases hy with ⟨G, rfl⟩
    exact ⟨F + G, evalPkappaL2_add hd kappa F G⟩
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨F, rfl⟩
    exact ⟨c • F, evalPkappaL2_smul hd kappa c F⟩

private theorem lpNorm_congr_ae {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {f g : α → E} {p : ENNReal} {μ : Measure α} (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  unfold lpNorm
  have hmeas : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g μ :=
    aestronglyMeasurable_congr hfg
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : AEStronglyMeasurable g μ := hmeas.mp hf
    simp [hf, hg, eLpNorm_congr_ae hfg]
  · have hg : ¬ AEStronglyMeasurable g μ := by
      intro hg
      exact hf (hmeas.mpr hg)
    simp [hf, hg]

private theorem gaussianL2Norm_eq_lpNorm
    {d : Nat} {α : Type*} [NormedAddCommGroup α] [MeasurableSpace α] [NormedSpace ℝ α]
    [BorelSpace α] (F : Cd d → α)
    (hF : AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem evalPkappa_lpNorm_eq_norm
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by
  calc
    lpNorm (evalPkappa kappa F) 2 (gammaD d)
        = Real.sqrt (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) :=
          (gaussianL2Norm_eq_lpNorm (evalPkappa kappa F)
            (memLp_two_evalPkappa hd kappa F).1).symm
    _ = ‖F‖ := by
          have hpow :
              (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) =
                ∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d := by
            congr 1
            ext z
            exact Real.rpow_natCast ‖evalPkappa kappa F z‖ 2
          rw [hpow, evalPkappa_total_mass hd kappa F, Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem evalPkappaL2_norm
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    ‖evalPkappaL2 kappa F‖ = ‖F‖ := by
  rw [evalPkappaL2_eq_toLp hd kappa F,
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.toReal_eLpNorm (memLp_two_evalPkappa hd kappa F).1]
  exact evalPkappa_lpNorm_eq_norm hd kappa F

theorem evalPkappaL2_sub
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F - G) = evalPkappaL2 kappa F - evalPkappaL2 kappa G := by
  rw [sub_eq_add_neg, evalPkappaL2_add hd kappa F (-G)]
  have hneg : evalPkappaL2 kappa (-G) = -evalPkappaL2 kappa G := by
    simpa using evalPkappaL2_smul hd kappa (-1 : ℂ) G
  rw [hneg]
  simp [sub_eq_add_neg]

theorem inner_evalPkappaL2_eq_star_pkappaInner
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (G F : Pkappa d kappa) :
    inner ℂ (evalPkappaL2 kappa G) (evalPkappaL2 kappa F) = star (pkappaInner G F) := by
  classical
  induction G using Finsupp.induction with
  | zero =>
      simp [evalPkappaL2_zero hd kappa, pkappaInner]
  | single_add alpha c G halpha hc hG =>
      rw [evalPkappaL2_add hd kappa (Finsupp.single alpha c : Pkappa d kappa) G,
        evalPkappaL2_single hd kappa alpha c, inner_add_left, inner_smul_left, hG]
      have hcoeff := finite_coeff_recovery hd kappa F alpha
      rw [← hcoeff]
      unfold pkappaInner
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index]
        · simp [coeffPkappa]
        · simp
      · intro a ha
        simp
      · intro a ha b1 b2
        ring

private theorem defect_lpNorm_eq
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    defect F G =
      lpNorm (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
        2 (gammaD d) := by
  have hmeas :
      AEStronglyMeasurable
        (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
        (gammaD d) :=
      (((continuous_evalPkappa kappa (F + G)).norm).sub
        ((continuous_evalPkappa kappa F).norm)).stronglyMeasurable.aestronglyMeasurable
  simpa [defect, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm
      (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
      hmeas

private theorem defect_lpNorm_evalPkappaL2_eq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    defect F G =
      lpNorm
        (fun z : Cd d =>
          ‖(evalPkappaL2 kappa (G + F) : L2Tensor d) z‖ -
            ‖(evalPkappaL2 kappa F : L2Tensor d) z‖)
        2 (gammaD d) := by
  rw [defect_lpNorm_eq kappa F G]
  refine lpNorm_congr_ae ?_
  have hGF :=
    (memLp_two_evalPkappa hd kappa (G + F)).coeFn_toLp
  have hF :=
    (memLp_two_evalPkappa hd kappa F).coeFn_toLp
  filter_upwards [hGF, hF] with z hGFz hFz
  rw [evalPkappaL2_eq_toLp hd kappa (G + F),
    evalPkappaL2_eq_toLp hd kappa F]
  rw [hGFz, hFz, add_comm G F]

private theorem phase_alignment
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (f0 u : H)
    (hf0 : ‖f0‖ = 1) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      let h := phase • (f0 + u) - f0
      (inner ℂ h f0).im = 0 ∧ ‖h‖ ≤ ‖u‖ := by
  let a : ℂ := inner ℂ f0 u
  let g : H := u - a • f0
  let β : ℂ := 1 + a
  have hf0_inner : inner ℂ f0 f0 = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hf0]
    simp
  have hg_left : inner ℂ f0 g = 0 := by
    dsimp [g, a]
    rw [inner_sub_right, inner_smul_right, hf0_inner]
    simp
  have hg_right : inner ℂ g f0 = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ) (x := g) (y := f0)).2 hg_left
  have hu_decomp : u = a • f0 + g := by
    dsimp [g]
    abel_nf
  rcases Complex.exists_norm_eq_mul_self β with ⟨phase, hphase, hphaseβ⟩
  refine ⟨phase, hphase, ?_⟩
  dsimp
  have hh_decomp :
      phase • (f0 + u) - f0 = ((phase * β - 1 : ℂ) • f0) + phase • g := by
    rw [hu_decomp, sub_eq_add_neg]
    calc
      phase • (f0 + (a • f0 + g)) + -f0
          = phase • ((1 + a) • f0 + g) + (-1 : ℂ) • f0 := by simp [add_smul, add_assoc]
      _ = (phase * β) • f0 + phase • g + (-1 : ℂ) • f0 := by simp [β, smul_add, mul_smul]
      _ = (phase * β) • f0 + (-1 : ℂ) • f0 + phase • g := by abel_nf
      _ = ((phase * β - 1 : ℂ) • f0) + phase • g := by
            rw [← add_smul]
            congr 1
  have h_inner_real :
      inner ℂ (phase • (f0 + u) - f0) f0 = ((‖β‖ - 1 : ℝ) : ℂ) := by
    rw [hh_decomp, inner_add_left, inner_smul_left, inner_smul_left, hg_right, mul_zero,
      add_zero, hf0_inner]
    have hstar : (starRingEnd ℂ) (phase * β - 1) = ((‖β‖ - 1 : ℝ) : ℂ) := by
      rw [map_sub, ← hphaseβ]
      simp
    simp [hstar]
  have himag : (inner ℂ (phase • (f0 + u) - f0) f0).im = 0 := by
    rw [h_inner_real]
    simp
  have hu_orth : inner ℂ (a • f0) g = 0 := by
    rw [inner_smul_left, hg_left]
    simp
  have hh_orth : inner ℂ (((phase * β - 1 : ℂ) • f0)) (phase • g) = 0 := by
    rw [inner_smul_left, inner_smul_right, hg_left]
    simp
  have hu_sq :
      ‖u‖ * ‖u‖ = ‖a • f0‖ * ‖a • f0‖ + ‖g‖ * ‖g‖ := by
    simpa [hu_decomp] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • f0) g hu_orth
  have hh_sq :
      ‖phase • (f0 + u) - f0‖ * ‖phase • (f0 + u) - f0‖
        = ‖((phase * β - 1 : ℂ) • f0)‖ * ‖((phase * β - 1 : ℂ) • f0)‖ +
          ‖phase • g‖ * ‖phase • g‖ := by
    rw [hh_decomp]
    simpa using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (((phase * β - 1 : ℂ) • f0)) (phase • g) hh_orth
  have hcoef : ‖(phase * β - 1 : ℂ)‖ ≤ ‖a‖ := by
    rw [← hphaseβ]
    have hreal : ((↑‖β‖ : ℂ) - 1) = (((‖β‖ - 1 : ℝ) : ℂ)) := by simp
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    simpa [β] using abs_norm_sub_norm_le β (1 : ℂ)
  have hcomp : ‖((phase * β - 1 : ℂ) • f0)‖ ≤ ‖a • f0‖ := by
    rw [norm_smul, norm_smul]
    simpa [hf0] using hcoef
  have hphase_g : ‖phase • g‖ = ‖g‖ := by rw [norm_smul, hphase, one_mul]
  have hnorm_sq_le :
      ‖phase • (f0 + u) - f0‖ * ‖phase • (f0 + u) - f0‖ ≤ ‖u‖ * ‖u‖ := by
    rw [hh_sq, hu_sq, hphase_g]
    have hcomp_sq :
        ‖((phase * β - 1 : ℂ) • f0)‖ * ‖((phase * β - 1 : ℂ) • f0)‖
          ≤ ‖a • f0‖ * ‖a • f0‖ := by
      nlinarith [hcomp, norm_nonneg (((phase * β - 1 : ℂ) • f0)),
        norm_nonneg (a • f0)]
    linarith
  constructor
  · exact himag
  · nlinarith [hnorm_sq_le, norm_nonneg (phase • (f0 + u) - f0), norm_nonneg u]

/--
Local stability after only fixing the real phase gauge.

This is the direct no-orthogonality consequence of `OrthogonalCoercivity`: small
perturbations whose phase has been normalized are controlled by the measured
modulus defect.
-/
theorem realGaugeLocalStability
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ H : Pkappa d kappa,
        ‖H‖ ≤ δ →
          (pkappaInner H F).im = 0 →
            ‖H‖ ≤ Mloc * defect F H := by
  have hF_ne : F ≠ 0 := pkappa_ne_zero_of_norm_eq_one hF_norm
  let S : Submodule ℂ (L2Tensor d) := polyL2Submodule hd kappa
  let f0 : S := ⟨evalPkappaL2 kappa F, ⟨F, rfl⟩⟩
  have hf0 : ‖Submodule.subtypeₗᵢ S f0‖ = 1 := by
    simpa [f0, evalPkappaL2_norm hd kappa F] using hF_norm
  rcases orthogonal_coercivity (kappa := kappa) hd F hF_ne hF_norm with
    ⟨Cperp, hCperp_pos, hCperp⟩
  have hM :
      ∀ g : S, inner ℂ g f0 = 0 →
        ‖g‖ ≤ Cperp *
          lpNorm
            (fun z : Cd d =>
              ‖(Submodule.subtypeₗᵢ S (g + f0) : L2Tensor d) z‖ -
                ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
            2 (gammaD d) := by
    intro g hg
    rcases g.2 with ⟨G, hG⟩
    have hinner_val :
        inner ℂ (evalPkappaL2 kappa G) (evalPkappaL2 kappa F) = 0 := by
      change inner ℂ (g : L2Tensor d) (f0 : L2Tensor d) = 0 at hg
      simpa [f0, hG] using hg
    have horth : orthogonalToPk F G := by
      dsimp [orthogonalToPk]
      have hstar_zero : star (pkappaInner G F) = 0 := by
        simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa G F] using hinner_val
      have hzero := congrArg star hstar_zero
      simpa using hzero
    have hnorm_g : ‖g‖ = ‖G‖ := by
      change ‖(g : L2Tensor d)‖ = ‖G‖
      rw [← hG, evalPkappaL2_norm hd kappa G]
    have hdef := defect_lpNorm_evalPkappaL2_eq hd kappa F G
    calc
      ‖g‖ = ‖G‖ := hnorm_g
      _ ≤ Cperp * defect F G := hCperp G horth
      _ = Cperp *
          lpNorm
            (fun z : Cd d =>
              ‖(Submodule.subtypeₗᵢ S (g + f0) : L2Tensor d) z‖ -
                ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
            2 (gammaD d) := by
            rw [hdef]
            congr 1
            apply lpNorm_congr_ae
            filter_upwards with z
            simp [S, f0, hG, evalPkappaL2_add hd kappa G F]
  rcases OrthogonalReduction.local_stability
      (μ := gammaD d) (ι := Submodule.subtypeₗᵢ S) f0 hf0
      Cperp hCperp_pos hM with
    ⟨δ, hδ_pos, Mloc, hMloc_pos, hlocal⟩
  refine ⟨δ, Mloc, hδ_pos, hMloc_pos, ?_⟩
  intro H hHδ hH_gauge
  let h : S := ⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩
  have hnorm_h : ‖h‖ ≤ δ := by
    have hnorm : ‖h‖ = ‖H‖ := by
      change ‖(h : L2Tensor d)‖ = ‖H‖
      simp [h, evalPkappaL2_norm hd kappa H]
    linarith
  have him_h : (inner ℂ h f0).im = 0 := by
    have hstar_im : (star (pkappaInner H F)).im = 0 := by
      rw [show star (pkappaInner H F) = (starRingEnd ℂ) (pkappaInner H F) from rfl,
        Complex.conj_im, hH_gauge, neg_zero]
    change (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0
    simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa H F] using hstar_im
  have hlocal_h := hlocal h hnorm_h him_h
  have hnorm_h_eq : ‖h‖ = ‖H‖ := by
    change ‖(h : L2Tensor d)‖ = ‖H‖
    simp [h, evalPkappaL2_norm hd kappa H]
  have hdef := defect_lpNorm_evalPkappaL2_eq hd kappa F H
  calc
    ‖H‖ = ‖h‖ := hnorm_h_eq.symm
    _ ≤ Mloc *
        lpNorm
          (fun z : Cd d =>
            ‖(Submodule.subtypeₗᵢ S (h + f0) : L2Tensor d) z‖ -
              ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
          2 (gammaD d) := hlocal_h
    _ = Mloc * defect F H := by
          rw [hdef]
          congr 1
          apply lpNorm_congr_ae
          filter_upwards with z
          simp [S, f0, h, evalPkappaL2_add hd kappa H F]

private theorem defect_phase_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    defect F (phase • Q - F) = modulusDefect kappa F Q := by
  unfold defect modulusDefect
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have heval : evalPkappa kappa (F + (phase • Q - F)) z = phase * evalPkappa kappa Q z := by
    have h1 := congrFun (evalPkappa_smul hd kappa phase Q) z
    have h2 := congrFun (evalPkappa_add hd kappa F (phase • Q - F)) z
    have h3 := congrFun (evalPkappa_sub hd kappa (phase • Q) F) z
    rw [h2, h3, h1]
    ring
  rw [heval, norm_mul, hphase, one_mul]

/-- Rewriting the perturbation defect as the two-signal modulus defect. -/
theorem defect_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) :
    defect F (Q - F) = modulusDefect kappa F Q := by
  have h :=
    defect_phase_sub_eq_modulusDefect (d := d) hd kappa F Q (phase := 1) (by simp)
  simpa using h

theorem modulusDefect_phase_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    modulusDefect kappa F (phase • Q) = modulusDefect kappa F Q := by
  rw [← defect_sub_eq_modulusDefect hd kappa F (phase • Q),
    defect_phase_sub_eq_modulusDefect hd kappa F Q hphase]

/--
Global stable recovery after fixing the positive phase gauge.

Once `Q` has been rotated so that its coefficient in the `F` direction is a
nonnegative real, no smallness hypothesis is needed: the coefficient error is
controlled by the measured modulus defect.
-/
theorem positiveGaugeStability
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Pkappa d kappa,
        positivePhaseGauge F Q ->
          ‖Q - F‖ ≤ C_F * modulusDefect kappa F Q := by
  have hF_ne : F ≠ 0 := pkappa_ne_zero_of_norm_eq_one hF_norm
  obtain ⟨C_F, hC_F_pos, hstable⟩ :=
    positiveGauge_coercivity hd kappa F hF_ne hF_norm
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q hposQ
  let G : Pkappa d kappa := Q - F
  have hposG : positivePhaseGauge F (F + G) := by
    simpa [G, add_comm, add_left_comm, add_assoc] using hposQ
  have hbound := hstable G hposG
  simpa [G, defect_sub_eq_modulusDefect hd kappa F Q] using hbound

/--
Global phase-optimized stability for finite Hermite-Fock polynomials.

For every finite signal `Q`, one can choose a unit global phase so that the
phase-corrected coefficient distance to the normalized base point `F` is
controlled by the measured modulus defect.  There is no local `δ` hypothesis.
-/
theorem phaseStability
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Pkappa d kappa,
        ∃ phase : ℂ, ‖phase‖ = 1 ∧
          phasedCoeffDistance F Q phase ≤ C_F * modulusDefect kappa F Q := by
  obtain ⟨C_F, hC_F_pos, hstable⟩ := positiveGaugeStability hd kappa F hF_norm
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  obtain ⟨phase, hphase, hpos⟩ := exists_phase_positivePhaseGauge F Q
  refine ⟨phase, hphase, ?_⟩
  have hbound := hstable (phase • Q) hpos
  simpa [phasedCoeffDistance, modulusDefect_phase_smul hd kappa F Q hphase] using hbound

/--
Local phase-optimized stability for finite Hermite-Fock polynomials.

Near a normalized nonzero base point `F`, every nearby finite polynomial `Q`
has a global phase making its coefficients close to those of `F`, with the
distance controlled by the measured modulus defect.
-/
theorem localPhaseStability
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ Q : Pkappa d kappa,
        ‖Q - F‖ ≤ δ →
          ∃ phase : ℂ, ‖phase‖ = 1 ∧
            phasedCoeffDistance F Q phase ≤ Mloc * modulusDefect kappa F Q := by
  rcases realGaugeLocalStability hd kappa F hF_norm with
    ⟨δ, Mloc, hδ_pos, hMloc_pos, hreal⟩
  let S : Submodule ℂ (L2Tensor d) := polyL2Submodule hd kappa
  let f0 : S := ⟨evalPkappaL2 kappa F, ⟨F, rfl⟩⟩
  have hf0 : ‖f0‖ = 1 := by
    change ‖(f0 : L2Tensor d)‖ = 1
    simpa [f0, evalPkappaL2_norm hd kappa F] using hF_norm
  refine ⟨δ, Mloc, hδ_pos, hMloc_pos, ?_⟩
  intro Q hQδ
  let u : S := ⟨evalPkappaL2 kappa (Q - F), ⟨Q - F, rfl⟩⟩
  rcases phase_alignment f0 u hf0 with ⟨phase, hphase, hphase_gauge, hphase_norm⟩
  let H : Pkappa d kappa := phase • Q - F
  have hH_L2 :
      (phase • (f0 + u) - f0 : S) = ⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩ := by
    apply Subtype.ext
    dsimp [H, f0, u]
    rw [evalPkappaL2_sub hd kappa (phase • Q) F, evalPkappaL2_smul hd kappa phase Q,
      evalPkappaL2_sub hd kappa Q F]
    module
  have hH_norm_le : ‖H‖ ≤ δ := by
    have hu_norm : ‖u‖ = ‖Q - F‖ := by
      change ‖(u : L2Tensor d)‖ = ‖Q - F‖
      simp [u, evalPkappaL2_norm hd kappa (Q - F)]
    have hH_norm_eq : ‖H‖ = ‖phase • (f0 + u) - f0‖ := by
      rw [hH_L2]
      change ‖H‖ = ‖evalPkappaL2 kappa H‖
      rw [evalPkappaL2_norm hd kappa H]
    calc
      ‖H‖ = ‖phase • (f0 + u) - f0‖ := hH_norm_eq
      _ ≤ ‖u‖ := hphase_norm
      _ = ‖Q - F‖ := hu_norm
      _ ≤ δ := hQδ
  have hH_gauge : (pkappaInner H F).im = 0 := by
    have hinner : (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0 := by
      have hphase_gauge' :
          (inner ℂ (⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩ : S) f0).im = 0 := by
        simpa only [← hH_L2] using hphase_gauge
      change (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0 at hphase_gauge'
      exact hphase_gauge'
    have hstar_im : (star (pkappaInner H F)).im = 0 := by
      simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa H F] using hinner
    have hconj := hstar_im
    rw [show star (pkappaInner H F) = (starRingEnd ℂ) (pkappaInner H F) from rfl,
      Complex.conj_im] at hconj
    rw [neg_eq_zero] at hconj
    exact hconj
  refine ⟨phase, hphase, ?_⟩
  calc
    phasedCoeffDistance F Q phase = ‖H‖ := rfl
    _ ≤ Mloc * defect F H := hreal H hH_norm_le hH_gauge
    _ = Mloc * modulusDefect kappa F Q := by
          rw [defect_phase_sub_eq_modulusDefect hd kappa F Q hphase]

end DimdPolyLEAN
