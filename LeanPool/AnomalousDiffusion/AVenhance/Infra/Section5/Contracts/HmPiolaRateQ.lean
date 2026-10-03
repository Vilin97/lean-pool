/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmPiolaRateCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourceRatesGradient

/-! # `L²` rate of the Hessian/gradient majorant `hmPiolaQ`

The pointwise bound of `HmPiolaRateCalculus` reduces the Piola source rate to the
spacetime `L²` norm of `hmPiolaQ`, a combination of `|∇T|` and the two first-order
Hessian rows of the terminal iterate.  This file reproduces, for that majorant, the
`L²` accounting that `hm_Gbar_gradient_rate_onA7` performs for the entries of `∇GDot`
(whose private intermediate estimates are not exported), together with the active
flow bounds from the stream-function estimates. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration
open AVenhance.Infra.Section4
open AVenhance.Infra.Section5.RelativeError

theorem HmPiolaRateQ.hmPiola_sqrt_vecNormSq_le_abs_coordinates (v : Vec 2) :
    Real.sqrt (vecNormSq v) ≤ |v 0| + |v 1| := by
  have hsum : vecNormSq v ≤ (|v 0| + |v 1|) ^ 2 := by
    unfold vecNormSq vecDot
    simp only [Fin.sum_univ_two]
    calc
      v 0 * v 0 + v 1 * v 1 = v 0 ^ 2 + v 1 ^ 2 := by ring
      _ = |v 0| ^ 2 + |v 1| ^ 2 := by rw [sq_abs, sq_abs]
      _ ≤ (|v 0| + |v 1|) ^ 2 := by
        nlinarith [mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]
  calc
    Real.sqrt (vecNormSq v) ≤ Real.sqrt ((|v 0| + |v 1|) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = |v 0| + |v 1| := Real.sqrt_sq (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The Euclidean magnitude of a spatial gradient has the `L²` bound supplied
by its vector energy. The two coordinate estimates are summed without
changing the normalized space-time measure. -/
theorem HmPiolaRateQ.hmPiola_iterate_gradient_magnitude_eLpNorm_le
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) {B : ℝ} (hB : 0 ≤ B)
    (hBenergy : Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (u t)))) ≤ B) :
    eLpNorm (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq
      (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) 2
      (volume.restrict timeCube) ≤ ENNReal.ofReal (2 * B) := by
  let g : ℝ × Vec 2 → Vec 2 := fun z =>
    spaceGrad (iterateSpatialWord w (u z.1)) z.2
  let μ : Measure (ℝ × Vec 2) := volume.restrict timeCube
  have hgCont : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    dsimp [g]
    exact (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  have hset : MeasurableSet
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    measurableSet_Ici.prod MeasurableSet.univ
  have hsubset : timeCube ⊆ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
    intro z hz
    exact ⟨hz.1.1.le, Set.mem_univ _⟩
  have hac : μ ≪ volume.restrict (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    (Measure.restrict_mono_set volume hsubset).absolutelyContinuous
  have hcoordCont (j : Fin 2) :
      ContinuousOn (fun z => g z j) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (continuous_apply j).comp_continuousOn hgCont
  have hcoordMeas (j : Fin 2) : AEStronglyMeasurable (fun z => g z j) μ :=
    ((hcoordCont j).aestronglyMeasurable hset (μ := volume)).mono_ac hac
  have hrootCont : ContinuousOn (fun z => Real.sqrt (vecNormSq (g z)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hnormsq : ContinuousOn (fun z => vecNormSq (g z))
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
      unfold vecNormSq vecDot
      exact continuousOn_finsetSum Finset.univ (fun i _ =>
        ((continuous_apply i).comp_continuousOn hgCont).mul
          ((continuous_apply i).comp_continuousOn hgCont))
    exact Real.continuous_sqrt.continuousOn.comp hnormsq
      (fun _ _ => vecNormSq_nonneg _)
  have hrootMeas : AEStronglyMeasurable
      (fun z => Real.sqrt (vecNormSq (g z))) μ :=
    (hrootCont.aestronglyMeasurable hset (μ := volume)).mono_ac hac
  have hint : Integrable (fun z => vecNormSq (g z)) μ := by
    change IntegrableOn (fun z : ℝ × Vec 2 =>
      vecNormSq (spaceGrad (iterateSpatialWord w (u z.1)) z.2)) timeCube
    exact iterate_word_gradient_energy_integrable hu w
  have henergy : (∫ z, vecNormSq (g z) ∂μ) ≤ B ^ 2 := by
    have henergyRoot : Real.sqrt (∫ z, vecNormSq (g z) ∂μ) ≤ B := by
      simpa [μ, spaceTimeGradNormSq, g] using hBenergy
    have hintNonneg : 0 ≤ ∫ z, vecNormSq (g z) ∂μ :=
      integral_nonneg (fun z => vecNormSq_nonneg (g z))
    calc
      _ = (Real.sqrt (∫ z, vecNormSq (g z) ∂μ)) ^ 2 :=
        (Real.sq_sqrt hintNonneg).symm
      _ ≤ B ^ 2 := by
        let s := Real.sqrt (∫ z, vecNormSq (g z) ∂μ)
        have hs : 0 ≤ s := by dsimp [s]; positivity
        have hprod : 0 ≤ (B - s) * (B + s) :=
          mul_nonneg (sub_nonneg.mpr (show s ≤ B by exact henergyRoot))
            (add_nonneg hB hs)
        dsimp [s] at hprod
        nlinarith
  have hcoordBound (j : Fin 2) :
      eLpNorm (fun z => g z j) 2 μ ≤ ENNReal.ofReal B := by
    exact amnr_coordinate_eLpNorm_two_le_of_dissipation j
      (hcoordMeas j) hint hB henergy
  have hpoint (z : ℝ × Vec 2) :
      ‖Real.sqrt (vecNormSq (g z))‖ ≤ ‖|g z 0| + |g z 1|‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact HmPiolaRateQ.hmPiola_sqrt_vecNormSq_le_abs_coordinates (g z)
  have hmono := eLpNorm_mono_ae hrootMeas
    (Filter.Eventually.of_forall hpoint) (p := 2)
  have hnorm0 : eLpNorm (fun z => |g z 0|) 2 μ = eLpNorm (fun z => g z 0) 2 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun z => g z 0) (hcoordMeas 0)
  have hnorm1 : eLpNorm (fun z => |g z 1|) 2 μ = eLpNorm (fun z => g z 1) 2 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun z => g z 1) (hcoordMeas 1)
  have hsum :
      eLpNorm (fun z : ℝ × Vec 2 => |g z 0| + |g z 1|) 2 μ ≤
        eLpNorm (fun z => |g z 0|) 2 μ + eLpNorm (fun z => |g z 1|) 2 μ :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
  have hsumBound : eLpNorm (fun z : ℝ × Vec 2 => |g z 0| + |g z 1|) 2 μ ≤
      ENNReal.ofReal B + ENNReal.ofReal B := by
    rw [hnorm0, hnorm1] at hsum
    exact hsum.trans (add_le_add (hcoordBound 0) (hcoordBound 1))
  calc
    _ ≤ eLpNorm (fun z : ℝ × Vec 2 => |g z 0| + |g z 1|) 2 μ := hmono
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := hsumBound
    _ = ENNReal.ofReal (2 * B) := by
      calc
        _ = ENNReal.ofReal (B + B) := by rw [← ENNReal.ofReal_add hB hB]
        _ = _ := by congr 1; ring

/-- Active flow bounds (stream-function estimates) for every stream sequence: on the support of
`ξ̂_{m,l}(t)`, `F_l` and `∇Y_l` are bounded by `2` and the second flow derivative by
`2^16/ε_{m-1}`. -/
theorem hmPiola_active_flow_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    ∀ l : ℤ, I.hatXiML m l t ≠ 0 →
      (∀ x i j, |I.flowGrad hΦ m l t x i j| ≤ 2) ∧
      (∀ x i j, |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2) ∧
      (∀ x p j q, |xFlowHess I hΦ m l t x p j q| ≤
        2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) := by
  intro l hl
  have hscales := section2Scales_canonical I
  have hAppB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hjoint := section2_joint_induction_with_derived_flow hscales hAppB2
  have hreg : StreamRegularityBounds (11 + 768 / (β - 1)) I Φ :=
    stream_regularity_bounds_of_increment_bounds hΦ hjoint.2.1
  obtain ⟨Cmat, hCmat, hflow, _hmaterial⟩ := hjoint.2.2
  exact hm_Gbar_active_flow_bounds hΦ hflow hreg hm (t := t) l hl

private theorem hmPiolaQ_eLpNorm_rate_onA7_Qnorm1 :
  ∀ (β D : ℝ), (1 : ℝ) ≤ D →
  let F : ℝ := (↑(Nstar β) : ℝ) * (↑((2 : ℕ) * Nstar β).factorial : ℝ);
  let Czero : ℝ := (2 : ℝ) * ((1 : ℝ) + F / (4 : ℝ));
  let Cword : ℝ := (2 : ℝ) * (4 : ℝ) ^ Nstar β * (↑((2 : ℕ) * Nstar β).factorial : ℝ) * ((4 : ℝ)
    * D ^ (3 : ℕ));
  ∀ (I : Ingredients β) (κ : ℝ) (M : ℕ) (θ₀ : Vec (2 : ℕ) → ℝ) (m : ℕ) (T : ℕ → ℝ → Vec (2 : ℕ)
    → ℝ), (0 : ℝ) < epsilon β I.Λ (m - (1 : ℕ)) → (0 : ℝ) < I.kappaSeq κ M (m - (1 : ℕ)) →
  let q : ℝ := (-1 : ℝ) - gamma β / (2 : ℝ);
  let invRoot : ℝ := (√(I.kappaSeq κ M (m - (1 : ℕ))))⁻¹;
  let θsize : ℝ := √(l2NormSq θ₀);
  let Bzero : ℝ := Czero * θsize * invRoot;
  let Bword : ℝ := Cword * θsize * invRoot * epsilon β I.Λ (m - (1 : ℕ)) ^ q;
  let μ : Measure (ℝ × Vec (2 : ℕ)) := volume.restrict timeCube;
  let Tn : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let r0 : ℝ × Vec (2 : ℕ) → ℝ := fun (z : ℝ × Vec (2 : ℕ)) => √(vecNormSq (spaceGrad (Tn z.1)
    z.2));
  let r1 : ℝ × Vec (2 : ℕ) → ℝ := fun (z : ℝ × Vec (2 : ℕ)) => √(vecNormSq (spaceGrad
    (iterateSpatialWord [(0 : Fin (2 : ℕ))] (Tn z.1)) z.2));
  let r2 : ℝ × Vec (2 : ℕ) → ℝ := fun (z : ℝ × Vec (2 : ℕ)) => √(vecNormSq (spaceGrad
    (iterateSpatialWord [(1 : Fin (2 : ℕ))] (Tn z.1)) z.2));
  eLpNorm r0 (2 : ENNReal) μ ≤ ENNReal.ofReal ((2 : ℝ) * Bzero) →
  let Q : ℝ × Vec (2 : ℕ) → ℝ := fun (z : ℝ × Vec (2 : ℕ)) => (4 : ℝ) * (r1 z + r2 z) + (2 : ℝ)
    ^ (19 : ℕ) / epsilon β I.Λ (m - (1 : ℕ)) * r0 z;
  eLpNorm (fun (z : ℝ × Vec (2 : ℕ)) => r1 z + r2 z) (2 : ENNReal) μ ≤ ENNReal.ofReal ((2 : ℝ) *
    Bword) + ENNReal.ofReal ((2 : ℝ) * Bword) → (∀ (c : ℝ), (0 : ℝ) ≤ c → ∀ (f : ℝ × Vec (2 : ℕ)
    → ℝ), eLpNorm (fun (z : ℝ × Vec (2 : ℕ)) => c * f z) (2 : ENNReal) μ = ENNReal.ofReal c *
    eLpNorm f (2 : ENNReal) μ) → eLpNorm Q (2 : ENNReal) μ ≤ ENNReal.ofReal ((16 : ℝ) * Bword +
    (2 : ℝ) ^ (20 : ℕ) / epsilon β I.Λ (m - (1 : ℕ)) * Bzero)
    := by
  intro β D hD F Czero Cword I κ M θ₀ m T hε hκprev q invRoot θsize Bzero Bword μ Tn r0 r1 r2
      hroot0 Q hsumRoots hscale
  have hsumBound : eLpNorm (fun z => r1 z + r2 z) 2 μ ≤
      ENNReal.ofReal (4 * Bword) := by
    calc
      _ ≤ ENNReal.ofReal (2 * Bword) + ENNReal.ofReal (2 * Bword) := hsumRoots
      _ = ENNReal.ofReal (4 * Bword) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * Bword)
          (by positivity : 0 ≤ 2 * Bword)]
        congr 1; ring
  have hfirst := (hscale 4 (by norm_num) (fun z => r1 z + r2 z)).symm
  have hlast := hscale (2 ^ 19 / epsilon β I.Λ (m - 1)) (by positivity) r0
  have hparts :
      eLpNorm (fun z : ℝ × Vec 2 =>
        4 * (r1 z + r2 z) + (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z) 2 μ ≤
        eLpNorm (fun z => 4 * (r1 z + r2 z)) 2 μ +
          eLpNorm (fun z => (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z) 2 μ :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
  have hfirstBound : eLpNorm (fun z : ℝ × Vec 2 => 4 * (r1 z + r2 z)) 2 μ ≤
      ENNReal.ofReal (16 * Bword) := by
    rw [← hfirst]
    calc
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (4 * Bword) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
      _ = ENNReal.ofReal (16 * Bword) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))]
        congr 1
        ring
  have hlastBound : eLpNorm (fun z : ℝ × Vec 2 =>
      (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z) 2 μ ≤
      ENNReal.ofReal ((2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) := by
    rw [hlast]
    calc
      _ ≤ ENNReal.ofReal (2 ^ 19 / epsilon β I.Λ (m - 1)) *
            ENNReal.ofReal (2 * Bzero) :=
        mul_le_mul_of_nonneg_left hroot0 (by positivity)
      _ = ENNReal.ofReal ((2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) := by
        rw [← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 2 ^ 19 / epsilon β I.Λ (m - 1))]
        congr 1
        ring
  calc
    _ = eLpNorm (fun z : ℝ × Vec 2 =>
        4 * (r1 z + r2 z) + (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z) 2 μ := by
      rfl
    _ ≤ eLpNorm (fun z : ℝ × Vec 2 => 4 * (r1 z + r2 z)) 2 μ +
          eLpNorm (fun z => (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z) 2 μ := hparts
    _ ≤ ENNReal.ofReal (16 * Bword) +
          ENNReal.ofReal ((2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) :=
      add_le_add hfirstBound hlastBound
    _ = ENNReal.ofReal (16 * Bword +
          (2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

private theorem hmPiolaQ_eLpNorm_rate_onA7_targetReal2 :
  ∀ (β D : ℝ),
  let F : ℝ := (↑(Nstar β) : ℝ) * (↑((2 : ℕ) * Nstar β).factorial : ℝ);
  let Czero : ℝ := (2 : ℝ) * ((1 : ℝ) + F / (4 : ℝ));
  let Cword : ℝ := (2 : ℝ) * (4 : ℝ) ^ Nstar β * (↑((2 : ℕ) * Nstar β).factorial : ℝ) * ((4 : ℝ)
    * D ^ (3 : ℕ));
  let Cgrad : ℝ := (16 : ℝ) * Cword + (2 : ℝ) ^ (20 : ℕ) * Czero;
  ∀ (I : Ingredients β) (κ : ℝ) (M : ℕ) (θ₀ : Vec (2 : ℕ) → ℝ) (m : ℕ), (0 : ℝ) < I.kappaSeq κ M
    (m - (1 : ℕ)) →
  let q : ℝ := (-1 : ℝ) - gamma β / (2 : ℝ);
  let invRoot : ℝ := (√(I.kappaSeq κ M (m - (1 : ℕ))))⁻¹;
  let θsize : ℝ := √(l2NormSq θ₀);
  let Bzero : ℝ := Czero * θsize * invRoot;
  let Bword : ℝ := Cword * θsize * invRoot * epsilon β I.Λ (m - (1 : ℕ)) ^ q;
  (epsilon β I.Λ (m - (1 : ℕ)))⁻¹ ≤ epsilon β I.Λ (m - (1 : ℕ)) ^ q → (16 : ℝ) * Bword + (2 : ℝ)
    ^ (20 : ℕ) / epsilon β I.Λ (m - (1 : ℕ)) * Bzero ≤ Cgrad * √(l2NormSq θ₀) * invRoot *
    epsilon β I.Λ (m - (1 : ℕ)) ^ q
    := by
  intro β D F Czero Cword Cgrad I κ M θ₀ m hκprev q invRoot θsize Bzero Bword hεinvRate
  have hX : 0 ≤ Real.sqrt (l2NormSq θ₀) * invRoot := by positivity
  have hcoeff : 16 * Cword * epsilon β I.Λ (m - 1) ^ q +
      2 ^ 20 * Czero * (epsilon β I.Λ (m - 1))⁻¹ ≤
      Cgrad * epsilon β I.Λ (m - 1) ^ q := by
    calc
      _ ≤ 16 * Cword * epsilon β I.Λ (m - 1) ^ q +
          2 ^ 20 * Czero * epsilon β I.Λ (m - 1) ^ q := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hεinvRate
          (by positivity))
      _ = Cgrad * epsilon β I.Λ (m - 1) ^ q := by dsimp [Cgrad]; ring
  dsimp [Bword, Bzero, θsize, invRoot]
  have heq :
      16 * (Cword * Real.sqrt (l2NormSq θ₀) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          epsilon β I.Λ (m - 1) ^ q) +
        (2 ^ 20 / epsilon β I.Λ (m - 1)) *
          (Czero * Real.sqrt (l2NormSq θ₀) *
            (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹) =
      (16 * Cword * epsilon β I.Λ (m - 1) ^ q +
        2 ^ 20 * Czero * (epsilon β I.Λ (m - 1))⁻¹) *
        (Real.sqrt (l2NormSq θ₀) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹) := by ring
  calc
    _ = (16 * Cword * epsilon β I.Λ (m - 1) ^ q +
        2 ^ 20 * Czero * (epsilon β I.Λ (m - 1))⁻¹) *
        (Real.sqrt (l2NormSq θ₀) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹) := heq
    _ ≤ (Cgrad * epsilon β I.Λ (m - 1) ^ q) *
        (Real.sqrt (l2NormSq θ₀) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹) :=
      mul_le_mul_of_nonneg_right hcoeff hX
    _ = Cgrad * Real.sqrt (l2NormSq θ₀) *
        (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
        epsilon β I.Λ (m - 1) ^ q := by ring

/-- The spacetime `L²` rate of the majorant `hmPiolaQ`: all thresholds and amplitudes
are chosen before the ingredients and data. -/
theorem hmPiolaQ_eLpNorm_rate_onA7 (β Ccut : ℝ) :
    ∃ C₁ Cgrad : ℝ, 0 ≤ Cgrad ∧
      OnA7Instances β Ccut C₁
        (fun I _Φ _hΦ κ M _R θ₀ m _θprev T =>
          eLpNorm (fun z : ℝ × Vec 2 =>
              hmPiolaQ (epsilon β I.Λ (m - 1)) (T (Nstar β)) z.1 z.2) 2
              (volume.restrict timeCube) ≤
            ENNReal.ofReal (Cgrad * Real.sqrt (l2NormSq θ₀) *
              (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
              epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2))) := by
  obtain ⟨D, hD, hTupgrade⟩ := iterate_T_upgrade_of_analytic β Ccut
  obtain ⟨C₁, hthreshold⟩ := iterate_contract_scales β D hD
  let F : ℝ := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)
  let Czero : ℝ := 2 * (1 + F / 4)
  let Cword : ℝ := 2 * (4 : ℝ) ^ Nstar β *
    ((2 * Nstar β).factorial : ℝ) * (4 * D ^ 3)
  let Cgrad : ℝ := 16 * Cword + 2 ^ 20 * Czero
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hCzero : 0 ≤ Czero := by dsimp [Czero]; positivity
  have hCword : 0 ≤ Cword := by dsimp [Cword]; positivity
  have hCgrad : 0 ≤ Cgrad := by dsimp [Cgrad]; positivity
  refine ⟨C₁, Cgrad, hCgrad, ?_⟩
  intro I hzeta hxi hhat hΛ Φ hΦ κ hκperm M hM hperm R hR θ₀ hθsmooth
    hθperiodic hθmean hθanalytic m hm hmM θprev T hθprev hT
  have hstart := hthreshold I hΛ R hR m hm
  have hm2 : 2 ≤ m := hstart.1
  have hε : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hε1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hpowSmall : D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 4 := by
    calc
      _ ≤ D ^ 3 * (4 * D ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hstart.2.2 (by positivity)
      _ = 1 / 4 := by field_simp [ne_of_gt (by positivity : 0 < D)]
  have hfactor :
      1 + (D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * F ≤ 1 + F / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hpowSmall hF
    dsimp [F]
    nlinarith
  have hprofile := hTupgrade I hzeta hxi hhat hΦ κ M hT hθprev hm2 hmM
    hperm R hR hstart.2.1 hstart.2.2 hθanalytic
  have hA5 := theta_A3_A5_data_of_frozen I Φ hΦ κ hM hperm
  obtain ⟨cA5, _, hcA5, _, _, hκA5⟩ := hA5
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := by
    have hεpos := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m - 1)
    have hapos := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m - 1)
    have hlower := (hκA5 (m - 1) (by omega) (by omega)).1
    have hpos : 0 < cA5 *
        (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) := by
      positivity
    exact hpos.trans_le (by simpa [Ingredients.kappaSeq] using hlower)
  have hκsqrt : 0 < Real.sqrt (I.kappaSeq κ M (m - 1)) :=
    Real.sqrt_pos.2 hκprev
  have hθnorm : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hzeroProfile' :
      Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      2 * Real.sqrt (l2NormSq θ₀) *
        (1 + (D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * F) := by
    calc
      _ = Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
          Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) := by
        simp [Ingredients.kappaSeq]
      _ ≤ 2 * Real.sqrt (l2NormSq θ₀) *
          (1 + D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
            (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)) := hprofile.1
      _ = _ := by dsimp [F]; ring
  have hzeroProfile :
      Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      Czero * Real.sqrt (l2NormSq θ₀) := by
    calc
      _ ≤ 2 * Real.sqrt (l2NormSq θ₀) *
          (1 + (D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * F) := by
        exact hzeroProfile'
      _ ≤ 2 * Real.sqrt (l2NormSq θ₀) * (1 + F / 4) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = Czero * Real.sqrt (l2NormSq θ₀) := by dsimp [Czero]; ring
  let q : ℝ := -1 - gamma β / 2
  have hwordProfile (k : Fin 2) :
      Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t =>
          spaceGrad (iterateSpatialWord [k] (T (Nstar β) t)))) ≤
        Cword * Real.sqrt (l2NormSq θ₀) *
          epsilon β I.Λ (m - 1) ^ q := by
    have hraw := hprofile.2 [k] [k] (by simp) (by simp) 0 (by norm_num) (by norm_num)
    have hdrop := (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hraw
    convert hdrop using 1
    · simp [Ingredients.kappaSeq]
    · simp [Cword, q, List.length]
      ring
  let invRoot : ℝ := (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹
  let θsize : ℝ := Real.sqrt (l2NormSq θ₀)
  let Bzero : ℝ := Czero * θsize * invRoot
  let Bword : ℝ := Cword * θsize * invRoot *
    epsilon β I.Λ (m - 1) ^ q
  have hinvRoot : 0 ≤ invRoot := by dsimp [invRoot]; positivity
  have hBzero : 0 ≤ Bzero := by dsimp [Bzero, θsize]; positivity
  have hBword : 0 ≤ Bword := by dsimp [Bword, θsize]; positivity
  have hzeroEnergy : Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤ Bzero := by
    have hmul : Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (T (Nstar β) t))) *
        Real.sqrt (I.kappaSeq κ M (m - 1)) ≤ Czero * Real.sqrt (l2NormSq θ₀) := by
      simpa [mul_comm] using hzeroProfile
    have hdiv := (le_div_iff₀ hκsqrt).2 hmul
    simpa [Bzero, invRoot, θsize, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hdiv
  have hwordEnergy (k : Fin 2) :
      Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord [k] (T (Nstar β) t)))) ≤ Bword := by
    have hmul : Real.sqrt (spaceTimeGradNormSq (fun t =>
        spaceGrad (iterateSpatialWord [k] (T (Nstar β) t)))) *
        Real.sqrt (I.kappaSeq κ M (m - 1)) ≤
        Cword * Real.sqrt (l2NormSq θ₀) * epsilon β I.Λ (m - 1) ^ q := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hwordProfile k
    have hdiv := (le_div_iff₀ hκsqrt).2 hmul
    simpa [Bword, invRoot, θsize, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hdiv
  let μ : Measure (ℝ × Vec 2) := volume.restrict timeCube
  let Tn : ℝ → Vec 2 → ℝ := T (Nstar β)
  let r0 : ℝ × Vec 2 → ℝ := fun z =>
    Real.sqrt (vecNormSq (spaceGrad (Tn z.1) z.2))
  let r1 : ℝ × Vec 2 → ℝ := fun z =>
    Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord [0] (Tn z.1)) z.2))
  let r2 : ℝ × Vec 2 → ℝ := fun z =>
    Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord [1] (Tn z.1)) z.2))
  have hTjoint := tIterate_contDiffOn_nonneg I hΦ hT hθprev (le_rfl)
  have hroot0 : eLpNorm r0 2 μ ≤ ENNReal.ofReal (2 * Bzero) := by
    simpa [r0, μ, Tn, iterateSpatialWord] using
      HmPiolaRateQ.hmPiola_iterate_gradient_magnitude_eLpNorm_le hTjoint [] hBzero hzeroEnergy
  have hroot1 : eLpNorm r1 2 μ ≤ ENNReal.ofReal (2 * Bword) := by
    simpa [r1, μ, Tn] using
      HmPiolaRateQ.hmPiola_iterate_gradient_magnitude_eLpNorm_le hTjoint [0] hBword (hwordEnergy 0)
  have hroot2 : eLpNorm r2 2 μ ≤ ENNReal.ofReal (2 * Bword) := by
    simpa [r2, μ, Tn] using
      HmPiolaRateQ.hmPiola_iterate_gradient_magnitude_eLpNorm_le hTjoint [1] hBword (hwordEnergy 1)
  have hεinvRate : (epsilon β I.Λ (m - 1))⁻¹ ≤
      epsilon β I.Λ (m - 1) ^ q := by
    have hq : q ≤ -1 := by dsimp [q]; linarith
    have hpow := Real.rpow_le_rpow_of_exponent_ge hε hε1 hq
    simpa [q, Real.rpow_neg_one] using hpow
  let Q : ℝ × Vec 2 → ℝ := fun z =>
    4 * (r1 z + r2 z) + (2 ^ 19 / epsilon β I.Λ (m - 1)) * r0 z
  have hsumRoots : eLpNorm (fun z : ℝ × Vec 2 => r1 z + r2 z) 2 μ ≤
      ENNReal.ofReal (2 * Bword) + ENNReal.ofReal (2 * Bword) := by
    exact (eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add hroot1 hroot2)
  have hscale (c : ℝ) (hc : 0 ≤ c) (f : ℝ × Vec 2 → ℝ) :
      eLpNorm (fun z => c * f z) 2 μ = ENNReal.ofReal c * eLpNorm f 2 μ := by
    have hfun : (fun z => c * f z) = c • f := by funext z; simp
    rw [hfun, eLpNorm_const_smul, Real.enorm_of_nonneg hc]
  have hQnorm : eLpNorm Q 2 μ ≤ ENNReal.ofReal
      (16 * Bword + (2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) := by
    exact @hmPiolaQ_eLpNorm_rate_onA7_Qnorm1 β D hD I κ M θ₀ m T hε hκprev hroot0 hsumRoots hscale
  have htargetReal : 16 * Bword +
      (2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero ≤
      Cgrad * Real.sqrt (l2NormSq θ₀) * invRoot *
        epsilon β I.Λ (m - 1) ^ q := by
    exact @hmPiolaQ_eLpNorm_rate_onA7_targetReal2 β D I κ M θ₀ m hκprev hεinvRate
  have hfinal : eLpNorm
      (fun z : ℝ × Vec 2 => hmPiolaQ (epsilon β I.Λ (m - 1)) Tn z.1 z.2) 2 μ ≤
      ENNReal.ofReal (Cgrad * Real.sqrt (l2NormSq θ₀) * invRoot *
        epsilon β I.Λ (m - 1) ^ q) := by
    calc
      _ = eLpNorm Q 2 μ := rfl
      _ ≤ ENNReal.ofReal
          (16 * Bword + (2 ^ 20 / epsilon β I.Λ (m - 1)) * Bzero) := hQnorm
      _ ≤ ENNReal.ofReal (Cgrad * Real.sqrt (l2NormSq θ₀) * invRoot *
          epsilon β I.Λ (m - 1) ^ q) :=
        ENNReal.ofReal_le_ofReal htargetReal
  simpa [Tn, μ, invRoot, q] using hfinal

end AVenhance.Infra.Section5.Contracts

end
