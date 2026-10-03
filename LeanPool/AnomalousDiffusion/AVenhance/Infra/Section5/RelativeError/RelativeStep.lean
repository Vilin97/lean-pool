/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeLeadingTBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeStepCoreIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmExtension
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar

/-! Conditional relative-step assembly with constants chosen before Ingredients.
The named physical leaves are ordinary hypotheses. This module never imports
Big-bound estimate or step-down estimate and does not certify their unresolved physical inputs. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration AVenhance.Infra.Section5.LeftToShow
open AVenhance.Infra.Section5.AnalyticBridge
namespace AVenhance.Infra.Section5.RelativeError

/-- Step-down conjunct (ii), conditional on the relative physical leaves.
The witness precedes I; the temperature premises contain only positive jets
and integrated gradients. The residual is assembled from all ten terms. -/
theorem relative_step (β C₀ A Ci Cr Ca Ct : ℝ) (hA : 2 ^ (14 : ℕ) ≤ A)
    (hCi : 0 ≤ Ci) (hCr : 0 ≤ Cr) (hCa : 0 ≤ Ca) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → IsZ2Periodic g → MeanZeroOn unitCube g →
        IsThetaAnalytic R g →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ (θm θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) g θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) g θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) g θprev T →
      let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x));
      let ε := epsilon β I.Λ (m - 1);
      let v := I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β));
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x)) ≤ A * S →
        Real.sqrt (spaceTimeGradNormSq (materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
          A * ε ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ * S *
            (tauP β I.Λ m)⁻¹ →
        PositiveTemperatureJets A (ε ^ (1 + gamma β / 2)) S (T (Nstar β)) →
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T Ci S →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x, sourceResidualIdentity I hΦ m
          (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T t x) →
        (∀ i, i < 10 → ContinuousOn (fun p : ℝ × Vec 2 =>
          section5Term I hΦ m (I.kappaSeq κ M m) (T (Nstar β))
            (sourceErrorD I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
            (iterateError I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T) i p.1 p.2)
          (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (fun x =>
          twistie4 I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x +
          twistie5 I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x +
          normie3 I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) →
        (∀ i, i < 10 → timeHMinusOneNorm
          (section5CenteredTerm I hΦ m (I.kappaSeq κ M m) (T (Nstar β))
            (sourceErrorD I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
            (iterateError I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T) i) ≤
          ENNReal.ofReal (Cr * Real.sqrt (I.kappaSeq κ M m) * ε ^ delta β * S)) →
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (v s) x - leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s x)) ≤
          Ca * ε ^ (2 * delta β) * S →
        Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤ Ct * ε ^ (2 * delta β) * S →
        ContinuousOn (fun p : ℝ × Vec 2 =>
          leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) p.1 p.2)
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
        ((6 : ℝ) / 5 ≤ β →
          epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        |I.kappaSeq κ M m * spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x) -
            I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)| ≤
          C * epsilon β I.Λ (m - 1) ^ delta β *
            (I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) := by
  obtain ⟨CL, hCL⟩ := relative_leading_energy_of_T_bounds β C₀ A hA
  let K := 2 * (Ci + 10 * Cr) + Ca + Ct + Real.sqrt |CL|
  let CE := K * (2 + K)
  refine ⟨max CL CE, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR g hg hgp hgm hga m hm hmM θm θprev T hu hp hTit
  dsimp only
  intro hT0 hDt hJets hInitial hResidual hContinuous hgroup hterms hLeadingError hTemperatureError
      hLead hβ hlater
  have hm2 : 2 ≤ m := by
    have hstar : 2 ≤ mTheta0 β I.Λ R := (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le
        hR).1
    omega
  have hκpos : 0 < κ := by
    have he : 0 < epsilon β I.Λ M := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le
    exact lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos he _)) (Set.mem_Icc.mp
        hperm).1
  have hκm : 0 < I.kappaSeq κ M m := kappaSeq_pos I hκpos M m
  have hν : 0 < I.kappaSeq κ M (m - 1) := kappaSeq_pos I hκpos M (m - 1)
  let ε := epsilon β I.Λ (m - 1);
  let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
    Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))
  have hε : 0 < ε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hε1 : ε ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have he : 0 ≤ ε ^ delta β := (Real.rpow_pos_of_pos hε _).le
  have he1 : ε ^ delta β ≤ 1 := Real.rpow_le_one hε.le hε1 hδ.le
  have hSsq : S ^ 2 = I.kappaSeq κ M (m - 1) *
      spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x) := by
    simp only [S, mul_pow, Real.sq_sqrt hν.le,
      Real.sq_sqrt (spaceTimeGradNormSq_nonneg' _)]
  have he2 : ε ^ (2 * delta β) = (ε ^ delta β) ^ 2 := by
    rw [mul_comm (2 : ℝ), Real.rpow_mul hε.le, Real.rpow_two]
  have hres := relative_residual_of_term_bounds I hΦ m (I.kappaSeq κ M m)
    (T (Nstar β)) (sourceErrorD I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
    (iterateError I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T)
    (streamVel (Φ m)) Cr ε (delta β) S hResidual hContinuous hgroup
    (hterms 0 (by norm_num)) (hterms 1 (by norm_num)) (hterms 2 (by norm_num))
    (hterms 3 (by norm_num)) (hterms 4 (by norm_num)) (hterms 5 (by norm_num))
    (hterms 6 (by norm_num)) (hterms 7 (by norm_num)) (hterms 8 (by norm_num)) (hterms 9 (by
        norm_num))
  have hsol := tIterates_classicalSol hTit
  have hTs : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
    fun t ht => Infra.Classical.classicalSmooth_slice_nonneg hsol.1 (t := t) ht
  -- open-time regularity of `HTilde_m` for the actual iterates (no `t = 0` premise)
  have hH : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 =>
      I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (Hm_contDiffOn_Ioi_top I hΦ (by omega) hκm hp hTit).of_le (by simp)
  have hHs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) :=
    fun t ht => Hm_slice_contDiff_pos I hΦ (by omega) hκm hp hTit ht
  have hHp : ∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) :=
    fun t ht => Hm_periodic_pos I hΦ (by omega) hκm hp hTit ht
  -- the energy estimate at `t = 1`; its gradient part is time-independent
  have herror := relative_ansatz_error I hΦ m hκm hu hsol.1 hTs hsol.2.1 hH hHs hHp
    (show 0 ≤ 10 * Cr by positivity) hε hS hInitial hres 1 ⟨zero_lt_one, le_rfl⟩
  have hans : Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (θm s) x - spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
      (2 * (Ci + 10 * Cr)) * ε ^ delta β * S := by
    exact (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans herror
  have henergy := hCL I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm
    m hm2 hmM S hS g θprev T hTit hT0 hDt hJets
  have henergy' := henergy.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self CL) (Real.rpow_nonneg hε.le _)) (sq_nonneg S))
  have hfinal := relative_step_from_errors_Ioi (2 * (Ci + 10 * Cr)) Ca Ct |CL|
    (by positivity) hCa hCt (abs_nonneg _) I hΦ m M κ θm θprev (T (Nstar β))
    hκm.le hν.le he he1 (spaceGrad_continuousOn hu.1) (ansatz_spaceGrad_extends_Ici I hΦ (by
        omega) hκm hp hTit)
    hLead (spaceGrad_continuousOn hsol.1) (spaceGrad_continuousOn hp.1)
    hans (by simpa only [← he2, ε] using hLeadingError)
    (by simpa only [← he2, ε] using hTemperatureError) (by simpa only [← he2, ε, hSsq] using
        henergy')
  apply hfinal.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right CL CE) he)
    (mul_nonneg hν.le (spaceTimeGradNormSq_nonneg' _))

end AVenhance.Infra.Section5.RelativeError
