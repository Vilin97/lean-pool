/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeNorms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Defs

/-! Relative energy comparison in the actual gradient carriers. This is a
conditional assembly helper, not a proof of the step-down estimate statement. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.LeftToShow
namespace AVenhance.Infra.Section5.RelativeError

theorem relative_step_from_errors
    (Cans Clead CT Cenergy : ℝ) (hCans : 0 ≤ Cans) (hClead : 0 ≤ Clead)
    (hCT : 0 ≤ CT) (hCenergy : 0 ≤ Cenergy)
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m M : ℕ) (κ : ℝ)
    (θm θprev T : ℝ → Vec 2 → ℝ)
    (hκm : 0 ≤ I.kappaSeq κ M m) (hν : 0 ≤ I.kappaSeq κ M (m - 1))
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1)
    (hθ : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (θm p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hAns : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) T p.1) p.2 i) 2
      (volume.restrict timeCube))
    (hLead : ContinuousOn (fun p : ℝ × Vec 2 =>
      leadingGrad I hΦ m (I.kappaSeq κ M m) T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hT : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hPrev : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (θprev p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hAnsatzError : Real.sqrt (I.kappaSeq κ M m) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x -
        spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) T s) x)) ≤
      Cans * e * (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
    (hLeadingError : Real.sqrt (I.kappaSeq κ M m) *
      Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) T s) x -
          leadingGrad I hΦ m (I.kappaSeq κ M m) T s x)) ≤
      Clead * e ^ 2 * (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
    (hTemperatureError : Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T s) x - spaceGrad (θprev s) x)) ≤
      CT * e ^ 2 * (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
    (hLeadingEnergy : |I.kappaSeq κ M m *
        spaceTimeGradNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) T) -
      I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (T s) x)| ≤
      Cenergy * e ^ 2 * (I.kappaSeq κ M (m - 1) *
        spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) :
    |I.kappaSeq κ M m * spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x) -
        I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)| ≤
      ((Cans + Clead + CT + Real.sqrt Cenergy) *
        (2 + (Cans + Clead + CT + Real.sqrt Cenergy))) * e *
        (I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)) := by
  let normG := fun (a : ℝ) (f : ℝ → Vec 2 → Vec 2) =>
    Real.sqrt a * Real.sqrt (spaceTimeGradNormSq f)
  let S := normG (I.kappaSeq κ M (m - 1)) (fun s x => spaceGrad (θprev s) x)
  let U := normG (I.kappaSeq κ M m) (fun s x => spaceGrad (θm s) x)
  let V := normG (I.kappaSeq κ M m)
    (fun s x => spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) T s) x)
  let L := normG (I.kappaSeq κ M m) (leadingGrad I hΦ m (I.kappaSeq κ M m) T)
  let Z := normG (I.kappaSeq κ M (m - 1)) (fun s x => spaceGrad (T s) x)
  have hnn (a : ℝ) (f : ℝ → Vec 2 → Vec 2) : 0 ≤ normG a f := by dsimp [normG]; positivity
  have hsq (a : ℝ) (ha : 0 ≤ a) (f : ℝ → Vec 2 → Vec 2) :
      (normG a f) ^ 2 = a * spaceTimeGradNormSq f := by
    dsimp [normG]
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt (show 0 ≤ spaceTimeGradNormSq f from
      integral_nonneg (fun _ => vecNormSq_nonneg _))]
  have hdiff (a : ℝ) (f g : ℝ → Vec 2 → Vec 2)
      (hf : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => f p.1 p.2 i) 2
        (volume.restrict timeCube))
      (hg : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => g p.1 p.2 i) 2
        (volume.restrict timeCube)) :
      |normG a f - normG a g| ≤ Real.sqrt a *
        Real.sqrt (spaceTimeGradNormSq (fun s x => f s x - g s x)) := by
    dsimp [normG]
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (relative_gradient_norm_sub_le_of_memLp hf hg)
        (Real.sqrt_nonneg _)
  have he2 : e ^ 2 ≤ e := by nlinarith only [he, he1]
  have hUV : |U - V| ≤ Cans * e * S := (hdiff _ _ _ (relative_gradient_memLp_of_continuous hθ)
      hAns).trans hAnsatzError
  have hVL : |V - L| ≤ Clead * e * S :=
    ((hdiff _ _ _ hAns (relative_gradient_memLp_of_continuous hLead)).trans hLeadingError).trans
        (by dsimp [S]; gcongr)
  have hZS : |Z - S| ≤ CT * e * S :=
    ((hdiff _ _ _ (relative_gradient_memLp_of_continuous hT)
      (relative_gradient_memLp_of_continuous hPrev)).trans hTemperatureError).trans (by
        dsimp [S]
        gcongr)
  have hLZ : |L - Z| ≤ Real.sqrt Cenergy * e * S := by
    apply relative_sqrt_square_gap (hnn _ _) (hnn _ _) (by positivity)
    have hh : |L ^ 2 - Z ^ 2| ≤ Cenergy * e ^ 2 * S ^ 2 := by
      simpa only [L, Z, S, hsq _ hκm, hsq _ hν] using hLeadingEnergy
    exact hh.trans_eq (by simp only [mul_pow, Real.sq_sqrt hCenergy])
  have hUS : |U - S| ≤ (Cans + Clead + CT + Real.sqrt Cenergy) * e * S := by
    have h := (abs_sub_le U V S).trans (add_le_add hUV
      ((abs_sub_le V L S).trans (add_le_add hVL
        ((abs_sub_le L Z S).trans (add_le_add hLZ hZS)))))
    exact h.trans_eq (by ring)
  have hfinal := relative_energy_gap_of_norm_gap (hnn _ _) (hnn _ _)
    (show 0 ≤ Cans + Clead + CT + Real.sqrt Cenergy by positivity) he he1 hUS
  simpa only [U, S, hsq _ hκm, hsq _ hν] using hfinal

end AVenhance.Infra.Section5.RelativeError
