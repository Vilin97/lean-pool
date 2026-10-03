/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeStepCore

/-! # The relative energy comparison with an open-time ansatz gradient

`relative_step_from_errors` asks for joint continuity of
`∇θTilde_m` on `[0,∞) × ℝ²`.  The ansatz is extension-dependent at `t = 0` (two-sided time
derivative in `Amnr`), so `relative_step_from_errors_Ioi` only asks that `∇θTilde_m`
agree on `(0,∞) × ℝ²` with some field continuous on `[0,∞) × ℝ²` (`OpenTimeExtends`).  Since
`spaceTimeGradNormSq` integrates over `timeCube ⊆ (0,∞) × ℝ²`, every norm is unchanged by passing
to the extension, which supplies the square integrability the `L²` triangle inequalities need. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.LeftToShow
namespace AVenhance.Infra.Section5.RelativeError

/-- `f` agrees on the open half space with a field continuous on the closed half space. -/
def OpenTimeExtends (f : ℝ → Vec 2 → Vec 2) : Prop :=
  ∃ G : ℝ × Vec 2 → Vec 2, ContinuousOn G (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
    ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)), f p.1 p.2 = G p

theorem OpenTimeExtends.of_continuousOn {f : ℝ → Vec 2 → Vec 2}
    (hf : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    OpenTimeExtends f :=
  ⟨fun p => f p.1 p.2, hf, fun _ _ => rfl⟩

/-- `spaceTimeGradNormSq` only sees `timeCube ⊆ (0,∞) × ℝ²`. -/
theorem spaceTimeGradNormSq_congr_Ioi {f g : ℝ → Vec 2 → Vec 2}
    (h : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)), f p.1 p.2 = g p.1 p.2) :
    spaceTimeGradNormSq f = spaceTimeGradNormSq g := by
  unfold spaceTimeGradNormSq
  refine setIntegral_congr_fun
    (measurableSet_Ioo.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))) ?_
  intro p hp
  simp only [h p ⟨hp.1.1, Set.mem_univ _⟩]

theorem relative_gradient_norm_sub_le_of_extends {f g : ℝ → Vec 2 → Vec 2}
    (hf : OpenTimeExtends f) (hg : OpenTimeExtends g) :
    |Real.sqrt (spaceTimeGradNormSq f) - Real.sqrt (spaceTimeGradNormSq g)| ≤
      Real.sqrt (spaceTimeGradNormSq (fun t x => f t x - g t x)) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  have e1 : spaceTimeGradNormSq f = spaceTimeGradNormSq (fun t x => F (t, x)) :=
    spaceTimeGradNormSq_congr_Ioi hfF
  have e2 : spaceTimeGradNormSq g = spaceTimeGradNormSq (fun t x => G (t, x)) :=
    spaceTimeGradNormSq_congr_Ioi hgG
  have e3 : spaceTimeGradNormSq (fun t x => f t x - g t x) =
      spaceTimeGradNormSq (fun t x => F (t, x) - G (t, x)) :=
    spaceTimeGradNormSq_congr_Ioi (fun p hp => by simp only [hfF p hp, hgG p hp])
  rw [e1, e2, e3]
  exact relative_gradient_norm_sub_le (f := fun t x => F (t, x)) (g := fun t x => G (t, x))
    (by simpa using hF) (by simpa using hG)

theorem relative_step_from_errors_Ioi
    (Cans Clead CT Cenergy : ℝ) (hCans : 0 ≤ Cans) (hClead : 0 ≤ Clead)
    (hCT : 0 ≤ CT) (hCenergy : 0 ≤ Cenergy)
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m M : ℕ) (κ : ℝ)
    (θm θprev T : ℝ → Vec 2 → ℝ)
    (hκm : 0 ≤ I.kappaSeq κ M m) (hν : 0 ≤ I.kappaSeq κ M (m - 1))
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1)
    (hθ : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (θm p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hAns : OpenTimeExtends (fun s x => spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) T s) x))
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
      (hf : OpenTimeExtends f) (hg : OpenTimeExtends g) :
      |normG a f - normG a g| ≤ Real.sqrt a *
        Real.sqrt (spaceTimeGradNormSq (fun s x => f s x - g s x)) := by
    dsimp [normG]
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (relative_gradient_norm_sub_le_of_extends hf hg)
      (Real.sqrt_nonneg _)
  have he2 : e ^ 2 ≤ e := by nlinarith only [he, he1]
  have hUV : |U - V| ≤ Cans * e * S := (hdiff _ _ _ (OpenTimeExtends.of_continuousOn hθ)
      hAns).trans hAnsatzError
  have hVL : |V - L| ≤ Clead * e * S :=
    ((hdiff _ _ _ hAns (OpenTimeExtends.of_continuousOn hLead)).trans hLeadingError).trans (by
        dsimp [S]; gcongr)
  have hZS : |Z - S| ≤ CT * e * S :=
    ((hdiff _ _ _ (OpenTimeExtends.of_continuousOn hT)
      (OpenTimeExtends.of_continuousOn hPrev)).trans hTemperatureError).trans (by dsimp [S]; gcongr)
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
