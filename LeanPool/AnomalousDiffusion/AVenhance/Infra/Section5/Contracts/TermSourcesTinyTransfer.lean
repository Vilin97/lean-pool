/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordRegularity

/-! # Space-time transfer for the `tiny` source contract

If a nonnegative function `f` of time is dominated on `(0,1)` by a nonnegative combination of the
slice energies `‖V_j(t)‖²_{L²}` of fields continuous on `[0,1] × ℝ²`, then its lower integral over
`(0,1)` is dominated by the same combination of the space-time energies.  The fields used are the
gradients of the spatial words applied to the last increment `T_{N*} - T_{N*-1}`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4

theorem sc_gradNormSq_nonneg (F : Vec 2 → Vec 2) : 0 ≤ gradNormSq F := by
  unfold gradNormSq
  exact integral_nonneg fun x => vecNormSq_nonneg (F x)

theorem sc_spaceTimeGradNormSq_nonneg (V : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq V := by
  unfold spaceTimeGradNormSq
  exact integral_nonneg fun p => vecNormSq_nonneg _

theorem sc_continuousOn_vecNormSq {V : ℝ → Vec 2 → Vec 2} {s : Set (ℝ × Vec 2)}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i) s) :
    ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2)) s :=
  LeftToShow.continuous_vecNormSq_two.comp_continuousOn (continuousOn_pi.2 hV)

theorem sc_sliceEnergy_continuousOn {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun t => gradNormSq (V t)) (Set.Icc (0 : ℝ) 1) :=
  LeftToShow.continuousOn_integral_unitCube (h := fun t x => vecNormSq (V t x))
    (sc_continuousOn_vecNormSq hV)

theorem sc_spaceTime_eq_integral {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    spaceTimeGradNormSq V = ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
  calc
    spaceTimeGradNormSq V = ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (V t x) :=
      LeftToShow.spaceTimeGradNormSq_eq_intervalIntegral (continuousOn_pi.2 hV)
    _ = ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      rfl

/-- **Generic transfer.**  A slicewise domination of `f` by `∑ c_j ‖V_j(t)‖²` gives the same
domination of the lower integral of `f` by `∑ c_j ‖V_j‖²_{L²((0,1)×𝕋²)}`. -/
theorem sc_lintegral_le_of_slices {ι : Type*} (S : Finset ι) {V : ι → ℝ → Vec 2 → Vec 2}
    {c : ι → ℝ} (hc : ∀ j ∈ S, 0 ≤ c j)
    (hV : ∀ j ∈ S, ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    {f : ℝ → ENNReal}
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ≤ ENNReal.ofReal (∑ j ∈ S, c j * gradNormSq (V j t))) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, f t ≤
      ENNReal.ofReal (∑ j ∈ S, c j * spaceTimeGradNormSq (V j)) := by
  have hgint : ∀ j ∈ S, IntegrableOn (fun t => gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
    fun j hj => ((sc_sliceEnergy_continuousOn (hV j hj)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hsum_int : IntegrableOn (fun t => ∑ j ∈ S, c j * gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
    integrable_finsetSum _ fun j hj => (hgint j hj).const_mul (c j)
  have hnn : ∀ t, 0 ≤ ∑ j ∈ S, c j * gradNormSq (V j t) := fun t =>
    Finset.sum_nonneg fun j hj => mul_nonneg (hc j hj) (sc_gradNormSq_nonneg _)
  have hint : ∫ t in Set.Ioo (0 : ℝ) 1, ∑ j ∈ S, c j * gradNormSq (V j t) =
      ∑ j ∈ S, c j * spaceTimeGradNormSq (V j) := by
    rw [integral_finsetSum _ fun j hj => (hgint j hj).const_mul (c j)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, sc_spaceTime_eq_integral (hV j hj)]
  calc ∫⁻ t in Set.Ioo (0 : ℝ) 1, f t
      ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (∑ j ∈ S, c j * gradNormSq (V j t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hf t ht
    _ = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, ∑ j ∈ S, c j * gradNormSq (V j t)) :=
        (ofReal_integral_eq_lintegral_ofReal hsum_int (ae_of_all _ hnn)).symm
    _ = _ := by rw [hint]

/-- The gradient field of the word `w` applied to the time slices of `u`. -/
def scWordGrad (u : ℝ → Vec 2 → ℝ) (w : List (Fin 2)) (t : ℝ) (x : Vec 2) : Vec 2 :=
  spaceGrad (iterateSpatialWord w (u t)) x

/-- Gradients of spatial words of a function jointly `C^∞` on the closed half space are continuous
on `[0,1] × ℝ²`. -/
theorem sc_wordGrad_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => scWordGrad u w p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have h := (iterateSpatialWord_smooth_up_to_initial hu (i :: w)).continuousOn
  exact h.mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)

theorem sc_increment_contDiff {β : ℝ} {T : ℕ → ℝ → Vec 2 → ℝ} {t : ℝ} (hN : 1 ≤ Nstar β)
    (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t)) :
    ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T (Nstar β) t) := by
  obtain ⟨n, hn⟩ : ∃ n, Nstar β = n + 1 := ⟨Nstar β - 1, by omega⟩
  have hinc : iterateIncrement T (Nstar β) t = fun x => T (Nstar β) t x - T (Nstar β - 1) t x := by
    rw [hn, iterateIncrement_succ]
    simp
  rw [hinc]
  exact hTa.sub hTb

theorem sc_wordEnergy_continuous {v : Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) :
    Continuous (fun x => vecNormSq (spaceGrad (iterateSpatialWord w v) x)) :=
  LeftToShow.continuous_vecNormSq_two.comp
    (iterate_gradient_smooth (iterateSpatialWord_smooth hv w)).continuous

/-- **Slicewise energy domination.**  At a fixed time, the weighted sum of the energy of the error
`e_{m-1}` and of the nondivergence part of `tiny` is bounded by the energies of the gradients of
the words of length `≤ 2` of the last increment. -/
theorem sc_slice_energy_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm κprev : ℝ} (T : ℕ → ℝ → Vec 2 → ℝ)
    (t : ℝ) (hN : 1 ≤ Nstar β) (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t))
    (hAs : ContDiff ℝ (⊤ : ℕ∞) (scCoeff I hΦ m κm κprev t))
    (hnd : Continuous (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t))
    {b cχ D r : ℝ} (hb : ∀ x j k, |scCoeff I hΦ m κm κprev t x j k| ≤ b)
    (hχ : ∀ (k : ℤ) (x : Vec 2) (j : Fin 2), |I.chiTilde hΦ m κm k t x j| ≤ cχ)
    (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ x, ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord (scCoeff I hΦ m κm κprev t) p x j k| ≤
        D * (p.length.factorial : ℝ) * r ^ p.length) :
    4 * gradNormSq (iterateError I hΦ m κm κprev T t) +
        2 * ((2 * Real.pi)⁻¹) ^ 2 *
          l2NormSq (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t) ≤
      (16 * b ^ 2 + 2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4))) *
        ∑ w ∈ scWords2, gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t) := by
  have hV := sc_increment_contDiff (T := T) hN hTa hTb
  set E : Vec 2 → Vec 2 := iterateError I hΦ m κm κprev T t with hE
  have hEc : Continuous E := by
    have : E = fun y => -((scCoeff I hΦ m κm κprev t y).mulVec
        (spaceGrad (iterateIncrement T (Nstar β) t) y)) := by
      funext y; exact sc_iterateError_eq I hΦ m κm κprev T t hN hTa hTb y
    rw [this]
    refine continuous_pi fun i => ?_
    change Continuous (fun y => -(∑ j : Fin 2, scCoeff I hΦ m κm κprev t y i j *
      spaceGrad (iterateIncrement T (Nstar β) t) y j))
    refine (continuous_finsetSum _ fun j _ => ?_).neg
    exact ((continuous_apply j).comp (continuous_apply i |>.comp hAs.continuous)).mul
      ((continuous_apply j).comp (iterate_gradient_smooth hV).continuous)
  have hEint : IntegrableOn (fun x => vecNormSq (E x)) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous (LeftToShow.continuous_vecNormSq_two.comp hEc)
  have hWint : ∀ w, IntegrableOn (fun x => vecNormSq
      (spaceGrad (iterateSpatialWord w (iterateIncrement T (Nstar β) t)) x)) unitCube :=
    fun w => LeftToShow.integrableOn_unitCube_of_continuous (sc_wordEnergy_continuous hV w)
  -- the energy of `e`
  have h1 : gradNormSq E ≤ 4 * b ^ 2 * gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) [] t)
      := by
    unfold gradNormSq scWordGrad
    rw [← integral_const_mul]
    exact integral_mono hEint ((hWint []).const_mul _) fun x =>
      sc_e_vecNormSq_le I hΦ m κm κprev T t hN hTa hTb x (hb x)
  -- the energy of the nondivergence part
  have hndint : IntegrableOn (fun x => (tinyNondivergencePart I hΦ m κm
      (iterateError I hΦ m κm κprev T) t x) ^ 2) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous (hnd.pow 2)
  have h2 : l2NormSq (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t) ≤
      5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4) * ∑ w ∈ scWords2,
        gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t) := by
    unfold l2NormSq gradNormSq scWordGrad
    rw [← integral_finsetSum _ fun w _ => hWint w, ← integral_const_mul]
    exact integral_mono hndint (((integrable_finsetSum _ fun w _ => hWint w)).const_mul _)
      fun x => sc_nd_sq_le_words I hΦ hm T t hN hTa hTb hAs hχ x hD hr (hAj x)
  have hsub : gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) [] t) ≤
      ∑ w ∈ scWords2, gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t) :=
    Finset.single_le_sum (f := fun w => gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t))
      (fun _ _ => sc_gradNormSq_nonneg _) (mem_scWords2 (by simp))
  have hs0 : 0 ≤ gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) [] t) :=
    sc_gradNormSq_nonneg _
  have hq : 0 ≤ 2 * ((2 * Real.pi)⁻¹) ^ 2 := by positivity
  have e1 : 4 * gradNormSq E ≤ 16 * b ^ 2 * ∑ w ∈ scWords2,
      gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t) := by
    calc 4 * gradNormSq E ≤ 4 * (4 * b ^ 2 * gradNormSq (scWordGrad (iterateIncrement T (Nstar β))
        [] t)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 16 * b ^ 2 * gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) [] t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub (by positivity)
  have e2 := mul_le_mul_of_nonneg_left h2 hq
  calc _ ≤ 16 * b ^ 2 * ∑ w ∈ scWords2, gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t) +
        2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4) *
          ∑ w ∈ scWords2, gradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w t)) :=
        add_le_add e1 e2
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
