/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyRegular
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyTransfer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowGeometry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity

/-! # The time negative norm of `tiny` in terms of the last increment

`timeHMinusOneNorm tiny ≤ 2 b_d + √(c ∑_w ‖∇ ∂^w V‖²_{L²((0,1)×𝕋²)})` where `V = T_{N*} - T_{N*-1}`
is the last increment, `b_d` bounds the `L²_{t,x}` norm of `d_m`, and `c` collects the coefficient
jets of `B = K_m - κ_{m-1} + s_{m-1}` and the corrector size.  Here only the structure of `tiny`
(`hMinusOneNorm_tiny_le_of_components`) and the slice regularity are used; no scale arithmetic. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4

theorem sc_one_le_Nstar {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 1 ≤ Nstar β :=
  le_trans (by norm_num) (Infra.Ingredients.Nstar_ge_256 hβ hβ')

theorem sc_l2NormSq_nonneg (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f := by
  unfold l2NormSq
  exact integral_nonneg fun x => sq_nonneg _

theorem sc_vecNormSq_add_le (a b : Vec 2) :
    vecNormSq (a + b) ≤ 2 * vecNormSq a + 2 * vecNormSq b := by
  rw [sc_vecNormSq_eq, sc_vecNormSq_eq, sc_vecNormSq_eq]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]

/-- Slices of a field continuous on the open half space are continuous. -/
theorem sc_slice_continuous {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) tcU) {t : ℝ} (ht : 0 < t) :
    Continuous (F t) := by
  have hemb : Continuous (fun x : Vec 2 => (t, x)) := by fun_prop
  have hc := hF.comp_continuous hemb (fun x => ⟨ht, Set.mem_univ x⟩)
  simpa only [Function.comp_def] using hc

theorem sc_slice_continuous_vec {F : ℝ → Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2 i) tcU) {t : ℝ}
    (ht : 0 < t) : Continuous (F t) :=
  continuous_pi fun i => sc_slice_continuous (F := fun t x => F t x i) (hF i) ht

section Bound

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
  (hm : 2 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm) {θ₀ : Vec 2 → ℝ}
  {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
  (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
  (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)

include hm hκm hθprev hT

/-- The slice bound `‖tiny(t)‖_{HDot⁻¹} ≤ ‖d+e‖_{L²} + (2π)⁻¹ ‖nd‖_{L²}`. -/
theorem sc_tiny_slice_le {t : ℝ} (ht : 0 < t)
    (hmean : MeanZeroOn unitCube (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t)) :
    hMinusOneNorm (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
        (iterateError I hΦ m κm κprev T) t) ≤
      ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x +
        iterateError I hΦ m κm κprev T t x))) +
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq
        (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t))) := by
  have hm1 : 1 ≤ m := by omega
  exact hMinusOneNorm_tiny_le_of_components I hΦ m κm _ _ t
    (Integration.memL2On_unitCube_of_continuous
      (sc_vecDiv_de_continuous I hΦ hm1 hκm hθprev hT ht))
    (Integration.memL2On_unitCube_of_continuous
      (sc_nd_continuous I hΦ hm1 hκm hθprev hT ht))
    (sc_nd_meanZero I hΦ hm1 hκm hθprev hT ht hmean)
    (sc_de_contDiff I hΦ hm1 hκm hθprev hT ht) (sc_de_periodic I hΦ hθprev hT ht)

omit hκm hθprev hT in
theorem sc_scCoeff_contDiff (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scCoeff I hΦ m κm κprev t) := by
  have hm1 : 1 ≤ m := by omega
  have hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞) (fun x => I.flowGrad hΦ m l t x) := fun l =>
    (Infra.Section4.iterate_flowGrad_joint_smooth I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hs := sMat_spatial_contDiff I hΦ m hm1 κm t hflow
  exact contDiff_const.add hs

omit hm hκm in
theorem sc_increment_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => iterateIncrement T (Nstar β) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hN := sc_one_le_Nstar I.one_lt_beta I.beta_lt
  obtain ⟨n, hn⟩ : ∃ n, Nstar β = n + 1 := ⟨Nstar β - 1, by omega⟩
  have hinc : (fun z : AmnrSpace => iterateIncrement T (Nstar β) z.1 z.2) =
      fun z => T (Nstar β) z.1 z.2 - T (Nstar β - 1) z.1 z.2 := by
    funext z
    rw [hn, iterateIncrement_succ]
    simp
  rw [hinc]
  exact (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl).sub
    (Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β - 1) (Nat.sub_le _ _))

/-- **The time negative norm of `tiny` in terms of the last increment.** -/
theorem sc_tiny_time_bound
    (hmean : Integration.TinyMeanZeroContract I hΦ m κm κprev T) {bd : ℝ} (hbd : 0 ≤ bd)
    (hd : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt
      (gradNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal bd)
    {b cχ D r : ℝ}
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x j k, |scCoeff I hΦ m κm κprev t x j k| ≤ b)
    (hχ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ (k : ℤ) (x : Vec 2) (j : Fin 2),
      |I.chiTilde hΦ m κm k t x j| ≤ cχ)
    (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x, ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord (scCoeff I hΦ m κm κprev t) p x j k| ≤
        D * (p.length.factorial : ℝ) * r ^ p.length) :
    timeHMinusOneNorm (fun t => tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
        (iterateError I hΦ m κm κprev T) t) ≤
      ENNReal.ofReal (2 * bd + Real.sqrt ((16 * b ^ 2 + 2 * ((2 * Real.pi)⁻¹) ^ 2 *
        (5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4))) * ∑ w ∈ scWords2,
          spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w))) := by
  have hm1 : 1 ≤ m := by omega
  have hN := sc_one_le_Nstar I.one_lt_beta I.beta_lt
  set c : ℝ := 16 * b ^ 2 + 2 * ((2 * Real.pi)⁻¹) ^ 2 *
    (5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4)) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hQ0 : 0 ≤ ∑ w ∈ scWords2, spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w)
      :=
    Finset.sum_nonneg fun _ _ => sc_spaceTimeGradNormSq_nonneg _
  have hu := sc_increment_contDiffOn I hΦ hθprev hT
  unfold timeHMinusOneNorm
  have hrest : ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (4 * gradNormSq
        (iterateError I hΦ m κm κprev T t) + 2 * ((2 * Real.pi)⁻¹) ^ 2 *
        l2NormSq (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t)) ≤
      ENNReal.ofReal (c * ∑ w ∈ scWords2,
        spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w)) := by
    have h := sc_lintegral_le_of_slices (S := scWords2)
      (V := fun w => scWordGrad (iterateIncrement T (Nstar β)) w) (c := fun _ => c)
      (fun _ _ => hc0)
      (fun w _ i => sc_wordGrad_continuousOn hu w i)
      (f := fun t => ENNReal.ofReal (4 * gradNormSq (iterateError I hΦ m κm κprev T t) +
        2 * ((2 * Real.pi)⁻¹) ^ 2 * l2NormSq
          (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t)))
      (fun t ht => by
        apply ENNReal.ofReal_le_ofReal
        have h := sc_slice_energy_le I hΦ hm T t hN
          (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
          (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev (Nat.sub_le _ _) ht.1.le)
          (sc_scCoeff_contDiff I hΦ hm t)
          (sc_nd_continuous I hΦ hm1 hκm hθprev hT ht.1) (hb t ht) (hχ t ht) hD hr (hAj t ht)
        rw [← Finset.mul_sum]
        exact h)
    rw [← Finset.mul_sum] at h
    exact h
  have hdc : ∀ t, 0 < t → Continuous (sourceErrorD I hΦ m κm (T (Nstar β)) t) := fun t ht =>
    sc_slice_continuous_vec (F := sourceErrorD I hΦ m κm (T (Nstar β)))
      (fun i => sc_d_continuousOn I hΦ hm1 hκm hθprev hT i) ht
  have hec : ∀ t, 0 < t → Continuous (iterateError I hΦ m κm κprev T t) := fun t ht =>
    sc_slice_continuous_vec (F := iterateError I hΦ m κm κprev T)
      (fun i => sc_e_continuousOn I hΦ hm1 hκm hθprev hT i) ht
  refine sc_time_norm_le
    (X := fun t => hMinusOneNorm (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t))
    (GF := fun t => gradNormSq (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x +
      iterateError I hΦ m κm κprev T t x))
    (Gd := fun t => gradNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t))
    (Ge := fun t => gradNormSq (iterateError I hΦ m κm κprev T t))
    (N := fun t => l2NormSq (tinyNondivergencePart I hΦ m κm
      (iterateError I hΦ m κm κprev T) t)) hbd (mul_nonneg hc0 hQ0)
    (fun t _ => sc_gradNormSq_nonneg _) (fun t _ => sc_gradNormSq_nonneg _)
    (fun t _ => sc_l2NormSq_nonneg _) (fun t _ => sc_gradNormSq_nonneg _) ?_
    (fun t ht => sc_tiny_slice_le I hΦ hm hκm hθprev hT ht.1 (hmean t ht)) ?_ hd hrest
  · intro t ht
    have h1 : IntegrableOn (fun x => vecNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t x))
        unitCube := LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp (hdc t ht.1))
    have h2 : IntegrableOn (fun x => vecNormSq (iterateError I hΦ m κm κprev T t x))
        unitCube := LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp (hec t ht.1))
    have h3 : IntegrableOn (fun x => vecNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t x +
        iterateError I hΦ m κm κprev T t x)) unitCube :=
      LeftToShow.integrableOn_unitCube_of_continuous
        (LeftToShow.continuous_vecNormSq_two.comp ((hdc t ht.1).add (hec t ht.1)))
    unfold gradNormSq
    calc ∫ x in unitCube, vecNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t x +
          iterateError I hΦ m κm κprev T t x)
        ≤ ∫ x in unitCube, (2 * vecNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t x) +
            2 * vecNormSq (iterateError I hΦ m κm κprev T t x)) :=
          integral_mono h3 ((h1.const_mul 2).add (h2.const_mul 2)) fun x =>
            sc_vecNormSq_add_le _ _
      _ = _ := by
          rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
            integral_const_mul]
  · exact sc_aemeasurable_gradNormSq (F := sourceErrorD I hΦ m κm (T (Nstar β)))
      (fun i => (sc_d_continuousOn I hΦ hm1 hκm hθprev hT i).mono
        (Set.prod_mono (fun t ht => ht.1) le_rfl))

end Bound

end AVenhance.Infra.Section5.Contracts
