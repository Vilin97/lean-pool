/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseTiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Tiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! # Slice regularity of the `tiny` pieces

For the actual iterates and `t > 0`: the source error `d_m`, the last-iterate error `e_{m-1}` and
the nondivergence part of `tiny` are continuous; `d + e` is `C^∞` and `ℤ²`-periodic; the mean of
the nondivergence part follows from the mean of `tiny`.  Also a measurability helper for slice
energies of fields jointly continuous on `(0,1) × ℝ²`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}

/-- A jointly `C^∞` field on the open half space has `C^∞` slices. -/
theorem sc_slice_contDiff {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => F p.1 p.2) tcU) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (F t) := by
  have hemb : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
  have h := hF.comp_contDiff hemb (fun x => ⟨ht, Set.mem_univ x⟩)
  simpa only [Function.comp_def] using h

/-- The mean of the divergence of a smooth periodic field over the unit cube vanishes. -/
theorem sc_integral_vecDiv_eq_zero {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : IsZ2Periodic F) : ∫ x in unitCube, vecDiv F x = 0 := by
  unfold vecDiv
  have hc (i : Fin 2) : Continuous (fun x => spaceGrad (fun y => F y i) x i) := by
    have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := contDiff_pi.mp hF i
    exact (contDiff_pi.mp (Infra.Section4.iterate_gradient_smooth hi) i).continuous
  rw [integral_finsetSum _ fun i _ => LeftToShow.integrableOn_unitCube_of_continuous (hc i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := contDiff_pi.mp hF i
  have hip : IsZ2Periodic (fun y => F y i) := fun n x => congrFun (hp n x) i
  have h := LeftToShow.integral_unitCube_mul_spaceGrad
    (f := fun _ : Vec 2 => (1 : ℝ)) (g := fun y => F y i) contDiff_const (hi.of_le (by simp))
    (fun _ _ => rfl) hip i
  simpa [spaceGrad] using h

/-! ### Measurability of slice energies -/

theorem TermSourcesTinyRegular.sc_unitCube_ae_eq_closed :
    unitCube =ᵐ[(volume : Measure (Vec 2))] Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
  simpa [volume_pi, unitCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
      (g := fun _ : Fin 2 => (1 : ℝ)))

/-- Cube integrals of fields continuous on `(0,1) × ℝ²` are continuous in `t ∈ (0,1)`. -/
theorem sc_continuousOn_cubeIntegral {h : ℝ → Vec 2 → ℝ}
    (hh : ContinuousOn (fun p : ℝ × Vec 2 => h p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun t => ∫ x in unitCube, h t x) (Set.Ioo (0 : ℝ) 1) := by
  have hcongr : ∀ t, ∫ x in unitCube, h t x =
      ∫ x in (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1), h t x :=
    fun t => setIntegral_congr_set TermSourcesTinyRegular.sc_unitCube_ae_eq_closed
  simp_rw [hcongr]
  rw [continuousOn_iff_continuous_domRestrict]
  have : LocallyCompactSpace (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  have hcont : Continuous (fun q : Set.Ioo (0 : ℝ) 1 × Vec 2 => h q.1.1 q.2) := by
    have hmap : Continuous (fun q : Set.Ioo (0 : ℝ) 1 × Vec 2 => (q.1.1, q.2)) := by fun_prop
    exact hh.comp_continuous hmap (fun q => ⟨q.1.2, Set.mem_univ _⟩)
  exact continuous_parametric_integral_of_continuous
    (f := fun (s : Set.Ioo (0 : ℝ) 1) (y : Vec 2) => h s.1 y) hcont
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem sc_aemeasurable_cubeIntegral {h : ℝ → Vec 2 → ℝ}
    (hh : ContinuousOn (fun p : ℝ × Vec 2 => h p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    AEMeasurable (fun t => ∫ x in unitCube, h t x) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  (sc_continuousOn_cubeIntegral hh).aemeasurable measurableSet_Ioo

theorem sc_aemeasurable_gradNormSq {F : ℝ → Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2 i)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    AEMeasurable (fun t => ENNReal.ofReal (gradNormSq (F t)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (F p.1 p.2))
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) :=
    LeftToShow.continuous_vecNormSq_two.comp_continuousOn (continuousOn_pi.2 hF)
  exact (sc_aemeasurable_cubeIntegral (h := fun t x => vecNormSq (F t x)) hc).ennreal_ofReal

section Pieces

variable (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm) {θ₀ : Vec 2 → ℝ}
  {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
  (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
  (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)

include hm hκm hθprev hT

/-- (1) joint continuity of `d_m` on the open half space. -/
theorem sc_d_continuousOn (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => sourceErrorD I hΦ m κm (T (Nstar β)) p.1 p.2 i) tcU :=
  tc_sourceErrorD_continuousOn I hΦ m hm hκm hθprev hT i

/-- (2) joint continuity of `e_{m-1}` on the open half space. -/
theorem sc_e_continuousOn (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => iterateError I hΦ m κm κprev T p.1 p.2 i) tcU := by
  have hT1 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hT0 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β - 1)
    (Nat.sub_le _ _)
  exact (tc_iterateError_contDiffOn I hΦ m hm hκm κprev hT0 hT1 i).continuousOn

/-- (3) `d + e` is `C^∞` on every positive-time slice. -/
theorem sc_de_contDiff {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x +
      iterateError I hΦ m κm κprev T t x) := by
  have hT1 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hT0 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β - 1)
    (Nat.sub_le _ _)
  have hw := tc_pulled_contDiffOn I hΦ m hm hT1
  have hat := tc_amnrTail_contDiffOn I hΦ m hm hκm hθprev hT
  refine contDiff_pi.2 fun i => ?_
  have hd : ContDiff ℝ ∞ (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x i) := by
    have hrw : (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x i) =
        fun x => ∑ a : Fin 2, ∑ b : Fin 2, (I.Jhat κm m t - I.flux κm m t) a b *
          tcPulled I hΦ m (T (Nstar β)) a b i t x + tcAmnrTail I hΦ m κm (T (Nstar β)) t x i := by
      funext x
      exact tc_sourceErrorD_apply I hΦ m hm κm (T (Nstar β)) t x i
    rw [hrw]
    exact (ContDiff.sum fun a _ => ContDiff.sum fun b _ => contDiff_const.mul
      (sc_slice_contDiff (F := fun t y => tcPulled I hΦ m (T (Nstar β)) a b i t y)
        (hw a b i) ht)).add
      (sc_slice_contDiff (F := fun t y => tcAmnrTail I hΦ m κm (T (Nstar β)) t y i) (hat i) ht)
  have he : ContDiff ℝ ∞ (fun x => iterateError I hΦ m κm κprev T t x i) :=
    sc_slice_contDiff (F := fun t y => iterateError I hΦ m κm κprev T t y i)
      (tc_iterateError_contDiffOn I hΦ m hm hκm κprev hT0 hT1 i) ht
  exact hd.add he

omit hm hκm in
/-- The divergence-form field `d_t + e_t` is `ℤ²`-periodic for `t > 0`. -/
theorem sc_de_periodic {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (fun x => sourceErrorD I hΦ m κm (T (Nstar β)) t x +
      iterateError I hΦ m κm κprev T t x) := by
  have hTp (i : ℕ) (hi : i ≤ Nstar β) : IsZ2Periodic (T i t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev hi ht.le
  have hgp (i : ℕ) (hi : i ≤ Nstar β) (n : Fin 2 → ℤ) (x : Vec 2) :
      spaceGrad (T i t) (x + latticeShift n) = spaceGrad (T i t) x :=
    Section5.RelativeError.spaceGrad_isZ2Periodic (hTp i hi) n x
  intro n x
  funext i
  have hd : sourceErrorD I hΦ m κm (T (Nstar β)) t (x + latticeShift n) i =
      sourceErrorD I hΦ m κm (T (Nstar β)) t x i := by
    have hfa : (∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t (x + latticeShift n)).transpose.mulVec
          ((I.Jhat κm m t - I.flux κm m t).mulVec
            ((I.flowGrad hΦ m l t (x + latticeShift n)).mulVec
              (spaceGrad (T (Nstar β) t) (x + latticeShift n)))))) =
        ∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).transpose.mulVec
          ((I.Jhat κm m t - I.flux κm m t).mulVec
            ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T (Nstar β) t) x)))) := by
      refine tsum_congr fun l => ?_
      have hf : I.flowGrad hΦ m l t (x + latticeShift n) = I.flowGrad hΦ m l t x := by
        ext a b
        exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t a b n x
      rw [hf, hgp (Nstar β) le_rfl n x]
    have hta : tcAmnrTail I hΦ m κm (T (Nstar β)) t (x + latticeShift n) i =
        tcAmnrTail I hΦ m κm (T (Nstar β)) t x i := by
      unfold tcAmnrTail
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => by
          exact congrArg (· * I.qMNR κm m a (Jcut β) t j k)
            (Integration.Amnr_isZ2Periodic_pos I hΦ m κm a (fun s hs =>
              Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl hs) (Jcut β) t ht i j k n x)
    unfold sourceErrorD
    rw [hfa]
    simp only [Pi.add_apply]
    congr 1
  have he : iterateError I hΦ m κm κprev T t (x + latticeShift n) i =
      iterateError I hΦ m κm κprev T t x i := by
    unfold iterateError
    rw [RelativeError.sMat_isZ2Periodic I hΦ m κm t n x, hgp _ (Nat.sub_le _ _) n x,
      hgp (Nstar β) le_rfl n x]
  simp only [Pi.add_apply, hd, he]

/-- (5) `tiny` is continuous on every positive-time slice. -/
theorem sc_tiny_slice_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t) := by
  have h := tc_tiny_continuousOn I hΦ m hm hκm hθprev hT
  have hemb : Continuous (fun x : Vec 2 => (t, x)) := by fun_prop
  have hc := h.comp_continuous hemb (fun x => ⟨ht, Set.mem_univ x⟩)
  simpa only [Function.comp_def] using hc

/-- The divergence of the smooth field `d_t + e_t` is continuous. -/
theorem sc_vecDiv_de_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (fun x => vecDiv (fun y => sourceErrorD I hΦ m κm (T (Nstar β)) t y +
      iterateError I hΦ m κm κprev T t y) x) := by
  have hF := sc_de_contDiff I hΦ hm hκm hθprev hT ht
  unfold vecDiv
  refine continuous_finsetSum _ fun i _ => ?_
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => (sourceErrorD I hΦ m κm (T (Nstar β)) t y +
      iterateError I hΦ m κm κprev T t y) i) := contDiff_pi.mp hF i
  exact (contDiff_pi.mp (Infra.Section4.iterate_gradient_smooth hi) i).continuous

/-- (6) The nondivergence part of `tiny` is continuous on positive-time slices. -/
theorem sc_nd_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t) := by
  have h := (sc_tiny_slice_continuous I hΦ hm hκm hθprev hT ht).sub
    (sc_vecDiv_de_continuous I hΦ hm hκm hθprev hT ht)
  refine h.congr fun x => ?_
  simp only [Pi.sub_apply, tiny_eq_divergence_add_nondivergence]
  ring

/-- (7) mean of `tiny` zero gives mean of its nondivergence part zero. -/
theorem sc_nd_meanZero {t : ℝ} (ht : 0 < t)
    (hmean : MeanZeroOn unitCube (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t)) :
    MeanZeroOn unitCube (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t) := by
  have hdiv := sc_integral_vecDiv_eq_zero (sc_de_contDiff I hΦ hm hκm hθprev hT ht)
    (sc_de_periodic I hΦ hθprev hT ht)
  have hi1 := LeftToShow.integrableOn_unitCube_of_continuous
    (sc_vecDiv_de_continuous I hΦ hm hκm hθprev hT ht)
  have hi2 := LeftToShow.integrableOn_unitCube_of_continuous
    (sc_nd_continuous I hΦ hm hκm hθprev hT ht)
  unfold MeanZeroOn at hmean ⊢
  have heq : tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t = fun x =>
        vecDiv (fun y => sourceErrorD I hΦ m κm (T (Nstar β)) t y +
          iterateError I hΦ m κm κprev T t y) x +
        tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t x :=
    tiny_eq_divergence_add_nondivergence I hΦ m κm _ _ t
  rw [heq, integral_add hi1 hi2, hdiv, zero_add] at hmean
  exact hmean

end Pieces

end AVenhance.Infra.Section5.Contracts
end
