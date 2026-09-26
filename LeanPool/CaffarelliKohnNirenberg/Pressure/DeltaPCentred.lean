/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWS

/-!
# Delta PCentred

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! The centred tensor and its distributional pressure identity. -/

/-- Fully centered velocity tensor used in the pressure-pairing identities. -/
def pressureUHat (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (z : ParabolicPoint) (i j : Fin 3) : ℝ :=
  -(u z i - c z.2 i) * (u z j - c z.2 j)

private lemma pressure_delta_p_centred_ae_hmixedZero_1 :
    ∀ {Ω : Set Vec3} {_ : ParabolicPoint → Vec3} {_ : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (Ω' : Set Vec3),
            closure Ω' ⊆ Ω →
              (∀ (i j : Fin (3 : ℕ)), tsupport (mixedSecond ψ i j) ⊆ Ω') →
                (∀ (i j : Fin (3 : ℕ)),
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (mixedSecond ψ i j) volume) →
                  ∀ (i j : Fin (3 : ℕ)),
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) => mixedSecond ψ i j x) =
                      (0 : ℝ)
    := by
  intro Ω f c ψ hψ hψc Ω' hΩ'Ω hmixedΩ hMixedInt i j
  have hleft : Integrable
      (fun x : Vec3 => (1 : ℝ) * mixedSecond ψ i j x) volume := by
    exact (hMixedInt i j).const_mul 1
  have hright : Integrable
      (fun x : Vec3 => (fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x)
        (basisVec i) * spatialDeriv ψ j x) volume := by
    have hz : Integrable (fun _ : Vec3 => (0 : ℝ)) volume := by
      fun_prop
    simpa only [fderiv_const_apply, zero_apply, zero_mul] using hz
  have hprod : Integrable (fun x : Vec3 => (1 : ℝ) * spatialDeriv ψ j x) volume := by
    simpa only [one_mul] using
      (contDiff_spatialDeriv_smooth hψ j).continuous.integrable_of_hasCompactSupport
        (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Vec3 => (1 : ℝ)) (g := spatialDeriv ψ j)
    (v := basisVec i) hright
    (by simpa [mixedSecond, spatialDeriv] using hleft) hprod
    (fun x _ => differentiableAt_const (c := (1 : ℝ)))
    (fun x _ => (contDiff_spatialDeriv_smooth hψ j).differentiable (by simp) x)
  have hfull : ∫ x, mixedSecond ψ i j x = 0 := by
    have hconst : ∀ x : Vec3,
        fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x = 0 := by
      intro x
      exact fderiv_const_apply 1
    have hz : ∫ x : Vec3,
        (fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x) (basisVec i) *
          spatialDeriv ψ j x = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with x
      rw [hconst x]
      simp
    rw [hz] at hIBP
    simpa only [one_mul, mixedSecond, spatialDeriv, neg_zero] using hIBP
  calc
    (∫ x in Ω, mixedSecond ψ i j x) =
        ∫ x, mixedSecond ψ i j x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun hxt =>
        hx ((hmixedΩ i j).trans (subset_closure.trans hΩ'Ω) hxt))
    _ = 0 := hfull

private lemma pressure_delta_p_centred_ae_hCzero_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3)
      (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
              fun (x : Vec3) => ∑ j : Fin (3 : ℕ), u (x, s) j * mixedSecond ψ j i x) =
            (0 : ℝ)) →
        (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => u (x, s) i * g x) Ω volume) →
          (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j)) →
            (∀ (i j : Fin (3 : ℕ)), HasCompactSupport (mixedSecond ψ i j)) →
              (∀ (i j : Fin (3 : ℕ)), tsupport (mixedSecond ψ i j) ⊆ Ω') →
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                    fun (x : Vec3) =>
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ), c s j * (u (x, s) i * mixedSecond ψ i j x)) =
                  (0 : ℝ)
    := by
  intro Ω u c ψ Ω' s hdiv_s huScalar hmixedCont hmixedC hmixedΩ
  have hswap : (fun x : Vec3 => ∑ i, ∑ j,
      c s j * (u (x, s) i * mixedSecond ψ i j x)) =
      (fun x : Vec3 => ∑ j, ∑ i,
        c s j * (u (x, s) i * mixedSecond ψ i j x)) := by
    funext x
    rw [Finset.sum_comm]
  calc
    (∫ x in Ω, ∑ i, ∑ j,
        c s j * (u (x, s) i * mixedSecond ψ i j x)) =
        ∫ x in Ω, ∑ j, ∑ i,
          c s j * (u (x, s) i * mixedSecond ψ i j x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrFun hswap x
    _ =
        ∑ j, ∫ x in Ω, ∑ i,
          c s j * (u (x, s) i * mixedSecond ψ i j x) := by
      simpa using integral_finsetSum (μ := volume.restrict Ω)
        (Finset.univ : Finset (Fin 3)) (fun j _ =>
          integrable_finsetSum' (Finset.univ : Finset (Fin 3))
            (fun i _ => (huScalar (i := i) (hmixedCont i j).continuous
              (hmixedC i j) (hmixedΩ i j)).const_mul (c s j)))
    _ = ∑ j, c s j * (∫ x in Ω, ∑ i,
        u (x, s) i * mixedSecond ψ i j x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (fun x => ∑ i, c s j *
          (u (x, s) i * mixedSecond ψ i j x)) =
          (fun x => c s j * ∑ i, u (x, s) i * mixedSecond ψ i j x) by
            funext x; rw [Finset.mul_sum]]
      rw [integral_const_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hdiv_s j, mul_zero]

private lemma pressure_delta_p_centred_ae_hcenter_3 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (s : ℝ),
      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
          (fun (x : Vec3) =>
            ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), u (x, s) i * u (x, s) j * mixedSecond ψ i j x)
          Ω volume →
        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
            (fun (x : Vec3) =>
              ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), c s i * (u (x, s) j * mixedSecond ψ i j x))
            Ω volume →
          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
              (fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), c s j * (u (x, s) i * mixedSecond ψ i j x))
              Ω volume →
            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                (fun (x : Vec3) =>
                  ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), c s i * c s j * mixedSecond ψ i j x)
                Ω volume →
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                    fun (x : Vec3) =>
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ), c s i * (u (x, s) j * mixedSecond ψ i j x)) =
                  (0 : ℝ) →
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                      fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ), c s j * (u (x, s) i * mixedSecond ψ i j x)) =
                    (0 : ℝ) →
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), c s i * c s j * mixedSecond ψ i j x) =
                      (0 : ℝ) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ), pressureUHat u c (x, s) i j * mixedSecond ψ i j x)
                      (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ), u (x, s) i * u (x, s) j * mixedSecond ψ i j x)
    := by
  intro Ω u c ψ s hA hB hC hD hBzero hCzero hDzero
  have hpoint : ∀ x : Vec3, (∑ i, ∑ j,
      pressureUHat u c ((x, s) : ParabolicPoint) i j * mixedSecond ψ i j x) =
      (-(∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
        ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x) +
        ∑ i, ∑ j, c s j * (u (x, s) i * mixedSecond ψ i j x) -
        ∑ i, ∑ j, c s i * c s j * mixedSecond ψ i j x) := by
    intro x
    change (∑ i, ∑ j,
      (-(u ((x, s) : ParabolicPoint) i - c s i) *
        (u ((x, s) : ParabolicPoint) j - c s j)) * mixedSecond ψ i j x) = _
    calc
      _ = ∑ i, ∑ j, (
          -(u ((x, s) : ParabolicPoint) i * u ((x, s) : ParabolicPoint) j *
              mixedSecond ψ i j x) +
            c s i * (u ((x, s) : ParabolicPoint) j * mixedSecond ψ i j x) +
            c s j * (u ((x, s) : ParabolicPoint) i * mixedSecond ψ i j x) -
            c s i * c s j * mixedSecond ψ i j x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib]
  calc
    (∫ x in Ω, ∑ i, ∑ j,
        pressureUHat u c ((x, s) : ParabolicPoint) i j * mixedSecond ψ i j x) =
        ∫ x in Ω,
          (-(∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j, c s j * (u (x, s) i * mixedSecond ψ i j x) -
            ∑ i, ∑ j, c s i * c s j * mixedSecond ψ i j x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = ∫ x in Ω,
        ((-(∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
          ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x)) +
          ∑ i, ∑ j, c s j * (u (x, s) i * mixedSecond ψ i j x)) -
          ∑ i, ∑ j, c s i * c s j * mixedSecond ψ i j x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x in Ω,
        ((-(∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
          ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x)) +
          ∑ i, ∑ j, c s j * (u (x, s) i * mixedSecond ψ i j x))) -
        ∫ x in Ω, ∑ i, ∑ j, c s i * c s j * mixedSecond ψ i j x := by
      have hsplit := integral_sub ((hA.neg.add hB).add hC) hD
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] using hsplit
    _ = -(∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
        (∫ x in Ω, ∑ i, ∑ j,
          c s i * (u (x, s) j * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          c s j * (u (x, s) i * mixedSecond ψ i j x)) -
        (∫ x in Ω, ∑ i, ∑ j,
          c s i * c s j * mixedSecond ψ i j x) := by
      have hABC := integral_add (hA.neg.add hB) hC
      have hAB := integral_add hA.neg hB
      have hABC' : (∫ x in Ω,
          ((-(∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x)) +
            ∑ i, ∑ j, c s j * (u (x, s) i * mixedSecond ψ i j x))) =
          (∫ x in Ω, (-(∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x))) +
            ∫ x in Ω, ∑ i, ∑ j,
              c s j * (u (x, s) i * mixedSecond ψ i j x) := by
        simpa only [Pi.add_apply, Pi.neg_apply] using hABC
      have hAB' : (∫ x in Ω, (-(∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j, c s i * (u (x, s) j * mixedSecond ψ i j x))) =
          (∫ x in Ω, -(∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x)) +
            ∫ x in Ω, ∑ i, ∑ j,
              c s i * (u (x, s) j * mixedSecond ψ i j x) := by
        simpa only [Pi.add_apply, Pi.neg_apply] using hAB
      rw [hABC', hAB']
      rw [integral_neg]
    _ = -(∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond ψ i j x) := by
      rw [hBzero, hCzero, hDzero]
      ring

theorem pressure_delta_p_centred_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x in Ω, p (x, s) * spatialLaplacian ψ x =
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUHat u c ((x, s) : ParabolicPoint) i j * mixedSecond ψ i j x) -
          ∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
  obtain ⟨Ω', _hΩ'open, _hψΩ₁, hψΩ', _hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hψc hψΩ hψc hψΩ
  have : IsFiniteMeasure (volume.restrict Ω') := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      _hΩ'compact.measure_lt_top).ne
  have hraw := pressure_slice_identity_ae hsol hψ hψc hψΩ
  have hdiv : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      ∫ x in Ω, ∑ j, u (x, s) j * mixedSecond ψ j i x = 0 := by
    rw [ae_all_iff]
    intro i
    have hd := divfree_slice_weak_of_suitable hsol
      (spatialDeriv ψ i) (contDiff_spatialDeriv_smooth hψ i)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i))
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hψΩ)
    filter_upwards [hd] with s hs
    simpa only [mixedSecond, spatialDeriv] using hs
  filter_upwards [hraw, hdiv, hLp] with s hraw_s hdiv_s hLp_s
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Ω') :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Ω') := huComp i |>.integrable (by norm_num)
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * g x) Ω volume := by
    exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
      (huInt i) hg hgc hgΩ).integrableOn
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * u (x, s) j * g x) Ω volume := by
    exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
      ((huComp i).integrable_mul (huComp j)) hg hgc hgΩ).integrableOn
  have hmixedCont (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hmixedC (i j : Fin 3) : HasCompactSupport (mixedSecond ψ i j) := by
    exact (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hmixedΩ (i j : Fin 3) : tsupport (mixedSecond ψ i j) ⊆ Ω' := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hψΩ')
  have hMixedInt (i j : Fin 3) : Integrable (mixedSecond ψ i j) volume := by
    exact (hmixedCont i j).continuous.integrable_of_hasCompactSupport (hmixedC i j)
  have hMixedOn (i j : Fin 3) : IntegrableOn (mixedSecond ψ i j) Ω volume :=
    (hMixedInt i j).integrableOn
  have hfinite {g : Fin 3 → Fin 3 → Vec3 → ℝ}
      (hg : ∀ i j, IntegrableOn (g i j) Ω volume) : IntegrableOn
      (fun x => ∑ i, ∑ j, g i j x) Ω volume := by
    change Integrable (∑ i, ∑ j, (fun x => g i j x)) (volume.restrict Ω)
    exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
        (fun j _ => hg i j))
  have hA : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * mixedSecond ψ i j x) Ω volume :=
    hfinite (fun i j => huuScalar (hmixedCont i j).continuous
      (hmixedC i j) (hmixedΩ i j))
  have hB : IntegrableOn (fun x => ∑ i, ∑ j,
      c s i * (u (x, s) j * mixedSecond ψ i j x)) Ω volume :=
    hfinite (fun i j => (huScalar (i := j) (hmixedCont i j).continuous
      (hmixedC i j) (hmixedΩ i j)).const_mul (c s i))
  have hC : IntegrableOn (fun x => ∑ i, ∑ j,
      c s j * (u (x, s) i * mixedSecond ψ i j x)) Ω volume :=
    hfinite (fun i j => (huScalar (i := i) (hmixedCont i j).continuous
      (hmixedC i j) (hmixedΩ i j)).const_mul (c s j))
  have hD : IntegrableOn (fun x => ∑ i, ∑ j,
      c s i * c s j * mixedSecond ψ i j x) Ω volume :=
    hfinite (fun i j => (hMixedOn i j).const_mul (c s i * c s j))
  have hdivSwap (i : Fin 3) : ∫ x in Ω, ∑ j,
      u (x, s) j * mixedSecond ψ i j x = 0 := by
    calc
      (∫ x in Ω, ∑ j, u (x, s) j * mixedSecond ψ i j x) =
          ∫ x in Ω, ∑ j, u (x, s) j * mixedSecond ψ j i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        apply Finset.sum_congr rfl
        intro j hj
        rw [mixedSecond_swap hψ i j x]
      _ = 0 := hdiv_s i
  have hmixedZero (i j : Fin 3) := @pressure_delta_p_centred_ae_hmixedZero_1 Ω f c ψ hψ hψc Ω'
    hΩ'Ω hmixedΩ hMixedInt i j
  have hBzero : ∫ x in Ω, ∑ i, ∑ j,
      c s i * (u (x, s) j * mixedSecond ψ i j x) = 0 := by
    calc
      (∫ x in Ω, ∑ i, ∑ j,
          c s i * (u (x, s) j * mixedSecond ψ i j x)) =
          ∑ i, ∫ x in Ω, ∑ j,
            c s i * (u (x, s) j * mixedSecond ψ i j x) := by
        simpa using integral_finsetSum (μ := volume.restrict Ω)
          (Finset.univ : Finset (Fin 3)) (fun i _ =>
            integrable_finsetSum' (Finset.univ : Finset (Fin 3))
              (fun j _ => (huScalar (i := j) (hmixedCont i j).continuous
                (hmixedC i j) (hmixedΩ i j)).const_mul (c s i)))
      _ = ∑ i, c s i * (∫ x in Ω, ∑ j,
          u (x, s) j * mixedSecond ψ i j x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (fun x => ∑ j, c s i *
            (u (x, s) j * mixedSecond ψ i j x)) =
            (fun x => c s i * ∑ j, u (x, s) j * mixedSecond ψ i j x) by
              funext x; rw [Finset.mul_sum]]
        rw [integral_const_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hdivSwap i, mul_zero]
  have hCzero := @pressure_delta_p_centred_ae_hCzero_2 Ω u c ψ Ω' s hdiv_s huScalar hmixedCont
    hmixedC hmixedΩ
  have hDzero : ∫ x in Ω, ∑ i, ∑ j,
      c s i * c s j * mixedSecond ψ i j x = 0 := by
    calc
      (∫ x in Ω, ∑ i, ∑ j,
          c s i * c s j * mixedSecond ψ i j x) =
          ∑ i, ∫ x in Ω, ∑ j,
            c s i * c s j * mixedSecond ψ i j x := by
        simpa using integral_finsetSum (μ := volume.restrict Ω)
          (Finset.univ : Finset (Fin 3)) (fun i _ =>
            integrable_finsetSum' (Finset.univ : Finset (Fin 3))
              (fun j _ => (hMixedOn i j).const_mul (c s i * c s j)))
      _ = ∑ i, ∑ j, (c s i * c s j) *
          (∫ x in Ω, mixedSecond ψ i j x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (fun x => ∑ j, c s i * c s j * mixedSecond ψ i j x) =
            (fun x => ∑ j, (c s i * c s j) * mixedSecond ψ i j x) by
              funext x; apply Finset.sum_congr rfl; intro j hj; ring]
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
        · intro j hj
          exact (hMixedOn i j).const_mul (c s i * c s j)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hmixedZero i j, mul_zero]
  have hcenter := @pressure_delta_p_centred_ae_hcenter_3 Ω u c ψ s hA hB hC hD hBzero hCzero hDzero
  rw [hraw_s, hcenter]

end CKN
