/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ParamExtension
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportSpatialBox
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Equation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Space-time vector test built from a spatial gradient and a temporal scalar test. -/
def pressureTest (ψ : Vec3 → ℝ) (θ : ℝ → ℝ) : Vec3 × ℝ → Vec3 :=
  fun z i => θ z.2 * spatialDeriv ψ i z.1

/-- The product test field on the ordinary product carrier. -/
def pressureTestProduct (ψ : Vec3 → ℝ) (θ : ℝ → ℝ) : Vec3 × ℝ → Vec3 :=
  pressureTest ψ θ

/-- The product test field viewed on the parabolic-point carrier. -/
def pressureTestParabolic (ψ : Vec3 → ℝ) (θ : ℝ → ℝ) :
    ParabolicPoint → Vec3 :=
  fun z => pressureTest ψ θ (z.1, z.2)

private theorem fderiv_zero_outside_tsupport {ψ : Vec3 → ℝ} {x : Vec3}
    (hx : x ∉ tsupport ψ) : fderiv ℝ ψ x = 0 := by
  have hev : ψ =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) :=
    Filter.eventually_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx)
      (fun y hy => by
        by_contra hne
        exact hy (subset_tsupport ψ (Function.mem_support.mpr hne)))
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const_apply]

private theorem spatialDeriv_zero_outside_tsupport {ψ : Vec3 → ℝ} {i : Fin 3}
    {x : Vec3} (hx : x ∉ tsupport ψ) : spatialDeriv ψ i x = 0 := by
  simp only [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx, zero_apply]

private theorem pressureTest_support_subset {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ ×ˢ tsupport θ) :
    pressureTest ψ θ z = 0 := by
  simp only [Set.mem_prod, not_and_or] at hz
  rcases hz with hzψ | hzθ
  · apply funext
    intro i
    simp only [pressureTest]
    rw [spatialDeriv_zero_outside_tsupport hzψ, mul_zero]
    rfl
  · apply funext
    intro i
    simp only [pressureTest]
    have hθzero : θ z.2 = 0 := by
      by_contra hne
      exact hzθ (subset_tsupport (f := θ) (Function.mem_support.mpr hne))
    rw [hθzero, zero_mul]
    rfl

theorem pressureTest_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    pressureTestProduct ψ θ ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (pressureTest ψ θ) := by
    apply contDiff_pi.mpr
    intro i
    exact (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff).mul
      (((contDiff_spatialDeriv_smooth hψ i).comp
        (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).of_le (by simp))
  have hsupport : tsupport (pressureTest ψ θ) ⊆ tsupport ψ ×ˢ tsupport θ := by
    apply closure_minimal
    · intro z hz
      exact by_contra fun hnot => hz (pressureTest_support_subset hnot)
    exact IsClosed.prod (isClosed_tsupport ψ) (isClosed_tsupport θ)
  have hcompact : IsCompact (tsupport (pressureTest ψ θ)) := by
    exact (hψc.isCompact.prod hθc.isCompact).of_isClosed_subset
      (isClosed_tsupport (pressureTest ψ θ)) hsupport
  refine ⟨hcont.of_le (by simp), hcompact, ?_⟩
  exact hsupport.trans (Set.prod_mono hψΩ hθI)

theorem pressureTest_spatialPartial
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z =
      θ z.2 * mixedSecond ψ j i z.1 := by
  unfold spatialPartial pressureTestParabolic pressureTest
  have hd : DifferentiableAt ℝ (spatialDeriv ψ i) z.1 :=
    (contDiff_spatialDeriv_smooth hψ i).differentiable (by simp) z.1
  rw [fderiv_const_mul hd (θ z.2)]
  simp only [spatialDeriv, mixedSecond, _root_.smul_apply, smul_eq_mul]

theorem pressureTest_timePartial
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (i : Fin 3) (z : ParabolicPoint) :
    timePartial (fun w => pressureTestParabolic ψ θ w i) z =
      (fderiv ℝ θ z.2) 1 * spatialDeriv ψ i z.1 := by
  unfold timePartial pressureTestParabolic pressureTest
  rw [fderiv_mul_const (hθ.differentiable (by simp) z.2)
    (spatialDeriv ψ i z.1)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

theorem mixedSecond_swap {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin 3) (x : Vec3) :
    mixedSecond ψ i j x = mixedSecond ψ j i x := by
  have hs : IsSymmSndFDerivAt ℝ ψ x :=
    ContDiffAt.isSymmSndFDerivAt (hψ.contDiffAt) (by norm_num)
  have hfc_cd : ContDiffAt ℝ (1 : ℕ∞) (fderiv ℝ ψ) x :=
    hψ.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)
  have hfc : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    hfc_cd.differentiableAt (by simp)
  have hci : DifferentiableAt ℝ (fun _ : Vec3 => basisVec i) x :=
    differentiableAt_const _
  have hcj : DifferentiableAt ℝ (fun _ : Vec3 => basisVec j) x :=
    differentiableAt_const _
  have hi := fderiv_clm_apply hfc hci
  have hj := fderiv_clm_apply hfc hcj
  have hi' := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hi
  have hj' := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hj
  change fderiv ℝ (spatialDeriv ψ i) x (basisVec j) = _ at hi'
  change fderiv ℝ (spatialDeriv ψ j) x (basisVec i) = _ at hj'
  change (fderiv ℝ (spatialDeriv ψ j) x) (basisVec i) =
    (fderiv ℝ (spatialDeriv ψ i) x) (basisVec j)
  rw [hj', hi']
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply] using hs.eq (basisVec i) (basisVec j)

theorem thirdDerivative_identity
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (x : Vec3) :
    spatialDeriv (mixedSecond ψ j i) j x =
      spatialDeriv (mixedSecond ψ j j) i x := by
  have hswap : mixedSecond ψ j i = mixedSecond ψ i j := by
    funext y
    exact mixedSecond_swap hψ j i y
  rw [hswap]
  change mixedSecond (spatialDeriv ψ j) j i x =
    mixedSecond (spatialDeriv ψ j) i j x
  exact mixedSecond_swap (contDiff_spatialDeriv_smooth hψ j) j i x

private theorem scalarProduct_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 → ℝ} {η : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ I) :
    (fun z : Vec3 × ℝ => ψ z.1 * η z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
  let g : Vec3 × ℝ → ℝ := fun z => ψ z.1 * η z.2
  have hsupport : tsupport g ⊆ tsupport ψ ×ˢ tsupport η := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      simp only [Set.mem_prod, not_and_or] at hnot
      rcases hnot with hψ' | hη'
      · exact hz (by simp [g, image_eq_zero_of_notMem_tsupport hψ'])
      · have hηzero : η z.2 = 0 := by
          by_contra hne
          exact hη' (subset_tsupport η (Function.mem_support.mpr hne))
        exact hz (by simp [g, hηzero])
    exact IsClosed.prod (isClosed_tsupport ψ) (isClosed_tsupport η)
  refine ⟨?_, ?_, hsupport.trans (Set.prod_mono hψΩ hηI)⟩
  · exact (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hη.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  · exact (hψc.isCompact.prod hηc.isCompact).of_isClosed_subset
      (isClosed_tsupport g) hsupport

private theorem tsupport_parabolic_eq_local (g : ParabolicPoint → ℝ) :
    tsupport g = parabolicHomeomorph ⁻¹' (tsupport fun q : Vec3 × ℝ => g q) := by
  have hsupp : Function.support g = parabolicHomeomorph ⁻¹'
      (Function.support fun q : Vec3 × ℝ => g q) := by
    ext z
    rw [Set.mem_preimage, Function.mem_support, Function.mem_support]
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

theorem pressure_time_integral_zero
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    IntegrableOn (fun z => ∑ i, u z i *
        timePartial (fun w => pressureTestParabolic ψ θ w i) z) (spaceTimeSet Ω I) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i *
        timePartial (fun w => pressureTestParabolic ψ θ w i) z = 0 := by
  let η : ℝ → ℝ := fun t => (fderiv ℝ θ t) 1
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    have h := hθ.contDiff_fderiv_apply (𝕜 := ℝ) (m := (⊤ : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t, (1 : ℝ))) :=
      contDiff_id.prodMk contDiff_const
    simpa [η, Function.comp_def] using h.comp hc
  have hηts : tsupport η ⊆ tsupport θ := tsupport_fderiv_apply_subset ℝ 1
  have hηc : HasCompactSupport η :=
    HasCompactSupport.of_support_subset_isCompact hθc.isCompact
      ((subset_tsupport η).trans hηts)
  have hηI : tsupport η ⊆ I := hηts.trans hθI
  let χ : ParabolicPoint → ℝ := fun z => ψ z.1 * η z.2
  have hχ : χ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
    exact scalarProduct_mem_spaceTimeTestFunction hψ hψc hψΩ hη hηc hηI
  obtain ⟨hχint, hχzero⟩ := hS2 χ hχ
  have hχeq : tsupport (fun q : Vec3 × ℝ => χ (q.1, q.2)) =
      tsupport ψ ×ˢ tsupport η := by
    have hsupp : Function.support (fun q : Vec3 × ℝ => χ (q.1, q.2)) =
        Function.support ψ ×ˢ Function.support η := by
      ext z
      simp only [χ, Function.mem_support, Set.mem_prod, mul_ne_zero_iff]
    rw [tsupport, tsupport, hsupp, closure_prod_eq]
    rfl
  have hχsupport : Function.support
      (fun z : ParabolicPoint => ∑ i, u z i * spatialPartial χ i z) ⊆
        tsupport χ := by
    rw [tsupport_parabolic_eq_local]
    change Function.support
      (fun z : ParabolicPoint => ∑ i, u z i * spatialPartial χ i z) ⊆
        parabolicHomeomorph ⁻¹' tsupport (fun q : Vec3 × ℝ => χ (q.1, q.2))
    rw [hχeq]
    intro z hz
    by_contra hnot
    have hnot' : parabolicHomeomorph z ∉ tsupport ψ ×ˢ tsupport η := hnot
    simp only [Set.mem_prod, not_and_or] at hnot'
    rcases hnot' with hψ' | hη'
    · apply hz
      have hψ'' : (z.1 : Vec3) ∉ tsupport ψ := by
        simpa only [parabolicHomeomorph_apply] using hψ'
      apply Finset.sum_eq_zero
      intro i hi
      have hzero : spatialPartial χ i z = 0 := by
        unfold spatialPartial
        rw [show (fun x : Vec3 => χ (x, z.2)) =
          (fun x => ψ x * η z.2) from rfl]
        rw [fderiv_mul_const (hψ.differentiable (by simp) z.1) (η z.2)]
        rw [fderiv_zero_outside_tsupport hψ'']
        simp
      rw [hzero, mul_zero]
    · have hη'' : z.2 ∉ tsupport η := by
        simpa only [parabolicHomeomorph_apply] using hη'
      have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hη''
      apply hz
      apply Finset.sum_eq_zero
      intro i hi
      have hspatial : spatialPartial χ i z = 0 := by
        unfold spatialPartial
        rw [show (fun x : Vec3 => χ (x, z.2)) = (fun _ => (0 : ℝ)) by
          funext x
          simp [χ, hzero], fderiv_const_apply]
        simp
      rw [hspatial, mul_zero]
  have hgInt : Integrable
      (fun z : ParabolicPoint => ∑ i, u z i * spatialPartial χ i z) volume :=
      (integrableOn_iff_integrable_of_support_subset hχsupport).mp hχint
  have hmain : ∫ z in spaceTimeSet Ω I,
      ∑ i, u z i * timePartial (fun w => pressureTestParabolic ψ θ w i) z =
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial χ i z := by
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [χ]
    simp only [pressureTest_timePartial hθ]
    unfold spatialPartial
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun x : Vec3 =>
      (fun w : Vec3 × ℝ => ψ w.1 * η w.2) (x, z.2)) =
        (fun x => ψ x * η z.2) from rfl,
      fderiv_mul_const (hψ.differentiable (by simp) z.1) (η z.2)]
    simp only [η, spatialDeriv, _root_.smul_apply, smul_eq_mul]
  have htimeInt : IntegrableOn (fun z => ∑ i, u z i *
      timePartial (fun w => pressureTestParabolic ψ θ w i) z) (spaceTimeSet Ω I) volume := by
    refine hgInt.integrableOn.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp [χ]
    simp only [pressureTest_timePartial hθ]
    unfold spatialPartial
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun x : Vec3 =>
      (fun w : Vec3 × ℝ => ψ w.1 * η w.2) (x, z.2)) =
        (fun x => ψ x * η z.2) from rfl,
      fderiv_mul_const (hψ.differentiable (by simp) z.1) (η z.2)]
    simp only [η, spatialDeriv, _root_.smul_apply, smul_eq_mul]
  exact ⟨htimeInt, hmain.trans hχzero⟩

private theorem local_restrict_isFiniteMeasure {Ω' : Set Vec3} {J : Set ℝ}
    (hΩ' : IsCompact (closure Ω')) (hJ : IsCompact (closure J)) :
    IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) := by
  let K : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' (closure Ω' ×ˢ closure J)
  have hK : IsCompact K :=
    parabolicHomeomorph.isCompact_preimage.2 (hΩ'.prod hJ)
  have hKtop : volume K < ⊤ := by
    change (volume : Measure (Vec3 × ℝ)) (closure Ω' ×ˢ closure J) < ⊤
    exact (hΩ'.prod hJ).measure_lt_top
  have hsub : spaceTimeSet Ω' J ⊆ K := by
    intro z hz
    change z.1 ∈ closure Ω' ∧ z.2 ∈ closure J
    exact ⟨subset_closure hz.1, subset_closure hz.2⟩
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono (μ := volume) hsub) hKtop).ne

private theorem local_memLp_two_of_energy
    {Ω' : Set Vec3} {J : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {hU : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J))}
    {hD : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J))}
    (henergy : (∫⁻ z in spaceTimeSet Ω' J,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp u 2 (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) := by
  have hu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_right le_rfl)) henergy
  have hD_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_left le_rfl)) henergy
  have hnorm {E : Type} [NormedAddCommGroup E] (v : ParabolicPoint → E)
      (hv : AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)))
      (hvlt : (∫⁻ z in spaceTimeSet Ω' J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
      Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
    have hvmeas : AEStronglyMeasurable
        (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict (spaceTimeSet Ω' J)) := hv.norm.pow 2
    have hvfin : ∫⁻ z in spaceTimeSet Ω' J,
        ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) ≠ ⊤ := by
      convert ne_of_lt hvlt using 1
      congr 1
      funext z
      calc
        ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) =
            ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
              norm_num [Real.rpow_natCast]
        _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
        _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
    exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
      (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp hvfin
  exact ⟨(memLp_two_iff_integrable_sq_norm hU).2 (hnorm u hU hu_lt),
    (memLp_two_iff_integrable_sq_norm hD).2 (hnorm Du hD hD_lt)⟩

private theorem support_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    Function.support (spatialDeriv ψ i) ⊆ tsupport ψ := by
  intro x hx
  by_contra hxt
  exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])

private theorem tsupport_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv ψ i) ⊆ tsupport ψ :=
  closure_minimal (support_spatialDeriv_subset i) (isClosed_tsupport ψ)

private theorem support_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond ψ i j) ⊆ tsupport ψ :=
  (support_spatialDeriv_subset (ψ := spatialDeriv ψ j) i).trans
    (tsupport_spatialDeriv_subset j)

private theorem tsupport_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond ψ i j) ⊆ tsupport ψ :=
  closure_minimal (support_mixedSecond_subset i j) (isClosed_tsupport ψ)

private theorem hasCompactSupport_spatialDeriv {ψ : Vec3 → ℝ} (hψc : HasCompactSupport ψ)
    (i : Fin 3) : HasCompactSupport (spatialDeriv ψ i) :=
  HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    (support_spatialDeriv_subset i)

private theorem hasCompactSupport_mixedSecond {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    HasCompactSupport (mixedSecond ψ i j) :=
  HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    (support_mixedSecond_subset i j)

private theorem q_memLp_is_integrable {q : ℝ} (hq : 5 / 2 < q)
    {f : ParabolicPoint → Vec3} {μ : Measure ParabolicPoint}
    [IsFiniteMeasure μ] (hf : MemLp f (ENNReal.ofReal q) μ) :
    Integrable f μ := by
  apply hf.integrable
  rw [ENNReal.one_le_ofReal]
  linarith only [hq]

private theorem exists_pressure_time_box {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : IsOpen I) (hIord : I.OrdConnected)
    (hθI : tsupport θ ⊆ I) (hθc : HasCompactSupport θ) :
    ∃ J : Set ℝ, IsOpen J ∧ tsupport θ ⊆ J ∧
      IsCompact (closure J) ∧ closure J ⊆ I ∧ J.OrdConnected := by
  let K : Set ℝ := tsupport θ
  have hK : IsCompact K := hθc.isCompact
  by_cases hKne : K.Nonempty
  · obtain ⟨a, ha⟩ := hK.exists_isLeast hKne
    obtain ⟨b, hb⟩ := hK.exists_isGreatest hKne
    obtain ⟨la, ua, hau, hlua⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hθI ha.1))
    obtain ⟨lb, ub, hbu, hlub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hθI hb.1))
    let l' : ℝ := (la + a) / 2
    let u' : ℝ := (b + ub) / 2
    have hll' : la < l' := by dsimp [l']; linarith only [hau.1]
    have hla' : l' < a := by dsimp [l']; linarith only [hau.1]
    have hbu' : b < u' := by dsimp [u']; linarith only [hbu.2]
    have huub' : u' < ub := by dsimp [u']; linarith only [hbu.2]
    have hlaI : l' ∈ I := hlua ⟨hll', hla'.trans hau.2⟩
    have hubI : u' ∈ I := hlub ⟨hbu.1.trans hbu', huub'⟩
    let J : Set ℝ := Ioo l' u'
    have hab : l' < u' := lt_of_lt_of_le hla' (ha.2 hb.1) |>.trans hbu'
    have hKJ : K ⊆ J := by
      intro t ht
      exact ⟨hla'.trans_le (ha.2 ht), (hb.2 ht).trans_lt hbu'⟩
    have hJsub : closure J ⊆ I := by
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact hIord.out hlaI hubI
    have hJcompact : IsCompact (closure J) := by
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact isCompact_Icc
    exact ⟨J, isOpen_Ioo, hKJ, hJcompact, hJsub, ordConnected_Ioo⟩
  · have hKeq : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    refine ⟨∅, isOpen_empty, ?_, ?_, ?_, ordConnected_empty⟩
    · change K ⊆ ∅
      rw [hKeq]
    · simpa only [closure_empty] using isCompact_empty
    · simpa only [closure_empty] using (empty_subset I)

private theorem theta_mul_spatial_zero
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hψΩ' : tsupport ψ ⊆ Ω') (hθJ : tsupport θ ⊆ J)
    {g : Vec3 → ℝ} (hg : ∀ x ∉ tsupport ψ, g x = 0)
    {z : ParabolicPoint} (hz : z ∉ spaceTimeSet Ω' J) :
    θ z.2 * g z.1 = 0 := by
  by_cases hx : z.1 ∈ Ω'
  · have ht : z.2 ∉ J := fun ht => hz ⟨hx, ht⟩
    have htθ : z.2 ∉ tsupport θ := fun htθ => ht (hθJ htθ)
    rw [image_eq_zero_of_notMem_tsupport htθ, zero_mul]
  · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ' hxψ)
    rw [hg z.1 hxψ, mul_zero]

private lemma pressure_test_terms_integrable_hpressOn_1 :
    ∀ {p : ParabolicPoint → ℝ} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        ∀ {θ : ℝ → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) θ →
            ∀ (Ω' : Set Vec3) (J : Set ℝ),
              let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
              Integrable p μ →
                (∀ (i j : Fin (3 : ℕ)),
                    ∃ (C : ℝ), ∀ (z : ParabolicPoint), ‖θ z.2 * mixedSecond ψ i j z.1‖ ≤ C) →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (z : ParabolicPoint) =>
                      p z *
                        ∑ i : Fin (3 : ℕ),
                          spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i)
                            i z)
                    (spaceTimeSet Ω' J) volume
    := by
  intro p ψ hψ θ hθ Ω' J μ hpInt hmixBound
  change Integrable (fun z => p z * ∑ i,
    spatialPartial (fun w => pressureTestParabolic ψ θ w i) i z) μ
  have hi (i : Fin 3) : Integrable
      (fun z => p z * spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) i z) μ := by
    have htermEq : (fun z => p z * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z) =
        (fun z => p z * (θ z.2 * mixedSecond ψ i i z.1)) := by
      funext z
      rw [pressureTest_spatialPartial hψ i i z]
    rw [htermEq]
    obtain ⟨C, hC⟩ := hmixBound i i
    have hmeas : AEStronglyMeasurable
        (fun z : ParabolicPoint => θ z.2 * mixedSecond ψ i i z.1) μ :=
      ((hθ.continuous.comp continuous_snd).mul
        ((contDiff_mixedSecond_smooth hψ i i).continuous.comp
          continuous_fst)).measurable.aestronglyMeasurable
    exact hpInt.mul_bdd hmeas
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
  have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => hi i)
  have heq : (fun z => p z * ∑ i, spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) i z) =
      ∑ i, (fun z => p z * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z) := by
    funext z
    simp only [Finset.sum_apply]
    rw [Finset.mul_sum]
  rw [heq]
  exact hs

private lemma pressure_test_terms_integrable_hconv_2 :
    ∀ {u : ParabolicPoint → Vec3} {ψ : Vec3 → ℝ} {θ : ℝ → ℝ} (Ω' : Set Vec3) (J : Set ℝ),
      (∀ (i j : Fin (3 : ℕ)) {z : ParabolicPoint},
          z ∉ spaceTimeSet Ω' J →
            spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z =
              (0 : ℝ)) →
        (∀ (i j : Fin (3 : ℕ)),
            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) =>
                u z i * u z j *
                  spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z)
              (spaceTimeSet Ω' J) volume) →
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  u z i * u z j *
                    spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z)
            volume
    := by
  intro u ψ θ Ω' J hspzero hconvOn
  have hi (i : Fin 3) : IntegrableOn
      (fun z => ∑ j, u z i * u z j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    have hj (j : Fin 3) := hconvOn i j
    have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => hj j)
    have heq : (fun z => ∑ j, u z i * u z j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) =
        ∑ j, (fun z => u z i * u z j * spatialPartial
          (fun w => pressureTestParabolic ψ θ w i) j z) := by
      funext z
      simp only [Finset.sum_apply]
    rw [heq]
    exact hs
  have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => hi i)
  have heq : (fun z => ∑ i, ∑ j, u z i * u z j * spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) j z) =
      ∑ i, (fun z => ∑ j, u z i * u z j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) := by
    funext z
    simp only [Finset.sum_apply]
  have hsumOn : IntegrableOn (fun z => ∑ i, ∑ j, u z i * u z j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    rw [heq]
    exact hs
  exact hsumOn.integrable_of_forall_notMem_eq_zero (by
    intro z hz
    refine Finset.sum_eq_zero ?_
    intro i hi
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [hspzero i j hz, mul_zero])

private lemma pressure_test_terms_integrable_hvisc_3 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {ψ : Vec3 → ℝ} {θ : ℝ → ℝ} (Ω' : Set Vec3)
      (J : Set ℝ),
      (∀ (i j : Fin (3 : ℕ)) {z : ParabolicPoint},
          z ∉ spaceTimeSet Ω' J →
            spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z =
              (0 : ℝ)) →
        (∀ (i j : Fin (3 : ℕ)),
            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) =>
                Du z i j *
                  spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z)
              (spaceTimeSet Ω' J) volume) →
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  Du z i j *
                    spatialPartial (fun (w : ParabolicPoint) => pressureTestParabolic ψ θ w i) j z)
            volume
    := by
  intro Du ψ θ Ω' J hspzero hviscOn
  have hi (i : Fin 3) : IntegrableOn
      (fun z => ∑ j, Du z i j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    have hj (j : Fin 3) := hviscOn i j
    have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => hj j)
    have heq : (fun z => ∑ j, Du z i j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) =
        ∑ j, (fun z => Du z i j * spatialPartial
          (fun w => pressureTestParabolic ψ θ w i) j z) := by
      funext z
      simp only [Finset.sum_apply]
    rw [heq]
    exact hs
  have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => hi i)
  have heq : (fun z => ∑ i, ∑ j, Du z i j * spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) j z) =
      ∑ i, (fun z => ∑ j, Du z i j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) := by
    funext z
    simp only [Finset.sum_apply]
  have hsumOn : IntegrableOn (fun z => ∑ i, ∑ j, Du z i j * spatialPartial
      (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    rw [heq]
    exact hs
  exact hsumOn.integrable_of_forall_notMem_eq_zero (by
    intro z hz
    refine Finset.sum_eq_zero ?_
    intro i hi
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [hspzero i j hz, mul_zero])

/-- The four spatial terms generated by a separated test field are integrable. -/
theorem pressure_test_terms_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    Integrable (fun z => ∑ i, ∑ j,
      u z i * u z j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) volume ∧
    Integrable (fun z => ∑ i, ∑ j,
      Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) volume ∧
    Integrable (fun z => p z * ∑ i,
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) i z) volume ∧
    Integrable (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i) volume := by
  rcases h with ⟨hΩ, hI, hIord, hq, _hf, hdata, _hS2, _hS3, _hS4⟩
  obtain ⟨Ω', hΩ'open, hψΩ', hΩ'compact, hΩ'Ω⟩ :=
    CKN.exists_spatial_box_of_tsupport_subset hΩ hψΩ hψc
  obtain ⟨J, _, hθJ, hJcompact, hJI, hJord⟩ :=
    exists_pressure_time_box hI hIord hθI hθc
  have hbox : localBox Ω I Ω' J :=
    ⟨hΩ'open, hΩ'compact, hΩ'Ω, hJord, hJcompact, hJI⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ := local_restrict_isFiniteMeasure hΩ'compact hJcompact
  obtain ⟨hu, hDu, _hpmeas, _hfmeas, _hsup, henergy, hp, hf, _hgrad⟩ :=
    hdata Ω' J hbox
  have hLp := local_memLp_two_of_energy (hU := hu) (hD := hDu) henergy
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hfInt : Integrable f μ := q_memLp_is_integrable hq hf
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hq]
  have huComp (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hDuComp (i j : Fin 3) : MemLp (fun z => Du z i j) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hfactorBound {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) : ∃ C : ℝ, ∀ z : ParabolicPoint,
      ‖θ z.2 * g z.1‖ ≤ C := by
    obtain ⟨Cθ, hCθ⟩ := hθc.exists_bound_of_continuous hθ.continuous
    obtain ⟨Cg, hCg⟩ := hgc.exists_bound_of_continuous hg
    let Cθ' := max Cθ 0
    let Cg' := max Cg 0
    refine ⟨Cθ' * Cg', ?_⟩
    intro z
    rw [norm_mul]
    have hθ' : ‖θ z.2‖ ≤ Cθ' := (hCθ z.2).trans (le_max_left _ _)
    have hg' : ‖g z.1‖ ≤ Cg' := (hCg z.1).trans (le_max_left _ _)
    exact mul_le_mul hθ' hg' (norm_nonneg _) (le_max_right _ _)
  have hmixBound (i j : Fin 3) : ∃ C : ℝ, ∀ z : ParabolicPoint,
      ‖θ z.2 * mixedSecond ψ i j z.1‖ ≤ C :=
    hfactorBound (contDiff_mixedSecond_smooth hψ i j).continuous
      (hasCompactSupport_mixedSecond hψc i j)
  have hderivBound (i : Fin 3) : ∃ C : ℝ, ∀ z : ParabolicPoint,
      ‖θ z.2 * spatialDeriv ψ i z.1‖ ≤ C :=
    hfactorBound (contDiff_spatialDeriv_smooth hψ i).continuous
      (hasCompactSupport_spatialDeriv hψc i)
  have hspzero (i j : Fin 3) {z : ParabolicPoint}
      (hz : z ∉ spaceTimeSet Ω' J) :
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z = 0 := by
    rw [pressureTest_spatialPartial hψ i j z]
    exact theta_mul_spatial_zero hψΩ' hθJ
      (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun hm => hx (tsupport_mixedSecond_subset j i hm))) hz
  have hforcezero (i : Fin 3) {z : ParabolicPoint}
      (hz : z ∉ spaceTimeSet Ω' J) : pressureTestParabolic ψ θ z i = 0 := by
    change θ z.2 * spatialDeriv ψ i z.1 = 0
    exact theta_mul_spatial_zero hψΩ' hθJ
      (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun hm => hx (tsupport_spatialDeriv_subset i hm))) hz
  have hconvOn (i j : Fin 3) : IntegrableOn
      (fun z => u z i * u z j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    change Integrable (fun z => u z i * u z j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) μ
    have htermEq : (fun z => u z i * u z j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) =
        (fun z => u z i * u z j * (θ z.2 * mixedSecond ψ j i z.1)) := by
      funext z
      rw [pressureTest_spatialPartial hψ i j z]
    rw [htermEq]
    obtain ⟨C, hC⟩ := hmixBound j i
    have hmeas : AEStronglyMeasurable
        (fun z : ParabolicPoint => θ z.2 * mixedSecond ψ j i z.1) μ :=
      ((hθ.continuous.comp continuous_snd).mul
        ((contDiff_mixedSecond_smooth hψ j i).continuous.comp
          continuous_fst)).measurable.aestronglyMeasurable
    exact ((huComp i).integrable_mul (huComp j)).mul_bdd hmeas
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have hviscOn (i j : Fin 3) : IntegrableOn
      (fun z => Du z i j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z)
      (spaceTimeSet Ω' J) volume := by
    change Integrable (fun z => Du z i j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) μ
    have htermEq : (fun z => Du z i j * spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) j z) =
        (fun z => Du z i j * (θ z.2 * mixedSecond ψ j i z.1)) := by
      funext z
      rw [pressureTest_spatialPartial hψ i j z]
    rw [htermEq]
    obtain ⟨C, hC⟩ := hmixBound j i
    have hmeas : AEStronglyMeasurable
        (fun z : ParabolicPoint => θ z.2 * mixedSecond ψ j i z.1) μ :=
      ((hθ.continuous.comp continuous_snd).mul
        ((contDiff_mixedSecond_smooth hψ j i).continuous.comp
          continuous_fst)).measurable.aestronglyMeasurable
    exact (hDuComp i j).integrable (by norm_num) |>.mul_bdd hmeas
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have hpressOn := @pressure_test_terms_integrable_hpressOn_1 p ψ hψ θ hθ Ω' J hpInt hmixBound
  have hforceOn (i : Fin 3) : IntegrableOn
      (fun z => f z i * pressureTestParabolic ψ θ z i)
      (spaceTimeSet Ω' J) volume := by
    change Integrable (fun z => f z i * (θ z.2 * spatialDeriv ψ i z.1)) μ
    obtain ⟨C, hC⟩ := hderivBound i
    have hmeas : AEStronglyMeasurable
        (fun z : ParabolicPoint => θ z.2 * spatialDeriv ψ i z.1) μ :=
      ((hθ.continuous.comp continuous_snd).mul
        ((contDiff_spatialDeriv_smooth hψ i).continuous.comp
          continuous_fst)).measurable.aestronglyMeasurable
    exact ((hfComp i).integrable hqE).mul_bdd hmeas
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
  have hconv := @pressure_test_terms_integrable_hconv_2 u ψ θ Ω' J hspzero hconvOn
  have hvisc := @pressure_test_terms_integrable_hvisc_3 Du ψ θ Ω' J hspzero hviscOn
  have hpress : Integrable
      (fun z => p z * ∑ i, spatialPartial
        (fun w => pressureTestParabolic ψ θ w i) i z) volume := by
    exact hpressOn.integrable_of_forall_notMem_eq_zero (by
      intro z hz
      have hzero : ∀ i : Fin 3, spatialPartial
          (fun w => pressureTestParabolic ψ θ w i) i z = 0 :=
        fun i => hspzero i i hz
      rw [Finset.sum_eq_zero (fun i _ => hzero i), mul_zero])
  have hforce : Integrable
      (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i) volume := by
    have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun i _ => hforceOn i)
    have heq : (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i) =
        ∑ i, (fun z => f z i * pressureTestParabolic ψ θ z i) := by
      funext z
      simp only [Finset.sum_apply]
    have hsumOn : IntegrableOn (fun z => ∑ i, f z i * pressureTestParabolic ψ θ z i)
        (spaceTimeSet Ω' J) volume := by
      rw [heq]
      exact hs
    exact hsumOn.integrable_of_forall_notMem_eq_zero (by
      intro z hz
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [hforcezero i hz, mul_zero])
  exact ⟨hconv, hvisc, hpress, hforce⟩

end CKN
