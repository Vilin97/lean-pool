/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmEndpoints
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A transported energy estimate on the unit torus.  The flow and material
derivative are explicit inputs, so the lemma is independent of the amplitude
normalization used to bound the source. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Ergodic

namespace AVenhance.Infra.Section4

theorem HmTransportedEnergy.hmEnergy_stDiv_eq_vecDiv
    {F : AVenhance.Infra.Section5.ST → Vec 2} {t : ℝ} {x : Vec 2}
    (hF : DifferentiableAt ℝ F (t, x)) :
    AVenhance.Infra.Section5.stDiv F (t, x) =
      AVenhance.vecDiv (fun y => F (t, y)) x := by
  let B : ℝ → Vec 2 → Vec 2 := fun s y => F (s, y)
  have hB : DifferentiableAt ℝ (Function.uncurry B) (t, x) := by
    simpa [B, Function.uncurry] using hF
  have hslice (v : Vec 2) :=
    AVenhance.Infra.Section5.fderiv_uncurry_vector_spatial
      (B := B) (t := t) (x := x) (v := v) hB
  have hcoord (i : Fin 2) :
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec i)) i =
        fderiv ℝ (fun y => B t y i) x (basisVec i) := by
    have h := congrArg (fun v : Vec 2 => v i) (hslice (basisVec i))
    rw [h, fderiv_apply (by
      have hc := hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
      simpa [B, Function.uncurry, Function.comp_def] using hc.differentiableAt) i]
    simp [ContinuousLinearMap.comp_apply]
  unfold AVenhance.Infra.Section5.stDiv AVenhance.vecDiv AVenhance.spaceGrad
  simp only [Fin.sum_univ_two]
  change (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 0)) 0 +
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 1)) 1 =
    (fderiv ℝ (fun y => B t y 0) x (basisVec 0)) +
      (fderiv ℝ (fun y => B t y 1) x (basisVec 1))
  rw [hcoord 0, hcoord 1]

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def HmTransportedEnergy.hmEnergyClosedCube : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem HmTransportedEnergy.hmEnergyClosedCube_compact : IsCompact
    HmTransportedEnergy.hmEnergyClosedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem HmTransportedEnergy.hmEnergy_unitCube_ae_eq_closedCube :
    AVenhance.unitCube =ᵐ[(volume : Measure (Vec 2))] HmTransportedEnergy.hmEnergyClosedCube := by
  simpa [volume_pi, AVenhance.unitCube, HmTransportedEnergy.hmEnergyClosedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc
      (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))

theorem HmTransportedEnergy.hmEnergy_cellAverage_eq_unitCube (f : Vec 2 → ℝ) :
    cellAverage f = ∫ x in AVenhance.unitCube, f x := by
  rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
  exact AVenhance.Infra.Torus.integral_unitCell_eq_unitCube f

instance HmTransportedEnergy.hmEnergy_uIcc_locallyCompact (a b : ℝ) :
    LocallyCompactSpace {x // x ∈ Set.uIcc a b} := by
  have hclosed : IsClosed (Set.uIcc a b) := isClosed_Icc
  exact hclosed.locallyCompactSpace

theorem HmTransportedEnergy.hmEnergy_slice_continuous {g : ℝ × Vec 2 → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    {s : ℝ} (hs : 0 < s) : Continuous (fun x => g (s, x)) := by
  exact hg.comp_continuous (continuous_const.prodMk continuous_id)
    (fun x => ⟨hs, mem_univ _⟩)

/-- The divergence in the material equation acts on `H_m` through
the periodic flux pairing. This identity avoids asking for a scalar
`L²_x` bound on `div d`; it is the form needed to combine `d` with the
space-time gradient estimate. -/
theorem hm_periodic_divergence_pairing
    {f : Vec 2 → ℝ} {V : Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    (hfper : IsZ2Periodic f)
    (hVper : ∀ i : Fin 2, IsZ2Periodic (fun x => V x i)) :
    (∫ x in AVenhance.unitCube, f x * AVenhance.vecDiv V x) =
      -∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad f x 0 * V x 0 +
          AVenhance.spaceGrad f x 1 * V x 1) := by
  let d0 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad (fun y => V y 0) x 0
  let d1 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad (fun y => V y 1) x 1
  let p0 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x 0 * V x 0
  let p1 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x 1 * V x 1
  have hV0 : ContDiff ℝ 1 (fun x => V x 0) :=
    (contDiff_pi.1 hV) 0 |>.of_le (by simp)
  have hV1 : ContDiff ℝ 1 (fun x => V x 1) :=
    (contDiff_pi.1 hV) 1 |>.of_le (by simp)
  have hparts0 := AVenhance.Infra.Classical.integral_unitCell_coord_ibp_real
    (i := 0) (hf.of_le (by simp)) hV0 hfper (hVper 0)
  have hparts1 := AVenhance.Infra.Classical.integral_unitCell_coord_ibp_real
    (i := 1) (hf.of_le (by simp)) hV1 hfper (hVper 1)
  have hd0 : Continuous d0 := by
    change Continuous (fun x => fderiv ℝ (fun x => V x 0) x
      (Homogenization.basisVec 0))
    exact (hV0.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd1 : Continuous d1 := by
    change Continuous (fun x => fderiv ℝ (fun x => V x 1) x
      (Homogenization.basisVec 1))
    exact (hV1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp0 : Continuous p0 := by
    dsimp [p0]
    exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (hV0.continuous)
  have hp1 : Continuous p1 := by
    dsimp [p1]
    exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (hV1.continuous)
  have hleft0 : IntegrableOn (fun x => f x * d0 x) AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
      (hf.continuous.mul hd0)
  have hleft1 : IntegrableOn (fun x => f x * d1 x) AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
      (hf.continuous.mul hd1)
  have hright0 : IntegrableOn p0 AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous hp0
  have hright1 : IntegrableOn p1 AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous hp1
  have hleft : IntegrableOn (fun x => f x * (d0 x + d1 x))
      AVenhance.unitCube := by
    exact AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
      (hf.continuous.mul (hd0.add hd1))
  have hright : IntegrableOn (fun x => p0 x + p1 x) AVenhance.unitCube :=
    hright0.add hright1
  have hdiv : ∀ x, AVenhance.vecDiv V x = d0 x + d1 x := by
    intro x
    simp [AVenhance.vecDiv, d0, d1, Fin.sum_univ_two]
  calc
    _ = ∫ x in AVenhance.unitCube, f x * (d0 x + d1 x) := by
      apply setIntegral_congr_fun (by
        change MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))
      intro x hx
      change f x * AVenhance.vecDiv V x = f x * (d0 x + d1 x)
      rw [hdiv x]
    _ = ∫ x in AVenhance.unitCube, (f x * d0 x + f x * d1 x) := by
      apply setIntegral_congr_fun (by
        change MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))
      intro x hx
      ring
    _ = (∫ x in AVenhance.unitCube, f x * d0 x) +
        ∫ x in AVenhance.unitCube, f x * d1 x := integral_add hleft0 hleft1
    _ = -(∫ x in AVenhance.unitCube, p0 x) -
        ∫ x in AVenhance.unitCube, p1 x := by
      dsimp [d0, d1, p0, p1]
      rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube,
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube] at hparts0 hparts1
      rw [hparts0, hparts1]
      ring
    _ = -∫ x in AVenhance.unitCube, (p0 x + p1 x) := by
      rw [integral_add hright0 hright1]
      ring
    _ = -∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad f x 0 * V x 0 +
          AVenhance.spaceGrad f x 1 * V x 1) := by
      simp [p0, p1]

/-- The scalar material source paired against `H_m` splits into its
regular source term and the dual pairing with its vector flux remainder. -/
theorem hm_periodic_source_pairing
    {f g : Vec 2 → ℝ} {V : Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 f) (hg : Continuous g) (hV : ContDiff ℝ 1 V)
    (hfper : IsZ2Periodic f)
    (hVper : ∀ i : Fin 2, IsZ2Periodic (fun x => V x i)) :
    (∫ x in AVenhance.unitCube,
      f x * (g x + AVenhance.vecDiv V x)) =
      (∫ x in AVenhance.unitCube, f x * g x) -
        ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x 0 * V x 0 +
            AVenhance.spaceGrad f x 1 * V x 1) := by
  let d0 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad (fun y => V y 0) x 0
  let d1 : Vec 2 → ℝ := fun x => AVenhance.spaceGrad (fun y => V y 1) x 1
  have hV0 : ContDiff ℝ 1 (fun x => V x 0) :=
    (contDiff_pi.1 hV) 0 |>.of_le (by simp)
  have hV1 : ContDiff ℝ 1 (fun x => V x 1) :=
    (contDiff_pi.1 hV) 1 |>.of_le (by simp)
  have hd0 : Continuous d0 := by
    change Continuous (fun x => fderiv ℝ (fun x => V x 0) x
      (Homogenization.basisVec 0))
    exact (hV0.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd1 : Continuous d1 := by
    change Continuous (fun x => fderiv ℝ (fun x => V x 1) x
      (Homogenization.basisVec 1))
    exact (hV1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdivCont : Continuous (AVenhance.vecDiv V) := by
    have hpoint : ∀ x, AVenhance.vecDiv V x = d0 x + d1 x := by
      intro x
      simp [AVenhance.vecDiv, d0, d1, Fin.sum_univ_two]
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [show AVenhance.vecDiv V = fun y => d0 y + d1 y by
      funext y
      exact hpoint y]
    exact (hd0.add hd1).continuousAt
  have hfgInt : IntegrableOn (fun x => f x * g x) AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
      (hf.continuous.mul hg)
  have hfdInt : IntegrableOn
      (fun x => f x * AVenhance.vecDiv V x) AVenhance.unitCube :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
      (hf.continuous.mul hdivCont)
  have hpair := hm_periodic_divergence_pairing hf hV hfper hVper
  calc
    _ = (∫ x in AVenhance.unitCube, f x * g x) +
        ∫ x in AVenhance.unitCube, f x * AVenhance.vecDiv V x := by
      rw [show (fun x : Vec 2 => f x * (g x + AVenhance.vecDiv V x)) =
        fun x => f x * g x + f x * AVenhance.vecDiv V x by
          funext x
          ring]
      exact integral_add hfgInt hfdInt
    _ = (∫ x in AVenhance.unitCube, f x * g x) -
        ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x 0 * V x 0 +
            AVenhance.spaceGrad f x 1 * V x 1) := by
      rw [hpair]
      ring

/-- The squared spatial norm is unchanged by a periodic volume-preserving
diffeomorphism of the flow. -/
theorem HmTransportedEnergy.hmEnergy_comp_integral_eq_at {F : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2) {t : ℝ}
    (hFper : IsZ2Periodic (F t)) :
    ∫ x in AVenhance.unitCube, (F t ((X t).toFun x)) ^ 2 =
      AVenhance.l2NormSq (F t) := by
  have hper : IsZPeriodic (fun x : Vec 2 => (F t x) ^ 2) := by
    intro x k
    exact congrArg (fun y : ℝ => y ^ 2) (hFper k x)
  have havg := cellAverage_comp_flow_eq (fun x : Vec 2 => (F t x) ^ 2)
    hper (X t)
  rw [HmTransportedEnergy.hmEnergy_cellAverage_eq_unitCube] at havg
  rw [HmTransportedEnergy.hmEnergy_cellAverage_eq_unitCube] at havg
  simpa [AVenhance.l2NormSq] using havg

theorem HmTransportedEnergy.hmEnergy_comp_integral_eq {F : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t)) (t : ℝ) :
    ∫ x in AVenhance.unitCube, (F t ((X t).toFun x)) ^ 2 =
      AVenhance.l2NormSq (F t) :=
  HmTransportedEnergy.hmEnergy_comp_integral_eq_at X (hFper t)

/-- The regular scalar source paired with a field. -/
def hmRegularPairing {F G : ℝ → Vec 2 → ℝ} (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, F t x * G t x

/-- The signed torus pairing of the gradient with its vector flux. -/
def hmFluxPairing {F : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    (t : ℝ) : ℝ :=
  -∫ x in AVenhance.unitCube,
    (AVenhance.spaceGrad (F t) x 0 * V t x 0 +
      AVenhance.spaceGrad (F t) x 1 * V t x 1)

/-- Along a volume-preserving flow, the actual material derivative
`G + div V` differentiates the transported squared norm by the regular
pairing plus the integrated gradient-flux pairing. No scalar `L²` estimate
on `div V` is used. -/
theorem hm_transported_energy_derivative_of_pairing
    {F G source : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (F t))
    (hSourcePer : ∀ t, 0 < t → IsZ2Periodic (source t))
    (hVper : ∀ t, 0 < t → ∀ i : Fin 2, IsZ2Periodic (fun x => V t x i))
    (hF : ∀ t, 0 < t → ContDiff ℝ 1 (F t))
    (hG : ∀ t, 0 < t → Continuous (G t))
    (hV : ∀ t, 0 < t → ContDiff ℝ 1 (V t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceSplit : ∀ t x, source t x = G t x + AVenhance.vecDiv (V t) x)
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => F s ((X s).toFun x))
        (source t ((X t).toFun x)) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => AVenhance.l2NormSq (F s))
      (2 * (hmRegularPairing (F := F) (G := G) t +
        hmFluxPairing (F := F) (V := V) t)) t := by
  let comp : ℝ × Vec 2 → ℝ := fun p => F p.1 ((X p.1).toFun p.2)
  let compSource : ℝ × Vec 2 → ℝ := fun p => source p.1 ((X p.1).toFun p.2)
  let energyComp : ℝ → ℝ := fun s => ∫ x in AVenhance.unitCube, comp (s, x) ^ 2
  let energyCompDeriv : ℝ → ℝ := fun s =>
    ∫ x in AVenhance.unitCube, 2 * comp (s, x) * compSource (s, x)
  let energy : ℝ → ℝ := fun s => AVenhance.l2NormSq (F s)
  have hCompSq : ContinuousOn (fun p => comp p ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := hComp.pow 2
  have hCompDeriv : ContinuousOn
      (fun p : ℝ × Vec 2 => 2 * comp p * compSource p)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    (continuousOn_const.mul hComp).mul hSourceComp
  have hCompDerivAt (s : ℝ) (hs : 0 < s) (x : Vec 2) :
      HasDerivAt (fun r => comp (r, x) ^ 2)
        (2 * comp (s, x) * compSource (s, x)) s := by
    have h := (hMaterial s hs x).pow 2
    have h' : HasDerivAt ((fun r => F r ((X r).toFun x)) ^ 2)
        (2 * F s ((X s).toFun x) * source s ((X s).toFun x)) s := by
      convert h using 1
      ring
    have hpow : ((fun r => F r ((X r).toFun x)) ^ 2) =
        fun r => (F r ((X r).toFun x)) ^ 2 := by
      funext r
      rfl
    rw [hpow] at h'
    simpa [comp, compSource] using h'
  have hEnergyCompDerivAt (s : ℝ) (hs : 0 < s) :
      HasDerivAt energyComp (energyCompDeriv s) s := by
    change HasDerivAt (fun r => ∫ x in AVenhance.unitCube, comp (r, x) ^ 2)
      (∫ x in AVenhance.unitCube,
        2 * comp (s, x) * compSource (s, x)) s
    exact AVenhance.Infra.Section5.LeftToShow.hasDerivAt_integral_unitCube
      hCompSq (fun r hr x => hCompDerivAt r hr x) hCompDeriv hs
  have hEnergyEq (s : ℝ) (hs : 0 < s) : energyComp s = energy s := by
    exact HmTransportedEnergy.hmEnergy_comp_integral_eq_at X (hFper s hs)
  have hEnergyDerivAt (s : ℝ) (hs : 0 < s) :
      HasDerivAt energy (energyCompDeriv s) s := by
    have hlocal : energy =ᶠ[𝓝 s] energyComp := by
      filter_upwards [IsOpen.mem_nhds
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))) hs] with r hr
      exact (hEnergyEq r hr).symm
    exact (hEnergyCompDerivAt s hs).congr_of_eventuallyEq hlocal
  have hprodPer : IsZ2Periodic (fun x => F t x * source t x) := by
    intro k x
    change F t (x + AVenhance.latticeShift k) *
        source t (x + AVenhance.latticeShift k) = F t x * source t x
    rw [hFper t ht k x, hSourcePer t ht k x]
  have hprodPerZ : IsZPeriodic (fun x => F t x * source t x) := by
    intro x k
    exact hprodPer k x
  have hflowPair :
      (∫ x in AVenhance.unitCube, comp (t, x) * compSource (t, x)) =
        ∫ x in AVenhance.unitCube, F t x * source t x := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          F t ((X t).toFun x) * source t ((X t).toFun x) := by rfl
      _ = cellAverage (fun x =>
          F t ((X t).toFun x) * source t ((X t).toFun x)) :=
        (HmTransportedEnergy.hmEnergy_cellAverage_eq_unitCube _).symm
      _ = cellAverage (fun x => F t x * source t x) := by
        exact cellAverage_comp_flow_eq (fun x => F t x * source t x)
          hprodPerZ (X t)
      _ = ∫ x in AVenhance.unitCube, F t x * source t x :=
        HmTransportedEnergy.hmEnergy_cellAverage_eq_unitCube _
  have hsourceFun : source t = fun x => G t x + AVenhance.vecDiv (V t) x :=
    funext (hSourceSplit t)
  have hspacePair := hm_periodic_source_pairing
    (hF t ht) (hG t ht) (hV t ht) (hFper t ht) (hVper t ht)
  have hEulerPair :
      (∫ x in AVenhance.unitCube, F t x * source t x) =
        hmRegularPairing (F := F) (G := G) t +
          hmFluxPairing (F := F) (V := V) t := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          F t x * (G t x + AVenhance.vecDiv (V t) x) := by
        rw [hsourceFun]
      _ = _ := by
        rw [hspacePair]
        simp [hmRegularPairing, hmFluxPairing]
        ring
  have hderivPair : energyCompDeriv t =
      2 * (hmRegularPairing (F := F) (G := G) t +
        hmFluxPairing (F := F) (V := V) t) := by
    change (∫ x in AVenhance.unitCube,
      2 * comp (t, x) * compSource (t, x)) = _
    rw [show (fun x : Vec 2 => 2 * comp (t, x) * compSource (t, x)) =
      fun x => 2 * (comp (t, x) * compSource (t, x)) by funext x; ring,
      integral_const_mul, hflowPair, hEulerPair]
  have h := hEnergyDerivAt t ht
  rw [hderivPair] at h
  simpa [energy] using h

/-- Joint continuity along a periodic measure-preserving flow makes the
spatial L² norm continuous in time on every compact interval bounded away
from zero. -/
theorem hm_transported_norm_continuous_of_joint
    {F : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (F t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => Real.sqrt (AVenhance.l2NormSq (F t)))
      (Set.Icc a b) := by
  let K : Set ℝ := Set.Icc a b
  let comp : ℝ × Vec 2 → ℝ := fun p => F p.1 ((X p.1).toFun p.2)
  have hKprod : K ×ˢ (Set.univ : Set (Vec 2)) ⊆
      Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
    intro p hp
    exact ⟨lt_of_lt_of_le ha hp.1.1, mem_univ _⟩
  have hjoint : Continuous (fun p : K × Vec 2 => comp (p.1.1, p.2)) := by
    have hmap : Continuous (fun p : K × Vec 2 => (p.1.1, p.2)) := by fun_prop
    exact (hComp.mono hKprod).comp_continuous hmap
      (fun p => ⟨p.1.2, mem_univ _⟩)
  have hparam : Continuous (fun t : K =>
      ∫ x in HmTransportedEnergy.hmEnergyClosedCube, comp (t.1, x) ^ 2) :=
    continuous_parametric_integral_of_continuous
      (f := fun (t : K) (x : Vec 2) => comp (t.1, x) ^ 2)
      (by
        change Continuous (fun p : K × Vec 2 => comp (p.1.1, p.2) ^ 2)
        exact hjoint.pow 2)
      HmTransportedEnergy.hmEnergyClosedCube_compact
  have henergyEq (t : K) :
      (∫ x in HmTransportedEnergy.hmEnergyClosedCube, comp (t.1, x) ^ 2) =
        AVenhance.l2NormSq (F t.1) := by
    have htpos : 0 < t.1 := lt_of_lt_of_le ha t.2.1
    calc
      _ = ∫ x in AVenhance.unitCube, comp (t.1, x) ^ 2 := by
        exact setIntegral_congr_set HmTransportedEnergy.hmEnergy_unitCube_ae_eq_closedCube.symm
      _ = AVenhance.l2NormSq (F t.1) :=
        HmTransportedEnergy.hmEnergy_comp_integral_eq_at X (hFper t.1 htpos)
  have henergyCont : ContinuousOn
      (fun t => AVenhance.l2NormSq (F t)) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : K => AVenhance.l2NormSq (F t.1))
    have heq : (fun t : K =>
        ∫ x in HmTransportedEnergy.hmEnergyClosedCube, comp (t.1, x) ^ 2) =
          fun t => AVenhance.l2NormSq (F t.1) := by
      funext t
      exact henergyEq t
    rw [← heq]
    exact hparam
  exact Real.continuous_sqrt.comp_continuousOn henergyCont

/-- A transported field with zero data at the left end of an interval
satisfies the standard energy FTC bound.  `source` is its actual material
derivative.  The proof uses torus volume preservation, Cauchy--Schwarz, and
FTC; `H` and `D` are abstract amplitudes and do not mention `theta₀` or a time
supremum of the underlying solution. -/
theorem hm_transported_energy_ftc
    {F source : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t))
    (hSourcePer : ∀ t, IsZ2Periodic (source t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => F s ((X s).toFun x))
        (source t ((X t).toFun x)) t)
    {a t H D : ℝ} (ha : 0 < a) (ht : 0 < t) (hH : 0 ≤ H)
    (hzero : F a = 0)
    (hFbound : ∀ s ∈ Set.uIcc a t,
      Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H)
    (hSourceBound : ∀ s ∈ Set.uIcc a t,
      Real.sqrt (AVenhance.l2NormSq (source s)) ≤ D) :
    (Real.sqrt (AVenhance.l2NormSq (F t))) ^ 2 ≤
      2 * |t - a| * D * H := by
  let comp : ℝ × Vec 2 → ℝ := fun p => F p.1 ((X p.1).toFun p.2)
  let compSource : ℝ × Vec 2 → ℝ := fun p => source p.1 ((X p.1).toFun p.2)
  let energyComp : ℝ → ℝ := fun s => ∫ x in AVenhance.unitCube, comp (s, x) ^ 2
  let energyCompDeriv : ℝ → ℝ := fun s =>
    ∫ x in AVenhance.unitCube, 2 * comp (s, x) * compSource (s, x)
  let energy : ℝ → ℝ := fun s => AVenhance.l2NormSq (F s)
  have hCompSq : ContinuousOn (fun p => comp p ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := hComp.pow 2
  have hCompDeriv : ContinuousOn
      (fun p : ℝ × Vec 2 => 2 * comp p * compSource p)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    (continuousOn_const.mul hComp).mul hSourceComp
  have hEnergyEq (s : ℝ) : energyComp s = energy s := by
    exact HmTransportedEnergy.hmEnergy_comp_integral_eq X hFper s
  have hCompDerivAt (s : ℝ) (hs : 0 < s) (x : Vec 2) :
      HasDerivAt (fun r => comp (r, x) ^ 2)
        (2 * comp (s, x) * compSource (s, x)) s := by
    have h := (hMaterial s hs x).pow 2
    change HasDerivAt ((fun r => F r ((X r).toFun x)) ^ 2)
      (2 * F s ((X s).toFun x) * source s ((X s).toFun x)) s
    convert h using 1; ring
  have hEnergyCompDerivAt (s : ℝ) (hs : 0 < s) :
      HasDerivAt energyComp (energyCompDeriv s) s := by
    change HasDerivAt (fun r => ∫ x in AVenhance.unitCube, comp (r, x) ^ 2)
      (∫ x in AVenhance.unitCube, 2 * comp (s, x) * compSource (s, x)) s
    exact AVenhance.Infra.Section5.LeftToShow.hasDerivAt_integral_unitCube
      hCompSq (fun r hr x => hCompDerivAt r hr x) hCompDeriv hs
  have hEnergyDerivAt (s : ℝ) (hs : 0 < s) :
      HasDerivAt energy (energyCompDeriv s) s := by
    have hlocal : energy =ᶠ[𝓝 s] energyComp := by
      filter_upwards [IsOpen.mem_nhds (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))) hs]
        with r hr
      exact (hEnergyEq r).symm
    exact (hEnergyCompDerivAt s hs).congr_of_eventuallyEq hlocal
  have hKcompact : IsCompact (Set.uIcc a t) := isCompact_uIcc
  have hKpos : Set.uIcc a t ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rcases (Set.mem_uIcc.mp hs) with hs' | hs'
    · exact lt_of_lt_of_le ha hs'.1
    · exact lt_of_lt_of_le ht hs'.1
  have hprimeContOn : ContinuousOn energyCompDeriv (Set.uIcc a t) := by
    let K : Set ℝ := Set.uIcc a t
    have hKprod : K ×ˢ (Set.univ : Set (Vec 2)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) :=
      Set.prod_mono hKpos (Set.Subset.refl _)
    have hg : Continuous
        (fun p : K × Vec 2 => 2 * comp (p.1.1, p.2) * compSource (p.1.1, p.2)) := by
      have hmap : Continuous (fun p : K × Vec 2 => (p.1.1, p.2)) := by fun_prop
      exact (hCompDeriv.mono hKprod).comp_continuous hmap
        (fun p => ⟨p.1.2, mem_univ _⟩)
    have hclosed : IsCompact HmTransportedEnergy.hmEnergyClosedCube :=
        HmTransportedEnergy.hmEnergyClosedCube_compact
    have hparam : Continuous (fun s : K =>
        ∫ x in HmTransportedEnergy.hmEnergyClosedCube,
          2 * comp (s.1, x) * compSource (s.1, x)) :=
      continuous_parametric_integral_of_continuous
        (f := fun (s : K) (x : Vec 2) =>
          2 * comp (s.1, x) * compSource (s.1, x)) hg hclosed
    have heq (s : K) :
        (∫ x in AVenhance.unitCube, 2 * comp (s.1, x) * compSource (s.1, x)) =
          ∫ x in HmTransportedEnergy.hmEnergyClosedCube, 2 * comp (s.1, x) * compSource (s.1, x)
              := by
      exact setIntegral_congr_set HmTransportedEnergy.hmEnergy_unitCube_ae_eq_closedCube
    have heqFun :
        (fun s : K => energyCompDeriv s.1) = fun s =>
          ∫ x in HmTransportedEnergy.hmEnergyClosedCube, 2 * comp (s.1, x) * compSource (s.1, x)
              := by
      funext s
      exact heq s
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun s : K => energyCompDeriv s.1)
    rw [heqFun]
    exact hparam
  have hprimeIntegrable : IntervalIntegrable energyCompDeriv volume a t :=
    hprimeContOn.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hEnergyDerivAt s (by
      rcases (Set.mem_uIcc.mp hs) with hs' | hs'
      · exact lt_of_lt_of_le ha hs'.1
      · exact lt_of_lt_of_le ht hs'.1)) hprimeIntegrable
  have hbase : energy a = 0 := by
    simp [energy, hzero, AVenhance.l2NormSq]
  have hderivBound : ∀ s ∈ Set.uIcc a t,
      |energyCompDeriv s| ≤ 2 * H * D := by
    intro s hs
    have hspos := hKpos hs
    have hFc := HmTransportedEnergy.hmEnergy_slice_continuous hComp hspos
    have hRc := HmTransportedEnergy.hmEnergy_slice_continuous hSourceComp hspos
    have hFi : IntegrableOn (fun x => comp (s, x) ^ 2) AVenhance.unitCube :=
      AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hFc.pow 2)
    have hRi : IntegrableOn (fun x => compSource (s, x) ^ 2) AVenhance.unitCube :=
      AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hRc.pow 2)
    have hFRi : IntegrableOn (fun x => comp (s, x) * compSource (s, x))
        AVenhance.unitCube :=
      AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
        (hFc.mul hRc)
    have hFi' : Integrable (fun x => comp (s, x) ^ 2)
        (volume.restrict AVenhance.unitCube) := by
      simpa only [IntegrableOn] using hFi
    have hRi' : Integrable (fun x => compSource (s, x) ^ 2)
        (volume.restrict AVenhance.unitCube) := by
      simpa only [IntegrableOn] using hRi
    have hFRi' : Integrable (fun x => comp (s, x) * compSource (s, x))
        (volume.restrict AVenhance.unitCube) := by
      simpa only [IntegrableOn] using hFRi
    have hcs := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
      hFi' hRi' hFRi'
    have hFiNeg : Integrable (fun x => (-comp (s, x)) ^ 2)
        (volume.restrict AVenhance.unitCube) := by
      simpa only [neg_sq] using hFi'
    have hFRiNeg : Integrable (fun x => -comp (s, x) * compSource (s, x))
        (volume.restrict AVenhance.unitCube) := by
      have hneg : IntegrableOn (fun x => -comp (s, x) * compSource (s, x))
          AVenhance.unitCube :=
        AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
          (hFc.neg.mul hRc)
      simpa only [IntegrableOn] using hneg
    have hcsNeg := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
      (f := fun x => -comp (s, x)) (g := fun x => compSource (s, x))
      hFiNeg hRi' hFRiNeg
    have hcompF := HmTransportedEnergy.hmEnergy_comp_integral_eq X hFper s
    have hcompR := HmTransportedEnergy.hmEnergy_comp_integral_eq (F := source) X hSourcePer s
    have hFs : Real.sqrt (∫ x in AVenhance.unitCube, comp (s, x) ^ 2) ≤ H := by
      rw [hcompF]
      exact hFbound s hs
    have hRs : Real.sqrt (∫ x in AVenhance.unitCube, compSource (s, x) ^ 2) ≤ D := by
      rw [hcompR]
      exact hSourceBound s hs
    have hprod :
        Real.sqrt (∫ x in AVenhance.unitCube, comp (s, x) ^ 2) *
          Real.sqrt (∫ x in AVenhance.unitCube, compSource (s, x) ^ 2) ≤ H * D :=
      mul_le_mul hFs hRs (Real.sqrt_nonneg _) hH
    have hcross : |∫ x in AVenhance.unitCube,
        comp (s, x) * compSource (s, x)| ≤ H * D := by
      have hcrossLo : -(H * D) ≤ ∫ x in AVenhance.unitCube,
          comp (s, x) * compSource (s, x) := by
        have hnegInt :
            (∫ x in AVenhance.unitCube, -comp (s, x) * compSource (s, x)) =
              -(∫ x in AVenhance.unitCube, comp (s, x) * compSource (s, x)) := by
          rw [show (fun x : Vec 2 => -comp (s, x) * compSource (s, x)) =
              fun x => -(comp (s, x) * compSource (s, x)) by
                funext x; ring,
            integral_neg]
        have h := hcsNeg
        rw [hnegInt] at h
        have hsqrt :
            Real.sqrt (∫ x in AVenhance.unitCube, (-comp (s, x)) ^ 2) *
              Real.sqrt (∫ x in AVenhance.unitCube, compSource (s, x) ^ 2) ≤ H * D := by
          simpa only [neg_sq] using hprod
        linarith
      have hcrossHi : ∫ x in AVenhance.unitCube,
          comp (s, x) * compSource (s, x) ≤ H * D := hcs.trans hprod
      exact abs_le.mpr ⟨hcrossLo, hcrossHi⟩
    have heqD : energyCompDeriv s =
        2 * (∫ x in AVenhance.unitCube,
          comp (s, x) * compSource (s, x)) := by
      change (∫ x in AVenhance.unitCube,
        2 * comp (s, x) * compSource (s, x)) = _
      rw [show (fun x : Vec 2 => 2 * comp (s, x) * compSource (s, x)) =
          fun x => 2 * (comp (s, x) * compSource (s, x)) by
            funext x; ring]
      exact integral_const_mul _ _
    rw [heqD, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul := mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [hmul]
  have hFTC' : energy t - energy a = ∫ s in a..t, energyCompDeriv s := hFTC.symm
  have hnormInt := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := t) (f := energyCompDeriv) (fun s hs => by
      have hb := hderivBound s (Set.uIoc_subset_uIcc hs)
      simpa [Real.norm_eq_abs] using hb)
  have htEnergy : energy t ≤ 2 * |t - a| * H * D := by
    have hnorm : |energy t| ≤ 2 * H * D * |t - a| := by
      have hrewrite : energy t = ∫ s in a..t, energyCompDeriv s := by
        calc
          energy t = energy t - energy a := by rw [hbase]; ring
          _ = ∫ s in a..t, energyCompDeriv s := hFTC'
      calc
        |energy t| = ‖∫ s in a..t, energyCompDeriv s‖ := by
          rw [hrewrite, Real.norm_eq_abs]
        _ ≤ 2 * H * D * |t - a| := hnormInt
    have henergyNonneg : 0 ≤ energy t := by
      dsimp [energy, AVenhance.l2NormSq]
      exact integral_nonneg fun _ => sq_nonneg _
    have habs : energy t ≤ |energy t| := le_abs_self _
    nlinarith [hnorm]
  have hsqrtSq : (Real.sqrt (AVenhance.l2NormSq (F t))) ^ 2 = energy t := by
    dsimp [energy]
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [hsqrtSq]
  calc
    energy t ≤ 2 * |t - a| * H * D := htEnergy
    _ = 2 * |t - a| * D * H := by ring

/-- A maximum on a compact interval replaces the separate time-uniform norm
and attainment premises in the transport absorption argument. -/
theorem hm_transport_cell_sup_le_of_continuous
    {f : ℝ → ℝ} {cell : Set ℝ} {H L D : ℝ}
    (hnonneg : ∀ t ∈ cell, 0 ≤ f t)
    (hLD : 0 ≤ L * D)
    (hFTC : ∀ t ∈ cell, f t ^ 2 ≤ 2 * L * D * H)
    (hH : ∃ t₀ ∈ cell, H = f t₀ ∧ ∀ t ∈ cell, f t ≤ f t₀) :
    ∀ t ∈ cell, f t ≤ 2 * L * D := by
  obtain ⟨t₀, ht₀, hHval, hmax⟩ := hH
  have hHnonneg : 0 ≤ H := by rw [hHval]; exact hnonneg t₀ ht₀
  have hupper : ∀ t ∈ cell, f t ≤ H := by
    intro t ht
    rw [hHval]
    exact hmax t ht
  by_cases hHzero : H = 0
  · intro t ht
    have hle := hupper t ht
    have hge := hnonneg t ht
    rw [hHzero] at hle
    have hzero : f t = 0 := le_antisymm hle hge
    rw [hzero]
    nlinarith [hLD]
  · have hHpos : 0 < H := lt_of_le_of_ne hHnonneg (Ne.symm hHzero)
    have hHFTC : H ^ 2 ≤ 2 * L * D * H := by
      rw [hHval]
      have h := hFTC t₀ ht₀
      rw [hHval] at h
      exact h
    have habsorb : H ≤ 2 * L * D := by
      have hdiv := div_le_div_of_nonneg_right hHFTC (le_of_lt hHpos)
      have hleft : H ^ 2 / H = H := by field_simp [hHpos.ne']
      have hright : (2 * L * D * H) / H = 2 * L * D := by
        field_simp [hHpos.ne']
      rw [hleft, hright] at hdiv
      exact hdiv
    intro t ht
    exact (hupper t ht).trans habsorb

/-- Uniform-in-time version of the transported energy estimate. The maximum
is taken internally on the compact interval, while `D` and the field scale
remain abstract parameters. -/
theorem hm_transported_energy_uniform
    {F source : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t))
    (hSourcePer : ∀ t, IsZ2Periodic (source t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => F s ((X s).toFun x))
        (source t ((X t).toFun x)) t)
    {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D)
    (hzero : F a = 0)
    (hNormCont : ContinuousOn
      (fun t => Real.sqrt (AVenhance.l2NormSq (F t))) (Set.Icc a b))
    (hSourceBound : ∀ s ∈ Set.Icc a b,
      Real.sqrt (AVenhance.l2NormSq (source s)) ≤ D) :
    ∀ t ∈ Set.Icc a b,
      Real.sqrt (AVenhance.l2NormSq (F t)) ≤ 2 * (b - a) * D := by
  let f : ℝ → ℝ := fun s => Real.sqrt (AVenhance.l2NormSq (F s))
  have haCell : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hcell : (Set.Icc a b).Nonempty := ⟨a, haCell⟩
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hNormCont' : ContinuousOn f (Set.Icc a b) := by
    simpa [f] using hNormCont
  obtain ⟨t₀, ht₀, hmax⟩ := hcompact.exists_isMaxOn hcell hNormCont'
  let H : ℝ := f t₀
  have hnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ f s := by
    intro s hs
    exact Real.sqrt_nonneg _
  have hFbound : ∀ r ∈ Set.Icc a b, f r ≤ H := by
    intro r hr
    exact hmax hr
  have hHnonneg : 0 ≤ H := by
    apply le_trans (Real.sqrt_nonneg _)
    exact hFbound a haCell
  have hFTC : ∀ s ∈ Set.Icc a b, f s ^ 2 ≤ 2 * (b - a) * D * H := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hFbound' : ∀ r ∈ Set.uIcc a s, f r ≤ H := by
      intro r hr
      have hrIcc : r ∈ Set.Icc a b := by
        rw [Set.mem_uIcc] at hr
        rcases hr with hr | hr
        · exact ⟨hr.1, le_trans hr.2 hs.2⟩
        · exact ⟨le_trans hs.1 hr.1, le_trans hr.2 hab⟩
      exact hFbound r hrIcc
    have hSourceBound' : ∀ r ∈ Set.uIcc a s,
        Real.sqrt (AVenhance.l2NormSq (source r)) ≤ D := by
      intro r hr
      have hrIcc : r ∈ Set.Icc a b := by
        rw [Set.mem_uIcc] at hr
        rcases hr with hr | hr
        · exact ⟨hr.1, le_trans hr.2 hs.2⟩
        · exact ⟨le_trans hs.1 hr.1, le_trans hr.2 hab⟩
      exact hSourceBound r hrIcc
    have henergy := hm_transported_energy_ftc X hFper hSourcePer
      hComp hSourceComp hMaterial ha hspos hHnonneg hzero hFbound' hSourceBound'
    have htime : |s - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2 a
    have hcoeff : 0 ≤ 2 * D * H := by positivity
    have htime' := mul_le_mul_of_nonneg_right htime hcoeff
    change f s ^ 2 ≤ 2 * (b - a) * D * H
    calc
      f s ^ 2 = (Real.sqrt (AVenhance.l2NormSq (F s))) ^ 2 := rfl
      _ ≤ 2 * |s - a| * D * H := henergy
      _ = |s - a| * (2 * D * H) := by ring
      _ ≤ (b - a) * (2 * D * H) := htime'
      _ = 2 * (b - a) * D * H := by ring
  have hbound := hm_transport_cell_sup_le_of_continuous
    hnonneg (mul_nonneg (sub_nonneg.mpr hab) hD)
    hFTC ⟨t₀, ht₀, rfl, fun s hs => hmax hs⟩
  intro s hs
  exact hbound s hs

/-- Maximum absorption for an inequality `f² ≤ A H + B`, with nonnegative
coefficients. -/
theorem hm_transport_cell_sup_le_of_quadraticCoefficients
    {f : ℝ → ℝ} {cell : Set ℝ} {H A B : ℝ}
    (hnonneg : ∀ t ∈ cell, 0 ≤ f t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hFTC : ∀ t ∈ cell, f t ^ 2 ≤ A * H + B)
    (hmax : ∃ t₀ ∈ cell, H = f t₀ ∧ ∀ t ∈ cell, f t ≤ f t₀) :
    ∀ t ∈ cell, f t ≤ A + Real.sqrt B := by
  obtain ⟨t₀, ht₀, hHval, hmax'⟩ := hmax
  have hHnonneg : 0 ≤ H := by rw [hHval]; exact hnonneg t₀ ht₀
  have hHquad : H ^ 2 ≤ A * H + B := by
    have h := hFTC t₀ ht₀
    rw [← hHval] at h
    exact h
  have hroot : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hHbound : H ≤ A + Real.sqrt B := by
    by_contra hnot
    have hstrict : A + Real.sqrt B < H := lt_of_not_ge hnot
    have hHpos : 0 < H := by linarith
    have hrootLe : Real.sqrt B ≤ H := by linarith
    have hgap : Real.sqrt B < H - A := by linarith
    have hprod₁ := mul_le_mul_of_nonneg_right hrootLe hroot
    have hprod₂ := mul_lt_mul_of_pos_left hgap hHpos
    have hprod : B < H * (H - A) := by
      calc
        B = Real.sqrt B * Real.sqrt B := by
          nlinarith [Real.sq_sqrt hB]
        _ ≤ H * Real.sqrt B := hprod₁
        _ < H * (H - A) := hprod₂
    nlinarith [hHquad]
  intro t ht
  have hpoint : f t ≤ H := by rw [hHval]; exact hmax' t ht
  exact hpoint.trans hHbound

/-- FTC for a transported energy after the spatial integration by parts has
split its derivative into the regular pairing and the flux pairing. The two
integrated bounds stay separate: the first carries the factor `H` absorbed
by the cell maximum, while the flux contribution is additive. -/
theorem hm_energy_ftc_of_integrated_pairings
    {energy regular flux : ℝ → ℝ} {a t L G H Q : ℝ}
    (hderiv : ∀ s ∈ Set.uIcc a t,
      HasDerivAt energy (2 * (regular s + flux s)) s)
    (hregInt : IntervalIntegrable regular volume a t)
    (hfluxInt : IntervalIntegrable flux volume a t)
    (hzero : energy a = 0)
    (hregBound : |∫ s in a..t, regular s| ≤ Real.sqrt L * G * H)
    (hfluxBound : |∫ s in a..t, flux s| ≤ Q) :
    energy t ≤ 2 * (Real.sqrt L * G * H + Q) := by
  have hsumInt : IntervalIntegrable (fun s => regular s + flux s) volume a t :=
    hregInt.add hfluxInt
  have hscaleInt : IntervalIntegrable
      (fun s => 2 * (regular s + flux s)) volume a t :=
    hsumInt.const_mul 2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hderiv s hs) hscaleInt
  have hpair : (∫ s in a..t, 2 * (regular s + flux s)) =
      2 * ((∫ s in a..t, regular s) + ∫ s in a..t, flux s) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hregInt hfluxInt]
  have henergy : energy t = 2 *
      ((∫ s in a..t, regular s) + ∫ s in a..t, flux s) := by
    rw [← hpair]
    have h := hftc.symm
    rw [hzero] at h
    linarith
  have hparts : |(∫ s in a..t, regular s) +
      ∫ s in a..t, flux s| ≤ Real.sqrt L * G * H + Q := by
    calc
      _ ≤ |∫ s in a..t, regular s| + |∫ s in a..t, flux s| := abs_add_le _ _
      _ ≤ Real.sqrt L * G * H + Q := add_le_add hregBound hfluxBound
  calc
    energy t = 2 * ((∫ s in a..t, regular s) +
        ∫ s in a..t, flux s) := henergy
    _ ≤ 2 * |(∫ s in a..t, regular s) +
        ∫ s in a..t, flux s| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 2 * (Real.sqrt L * G * H + Q) :=
      mul_le_mul_of_nonneg_left hparts (by norm_num)
    _ = 2 * (Real.sqrt L * G * H + Q) := by ring

/-- The transported norm estimate with its maximum chosen internally. The
base point may be either end of the closed interval; this handles refresh cells
that meet time zero by integrating backward from their positive right
endpoint. `hregBound` is the time-integrated regular pairing estimate under
an arbitrary cell envelope, and `hfluxBound` is the integrated signed flux
pairing estimate. -/
theorem hm_transported_norm_uniform_of_integrated_pairings
    {F G source : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (F t))
    (hSourcePer : ∀ t, 0 < t → IsZ2Periodic (source t))
    (hVper : ∀ t, 0 < t → ∀ i : Fin 2, IsZ2Periodic (fun x => V t x i))
    (hF : ∀ t, 0 < t → ContDiff ℝ 1 (F t))
    (hG : ∀ t, 0 < t → Continuous (G t))
    (hV : ∀ t, 0 < t → ContDiff ℝ 1 (V t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceSplit : ∀ t x, source t x = G t x + AVenhance.vecDiv (V t) x)
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => F s ((X s).toFun x))
        (source t ((X t).toFun x)) t)
    {a b anchor Gscale Q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hanchor : anchor ∈ Set.Icc a b)
    (hzero : F anchor = fun _ => 0)
    (hNormCont : ContinuousOn
      (fun t => Real.sqrt (AVenhance.l2NormSq (F t))) (Set.Icc a b))
    (hGscale : 0 ≤ Gscale) (hQ : 0 ≤ Q)
    (hregInt : ∀ t ∈ Set.Icc a b,
      IntervalIntegrable (hmRegularPairing (F := F) (G := G)) volume anchor t)
    (hfluxInt : ∀ t ∈ Set.Icc a b,
      IntervalIntegrable (hmFluxPairing (F := F) (V := V)) volume anchor t)
    (hregBound : ∀ t ∈ Set.Icc a b, ∀ H : ℝ,
      (∀ s ∈ Set.Icc a b,
        Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H) →
      |∫ s in anchor..t, hmRegularPairing (F := F) (G := G) s| ≤
        Real.sqrt (b - a) * Gscale * H)
    (hfluxBound : ∀ t ∈ Set.Icc a b,
      |∫ s in anchor..t, hmFluxPairing (F := F) (V := V) s| ≤ Q) :
    ∀ t ∈ Set.Icc a b,
      Real.sqrt (AVenhance.l2NormSq (F t)) ≤
        2 * Real.sqrt (b - a) * Gscale + Real.sqrt (2 * Q) := by
  let f : ℝ → ℝ := fun t => Real.sqrt (AVenhance.l2NormSq (F t))
  have haCell : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨t₀, ht₀, hmax⟩ :=
    (isCompact_Icc.exists_isMaxOn ⟨a, haCell⟩ (by simpa [f] using hNormCont))
  let H : ℝ := f t₀
  have hHnonneg : 0 ≤ H := Real.sqrt_nonneg _
  have hFbound : ∀ s ∈ Set.Icc a b, f s ≤ H := by
    intro s hs
    exact hmax hs
  have hFTC : ∀ t ∈ Set.Icc a b,
      f t ^ 2 ≤ (2 * Real.sqrt (b - a) * Gscale) * H + 2 * Q := by
    intro t ht
    have hderiv : ∀ s ∈ Set.uIcc anchor t,
        HasDerivAt (fun r => f r ^ 2)
          (2 * (hmRegularPairing (F := F) (G := G) s +
            hmFluxPairing (F := F) (V := V) s)) s := by
      intro s hs
      have hsCell : s ∈ Set.Icc a b := by
        rw [Set.mem_uIcc] at hs
        rcases hs with hs | hs
        · exact ⟨le_trans hanchor.1 hs.1,
            le_trans hs.2 ht.2⟩
        · exact ⟨le_trans ht.1 hs.1,
            le_trans hs.2 hanchor.2⟩
      have hspos : 0 < s := lt_of_lt_of_le ha hsCell.1
      have hd := hm_transported_energy_derivative_of_pairing X hFper
        hSourcePer hVper hF hG hV hComp hSourceComp hSourceSplit hMaterial hspos
      have hlocal : (fun r => f r ^ 2) =ᶠ[𝓝 s]
          fun r => AVenhance.l2NormSq (F r) := Filter.Eventually.of_forall fun r => by
        dsimp [f]
        exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
      exact hd.congr_of_eventuallyEq hlocal
    have hzeroEnergy : f anchor ^ 2 = 0 := by
      simp [f, hzero, AVenhance.l2NormSq]
    have henergy := hm_energy_ftc_of_integrated_pairings
      (L := b - a) (G := Gscale) (H := H)
      hderiv
      (hregInt t ht) (hfluxInt t ht) hzeroEnergy
      (hregBound t ht H hFbound) (hfluxBound t ht)
    calc
      f t ^ 2 ≤ 2 * (Real.sqrt (b - a) * Gscale * H + Q) := henergy
      _ = (2 * Real.sqrt (b - a) * Gscale) * H + 2 * Q := by ring
  have hA : 0 ≤ 2 * Real.sqrt (b - a) * Gscale := by positivity
  have hB : 0 ≤ 2 * Q := by positivity
  have hbound := hm_transport_cell_sup_le_of_quadraticCoefficients
    (fun t ht => Real.sqrt_nonneg _) hA hB hFTC
      ⟨t₀, ht₀, rfl, hFbound⟩
  intro t ht
  exact hbound t ht

/-- Convert the transported quadratic-energy bound to the `eLpNorm`
field shape for a continuous periodic slice. -/
theorem hm_continuous_slice_eLpNorm_le_of_l2NormSq_bound
    {f : Vec 2 → ℝ} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (hbound : Real.sqrt (AVenhance.l2NormSq f) ≤ B) :
    eLpNorm f 2 (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal B := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict AVenhance.unitCube) := hf.aestronglyMeasurable
  have hsqCont : Continuous (fun x => f x ^ 2) := hf.pow 2
  have hsqOn := AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous
    hsqCont
  have hsq : Integrable (fun x => f x ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [IntegrableOn] using hsqOn
  have hIntEq : (∫ x in AVenhance.unitCube, f x ^ 2) =
      AVenhance.l2NormSq f := by
    rfl
  have hEnergyBound :
      (∫ x in AVenhance.unitCube, f x ^ 2) ≤ B ^ 2 := by
    rw [hIntEq]
    exact (Real.sqrt_le_iff.mp hbound).2
  exact AVenhance.Infra.Section4.amnr_scalar_eLpNorm_two_le_of_square
    hmeas hsq hB hEnergyBound

/-- Both the potential and its material source vanish at each half-cell
boundary. -/
theorem frozen_hm_halfCell_endpoints_zero
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (l : ℤ) :
    (I.Hm hΦ m κ T ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) = fun _ => 0) ∧
    (∀ x, AVenhance.Infra.Section5.hmEndpoint I hΦ m κ T
      (AVenhance.Jcut β) ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) x -
      AVenhance.Infra.Section5.hmEndpoint I hΦ m κ T 0
      ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) x = 0) := by
  constructor
  · exact AVenhance.Infra.Section4.Hm_eq_zero_at_halfCell I hΦ hm κ T l
  · intro x
    rw [AVenhance.Infra.Section4.hmEndpoint_eq_zero_at_halfCell I hΦ hm κ T
      (AVenhance.Jcut β) l, AVenhance.Infra.Section4.hmEndpoint_eq_zero_at_halfCell
      I hΦ hm κ T 0 l]
    ring

/-- The actual `H_m` vanishes at the left half-cell endpoint, so the
transported FTC gives a cellwise `L²` bound without a norm-attainment or
time-constant-norm premise. `source` is the scalar material derivative; its
scale and amplitude stay abstract. -/
theorem frozen_hm_halfCell_eLpNorm_bound
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    {source : ℝ → Vec 2 → ℝ}
    (hFper : ∀ t, IsZ2Periodic (I.Hm hΦ m κ T t))
    (hSourcePer : ∀ t, IsZ2Periodic (source t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => I.Hm hΦ m κ T s ((X s).toFun x))
        (source t ((X t).toFun x)) t)
    {b D B : ℝ} (hc : 0 < (l + 1 / 2) * AVenhance.tauPP β I.Λ m)
    (hcb : (l + 1 / 2) * AVenhance.tauPP β I.Λ m ≤ b)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hNormCont : ContinuousOn
      (fun t => Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)))
      (Set.Icc ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) b))
    (hSourceBound : ∀ t ∈ Set.Icc ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) b,
      Real.sqrt (AVenhance.l2NormSq (source t)) ≤ D)
    (hScale : 2 * (b - (l + 1 / 2) * AVenhance.tauPP β I.Λ m) * D ≤ B)
    (hSliceCont : ∀ t ∈ Set.Icc
      ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) b,
      Continuous (I.Hm hΦ m κ T t)) :
    ∀ t ∈ Set.Icc ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) b,
      eLpNorm (I.Hm hΦ m κ T t) 2
        (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal B := by
  let c : ℝ := (l + 1 / 2) * AVenhance.tauPP β I.Λ m
  have hzero : I.Hm hΦ m κ T c = fun _ => 0 := by
    simpa [c] using
      (frozen_hm_halfCell_endpoints_zero I hΦ hm κ T l).1
  have henergy := hm_transported_energy_uniform X hFper hSourcePer
    hComp hSourceComp hMaterial hc hcb hD hzero hNormCont hSourceBound
  intro t ht
  have hslice := hm_continuous_slice_eLpNorm_le_of_l2NormSq_bound
    (hSliceCont t ht) hB ((henergy t ht).trans hScale)
  exact hslice

end AVenhance.Infra.Section4
