/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Generic torus transport energy, isolated from the broken physical Hm
consumer. The valid generic argument is ported from HmTransportedEnergy;
no physical source estimate is inferred from these analytic lemmas. -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5.RelativeError.Transport
/-- Closed spatial unit cell used for compactness and periodic integration. -/
def RelativeInitialDefectTransport.hmEnergyClosedCube : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem RelativeInitialDefectTransport.hmEnergyClosedCube_compact : IsCompact
    RelativeInitialDefectTransport.hmEnergyClosedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem RelativeInitialDefectTransport.hmEnergy_unitCube_ae_eq_closedCube :
    AVenhance.unitCube =ᵐ[(volume : Measure (Vec 2))]
        RelativeInitialDefectTransport.hmEnergyClosedCube := by
  simpa [volume_pi, AVenhance.unitCube, RelativeInitialDefectTransport.hmEnergyClosedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc
      (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))

theorem RelativeInitialDefectTransport.hmEnergy_cellAverage_eq_unitCube (f : Vec 2 → ℝ) :
    cellAverage f = ∫ x in AVenhance.unitCube, f x := by
  rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
  exact AVenhance.Infra.Torus.integral_unitCell_eq_unitCube f

instance RelativeInitialDefectTransport.hmEnergy_uIcc_locallyCompact (a b : ℝ) :
    LocallyCompactSpace {x // x ∈ Set.uIcc a b} := by
  have hclosed : IsClosed (Set.uIcc a b) := isClosed_Icc
  exact hclosed.locallyCompactSpace

theorem RelativeInitialDefectTransport.hmEnergy_slice_continuous {g : ℝ × Vec 2 → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    {s : ℝ} (hs : 0 < s) : Continuous (fun x => g (s, x)) := by
  exact hg.comp_continuous (continuous_const.prodMk continuous_id)
    (fun x => ⟨hs, mem_univ _⟩)

/-- The squared spatial norm is unchanged by a periodic volume-preserving
diffeomorphism of the flow. -/
theorem RelativeInitialDefectTransport.hmEnergy_comp_integral_eq {F : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t)) (t : ℝ) :
    ∫ x in AVenhance.unitCube, (F t ((X t).toFun x)) ^ 2 =
      AVenhance.l2NormSq (F t) := by
  have hper : IsZPeriodic (fun x : Vec 2 => (F t x) ^ 2) := by
    intro x k
    exact congrArg (fun y : ℝ => y ^ 2) (hFper t k x)
  have havg := cellAverage_comp_flow_eq (fun x : Vec 2 => (F t x) ^ 2)
    hper (X t)
  rw [RelativeInitialDefectTransport.hmEnergy_cellAverage_eq_unitCube] at havg
  rw [RelativeInitialDefectTransport.hmEnergy_cellAverage_eq_unitCube] at havg
  simpa [AVenhance.l2NormSq] using havg

/-- Joint continuity along a periodic measure-preserving flow makes the
spatial L² norm continuous in time on every compact interval bounded away
from zero. -/
theorem hm_transported_norm_continuous_of_joint
    {F : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t))
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
      ∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube, comp (t.1, x) ^ 2) :=
    continuous_parametric_integral_of_continuous
      (f := fun (t : K) (x : Vec 2) => comp (t.1, x) ^ 2)
      (by
        change Continuous (fun p : K × Vec 2 => comp (p.1.1, p.2) ^ 2)
        exact hjoint.pow 2)
      RelativeInitialDefectTransport.hmEnergyClosedCube_compact
  have henergyEq (t : K) :
      (∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube, comp (t.1, x) ^ 2) =
        AVenhance.l2NormSq (F t.1) := by
    calc
      _ = ∫ x in AVenhance.unitCube, comp (t.1, x) ^ 2 := by
        exact setIntegral_congr_set
            RelativeInitialDefectTransport.hmEnergy_unitCube_ae_eq_closedCube.symm
      _ = AVenhance.l2NormSq (F t.1) := RelativeInitialDefectTransport.hmEnergy_comp_integral_eq X
          hFper t.1
  have henergyCont : ContinuousOn
      (fun t => AVenhance.l2NormSq (F t)) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : K => AVenhance.l2NormSq (F t.1))
    have heq : (fun t : K =>
        ∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube, comp (t.1, x) ^ 2) =
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
theorem hm_transported_energy_ftc_integrated
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
    (hSourceIntegral : |∫ s in a..t, Real.sqrt (AVenhance.l2NormSq (source s))| ≤ D) :
    (Real.sqrt (AVenhance.l2NormSq (F t))) ^ 2 ≤
      2 * D * H := by
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
    exact RelativeInitialDefectTransport.hmEnergy_comp_integral_eq X hFper s
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
    have hclosed : IsCompact RelativeInitialDefectTransport.hmEnergyClosedCube :=
        RelativeInitialDefectTransport.hmEnergyClosedCube_compact
    have hparam : Continuous (fun s : K =>
        ∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube,
          2 * comp (s.1, x) * compSource (s.1, x)) :=
      continuous_parametric_integral_of_continuous
        (f := fun (s : K) (x : Vec 2) =>
          2 * comp (s.1, x) * compSource (s.1, x)) hg hclosed
    have heq (s : K) :
        (∫ x in AVenhance.unitCube, 2 * comp (s.1, x) * compSource (s.1, x)) =
          ∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube, 2 * comp (s.1, x) * compSource
              (s.1, x) := by
      exact setIntegral_congr_set RelativeInitialDefectTransport.hmEnergy_unitCube_ae_eq_closedCube
    have heqFun :
        (fun s : K => energyCompDeriv s.1) = fun s =>
          ∫ x in RelativeInitialDefectTransport.hmEnergyClosedCube, 2 * comp (s.1, x) * compSource
              (s.1, x) := by
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
      |energyCompDeriv s| ≤ 2 * H * Real.sqrt (AVenhance.l2NormSq (source s)) := by
    intro s hs
    let D := Real.sqrt (AVenhance.l2NormSq (source s))
    have hspos := hKpos hs
    have hFc := RelativeInitialDefectTransport.hmEnergy_slice_continuous hComp hspos
    have hRc := RelativeInitialDefectTransport.hmEnergy_slice_continuous hSourceComp hspos
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
    have hcompF := RelativeInitialDefectTransport.hmEnergy_comp_integral_eq X hFper s
    have hcompR := RelativeInitialDefectTransport.hmEnergy_comp_integral_eq (F := source) X
        hSourcePer s
    have hFs : Real.sqrt (∫ x in AVenhance.unitCube, comp (s, x) ^ 2) ≤ H := by
      rw [hcompF]
      exact hFbound s hs
    have hRs : Real.sqrt (∫ x in AVenhance.unitCube, compSource (s, x) ^ 2) ≤ D := by
      rw [hcompR]
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
  have hsourceCont : ContinuousOn
      (fun s => Real.sqrt (AVenhance.l2NormSq (source s))) (Set.uIcc a t) := by
    have hmin : 0 < min a t := lt_min ha ht
    exact hm_transported_norm_continuous_of_joint X hSourcePer hSourceComp hmin
  have hboundInt : IntervalIntegrable
      (fun s => 2 * H * Real.sqrt (AVenhance.l2NormSq (source s))) volume a t :=
    (continuousOn_const.mul hsourceCont).intervalIntegrable
  have hnormInt := intervalIntegral.norm_integral_le_abs_of_norm_le
    (f := energyCompDeriv) (g := fun s => 2 * H * Real.sqrt (AVenhance.l2NormSq (source s)))
    ((ae_restrict_mem measurableSet_uIoc).mono fun s hs => by
      simpa only [Real.norm_eq_abs] using hderivBound s (Set.uIoc_subset_uIcc hs)) hboundInt
  have hnormInt' : ‖∫ s in a..t, energyCompDeriv s‖ ≤ 2 * H * D := by
    apply hnormInt.trans
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * H)]
    exact mul_le_mul_of_nonneg_left hSourceIntegral (by positivity)
  have htEnergy : energy t ≤ 2 * D * H := by
    have hrewrite : energy t = ∫ s in a..t, energyCompDeriv s := by
      calc
        energy t = energy t - energy a := by rw [hbase]; ring
        _ = ∫ s in a..t, energyCompDeriv s := hFTC'
    have hn : |energy t| ≤ 2 * H * D := by
      simpa only [hrewrite, Real.norm_eq_abs] using hnormInt'
    exact (le_abs_self _).trans (hn.trans_eq (by ring))
  have hsqrtSq : (Real.sqrt (AVenhance.l2NormSq (F t))) ^ 2 = energy t := by
    dsimp [energy]
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [hsqrtSq]
  calc
    energy t ≤ 2 * D * H := htEnergy
    _ = 2 * D * H := by ring

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

end AVenhance.Infra.Section5.RelativeError.Transport
