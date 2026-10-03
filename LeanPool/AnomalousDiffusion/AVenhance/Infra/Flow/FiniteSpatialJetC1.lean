/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Partial

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetTaylor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetGlobal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearFlowCLM
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalRemainderOnWindow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearGlobalExistence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteJetFlowGroupLaw
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1Core
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Fixed-start C¹ smooth dependence for each finite recursive jet flow. -/

@[expose] public section

open Homogenization
open Module
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Reconstruct the full state derivative from the next recursive jet flow. -/
def spatialJetFlowDerivativeOperator
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (t s : ℝ) (z : SpatialJetState n) :
    SpatialJetState n →L[ℝ] SpatialJetState n :=
  let basis := Module.finBasis ℝ (SpatialJetState n)
  basis.constrL (fun i =>
    (spatialJetFlow hb X hX (n + 1) t
      (z, fun j => if j = (0 : Fin 2) then basis i else 0) s).2 0)

/-- The reconstructed operator is continuous in the base state. -/
theorem spatialJetFlowDerivativeOperator_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s : ℝ) :
    Continuous (fun p : ℝ × SpatialJetState n =>
      spatialJetFlowDerivativeOperator hb hX n p.1 s p.2) := by
  let E := SpatialJetState n
  let basis : Basis (Fin (finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let build : (Fin (finrank ℝ E) → E) →ₗ[ℝ] E →L[ℝ] E :=
    { toFun := fun values => basis.constrL values
      map_add' := by
        intro f g
        ext v
        simp [Module.Basis.constrL_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext v
        simp [Module.Basis.constrL_apply, Finset.smul_sum, smul_smul, mul_comm] }
  have hbuild : Continuous build := build.continuous_of_finiteDimensional
  let values : (ℝ × SpatialJetState n) → (Fin (finrank ℝ E) → E) := fun p i =>
    (spatialJetFlow hb X hX (n + 1) p.1
      (p.2, fun j => if j = (0 : Fin 2) then basis i else 0) s).2 0
  have hvalues : Continuous values := by
    apply continuous_pi
    intro i
    let input : (ℝ × E) → ℝ × SpatialJetState (n + 1) := fun p =>
      (p.1, (p.2, fun j => if j = (0 : Fin 2) then basis i else 0))
    have hinput : Continuous input := by fun_prop
    have hflow := spatialJetFlow_continuous_fixed_start hb hX (n + 1) s
    have hnext : Continuous (fun p : ℝ × E =>
        spatialJetFlow hb X hX (n + 1) p.1
          (p.2, fun j => if j = (0 : Fin 2) then basis i else 0) s) := by
      exact hflow.comp hinput
    exact (continuous_apply (0 : Fin 2)).comp (continuous_snd.comp hnext)
  have heq : (fun p : ℝ × E => spatialJetFlowDerivativeOperator hb hX n p.1 s p.2) =
      fun p => build (values p) := by
    funext p
    rfl
  rw [heq]
  exact hbuild.comp hvalues

theorem spatialJetFlow_hasFDerivAt_forward
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s t : ℝ) (hst : s ≤ t) (z : SpatialJetState n) :
    HasFDerivAt (fun w => spatialJetFlow hb X hX n t w s)
      (spatialJetFlowDerivativeOperator hb hX n t s z) z := by
  let E := SpatialJetState n
  let F : ℝ → E → E := spatialJetField b n
  let Y : ℝ → E → ℝ → E := spatialJetFlow hb X hX n
  let a : ℝ := s - 1
  let d : ℝ := t + 1
  let R₀ : ℝ := ‖z‖ + 1
  have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hzR₀ : ‖z‖ ≤ R₀ := by dsimp [R₀]; linarith
  have hY : IsFlowOn F Y := by
    exact spatialJetFlow_isFlow hb hX n
  obtain ⟨C₀, hC₀, hYbound⟩ :=
    spatialJetFlow_bounded_on_window hb hX n a d s R₀ hR₀
  let G : ℝ × E → E := Function.uncurry F
  have hG : ContDiff ℝ ∞ G := spatialJetField_smooth hb n
  let A : ℝ → E →L[ℝ] E := fun r =>
    (fderiv ℝ G (r, Y r z s)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)
  have hpath : Continuous (fun r => Y r z s) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hY.2 z s r).continuousAt
  have hparam : Continuous (fun r : ℝ => (r, Y r z s)) := continuous_id.prodMk hpath
  have hAcont : Continuous A := by
    have hD : ContDiff ℝ ∞ (fun p : ℝ × E =>
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      (hG.fderiv_right (by norm_num)).clm_comp contDiff_const
    exact hD.continuous.comp hparam
  obtain ⟨V, hV, _⟩ := existsUnique_linearFlowOn A hAcont
  obtain ⟨M, hM₀, hMraw⟩ := spatialJetField_fderiv_bound_on_window hb n a d C₀
  have htubeY (r : ℝ) (hr : r ∈ Icc a d) : ‖Y r z s‖ ≤ C₀ :=
    hYbound r hr z hzR₀
  have hAeq (r : ℝ) : A r = fderiv ℝ (F r) (Y r z s) := by
    dsimp [A, G, F]
    exact (spatialJetField_fderiv_eq_joint hb n r (Y r z s)).symm
  have hAbound : ∀ r, r ∈ Icc a d → ‖A r‖ ≤ M := by
    intro r hr
    rw [hAeq r]
    exact hMraw r hr (Y r z s) (htubeY r hr)
  let Eexp : ℝ := Real.exp (M * (t - s))
  let R : ℝ := C₀ + Eexp
  have hEexp : 0 ≤ Eexp := (Real.exp_pos _).le
  have hR : 0 ≤ R := add_nonneg hC₀ hEexp
  obtain ⟨T, hT₀, hTaylorRaw⟩ :=
    spatialJetField_taylor_remainder_on_window hb n a d R hR
  obtain ⟨K, hK⟩ := spatialJetField_lipschitzOnWith_on_window hb n a d 0 R
  let L : ℝ := K
  have hL₀ : 0 ≤ L := K.2
  have hwin (r : ℝ) (hr : r ∈ Ico s t) : r ∈ Icc a d := by
    constructor <;> dsimp [a, d] <;> linarith [hr.1, hr.2]
  have hwinClosed (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Icc a d := by
    constructor <;> dsimp [a, d] <;> linarith [hr.1, hr.2]
  have hLip (r : ℝ) (hr : r ∈ Ico s t) :
      LipschitzOnWith ⟨L, hL₀⟩ (F r) (Metric.closedBall (0 : E) R) := by
    change LipschitzOnWith K (spatialJetField b n r) (Metric.closedBall 0 R)
    exact hK r (hwin r hr)
  have hTaylor (r : ℝ) (hr : r ∈ Ico s t) (v : E)
      (hu : ‖Y r z s‖ ≤ R) (hv : ‖v‖ ≤ R) :
      ‖F r v - F r (Y r z s) - A r (v - Y r z s)‖ ≤
        T * ‖v - Y r z s‖ * ‖v - Y r z s‖ := by
    have hraw := hTaylorRaw r (hwin r hr) (Y r z s) v hu hv
    have hslice : fderiv ℝ (spatialJetField b n r) (Y r z s) = A r :=
      (hAeq r).symm
    simpa [F, hslice] using hraw
  have htraj : ∀ r, r ∈ Icc s t → ∀ w : E, ‖w - z‖ ≤ 1 →
      ‖Y r w s‖ ≤ C₀ := by
    intro r hr w hw
    apply hYbound r (hwinClosed r hr) w
    have hw' : ‖w - z‖ + ‖z‖ ≤ 1 + ‖z‖ := by
      simpa [add_comm] using add_le_add_right hw ‖z‖
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ R₀ := by dsimp [R₀]; linarith [hw']
  have hTube : C₀ + Real.exp (M * (t - s)) ≤ R := by rfl
  have hAon : ∀ r, r ∈ Icc s t → ‖A r‖ ≤ M := by
    intro r hr
    exact hAbound r (hwinClosed r hr)
  obtain ⟨C, hC, hrem⟩ := flowOn_variational_quadratic_remainder_on_window
    F hY z A hV hst hM₀ hT₀ hL₀ hAon hAeq htraj hTube hLip hTaylor
  have has : s ∈ Ioo a d := by dsimp [a, d]; constructor <;> linarith
  have ht' : t ∈ Icc a d := by dsimp [a, d]; constructor <;> linarith [hst]
  obtain ⟨J, hJ⟩ := linearFlow_continuousLinearMap_on_window A hV
    (a := a) (d := d) (s := s) (t := t) (M := M) has ht' hM₀ hAbound
  let basis : Basis (Fin (finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let Z : ℝ → SpatialJetState (n + 1) → ℝ → SpatialJetState (n + 1) :=
    spatialJetFlow hb X hX (n + 1)
  have hZ : IsFlowOn (spatialJetField b (n + 1)) Z :=
    spatialJetFlow_isFlow hb hX (n + 1)
  let P : SpatialJetState (n + 1) →L[ℝ] E :=
    (ContinuousLinearMap.proj (0 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ E (Fin 2 → E))
  have hcolumn (i : Fin (finrank ℝ E)) :
      (spatialJetFlowDerivativeOperator hb hX n t s z) (basis i) =
        V t (basis i) s := by
    let wi : SpatialJetState (n + 1) :=
      (z, fun j => if j = (0 : Fin 2) then basis i else 0)
    let col : ℝ → E := fun r => (Z r wi s).2 0
    have hcolStart : col s = basis i := by
      change (Z s wi s).2 0 = basis i
      rw [hZ.1 wi s]
      simp [wi]
    have hcolderiv (r : ℝ) : HasDerivAt col (A r (col r)) r := by
      have hprojection := P.hasFDerivAt.comp_hasDerivAt r (hZ.2 wi s r)
      have hfunction : (P ∘ fun q => Z q wi s) = col := by
        funext q
        rfl
      rw [hfunction] at hprojection
      have hbaseEq : (Z r wi s).1 = Y r z s := rfl
      have hvalue : P (spatialJetField b (n + 1) r (Z r wi s)) = A r (col r) := by
        change ((fderiv ℝ (Function.uncurry (spatialJetField b n))
          (r, (Z r wi s).1)).comp (ContinuousLinearMap.inr ℝ ℝ E))
            ((Z r wi s).2 0) = A r ((Z r wi s).2 0)
        rw [hbaseEq]
      rw [hvalue] at hprojection
      exact hprojection
    have hAlip (r : ℝ) (hr : r ∈ Ioo a d) :
        LipschitzOnWith ⟨M, hM₀⟩ (fun v : E => A r v) Set.univ := by
      have hnorm := hAbound r (Ioo_subset_Icc_self hr)
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : A r u - A r v = A r (u - v) := by rw [map_sub]
      rw [hsub]
      calc
        ‖A r (u - v)‖ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
        _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    have hcolcont : ContinuousOn col (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hcolderiv r)
    have hVcont : ContinuousOn (fun r => V r (basis i) s) (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hV.2 (basis i) s r)
    have hEq := ODE_solution_unique_of_mem_Icc
      (v := fun r q => A r q) (s := fun _ => (Set.univ : Set E))
      (K := ⟨M, hM₀⟩) (f := col) (g := fun r => V r (basis i) s)
      (a := a) (b := d) (t₀ := s)
      hAlip has hcolcont
      (fun r _ => hcolderiv r)
      (fun _ _ => Set.mem_univ _)
      hVcont
      (fun r _ => hV.2 (basis i) s r)
      (fun _ _ => Set.mem_univ _)
      (by rw [hcolStart, hV.1])
    have hcolEnd := hEq ht'
    have hDcol :
        (spatialJetFlowDerivativeOperator hb hX n t s z) (basis i) = col t := by
      change basis.constrL
        (fun j => (spatialJetFlow hb X hX (n + 1) t
          (z, fun k => if k = (0 : Fin 2) then basis j else 0) s).2 0)
        (basis i) = col t
      rw [Module.Basis.constrL_basis]
    rw [hDcol, hcolEnd]
  have hDJ : spatialJetFlowDerivativeOperator hb hX n t s z = J := by
    have hDJlin :
        (spatialJetFlowDerivativeOperator hb hX n t s z : E →ₗ[ℝ] E) =
          (J : E →ₗ[ℝ] E) := by
      apply LinearMap.ext_on (s := Set.range basis) basis.span_eq
      intro v hv
      rcases hv with ⟨i, rfl⟩
      exact (hcolumn i).trans (hJ (basis i)).symm
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T : E →ₗ[ℝ] E => T v) hDJlin
  have hDflow (v : E) :
      spatialJetFlowDerivativeOperator hb hX n t s z v = V t v s := by
    rw [hDJ]
    exact hJ v
  have hderiv : HasFDerivAt (fun w => Y t w s)
      (spatialJetFlowDerivativeOperator hb hX n t s z) z := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    let δ : ℝ := min 1 (ε / (C + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδnorm : ‖(0 : E)‖ < δ := by simpa using hδ
    filter_upwards
      [(continuous_norm.continuousAt.tendsto).eventually (Iio_mem_nhds hδnorm)]
      with h hh'
    have hh₁ : ‖h‖ ≤ 1 := le_trans hh'.le (min_le_left _ _)
    have hcoef : C * ‖h‖ ≤ ε := by
      calc
        C * ‖h‖ ≤ C * δ := mul_le_mul_of_nonneg_left hh'.le hC
        _ ≤ ε := by
          calc
            C * min 1 (ε / (C + 1)) ≤ C * (ε / (C + 1)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hC
            _ = (C * ε) / (C + 1) := by ring
            _ ≤ ε := (div_le_iff₀ (by positivity)).2 <| by
              nlinarith [mul_nonneg hC hε.le]
    calc
      ‖Y t (z + h) s - Y t z s -
          spatialJetFlowDerivativeOperator hb hX n t s z h‖ ≤
          C * ‖h‖ * ‖h‖ := by
        rw [hDflow]
        exact hrem h hh₁
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  exact hderiv

theorem FiniteSpatialJetC1.isFlowOn_reverseTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {Y : ℝ → E → ℝ → E}
    (hY : IsFlowOn F Y) :
    IsFlowOn (fun t z => -F (-t) z) (fun t z s => Y (-t) z (-s)) := by
  constructor
  · intro z s
    exact hY.1 z (-s)
  · intro z s t
    have hbase : HasDerivAt (fun r => Y r z (-s))
        (F (-t) (Y (-t) z (-s))) (0 - t) := by
      simpa only [zero_sub] using hY.2 z (-s) (-t)
    have hrev := hbase.comp_const_sub 0 t
    simpa only [zero_sub, map_neg] using hrev

theorem FiniteSpatialJetC1.spatialJetField_reverseTime
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    (t : ℝ) (z : SpatialJetState n) :
    spatialJetField (regularityReverseTimeField b) n t z =
      -spatialJetField b n (-t) z := by
  have hbr : SmoothPeriodicField (regularityReverseTimeField b) :=
    smoothPeriodicField_regularityReverseTime hb
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rcases z with ⟨base, directions⟩
      have hslice : spatialJetField (regularityReverseTimeField b) n t =
          fun w => -spatialJetField b n (-t) w := by
        funext w
        exact ih t w
      have hleft := spatialJetField_fderiv_eq_joint hbr n t base
      have hright := spatialJetField_fderiv_eq_joint hb n (-t) base
      have hD :
          (fderiv ℝ (Function.uncurry (spatialJetField
            (regularityReverseTimeField b) n)) (t, base)).comp
              (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)) =
          -((fderiv ℝ (Function.uncurry (spatialJetField b n))
            (-t, base)).comp (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) := by
        rw [← hleft, ← hright, hslice]
        change fderiv ℝ (-(spatialJetField b n (-t))) base = _
        rw [fderiv_neg]
      dsimp only [spatialJetField]
      apply Prod.ext
      · exact ih t base
      · funext i
        change ((fderiv ℝ (Function.uncurry (spatialJetField
            (regularityReverseTimeField b) n)) (t, base)).comp
              (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) (directions i) =
          -((fderiv ℝ (Function.uncurry (spatialJetField b n))
            (-t, base)).comp (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)))
              (directions i)
        simpa using congrArg (fun L : SpatialJetState n →L[ℝ] SpatialJetState n =>
          L (directions i)) hD

theorem spatialJetFlow_reverseTime_eq
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (t : ℝ) (z : SpatialJetState n) (s : ℝ) :
    spatialJetFlow (smoothPeriodicField_regularityReverseTime hb)
      (regularityReverseTimeFlow X) (isFlow_regularityReverseTime hX) n t z s =
        spatialJetFlow hb X hX n (-t) z (-s) := by
  let br := regularityReverseTimeField b
  let Xr := regularityReverseTimeFlow X
  let Yr := spatialJetFlow (smoothPeriodicField_regularityReverseTime hb)
    Xr (isFlow_regularityReverseTime hX) n
  let Y := spatialJetFlow hb X hX n
  let W : ℝ → SpatialJetState n → ℝ → SpatialJetState n :=
    fun q w u => Y (-q) w (-u)
  have hYr : IsFlowOn (spatialJetField br n) Yr := by
    exact spatialJetFlow_isFlow (smoothPeriodicField_regularityReverseTime hb)
      (isFlow_regularityReverseTime hX) n
  have hY : IsFlowOn (spatialJetField b n) Y := spatialJetFlow_isFlow hb hX n
  have hWraw := FiniteSpatialJetC1.isFlowOn_reverseTime hY
  have hW : IsFlowOn (spatialJetField br n) W := by
    constructor
    · intro w u
      exact hWraw.1 w u
    · intro w u q
      have h := hWraw.2 w u q
      change HasDerivAt (fun r => Y (-r) w (-u))
        (-spatialJetField b n (-q) (Y (-q) w (-u))) q at h
      change HasDerivAt (fun r => Y (-r) w (-u))
        (spatialJetField br n q (Y (-q) w (-u))) q
      rw [FiniteSpatialJetC1.spatialJetField_reverseTime hb n q (Y (-q) w (-u))]
      exact h
  let a : ℝ := min s t - 1
  let d : ℝ := max s t + 1
  have hs : s ∈ Icc a d := by
    constructor <;> dsimp [a, d] <;> linarith [min_le_left s t, le_max_left s t]
  have ht : t ∈ Icc a d := by
    constructor <;> dsimp [a, d] <;> linarith [min_le_right s t, le_max_right s t]
  have heq := spatialJetField_flow_unique_on_window
    (smoothPeriodicField_regularityReverseTime hb) n hYr hW a d s hs z t ht
  simpa [Yr, W, Y, br, Xr] using heq

theorem spatialJetFlow_hasFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s t : ℝ) (z : SpatialJetState n) :
    HasFDerivAt (fun w => spatialJetFlow hb X hX n t w s)
      (spatialJetFlowDerivativeOperator hb hX n t s z) z := by
  by_cases hst : s ≤ t
  · exact spatialJetFlow_hasFDerivAt_forward hb hX n s t hst z
  · have hts : t ≤ s := le_of_not_ge hst
    let br := regularityReverseTimeField b
    let Xr := regularityReverseTimeFlow X
    let hbr := smoothPeriodicField_regularityReverseTime hb
    let hXr := isFlow_regularityReverseTime hX
    have hreverse := spatialJetFlow_hasFDerivAt_forward hbr hXr n (-s) (-t)
      (by linarith) z
    have hfun : (fun w => spatialJetFlow hbr Xr hXr n (-t) w (-s)) =
        fun w => spatialJetFlow hb X hX n t w s := by
      funext w
      simpa [br, Xr, hbr, hXr] using
        spatialJetFlow_reverseTime_eq hb hX n (-t) w (-s)
    have hD : spatialJetFlowDerivativeOperator hbr hXr n (-t) (-s) z =
        spatialJetFlowDerivativeOperator hb hX n t s z := by
      apply ContinuousLinearMap.ext
      intro v
      let basis : Basis (Fin (finrank ℝ (SpatialJetState n))) ℝ (SpatialJetState n) :=
        Module.finBasis ℝ (SpatialJetState n)
      have hlin :
          (spatialJetFlowDerivativeOperator hbr hXr n (-t) (-s) z :
            SpatialJetState n →ₗ[ℝ] SpatialJetState n) =
          (spatialJetFlowDerivativeOperator hb hX n t s z :
            SpatialJetState n →ₗ[ℝ] SpatialJetState n) := by
        apply LinearMap.ext_on (s := Set.range basis) basis.span_eq
        intro w hw
        rcases hw with ⟨i, rfl⟩
        change basis.constrL
            (fun j => (spatialJetFlow hbr Xr hXr (n + 1) (-t)
              (z, fun k => if k = (0 : Fin 2) then basis j else 0) (-s)).2 0)
            (basis i) =
          basis.constrL
            (fun j => (spatialJetFlow hb X hX (n + 1) t
              (z, fun k => if k = (0 : Fin 2) then basis j else 0) s).2 0)
            (basis i)
        rw [Module.Basis.constrL_basis, Module.Basis.constrL_basis]
        simpa [br, Xr, hbr, hXr, neg_neg] using
          congrArg (fun q : SpatialJetState (n + 1) => q.2 0)
            (spatialJetFlow_reverseTime_eq hb hX (n + 1) (-t)
              (z, fun j => if j = (0 : Fin 2) then basis i else 0) (-s))
      exact congrArg (fun L : SpatialJetState n →ₗ[ℝ] SpatialJetState n => L v) hlin
    have htransfer := hreverse.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => (congrFun hfun w).symm)
    rw [hD] at htransfer
    exact htransfer

theorem spatialJetFlow_spatial_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s t : ℝ) :
    ContDiff ℝ 1 (fun z => spatialJetFlow hb X hX n t z s) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro z
    exact (spatialJetFlow_hasFDerivAt hb hX n s t z).differentiableAt
  · have hderiv :
        fderiv ℝ (fun z => spatialJetFlow hb X hX n t z s) =
          fun z => spatialJetFlowDerivativeOperator hb hX n t s z := by
      funext z
      exact (spatialJetFlow_hasFDerivAt hb hX n s t z).fderiv
    rw [hderiv]
    have hcontinuous := spatialJetFlowDerivativeOperator_continuous hb hX n s
    let input : SpatialJetState n → ℝ × SpatialJetState n := fun z => (t, z)
    have hinput : Continuous input := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def, input] using hcontinuous.comp hinput

/-- Every finite recursive jet flow is jointly C¹ in target time and its
initial state when the start time is fixed. -/
theorem spatialJetFlow_fixed_start_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s : ℝ) :
    ContDiff ℝ 1 (fun p : ℝ × SpatialJetState n =>
      spatialJetFlow hb X hX n p.1 p.2 s) := by
  let f : ℝ × SpatialJetState n → SpatialJetState n := fun p =>
    spatialJetFlow hb X hX n p.1 p.2 s
  let dtime : ℝ × SpatialJetState n → SpatialJetState n := fun p =>
    spatialJetField b n p.1 (f p)
  let dparam : ℝ × SpatialJetState n →
      SpatialJetState n →L[ℝ] SpatialJetState n := fun p =>
    spatialJetFlowDerivativeOperator hb hX n p.1 s p.2
  have hTime (t : ℝ) (z : SpatialJetState n) :
      HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t := by
    simpa [f, dtime] using (spatialJetFlow_isFlow hb hX n).2 z s t
  have hSlice (t : ℝ) :
      ContDiff ℝ 1 (fun z => f (t, z)) := by
    simpa [f] using spatialJetFlow_spatial_contDiff_one hb hX n s t
  have hParam (t : ℝ) (z : SpatialJetState n) :
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z := by
    have hAt : ContDiffAt ℝ 1 (fun w => f (t, w)) z := (hSlice t).contDiffAt
    have hs := hAt.hasStrictFDerivAt (by norm_num)
    have hD := (spatialJetFlow_hasFDerivAt hb hX n s t z).fderiv
    change fderiv ℝ (fun w => f (t, w)) z = dparam (t, z) at hD
    rw [hD] at hs
    exact hs
  have hTimeCont : Continuous dtime := by
    have hY := spatialJetFlow_continuous_fixed_start hb hX n s
    have hpair : Continuous (fun p : ℝ × SpatialJetState n => (p.1, f p)) :=
      continuous_fst.prodMk (by simpa [f] using hY)
    have hF : Continuous (Function.uncurry (spatialJetField b n)) :=
      (spatialJetField_smooth hb n).continuous
    exact hF.comp hpair
  have hParamCont : Continuous dparam := by
    change Continuous (fun p : ℝ × SpatialJetState n =>
      spatialJetFlowDerivativeOperator hb hX n p.1 s p.2)
    exact spatialJetFlowDerivativeOperator_continuous hb hX n s
  exact contDiff_one_of_time_and_parameter_derivatives f dtime dparam
    hTime hParam hTimeCont hParamCont

/-- Explicit total derivative for the fixed-start augmented flow. -/
theorem spatialJetFlow_fixed_start_hasFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s : ℝ) (p : ℝ × SpatialJetState n) :
    HasFDerivAt
      (fun q : ℝ × SpatialJetState n =>
        spatialJetFlow hb X hX n q.1 q.2 s)
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (spatialJetField b n p.1
            (spatialJetFlow hb X hX n p.1 p.2 s))).coprod
        (spatialJetFlowDerivativeOperator hb hX n p.1 s p.2)) p := by
  let f : ℝ × SpatialJetState n → SpatialJetState n := fun q =>
    spatialJetFlow hb X hX n q.1 q.2 s
  let dtime : ℝ × SpatialJetState n → SpatialJetState n := fun q =>
    spatialJetField b n q.1 (f q)
  let dparam : ℝ × SpatialJetState n →
      SpatialJetState n →L[ℝ] SpatialJetState n := fun q =>
    spatialJetFlowDerivativeOperator hb hX n q.1 s q.2
  have hTime (t : ℝ) (z : SpatialJetState n) :
      HasDerivAt (fun r => f (r, z)) (dtime (t, z)) t := by
    simpa [f, dtime] using (spatialJetFlow_isFlow hb hX n).2 z s t
  have hParam (t : ℝ) (z : SpatialJetState n) :
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, z)) z := by
    have hSlice := spatialJetFlow_spatial_contDiff_one hb hX n s t
    have hAt : ContDiffAt ℝ 1 (fun w => f (t, w)) z := by
      simpa [f] using hSlice.contDiffAt (x := z)
    have hs := hAt.hasStrictFDerivAt (by norm_num)
    have hD := (spatialJetFlow_hasFDerivAt hb hX n s t z).fderiv
    change fderiv ℝ (fun w => f (t, w)) z = dparam (t, z) at hD
    rw [hD] at hs
    exact hs
  let dtimeCLM : ℝ × SpatialJetState n → ℝ →L[ℝ] SpatialJetState n :=
    fun q => ContinuousLinearMap.toSpanSingleton ℝ (dtime q)
  have hdtimeCLM : Continuous dtimeCLM := by
    have hTimeCont : Continuous dtime := by
      have hY := spatialJetFlow_continuous_fixed_start hb hX n s
      have hpair : Continuous (fun q : ℝ × SpatialJetState n => (q.1, f q)) :=
        continuous_fst.prodMk (by simpa [f] using hY)
      exact (spatialJetField_smooth hb n).continuous.comp hpair
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ)
      (E := SpatialJetState n)).continuous.comp hTimeCont
  have hdparam : Continuous dparam := by
    change Continuous (fun q : ℝ × SpatialJetState n =>
      spatialJetFlowDerivativeOperator hb hX n q.1 s q.2)
    exact spatialJetFlowDerivativeOperator_continuous hb hX n s
  have hderiv := hasStrictFDerivAt_uncurry_coprod
    (f := fun t z => f (t, z))
    (f₁ := fun t z => dtimeCLM (t, z))
    (f₂ := fun t z => dparam (t, z))
    (Filter.Eventually.of_forall fun q => (hTime q.1 q.2).hasFDerivAt)
    (Filter.Eventually.of_forall fun q => (hParam q.1 q.2).hasFDerivAt)
    (by
      change ContinuousAt (fun q : ℝ × SpatialJetState n => dtimeCLM q) p
      exact hdtimeCLM.continuousAt)
    (by
      change ContinuousAt (fun q : ℝ × SpatialJetState n => dparam q) p
      exact hdparam.continuousAt)
  have hfinal := hderiv.hasFDerivAt
  change HasFDerivAt
    (fun q : ℝ × SpatialJetState n =>
      spatialJetFlow hb X hX n q.1 q.2 s)
    ((dtimeCLM p).coprod (dparam p)) p at hfinal
  simpa [f, dtime, dparam, dtimeCLM] using hfinal

end

end AVenhance.Infra.Flow
