/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualFluxRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PulledFluxSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46IteratesRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualRegularity

/-! Construct the residual calculus data from the classical iterates,
their actual AMNR regularity, and the smooth flow. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance AVenhance.Infra.Section4

/-- Every component of the source's pointwise residual-calculus record is
obtained from the classical iterate and the declared smooth flow. -/
def frozenResidualPointwiseDataOfIterates {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (hκm : 0 < κm)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) :
    FrozenResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ := by
  classical
  let Tlast : ℝ → Vec 2 → ℝ := T (Nstar β)
  have hTjoint : ContDiffOn ℝ ∞ (Function.uncurry Tlast)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    exact tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl
  have hU : IsOpen ResidualPointwiseConstructor.residualPositiveDomain := isOpen_Ioi.prod
      isOpen_univ
  have hUp (z : ℝ × Vec 2) (hz : z ∈ ResidualPointwiseConstructor.residualPositiveDomain) :
      ResidualPointwiseConstructor.residualPositiveDomain ∈ 𝓝 z := hU.mem_nhds hz
  have hHmOn := residual_Hm_contDiffOn_two I hΦ hm hκm hθprev hT
  have hTlastSlice : ContDiff ℝ ∞ (Tlast t) :=
    tIterate_space_contDiff I hΦ hT hθprev le_rfl (le_of_lt ht)
  have hTprevSlice : ContDiff ℝ ∞ (T (Nstar β - 1) t) :=
    tIterate_space_contDiff I hΦ hT hθprev (by omega) (le_of_lt ht)
  have hTlastC3 : ContDiff ℝ 3 (Tlast t) := hTlastSlice.of_le (by norm_num)
  have hTprevC3 : ContDiff ℝ 3 (T (Nstar β - 1) t) :=
    hTprevSlice.of_le (by norm_num)
  have hTlastGrad : ContDiff ℝ 2 (spaceGrad (Tlast t)) :=
    ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hTlastC3
  have hHmSlice : ContDiff ℝ 2 (I.Hm hΦ m κm Tlast t) := by
    exact ResidualPointwiseConstructor.residual_contDiffOn_slice hHmOn ht
  have hTjointU : ContDiffOn ℝ ∞ (Function.uncurry Tlast)
      ResidualPointwiseConstructor.residualPositiveDomain := hTjoint.mono (by
        intro z hz
        exact ⟨Set.mem_Ici.mpr (le_of_lt hz.1), Set.mem_univ _⟩)
  have hTjointPos : ContDiffOn ℝ 1 (Function.uncurry Tlast)
      ResidualPointwiseConstructor.residualPositiveDomain := hTjointU.of_le (by norm_num)
  have hTpoint : ContDiffAt ℝ 1 (Function.uncurry Tlast) (t, x) :=
    (hTjointPos.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩))
  have hHmPoint : ContDiffAt ℝ 2
      (Function.uncurry fun s y => I.Hm hΦ m κm Tlast s y) (t, x) :=
    hHmOn.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
  refine {
    Dt := fun r => deriv (fun s => I.Hmr hΦ m κm Tlast r s x) t
    LHm := fun r => fderiv ℝ (I.Hmr hΦ m κm Tlast r t) x
    hDt := by
      intro r hr
      have hHmr := residual_Hmr_contDiffOn_two I hΦ hm hκm hθprev hT r hr
      have hHmr1 : ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain := hHmr.of_le (by norm_num)
      have hHmrU : ContDiffOn ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y)
          ResidualPointwiseConstructor.residualPositiveDomain := by
        change ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain
        exact hHmr1
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt (F := fun s y =>
        I.Hmr hΦ m κm Tlast r s y) (x := x) hHmrU ht
      rw [hder.deriv]
      exact hder
    hDx := by
      intro r hr
      have hHmr := residual_Hmr_contDiffOn_two I hΦ hm hκm hθprev hT r hr
      have hp := hHmOn
      have hAt := hHmr.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
      have hAt1 : ContDiffAt ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y) (t, x) :=
        hAt.of_le (by norm_num)
      have hAtU : ContDiffAt ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y) (t, x) := by
        change ContDiffAt ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2) (t, x)
        exact hAt1
      exact ResidualPointwiseConstructor.residual_slice_hasFDerivAt_canonical hAtU
    hA := by
      intro r hr n i j k z hz
      have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT n r 1
        (ResidualPointwiseConstructor.residual_amnrBudget_one hr) i j k
      exact (hreg.contDiffAt (hUp z ⟨hz, Set.mem_univ _⟩)).differentiableAt
        (by norm_num)
    hPair := by
      intro r hr a z hz
      have hAtA (i : Fin 2) : ContDiffAt ℝ 1
          (fun p : ℝ × Vec 2 =>
            I.Amnr hΦ m κm a.1.1 Tlast r p.1 p.2 i a.1.2 a.2) z := by
        have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
          a.1.1 r 1 (ResidualPointwiseConstructor.residual_amnrBudget_one hr) i a.1.2 a.2
        exact hreg.contDiffAt (hUp z ⟨hz, Set.mem_univ _⟩)
      have hq := residual_qMNR_contDiff I κm m a.1.1 (r + 1)
      have hqEntry : ContDiff ℝ ∞ (fun s =>
          (I.qMNR κm m a.1.1 (r + 1) s) a.1.2 a.2) :=
        (contDiff_pi.mp ((contDiff_pi.mp hq) a.1.2)) a.2
      have hqJoint : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
          (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) := by
        exact hqEntry.comp contDiff_fst
      have hPairAt : ContDiffAt ℝ 1
          (amnrPairFlux I hΦ m κm Tlast r a) z := by
        apply contDiffAt_pi.mpr
        intro i
        have hqJoint1 : ContDiff ℝ 1 (fun p : ℝ × Vec 2 =>
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) :=
          hqJoint.of_le (by simp)
        have hqAt : ContDiffAt ℝ 1 (fun p : ℝ × Vec 2 =>
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) z := hqJoint1.contDiffAt
        change ContDiffAt ℝ 1 (fun p : ℝ × Vec 2 =>
          I.Amnr hΦ m κm a.1.1 Tlast r p.1 p.2 i a.1.2 a.2 *
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) z
        exact (hAtA i).mul hqAt
      exact hPairAt.differentiableAt (by norm_num)
    hFlux := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          2 + r ≤ Nstar β := by
        have hcut := Finset.mem_range.mp hr
        unfold Jcut at hcut
        omega
      have hflux := residual_pairFluxSum_contDiffOn I hΦ hm hκm hθprev hT
        (Nstar β) r 2 hbudget
      exact hflux.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
    hEndNext := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          1 + (r + 1) ≤ Nstar β := ResidualPointwiseConstructor.residual_hmEndpoint_budget hr
      have hend := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκm
        hθprev hT (Nstar β) (r + 1) 1 hbudget
      exact hend.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩) |>.differentiableAt
        (by norm_num)
    hEnd := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          1 + r ≤ Nstar β := by
        have h := ResidualPointwiseConstructor.residual_hmEndpoint_budget hr
        omega
      have hend := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκm
        hθprev hT (Nstar β) r 1 hbudget
      exact hend.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩) |>.differentiableAt
        (by norm_num)
    hTail := by
      let Tail : Vec 2 → Vec 2 := fun y i =>
        ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n Tlast (Jcut β) t y i j k *
            I.qMNR κm m n (Jcut β) t j k
      have hTail : ContDiff ℝ 1 Tail := by
        simpa [Tail, Tlast] using
          ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff I hΦ m hm κm κprev hκm T
            hθprev hT ht
      exact (hTail.differentiable (by norm_num) x)
    hBase := (LeftJacobian.contDiff_pulledGapFlux I hΦ m hm (I.Jhat κm m t - I.Kmat κm m t) Tlast t
      hTlastSlice).differentiable (by simp) x
    hTtime := by
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt (F := Tlast) (x := x)
        hTjointPos ht
      rw [hder.deriv]
      exact hder
    hHtime := by
      have hHmOn1 : ContDiffOn ℝ 1
          (Function.uncurry fun s y => I.Hm hΦ m κm Tlast s y)
          ResidualPointwiseConstructor.residualPositiveDomain := by
        change ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hm hΦ m κm Tlast z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain
        exact hHmOn.of_le (by norm_num)
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt
        (F := fun s y => I.Hm hΦ m κm Tlast s y) (x := x) hHmOn1 ht
      rw [hder.deriv]
      exact hder
    hXi := by
      intro k hk
      exact (Integration.contDiff_xiMK I m k).differentiable
        (by norm_num) t |>.hasDerivAt
    Lχ := fun k => fderiv ℝ
      (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y) (t, x)
    LG := fun k => fderiv ℝ
      (Function.uncurry fun s y => G I hΦ m Tlast (lIdx β I.Λ m k) s y) (t, x)
    hChiJoint := by
      intro k hk
      have hchi : ContDiff ℝ 2
          (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y) := by
        apply contDiff_pi.mpr
        intro i
        exact Integration.chiTilde_component_contDiff_two I hΦ m κm k i
      exact (hchi.differentiable (by norm_num) (t, x)).hasFDerivAt
    hGJoint := by
      intro k hk
      have hGOn := ResidualPointwiseConstructor.residual_Gjoint_contDiffOn I hΦ m Tlast hTjoint
        (lIdx β I.Λ m k)
      have hGAt := hGOn.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
      exact (hGAt.differentiableAt (by simp)).hasFDerivAt
    hr46 := (tIterate_r46Flux_regular I hΦ hm κm hT hθprev le_rfl ht).1.differentiable
      (by simp) x
    hDE := by
      let Tail : Vec 2 → Vec 2 := fun y i =>
        ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n Tlast (Jcut β) t y i j k *
            I.qMNR κm m n (Jcut β) t j k
      have hTail : ContDiff ℝ 1 Tail := by
        simpa [Tail, Tlast] using
          ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff I hΦ m hm κm κprev hκm T
            hθprev hT ht
      have hgap := LeftJacobian.contDiff_pulledGapFlux I hΦ m hm (I.Jhat κm m t - I.flux κm m t)
        Tlast t hTlastSlice
      have hiterate := ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3
      have hsum : ContDiff ℝ 1 (fun y =>
          (∑' l : ℤ, I.hatXiML m l t •
            ((I.flowGrad hΦ m l t y).transpose.mulVec
              ((I.Jhat κm m t - I.flux κm m t).mulVec
                ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (Tlast t) y))))) + Tail y +
            iterateError I hΦ m κm κprev T t y) :=
        ((hgap.of_le (by simp)).add hTail).add (hiterate.of_le (by norm_num))
      exact hsum.differentiable (by norm_num) x
    hSmooth := hTlastSlice
    hHGlobal := by
      intro y
      exact ((hHmSlice.differentiable (by norm_num) y).hasFDerivAt)
    hChiGlobal := by
      intro k hk y
      have hchi := ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κm k t
      exact (hchi.differentiable (by norm_num) y).hasFDerivAt
    hGGlobal := by
      intro k hk y
      have hG := ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint
        (le_of_lt ht) (lIdx β I.Λ m k)
      exact (hG.differentiable (by norm_num) y).hasFDerivAt
    hCorrectorFlux := by
      intro q hq i j
      let l := lIdx β I.Λ m q.1
      have hInv : ContDiff ℝ 2 (I.xFlowInv hΦ m l t) :=
        xFlowInv_spatial_contDiff_two I hΦ m l t
      have hpsi : ContDiff ℝ 2 (fun y =>
          psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) :=
        (ResidualPointwiseConstructor.residual_psi_contDiff_two I m q.1).comp hInv
      have hchi : ContDiff ℝ 2 (I.chiTilde hΦ m κm q.1 t) :=
        ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κm q.1 t
      have hgradChi : ContDiff ℝ 1
          (fun y => gradMatrix (I.chiTilde hΦ m κm q.1 t) y) :=
        ResidualPointwiseConstructor.residual_gradMatrix_contDiff (n := 1) hchi
      have hcoef : ContDiff ℝ 1 (fun y =>
          I.hatZetaML m l t * I.zetaMK m q.1 t *
            psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) :=
        (contDiff_const.mul (hpsi.of_le (by norm_num)))
      have hbase : ContDiff ℝ 1 (fun y =>
          κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (I.hatZetaML m l t * I.zetaMK m q.1 t *
              psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) • sigmaMat) := by
        exact contDiff_const.add (hcoef.smul contDiff_const)
      have hright : ContDiff ℝ 1 (fun y =>
          (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            gradMatrix (I.chiTilde hΦ m κm q.1 t) y) :=
        contDiff_const.add hgradChi
      have hflux := ResidualPointwiseConstructor.residual_matrixMul_contDiff hbase hright
      have hentry : ContDiff ℝ 1
          (fun y => correctorFlux I hΦ m κm q.1 t y i j) := by
        simpa [correctorFlux, gradChiTilde, l] using
          (contDiff_pi.mp ((contDiff_pi.mp hflux) i) j)
      exact (hentry.differentiable (by norm_num) x).hasFDerivAt
    hGodd := by
      intro q
      have hG := ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint
        (le_of_lt ht) (lIdx β I.Λ m q.1)
      exact (hG.differentiable (by norm_num) x).hasFDerivAt
    LM := fderiv ℝ (fun y =>
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (Tlast t) y -
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t • G I hΦ m Tlast
              (lIdx β I.Λ m q.1) t y)) x
    LC := fderiv ℝ (fun y =>
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • (diffusionMatrix I hΦ m κm t y).mulVec
          (chiGradG I hΦ m κm Tlast q.1 t y)) x
    LHflux := fderiv ℝ (fun y =>
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (I.Hm hΦ m κm Tlast t) y)) x
    hMismatch := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hGmode (q : {k : ℤ // Odd k}) : ContDiff ℝ ∞
          (fun y => G I hΦ m Tlast (lIdx β I.Λ m q.1) t y) :=
        ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint (le_of_lt ht)
          (lIdx β I.Λ m q.1)
      have hGsum : ContDiff ℝ 2 (fun y =>
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t • G I hΦ m Tlast
              (lIdx β I.Λ m q.1) t y) := by
        apply ContDiff.sum
        intro q hq
        have hG2 : ContDiff ℝ 2
            (fun y => G I hΦ m Tlast (lIdx β I.Λ m q.1) t y) :=
          (hGmode q).of_le (by norm_num)
        have hξ : ContDiff ℝ 2
            (fun _ : Vec 2 => I.xiMK m q.1 t) := contDiff_const
        exact hξ.smul hG2
      have hV : ContDiff ℝ 1 (fun y =>
          spaceGrad (Tlast t) y -
            ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
              I.xiMK m q.1 t • G I hΦ m Tlast
                (lIdx β I.Λ m q.1) t y) := by
        exact (hTlastGrad.of_le (by norm_num)).sub (hGsum.of_le (by norm_num))
      have hflux := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hV
      exact (hflux.differentiable (by norm_num) x).hasFDerivAt
    hChiFlux := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hterm (q : {k : ℤ // Odd k}) : ContDiff ℝ 1
          (fun y => (diffusionMatrix I hΦ m κm t y).mulVec
            (chiGradG I hΦ m κm Tlast q.1 t y)) := by
        have hχG := ResidualPointwiseConstructor.residual_chiGradG_contDiff I hΦ m κm Tlast q.1 t
          hTjoint (le_of_lt ht)
        exact ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hχG
      have hsum : ContDiff ℝ 1 (fun y =>
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t •
              (diffusionMatrix I hΦ m κm t y).mulVec
                (chiGradG I hΦ m κm Tlast q.1 t y)) := by
        apply ContDiff.sum
        intro q hqmem
        have hξ : ContDiff ℝ 1
            (fun _ : Vec 2 => I.xiMK m q.1 t) := contDiff_const
        exact hξ.smul (hterm q)
      exact (hsum.differentiable (by norm_num) x).hasFDerivAt
    hHmFlux := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hgrad := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order (n := 1) hHmSlice
      have hflux := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hgrad
      exact (hflux.differentiable (by norm_num) x).hasFDerivAt
    hVecGlobal := by
      intro y
      have hM : ContDiff ℝ 2 (fun z => I.Kmat κm m t + I.sMat hΦ m κm t z) :=
        contDiff_const.add (sMat_spatial_contDiff_two I hΦ m hm κm t)
      have hV := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM
        (hTlastGrad.of_le (by norm_num))
      exact (hV.differentiable (by norm_num) y)
    hIterateGlobal := by
      intro y
      exact (ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3).differentiable
          (by norm_num) y
    hVecDiv := by
      have hM : ContDiff ℝ 2 (fun z => I.Kmat κm m t + I.sMat hΦ m κm t z) :=
        contDiff_const.add (sMat_spatial_contDiff_two I hΦ m hm κm t)
      have hV := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM
        (hTlastGrad.of_le (by norm_num))
      have hdiv := ResidualPointwiseConstructor.residual_vecDiv_contDiff hV
      exact hdiv.differentiable (by norm_num) x
    hIterateDiv := by
      have hiter := ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3
      exact (ResidualPointwiseConstructor.residual_vecDiv_contDiff hiter).differentiable (by
          norm_num) x
    hAnsatz := by
      classical
      let S := (I.xiMK_support_finite m t).toFinset
      have hzero (k : ℤ) (hk : k ∉ S) : I.xiMK m k t = 0 := by
        by_contra hne
        exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)
      have hfun : I.ansatz hΦ m κm Tlast t = fun y =>
          Tlast t y +
            (∑ k ∈ S, Integration.ansatzSummand I hΦ m κm Tlast k t y) +
              I.Hm hΦ m κm Tlast t y := by
        funext y
        rw [Integration.ansatz_eq_summand]
        congr 2
        exact tsum_eq_sum fun k hk =>
          Integration.ansatzSummand_eq_zero I hΦ m κm Tlast (hzero k hk) y
      rw [hfun]
      have hSeries : ContDiff ℝ 2 (fun y =>
          Tlast t y +
            (∑ k ∈ S, Integration.ansatzSummand I hΦ m κm Tlast k t y)) := by
        apply (hTlastSlice.of_le (by norm_num)).add
        apply ContDiff.sum
        intro k hk
        exact Integration.ansatzSummand_slice_contDiff I hΦ m κm k hTlastSlice
          |>.of_le (by norm_num)
      exact (hSeries.add hHmSlice).contDiffAt
  }

end AVenhance.Infra.Section5

end
