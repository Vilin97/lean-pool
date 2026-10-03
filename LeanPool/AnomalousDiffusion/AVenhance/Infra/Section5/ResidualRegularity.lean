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

/-! Construct the residual calculus data from the classical iterates,
their actual AMNR regularity, and the smooth flow. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance AVenhance.Infra.Section4

/-- Joint time-space domain with strictly positive time. -/
abbrev ResidualPointwiseConstructor.residualPositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem ResidualPointwiseConstructor.residual_Gslice_smooth {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (l : ℤ) :
    ContDiff ℝ ∞ (G I hΦ m T l t) := by
  have hcoord (i : Fin 2) : ContDiffOn ℝ ∞
      (fun p : ℝ × Vec 2 => G I hΦ m T l p.1 p.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    Integration.transportedGrad_contDiffOn I hΦ m l hT i
  have hembed : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
  apply contDiff_pi.mpr
  intro i
  have hmaps : Set.MapsTo (fun x : Vec 2 => (t, x)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro y _
    exact ⟨ht, Set.mem_univ _⟩
  have hcomp := (hcoord i).comp hembed.contDiffOn hmaps
  exact contDiffOn_univ.mp (by simpa [Function.comp_def] using hcomp)

theorem ResidualPointwiseConstructor.residual_Gbar_slice_smooth {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (Gbar I hΦ m T t) := by
  let S := (I.hatXiML_support_finite hm t).toFinset
  have hrep : Gbar I hΦ m T t = fun x =>
      ∑ l ∈ S, I.hatXiML m l t • G I hΦ m T l t x := by
    funext x
    exact Gbar_eq_finite_support I hΦ m hm T t x
  rw [hrep]
  apply ContDiff.sum
  intro l hl
  have hc : ContDiff ℝ ∞ (fun _ : Vec 2 => I.hatXiML m l t) := contDiff_const
  exact hc.smul (ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht l)

theorem ResidualPointwiseConstructor.residual_Gbar_eq_source_flowAverage {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) (hT : ContDiff ℝ 1 (T t)) :
    Gbar I hΦ m T t x = ∑' l : ℤ,
      I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)) := by
  apply tsum_congr
  intro l
  have hG := G_eq_flowGrad_mulVec I hΦ m T l t x
    (hT.differentiable (by norm_num) x).hasFDerivAt
    ((xFlow_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) (I.xFlowInv hΦ m l t x)).hasFDerivAt
    (by
      let b := streamVel (Φ (m - 1))
      let F := flow b (hΦ.adm_pred m).vel_continuous
        (hΦ.adm_pred m).vel_lipschitz
      have hF : IsFlow b F := flow_isFlow b
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
      let s := (l : ℝ) * tauPP β I.Λ m
      change F t (F s x t) s = x
      calc
        F t (F s x t) s = F t x t :=
          Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
        _ = x := hF.1 x t)
  simpa [Gbar, smul_eq_mul] using congrArg
    (fun z : Vec 2 => I.hatXiML m l t • z) hG

theorem ResidualPointwiseConstructor.residual_time_hasDerivAt {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) ResidualPointwiseConstructor.residualPositiveDomain)
    (ht : 0 < t) :
    HasDerivAt (fun s => F s x)
      (fderiv ℝ (Function.uncurry F) (t, x) (1, 0)) t := by
  have hp : (t, x) ∈ ResidualPointwiseConstructor.residualPositiveDomain := by simp
      [ResidualPointwiseConstructor.residualPositiveDomain, ht]
  have hAt := hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have hfun : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (t, x)) (t, x) :=
    (hAt.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => (s, x)) (1, (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  simpa [Function.uncurry, Function.comp_def] using
    hfun.comp_hasDerivAt t hpath

theorem ResidualPointwiseConstructor.residual_slice_hasFDerivAt {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2} {L : Vec 2 →L[ℝ] ℝ}
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t, x))
    (hL : L = (fderiv ℝ (Function.uncurry F) (t, x)).comp
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2)))) :
    HasFDerivAt (F t) L x := by
  have hfun : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (t, x)) (t, x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hcomp := hfun.comp x hpath
  simpa [Function.uncurry, Function.comp_def, hL] using hcomp

theorem ResidualPointwiseConstructor.residual_slice_hasFDerivAt_canonical {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2}
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t, x)) :
    HasFDerivAt (F t) (fderiv ℝ (F t) x) x := by
  have huncurry := (hF.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hslice := huncurry.comp x hpath
  exact hslice.differentiableAt.hasFDerivAt

theorem ResidualPointwiseConstructor.residual_matrixMulVec_contDiff {n : ℕ}
    {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → Vec 2}
    (hM : ContDiff ℝ n M) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun x => (M x).mulVec (v x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ n (fun x => ∑ j : Fin 2, M x i j * v x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.mp ((contDiff_pi.mp hM) i)) j).mul
    (contDiff_pi.mp hv j)

theorem ResidualPointwiseConstructor.residual_vecDiv_contDiff {n : ℕ}
    {V : Vec 2 → Vec 2} (hV : ContDiff ℝ (n + 1) V) :
    ContDiff ℝ n (fun x => vecDiv V x) := by
  have hD : ContDiff ℝ n (fderiv ℝ V) := hV.fderiv_right (by simp)
  have hterm (i : Fin 2) : ContDiff ℝ n
      (fun x => (fderiv ℝ V x (basisVec i)) i) := by
    have hEval : ContDiff ℝ n (fun x => fderiv ℝ V x (basisVec i)) :=
      hD.clm_apply contDiff_const
    exact (contDiff_pi.mp hEval) i
  have hsum : ContDiff ℝ n
      (fun x => ∑ i : Fin 2, (fderiv ℝ V x (basisVec i)) i) := by
    apply ContDiff.sum
    intro i hi
    exact hterm i
  have heq : (fun x => vecDiv V x) =
      fun x => ∑ i : Fin 2, (fderiv ℝ V x (basisVec i)) i := by
    funext x
    unfold vecDiv
    apply Finset.sum_congr rfl
    intro i hi
    change fderiv ℝ (fun y => V y i) x (basisVec i) = _
    rw [fderiv_apply (hV.differentiable (by simp) x) i]
    rfl
  rw [heq]
  exact hsum

theorem ResidualPointwiseConstructor.residual_Gspatial_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (l : ℤ) :
    ContDiff ℝ ∞ (fun x => G I hΦ m T l t x) :=
  ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht l

theorem ResidualPointwiseConstructor.residual_gradMatrix_contDiff {n : ℕ} {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun x => gradMatrix F x) := by
  have hD : ContDiff ℝ n (fderiv ℝ F) := hF.fderiv_right (by simp)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hEval : ContDiff ℝ n (fun x => fderiv ℝ F x (basisVec i)) :=
    hD.clm_apply contDiff_const
  have hEntry := contDiff_pi.mp hEval j
  have heq : (fun x => gradMatrix F x i j) =
      fun x => fderiv ℝ F x (basisVec i) j := by
    funext x
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => F y j) x (basisVec i) = _
    rw [fderiv_apply (hF.differentiable (by simp) x) j]
    rfl
  rw [heq]
  exact hEntry

theorem ResidualPointwiseConstructor.residual_contDiffOn_slice {n : ℕ}
    {F : ℝ × Vec 2 → ℝ} (hF : ContDiffOn ℝ n F ResidualPointwiseConstructor.residualPositiveDomain)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ n (fun x => F (t, x)) := by
  let embed : Vec 2 → ℝ × Vec 2 := fun x => (t, x)
  have hembed : ContDiff ℝ n embed := by fun_prop
  have hmaps : Set.MapsTo embed Set.univ ResidualPointwiseConstructor.residualPositiveDomain := by
    intro x hx
    simp [embed, ResidualPointwiseConstructor.residualPositiveDomain, ht]
  have hcomp := hF.comp hembed.contDiffOn hmaps
  have heq : F ∘ embed = fun x => F (t, x) := rfl
  rw [heq] at hcomp
  exact contDiffOn_univ.mp hcomp

theorem ResidualPointwiseConstructor.residual_hmEndpoint_budget {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 1 + (r + 1) ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_hmFlux_budget {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 3 + r ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_amnrBudget_one {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 1 + r ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_terminalBudget_one {β : ℝ}
    (hN : 1 ≤ Nstar β) : 1 + Jcut β ≤ Nstar β := by
  have h := AVenhance.Infra.Section4.Jcut_budget hN
  omega

theorem ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (spaceGrad f) := by
  have hD : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by simp)
  apply contDiff_pi.mpr
  intro i
  have hEval : ContDiff ℝ n
      (fun y => fderiv ℝ f y (basisVec i)) := hD.clm_apply contDiff_const
  simpa [spaceGrad, ContinuousLinearMap.comp_zero] using hEval

theorem ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev t : ℝ) (_ht : 0 ≤ t) (T : ℕ → ℝ → Vec 2 → ℝ)
    (hprev : ContDiff ℝ 3 (T (Nstar β - 1) t))
    (hlast : ContDiff ℝ 3 (T (Nstar β) t)) :
    ContDiff ℝ 2 (fun y => iterateError I hΦ m κm κprev T t y) := by
  have hsmat := sMat_spatial_contDiff_two I hΦ m hm κm t
  have hM : ContDiff ℝ 2 (fun y =>
      I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := by
    exact (contDiff_const.sub contDiff_const).add hsmat
  have hgradPrev := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hprev
  have hgradLast := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hlast
  have hV : ContDiff ℝ 2 (fun y =>
      spaceGrad (T (Nstar β - 1) t) y - spaceGrad (T (Nstar β) t) y) := by
    exact (hgradPrev.of_le (by norm_num)).sub (hgradLast.of_le (by norm_num))
  have hmul := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM hV
  simpa [iterateError] using hmul

theorem ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (hκm : 0 < κm) (T : ℕ → ℝ → Vec 2 → ℝ)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 1 (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k *
        I.qMNR κm m n (Jcut β) t j k) := by
  classical
  have hN : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hbudget := ResidualPointwiseConstructor.residual_terminalBudget_one hN
  have hA (n : ℕ) (hn : n ∈ Finset.range (Nstar β))
      (i j k : Fin 2) : ContDiff ℝ 1
        (fun y => I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k) := by
    have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
      n (Jcut β) 1 hbudget i j k
    have hslice := ResidualPointwiseConstructor.residual_contDiffOn_slice hreg ht
    simpa using hslice
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun y => ∑ n ∈ Finset.range (Nstar β),
    ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k *
        I.qMNR κm m n (Jcut β) t j k)
  apply ContDiff.sum
  intro n hn
  apply ContDiff.sum
  intro j hj
  apply ContDiff.sum
  intro k hk
  exact (hA n hn i j k).mul contDiff_const

theorem ResidualPointwiseConstructor.residual_chiSlice_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (I.chiTilde hΦ m κ k t) := by
  apply contDiff_pi.mpr
  intro i
  let embed : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hembed : ContDiff ℝ 2 embed := by fun_prop
  have hi := (Integration.chiTilde_component_contDiff_two I hΦ m κ k i).comp hembed
  simpa [embed, Function.comp_def] using hi

theorem ResidualPointwiseConstructor.residual_Gjoint_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (l : ℤ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec 2 => G I hΦ m T l z.1 z.2)
      ResidualPointwiseConstructor.residualPositiveDomain := by
  apply contDiffOn_pi.mpr
  intro i
  exact (Integration.transportedGrad_contDiffOn I hΦ m l hT i).mono (by
    intro z hz
    exact ⟨Set.mem_Ici.mpr (le_of_lt hz.1), Set.mem_univ _⟩)

theorem ResidualPointwiseConstructor.residual_matrixMul_contDiff {n : ℕ}
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun y => A y * B y) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ n (fun y => ∑ p : Fin 2, A y i p * B y p j)
  apply ContDiff.sum
  intro p hp
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) p).mul
    (contDiff_pi.mp (contDiff_pi.mp hB p) j)

theorem ResidualPointwiseConstructor.residual_psi_contDiff_two {β : ℝ} (I : Ingredients β)
    (m : ℕ) (k : ℤ) : ContDiff ℝ 2 (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ 2
      (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

theorem ResidualPointwiseConstructor.residual_psiTilde_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (_hm : 1 ≤ m) (t : ℝ) :
    ContDiff ℝ 1 (psiTilde I hΦ m t) := by
  classical
  let S : Finset {k : ℤ // Odd k} :=
    ((I.zetaMK_support_finite m t).preimage
      (fun _ _ _ _ h => Subtype.ext h)).toFinset
  have hsum : psiTilde I hΦ m t = fun y =>
      ∑ k ∈ S, I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
        psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y) := by
    funext y
    unfold psiTilde
    apply tsum_eq_sum
    intro k hk
    have hz : I.zetaMK m k.1 t = 0 := by
      by_contra hne
      have hS : k ∈ S := by
        simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact hne
      apply hk
      exact hS
    simp [hz]
  rw [hsum]
  apply ContDiff.sum
  intro k hk
  have hInv : ContDiff ℝ 2
      (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t) :=
    xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k.1) t
  have hpsi := (ResidualPointwiseConstructor.residual_psi_contDiff_two I m k.1).comp hInv
  have hc : ContDiff ℝ 1 (fun _ : Vec 2 =>
      I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t) := contDiff_const
  exact ((hc.mul (hpsi.of_le (by norm_num))).of_le (by norm_num))

theorem ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κ : ℝ) (t : ℝ) :
    ContDiff ℝ 1 (fun y => diffusionMatrix I hΦ m κ t y) := by
  have hpsi := ResidualPointwiseConstructor.residual_psiTilde_contDiff I hΦ m hm t
  have hscaled : ContDiff ℝ 1 (fun y => psiTilde I hΦ m t y • sigmaMat) :=
    hpsi.smul contDiff_const
  exact contDiff_const.add hscaled

theorem ResidualPointwiseConstructor.residual_chiGradG_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (ht : 0 ≤ t) :
    ContDiff ℝ 1 (chiGradG I hΦ m κ T k t) := by
  have hchi : ContDiff ℝ 2 (I.chiTilde hΦ m κ k t) :=
    ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κ k t
  have hG : ContDiff ℝ ∞ (G I hΦ m T (lIdx β I.Λ m k) t) :=
    ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht (lIdx β I.Λ m k)
  have hgrad : ContDiff ℝ 1 (fun y =>
      gradG I hΦ m T (lIdx β I.Λ m k) t y) := by
    have hGM := ResidualPointwiseConstructor.residual_gradMatrix_contDiff (n := 1) (hG.of_le (by
        norm_num))
    have heq : (fun y => gradG I hΦ m T (lIdx β I.Λ m k) t y) =
        fun y => gradMatrix (G I hΦ m T (lIdx β I.Λ m k) t) y := by
      funext y
      ext i j
      simp [gradG, gradMatrix, Matrix.of_apply]
    rw [heq]
    exact hGM
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun y => ∑ j : Fin 2,
    I.chiTilde hΦ m κ k t y j *
      gradG I hΦ m T (lIdx β I.Λ m k) t y i j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp hchi j).of_le (by norm_num) |>.mul
    ((contDiff_pi.mp (contDiff_pi.mp hgrad i)) j)

end AVenhance.Infra.Section5

end
