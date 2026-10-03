/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Twistie3
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity

/-! # Joint regularity of the flux ingredients on the open half space

All statements are on `(0,∞) × ℝ²`.  Jointly `C^∞` pieces: the diffusion matrix, `∇T`, `G_l`, the
shear field pulled back by the flows.  The twisted corrector carries the time factor `corrTime`
(only proved `C²`), so the divergence-form fluxes are treated at joint order `2`; this suffices for
continuity of their divergences. -/

@[expose] public section

open Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ### The diffusion matrix -/

theorem tf_contDiff_zetaMK (m : ℕ) (k : ℤ) : ContDiff ℝ ∞ (I.zetaMK m k) := by
  unfold Ingredients.zetaMK scaledCutoff
  exact I.zeta_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- `ψTilde_m` is jointly `C^∞`. -/
theorem tf_psiTilde_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => psiTilde I hΦ m p.1 p.2) := by
  rw [← contDiffOn_univ]
  have h := tf_contDiffOn_tsum (n := ∞) (U := Set.univ)
    (f := fun (k : {k : ℤ // Odd k}) (p : ℝ × Vec 2) =>
      I.hatZetaML m (lIdx β I.Λ m k.1) p.1 * I.zetaMK m k.1 p.1 *
        psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) p.1 p.2))
    (P := fun k t => I.zetaMK m k.1 t = 0)
    (tf_active_odd (tf_zetaMK_active I m))
    (by intro k q h; simp [h])
    (fun k => by
      refine ContDiff.contDiffOn ?_
      exact (((Section5.RelativeError.hatZetaML_contDiff I m _).comp contDiff_fst).mul
        ((tf_contDiff_zetaMK I m k.1).comp contDiff_fst)).mul
        ((Infra.Section4.amnr_psi_contDiff I m k.1).comp
          (xFlowInv_joint_contDiff_infty I hΦ m _)))
  exact h

/-- Each entry of the diffusion matrix is jointly `C^∞`. -/
theorem tf_diffusion_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => diffusionMatrix I hΦ m κm p.1 p.2 i j) := by
  have h := tf_psiTilde_contDiff I hΦ m
  simp only [diffusionMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.add (h.mul contDiff_const)

/-! ### Gradients of `T`, `G_l` -/

theorem tf_gradT_contDiffOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2 j) tfU :=
  tf_spaceGrad_contDiffOn_Ioi (m := 2) (n := ∞) (by norm_num)
    (hT.mono (Set.prod_mono Set.Ioi_subset_Ici_self subset_rfl)) j

theorem tf_G_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => G I hΦ m T l p.1 p.2 j) tfU :=
  (transportedGrad_contDiffOn I hΦ m l hT j).mono
    (Set.prod_mono Set.Ioi_subset_Ici_self subset_rfl)

theorem tf_gradG_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i j : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => gradG I hΦ m T l p.1 p.2 i j) tfU :=
  tf_spaceGrad_contDiffOn_Ioi (m := 2) (n := ∞) (by norm_num)
    (F := fun t y => G I hΦ m T l t y j) (tf_G_contDiffOn I hΦ m l hT j) i

/-! ### The generic flux form -/

/-- `∑_k c_k(t) D(t,x) W_k(t,x)` over odd `k`. -/
def tfFlux (c : {k : ℤ // Odd k} → ℝ → ℝ) (D : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (W : {k : ℤ // Odd k} → ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k, c k t • (D t x).mulVec (W k t x)

theorem tfFlux_contDiffOn {n : WithTop ℕ∞} (c : {k : ℤ // Odd k} → ℝ → ℝ)
    (D : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (W : {k : ℤ // Odd k} → ℝ → Vec 2 → Vec 2)
    (hc : ∀ k, ContDiff ℝ n (c k))
    (hD : ∀ i j, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => D p.1 p.2 i j) tfU)
    (hW : ∀ k j, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => W k p.1 p.2 j) tfU)
    (hact : ∀ t₀ : ℝ, ∃ S : Finset {k : ℤ // Odd k}, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → c k t = 0)
    (i : Fin 2) :
    ContDiffOn ℝ n (fun p : ℝ × Vec 2 => tfFlux c D W p.1 p.2 i) tfU := by
  have hvec : ContDiffOn ℝ n (fun p : ℝ × Vec 2 => tfFlux c D W p.1 p.2) tfU :=
    tf_contDiffOn_tsum (f := fun k p => c k p.1 • (D p.1 p.2).mulVec (W k p.1 p.2))
      (P := fun k t => c k t = 0) hact (by intro k q h; simp [h])
      (fun k => contDiffOn_pi.2 fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact ((hc k).comp contDiff_fst).contDiffOn.mul (tf_mulVec_contDiffOn hD (hW k) i))
  exact contDiffOn_pi.1 hvec i

/-! ### `twistie3` -/

theorem tf_twistie3Flux_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => twistie3Flux I hΦ m κm T p.1 p.2 i) tfU := by
  have h := tfFlux_contDiffOn (n := 2) (fun k t => I.xiMK m k.1 t)
    (fun t x => diffusionMatrix I hΦ m κm t x)
    (fun k t x => spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k.1) t x)
    (fun k => (contDiff_xiMK I m k.1).of_le (by norm_num))
    (fun i j => ((tf_diffusion_contDiff I hΦ m κm i j).of_le (by norm_num)).contDiffOn)
    (fun k j => (tf_gradT_contDiffOn hT j).sub
      ((tf_G_contDiffOn I hΦ m _ hT j).of_le (by norm_num)))
    (tf_active_odd (exists_active_finset I m)) i
  exact h

/-! ### `normie2` -/

theorem tf_normie2Flux_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => I.Hm hΦ m κm T p.1 p.2) tfU)
    (i : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => normie2Flux I hΦ m κm T p.1 p.2 i) tfU :=
  tf_mulVec_contDiffOn (A := fun p : ℝ × Vec 2 => diffusionMatrix I hΦ m κm p.1 p.2)
    (v := fun p : ℝ × Vec 2 => spaceGrad (fun z => I.Hm hΦ m κm T p.1 z) p.2)
    (fun i j => ((tf_diffusion_contDiff I hΦ m κm i j).of_le (by norm_num)).contDiffOn)
    (fun j => tf_spaceGrad_contDiffOn_Ioi (m := 2) (n := ∞) (by norm_num)
      (F := fun t z => I.Hm hΦ m κm T t z) hH j) i

/-! ### `normie1` -/

/-- The `T`-dependent factor of `ΧTilde_{m,k} ∇G_{l_k}`: the corrector without its time factor. -/
def tfChiW (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    Vec 2 :=
  fun i => ∑ j : Fin 2,
    -(uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) *
      gradG I hΦ m T (lIdx β I.Λ m k) t x i j

theorem tf_chiGradG_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    chiGradG I hΦ m κm T k t x = I.corrTime κm m k t • tfChiW I hΦ m T k t x := by
  funext i
  simp only [chiGradG, tfChiW, Ingredients.chiTilde, Ingredients.chiMK, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tf_normie1Flux_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) :
    normie1Flux I hΦ m κm T t x =
      tfFlux (fun k t => I.xiMK m k.1 t * I.corrTime κm m k.1 t)
        (fun t x => diffusionMatrix I hΦ m κm t x)
        (fun k t x => tfChiW I hΦ m T k.1 t x) t x := by
  unfold normie1Flux tfFlux
  refine tsum_congr fun k => ?_
  rw [tf_chiGradG_eq, Matrix.mulVec_smul, smul_smul]

theorem tf_chiW_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (k : ℤ) (i : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => tfChiW I hΦ m T k p.1 p.2 i) tfU := by
  unfold tfChiW
  refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
  · have hu : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
        uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2) j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_uShear' β I.Λ m k).comp
        (xFlowInv_joint_contDiff_infty I hΦ m _))
    exact (hu.neg.of_le (by norm_num)).contDiffOn
  · exact tf_gradG_contDiffOn I hΦ m _ hT i j

theorem tf_normie1Flux_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => normie1Flux I hΦ m κm T p.1 p.2 i) tfU := by
  have h := tfFlux_contDiffOn (n := 2) (fun k t => I.xiMK m k.1 t * I.corrTime κm m k.1 t)
    (fun t x => diffusionMatrix I hΦ m κm t x)
    (fun k t x => tfChiW I hΦ m T k.1 t x)
    (fun k => ((contDiff_xiMK I m k.1).of_le (by norm_num)).mul
      (Infra.Section3.corrTime_contDiff_two I κm k.1))
    (fun i j => ((tf_diffusion_contDiff I hΦ m κm i j).of_le (by norm_num)).contDiffOn)
    (fun k j => tf_chiW_contDiffOn I hΦ m hT k.1 j)
    (fun t₀ => by
      obtain ⟨S, hS⟩ := tf_active_odd (exists_active_finset I m) t₀
      exact ⟨S, fun k hk t ht => by simp [hS k hk t ht]⟩) i
  refine h.congr ?_
  intro p _
  rw [tf_normie1Flux_eq]

/-! ### `R46` -/

/-- The vector inside the (time-only) flux matrix in `R46`. -/
def tfR46Inner (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    Vec 2 :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
    (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x)

theorem tf_Gbar_contDiffOn (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => Gbar I hΦ m T p.1 p.2) tfU :=
  tf_contDiffOn_tsum (f := fun (l : ℤ) (p : ℝ × Vec 2) => I.hatXiML m l p.1 • G I hΦ m T l p.1 p.2)
    (P := fun l t => I.hatXiML m l t = 0) (tf_hatXiML_active I hm)
    (by intro l q h; simp [h])
    (fun l => contDiffOn_pi.2 fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (((Section5.RelativeError.hatXiML_contDiff I m l).of_le (by simp)).comp
        contDiff_fst).contDiffOn.mul (tf_G_contDiffOn I hΦ m l hT j))

theorem tf_R46Inner_contDiffOn (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => tfR46Inner I hΦ m T p.1 p.2 j) tfU := by
  have hvec : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => tfR46Inner I hΦ m T p.1 p.2) tfU :=
    tf_contDiffOn_tsum
      (f := fun (k : {k : ℤ // Odd k}) (p : ℝ × Vec 2) =>
        I.xiMK m k.1 p.1 • (Gbar I hΦ m T p.1 p.2 - G I hΦ m T (lIdx β I.Λ m k.1) p.1 p.2))
      (P := fun k t => I.xiMK m k t = 0) (tf_active_odd (exists_active_finset I m))
      (by intro k q h; simp [h])
      (fun k => contDiffOn_pi.2 fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        exact ((contDiff_xiMK I m k.1).comp contDiff_fst).contDiffOn.mul
          ((contDiffOn_pi.1 (tf_Gbar_contDiffOn I hΦ hm hT) j).sub
            (tf_G_contDiffOn I hΦ m _ hT j)))
  exact contDiffOn_pi.1 hvec j

theorem tf_spaceGrad_lin {f g : Vec 2 → ℝ} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a b : ℝ) (i : Fin 2) :
    spaceGrad (fun y => a * f y + b * g y) x i = a * spaceGrad f x i + b * spaceGrad g x i := by
  have h := (hf.hasFDerivAt.const_mul a).add (hg.hasFDerivAt.const_mul b)
  have h2 : fderiv ℝ (fun y => a * f y + b * g y) x = a • fderiv ℝ f x + b • fderiv ℝ g x :=
    h.fderiv
  simp only [spaceGrad]
  rw [h2]
  simp

theorem tf_R46_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (x : Vec 2) (hd : ∀ j : Fin 2, DifferentiableAt ℝ (fun y => tfR46Inner I hΦ m T t y j) x) :
    R46 I hΦ m κm T t x = ∑ i : Fin 2, (I.flux κm m t i 0 * spaceGrad (fun y => tfR46Inner I hΦ m
        T t y 0) x i +
      I.flux κm m t i 1 * spaceGrad (fun y => tfR46Inner I hΦ m T t y 1) x i) := by
  unfold R46 vecDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have := tf_spaceGrad_lin (hd 0) (hd 1) (I.flux κm m t i 0) (I.flux κm m t i 1) i
  rw [← this]
  congr 2
  funext y
  simp [tfR46Inner, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem tf_R46_continuousOn (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => R46 I hΦ m κm T p.1 p.2) tfU := by
  have hE := tf_R46Inner_contDiffOn I hΦ hm hT
  have hg : ∀ j i : Fin 2, ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad (fun y => tfR46Inner I hΦ m T p.1 y j) p.2 i) tfU :=
    fun j i => (tf_spaceGrad_contDiffOn_Ioi (m := 1) (n := ∞) (by norm_num)
      (F := fun t y => tfR46Inner I hΦ m T t y j) (hE j) i).continuousOn
  have hfl : ∀ i j : Fin 2, Continuous (fun p : ℝ × Vec 2 => I.flux κm m p.1 i j) :=
    fun i j => (Infra.Section3.flux_entry_time_continuous I hm κm i j).comp continuous_fst
  have hcont : ContinuousOn (fun p : ℝ × Vec 2 => ∑ i : Fin 2,
      (I.flux κm m p.1 i 0 * spaceGrad (fun y => tfR46Inner I hΦ m T p.1 y 0) p.2 i +
        I.flux κm m p.1 i 1 * spaceGrad (fun y => tfR46Inner I hΦ m T p.1 y 1) p.2 i)) tfU :=
    continuousOn_finsetSum _ fun i _ =>
      ((hfl i 0).continuousOn.mul (hg 0 i)).add ((hfl i 1).continuousOn.mul (hg 1 i))
  refine hcont.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  refine tf_R46_eq I hΦ m κm T t x fun j => ?_
  have h : ContDiffOn ℝ ∞ ((fun p : ℝ × Vec 2 => tfR46Inner I hΦ m T p.1 p.2 j) ∘
      (fun y : Vec 2 => (t, y))) Set.univ :=
    (hE j).comp (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact ((contDiffOn_univ.mp h).differentiable (by simp)) x

end AVenhance.Infra.Section5.Contracts
end
