/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectMaterialRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola

/-! The actual positive-time Hm material equation. Every calculus premise of
the finite telescope is discharged from the actual T iteration. -/

@[expose] public section

noncomputable section
open Filter Topology Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeInitialDefectMaterialEquation.stDiv_eq_vecDiv
    {F : ST → Vec 2} {t : ℝ} {x : Vec 2}
    (hF : DifferentiableAt ℝ F (t, x)) :
    stDiv F (t, x) = vecDiv (fun y => F (t, y)) x := by
  let B : ℝ → Vec 2 → Vec 2 := fun s y => F (s, y)
  have hB : DifferentiableAt ℝ (Function.uncurry B) (t, x) := by
    simpa [B, Function.uncurry] using hF
  have hslice : DifferentiableAt ℝ (B t) x := by
    exact hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x) |>.differentiableAt
  have hcoord (i : Fin 2) :
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec i)) i =
        fderiv ℝ (fun y => B t y i) x (basisVec i) := by
    have hvec := fderiv_uncurry_vector_spatial
      (B := B) (t := t) (x := x) (v := basisVec i) hB
    have h := congrArg (fun v : Vec 2 => v i) hvec
    rw [h, fderiv_apply hslice i]
    simp [ContinuousLinearMap.comp_apply]
  unfold stDiv vecDiv spaceGrad
  simp only [Fin.sum_univ_two]
  change (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 0)) 0 +
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 1)) 1 =
    (fderiv ℝ (fun y => B t y 0) x (basisVec 0)) +
      (fderiv ℝ (fun y => B t y 1) x (basisVec 1))
  rw [hcoord 0, hcoord 1]

/-- Actual A/q fluxes are jointly smooth on positive times, independently
of whether the q index is r or r+1. -/
theorem relative_initial_Aq_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    (n r q : ℕ) (i j k : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ST =>
      I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k *
        I.qMNR κm m n q z.1 j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => I.qMNR κm m n q t j k) :=
    contDiff_pi.mp (contDiff_pi.mp (residual_qMNR_contDiff I κm m n q) j) k
  exact (amnr_contDiffOn_Ioi_top I hΦ hm hκm hθ hT n r _ _ _).mul
    (hq.comp contDiff_fst).contDiffOn

/-- Finite actual A/q flux sums have open-time joint regularity. -/
theorem relative_initial_Aq_sum_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T) (N r q : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ST => fun i : Fin 2 =>
      ∑ n ∈ Finset.range N, ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k *
          I.qMNR κm m n q z.1 j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  apply contDiffOn_pi.mpr
  intro i
  exact ContDiffOn.sum fun n _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    relative_initial_Aq_contDiffOn I hΦ hm hκm hθ hT n r q i j k

/-- The actual Hm satisfies the endpoint material equation at every positive
 time; all differentiability inputs of the telescope are proved internally. -/
theorem relative_initial_Hm_material_equation {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm κprev g θprev T)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    deriv (fun s => I.Hm hΦ m κm (T (Nstar β)) s x) t +
      fderiv ℝ (I.Hm hΦ m κm (T (Nstar β)) t) x
        (streamVel (Φ (m - 1)) t x) =
      hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) t x -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 t x := by
  have hnhds (z : ST) (hz : 0 < z.1) :
      Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ nhds z :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩
  have hHr (r : ℕ) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ST => I.Hmr hΦ m κm (T (Nstar β)) r z.1 z.2) (t, x) :=
    (Hmr_contDiffOn_Ioi_top I hΦ hm hκm hθ hT r).contDiffAt (hnhds (t, x) ht)
  have hDt (r : ℕ) : DifferentiableAt ℝ
      (fun s => I.Hmr hΦ m κm (T (Nstar β)) r s x) t := by
    have hc := ((hHr r).differentiableAt (by simp)).comp t
      (differentiableAt_id.prodMk (differentiableAt_const x) :
        DifferentiableAt ℝ (fun s : ℝ => (s, x)) t)
    simpa only [Function.comp_def, id_eq] using hc
  have hDx (r : ℕ) : DifferentiableAt ℝ
      (I.Hmr hΦ m κm (T (Nstar β)) r t) x := by
    have hc := ((hHr r).differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id :
        DifferentiableAt ℝ (fun y : Vec 2 => (t, y)) x)
    simpa only [Function.comp_def, id_eq] using hc
  have hb : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ST => streamVel (Φ (m - 1)) z.1 z.2) := by
    exact (Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hdiv (z : ST) :
      stDiv (fun w => streamVel (Φ (m - 1)) w.1 w.2) z = 0 := by
    rw [RelativeInitialDefectMaterialEquation.stDiv_eq_vecDiv (hb.differentiable (by simp) z)]
    exact Infra.Classical.streamVel_vecDiv_eq_zero _ (hΦ.adm_pred m) z.1 z.2
  have hsum (r q : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ST => fun i : Fin 2 => ∑ n ∈ Finset.range (Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k *
            I.qMNR κm m n q z.1 j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    relative_initial_Aq_sum_contDiffOn I hΦ hm hκm hθ hT (Nstar β) r q
  apply frozen_Hm_material_equation I hΦ m κm (T (Nstar β)) t x ht
    (fun r => deriv (fun s => I.Hmr hΦ m κm (T (Nstar β)) r s x) t)
    (fun r => fderiv ℝ (I.Hmr hΦ m κm (T (Nstar β)) r t) x)
    (fun r _ => (hDt r).hasDerivAt) (fun r _ => (hDx r).hasFDerivAt)
    (hb.of_le (by simp)) hdiv
  · intro r _ n i j k z hz
    exact ((amnr_contDiffOn_Ioi_top I hΦ hm hκm hθ hT n r i j k).contDiffAt
      (hnhds z hz)).differentiableAt (by simp)
  · intro r _ a z hz
    apply differentiableAt_pi.mpr
    intro i
    exact ((relative_initial_Aq_contDiffOn I hΦ hm hκm hθ hT
      a.1.1 r (r + 1) i a.1.2 a.2).contDiffAt (hnhds z hz)).differentiableAt (by simp)
  · intro r _
    have heq : amnrPairFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r =
        fun z : ST => fun i : Fin 2 => ∑ n ∈ Finset.range (Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k *
              I.qMNR κm m n (r + 1) z.1 j k := by
      funext z
      exact amnrPairFluxSum_eq_nested I hΦ m (Nstar β) κm (T (Nstar β)) r z
    rw [heq]
    exact ((hsum r (r + 1)).contDiffAt (hnhds (t, x) ht)).of_le (by simp)
  all_goals
    intro r _
    have heq (q : ℕ) : amnrPairEndpointFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) q =
        fun z : ST => fun i : Fin 2 => ∑ n ∈ Finset.range (Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            I.Amnr hΦ m κm n (T (Nstar β)) q z.1 z.2 i j k *
              I.qMNR κm m n q z.1 j k := by
      funext z
      exact amnrPairEndpointFluxSum_eq_nested I hΦ m (Nstar β) κm (T (Nstar β)) q z
    rw [heq]
    exact ((hsum _ _).contDiffAt (hnhds (t, x) ht)).differentiableAt (by simp)

end AVenhance.Infra.Section5.RelativeError
