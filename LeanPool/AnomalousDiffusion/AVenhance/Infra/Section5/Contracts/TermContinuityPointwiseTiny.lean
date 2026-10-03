/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseTerms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.JhatFacts

/-! # Joint continuity of `tiny` for the actual iterates

`tiny = ∇·(d + e) + ∑_k ξ_{m,k} ΧTilde_{m,k} · (∇X ∘ X⁻¹) ∇(∇·e)`, with `d = sourceErrorD` and
`e = iterateError`.  In the corrected form, `d = Σ_l ξ̂_l F_lᵀ (JHat - 𝒥) F_l ∇T + tail`.  The
    coefficient `JHat_m - 𝒥_m`
of `d` is only continuous in time, so the divergence of `d + e` is computed by differentiating under
the (spatially constant) matrix: the first summand is `Σ_{a,b} (JHat - 𝒥)_{ab} w_{abi}` with the
    jointly
smooth `w_{abi} = Σ_l ξ̂_l (F_l)_{ai} (F_l ∇T)_b` (`tcPulled`). -/

@[expose] public section

noncomputable section

open Filter Topology Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)

/-- Slices of a jointly differentiable field on the open half space are differentiable. -/
theorem tc_slice_differentiableAt {F : ℝ → Vec 2 → ℝ} {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hF : ContDiffOn ℝ n (fun p : ℝ × Vec 2 => F p.1 p.2) tcU) {t : ℝ} (ht : 0 < t)
    (x : Vec 2) : DifferentiableAt ℝ (F t) x := by
  have h : ContDiffOn ℝ n ((fun p : ℝ × Vec 2 => F p.1 p.2) ∘ (fun y : Vec 2 => (t, y)))
      Set.univ :=
    hF.comp (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact (contDiffOn_univ.mp h).differentiable hn x

/-- The scalar field `w_{abi} = ∑_l ξ̂_{m,l} (F_l)_{ai} (F_l ∇T)_b` (with `F_l = ∇X_l ∘ X_l⁻¹`),
the part of the first summand of `d_m` that does not involve the time-only matrix `JHat - 𝒥`. -/
def tcPulled (T : ℝ → Vec 2 → ℝ) (a b i : Fin 2) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' l : ℤ, I.hatXiML m l t •
    (I.flowGrad hΦ m l t x a i * (I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x) b)

/-- The terminal `A_{m,n,Jcut} q_{m,n,Jcut}` tail of `d_m`. -/
def tcAmnrTail (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  fun i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
    I.Amnr hΦ m κm n T (Jcut β) t x i j k * I.qMNR κm m n (Jcut β) t j k

/-- Coordinates of `d_m`: `∑_{a,b} (JHat - 𝒥)_{ab} w_{abi} + tail_i`. -/
theorem tc_sourceErrorD_apply (hm : 1 ≤ m) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (i : Fin 2) :
    sourceErrorD I hΦ m κm T t x i =
      ∑ a : Fin 2, ∑ b : Fin 2, (I.Jhat κm m t - I.flux κm m t) a b *
        tcPulled I hΦ m T a b i t x + tcAmnrTail I hΦ m κm T t x i := by
  unfold sourceErrorD tcPulled tcAmnrTail
  simp only [Pi.add_apply]
  congr 1
  have hw : ∀ a b : Fin 2, (∑' l : ℤ, I.hatXiML m l t •
      (I.flowGrad hΦ m l t x a i * (I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x) b)) =
      ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset, I.hatXiML m l t •
        (I.flowGrad hΦ m l t x a i * (I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x) b) :=
    fun a b => LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t _
  simp only [hw]
  rw [LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The `w_{abi}` field is jointly `C^∞` on the open half space. -/
theorem tc_pulled_contDiffOn (hm : 1 ≤ m) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (a b i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => tcPulled I hΦ m T a b i p.1 p.2) tcU := by
  unfold tcPulled
  refine tc_contDiffOn_tsum (g := fun (l : ℤ) (p : ℝ × Vec 2) =>
    I.hatXiML m l p.1 •
      (I.flowGrad hΦ m l p.1 p.2 a i * (I.flowGrad hΦ m l p.1 p.2).mulVec (spaceGrad (T p.1) p.2)
          b))
    ?_ ?_
  · intro l
    simp only [smul_eq_mul]
    exact (((Section5.RelativeError.hatXiML_contDiff I m l).comp contDiff_fst).contDiffOn).mul
      ((Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l a i).contDiffOn.mul
        (tc_mulVec_contDiffOn (A := fun t x => I.flowGrad hΦ m l t x)
          (v := fun t x => spaceGrad (T t) x)
          (fun i j => (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l i j).contDiffOn)
          (tc_spaceGrad_T_contDiffOn hT) b))
  · rintro ⟨t, x⟩ _
    obtain ⟨S, hS⟩ := Section5.RelativeError.exists_finset_hatXi_vanish I hm t
    refine ⟨S, ?_⟩
    have hopen : IsOpen {q : ℝ × Vec 2 | |q.1 - t| < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds (by simp)] with q hq l hl
    simp [hS q.1 hq l hl]

/-- The terminal tail of `d_m` is jointly `C^∞` on the open half space. -/
theorem tc_amnrTail_contDiffOn (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => tcAmnrTail I hΦ m κm (T (Nstar β)) p.1 p.2 i) tcU := by
  unfold tcAmnrTail
  refine ContDiffOn.sum fun n _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
  have hq : ContDiff ℝ ∞ (fun t : ℝ => I.qMNR κm m n (Jcut β) t j k) :=
    contDiff_pi.mp (contDiff_pi.mp (residual_qMNR_contDiff I κm m n (Jcut β)) j) k
  exact (Integration.amnr_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT n (Jcut β) i j k).mul
    (hq.comp contDiff_fst).contDiffOn

/-- The last-iterate error is jointly `C^∞` on the open half space. -/
theorem tc_iterateError_contDiffOn (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (κprev : ℝ)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT0 : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T (Nstar β - 1) p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hT1 : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T (Nstar β) p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => iterateError I hΦ m κm κprev T p.1 p.2 i) tcU := by
  have hA : ∀ a b, ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      (I.Kmat κm m p.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm p.1 p.2) a b)
      tcU := fun a b =>
    (Section5.RelativeError.contDiff_matrix_entry
      (((Section5.RelativeError.Kmat_joint_contDiff I hm hκm).sub contDiff_const).add
        (Section5.RelativeError.sMat_joint_contDiff I hΦ hm hκm)) a b).contDiffOn
  exact tc_mulVec_contDiffOn
    (A := fun t x => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t x)
    (v := fun t x => spaceGrad (T (Nstar β - 1) t) x - spaceGrad (T (Nstar β) t) x) hA
    (fun j => (tc_spaceGrad_T_contDiffOn hT0 j).sub (tc_spaceGrad_T_contDiffOn hT1 j)) i

/-- Divergence of `∑_{p,q} M_{pq} w_{pqi} + a_i + e_i` with `M` constant in space (product rule in
coordinates). -/
theorem tc_vecDiv_pulled_add (M : Matrix (Fin 2) (Fin 2) ℝ)
    {w : Fin 2 → Fin 2 → Fin 2 → Vec 2 → ℝ} {a e : Vec 2 → Vec 2} {x : Vec 2}
    (hw : ∀ p q i, DifferentiableAt ℝ (w p q i) x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (he : ∀ i, DifferentiableAt ℝ (fun y => e y i) x) :
    vecDiv (fun y i => ∑ p : Fin 2, ∑ q : Fin 2, M p q * w p q i y + a y i + e y i) x =
      ∑ i : Fin 2, (∑ p : Fin 2, ∑ q : Fin 2, M p q * spaceGrad (w p q i) x i +
        spaceGrad (fun y => a y i) x i + spaceGrad (fun y => e y i) x i) := by
  unfold vecDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : HasFDerivAt (fun y => ∑ p : Fin 2, ∑ q : Fin 2, M p q * w p q i y)
      (∑ p : Fin 2, ∑ q : Fin 2, M p q • fderiv ℝ (w p q i) x) x :=
    HasFDerivAt.fun_sum fun p _ => HasFDerivAt.fun_sum fun q _ =>
      ((hw p q i).hasFDerivAt).const_mul (M p q)
  have hd : HasFDerivAt (fun y => ∑ p : Fin 2, ∑ q : Fin 2, M p q * w p q i y + a y i + e y i)
      ((∑ p : Fin 2, ∑ q : Fin 2, M p q • fderiv ℝ (w p q i) x) + fderiv ℝ (fun y => a y i) x +
        fderiv ℝ (fun y => e y i) x) x :=
    (hs.add (ha i).hasFDerivAt).add (he i).hasFDerivAt
  simp only [spaceGrad]
  rw [hd.fderiv]
  simp

/-- The divergence of `d_m + e` for a jointly smooth `e` is jointly continuous on the open half
space: `d_m` has the time-only (merely continuous) coefficient `JHat - 𝒥`, so the divergence is
computed by differentiating under it. -/
theorem tc_vecDiv_sourceErrorD_add_continuousOn (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {e : ℝ → Vec 2 → Vec 2}
    (he : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => e p.1 p.2 i) tcU) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      vecDiv (fun y => sourceErrorD I hΦ m κm (T (Nstar β)) p.1 y + e p.1 y) p.2) tcU := by
  have hT1 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hw := tc_pulled_contDiffOn I hΦ m hm hT1
  have hat := tc_amnrTail_contDiffOn I hΦ m hm hκm hθprev hT
  have hE : ContinuousOn (fun p : ℝ × Vec 2 =>
      ∑ i : Fin 2, (∑ a : Fin 2, ∑ b : Fin 2, (I.Jhat κm m p.1 - I.flux κm m p.1) a b *
          spaceGrad (fun y => tcPulled I hΦ m (T (Nstar β)) a b i p.1 y) p.2 i +
        spaceGrad (fun y => tcAmnrTail I hΦ m κm (T (Nstar β)) p.1 y i) p.2 i +
        spaceGrad (fun y => e p.1 y i) p.2 i)) tcU := by
    refine continuousOn_finsetSum _ fun i _ => ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ =>
        ContinuousOn.mul ?_ ?_
      · simp only [Matrix.sub_apply]
        exact (((LeftToShow.Jhat_entry_continuous_pub I hm hκm a b).sub
          (Infra.Section3.flux_entry_time_continuous I hm κm a b)).comp
            continuous_fst).continuousOn
      · exact (tc_spaceGrad_contDiffOn (m := 0) (n := ∞) (by simp)
          (F := fun t y => tcPulled I hΦ m (T (Nstar β)) a b i t y) (hw a b i) i).continuousOn
    · exact (tc_spaceGrad_contDiffOn (m := 0) (n := ∞) (by simp)
        (F := fun t y => tcAmnrTail I hΦ m κm (T (Nstar β)) t y i) (hat i) i).continuousOn
    · exact (tc_spaceGrad_contDiffOn (m := 0) (n := ∞) (by simp)
        (F := fun t y => e t y i) (he i) i).continuousOn
  refine hE.congr fun p hp => ?_
  have ht : 0 < p.1 := hp.1
  have hfield : (fun y => sourceErrorD I hΦ m κm (T (Nstar β)) p.1 y + e p.1 y) =
      fun y i => ∑ a : Fin 2, ∑ b : Fin 2, (I.Jhat κm m p.1 - I.flux κm m p.1) a b *
        tcPulled I hΦ m (T (Nstar β)) a b i p.1 y +
          tcAmnrTail I hΦ m κm (T (Nstar β)) p.1 y i + e p.1 y i := by
    funext y i
    rw [Pi.add_apply, tc_sourceErrorD_apply I hΦ m hm]
  change vecDiv (fun y => sourceErrorD I hΦ m κm (T (Nstar β)) p.1 y + e p.1 y) p.2 = _
  rw [hfield]
  exact tc_vecDiv_pulled_add (I.Jhat κm m p.1 - I.flux κm m p.1)
    (w := fun a b i y => tcPulled I hΦ m (T (Nstar β)) a b i p.1 y)
    (a := fun y => tcAmnrTail I hΦ m κm (T (Nstar β)) p.1 y) (e := fun y => e p.1 y)
    (fun a b i => tc_slice_differentiableAt (by simp)
      (F := fun t y => tcPulled I hΦ m (T (Nstar β)) a b i t y) (hw a b i) ht p.2)
    (fun i => tc_slice_differentiableAt (by simp)
      (F := fun t y => tcAmnrTail I hΦ m κm (T (Nstar β)) t y i) (hat i) ht p.2)
    (fun i => tc_slice_differentiableAt (by simp)
      (F := fun t y => e t y i) (he i) ht p.2)

/-- The divergence of `d_m` is jointly continuous on the open half space. -/
theorem tc_vecDiv_sourceErrorD_continuousOn (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      vecDiv (sourceErrorD I hΦ m κm (T (Nstar β)) p.1) p.2) tcU := by
  have h := tc_vecDiv_sourceErrorD_add_continuousOn I hΦ m hm hκm hθprev hT
    (e := fun _ _ => 0) (fun i => contDiffOn_const)
  refine h.congr fun p _ => ?_
  simp

/-- `d_m` is jointly continuous on the open half space. -/
theorem tc_sourceErrorD_continuousOn (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => sourceErrorD I hΦ m κm (T (Nstar β)) p.1 p.2 i) tcU := by
  have hT1 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hw := tc_pulled_contDiffOn I hΦ m hm hT1
  have hat := tc_amnrTail_contDiffOn I hΦ m hm hκm hθprev hT
  have hE : ContinuousOn (fun p : ℝ × Vec 2 =>
      ∑ a : Fin 2, ∑ b : Fin 2, (I.Jhat κm m p.1 - I.flux κm m p.1) a b *
        tcPulled I hΦ m (T (Nstar β)) a b i p.1 p.2 +
          tcAmnrTail I hΦ m κm (T (Nstar β)) p.1 p.2 i) tcU := by
    refine ContinuousOn.add (continuousOn_finsetSum _ fun a _ =>
      continuousOn_finsetSum _ fun b _ => ContinuousOn.mul ?_ (hw a b i).continuousOn)
      (hat i).continuousOn
    simp only [Matrix.sub_apply]
    exact (((LeftToShow.Jhat_entry_continuous_pub I hm hκm a b).sub
      (Infra.Section3.flux_entry_time_continuous I hm κm a b)).comp
        continuous_fst).continuousOn
  exact hE.congr fun p _ => tc_sourceErrorD_apply I hΦ m hm κm (T (Nstar β)) p.1 p.2 i

/-- `tiny` for the actual iterates is jointly continuous on the open half space. -/
theorem tc_tiny_continuousOn (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
        (iterateError I hΦ m κm κprev T) p.1 p.2) tcU := by
  have hT1 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hT0 := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β - 1)
    (Nat.sub_le _ _)
  have he := tc_iterateError_contDiffOn I hΦ m hm hκm κprev hT0 hT1
  unfold tiny
  refine ContinuousOn.add ?_ ?_
  · exact tc_vecDiv_sourceErrorD_add_continuousOn I hΦ m hm hκm hθprev hT he
  · -- the nondivergence tail
    refine tc_xi_tsum_continuousOn I m (g := fun k t x =>
      vecDot (I.chiTilde hΦ m κm k.1 t x)
        ((flowGradK I hΦ m k.1 t x).mulVec
          (gradDiv (iterateError I hΦ m κm κprev T) t x))) fun k => ?_
    exact tc_vecDot_mulVec_continuousOn (fun i => tc_chiTilde_continuousOn I hΦ m κm k.1 i)
      (fun i j => tc_flowGradK_continuousOn I hΦ m k.1 i j)
      (fun j => (tc_gradDiv_contDiffOn (m := 0) (n := ∞) (by simp) he j).continuousOn)

end AVenhance.Infra.Section5.Contracts
