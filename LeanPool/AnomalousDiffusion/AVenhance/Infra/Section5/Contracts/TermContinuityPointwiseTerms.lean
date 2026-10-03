/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseFields
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity

/-! # Joint continuity of `cutoff1`, `twistie1`, `twistie4`, `twistie5`, `normie3` for a smooth `T`

Each term is a locally finite (in time) sum over odd cutoff indices of products of jointly smooth
fields, with at most one spatial derivative of the `C¹`/`C²` fields `∇ΧTilde`, `∇Χ`, `∇X⁻¹`, and
`div`/`gradDiv` of jointly `C^∞` fields. -/

@[expose] public section

noncomputable section

open Filter Topology Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)

/-! ### Odd sums weighted by `ξ_{m,k}` -/

/-- `∑_k ξ_{m,k}(t) g_k(t,x)` is continuous when each `g_k` is. -/
theorem tc_xi_tsum_continuousOn {g : {k : ℤ // Odd k} → ℝ → Vec 2 → ℝ}
    (hg : ∀ k, ContinuousOn (fun p : ℝ × Vec 2 => g k p.1 p.2) tcU) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k p.1 * g k p.1 p.2) tcU := by
  refine tc_odd_continuousOn_tsum I m (g := fun k p => I.xiMK m k.1 p.1 * g k p.1 p.2) ?_ ?_
  · intro k
    exact ((Integration.contDiff_xiMK I m k.1).continuous.comp continuous_fst).continuousOn.mul
      (hg k)
  · intro k t h x
    simp [h.self_of_nhds]

/-- A product of continuous coordinates, in the shape `⟨u, M v⟩`. -/
theorem tc_vecDot_mulVec_continuousOn {u : ℝ → Vec 2 → Vec 2} {M : ℝ → Vec 2 → Matrix (Fin 2) (Fin
    2) ℝ}
    {w : ℝ → Vec 2 → Vec 2}
    (hu : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => u p.1 p.2 i) tcU)
    (hM : ∀ i j, ContinuousOn (fun p : ℝ × Vec 2 => M p.1 p.2 i j) tcU)
    (hw : ∀ j, ContinuousOn (fun p : ℝ × Vec 2 => w p.1 p.2 j) tcU) :
    ContinuousOn (fun p : ℝ × Vec 2 => vecDot (u p.1 p.2) ((M p.1 p.2).mulVec (w p.1 p.2))) tcU :=
        by
  simp only [vecDot, Matrix.mulVec, dotProduct]
  exact continuousOn_finsetSum _ fun i _ => (hu i).mul
    (continuousOn_finsetSum _ fun j _ => (hM i j).mul (hw j))

/-- A product of continuous coordinates, in the shape `⟨u, v⟩`. -/
theorem tc_vecDot_continuousOn {u v : ℝ × Vec 2 → Vec 2}
    (hu : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => u p i) tcU)
    (hv : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => v p i) tcU) :
    ContinuousOn (fun p : ℝ × Vec 2 => vecDot (u p) (v p)) tcU := by
  simp only [vecDot]
  exact continuousOn_finsetSum _ fun i _ => (hu i).mul (hv i)

/-- The coordinates of the twisted corrector are continuous. -/
theorem tc_chiTilde_continuousOn (κm : ℝ) (k : ℤ) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => I.chiTilde hΦ m κm k p.1 p.2 i) tcU :=
  (tc_chiTilde_contDiffOn I hΦ m κm k i).continuousOn

/-- The coordinates of the pulled gradient are continuous. -/
theorem tc_G_continuousOn (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => G I hΦ m T l p.1 p.2 i) tcU :=
  (tc_G_contDiffOn I hΦ m l hT i).continuousOn

/-- The coordinates of the flow-gradient matrix are continuous. -/
theorem tc_flowGradK_continuousOn (k : ℤ) (i j : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => flowGradK I hΦ m k p.1 p.2 i j) tcU :=
  (tc_flowGradK_contDiffOn I hΦ m k i j).continuousOn

/-! ### `cutoff1` -/

/-- `cutoff1` of a smooth `T` is jointly continuous on the open half space. -/
theorem tc_cutoff1_continuousOn (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => cutoff1 I hΦ m κm T p.1 p.2) tcU := by
  unfold cutoff1
  refine tc_odd_continuousOn_tsum I m (g := fun k p =>
    deriv (I.xiMK m k.1) p.1 *
      vecDot (I.chiTilde hΦ m κm k.1 p.1 p.2) (G I hΦ m T (lIdx β I.Λ m k.1) p.1 p.2)) ?_ ?_
  · intro k
    have hxi : Continuous (fun p : ℝ × Vec 2 => deriv (I.xiMK m k.1) p.1) :=
      ((Integration.contDiff_xiMK I m k.1).continuous_deriv (by simp)).comp continuous_fst
    exact hxi.continuousOn.mul (tc_vecDot_continuousOn
      (fun i => tc_chiTilde_continuousOn I hΦ m κm k.1 i)
      (fun i => tc_G_continuousOn I hΦ m (lIdx β I.Λ m k.1) hT i))
  · intro k t h x
    simp [tc_deriv_xiMK_eq_zero I m k.1 h]

/-! ### Matrix-vector helper -/

/-- Coordinates of `A v` are jointly `C^n` when those of `A` and `v` are. -/
theorem tc_mulVec_contDiffOn {n : WithTop ℕ∞} {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2}
    (hA : ∀ i j, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => A p.1 p.2 i j) tcU)
    (hv : ∀ j, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => v p.1 p.2 j) tcU) (i : Fin 2) :
    ContDiffOn ℝ n (fun p : ℝ × Vec 2 => (A p.1 p.2).mulVec (v p.1 p.2) i) tcU := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => (hA i j).mul (hv j)

/-- The averaged forcing matrix `𝐊_m + 𝐬_{m-1}` is jointly `C^∞`. -/
theorem tc_KmatAddSMat_contDiffOn (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      (I.Kmat κm m p.1 + I.sMat hΦ m κm p.1 p.2) i j) tcU :=
  (Section5.RelativeError.contDiff_matrix_entry
    ((Section5.RelativeError.Kmat_joint_contDiff I hm hκm).add
      (Section5.RelativeError.sMat_joint_contDiff I hΦ hm hκm)) i j).contDiffOn

/-- The gradient coordinates of a smooth `T` are jointly `C^∞` on the open half space. -/
theorem tc_spaceGrad_T_contDiffOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2 j) tcU :=
  Integration.contDiffOn_spaceGrad_slice_Ioi
    (hT.mono (Set.prod_mono Set.Ioi_subset_Ici_self le_rfl)) j

/-! ### `twistie1` -/

/-- `twistie1` of a smooth `T` is jointly continuous on the open half space. -/
theorem tc_twistie1_continuousOn (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie1 I hΦ m κm T p.1 p.2) tcU := by
  unfold twistie1
  have hV : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      ((I.Kmat κm m p.1 + I.sMat hΦ m κm p.1 p.2).mulVec (spaceGrad (T p.1) p.2)) i) tcU :=
    tc_mulVec_contDiffOn (A := fun t x => I.Kmat κm m t + I.sMat hΦ m κm t x)
      (v := fun t x => spaceGrad (T t) x) (tc_KmatAddSMat_contDiffOn I hΦ m hm hκm)
      (tc_spaceGrad_T_contDiffOn hT)
  have hgd : ∀ j, ContinuousOn (fun p : ℝ × Vec 2 =>
      gradDiv (fun s y => (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec (spaceGrad (T s) y))
        p.1 p.2 j) tcU := fun j =>
    (tc_gradDiv_contDiffOn (m := 0) (n := ∞) (by simp) hV j).continuousOn
  refine tc_xi_tsum_continuousOn I m (g := fun k t x =>
    vecDot (I.chiTilde hΦ m κm k.1 t x)
      ((flowGradK I hΦ m k.1 t x).mulVec
        (gradDiv (fun s y => (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
          (spaceGrad (T s) y)) t x))) fun k => ?_
  exact tc_vecDot_mulVec_continuousOn (fun i => tc_chiTilde_continuousOn I hΦ m κm k.1 i)
    (fun i j => tc_flowGradK_continuousOn I hΦ m k.1 i j) hgd

/-! ### Divergence-form fluxes of `twistie4`, `twistie5` -/

/-- The `i`-th coordinate of `∑_k ξ_{m,k}(t) g_k(t,x)` is jointly `C^n` when those of each `g_k`
    are. -/
theorem tc_xi_tsum_vec_contDiffOn {n : WithTop ℕ∞} (hn : n ≤ ∞) {g : {k : ℤ // Odd k} → ℝ → Vec 2
    → Vec 2}
    (hg : ∀ k j, ContDiffOn ℝ n (fun p : ℝ × Vec 2 => g k p.1 p.2 j) tcU) (i : Fin 2) :
    ContDiffOn ℝ n (fun p : ℝ × Vec 2 =>
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k p.1 • g k p.1 p.2) i) tcU := by
  have h := tc_odd_contDiffOn_tsum I m (n := n)
    (g := fun k p => I.xiMK m k.1 p.1 • g k p.1 p.2) (fun k => contDiffOn_pi.2 fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (((Integration.contDiff_xiMK I m k.1).of_le hn).comp
        contDiff_fst).contDiffOn.mul (hg k j)) (by
      intro k t h x
      simp [h.self_of_nhds])
  exact contDiffOn_pi.1 h i

/-- The matrix field inside the flux of `twistie4` is jointly `C¹`. -/
theorem tc_twistie4Field_contDiffOn (κm : ℝ) (k : ℤ) (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      (κm • ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 z) p.2 - 1) *
        gradMatrix (fun z => I.chiMK κm m k p.1 z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2))) i j) tcU := by
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, smul_eq_mul]
  refine contDiffOn_const.mul (ContDiffOn.sum fun a _ => ContDiffOn.mul ?_ ?_)
  · exact ((tc_gradXInv_contDiffOn I hΦ m (lIdx β I.Λ m k) i a).of_le (by simp)).sub
      contDiffOn_const
  · exact tc_gradChiMK_comp_contDiffOn I hΦ m κm k (lIdx β I.Λ m k) a j

/-- The flux `∑_k ξ_k D_k G_k` of `twistie4` is jointly `C¹` on the open half space. -/
theorem tc_twistie4Flux_contDiffOn (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k p.1 • (κm •
        ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 z) p.2 - 1) *
          gradMatrix (fun z => I.chiMK κm m k p.1 z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2))).mulVec
        (G I hΦ m T (lIdx β I.Λ m k) p.1 p.2)) i) tcU :=
  tc_xi_tsum_vec_contDiffOn I m (n := 1) (by simp)
    (g := fun k t y => (κm •
        ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t z) y - 1) *
          gradMatrix (fun z => I.chiMK κm m k.1 t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y))).mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t y))
    (fun k j => tc_mulVec_contDiffOn (n := 1)
      (A := fun t y => κm •
        ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t z) y - 1) *
          gradMatrix (fun z => I.chiMK κm m k.1 t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y)))
      (v := fun t y => G I hΦ m T (lIdx β I.Λ m k.1) t y)
      (fun a b => tc_twistie4Field_contDiffOn I hΦ m κm k.1 a b)
      (fun b => (tc_G_contDiffOn I hΦ m (lIdx β I.Λ m k.1) hT b).of_le (by simp)) j) i

/-- `twistie4` of a smooth `T` is jointly continuous on the open half space. -/
theorem tc_twistie4_continuousOn (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie4 I hΦ m κm T p.1 p.2) tcU := by
  unfold twistie4
  refine ContinuousOn.neg ?_
  exact (tc_vecDiv_contDiffOn (m := 0) (n := 1) (by norm_num)
    (V := fun t y => ∑' k : {k : ℤ // Odd k}, I.xiMK m k t • (κm •
      ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) *
        gradMatrix (fun z => I.chiMK κm m k t z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y))
    (fun i => tc_twistie4Flux_contDiffOn I hΦ m κm hT i)).continuousOn

/-! ### `twistie5` -/

/-- The matrix field inside the flux of `twistie5` is jointly `C¹`. -/
theorem tc_twistie5Field_contDiffOn (κm : ℝ) (k : ℤ) (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      ((1 - (flowGradK I hΦ m k p.1 p.2).transpose) *
        ((I.hatZetaML m (lIdx β I.Λ m k) p.1 * I.zetaMK m k p.1 *
            psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2)) • sigmaMat +
          κm • gradMatrix (fun z => I.chiMK κm m k p.1 z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2))) i j) tcU := by
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  refine ContDiffOn.sum fun a _ => ContDiffOn.mul ?_ ?_
  · exact contDiffOn_const.sub ((tc_flowGradK_contDiffOn I hΦ m k a i).of_le (by simp))
  · exact (((tc_psiCoeff_contDiffOn I hΦ m k).of_le (by simp)).mul contDiffOn_const).add
      (contDiffOn_const.mul (tc_gradChiMK_comp_contDiffOn I hΦ m κm k (lIdx β I.Λ m k) a j))

/-- The flux `∑_k ξ_k E_k G_k` of `twistie5` is jointly `C¹` on the open half space. -/
theorem tc_twistie5Flux_contDiffOn (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k p.1 • ((1 - (flowGradK I hΦ m k p.1 p.2).transpose) *
        ((I.hatZetaML m (lIdx β I.Λ m k) p.1 * I.zetaMK m k p.1 *
            psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2)) • sigmaMat +
          κm • gradMatrix (fun z => I.chiMK κm m k p.1 z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2))).mulVec
        (G I hΦ m T (lIdx β I.Λ m k) p.1 p.2)) i) tcU :=
  tc_xi_tsum_vec_contDiffOn I m (n := 1) (by simp)
    (g := fun k t y => ((1 - (flowGradK I hΦ m k.1 t y).transpose) *
        ((I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
            psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y)) • sigmaMat +
          κm • gradMatrix (fun z => I.chiMK κm m k.1 t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y))).mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t y))
    (fun k j => tc_mulVec_contDiffOn (n := 1)
      (A := fun t y => (1 - (flowGradK I hΦ m k.1 t y).transpose) *
        ((I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
            psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y)) • sigmaMat +
          κm • gradMatrix (fun z => I.chiMK κm m k.1 t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y)))
      (v := fun t y => G I hΦ m T (lIdx β I.Λ m k.1) t y)
      (fun a b => tc_twistie5Field_contDiffOn I hΦ m κm k.1 a b)
      (fun b => (tc_G_contDiffOn I hΦ m (lIdx β I.Λ m k.1) hT b).of_le (by simp)) j) i

/-- `twistie5` of a smooth `T` is jointly continuous on the open half space. -/
theorem tc_twistie5_continuousOn (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => twistie5 I hΦ m κm T p.1 p.2) tcU := by
  unfold twistie5
  refine ContinuousOn.neg ?_
  exact (tc_vecDiv_contDiffOn (m := 0) (n := 1) (by norm_num)
    (V := fun t y => ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      ((1 - (flowGradK I hΦ m k t y).transpose) *
        ((I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
            psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
          κm • gradMatrix (fun z => I.chiMK κm m k t z)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y))
    (fun i => tc_twistie5Flux_contDiffOn I hΦ m κm hT i)).continuousOn

/-! ### Corrector flux -/

/-! ### `normie3` -/

/-- The unpulled cell-flux matrix entries are jointly continuous on the open half space. -/
theorem tc_cellFlux_continuousOn (κm : ℝ) (k : ℤ) (i j : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => cellFlux I hΦ m κm k p.1 p.2 i j) tcU := by
  unfold cellFlux selCoeff
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine continuousOn_finsetSum _ fun a _ => ContinuousOn.mul ?_ ?_
  · exact continuousOn_const.add
      ((tc_psiCoeff_contDiffOn I hΦ m k).continuousOn.mul continuousOn_const)
  · exact continuousOn_const.add
      ((tc_gradChiMK_comp_contDiffOn I hΦ m κm k (lIdx β I.Λ m k) a j).continuousOn)

/-- `normie3` of a smooth `T` is jointly continuous on the open half space. -/
theorem tc_normie3_continuousOn (hm : 1 ≤ m) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => normie3 I hΦ m κm T p.1 p.2) tcU := by
  unfold normie3
  refine tc_xi_tsum_continuousOn I m (g := fun k t x =>
    frob ((flowGradK I hΦ m k.1 t x).transpose * (I.flux κm m t - cellFlux I hΦ m κm k.1 t x))
      (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) fun k => ?_
  simp only [frob, Matrix.mul_apply, Matrix.sub_apply, Matrix.transpose_apply]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  refine ContinuousOn.mul (continuousOn_finsetSum _ fun a _ => ContinuousOn.mul ?_
      (ContinuousOn.sub ?_ ?_)) ?_
  · exact tc_flowGradK_continuousOn I hΦ m k.1 a i
  · exact ((Infra.Section3.flux_entry_time_continuous I hm κm a j).comp continuous_fst).continuousOn
  · exact tc_cellFlux_continuousOn I hΦ m κm k.1 a j
  · exact (tc_gradG_contDiffOn I hΦ m (lIdx β I.Λ m k.1) hT i j).continuousOn

end AVenhance.Infra.Section5.Contracts
