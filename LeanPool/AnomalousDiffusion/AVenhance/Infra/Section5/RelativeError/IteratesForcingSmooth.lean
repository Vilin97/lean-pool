/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Regularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalJointSmoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.TForcing

/-! # RelativeError item 13: smoothness and periodicity of the iterate forcing `TForcing`

The forcing `∇·((𝐊_m − κ_{m-1} I + 𝐬_{m-1}) ∇T^{(i-1)})` is jointly `C^∞` on `[0,∞) × ℝ²` and
`ℤ²`-periodic in `x`, whenever `T^{(i-1)}` is `C^∞` on `[0,∞) × ℝ²` (resp. periodic).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped Matrix.Norms.Elementwise ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-! ### Slices of jointly smooth functions on the closed half-space -/

/-- The spatial gradient of a slice, as a partial derivative of the joint map within `s`. -/
theorem spaceGrad_slice_eq_fderivWithin {F : ℝ × Vec 2 → ℝ} {s : Set (ℝ × Vec 2)} (t : ℝ)
    (x : Vec 2) (hs : ∀ y, (t, y) ∈ s) (hF : DifferentiableWithinAt ℝ F s (t, x)) (j : Fin 2) :
    spaceGrad (fun y => F (t, y)) x j = fderivWithin ℝ F s (t, x) (0, basisVec j) := by
  have hd : HasFDerivWithinAt F (fderivWithin ℝ F s (t, x)) s (t, x) := hF.hasFDerivWithinAt
  have hc := hd.comp x (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt (s := Set.univ)
    (fun y _ => hs y)
  rw [hasFDerivWithinAt_univ] at hc
  simp only [spaceGrad]
  rw [show (fun y => F (t, y)) = F ∘ (fun y => (t, y)) from rfl, hc.fderiv]
  rfl

/-- A function `C^∞` on `[0,∞) × ℝ²` is `C^∞` on each slice at a nonnegative time. -/
theorem slice_contDiff_of_contDiffOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞) (T t) := by
  have h : ContDiffOn ℝ (⊤ : ℕ∞) ((fun p : ℝ × Vec 2 => T p.1 p.2) ∘ (fun y : Vec 2 => (t, y)))
      Set.univ :=
    hT.comp (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact contDiffOn_univ.mp h

/-- Each component of the spatial gradient of a `C^∞`-on-`[0,∞) × ℝ²` function is again
`C^∞` on `[0,∞) × ℝ²`, jointly in `(t,x)`. -/
theorem contDiffOn_spaceGrad_slice {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => spaceGrad (F p.1) p.2 j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hs
  have hsu : UniqueDiffOn ℝ s := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        fderivWithin ℝ (fun q : ℝ × Vec 2 => F q.1 q.2) s p (0, basisVec j)) s :=
    (hF.fderivWithin hsu (by simp)).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact spaceGrad_slice_eq_fderivWithin (F := fun q : ℝ × Vec 2 => F q.1 q.2) (s := s) t x
    (fun y => ⟨ht, trivial⟩) (hF.differentiableOn (by simp) (t, x) ⟨ht, trivial⟩) j

/-! ### Matrix-valued smoothness helpers -/

theorem contDiff_matrix_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}
    {f : E → Matrix (Fin 2) (Fin 2) ℝ} (h : ∀ i j, ContDiff ℝ n (fun x => f x i j)) :
    ContDiff ℝ n f :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j => h i j

theorem contDiff_matrix_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}
    {f : E → Matrix (Fin 2) (Fin 2) ℝ} (h : ContDiff ℝ n f) (i j : Fin 2) :
    ContDiff ℝ n (fun x => f x i j) :=
  contDiff_pi.1 (contDiff_pi.1 h i) j

/-! ### Joint smoothness of `𝐬_{m-1}` -/

section SMat

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The matrix `𝐊_m(t)` is jointly `C^∞` in `(t,x)` (constant in `x`). -/
theorem Kmat_joint_contDiff {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => I.Kmat κ m p.1) :=
  (Kmat_contDiff_top I hm hκ).comp contDiff_fst

/-- The averaged coefficient `𝐬_{m-1}` is jointly `C^∞` in `(t,x)` on all of `ℝ × ℝ²`. -/
theorem sMat_joint_contDiff (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => I.sMat hΦ m κm p.1 p.2) := by
  apply (Infra.Section4.sMat_coarseCoeffForm I hΦ m κm).joint_contDiff hm
    (Kmat_joint_contDiff I hm hκm)
  intro l
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l i j

end SMat

/-! ### Smoothness of the forcing -/

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The iterate forcing is jointly `C^∞` on `[0,∞) × ℝ²` if the previous iterate is. -/
theorem TForcing_contDiffOn (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (κprev : ℝ) {Tprev : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => Tprev p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => I.TForcing hΦ m κm κprev Tprev p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      I.Kmat κm m p.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm p.1 p.2) :=
    ((Kmat_joint_contDiff I hm hκm).sub contDiff_const).add (sMat_joint_contDiff I hΦ hm hκm)
  have hG : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        ((I.Kmat κm m p.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm p.1 p.2).mulVec
          (spaceGrad (Tprev p.1) p.2)) i) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffOn.sum fun j _ =>
      (contDiff_matrix_entry hA i j).contDiffOn.mul (contDiffOn_spaceGrad_slice hT j)
  unfold Ingredients.TForcing vecDiv
  exact ContDiffOn.sum fun i _ =>
    contDiffOn_spaceGrad_slice
      (F := fun t y => ((I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y).mulVec (spaceGrad (Tprev t) y)) i) (hG i) i

/-! ### Periodicity of the forcing -/

/-- The spatial gradient of a `ℤ²`-periodic function is `ℤ²`-periodic. -/
theorem spaceGrad_isZ2Periodic {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) :
    IsZ2Periodic (spaceGrad f) := by
  intro k x
  have hfun : (fun y => f (y + latticeShift k)) = f := funext (hf k)
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (latticeShift k) (x := x)
  rw [hfun] at h
  funext i
  simp only [spaceGrad, ← h]

/-- The averaged coefficient `𝐬_{m-1}(t)` is `ℤ²`-periodic. -/
theorem sMat_isZ2Periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm t : ℝ) :
    IsZ2Periodic (I.sMat hΦ m κm t) := by
  apply (Infra.Section4.sMat_coarseCoeffForm I hΦ m κm).periodic t
  intro l k x
  ext i j
  exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t i j k x

/-- The iterate forcing is `ℤ²`-periodic in `x` whenever the previous iterate is. -/
theorem TForcing_periodic (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 1 ≤ m) (κm κprev : ℝ)
    {Tprev : ℝ → Vec 2 → ℝ} {t : ℝ} (_hTt : ContDiff ℝ 1 (Tprev t))
    (hTp : IsZ2Periodic (Tprev t)) :
    IsZ2Periodic (I.TForcing hΦ m κm κprev Tprev t) := by
  have hVi : ∀ i : Fin 2, IsZ2Periodic (fun y =>
      ((I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y).mulVec (spaceGrad (Tprev t) y)) i) := by
    intro i k' y
    beta_reduce
    rw [sMat_isZ2Periodic I hΦ m κm t k' y, spaceGrad_isZ2Periodic hTp k' y]
  intro k x
  unfold Ingredients.TForcing vecDiv
  exact Finset.sum_congr rfl fun i _ => congrFun (spaceGrad_isZ2Periodic (hVi i) k x) i

end AVenhance.Infra.Section5.RelativeError
