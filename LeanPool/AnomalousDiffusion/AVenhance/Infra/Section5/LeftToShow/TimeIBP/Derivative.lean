/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Defs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.PeriodicSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Liouville
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation

/-! # Time derivative of `∫ ∂_iT ∂_jT`

Source: `enhance.tex` 8780–8800.  For a divergence-free smooth periodic drift `b`, the drift terms
of `D_t ∇T = ∂_t ∇T + b·∇∇T` cancel in `∫ (D_t∂_iT ∂_jT + ∂_iT D_t∂_jT)`, since they integrate
to `∫ b·∇(∂_iT ∂_jT) = -∫ (∇·b) ∂_iT ∂_jT = 0`.  We also build the continuous extension
`matGradExt` of `D_t ∇T` to the closed half-space `t ≥ 0`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

/-- The closed half-space `t ≥ 0`. -/
def halfSpace : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ Set.univ

/-- The `i`-th spatial gradient component as a function on space-time. -/
def gradCoord (T : ℝ → Vec 2 → ℝ) (i : Fin 2) (p : ℝ × Vec 2) : ℝ := spaceGrad (T p.1) p.2 i

theorem uniqueDiffOn_halfSpace : UniqueDiffOn ℝ halfSpace :=
  UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ

theorem isOpen_posSpace : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
  isOpen_Ioi.prod isOpen_univ

theorem posSpace_subset_halfSpace :
    Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ⊆ halfSpace :=
  Set.prod_mono Set.Ioi_subset_Ici_self subset_rfl

theorem halfSpace_mem_nhds {t : ℝ} (ht : 0 < t) (x : Vec 2) : halfSpace ∈ 𝓝 (t, x) :=
  Filter.mem_of_superset (isOpen_posSpace.mem_nhds ⟨ht, trivial⟩) posSpace_subset_halfSpace

section Smooth

variable {T : ℝ → Vec 2 → ℝ}

theorem gradCoord_contDiffOn
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (gradCoord T i) halfSpace := by
  have h1 := (hT.fderivWithin uniqueDiffOn_halfSpace (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiffOn_const (c := ((0 : ℝ), basisVec i)))
  refine h1.congr ?_
  intro p hp
  exact fderiv_slice_eq_fderivWithin hT hp.1 p.2 (basisVec i)

theorem gradCoord_slice_contDiff
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞) (fun y => gradCoord T i (t, y)) := by
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) Set.univ :=
    contDiffOn_const.prodMk contDiffOn_id
  have hcomp := (gradCoord_contDiffOn hT i).comp hmap fun x _ => ⟨ht, mem_univ _⟩
  exact contDiffOn_univ.mp hcomp

theorem differentiableAt_gradCoord
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) : DifferentiableAt ℝ (gradCoord T i) (t, x) :=
  (((gradCoord_contDiffOn hT i).contDiffAt (halfSpace_mem_nhds ht x))).differentiableAt (by simp)

theorem hasDerivAt_gradCoord_time
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun r => gradCoord T i (r, x))
      (fderiv ℝ (gradCoord T i) (t, x) (1, 0)) t := by
  have hf := (differentiableAt_gradCoord hT i ht x).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  simpa [Function.comp_def] using hf.comp_hasDerivAt t hline

/-- Restricting a space-time derivative to a spatial direction. -/
theorem fderiv_spatial_eq {G : ℝ × Vec 2 → ℝ} {t : ℝ} {x : Vec 2}
    (hG : DifferentiableAt ℝ G (t, x)) (v : Vec 2) :
    fderiv ℝ G (t, x) (0, v) = fderiv ℝ (fun y => G (t, y)) x v := by
  have hspace : HasFDerivAt (fun y => G (t, y))
      ((fderiv ℝ G (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x :=
    hG.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [hspace.fderiv]
  simp

/-- At positive times the material gradient is the time derivative plus the advective term. -/
theorem materialGrad_apply_eq {b : ℝ → Vec 2 → Vec 2}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) (i : Fin 2) :
    materialGrad b T t x i = fderiv ℝ (gradCoord T i) (t, x) (1, 0) +
      fderiv ℝ (fun y => gradCoord T i (t, y)) x (b t x) := by
  have h1 : materialGrad b T t x i = fderiv ℝ (gradCoord T i) (t, x) (1, b t x) := rfl
  have h2 : ((1 : ℝ), b t x) = ((1 : ℝ), (0 : Vec 2)) + ((0 : ℝ), b t x) := by simp
  rw [h1, h2, map_add, fderiv_spatial_eq (differentiableAt_gradCoord hT i ht x)]

/-- The continuous extension of `D_t ∇T` to `t ≥ 0`. -/
def matGradExt (b : ℝ → Vec 2 → Vec 2) (T : ℝ → Vec 2 → ℝ) (i : Fin 2) (p : ℝ × Vec 2) : ℝ :=
  fderivWithin ℝ (gradCoord T i) halfSpace p (1, b p.1 p.2)

theorem matGradExt_eq_materialGrad {b : ℝ → Vec 2 → Vec 2} {t : ℝ} (ht : 0 < t) (x : Vec 2)
    (i : Fin 2) : matGradExt b T i (t, x) = materialGrad b T t x i := by
  unfold matGradExt
  rw [fderivWithin_of_mem_nhds (halfSpace_mem_nhds ht x)]
  rfl

theorem matGradExt_continuousOn {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2) :
    ContinuousOn (matGradExt b T i) halfSpace := by
  have h1 := (gradCoord_contDiffOn hT i).continuousOn_fderivWithin uniqueDiffOn_halfSpace
    (by simp)
  have h2 : ContinuousOn (fun p : ℝ × Vec 2 => ((1 : ℝ), b p.1 p.2)) halfSpace :=
    continuousOn_const.prodMk (hb.smooth.continuous.comp continuous_id).continuousOn
  exact h1.clm_apply h2

end Smooth

section Drift

/-- A linear functional evaluated on a vector is the dot product with its values on the basis. -/
theorem clm_apply_eq_vecDot (L : Vec 2 →L[ℝ] ℝ) (v : Vec 2) :
    L v = vecDot v (fun k => L (basisVec k)) := by
  have hbasis : v = ∑ k : Fin 2, (v k) • basisVec k := by
    funext j
    fin_cases j <;> simp [basisVec, Fin.sum_univ_two]
  conv_lhs => rw [hbasis]
  simp [vecDot, Fin.sum_univ_two]

/-- `∇·b` as the sum of coordinate derivatives of the slice. -/
theorem spatialDivergence_eq_sum {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence b t x = ∑ k : Fin 2, spaceGrad (fun y => b t y k) x k := by
  rw [Infra.Flow.spatialDivergence, Infra.Flow.jointSpatialFDeriv_eq_slice hb]
  rw [Fin.sum_univ_two]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (b t) :=
    hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (b t) x := hsmooth.differentiable (by simp) x
  have h0 := fderiv_apply hd 0
  have h1 := fderiv_apply hd 1
  have h0' : fderiv ℝ (fun y => b t y 0) x (basisVec 0) = fderiv ℝ (b t) x (basisVec 0) 0 := by
    rw [h0]
    rfl
  have h1' : fderiv ℝ (fun y => b t y 1) x (basisVec 1) = fderiv ℝ (b t) x (basisVec 1) 1 := by
    rw [h1]
    rfl
  change fderiv ℝ (b t) x (basisVec 0) 0 + fderiv ℝ (b t) x (basisVec 1) 1 =
    fderiv ℝ (fun y => b t y 0) x (basisVec 0) + fderiv ℝ (fun y => b t y 1) x (basisVec 1)
  rw [h0', h1']

theorem continuous_slice_drift {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (t : ℝ) : Continuous (b t) :=
  hb.smooth.continuous.comp (Continuous.prodMk (f := fun _ : Vec 2 => t) continuous_const
    continuous_id)

/-- The advective term `b·∇(∂_iT ∂_jT)`. -/
def driftTerm (b : ℝ → Vec 2 → Vec 2) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (i j : Fin 2)
    (x : Vec 2) : ℝ :=
  vecDot (b t x) (spaceGrad (fun y => gradCoord T i (t, y) * gradCoord T j (t, y)) x)

variable {T : ℝ → Vec 2 → ℝ}

/-- Product rule for the advective terms. -/
theorem fderiv_mul_add_eq_driftTerm {b : ℝ → Vec 2 → Vec 2}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) {t : ℝ}
    (ht : 0 ≤ t) (i j : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y => gradCoord T i (t, y)) x (b t x) * gradCoord T j (t, x) +
        gradCoord T i (t, x) * fderiv ℝ (fun y => gradCoord T j (t, y)) x (b t x) =
      driftTerm b T t i j x := by
  have hi := (gradCoord_slice_contDiff hT i ht).differentiable (by simp) x
  have hj := (gradCoord_slice_contDiff hT j ht).differentiable (by simp) x
  unfold driftTerm spaceGrad
  rw [← clm_apply_eq_vecDot (fderiv ℝ (fun y => gradCoord T i (t, y) * gradCoord T j (t, y)) x)
    (b t x), fderiv_fun_mul hi hj]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem driftTerm_continuous {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) {t : ℝ}
    (ht : 0 ≤ t) (i j : Fin 2) : Continuous (driftTerm b T t i j) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y => gradCoord T i (t, y) * gradCoord T j (t, y)) :=
    (gradCoord_slice_contDiff hT i ht).mul (gradCoord_slice_contDiff hT j ht)
  have hgrad : Continuous (spaceGrad fun y => gradCoord T i (t, y) * gradCoord T j (t, y)) := by
    refine continuous_pi fun k => ?_
    exact (hP.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbt : Continuous (b t) := continuous_slice_drift hb t
  unfold driftTerm vecDot
  exact continuous_finsetSum _ fun k _ => ((continuous_apply k).comp hbt).mul
    ((continuous_apply k).comp hgrad)

/-- The advective terms integrate to zero for a divergence-free periodic drift. -/
theorem integral_driftTerm_eq_zero {b : ℝ → Vec 2 → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, Infra.Flow.spatialDivergence b t x = 0)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace)
    (hTper : ∀ t, 0 ≤ t → IsZ2Periodic (T t)) {t : ℝ} (ht : 0 ≤ t) (i j : Fin 2) :
    ∫ x in unitCube, driftTerm b T t i j x = 0 := by
  set P : Vec 2 → ℝ := fun y => gradCoord T i (t, y) * gradCoord T j (t, y) with hPdef
  have hgi := gradCoord_slice_contDiff hT i ht
  have hgj := gradCoord_slice_contDiff hT j ht
  have hP : ContDiff ℝ 1 P := (hgi.mul hgj).of_le (by simp)
  -- periodicity of the gradient components
  have hTslice : ContDiff ℝ 1 (T t) := by
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hcomp := hT.comp hmap fun x _ => ⟨ht, mem_univ _⟩
    exact ((contDiffOn_univ.mp hcomp : ContDiff ℝ (⊤ : ℕ∞) fun x => T t x)).of_le (by simp)
  have hgradPer := isZ2Periodic_spaceGrad hTslice (hTper t ht)
  have hcoordPer : ∀ k : Fin 2, IsZ2Periodic (fun y => gradCoord T k (t, y)) :=
    fun k n x => congrArg (fun v : Vec 2 => v k) (hgradPer n x)
  have hPper : IsZ2Periodic P := by
    intro n x
    change gradCoord T i (t, x + latticeShift n) * gradCoord T j (t, x + latticeShift n) = _
    have h1 := hcoordPer i n x
    have h2 := hcoordPer j n x
    simp only at h1 h2
    rw [h1, h2]
  -- the drift component functions
  have hbt : ContDiff ℝ (⊤ : ℕ∞) (b t) := hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hbk : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => b t y k) := fun k =>
    ((contDiff_pi.mp hbt k)).of_le (by simp)
  have hbper : ∀ k : Fin 2, IsZ2Periodic (fun y => b t y k) := by
    intro k n x
    have := hb.periodic 0 n t x
    simp only [Int.cast_zero, add_zero] at this
    exact congrArg (fun v : Vec 2 => v k) this
  have hcontP : Continuous (spaceGrad P) := by
    refine continuous_pi fun k => ?_
    exact (hP.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontb : ∀ k : Fin 2, Continuous fun y => spaceGrad (fun z => b t z k) y k := fun k =>
    ((hbk k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hibp : ∀ k : Fin 2, (∫ x in unitCube, b t x k * spaceGrad P x k) =
      -∫ x in unitCube, spaceGrad (fun z => b t z k) x k * P x :=
    fun k => integral_unitCube_mul_spaceGrad (hbk k) hP (hbper k) hPper k
  have hint1 : ∀ k : Fin 2, IntegrableOn (fun x => b t x k * spaceGrad P x k) unitCube := fun k =>
    integrableOn_unitCube_of_continuous
      (((continuous_apply k).comp (continuous_slice_drift hb t)).mul
        ((continuous_apply k).comp hcontP))
  have hint2 : ∀ k : Fin 2, IntegrableOn (fun x => spaceGrad (fun z => b t z k) x k * P x)
      unitCube := fun k =>
    integrableOn_unitCube_of_continuous ((hcontb k).mul (hP.continuous))
  unfold driftTerm
  have hsum : (∫ x in unitCube, vecDot (b t x) (spaceGrad P x)) =
      ∑ k : Fin 2, ∫ x in unitCube, b t x k * spaceGrad P x k := by
    simp only [vecDot]
    exact integral_finsetSum _ fun k _ => hint1 k
  rw [hsum]
  simp only [hibp, Fin.sum_univ_two]
  have hzero : ∀ x, spaceGrad (fun z => b t z 0) x 0 * P x +
      spaceGrad (fun z => b t z 1) x 1 * P x = 0 := by
    intro x
    have h := hdiv t x
    rw [spatialDivergence_eq_sum hb, Fin.sum_univ_two] at h
    rw [← add_mul, h, zero_mul]
  have hdivint : (∫ x in unitCube, (spaceGrad (fun z => b t z 0) x 0 * P x +
      spaceGrad (fun z => b t z 1) x 1 * P x)) = 0 := by simp [hzero]
  rw [integral_add (hint2 0) (hint2 1)] at hdivint
  linarith

/-- `∂_t ∫ ∂_iT ∂_jT = ∫ (D_t∂_iT ∂_jT + ∂_iT D_t∂_jT)` for a divergence-free periodic drift. -/
theorem hasDerivAt_integral_gradProduct {b : ℝ → Vec 2 → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, Infra.Flow.spatialDivergence b t x = 0) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTper : ∀ t, 0 ≤ t → IsZ2Periodic (T t)) {t : ℝ} (ht : 0 < t) (i j : Fin 2) :
    HasDerivAt (fun s => ∫ x in unitCube, spaceGrad (T s) x i * spaceGrad (T s) x j)
      (∫ x in unitCube, (materialGrad b T t x i * spaceGrad (T t) x j +
        spaceGrad (T t) x i * materialGrad b T t x j)) t := by
  have hT' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace := hT
  have hGi : ContDiffOn ℝ (⊤ : ℕ∞) (gradCoord T i) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (gradCoord_contDiffOn hT' i).mono posSpace_subset_halfSpace
  have hGj : ContDiffOn ℝ (⊤ : ℕ∞) (gradCoord T j) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (gradCoord_contDiffOn hT' j).mono posSpace_subset_halfSpace
  have hDi : ContinuousOn (fun p => fderiv ℝ (gradCoord T i) p (1, 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (hGi.continuousOn_fderiv_of_isOpen isOpen_posSpace (by simp)).clm_apply continuousOn_const
  have hDj : ContinuousOn (fun p => fderiv ℝ (gradCoord T j) p (1, 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (hGj.continuousOn_fderiv_of_isOpen isOpen_posSpace (by simp)).clm_apply continuousOn_const
  have key := hasDerivAt_integral_unitCube
    (h := fun s x => gradCoord T i (s, x) * gradCoord T j (s, x))
    (h' := fun s x => fderiv ℝ (gradCoord T i) (s, x) (1, 0) * gradCoord T j (s, x) +
      gradCoord T i (s, x) * fderiv ℝ (gradCoord T j) (s, x) (1, 0))
    (hGi.continuousOn.mul hGj.continuousOn)
    (fun s hs x => (hasDerivAt_gradCoord_time hT' i hs x).mul (hasDerivAt_gradCoord_time hT' j hs
        x))
    ((hDi.mul hGj.continuousOn).add (hGi.continuousOn.mul hDj)) ht
  refine key.congr_deriv ?_
  have hcont : Continuous fun x : Vec 2 =>
      fderiv ℝ (gradCoord T i) (t, x) (1, 0) * gradCoord T j (t, x) +
        gradCoord T i (t, x) * fderiv ℝ (gradCoord T j) (t, x) (1, 0) := by
    have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
    have hmem : ∀ x : Vec 2, (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) :=
      fun x => ⟨ht, trivial⟩
    exact (((hDi.mul hGj.continuousOn).add (hGi.continuousOn.mul hDj)).comp_continuous hline hmem)
  have hpt : ∀ x, materialGrad b T t x i * spaceGrad (T t) x j +
      spaceGrad (T t) x i * materialGrad b T t x j =
      (fderiv ℝ (gradCoord T i) (t, x) (1, 0) * gradCoord T j (t, x) +
        gradCoord T i (t, x) * fderiv ℝ (gradCoord T j) (t, x) (1, 0)) + driftTerm b T t i j x := by
    intro x
    rw [← fderiv_mul_add_eq_driftTerm (b := b) hT' ht.le i j x, materialGrad_apply_eq hT' ht x i,
      materialGrad_apply_eq hT' ht x j]
    change (_ + _) * gradCoord T j (t, x) + gradCoord T i (t, x) * (_ + _) = _
    ring
  simp_rw [hpt]
  rw [integral_add (integrableOn_unitCube_of_continuous hcont)
    (integrableOn_unitCube_of_continuous (driftTerm_continuous hb hT' ht.le i j)),
    integral_driftTerm_eq_zero hb hdiv hT' hTper ht.le i j, add_zero]

end Drift

end AVenhance.Infra.Section5.LeftToShow

end
