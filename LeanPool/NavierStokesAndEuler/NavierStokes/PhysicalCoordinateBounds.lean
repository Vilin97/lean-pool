/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Fixed-order bounds for the physical similarity coordinates

The inverse-coordinate jets are constructed from the actual inverse
Jacobian. Their normalized values extend smoothly to the compact set
`q = 1`, `|eta| ≤ 1`. Anisotropic homogeneity then gives a loss of at most
one power of `q` per physical derivative.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.PhysicalCoordinateBounds

open SimilarityCoordinates

abbrev Point := ℝ × (ℝ × ℝ)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

noncomputable def D (a : ℝ) : ℝ := (1 - a) / 2

noncomputable def positiveTime : Set Point := {p | 0 < p.1}

noncomputable def qCoord (a : ℝ) (p : Point) : ℝ := coordinateQ a (p.1, p.2.2)

noncomputable def inverseCoordinates (a : ℝ) (p : Point) : Point := (qCoord a p, p.2)

noncomputable def inverseDifferential (a : ℝ) (y : Point) : Point →L[ℝ] Point :=
  (((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ)).comp
    ((scalarSlope a y.2.2 y.1)⁻¹ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    (2 * y.2.2 * y.1 ^ a / scalarSlope a y.2.2 y.1) •
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) +
    (0 : Point →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] theorem inverseDifferential_apply (a : ℝ) (y v : Point) :
    inverseDifferential a y v =
      ((v.1 + 2 * y.2.2 * y.1 ^ a * v.2.2) / scalarSlope a y.2.2 y.1, v.2) := by
  apply Prod.ext
  · change (scalarSlope a y.2.2 y.1)⁻¹ * v.1 +
      (2 * y.2.2 * y.1 ^ a / scalarSlope a y.2.2 y.1) * v.2.2 + 0 = _
    ring
  · change (0 : ℝ × ℝ) + v.2 = v.2
    exact zero_add _

theorem positiveTime_isOpen : IsOpen positiveTime :=
  isOpen_lt continuous_const continuous_fst

theorem qCoord_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point}
    (hp : p ∈ positiveTime) : 0 < qCoord a p :=
  (coordinateQ_spec ha ha1 (p := (p.1, p.2.2)) hp).1

theorem qCoord_contDiffAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point}
    (hp : p ∈ positiveTime) : ContDiffAt ℝ ∞ (qCoord a) p :=
  (coordinateQ_smooth ha ha1 (p := (p.1, p.2.2)) hp).comp p
    (contDiffAt_fst.prodMk contDiffAt_snd.snd)

theorem inverseCoordinates_contDiffAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point}
    (hp : p ∈ positiveTime) : ContDiffAt ℝ ∞ (inverseCoordinates a) p :=
  (qCoord_contDiffAt ha ha1 hp).prodMk contDiffAt_snd

theorem inverseCoordinates_slope_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point}
    (hp : p ∈ positiveTime) : 0 < scalarSlope a p.2.2 (qCoord a p) := by
  have hq := coordinateQ_spec ha ha1 (p := (p.1, p.2.2)) hp
  exact scalarSlope_pos ha ha1 hq.1 (by change 0 < forwardScalar a p.2.2 (coordinateQ a (p.1,
    p.2.2)); rwa [hq.2])

theorem inverseCoordinates_hasFDerivAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point}
    (hp : p ∈ positiveTime) :
    HasFDerivAt (inverseCoordinates a) (inverseDifferential a (inverseCoordinates a p)) p := by
  have hq := ((coordinateQ_smooth ha ha1 (p := (p.1, p.2.2)) hp).differentiableAt (by
    simp)).hasFDerivAt
  have hm : HasFDerivAt (fun p : Point => (p.1, p.2.2))
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.comp p hasFDerivAt_snd)
  have hc := (hq.comp p hm).prodMk hasFDerivAt_snd
  have heq : inverseDifferential a (inverseCoordinates a p) =
      ((fderiv ℝ (coordinateQ a) (p.1, p.2.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).prod
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [inverseDifferential_apply]
    change ((v.1 + 2 * p.2.2 * qCoord a p ^ a * v.2.2) /
      scalarSlope a p.2.2 (qCoord a p), v.2) =
      (fderiv ℝ (coordinateQ a) (p.1, p.2.2) (v.1, v.2.2), v.2)
    rw [coordinateQ_fderiv_apply ha ha1 (p := (p.1, p.2.2)) hp]
    rfl
  rw [heq]
  exact hc

theorem inverseDifferential_contDiffAt {a : ℝ} {y : Point}
    (hy : 0 < y.1) (hs : scalarSlope a y.2.2 y.1 ≠ 0) :
    ContDiffAt ℝ ∞ (inverseDifferential a) y := by
  have hm : ContDiffAt ℝ ∞ (fun y : Point => scalarSlope a y.2.2 y.1) y :=
    contDiffAt_const.sub (((contDiffAt_snd.snd.pow 2).mul contDiffAt_const).mul
      (contDiffAt_fst.rpow_const_of_ne hy.ne'))
  have hn : ContDiffAt ℝ ∞ (fun y : Point => 2 * y.2.2 * y.1 ^ a) y :=
    (contDiffAt_const.mul contDiffAt_snd.snd).mul
      (contDiffAt_fst.rpow_const_of_ne hy.ne')
  exact (contDiffAt_const.clm_comp (((hm.inv hs).smul contDiffAt_const).add
    ((hn.div hm hs).smul contDiffAt_const))).add contDiffAt_const

/-- Actual inverse jets, computed by recursively differentiating through
the inverse Jacobian. This definition assumes no derivative estimates. -/
noncomputable def inverseJet (a : ℝ) (g : Point → ℝ) :
    (n : ℕ) → Point → Point[×n]→L[ℝ] ℝ
  | 0, y => (continuousMultilinearCurryFin0 ℝ Point ℝ).symm (g y)
  | n + 1, y =>
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Point) ℝ).symm
      ((fderiv ℝ (inverseJet a g n) y).comp (inverseDifferential a y))

theorem inverseJet_contDiffAt {a : ℝ} {g : Point → ℝ} {y : Point}
    (hy : 0 < y.1) (hs : scalarSlope a y.2.2 y.1 ≠ 0)
    (hg : ContDiffAt ℝ ∞ g y) (n : ℕ) :
    ContDiffAt ℝ ∞ (inverseJet a g n) y := by
  induction n with
  | zero =>
    exact hg.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ Point ℝ).symm : ℝ →L[ℝ] Point[×0]→L[ℝ] ℝ)
  | succ n ih =>
    exact ((ih.fderiv_right infty_add_one_le).clm_comp
      (inverseDifferential_contDiffAt hy hs)).continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Point) ℝ).symm :
          (Point →L[ℝ] Point[×n]→L[ℝ] ℝ) →L[ℝ] Point[×(n + 1)]→L[ℝ] ℝ)

theorem iteratedFDeriv_comp_inverse {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {g : Point → ℝ} (hg : ContDiffOn ℝ ∞ g positiveTime)
    (n : ℕ) {p : Point} (hp : p ∈ positiveTime) :
    iteratedFDeriv ℝ n (g ∘ inverseCoordinates a) p =
      inverseJet a g n (inverseCoordinates a p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have heq : iteratedFDeriv ℝ n (g ∘ inverseCoordinates a) =ᶠ[𝓝 p]
        (inverseJet a g n ∘ inverseCoordinates a) := by
      filter_upwards [positiveTime_isOpen.mem_nhds hp] with p' hp'
      exact ih hp'
    have hq := qCoord_pos ha ha1 hp
    have hj := inverseJet_contDiffAt hq (inverseCoordinates_slope_pos ha ha1 hp).ne'
      (hg.contDiffAt (positiveTime_isOpen.mem_nhds
        (show inverseCoordinates a p ∈ positiveTime from hq))) n
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Point) ℝ).symm
      (fderiv ℝ (iteratedFDeriv ℝ n (g ∘ inverseCoordinates a)) p) = _
    rw [heq.fderiv_eq]
    rw [fderiv_comp p (hj.differentiableAt (by simp))
      ((inverseCoordinates_contDiffAt ha ha1 hp).differentiableAt (by simp)),
      (inverseCoordinates_hasFDerivAt ha ha1 hp).fderiv]
    rfl

noncomputable def normalizedCompact (lo hi : ℝ) : Set Point :=
  ({1} : Set ℝ) ×ˢ (Icc lo hi ×ˢ Icc (-1 : ℝ) 1)

theorem normalizedCompact_isCompact (lo hi : ℝ) : IsCompact (normalizedCompact lo hi) :=
  isCompact_singleton.prod (isCompact_Icc.prod isCompact_Icc)

theorem normalized_slope_pos {a lo hi : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {y : Point} (hy : y ∈ normalizedCompact lo hi) : 0 < scalarSlope a y.2.2 y.1 := by
  have hy1 : y.1 = 1 := hy.1
  have hz : y.2.2 ^ 2 ≤ 1 := by nlinarith [hy.2.2.1, hy.2.2.2]
  have haz := mul_le_mul_of_nonneg_left hz ha.le
  simp only [scalarSlope, hy1, Real.one_rpow, mul_one]
  nlinarith

theorem exists_normalized_jet_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {g : Point → ℝ} (hg : ContDiffOn ℝ ∞ g positiveTime) (lo hi : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ normalizedCompact lo hi, ‖inverseJet a g n y‖ ≤ C := by
  have hc : ContinuousOn (inverseJet a g n) (normalizedCompact lo hi) := by
    intro y hy
    have hq : 0 < y.1 := by rw [show y.1 = 1 from hy.1]; norm_num
    exact (inverseJet_contDiffAt hq (normalized_slope_pos ha ha1 hy).ne'
      (hg.contDiffAt (positiveTime_isOpen.mem_nhds
        (show y ∈ positiveTime from hq))) n).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (normalizedCompact_isCompact lo hi).exists_bound_of_continuousOn hc
  exact ⟨max C 0 + 1, by positivity, fun y hy => (hC y hy).trans (by linarith [le_max_left C 0])⟩

/-- The physical dilation: time and squared radius have weight one, while
the axial variable has weight `D = (1-a)/2`. -/
noncomputable def dilation (a r : ℝ) : Point →L[ℝ] Point :=
  (r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((r • ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
      (((r ^ D a) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

@[simp] theorem dilation_apply (a r : ℝ) (p : Point) :
    dilation a r p = (r * p.1, (r * p.2.1, r ^ D a * p.2.2)) := rfl

theorem dilation_inv_cancel {r : ℝ} (hr : 0 < r) (a : ℝ) (p : Point) :
    dilation a r (dilation a r⁻¹ p) = p := by
  ext <;> simp [dilation_apply, Real.inv_rpow hr.le, hr.ne', (Real.rpow_pos_of_pos hr (D a)).ne']

theorem dilation_positive {r : ℝ} (hr : 0 < r) (a : ℝ) {p : Point}
    (hp : p ∈ positiveTime) : dilation a r p ∈ positiveTime := mul_pos hr hp

theorem forwardScalar_dilation {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (a z : ℝ) :
    forwardScalar a (r ^ D a * z) (r * q) = r * forwardScalar a z q := by
  have hscale : (r ^ D a) ^ 2 * r ^ a = r := by
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    have he : D a * (2 : ℕ) + a = 1 := by dsimp [D]; ring
    rw [he, Real.rpow_one]
  rw [forwardScalar, Real.mul_rpow hr.le hq.le, mul_pow]
  calc
    _ = r * q - ((r ^ D a) ^ 2 * r ^ a) * (z ^ 2 * q ^ a) := by ring
    _ = _ := by rw [hscale]; dsimp [forwardScalar]; ring

theorem qCoord_dilation {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r)
    {p : Point} (hp : p ∈ positiveTime) : qCoord a (dilation a r p) = r * qCoord a p := by
  apply (eq_coordinateQ ha ha1 (p := (r * p.1, r ^ D a * p.2.2))
    (mul_pos hr hp) (mul_pos hr (qCoord_pos ha ha1 hp)) ?_).symm
  rw [forwardScalar_dilation hr (qCoord_pos ha ha1 hp)]
  exact congrArg (r * ·) (coordinateQ_spec ha ha1 (p := (p.1, p.2.2)) hp).2

theorem inverseCoordinates_dilation {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r)
    {p : Point} (hp : p ∈ positiveTime) :
    inverseCoordinates a (dilation a r p) = dilation a r (inverseCoordinates a p) := by
  apply Prod.ext
  · exact qCoord_dilation ha ha1 hr hp
  · rfl

noncomputable def etaCoord (a : ℝ) (p : Point) : ℝ := p.2.2 / qCoord a p ^ D a

noncomputable def xCoord (a : ℝ) (p : Point) : ℝ := p.2.1 / qCoord a p

theorem normalized_inverseCoordinates {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p ∈ positiveTime) :
    inverseCoordinates a (dilation a (qCoord a p)⁻¹ p) =
      (1, (xCoord a p, etaCoord a p)) := by
  have hq := qCoord_pos ha ha1 hp
  rw [inverseCoordinates_dilation ha ha1 (inv_pos.mpr hq) hp]
  simp only [dilation_apply, inverseCoordinates, xCoord, etaCoord, Real.inv_rpow hq.le]
  ext <;> simp [hq.ne', div_eq_mul_inv, mul_comm]

theorem normalized_mem {a lo hi : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p ∈ positiveTime) (hx : xCoord a p ∈ Icc lo hi) :
    inverseCoordinates a (dilation a (qCoord a p)⁻¹ p) ∈ normalizedCompact lo hi := by
  rw [normalized_inverseCoordinates ha ha1 hp]
  refine ⟨rfl, hx, ?_⟩
  have he := coordinateEta_abs_lt_one ha ha1 (p := (p.1, p.2.2)) hp
  exact ⟨(abs_lt.mp he).1.le, (abs_lt.mp he).2.le⟩

theorem iteratedFDeriv_comp_linear_open {F : Point → ℝ} {s : Set Point}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (L : Point →L[ℝ] Point)
    (n : ℕ) {p : Point} (hp : L p ∈ s) :
    iteratedFDeriv ℝ n (F ∘ L) p =
      (iteratedFDeriv ℝ n F (L p)).compContinuousLinearMap (fun _ => L) := by
  have hs' := hs.preimage L.continuous
  have hd := L.iteratedFDerivWithin_comp_right hF hs.uniqueDiffOn hs'.uniqueDiffOn hp
    (nat_le_infty n)
  rwa [iteratedFDerivWithin_of_isOpen n hs' hp, iteratedFDerivWithin_of_isOpen n hs hp] at hd

theorem iteratedFDeriv_eq_of_eventuallyEq {F G : Point → ℝ} {p : Point}
    (heq : F =ᶠ[𝓝 p] G) (n : ℕ) : iteratedFDeriv ℝ n F p = iteratedFDeriv ℝ n G p := by
  have h : F =ᶠ[𝓝[univ] p] G := by simpa only [nhdsWithin_univ] using heq
  simpa only [iteratedFDerivWithin_univ] using h.iteratedFDerivWithin_eq heq.self_of_nhds n

theorem norm_dilation_le {r : ℝ} (hr : 0 ≤ r) (a : ℝ) :
    ‖dilation a r‖ ≤ max r (r ^ D a) := by
  have hB : 0 ≤ max r (r ^ D a) := hr.trans (le_max_left _ _)
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h3 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  simp only [dilation_apply, Prod.norm_def, norm_mul, Real.norm_of_nonneg hr,
    Real.norm_of_nonneg (Real.rpow_nonneg hr _)]
  exact max_le
    (mul_le_mul (le_max_left _ _) h1 (norm_nonneg _) hB)
    (max_le (mul_le_mul (le_max_left _ _) h2 (norm_nonneg _) hB)
      (mul_le_mul (le_max_right _ _) h3 (norm_nonneg _) hB))

noncomputable def scaleFactor (a qbig : ℝ) : ℝ := max 1 (qbig ^ (1 - D a))

theorem scaleFactor_pos (a qbig : ℝ) : 0 < scaleFactor a qbig :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_inverse_dilation_le {a q qbig : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hqb : q ≤ qbig) : ‖dilation a q⁻¹‖ ≤ scaleFactor a qbig / q := by
  have he : 0 ≤ 1 - D a := by dsimp [D]; linarith
  have hpow : q ^ (1 - D a) ≤ scaleFactor a qbig :=
    (Real.rpow_le_rpow hq.le hqb he).trans (le_max_right _ _)
  have hfirst : q⁻¹ ≤ scaleFactor a qbig / q := by
    rw [div_eq_mul_inv]
    change q⁻¹ ≤ max 1 (qbig ^ (1 - D a)) * q⁻¹
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (le_max_left (1 : ℝ) (qbig ^ (1 - D a))) (inv_nonneg.mpr hq.le)
  have hlast : q⁻¹ ^ D a ≤ scaleFactor a qbig / q := by
    rw [Real.inv_rpow hq.le, ← Real.rpow_neg hq.le]
    rw [show -D a = (1 - D a) - 1 by ring, Real.rpow_sub_one hq.ne']
    exact div_le_div_of_nonneg_right hpow hq.le
  exact (norm_dilation_le (inv_nonneg.mpr hq.le) a).trans (max_le hfirst hlast)

theorem pullback_contDiffOn {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {g : Point → ℝ} (hg : ContDiffOn ℝ ∞ g positiveTime) :
    ContDiffOn ℝ ∞ (g ∘ inverseCoordinates a) positiveTime := by
  intro p hp
  exact ((hg.contDiffAt (positiveTime_isOpen.mem_nhds
    (show inverseCoordinates a p ∈ positiveTime from qCoord_pos ha ha1 hp))).comp p
      (inverseCoordinates_contDiffAt ha ha1 hp)).contDiffWithinAt

/-- A homogeneous smooth function of the inverse coordinates has loss at
most `n`, independent of its degree. No derivative bound is an input. -/
theorem homogeneous_derivative_bound {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {g : Point → ℝ} (hg : ContDiffOn ℝ ∞ g positiveTime)
    (hhom : ∀ r > 0, ∀ y ∈ positiveTime, g (dilation a r y) = r ^ b * g y)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ positiveTime, qCoord a p ≤ qbig → xCoord a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (g ∘ inverseCoordinates a) p‖ ≤ C * qCoord a p ^ (b - n) := by
  let F := g ∘ inverseCoordinates a
  have hF := pullback_contDiffOn ha ha1 hg
  have hhomF : ∀ r > 0, ∀ y ∈ positiveTime, F (dilation a r y) = r ^ b * F y := by
    intro r hr y hy
    dsimp only [F, comp_apply]
    rw [inverseCoordinates_dilation ha ha1 hr hy]
    exact hhom r hr _ (qCoord_pos ha ha1 hy)
  obtain ⟨K, hK, hbound⟩ := exists_normalized_jet_bound ha ha1 hg lo hi n
  refine ⟨K * scaleFactor a qbig ^ n, mul_pos hK (pow_pos (scaleFactor_pos a qbig) _), ?_⟩
  intro p hp hqb hx
  let q := qCoord a p
  let L := dilation a q⁻¹
  have hq : 0 < q := qCoord_pos ha ha1 hp
  have hLp : L p ∈ positiveTime := dilation_positive (inv_pos.mpr hq) a hp
  have heq : F =ᶠ[𝓝 p] q ^ b • (F ∘ L) := by
    filter_upwards [positiveTime_isOpen.mem_nhds hp] with y hy
    change F y = q ^ b * F (L y)
    have he := hhomF q hq (L y) (dilation_positive (inv_pos.mpr hq) a hy)
    rwa [dilation_inv_cancel hq] at he
  have hcomp : ContDiffAt ℝ (n : WithTop ℕ∞) (F ∘ L) p :=
    ((hF.contDiffAt (positiveTime_isOpen.mem_nhds hLp)).comp p L.contDiff.contDiffAt).of_le
      (nat_le_infty n)
  have hjet : ‖iteratedFDeriv ℝ n F (L p)‖ ≤ K := by
    rw [iteratedFDeriv_comp_inverse ha ha1 hg n hLp]
    exact hbound _ (normalized_mem ha ha1 hp hx)
  have hLn : ‖L‖ ^ n ≤ (scaleFactor a qbig / q) ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_inverse_dilation_le ha hq hqb) n
  rw [iteratedFDeriv_eq_of_eventuallyEq heq n,
    iteratedFDeriv_const_smul_apply hcomp,
    norm_smul (q ^ b : ℝ) (iteratedFDeriv ℝ n (F ∘ L) p),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hq b).le,
    iteratedFDeriv_comp_linear_open positiveTime_isOpen hF L n hLp]
  calc
    _ ≤ q ^ b * (‖iteratedFDeriv ℝ n F (L p)‖ * ∏ _ : Fin n, ‖L‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
        (Real.rpow_pos_of_pos hq b).le
    _ = q ^ b * (‖iteratedFDeriv ℝ n F (L p)‖ * ‖L‖ ^ n) := by simp
    _ ≤ q ^ b * (K * (scaleFactor a qbig / q) ^ n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hjet hLn (by positivity) hK.le)
        (Real.rpow_pos_of_pos hq b).le
    _ = K * scaleFactor a qbig ^ n * q ^ (b - n) := by
      rw [Real.rpow_sub hq, Real.rpow_natCast, div_pow]
      ring

noncomputable def powerLift (b : ℝ) (y : Point) : ℝ := y.1 ^ b

noncomputable def etaLift (a : ℝ) (y : Point) : ℝ := y.2.2 / y.1 ^ D a

noncomputable def xLift (y : Point) : ℝ := y.2.1 / y.1

theorem powerLift_contDiffOn (b : ℝ) : ContDiffOn ℝ ∞ (powerLift b) positiveTime := by
  intro y hy
  exact (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt

theorem etaLift_contDiffOn (a : ℝ) : ContDiffOn ℝ ∞ (etaLift a) positiveTime := by
  intro y hy
  exact (contDiffAt_snd.snd.div (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hy))
    (Real.rpow_pos_of_pos hy (D a)).ne').contDiffWithinAt

theorem xLift_contDiffOn : ContDiffOn ℝ ∞ xLift positiveTime := by
  intro y hy
  exact (contDiffAt_snd.fst.div contDiffAt_fst (ne_of_gt hy)).contDiffWithinAt

theorem powerLift_homogeneous (a b : ℝ) {r : ℝ} (hr : 0 < r)
    {y : Point} (hy : y ∈ positiveTime) :
    powerLift b (dilation a r y) = r ^ b * powerLift b y :=
  Real.mul_rpow hr.le (show 0 ≤ y.1 from le_of_lt hy)

theorem etaLift_homogeneous (a : ℝ) {r : ℝ} (hr : 0 < r)
    {y : Point} (hy : y ∈ positiveTime) :
    etaLift a (dilation a r y) = r ^ (0 : ℝ) * etaLift a y := by
  dsimp only [etaLift, dilation_apply]
  rw [Real.mul_rpow hr.le (show 0 ≤ y.1 from le_of_lt hy), Real.rpow_zero, one_mul]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hr (D a)).ne'

theorem xLift_homogeneous (a : ℝ) {r : ℝ} (hr : 0 < r)
    {y : Point} (_hy : y ∈ positiveTime) :
    xLift (dilation a r y) = r ^ (0 : ℝ) * xLift y := by
  dsimp only [xLift, dilation_apply]
  rw [Real.rpow_zero, one_mul]
  exact mul_div_mul_left _ _ hr.ne'

/-- Every fixed real power has the same derivative loss `n`; its degree
remains explicitly in the weight `q^(b-n)`. -/
theorem power_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (b lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ positiveTime, qCoord a p ≤ qbig → xCoord a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (fun y => qCoord a y ^ b) p‖ ≤ C * qCoord a p ^ (b - n) :=
  homogeneous_derivative_bound ha ha1 (powerLift_contDiffOn b)
    (fun _r hr _y hy => powerLift_homogeneous a b hr hy) lo hi qbig n

theorem q_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ positiveTime, qCoord a p ≤ qbig → xCoord a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (qCoord a) p‖ ≤ C * qCoord a p ^ (1 - (n : ℝ)) := by
  simpa only [Real.rpow_one] using power_derivative_bound ha ha1 1 lo hi qbig n

theorem eta_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ positiveTime, qCoord a p ≤ qbig → xCoord a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (etaCoord a) p‖ ≤ C * qCoord a p ^ (-(n : ℝ)) := by
  have heq : etaLift a ∘ inverseCoordinates a = etaCoord a := rfl
  simpa only [heq, sub_zero, zero_sub] using
    homogeneous_derivative_bound ha ha1 (etaLift_contDiffOn a)
      (fun _r hr _y hy => etaLift_homogeneous a hr hy) lo hi qbig n

theorem x_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ positiveTime, qCoord a p ≤ qbig → xCoord a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (xCoord a) p‖ ≤ C * qCoord a p ^ (-(n : ℝ)) := by
  have heq : xLift ∘ inverseCoordinates a = xCoord a := rfl
  simpa only [heq, sub_zero, zero_sub] using
    homogeneous_derivative_bound ha ha1 xLift_contDiffOn
      (fun _r hr _y hy => xLift_homogeneous a hr hy) lo hi qbig n

noncomputable def timeReflection : Point ≃ₗᵢ[ℝ] Point where
  toLinearEquiv := LinearEquiv.prodCongr (LinearEquiv.neg ℝ) (LinearEquiv.refl ℝ (ℝ × ℝ))
  norm_map' := by
    intro p
    change max ‖-p.1‖ ‖p.2‖ = max ‖p.1‖ ‖p.2‖
    rw [norm_neg]

noncomputable def timeShift (p : Point) : Point := (1 - p.1, p.2)

theorem timeShift_eq (p : Point) :
    timeShift p = ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) + timeReflection p := by
  apply Prod.ext
  · change 1 - p.1 = 1 + -p.1
    ring
  · change p.2 = (0 : ℝ × ℝ) + p.2
    simp

theorem norm_iteratedFDeriv_timeShift (F : Point → ℝ) (n : ℕ) (p : Point) :
    ‖iteratedFDeriv ℝ n (F ∘ timeShift) p‖ = ‖iteratedFDeriv ℝ n F (timeShift p)‖ := by
  have heq : (F ∘ timeShift) =
      (fun y => F (((1 : ℝ), ((0 : ℝ), (0 : ℝ))) + y)) ∘ timeReflection := by
    funext y
    exact congrArg F (timeShift_eq y)
  rw [heq, timeReflection.norm_iteratedFDeriv_comp_right,
    iteratedFDeriv_comp_add_left, ← timeShift_eq]

/-- Physical coordinates use `(t,s,z)`. The exponent parameter here is
`a = 2h`, so these definitions agree with the coordinates used by NaturalCore. -/
noncomputable def physicalQ (a : ℝ) : Point → ℝ := qCoord a ∘ timeShift

noncomputable def physicalEta (a : ℝ) : Point → ℝ := etaCoord a ∘ timeShift

noncomputable def physicalX (a : ℝ) : Point → ℝ := xCoord a ∘ timeShift

theorem physicalQ_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {p : Point} (hp : p.1 < 1) :
    0 < physicalQ a p := qCoord_pos ha ha1 (sub_pos.mpr hp)

theorem physicalEta_abs_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p.1 < 1) : |physicalEta a p| < 1 :=
  coordinateEta_abs_lt_one ha ha1 (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)

theorem physicalQ_contDiffAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalQ a) p :=
  (qCoord_contDiffAt ha ha1 (p := timeShift p) (sub_pos.mpr hp)).comp p
    ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd)

theorem physicalEta_contDiffAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalEta a) p :=
  contDiffAt_snd.snd.div ((physicalQ_contDiffAt ha ha1 hp).rpow_const_of_ne
    (physicalQ_pos ha ha1 hp).ne') (Real.rpow_pos_of_pos (physicalQ_pos ha ha1 hp) (D a)).ne'

theorem physicalX_contDiffAt {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : Point} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalX a) p :=
  contDiffAt_snd.fst.div (physicalQ_contDiffAt ha ha1 hp) (physicalQ_pos ha ha1 hp).ne'

theorem physical_power_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (b lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (fun y => physicalQ a y ^ b) p‖ ≤
        C * physicalQ a p ^ (b - n) := by
  obtain ⟨C, hC, hbound⟩ := power_derivative_bound ha ha1 b lo hi qbig n
  refine ⟨C, hC, ?_⟩
  intro p hp hq hx
  change ‖iteratedFDeriv ℝ n ((fun y => qCoord a y ^ b) ∘ timeShift) p‖ ≤ _
  rw [norm_iteratedFDeriv_timeShift]
  exact hbound (timeShift p) (sub_pos.mpr hp) hq hx

theorem physical_q_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (physicalQ a) p‖ ≤ C * physicalQ a p ^ (1 - (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := q_derivative_bound ha ha1 lo hi qbig n
  refine ⟨C, hC, ?_⟩
  intro p hp hq hx
  rw [physicalQ, norm_iteratedFDeriv_timeShift]
  exact hbound (timeShift p) (sub_pos.mpr hp) hq hx

theorem physical_eta_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (physicalEta a) p‖ ≤ C * physicalQ a p ^ (-(n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := eta_derivative_bound ha ha1 lo hi qbig n
  refine ⟨C, hC, ?_⟩
  intro p hp hq hx
  rw [physicalEta, norm_iteratedFDeriv_timeShift]
  exact hbound (timeShift p) (sub_pos.mpr hp) hq hx

theorem physical_x_derivative_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (physicalX a) p‖ ≤ C * physicalQ a p ^ (-(n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := x_derivative_bound ha ha1 lo hi qbig n
  refine ⟨C, hC, ?_⟩
  intro p hp hq hx
  rw [physicalX, norm_iteratedFDeriv_timeShift]
  exact hbound (timeShift p) (sub_pos.mpr hp) hq hx

/-- One common constant controls all three coordinate functions, with the
same explicit loss `n`. The constant depends only on the fixed geometry
and the derivative order. -/
theorem physical_coordinate_derivative_bounds {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ n (physicalQ a) p‖ ≤ C * physicalQ a p ^ (-(n : ℝ)) ∧
      ‖iteratedFDeriv ℝ n (physicalEta a) p‖ ≤ C * physicalQ a p ^ (-(n : ℝ)) ∧
      ‖iteratedFDeriv ℝ n (physicalX a) p‖ ≤ C * physicalQ a p ^ (-(n : ℝ)) := by
  obtain ⟨Cq, hCq, hq⟩ := physical_q_derivative_bound ha ha1 lo hi qbig n
  obtain ⟨Ce, hCe, he⟩ := physical_eta_derivative_bound ha ha1 lo hi qbig n
  obtain ⟨Cx, hCx, hx⟩ := physical_x_derivative_bound ha ha1 lo hi qbig n
  let B := max qbig 1
  let C := max (Cq * B) (max Ce Cx)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hqC : Cq * B ≤ C := le_max_left _ _
  have heC : Ce ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hxC : Cx ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, (mul_pos hCq hB).trans_le hqC, ?_⟩
  intro p hp hqb hxp
  have hpq := physicalQ_pos ha ha1 hp
  have hw : 0 ≤ physicalQ a p ^ (-(n : ℝ)) := (Real.rpow_pos_of_pos hpq _).le
  refine ⟨?_, (he p hp hqb hxp).trans (mul_le_mul_of_nonneg_right heC hw),
    (hx p hp hqb hxp).trans (mul_le_mul_of_nonneg_right hxC hw)⟩
  calc
    _ ≤ Cq * physicalQ a p ^ (1 - (n : ℝ)) := hq p hp hqb hxp
    _ = (Cq * physicalQ a p) * physicalQ a p ^ (-(n : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hpq, Real.rpow_one]
      ring
    _ ≤ (Cq * B) * physicalQ a p ^ (-(n : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hqb.trans (le_max_left _ _)) hCq.le) hw
    _ ≤ C * physicalQ a p ^ (-(n : ℝ)) := mul_le_mul_of_nonneg_right hqC hw

theorem norm_fderiv_eq_iterated_one (F : Point → ℝ) (p : Point) :
    ‖fderiv ℝ F p‖ = ‖iteratedFDeriv ℝ 1 F p‖ := by
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := p) (n := 0))

theorem physical_coordinate_fderiv_bounds {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (lo hi qbig : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Point, p.1 < 1 →
      physicalQ a p ≤ qbig → physicalX a p ∈ Icc lo hi →
      ‖fderiv ℝ (physicalQ a) p‖ ≤ C / physicalQ a p ∧
      ‖fderiv ℝ (physicalEta a) p‖ ≤ C / physicalQ a p ∧
      ‖fderiv ℝ (physicalX a) p‖ ≤ C / physicalQ a p := by
  simpa only [← norm_fderiv_eq_iterated_one, Nat.cast_one, Real.rpow_neg_one,
    div_eq_mul_inv] using physical_coordinate_derivative_bounds ha ha1 lo hi qbig 1

end NavierStokes.PhysicalCoordinateBounds
