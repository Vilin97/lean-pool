/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.BarNormBridge

/-! Faà di Bruno transfer of material-Jacobian bounds through the flow map. -/

@[expose] public section

open MeasureTheory Homogenization
open AVenhance.FaaDiBruno

noncomputable section

namespace AVenhance.Infra.Construction

theorem MaterialFlowComposition.orderedPartial_eq_iteratedFDeriv_local
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ n f)
    (x : Vec 2) (J : Fin n → Fin 2) :
    orderedPartial n f x J =
      iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) := by
  change iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
      (fun k => coordinateVectorOne 2 (J k)) = _
  have h := (vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    (f := f) hf (WithLp.toLp 1 x) (i := n) le_rfl
  have h' := congrArg
    (fun T => T (fun k => coordinateVectorOne 2 (J k))) h
  simpa [liftVecOne, coordinateVectorOne, basisVec, vecOneEquiv,
    PiLp.coe_continuousLinearEquiv] using h'

/-- Uniform coordinate derivative bounds imply the corresponding Appendix B
derivative seminorm bound. -/
theorem MaterialFlowComposition.derivativeSup_le_of_uniform_coordinate_bound
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ n f) {B : ℝ}
    (hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun k => basisVec (J k))‖ ≤ B) :
    FaaDiBruno.derivativeSup n f ≤ ENNReal.ofReal B := by
  unfold FaaDiBruno.derivativeSup
  apply iSup_le
  intro J
  unfold FaaDiBruno.partialSup
  have hae : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖orderedPartial n f x J‖ₑ ≤ ENNReal.ofReal B := by
    filter_upwards with x
    rw [MaterialFlowComposition.orderedPartial_eq_iteratedFDeriv_local hf x J]
    simpa using ENNReal.ofReal_le_ofReal (hcoord x J)
  rw [eLpNormEssSup_eq_essSup_enorm]
  exact essSup_le_of_ae_le _ hae

/-- Coordinate derivatives bounded at the natural inverse-regularity radius
give a uniform source seminorm, with the finite order loss exposed. -/
theorem MaterialFlowComposition.snorm_le_of_uniform_coordinate_bound
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    {R : ℝ} (hR : 0 < R) {B : ℝ}
    (hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun k => basisVec (J k))‖ ≤ B) :
    FaaDiBruno.snorm f n R ≤ ENNReal.ofReal
      ((((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (R⁻¹) ^ n * B) := by
  have hderiv := MaterialFlowComposition.derivativeSup_le_of_uniform_coordinate_bound f hf hcoord
  rw [FaaDiBruno.snorm]
  rw [← ENNReal.ofReal_inv_of_pos hR,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ R⁻¹)]
  have hcoeff : 0 ≤ ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) := by positivity
  calc
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        ENNReal.ofReal ((R⁻¹) ^ n) * ENNReal.ofReal B :=
      mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ = ENNReal.ofReal
        ((((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * (R⁻¹) ^ n * B) := by
      rw [← ENNReal.ofReal_mul hcoeff,
        ← ENNReal.ofReal_mul (by positivity :
          0 ≤ ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) * (R⁻¹) ^ n)]

theorem MaterialFlowComposition.materialJacobianField_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s : ℝ)
    (ell : ℕ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar
        (constructionMaterialIterate
          (fun q y => streamVel (Φ m) (s + q) y) ell
          (fun q y => constructionComposedFlowJacobian hseq m s q y
            (basisVec j) i))) := by
  let b : ℝ → Vec 2 → Vec 2 := fun q y => streamVel (Φ m) (s + q) y
  let F : ℝ → Vec 2 → ℝ := fun q y =>
    constructionComposedFlowJacobian hseq m s q y (basisVec j) i
  let v : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  have hv : Infra.Flow.SmoothPeriodicField v :=
    smoothPeriodic_streamVel (streamSeq_isAdmissible hseq m)
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := by
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => v p.1 p.2) := hv.smooth
    have hshift : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => streamVel (Φ m) (s + p.1) p.2)
    exact hbase.comp hshift
  have hmatrix := constructionComposedFlowJacobian_joint_contDiff
    (hseq := hseq) m s
  have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2 (basisVec j)) :=
    hmatrix.clm_apply contDiff_const
  have hentry : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2 (basisVec j) i)
    exact (contDiff_pi.1 hcolumn) i
  have hiterate := constructionMaterialIterate_joint_contDiff hb hentry ell
  simpa [F, b] using hiterate

/-- A material Jacobian field has a uniform Appendix B seminorm after
normalizing its source derivative scale. -/
theorem MaterialFlowComposition.materialJacobianField_snorm
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData I Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (ell n : ℕ) (hnell : n + ell ≤ Nstar β)
    (i j : Fin 2) :
    FaaDiBruno.snorm
      (fun y => constructionMaterialIterate
        (fun q z => streamVel (Φ m) (s + q) z) ell
        (fun q z => constructionComposedFlowJacobian hseq m s q z
          (basisVec j) i) r y)
      n (epsilon β I.Λ m)⁻¹ ≤
      ENNReal.ofReal (Cmat * ((Nstar β + 1 : ℝ) ^ 2) *
        (epsilon β I.Λ m ^ (β - 2)) ^ ell) := by
  let e : ℝ := epsilon β I.Λ m
  let H : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => constructionComposedFlowJacobian hseq m s q z
      (basisVec j) i) r y
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hR : 0 < e⁻¹ := inv_pos.mpr he
  have hH : ContDiff ℝ n H := by
    have hspace :=
      (MaterialFlowComposition.materialJacobianField_joint_smooth (hseq := hseq) m s ell i j).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (r, y)))
    have hspace' : ContDiff ℝ (⊤ : ℕ∞) H := by
      simpa [H, constructionJointScalar, Function.comp_def] using hspace
    exact hspace'.of_le (by simp)
  have hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n H x (fun k => basisVec (J k))‖ ≤
        Cmat * e⁻¹ ^ n * (e ^ (β - 2)) ^ ell := by
    intro x J
    exact hflow.material_jacobian m hm s r hr n ell hnell i j x J
  have hseminorm := MaterialFlowComposition.snorm_le_of_uniform_coordinate_bound H hH hR hcoord
  have hcancel : e ^ n * e⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt he), one_pow]
  have hfactor : ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) ≤
      ((Nstar β + 1 : ℝ) ^ 2) := by
    have hindex : (n : ℝ) + 1 ≤ (Nstar β : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (by omega : n ≤ Nstar β) 1
    have hfact : 1 ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((Nstar β : ℝ) + 1) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hindex
    exact (div_le_self (by positivity) (by linarith)).trans hsq
  have hreal : (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
      ((e⁻¹)⁻¹) ^ n * (Cmat * e⁻¹ ^ n * (e ^ (β - 2)) ^ ell) ≤
      Cmat * ((Nstar β + 1 : ℝ) ^ 2) * (e ^ (β - 2)) ^ ell := by
    rw [show ((e⁻¹)⁻¹) ^ n = e ^ n by rw [inv_inv]]
    have hCmat : 0 ≤ Cmat := le_trans (by norm_num) hflow.material_constant_ge_one
    have hEell : 0 ≤ (e ^ (β - 2)) ^ ell := by positivity
    calc
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * Cmat *
          (e ^ n * e⁻¹ ^ n) * (e ^ (β - 2)) ^ ell := by ring
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * Cmat *
          (e ^ (β - 2)) ^ ell := by rw [hcancel]; ring
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (Cmat * (e ^ (β - 2)) ^ ell) := by ring
      _ ≤ ((Nstar β + 1 : ℝ) ^ 2) *
          (Cmat * (e ^ (β - 2)) ^ ell) :=
            mul_le_mul_of_nonneg_right hfactor (mul_nonneg hCmat hEell)
      _ = Cmat * ((Nstar β + 1 : ℝ) ^ 2) *
          (e ^ (β - 2)) ^ ell := by ring
  have hfinal := hseminorm.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa [H, e] using hfinal

theorem MaterialFlowComposition.constructionFlowSlice_smooth_local
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => constructionFlow hseq m (s + r) x s) := by
  let hφ := streamSeq_isAdmissible hseq m
  let b := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b := smoothPeriodic_streamVel hφ
  have hX : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hjoint := Infra.Flow.flow_joint_contDiff_infty hb hX
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => (s + r, x, s)) := by fun_prop
  simpa only [Function.comp_def] using hjoint.comp hmap

/-- The forward flow map has the scale-normalized composition seminorm
required by App. B.3, using the corrected `c.flowreg` derivative display. -/
theorem MaterialFlowComposition.constructionFlowSlice_snorm
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData I Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ Nstar β) :
    FaaDiBruno.snorm
      (fun x : Vec 2 => constructionFlow hseq m (s + r) x s) n
      (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ≤
      ENNReal.ofReal (2 * ((Nstar β + 1 : ℝ) ^ 2) *
        (2 ^ 14 * (epsilon β I.Λ m)⁻¹)⁻¹) := by
  let e : ℝ := epsilon β I.Λ m
  let Rg : ℝ := 2 ^ 14 * e⁻¹
  let Cg : ℝ := 2 * ((Nstar β + 1 : ℝ) ^ 2) * Rg⁻¹
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hflowSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => constructionFlow hseq m (s + r) x s) :=
    MaterialFlowComposition.constructionFlowSlice_smooth_local (hseq := hseq) m s r
  have hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => constructionFlow hseq m (s + r) y s)
        x (fun k => basisVec (J k))‖ ≤
        2 * n.factorial * Rg ^ (n - 1) := by
    intro x J
    have hderiv := hflow.flow_higher_derivative m hm s r hr n hn x J
    simpa [Rg, e] using hderiv
  have hseminorm := MaterialFlowComposition.snorm_le_of_uniform_coordinate_bound
    (fun x : Vec 2 => constructionFlow hseq m (s + r) x s)
    (hflowSmooth.of_le (by exact_mod_cast le_top)) hRg hcoord
  have hpow : (Rg⁻¹) ^ n * Rg ^ (n - 1) = Rg⁻¹ := by
    rw [inv_pow]
    have hstep : Rg ^ n = Rg ^ (n - 1) * Rg := by
      calc
        Rg ^ n = Rg ^ (n - 1 + 1) :=
          congrArg (fun q : ℕ => Rg ^ q) (Nat.sub_add_cancel hn).symm
        _ = Rg ^ (n - 1) * Rg := pow_succ Rg (n - 1)
    rw [hstep]
    field_simp [ne_of_gt hRg]
  have hfactor : ((n : ℝ) + 1) ^ 2 ≤ ((Nstar β + 1 : ℝ) ^ 2) := by
    have hindex : (n : ℝ) + 1 ≤ (Nstar β : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (by omega : n ≤ Nstar β) 1
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hindex
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hreal : (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
      (Rg⁻¹) ^ n * (2 * n.factorial * Rg ^ (n - 1)) ≤ Cg := by
    calc
      _ = 2 * ((n : ℝ) + 1) ^ 2 * ((Rg⁻¹) ^ n * Rg ^ (n - 1)) := by
        field_simp [ne_of_gt hfact]
      _ = 2 * ((n : ℝ) + 1) ^ 2 * Rg⁻¹ := by rw [hpow]
      _ ≤ 2 * ((Nstar β + 1 : ℝ) ^ 2) * Rg⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor (by norm_num)) (inv_nonneg.mpr hRg.le)
      _ = Cg := by rfl
  have hfinal := hseminorm.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa [Rg, Cg, e, FaaDiBruno.snorm] using hfinal

/-- Uniform constant for composing material derivatives with the flow. -/
def materialFlowCompositionConstant (β Cmat : ℝ) : ℝ :=
  Cmat * ((Nstar β + 1 : ℝ) ^ 2) * ((Nstar β).factorial : ℝ) *
    (2 ^ 14 * (1 + (Nstar β + 1 : ℝ) ^ 2)) ^ Nstar β

/-- Spatial differentiation of the pulled back material Jacobian is controlled
by App. B.3, the pointwise source material display, and the flow derivative
display. -/
theorem materialJacobianPullback_spatial_bound
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData I Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (ell n : ℕ) (hnell : n + ell ≤ Nstar β)
    (i j : Fin 2) (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n
      (fun y => constructionMaterialIterate
        (fun q z => streamVel (Φ m) (s + q) z) ell
        (fun q z => constructionComposedFlowJacobian hseq m s q z
          (basisVec j) i) r
        (constructionFlow hseq m (s + r) y s))
      x (fun k => basisVec (J k))‖ ≤
      materialFlowCompositionConstant β Cmat *
        (epsilon β I.Λ m)⁻¹ ^ n *
        (epsilon β I.Λ m ^ (β - 2)) ^ ell := by
  let e : ℝ := epsilon β I.Λ m
  let Eell : ℝ := (e ^ (β - 2)) ^ ell
  let N : ℝ := (Nstar β : ℝ) + 1
  let Rg : ℝ := 2 ^ 14 * e⁻¹
  let Rh : ℝ := e⁻¹
  let Cg : ℝ := 2 * N ^ 2 * Rg⁻¹
  let Ch : ℝ := Cmat * N ^ 2 * Eell
  let Rcomp : ℝ := Rg * (1 + 2 * Cg * Rh)
  let K : ℝ := 2 ^ 14 * (1 + N ^ 2)
  let X : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + r) y s
  let H : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => constructionComposedFlowJacobian hseq m s q z
      (basisVec j) i) r y
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCmat : 0 < Cmat := lt_of_lt_of_le (by norm_num)
    hflow.material_constant_ge_one
  have hEbase : 0 < e ^ (β - 2) := Real.rpow_pos_of_pos he _
  have hEell : 0 < Eell := by
    dsimp [Eell]
    exact pow_pos hEbase _
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hRh : 0 < Rh := by dsimp [Rh]; positivity
  have hCg : 0 < Cg := by
    have hRginv : 0 < Rg⁻¹ := inv_pos.mpr hRg
    dsimp [Cg]
    positivity
  have hCh : 0 < Ch := by dsimp [Ch]; positivity
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (Nstar β : ℝ) + 1
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hRcomp : 0 < Rcomp := by dsimp [Rcomp]; positivity
  have hHtop : ContDiff ℝ (⊤ : ℕ∞) H := by
    have h := (MaterialFlowComposition.materialJacobianField_joint_smooth
      (hseq := hseq) m s ell i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (r, y)))
    simpa [H, constructionJointScalar, Function.comp_def] using h
  have hXtop : ContDiff ℝ (⊤ : ℕ∞) X := by
    simpa [X] using MaterialFlowComposition.constructionFlowSlice_smooth_local (hseq := hseq) m s r
  have hH : ContDiff ℝ n H := hHtop.of_le (by simp)
  have hXn : ContDiff ℝ n X := hXtop.of_le (by simp)
  have hHsnorm (q : ℕ) (hq : q ≤ n) :
      FaaDiBruno.snorm H q Rh ≤ ENNReal.ofReal Ch := by
    have hqell : q + ell ≤ Nstar β := by omega
    simpa [H, Rh, Ch, Eell, e, N] using
      MaterialFlowComposition.materialJacobianField_snorm hflow hm s r hr ell q hqell i j
  have hXsnorm (q : ℕ) (hq0 : 1 ≤ q) (hq : q ≤ n) :
      FaaDiBruno.snorm X q Rg ≤ ENNReal.ofReal Cg := by
    have hqN : q ≤ Nstar β := by omega
    simpa [X, Rg, Cg, N, e] using
      MaterialFlowComposition.constructionFlowSlice_snorm hflow hm s r hr q hq0 hqN
  have hcomposition := FaaDiBruno.compositionEstimate10528
    H X hH hXn hCh hCg hRh hRg hHsnorm hXsnorm n (by omega)
  have hcompositionSmooth : ContDiff ℝ n (H ∘ X) := hH.comp hXn
  have hbar : barNorm n Rcomp (H ∘ X) ≤ ENNReal.ofReal Ch := by
    rw [FaaDiBruno.barNorm_eq_snorm hcompositionSmooth]
    simpa [H, X, Rcomp, Rg, Cg, Rh, Ch, Eell, e, N] using hcomposition
  have hcontinuous : Continuous (fun y : Vec 2 =>
      iteratedFDeriv ℝ n (H ∘ X) y (fun k => basisVec (J k))) := by
    have h := hcompositionSmooth.continuous_iteratedFDeriv'
    fun_prop
  have hRcomp' : 0 < Rcomp := hRcomp
  have hCh : 0 ≤ Ch := hCh.le
  have hpoint := barNorm_iterated_pointwise
    (n := n) (R := Rcomp) (B := Ch) J hcontinuous hRcomp' hCh hbar x
  have hRcompEq : Rcomp =
      2 ^ 14 * (1 + N ^ 2 / 2 ^ 12) * e⁻¹ := by
    dsimp [Rcomp, Rg, Cg, Rh]
    field_simp [ne_of_gt he]
  have hRratio : 1 + N ^ 2 / 2 ^ 12 ≤ 1 + N ^ 2 := by
    have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
    linarith only [hN2]
  have hRcompLe : Rcomp ≤ K * e⁻¹ := by
    rw [hRcompEq]
    dsimp [K]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRratio (by norm_num)) (inv_nonneg.mpr he.le)
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith only [sq_nonneg N]
  have hRpow : Rcomp ^ n ≤ K ^ (Nstar β) * e⁻¹ ^ n := by
    calc
      Rcomp ^ n ≤ (K * e⁻¹) ^ n := pow_le_pow_left₀ hRcomp.le hRcompLe n
      _ = K ^ n * e⁻¹ ^ n := by rw [mul_pow]
      _ ≤ K ^ (Nstar β) * e⁻¹ ^ n := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hK (by omega)) (by positivity)
  have hfac : (n.factorial : ℝ) ≤ (Nstar β).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ Nstar β)
  have hden : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hn0r : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact one_le_pow₀ (by linarith only [hn0r])
  have hpointSimple : ‖iteratedFDeriv ℝ n (H ∘ X) x
      (fun k => basisVec (J k))‖ ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := by
    have hdiv : Ch / (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) *
        Rcomp⁻¹ ^ n) ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := by
      have hcancel : Rcomp ^ n * Rcomp⁻¹ ^ n = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hRcomp), one_pow]
      apply (div_le_iff₀ (by positivity)).2
      field_simp [ne_of_gt hRcomp]
      calc
        1 = (Rcomp ^ n * Rcomp⁻¹ ^ n) * 1 := by rw [hcancel]; ring
        _ ≤ (Rcomp ^ n * Rcomp⁻¹ ^ n) * ((n : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hden (by positivity)
        _ = Rcomp ^ n * ((n : ℝ) + 1) ^ 2 * (1 / Rcomp) ^ n := by
          rw [one_div]
          ring
    exact hpoint.trans hdiv
  calc
    _ ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := hpointSimple
    _ = Cmat * N ^ 2 * Eell * (n.factorial : ℝ) * Rcomp ^ n := by
      simp [Ch]
    _ ≤ Cmat * N ^ 2 * Eell * ((Nstar β).factorial : ℝ) *
        (K ^ (Nstar β) * e⁻¹ ^ n) := by
      rw [show Cmat * N ^ 2 * Eell * (n.factorial : ℝ) * Rcomp ^ n =
        (Cmat * N ^ 2 * Eell) * ((n.factorial : ℝ) * Rcomp ^ n) by ring]
      rw [show Cmat * N ^ 2 * Eell * ((Nstar β).factorial : ℝ) *
        (K ^ (Nstar β) * e⁻¹ ^ n) =
        (Cmat * N ^ 2 * Eell) *
          (((Nstar β).factorial : ℝ) * (K ^ (Nstar β) * e⁻¹ ^ n)) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (n.factorial : ℝ) * Rcomp ^ n ≤
            ((Nstar β).factorial : ℝ) * Rcomp ^ n :=
              mul_le_mul_of_nonneg_right hfac (by positivity)
        _ ≤ ((Nstar β).factorial : ℝ) *
            (K ^ (Nstar β) * e⁻¹ ^ n) :=
              mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ = materialFlowCompositionConstant β Cmat * e⁻¹ ^ n * Eell := by
      dsimp [materialFlowCompositionConstant, N, K]
      ring

theorem MaterialFlowComposition.iteratedTimeDerivative_neg_local
    (ell : ℕ) (f : ℝ → ℝ) :
    iteratedTimeDerivative ell (fun t => -f t) =
      fun t => -iteratedTimeDerivative ell f t := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      funext t
      simp [iteratedTimeDerivative, ih]

theorem MaterialFlowComposition.norm_iteratedFDeriv_neg_local {g : Vec 2 → ℝ}
    (n : ℕ) (x : Vec 2) (J : Fin n → Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => -g y) x J‖ =
      ‖iteratedFDeriv ℝ n g x J‖ := by
  change ‖iteratedFDeriv ℝ n (-g) x J‖ = _
  rw [iteratedFDeriv_neg]
  change ‖-(iteratedFDeriv ℝ n g x J)‖ = _
  rw [norm_neg]

/-- `c.material.goal`, with the source `c.material.DX.Xinv` field read from
`FlowBoundsData`. The two dimensional cofactor converts the inverse Jacobian
to entries of the composed forward Jacobian, the material pullback identity
turns those entries into time derivatives, and App. B.3 transfers their
spatial estimates through the flow. -/
theorem c_material_goal_source_of_flow_bounds
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData I Φ hseq Cmat) (hm : 1 ≤ m) :
    CMaterialGoalSourceData I Φ hseq
      (materialFlowCompositionConstant β Cmat) m := by
  refine ⟨?_⟩
  intro s r hr n ell hnell i j x J
  let Q : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => constructionComposedFlowJacobian hseq m s q z
      (basisVec (1 - i)) (1 - j)) r
    (constructionFlow hseq m (s + r) y s)
  have hentry (y : Vec 2) :
      (fun q : ℝ => inverseJacobianPulledBack hseq m s q y
        (basisVec j) i) =
      fun q => if i = j then
        constructionFlowJacobian hseq m q s y
          (basisVec (1 - i)) (1 - j)
      else -constructionFlowJacobian hseq m q s y
          (basisVec (1 - i)) (1 - j) := by
    funext q
    obtain ⟨h00, h10, h01, h11⟩ :=
      inverseJacobianPulledBack_cofactor_entries (hseq := hseq) m s q y
    fin_cases i <;> fin_cases j <;>
      simp_all [Homogenization.basisVec]
  have htarget :
      (fun y : Vec 2 => iteratedTimeDerivative ell
        (fun q => inverseJacobianPulledBack hseq m s q y
          (basisVec j) i) r) =
      fun y => if i = j then Q y else -Q y := by
    funext y
    have hc := congrArg
      (fun f : ℝ → ℝ => iteratedTimeDerivative ell f r) (hentry y)
    by_cases hij : i = j
    · have hpull := constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
        (hseq := hseq) m s y (1 - j) (1 - i) ell r
      have hc' : iteratedTimeDerivative ell
          (fun q => inverseJacobianPulledBack hseq m s q y
            (basisVec j) i) r =
          iteratedTimeDerivative ell
            (fun q => constructionFlowJacobian hseq m q s y
              (basisVec (1 - i)) (1 - j)) r := by
        simpa [hij] using hc
      simpa [hij, Q] using hc'.trans hpull.symm
    · have hpull := constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
        (hseq := hseq) m s y (1 - j) (1 - i) ell r
      have hc' : iteratedTimeDerivative ell
          (fun q => inverseJacobianPulledBack hseq m s q y
            (basisVec j) i) r =
          iteratedTimeDerivative ell
            (fun q => -constructionFlowJacobian hseq m q s y
              (basisVec (1 - i)) (1 - j)) r := by
        simpa [hij] using hc
      have hneg : iteratedTimeDerivative ell
          (fun q => -constructionFlowJacobian hseq m q s y
            (basisVec (1 - i)) (1 - j)) r = -Q y := by
        rw [MaterialFlowComposition.iteratedTimeDerivative_neg_local]
        simpa [Q] using congrArg (fun z : ℝ => -z) hpull.symm
      simpa [hij, Q] using hc'.trans hneg
  have hbound := materialJacobianPullback_spatial_bound
    hflow hm s r hr ell n hnell (1 - j) (1 - i) x J
  rw [htarget]
  by_cases hij : i = j
  · simpa [hij, Q] using hbound
  · simp only [ite_eq_right hij]
    rw [MaterialFlowComposition.norm_iteratedFDeriv_neg_local]
    simpa [Q, inv_pow] using hbound

end AVenhance.Infra.Construction

end
