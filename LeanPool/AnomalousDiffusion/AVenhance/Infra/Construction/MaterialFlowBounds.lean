/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialSpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowIdentities
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart

/-! # Material Flow Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

/-- The source-form §2 displays sufficient for the spatial slices of the
material Jacobian consequences. This package deliberately excludes the
material conclusion being derived below. -/
structure Section2SpatialFlowData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ) (m : ℕ) : Prop where
  flow_close : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ x : Vec 2,
      ‖constructionFlowJacobian hseq m r s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |r| * a β I.Λ m ∧
      2 ^ 23 * |r| * a β I.Λ m ≤ 1 / 4
  flow_jacobian_composed : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionComposedFlowJacobian hseq m s r x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => constructionComposedFlowJacobian hseq m s r x)
  flow_higher_derivative : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
          constructionFlow hseq m (s + r) y s) x
          (fun k => basisVec (J k))‖ ≤
            2 * n.factorial *
              (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)

theorem MaterialFlowBounds.flow_slice_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => constructionFlow hseq m (s + r) y s) := by
  let hφ := streamSeq_isAdmissible hseq m
  let b := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b := smoothPeriodic_streamVel hφ
  have hX : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hjoint := Infra.Flow.flow_joint_contDiff_infty hb hX
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => (s + r, y, s)) := by fun_prop
  simpa only [Function.comp_def] using hjoint.comp hmap

theorem MaterialFlowBounds.iteratedFDeriv_component {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Vec 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x
      J = iteratedFDeriv ℝ n f x J i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x J = _
  rw [hcomp]
  rfl

theorem MaterialFlowBounds.iteratedFDeriv_gradient_scalar {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q : ℕ) (x : Vec 2)
    (J : Fin q → Fin 2) (j : Fin 2) :
    iteratedFDeriv ℝ q (fun y : Vec 2 => fderiv ℝ g y (basisVec j)) x
      (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ (q + 1) g x
      (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) := by
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hdf (i := q)
    (by simp) (x := x) (u := basisVec j) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := g) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec j))
  calc
    _ = (iteratedFDeriv ℝ q (fun y : Vec 2 => fderiv ℝ g y) x
        (fun k => basisVec (J k))) (basisVec j) := hval
    _ = iteratedFDeriv ℝ (q + 1) g x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) := by simpa using hnext.symm

theorem MaterialFlowBounds.norm_iteratedFDeriv_neg {g : Vec 2 → ℝ}
    (n : ℕ) (x : Vec 2) (J : Fin n → Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => -g y) x J‖ =
      ‖iteratedFDeriv ℝ n g x J‖ := by
  change ‖iteratedFDeriv ℝ n (-g) x J‖ = _
  rw [iteratedFDeriv_neg]
  change ‖-(iteratedFDeriv ℝ n g x J)‖ = _
  rw [norm_neg]

theorem MaterialFlowBounds.fderiv_component_apply {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => f y i) x (basisVec j) =
      fderiv ℝ f x (basisVec j) i := by
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa using h'

theorem MaterialFlowBounds.fin_snoc_basisVec {n : ℕ} (J : Fin n → Fin 2)
    (j : Fin 2) :
    Fin.snoc (fun k => basisVec (J k)) (basisVec j) =
      fun k => basisVec (Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) J j k) := by
  funext k
  refine Fin.lastCases ?_ (fun q => ?_) k
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]

theorem MaterialFlowBounds.basisVec_norm_eq_one (j : Fin 2) : ‖basisVec j‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro k
    by_cases hk : k = j <;> simp [basisVec, hk]
  · have hk := norm_le_pi_norm (basisVec j) j
    simpa [basisVec] using hk

theorem MaterialFlowBounds.iteratedFDeriv_flowJacobian_entry
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (n : ℕ)
    (x : Vec 2) (J : Fin n → Fin 2) (i j : Fin 2) :
    iteratedFDeriv ℝ n
      (fun y : Vec 2 => constructionFlowJacobian hseq m r s y (basisVec j) i)
      x (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ (n + 1)
      (fun y : Vec 2 => constructionFlow hseq m (s + r) y s) x
      (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) i := by
  let F : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + r) y s
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := MaterialFlowBounds.flow_slice_smooth m s r
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => F y i) :=
    (contDiff_pi.1 hF) i
  have hgrad : (fun y : Vec 2 =>
      constructionFlowJacobian hseq m r s y (basisVec j) i) =
      fun y => fderiv ℝ (fun z : Vec 2 => F z i) y (basisVec j) := by
    funext y
    rw [MaterialFlowBounds.fderiv_component_apply hF y i j]
    rfl
  rw [hgrad]
  rw [MaterialFlowBounds.iteratedFDeriv_gradient_scalar hi n x J j]
  exact MaterialFlowBounds.iteratedFDeriv_component hF (n + 1) x
    (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) i

theorem inverseJacobianPulledBack_cofactor_entries
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (x : Vec 2) :
    inverseJacobianPulledBack hseq m s r x (basisVec 0) 0 =
        constructionFlowJacobian hseq m r s x (basisVec 1) 1 ∧
    inverseJacobianPulledBack hseq m s r x (basisVec 1) 0 =
        -constructionFlowJacobian hseq m r s x (basisVec 1) 0 ∧
    inverseJacobianPulledBack hseq m s r x (basisVec 0) 1 =
        -constructionFlowJacobian hseq m r s x (basisVec 0) 1 ∧
    inverseJacobianPulledBack hseq m s r x (basisVec 1) 1 =
        constructionFlowJacobian hseq m r s x (basisVec 0) 0 := by
  let hφ := streamSeq_isAdmissible hseq m
  let b := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b := smoothPeriodic_streamVel hφ
  have hX : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  obtain ⟨_, _, hinv, _⟩ := Infra.Flow.flow_fixed_time_maps_are_C1_inverses
    hb hX s (s + r)
  have hmap : constructionFlowInv hseq m (s + r)
      (constructionFlow hseq m (s + r) x s) s = x := by
    simpa [constructionFlowInv, constructionFlow, flowInv] using hinv x
  have hcof := constructionComposedJacobian_cofactor_entries
    (hseq := hseq) m s r (constructionFlow hseq m (s + r) x s)
  have hcomp00 : constructionComposedFlowJacobian hseq m s r
      (constructionFlow hseq m (s + r) x s) (basisVec 0) 0 =
      constructionFlowJacobian hseq m r s x (basisVec 0) 0 := by
    simp [constructionComposedFlowJacobian, constructionFlowJacobian, hmap]
  have hcomp10 : constructionComposedFlowJacobian hseq m s r
      (constructionFlow hseq m (s + r) x s) (basisVec 1) 0 =
      constructionFlowJacobian hseq m r s x (basisVec 1) 0 := by
    simp [constructionComposedFlowJacobian, constructionFlowJacobian, hmap]
  have hcomp01 : constructionComposedFlowJacobian hseq m s r
      (constructionFlow hseq m (s + r) x s) (basisVec 0) 1 =
      constructionFlowJacobian hseq m r s x (basisVec 0) 1 := by
    simp [constructionComposedFlowJacobian, constructionFlowJacobian, hmap]
  have hcomp11 : constructionComposedFlowJacobian hseq m s r
      (constructionFlow hseq m (s + r) x s) (basisVec 1) 1 =
      constructionFlowJacobian hseq m r s x (basisVec 1) 1 := by
    simp [constructionComposedFlowJacobian, constructionFlowJacobian, hmap]
  rcases hcof with ⟨h00, h10, h01, h11⟩
  dsimp [inverseJacobianPulledBack]
  constructor
  · rw [← hcomp11]
    exact h11.symm
  constructor
  · rw [← hcomp10]
    linarith
  constructor
  · rw [← hcomp01]
    linarith
  · rw [← hcomp00]
    exact h00.symm

theorem MaterialFlowBounds.pulledBackEntry_eq_flowJacobian_entry
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (i j : Fin 2) :
    (fun x : Vec 2 => inverseJacobianPulledBack hseq m s r x (basisVec j) i) =
    if i = j then
      (fun x => constructionFlowJacobian hseq m r s x (basisVec (1 - i)) (1 - j))
    else
      (fun x => -constructionFlowJacobian hseq m r s x (basisVec (1 - i)) (1 - j)) := by
  funext x
  have h := inverseJacobianPulledBack_cofactor_entries
    (hseq := hseq) m s r x
  fin_cases i <;> fin_cases j <;>
    simp_all [Homogenization.basisVec]

theorem MaterialFlowBounds.flowJacobian_entry_norm_le_two
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {m : ℕ}
    (hflow : Section2SpatialFlowData I Φ hseq m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (x : Vec 2) (i j : Fin 2) :
    ‖constructionFlowJacobian hseq m r s x (basisVec j) i‖ ≤ 2 := by
  have hclose := (hflow.flow_close s r hr x)
  let J := constructionFlowJacobian hseq m r s x
  let e := basisVec j
  have he : ‖e‖ = 1 := by
    dsimp [e]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonempty]
      intro k
      by_cases hk : k = j <;> simp [basisVec, hk]
    · have hk := norm_le_pi_norm (basisVec j) j
      simpa [basisVec] using hk
  have hdev : ‖(J - ContinuousLinearMap.id ℝ (Vec 2)) e‖ ≤ 1 / 4 := by
    calc
      _ ≤ ‖J - ContinuousLinearMap.id ℝ (Vec 2)‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖J - ContinuousLinearMap.id ℝ (Vec 2)‖ := by rw [he, mul_one]
      _ ≤ 1 / 4 := hclose.1.trans hclose.2
  have hvec : ‖J e‖ ≤ 2 := by
    have hdecomp : J e = (J - ContinuousLinearMap.id ℝ (Vec 2)) e + e := by
      simp
    rw [hdecomp]
    calc
      _ ≤ ‖(J - ContinuousLinearMap.id ℝ (Vec 2)) e‖ + ‖e‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := add_le_add hdev (by rw [he])
      _ ≤ 2 := by norm_num
  exact (norm_le_pi_norm (J e) i).trans hvec

theorem MaterialFlowBounds.iteratedFDeriv_add_const_eq_of_pos
    {n : ℕ} {f : Vec 2 → ℝ} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) (c : ℝ) (x : Vec 2) (J : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (fun y => f y + c) x J =
      iteratedFDeriv ℝ n f x J := by
  have hfun : (fun y : Vec 2 => f y + c) = f + fun _ => c := by
    funext y
    rfl
  rw [hfun]
  rw [iteratedFDeriv_add_apply hf.contDiffAt contDiff_const.contDiffAt]
  have hconst := iteratedFDeriv_const_of_ne
    (𝕜 := ℝ) (E := Vec 2) (F := ℝ) (n := n) (by omega) c
  rw [hconst]
  simp

/-- The `ell = 0` slice of `c.material.DX.Xinv`, derived from the explicit
`flow_jacobian_composed` seminorm display in `Section2FlowBoundsAtScale`. -/
def section2MaterialSpatialConstant (N : ℕ) : ℝ :=
  42 + 40 * ∑ q ∈ Finset.range (N + 1),
    ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))

theorem section2_material_jacobian_spatial_slice_of_flow_bounds
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {m N : ℕ}
    (hflow : Section2SpatialFlowData I Φ hseq m) :
    1 ≤ section2MaterialSpatialConstant N ∧ ∀ s r : ℝ,
      |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
      ∀ n : ℕ, n ≤ N → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => constructionComposedFlowJacobian hseq m s r y
              (basisVec j) i)
            x (fun k => basisVec (J k))‖ ≤
              section2MaterialSpatialConstant N * (epsilon β I.Λ m)⁻¹ ^ n := by
  let S : ℝ := ∑ q ∈ Finset.range (N + 1),
      ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))
  let Cmat : ℝ := 42 + 40 * S
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 1 ≤ Cmat := by dsimp [Cmat]; linarith
  refine ⟨?_, ?_⟩
  · simpa [section2MaterialSpatialConstant, Cmat, S] using hC
  intro s r hr n hn i j x J
  let R : ℝ := 2 ^ 10 * (epsilon β I.Λ m)⁻¹
  let F : Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    constructionComposedFlowJacobian hseq m s r
  let g : Vec 2 → ℝ := fun y => F y (basisVec j) i
  let h : Vec 2 → ℝ := fun y =>
    (F y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  let c : ℝ := (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  have he : 0 < epsilon β I.Λ m :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hR : 0 < R := by dsimp [R]; positivity
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    exact hflow.composed_jacobian_smooth s r hr
  have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    fun_prop
  have hhsmooth : ContDiff ℝ (⊤ : ℕ∞) h := by
    dsimp [h]
    fun_prop
  have hbarAll : flowJacobianBarNorm n R
      (fun y => F y - ContinuousLinearMap.id ℝ (Vec 2)) ≤
        ENNReal.ofReal 40 := by
    simpa [R, F] using hflow.flow_jacobian_composed s r hr n
  have hbar : barNorm n R h ≤ ENNReal.ofReal 40 := by
    unfold flowJacobianBarNorm at hbarAll
    change (⨆ i : Fin 2, ⨆ j : Fin 2,
      barNorm n R (fun y =>
        (F y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i)) ≤ _ at hbarAll
    change barNorm n R
      (fun y => (F y - ContinuousLinearMap.id ℝ (Vec 2))
        (basisVec j) i) ≤ ENNReal.ofReal 40
    apply le_trans _ hbarAll
    apply le_iSup_of_le i
    apply le_iSup_of_le j
    rfl
  have hhn : ContDiff ℝ n h := hhsmooth.of_le (by simp)
  have hcontinuous : Continuous (fun y : Vec 2 =>
      iteratedFDeriv ℝ n h y (fun k => basisVec (J k))) := by
    have h := hhn.continuous_iteratedFDeriv'
    fun_prop
  have hpt := barNorm_iterated_pointwise (n := n) (R := R) (B := 40)
    J hcontinuous hR (by norm_num) hbar x
  have hdecomp : g = fun y : Vec 2 => h y + c := by
    funext y
    simp [g, h, c, F]
  have hpow : 0 ≤ (epsilon β I.Λ m)⁻¹ ^ n := by positivity
  by_cases hn0 : n = 0
  · subst n
    have hHval : ‖h x‖ ≤ 40 := by
      simpa [iteratedFDeriv_zero_apply] using hpt
    have hc : ‖c‖ ≤ 1 := by
      dsimp [c]
      calc
        _ = ‖(basisVec j) i‖ := by simp
        _ ≤ ‖basisVec j‖ := norm_le_pi_norm (basisVec j) i
        _ = 1 := MaterialFlowBounds.basisVec_norm_eq_one j
    have hGval : ‖g x‖ ≤ 41 := by
      rw [hdecomp]
      calc
        _ ≤ ‖h x‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 40 + 1 := add_le_add hHval hc
        _ = 41 := by norm_num
    have hC41 : (41 : ℝ) ≤ Cmat := by dsimp [Cmat]; linarith
    have hGmat : ‖g x‖ ≤ Cmat := hGval.trans hC41
    simpa [iteratedFDeriv_zero_apply, g, F, section2MaterialSpatialConstant,
      Cmat, S] using hGmat
  · have hnpos : 1 ≤ n := by omega
    have hderivEq : iteratedFDeriv ℝ n g x
        (fun k => basisVec (J k)) =
      iteratedFDeriv ℝ n h x (fun k => basisVec (J k)) := by
      rw [hdecomp]
      exact MaterialFlowBounds.iteratedFDeriv_add_const_eq_of_pos
        hhn hnpos c x (fun k => basisVec (J k))
    have hfact : 0 < (n.factorial : ℝ) := by positivity
    let D : ℝ := ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) * R⁻¹ ^ n
    have hD : 0 < D := by dsimp [D]; positivity
    have hnormalize :
        40 / D ≤ 40 * (n.factorial : ℝ) * R ^ n := by
      apply (div_le_iff₀ hD).2
      have hprod : (40 * (n.factorial : ℝ) * R ^ n) * D =
          40 * ((n : ℝ) + 1) ^ 2 := by
        dsimp [D]
        rw [mul_assoc, ← mul_assoc, ← mul_assoc]
        rw [inv_pow]
        field_simp [ne_of_gt hR, ne_of_gt hfact]
      rw [hprod]
      have hsquare : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
        have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
        nlinarith
      nlinarith
    have hpoint : ‖iteratedFDeriv ℝ n h x
        (fun k => basisVec (J k))‖ ≤
          40 * (n.factorial : ℝ) * R ^ n := by
      calc
        _ ≤ 40 / D := by simpa [D] using hpt
        _ ≤ 40 * (n.factorial : ℝ) * R ^ n := hnormalize
    let fsum : ℕ → ℝ := fun q =>
      ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))
    have hsum : fsum n ≤ S := by
      dsimp [fsum, S]
      exact Finset.single_le_sum
        (f := fun q : ℕ => ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)))
        (s := Finset.range (N + 1))
        (fun q hq => by positivity)
        (Finset.mem_range.mpr (by omega))
    have hcoef : 40 * (n.factorial : ℝ) * (2 : ℝ) ^ (10 * n) ≤ Cmat := by
      dsimp [Cmat]
      nlinarith [hsum]
    have hRpow : R ^ n = (2 : ℝ) ^ (10 * n) *
        (epsilon β I.Λ m)⁻¹ ^ n := by
      dsimp [R]
      rw [mul_pow, ← pow_mul]
    have hbound : ‖iteratedFDeriv ℝ n g x
        (fun k => basisVec (J k))‖ ≤
          Cmat * (epsilon β I.Λ m)⁻¹ ^ n := by
      rw [hderivEq]
      calc
        _ ≤ 40 * (n.factorial : ℝ) * R ^ n := hpoint
        _ = (40 * (n.factorial : ℝ) * (2 : ℝ) ^ (10 * n)) *
            (epsilon β I.Λ m)⁻¹ ^ n := by rw [hRpow]; ring
        _ ≤ Cmat * (epsilon β I.Λ m)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right hcoef hpow
    simpa [section2MaterialSpatialConstant, Cmat, S] using hbound

end AVenhance.Infra.Construction
end
