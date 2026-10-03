/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialAuxiliaryInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialGoalSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialPullback
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds

/-! The finite noncommuting word induction is identified with the source
material iterates and packaged as `p.material.goal`. -/

@[expose] public section

open Homogenization MeasureTheory

noncomputable section

namespace AVenhance.Infra.Construction

open AVenhance.Infra.Section4

theorem MaterialGoalAllOrders.material_aux_pure_material_word_eq
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (ell : ℕ) :
    amnrWord (constructionJointVector b) (List.replicate ell none)
      (constructionJointScalar F) =
      constructionJointScalar (constructionMaterialIterate b ell F) := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      change amnrOp (constructionJointVector b) none
          (amnrWord (constructionJointVector b) (List.replicate ell none)
            (constructionJointScalar F)) =
        constructionJointScalar (constructionMaterialIterate b (ell + 1) F)
      rw [ih]
      funext p
      have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
      have hstep := constructionMaterialDerivative_eq_joint_fderiv
        (b := b) (F := constructionMaterialIterate b ell F) hiterate p.1 p.2
      change fderiv ℝ (constructionJointScalar
        (constructionMaterialIterate b ell F)) p
          (1, b p.1 p.2) = _
      simpa [constructionJointScalar, constructionJointVector,
        constructionMaterialIterate] using hstep.symm

theorem MaterialGoalAllOrders.material_aux_mixed_velocity_word_eq
    {β : ℝ} {I : AVenhance.Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m ell : ℕ) (i : Fin 2) (α : List (Fin 2)) :
    amnrWord (fun z : AmnrSpace => AVenhance.streamVel (Φ m) z.1 z.2)
      (amnrMixedWord α ell)
      (fun z => AVenhance.streamVel (Φ m) z.1 z.2 i) =
      fun z => amnrSpaceWord α
        (fun y => constructionMaterialIterate (streamVel (Φ m)) ell
          (fun r x => streamVel (Φ m) r x i) z.1 y) z.2 := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let bJ : AmnrSpace → Vec 2 := fun z => b z.1 z.2
  let F : ℝ → Vec 2 → ℝ := fun r x => b r x i
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) :=
    (smoothPeriodic_streamVel (streamSeq_isAdmissible hΦ m)).smooth
  have hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    exact (contDiff_apply ℝ ℝ i).comp hb
  have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
  change amnrWord bJ (α.map some ++ List.replicate ell none)
      (fun z => F z.1 z.2) = _
  rw [amnrWord_append]
  have hinner : amnrWord bJ (List.replicate ell none)
      (fun z => F z.1 z.2) =
      fun z => constructionMaterialIterate b ell F z.1 z.2 := by
    change amnrWord (constructionJointVector b) (List.replicate ell none)
        (constructionJointScalar F) = _
    exact MaterialGoalAllOrders.material_aux_pure_material_word_eq hb hF ell
  rw [hinner]
  exact amnrWord_spatial_slice hiterate bJ α

theorem MaterialGoalAllOrders.material_aux_fderiv_component
    {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => f y i) x (basisVec j) =
      fderiv ℝ f x (basisVec j) i := by
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa using h'

theorem MaterialGoalAllOrders.material_aux_gradient_iterate_eq
    {b : ℝ → Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointVector b)) (ell : ℕ) (i j : Fin 2) :
    constructionMaterialIterate b ell
        (fun r x => fderiv ℝ (fun y : Vec 2 => b r y i) x (basisVec j)) =
      materialIterateGradientEntry b ell b i j := by
  let F := fun r x => fderiv ℝ (fun y : Vec 2 => b r y i) x (basisVec j)
  let G := fun r x => fderiv ℝ (b r) x (basisVec j) i
  have hseed : F = G := by
    funext r x
    have hsliceMap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (r, y)) := by
      fun_prop
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (b r) := by
      have hs := hb.comp hsliceMap
      simpa [constructionJointVector, Function.comp_def] using hs
    exact MaterialGoalAllOrders.material_aux_fderiv_component hslice x i j
  have hiterate : constructionMaterialIterate b ell F =
      constructionMaterialIterate b ell G := by
    induction ell with
    | zero => exact hseed
    | succ ell ih =>
        change constructionMaterialDerivative b
          (constructionMaterialIterate b ell F) =
          constructionMaterialDerivative b (constructionMaterialIterate b ell G)
        rw [ih]
  simpa [F, G, materialIterateGradientEntry] using hiterate

theorem MaterialGoalAllOrders.material_aux_mixed_gradient_word_eq
    {β : ℝ} {I : AVenhance.Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m ell : ℕ) (i j : Fin 2) (α : List (Fin 2)) :
    amnrWord (fun z : AmnrSpace => AVenhance.streamVel (Φ m) z.1 z.2)
      (amnrMixedWord α ell)
      (amnrVelocityGradient
        (fun z : AmnrSpace => AVenhance.streamVel (Φ m) z.1 z.2) i j) =
      fun z => amnrSpaceWord α
        (fun y => materialIterateGradientEntry (streamVel (Φ m)) ell
          (streamVel (Φ m)) i j z.1 y) z.2 := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let bJ : AmnrSpace → Vec 2 := fun z => b z.1 z.2
  let F : ℝ → Vec 2 → ℝ := fun r x =>
    fderiv ℝ (fun y : Vec 2 => b r y i) x (basisVec j)
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) :=
    (smoothPeriodic_streamVel (streamSeq_isAdmissible hΦ m)).smooth
  have hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    have hgrad := amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn i j
    change ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient bJ i j)
    exact contDiffOn_univ.mp hgrad
  have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
  have hterminal : constructionJointScalar F = amnrVelocityGradient bJ i j := by
    rfl
  change amnrWord bJ (α.map some ++ List.replicate ell none)
      (amnrVelocityGradient bJ i j) = _
  rw [amnrWord_append]
  have hinner : amnrWord bJ (List.replicate ell none)
      (amnrVelocityGradient bJ i j) =
      fun z => materialIterateGradientEntry b ell (streamVel (Φ m)) i j z.1 z.2 := by
    have hpure := MaterialGoalAllOrders.material_aux_pure_material_word_eq hb hF ell
    calc
      _ = amnrWord bJ (List.replicate ell none) (constructionJointScalar F) := by
        rw [← hterminal]
      _ = constructionJointScalar (constructionMaterialIterate b ell F) := by
        change amnrWord (constructionJointVector b) (List.replicate ell none)
          (constructionJointScalar F) = _
        exact hpure
      _ = _ := by
        funext z
        exact congrFun (congrFun
          (MaterialGoalAllOrders.material_aux_gradient_iterate_eq hb ell i j) z.1) z.2
  rw [hinner]
  have hiterate' : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => materialIterateGradientEntry b ell (streamVel (Φ m)) i j z.1 z.2) := by
    have heq : constructionJointScalar (constructionMaterialIterate b ell F) =
        fun z : AmnrSpace => materialIterateGradientEntry b ell (streamVel (Φ m)) i j z.1 z.2 := by
      funext z
      exact congrFun (congrFun (MaterialGoalAllOrders.material_aux_gradient_iterate_eq hb ell i j)
          z.1) z.2
    rw [← heq]
    exact hiterate
  exact amnrWord_spatial_slice hiterate' bJ α

theorem MaterialGoalAllOrders.material_aux_iteratedFDeriv_component
    {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (x : Vec 2) (J : Fin n → Fin 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x
      (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x (fun k => basisVec (J k)) = _
  rw [hcomp]
  rfl

/-- All source-form `p.material.goal` bounds follow from the spatial stream-regularity estimates
and the differentiated recursion. The material cutoff is exactly `Nstar`;
the larger AMNR word budget is only an auxiliary combinatorial allowance. -/
theorem MaterialGoalAllOrders.p_material_goal_source_with_levels {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {K : ℝ} (hK : 1 ≤ K)
    (hlevels : MaterialAuxJetLevels I Φ (2 * Nstar β + 1) K (Nstar β))
    (m : ℕ) : PMaterialGoalSourceData I Φ K m := by
  refine ⟨hK, ?_, ?_⟩
  · intro n ell hpositive htotal t x J
    let α := List.ofFn J
    let B := K * epsilon β I.Λ m ^ (β - 1) *
      (epsilon β I.Λ m)⁻¹ ^ n * a β I.Λ m ^ ell
    have hE : 0 < epsilon β I.Λ m :=
      Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hA : 0 < a β I.Λ m :=
      Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hbudget : α.length + 2 * ell + 1 ≤ 2 * Nstar β + 1 := by
      simp [α]
      omega
    have hne : amnrMixedWord α ell ≠ [] := by
      intro hz
      have hlen := congrArg List.length hz
      simp [amnrMixedWord, α] at hlen
      omega
    have hcomponent (i : Fin 2) :
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate (streamVel (Φ m)) ell
            (fun r z => streamVel (Φ m) r z i) t y)
          x (fun k => basisVec (J k))‖ ≤ B := by
      have hword := hlevels.velocity m α ell (by omega) hne hbudget i (t, x)
      have heq := congrFun
        (MaterialGoalAllOrders.material_aux_mixed_velocity_word_eq hΦ m ell i α) (t, x)
      have hb := (smoothPeriodic_streamVel (streamSeq_isAdmissible hΦ m)).smooth
      have hF : ContDiff ℝ (⊤ : ℕ∞)
          (constructionJointScalar (fun r z => streamVel (Φ m) r z i)) := by
        change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 =>
          (constructionJointVector (streamVel (Φ m)) z) i)
        exact (contDiff_apply ℝ ℝ i).comp hb
      have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
      have hsliceMap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by
        fun_prop
      have hslice : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec 2 => constructionMaterialIterate (streamVel (Φ m)) ell
            (fun r z => streamVel (Φ m) r z i) t y) := by
        have hs := hiterate.comp hsliceMap
        change ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec 2 => constructionMaterialIterate (streamVel (Φ m)) ell
            (fun r z => streamVel (Φ m) r z i) t y) at hs
        exact hs
      simp only [α] at hword heq
      rw [heq] at hword
      rw [amnrSpaceWord_ofFn_eq_iteratedFDeriv hslice n J] at hword
      simpa [B, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hword
    have hvecSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => materialIterateVector (streamVel (Φ m)) ell
          (streamVel (Φ m)) t y) := by
      apply contDiff_pi.2
      intro i
      have hb := (smoothPeriodic_streamVel (streamSeq_isAdmissible hΦ m)).smooth
      have hF : ContDiff ℝ (⊤ : ℕ∞)
          (constructionJointScalar (fun r z => streamVel (Φ m) r z i)) := by
        change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 =>
          (constructionJointVector (streamVel (Φ m)) z) i)
        exact (contDiff_apply ℝ ℝ i).comp hb
      have hit := constructionMaterialIterate_joint_contDiff hb hF ell
      have hsliceMap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by
        fun_prop
      have hs := hit.comp hsliceMap
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => constructionMaterialIterate (streamVel (Φ m)) ell
          (fun r z => streamVel (Φ m) r z i) t y) at hs
      exact hs
    have hderiv : ∀ i,
        ‖iteratedFDeriv ℝ n
          (fun y : Vec 2 => materialIterateVector (streamVel (Φ m)) ell
            (streamVel (Φ m)) t y) x (fun k => basisVec (J k)) i‖ ≤ B := by
      intro i
      have heq : (fun y : Vec 2 => materialIterateVector (streamVel (Φ m)) ell
          (streamVel (Φ m)) t y i) =
          (fun y => constructionMaterialIterate (streamVel (Φ m)) ell
            (fun r z => streamVel (Φ m) r z i) t y) := by
        funext y
        rfl
      rw [← MaterialGoalAllOrders.material_aux_iteratedFDeriv_component hvecSmooth n x J i, heq]
      exact hcomponent i
    have hnorm : ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => materialIterateVector (streamVel (Φ m)) ell
          (streamVel (Φ m)) t y) x (fun k => basisVec (J k))‖ ≤ B := by
      rw [pi_norm_le_iff_of_nonneg hB]
      exact hderiv
    simpa [B, a, mul_assoc, mul_left_comm, mul_comm] using hnorm
  · intro n ell hn htotal t x i j J
    let α := List.ofFn J
    let q := n - 1
    let B := K * a β I.Λ m *
      (epsilon β I.Λ m)⁻¹ ^ q * a β I.Λ m ^ ell
    have hbudget : α.length + 2 * ell + 2 ≤ 2 * Nstar β + 1 := by
      simp [α]
      omega
    have hE : 0 < epsilon β I.Λ m :=
      Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hA : 0 < a β I.Λ m :=
      Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hb := (smoothPeriodic_streamVel (streamSeq_isAdmissible hΦ m)).smooth
    have hF : ContDiff ℝ (⊤ : ℕ∞)
        (constructionJointScalar
          (fun r z => fderiv ℝ (fun y : Vec 2 => streamVel (Φ m) r y i)
            z (basisVec j))) := by
      have hgrad := amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn i j
      change ContDiff ℝ (⊤ : ℕ∞)
        (amnrVelocityGradient (fun z : AmnrSpace => streamVel (Φ m) z.1 z.2) i j)
      exact contDiffOn_univ.mp hgrad
    have hiterate := constructionMaterialIterate_joint_contDiff
      hb hF ell
    have hsliceMap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by
      fun_prop
    have hiterEq := MaterialGoalAllOrders.material_aux_gradient_iterate_eq hb ell i j
    have hslice0 : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => constructionMaterialIterate (streamVel (Φ m)) ell
          (fun r z => fderiv ℝ (fun w : Vec 2 => streamVel (Φ m) r w i)
            z (basisVec j)) t y) := by
      have hs := hiterate.comp hsliceMap
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => constructionMaterialIterate (streamVel (Φ m)) ell
          (fun r z => fderiv ℝ (fun w : Vec 2 => streamVel (Φ m) r w i)
            z (basisVec j)) t y) at hs
      exact hs
    have hslice : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => materialIterateGradientEntry (streamVel (Φ m)) ell
          (streamVel (Φ m)) i j t y) := by
      rw [← congrFun hiterEq t]
      exact hslice0
    have hword := hlevels.gradient m α ell (by omega) hbudget i j (t, x)
    have heq := congrFun
      (MaterialGoalAllOrders.material_aux_mixed_gradient_word_eq hΦ m ell i j α) (t, x)
    simp only [α] at hword heq
    rw [heq] at hword
    rw [amnrSpaceWord_ofFn_eq_iteratedFDeriv hslice q J] at hword
    simpa [B, q, a, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hword

end AVenhance.Infra.Construction

end
