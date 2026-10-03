/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation
public import Mathlib.Analysis.ODE.Gronwall

/-! Uniform-in-time comparison estimates for first spatial variations. -/

@[expose] public section

open Homogenization
open Set
open Asymptotics
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem SecondSpatial.gronwallBound_zero_scale_second (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- A homogeneous linear flow with operator norm at most `M` grows by at most
`exp (M * (t-s))` on a forward interval. -/
theorem SecondSpatial.linearFlow_norm_bound_on_Ico
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (M : ℝ)
    (hM : 0 ≤ M) (hA : ∀ r, ‖A r‖ ≤ M)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (hV : AVenhance.IsFlow (fun r v => A r v) V)
    (s t : ℝ) (_hst : s ≤ t) :
    ∀ v r, r ∈ Ico s t →
      ‖V r v s‖ ≤ Real.exp (M * (t - s)) * ‖v‖ := by
  have hAL : ∀ r u w, ‖A r u - A r w‖ ≤ M * ‖u - w‖ := by
    intro r u w
    calc
      ‖A r u - A r w‖ = ‖A r (u - w)‖ := by rw [map_sub]
      _ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ := mul_le_mul_of_nonneg_right (hA r) (norm_nonneg _)
  have hzero := linearSystemFlow_zero A M hAL hV s
  intro v r hr
  have hgr := flow_spatial_gronwall (fun q z => A q z) hAL hV v 0 s r
  have hexp : Real.exp (M * |r - s|) ≤ Real.exp (M * (t - s)) := by
    apply Real.exp_le_exp.mpr
    calc
      M * |r - s| = M * (r - s) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
      _ ≤ M * (t - s) := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hM
  calc
    ‖V r v s‖ = ‖V r v s - V r 0 s‖ := by rw [hzero r, sub_zero]
    _ ≤ Real.exp (M * |r - s|) * ‖v - 0‖ := hgr
    _ ≤ Real.exp (M * (t - s)) * ‖v‖ := by
      simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg v)

/-- On a forward interval, the first variational solutions at two starting
points differ by at most a constant times the starting-point distance and the
initial direction norm. The constant is uniform in target time. -/
theorem exists_flow_variational_difference_bound_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (L M C : ℝ) (hL₀ : 0 ≤ L) (hM₀ : 0 ≤ M) (hC₀ : 0 ≤ C)
    (hL : ∀ q u w, ‖b q u - b q w‖ ≤ L * ‖u - w‖)
    (hM : ∀ q z, ‖jointSpatialFDeriv b q z‖ ≤ M)
    (hC : ∀ q z w,
      ‖jointSpatialFDeriv b q z - jointSpatialFDeriv b q w‖ ≤ C * ‖z - w‖)
    (x y : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∃ Vx, AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) Vx ∧
    ∃ Vy, AVenhance.IsFlow (linearizedFieldAlongFlow b X y s) Vy ∧
    ∃ K : ℝ, 0 ≤ K ∧
      K = gronwallBound 0 M
        (C * Real.exp (L * (t - s)) * Real.exp (M * (t - s))) (t - s) ∧
      ∀ r, r ∈ Icc s t → ∀ v, ‖Vy r v s - Vx r v s‖ ≤ K * ‖x - y‖ * ‖v‖ := by
  let d : ℝ := t - s
  let F : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let D : ℝ := C * F * E
  let K : ℝ := gronwallBound 0 M D d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hF₀ : 0 ≤ F := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hD₀ : 0 ≤ D := mul_nonneg (mul_nonneg hC₀ hF₀) hE₀
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
    have h := hmono (show 0 ≤ d by exact hd₀)
    simpa [K, gronwallBound_x0] using h
  obtain ⟨Vx, hVx, _⟩ := existsUnique_flow_variationalEquation hb hX x s
  obtain ⟨Vy, hVy, _⟩ := existsUnique_flow_variationalEquation hb hX y s
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q y s)
  have hAxLip : ∀ q u w, ‖Ax q u - Ax q w‖ ≤ M * ‖u - w‖ := by
    intro q u w
    calc
      ‖Ax q u - Ax q w‖ = ‖Ax q (u - w)‖ := by rw [map_sub]
      _ ≤ ‖Ax q‖ * ‖u - w‖ := (Ax q).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM q (X q x s)) (norm_nonneg _)
  have htraj : ∀ q, q ∈ Icc s t →
      ‖X q y s - X q x s‖ ≤ F * ‖x - y‖ := by
    intro q hq
    have hgr := flow_spatial_gronwall_of_le b hL hX y x s q hq.1
    have hexp : Real.exp (L * (q - s)) ≤ F := by
      apply Real.exp_le_exp.mpr
      dsimp [F, d]
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2]) hL₀
    calc
      ‖X q y s - X q x s‖ ≤ Real.exp (L * (q - s)) * ‖y - x‖ := hgr
      _ = Real.exp (L * (q - s)) * ‖x - y‖ := by rw [norm_sub_rev]
      _ ≤ F * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg (x - y))
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hAxlipN : ∀ q, LipschitzWith KN (Ax q) := by
    intro q
    apply LipschitzWith.of_dist_le_mul
    intro u w
    rw [dist_eq_norm, dist_eq_norm]
    exact hAxLip q u w
  have hVxBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vx q v s‖ ≤ E * ‖v‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico Ax M hM₀
      (fun q => hM q (X q x s)) hVx s t hst v q hq
    simpa [E, d] using h
  have hVyBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vy q v s‖ ≤ E * ‖v‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico Ay M hM₀
      (fun q => hM q (X q y s)) hVy s t hst v q hq
    simpa [E, d] using h
  have hKformula : K = gronwallBound 0 M
      (C * Real.exp (L * (t - s)) * Real.exp (M * (t - s))) (t - s) := by
    dsimp [K, D, F, E, d]
  refine ⟨Vx, hVx, Vy, hVy, K, hK₀, hKformula, ?_⟩
  intro r hr v
  let ε : ℝ := D * ‖x - y‖ * ‖v‖
  have hcoef : ∀ q, q ∈ Ico s t →
      ‖Ay q (Vy q v s) - Ax q (Vy q v s)‖ ≤ ε := by
    intro q hq
    have hAxy : ‖Ay q - Ax q‖ ≤ C * F * ‖x - y‖ := by
      calc
        ‖Ay q - Ax q‖ ≤ C * ‖X q y s - X q x s‖ := by
          simpa [Ay, Ax] using hC q (X q y s) (X q x s)
        _ ≤ C * (F * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (htraj q ⟨hq.1, le_of_lt hq.2⟩) hC₀
        _ = C * F * ‖x - y‖ := by ring
    calc
      ‖Ay q (Vy q v s) - Ax q (Vy q v s)‖ ≤
          ‖Ay q - Ax q‖ * ‖Vy q v s‖ := by
            simpa only [sub_apply] using (Ay q - Ax q).le_opNorm (Vy q v s)
      _ ≤ (C * F * ‖x - y‖) * (E * ‖v‖) :=
          mul_le_mul (hAxy) (hVyBound v q hq) (norm_nonneg _) (by positivity)
      _ = ε := by dsimp [ε, D]; ring
  let f : ℝ → Vec 2 := fun q => Vx q v s
  let g : ℝ → Vec 2 := fun q => Vy q v s
  have hfderiv (q : ℝ) : HasDerivAt f (Ax q (f q)) q := by
    simpa [f, Ax, linearizedFieldAlongFlow] using hVx.2 v s q
  have hgderiv (q : ℝ) : HasDerivAt g (Ay q (g q)) q := by
    simpa [g, Ay, linearizedFieldAlongFlow] using hVy.2 v s q
  have hfcont : ContinuousOn f (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hfderiv q)
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hgderiv q)
  have hfwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt f (Ax q (f q)) (Ici q) q :=
    fun q _ => (hfderiv q).hasDerivWithinAt
  have hgwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt g (Ay q (g q)) (Ici q) q :=
    fun q _ => (hgderiv q).hasDerivWithinAt
  have hfapprox : ∀ q ∈ Ico s t,
      dist (Ax q (f q)) (Ax q (f q)) ≤ (0 : ℝ) := by
    intro q hq
    simp
  have hgapprox : ∀ q ∈ Ico s t,
      dist (Ay q (g q)) (Ax q (g q)) ≤ ε := by
    intro q hq
    rw [dist_eq_norm]
    exact hcoef q hq
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, hVx.1, hVy.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (E := Vec 2) (K := KN) (v := fun q z => Ax q z)
    (f := f) (g := g) (f' := fun q => Ax q (f q)) (g' := fun q => Ay q (g q))
    (a := s) (b := t) (εf := 0) (εg := ε) (δ := 0)
    hAxlipN hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hdist := hcomp r hr
  have hKcast : (KN : ℝ) = M := rfl
  have hdist' : ‖Vx r v s - Vy r v s‖ ≤ gronwallBound 0 M ε (r - s) := by
    simpa only [f, g, dist_eq_norm, hKcast, zero_add] using hdist
  have htime : r - s ≤ d := by dsimp [d]; linarith [hr.2]
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
  let P : ℝ := ‖x - y‖ * ‖v‖
  have hscale : gronwallBound 0 M ε (r - s) =
      P * gronwallBound 0 M D (r - s) := by
    rw [show ε = P * D by dsimp [ε, P, D]; ring]
    rw [SecondSpatial.gronwallBound_zero_scale_second M D P (r - s)]
  calc
    ‖Vy r v s - Vx r v s‖ ≤ gronwallBound 0 M ε (r - s) := by
      simpa only [norm_sub_rev] using hdist'
    _ = P * gronwallBound 0 M D (r - s) := hscale
    _ ≤ P * K := by
      dsimp [P, K]
      exact mul_le_mul_of_nonneg_left (hmono htime) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = K * ‖x - y‖ * ‖v‖ := by dsimp [P]; ring

private theorem exists_flow_second_spatial_derivative_of_le_forcing1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (x : Vec (2 : ℕ)) (s t L M Cjac T : ℝ), (0 : ℝ) ≤ T → (∀ (t :
    ℝ) (x y v : Vec (2 : ℕ)), ‖(jointSpatialFDeriv b t y : Vec (2 : ℕ) → Vec (2 : ℕ)) v -
    (jointSpatialFDeriv b t x : Vec (2 : ℕ) → Vec (2 : ℕ)) v - (fderiv ℝ (fun (z : Vec (2 : ℕ))
    => (jointSpatialFDeriv b t z : Vec (2 : ℕ) → Vec (2 : ℕ)) v) x : Vec (2 : ℕ) → Vec (2 : ℕ))
    (y - x)‖ ≤ T * ‖v‖ * ‖y - x‖ * ‖y - x‖) → ∀ (C₂ : ℝ), (0 : ℝ) ≤ C₂ → (∀ (t : ℝ) (x h k : Vec
    (2 : ℕ)), ‖spatialSecondDerivativeEval b t x h k‖ ≤ C₂ * ‖h‖ * ‖k‖) →
  let V : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb hX
    x s);
  ∀ (Ctraj : ℝ), (0 : ℝ) ≤ Ctraj → (∀ r ∈ Icc s t, ∀ (h : Vec (2 : ℕ)), ‖X r (x + h) s - X r x s
    - V r h s‖ ≤ Ctraj * ‖h‖ * ‖h‖) →
  let d : ℝ := t - s;
  let F : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let Dvar : ℝ := Cjac * F * E;
  let Kvar : ℝ := gronwallBound 0 M Dvar d;
  let Cforce : ℝ := T * E * F * F + C₂ * Ctraj * E + C₂ * E * Kvar;
  ∀ (h k : Vec (2 : ℕ)) (Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ)), (∀ q ∈ Ico s t, ‖Vy q k s‖ ≤ E
    * ‖k‖) → (∀ q ∈ Ico s t, ‖V q h s‖ ≤ E * ‖h‖) → (∀ q ∈ Ico s t, ‖X q (x + h) s - X q x s‖ ≤
    F * ‖h‖) → (∀ q ∈ Ico s t, ‖Vy q k s - V q k s‖ ≤ Kvar * ‖h‖ * ‖k‖) →
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => jointSpatialFDeriv b q (X q x s);
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => jointSpatialFDeriv b q (X q (x + h) s);
  let Bq : ℝ → Vec 2 → Vec 2 → Vec 2 := fun q u v => spatialSecondDerivativeEval b q (X q x s) u
    v;
  let ε : ℝ := Cforce * ‖h‖ * ‖h‖ * ‖k‖;
  ∀ q ∈ Ico s t, ‖(Ay q : Vec (2 : ℕ) → Vec (2 : ℕ)) (Vy q k s) - (Ax q : Vec (2 : ℕ) → Vec (2 :
    ℕ)) (Vy q k s) - Bq q (V q h s) (V q k s)‖ ≤ ε
    := by
  intro b hb X hX x s t L M Cjac T hT₀ hT C₂ hC₂₀ hC₂ V Ctraj hCtraj₀ hCtraj d F E Dvar Kvar
      Cforce h k Vy hVhyBound hVhBound htraj hVdiff' Ax Ay Bq ε q hq
  let δ : Vec 2 := X q (x + h) s - X q x s
  have hTaylor := hT q (X q x s) (X q (x + h) s) (Vy q k s)
  have hTaylorId : Bq q δ (Vy q k s) =
      fderiv ℝ (fun z => jointSpatialFDeriv b q z (Vy q k s))
        (X q x s) δ := by
    exact spatialSecondDerivativeEval_eq_spatialJacobianFDeriv_apply
      hb q (X q x s) δ (Vy q k s)
  rw [← hTaylorId] at hTaylor
  have hTaylor' :
      ‖Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q δ (Vy q k s)‖ ≤
        T * ‖Vy q k s‖ * ‖δ‖ * ‖δ‖ := by
    simpa [Ay, Ax] using hTaylor
  have hBleft : Bq q δ (Vy q k s) - Bq q (V q h s) (Vy q k s) =
      Bq q (δ - V q h s) (Vy q k s) := by
    have hδ : δ = (δ - V q h s) + V q h s := by abel
    calc
      Bq q δ (Vy q k s) - Bq q (V q h s) (Vy q k s) =
          Bq q ((δ - V q h s) + V q h s) (Vy q k s) -
            Bq q (V q h s) (Vy q k s) := by
              exact congrArg (fun z => z - Bq q (V q h s) (Vy q k s))
                (congrArg (fun u => Bq q u (Vy q k s)) hδ)
      _ = Bq q (δ - V q h s) (Vy q k s) := by
            have hadd : Bq q ((δ - V q h s) + V q h s) (Vy q k s) =
                Bq q (δ - V q h s) (Vy q k s) +
                  Bq q (V q h s) (Vy q k s) := by
              simpa [Bq] using spatialSecondDerivativeEval_add_left b q (X q x s)
                (δ - V q h s) (V q h s) (Vy q k s)
            rw [hadd]
            abel
  have hBright : Bq q (V q h s) (Vy q k s) -
      Bq q (V q h s) (V q k s) =
        Bq q (V q h s) (Vy q k s - V q k s) := by
    have hy : Vy q k s = (Vy q k s - V q k s) + V q k s := by abel
    calc
      Bq q (V q h s) (Vy q k s) - Bq q (V q h s) (V q k s) =
      Bq q (V q h s) ((Vy q k s - V q k s) + V q k s) -
            Bq q (V q h s) (V q k s) := by
              exact congrArg (fun z => z - Bq q (V q h s) (V q k s))
                (congrArg (fun v => Bq q (V q h s) v) hy)
      _ = Bq q (V q h s) (Vy q k s - V q k s) := by
            have hadd : Bq q (V q h s)
                ((Vy q k s - V q k s) + V q k s) =
                Bq q (V q h s) (Vy q k s - V q k s) +
                  Bq q (V q h s) (V q k s) := by
              simpa [Bq] using spatialSecondDerivativeEval_add_right b q (X q x s)
                (V q h s) (Vy q k s - V q k s) (V q k s)
            rw [hadd]
            abel
  have hsplit :
      Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q (V q h s) (V q k s) =
        (Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q δ (Vy q k s)) +
          Bq q (δ - V q h s) (Vy q k s) +
          Bq q (V q h s) (Vy q k s - V q k s) := by
    rw [← hBleft, ← hBright]
    abel
  have htrajQ := htraj q hq
  have htrajRem := hCtraj q ⟨hq.1, le_of_lt hq.2⟩ h
  have hδrem : ‖δ - V q h s‖ ≤ Ctraj * ‖h‖ * ‖h‖ := by
    simpa [δ] using htrajRem
  have hB₁ : ‖Bq q (δ - V q h s) (Vy q k s)‖ ≤
      C₂ * (Ctraj * ‖h‖ * ‖h‖) * (E * ‖k‖) := by
    calc
      _ ≤ C₂ * ‖δ - V q h s‖ * ‖Vy q k s‖ := hC₂ q (X q x s) _ _
      _ ≤ C₂ * (Ctraj * ‖h‖ * ‖h‖) * (E * ‖k‖) := by
        have hfirst := mul_le_mul_of_nonneg_left hδrem hC₂₀
        have hsecond := hVhyBound q hq
        calc
          C₂ * ‖δ - V q h s‖ * ‖Vy q k s‖ =
              (C₂ * ‖δ - V q h s‖) * ‖Vy q k s‖ := by ring
          _ ≤ (C₂ * (Ctraj * ‖h‖ * ‖h‖)) * ‖Vy q k s‖ :=
                mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
          _ ≤ (C₂ * (Ctraj * ‖h‖ * ‖h‖)) * (E * ‖k‖) :=
                mul_le_mul_of_nonneg_left hsecond (by positivity)
          _ = C₂ * (Ctraj * ‖h‖ * ‖h‖) * (E * ‖k‖) := by ring
  have hB₂ : ‖Bq q (V q h s) (Vy q k s - V q k s)‖ ≤
      C₂ * (E * ‖h‖) * (Kvar * ‖h‖ * ‖k‖) := by
    calc
      _ ≤ C₂ * ‖V q h s‖ * ‖Vy q k s - V q k s‖ := hC₂ q (X q x s) _ _
      _ ≤ C₂ * (E * ‖h‖) * (Kvar * ‖h‖ * ‖k‖) := by
        have hfirst := hVhBound q hq
        have hsecond := hVdiff' q hq
        calc
          C₂ * ‖V q h s‖ * ‖Vy q k s - V q k s‖ =
              (C₂ * ‖V q h s‖) * ‖Vy q k s - V q k s‖ := by ring
          _ ≤ (C₂ * (E * ‖h‖)) * ‖Vy q k s - V q k s‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hfirst hC₂₀) (norm_nonneg _)
          _ ≤ (C₂ * (E * ‖h‖)) * (Kvar * ‖h‖ * ‖k‖) :=
                mul_le_mul_of_nonneg_left hsecond (by positivity)
          _ = C₂ * (E * ‖h‖) * (Kvar * ‖h‖ * ‖k‖) := by ring
  have hTa : ‖Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q δ (Vy q k s)‖ ≤
      (T * E * F * F) * ‖h‖ * ‖h‖ * ‖k‖ := by
    have hδ : ‖δ‖ ≤ F * ‖h‖ := by simpa [δ] using htrajQ
    calc
      _ ≤ T * ‖Vy q k s‖ * ‖δ‖ * ‖δ‖ := hTaylor'
      _ ≤ T * (E * ‖k‖) * (F * ‖h‖) * (F * ‖h‖) := by
        gcongr
        exact hVhyBound q hq
      _ = (T * E * F * F) * ‖h‖ * ‖h‖ * ‖k‖ := by ring
  rw [hsplit]
  calc
    ‖(Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q δ (Vy q k s)) +
        Bq q (δ - V q h s) (Vy q k s) +
        Bq q (V q h s) (Vy q k s - V q k s)‖ ≤
    ‖Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q δ (Vy q k s)‖ +
          ‖Bq q (δ - V q h s) (Vy q k s)‖ +
          ‖Bq q (V q h s) (Vy q k s - V q k s)‖ := by
            calc
              _ = ‖((Ay q (Vy q k s) - Ax q (Vy q k s) -
                  Bq q δ (Vy q k s)) + Bq q (δ - V q h s) (Vy q k s)) +
                    Bq q (V q h s) (Vy q k s - V q k s)‖ := rfl
              _ ≤ ‖(Ay q (Vy q k s) - Ax q (Vy q k s) -
                  Bq q δ (Vy q k s)) + Bq q (δ - V q h s) (Vy q k s)‖ +
                    ‖Bq q (V q h s) (Vy q k s - V q k s)‖ := norm_add_le _ _
              _ ≤ (‖Ay q (Vy q k s) - Ax q (Vy q k s) -
                  Bq q δ (Vy q k s)‖ +
                ‖Bq q (δ - V q h s) (Vy q k s)‖) +
                    ‖Bq q (V q h s) (Vy q k s - V q k s)‖ := by
                exact add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (T * E * F * F) * ‖h‖ * ‖h‖ * ‖k‖ +
          (C₂ * (Ctraj * ‖h‖ * ‖h‖) * (E * ‖k‖)) +
          (C₂ * (E * ‖h‖) * (Kvar * ‖h‖ * ‖k‖)) := by
            exact add_le_add (add_le_add hTa hB₁) hB₂
    _ = Cforce * ‖h‖ * ‖h‖ * ‖k‖ := by
          dsimp [Cforce]
          ring
    _ = ε := by rfl

private theorem exists_flow_second_spatial_derivative_of_le_branch1_branch1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (x : Vec (2 : ℕ)) (s t L M : ℝ) (hM₀ : (0 : ℝ) ≤ M) (Cjac T :
    ℝ), (0 : ℝ) ≤ T → ∀ (C₂ : ℝ), (0 : ℝ) ≤ C₂ →
  let V : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb hX
    x s);
  ∀ (hV : IsFlow (linearizedFieldAlongFlow b X x s) V) (Ctraj : ℝ), (0 : ℝ) ≤ Ctraj →
  let d : ℝ := t - s;
  let F : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let Dvar : ℝ := Cjac * F * E;
  let Kvar : ℝ := gronwallBound 0 M Dvar d;
  let Cforce : ℝ := T * E * F * F + C₂ * Ctraj * E + C₂ * E * Kvar;
  let Q : ℝ := gronwallBound 0 M Cforce d;
  (0 : ℝ) ≤ Kvar → ∀ (h k : Vec (2 : ℕ)) (Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ)),
  let Vh : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb
    hX (x + h) s);
  Vh = Vy →
  let ε : ℝ := Cforce * ‖h‖ * ‖h‖ * ‖k‖;
  let KN : ℝ≥0 := ⟨M, hM₀⟩;
  let R : ℝ → Vec 2 := fun q => Vy q k s - V q k s - flowSecondVariation hb hX x s hV h k q 0 s;
  let f : ℝ → Vec 2 := fun _ => 0;
  let g : ℝ → Vec 2 := fun q => R q;
  (∀ t_1 ∈ Icc s t, dist (f t_1) (g t_1) ≤ gronwallBound (0 : ℝ) (↑KN : ℝ) ((0 : ℝ) + ε) (t_1 -
    s)) → (↑KN : ℝ) = M → gronwallBound (0 : ℝ) M ε d = ‖h‖ * ‖h‖ * ‖k‖ * Q → ∀ q ∈ Icc s t,
    ‖Classical.choose (existsUnique_flow_variationalEquation hb hX (x + h) s) q k s - V q k s -
    flowSecondVariation hb hX x s (Classical.choose_spec (existsUnique_flow_variationalEquation
    hb hX x s)).left h k q (0 : Vec (2 : ℕ)) s‖ ≤ Q * ‖h‖ * ‖h‖ * ‖k‖
    := by
  intro b hb X hX x s t L M hM₀ Cjac T hT₀ C₂ hC₂₀ V hV Ctraj hCtraj₀ d F E Dvar Kvar Cforce Q
      hKvar₀ h k Vy Vh hVhEq ε KN R f g hcomp hKcast hεscale q hq
  have hdistq := hcomp q hq
  have hdistq' : ‖R q‖ ≤ gronwallBound 0 M ε (q - s) := by
    simpa [f, g, R, d, dist_eq_norm, hKcast, zero_add, norm_sub_rev] using hdistq
  have hε₀ : 0 ≤ ε := by dsimp [ε, Cforce]; positivity
  have htime : q - s ≤ d := by dsimp [d]; linarith [hq.2]
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hε₀ hM₀
  have hVhReplace :
      ‖Vh q k s - V q k s -
          flowSecondVariation hb hX x s
            (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
            h k q 0 s‖ = ‖R q‖ := by
    rw [hVhEq]
  rw [hVhReplace]
  calc
    ‖R q‖ ≤ gronwallBound 0 M ε (q - s) := hdistq'
    _ ≤ gronwallBound 0 M ε d := hmono htime
    _ = (‖h‖ * ‖h‖ * ‖k‖) * Q := hεscale
    _ = Q * ‖h‖ * ‖h‖ * ‖k‖ := by ring

private theorem exists_flow_second_spatial_derivative_of_le_branch1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (x : Vec (2 : ℕ)) (s t : ℝ), s ≤ t → ∀ (L : ℝ), (0 : ℝ) ≤ L →
    (∀ (t : ℝ) (x y : Vec (2 : ℕ)), ‖b t x - b t y‖ ≤ L * ‖x - y‖) → ∀ (M : ℝ), (0 : ℝ) ≤ M → (∀
    (t : ℝ) (x : Vec (2 : ℕ)), ‖jointSpatialFDeriv b t x‖ ≤ M) → ∀ (Cjac : ℝ), (0 : ℝ) ≤ Cjac →
    (∀ (t : ℝ) (x y : Vec (2 : ℕ)), ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac
    * ‖x - y‖) → ∀ (T : ℝ), (0 : ℝ) ≤ T → (∀ (t : ℝ) (x y v : Vec (2 : ℕ)), ‖(jointSpatialFDeriv
    b t y : Vec (2 : ℕ) → Vec (2 : ℕ)) v - (jointSpatialFDeriv b t x : Vec (2 : ℕ) → Vec (2 :
    ℕ)) v - (fderiv ℝ (fun (z : Vec (2 : ℕ)) => (jointSpatialFDeriv b t z : Vec (2 : ℕ) → Vec (2
    : ℕ)) v) x : Vec (2 : ℕ) → Vec (2 : ℕ)) (y - x)‖ ≤ T * ‖v‖ * ‖y - x‖ * ‖y - x‖) → ∀ (C₂ :
    ℝ), (0 : ℝ) ≤ C₂ → (∀ (t : ℝ) (x h k : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval b t x h k‖
    ≤ C₂ * ‖h‖ * ‖k‖) →
  let V : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb hX
    x s);
  ∀ (hV : IsFlow (linearizedFieldAlongFlow b X x s) V), (∀ (y : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 :
    ℕ)), IsFlow (linearizedFieldAlongFlow b X x s) y → y = V) → ∀ (Ctraj : ℝ), (0 : ℝ) ≤ Ctraj →
    (∀ r ∈ Icc s t, ∀ (h : Vec (2 : ℕ)), ‖X r (x + h) s - X r x s - V r h s‖ ≤ Ctraj * ‖h‖ *
    ‖h‖) → ∀ (B : Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)), (∀ (h k : Vec (2 : ℕ)), ((B
    : Vec (2 : ℕ) → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)) h : Vec (2 : ℕ) → Vec (2 : ℕ)) k =
    flowSecondVariation hb hX x s hV h k t (0 : Vec (2 : ℕ)) s) →
  let d : ℝ := t - s;
  let F : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let Dvar : ℝ := Cjac * F * E;
  let Kvar : ℝ := gronwallBound 0 M Dvar d;
  let Cforce : ℝ := T * E * F * F + C₂ * Ctraj * E + C₂ * E * Kvar;
  let Q : ℝ := gronwallBound 0 M Cforce d;
  (0 : ℝ) ≤ Kvar → (∀ (k : Vec (2 : ℕ)), (fderiv ℝ (fun (y : Vec (2 : ℕ)) => X t y s) x : Vec (2
    : ℕ) → Vec (2 : ℕ)) k = V t k s) → ∀ (h k : Vec (2 : ℕ)), ‖(fderiv ℝ (fun (y : Vec (2 : ℕ))
    => X t y s) (x + h) : Vec (2 : ℕ) → Vec (2 : ℕ)) k - (fderiv ℝ (fun (y : Vec (2 : ℕ)) => X t
    y s) x : Vec (2 : ℕ) → Vec (2 : ℕ)) k - ((B : Vec (2 : ℕ) → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)) h
    : Vec (2 : ℕ) → Vec (2 : ℕ)) k‖ ≤ Q * ‖h‖ * ‖h‖ * ‖k‖ ∧ ∀ q ∈ Icc s t, ‖Classical.choose
    (existsUnique_flow_variationalEquation hb hX (x + h) s) q k s - V q k s -
    flowSecondVariation hb hX x s (Classical.choose_spec (existsUnique_flow_variationalEquation
    hb hX x s)).left h k q (0 : Vec (2 : ℕ)) s‖ ≤ Q * ‖h‖ * ‖h‖ * ‖k‖
    := by
  intro b hb X hX x s t hst L hL₀ hL M hM₀ hM Cjac hCjac₀ hCjac T hT₀ hT C₂ hC₂₀ hC₂ V hV hVuniq
      Ctraj hCtraj₀ hCtraj B hB d F E Dvar Kvar Cforce Q hKvar₀ hJx h k
  obtain ⟨Vx, hVx, Vy, hVy, Kvar', hKvar'₀, hKvar'formula, hVdiff⟩ :=
    exists_flow_variational_difference_bound_all_times_of_le
      hb hX L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac x (x + h) s t hst
  have hVxEq : Vx = V := hVuniq Vx hVx
  let Vh : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX (x + h) s)
  have hVh : AVenhance.IsFlow (linearizedFieldAlongFlow b X (x + h) s) Vh :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX (x + h) s)).1
  have hVhEq : Vh = Vy :=
    ((Classical.choose_spec (existsUnique_flow_variationalEquation hb hX (x + h) s)).2
      Vy hVy).symm
  have hKvarEq : Kvar' = Kvar := by
    rw [hKvar'formula]
  have hVhyBound (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vy q k s‖ ≤ E * ‖k‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r (x + h) s)) M hM₀
      (fun r => hM r (X r (x + h) s)) hVy s t hst k q hq
    simpa [E, d] using h
  have hVhBound (q : ℝ) (hq : q ∈ Ico s t) :
      ‖V q h s‖ ≤ E * ‖h‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r x s)) M hM₀
      (fun r => hM r (X r x s)) hV s t hst h q hq
    simpa [E, d] using h
  have htraj (q : ℝ) (hq : q ∈ Ico s t) :
      ‖X q (x + h) s - X q x s‖ ≤ F * ‖h‖ := by
    have hgr := flow_spatial_gronwall_of_le b hL hX (x + h) x s q hq.1
    have hexp : Real.exp (L * (q - s)) ≤ F := by
      apply Real.exp_le_exp.mpr
      dsimp [F, d]
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2]) hL₀
    calc
      ‖X q (x + h) s - X q x s‖ ≤
          Real.exp (L * (q - s)) * ‖(x + h) - x‖ := hgr
      _ ≤ F * ‖h‖ := by
        simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg h)
  have hVdiff' (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vy q k s - V q k s‖ ≤ Kvar * ‖h‖ * ‖k‖ := by
    have h := hVdiff q ⟨hq.1, le_of_lt hq.2⟩ k
    rw [hVxEq, hKvarEq] at h
    simpa [norm_sub_rev] using h
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q (x + h) s)
  let Bq : ℝ → Vec 2 → Vec 2 → Vec 2 :=
    fun q u v => spatialSecondDerivativeEval b q (X q x s) u v
  let ε : ℝ := Cforce * ‖h‖ * ‖h‖ * ‖k‖
  have hforcing (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q (V q h s) (V q k s)‖ ≤ ε := by
    exact @exists_flow_second_spatial_derivative_of_le_forcing1 b hb X hX x s t L M Cjac T hT₀ hT
        C₂ hC₂₀ hC₂ Ctraj hCtraj₀ hCtraj h k Vy hVhyBound hVhBound htraj hVdiff' q hq
  have hAL : ∀ q u w, ‖Ax q u - Ax q w‖ ≤ M * ‖u - w‖ := by
    intro q u w
    calc
      ‖Ax q u - Ax q w‖ = ‖Ax q (u - w)‖ := by rw [map_sub]
      _ ≤ ‖Ax q‖ * ‖u - w‖ := (Ax q).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM q (X q x s)) (norm_nonneg _)
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hALip : ∀ q, LipschitzWith KN (Ax q) := by
    intro q
    apply LipschitzWith.of_dist_le_mul
    intro u w
    rw [dist_eq_norm, dist_eq_norm]
    exact hAL q u w
  let R : ℝ → Vec 2 := fun q => Vy q k s - V q k s -
    flowSecondVariation hb hX x s hV h k q 0 s
  let f : ℝ → Vec 2 := fun _ => 0
  let g : ℝ → Vec 2 := fun q => R q
  let G : ℝ → Vec 2 := fun q =>
    Ay q (Vy q k s) - Ax q (Vy q k s) - Bq q (V q h s) (V q k s)
  have hfderiv (q : ℝ) : HasDerivAt f (Ax q (f q)) q := by
    simpa [f] using (hasDerivAt_const q (0 : Vec 2))
  have hgderiv (q : ℝ) : HasDerivAt g (Ax q (g q) + G q) q := by
    have hsum := (hVy.2 k s q).sub (hV.2 k s q)
    have hW := flowSecondVariation_isFlow hb hX x s hV h k
    have hWderiv := hW.2 0 s q
    have hsub := hsum.sub hWderiv
    convert hsub using 1
    ext i
    simp [g, R, G, Ax, Ay, Bq, linearizedFieldAlongFlow, map_sub]
    abel
  have hfcont : ContinuousOn f (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hfderiv q)
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hgderiv q)
  have hfwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt f (Ax q (f q)) (Ici q) q :=
    fun q _ => (hfderiv q).hasDerivWithinAt
  have hgwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt g (Ax q (g q) + G q) (Ici q) q :=
    fun q _ => (hgderiv q).hasDerivWithinAt
  have hfapprox : ∀ q ∈ Ico s t,
      dist (Ax q (f q)) (Ax q (f q)) ≤ (0 : ℝ) := by
    intro q hq
    simp
  have hgapprox : ∀ q ∈ Ico s t,
      dist (Ax q (g q) + G q) (Ax q (g q)) ≤ ε := by
    intro q hq
    rw [dist_eq_norm]
    simpa [G, sub_eq_add_neg] using hforcing q hq
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    have hW := flowSecondVariation_isFlow hb hX x s hV h k
    simp [f, g, R, hV.1, hVy.1, hW.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (E := Vec 2) (K := KN) (v := fun q z => Ax q z)
    (f := f) (g := g) (f' := fun q => Ax q (f q))
    (g' := fun q => Ax q (g q) + G q)
    (a := s) (b := t) (εf := 0) (εg := ε) (δ := 0)
    hALip hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hdist := hcomp t ⟨hst, le_rfl⟩
  have hKcast : (KN : ℝ) = M := rfl
  have hdist' : ‖R t‖ ≤ gronwallBound 0 M ε d := by
    simpa [f, g, R, d, dist_eq_norm, hKcast, zero_add, norm_sub_rev] using hdist
  have hεscale : gronwallBound 0 M ε d =
      (‖h‖ * ‖h‖ * ‖k‖) * Q := by
    rw [show ε = (‖h‖ * ‖h‖ * ‖k‖) * Cforce by dsimp [ε]; ring]
    rw [SecondSpatial.gronwallBound_zero_scale_second M Cforce (‖h‖ * ‖h‖ * ‖k‖) d]
  constructor
  · have hVyAt : fderiv ℝ (fun y => X t y s) (x + h) k = Vy t k s := by
      obtain ⟨Vy', Jy, hVy', hJy, hDy⟩ :=
        exists_flow_hasFDerivAt_spatial_of_le hb hX (x + h) s t hst
      obtain ⟨Vycanonical, hu⟩ := existsUnique_flow_variationalEquation hb hX (x + h) s
      have hEq' : Vy' = Vycanonical := hu.2 Vy' hVy'
      have hcanonicalEq : Vycanonical = Vy := (hu.2 Vy hVy).symm
      have hEq : Vy' = Vy := by
        calc
          Vy' = Vycanonical := hEq'
          _ = Vy := hcanonicalEq
      rw [hDy.fderiv, hJy k, hEq]
    have hVxAt : fderiv ℝ (fun y => X t y s) x k = V t k s := hJx k
    rw [hVyAt, hVxAt, hB h k]
    calc
      ‖R t‖ ≤ gronwallBound 0 M ε d := hdist'
      _ = (‖h‖ * ‖h‖ * ‖k‖) * Q := hεscale
      _ = Q * ‖h‖ * ‖h‖ * ‖k‖ := by ring
  · exact @exists_flow_second_spatial_derivative_of_le_branch1_branch1 b hb X hX x s t L M hM₀
      Cjac T hT₀ C₂ hC₂₀ hV Ctraj hCtraj₀ hKvar₀ h k Vy hVhEq hcomp hKcast hεscale
/-- The spatial derivative of the flow has a quadratic Taylor remainder whose
linear term is the continuous bilinear second variation. -/
theorem exists_flow_second_spatial_derivative_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∃ V, AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V ∧
    ∃ B : Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2,
      (∀ h k, B h k = flowSecondVariation hb hX x s
        ((existsUnique_flow_variationalEquation hb hX x s).choose_spec.1) h k t 0 s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h k,
      (‖fderiv ℝ (fun y => X t y s) (x + h) k -
          fderiv ℝ (fun y => X t y s) x k - B h k‖ ≤
        C * ‖h‖ * ‖h‖ * ‖k‖) ∧
      ∀ q, q ∈ Icc s t →
        ‖(Classical.choose
            (existsUnique_flow_variationalEquation hb hX (x + h) s)) q k s -
          V q k s - flowSecondVariation hb hX x s
            (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
            h k q 0 s‖ ≤
            C * ‖h‖ * ‖h‖ * ‖k‖ := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨T, hT₀, hT⟩ := exists_global_spatialFDeriv_apply_taylor_remainder hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  let V : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  have hVuniq : ∀ y, AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) y → y = V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2
  obtain ⟨Ctraj, hCtraj₀, hCtraj⟩ :=
    flow_variational_quadratic_remainder_all_times_of_le hb hX x s t hst hV
  obtain ⟨B, hB⟩ := exists_flowSecondVariationContinuousBilinear_of_le
    hb hX x s t hst hV
  let d : ℝ := t - s
  let F : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let Dvar : ℝ := Cjac * F * E
  let Kvar : ℝ := gronwallBound 0 M Dvar d
  let Cforce : ℝ := T * E * F * F + C₂ * Ctraj * E + C₂ * E * Kvar
  let Q : ℝ := gronwallBound 0 M Cforce d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hF₀ : 0 ≤ F := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hDvar₀ : 0 ≤ Dvar := mul_nonneg (mul_nonneg hCjac₀ hF₀) hE₀
  have hKvar₀ : 0 ≤ Kvar := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hDvar₀ hM₀
    have h := hmono hd₀
    simpa [Kvar, gronwallBound_x0] using h
  have hCforce₀ : 0 ≤ Cforce := by
    dsimp [Cforce]
    positivity
  have hQ₀ : 0 ≤ Q := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
    have h := hmono hd₀
    simpa [Q, gronwallBound_x0] using h
  have hQformula : Q = gronwallBound 0 M Cforce (t - s) := by
    dsimp [Q, d]
  obtain ⟨V0, J0, hV0, hJ0, hD0⟩ :=
    exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
  have hV0Eq : V0 = V := hVuniq V0 hV0
  have hJx : ∀ k, fderiv ℝ (fun y => X t y s) x k = V t k s := by
    intro k
    rw [hD0.fderiv, hJ0 k, hV0Eq]
  refine ⟨V, hV, B, ?_, Q, hQ₀, ?_⟩
  · intro h k
    simpa [V] using hB h k
  · exact @exists_flow_second_spatial_derivative_of_le_branch1 b hb X hX x s t hst L hL₀ hL M hM₀
      hM Cjac hCjac₀ hCjac T hT₀ hT C₂ hC₂₀ hC₂ hV hVuniq Ctraj hCtraj₀ hCtraj B hB hKvar₀ hJx
/-- The first spatial derivative of a forward flow map is differentiable, and
its derivative is the continuous bilinear second variation. -/
theorem exists_flow_spatialFDeriv_hasFDerivAt_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∃ V, AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V ∧
    ∃ B : Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2,
      (∀ h k, B h k = flowSecondVariation hb hX x s
        ((existsUnique_flow_variationalEquation hb hX x s).choose_spec.1)
        h k t 0 s) ∧
      HasFDerivAt (fun y => fderiv ℝ (fun z => X t z s) y) B x := by
  obtain ⟨V, hV, B, hB, C, hC₀, hrem⟩ :=
    exists_flow_second_spatial_derivative_of_le hb hX x s t hst
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    fun y => fderiv ℝ (fun z => X t z s) y
  have hJrem (u : Vec 2) : ‖J (x + u) - J x - B u‖ ≤ C * ‖u‖ * ‖u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro k
    have h := (hrem u k).1
    simpa [J, sub_apply] using h
  have hnormLittle : (fun u : Vec 2 => ‖J (x + u) - J x - B u‖) =o[𝓝 0]
      fun u => ‖u‖ := by
    rw [isLittleO_iff]
    intro c hc
    have hcball : Metric.ball (0 : Vec 2) (c / (C + 1)) ∈ 𝓝 (0 : Vec 2) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hcball] with u hu
    have hu' : ‖u‖ < c / (C + 1) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hscaled' : ‖u‖ * (C + 1) < c :=
      (lt_div_iff₀ (by linarith [hC₀])).mp hu'
    have hscaled : (C + 1) * ‖u‖ ≤ c := by
      exact le_of_lt (by simpa [mul_comm] using hscaled')
    have hbnd : ‖J (x + u) - J x - B u‖ ≤ c * ‖u‖ := by
      calc
        ‖J (x + u) - J x - B u‖ ≤ C * ‖u‖ * ‖u‖ := hJrem u
        _ ≤ c * ‖u‖ := by
          have hC : C ≤ C + 1 := by linarith [hC₀]
          calc
            C * ‖u‖ * ‖u‖ = C * (‖u‖ * ‖u‖) := by ring
            _ ≤ (C + 1) * (‖u‖ * ‖u‖) :=
              mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = ((C + 1) * ‖u‖) * ‖u‖ := by ring
            _ ≤ c * ‖u‖ := mul_le_mul_of_nonneg_right hscaled (norm_nonneg _)
    change |‖J (x + u) - J x - B u‖| ≤ c * |‖u‖|
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hbnd
  have hLittle : (fun u : Vec 2 => J (x + u) - J x - B u) =o[𝓝 0]
      fun u => u := by
    exact isLittleO_norm_norm.mp hnormLittle
  refine ⟨V, hV, B, hB, ?_⟩
  apply (hasFDerivAt_iff_isLittleO_nhds_zero).2
  simpa [J] using hLittle

/-- On a forward compact time interval, each spatial direction of the first
variation is jointly continuous in target time and base point. -/
theorem flow_variational_direction_jointContinuous_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      fderiv ℝ (fun z => X p.1 z s) p.2 h) (Icc s t ×ˢ univ) := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨_, _, _, _, K, hK₀, hKformula, _⟩ :=
    exists_flow_variational_difference_bound_all_times_of_le
      hb hX L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac
      (0 : Vec 2) 0 s t hst
  let Kdir : ℝ≥0 := ⟨K * ‖h‖, mul_nonneg hK₀ (norm_nonneg h)⟩
  let f : Vec 2 × ℝ → Vec 2 := fun p =>
    fderiv ℝ (fun z => X p.2 z s) p.1 h
  have htime (x : Vec 2) : ContinuousOn (fun q => f (x, q)) (Icc s t) := by
    let V : ℝ → Vec 2 → ℝ → Vec 2 :=
      Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
    have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
    have hVuniq : ∀ Y,
        AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) Y → Y = V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2
    have hident (q : ℝ) : f (x, q) = V q h s := by
      obtain ⟨Vq, Jq, hVq, hJq, hDq⟩ :=
        exists_flow_hasFDerivAt_spatial hb hX x s q
      have hVqEq : Vq = V := hVuniq Vq hVq
      change fderiv ℝ (fun z => X q z s) x h = V q h s
      rw [hDq.fderiv, hJq h, hVqEq]
    have hVcont : ContinuousOn (fun q => V q h s) (Icc s t) :=
      HasDerivAt.continuousOn (fun q _ => hV.2 h s q)
    exact hVcont.congr (fun q _ => hident q)
  have hspace (q : ℝ) (hq : q ∈ Icc s t) :
      LipschitzOnWith Kdir (fun x => f (x, q)) univ := by
    have hLip : LipschitzWith Kdir (fun x => f (x, q)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      obtain ⟨Vx, hVx, Vy, hVy, K', _, hK'formula, hVdiff⟩ :=
        exists_flow_variational_difference_bound_all_times_of_le
          hb hX L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac x y s t hst
      have hKeq : K' = K := by
        calc
          K' = gronwallBound 0 M
              (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t - s))) (t - s) := hK'formula
          _ = K := hKformula.symm
      obtain ⟨Vxq, Jxq, hVxq, hJxq, hDxq⟩ :=
        exists_flow_hasFDerivAt_spatial_of_le hb hX x s q hq.1
      obtain ⟨Vyq, Jyq, hVyq, hJyq, hDyq⟩ :=
        exists_flow_hasFDerivAt_spatial_of_le hb hX y s q hq.1
      obtain ⟨Vxc, hVxUnique⟩ := existsUnique_flow_variationalEquation hb hX x s
      obtain ⟨Vyc, hVyUnique⟩ := existsUnique_flow_variationalEquation hb hX y s
      have hVxEq : Vxq = Vx := by
        calc
          Vxq = Vxc := hVxUnique.2 Vxq hVxq
          _ = Vx := (hVxUnique.2 Vx hVx).symm
      have hVyEq : Vyq = Vy := by
        calc
          Vyq = Vyc := hVyUnique.2 Vyq hVyq
          _ = Vy := (hVyUnique.2 Vy hVy).symm
      have hx : f (x, q) = Vx q h s := by
        change fderiv ℝ (fun z => X q z s) x h = Vx q h s
        rw [hDxq.fderiv, hJxq h, hVxEq]
      have hy : f (y, q) = Vy q h s := by
        change fderiv ℝ (fun z => X q z s) y h = Vy q h s
        rw [hDyq.fderiv, hJyq h, hVyEq]
      have hdiff := hVdiff q ⟨hq.1, hq.2⟩ h
      rw [hKeq] at hdiff
      calc
        ‖f (x, q) - f (y, q)‖ = ‖Vx q h s - Vy q h s‖ := by rw [hx, hy]
        _ = ‖Vy q h s - Vx q h s‖ := norm_sub_rev _ _
        _ ≤ K * ‖x - y‖ * ‖h‖ := hdiff
        _ = (K * ‖h‖) * dist x y := by rw [dist_eq_norm]; ring
    exact hLip.lipschitzOnWith
  let g : ℝ × Vec 2 → Vec 2 := fun p => f (p.2, p.1)
  have hprod : ContinuousOn g (Icc s t ×ˢ univ) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' g Kdir hspace
      (fun x _ => by simpa [g] using htime x)
  simpa [g, f] using hprod

/-- The second spatial derivative of the field is globally Lipschitz in its
base point, with a constant uniform in time and both directions. -/
theorem exists_global_spatialSecondDerivativeEval_lipschitz
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y h k,
      ‖spatialSecondDerivativeEval b t x h k -
        spatialSecondDerivativeEval b t y h k‖ ≤ C * ‖x - y‖ * ‖h‖ * ‖k‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialThirdFDeriv_bound hb
  refine ⟨C, hC₀, ?_⟩
  intro t x y h k
  let f : Vec 2 → Vec 2 := fun z => b t z
  let G := fun z => iteratedFDeriv ℝ 2 f z
  let m : Fin 2 → Vec 2 := fun i => if i = 0 then h else k
  have hf : ContDiff ℝ ∞ f := by
    exact hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hG : Differentiable ℝ G := by
    have htwo : (2 : ℕ∞ω) < ∞ := by
      change (↑(2 : ℕ∞) : ℕ∞ω) < (↑(⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
    simpa [G] using hf.differentiable_iteratedFDeriv htwo
  have hGderiv : ∀ z, ‖fderiv ℝ G z‖ ≤ C := by
    intro z
    change ‖fderiv ℝ (fun z => iteratedFDeriv ℝ 2 f z) z‖ ≤ C
    rw [norm_fderiv_iteratedFDeriv]
    exact hC t z
  have hGlip : ‖G x - G y‖ ≤ C * ‖x - y‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG z) (fun z _ => hGderiv z) (Set.mem_univ _) (Set.mem_univ _)
  have hEval (z : Vec 2) :
      spatialSecondDerivativeEval b t z h k = G z m := by
    rw [spatialSecondDerivativeEval_eq_spatialJacobianFDeriv_apply hb]
    have hslice : (fun w => jointSpatialFDeriv b t w k) =
        fun w => (fderiv ℝ f w) k := by
      funext w
      rw [jointSpatialFDeriv_eq_slice hb]
    rw [hslice]
    have hfSlice : Differentiable ℝ (fderiv ℝ f) :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hconst : DifferentiableAt ℝ (fun _ : Vec 2 => k) z := differentiableAt_const k
    have heval := fderiv_clm_apply (hfSlice z) hconst
    have hD2 : fderiv ℝ (fun w => (fderiv ℝ f w) k) z h =
        (fderiv ℝ (fderiv ℝ f) z h) k := by
      rw [heval]
      simp
    rw [hD2]
    simp [G, m, iteratedFDeriv_two_apply]
  have hprod : (∏ i : Fin 2, ‖m i‖) = ‖h‖ * ‖k‖ := by
    simp [m, Fin.prod_univ_succ]
  calc
    ‖spatialSecondDerivativeEval b t x h k -
        spatialSecondDerivativeEval b t y h k‖ =
          ‖(G x - G y) m‖ := by rw [hEval x, hEval y]; simp
    _ ≤ ‖G x - G y‖ * ∏ i : Fin 2, ‖m i‖ := (G x - G y).le_opNorm m
    _ ≤ (C * ‖x - y‖) * (‖h‖ * ‖k‖) := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hGlip (by positivity)
    _ = C * ‖x - y‖ * ‖h‖ * ‖k‖ := by ring

/-- The second variational flow depends Lipschitz continuously on the base
point, uniformly over a forward time interval. -/
noncomputable def flowSecondVariationLipschitzConstant
    (L M Cjac C₂ C₃ s t : ℝ) : ℝ :=
  let d := t - s
  let F := Real.exp (L * d)
  let E := Real.exp (M * d)
  let Kvar := gronwallBound 0 M (Cjac * F * E) d
  let Ksecond := gronwallBound 0 M (C₂ * E * E) d
  let Cforce := Cjac * F * Ksecond + C₃ * F * E * E +
    C₂ * Kvar * E + C₂ * E * Kvar
  gronwallBound 0 M Cforce d

private theorem exists_flow_secondVariation_lipschitz_all_times_of_le_force2 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (L M C₂ C₃ : ℝ), (0 : ℝ) ≤ C₂ → (0 : ℝ) ≤ C₃ → (∀ (t : ℝ) (x
    h k : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval b t x h k‖ ≤ C₂ * ‖h‖ * ‖k‖) → (∀ (t : ℝ)
    (x y h k : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval b t x h k -
    spatialSecondDerivativeEval b t y h k‖ ≤ C₃ * ‖x - y‖ * ‖h‖ * ‖k‖) → ∀ (x y : Vec (2 : ℕ))
    (s t : ℝ) (h k : Vec (2 : ℕ)) (Kvar : ℝ), (0 : ℝ) ≤ Kvar →
  let Vx : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb
    hX x s);
  let Vy : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb
    hX y s);
  let d : ℝ := t - s;
  let F : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  (∀ q ∈ Ico s t, ‖X q y s - X q x s‖ ≤ F * ‖x - y‖) → (∀ (v : Vec (2 : ℕ)), ∀ q ∈ Ico s t, ‖Vx
    q v s‖ ≤ E * ‖v‖) → (∀ (v : Vec (2 : ℕ)), ∀ q ∈ Ico s t, ‖Vy q v s‖ ≤ E * ‖v‖) → (∀ q ∈ Ico
    s t, ∀ (v : Vec (2 : ℕ)), ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖) →
  let Sx : ℝ → Vec 2 → Vec 2 → Vec 2 := fun q u v => spatialSecondDerivativeEval b q (X q x s) u
    v;
  let Sy : ℝ → Vec 2 → Vec 2 → Vec 2 := fun q u v => spatialSecondDerivativeEval b q (X q y s) u
    v;
  let Fx : ℝ → Vec 2 := fun q => Sx q (Vx q h s) (Vx q k s);
  let Fy : ℝ → Vec 2 := fun q => Sy q (Vy q h s) (Vy q k s);
  ∀ q ∈ Ico s t, ‖Fy q - Fx q‖ ≤ (C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) * ‖x - y‖ *
    ‖h‖ * ‖k‖
    := by
  intro b hb X hX L M C₂ C₃ hC₂₀ hC₃₀ hC₂ hC₃ x y s t h k Kvar hKvar₀ Vx Vy d F E htraj hVxBound
      hVyBound hVdiff' Sx Sy Fx Fy q hq
  have hsplit : Fy q - Fx q =
      (Sy q (Vy q h s) (Vy q k s) - Sx q (Vy q h s) (Vy q k s)) +
        Sx q (Vy q h s - Vx q h s) (Vy q k s) +
        Sx q (Vx q h s) (Vy q k s - Vx q k s) := by
    have hleft : Sx q (Vy q h s) (Vy q k s) -
        Sx q (Vx q h s) (Vy q k s) =
          Sx q (Vy q h s - Vx q h s) (Vy q k s) := by
      have harg : Vy q h s = (Vy q h s - Vx q h s) + Vx q h s := by abel
      calc
        Sx q (Vy q h s) (Vy q k s) - Sx q (Vx q h s) (Vy q k s) =
            Sx q ((Vy q h s - Vx q h s) + Vx q h s) (Vy q k s) -
              Sx q (Vx q h s) (Vy q k s) := by
                exact congrArg (fun z => z - Sx q (Vx q h s) (Vy q k s))
                  (congrArg (fun u => Sx q u (Vy q k s)) harg)
        _ = Sx q (Vy q h s - Vx q h s) (Vy q k s) := by
          change spatialSecondDerivativeEval b q (X q x s)
              ((Vy q h s - Vx q h s) + Vx q h s) (Vy q k s) - _ = _
          rw [spatialSecondDerivativeEval_add_left]
          abel
    have hright : Sx q (Vx q h s) (Vy q k s) -
        Sx q (Vx q h s) (Vx q k s) =
          Sx q (Vx q h s) (Vy q k s - Vx q k s) := by
      have karg : Vy q k s = (Vy q k s - Vx q k s) + Vx q k s := by abel
      calc
        Sx q (Vx q h s) (Vy q k s) - Sx q (Vx q h s) (Vx q k s) =
            Sx q (Vx q h s) ((Vy q k s - Vx q k s) + Vx q k s) -
              Sx q (Vx q h s) (Vx q k s) := by
                exact congrArg (fun z => z - Sx q (Vx q h s) (Vx q k s))
                  (congrArg (fun v => Sx q (Vx q h s) v) karg)
        _ = Sx q (Vx q h s) (Vy q k s - Vx q k s) := by
          change spatialSecondDerivativeEval b q (X q x s) (Vx q h s)
              ((Vy q k s - Vx q k s) + Vx q k s) - _ = _
          rw [spatialSecondDerivativeEval_add_right]
          abel
    calc
      Fy q - Fx q = (Sy q (Vy q h s) (Vy q k s) -
          Sx q (Vy q h s) (Vy q k s)) +
            (Sx q (Vy q h s) (Vy q k s) -
              Sx q (Vx q h s) (Vy q k s)) +
            (Sx q (Vx q h s) (Vy q k s) - Sx q (Vx q h s) (Vx q k s)) := by abel
      _ = _ := by rw [hleft, hright]
  have hfirst : ‖Sy q (Vy q h s) (Vy q k s) -
      Sx q (Vy q h s) (Vy q k s)‖ ≤
      (C₃ * F * E * E) * ‖x - y‖ * ‖h‖ * ‖k‖ := by
    calc
      _ ≤ C₃ * ‖X q y s - X q x s‖ * ‖Vy q h s‖ * ‖Vy q k s‖ :=
        hC₃ q (X q y s) (X q x s) (Vy q h s) (Vy q k s)
      _ ≤ C₃ * (F * ‖x - y‖) * (E * ‖h‖) * (E * ‖k‖) := by
        calc
          _ ≤ (C₃ * (F * ‖x - y‖)) * ‖Vy q h s‖ * ‖Vy q k s‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (htraj q hq) hC₃₀)
                (norm_nonneg _)) (norm_nonneg _)
          _ ≤ (C₃ * (F * ‖x - y‖)) * (E * ‖h‖) * ‖Vy q k s‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hVyBound h q hq) (by positivity))
              (norm_nonneg _)
          _ ≤ C₃ * (F * ‖x - y‖) * (E * ‖h‖) * (E * ‖k‖) := by
            exact mul_le_mul_of_nonneg_left (hVyBound k q hq) (by positivity)
      _ = (C₃ * F * E * E) * ‖x - y‖ * ‖h‖ * ‖k‖ := by ring
  have hsecond : ‖Sx q (Vy q h s - Vx q h s) (Vy q k s)‖ ≤
      (C₂ * Kvar * E) * ‖x - y‖ * ‖h‖ * ‖k‖ := by
    calc
      _ ≤ C₂ * ‖Vy q h s - Vx q h s‖ * ‖Vy q k s‖ :=
        hC₂ q (X q x s) _ _
      _ ≤ C₂ * (Kvar * ‖x - y‖ * ‖h‖) * (E * ‖k‖) := by
        calc
          _ ≤ C₂ * (Kvar * ‖x - y‖ * ‖h‖) * ‖Vy q k s‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hVdiff' q hq h) (by positivity))
              (norm_nonneg _)
          _ ≤ C₂ * (Kvar * ‖x - y‖ * ‖h‖) * (E * ‖k‖) := by
            exact mul_le_mul_of_nonneg_left (hVyBound k q hq) (by positivity)
      _ = (C₂ * Kvar * E) * ‖x - y‖ * ‖h‖ * ‖k‖ := by ring
  have hthird : ‖Sx q (Vx q h s) (Vy q k s - Vx q k s)‖ ≤
      (C₂ * E * Kvar) * ‖x - y‖ * ‖h‖ * ‖k‖ := by
    calc
      _ ≤ C₂ * ‖Vx q h s‖ * ‖Vy q k s - Vx q k s‖ :=
        hC₂ q (X q x s) _ _
      _ ≤ C₂ * (E * ‖h‖) * (Kvar * ‖x - y‖ * ‖k‖) := by
        calc
          _ ≤ C₂ * (E * ‖h‖) * ‖Vy q k s - Vx q k s‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hVxBound h q hq) (by positivity))
              (norm_nonneg _)
          _ ≤ C₂ * (E * ‖h‖) * (Kvar * ‖x - y‖ * ‖k‖) := by
            exact mul_le_mul_of_nonneg_left (hVdiff' q hq k) (by positivity)
      _ = (C₂ * E * Kvar) * ‖x - y‖ * ‖h‖ * ‖k‖ := by ring
  rw [hsplit]
  calc
    _ ≤ (‖Sy q (Vy q h s) (Vy q k s) - Sx q (Vy q h s) (Vy q k s)‖ +
        ‖Sx q (Vy q h s - Vx q h s) (Vy q k s)‖ +
        ‖Sx q (Vx q h s) (Vy q k s - Vx q k s)‖) := by
          calc
            _ ≤ ‖(Sy q (Vy q h s) (Vy q k s) -
                  Sx q (Vy q h s) (Vy q k s)) +
                  Sx q (Vy q h s - Vx q h s) (Vy q k s)‖ +
                  ‖Sx q (Vx q h s) (Vy q k s - Vx q k s)‖ := norm_add_le _ _
            _ ≤ _ := add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ _ := by
      calc
        _ ≤ ((C₃ * F * E * E) * ‖x - y‖ * ‖h‖ * ‖k‖ +
            (C₂ * Kvar * E) * ‖x - y‖ * ‖h‖ * ‖k‖) +
            (C₂ * E * Kvar) * ‖x - y‖ * ‖h‖ * ‖k‖ := by
              exact add_le_add (add_le_add hfirst hsecond) hthird
        _ = (C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) *
            ‖x - y‖ * ‖h‖ * ‖k‖ := by ring

private theorem exists_flow_secondVariation_lipschitz_all_times_of_le_Gbound3 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (L M Cjac C₂ C₃ : ℝ), (0 : ℝ) ≤ Cjac → (∀ (t : ℝ) (x y : Vec
    (2 : ℕ)), ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac * ‖x - y‖) → ∀ (x y :
    Vec (2 : ℕ)) (s t : ℝ) (h k : Vec (2 : ℕ)) (Kvar : ℝ),
  let Vx : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb
    hX x s);
  let Vy : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose (existsUnique_flow_variationalEquation hb
    hX y s);
  ∀ (hVy : IsFlow (linearizedFieldAlongFlow b X y s) Vy) (Ksecond : ℝ), (∀ r ∈ Icc s t, ∀ (h k :
    Vec (2 : ℕ)), ‖flowSecondVariation hb hX y s hVy h k r (0 : Vec (2 : ℕ)) s‖ ≤ Ksecond * ‖h‖
    * ‖k‖) →
  let d : ℝ := t - s;
  let F : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let Cforce : ℝ := Cjac * F * Ksecond + C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar;
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => jointSpatialFDeriv b q (X q x s);
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => jointSpatialFDeriv b q (X q y s);
  (∀ q ∈ Ico s t, ‖X q y s - X q x s‖ ≤ F * ‖x - y‖) →
  let Sx : ℝ → Vec 2 → Vec 2 → Vec 2 := fun q u v => spatialSecondDerivativeEval b q (X q x s) u
    v;
  let Sy : ℝ → Vec 2 → Vec 2 → Vec 2 := fun q u v => spatialSecondDerivativeEval b q (X q y s) u
    v;
  let Fx : ℝ → Vec 2 := fun q => Sx q (Vx q h s) (Vx q k s);
  let Fy : ℝ → Vec 2 := fun q => Sy q (Vy q h s) (Vy q k s);
  let ε : ℝ := Cforce * ‖x - y‖ * ‖h‖ * ‖k‖;
  (∀ q ∈ Ico s t, ‖Fy q - Fx q‖ ≤ (C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) * ‖x - y‖ *
    ‖h‖ * ‖k‖) →
  let Wy : ℝ → Vec 2 := fun q => flowSecondVariation hb hX y s hVy h k q 0 s;
  let G : ℝ → Vec 2 := fun q => Ay q (Wy q) - Ax q (Wy q) + Fy q - Fx q;
  ∀ q ∈ Ico s t, ‖G q‖ ≤ ε
    := by
  intro b hb X hX L M Cjac C₂ C₃ hCjac₀ hCjac x y s t h k Kvar Vx Vy hVy Ksecond hWbound d F E
      Cforce Ax Ay htraj Sx Sy Fx Fy ε hforce Wy G q hq
  have htrajQ := htraj q hq
  have hAxDiff : ‖Ay q - Ax q‖ ≤ Cjac * F * ‖x - y‖ := by
    calc
      ‖Ay q - Ax q‖ ≤ Cjac * ‖X q y s - X q x s‖ := by
        simpa [Ay, Ax] using hCjac q (X q y s) (X q x s)
      _ ≤ Cjac * (F * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left htrajQ hCjac₀
      _ = Cjac * F * ‖x - y‖ := by ring
  have hAterm : ‖Ay q (Wy q) - Ax q (Wy q)‖ ≤
      (Cjac * F * Ksecond) * ‖x - y‖ * ‖h‖ * ‖k‖ := by
    have hw := hWbound q ⟨hq.1, le_of_lt hq.2⟩ h k
    have hw' : ‖Wy q‖ ≤ Ksecond * ‖h‖ * ‖k‖ := by
      simpa [Wy] using hw
    calc
      _ ≤ ‖Ay q - Ax q‖ * ‖Wy q‖ := by
        simpa only [sub_apply] using (Ay q - Ax q).le_opNorm (Wy q)
      _ ≤ (Cjac * F * ‖x - y‖) * (Ksecond * ‖h‖ * ‖k‖) :=
        mul_le_mul hAxDiff hw' (norm_nonneg _) (by positivity)
      _ = (Cjac * F * Ksecond) * ‖x - y‖ * ‖h‖ * ‖k‖ := by ring
  have hFbound := hforce q hq
  have htotal := add_le_add hAterm hFbound
  dsimp [G, ε, Cforce]
  calc
    ‖Ay q (Wy q) - Ax q (Wy q) + Fy q - Fx q‖ ≤
        ‖Ay q (Wy q) - Ax q (Wy q)‖ + ‖Fy q - Fx q‖ := by
          simpa [sub_eq_add_neg, add_assoc] using norm_add_le
            (Ay q (Wy q) - Ax q (Wy q)) (Fy q - Fx q)
    _ ≤ (Cjac * F * Ksecond + C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) *
        ‖x - y‖ * ‖h‖ * ‖k‖ := by
          calc
            _ ≤ (Cjac * F * Ksecond) * ‖x - y‖ * ‖h‖ * ‖k‖ +
                (C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) *
                  ‖x - y‖ * ‖h‖ * ‖k‖ := htotal
            _ = _ := by ring

theorem exists_flow_secondVariation_lipschitz_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (L M Cjac C₂ C₃ : ℝ)
    (hL₀ : 0 ≤ L) (hM₀ : 0 ≤ M) (hCjac₀ : 0 ≤ Cjac)
    (hC₂₀ : 0 ≤ C₂) (hC₃₀ : 0 ≤ C₃)
    (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (hM : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (hCjac : ∀ t x y,
      ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac * ‖x - y‖)
    (hC₂ : ∀ t x h k,
      ‖spatialSecondDerivativeEval b t x h k‖ ≤ C₂ * ‖h‖ * ‖k‖)
    (hC₃ : ∀ t x y h k,
      ‖spatialSecondDerivativeEval b t x h k - spatialSecondDerivativeEval b t y h k‖ ≤
        C₃ * ‖x - y‖ * ‖h‖ * ‖k‖)
    (x y : Vec 2) (s t : ℝ) (hst : s ≤ t) (h k : Vec 2) :
    ∃ C : ℝ, 0 ≤ C ∧ C = flowSecondVariationLipschitzConstant L M Cjac C₂ C₃ s t ∧
      ∀ q, q ∈ Icc s t →
      ‖flowSecondVariation hb hX y s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
          h k q 0 s -
        flowSecondVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
          h k q 0 s‖ ≤ C * ‖x - y‖ * ‖h‖ * ‖k‖ := by
  obtain ⟨Vx₀, hVx₀, Vy₀, hVy₀, Kvar, hKvar₀, hKvarFormula, hVdiff⟩ :=
    exists_flow_variational_difference_bound_all_times_of_le
      hb hX L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac x y s t hst
  let Vx : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  let Vy : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX y s)
  have hVx : IsFlow (linearizedFieldAlongFlow b X x s) Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  have hVy : IsFlow (linearizedFieldAlongFlow b X y s) Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s)).1
  have hVxEq : Vx₀ = Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2 Vx₀ hVx₀
  have hVyEq : Vy₀ = Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s)).2 Vy₀ hVy₀
  have hVdiffCanon (q : ℝ) (hq : q ∈ Icc s t) (v : Vec 2) :
      ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖ := by
    simpa only [hVyEq, hVxEq] using hVdiff q hq v
  obtain ⟨Ksecond, hKsecond₀, hKsecondFormula, hWbound⟩ :=
    flowSecondVariation_bound_all_times_of_le hb hX M C₂ hM₀ hM hC₂₀ hC₂
      y s t hst hVy
  let d : ℝ := t - s
  let F : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let Cforce : ℝ := Cjac * F * Ksecond + C₃ * F * E * E +
    C₂ * Kvar * E + C₂ * E * Kvar
  let K : ℝ := gronwallBound 0 M Cforce d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hF₀ : 0 ≤ F := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hCforce₀ : 0 ≤ Cforce := by dsimp [Cforce]; positivity
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
    have h := hmono hd₀
    simpa [K, gronwallBound_x0] using h
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q y s)
  have hAxLip : ∀ q u v, ‖Ax q u - Ax q v‖ ≤ M * ‖u - v‖ := by
    intro q u v
    calc
      ‖Ax q u - Ax q v‖ = ‖Ax q (u - v)‖ := by rw [map_sub]
      _ ≤ ‖Ax q‖ * ‖u - v‖ := (Ax q).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM q (X q x s)) (norm_nonneg _)
  have htraj (q : ℝ) (hq : q ∈ Ico s t) :
      ‖X q y s - X q x s‖ ≤ F * ‖x - y‖ := by
    have hgr := flow_spatial_gronwall_of_le b hL hX y x s q hq.1
    have hexp : Real.exp (L * (q - s)) ≤ F := by
      apply Real.exp_le_exp.mpr
      dsimp [F, d]
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2]) hL₀
    calc
      ‖X q y s - X q x s‖ ≤ Real.exp (L * (q - s)) * ‖y - x‖ := hgr
      _ = Real.exp (L * (q - s)) * ‖x - y‖ := by rw [norm_sub_rev]
      _ ≤ F * ‖x - y‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hVxBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vx q v s‖ ≤ E * ‖v‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r x s)) M hM₀
      (fun r => hM r (X r x s)) hVx s t hst v q hq
    simpa [E, d] using h
  have hVyBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vy q v s‖ ≤ E * ‖v‖ := by
    have h := SecondSpatial.linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r y s)) M hM₀
      (fun r => hM r (X r y s)) hVy s t hst v q hq
    simpa [E, d] using h
  have hKvarEq : Kvar = gronwallBound 0 M
      (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t - s))) (t - s) :=
    hKvarFormula
  have hVdiff' (q : ℝ) (hq : q ∈ Ico s t) (v : Vec 2) :
      ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖ :=
    hVdiffCanon q ⟨hq.1, le_of_lt hq.2⟩ v
  let Sx : ℝ → Vec 2 → Vec 2 → Vec 2 :=
    fun q u v => spatialSecondDerivativeEval b q (X q x s) u v
  let Sy : ℝ → Vec 2 → Vec 2 → Vec 2 :=
    fun q u v => spatialSecondDerivativeEval b q (X q y s) u v
  let Fx : ℝ → Vec 2 := fun q => Sx q (Vx q h s) (Vx q k s)
  let Fy : ℝ → Vec 2 := fun q => Sy q (Vy q h s) (Vy q k s)
  let ε : ℝ := Cforce * ‖x - y‖ * ‖h‖ * ‖k‖
  have hforce (q : ℝ) (hq : q ∈ Ico s t) : ‖Fy q - Fx q‖ ≤
      (C₃ * F * E * E + C₂ * Kvar * E + C₂ * E * Kvar) *
        ‖x - y‖ * ‖h‖ * ‖k‖ := by
    exact @exists_flow_secondVariation_lipschitz_all_times_of_le_force2 b hb X hX L M C₂ C₃ hC₂₀
        hC₃₀ hC₂ hC₃ x y s t h k Kvar hKvar₀ htraj hVxBound hVyBound hVdiff' q hq
  let Wx : ℝ → Vec 2 := fun q => flowSecondVariation hb hX x s hVx h k q 0 s
  let Wy : ℝ → Vec 2 := fun q => flowSecondVariation hb hX y s hVy h k q 0 s
  let Z : ℝ → Vec 2 := fun q => Wy q - Wx q
  let G : ℝ → Vec 2 := fun q =>
    Ay q (Wy q) - Ax q (Wy q) + Fy q - Fx q
  have hWxd := flowSecondVariation_isFlow hb hX x s
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1) h k
  have hWyd := flowSecondVariation_isFlow hb hX y s
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1) h k
  have hZderiv (q : ℝ) : HasDerivAt Z (Ax q (Z q) + G q) q := by
    have hsum := (hWyd.2 0 s q).sub (hWxd.2 0 s q)
    convert hsum using 1
    ext i
    simp [Z, G, Wx, Wy, Ax, Ay, Fx, Fy, Sx, Sy]
    abel
  have hALip : ∀ q u v, ‖Ax q u - Ax q v‖ ≤ M * ‖u - v‖ := hAxLip
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hALipschitz : ∀ q, LipschitzWith KN (fun z => Ax q z) := by
    intro q
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hALip q u v
  let f : ℝ → Vec 2 := fun _ => 0
  let g : ℝ → Vec 2 := Z
  have hfderiv (q : ℝ) : HasDerivAt f (Ax q (f q)) q := by
    simpa [f] using (hasDerivAt_const q (0 : Vec 2))
  have hgderiv (q : ℝ) : HasDerivAt g (Ax q (g q) + G q) q := by
    simpa [g] using hZderiv q
  have hfcont : ContinuousOn f (Icc s t) := continuousOn_const
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hgderiv q)
  have hfwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt f (Ax q (f q)) (Ici q) q :=
    fun q _ => (hfderiv q).hasDerivWithinAt
  have hgwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt g (Ax q (g q) + G q) (Ici q) q :=
    fun q _ => (hgderiv q).hasDerivWithinAt
  have hfapprox : ∀ q ∈ Ico s t,
      dist (Ax q (f q)) (Ax q (f q)) ≤ (0 : ℝ) := by
    intro q hq
    simp
  have hGbound (q : ℝ) (hq : q ∈ Ico s t) :
      ‖G q‖ ≤ ε := by
    exact @exists_flow_secondVariation_lipschitz_all_times_of_le_Gbound3 b hb X hX L M Cjac C₂ C₃
        hCjac₀ hCjac x y s t h k Kvar hVy Ksecond hWbound htraj hforce q hq
  have hgapprox : ∀ q ∈ Ico s t,
      dist (Ax q (g q) + G q) (Ax q (g q)) ≤ ε := by
    intro q hq
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hGbound q hq
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, Z, Wx, Wy, hWxd.1, hWyd.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (K := KN) (v := fun q z => Ax q z) (f := f) (g := g)
    (f' := fun q => Ax q (f q)) (g' := fun q => Ax q (g q) + G q)
    (a := s) (b := t) (εf := 0) (εg := ε) (δ := 0)
    hALipschitz hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hKcast : (KN : ℝ) = M := rfl
  let P : ℝ := ‖x - y‖ * ‖h‖ * ‖k‖
  have hεscale : gronwallBound 0 M ε d = P * K := by
    rw [show ε = P * Cforce by dsimp [ε, P]; ring]
    rw [SecondSpatial.gronwallBound_zero_scale_second M Cforce P d]
  have hKformula : K = flowSecondVariationLipschitzConstant L M Cjac C₂ C₃ s t := by
    dsimp [K, flowSecondVariationLipschitzConstant, Cforce, F, E, d]
    rw [hKsecondFormula, hKvarFormula]
  refine ⟨K, hK₀, hKformula, ?_⟩
  intro q hq
  have hdist := hcomp q hq
  have hnorm : ‖Z q‖ = dist (f q) (g q) := by
    simp only [dist_eq_norm, zero_sub, neg_sub, Z, f, g]
    exact norm_sub_rev _ _
  have hdist' : ‖Z q‖ ≤ gronwallBound 0 M ε (q - s) := by
    rw [hnorm]
    simpa only [hKcast, zero_add] using hdist
  have htime : q - s ≤ d := by dsimp [d]; linarith [hq.2]
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
  have hscale : gronwallBound 0 M ε (q - s) = P *
      gronwallBound 0 M Cforce (q - s) := by
    rw [show ε = P * Cforce by dsimp [ε, P]; ring]
    rw [SecondSpatial.gronwallBound_zero_scale_second M Cforce P (q - s)]
  have hKbound : gronwallBound 0 M Cforce (q - s) ≤ K := by
    dsimp [K]
    exact hmono htime
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  calc
    ‖flowSecondVariation hb hX y s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
        h k q 0 s -
      flowSecondVariation hb hX x s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
        h k q 0 s‖ = ‖Z q‖ := by
          change ‖Wy q - Wx q‖ = ‖Z q‖
          rfl
    _ ≤ gronwallBound 0 M ε (q - s) := hdist'
    _ = P * gronwallBound 0 M Cforce (q - s) := hscale
    _ ≤ P * K := mul_le_mul_of_nonneg_left hKbound hP₀
    _ = K * ‖x - y‖ * ‖h‖ * ‖k‖ := by dsimp [P]; ring

end AVenhance.Infra.Flow
