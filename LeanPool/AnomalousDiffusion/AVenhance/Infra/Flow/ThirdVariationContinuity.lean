/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Existence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Multilinear
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Growth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondVariationContinuity

/-! Uniform base-point continuity estimates for the third variation. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem ThirdVariationContinuity.gronwallBound_zero_scale_third_cont (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- A homogeneous linear flow with operator norm at most `M` grows by at
most `exp (M * (t-s))` on a forward interval. -/
theorem ThirdVariationContinuity.thirdCont_linearFlow_norm_bound_on_Ico
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

/-- The uniform base-point Lipschitz constant for the third variation on a
forward compact target-time interval. -/
noncomputable def flowThirdVariationLipschitzConstant
    (L M Cjac C₂ C₂lip C₃ C₄ s t : ℝ) : ℝ :=
  let d := t - s
  let F := Real.exp (L * d)
  let E := Real.exp (M * d)
  let Kvar := gronwallBound 0 M (Cjac * F * E) d
  let K₂ := gronwallBound 0 M (C₂ * E * E) d
  let K₃ := flowThirdVariationGrowthConstant M C₂ C₃ s t
  let C₂diff := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t
  let CthirdForce := C₄ * F * E * E * E + 3 * C₃ * Kvar * E * E
  let CsecondForce := C₂lip * F * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar
  let Cforce := Cjac * F * K₃ + CthirdForce + 3 * CsecondForce
  gronwallBound 0 M Cforce d

private theorem exists_flow_thirdVariation_lipschitz_all_times_of_le_D₃diff1 :
  ∀ {b_1 : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b_1) {X : ℝ → Vec (2 : ℕ) →
    ℝ → Vec (2 : ℕ)} (hX : IsFlow b_1 X) (L M Cjac C₃ C₄ : ℝ), (0 : ℝ) ≤ C₃ → (0 : ℝ) ≤ C₄ → (∀
    (t : ℝ) (x h k l : Vec (2 : ℕ)), ‖spatialThirdDerivativeEval b_1 t x h k l‖ ≤ C₃ * ‖h‖ * ‖k‖
    * ‖l‖) → (∀ (t : ℝ) (x y h k l : Vec (2 : ℕ)), ‖spatialThirdDerivativeEval b_1 t x h k l -
    spatialThirdDerivativeEval b_1 t y h k l‖ ≤ C₄ * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖) → ∀ (x y : Vec
    (2 : ℕ)) (s t : ℝ),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  (0 : ℝ) ≤ Kvar →
  let Vx : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX x s);
  let Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX y s);
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E + (3 : ℝ) * C₃ * Kvar * E * E;
  (∀ q ∈ Ico s t, ‖X q y s - X q x s‖ ≤ Ftraj * ‖x - y‖) → (∀ (v : Vec (2 : ℕ)), ∀ q ∈ Ico s t,
    ‖Vx q v s‖ ≤ E * ‖v‖) → (∀ (v : Vec (2 : ℕ)), ∀ q ∈ Ico s t, ‖Vy q v s‖ ≤ E * ‖v‖) → (∀ q ∈
    Ico s t, ∀ (v : Vec (2 : ℕ)), ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖) →
  let field : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ) := b_1;
  ∀ q ∈ Ico s t, ∀ (a b c : Vec (2 : ℕ)), ‖spatialThirdDerivativeEval field q (X q y s) (Vy q a
    s) (Vy q b s) (Vy q c s) - spatialThirdDerivativeEval field q (X q x s) (Vx q a s) (Vx q b
    s) (Vx q c s)‖ ≤ CthirdForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖
    := by
  intro b_1 hb X hX L M Cjac C₃ C₄ hC₃₀ hC₄₀ hC₃ hC₄lip x y s t Kvar hKvarUniform₀ Vx Vy d Ftraj E
      CthirdForce htraj hVxBound hVyBound hVdiff' field q hq a b c
  let Tₓ (u v w : Vec 2) := spatialThirdDerivativeEval field q (X q x s) u v w
  let Tᵧ (u v w : Vec 2) := spatialThirdDerivativeEval field q (X q y s) u v w
  have hfirst : Tₓ (Vy q a s) (Vy q b s) (Vy q c s) -
      Tₓ (Vx q a s) (Vy q b s) (Vy q c s) =
      Tₓ (Vy q a s - Vx q a s) (Vy q b s) (Vy q c s) := by
    dsimp [Tₓ, field]
    have harg : Vy q a s = (Vy q a s - Vx q a s) + Vx q a s := by abel
    rw [harg, spatialThirdDerivativeEval_add_left hb]
    abel_nf
  have hmiddle : Tₓ (Vx q a s) (Vy q b s) (Vy q c s) -
      Tₓ (Vx q a s) (Vx q b s) (Vy q c s) =
      Tₓ (Vx q a s) (Vy q b s - Vx q b s) (Vy q c s) := by
    dsimp [Tₓ, field]
    have harg : Vy q b s = (Vy q b s - Vx q b s) + Vx q b s := by abel
    rw [harg, spatialThirdDerivativeEval_add_middle hb]
    abel_nf
  have hlast : Tₓ (Vx q a s) (Vx q b s) (Vy q c s) -
      Tₓ (Vx q a s) (Vx q b s) (Vx q c s) =
      Tₓ (Vx q a s) (Vx q b s) (Vy q c s - Vx q c s) := by
    dsimp [Tₓ, field]
    have harg : Vy q c s = (Vy q c s - Vx q c s) + Vx q c s := by abel
    rw [harg, spatialThirdDerivativeEval_add_right hb]
    abel_nf
  have hsplit :
      Tᵧ (Vy q a s) (Vy q b s) (Vy q c s) -
          Tₓ (Vx q a s) (Vx q b s) (Vx q c s) =
        (Tᵧ (Vy q a s) (Vy q b s) (Vy q c s) -
            Tₓ (Vy q a s) (Vy q b s) (Vy q c s)) +
          Tₓ (Vy q a s - Vx q a s) (Vy q b s) (Vy q c s) +
          Tₓ (Vx q a s) (Vy q b s - Vx q b s) (Vy q c s) +
          Tₓ (Vx q a s) (Vx q b s) (Vy q c s - Vx q c s) := by
    calc
      _ = (Tᵧ (Vy q a s) (Vy q b s) (Vy q c s) -
            Tₓ (Vy q a s) (Vy q b s) (Vy q c s)) +
          ((Tₓ (Vy q a s) (Vy q b s) (Vy q c s) -
              Tₓ (Vx q a s) (Vy q b s) (Vy q c s)) +
            (Tₓ (Vx q a s) (Vy q b s) (Vy q c s) -
              Tₓ (Vx q a s) (Vx q b s) (Vy q c s)) +
            (Tₓ (Vx q a s) (Vx q b s) (Vy q c s) -
              Tₓ (Vx q a s) (Vx q b s) (Vx q c s))) := by abel
      _ = _ := by rw [hfirst, hmiddle, hlast]; abel
  let P : ℝ := ‖a‖ * ‖b‖ * ‖c‖
  let dx : ℝ := ‖x - y‖
  let term₀ := Tᵧ (Vy q a s) (Vy q b s) (Vy q c s) -
    Tₓ (Vy q a s) (Vy q b s) (Vy q c s)
  let term₁ := Tₓ (Vy q a s - Vx q a s) (Vy q b s) (Vy q c s)
  let term₂ := Tₓ (Vx q a s) (Vy q b s - Vx q b s) (Vy q c s)
  let term₃ := Tₓ (Vx q a s) (Vx q b s) (Vy q c s - Vx q c s)
  have hbase : ‖term₀‖ ≤ (C₄ * Ftraj * E * E * E) * dx * P := by
    dsimp [term₀, Tᵧ, Tₓ, dx, P]
    calc
      _ ≤ C₄ * ‖X q y s - X q x s‖ * ‖Vy q a s‖ *
          ‖Vy q b s‖ * ‖Vy q c s‖ :=
        hC₄lip q (X q y s) (X q x s) (Vy q a s) (Vy q b s) (Vy q c s)
      _ ≤ C₄ * (Ftraj * ‖x - y‖) * (E * ‖a‖) *
          (E * ‖b‖) * (E * ‖c‖) := by
        gcongr
        · exact htraj q hq
        · exact hVyBound a q hq
        · exact hVyBound b q hq
        exact hVyBound c q hq
      _ = (C₄ * Ftraj * E * E * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hdir₁ : ‖term₁‖ ≤ (C₃ * Kvar * E * E) * dx * P := by
    dsimp [term₁, Tₓ, dx, P]
    calc
      _ ≤ C₃ * ‖Vy q a s - Vx q a s‖ * ‖Vy q b s‖ * ‖Vy q c s‖ :=
        hC₃ q (X q x s) _ _ _
      _ ≤ C₃ * (Kvar * ‖x - y‖ * ‖a‖) * (E * ‖b‖) * (E * ‖c‖) := by
        gcongr
        · exact hVdiff' q hq a
        · exact hVyBound b q hq
        exact hVyBound c q hq
      _ = (C₃ * Kvar * E * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hdir₂ : ‖term₂‖ ≤ (C₃ * Kvar * E * E) * dx * P := by
    dsimp [term₂, Tₓ, dx, P]
    calc
      _ ≤ C₃ * ‖Vx q a s‖ * ‖Vy q b s - Vx q b s‖ * ‖Vy q c s‖ :=
        hC₃ q (X q x s) _ _ _
      _ ≤ C₃ * (E * ‖a‖) * (Kvar * ‖x - y‖ * ‖b‖) * (E * ‖c‖) := by
        gcongr
        · exact hVxBound a q hq
        · exact hVdiff' q hq b
        exact hVyBound c q hq
      _ = (C₃ * Kvar * E * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hdir₃ : ‖term₃‖ ≤ (C₃ * Kvar * E * E) * dx * P := by
    dsimp [term₃, Tₓ, dx, P]
    calc
      _ ≤ C₃ * ‖Vx q a s‖ * ‖Vx q b s‖ * ‖Vy q c s - Vx q c s‖ :=
        hC₃ q (X q x s) _ _ _
      _ ≤ C₃ * (E * ‖a‖) * (E * ‖b‖) * (Kvar * ‖x - y‖ * ‖c‖) := by
        gcongr
        · exact hVxBound a q hq
        · exact hVxBound b q hq
        exact hVdiff' q hq c
      _ = (C₃ * Kvar * E * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have h012 : ‖term₀ + term₁ + term₂‖ ≤
      ‖term₀‖ + ‖term₁‖ + ‖term₂‖ := by
    calc
      _ ≤ ‖term₀ + term₁‖ + ‖term₂‖ := norm_add_le _ _
      _ ≤ (‖term₀‖ + ‖term₁‖) + ‖term₂‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖term₀‖ + ‖term₁‖ + ‖term₂‖ := by ring
  have hsum : ‖term₀ + term₁ + term₂ + term₃‖ ≤
      ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := by
    calc
      _ ≤ ‖term₀ + term₁ + term₂‖ + ‖term₃‖ := norm_add_le _ _
      _ ≤ (‖term₀‖ + ‖term₁‖ + ‖term₂‖) + ‖term₃‖ :=
        add_le_add h012 le_rfl
      _ = ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := by ring
  rw [hsplit]
  calc
    _ ≤ ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := hsum
    _ ≤ (C₄ * Ftraj * E * E * E) * dx * P +
        (C₃ * Kvar * E * E) * dx * P +
        (C₃ * Kvar * E * E) * dx * P +
        (C₃ * Kvar * E * E) * dx * P := by
          exact add_le_add (add_le_add (add_le_add hbase hdir₁) hdir₂) hdir₃
    _ = CthirdForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
      dsimp [CthirdForce, dx, P]
      ring

private theorem exists_flow_thirdVariation_lipschitz_all_times_of_le_D₂diff2 :
  ∀ {b_1 : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b_1) {X : ℝ → Vec (2 : ℕ) →
    ℝ → Vec (2 : ℕ)} (hX : IsFlow b_1 X) (L M Cjac C₂ C₂lip : ℝ), (0 : ℝ) ≤ C₂ → (0 : ℝ) ≤ C₂lip
    → (∀ (t : ℝ) (x h k : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval b_1 t x h k‖ ≤ C₂ * ‖h‖ *
    ‖k‖) → (∀ (t : ℝ) (x y h k : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval b_1 t x h k -
    spatialSecondDerivativeEval b_1 t y h k‖ ≤ C₂lip * ‖x - y‖ * ‖h‖ * ‖k‖) → ∀ (x y : Vec (2 :
    ℕ)) (s t : ℝ),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  let Vx : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX x s);
  let Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX y s);
  ∀ (hVx : IsFlow (linearizedFieldAlongFlow b_1 X x s) Vx) (hVy : IsFlow
    (linearizedFieldAlongFlow b_1 X y s) Vy),
  let K₂ : ℝ := gronwallBound (0 : ℝ) M (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s)))
    (t - s);
  (0 : ℝ) ≤ K₂ →
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t;
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar;
  (0 : ℝ) ≤ C₂diff → (∀ q ∈ Ico s t, ‖X q y s - X q x s‖ ≤ Ftraj * ‖x - y‖) → (∀ (v : Vec (2 :
    ℕ)), ∀ q ∈ Ico s t, ‖Vy q v s‖ ≤ E * ‖v‖) → (∀ q ∈ Ico s t, ∀ (v : Vec (2 : ℕ)), ‖Vy q v s -
    Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖) → (∀ q ∈ Icc s t, ∀ (a b : Vec (2 : ℕ)),
    ‖flowSecondVariation hb hX x s hVx a b q (0 : Vec (2 : ℕ)) s‖ ≤ K₂ * ‖a‖ * ‖b‖) → (∀ q ∈ Icc
    s t, ∀ (a b : Vec (2 : ℕ)), ‖flowSecondVariation hb hX y s hVy a b q (0 : Vec (2 : ℕ)) s‖ ≤
    K₂ * ‖a‖ * ‖b‖) → (∀ q ∈ Icc s t, ∀ (a b : Vec (2 : ℕ)), ‖flowSecondVariation hb hX y s hVy
    a b q (0 : Vec (2 : ℕ)) s - flowSecondVariation hb hX x s hVx a b q (0 : Vec (2 : ℕ)) s‖ ≤
    C₂diff * ‖x - y‖ * ‖a‖ * ‖b‖) →
  let field : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ) := b_1;
  ∀ q ∈ Ico s t, ∀ (a b c : Vec (2 : ℕ)), ‖spatialSecondDerivativeEval field q (X q y s)
    (flowSecondVariation hb hX y s hVy a b q (0 : Vec (2 : ℕ)) s) (Vy q c s) -
    spatialSecondDerivativeEval field q (X q x s) (flowSecondVariation hb hX x s hVx a b q (0 :
    Vec (2 : ℕ)) s) (Vx q c s)‖ ≤ CsecondForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖
    := by
  intro b_1 hb X hX L M Cjac C₂ C₂lip hC₂₀ hC₂lip₀ hC₂ hC₂lip x y s t Kvar Vx Vy hVx hVy K₂ hK₂₀
      C₂diff d Ftraj E CsecondForce hC₂diff₀ htraj hVyBound hVdiff' hW₂xBound hW₂yBound hW₂diff
      field q hq a b c
  let Sₓ (u v : Vec 2) := spatialSecondDerivativeEval field q (X q x s) u v
  let Sᵧ (u v : Vec 2) := spatialSecondDerivativeEval field q (X q y s) u v
  let Wₓ := flowSecondVariation hb hX x s hVx a b q 0 s
  let Wᵧ := flowSecondVariation hb hX y s hVy a b q 0 s
  have hleft : Sₓ Wᵧ (Vy q c s) - Sₓ Wₓ (Vy q c s) =
      Sₓ (Wᵧ - Wₓ) (Vy q c s) := by
    have harg : Wᵧ = (Wᵧ - Wₓ) + Wₓ := by abel
    calc
      _ = Sₓ ((Wᵧ - Wₓ) + Wₓ) (Vy q c s) - Sₓ Wₓ (Vy q c s) := by
        exact congrArg (fun z => z - Sₓ Wₓ (Vy q c s))
          (congrArg (fun z => Sₓ z (Vy q c s)) harg)
      _ = Sₓ (Wᵧ - Wₓ) (Vy q c s) := by
        change spatialSecondDerivativeEval field q (X q x s)
            ((Wᵧ - Wₓ) + Wₓ) (Vy q c s) - _ = _
        rw [spatialSecondDerivativeEval_add_left]
        abel
  have hright : Sₓ Wₓ (Vy q c s) - Sₓ Wₓ (Vx q c s) =
      Sₓ Wₓ (Vy q c s - Vx q c s) := by
    have harg : Vy q c s = (Vy q c s - Vx q c s) + Vx q c s := by abel
    calc
      _ = Sₓ Wₓ ((Vy q c s - Vx q c s) + Vx q c s) - Sₓ Wₓ (Vx q c s) := by
        exact congrArg (fun z => z - Sₓ Wₓ (Vx q c s))
          (congrArg (fun z => Sₓ Wₓ z) harg)
      _ = Sₓ Wₓ (Vy q c s - Vx q c s) := by
        change spatialSecondDerivativeEval field q (X q x s) Wₓ
            ((Vy q c s - Vx q c s) + Vx q c s) - _ = _
        rw [spatialSecondDerivativeEval_add_right]
        abel
  have hsplit : Sᵧ Wᵧ (Vy q c s) - Sₓ Wₓ (Vx q c s) =
      (Sᵧ Wᵧ (Vy q c s) - Sₓ Wᵧ (Vy q c s)) +
        Sₓ (Wᵧ - Wₓ) (Vy q c s) + Sₓ Wₓ (Vy q c s - Vx q c s) := by
    calc
      _ = (Sᵧ Wᵧ (Vy q c s) - Sₓ Wᵧ (Vy q c s)) +
          ((Sₓ Wᵧ (Vy q c s) - Sₓ Wₓ (Vy q c s)) +
            (Sₓ Wₓ (Vy q c s) - Sₓ Wₓ (Vx q c s))) := by abel
      _ = _ := by rw [hleft, hright]; abel
  let dx : ℝ := ‖x - y‖
  let P : ℝ := ‖a‖ * ‖b‖ * ‖c‖
  let term₀ := Sᵧ Wᵧ (Vy q c s) - Sₓ Wᵧ (Vy q c s)
  let term₁ := Sₓ (Wᵧ - Wₓ) (Vy q c s)
  let term₂ := Sₓ Wₓ (Vy q c s - Vx q c s)
  have hbase : ‖term₀‖ ≤ (C₂lip * Ftraj * K₂ * E) * dx * P := by
    dsimp [term₀, Sᵧ, Sₓ, Wᵧ, Wₓ, dx, P, field]
    have hqcc : q ∈ Icc s t := ⟨hq.1, le_of_lt hq.2⟩
    calc
      _ ≤ C₂lip * ‖X q y s - X q x s‖ *
          ‖flowSecondVariation hb hX y s hVy a b q 0 s‖ * ‖Vy q c s‖ :=
        hC₂lip q (X q y s) (X q x s)
          (flowSecondVariation hb hX y s hVy a b q 0 s) (Vy q c s)
      _ ≤ C₂lip * (Ftraj * ‖x - y‖) *
          (K₂ * ‖a‖ * ‖b‖) * (E * ‖c‖) := by
        gcongr
        · exact htraj q hq
        · exact hW₂yBound q hqcc a b
        exact hVyBound c q hq
      _ = (C₂lip * Ftraj * K₂ * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hmiddle : ‖term₁‖ ≤ (C₂ * C₂diff * E) * dx * P := by
    dsimp [term₁, Sₓ, Wᵧ, Wₓ, dx, P, field]
    have hqcc : q ∈ Icc s t := ⟨hq.1, le_of_lt hq.2⟩
    calc
      _ ≤ C₂ * ‖flowSecondVariation hb hX y s hVy a b q 0 s -
            flowSecondVariation hb hX x s hVx a b q 0 s‖ * ‖Vy q c s‖ :=
        hC₂ q (X q x s) _ _
      _ ≤ C₂ * (C₂diff * ‖x - y‖ * ‖a‖ * ‖b‖) * (E * ‖c‖) := by
        gcongr
        · exact hW₂diff q hqcc a b
        exact hVyBound c q hq
      _ = (C₂ * C₂diff * E) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hlast : ‖term₂‖ ≤ (C₂ * K₂ * Kvar) * dx * P := by
    dsimp [term₂, Sₓ, Wₓ, dx, P, field]
    have hqcc : q ∈ Icc s t := ⟨hq.1, le_of_lt hq.2⟩
    calc
      _ ≤ C₂ * ‖flowSecondVariation hb hX x s hVx a b q 0 s‖ *
            ‖Vy q c s - Vx q c s‖ := hC₂ q (X q x s) _ _
      _ ≤ C₂ * (K₂ * ‖a‖ * ‖b‖) *
            (Kvar * ‖x - y‖ * ‖c‖) := by
        gcongr
        · exact hW₂xBound q hqcc a b
        exact hVdiff' q hq c
      _ = (C₂ * K₂ * Kvar) * ‖x - y‖ *
          (‖a‖ * ‖b‖ * ‖c‖) := by ring
  have hbase' : ‖term₀‖ ≤
      (C₂lip * Ftraj * K₂ * E) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    simpa [dx, P, mul_assoc] using hbase
  have hmiddle' : ‖term₁‖ ≤
      (C₂ * C₂diff * E) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    simpa [dx, P, mul_assoc] using hmiddle
  have hlast' : ‖term₂‖ ≤
      (C₂ * K₂ * Kvar) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    simpa [dx, P, mul_assoc] using hlast
  have hsum : ‖term₀ + term₁ + term₂‖ ≤ ‖term₀‖ + ‖term₁‖ + ‖term₂‖ := by
    calc
      _ ≤ ‖term₀ + term₁‖ + ‖term₂‖ := norm_add_le _ _
      _ ≤ (‖term₀‖ + ‖term₁‖) + ‖term₂‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖term₀‖ + ‖term₁‖ + ‖term₂‖ := by ring
  rw [hsplit]
  calc
    _ ≤ ‖term₀‖ + ‖term₁‖ + ‖term₂‖ := hsum
    _ ≤ (C₂lip * Ftraj * K₂ * E) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ +
        (C₂ * C₂diff * E) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ +
        (C₂ * K₂ * Kvar) * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
      exact add_le_add (add_le_add hbase' hmiddle') hlast'
    _ = CsecondForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
      dsimp [CsecondForce]
      ring

private theorem exists_flow_thirdVariation_lipschitz_all_times_of_le_Fbound3 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (L M Cjac C₂ C₂lip C₃ C₄ : ℝ) (x y : Vec (2 : ℕ)) (s t : ℝ)
    (h k l : Vec (2 : ℕ)),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  let Vx : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX x s);
  let Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX y s);
  ∀ (hVx : IsFlow (linearizedFieldAlongFlow b X x s) Vx) (hVy : IsFlow (linearizedFieldAlongFlow
    b X y s) Vy),
  let K₂ : ℝ := gronwallBound (0 : ℝ) M (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s)))
    (t - s);
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t;
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E + (3 : ℝ) * C₃ * Kvar * E * E;
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar;
  let field : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ) := b;
  (∀ q ∈ Ico s t, ∀ (a b c : Vec (2 : ℕ)), ‖spatialThirdDerivativeEval field q (X q y s) (Vy q a
    s) (Vy q b s) (Vy q c s) - spatialThirdDerivativeEval field q (X q x s) (Vx q a s) (Vx q b
    s) (Vx q c s)‖ ≤ CthirdForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖) → (∀ q ∈ Ico s t, ∀ (a b_1 c : Vec
    (2 : ℕ)), ‖spatialSecondDerivativeEval field q (X q y s) (flowSecondVariation hb hX y s hVy
    a b_1 q (0 : Vec (2 : ℕ)) s) (Vy q c s) - spatialSecondDerivativeEval field q (X q x s)
    (flowSecondVariation hb hX x s hVx a b_1 q (0 : Vec (2 : ℕ)) s) (Vx q c s)‖ ≤ CsecondForce *
    ‖x - y‖ * ‖a‖ * ‖b_1‖ * ‖c‖) →
  let Fx : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q x s) (Vx q h s)
    (Vx q k s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX
    x s hVx h k q (0 : Vec (2 : ℕ)) s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s)
    (flowSecondVariation hb hX x s hVx h l q (0 : Vec (2 : ℕ)) s) (Vx q k s) +
    spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX x s hVx k l q (0 : Vec
    (2 : ℕ)) s) (Vx q h s);
  let Fy : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q y s) (Vy q h s)
    (Vy q k s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX
    y s hVy h k q (0 : Vec (2 : ℕ)) s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s)
    (flowSecondVariation hb hX y s hVy h l q (0 : Vec (2 : ℕ)) s) (Vy q k s) +
    spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX y s hVy k l q (0 : Vec
    (2 : ℕ)) s) (Vy q h s);
  let Cperturb : ℝ := CthirdForce + (3 : ℝ) * CsecondForce;
  (∀ (q : ℝ), Fy q - Fx q = spatialThirdDerivativeEval b q (X q y s) (Vy q h s) (Vy q k s) (Vy q
    l s) - spatialThirdDerivativeEval b q (X q x s) (Vx q h s) (Vx q k s) (Vx q l s) +
    (spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX y s hVy h k q (0 : Vec
    (2 : ℕ)) s) (Vy q l s) - spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb
    hX x s hVx h k q (0 : Vec (2 : ℕ)) s) (Vx q l s)) + (spatialSecondDerivativeEval b q (X q y
    s) (flowSecondVariation hb hX y s hVy h l q (0 : Vec (2 : ℕ)) s) (Vy q k s) -
    spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX x s hVx h l q (0 : Vec
    (2 : ℕ)) s) (Vx q k s)) + (spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb
    hX y s hVy k l q (0 : Vec (2 : ℕ)) s) (Vy q h s) - spatialSecondDerivativeEval b q (X q x s)
    (flowSecondVariation hb hX x s hVx k l q (0 : Vec (2 : ℕ)) s) (Vx q h s))) → ∀ q ∈ Ico s t,
    ‖Fy q - Fx q‖ ≤ Cperturb * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖
    := by
  intro b hb X hX L M Cjac C₂ C₂lip C₃ C₄ x y s t h k l Kvar Vx Vy hVx hVy K₂ C₂diff d Ftraj E
      CthirdForce CsecondForce field hD₃diff hD₂diff Fx Fy Cperturb hFsplit q hq
  rw [hFsplit q]
  let term₀ := spatialThirdDerivativeEval b q (X q y s)
      (Vy q h s) (Vy q k s) (Vy q l s) -
    spatialThirdDerivativeEval b q (X q x s)
      (Vx q h s) (Vx q k s) (Vx q l s)
  let term₁ := spatialSecondDerivativeEval b q (X q y s)
      (flowSecondVariation hb hX y s hVy h k q 0 s) (Vy q l s) -
    spatialSecondDerivativeEval b q (X q x s)
      (flowSecondVariation hb hX x s hVx h k q 0 s) (Vx q l s)
  let term₂ := spatialSecondDerivativeEval b q (X q y s)
      (flowSecondVariation hb hX y s hVy h l q 0 s) (Vy q k s) -
    spatialSecondDerivativeEval b q (X q x s)
      (flowSecondVariation hb hX x s hVx h l q 0 s) (Vx q k s)
  let term₃ := spatialSecondDerivativeEval b q (X q y s)
      (flowSecondVariation hb hX y s hVy k l q 0 s) (Vy q h s) -
    spatialSecondDerivativeEval b q (X q x s)
      (flowSecondVariation hb hX x s hVx k l q 0 s) (Vx q h s)
  change ‖term₀ + term₁ + term₂ + term₃‖ ≤ _
  have hsum : ‖term₀ + term₁ + term₂ + term₃‖ ≤
      ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := by
    calc
      _ ≤ ‖term₀ + term₁ + term₂‖ + ‖term₃‖ := norm_add_le _ _
      _ ≤ (‖term₀ + term₁‖ + ‖term₂‖) + ‖term₃‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖term₀‖ + ‖term₁‖) + ‖term₂‖) + ‖term₃‖ := by
        apply add_le_add
        · exact add_le_add (norm_add_le _ _) le_rfl
        · exact le_rfl
      _ = ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := by ring
  have hD₃ := hD₃diff q hq h k l
  have hD₂₁ := hD₂diff q hq h k l
  have hD₂₂ := hD₂diff q hq h l k
  have hD₂₃ := hD₂diff q hq k l h
  have hD₂₂' :
      ‖spatialSecondDerivativeEval b q (X q y s)
          (flowSecondVariation hb hX y s hVy h l q 0 s) (Vy q k s) -
        spatialSecondDerivativeEval b q (X q x s)
          (flowSecondVariation hb hX x s hVx h l q 0 s) (Vx q k s)‖ ≤
        CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
    calc
      _ ≤ CsecondForce * ‖x - y‖ * ‖h‖ * ‖l‖ * ‖k‖ := hD₂₂
      _ = CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by ring
  have hD₂₃' :
      ‖spatialSecondDerivativeEval b q (X q y s)
          (flowSecondVariation hb hX y s hVy k l q 0 s) (Vy q h s) -
        spatialSecondDerivativeEval b q (X q x s)
          (flowSecondVariation hb hX x s hVx k l q 0 s) (Vx q h s)‖ ≤
        CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
    calc
      _ ≤ CsecondForce * ‖x - y‖ * ‖k‖ * ‖l‖ * ‖h‖ := hD₂₃
      _ = CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by ring
  calc
    _ ≤ ‖term₀‖ + ‖term₁‖ + ‖term₂‖ + ‖term₃‖ := hsum
    _ ≤ CthirdForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ +
        CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ +
        CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ +
        CsecondForce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
      exact add_le_add (add_le_add (add_le_add hD₃ hD₂₁) hD₂₂') hD₂₃'
    _ = Cperturb * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
      dsimp [Cperturb]
      ring

private theorem exists_flow_thirdVariation_lipschitz_all_times_of_le_Gbound4 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (L M Cjac C₂ C₂lip C₃ C₄ : ℝ), (0 : ℝ) ≤ Cjac → (∀ (t : ℝ) (x
    y : Vec (2 : ℕ)), ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac * ‖x - y‖) →
    ∀ (x y : Vec (2 : ℕ)) (s t : ℝ) (h k l : Vec (2 : ℕ)),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  let Vx : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX x s);
  let Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX y s);
  ∀ (hVx : IsFlow (linearizedFieldAlongFlow b X x s) Vx) (hVy : IsFlow (linearizedFieldAlongFlow
    b X y s) Vy),
  let K₂ : ℝ := gronwallBound (0 : ℝ) M (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s)))
    (t - s);
  let K₃ : ℝ := flowThirdVariationGrowthConstant M C₂ C₃ s t;
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t;
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E + (3 : ℝ) * C₃ * Kvar * E * E;
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar;
  let Cforce : ℝ := Cjac * Ftraj * K₃ + CthirdForce + (3 : ℝ) * CsecondForce;
  let Ax : ℝ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (q : ℝ) => jointSpatialFDeriv b q (X q x s);
  let Ay : ℝ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (q : ℝ) => jointSpatialFDeriv b q (X q y s);
  (∀ q ∈ Ico s t, ‖X q y s - X q x s‖ ≤ Ftraj * ‖x - y‖) →
  let Fx : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q x s) (Vx q h s)
    (Vx q k s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX
    x s hVx h k q (0 : Vec (2 : ℕ)) s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s)
    (flowSecondVariation hb hX x s hVx h l q (0 : Vec (2 : ℕ)) s) (Vx q k s) +
    spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX x s hVx k l q (0 : Vec
    (2 : ℕ)) s) (Vx q h s);
  let Fy : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q y s) (Vy q h s)
    (Vy q k s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX
    y s hVy h k q (0 : Vec (2 : ℕ)) s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s)
    (flowSecondVariation hb hX y s hVy h l q (0 : Vec (2 : ℕ)) s) (Vy q k s) +
    spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX y s hVy k l q (0 : Vec
    (2 : ℕ)) s) (Vy q h s);
  let Cperturb : ℝ := CthirdForce + (3 : ℝ) * CsecondForce;
  (∀ q ∈ Ico s t, ‖Fy q - Fx q‖ ≤ Cperturb * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖) →
  let Wy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := flowThirdVariation hb hX y s hVy h k l;
  (∀ q ∈ Icc s t, ‖Wy q (0 : Vec (2 : ℕ)) s‖ ≤ K₃ * ‖h‖ * ‖k‖ * ‖l‖) →
  let ε : ℝ := Cforce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖;
  let G : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => (Ay q - Ax q) (Wy q (0 : Vec (2 : ℕ)) s) + Fy q - Fx
    q;
  (∀ (q : ℝ), G q = (Ay q) (Wy q (0 : Vec (2 : ℕ)) s) - (Ax q) (Wy q (0 : Vec (2 : ℕ)) s) + (Fy
    q - Fx q)) → ∀ q ∈ Ico s t, ‖G q‖ ≤ ε
    := by
  intro b hb X hX L M Cjac C₂ C₂lip C₃ C₄ hCjac₀ hCjac x y s t h k l Kvar Vx Vy hVx hVy K₂ K₃
      C₂diff d Ftraj E CthirdForce CsecondForce Cforce Ax Ay htraj Fx Fy Cperturb hFbound Wy
      hW₃yBound ε G hGsplit q hq
  have hAxy : ‖Ay q - Ax q‖ ≤ Cjac * Ftraj * ‖x - y‖ := by
    calc
      _ ≤ Cjac * ‖X q y s - X q x s‖ := by
        simpa [Ay, Ax] using hCjac q (X q y s) (X q x s)
      _ ≤ Cjac * (Ftraj * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (htraj q hq) hCjac₀
      _ = Cjac * Ftraj * ‖x - y‖ := by ring
  have hAterm :
      ‖Ay q (Wy q 0 s) - Ax q (Wy q 0 s)‖ ≤
        (Cjac * Ftraj * K₃) * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
    have hW := hW₃yBound q ⟨hq.1, le_of_lt hq.2⟩
    calc
      _ = ‖(Ay q - Ax q) (Wy q 0 s)‖ := by rw [sub_apply]
      _ ≤ ‖Ay q - Ax q‖ * ‖Wy q 0 s‖ := (Ay q - Ax q).le_opNorm _
      _ ≤ (Cjac * Ftraj * ‖x - y‖) *
          (K₃ * ‖h‖ * ‖k‖ * ‖l‖) := by
        gcongr
      _ = (Cjac * Ftraj * K₃) * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by ring
  rw [hGsplit q]
  calc
    _ ≤ ‖Ay q (Wy q 0 s) - Ax q (Wy q 0 s)‖ + ‖Fy q - Fx q‖ :=
      norm_add_le _ _
    _ ≤ (Cjac * Ftraj * K₃) * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ +
        Cperturb * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      add_le_add hAterm (hFbound q hq)
    _ = Cforce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
      dsimp [Cforce, Cperturb, CthirdForce, CsecondForce]
      ring
    _ = ε := by rfl

private theorem exists_flow_thirdVariation_lipschitz_all_times_of_le_Cforce₀5 :
  ∀ (L M Cjac C₂ C₂lip C₃ C₄ : ℝ), (0 : ℝ) ≤ Cjac → (0 : ℝ) ≤ C₂ → (0 : ℝ) ≤ C₂lip → (0 : ℝ) ≤
    C₃ → (0 : ℝ) ≤ C₄ → ∀ (s t : ℝ),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  (0 : ℝ) ≤ Kvar →
  let K₂ : ℝ := gronwallBound (0 : ℝ) M (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s)))
    (t - s);
  (0 : ℝ) ≤ K₂ →
  let K₃ : ℝ := flowThirdVariationGrowthConstant M C₂ C₃ s t;
  (0 : ℝ) ≤ K₃ →
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t;
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E + (3 : ℝ) * C₃ * Kvar * E * E;
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar;
  let Cforce : ℝ := Cjac * Ftraj * K₃ + CthirdForce + (3 : ℝ) * CsecondForce;
  (0 : ℝ) ≤ C₂diff → (0 : ℝ) ≤ Ftraj → (0 : ℝ) ≤ Cforce
    := by
  intro L M Cjac C₂ C₂lip C₃ C₄ hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀ s t Kvar hKvarUniform₀ K₂ hK₂₀ K₃
      hK₃₀ C₂diff d Ftraj E CthirdForce CsecondForce Cforce hC₂diff₀ hFtraj₀
  have hthird₀ : 0 ≤ CthirdForce := by
    dsimp [CthirdForce]
    positivity
  have hsecond₀ : 0 ≤ CsecondForce := by
    dsimp [CsecondForce]
    have h₁ : 0 ≤ C₂lip * Ftraj * K₂ * E := by positivity
    have h₂ : 0 ≤ C₂ * C₂diff * E := by positivity
    have h₃ : 0 ≤ C₂ * K₂ * Kvar := by positivity
    linarith
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hCjac₀ hFtraj₀) hK₃₀) hthird₀)
    (mul_nonneg (by norm_num) hsecond₀)

private theorem third_variation_lipschitz_bound :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
    Vec (2 : ℕ)} (hX : IsFlow b X) (L M Cjac C₂ C₂lip C₃ C₄ : ℝ), (0 : ℝ) ≤ M → (0 : ℝ) ≤ Cjac →
    (∀ (t : ℝ) (x y : Vec (2 : ℕ)), ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac
    * ‖x - y‖) → ∀ (x y : Vec (2 : ℕ)) (s t : ℝ) (h k l : Vec (2 : ℕ)),
  let Kvar : ℝ := gronwallBound (0 : ℝ) M (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t -
    s))) (t - s);
  let Vx : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX x s);
  let Vy : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ) := Classical.choose
    (existsUnique_flow_variationalEquation hb hX y s);
  ∀ (hVx : IsFlow (linearizedFieldAlongFlow b X x s) Vx) (hVy : IsFlow (linearizedFieldAlongFlow
    b X y s) Vy),
  let K₂ : ℝ := gronwallBound (0 : ℝ) M (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s)))
    (t - s);
  ∀ (K₃y : ℝ), (∀ (h k l : Vec (2 : ℕ)), ∀ q ∈ Icc s t, ‖flowThirdVariation hb hX y s hVy h k l
    q (0 : Vec (2 : ℕ)) s‖ ≤ K₃y * ‖h‖ * ‖k‖ * ‖l‖) →
  let K₃ : ℝ := flowThirdVariationGrowthConstant M C₂ C₃ s t;
  K₃y = K₃ →
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t;
  let d : ℝ := t - s;
  let Ftraj : ℝ := Real.exp (L * d);
  let E : ℝ := Real.exp (M * d);
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E + (3 : ℝ) * C₃ * Kvar * E * E;
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E + C₂ * C₂diff * E + C₂ * K₂ * Kvar;
  let Cforce : ℝ := Cjac * Ftraj * K₃ + CthirdForce + (3 : ℝ) * CsecondForce;
  let K : ℝ := gronwallBound (0 : ℝ) M Cforce d;
  (0 : ℝ) ≤ Cforce → (0 : ℝ) ≤ K →
  let Ax : ℝ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (q : ℝ) => jointSpatialFDeriv b q (X q x s);
  let _ : ℝ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (q : ℝ) => jointSpatialFDeriv b q (X q y s);
  (∀ (q : ℝ) (u v : Vec (2 : ℕ)), ‖(Ax q) u - (Ax q) v‖ ≤ M * ‖u - v‖) → (∀ q ∈ Ico s t, ‖X q y
    s - X q x s‖ ≤ Ftraj * ‖x - y‖) →
  let field : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ) := b;
  (∀ q ∈ Ico s t, ∀ (a b c : Vec (2 : ℕ)), ‖spatialThirdDerivativeEval field q (X q y s) (Vy q a
    s) (Vy q b s) (Vy q c s) - spatialThirdDerivativeEval field q (X q x s) (Vx q a s) (Vx q b
    s) (Vx q c s)‖ ≤ CthirdForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖) → (∀ q ∈ Ico s t, ∀ (a b_1 c : Vec
    (2 : ℕ)), ‖spatialSecondDerivativeEval field q (X q y s) (flowSecondVariation hb hX y s hVy
    a b_1 q (0 : Vec (2 : ℕ)) s) (Vy q c s) - spatialSecondDerivativeEval field q (X q x s)
    (flowSecondVariation hb hX x s hVx a b_1 q (0 : Vec (2 : ℕ)) s) (Vx q c s)‖ ≤ CsecondForce *
    ‖x - y‖ * ‖a‖ * ‖b_1‖ * ‖c‖) →
  let Fx : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q x s) (Vx q h s)
    (Vx q k s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX
    x s hVx h k q (0 : Vec (2 : ℕ)) s) (Vx q l s) + spatialSecondDerivativeEval b q (X q x s)
    (flowSecondVariation hb hX x s hVx h l q (0 : Vec (2 : ℕ)) s) (Vx q k s) +
    spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX x s hVx k l q (0 : Vec
    (2 : ℕ)) s) (Vx q h s);
  let Fy : ℝ → Vec (2 : ℕ) := fun (q : ℝ) => spatialThirdDerivativeEval b q (X q y s) (Vy q h s)
    (Vy q k s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX
    y s hVy h k q (0 : Vec (2 : ℕ)) s) (Vy q l s) + spatialSecondDerivativeEval b q (X q y s)
    (flowSecondVariation hb hX y s hVy h l q (0 : Vec (2 : ℕ)) s) (Vy q k s) +
    spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX y s hVy k l q (0 : Vec
    (2 : ℕ)) s) (Vy q h s);
  let _ : ℝ := CthirdForce + (3 : ℝ) * CsecondForce;
  (∀ (q : ℝ), Fy q - Fx q = spatialThirdDerivativeEval b q (X q y s) (Vy q h s) (Vy q k s) (Vy q
    l s) - spatialThirdDerivativeEval b q (X q x s) (Vx q h s) (Vx q k s) (Vx q l s) +
    (spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb hX y s hVy h k q (0 : Vec
    (2 : ℕ)) s) (Vy q l s) - spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb
    hX x s hVx h k q (0 : Vec (2 : ℕ)) s) (Vx q l s)) + (spatialSecondDerivativeEval b q (X q y
    s) (flowSecondVariation hb hX y s hVy h l q (0 : Vec (2 : ℕ)) s) (Vy q k s) -
    spatialSecondDerivativeEval b q (X q x s) (flowSecondVariation hb hX x s hVx h l q (0 : Vec
    (2 : ℕ)) s) (Vx q k s)) + (spatialSecondDerivativeEval b q (X q y s) (flowSecondVariation hb
    hX y s hVy k l q (0 : Vec (2 : ℕ)) s) (Vy q h s) - spatialSecondDerivativeEval b q (X q x s)
    (flowSecondVariation hb hX x s hVx k l q (0 : Vec (2 : ℕ)) s) (Vx q h s))) → ∃ (C : ℝ), (0 :
    ℝ) ≤ C ∧ C = flowThirdVariationLipschitzConstant L M Cjac C₂ C₂lip C₃ C₄ s t ∧ ∀ q ∈ Icc s
    t, ‖flowThirdVariation hb hX y s (Classical.choose_spec
    (existsUnique_flow_variationalEquation hb hX y s)).left h k l q (0 : Vec (2 : ℕ)) s -
    flowThirdVariation hb hX x s (Classical.choose_spec (existsUnique_flow_variationalEquation
    hb hX x s)).left h k l q (0 : Vec (2 : ℕ)) s‖ ≤ C * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖
    := by
  intro b hb X hX L M Cjac C₂ C₂lip C₃ C₄ hM₀ hCjac₀ hCjac x y s t h k l Kvar Vx Vy hVx hVy K₂ K₃y
      hW₃y K₃ hK₃yEq C₂diff d Ftraj E CthirdForce CsecondForce Cforce K hCforce₀ hK₀ Ax Ay hAxLip
      htraj field hD₃diff hD₂diff Fx Fy Cperturb hFsplit
  have hFbound (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Fy q - Fx q‖ ≤ Cperturb * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
    exact @exists_flow_thirdVariation_lipschitz_all_times_of_le_Fbound3 b hb X hX L M Cjac C₂
        C₂lip C₃ C₄ x y s t h k l hVx hVy hD₃diff hD₂diff hFsplit q hq
  let Wx : ℝ → Vec 2 → ℝ → Vec 2 :=
    flowThirdVariation hb hX x s hVx h k l
  let Wy : ℝ → Vec 2 → ℝ → Vec 2 :=
    flowThirdVariation hb hX y s hVy h k l
  have hW₃yBound (q : ℝ) (hq : q ∈ Icc s t) :
      ‖Wy q 0 s‖ ≤ K₃ * ‖h‖ * ‖k‖ * ‖l‖ := by
    simpa only [hK₃yEq, Wy] using hW₃y h k l q hq
  let ε : ℝ := Cforce * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖
  let G : ℝ → Vec 2 := fun q =>
    (Ay q - Ax q) (Wy q 0 s) + Fy q - Fx q
  have hGsplit (q : ℝ) : G q =
      (Ay q (Wy q 0 s) - Ax q (Wy q 0 s)) + (Fy q - Fx q) := by
    dsimp [G]
    rw [sub_apply]
    abel
  have hGbound (q : ℝ) (hq : q ∈ Ico s t) : ‖G q‖ ≤ ε := by
    exact @exists_flow_thirdVariation_lipschitz_all_times_of_le_Gbound4 b hb X hX L M Cjac C₂
        C₂lip C₃ C₄ hCjac₀ hCjac x y s t h k l hVx hVy htraj hFbound hW₃yBound hGsplit q hq
  have hWx := flowThirdVariation_isFlow hb hX x s hVx h k l
  have hWy := flowThirdVariation_isFlow hb hX y s hVy h k l
  let f : ℝ → Vec 2 := fun q => Wx q 0 s
  let g : ℝ → Vec 2 := fun q => Wy q 0 s
  have hfderiv (q : ℝ) : HasDerivAt f (Ax q (f q) + Fx q) q := by
    simpa [f, Wx, Fx, Ax, add_assoc] using hWx.2 0 s q
  have hgderiv (q : ℝ) : HasDerivAt g (Ax q (g q) + Fx q + G q) q := by
    have hraw : HasDerivAt g (Ay q (g q) + Fy q) q := by
      simpa [g, Wy, Fy, Ay, add_assoc] using hWy.2 0 s q
    convert hraw using 1
    dsimp [G]
    rw [sub_apply]
    abel
  have hfcont : ContinuousOn f (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hfderiv q)
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hgderiv q)
  have hfwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt f (Ax q (f q) + Fx q) (Ici q) q :=
    fun q _ => (hfderiv q).hasDerivWithinAt
  have hgwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt g (Ax q (g q) + Fx q + G q) (Ici q) q :=
    fun q _ => (hgderiv q).hasDerivWithinAt
  have hfapprox : ∀ q ∈ Ico s t,
      dist (Ax q (f q) + Fx q) (Ax q (f q) + Fx q) ≤ (0 : ℝ) := by
    intro q hq
    simp
  have hgapprox : ∀ q ∈ Ico s t,
      dist (Ax q (g q) + Fx q + G q) (Ax q (g q) + Fx q) ≤ ε := by
    intro q hq
    rw [dist_eq_norm]
    have hsub : (Ax q (g q) + Fx q + G q) - (Ax q (g q) + Fx q) = G q := by
      abel
    rw [hsub]
    exact hGbound q hq
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hAlip : ∀ q, LipschitzWith KN (fun z => Ax q z + Fx q) := by
    intro q
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (Ax q u + Fx q) - (Ax q v + Fx q) = Ax q u - Ax q v := by
      abel
    rw [hsub]
    exact hAxLip q u v
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, Wx, Wy, hWx.1, hWy.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (K := KN) (v := fun q z => Ax q z + Fx q) (f := f) (g := g)
    (f' := fun q => Ax q (f q) + Fx q)
    (g' := fun q => Ax q (g q) + Fx q + G q)
    (a := s) (b := t) (εf := 0) (εg := ε) (δ := 0)
    hAlip hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hKcast : (KN : ℝ) = M := rfl
  let P : ℝ := ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖
  have hscale : gronwallBound 0 M ε (t - s) = P * K := by
    rw [show ε = P * Cforce by dsimp [ε, P]; ring]
    rw [ThirdVariationContinuity.gronwallBound_zero_scale_third_cont M Cforce P (t - s)]
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hdist (q : ℝ) (hq : q ∈ Icc s t) :
      ‖g q - f q‖ ≤ gronwallBound 0 M ε (q - s) := by
    have h := hcomp q hq
    simpa [dist_eq_norm, norm_sub_rev, hKcast] using h
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
  have htime (q : ℝ) (hq : q ∈ Icc s t) : q - s ≤ t - s := by
    rcases hq with ⟨_, hqt⟩
    linarith
  have hpoint (q : ℝ) (hq : q ∈ Icc s t) :
      ‖g q - f q‖ ≤ P * K := by
    calc
      _ ≤ gronwallBound 0 M ε (q - s) := hdist q hq
      _ = P * gronwallBound 0 M Cforce (q - s) := by
        rw [show ε = P * Cforce by dsimp [ε, P]; ring]
        rw [ThirdVariationContinuity.gronwallBound_zero_scale_third_cont M Cforce P (q - s)]
      _ ≤ P * K := by
        apply mul_le_mul_of_nonneg_left _ hP₀
        dsimp [K]
        exact hmono (htime q hq)
  refine ⟨K, hK₀, ?_, ?_⟩
  · dsimp [K, flowThirdVariationLipschitzConstant, Cforce, CthirdForce,
      CsecondForce, Ftraj, E, d, Kvar, K₂, K₃, C₂diff]
    try rfl
  intro q hq
  have hpointq := hpoint q hq
  change ‖flowThirdVariation hb hX y s hVy h k l q 0 s -
      flowThirdVariation hb hX x s hVx h k l q 0 s‖ ≤ _
  simpa [f, g, Wx, Wy, P, mul_assoc, mul_left_comm, mul_comm] using hpointq

/-- The third variational flow is Lipschitz in its initial point, uniformly
over a forward compact target-time interval and all three directions. -/
theorem exists_flow_thirdVariation_lipschitz_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (L M Cjac C₂ C₂lip C₃ C₄ : ℝ)
    (hL₀ : 0 ≤ L) (hM₀ : 0 ≤ M) (hCjac₀ : 0 ≤ Cjac)
    (hC₂₀ : 0 ≤ C₂) (hC₂lip₀ : 0 ≤ C₂lip) (hC₃₀ : 0 ≤ C₃)
    (hC₄₀ : 0 ≤ C₄)
    (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (hM : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (hCjac : ∀ t x y,
      ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ Cjac * ‖x - y‖)
    (hC₂ : ∀ t x h k,
      ‖spatialSecondDerivativeEval b t x h k‖ ≤ C₂ * ‖h‖ * ‖k‖)
    (hC₂lip : ∀ t x y h k,
      ‖spatialSecondDerivativeEval b t x h k - spatialSecondDerivativeEval b t y h k‖ ≤
        C₂lip * ‖x - y‖ * ‖h‖ * ‖k‖)
    (hC₃ : ∀ t x h k l,
      ‖spatialThirdDerivativeEval b t x h k l‖ ≤ C₃ * ‖h‖ * ‖k‖ * ‖l‖)
    (hC₄lip : ∀ t x y h k l,
      ‖spatialThirdDerivativeEval b t x h k l - spatialThirdDerivativeEval b t y h k l‖ ≤
        C₄ * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖)
    (x y : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ∀ h k l, ∃ C : ℝ, 0 ≤ C ∧ C = flowThirdVariationLipschitzConstant
      L M Cjac C₂ C₂lip C₃ C₄ s t ∧ ∀ q, q ∈ Icc s t →
      ‖flowThirdVariation hb hX y s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
          h k l q 0 s -
        flowThirdVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
          h k l q 0 s‖ ≤ C * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
  intro h k l
  obtain ⟨Vx₀, hVx₀, Vy₀, hVy₀, Kvar₀, hKvar₀, hKvarFormula, hVdiff⟩ :=
    exists_flow_variational_difference_bound_all_times_of_le
      hb hX L M Cjac hL₀ hM₀ hCjac₀ hL hM hCjac x y s t hst
  let Kvar : ℝ := gronwallBound 0 M
    (Cjac * Real.exp (L * (t - s)) * Real.exp (M * (t - s))) (t - s)
  have hKvarEq : Kvar₀ = Kvar := by simpa [Kvar] using hKvarFormula
  have hKvarUniform₀ : 0 ≤ Kvar := by rw [← hKvarEq]; exact hKvar₀
  let Vx : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  let Vy : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX y s)
  have hVx : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  have hVy : AVenhance.IsFlow (linearizedFieldAlongFlow b X y s) Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s)).1
  have hVxEq : Vx₀ = Vx :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2 Vx₀ hVx₀
  have hVyEq : Vy₀ = Vy :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s)).2 Vy₀ hVy₀
  have hVdiffCanon (q : ℝ) (hq : q ∈ Icc s t) (v : Vec 2) :
      ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖ := by
    simpa only [hVyEq, hVxEq, hKvarEq] using hVdiff q hq v
  obtain ⟨K₂x, hK₂x₀, hK₂xFormula, hW₂x⟩ :=
    flowSecondVariation_bound_all_times_of_le hb hX M C₂ hM₀ hM hC₂₀ hC₂
      x s t hst hVx
  obtain ⟨K₂y, hK₂y₀, hK₂yFormula, hW₂y⟩ :=
    flowSecondVariation_bound_all_times_of_le hb hX M C₂ hM₀ hM hC₂₀ hC₂
      y s t hst hVy
  let K₂ : ℝ := gronwallBound 0 M
    (C₂ * Real.exp (M * (t - s)) * Real.exp (M * (t - s))) (t - s)
  have hK₂xEq : K₂x = K₂ := by simpa [K₂] using hK₂xFormula
  have hK₂yEq : K₂y = K₂ := by simpa [K₂] using hK₂yFormula
  have hK₂₀ : 0 ≤ K₂ := by rw [← hK₂xEq]; exact hK₂x₀
  obtain ⟨K₃y, hK₃y₀, hK₃Eq, hW₃y⟩ :=
    flowThirdVariation_bound_all_times_of_le hb hX y s t hst hVy
      M C₂ C₃ hM₀ hM hC₂₀ hC₂ hC₃₀ hC₃
  let K₃ : ℝ := flowThirdVariationGrowthConstant M C₂ C₃ s t
  have hK₃yEq : K₃y = K₃ := by simpa [K₃] using hK₃Eq
  have hK₃₀ : 0 ≤ K₃ := by rw [← hK₃yEq]; exact hK₃y₀
  let C₂diff : ℝ := flowSecondVariationLipschitzConstant L M Cjac C₂ C₂lip s t
  let d : ℝ := t - s
  let Ftraj : ℝ := Real.exp (L * d)
  let E : ℝ := Real.exp (M * d)
  let CthirdForce : ℝ := C₄ * Ftraj * E * E * E +
    3 * C₃ * Kvar * E * E
  let CsecondForce : ℝ := C₂lip * Ftraj * K₂ * E +
    C₂ * C₂diff * E + C₂ * K₂ * Kvar
  let Cforce : ℝ := Cjac * Ftraj * K₃ + CthirdForce + 3 * CsecondForce
  have hC₂diff₀ : 0 ≤ C₂diff := by
    obtain ⟨C, hC₀, hCeq, _⟩ :=
      exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₂lip hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀
        hL hM hCjac hC₂ hC₂lip 0 0 s t hst 0 0
    dsimp [C₂diff]
    rw [← hCeq]
    exact hC₀
  let K : ℝ := gronwallBound 0 M Cforce d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hFtraj₀ : 0 ≤ Ftraj := (Real.exp_pos _).le
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hCforce₀ : 0 ≤ Cforce := by
    exact @exists_flow_thirdVariation_lipschitz_all_times_of_le_Cforce₀5 L M Cjac C₂ C₂lip C₃ C₄
        hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀ s t hKvarUniform₀ hK₂₀ hK₃₀ hC₂diff₀ hFtraj₀
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
    simpa [K, gronwallBound_x0] using hmono hd₀
  let Ax : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  let Ay : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q y s)
  have hAxLip : ∀ q u v, ‖Ax q u - Ax q v‖ ≤ M * ‖u - v‖ := by
    intro q u v
    calc
      ‖Ax q u - Ax q v‖ = ‖Ax q (u - v)‖ := by rw [map_sub]
      _ ≤ ‖Ax q‖ * ‖u - v‖ := (Ax q).le_opNorm _
      _ ≤ M * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (hM q (X q x s)) (norm_nonneg _)
  have htraj (q : ℝ) (hq : q ∈ Ico s t) :
      ‖X q y s - X q x s‖ ≤ Ftraj * ‖x - y‖ := by
    have hgr := flow_spatial_gronwall_of_le b hL hX y x s q hq.1
    have hexp : Real.exp (L * (q - s)) ≤ Ftraj := by
      apply Real.exp_le_exp.mpr
      dsimp [Ftraj, d]
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2]) hL₀
    calc
      ‖X q y s - X q x s‖ ≤ Real.exp (L * (q - s)) * ‖y - x‖ := hgr
      _ = Real.exp (L * (q - s)) * ‖x - y‖ := by rw [norm_sub_rev]
      _ ≤ Ftraj * ‖x - y‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hVxBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vx q v s‖ ≤ E * ‖v‖ := by
    have h := ThirdVariationContinuity.thirdCont_linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r x s)) M hM₀
      (fun r => hM r (X r x s)) hVx s t hst v q hq
    simpa [E, d] using h
  have hVyBound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖Vy q v s‖ ≤ E * ‖v‖ := by
    have h := ThirdVariationContinuity.thirdCont_linearFlow_norm_bound_on_Ico
      (fun r => jointSpatialFDeriv b r (X r y s)) M hM₀
      (fun r => hM r (X r y s)) hVy s t hst v q hq
    simpa [E, d] using h
  have hVdiff' (q : ℝ) (hq : q ∈ Ico s t) (v : Vec 2) :
      ‖Vy q v s - Vx q v s‖ ≤ Kvar * ‖x - y‖ * ‖v‖ :=
    hVdiffCanon q ⟨hq.1, le_of_lt hq.2⟩ v
  have hW₂xBound (q : ℝ) (hq : q ∈ Icc s t) (a b : Vec 2) :
      ‖flowSecondVariation hb hX x s hVx a b q 0 s‖ ≤ K₂ * ‖a‖ * ‖b‖ := by
    simpa only [hK₂xEq] using hW₂x q hq a b
  have hW₂yBound (q : ℝ) (hq : q ∈ Icc s t) (a b : Vec 2) :
      ‖flowSecondVariation hb hX y s hVy a b q 0 s‖ ≤ K₂ * ‖a‖ * ‖b‖ := by
    simpa only [hK₂yEq] using hW₂y q hq a b
  have hW₂diff (q : ℝ) (hq : q ∈ Icc s t) (a b : Vec 2) :
      ‖flowSecondVariation hb hX y s hVy a b q 0 s -
        flowSecondVariation hb hX x s hVx a b q 0 s‖ ≤
          C₂diff * ‖x - y‖ * ‖a‖ * ‖b‖ := by
    obtain ⟨Cxy, _, hCxyEq, hpoint⟩ :=
      exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₂lip hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀
        hL hM hCjac hC₂ hC₂lip x y s t hst a b
    have h := hpoint q hq
    rw [hCxyEq] at h
    simpa [C₂diff] using h
  let field : ℝ → Vec 2 → Vec 2 := b
  have hD₃diff (q : ℝ) (hq : q ∈ Ico s t) (a b c : Vec 2) :
      ‖spatialThirdDerivativeEval field q (X q y s)
          (Vy q a s) (Vy q b s) (Vy q c s) -
        spatialThirdDerivativeEval field q (X q x s)
          (Vx q a s) (Vx q b s) (Vx q c s)‖ ≤
        CthirdForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    exact @exists_flow_thirdVariation_lipschitz_all_times_of_le_D₃diff1 _ hb X hX L M Cjac C₃ C₄
        hC₃₀ hC₄₀ hC₃ hC₄lip x y s t hKvarUniform₀ htraj hVxBound hVyBound hVdiff' q hq a b c
  have hD₂diff (q : ℝ) (hq : q ∈ Ico s t) (a b c : Vec 2) :
      ‖spatialSecondDerivativeEval field q (X q y s)
          (flowSecondVariation hb hX y s hVy a b q 0 s) (Vy q c s) -
        spatialSecondDerivativeEval field q (X q x s)
          (flowSecondVariation hb hX x s hVx a b q 0 s) (Vx q c s)‖ ≤
        CsecondForce * ‖x - y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    exact @exists_flow_thirdVariation_lipschitz_all_times_of_le_D₂diff2 _ hb X hX L M Cjac C₂
        C₂lip hC₂₀ hC₂lip₀ hC₂ hC₂lip x y s t hVx hVy hK₂₀ hC₂diff₀ htraj hVyBound hVdiff'
        hW₂xBound hW₂yBound hW₂diff q hq a b c
  let Wx : ℝ → Vec 2 → ℝ → Vec 2 :=
    flowThirdVariation hb hX x s hVx h k l
  let Wy : ℝ → Vec 2 → ℝ → Vec 2 :=
    flowThirdVariation hb hX y s hVy h k l
  have hWx := flowThirdVariation_isFlow hb hX x s hVx h k l
  have hWy := flowThirdVariation_isFlow hb hX y s hVy h k l
  let Fx : ℝ → Vec 2 := fun q =>
    spatialThirdDerivativeEval b q (X q x s)
        (Vx q h s) (Vx q k s) (Vx q l s) +
      spatialSecondDerivativeEval b q (X q x s)
        (flowSecondVariation hb hX x s hVx h k q 0 s) (Vx q l s) +
      spatialSecondDerivativeEval b q (X q x s)
        (flowSecondVariation hb hX x s hVx h l q 0 s) (Vx q k s) +
      spatialSecondDerivativeEval b q (X q x s)
        (flowSecondVariation hb hX x s hVx k l q 0 s) (Vx q h s)
  let Fy : ℝ → Vec 2 := fun q =>
    spatialThirdDerivativeEval b q (X q y s)
        (Vy q h s) (Vy q k s) (Vy q l s) +
      spatialSecondDerivativeEval b q (X q y s)
        (flowSecondVariation hb hX y s hVy h k q 0 s) (Vy q l s) +
      spatialSecondDerivativeEval b q (X q y s)
        (flowSecondVariation hb hX y s hVy h l q 0 s) (Vy q k s) +
      spatialSecondDerivativeEval b q (X q y s)
        (flowSecondVariation hb hX y s hVy k l q 0 s) (Vy q h s)
  let Cperturb : ℝ := CthirdForce + 3 * CsecondForce
  have hFsplit (q : ℝ) : Fy q - Fx q =
      (spatialThirdDerivativeEval b q (X q y s)
          (Vy q h s) (Vy q k s) (Vy q l s) -
        spatialThirdDerivativeEval b q (X q x s)
          (Vx q h s) (Vx q k s) (Vx q l s)) +
      (spatialSecondDerivativeEval b q (X q y s)
          (flowSecondVariation hb hX y s hVy h k q 0 s) (Vy q l s) -
        spatialSecondDerivativeEval b q (X q x s)
          (flowSecondVariation hb hX x s hVx h k q 0 s) (Vx q l s)) +
      (spatialSecondDerivativeEval b q (X q y s)
          (flowSecondVariation hb hX y s hVy h l q 0 s) (Vy q k s) -
        spatialSecondDerivativeEval b q (X q x s)
          (flowSecondVariation hb hX x s hVx h l q 0 s) (Vx q k s)) +
      (spatialSecondDerivativeEval b q (X q y s)
          (flowSecondVariation hb hX y s hVy k l q 0 s) (Vy q h s) -
        spatialSecondDerivativeEval b q (X q x s)
          (flowSecondVariation hb hX x s hVx k l q 0 s) (Vx q h s)) := by
    dsimp [Fx, Fy]
    abel
  exact @third_variation_lipschitz_bound b hb X hX L M Cjac C₂ C₂lip C₃ C₄ hM₀ hCjac₀ hCjac x y s
      t h k l hVx hVy K₃y hW₃y hK₃yEq hCforce₀ hK₀ hAxLip htraj hD₃diff hD₂diff hFsplit
/-- On a forward compact target-time interval, a fixed third spatial
variation is jointly continuous in target time and initial point. -/
theorem flow_thirdVariation_jointContinuous_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      flowThirdVariation hb hX p.2 s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX p.2 s) |>.1)
        h k l p.1 0 s) (Icc s t ×ˢ univ) := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₂lip, hC₂lip₀, hC₂lip⟩ :=
    exists_global_spatialSecondDerivativeEval_lipschitz hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialThirdDerivativeEval_bound hb
  obtain ⟨C₄, hC₄₀, hC₄lip⟩ :=
    exists_global_spatialThirdDerivativeEval_lipschitz hb
  let Csp := flowThirdVariationLipschitzConstant L M Cjac C₂ C₂lip C₃ C₄ s t
  have hCsp₀ : 0 ≤ Csp := by
    obtain ⟨C, hC₀, hCeq, _⟩ := exists_flow_thirdVariation_lipschitz_all_times_of_le
      hb hX L M Cjac C₂ C₂lip C₃ C₄
      hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀
      hL hM hCjac hC₂ hC₂lip hC₃ hC₄lip 0 0 s t hst h k l
    dsimp [Csp]
    rw [← hCeq]
    exact hC₀
  let Kdir : ℝ≥0 := ⟨Csp * ‖h‖ * ‖k‖ * ‖l‖,
    mul_nonneg (mul_nonneg (mul_nonneg hCsp₀ (norm_nonneg h))
      (norm_nonneg k)) (norm_nonneg l)⟩
  let f : Vec 2 × ℝ → Vec 2 := fun p =>
    flowThirdVariation hb hX p.1 s
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX p.1 s) |>.1)
      h k l p.2 0 s
  have htime (x : Vec 2) : ContinuousOn (fun q => f (x, q)) (Icc s t) := by
    let V : ℝ → Vec 2 → ℝ → Vec 2 :=
      Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
    have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
    let W : ℝ → Vec 2 → ℝ → Vec 2 :=
      flowThirdVariation hb hX x s hV h k l
    have hW := flowThirdVariation_isFlow hb hX x s hV h k l
    have hident (q : ℝ) : f (x, q) = W q 0 s := by rfl
    have hWcont : ContinuousOn (fun q => W q 0 s) (Icc s t) :=
      HasDerivAt.continuousOn (fun q _ => hW.2 0 s q)
    exact hWcont.congr (fun q _ => hident q)
  have hspace (q : ℝ) (hq : q ∈ Icc s t) :
      LipschitzOnWith Kdir (fun x => f (x, q)) univ := by
    have hLip : LipschitzWith Kdir (fun x => f (x, q)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      obtain ⟨Cxy, _, hCxyEq, hbound⟩ :=
        exists_flow_thirdVariation_lipschitz_all_times_of_le
          hb hX L M Cjac C₂ C₂lip C₃ C₄
          hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀
          hL hM hCjac hC₂ hC₂lip hC₃ hC₄lip x y s t hst h k l
      have hpoint := hbound q hq
      rw [hCxyEq] at hpoint
      have hdirbound :
          ‖f (x, q) - f (y, q)‖ ≤ Csp * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
        calc
          _ = ‖f (y, q) - f (x, q)‖ := norm_sub_rev _ _
          _ ≤ Csp * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
            simpa [f] using hpoint
      calc
        ‖f (x, q) - f (y, q)‖ ≤
            Csp * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := hdirbound
        _ = (Kdir : ℝ) * dist x y := by
          rw [dist_eq_norm]
          change Csp * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ =
            (Csp * ‖h‖ * ‖k‖ * ‖l‖) * ‖x - y‖
          ring
    exact hLip.lipschitzOnWith
  let g : ℝ × Vec 2 → Vec 2 := fun p => f (p.2, p.1)
  have hprod : ContinuousOn g (Icc s t ×ˢ univ) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' g Kdir hspace
      (fun x _ => by simpa [g] using htime x)
  simpa [g, f] using hprod

end AVenhance.Infra.Flow
