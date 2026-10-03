/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GlobalGradientCurves

/-! # Regularity and unique level crossings of gradient curves

Global ODE uniqueness excludes finite-time arrival at a critical point.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [T2Space M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- A global gradient curve starting at a regular point stays regular at
every finite time. -/
theorem gradient_ne_zero_along_curve {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (gradient (I := I) f))
    (h0 : gradient (I := I) f (γ 0) ≠ 0) (t : ℝ) :
    gradient (I := I) f (γ t) ≠ 0 := by
  intro hz
  have hconst : IsMIntegralCurve (fun _ : ℝ => γ t) (gradient (I := I) f) := by
    intro s
    simp only [hz, ContinuousLinearMap.smulRight_zero]
    convert (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) (c := γ t) (x := s)) using 1 <;> rfl
  let : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (contMDiff_gradient 1 hf) hγ hconst (t₀ := t) rfl
  have he0 := congrFun he 0
  exact h0 (he0 ▸ hz)

/-- The function value is strictly increasing alongAlmostSchur every regular complete
gradient curve. -/
theorem strictMono_gradient_curve {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (gradient (I := I) f))
    (h0 : gradient (I := I) f (γ 0) ≠ 0) : StrictMono (f ∘ γ) := by
  apply strictMono_of_deriv_pos
  intro t
  have hd := hasDerivAt_comp_integralCurve
    ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hγ.isMIntegralCurveAt t)
  rw [hd.deriv, ← inner_gradient, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (gradient_ne_zero_along_curve hf hγ h0 t))

/-- Every intermediate level has a unique crossing time on each regular
Obata gradient curve constructed from compactness. -/
theorem exists_obata_unique_level_curves [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ x : M, -a < f x ∧ f x < a → ∃ γ : ℝ → M,
        γ 0 = x ∧ IsMIntegralCurve γ (gradient (I := I) f) ∧
        StrictMono (f ∘ γ) ∧
        (∀ b : ℝ, -a < b ∧ b < a → ∃! t : ℝ, f (γ t) = b) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, hb, ?_⟩
  intro x hx
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_gradient_curve hf x
  have h0 : gradient (I := I) f (γ 0) ≠ 0 := by
    rw [hγ0]
    intro hz
    have he := hn x
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hs : 0 < f p ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
    have := mul_pos hK hs
    linarith
  have hm := strictMono_gradient_curve hf hγ h0
  refine ⟨γ, hγ0, hγ, hm, ?_⟩
  intro b hba
  have hd : ∀ t, HasDerivAt (f ∘ γ) (K * (f p ^ 2 - f (γ t) ^ 2)) t := by
    intro t
    have hd := hasDerivAt_comp_integralCurve
      ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hγ.isMIntegralCurveAt t)
    rw [← inner_gradient, real_inner_self_eq_norm_sq, hn] at hd
    exact hd
  obtain ⟨t, ht⟩ := exists_time_obata_scalar hK hp (fun t => hb (γ t)) hd
    (by simpa only [Function.comp_apply, hγ0] using hx) hba
  exact ⟨t, ht, fun s hs => hm.injective (hs.trans ht.symm)⟩

end LichnerowiczObata
