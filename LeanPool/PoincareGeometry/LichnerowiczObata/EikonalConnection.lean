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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRadial

/-! # Covariant acceleration of an eikonal gradient

The connection is the constructed Levi–Civita connection. This pointwise
statement does not assert global existence or minimizing properties of curves.
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

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- A locally constant gradient norm forces zero covariant acceleration
in the gradient direction. -/
theorem cov_gradient_self_eq_zero {f : M → ℝ} {x : M} {c : ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hn : ∀ᶠ y in 𝓝 x, ‖gradient (I := I) f y‖ = c) :
    LC (gradient (I := I) f) x (gradient (I := I) f x) = 0 := by
  have he : (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y))
      =ᶠ[𝓝 x] (fun _ => c ^ 2) := by
    filter_upwards [hn] with y hy
    rw [real_inner_self_eq_norm_sq, hy]
  have hd : mvfderiv I
      (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y)) x = 0 := by
    unfold mvfderiv
    rw [he.mfderiv_eq, mfderiv_const]
    ext v
    rfl
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left]
  have hn' := differential_gradient_norm_sq_at hf v
  rw [hd, zero_apply] at hn'
  have hs := hessian_symmetric_at LC leviCivitaConnection_metricCompatible
    (congrFun leviCivitaConnection_torsion x) hf v (gradient (I := I) f x)
  rw [hs] at hn'
  change 0 = 2 * inner ℝ (LC (gradient (I := I) f) x (gradient (I := I) f x)) v at hn'
  linarith

/-- The radial candidate has the same finite regularity as the Obata function
at every level strictly between its extrema. -/
theorem contMDiffAt_obataRadial {n : ℕ∞ω} {K a : ℝ} {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) n f x)
    (hm : f x / a ≠ -1) (hp : f x / a ≠ 1) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (obataRadial K a f) x := by
  have hg : ContDiffAt ℝ n (fun t : ℝ => Real.arccos (t / a) / Real.sqrt K) (f x) :=
    ((Real.contDiffAt_arccos hm hp).comp (f x) (contDiffAt_id.div_const a)).div_const _
  exact hg.comp_contMDiffAt hf

/-- Under the proved energy profile, the radial gradient has zero covariant
acceleration throughout the open region between the extrema. -/
theorem cov_obataRadial_gradient_self_eq_zero {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {x : M} (hx : -a < f x ∧ f x < a) :
    LC (gradient (I := I) (obataRadial K a f)) x
      (gradient (I := I) (obataRadial K a f) x) = 0 := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  apply cov_gradient_self_eq_zero
    (contMDiffAt_obataRadial (hf x) (ne_of_gt hm) (ne_of_lt hp))
  have hnear : ∀ᶠ y in 𝓝 x, -a < f y ∧ f y < a :=
    hf.continuous.continuousAt (Ioo_mem_nhds hx.1 hx.2)
  filter_upwards [hnear] with y hy
  exact norm_gradient_obataRadial hK ha ((hf y).mdifferentiableAt (by norm_num)) hy (hn y)

/-- The actual Obata equation supplies an autoparallel radial gradient on
the region between the two extremal levels. -/
theorem exists_obata_radial_autoparallel
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ x, -a < f x ∧ f x < a →
        ‖gradient (I := I) (obataRadial K a f) x‖ = 1 ∧
        LC (gradient (I := I) (obataRadial K a f)) x
          (gradient (I := I) (obataRadial K a f) x) = 0) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, hb, ?_⟩
  intro x hx
  exact ⟨norm_gradient_obataRadial hK hp ((hf x).mdifferentiableAt (by norm_num)) hx (hn x),
    cov_obataRadial_gradient_self_eq_zero hK hp hf hn hx⟩

end LichnerowiczObata
