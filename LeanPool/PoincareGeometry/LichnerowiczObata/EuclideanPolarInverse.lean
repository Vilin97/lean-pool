/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarInverseDifferentiability
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-! # Differentiable Euclidean polar coordinates off the origin -/

@[expose] public noncomputable section
open Set TopologicalSpace
open scoped Manifold Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem fderiv_euclideanPolar_apply (u w : P) (r s : ℝ) :
    fderiv ℝ (fun q : P × ℝ => q.2 • q.1) (u, r) (w, s) = r • w + s • u := by
  have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, r))).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, r)))
  have he := congrArg (fun D : P × ℝ →L[ℝ] P => D (w, s)) hd.fderiv
  convert he using 1 <;> rfl

theorem euclideanPolar_metric (u : Metric.sphere (0 : P) 1)
    (w v : P) (hw : inner ℝ (u : P) w = 0) (hv : inner ℝ (u : P) v = 0)
    (r s t : ℝ) :
    inner ℝ (fderiv ℝ (fun q : P × ℝ => q.2 • q.1) (u, r) (w, s))
      (fderiv ℝ (fun q : P × ℝ => q.2 • q.1) (u, r) (v, t)) =
      r ^ 2 * inner ℝ w v + s * t := by
  rw [fderiv_euclideanPolar_apply, fderiv_euclideanPolar_apply]
  have hwu : inner ℝ w (u : P) = 0 := by rw [real_inner_comm, hw]
  have huu : inner ℝ (u : P) (u : P) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere u]
    norm_num
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hv, hwu, huu]
  ring

variable {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]

theorem euclideanPolar_derivative_injOn (u : Metric.sphere (0 : P) 1)
    {r : ℝ} (hr : 0 < r) :
    Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P)
      (fun q : P × ℝ => q.2 • q.1) ((u : P), r))
      {q : P × ℝ | inner ℝ (u : P) q.1 = 0} := by
  rw [mfderiv_eq_fderiv]
  change Set.InjOn (fderiv ℝ (fun q : P × ℝ => q.2 • q.1) ((u : P), r))
    {q : P × ℝ | inner ℝ (u : P) q.1 = 0}
  apply polar_derivative_injOn _ (sq_pos_of_pos hr)
  intro v hv t
  exact euclideanPolar_metric u v v hv hv r t t

/-- A single differentiable inverse covers all nonzero Euclidean points,
and agrees there with the usual normalized-vector and norm coordinates. -/
theorem exists_euclidean_polar_inverse (u₀ : Metric.sphere (0 : P) 1) :
    ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : P) 1 × ℝ) P,
      e.source = {q | 0 < q.2} ∧ e.target = ({0}ᶜ : Set P) ∧
      (∀ q ∈ e.source, e q = q.2 • (q.1 : P)) ∧
      (∀ x : ({0}ᶜ : Set P), e.symm (x : P) =
        ((homeomorphUnitSphereProd P x).1, ((homeomorphUnitSphereProd P x).2 : ℝ))) ∧
      ∀ x ≠ 0, MDifferentiableAt 𝓘(ℝ, P) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x := by
  let : FiniteDimensional ℝ P := .of_fact_finrank_eq_succ n
  obtain ⟨e, hs, ht, he, hi, hd⟩ := exists_differentiable_polar_inverse_on_target
    (I := 𝓘(ℝ, P)) (n := n) ⟨Ioi 0, isOpen_Ioi⟩
    ⟨({0}ᶜ : Set P), isOpen_compl_singleton⟩
    (homeomorphUnitSphereProd P).symm (u₀, ⟨1, by change (0 : ℝ) < 1; norm_num⟩)
    (fun q : P × ℝ => q.2 • q.1) (fun _ => rfl) Fact.out
    (by
      intro u r hr
      refine ⟨?_, euclideanPolar_derivative_injOn u hr⟩
      apply mdifferentiableAt_iff_differentiableAt.mpr
      fun_prop)
  exact ⟨e, hs, ht, he, hi, fun x hx => hd x (by simpa using hx)⟩

end LichnerowiczObata
