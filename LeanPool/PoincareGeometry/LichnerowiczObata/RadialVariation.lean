/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialProduct

/-! # Tangent variations of the constructed radial family -/

@[expose] public noncomputable section
open Set Filter AlmostSchur Bundle
open scoped Topology Manifold ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Differentiating a constant-level map gives actual vectors orthogonal
to the level gradient. No orthogonality of the variations is assumed. -/
theorem inner_gradient_mfderiv_eq_zero {ρ : M → ℝ} {ψ : M → M} {x : M} {c : ℝ}
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (ψ x))
    (hψ : MDifferentiableAt I I ψ x)
    (he : (ρ ∘ ψ) =ᶠ[𝓝 x] (fun _ => c)) (v : TangentSpace I x) :
    inner ℝ (gradient (I := I) ρ (ψ x)) (mfderiv I I ψ x v) = 0 := by
  rw [inner_gradient]
  change mfderiv I 𝓘(ℝ, ℝ) ρ (ψ x) (mfderiv I I ψ x v) = 0
  have hd := mfderiv_comp x hρ hψ
  have hz : mfderiv I 𝓘(ℝ, ℝ) (ρ ∘ ψ) x = 0 := by
    rw [he.mfderiv_eq, mfderiv_const]
  have hv := congrArg (fun L => L v) (hd.symm.trans hz)
  exact hv

/-- Initial-point derivatives of a smooth radial family are angular
vectors, because the attained radial coordinate is independent of that
initial point. -/
theorem radial_variation_orthogonal {U : Set M} {J : Set ℝ} {ρ : M → ℝ}
    {η : M × ℝ → M} (hU : IsOpen U) (hJ : IsOpen J)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η (U ×ˢ J))
    (hlevel : ∀ y ∈ U, ∀ r ∈ J, ρ (η (y, r)) = r)
    {x : M} (hx : x ∈ U) {r : ℝ} (hr : r ∈ J)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (η (x, r))) (v : TangentSpace I x) :
    inner ℝ (gradient (I := I) ρ (η (x, r)))
      (mfderiv I I (fun y => η (y, r)) x v) = 0 := by
  have hs := hη.contMDiffAt (prod_mem_nhds (hU.mem_nhds hx) (hJ.mem_nhds hr))
  have hψ : ContMDiffAt I I 1 (fun y => η (y, r)) x :=
    hs.comp x (contMDiffAt_id.prodMk contMDiffAt_const)
  apply inner_gradient_mfderiv_eq_zero (c := r) hρ (hψ.mdifferentiableAt (by norm_num)) _ v
  exact eventually_of_mem (hU.mem_nhds hx) (fun y hy => hlevel y hy r hr)

/-- The actual Obata radial family has angular initial-point variations
at every regular starting point and every interior radial time. -/
theorem obata_radial_variation_orthogonal {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a) {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({y | -a < f y ∧ f y < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hlevel : ∀ y, -a < f y ∧ f y < a → ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      obataRadial K a f (η (y, r)) = r)
    {x : M} (hx : -a < f x ∧ f x < a) {r : ℝ}
    (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) (v : TangentSpace I x) :
    inner ℝ (gradient (I := I) (obataRadial K a f) (η (x, r)))
      (mfderiv I I (fun y => η (y, r)) x v) = 0 := by
  have he := obataRadial_cos hK ha (η (x, r)) (hb (η (x, r)))
  rw [hlevel x hx r hr] at he
  have hreg : -a < f (η (x, r)) ∧ f (η (x, r)) < a := by
    rw [← he]
    exact obata_cos_level_mem hK ha hr
  have hm : -1 < f (η (x, r)) / a := (lt_div_iff₀ ha).mpr (by nlinarith [hreg.1])
  have hp : f (η (x, r)) / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hreg.2)
  have hg : ContDiffAt ℝ 1 (fun t : ℝ => Real.arccos (t / a) / Real.sqrt K)
      (f (η (x, r))) :=
    ((Real.contDiffAt_arccos hm.ne' hp.ne).comp (f (η (x, r)))
      (contDiffAt_id.div_const a)).div_const _
  have hρ := (hg.comp_contMDiffAt (hf (η (x, r)))).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hU : IsOpen {y : M | -a < f y ∧ f y < a} :=
    (isOpen_lt continuous_const hf.continuous).inter (isOpen_lt hf.continuous continuous_const)
  exact radial_variation_orthogonal hU isOpen_Ioo hη hlevel hx hr hρ v

/-- Differentiating the reset identity gives the composition law for
actual tangent transport between radial levels. -/
theorem mfderiv_radial_reset {U : Set M} {J : Set ℝ} {η : M × ℝ → M}
    (hU : IsOpen U) (hJ : IsOpen J)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η (U ×ˢ J))
    (hmem : ∀ y ∈ U, ∀ r ∈ J, η (y, r) ∈ U)
    (hreset : ∀ y ∈ U, ∀ r ∈ J, ∀ s ∈ J, η (η (y, r), s) = η (y, s))
    {x : M} (hx : x ∈ U) {r s : ℝ} (hr : r ∈ J) (hs : s ∈ J) :
    (mfderiv I I (fun y => η (y, s)) (η (x, r))).comp
      (mfderiv I I (fun y => η (y, r)) x) = mfderiv I I (fun y => η (y, s)) x := by
  have hslice (y : M) (hy : y ∈ U) (t : ℝ) (ht : t ∈ J) :
      MDifferentiableAt I I (fun z => η (z, t)) y := by
    have hj := hη.contMDiffAt (prod_mem_nhds (hU.mem_nhds hy) (hJ.mem_nhds ht))
    exact (hj.comp y (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by norm_num)
  have he : ((fun y => η (y, s)) ∘ (fun y => η (y, r))) =ᶠ[𝓝 x] (fun y => η (y, s)) :=
    eventually_of_mem (hU.mem_nhds hx) (fun y hy => hreset y hy r hr s hs)
  exact (mfderiv_comp x (hslice _ (hmem x hx r hr) s hs) (hslice x hx r hr)).symm.trans
    he.mfderiv_eq

/-- At the starting radial level, the spatial variation and the time
variation sum to the original tangent vector. This follows by differentiating
the actual identity `η(y, ρ(y)) = y`. -/
theorem radial_initial_derivative {ρ : M → ℝ} {η : M × ℝ → M} {x : M}
    (hη : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I η (x, ρ x))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hinit : (fun y => η (y, ρ y)) =ᶠ[𝓝 x] id) (v : TangentSpace I x) :
    mfderiv I I (fun y => η (y, ρ x)) x v +
      mfderiv 𝓘(ℝ, ℝ) I (fun t => η (x, t)) (ρ x) (mfderiv I 𝓘(ℝ, ℝ) ρ x v) = v := by
  have hd := mfderiv_comp x hη (mdifferentiableAt_id.prodMk hρ)
  have he : mfderiv I I (fun y => η (y, ρ y)) x = ContinuousLinearMap.id ℝ _ := by
    rw [hinit.mfderiv_eq, mfderiv_id]
  change mfderiv I I (fun y => η (y, ρ y)) x = _ at hd
  simp only [id_eq] at hd
  erw [mfderiv_prod_eq_add_comp hη, mfderiv_prodMk mdifferentiableAt_id hρ,
    mfderiv_id] at hd
  rw [he] at hd
  have hv := congrArg (fun L => L v) hd.symm
  convert hv using 1 <;> rfl

/-- Transport back to the initial radial level fixes every angular vector. -/
theorem radial_initial_derivative_of_tangent {ρ : M → ℝ} {η : M × ℝ → M} {x : M}
    (hη : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I η (x, ρ x))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hinit : (fun y => η (y, ρ y)) =ᶠ[𝓝 x] id) (v : TangentSpace I x)
    (hv : mfderiv I 𝓘(ℝ, ℝ) ρ x v = 0) :
    mfderiv I I (fun y => η (y, ρ x)) x v = v := by
  have hd := radial_initial_derivative hη hρ hinit v
  simpa only [hv, map_zero, add_zero] using hd

/-- Radial transport cannot kill a nonzero angular vector. Its left inverse
is the derivative of transport back to the starting level. -/
theorem radial_transport_kernel_trivial {U : Set M} {J : Set ℝ} {ρ : M → ℝ}
    {η : M × ℝ → M} (hU : IsOpen U) (hJ : IsOpen J)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η (U ×ˢ J))
    (hmem : ∀ y ∈ U, ∀ r ∈ J, η (y, r) ∈ U)
    (hreset : ∀ y ∈ U, ∀ r ∈ J, ∀ s ∈ J, η (η (y, r), s) = η (y, s))
    (hinit : ∀ y ∈ U, η (y, ρ y) = y)
    {x : M} (hx : x ∈ U) (hρx : ρ x ∈ J)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x) {r : ℝ} (hr : r ∈ J)
    (v : TangentSpace I x) (hv : mfderiv I 𝓘(ℝ, ℝ) ρ x v = 0)
    (hz : mfderiv I I (fun y => η (y, r)) x v = 0) : v = 0 := by
  have hc := mfderiv_radial_reset hU hJ hη hmem hreset hx hr hρx
  have hd := congrArg (fun L => L v) hc
  have hj := (hη.contMDiffAt (prod_mem_nhds (hU.mem_nhds hx) (hJ.mem_nhds hρx))).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hi := radial_initial_derivative_of_tangent hj hρ
    (eventually_of_mem (hU.mem_nhds hx) (fun y hy => hinit y hy)) v hv
  have he : mfderiv I I (fun y => η (y, ρ x)) (η (x, r))
      (mfderiv I I (fun y => η (y, r)) x v) = v := by
    exact hd.trans hi
  simpa only [hz, map_zero] using he.symm

end LichnerowiczObata
