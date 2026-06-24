/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Analysis.Complex.Schwarz
import LeanPool.RiemannMappingTheorem.Defs
import LeanPool.RiemannMappingTheorem.ToMathlib

/-!
# LeanPool.RiemannMappingTheorem.Etape2
-/

open Complex ComplexConjugate Set Metric Topology Filter

variable {z u z₀ : ℂ} (U : Set ℂ) [good_domain U]

lemma one_sub_mul_conj_ne_zero (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) : 1 - z * conj u ≠ 0 := by
  rw [mem_𝔻_iff] at hu hz
  refine sub_ne_zero.mpr (mt (congr_arg (‖·‖ : ℂ → _)) (ne_comm.mp (ne_of_lt ?_)))
  simpa using mul_lt_mul'' hz hu (norm_nonneg z) (norm_nonneg u)

lemma one_sub_mul_conj_add_mul_conj_ne_zero (hu : u ∈ 𝔻) :
    1 - z * conj u + (z - u) * conj u ≠ 0 := by
  have h1 := one_sub_mul_conj_ne_zero hu hu
  ring_nf
  simp [h1, mul_comm]

lemma normSq_sub_normSq :
    normSq (z - u) - normSq (1 - z * conj u) = (normSq z - 1) * (1 - normSq u) := by
  simp [← ofReal_inj, normSq_eq_conj_mul_self]
  ring

/-- The Möbius transformation `preΦ u z = (z - u) / (1 - z·ū)` underlying
the disk automorphism `φ`. Maps `𝔻` to itself when `u ∈ 𝔻`. -/
noncomputable def preΦ (u z : ℂ) : ℂ := (z - u) / (1 - z * conj u)

lemma pre_φ_inv (hu : u ∈ 𝔻) : LeftInvOn (preΦ (-u)) (preΦ u) 𝔻 := by
  rintro z hz
  have := one_sub_mul_conj_ne_zero hu hz
  have := one_sub_mul_conj_add_mul_conj_ne_zero (z := z) hu
  simp [field, preΦ]
  ring

/-- The disk automorphism `φ u : 𝔻 → 𝔻` packaged as an `embedding`.
Equals `preΦ u` and sends `u ↦ 0`. -/
noncomputable def φ (hu : u ∈ 𝔻) : embedding 𝔻 𝔻 :=
{
  toFun := fun z => (z - u) / (1 - z * conj u),
  is_diff := (differentiableOn_id.sub (differentiableOn_const u)).div
    ((differentiableOn_const 1).sub (differentiableOn_id.mul (differentiableOn_const _)))
    (fun _ => one_sub_mul_conj_ne_zero hu),
  is_inj := (pre_φ_inv hu).injOn,
  maps_to := by
    rintro z hz
    simp only [mem_𝔻_iff, norm_div]
    refine (div_lt_iff₀ (norm_pos_iff.mpr (one_sub_mul_conj_ne_zero hu hz))).mpr ?_
    rw [one_mul]
    apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, ← sub_lt_zero, normSq_sub_normSq,
      normSq_eq_norm_sq, normSq_eq_norm_sq]
    apply mul_neg_of_neg_of_pos
    · simpa using mem_𝔻_iff.mp hz
    · simpa using mem_𝔻_iff.mp hu
}

lemma φ_deriv (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) :
    deriv (φ hu) z = (1 - u * conj u) / ((1 - z * conj u) ^ 2) := by
  have h3 : 1 - z * conj u ≠ 0 := one_sub_mul_conj_ne_zero hu hz
  simp [φ, h3]
  field_simp
  ring

lemma φ_inv (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) : φ (neg_in_𝔻 hu) (φ hu z) = z :=
  pre_φ_inv hu hz

lemma non_injective_schwarz {f : ℂ → ℂ} (f_diff : DifferentiableOn ℂ f 𝔻)
    (f_img : MapsTo f 𝔻 𝔻) (f_noninj : ¬ InjOn f 𝔻) : ‖deriv f 0‖ < 1 := by
  set u := f 0
  have u_in_𝔻 : u ∈ 𝔻 := f_img (mem_ball_self zero_lt_one)
  let g := φ u_in_𝔻 ∘ f
  have g_diff : DifferentiableOn ℂ g 𝔻 := (φ u_in_𝔻).is_diff.comp f_diff f_img
  have g_maps : MapsTo g 𝔻 𝔻 := (φ u_in_𝔻).maps_to.comp f_img
  have g_0_eq_0 : g 0 = 0 := by simp [g, φ, u]
  by_cases h : ‖deriv g 0‖ = 1
  case pos =>
    have h2 : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
      rw [g_0_eq_0]
      exact g_maps.mono_right ball_subset_closedBall
    have hdiv : ‖dslope g 0 0‖ = 1 / 1 := by
      rwa [dslope_same, div_one]
    have h1 : Set.EqOn g (fun z => g 0 + (z - 0) • dslope g 0 0) (Metric.ball 0 1) :=
      affine_of_mapsTo_ball_of_norm_dslope_eq_div g_diff h2 (mem_ball_self zero_lt_one) hdiv
    have g_lin : EqOn g (fun (z : ℂ) => z • deriv g 0) (ball 0 1) := by
      convert h1 using 1
      ext1 z
      rw [g_0_eq_0, zero_add, sub_zero, dslope_same]
    have g'0_ne_0 : deriv g 0 ≠ 0 := fun h' => by simp [h'] at h
    have g_inj : InjOn g 𝔻 := fun x hx y hy => by
      rw [g_lin hx, g_lin hy]
      simp [g'0_ne_0]
    exact absurd g_inj (mt InjOn.of_comp f_noninj)
  case neg =>
    have g_maps_cl : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
      rw [g_0_eq_0]
      exact g_maps.mono_right ball_subset_closedBall
    have g'0_lt_1 : ‖deriv g 0‖ < 1 :=
      Ne.lt_of_le h (norm_deriv_le_one_of_mapsTo_ball g_diff g_maps_cl zero_lt_one)
    have g'0_eq_mul : deriv g 0 = deriv (φ u_in_𝔻) u * deriv f 0 :=
      deriv_comp 0 ((φ u_in_𝔻).is_diff.differentiableAt (isOpen_ball.mem_nhds u_in_𝔻))
        (f_diff.differentiableAt (ball_mem_nhds _ zero_lt_one))
    have e1 : 1 - (normSq u : ℂ) ≠ 0 := by
      simpa [normSq_eq_conj_mul_self, mul_comm] using one_sub_mul_conj_ne_zero u_in_𝔻 u_in_𝔻
    have φ'u_u : deriv (φ u_in_𝔻) u = 1 / (1 - normSq u) := by
      set w := 1 - conj u * u with hw
      have : w ≠ 0 := by simpa [normSq_eq_conj_mul_self, mul_comm u] using e1
      rw [φ_deriv u_in_𝔻 u_in_𝔻, normSq_eq_conj_mul_self, mul_comm u, ← hw]
      field_simp
    have e3 : normSq u < 1 := by
      rw [normSq_eq_norm_sq]
      simp only [sq_lt_one_iff_abs_lt_one, abs_norm, mem_𝔻_iff.mp u_in_𝔻]
    simp only [φ'u_u, one_div] at g'0_eq_mul
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ e1] at g'0_eq_mul
    rw [g'0_eq_mul, norm_mul, mul_comm, ← one_mul (1 : ℝ)]
    refine mul_lt_mul g'0_lt_1 ?_ (norm_pos_iff.mpr e1) zero_le_one
    norm_cast
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    refine ⟨by linarith [normSq_nonneg u], by linarith⟩

lemma step_2 (hz₀ : z₀ ∈ U) (f : embedding U 𝔻) (hf : f '' U ⊂ 𝔻) :
    ∃ h : embedding U 𝔻, ‖deriv f z₀‖ < ‖deriv h z₀‖ := by
  obtain ⟨u, u_in_𝔻, u_not_in_f_U⟩ := exists_of_ssubset hf
  let φᵤ : embedding 𝔻 𝔻 := φ u_in_𝔻
  let φᵤf : embedding U 𝔻 := φᵤ.comp f
  have φᵤf_ne_zero : ∀ z ∈ U, φᵤf z ≠ 0 := fun z z_in_U hz => by
    refine u_not_in_f_U ⟨z, z_in_U, ?_⟩
    apply φᵤ.is_inj (f.maps_to z_in_U) u_in_𝔻
    dsimp [φᵤf] at hz
    rw [hz]
    simp [φᵤ, φ]
  obtain ⟨g, hg⟩ := φᵤf.sqrt' φᵤf_ne_zero
  let v : ℂ := g z₀
  have v_in_𝔻 : v ∈ 𝔻 := g.maps_to hz₀
  let h : embedding U 𝔻 := (φ v_in_𝔻).comp g
  have h_z₀_eq_0 : h z₀ = 0 := by simp [h, φ, v]
  let σ : ℂ → ℂ := fun z => z ^ 2
  let ψ : ℂ → ℂ := φ (neg_in_𝔻 u_in_𝔻) ∘ σ ∘ φ (neg_in_𝔻 v_in_𝔻)
  have f_eq_ψ_h : EqOn f (ψ ∘ h) U := fun z hz => by
    have e1 := φ_inv v_in_𝔻 (g.maps_to hz)
    have e2 := hg hz
    have e3 := φ_inv u_in_𝔻 (f.maps_to hz)
    dsimp [φᵤf] at e2
    simp [ψ, σ, h, e1, ← e2, e3, φᵤ]
  have ψ_is_diff : DifferentiableOn ℂ ψ 𝔻 := by
    refine (φ (neg_in_𝔻 u_in_𝔻)).is_diff.comp ?_ ?_
    · exact ((differentiable_id.differentiableOn.pow 2).comp (φ (neg_in_𝔻 v_in_𝔻)).is_diff
        (φ (neg_in_𝔻 v_in_𝔻)).maps_to)
    · exact fun z hz => by simpa [σ, 𝔻] using (φ (neg_in_𝔻 v_in_𝔻)).maps_to hz
  have deriv_eq_mul : deriv f z₀ = deriv ψ 0 * deriv h z₀ := by
    rw [(eventuallyEq_of_mem (good_domain.is_open.mem_nhds hz₀) f_eq_ψ_h).deriv_eq,
      ← h_z₀_eq_0]
    exact deriv_comp z₀ (h_z₀_eq_0 ▸ ψ_is_diff.differentiableAt (ball_mem_nhds _ zero_lt_one))
      (h.is_diff.differentiableAt (good_domain.is_open.mem_nhds hz₀))
  rw [deriv_eq_mul, norm_mul]
  refine ⟨h, mul_lt_of_lt_one_left ?_ ?_⟩
  · exact norm_pos_iff.2 (embedding.deriv_ne_zero good_domain.is_open hz₀)
  · apply non_injective_schwarz ψ_is_diff
    · refine fun z hz => (φ (neg_in_𝔻 u_in_𝔻)).maps_to (mem_𝔻_iff.mpr ?_)
      simpa [σ] using mem_𝔻_iff.mp ((φ (neg_in_𝔻 v_in_𝔻)).maps_to hz)
    · simp only [InjOn, not_forall, exists_prop]
      have e1 : (2⁻¹ : ℂ) ∈ 𝔻 := mem_𝔻_iff.mpr (by norm_num)
      have e2 : (-2⁻¹ : ℂ) ∈ 𝔻 := neg_in_𝔻 e1
      refine ⟨φ v_in_𝔻 2⁻¹, (φ v_in_𝔻).maps_to e1, φ v_in_𝔻 (-2⁻¹),
        (φ v_in_𝔻).maps_to e2, ?_, fun h => ?_⟩
      · simp [ψ, σ, φ_inv v_in_𝔻 e1, φ_inv v_in_𝔻 e2]
      · have hinj := (φ v_in_𝔻).is_inj e1 e2 h
        norm_num at hinj
