/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Barriers.Construction

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron barrier pairs for the Laplace operator

For a bounded open set `C` with a uniform exterior sphere condition and boundary
data `g` that is `L`-Lipschitz on `closure C` for the Euclidean distance, we
assemble a `DirichletBarrierPair` for `-Δu = 0`:

* the upper barrier is `U_g = inf_{p ∈ P} (g x₀ + A Φ_p)`;
* the lower barrier is `-U_{-g}`, using that the Laplace operator equals its
  own `negOperator`.

Both barriers are continuous, attain the boundary data, and satisfy the
Hölder-`1/2` boundary modulus `|B(x) - g(x₀)| ≤ K |x - x₀|^{1/2}` with a constant
`K` depending only on `n`, `R`, `L` and the diameter of `C`. When the frontier
is empty we use the constant barriers `0`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace ViscositySolns

variable {n : Nat}

/-- Constants are viscosity supersolutions of `-Δu = 0` on open sets. -/
theorem viscositySupersolution_laplaceOperator_const {C : Set (Point n)} (hCopen : IsOpen C)
    (a : Real) : ViscositySupersolution C laplaceOperator (fun _ => a) := by
  refine ⟨continuousOn_const.lowerSemicontinuousOn, fun x hx J hJ => ?_⟩
  have hK : (⟨0, 0⟩ : Jet n) ∈ Superjet C (fun _ => a) x :=
    ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _,
      Eventually.of_forall fun y => by simp [quadraticModel]⟩
  have hxint : x ∈ interior C := mem_interior_iff_mem_nhds.2 (hCopen.mem_nhds hx)
  have h := trace_hessian_le_of_mem_subjet_of_mem_superjet hxint hJ hK
  rw [laplaceOperator_apply]
  simp only [Matrix.trace_zero] at h
  linarith

/-- Constants are viscosity subsolutions of `-Δu = 0` on open sets. -/
theorem viscositySubsolution_laplaceOperator_const {C : Set (Point n)} (hCopen : IsOpen C)
    (a : Real) : ViscositySubsolution C laplaceOperator (fun _ => a) := by
  have h := viscositySupersolution_neg_iff.mp
    (viscositySupersolution_laplaceOperator_const hCopen (-a))
  rw [negOperator_laplaceOperator] at h
  simpa using h

/-- A function that is `L`-Lipschitz for the Euclidean distance is continuous. -/
theorem continuousOn_of_abs_sub_le_mul_sqrt_eucSq {S : Set (Point n)}
    {g : Point n -> Real} {L : Real}
    (hg : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| <= L * Real.sqrt (eucSq x y)) :
    ContinuousOn g S := by
  intro x hx
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  have hc : Continuous fun y : Point n => L * Real.sqrt (eucSq y x) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_eucSq.comp (continuous_id.prodMk continuous_const)))
  have hlim := hc.tendsto x
  rw [eucSq_self, Real.sqrt_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.norm_eq_abs]
  exact hg y hy x hx

/-- Bounded sets have bounded squared Euclidean diameter. -/
theorem exists_eucSq_le_of_isBounded {C : Set (Point n)} (hC : Bornology.IsBounded C) :
    ∃ D : Real, ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D := by
  obtain ⟨M, hM⟩ := hC.closure.exists_norm_le
  refine ⟨n * (2 * |M|) ^ 2, fun x hx y hy => ?_⟩
  have h1 : ‖x - y‖ <= 2 * |M| :=
    (norm_sub_le x y).trans (by linarith [hM x hx, hM y hy, le_abs_self M])
  calc
    eucSq x y <= n * ‖x - y‖ ^ 2 := eucSq_le_card_mul_norm_sq x y
    _ <= n * (2 * |M|) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (Nat.cast_nonneg n)

theorem upperEnvelope_eq_of_continuous {C : Set (Point n)} {u : Point n -> Real}
    (hu : Continuous u) {x : Point n} (hx : x ∈ closure C) :
    upperEnvelope C u x = u x := by
  have : (𝓝[C] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact ((hu.tendsto x).mono_left nhdsWithin_le_nhds).limsup_eq

theorem lowerEnvelope_eq_of_continuous {C : Set (Point n)} {u : Point n -> Real}
    (hu : Continuous u) {x : Point n} (hx : x ∈ closure C) :
    lowerEnvelope C u x = u x := by
  have : (𝓝[C] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact ((hu.tendsto x).mono_left nhdsWithin_le_nhds).liminf_eq

section Assembly

variable {C : Set (Point n)} {R D L : Real}

/-- The coefficient `A = L / √c` of the barrier branches. -/
def laplaceBarrierCoeff (n : Nat) (R D L : Real) : Real :=
  L / Real.sqrt (laplaceBarrierLowerConst n R D)

/-- The Hölder-`1/2` modulus constant `K = A √(α (√D + R))`. -/
def laplaceBarrierModulus (n : Nat) (R D L : Real) : Real :=
  laplaceBarrierCoeff n R D L * Real.sqrt (laplaceBarrierRate n R * (Real.sqrt D + R))

theorem laplaceBarrierCoeff_nonneg (hL : 0 <= L) : 0 <= laplaceBarrierCoeff n R D L := by
  unfold laplaceBarrierCoeff
  positivity

theorem laplaceBarrierModulus_nonneg (hL : 0 <= L) : 0 <= laplaceBarrierModulus n R D L := by
  unfold laplaceBarrierModulus
  have := laplaceBarrierCoeff_nonneg (n := n) (R := R) (D := D) hL
  positivity

/-- Each branch dominates the Lipschitz growth `L |x - x₀|` on `closure C`. -/
theorem mul_sqrt_eucSq_le_coeff_mul_profile (hR : 0 < R)
    (hD : ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D) (hL : 0 <= L)
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) {x : Point n}
    (hx : x ∈ closure C) :
    L * Real.sqrt (eucSq x p.1) <=
      laplaceBarrierCoeff n R D L * laplaceBarrierProfile (laplaceBarrierRate n R) R p x := by
  have hc := Real.sqrt_pos.2 (laplaceBarrierLowerConst_pos (n := n) hR D)
  have hAc : laplaceBarrierCoeff n R D L * Real.sqrt (laplaceBarrierLowerConst n R D) = L :=
    div_mul_cancel₀ L hc.ne'
  have h := mul_le_mul_of_nonneg_left (sqrt_lowerConst_mul_le_laplaceBarrierProfile hR hD hp hx)
    (laplaceBarrierCoeff_nonneg (n := n) (R := R) (D := D) hL)
  rw [← mul_assoc, hAc] at h
  exact h

/-- The properties of the upper barrier `U_h` for Lipschitz boundary data `h`. -/
theorem laplaceUpperBarrier_properties (hCopen : IsOpen C) (hCbdd : Bornology.IsBounded C)
    (hext : UniformExteriorSphereSq C R)
    (hD : ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D) (hL : 0 <= L)
    {x₀ : Point n} (hx₀ : x₀ ∈ frontier C) {h : Point n -> Real}
    (hh : ∀ x ∈ closure C, ∀ y ∈ closure C, |h x - h y| <= L * Real.sqrt (eucSq x y)) :
    Continuous (laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) h) ∧
      ViscositySupersolution C laplaceOperator
        (laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) h) ∧
      (∀ z ∈ frontier C, laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) h z = h z) ∧
      ∀ z ∈ frontier C, ∀ x ∈ closure C,
        laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) h x <=
          h z + laplaceBarrierModulus n R D L * Real.sqrt (Real.sqrt (eucSq x z)) := by
  have hR := hext.1
  have hhc : ContinuousOn h (closure C) := continuousOn_of_abs_sub_le_mul_sqrt_eucSq hh
  have hA := laplaceBarrierCoeff_nonneg (n := n) (R := R) (D := D) hL
  refine ⟨continuous_laplaceUpperBarrier hCbdd hhc,
    viscositySupersolution_laplaceUpperBarrier hCopen hCbdd hext hA hhc hx₀, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := nonempty_exteriorSphereParams hext hz
    refine le_antisymm ?_ ?_
    · have h1 := laplaceUpperBarrier_le (A := laplaceBarrierCoeff n R D L) hCbdd hhc hy z
      have h2 : laplaceBarrierProfile (laplaceBarrierRate n R) R (z, y) z = 0 :=
        laplaceBarrierProfile_self hy
      simpa [laplaceBarrierBranch, h2] using h1
    · refine le_laplaceUpperBarrier hz hext z fun p hp => ?_
      have hzC : z ∈ closure C := frontier_subset_closure hz
      have h1 := mul_sqrt_eucSq_le_coeff_mul_profile hR hD hL hp hzC
      have h2 := hh z hzC p.1 (frontier_subset_closure hp.1)
      have h3 := le_abs_self (h z - h p.1)
      unfold laplaceBarrierBranch
      linarith
  · intro z hz x hx
    obtain ⟨y, hy⟩ := nonempty_exteriorSphereParams hext hz
    have h1 := laplaceUpperBarrier_le (A := laplaceBarrierCoeff n R D L) hCbdd hhc hy x
    have h2 := mul_le_mul_of_nonneg_left (laplaceBarrierProfile_le hR hD hy hx) hA
    unfold laplaceBarrierBranch at h1
    unfold laplaceBarrierModulus
    rw [← mul_assoc] at h2
    exact h1.trans (by simpa using h2)

/-- The lower barrier `-U_{-g}` lies below the upper barrier `U_g` on `closure C`. -/
theorem neg_laplaceUpperBarrier_neg_le (hext : UniformExteriorSphereSq C R)
    (hD : ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D) (hL : 0 <= L)
    {x₀ : Point n} (hx₀ : x₀ ∈ frontier C) {g : Point n -> Real}
    (hg : ∀ x ∈ closure C, ∀ y ∈ closure C, |g x - g y| <= L * Real.sqrt (eucSq x y))
    {x : Point n} (hx : x ∈ closure C) :
    -laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) (fun y => -g y) x <=
      laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) g x := by
  have hR := hext.1
  have hgc : ContinuousOn g (closure C) := continuousOn_of_abs_sub_le_mul_sqrt_eucSq hg
  refine le_laplaceUpperBarrier hx₀ hext x fun p hp => ?_
  have hV := le_laplaceUpperBarrier (A := laplaceBarrierCoeff n R D L) (g := fun y => -g y)
    hx₀ hext x (b := -g p.1 - laplaceBarrierCoeff n R D L *
      laplaceBarrierProfile (laplaceBarrierRate n R) R p x) fun q hq => by
    have hp1 : p.1 ∈ closure C := frontier_subset_closure hp.1
    have hq1 : q.1 ∈ closure C := frontier_subset_closure hq.1
    have h1 := mul_sqrt_eucSq_le_coeff_mul_profile hR hD hL hp hx
    have h2 := mul_sqrt_eucSq_le_coeff_mul_profile hR hD hL hq hx
    have h3 := hg q.1 hq1 p.1 hp1
    have h4 := le_abs_self (g q.1 - g p.1)
    have h5 := sqrt_eucSq_triangle q.1 x p.1
    rw [eucSq_comm q.1 x] at h5
    have h6 := mul_le_mul_of_nonneg_left h5 hL
    unfold laplaceBarrierBranch
    linarith
  unfold laplaceBarrierBranch
  linarith

end Assembly

/--
**Perron barriers for the Laplace operator under a uniform exterior sphere
condition.** Let `C` be a bounded open set satisfying the uniform exterior
sphere condition with radius `R`, and let `L ≥ 0`. There is a constant `K`,
depending only on `n`, `R`, `L` and the diameter of `C`, such that every `g`
which is `L`-Lipschitz on `closure C` for the Euclidean distance admits a
Dirichlet barrier pair for `-Δu = 0` whose members are continuous on
`closure C`, attain the boundary values `g` in the envelope sense, and satisfy
the Hölder-`1/2` boundary modulus `|B(x) - g(x₀)| ≤ K |x - x₀|^{1/2}`.
-/
theorem exists_laplace_barrierPair_of_uniformExteriorSphereSq
    {C : Set (Point n)} (hCopen : IsOpen C) (hCbdd : Bornology.IsBounded C)
    {R : Real} (hext : UniformExteriorSphereSq C R) (L : Real) (hL : 0 <= L) :
    ∃ K : Real, 0 <= K ∧ ∀ g : Point n -> Real,
      (∀ x ∈ closure C, ∀ y ∈ closure C, |g x - g y| <= L * Real.sqrt (eucSq x y)) ->
      ∃ B : DirichletBarrierPair C (frontier C) laplaceOperator g,
        ContinuousOn B.lower (closure C) ∧ ContinuousOn B.upper (closure C) ∧
        BoundaryLowerTraceOn C (frontier C) g B.lower ∧
        BoundaryUpperTraceOn C (frontier C) g B.upper ∧
        ∀ x₀ ∈ frontier C, ∀ x ∈ closure C,
          B.upper x <= g x₀ + K * Real.sqrt (Real.sqrt (eucSq x x₀)) ∧
          g x₀ - K * Real.sqrt (Real.sqrt (eucSq x x₀)) <= B.lower x := by
  obtain ⟨D, hD⟩ := exists_eucSq_le_of_isBounded hCbdd
  refine ⟨laplaceBarrierModulus n R D L, laplaceBarrierModulus_nonneg hL, fun g hg => ?_⟩
  rcases (frontier C).eq_empty_or_nonempty with hfr | ⟨x₀, hx₀⟩
  · -- Empty frontier: the constant barriers `0`.
    refine ⟨⟨fun _ => 0, fun _ => 0,
      ⟨viscositySubsolution_laplaceOperator_const hCopen 0, fun x hx => by simp [hfr] at hx,
        continuousOn_const.upperSemicontinuousOn⟩,
      ⟨viscositySupersolution_laplaceOperator_const hCopen 0, fun x hx => by simp [hfr] at hx,
        continuousOn_const.lowerSemicontinuousOn⟩,
      fun _ _ => le_rfl⟩, continuousOn_const, continuousOn_const, fun x hx => ?_, fun x hx => ?_,
      fun x hx => ?_⟩ <;> simp [hfr] at hx
  · have hg' : ∀ x ∈ closure C, ∀ y ∈ closure C,
        |(fun z => -g z) x - (fun z => -g z) y| <= L * Real.sqrt (eucSq x y) := by
      intro x hx y hy
      have h := hg x hx y hy
      rw [← abs_neg]
      simpa [neg_sub, sub_eq_add_neg, add_comm] using h
    obtain ⟨hUc, hUsuper, hUbd, hUmod⟩ :=
      laplaceUpperBarrier_properties hCopen hCbdd hext hD hL hx₀ hg
    obtain ⟨hVc, hVsuper, hVbd, hVmod⟩ :=
      laplaceUpperBarrier_properties hCopen hCbdd hext hD hL hx₀ hg'
    set U := laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) g with hU
    set V := laplaceUpperBarrier C R (laplaceBarrierCoeff n R D L) (fun y => -g y) with hV
    have hsub : ViscositySubsolution C laplaceOperator (fun y => -V y) := by
      have h := viscositySupersolution_neg_iff.mp hVsuper
      rwa [negOperator_laplaceOperator] at h
    have hVn : Continuous fun y => -V y := hVc.neg
    refine ⟨⟨fun y => -V y, U,
      ⟨hsub, fun z hz => by simp [hVbd z hz], hVn.continuousOn.upperSemicontinuousOn⟩,
      ⟨hUsuper, fun z hz => by simp [hUbd z hz], hUc.continuousOn.lowerSemicontinuousOn⟩,
      fun x hx => ?_⟩, hVn.continuousOn, hUc.continuousOn, fun z hz => ?_, fun z hz => ?_,
      fun z hz x hx => ⟨hUmod z hz x hx, ?_⟩⟩
    · have hxC : x ∈ closure C := by
        rcases hx with hx | hx
        · exact subset_closure hx
        · exact frontier_subset_closure hx
      exact neg_laplaceUpperBarrier_neg_le hext hD hL hx₀ hg hxC
    · rw [lowerEnvelope_eq_of_continuous hVn (frontier_subset_closure hz), hVbd z hz, neg_neg]
    · rw [upperEnvelope_eq_of_continuous hUc (frontier_subset_closure hz), hUbd z hz]
    · have h := hVmod z hz x hx
      change _ <= -V x
      linarith

end ViscositySolns
