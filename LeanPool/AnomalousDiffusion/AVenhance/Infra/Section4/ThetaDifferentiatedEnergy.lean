/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiated
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaClassicalUniqueness

/-! The differentiated classical θ equation in divergence form and its
instantaneous torus energy identity. -/

@[expose] public section

open Homogenization
open MeasureTheory
open scoped Topology

namespace AVenhance.Infra.Section4

/-- Joint time-space domain with strictly positive time. -/
def ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem ThetaDifferentiatedEnergy.thetaEnergy_smooth_slice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec 2 → E}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f)
      ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (f t) := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => f t x) Set.univ := by
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ x ∈ Set.univ, (t, x) ∈ ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain := by
      intro x hx
      exact ⟨ht, Set.mem_univ x⟩
    have h := hf.comp hmap hmem
    simpa [Function.uncurry, Function.comp_def] using h
  exact contDiffOn_univ.mp hcomp

/-- Zero initial data select the zero classical solution by the energy
uniqueness theorem. -/
theorem theta_classical_solution_eq_zero_of_zero_data
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) θ₀ θ) (hθ₀ : θ₀ = 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec 2, θ t x = 0 := by
  let z : ℝ → Vec 2 → ℝ := fun _ _ => 0
  have hz : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) θ₀ z := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact contDiffOn_const
    · intro t ht k x
      rfl
    · intro x
      simp [z, hθ₀]
    · intro t ht x
      simp [AVenhance.advDiffOp, z, AVenhance.spaceGrad, AVenhance.spaceLap,
        Homogenization.vecDot]
  intro t ht x
  have heq := streamVel_classical_unique φ hφ κ hκ
    (fun _ _ => 0) θ₀ hsol hz t ht x
  simpa [z] using heq.symm

theorem ThetaDifferentiatedEnergy.theta_spaceGrad_neg {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => -f y) x i =
      -AVenhance.spaceGrad f x i := by
  have h := classicalSpaceGrad_sub (fun _ : Vec 2 => (0 : ℝ)) f
    contDiff_const hf i x
  simp [AVenhance.spaceGrad] at h ⊢

/-- The first stream derivative in a commutator term is transferred onto the
stream potential by torus integration by parts. This is the skew-symmetric
step that makes the q = 1 energy term use only the stream-regularity order-two bound. -/
theorem theta_stream_flux_pairing_integration_by_parts
    {g h u : Vec 2 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hgp : AVenhance.IsZ2Periodic g) (hhp : AVenhance.IsZ2Periodic h)
    (hup : AVenhance.IsZ2Periodic u) :
    (∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad u x)
        (fun j => g x * AVenhance.streamVel (fun _ => h) 0 x j)) =
      -(∫ x in AVenhance.unitCube,
        u x * vecDot (AVenhance.spaceGrad g x)
          (AVenhance.streamVel (fun _ => h) 0 x)) := by
  let v : Vec 2 → Vec 2 := AVenhance.streamVel (fun _ => h) 0
  let F : Vec 2 → Vec 2 := fun x j => g x * v x j
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := theta_streamVel_contDiff h hh
  have hvper : AVenhance.IsZ2Periodic v := theta_streamVel_periodic h hh hhp
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply contDiff_pi.2
    intro j
    exact hg.mul (contDiff_pi.mp hv j)
  have hFper : AVenhance.IsZ2Periodic F := by
    intro k x
    funext j
    change g (x + AVenhance.latticeShift k) * v (x + AVenhance.latticeShift k) j =
      g x * v x j
    rw [hgp k x, congrFun (hvper k x) j]
  have hdivV (x : Vec 2) : AVenhance.vecDiv v x = 0 := by
    have h := theta_streamVel_ordered_derivative_divergence_free h hh [] x
    simpa [AVenhance.vecDiv, classicalWordDerivative, Classical.classicalWordDerivative] using h
  have hdivF (x : Vec 2) :
      AVenhance.vecDiv F x = vecDot (AVenhance.spaceGrad g x) (v x) := by
    simpa [F, v] using theta_product_vector_divergence hg hv hdivV x
  have hparts := theta_divergence_pairing hu hup hF hFper
  have hreplace :
      (∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv F x) =
        ∫ x in AVenhance.unitCube,
          u x * vecDot (AVenhance.spaceGrad g x) (v x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hdivF x]
  have hparts' := hparts
  rw [hreplace] at hparts'
  simpa [F, v] using (by linarith :
    (∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad u x) (F x)) =
      -(∫ x in AVenhance.unitCube,
        u x * vecDot (AVenhance.spaceGrad g x) (v x)))

/-- Each component of the rotated gradient has square bounded by the full
gradient energy. -/
theorem theta_streamVel_component_sq_le_gradient
    {h : Vec 2 → ℝ} (x : Vec 2) (j : Fin 2) :
    (AVenhance.streamVel (fun _ => h) 0 x j) ^ 2 ≤
      vecNormSq (AVenhance.spaceGrad h x) := by
  have h0 : AVenhance.streamVel (fun _ => h) 0 x 0 =
      -AVenhance.spaceGrad h x 1 := by
    simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have h1 : AVenhance.streamVel (fun _ => h) 0 x 1 =
      AVenhance.spaceGrad h x 0 := by
    simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  fin_cases j
  · change (AVenhance.streamVel (fun _ => h) 0 x 0) ^ 2 ≤ _
    rw [h0]
    simpa using
      Homogenization.sq_apply_le_vecNormSq (AVenhance.spaceGrad h x) 1
  · change (AVenhance.streamVel (fun _ => h) 0 x 1) ^ 2 ≤ _
    rw [h1]
    exact Homogenization.sq_apply_le_vecNormSq (AVenhance.spaceGrad h x) 0

/-- The q = 1 energy term becomes a lower-order gradient square after the
skew integration by parts. -/
theorem theta_first_order_flux_density_abs_le
    {u h g : Vec 2 → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (x : Vec 2)
    (hu : u x ^ 2 ≤ vecNormSq (AVenhance.spaceGrad h x))
    (hg : ∀ j : Fin 2, |AVenhance.spaceGrad g x j| ≤ M) :
    |u x * vecDot (AVenhance.spaceGrad g x)
      (AVenhance.streamVel (fun _ => h) 0 x)| ≤
      2 * M * vecNormSq (AVenhance.spaceGrad h x) := by
  let G := vecNormSq (AVenhance.spaceGrad h x)
  have hG : 0 ≤ G := Homogenization.vecNormSq_nonneg _
  have hterm (j : Fin 2) :
      |u x * AVenhance.spaceGrad g x j *
        AVenhance.streamVel (fun _ => h) 0 x j| ≤ M * G := by
    have hv := theta_streamVel_component_sq_le_gradient (h := h) x j
    have hprod : |u x * AVenhance.streamVel (fun _ => h) 0 x j| ≤ G := by
      have hyoung := Homogenization.abs_le_add_halves_of_sq_le_mul
        (u := u x * AVenhance.streamVel (fun _ => h) 0 x j)
        (A := (u x) ^ 2)
        (B := (AVenhance.streamVel (fun _ => h) 0 x j) ^ 2)
        (by rw [mul_pow]) (sq_nonneg _) (sq_nonneg _)
      dsimp [G]
      linarith [hu, hv]
    calc
      |u x * AVenhance.spaceGrad g x j *
          AVenhance.streamVel (fun _ => h) 0 x j| =
        |AVenhance.spaceGrad g x j| *
          |u x * AVenhance.streamVel (fun _ => h) 0 x j| := by
            rw [abs_mul, abs_mul]
            rw [abs_mul]
            ring_nf
      _ ≤ M * G := mul_le_mul (hg j) hprod (abs_nonneg _) hM
  calc
    |u x * vecDot (AVenhance.spaceGrad g x)
        (AVenhance.streamVel (fun _ => h) 0 x)| =
      |u x * AVenhance.spaceGrad g x 0 *
          AVenhance.streamVel (fun _ => h) 0 x 0 +
        u x * AVenhance.spaceGrad g x 1 *
          AVenhance.streamVel (fun _ => h) 0 x 1| := by
            rw [Homogenization.vecDot, Fin.sum_univ_two]
            rw [mul_add]
            congr 1
            ring
    _ ≤ |u x * AVenhance.spaceGrad g x 0 *
          AVenhance.streamVel (fun _ => h) 0 x 0| +
        |u x * AVenhance.spaceGrad g x 1 *
          AVenhance.streamVel (fun _ => h) 0 x 1| := abs_add_le _ _
    _ ≤ M * G + M * G := add_le_add (hterm 0) (hterm 1)
    _ = 2 * M * vecNormSq (AVenhance.spaceGrad h x) := by ring

/-- The q = 1 commutator flux pairing is controlled by the lower-order
gradient energy after periodic integration by parts.  This is the sharper
first-order estimate used to check the printed analytic recursion. -/
theorem theta_first_order_flux_pairing_abs_le
    {u h g : Vec 2 → ℝ} {M : ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hgp : AVenhance.IsZ2Periodic g) (hhp : AVenhance.IsZ2Periodic h)
    (hup : AVenhance.IsZ2Periodic u) (hM : 0 ≤ M)
    (hcomp : ∀ x, u x ^ 2 ≤ vecNormSq (AVenhance.spaceGrad h x))
    (hgrad : ∀ x j, |AVenhance.spaceGrad g x j| ≤ M) :
    |∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad u x)
        (fun j => g x * AVenhance.streamVel (fun _ => h) 0 x j)| ≤
      2 * M * (∫ x in AVenhance.unitCube,
        vecNormSq (AVenhance.spaceGrad h x)) := by
  have hparts := theta_stream_flux_pairing_integration_by_parts
    hg hh hu hgp hhp hup
  have hsg : Continuous (AVenhance.spaceGrad g) := by
    apply continuous_pi
    intro j
    change Continuous (fun x => fderiv ℝ g x (Homogenization.basisVec j))
    exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsh : Continuous (AVenhance.spaceGrad h) := by
    apply continuous_pi
    intro j
    change Continuous (fun x => fderiv ℝ h x (Homogenization.basisVec j))
    exact (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hv : Continuous (AVenhance.streamVel (fun _ => h) 0) :=
    (theta_streamVel_contDiff h hh).continuous
  have hdot : Continuous (fun x =>
      vecDot (AVenhance.spaceGrad g x)
        (AVenhance.streamVel (fun _ => h) 0 x)) := by
    change Continuous (fun x => ∑ j : Fin 2,
      AVenhance.spaceGrad g x j * AVenhance.streamVel (fun _ => h) 0 x j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hsg).mul ((continuous_apply j).comp hv)
  have hnormsq : Continuous (fun x =>
      vecNormSq (AVenhance.spaceGrad h x)) := by
    change Continuous (fun x => ∑ j : Fin 2,
      AVenhance.spaceGrad h x j * AVenhance.spaceGrad h x j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hsh).mul ((continuous_apply j).comp hsh)
  have hrightInt : IntegrableOn
      (fun x => |u x * vecDot (AVenhance.spaceGrad g x)
        (AVenhance.streamVel (fun _ => h) 0 x)|) AVenhance.unitCube := by
    exact thetaTime_integrableOn_unitCube ((hu.continuous).mul hdot |>.abs)
  have hgradInt : IntegrableOn
      (fun x => 2 * M * vecNormSq (AVenhance.spaceGrad h x))
      AVenhance.unitCube := by
    exact thetaTime_integrableOn_unitCube (hnormsq.const_mul (2 * M))
  have hmono := MeasureTheory.setIntegral_mono_on hrightInt hgradInt
    thetaTime_measurableSet_unitCube (fun x hx => by
      simpa using theta_first_order_flux_density_abs_le
        (hM := hM) x (hcomp x) (hgrad x))
  calc
    |∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad u x)
          (fun j => g x * AVenhance.streamVel (fun _ => h) 0 x j)|
        = |∫ x in AVenhance.unitCube,
            u x * vecDot (AVenhance.spaceGrad g x)
              (AVenhance.streamVel (fun _ => h) 0 x)| := by
          rw [hparts]
          simp
    _ ≤ ∫ x in AVenhance.unitCube,
          |u x * vecDot (AVenhance.spaceGrad g x)
            (AVenhance.streamVel (fun _ => h) 0 x)| :=
          abs_integral_le_integral_abs
    _ ≤ ∫ x in AVenhance.unitCube,
          2 * M * vecNormSq (AVenhance.spaceGrad h x) := hmono
    _ = 2 * M * (∫ x in AVenhance.unitCube,
          vecNormSq (AVenhance.spaceGrad h x)) := by
          rw [integral_const_mul]

/-- For every ordered spatial derivative, the differentiated equation is a
forced equation in the divergence form generated by the stream potential.
The energy pairing is exact, before estimating the flux by the
    stream-regularity/diffusivity-recursion data. -/
theorem theta_classical_differentiated_energy_pairing
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) θ₀ θ)
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) :
    (∫ x in AVenhance.unitCube,
      classicalWordDerivative w (θ t) x *
        deriv (fun s => classicalWordDerivative w (θ s) x) t) +
      κ * (∫ x in AVenhance.unitCube,
        vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
      -(∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x)) := by
  let b : ℝ → Vec 2 → Vec 2 := AVenhance.streamVel φ
  let u : ℝ → Vec 2 → ℝ := fun s x => classicalWordDerivative w (θ s) x
  let Flux : Vec 2 → Vec 2 := thetaStreamCommutatorFlux w (φ t) (θ t)
  let F : ℝ → Vec 2 → Vec 2 := fun s =>
    thetaStreamCommutatorFlux w (φ s) (θ s)
  have hθOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain := by
    apply hsol.1.mono
    rintro ⟨s, x⟩ hp
    have hs : 0 < s := by simpa [ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain] using hp.1
    exact ⟨le_of_lt hs, Set.mem_univ x⟩
  have hbOpen : ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (AVenhance.streamVel φ))
          ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain := by
    simpa [ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain, classicalPositiveTimeDomain] using
      theta_streamVel_joint_contDiffOn hφ
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain := by
    have hjoint := thetaJointWordDerivative_contDiffOn hθOpen w
    apply hjoint.congr
    intro p hp
    rcases p with ⟨s, x⟩
    have hs : 0 < s := by
      simpa [ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain] using hp.1
    exact (thetaJointWordDerivative_eq_classicalWordDerivative hθOpen w hs x).symm
  have huSlice : ContDiff ℝ (⊤ : ℕ∞) (u t) := classicalSmooth_slice huOpen ht
  have hθSlice : ContDiff ℝ (⊤ : ℕ∞) (θ t) := classicalSmooth_slice hθOpen ht
  have hφSlice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hφOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
        ThetaDifferentiatedEnergy.thetaEnergyPositiveDomain := by
      exact hφ.1.contDiffOn
    exact classicalSmooth_slice hφOpen ht
  have hφper : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have hθper : AVenhance.IsZ2Periodic (θ t) := hsol.2.1 t (le_of_lt ht)
  have huper : AVenhance.IsZ2Periodic (u t) := by
    simpa [u] using classicalWordDerivative_periodic w hθSlice
      (hsol.2.1 t (le_of_lt ht))
  have hflux := thetaStreamCommutatorFlux_contDiff_periodic w
    hφSlice hθSlice hφper hθper
  have hflux0 : ContDiff ℝ (⊤ : ℕ∞) (Flux) := by
    simpa [Flux] using hflux.1
  have hfluxper : AVenhance.IsZ2Periodic Flux := by
    simpa [Flux] using hflux.2
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) := by
    apply contDiff_pi.2
    intro j
    simpa [F, Flux] using (contDiff_pi.mp hflux0 j)
  have hFper : AVenhance.IsZ2Periodic (F t) := by
    intro k x
    funext j
    change Flux (x + AVenhance.latticeShift k) j = Flux x j
    exact congrFun (hfluxper k x) j
  have hfluxDiv := thetaStreamCommutatorFlux_divergence w (φ t) (θ t)
    hφSlice hθSlice
  have hpde (x : Vec 2) :
      deriv (fun s => u s x) t - κ * AVenhance.spaceLap (u t) x +
        vecDot (b t x) (AVenhance.spaceGrad (u t) x) =
          AVenhance.vecDiv (F t) x := by
    have hdiff := theta_classical_differentiated_transport_equation
      hsol hbOpen ht w x
    have hdiff' : classicalTimePartial u (t, x) -
        κ * AVenhance.spaceLap (u t) x +
        vecDot (b t x) (AVenhance.spaceGrad (u t) x) +
        ∑ j : Fin 2,
          classicalWordCommutatorExpansion w (fun y => b t y j)
            (fun y => AVenhance.spaceGrad (θ t) y j) x = 0 := by
      simpa [u, b, classicalTransport, Classical.classicalTransport] using hdiff
    have htime := classicalTimePartial_eq_deriv huOpen ht x
    calc
      _ = -∑ j : Fin 2,
          classicalWordCommutatorExpansion w (fun y => b t y j)
            (fun y => AVenhance.spaceGrad (θ t) y j) x := by
        rw [← htime]
        linarith [hdiff']
      _ = AVenhance.vecDiv (F t) x := by
        rw [hfluxDiv]
        rfl
  have hpair := theta_forced_classical_energy_pairing hφ
    huSlice huper hFslice hFper hpde
  simpa [u, F, Flux] using hpair

/-- Equivalent non-divergence energy pairing. The forcing is the transport
commutator itself, which is the form used in the normalized derivative
recursion. -/
theorem theta_classical_differentiated_transport_energy_pairing
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) θ₀ θ)
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) :
    (∫ x in AVenhance.unitCube,
      classicalWordDerivative w (θ t) x *
        deriv (fun s => classicalWordDerivative w (θ s) x) t) +
      κ * (∫ x in AVenhance.unitCube,
        vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
    -(∫ x in AVenhance.unitCube,
      classicalWordDerivative w (θ t) x *
        (classicalWordDerivative w
            (classicalTransport (AVenhance.streamVel φ t) (θ t)) x -
          vecDot (AVenhance.streamVel φ t x)
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x))) := by
  let u : Vec 2 → ℝ := classicalWordDerivative w (θ t)
  let b : Vec 2 → Vec 2 := AVenhance.streamVel φ t
  let F : Vec 2 → Vec 2 := thetaStreamCommutatorFlux w (φ t) (θ t)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    exact classicalWordDerivative_contDiff w (θ t)
      (classicalSmooth_slice_nonneg hsol.1 ht.le)
  have huper : AVenhance.IsZ2Periodic u := by
    exact classicalWordDerivative_periodic w
      (classicalSmooth_slice_nonneg hsol.1 ht.le) (hsol.2.1 t ht.le)
  have hφslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (t, x)) := contDiff_const.prodMk contDiff_id
    have hcomp := hφ.1.comp hmap
    simpa [Function.uncurry, Function.comp_def] using hcomp
  have hφper : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have hflux := thetaStreamCommutatorFlux_contDiff_periodic w
    hφslice (classicalSmooth_slice_nonneg hsol.1 ht.le) hφper
    (hsol.2.1 t ht.le)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by simpa [F] using hflux.1
  have hFper : AVenhance.IsZ2Periodic F := by simpa [F] using hflux.2
  have hdivPair := theta_divergence_pairing hu huper hF hFper
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    change ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (fun _ => φ t) 0)
    exact theta_streamVel_contDiff (φ t) hφslice
  have hcomm (x : Vec 2) :
      AVenhance.vecDiv F x =
        -(classicalWordDerivative w (classicalTransport b (θ t)) x -
          vecDot (b x) (AVenhance.spaceGrad u x)) := by
    have hdiv := thetaStreamCommutatorFlux_divergence w (φ t) (θ t)
      hφslice (classicalSmooth_slice_nonneg hsol.1 ht.le) x
    have htransport := classicalWordDerivative_transport_eq_commutatorExpansion
      w b (θ t) hb (classicalSmooth_slice_nonneg hsol.1 ht.le) x
    have htransport' :
        classicalWordDerivative w (classicalTransport b (θ t)) x -
          vecDot (b x) (AVenhance.spaceGrad u x) =
        ∑ j : Fin 2,
          classicalWordCommutatorExpansion w (fun y =>
            AVenhance.streamVel (fun _ => φ t) 0 y j)
            (fun y => AVenhance.spaceGrad (θ t) y j) x := by
      simpa [b, u, AVenhance.streamVel] using htransport
    rw [hdiv, ← htransport']
  have hdivIntegral :
      (∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv F x) =
        -(∫ x in AVenhance.unitCube,
          u x * (classicalWordDerivative w (classicalTransport b (θ t)) x -
            vecDot (b x) (AVenhance.spaceGrad u x))) := by
    have heq : (fun x => u x * AVenhance.vecDiv F x) =
      fun x => -(u x *
          (classicalWordDerivative w (classicalTransport b (θ t)) x -
            vecDot (b x) (AVenhance.spaceGrad u x))) := by
      funext x
      rw [hcomm x]
      ring
    rw [heq, integral_neg]
  have henergy := theta_classical_differentiated_energy_pairing hφ hsol ht w
  have henergyDiv :
      (∫ x in AVenhance.unitCube,
        u x * deriv (fun s => classicalWordDerivative w (θ s) x) t) +
        κ * (∫ x in AVenhance.unitCube, vecNormSq (AVenhance.spaceGrad u x)) =
        ∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv F x := by
    calc
      _ = -(∫ x in AVenhance.unitCube,
          vecDot (AVenhance.spaceGrad u x) (F x)) := by
        simpa [u, F] using henergy
      _ = ∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv F x := hdivPair.symm
  rw [hdivIntegral] at henergyDiv
  simpa [u, b] using henergyDiv

end AVenhance.Infra.Section4
