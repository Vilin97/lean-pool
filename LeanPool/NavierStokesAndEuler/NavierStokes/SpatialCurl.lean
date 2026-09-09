/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The physical Euclidean curl

All derivatives in this file are genuine Fréchet derivatives on the Euclidean
space used in `ProblemStatement`. In particular, mixed-partial symmetry is
proved from C² regularity, rather than assumed for formal derivative symbols.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SpatialCurl

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

/-- The `(j,i)` entry of a spatial derivative. -/
def derivativeEntry (i j : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ Space (coordinateVector i))

@[simp] theorem derivativeEntry_apply (i j : Fin 3) (L : Space →L[ℝ] Space) :
    derivativeEntry i j L = (L (coordinateVector i)) j := rfl

/-- The usual antisymmetric part of a Jacobian, identified with a vector. -/
def curlLinear : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (derivativeEntry 1 2 - derivativeEntry 2 1).smulRight (coordinateVector 0) +
  (derivativeEntry 2 0 - derivativeEntry 0 2).smulRight (coordinateVector 1) +
  (derivativeEntry 0 1 - derivativeEntry 1 0).smulRight (coordinateVector 2)

@[simp] theorem curlLinear_apply_zero (L : Space →L[ℝ] Space) :
    (curlLinear L) 0 = (L (coordinateVector 1)) 2 - (L (coordinateVector 2)) 1 := by
  simp [curlLinear, coordinateVector]

@[simp] theorem curlLinear_apply_one (L : Space →L[ℝ] Space) :
    (curlLinear L) 1 = (L (coordinateVector 2)) 0 - (L (coordinateVector 0)) 2 := by
  simp [curlLinear, coordinateVector]

@[simp] theorem curlLinear_apply_two (L : Space →L[ℝ] Space) :
    (curlLinear L) 2 = (L (coordinateVector 0)) 1 - (L (coordinateVector 1)) 0 := by
  simp [curlLinear, coordinateVector]

/-- Curl of a potential on physical Euclidean three-space. -/
def curl (A : Space → Space) (x : Space) : Space := curlLinear (fderiv ℝ A x)

/-- Curl taken only in space, with the physical time held fixed. -/
def spatialCurl (A : VelocityField) : VelocityField :=
  fun z => curl (fun y => A (z.1, y)) z.2

/-- Actual mixed-partial symmetry, obtained from Schwarz's theorem. -/
theorem mixed_partial_symmetry {A : Space → Space} {x : Space}
    (hA : ContDiffAt ℝ 2 A x) (i j : Fin 3) :
    fderiv ℝ (fderiv ℝ A) x (coordinateVector i) (coordinateVector j) =
      fderiv ℝ (fderiv ℝ A) x (coordinateVector j) (coordinateVector i) := by
  exact (hA.isSymmSndFDerivAt (by simp)).eq (coordinateVector i) (coordinateVector j)

/-- Differentiating the curl is applying a fixed continuous linear map to
the actual second derivative of its potential. -/
theorem fderiv_curl {A : Space → Space} {x : Space}
    (hA : ContDiffAt ℝ 2 A x) :
    fderiv ℝ (curl A) x = curlLinear.comp (fderiv ℝ (fderiv ℝ A) x) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ A) x :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (curlLinear.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

/-- Divergence of curl is zero for every C² potential at the point in question. -/
theorem divergence_curl {A : Space → Space} {x : Space}
    (hA : ContDiffAt ℝ 2 A x) :
    (∑ i : Fin 3, (fderiv ℝ (curl A) x (coordinateVector i)) i) = 0 := by
  rw [fderiv_curl hA]
  rw [Fin.sum_univ_three]
  simp only [ContinuousLinearMap.comp_apply, curlLinear_apply_zero,
    curlLinear_apply_one, curlLinear_apply_two]
  have h01 := congrArg (fun v : Space => v 2) (mixed_partial_symmetry hA 0 1)
  have h02 := congrArg (fun v : Space => v 1) (mixed_partial_symmetry hA 0 2)
  have h12 := congrArg (fun v : Space => v 0) (mixed_partial_symmetry hA 1 2)
  dsimp at h01 h02 h12
  rw [h01, h02, h12]
  abel

/-- The divergence in the actual PDE target vanishes on every C² spatial
slice, including the time-zero slice when its spatial regularity is given. -/
theorem spatialDivergence_spatialCurl (A : VelocityField) (t : ℝ) (x : Space)
    (hA : ContDiffAt ℝ 2 (fun y : Space => A (t, y)) x) :
    spatialDivergence (spatialCurl A) t x = 0 := by
  change (∑ i : Fin 3,
    (fderiv ℝ (curl (fun y : Space => A (t, y))) x (coordinateVector i)) i) = 0
  exact divergence_curl hA

/-- One derivative of regularity is sufficient for taking the curl. -/
theorem contDiffAt_curl {A : Space → Space} {x : Space} {m n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (curl A) x :=
  curlLinear.contDiff.comp_contDiffAt x (hA.fderiv_right hmn)

theorem contDiff_curl {A : Space → Space} {m n : WithTop ℕ∞}
    (hA : ContDiff ℝ n A) (hmn : m + 1 ≤ n) : ContDiff ℝ m (curl A) :=
  curlLinear.contDiff.comp (hA.fderiv_right hmn)

/-- Joint spacetime smoothness is preserved, with loss of one derivative. -/
theorem contDiff_spatialCurl {A : VelocityField} {m n : WithTop ℕ∞}
    (hA : ContDiff ℝ n A) (hmn : m + 1 ≤ n) : ContDiff ℝ m (spatialCurl A) := by
  have hp : ContDiff ℝ n (fun p : SpaceTime × Space => A (p.1.1, p.2)) :=
    hA.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ m
      (fun z : SpaceTime => fderiv ℝ (fun y : Space => A (z.1, y)) z.2) :=
    hp.fderiv contDiff_snd hmn
  exact curlLinear.contDiff.comp hd

theorem contDiffAt_spatialCurl {A : VelocityField} {z : SpaceTime} {m n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A z) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (spatialCurl A) z := by
  have hp : ContDiffAt ℝ n (fun p : SpaceTime × Space => A (p.1.1, p.2)) (z, z.2) :=
    hA.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ m
      (fun w : SpaceTime => fderiv ℝ (fun y : Space => A (w.1, y)) w.2) z :=
    hp.fderiv contDiffAt_snd hmn
  exact curlLinear.contDiff.comp_contDiffAt z hd

/-- Relative spacetime regularity suffices even at the endpoint of a time
interval, since the spatial derivative is taken on all of space. -/
theorem contDiffOn_spatialCurl {A : VelocityField} {times : Set ℝ}
    {m n : WithTop ℕ∞} (hA : ContDiffOn ℝ n A (times ×ˢ (univ : Set Space)))
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (spatialCurl A) (times ×ˢ (univ : Set Space)) := by
  intro z hz
  have hp : ContDiffWithinAt ℝ n
      (fun p : SpaceTime × Space => A (p.1.1, p.2))
      ((times ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) (z, z.2) := by
    apply (hA z hz).comp (z, z.2)
      (contDiff_fst.fst.prodMk contDiff_snd).contDiffWithinAt
    intro p hp
    exact ⟨hp.1.1, mem_univ _⟩
  have hd : ContDiffWithinAt ℝ m
      (fun w : SpaceTime => fderivWithin ℝ (fun y : Space => A (w.1, y)) univ w.2)
      (times ×ˢ (univ : Set Space)) z :=
    hp.fderivWithin contDiffWithinAt_snd uniqueDiffOn_univ hmn hz (by simp)
  have hd' : ContDiffWithinAt ℝ m
      (fun w : SpaceTime => fderiv ℝ (fun y : Space => A (w.1, y)) w.2)
      (times ×ˢ (univ : Set Space)) z := by
    simpa only [fderivWithin_univ] using hd
  exact hd'.continuousLinearMap_comp curlLinear

theorem contDiff_spatialSlice {A : VelocityField} {times : Set ℝ} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n A (times ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ times) : ContDiff ℝ n (fun x : Space => A (t, x)) :=
  hA.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)

theorem spatialDivergence_spatialCurl_on {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ 2 A (times ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    spatialDivergence (spatialCurl A) t x = 0 :=
  spatialDivergence_spatialCurl A t x (contDiff_spatialSlice hA ht).contDiffAt

/-- Equality of potentials on a neighborhood gives equality of their curls. -/
theorem curl_eq_of_eventuallyEq {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A x = curl B x := by
  unfold curl
  rw [h.fderiv_eq]

theorem curl_eventuallyEq {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A =ᶠ[𝓝 x] curl B :=
  h.fderiv.mono fun _ h' => congrArg curlLinear h'

/-- A periodic potential gives a periodic curl; the identity also holds for
the totalized derivative at points without differentiability. -/
theorem curl_periodic {A : Space → Space} {a : Space}
    (h : ∀ x, A (x + a) = A x) : ∀ x, curl A (x + a) = curl A x := by
  intro x
  unfold curl
  congr 1
  rw [← fderiv_comp_add_right a]
  exact congrArg (fun f : Space → Space => fderiv ℝ f x) (funext h)

theorem spatialCurl_periodic {A : VelocityField} {times : Set ℝ}
    (hA : UnitSpatialPeriodsOn times A) : UnitSpatialPeriodsOn times (spatialCurl A) := by
  intro t ht x i
  exact curl_periodic (fun y => hA t ht y i) x

@[simp] theorem curl_zero (x : Space) : curl (fun _ => (0 : Space)) x = 0 := by
  simp [curl]

theorem spatialCurl_eq_zero_of_timeSlice {A : VelocityField} {t : ℝ}
    (hA : ∀ x : Space, A (t, x) = 0) (x : Space) : spatialCurl A (t, x) = 0 := by
  change curl (fun y : Space => A (t, y)) x = 0
  rw [funext hA]
  exact curl_zero x

theorem compactFutureTimeSupport_spatialCurl {A : VelocityField}
    (hA : CompactFutureTimeSupport A) : CompactFutureTimeSupport (spatialCurl A) := by
  obtain ⟨T, hT, hzero⟩ := hA
  exact ⟨T, hT, fun t ht x => spatialCurl_eq_zero_of_timeSlice (hzero t ht) x⟩

theorem curl_eq_zero_of_not_mem_tsupport {A : Space → Space} {x : Space}
    (hx : x ∉ tsupport A) : curl A x = 0 := by
  simp [curl, fderiv_of_notMem_tsupport ℝ hx]

/-- Taking a curl cannot enlarge closed spatial support. -/
theorem tsupport_curl_subset (A : Space → Space) : tsupport (curl A) ⊆ tsupport A := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (curl_eq_zero_of_not_mem_tsupport h)

theorem hasCompactSupport_curl {A : Space → Space} (hA : HasCompactSupport A) :
    HasCompactSupport (curl A) :=
  hA.fderiv ℝ |>.comp_left (g := curlLinear) (map_zero curlLinear)

theorem tsupport_curl_cutoff_subset (χ : Space → ℝ) (A : Space → Space) :
    tsupport (curl (fun y => χ y • A y)) ⊆ tsupport χ :=
  (tsupport_curl_subset _).trans (tsupport_smul_subset_left χ A)

theorem hasCompactSupport_curl_cutoff {χ : Space → ℝ} (hχ : HasCompactSupport χ)
    (A : Space → Space) : HasCompactSupport (curl (fun y => χ y • A y)) :=
  hasCompactSupport_curl hχ.smul_right

/-- Multiplying the potential by a spatial cutoff and then taking its curl
gives a genuinely divergence-free field. -/
theorem divergence_curl_cutoff {χ : Space → ℝ} {A : Space → Space} {x : Space}
    (hχ : ContDiffAt ℝ 2 χ x) (hA : ContDiffAt ℝ 2 A x) :
    (∑ i : Fin 3, (fderiv ℝ (curl (fun y => χ y • A y)) x (coordinateVector i)) i) = 0 :=
  divergence_curl (hχ.smul hA)

/-- A cutoff equal to one near a point preserves the original curl there. -/
theorem curl_cutoff_eq {χ : Space → ℝ} {A : Space → Space} {x : Space}
    (hχ : ∀ᶠ y in 𝓝 x, χ y = 1) : curl (fun y => χ y • A y) x = curl A x := by
  apply curl_eq_of_eventuallyEq
  filter_upwards [hχ] with y hy
  simp [hy]

end NavierStokes.SpatialCurl
