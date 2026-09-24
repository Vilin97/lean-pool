/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedUnion
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedGeometry
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The spatial gradient of a pressure slice on a whole ball

Display (3.5) produces, on a backward cylinder of radius `ρ`, a weak spatial
gradient of the pressure slice only on the concentric ball of radius `ρ / 2`,
and the radius `ρ` is limited by the time window that the cylinder must fit
into.  A single application therefore never reaches a prescribed ball.

Applying it instead on every sufficiently small cylinder of a fixed countable
family and gluing the outcomes reaches every ball whose closure stays inside
the spatial domain, at almost every time of the whole time set.  The gluing is
`exists_weakPartialDerivOn_of_local`; the countable family comes from a
countable dense set of centres together with rational radii and rational top
times, so that the almost-everywhere conditions can be intersected.

Because a locally integrable weak partial derivative is unique almost
everywhere on an open set, every bound proved for a slice gradient on a
sub-ball is inherited by the glued field there.  That is the mechanism that
makes a bound available at *every* cell scale rather than at one scale only.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Any bound proved for one weak partial derivative on an open subset is
inherited by every weak partial derivative of the same function on a larger
set.  Both are locally integrable there, so they agree almost everywhere. -/
theorem eLpNorm_le_of_hasWeakPartialDerivOn {d : ℕ}
    {B B' : Set (Vec d)} (hB' : IsOpen B') (hB'B : B' ⊆ B)
    {i : Fin d} {u G D : Vec d → ℝ} {r K : ℝ≥0∞}
    (hGloc : LocallyIntegrableOn G B volume)
    (hDloc : LocallyIntegrableOn D B' volume)
    (hG : HasWeakPartialDerivOn B i u G)
    (hD : HasWeakPartialDerivOn B' i u D)
    (hK : eLpNorm D r (volume.restrict B') ≤ K) :
    eLpNorm G r (volume.restrict B') ≤ K := by
  have h : G =ᵐ[volume.restrict B'] D :=
    HasWeakPartialDerivOn.ae_eq hB' (hGloc.mono_set hB'B) hDloc
      (hG.restrict hB' hB'B) hD
  rwa [eLpNorm_congr_ae h]

/-- From the slice estimate on every admissible small backward cylinder to a
weak spatial derivative on a whole ball, at almost every time.

The hypothesis is exactly the shape display (3.5) delivers: for each centre,
top time and radius whose closed cylinder lies in the space-time domain, a
weak spatial derivative on the concentric ball of half the radius, for almost
every time of that cylinder's window. -/
theorem ae_exists_weakPartialDerivOn_ball_of_small_cylinders
    {Ω : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    {x₀ : Vec3} {R : ℝ} (hRΩ : vec3Ball x₀ R ⊆ Ω)
    {i : Fin 3} {p : ParabolicPoint → ℝ}
    (hp : ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) (vec3Ball x₀ R) volume)
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball c (ρ / 2)) i (fun x => p (x, s)) g) :
    ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x₀ R) volume ∧
      HasWeakPartialDerivOn (vec3Ball x₀ R) i (fun x => p (x, t)) g := by
  classical
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  have : Countable ↥S := hScount.to_subtype
  have hfam : ∀ a : ↥S × ℚ × ℚ, ∀ᵐ t ∂(volume.restrict I),
      0 < ((a.2.2 : ℚ) : ℝ) →
      closure (parabolicCylinder (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ) ((a.2.2 : ℚ) : ℝ)) ⊆
        CKN.spaceTimeSet Ω I →
      t ∈ Ioc (((a.2.1 : ℚ) : ℝ) - ((a.2.2 : ℚ) : ℝ) ^ 2) ((a.2.1 : ℚ) : ℝ) →
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) i
          (fun x => p (x, t)) g := by
    intro a
    by_cases hρ : 0 < ((a.2.2 : ℚ) : ℝ)
    · by_cases hsub : closure (parabolicCylinder (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ)
        ((a.2.2 : ℚ) : ℝ)) ⊆ CKN.spaceTimeSet Ω I
      · have h := hslice (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ) ((a.2.2 : ℚ) : ℝ) hρ hsub
        have h2 := ae_imp_of_ae_restrict h
        refine ae_restrict_of_ae (h2.mono ?_)
        intro t ht _ _ hmem
        exact ht hmem
      · exact Filter.Eventually.of_forall (fun _ _ h => absurd h hsub)
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hρ)
  have hall : ∀ᵐ t ∂(volume.restrict I), ∀ a : ↥S × ℚ × ℚ,
      0 < ((a.2.2 : ℚ) : ℝ) →
      closure (parabolicCylinder (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ) ((a.2.2 : ℚ) : ℝ)) ⊆
        CKN.spaceTimeSet Ω I →
      t ∈ Ioc (((a.2.1 : ℚ) : ℝ) - ((a.2.2 : ℚ) : ℝ) ^ 2) ((a.2.1 : ℚ) : ℝ) →
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) i
          (fun x => p (x, t)) g := ae_all_iff.mpr hfam
  filter_upwards [hp, hall, self_mem_ae_restrict hI.measurableSet] with t htp htall htI
  refine exists_weakPartialDerivOn_of_local (isOpen_vec3Ball x₀ R) htp ?_
  intro x hx
  obtain ⟨c, t₀, ρ, hcS, hρ, hxmem, hsub2, hclos, hmem⟩ :=
    exists_small_cylinder_of_mem hI hSdense hx htI
  refine ⟨vec3Ball c ((ρ : ℝ) / 2), isOpen_vec3Ball _ _, hxmem, hsub2, ?_⟩
  exact htall (⟨c, hcS⟩, t₀, ρ) hρ
    (hclos.trans (Set.prod_mono hRΩ (subset_refl I))) hmem

/-- The explicit Euclidean ball of positive radius is the Euclidean norm ball.
The slice estimate states its carrier with the first, the parabolic geometry
with the second. -/
private theorem euclideanBall_eq_vec3Ball_of_pos {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The same statement with the slice estimate's own carrier notation. -/
theorem ae_exists_weakPartialDerivOn_ball_of_small_euclidean_cylinders
    {Ω : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    {x₀ : Vec3} {R : ℝ} (hRΩ : vec3Ball x₀ R ⊆ Ω)
    {i : Fin 3} {p : ParabolicPoint → ℝ}
    (hp : ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) (vec3Ball x₀ R) volume)
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun x => p (x, s)) g) :
    ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x₀ R) volume ∧
      HasWeakPartialDerivOn (vec3Ball x₀ R) i (fun x => p (x, t)) g := by
  refine ae_exists_weakPartialDerivOn_ball_of_small_cylinders hI hRΩ hp ?_
  intro c t₀ ρ hρ hsub
  have hball : euclideanBall c (ρ / 2) = vec3Ball c (ρ / 2) :=
    euclideanBall_eq_vec3Ball_of_pos (by linarith only [hρ])
  simpa only [hball] using hslice c t₀ ρ hρ hsub

/-- The unit-cylinder domain hypothesis of the origin carrier puts every ball
of radius below one inside the spatial domain. -/
theorem vec3Ball_subset_of_origin_dom {Ω : Set Vec3} {I : Set ℝ} {R : ℝ}
    (hR : R ≤ 1)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I) :
    vec3Ball (0 : Vec3) R ⊆ Ω := by
  intro y hy
  have hmem : ((y, (0 : ℝ)) : ParabolicPoint) ∈
      closure (parabolicCylinder (0 : Vec3) 0 1) := by
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (le_of_lt hy) hR
    · norm_num
    · norm_num
  exact (hdom hmem).1

/-- The carrier that the origin-cell slice clause asks for, produced from the
small-cylinder form of display (3.5).  The conclusion is the first clause of
the origin-pressure-gradient slice data with the majorant clause removed: the
majorant has to come from the quantitative slice bound, not from this
qualitative statement. -/
theorem ae_exists_origin_slice_gradient_of_small_cylinders
    {Ω : Set Vec3} {I : Set ℝ} (hI : IsOpen I) {R₀ : ℝ} (hR₀ : R₀ ≤ 1)
    {p : ParabolicPoint → ℝ}
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I)
    (hp : ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) (vec3Ball (0 : Vec3) R₀) volume)
    (hslice : ∀ k : Fin 3, ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) k (fun x => p (x, s)) g) :
    ∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) k (fun x => p (x, t)) g :=
  fun k => ae_exists_weakPartialDerivOn_ball_of_small_euclidean_cylinders hI
    (vec3Ball_subset_of_origin_dom hR₀ hdom) hp (hslice k)

end CKN.Core.Step4
