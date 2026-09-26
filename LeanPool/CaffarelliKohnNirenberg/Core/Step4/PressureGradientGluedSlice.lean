/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersShift
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedLocality
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSelectionCore
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

public section

section

/-!
# Small backward cylinders around an interior space-time point

Around a point of an open Euclidean ball and a time interior to the time set
there is a backward parabolic cylinder with rational radius and rational top
time, centred at a point of any prescribed dense set, whose closure lies in the
product of the ball and the time set, whose half-radius ball still contains the
point and lies in the ball, and whose time window contains the given time.
This is the geometric step that lets one apply a slice estimate on arbitrarily
small cylinders drawn from a fixed countable family.
-/

open MeasureTheory Set
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Step4

/-- The triangle inequality for the Euclidean norm on `Vec3`. -/
private lemma norm_sub_triangle (a b c : Vec3) :
    vec3EuclideanNorm (a - c) ≤ vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  have h : WithLp.toLp 2 (a - c) =
      WithLp.toLp 2 (a - b) + WithLp.toLp 2 (b - c) := by
    rw [← WithLp.toLp_add]
    congr 1
    abel
  rw [h]
  exact norm_add_le _ _

/-- Around a point `x` of an open Euclidean ball and a time `s` interior to an open time
set there is a backward parabolic cylinder with rational radius and rational top time,
centred at a point of any prescribed dense set `S`, whose half-radius ball contains `x`
and lies in the original ball, whose closure lies in the product of the ball and the time
set, and whose time window contains `s`. -/
theorem exists_small_cylinder_of_mem
    {x₀ : Vec3} {R : ℝ} {I : Set ℝ} (hI : IsOpen I)
    {S : Set Vec3} (hSd : Dense S)
    {x : Vec3} (hx : x ∈ vec3Ball x₀ R) {s : ℝ} (hs : s ∈ I) :
    ∃ (c : Vec3) (t₀ ρ : ℚ), c ∈ S ∧ 0 < (ρ : ℝ) ∧
      x ∈ vec3Ball c ((ρ : ℝ) / 2) ∧
      vec3Ball c ((ρ : ℝ) / 2) ⊆ vec3Ball x₀ R ∧
      closure (parabolicCylinder c (t₀ : ℝ) (ρ : ℝ)) ⊆ vec3Ball x₀ R ×ˢ I ∧
      s ∈ Set.Ioc ((t₀ : ℝ) - (ρ : ℝ) ^ 2) (t₀ : ℝ) := by
  have hxlt : vec3EuclideanNorm (x - x₀) < R := by
    rwa [mem_vec3Ball] at hx
  -- the distance from `x` to the boundary of the ball
  set d : ℝ := R - vec3EuclideanNorm (x - x₀) with hd
  have hdpos : 0 < d := by
    rw [hd]
    linarith only [hxlt]
  -- a spacing that keeps the cylinder in the ball and its time window in the time set
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hI s hs
  set m : ℝ := min (4 * d / 5) (min 1 δ) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (by linarith only [hdpos]) (lt_min (by norm_num) hδpos)
  obtain ⟨ρ, hρ0, hρm⟩ := exists_rat_btwn hmpos
  have hρ45 : (ρ : ℝ) < 4 * d / 5 := hρm.trans_le (min_le_left _ _)
  have hρ1 : (ρ : ℝ) < 1 :=
    (hρm.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hρδ : (ρ : ℝ) < δ :=
    (hρm.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hρsqpos : 0 < (ρ : ℝ) ^ 2 := pow_pos hρ0 2
  have hρsqδ : (ρ : ℝ) ^ 2 < δ := by
    have hlt : (ρ : ℝ) ^ 2 < (ρ : ℝ) := by
      have h := mul_lt_mul_of_pos_right hρ1 hρ0
      simpa [pow_two] using h
    linarith only [hlt, hρδ]
  -- a rational top time just above `s`
  obtain ⟨t₀, hslt, ht₀lt⟩ :=
    exists_rat_btwn (show s < s + (ρ : ℝ) ^ 2 / 2 by linarith only [hρsqpos])
  -- a centre drawn from the dense set, close to `x`
  have hxmem : x ∈ vec3Ball x ((ρ : ℝ) / 4) := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    linarith only [hρ0]
  obtain ⟨c, hcball, hcS⟩ :=
    hSd.inter_open_nonempty (vec3Ball x ((ρ : ℝ) / 4))
      (isOpen_vec3Ball x ((ρ : ℝ) / 4)) ⟨x, hxmem⟩
  have hcx : vec3EuclideanNorm (c - x) < (ρ : ℝ) / 4 := by
    rwa [mem_vec3Ball] at hcball
  refine ⟨c, t₀, ρ, hcS, hρ0, ?_, ?_, ?_, ?_⟩
  · -- the point lies in the half-radius ball
    rw [mem_vec3Ball, CKN.Foundation.Heat.vec3EuclideanNorm_sub_comm]
    linarith only [hcx, hρ0]
  · -- the half-radius ball lies in the original ball
    intro y hy
    rw [mem_vec3Ball] at hy ⊢
    have h1 := norm_sub_triangle y c x₀
    have h2 := norm_sub_triangle c x x₀
    have h3 : 3 * (ρ : ℝ) / 4 < d := by linarith only [hρ45, hdpos]
    linarith only [h1, h2, hy, hcx, hd, h3]
  · -- the closed cylinder lies in the product of the ball and the time set
    rintro ⟨y, t⟩ hp
    rw [closure_parabolicCylinder hρ0] at hp
    change vec3EuclideanNorm (y - c) ≤ (ρ : ℝ) ∧
      ((t₀ : ℝ) - (ρ : ℝ) ^ 2 ≤ t ∧ t ≤ (t₀ : ℝ)) at hp
    obtain ⟨hyn, hti₁, hti₂⟩ := hp
    change y ∈ vec3Ball x₀ R ∧ t ∈ I
    refine ⟨?_, ?_⟩
    · rw [mem_vec3Ball]
      have h1 := norm_sub_triangle y c x₀
      have h2 := norm_sub_triangle c x x₀
      have h5 : 5 * (ρ : ℝ) / 4 < d := by linarith only [hρ45]
      linarith only [h1, h2, hyn, hcx, hd, h5]
    · refine hδsub ?_
      rw [Real.ball_eq_Ioo]
      refine ⟨?_, ?_⟩
      · linarith only [hti₁, hslt, hρsqδ]
      · have hhalf : (ρ : ℝ) ^ 2 / 2 < δ := by linarith only [hρsqpos, hρsqδ]
        linarith only [hti₂, ht₀lt, hhalf]
  · -- the given time lies in the time window of the cylinder
    refine ⟨?_, le_of_lt hslt⟩
    linarith only [ht₀lt, hρsqpos]

end CKN.Core.Step4
end

end

section

/-!
# Gluing weak partial derivatives over an open cover

Weak partial derivatives produced separately on the members of an open cover
agree almost everywhere on the overlaps, because a locally integrable weak
partial derivative is unique almost everywhere on an open set.  They therefore
glue: over a countable open cover the pieces are represented by one function,
and by locality that function is the weak partial derivative on the union.

The second statement is the form used in practice.  It says that the existence
of a weak partial derivative is a purely local matter: if every point of an
open set has a neighbourhood on which `u` has a locally integrable `i`th weak
partial derivative, then `u` has one on the whole set.  Second countability of
`Fin d → ℝ` reduces the given family to a countable subfamily.
-/

open MeasureTheory Set
noncomputable section
namespace CKN

/-- Weak partial derivatives given on the members of a countable open cover of
`U` glue to a single locally integrable weak partial derivative on `U`, which
agrees almost everywhere with each given piece. -/
theorem exists_weakPartialDerivOn_of_countable_cover {d : ℕ}
    {U : Set (Vec d)} {V : ℕ → Set (Vec d)} {i : Fin d} {u : Vec d → ℝ}
    {g : ℕ → Vec d → ℝ}
    (hU : MeasurableSet U) (hV : ∀ n, IsOpen (V n)) (hcover : U ⊆ ⋃ n, V n)
    (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ n, LocallyIntegrableOn (g n) (V n) volume)
    (hweak : ∀ n, HasWeakPartialDerivOn (V n) i u (g n)) :
    ∃ G : Vec d → ℝ, LocallyIntegrableOn G U volume ∧
      HasWeakPartialDerivOn U i u G ∧
      ∀ n, G =ᵐ[volume.restrict (V n)] g n := by
  have hagree : ∀ m n, g m =ᵐ[volume.restrict (V m ∩ V n)] g n := by
    intro m n
    have hopen : IsOpen (V m ∩ V n) := (hV m).inter (hV n)
    exact HasWeakPartialDerivOn.ae_eq hopen
      ((hg m).mono_set inter_subset_left) ((hg n).mono_set inter_subset_right)
      ((hweak m).restrict hopen inter_subset_left)
      ((hweak n).restrict hopen inter_subset_right)
  obtain ⟨G, hG⟩ := exists_ae_eq_of_countable_family (fun n => (hV n).measurableSet) hagree
  have hGloc : LocallyIntegrableOn G U volume :=
    locallyIntegrableOn_of_ae_eq_cover hV hcover hg hG
  refine ⟨G, hGloc, ?_, hG⟩
  refine hasWeakPartialDerivOn_of_isOpen_cover hU hV hcover hu hGloc fun n => ?_
  exact (hweak n).congr_deriv_ae (hG n).symm

/-- Existence of a weak partial derivative is local: a function with a locally
integrable `i`th weak partial derivative near every point of an open set has
one on the whole set. -/
theorem exists_weakPartialDerivOn_of_local {d : ℕ}
    {U : Set (Vec d)} {i : Fin d} {u : Vec d → ℝ}
    (hU : IsOpen U) (hu : LocallyIntegrableOn u U volume)
    (hlocal : ∀ x ∈ U, ∃ W : Set (Vec d), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ g : Vec d → ℝ, LocallyIntegrableOn g W volume ∧
        HasWeakPartialDerivOn W i u g) :
    ∃ G : Vec d → ℝ, LocallyIntegrableOn G U volume ∧
      HasWeakPartialDerivOn U i u G := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · refine ⟨fun _ => 0, fun x hx => absurd hx (notMem_empty x), ?_⟩
    intro φ _ _ _
    simp
  · choose! W hWopen hWmem _hWU g hgloc hgweak using hlocal
    set Wsub : U → Set (Vec d) := fun a => W (a : Vec d) with hWsubdef
    have hUcov : U ⊆ ⋃ a : U, Wsub a := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, hWmem x hx⟩
    obtain ⟨T, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_iUnion_countable Wsub (fun a => hWopen (a : Vec d) a.2)
    obtain ⟨x₀, hx₀⟩ := hUne
    have hTne : T.Nonempty := by
      have hx₀mem : x₀ ∈ ⋃ a ∈ T, Wsub a := by rw [hTeq]; exact hUcov hx₀
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx₀mem
      obtain ⟨haT, -⟩ := mem_iUnion.mp ha
      exact ⟨a, haT⟩
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hcover : U ⊆ ⋃ n : ℕ, Wsub (f n) := by
      intro x hx
      have hxmem : x ∈ ⋃ a ∈ T, Wsub a := by rw [hTeq]; exact hUcov hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hxmem
      obtain ⟨haT, hxa⟩ := mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := hf ▸ haT
      exact mem_iUnion.mpr ⟨n, hn ▸ hxa⟩
    obtain ⟨G, hGloc, hGweak, -⟩ :=
      exists_weakPartialDerivOn_of_countable_cover (V := fun n => Wsub (f n))
        hU.measurableSet (fun n => hWopen (f n : Vec d) (f n).2) hcover hu
        (fun n => hgloc (f n : Vec d) (f n).2)
        (fun n => hgweak (f n : Vec d) (f n).2)
    exact ⟨G, hGloc, hGweak⟩

end CKN
end

end

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
