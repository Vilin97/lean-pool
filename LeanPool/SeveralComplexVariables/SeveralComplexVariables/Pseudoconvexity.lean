/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Order.ProjIcc
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsContinuation
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Thullen
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Plurisubharmonic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Subharmonic.Majorant

/-!
# Pseudoconvexity

This file relates domains of holomorphy to plurisubharmonic functions and to two geometric
convexity notions.

* **Boundary distance.** On a domain of holomorphy in `Fin n → ℂ`, the negative logarithm of
the supremum-norm distance to the complement is plurisubharmonic. The proof is
[Hörmander][Hormander1973]'s: a
harmonic polynomial majorant of `-log δ` on a circle in a complex line gives, through the
weighted hull-radius bound of Thullen's lemma, the same bound at the center.
* **Pseudoconvexity.** An open set is pseudoconvex if it carries a continuous
  plurisubharmonic exhaustion function. Domains of holomorphy are pseudoconvex.
* **Continuity principle.** Along a continuous family of affine analytic discs whose boundary
  circles stay in a pseudoconvex set and whose initial disc lies in the set, every disc lies in
  the set. This is the Kontinuitätssatz for affine discs, proved by the maximum principle for
  plurisubharmonic functions on discs.
* **Hartogs convexity.** In a product `E × ℂ`, a set satisfying the continuity principle
  contains the filled cylinder of every Hartogs cylinder it contains.
* **Kontinuitätssatz.** On a domain of holomorphy in a finite-dimensional complex normed space, the
continuity principle
holds for continuous families of holomorphic discs, not only affine ones: every point of a
holomorphic disc lies in the holomorphic hull of the boundary circle, and Thullen's radius
bound keeps the discs at a fixed distance from the complement.

The boundary-distance result uses the supremum norm on `Fin n → ℂ`. For the whole space,
`Metric.infDist` of the empty complement and `Real.log 0` are both zero, so the function in
that theorem is identically zero. This is a real-valued convention; `boundaryEDistance` instead
takes the value `∞` for an empty complement. Pseudoconvexity and the holomorphic continuity
principle are transported to arbitrary finite-dimensional complex normed spaces; this transport
does not identify their boundary-distance functions.

The converse implications, from pseudoconvexity back to the domain-of-holomorphy property, form
the Levi problem and are outside the present scope.

References: [Hörmander][Hormander1973] (1973), Theorems 2.5.4, 2.6.5 and 2.6.7;
[Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Sections 1 and 3;
[Range][Range1986] (1986), Chapter II, Sections 2 and 5.

## Main definitions

* `IsPseudoconvex`: An open set is pseudoconvex if it carries a continuous plurisubharmonic
  exhaustion function: one whose sublevel sets inside the set are compact.
* `SatisfiesContinuityPrinciple`: **Continuity principle for affine analytic discs.** Along a
  continuous family of affine analytic discs whose boundary circles stay in the set and whose
  initial disc lies in the set, every disc of the family lies in the set.
* `SatisfiesHolomorphicContinuityPrinciple`: **Continuity principle for holomorphic discs
  (Kontinuitätssatz).** Along a continuous family of holomorphic discs whose boundary circles stay
  in the set and whose initial disc lies in the set, every disc of the family lies in the set.
* `IsHartogsConvex`: **Hartogs convexity** for cylinder figures: whenever a Hartogs cylinder over an
  open preconnected base, with disc fibers over a nonempty open part of the base, lies in the set,
  so does the filled cylinder.

## Main results

* `IsDomainOfHolomorphy.plurisubharmonicOn_neg_log_infDist`: **Plurisubharmonicity of the boundary
  distance ([Hörmander][Hormander1973] 2.6.5).** On a domain of holomorphy in `Fin n → ℂ`, the
  negative logarithm of the distance to the complement is plurisubharmonic.
* `IsDomainOfHolomorphy.isPseudoconvex_fin`: **Domains of holomorphy in coordinates are
  pseudoconvex.** The exhaustion is the maximum of the negative logarithm of the boundary distance
  and the norm.
* `IsPseudoconvex.satisfiesContinuityPrinciple`: **Pseudoconvex sets satisfy the continuity
  principle ([Fritzsche–Grauert][FritzscheGrauert2002] II.3.1).**
* `IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple_fin`: **Domains of holomorphy in
  coordinates satisfy the continuity principle for holomorphic discs.** The coordinate-free version
  is `IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple`.
* `IsDomainOfHolomorphy.isPseudoconvex`: **Domains of holomorphy are pseudoconvex.** The exhaustion
  is transported from the coordinate version `IsDomainOfHolomorphy.isPseudoconvex_fin`.
* `IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple`: **Domains of holomorphy satisfy
  the continuity principle for holomorphic discs.**
* `SatisfiesContinuityPrinciple.isHartogsConvex`: **The continuity principle implies Hartogs
  convexity ([Fritzsche–Grauert][FritzscheGrauert2002] II.1.5).** The disc fibers are slid along a
  path in the base from the part carrying full discs.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public section

open Complex Filter Metric Set Real
open scoped Topology

namespace SeveralComplexVariables

/-- Clamp a real parameter to the unit interval. -/
private noncomputable def clampIcc01 (t : ℝ) : ℝ := Set.projIcc 0 1 zero_le_one t

/-- Clamping to `[0, 1]` is continuous. -/
private theorem continuous_clampIcc01 : Continuous clampIcc01 := continuous_subtype_val.comp
  continuous_projIcc

/-- The clamp of any real lies in `[0, 1]`. -/
private theorem clampIcc01_mem_Icc (t : ℝ) : clampIcc01 t ∈ Icc (0 : ℝ) 1 :=
  (Set.projIcc 0 1 zero_le_one t).property

/-- Clamping is the identity on `[0, 1]`. -/
private theorem clampIcc01_eq_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampIcc01 t = t
    := congrArg
  Subtype.val (Set.projIcc_of_mem zero_le_one ht)

/-- Clamping is idempotent. -/
private theorem clampIcc01_idem (t : ℝ) : clampIcc01 (clampIcc01 t) = clampIcc01 t :=
  clampIcc01_eq_of_mem_Icc (clampIcc01_mem_Icc t)

section BoundaryDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Points of a closed disc in a complex line lie in the holomorphic hull of its boundary circle, by
the maximum modulus principle. -/
theorem mem_holomorphicHull_of_mem_disc {U : Set E} {a w : E} {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ t ∈ closedBall (0 : ℂ) r, a + t • w ∈ U) {t : ℂ} (ht : t ∈ closedBall (0 : ℂ) r) :
    a + t • w ∈ holomorphicHull U ((fun t : ℂ => a + t • w) '' sphere 0 r) := by
  refine ⟨hdisc t ht, fun f hf M hM => ?_⟩
  have hg : DiffContOnCl ℂ (fun t : ℂ => f (a + t • w)) (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hr.ne']
    exact fun s hs => ((hf _ (hdisc s hs)).comp_of_eq
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
        rfl).differentiableAt.differentiableWithinAt
  have hbd : ∀ s ∈ frontier (ball (0 : ℂ) r), ‖f (a + s • w)‖ ≤ M := by
    intro s hs
    rw [frontier_ball 0 hr.ne'] at hs
    exact hM _ ⟨s, hs, rfl⟩
  have := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg hbd
    (z := t) (by rw [closure_ball 0 hr.ne']; exact ht)
  exact this

/-- Every point of a closed holomorphic disc lies in the holomorphic hull of the boundary circle, by
the maximum modulus principle. -/
theorem mem_holomorphicHull_of_analytic_disc {U : Set E} {φ : ℂ → E} {r : ℝ} (hr : 0 < r)
    (hφ : AnalyticOnNhd ℂ φ (closedBall 0 r)) (hdisc : ∀ t ∈ closedBall (0 : ℂ) r, φ t ∈ U)
    {t : ℂ} (ht : t ∈ closedBall (0 : ℂ) r) : φ t ∈ holomorphicHull U (φ '' sphere 0 r) := by
  refine ⟨hdisc t ht, fun f hf M hM => ?_⟩
  have hg : DiffContOnCl ℂ (fun t : ℂ => f (φ t)) (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hr.ne']
    exact fun s hs => ((hf _ (hdisc s hs)).comp_of_eq (hφ s hs)
      rfl).differentiableAt.differentiableWithinAt
  have hbd : ∀ s ∈ frontier (ball (0 : ℂ) r), ‖f (φ s)‖ ≤ M := by
    intro s hs
    rw [frontier_ball 0 hr.ne'] at hs
    exact hM _ ⟨s, hs, rfl⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg hbd
    (z := t) (by rw [closure_ball 0 hr.ne']; exact ht)

variable {n : ℕ}

/-- **Plurisubharmonicity of the boundary distance ([Hörmander][Hormander1973] 2.6.5).** On a domain
of holomorphy in `Fin n → ℂ`, the negative logarithm of the supremum-norm distance to the
complement is plurisubharmonic. When the complement is empty, this function is zero by the
conventions `Metric.infDist_empty` and `Real.log_zero`. -/
theorem IsDomainOfHolomorphy.plurisubharmonicOn_neg_log_infDist {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) :
    PlurisubharmonicOn (fun z => -Real.log (infDist z Uᶜ)) U := by
  rcases eq_empty_or_nonempty Uᶜ with hc | hc
  · simp only [hc, infDist_empty, Real.log_zero, neg_zero]
    exact plurisubharmonicOn_const 0 U
  have hpos : ∀ z ∈ U, 0 < infDist z Uᶜ := fun z hz =>
    (infDist_pos_iff_notMem_closure hc).mp (by rwa [ho.isClosed_compl.closure_eq, notMem_compl_iff])
  have hcont : ContinuousOn (fun z => -Real.log (infDist z Uᶜ)) U :=
    ((continuous_infDist_pt Uᶜ).continuousOn.log fun z hz => (hpos z hz).ne').neg
  refine plurisubharmonicOn_of_hasSubmeanAt hcont.upperSemicontinuousOn fun a ha w => ?_
  -- the constant slice
  by_cases hw : w = 0
  · simp only [hw, smul_zero, add_zero]
    exact hasSubmeanAt_const _ 0
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hline : Continuous fun t : ℂ => a + t • w := by fun_prop
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hline.continuousAt.preimage_mem_nhds (by
    change U ∈ 𝓝 ((fun t : ℂ => a + t • w) 0)
    simp only [zero_smul, add_zero]
    exact ho.mem_nhds ha))
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ => ?_
  have hdisc : ∀ t ∈ closedBall (0 : ℂ) r, a + t • w ∈ U := fun t ht =>
    hball (closedBall_subset_ball hrρ ht)
  have hslice_cont : ContinuousOn (fun t : ℂ => -Real.log (infDist (a + t • w) Uᶜ)) (sphere 0 r) :=
    hcont.comp hline.continuousOn fun t ht => hdisc t (sphere_subset_closedBall ht)
  refine ⟨hslice_cont.circleIntegrable hr.le, ?_⟩
  refine le_circleAverage_of_forall_polynomial_majorant hr hslice_cont fun Q hQ => ?_
  simp only [zero_smul, add_zero]
  -- the entire function realizing the polynomial majorant along the line
  set F : (Fin n → ℂ) → ℂ := fun z => Q.eval ((z i - a i) / w i / r) with hF
  have hFline : ∀ t : ℂ, F (a + t • w) = Q.eval ((t - 0) / r) := fun t => by
    simp only [hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, sub_zero]
    rw [mul_div_cancel_right₀ _ hi]
  set q : (Fin n → ℂ) → ℂ := fun z => Complex.exp (-F z) with hq
  have hqan : AnalyticOnNhd ℂ q U := by
    have hd : Differentiable ℂ q := by
      apply Complex.differentiable_exp.comp
      apply Differentiable.neg
      exact Q.differentiable.comp (by fun_prop)
    exact hd.analyticOnNhd_of_finiteDimensional.mono (subset_univ U)
  have hqnorm : ∀ z, ‖q z‖ = Real.exp (-(F z).re) := fun z => by
    simp [hq, Complex.norm_exp]
  set K := (fun t : ℂ => a + t • w) '' sphere 0 r with hK
  have hKc : IsCompact K := (isCompact_sphere 0 r).image hline
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hdisc t (sphere_subset_closedBall ht)
  have hrad : ∀ z ∈ K, ball z ‖q z‖ ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hQ t ht
    rw [← hFline t] at h1
    change ball (a + t • w) ‖q (a + t • w)‖ ⊆ U
    rw [hqnorm]
    have hδ : 0 < infDist (a + t • w) Uᶜ := hpos _ (hdisc t (sphere_subset_closedBall ht))
    have h2 : Real.exp (-(F (a + t • w)).re) ≤ infDist (a + t • w) Uᶜ := by
      rw [← Real.le_log_iff_exp_le hδ]
      linarith
    apply (ball_subset_ball h2).trans
    simpa using (ball_infDist_subset_compl (x := a + t • w) (s := Uᶜ))
  have hhull := hU.holomorphic_radius_bound ho hKc hKU hqan hrad a
    (by simpa using mem_holomorphicHull_of_mem_disc hr hdisc (mem_closedBall_self hr.le))
  -- the radius bound at the center gives the distance bound
  have hδa : 0 < infDist a Uᶜ := hpos a ha
  have hle : ‖q a‖ ≤ infDist a Uᶜ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hc).mp hlt
    exact hy (hhull (by rwa [mem_ball, dist_comm]))
  rw [hqnorm, ← Real.le_log_iff_exp_le hδa] at hle
  have hFa : F a = Q.eval 0 := by
    have := hFline 0
    simpa using this
  rw [hFa] at hle
  linarith

end BoundaryDistance

section Pseudoconvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An open set is pseudoconvex if it carries a continuous plurisubharmonic exhaustion function: one
whose sublevel sets inside the set are compact. -/
@[expose] def IsPseudoconvex (U : Set E) : Prop :=
  IsOpen U ∧ ∃ φ : E → ℝ, ContinuousOn φ U ∧ PlurisubharmonicOn φ U ∧
    ∀ c : ℝ, IsCompact {z ∈ U | φ z ≤ c}

/-- A pseudoconvex set is open. -/
theorem IsPseudoconvex.isOpen {U : Set E} (h : IsPseudoconvex U) : IsOpen U := h.1

variable {n : ℕ}

/-- **Domains of holomorphy in coordinates are pseudoconvex.** The exhaustion is the maximum
of the negative logarithm of the boundary distance and the norm. The coordinate-free version
is `IsDomainOfHolomorphy.isPseudoconvex`. -/
theorem IsDomainOfHolomorphy.isPseudoconvex_fin {U : Set (Fin n → ℂ)} (hU : IsDomainOfHolomorphy U)
    (ho : IsOpen U) : IsPseudoconvex U := by
  refine ⟨ho, ?_⟩
  rcases eq_empty_or_nonempty Uᶜ with hc | hc
  · have hU' : U = univ := compl_empty_iff.mp hc
    refine ⟨fun z => ‖z‖, continuous_norm.continuousOn, plurisubharmonicOn_norm.mono (subset_univ
      U),
      fun c => ?_⟩
    convert isCompact_closedBall (0 : Fin n → ℂ) c using 1
    ext z
    simp [hU']
  have hpos : ∀ z ∈ U, 0 < infDist z Uᶜ := fun z hz =>
    (infDist_pos_iff_notMem_closure hc).mp (by rwa [ho.isClosed_compl.closure_eq, notMem_compl_iff])
  refine ⟨fun z => max (-Real.log (infDist z Uᶜ)) ‖z‖, ?_, ?_, fun c => ?_⟩
  · exact (((continuous_infDist_pt Uᶜ).continuousOn.log fun z hz => (hpos z hz).ne').neg).sup
      continuous_norm.continuousOn
  · exact (hU.plurisubharmonicOn_neg_log_infDist ho).sup (plurisubharmonicOn_norm.mono
    (subset_univ U))
  · have heq : {z ∈ U | max (-Real.log (infDist z Uᶜ)) ‖z‖ ≤ c} =
        {z | Real.exp (-c) ≤ infDist z Uᶜ} ∩ closedBall 0 c := by
      ext z
      simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right, max_le_iff]
      constructor
      · rintro ⟨hz, h1, h2⟩
        refine ⟨?_, h2⟩
        rw [← Real.le_log_iff_exp_le (hpos z hz)]
        linarith
      · rintro ⟨h1, h2⟩
        have hδ : 0 < infDist z Uᶜ := (Real.exp_pos _).trans_le h1
        have hz : z ∈ U := by
          by_contra hz
          rw [infDist_zero_of_mem hz] at hδ
          exact lt_irrefl _ hδ
        refine ⟨hz, ?_, h2⟩
        rw [← Real.le_log_iff_exp_le hδ] at h1
        linarith
    rw [heq]
    refine isCompact_of_isClosed_isBounded ((isClosed_le continuous_const
      (continuous_infDist_pt Uᶜ)).inter isClosed_closedBall) ?_
    exact isBounded_closedBall.subset inter_subset_right

/-- **Continuity principle for affine analytic discs.** Along a continuous family of affine
analytic discs whose boundary circles stay in the set and whose initial disc lies in the set,
every disc of the family lies in the set. -/
@[expose] def SatisfiesContinuityPrinciple (U : Set E) : Prop :=
  ∀ a b : ℝ → E, Continuous a → Continuous b →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ sphere (0 : ℂ) 1, a t + ζ • b t ∈ U) →
    (∀ ζ ∈ closedBall (0 : ℂ) 1, a 0 + ζ • b 0 ∈ U) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ closedBall (0 : ℂ) 1, a t + ζ • b t ∈ U

/-- **Pseudoconvex sets satisfy the continuity principle ([Fritzsche–Grauert][FritzscheGrauert2002]
II.3.1).** -/
theorem IsPseudoconvex.satisfiesContinuityPrinciple {U : Set E} (h : IsPseudoconvex U) :
    SatisfiesContinuityPrinciple U := by
  obtain ⟨hU, φ, hφc, hφpsh, hφex⟩ := h
  intro a b ha hb hbd h0
  set p := clampIcc01
  have hpc : Continuous p := continuous_clampIcc01
  have hpI : ∀ t, p t ∈ Icc (0 : ℝ) 1 := clampIcc01_mem_Icc
  have hpid : ∀ t ∈ Icc (0 : ℝ) 1, p t = t := fun t ht => clampIcc01_eq_of_mem_Icc ht
  have hpp : ∀ t, p (p t) = p t := clampIcc01_idem
  set Φ : ℝ × ℂ → E := fun q => a (p q.1) + q.2 • b (p q.1) with hΦ
  have hΦc : Continuous Φ := by fun_prop
  -- the compact set of boundary points and initial disc points
  set K₀ := Φ '' (Icc (0 : ℝ) 1 ×ˢ sphere (0 : ℂ) 1) ∪ Φ '' ({0} ×ˢ closedBall (0 : ℂ) 1) with hK₀
  have hK₀c : IsCompact K₀ :=
    ((isCompact_Icc.prod (isCompact_sphere _ _)).image hΦc).union
      ((isCompact_singleton.prod (isCompact_closedBall _ _)).image hΦc)
  have hK₀U : K₀ ⊆ U := by
    rintro _ (⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩ | ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩)
    · simp only [hΦ, hpid t ht]
      exact hbd t ht ζ hζ
    · simp only [mem_singleton_iff] at ht
      simp only [hΦ, ht, hpid 0 (left_mem_Icc.mpr zero_le_one)]
      exact h0 ζ hζ
  obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn (hφc.mono hK₀U)
  have hCle : ∀ z ∈ K₀, φ z ≤ C := fun z hz => (le_abs_self _).trans (by simpa using hC z hz)
  set L := {z ∈ U | φ z ≤ C} with hL
  have hLc : IsCompact L := hφex C
  have hLU : L ⊆ U := fun z hz => hz.1
  -- the parameters whose disc lies in `U`
  set W := {t : ℝ | ∀ ζ ∈ closedBall (0 : ℂ) 1, Φ (t, ζ) ∈ U} with hW
  have hdisc : ∀ t ∈ W, ∀ ζ ∈ closedBall (0 : ℂ) 1, Φ (t, ζ) ∈ L := by
    intro t ht ζ hζ
    have hat : a (p t) ∈ U := by simpa [hΦ] using ht 0 (mem_closedBall_self zero_le_one)
    have hsl : SubharmonicOn (fun ζ : ℂ => φ (a (p t) + ζ • b (p t))) (ball 0 1) :=
      (hφpsh.slice hat (b (p t))).mono fun ζ hζ => ht ζ (ball_subset_closedBall hζ)
    have husc : UpperSemicontinuousOn (fun ζ : ℂ => φ (a (p t) + ζ • b (p t))) (closedBall 0 1) :=
      (hφc.comp (by fun_prop : Continuous fun ζ : ℂ => a (p t) + ζ • b (p t)).continuousOn
        fun ζ hζ => ht ζ hζ).upperSemicontinuousOn
    have hbdy : ∀ ζ ∈ sphere (0 : ℂ) 1, φ (a (p t) + ζ • b (p t)) ≤ C := by
      intro ζ hζ
      apply hCle
      refine Or.inl ⟨(p t, ζ), ⟨hpI t, hζ⟩, ?_⟩
      simp only [hΦ, hpp]
    exact ⟨ht ζ hζ, hsl.le_of_le_sphere zero_lt_one husc hbdy ζ hζ⟩
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have := (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
      (x₀ := t) (P := fun t ζ => Φ (t, ζ) ∈ U) fun ζ hζ =>
        hΦc.continuousAt.preimage_mem_nhds (hU.mem_nhds (ht ζ hζ))
    exact this
  have hWcl : IsClosed W := by
    rw [← closure_subset_iff_isClosed]
    intro t ht ζ hζ
    have hne : NeBot (𝓝[W] t) := mem_closure_iff_nhdsWithin_neBot.mp ht
    have htend : Tendsto (fun t' => Φ (t', ζ)) (𝓝[W] t) (𝓝 (Φ (t, ζ))) :=
      ((hΦc.comp (continuous_id.prodMk continuous_const)).tendsto t).mono_left nhdsWithin_le_nhds
    have hmem : Φ (t, ζ) ∈ closure L :=
      mem_closure_of_tendsto htend (eventually_nhdsWithin_of_forall fun t' ht' => hdisc t' ht' ζ hζ)
    rw [hLc.isClosed.closure_eq] at hmem
    exact hLU hmem
  have hW0 : (0 : ℝ) ∈ W := by
    intro ζ hζ
    simp only [hΦ, hpid 0 (left_mem_Icc.mpr zero_le_one)]
    exact h0 ζ hζ
  have hWuniv : W = univ := IsClopen.eq_univ (⟨hWcl, hWo⟩ : IsClopen W) ⟨0, hW0⟩
  intro t ht ζ hζ
  have := (hWuniv ▸ mem_univ t : t ∈ W) ζ hζ
  simpa [hΦ, hpid t ht] using this

end Pseudoconvex


section HolomorphicContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Continuity principle for holomorphic discs (Kontinuitätssatz).** Along a continuous
family of holomorphic discs whose boundary circles stay in the set and whose initial disc lies
in the set, every disc of the family lies in the set. -/
@[expose] def SatisfiesHolomorphicContinuityPrinciple (U : Set E) : Prop :=
  ∀ φ : ℝ → ℂ → E, Continuous (fun q : ℝ × ℂ => φ q.1 q.2) →
    (∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (φ t) (closedBall 0 1)) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ sphere (0 : ℂ) 1, φ t ζ ∈ U) →
    (∀ ζ ∈ closedBall (0 : ℂ) 1, φ 0 ζ ∈ U) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ closedBall (0 : ℂ) 1, φ t ζ ∈ U

/-- The holomorphic continuity principle contains the affine one. -/
theorem SatisfiesHolomorphicContinuityPrinciple.satisfiesContinuityPrinciple {U : Set E}
    (h : SatisfiesHolomorphicContinuityPrinciple U) : SatisfiesContinuityPrinciple U := by
  intro a b ha hb hbd h0
  exact h (fun t ζ => a t + ζ • b t) (by fun_prop)
    (fun t _ ζ _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const)) hbd h0

variable {n : ℕ}

/-- **Domains of holomorphy in coordinates satisfy the continuity principle for holomorphic
discs.** The coordinate-free version is
`IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple`. -/
theorem IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple_fin {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : SatisfiesHolomorphicContinuityPrinciple U := by
  intro φ hφc hφan hbd h0
  rcases eq_empty_or_nonempty Uᶜ with hc | hc
  · have hU' : U = univ := compl_empty_iff.mp hc
    intro t _ ζ _
    rw [hU']
    exact mem_univ _
  set p := clampIcc01
  have hpc : Continuous p := continuous_clampIcc01
  have hpI : ∀ t, p t ∈ Icc (0 : ℝ) 1 := clampIcc01_mem_Icc
  have hpid : ∀ t ∈ Icc (0 : ℝ) 1, p t = t := fun t ht => clampIcc01_eq_of_mem_Icc ht
  have hpp : ∀ t, p (p t) = p t := clampIcc01_idem
  set Φ : ℝ × ℂ → Fin n → ℂ := fun q => φ (p q.1) q.2 with hΦ
  have hΦc : Continuous Φ := hφc.comp ((hpc.comp continuous_fst).prodMk continuous_snd)
  -- the compact set of boundary points and initial disc points
  set K₀ := Φ '' (Icc (0 : ℝ) 1 ×ˢ sphere (0 : ℂ) 1) ∪ Φ '' ({0} ×ˢ closedBall (0 : ℂ) 1) with hK₀
  have hK₀c : IsCompact K₀ :=
    ((isCompact_Icc.prod (isCompact_sphere _ _)).image hΦc).union
      ((isCompact_singleton.prod (isCompact_closedBall _ _)).image hΦc)
  have hK₀U : K₀ ⊆ U := by
    rintro _ (⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩ | ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩)
    · simp only [hΦ, hpid t ht]
      exact hbd t ht ζ hζ
    · simp only [mem_singleton_iff] at ht
      simp only [hΦ, ht, hpid 0 (left_mem_Icc.mpr zero_le_one)]
      exact h0 ζ hζ
  have hK₀ne : K₀.Nonempty :=
    ⟨Φ (0, 1), Or.inl ⟨(0, 1), ⟨left_mem_Icc.mpr zero_le_one, by simp⟩, rfl⟩⟩
  -- the minimal boundary distance over that compact set
  obtain ⟨z₀, hz₀K, hz₀min⟩ :=
    hK₀c.exists_isMinOn hK₀ne (continuous_infDist_pt Uᶜ).continuousOn
  set m := infDist z₀ Uᶜ with hm
  have hm0 : 0 < m := (infDist_pos_iff_notMem_closure hc).mp (by
    rw [ho.isClosed_compl.closure_eq]
    exact notMem_compl_iff.mpr (hK₀U hz₀K))
  have hmK : ∀ z ∈ K₀, m ≤ infDist z Uᶜ := fun z hz => hz₀min hz
  have hmC : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  set L := {z : Fin n → ℂ | m ≤ infDist z Uᶜ} with hL
  have hLc : IsClosed L := isClosed_le continuous_const (continuous_infDist_pt _)
  have hLU : L ⊆ U := fun z hz => by
    by_contra hzU
    have : infDist z Uᶜ = 0 := infDist_zero_of_mem hzU
    have hz' : m ≤ infDist z Uᶜ := hz
    linarith
  -- the parameters whose disc lies in `U`
  set W := {t : ℝ | ∀ ζ ∈ closedBall (0 : ℂ) 1, Φ (t, ζ) ∈ U} with hW
  have hdisc : ∀ t ∈ W, ∀ ζ ∈ closedBall (0 : ℂ) 1, Φ (t, ζ) ∈ L := by
    intro t ht ζ hζ
    have han : AnalyticOnNhd ℂ (φ (p t)) (closedBall 0 1) := hφan (p t) (hpI t)
    have hdU : ∀ ζ ∈ closedBall (0 : ℂ) 1, φ (p t) ζ ∈ U := fun ζ hζ => ht ζ hζ
    have hhull := mem_holomorphicHull_of_analytic_disc zero_lt_one han hdU hζ
    have hKt : (φ (p t)) '' sphere 0 1 ⊆ K₀ := by
      rintro _ ⟨ζ', hζ', rfl⟩
      exact Or.inl ⟨(p t, ζ'), ⟨hpI t, hζ'⟩, by simp only [hΦ, hpp]⟩
    have hKtc : IsCompact ((φ (p t)) '' sphere 0 1) :=
      (isCompact_sphere _ _).image_of_continuousOn (han.continuousOn.mono sphere_subset_closedBall)
    have hrad := hU.holomorphic_radius_bound ho hKtc (hKt.trans hK₀U) (q := fun _ => (m : ℂ))
      analyticOnNhd_const (fun z hz => by
        rw [hmC]
        exact (ball_subset_ball (hmK z (hKt hz))).trans
          (by simpa using ball_infDist_subset_compl (x := z) (s := Uᶜ))) _ hhull
    rw [hmC] at hrad
    change m ≤ infDist (φ (p t) ζ) Uᶜ
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hc).mp hlt
    exact hy (hrad (by rwa [mem_ball, dist_comm]))
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have := (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
      (x₀ := t) (P := fun t ζ => Φ (t, ζ) ∈ U) fun ζ hζ =>
        hΦc.continuousAt.preimage_mem_nhds (ho.mem_nhds (ht ζ hζ))
    exact this
  have hWcl : IsClosed W := by
    rw [← closure_subset_iff_isClosed]
    intro t ht ζ hζ
    have hne : NeBot (𝓝[W] t) := mem_closure_iff_nhdsWithin_neBot.mp ht
    have htend : Tendsto (fun t' => Φ (t', ζ)) (𝓝[W] t) (𝓝 (Φ (t, ζ))) :=
      ((hΦc.comp (continuous_id.prodMk continuous_const)).tendsto t).mono_left nhdsWithin_le_nhds
    have hmem : Φ (t, ζ) ∈ closure L :=
      mem_closure_of_tendsto htend (eventually_nhdsWithin_of_forall fun t' ht' => hdisc t' ht' ζ hζ)
    rw [hLc.closure_eq] at hmem
    exact hLU hmem
  have hW0 : (0 : ℝ) ∈ W := by
    intro ζ hζ
    simp only [hΦ, hpid 0 (left_mem_Icc.mpr zero_le_one)]
    exact h0 ζ hζ
  have hWuniv : W = univ := IsClopen.eq_univ (⟨hWcl, hWo⟩ : IsClopen W) ⟨0, hW0⟩
  intro t ht ζ hζ
  have := (hWuniv ▸ mem_univ t : t ∈ W) ζ hζ
  simpa [hΦ, hpid t ht] using this

end HolomorphicContinuity

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Pseudoconvexity pulls back along a continuous linear equivalence. -/
theorem IsPseudoconvex.of_image_equiv {U : Set E} (L : E ≃L[ℂ] F)
    (h : IsPseudoconvex (L '' U)) : IsPseudoconvex U := by
  obtain ⟨ho, φ, hφc, hφp, hφk⟩ := h
  have hU : IsOpen U := by
    have : U = L ⁻¹' (L '' U) := (L.injective.preimage_image U).symm
    rw [this]
    exact ho.preimage L.continuous
  refine ⟨hU, fun z => φ (L z), hφc.comp L.continuous.continuousOn (mapsTo_image L U), ?_,
    fun c => ?_⟩
  · have := hφp.comp_affine (L : E →L[ℂ] F) 0
    simp only [zero_add, ContinuousLinearEquiv.coe_coe] at this
    exact this.mono fun z hz => mem_image_of_mem L hz
  · have heq : {z ∈ U | φ (L z) ≤ c} = L.symm '' {w ∈ L '' U | φ w ≤ c} := by
      ext z
      constructor
      · rintro ⟨hz, hc⟩
        exact ⟨L z, ⟨mem_image_of_mem L hz, hc⟩, L.symm_apply_apply z⟩
      · rintro ⟨w, ⟨hw, hc⟩, rfl⟩
        refine ⟨?_, by simpa using hc⟩
        obtain ⟨z, hz, rfl⟩ := hw
        simpa using hz
    rw [heq]
    exact (hφk c).image L.symm.continuous

/-- The holomorphic continuity principle pulls back along a continuous linear equivalence. -/
theorem SatisfiesHolomorphicContinuityPrinciple.of_image_equiv {U : Set E} (L : E ≃L[ℂ] F)
    (h : SatisfiesHolomorphicContinuityPrinciple (L '' U)) :
    SatisfiesHolomorphicContinuityPrinciple U := by
  intro φ hφc hφa hbd h0 t ht ζ hζ
  have := h (fun t ζ => L (φ t ζ)) (L.continuous.comp hφc)
    (fun t ht => (L.toContinuousLinearMap.analyticOnNhd univ).comp (hφa t ht) (mapsTo_univ _ _))
    (fun t ht ζ hζ => mem_image_of_mem L (hbd t ht ζ hζ))
    (fun ζ hζ => mem_image_of_mem L (h0 ζ hζ)) t ht ζ hζ
  exact L.injective.mem_set_image.mp this

variable [FiniteDimensional ℂ E]

/-- **Domains of holomorphy are pseudoconvex.** The exhaustion is transported from the
coordinate version `IsDomainOfHolomorphy.isPseudoconvex_fin`. -/
theorem IsDomainOfHolomorphy.isPseudoconvex {U : Set E} (hU : IsDomainOfHolomorphy U)
    (ho : IsOpen U) : IsPseudoconvex U := by
  let L := (Module.finBasis ℂ E).equivFunL
  exact IsPseudoconvex.of_image_equiv L ((hU.image_equiv L).isPseudoconvex_fin (L.isOpenMap U ho))

/-- **Domains of holomorphy satisfy the continuity principle for holomorphic discs.** -/
theorem IsDomainOfHolomorphy.satisfiesHolomorphicContinuityPrinciple {U : Set E}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : SatisfiesHolomorphicContinuityPrinciple U := by
  let L := (Module.finBasis ℂ E).equivFunL
  exact SatisfiesHolomorphicContinuityPrinciple.of_image_equiv L
    ((hU.image_equiv L).satisfiesHolomorphicContinuityPrinciple_fin (L.isOpenMap U ho))

/-- Domains of holomorphy satisfy the affine continuity principle. -/
theorem IsDomainOfHolomorphy.satisfiesContinuityPrinciple {U : Set E}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : SatisfiesContinuityPrinciple U :=
  (hU.satisfiesHolomorphicContinuityPrinciple ho).satisfiesContinuityPrinciple

end Transport

section Hartogs

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- **Hartogs convexity** for cylinder figures: whenever a Hartogs cylinder over an open
preconnected base, with disc fibers over a nonempty open part of the base, lies in the set, so
does the filled cylinder. -/
@[expose] def IsHartogsConvex (U : Set (E' × ℂ)) : Prop :=
  ∀ (D D₀ : Set E') (ρ R : ℝ), IsOpen D → IsPreconnected D → IsOpen D₀ → D₀.Nonempty →
    D₀ ⊆ D → 0 ≤ ρ → ρ < R → hartogsCylinder D D₀ ρ R ⊆ U → D ×ˢ ball 0 R ⊆ U

/-- **The continuity principle implies Hartogs convexity ([Fritzsche–Grauert][FritzscheGrauert2002]
II.1.5).** The disc
fibers are slid along a path in the base from the part carrying full discs. -/
theorem SatisfiesContinuityPrinciple.isHartogsConvex {U : Set (E' × ℂ)}
    (h : SatisfiesContinuityPrinciple U) : IsHartogsConvex U := by
  intro D D₀ ρ R hD hDc hD₀ hne hsub hρ hρR hcyl
  rintro ⟨w, ζ₀⟩ ⟨hw, hζ₀⟩
  obtain ⟨w₀, hw₀⟩ := hne
  have hζ₀' : ‖ζ₀‖ < R := mem_ball_zero_iff.mp hζ₀
  obtain ⟨R', hR'₁, hR'₂⟩ := exists_between (max_lt hρR hζ₀')
  have hρR' : ρ < R' := (le_max_left _ _).trans_lt hR'₁
  have hζR' : ‖ζ₀‖ < R' := (le_max_right _ _).trans_lt hR'₁
  have hR'pos : 0 < R' := hρ.trans_lt hρR'
  have hpath : JoinedIn D w₀ w :=
    (hD.isConnected_iff_isPathConnected.mp ⟨⟨w, hw⟩, hDc⟩).joinedIn w₀ (hsub hw₀) w hw
  set γ := hpath.somePath with hγ
  have hγD : ∀ t, γ.extend t ∈ D := fun t => by
    have : γ.extend t ∈ range γ := by
      rw [← Path.extend_range]
      exact mem_range_self t
    obtain ⟨s, hs⟩ := this
    rw [← hs]
    exact hpath.somePath_mem s
  set a : ℝ → E' × ℂ := fun t => (γ.extend t, (0 : ℂ)) with ha
  set b : ℝ → E' × ℂ := fun _ => ((0 : E'), (R' : ℂ)) with hb
  have hpt : ∀ (t : ℝ) (ζ : ℂ), a t + ζ • b t = (γ.extend t, ζ * R') := fun t ζ => by
    simp [ha, hb]
  have hac : Continuous a := (γ.continuous_extend).prodMk continuous_const
  have hbc : Continuous b := continuous_const
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ sphere (0 : ℂ) 1, a t + ζ • b t ∈ U := by
    intro t _ ζ hζ
    rw [hpt]
    apply hcyl
    have hζn : ‖ζ * R'‖ = R' := by
      rw [norm_mul, mem_sphere_zero_iff_norm.mp hζ, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR'pos]
    refine Or.inl ⟨hγD t, ?_, ?_⟩
    · rw [mem_ball_zero_iff, hζn]; exact hR'₂
    · rw [mem_closedBall_zero_iff, hζn]; exact not_le.mpr hρR'
  have h0 : ∀ ζ ∈ closedBall (0 : ℂ) 1, a 0 + ζ • b 0 ∈ U := by
    intro ζ hζ
    rw [hpt]
    apply hcyl
    refine Or.inr ⟨by rw [Path.extend_zero]; exact hw₀, ?_⟩
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR'pos]
    calc ‖ζ‖ * R' ≤ 1 * R' :=
          mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hζ) hR'pos.le
      _ < R := by linarith
  have hfin := h a b hac hbc hbd h0 1 (right_mem_Icc.mpr zero_le_one) (ζ₀ / R') (by
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR'pos, div_le_one hR'pos]
    exact hζR'.le)
  rw [hpt, Path.extend_one, div_mul_cancel₀ _ (by exact_mod_cast hR'pos.ne')] at hfin
  exact hfin

/-- Pseudoconvex sets in a product with `ℂ` are Hartogs convex. -/
theorem IsPseudoconvex.isHartogsConvex {U : Set (E' × ℂ)} (h : IsPseudoconvex U) :
    IsHartogsConvex U :=
  h.satisfiesContinuityPrinciple.isHartogsConvex

end Hartogs

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
