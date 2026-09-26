/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# The local second-order ODE package

Geodesics are second-order integral curves.  This module isolates the ordinary
differential-equation step in a form that can later be instantiated with the
coordinate Christoffel field of the constructed Levi--Civita connection.  It
contains no geometric existence or completeness assumption.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace BonnetMyersEntry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Time-dependent first-order equations

The parallel-transport equation along a prescribed curve has a time-dependent
right-hand side.  Mathlib's local theorem is stated for an autonomous vector
field, so we adjoin the clock coordinate.  The small interval shrink below is
deliberate: it makes the clock-coordinate identity an ordinary consequence of
the derivative equation, rather than an implicit convention about the ODE. -/

structure LocalFirstOrderSolution (f : ℝ → E → E) (t₀ : ℝ) (v₀ : E) where
  curve : ℝ → E
  radius : ℝ
  radius_pos : 0 < radius
  initial : curve t₀ = v₀
  hasDeriv : ∀ t ∈ Ioo (t₀ - radius) (t₀ + radius),
    HasDerivAt curve (f t (curve t)) t

theorem exists_localFirstOrderSolution_of_contDiffAt
    {f : ℝ → E → E} {t₀ : ℝ} {v₀ : E}
    (hf : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ f p.1 p.2) (t₀, v₀)) :
    Nonempty (LocalFirstOrderSolution f t₀ v₀) := by
  let F : ℝ × E → ℝ × E := fun p ↦ (1, f p.1 p.2)
  have hF : ContDiffAt ℝ 1 F (t₀, v₀) := by
    exact contDiffAt_const.prodMk hf
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  let r : ℝ := ε / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have htime : ∀ t ∈ Ioo (t₀ - r) (t₀ + r), (α t).1 = t := by
    have hfst : ∀ t ∈ Icc (t₀ - r) (t₀ + r),
        HasDerivAt (fun s ↦ (α s).1) 1 t := by
      intro t ht
      have htopen : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
        constructor <;> dsimp [r] at ht ⊢ <;> linarith [ht.1, ht.2, hε]
      have h := (hα t htopen).hasFDerivAt.fst.hasDerivAt
      simpa [F] using h
    have hdiff : DifferentiableOn ℝ (fun s ↦ (α s).1 - s)
        (Ioo (t₀ - r) (t₀ + r)) := by
      intro t ht
      have htIcc : t ∈ Icc (t₀ - r) (t₀ + r) :=
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      exact ((hfst t htIcc).sub (hasDerivAt_id' t)).differentiableAt
        |>.differentiableWithinAt
    have hderiv : Set.EqOn (deriv (fun s ↦ (α s).1 - s)) (fun _ ↦ (0 : ℝ))
        (Ioo (t₀ - r) (t₀ + r)) := by
      intro t ht
      have htIcc : t ∈ Icc (t₀ - r) (t₀ + r) :=
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      change deriv ((fun s ↦ (α s).1) - (fun s ↦ s)) t = 0
      rw [((hfst t htIcc).sub (hasDerivAt_id' t)).deriv]
      norm_num
    have hconst : ∀ t ∈ Ioo (t₀ - r) (t₀ + r),
        ((fun s ↦ (α s).1 - s) t₀) = ((fun s ↦ (α s).1 - s) t) := by
      intro t ht
      have ht₀ : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := by
        constructor <;> linarith
      exact isOpen_Ioo.is_const_of_deriv_eq_zero (x := t₀) (y := t)
        isPreconnected_Ioo hdiff hderiv ht₀ ht
    intro t ht
    have hvalue := hconst t ht
    have hα0fst : (α t₀).1 = t₀ := congrArg Prod.fst hα0
    dsimp at hvalue
    nlinarith [hα0fst]
  refine ⟨⟨fun t ↦ (α t).2, r, hr, ?_, ?_⟩⟩
  · simpa [hα0]
  · intro t ht
    have htopen : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
      constructor <;> dsimp [r] at ht ⊢ <;> linarith [ht.1, ht.2, hε]
    have hsecond : HasDerivAt (fun s ↦ (α s).2) (f (α t).1 (α t).2) t := by
      have h := (hα t htopen).hasFDerivAt.snd.hasDerivAt
      simpa [F] using h
    rw [htime t ht] at hsecond
    exact hsecond

/-! ### Linear parallel equations in a fixed model fibre

The coordinate form of parallel transport is a homogeneous linear equation.  We
keep this package separate from the manifold-specific frame bookkeeping: it is
the exact analytic statement needed after a connection coefficient matrix has
been read along a curve. -/

structure LocalLinearTransportSolution (A : ℝ → E →L[ℝ] E) (t₀ : ℝ) (v₀ : E) where
  curve : ℝ → E
  radius : ℝ
  radius_pos : 0 < radius
  initial : curve t₀ = v₀
  hasDeriv : ∀ t ∈ Ioo (t₀ - radius) (t₀ + radius),
    HasDerivAt curve (-(A t) (curve t)) t

theorem exists_localLinearTransportSolution_of_contDiffAt
    {A : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₀ : E}
    (hA : ContDiffAt ℝ 1 A t₀) :
    Nonempty (LocalLinearTransportSolution A t₀ v₀) := by
  have hA' : ContDiffAt ℝ 1
      (fun p : ℝ × E ↦ A p.1) (t₀, v₀) :=
    hA.comp (t₀, v₀) contDiffAt_fst
  have hsystem : ContDiffAt ℝ 1
      (fun p : ℝ × E ↦ -(A p.1) p.2) (t₀, v₀) := by
    simpa only [Pi.neg_apply] using (hA'.clm_apply contDiffAt_snd).neg
  obtain ⟨sol⟩ := exists_localFirstOrderSolution_of_contDiffAt
    (f := fun t v ↦ -(A t) v) (t₀ := t₀) (v₀ := v₀) hsystem
  exact ⟨⟨sol.curve, sol.radius, sol.radius_pos, sol.initial, sol.hasDeriv⟩⟩

namespace LocalLinearTransportSolution

omit [CompleteSpace E] in
/-- Two local solutions of the same linear transport equation with the same
initial time and model vector agree as germs.  The clock is included in the
state before invoking ODE uniqueness, so the proof does not mistake a
time-dependent coefficient for an autonomous equation on the fibre. -/
theorem eventuallyEq_of_same_initial
    {A : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₀ : E}
    (sol₁ sol₂ : LocalLinearTransportSolution A t₀ v₀)
    (hA : ContDiffAt ℝ 1 A t₀) :
    sol₁.curve =ᶠ[𝓝 t₀] sol₂.curve := by
  let G : ℝ × E → ℝ × E := fun p ↦ (1, -(A p.1) p.2)
  have hA' : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ A p.1) (t₀, v₀) :=
    hA.comp (t₀, v₀) contDiffAt_fst
  have hG : ContDiffAt ℝ 1 G (t₀, v₀) := by
    simpa [G] using contDiffAt_const.prodMk (hA'.clm_apply contDiffAt_snd).neg
  obtain ⟨K, S, hS, hK⟩ := hG.exists_lipschitzOnWith
  let p₁ : ℝ → ℝ × E := fun t ↦ (t, sol₁.curve t)
  let p₂ : ℝ → ℝ × E := fun t ↦ (t, sol₂.curve t)
  have hzero₁ : t₀ ∈ Ioo (t₀ - sol₁.radius) (t₀ + sol₁.radius) := by
    constructor <;> linarith [sol₁.radius_pos]
  have hzero₂ : t₀ ∈ Ioo (t₀ - sol₂.radius) (t₀ + sol₂.radius) := by
    constructor <;> linarith [sol₂.radius_pos]
  have hp₁zero : HasDerivAt p₁ (G (p₁ t₀)) t₀ := by
    simpa [p₁, G, sol₁.initial] using
      (hasDerivAt_id' t₀).prodMk (sol₁.hasDeriv t₀ hzero₁)
  have hp₂zero : HasDerivAt p₂ (G (p₂ t₀)) t₀ := by
    simpa [p₂, G, sol₂.initial] using
      (hasDerivAt_id' t₀).prodMk (sol₂.hasDeriv t₀ hzero₂)
  have hp₁initial : p₁ t₀ = (t₀, v₀) := by
    simp [p₁, sol₁.initial]
  have hp₂initial : p₂ t₀ = (t₀, v₀) := by
    simp [p₂, sol₂.initial]
  have hp₁mem : p₁ ⁻¹' S ∈ 𝓝 t₀ := by
    have : S ∈ 𝓝 (p₁ t₀) := by rwa [hp₁initial]
    exact hp₁zero.continuousAt.preimage_mem_nhds this
  have hp₂mem : p₂ ⁻¹' S ∈ 𝓝 t₀ := by
    have : S ∈ 𝓝 (p₂ t₀) := by rwa [hp₂initial]
    exact hp₂zero.continuousAt.preimage_mem_nhds this
  have hinter₁ : Ioo (t₀ - sol₁.radius) (t₀ + sol₁.radius) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds (by linarith [sol₁.radius_pos])
      (by linarith [sol₁.radius_pos])
  have hinter₂ : Ioo (t₀ - sol₂.radius) (t₀ + sol₂.radius) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds (by linarith [sol₂.radius_pos])
      (by linarith [sol₂.radius_pos])
  have hp₁deriv : ∀ᶠ t in 𝓝 t₀, HasDerivAt p₁ (G (p₁ t)) t := by
    filter_upwards [hinter₁] with t ht
    simpa [p₁, G] using (hasDerivAt_id' t).prodMk (sol₁.hasDeriv t ht)
  have hp₂deriv : ∀ᶠ t in 𝓝 t₀, HasDerivAt p₂ (G (p₂ t)) t := by
    filter_upwards [hinter₂] with t ht
    simpa [p₂, G] using (hasDerivAt_id' t).prodMk (sol₂.hasDeriv t ht)
  have hf : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt p₁ (G (p₁ t)) t ∧ p₁ t ∈ S := by
    filter_upwards [hp₁deriv, hp₁mem] with t ht hmem
    exact ⟨ht, hmem⟩
  have hg : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt p₂ (G (p₂ t)) t ∧ p₂ t ∈ S := by
    filter_upwards [hp₂deriv, hp₂mem] with t ht hmem
    exact ⟨ht, hmem⟩
  have hv : ∀ᶠ _t in 𝓝 t₀, LipschitzOnWith K G S :=
    Filter.Eventually.of_forall fun _ ↦ hK
  have hp : p₁ =ᶠ[𝓝 t₀] p₂ := ODE_solution_unique_of_eventually
    (v := fun _ z ↦ G z) (s := fun _ ↦ S)
    (f := p₁) (g := p₂) (t₀ := t₀) hv hf hg
    (hp₁initial.trans hp₂initial.symm)
  filter_upwards [hp] with t ht
  exact congrArg Prod.snd ht

omit [CompleteSpace E] in
/-- Two local linear-transport solutions agree as germs when their initial
data agree and their time-dependent coefficient operators agree as germs.  The
clock is included in the state before invoking ODE uniqueness, so this is a
genuine uniqueness result for a non-autonomous equation. -/
theorem eventuallyEq_of_same_initial_of_eventuallyEq
    {A₁ A₂ : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₀ : E}
    (sol₁ : LocalLinearTransportSolution A₁ t₀ v₀)
    (sol₂ : LocalLinearTransportSolution A₂ t₀ v₀)
    (hA : ContDiffAt ℝ 1 A₁ t₀)
    (hAeq : A₁ =ᶠ[𝓝 t₀] A₂) :
    sol₁.curve =ᶠ[𝓝 t₀] sol₂.curve := by
  let G : ℝ × E → ℝ × E := fun p ↦ (1, -(A₁ p.1) p.2)
  have hA' : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ A₁ p.1) (t₀, v₀) :=
    hA.comp (t₀, v₀) contDiffAt_fst
  have hG : ContDiffAt ℝ 1 G (t₀, v₀) := by
    simpa [G] using contDiffAt_const.prodMk (hA'.clm_apply contDiffAt_snd).neg
  obtain ⟨K, S, hS, hK⟩ := hG.exists_lipschitzOnWith
  let p₁ : ℝ → ℝ × E := fun t ↦ (t, sol₁.curve t)
  let p₂ : ℝ → ℝ × E := fun t ↦ (t, sol₂.curve t)
  have hzero₁ : t₀ ∈ Ioo (t₀ - sol₁.radius) (t₀ + sol₁.radius) := by
    constructor <;> linarith [sol₁.radius_pos]
  have hzero₂ : t₀ ∈ Ioo (t₀ - sol₂.radius) (t₀ + sol₂.radius) := by
    constructor <;> linarith [sol₂.radius_pos]
  have hp₁zero : HasDerivAt p₁ (G (p₁ t₀)) t₀ := by
    simpa [p₁, G, sol₁.initial] using
      (hasDerivAt_id' t₀).prodMk (sol₁.hasDeriv t₀ hzero₁)
  have hp₂zero : HasDerivAt p₂ (G (p₂ t₀)) t₀ := by
    have hAeq0 : A₁ t₀ = A₂ t₀ := hAeq.self_of_nhds
    simpa [p₂, G, sol₂.initial, hAeq0] using
      (hasDerivAt_id' t₀).prodMk (sol₂.hasDeriv t₀ hzero₂)
  have hp₁initial : p₁ t₀ = (t₀, v₀) := by
    simp [p₁, sol₁.initial]
  have hp₂initial : p₂ t₀ = (t₀, v₀) := by
    simp [p₂, sol₂.initial]
  have hp₁mem : p₁ ⁻¹' S ∈ 𝓝 t₀ := by
    have : S ∈ 𝓝 (p₁ t₀) := by rwa [hp₁initial]
    exact hp₁zero.continuousAt.preimage_mem_nhds this
  have hp₂mem : p₂ ⁻¹' S ∈ 𝓝 t₀ := by
    have : S ∈ 𝓝 (p₂ t₀) := by rwa [hp₂initial]
    exact hp₂zero.continuousAt.preimage_mem_nhds this
  have hinter₁ : Ioo (t₀ - sol₁.radius) (t₀ + sol₁.radius) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds (by linarith [sol₁.radius_pos])
      (by linarith [sol₁.radius_pos])
  have hinter₂ : Ioo (t₀ - sol₂.radius) (t₀ + sol₂.radius) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds (by linarith [sol₂.radius_pos])
      (by linarith [sol₂.radius_pos])
  have hp₁deriv : ∀ᶠ t in 𝓝 t₀, HasDerivAt p₁ (G (p₁ t)) t := by
    filter_upwards [hinter₁] with t ht
    simpa [p₁, G] using (hasDerivAt_id' t).prodMk (sol₁.hasDeriv t ht)
  have hp₂deriv : ∀ᶠ t in 𝓝 t₀, HasDerivAt p₂ (G (p₂ t)) t := by
    filter_upwards [hinter₂, hAeq] with t ht hAt
    simpa [p₂, G, hAt] using
      (hasDerivAt_id' t).prodMk (sol₂.hasDeriv t ht)
  have hf : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt p₁ (G (p₁ t)) t ∧ p₁ t ∈ S := by
    filter_upwards [hp₁deriv, hp₁mem] with t ht hmem
    exact ⟨ht, hmem⟩
  have hg : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt p₂ (G (p₂ t)) t ∧ p₂ t ∈ S := by
    filter_upwards [hp₂deriv, hp₂mem] with t ht hmem
    exact ⟨ht, hmem⟩
  have hv : ∀ᶠ _t in 𝓝 t₀, LipschitzOnWith K G S :=
    Filter.Eventually.of_forall fun _ ↦ hK
  have hp : p₁ =ᶠ[𝓝 t₀] p₂ := ODE_solution_unique_of_eventually
    (v := fun _ z ↦ G z) (s := fun _ ↦ S)
    (f := p₁) (g := p₂) (t₀ := t₀) hv hf hg
    (hp₁initial.trans hp₂initial.symm)
  filter_upwards [hp] with t ht
  exact congrArg Prod.snd ht

omit [CompleteSpace E] in
/-- The germ-uniqueness theorem is stable under an explicitly supplied
equality of initial model vectors.  Keeping this transport avoids ad-hoc
dependent casts when a tangent vector has first been reconstructed through a
bundle trivialization. -/
theorem eventuallyEq_of_initial_eq_of_eventuallyEq
    {A₁ A₂ : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₁ v₂ : E}
    (sol₁ : LocalLinearTransportSolution A₁ t₀ v₁)
    (sol₂ : LocalLinearTransportSolution A₂ t₀ v₂)
    (hinit : v₁ = v₂)
    (hA : ContDiffAt ℝ 1 A₁ t₀)
    (hAeq : A₁ =ᶠ[𝓝 t₀] A₂) :
    sol₁.curve =ᶠ[𝓝 t₀] sol₂.curve := by
  subst v₂
  exact eventuallyEq_of_same_initial_of_eventuallyEq sol₁ sol₂ hA hAeq

/-- The sum of two local solutions of the same homogeneous linear equation is
a local solution with the summed initial coefficient.  The radius is shrunk
to the common domain; this is the algebraic input for preserving inner
products of independently transported vectors. -/
def add
    {A : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₁ v₂ : E}
    (sol₁ : LocalLinearTransportSolution A t₀ v₁)
    (sol₂ : LocalLinearTransportSolution A t₀ v₂) :
    LocalLinearTransportSolution A t₀ (v₁ + v₂) where
  curve := fun t ↦ sol₁.curve t + sol₂.curve t
  radius := min sol₁.radius sol₂.radius
  radius_pos := lt_min sol₁.radius_pos sol₂.radius_pos
  initial := by rw [sol₁.initial, sol₂.initial]
  hasDeriv := by
    intro t ht
    have ht₁ : t ∈ Ioo (t₀ - sol₁.radius) (t₀ + sol₁.radius) := by
      have hle : min sol₁.radius sol₂.radius ≤ sol₁.radius := min_le_left _ _
      constructor <;> linarith [ht.1, ht.2]
    have ht₂ : t ∈ Ioo (t₀ - sol₂.radius) (t₀ + sol₂.radius) := by
      have hle : min sol₁.radius sol₂.radius ≤ sol₂.radius := min_le_right _ _
      constructor <;> linarith [ht.1, ht.2]
    change HasDerivAt (sol₁.curve + sol₂.curve)
      (-(A t) ((sol₁.curve + sol₂.curve) t)) t
    simpa only [Pi.add_apply, map_add, neg_add] using
      (sol₁.hasDeriv t ht₁).add (sol₂.hasDeriv t ht₂)

/-- Reverse a local linear-transport solution in time.  The transformed
coefficient is explicit: reversing `w' = -A(t)w` gives
`w' = -(-A(-t))w`.  This is the analytic time-reversal datum needed to turn
forward parallel transport into backward transport without identifying fibres
by convention. -/
def reverse
    {A : ℝ → E →L[ℝ] E} {v₀ : E}
    (sol : LocalLinearTransportSolution A 0 v₀) :
    LocalLinearTransportSolution (fun t ↦ -(A (-t))) 0 v₀ where
  curve := fun t ↦ sol.curve (-t)
  radius := sol.radius
  radius_pos := sol.radius_pos
  initial := by simpa using sol.initial
  hasDeriv := by
    intro t ht
    have ht' : -t ∈ Ioo (0 - sol.radius) (0 + sol.radius) := by
      constructor <;> linarith [ht.1, ht.2]
    change HasDerivAt (sol.curve ∘ Neg.neg)
      (-((-(A (-t))) (sol.curve (-t)))) t
    simpa [Function.comp_def] using
      HasDerivAt.scomp t (sol.hasDeriv (-t) ht') (hasDerivAt_neg t)

/-- Recenter a local linear-transport solution at an interior time.  The new
equation records the translated coefficient function explicitly, so this is
an ODE certificate rather than a notation-level change of parameter. -/
def recenter
    {A : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₀ : E}
    (sol : LocalLinearTransportSolution A t₀ v₀) (τ : ℝ)
    (hτ : τ ∈ Ioo (t₀ - sol.radius) (t₀ + sol.radius)) :
    LocalLinearTransportSolution (fun s ↦ A (τ + s)) 0 (sol.curve τ) where
  curve := fun s ↦ sol.curve (τ + s)
  radius := min (τ - (t₀ - sol.radius)) ((t₀ + sol.radius) - τ)
  radius_pos := by
    apply lt_min <;> linarith [hτ.1, hτ.2]
  initial := by simp
  hasDeriv := by
    intro s hs
    have hleft : min (τ - (t₀ - sol.radius)) ((t₀ + sol.radius) - τ) ≤
        τ - (t₀ - sol.radius) := min_le_left _ _
    have hright : min (τ - (t₀ - sol.radius)) ((t₀ + sol.radius) - τ) ≤
        (t₀ + sol.radius) - τ := min_le_right _ _
    have hinside : τ + s ∈ Ioo (t₀ - sol.radius) (t₀ + sol.radius) := by
      constructor <;> linarith [hs.1, hs.2]
    have hadd : HasDerivAt (fun r : ℝ ↦ τ + r) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add τ
    simpa [Function.comp_def] using
      HasDerivAt.scomp s (sol.hasDeriv (τ + s) hinside) hadd

@[simp] theorem recenter_curve
    {A : ℝ → E →L[ℝ] E} {t₀ : ℝ} {v₀ : E}
    (sol : LocalLinearTransportSolution A t₀ v₀) (τ : ℝ)
    (hτ : τ ∈ Ioo (t₀ - sol.radius) (t₀ + sol.radius)) (s : ℝ) :
    (sol.recenter τ hτ).curve s = sol.curve (τ + s) := rfl

end LocalLinearTransportSolution

/-- The first-order system associated to a second-order equation `x'' = F x x'`. -/
def secondOrderSystem (F : E → E → E) : E × E → E × E :=
  fun z ↦ (z.2, F z.1 z.2)

@[simp] lemma secondOrderSystem_fst (F : E → E → E) (z : E × E) :
    (secondOrderSystem F z).1 = z.2 := rfl

@[simp] lemma secondOrderSystem_snd (F : E → E → E) (z : E × E) :
    (secondOrderSystem F z).2 = F z.1 z.2 := rfl
/-- Two curves solving one autonomous second-order system on the same open
preconnected time domain agree everywhere there when they share one initial
state.  This domain-level form also handles asymmetric time intervals. -/
theorem secondOrder_pair_eqOn_of_same_initial
    {F : E → E → E} {J : Set ℝ} {p₁ p₂ : ℝ → E × E}
    (hJopen : IsOpen J) (hJpre : IsPreconnected J) (hzero : (0 : ℝ) ∈ J)
    (hp₁ : ∀ t ∈ J,
      HasDerivAt p₁ (secondOrderSystem F (p₁ t)) t)
    (hp₂ : ∀ t ∈ J,
      HasDerivAt p₂ (secondOrderSystem F (p₂ t)) t)
    (hF : ∀ t ∈ J,
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (p₁ t))
    (hinitial : p₁ 0 = p₂ 0) :
    Set.EqOn p₁ p₂ J := by
  letI : PreconnectedSpace J := Subtype.preconnectedSpace hJpre
  have hp₁cont : Continuous (fun t : J ↦ p₁ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₁ t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  have hp₂cont : Continuous (fun t : J ↦ p₂ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₂ t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  let S : Set J := {t | p₁ t = p₂ t}
  have hSclosed : IsClosed S := isClosed_eq hp₁cont hp₂cont
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change p₁ t = p₂ t at ht
    obtain ⟨K, U, hU, hLip⟩ := (hF t t.property).exists_lipschitzOnWith
    have hJnhds : J ∈ 𝓝 (t : ℝ) := hJopen.mem_nhds t.property
    have hp₁mem : p₁ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₁ t t.property).continuousAt.preimage_mem_nhds hU
    have hUp₂ : U ∈ 𝓝 (p₂ t) := by simpa only [← ht] using hU
    have hp₂mem : p₂ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₂ t t.property).continuousAt.preimage_mem_nhds hUp₂
    have heq : p₁ =ᶠ[𝓝 (t : ℝ)] p₂ := by
      apply ODE_solution_unique_of_eventually
        (v := fun _ q ↦ secondOrderSystem F q) (s := fun _ ↦ U)
        (K := K)
      · exact Filter.Eventually.of_forall (fun _ ↦ hLip)
      · filter_upwards [hJnhds, hp₁mem] with q hqJ hqU
        exact ⟨hp₁ q hqJ, hqU⟩
      · filter_upwards [hJnhds, hp₂mem] with q hqJ hqU
        exact ⟨hp₂ q hqJ, hqU⟩
      · exact ht
    change {q : J | p₁ q = p₂ q} ∈ 𝓝 t
    exact continuousAt_subtype_val.eventually heq
  let zeroJ : J := ⟨0, hzero⟩
  have hzeroS : zeroJ ∈ S := hinitial
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (⟨hSclosed, hSopen⟩ : IsClopen S) ⟨zeroJ, hzeroS⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : J) ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hmem

/-- A local solution of a second-order equation, recorded on an open interval. -/
structure LocalSecondOrderSolution (F : E → E → E) (x₀ v₀ : E) where
  curve : ℝ → E
  velocity : ℝ → E
  radius : ℝ
  radius_pos : 0 < radius
  initial_curve : curve 0 = x₀
  initial_velocity : velocity 0 = v₀
  curve_hasDeriv : ∀ t ∈ Ioo (-radius) radius,
    HasDerivAt curve (velocity t) t
  velocity_hasDeriv : ∀ t ∈ Ioo (-radius) radius,
    HasDerivAt velocity (F (curve t) (velocity t)) t

namespace LocalSecondOrderSolution

variable {F : E → E → E} {x₀ v₀ : E}

lemma continuousOn_curve (sol : LocalSecondOrderSolution F x₀ v₀) :
    ContinuousOn sol.curve (Ioo (-sol.radius) sol.radius) := by
  intro t ht
  exact (sol.curve_hasDeriv t ht).continuousAt.continuousWithinAt

lemma continuousOn_velocity (sol : LocalSecondOrderSolution F x₀ v₀) :
    ContinuousOn sol.velocity (Ioo (-sol.radius) sol.radius) := by
  intro t ht
  exact (sol.velocity_hasDeriv t ht).continuousAt.continuousWithinAt

lemma contDiffAt_curve (sol : LocalSecondOrderSolution F x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    ContDiffAt ℝ 1 sol.curve t := by
  rw [contDiffAt_one_iff]
  refine ⟨fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity s),
    Ioo (-sol.radius) sol.radius, isOpen_Ioo.mem_nhds ht, ?_, ?_⟩
  · intro s hs
    have hvel : ContinuousAt sol.velocity s :=
      (sol.velocity_hasDeriv s hs).continuousAt
    have hspan : ContinuousAt
        (fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v)
        (sol.velocity s) :=
      by
        have hglobal : Continuous
            (fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) := by
          change Continuous
            (fun v : E ↦ ContinuousLinearMap.toSpanSingletonCLE
              (𝕜 := ℝ) (E := E) v)
          exact (ContinuousLinearMap.toSpanSingletonCLE
            (𝕜 := ℝ) (E := E)).continuous
        exact hglobal.continuousAt
    have hcomp : ContinuousAt
        (fun r : ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity r)) s :=
      ContinuousAt.comp' (f := sol.velocity)
        (g := fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) hspan hvel
    exact hcomp.continuousWithinAt
  · intro s hs
    exact (sol.curve_hasDeriv s hs).hasFDerivAt

lemma contDiffAt_velocity (sol : LocalSecondOrderSolution F x₀ v₀)
    (hF : ContDiff ℝ 1 (fun z : E × E ↦ secondOrderSystem F z))
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    ContDiffAt ℝ 1 sol.velocity t := by
  have hFcont : Continuous (fun z : E × E ↦ F z.1 z.2) := by
    have hsys : Continuous (secondOrderSystem F) := hF.continuous
    change Continuous (fun z : E × E ↦ (secondOrderSystem F z).2)
    exact continuous_snd.comp hsys
  have hpair : ContinuousOn (fun s ↦ (sol.curve s, sol.velocity s))
      (Ioo (-sol.radius) sol.radius) :=
    ContinuousOn.prodMk sol.continuousOn_curve sol.continuousOn_velocity
  rw [contDiffAt_one_iff]
  refine ⟨fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (F (sol.curve s) (sol.velocity s)),
    Ioo (-sol.radius) sol.radius, isOpen_Ioo.mem_nhds ht, ?_, ?_⟩
  · intro s hs
    have hF_s : ContinuousAt (fun r ↦ F (sol.curve r) (sol.velocity r)) s :=
      hFcont.continuousAt.comp₂
        (sol.curve_hasDeriv s hs).continuousAt
        (sol.velocity_hasDeriv s hs).continuousAt
    have hspan : ContinuousAt
        (fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v)
        (F (sol.curve s) (sol.velocity s)) :=
      by
        have hglobal : Continuous
            (fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) := by
          change Continuous
            (fun v : E ↦ ContinuousLinearMap.toSpanSingletonCLE
              (𝕜 := ℝ) (E := E) v)
          exact (ContinuousLinearMap.toSpanSingletonCLE
            (𝕜 := ℝ) (E := E)).continuous
        exact hglobal.continuousAt
    have hcomp : ContinuousAt
        (fun r : ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ
          (F (sol.curve r) (sol.velocity r))) s :=
      ContinuousAt.comp' (f := fun r : ℝ ↦ F (sol.curve r) (sol.velocity r))
        (g := fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) hspan hF_s
    exact hcomp.continuousWithinAt
  · intro s hs
    exact (sol.velocity_hasDeriv s hs).hasFDerivAt

lemma contDiffAt_velocity_of_contDiffAt
    (sol : LocalSecondOrderSolution F x₀ v₀)
    (hF : ContDiffAt ℝ 1
      (fun z : E × E ↦ secondOrderSystem F z) (x₀, v₀)) :
    ContDiffAt ℝ 1 sol.velocity 0 := by
  obtain ⟨U, hU, hUdiff⟩ := hF.contDiffOn
    (m := (1 : WithTop ℕ∞)) (n := (1 : WithTop ℕ∞)) le_rfl
      (by simp)
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hpair : ContinuousAt
      (fun s ↦ (sol.curve s, sol.velocity s)) 0 := by
    exact (sol.curve_hasDeriv 0 hzero).continuousAt.prodMk
      (sol.velocity_hasDeriv 0 hzero).continuousAt
  have hpair0 : (sol.curve 0, sol.velocity 0) = (x₀, v₀) := by
    simp [sol.initial_curve, sol.initial_velocity]
  have hpre : (fun s ↦ (sol.curve s, sol.velocity s)) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    have hU0 : U ∈ 𝓝 (sol.curve 0, sol.velocity 0) := by
      simpa [hpair0] using hU
    exact hpair.preimage_mem_nhds hU0
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp hpre
  let S : Set ℝ := W ∩ Ioo (-sol.radius) sol.radius
  have hSopen : IsOpen S := hWopen.inter isOpen_Ioo
  have hSzero : (0 : ℝ) ∈ S := ⟨hWzero, hzero⟩
  have hSdom : S ⊆ Ioo (-sol.radius) sol.radius := inter_subset_right
  have hSpre : (fun s ↦ (sol.curve s, sol.velocity s)) ⁻¹' U ⊇ S := by
    intro s hs
    exact hWsub hs.1
  have hpairOn : ContinuousOn
      (fun s ↦ (sol.curve s, sol.velocity s)) S := by
    exact ContinuousOn.prodMk
      (fun s hs ↦ (sol.curve_hasDeriv s (hSdom hs)).continuousAt.continuousWithinAt)
      (fun s hs ↦ (sol.velocity_hasDeriv s (hSdom hs)).continuousAt.continuousWithinAt)
  have hsystemOn : ContinuousOn
      (fun s ↦ secondOrderSystem F (sol.curve s, sol.velocity s)) S := by
    apply hUdiff.continuousOn.comp' hpairOn
    exact hSpre
  have hforceOn : ContinuousOn
      (fun s ↦ F (sol.curve s) (sol.velocity s)) S := by
    change ContinuousOn
      (fun s ↦ (secondOrderSystem F (sol.curve s, sol.velocity s)).2) S
    exact continuous_snd.comp_continuousOn hsystemOn
  have hspan : Continuous
      (fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) := by
    change Continuous
      (fun v : E ↦ ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := E) v)
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := E)).continuous
  rw [contDiffAt_one_iff]
  refine ⟨fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (F (sol.curve s) (sol.velocity s)), S,
    hSopen.mem_nhds hSzero, ?_, ?_⟩
  · change ContinuousOn
      ((fun v : E ↦ ContinuousLinearMap.toSpanSingleton ℝ v) ∘
        (fun s ↦ F (sol.curve s) (sol.velocity s))) S
    exact hspan.comp_continuousOn hforceOn
  · intro s hs
    exact (sol.velocity_hasDeriv s (hSdom hs)).hasFDerivAt

/-- The position--velocity pair of an ordinary second-order solution solves
the associated first-order system. -/
lemma pair_hasDerivAt (sol : LocalSecondOrderSolution F x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    HasDerivAt (fun s ↦ (sol.curve s, sol.velocity s))
      (secondOrderSystem F (sol.curve t, sol.velocity t)) t := by
  simpa [secondOrderSystem] using
    (sol.curve_hasDeriv t ht).prodMk (sol.velocity_hasDeriv t ht)
/-- Two ordinary solutions of the same autonomous second-order equation with
the same initial data agree on their whole common open interval, provided the
vector field is locally `C¹` along the first solution. -/
theorem pair_eqOn_common_interval_of_same_initial
    (sol₁ sol₂ : LocalSecondOrderSolution F x₀ v₀)
    (hF : ∀ t ∈ Ioo (-(min sol₁.radius sol₂.radius))
        (min sol₁.radius sol₂.radius),
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q)
        (sol₁.curve t, sol₁.velocity t)) :
    Set.EqOn (fun t ↦ (sol₁.curve t, sol₁.velocity t))
      (fun t ↦ (sol₂.curve t, sol₂.velocity t))
      (Ioo (-(min sol₁.radius sol₂.radius))
        (min sol₁.radius sol₂.radius)) := by
  let R : ℝ := min sol₁.radius sol₂.radius
  let J : Set ℝ := Ioo (-R) R
  let p₁ : ℝ → E × E := fun t ↦ (sol₁.curve t, sol₁.velocity t)
  let p₂ : ℝ → E × E := fun t ↦ (sol₂.curve t, sol₂.velocity t)
  have hRpos : 0 < R := lt_min sol₁.radius_pos sol₂.radius_pos
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  letI : PreconnectedSpace J := Subtype.preconnectedSpace hJpre
  have hJ₁ : J ⊆ Ioo (-sol₁.radius) sol₁.radius := by
    intro t ht
    dsimp [J, R] at ht
    have hle : min sol₁.radius sol₂.radius ≤ sol₁.radius := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hJ₂ : J ⊆ Ioo (-sol₂.radius) sol₂.radius := by
    intro t ht
    dsimp [J, R] at ht
    have hle : min sol₁.radius sol₂.radius ≤ sol₂.radius := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hp₁deriv (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₁ (secondOrderSystem F (p₁ t)) t := by
    simpa [p₁] using sol₁.pair_hasDerivAt (hJ₁ ht)
  have hp₂deriv (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₂ (secondOrderSystem F (p₂ t)) t := by
    simpa [p₂] using sol₂.pair_hasDerivAt (hJ₂ ht)
  have hp₁cont : Continuous (fun t : J ↦ p₁ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₁deriv t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  have hp₂cont : Continuous (fun t : J ↦ p₂ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₂deriv t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  let S : Set J := {t | p₁ t = p₂ t}
  have hSclosed : IsClosed S := isClosed_eq hp₁cont hp₂cont
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change p₁ t = p₂ t at ht
    have hFt : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (p₁ t) := by
      simpa [J, R, p₁] using hF t t.property
    obtain ⟨K, U, hU, hLip⟩ := hFt.exists_lipschitzOnWith
    have hJnhds : J ∈ 𝓝 (t : ℝ) := hJopen.mem_nhds t.property
    have hp₁mem : p₁ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₁deriv t t.property).continuousAt.preimage_mem_nhds hU
    have hUp₂ : U ∈ 𝓝 (p₂ t) := by simpa only [← ht] using hU
    have hp₂mem : p₂ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₂deriv t t.property).continuousAt.preimage_mem_nhds hUp₂
    have heq : p₁ =ᶠ[𝓝 (t : ℝ)] p₂ := by
      apply ODE_solution_unique_of_eventually
        (v := fun _ q ↦ secondOrderSystem F q) (s := fun _ ↦ U)
        (K := K)
      · exact Filter.Eventually.of_forall (fun _ ↦ hLip)
      · filter_upwards [hJnhds, hp₁mem] with q hqJ hqU
        exact ⟨hp₁deriv q hqJ, hqU⟩
      · filter_upwards [hJnhds, hp₂mem] with q hqJ hqU
        exact ⟨hp₂deriv q hqJ, hqU⟩
      · exact ht
    change {q : J | p₁ q = p₂ q} ∈ 𝓝 t
    exact continuousAt_subtype_val.eventually heq
  have hzeroJ : (0 : ℝ) ∈ J := by
    dsimp [J]
    exact ⟨neg_lt_zero.mpr hRpos, hRpos⟩
  let zeroJ : J := ⟨0, hzeroJ⟩
  have hzeroS : zeroJ ∈ S := by
    change p₁ 0 = p₂ 0
    simp [p₁, p₂, sol₁.initial_curve, sol₁.initial_velocity,
      sol₂.initial_curve, sol₂.initial_velocity]
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (⟨hSclosed, hSopen⟩ : IsClopen S) ⟨zeroJ, hzeroS⟩
  intro t ht
  have htJ : t ∈ J := by simpa [J, R] using ht
  have hmem : (⟨t, htJ⟩ : J) ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hmem

end LocalSecondOrderSolution

theorem exists_localSecondOrderSolution_of_contDiffAt
    {F : E → E → E} {x₀ v₀ : E}
    (hF : ContDiffAt ℝ 1 (fun z : E × E ↦ secondOrderSystem F z) (x₀, v₀)) :
    Nonempty (LocalSecondOrderSolution F x₀ v₀) := by
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  let x : ℝ → E := fun t ↦ (α t).1
  let v : ℝ → E := fun t ↦ (α t).2
  refine ⟨⟨x, v, ε, hε, ?_, ?_, ?_, ?_⟩⟩
  · simpa [x, hα0]
  · simpa [v, hα0]
  · intro t ht
    have h : HasDerivAt (fun s ↦ (α s).1)
        ((secondOrderSystem F (α t)).1) t :=
      by
        convert (hα t (by simpa using ht)).hasFDerivAt.fst.hasDerivAt using 1 <;>
          simp [ContinuousLinearMap.compSL_apply,
            ContinuousLinearMap.toSpanSingleton_apply]
    simpa [x, v, secondOrderSystem] using h
  · intro t ht
    have h : HasDerivAt (fun s ↦ (α s).2)
        ((secondOrderSystem F (α t)).2) t :=
      by
        convert (hα t (by simpa using ht)).hasFDerivAt.snd.hasDerivAt using 1 <;>
          simp [ContinuousLinearMap.compSL_apply,
            ContinuousLinearMap.toSpanSingleton_apply]
    simpa [x, v, secondOrderSystem] using h

theorem exists_localSecondOrderSolution {F : E → E → E} {x₀ v₀ : E}
    (hF : ContDiff ℝ 1 (fun z : E × E ↦ secondOrderSystem F z)) :
    Nonempty (LocalSecondOrderSolution F x₀ v₀) :=
  exists_localSecondOrderSolution_of_contDiffAt hF.contDiffAt

end BonnetMyersEntry

namespace BonnetMyersEntry

open Manifold
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]

/-- A coordinate solution whose image stays in the target of one extended chart.

This is the small chart-level bridge between the ordinary ODE theorem and a
curve on a boundaryless manifold.  The target-membership field is explicit:
later geometric arguments may therefore use the chart inverse without an
unstated domain convention.
-/
structure LocalChartSecondOrderSolution (I : ModelWithCorners ℝ E H)
    (F : E → E → E) (x₀ : M) (v₀ : E) where
  coordinate : ℝ → E
  velocity : ℝ → E
  radius : ℝ
  radius_pos : 0 < radius
  coordinate_initial : coordinate 0 = extChartAt I x₀ x₀
  velocity_initial : velocity 0 = v₀
  coordinate_hasDeriv : ∀ t ∈ Ioo (-radius) radius,
    HasDerivAt coordinate (velocity t) t
  velocity_hasDeriv : ∀ t ∈ Ioo (-radius) radius,
    HasDerivAt velocity (F (coordinate t) (velocity t)) t
  coordinate_mem_target : ∀ t ∈ Ioo (-radius) radius,
    coordinate t ∈ (extChartAt I x₀).target

theorem exists_localChartSecondOrderSolution_of_contDiffAt
    {F : E → E → E} {x₀ : M} {v₀ : E}
    (hF : ContDiffAt ℝ 1 (fun z : E × E ↦ secondOrderSystem F z)
      (extChartAt I x₀ x₀, v₀)) :
    Nonempty (LocalChartSecondOrderSolution I F x₀ v₀) := by
  obtain ⟨sol⟩ := exists_localSecondOrderSolution_of_contDiffAt (F := F)
    (x₀ := extChartAt I x₀ x₀) (v₀ := v₀) hF
  let e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds (mem_extChartAt_target (I := I) x₀)
  have hcurve0 : sol.curve 0 = e x₀ := by
    simpa [e] using sol.initial_curve
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcont : ContinuousAt sol.curve 0 :=
    (sol.curve_hasDeriv 0 hzero).continuousAt
  have hpre : sol.curve ⁻¹' e.target ∈ 𝓝 (0 : ℝ) := by
    rw [← hcurve0] at htarget
    exact hcont.preimage_mem_nhds htarget
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min sol.radius (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min sol.radius_pos (by linarith)
  refine ⟨⟨sol.curve, sol.velocity, r, hr, sol.initial_curve,
    sol.initial_velocity, ?_, ?_, ?_⟩⟩
  · intro t ht
    apply sol.curve_hasDeriv t
    constructor
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.1]
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.2]
  · intro t ht
    apply sol.velocity_hasDeriv t
    constructor
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.1]
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.2]
  · intro t ht
    apply hδsub
    rw [Metric.mem_ball]
    have hmin : r ≤ δ / 2 := min_le_right _ _
    have habs : |t| < r := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have habsδ : |t - 0| < δ := by
      rw [sub_zero]
      linarith
    exact habsδ

theorem exists_localChartSecondOrderSolution {F : E → E → E} {x₀ : M} {v₀ : E}
    (hF : ContDiff ℝ 1 (fun z : E × E ↦ secondOrderSystem F z)) :
    Nonempty (LocalChartSecondOrderSolution I F x₀ v₀) := by
  obtain ⟨sol⟩ := exists_localSecondOrderSolution (F := F)
    (x₀ := extChartAt I x₀ x₀) (v₀ := v₀) hF
  let e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds (mem_extChartAt_target (I := I) x₀)
  have hcurve0 : sol.curve 0 = e x₀ := by
    simpa [e] using sol.initial_curve
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcont : ContinuousAt sol.curve 0 :=
    (sol.curve_hasDeriv 0 hzero).continuousAt
  have hpre : sol.curve ⁻¹' e.target ∈ 𝓝 (0 : ℝ) := by
    rw [← hcurve0] at htarget
    exact hcont.preimage_mem_nhds htarget
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min sol.radius (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min sol.radius_pos (by linarith)
  refine ⟨⟨sol.curve, sol.velocity, r, hr, sol.initial_curve,
    sol.initial_velocity, ?_, ?_, ?_⟩⟩
  · intro t ht
    apply sol.curve_hasDeriv t
    constructor
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.1]
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.2]
  · intro t ht
    apply sol.velocity_hasDeriv t
    constructor
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.1]
    · have hmin : r ≤ sol.radius := min_le_left _ _
      linarith [ht.2]
  · intro t ht
    apply hδsub
    rw [Metric.mem_ball]
    have hmin : r ≤ δ / 2 := min_le_right _ _
    have habs : |t| < r := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have habsδ : |t - 0| < δ := by
      rw [sub_zero]
      linarith
    exact habsδ

namespace LocalChartSecondOrderSolution

variable {F : E → E → E} {x₀ : M} {v₀ : E}

/-- The manifold-valued curve obtained by applying the inverse of the fixed
extended chart to the coordinate solution. -/
def curve (sol : LocalChartSecondOrderSolution I F x₀ v₀) : ℝ → M :=
  (extChartAt I x₀).symm ∘ sol.coordinate

lemma curve_eq_chart (sol : LocalChartSecondOrderSolution I F x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    (extChartAt I x₀) (curve sol t) = sol.coordinate t := by
  rw [curve, Function.comp_apply, PartialEquiv.right_inv]
  exact sol.coordinate_mem_target t ht

lemma curve_initial (sol : LocalChartSecondOrderSolution I F x₀ v₀) :
    curve sol 0 = x₀ := by
  rw [curve, Function.comp_apply, sol.coordinate_initial]
  exact (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)

lemma curve_hasMFDerivAt (sol : LocalChartSecondOrderSolution I F x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I (curve sol) t
      ((mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t)) := by
  have hcoord : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) sol.coordinate t
      (ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t)) := by
    exact (sol.coordinate_hasDeriv t ht).hasFDerivAt.hasMFDerivAt
  have hsymmWithin : HasMFDerivWithinAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm
      (range (I : H → E)) (sol.coordinate t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t)) := by
    exact (mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := x₀) (z := sol.coordinate t)
      (sol.coordinate_mem_target t ht)).hasMFDerivWithinAt
  have hsymm : HasMFDerivAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm (sol.coordinate t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t)) := by
    apply hsymmWithin.hasMFDerivAt
    rw [I.range_eq_univ]
    exact Filter.univ_mem
  change HasMFDerivAt (𝓘(ℝ, ℝ)) I
    ((extChartAt I x₀).symm ∘ sol.coordinate) t
      ((mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t))
  exact hsymm.comp t hcoord

lemma pair_hasDerivAt (sol : LocalChartSecondOrderSolution I F x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    HasDerivAt (fun s ↦ (sol.coordinate s, sol.velocity s))
      (secondOrderSystem F (sol.coordinate t, sol.velocity t)) t := by
  simpa [secondOrderSystem] using
    (sol.coordinate_hasDeriv t ht).prodMk (sol.velocity_hasDeriv t ht)

/-- Two local chart solutions of the same second-order equation with the same
initial data agree on a neighborhood of the initial time.  The proof uses the
actual local Lipschitz consequence of `ContDiffAt`; no global uniqueness or
extension convention is hidden in the statement. -/
theorem eventuallyEq_of_same_initial
    (sol₁ sol₂ : LocalChartSecondOrderSolution I F x₀ v₀)
    (hF : ContDiffAt ℝ 1
      (fun z : E × E ↦ secondOrderSystem F z)
      (extChartAt I x₀ x₀, v₀)) :
    (fun t ↦ (sol₁.coordinate t, sol₁.velocity t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ (sol₂.coordinate t, sol₂.velocity t)) := by
  obtain ⟨K, S, hS, hK⟩ := hF.exists_lipschitzOnWith
  let pair₁ : ℝ → E × E := fun t ↦ (sol₁.coordinate t, sol₁.velocity t)
  let pair₂ : ℝ → E × E := fun t ↦ (sol₂.coordinate t, sol₂.velocity t)
  have hzero₁ : (0 : ℝ) ∈ Ioo (-sol₁.radius) sol₁.radius := by
    constructor <;> linarith [sol₁.radius_pos]
  have hzero₂ : (0 : ℝ) ∈ Ioo (-sol₂.radius) sol₂.radius := by
    constructor <;> linarith [sol₂.radius_pos]
  have hpair₁deriv : HasDerivAt pair₁
      (secondOrderSystem F (pair₁ 0)) 0 := by
    simpa [pair₁] using pair_hasDerivAt (F := F) sol₁ hzero₁
  have hpair₂deriv : HasDerivAt pair₂
      (secondOrderSystem F (pair₂ 0)) 0 := by
    simpa [pair₂] using pair_hasDerivAt (F := F) sol₂ hzero₂
  have hp₁ : pair₁ 0 = (extChartAt I x₀ x₀, v₀) := by
    simp [pair₁, sol₁.coordinate_initial, sol₁.velocity_initial]
  have hp₂ : pair₂ 0 = (extChartAt I x₀ x₀, v₀) := by
    simp [pair₂, sol₂.coordinate_initial, sol₂.velocity_initial]
  have hS₁ : S ∈ 𝓝 (pair₁ 0) := by
    rw [hp₁]
    exact hS
  have hS₂ : S ∈ 𝓝 (pair₂ 0) := by
    rw [hp₂]
    exact hS
  have hpair₁mem : pair₁ ⁻¹' S ∈ 𝓝 (0 : ℝ) :=
    hpair₁deriv.continuousAt.preimage_mem_nhds hS₁
  have hpair₂mem : pair₂ ⁻¹' S ∈ 𝓝 (0 : ℝ) :=
    hpair₂deriv.continuousAt.preimage_mem_nhds hS₂
  have hinter₁ : Ioo (-sol₁.radius) sol₁.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [sol₁.radius_pos])
      (by linarith [sol₁.radius_pos])
  have hinter₂ : Ioo (-sol₂.radius) sol₂.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [sol₂.radius_pos])
      (by linarith [sol₂.radius_pos])
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt pair₁ (secondOrderSystem F (pair₁ t)) t ∧ pair₁ t ∈ S := by
    filter_upwards [hinter₁, hpair₁mem] with t ht hmem
    exact ⟨by simpa [pair₁] using pair_hasDerivAt (F := F) sol₁ ht, hmem⟩
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt pair₂ (secondOrderSystem F (pair₂ t)) t ∧ pair₂ t ∈ S := by
    filter_upwards [hinter₂, hpair₂mem] with t ht hmem
    exact ⟨by simpa [pair₂] using pair_hasDerivAt (F := F) sol₂ ht, hmem⟩
  have hv : ∀ᶠ t in 𝓝 (0 : ℝ),
      LipschitzOnWith K (secondOrderSystem F) S :=
    Filter.Eventually.of_forall (fun _ ↦ hK)
  have hinitial : pair₁ 0 = pair₂ 0 := by
    simp [pair₁, pair₂, sol₁.coordinate_initial, sol₁.velocity_initial,
      sol₂.coordinate_initial, sol₂.velocity_initial]
  exact ODE_solution_unique_of_eventually
    (v := fun _ z ↦ secondOrderSystem F z) (s := fun _ ↦ S)
    (f := pair₁) (g := pair₂) (t₀ := 0) hv hf hg hinitial
/-- Two solutions of the same autonomous second-order equation with the same
initial data agree on their whole common open interval, provided the vector
field is locally `C¹` along the first solution.  This is the interval-level
form of ODE uniqueness needed to identify the endpoints of compatible local
geodesic pieces, rather than merely their initial germs. -/
theorem pair_eqOn_common_interval_of_same_initial
    (sol₁ sol₂ : LocalChartSecondOrderSolution I F x₀ v₀)
    (hF : ∀ t ∈ Ioo (-(min sol₁.radius sol₂.radius))
        (min sol₁.radius sol₂.radius),
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q)
        (sol₁.coordinate t, sol₁.velocity t)) :
    Set.EqOn (fun t ↦ (sol₁.coordinate t, sol₁.velocity t))
      (fun t ↦ (sol₂.coordinate t, sol₂.velocity t))
      (Ioo (-(min sol₁.radius sol₂.radius))
        (min sol₁.radius sol₂.radius)) := by
  let R : ℝ := min sol₁.radius sol₂.radius
  let J : Set ℝ := Ioo (-R) R
  let p₁ : ℝ → E × E := fun t ↦ (sol₁.coordinate t, sol₁.velocity t)
  let p₂ : ℝ → E × E := fun t ↦ (sol₂.coordinate t, sol₂.velocity t)
  have hRpos : 0 < R := lt_min sol₁.radius_pos sol₂.radius_pos
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  letI : PreconnectedSpace J := Subtype.preconnectedSpace hJpre
  have hJ₁ : J ⊆ Ioo (-sol₁.radius) sol₁.radius := by
    intro t ht
    dsimp [J, R] at ht
    have hle : min sol₁.radius sol₂.radius ≤ sol₁.radius := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hJ₂ : J ⊆ Ioo (-sol₂.radius) sol₂.radius := by
    intro t ht
    dsimp [J, R] at ht
    have hle : min sol₁.radius sol₂.radius ≤ sol₂.radius := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hp₁deriv (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₁ (secondOrderSystem F (p₁ t)) t := by
    simpa [p₁] using sol₁.pair_hasDerivAt (hJ₁ ht)
  have hp₂deriv (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₂ (secondOrderSystem F (p₂ t)) t := by
    simpa [p₂] using sol₂.pair_hasDerivAt (hJ₂ ht)
  have hp₁cont : Continuous (fun t : J ↦ p₁ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₁deriv t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  have hp₂cont : Continuous (fun t : J ↦ p₂ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hp₂deriv t t.property).continuousAt.comp_of_eq
      continuousAt_subtype_val rfl
  let S : Set J := {t | p₁ t = p₂ t}
  have hSclosed : IsClosed S := isClosed_eq hp₁cont hp₂cont
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change p₁ t = p₂ t at ht
    have hFt : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (p₁ t) := by
      simpa [J, R, p₁] using hF t t.property
    obtain ⟨K, U, hU, hLip⟩ := hFt.exists_lipschitzOnWith
    have hJnhds : J ∈ 𝓝 (t : ℝ) := hJopen.mem_nhds t.property
    have hp₁mem : p₁ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₁deriv t t.property).continuousAt.preimage_mem_nhds hU
    have hUp₂ : U ∈ 𝓝 (p₂ t) := by simpa only [← ht] using hU
    have hp₂mem : p₂ ⁻¹' U ∈ 𝓝 (t : ℝ) :=
      (hp₂deriv t t.property).continuousAt.preimage_mem_nhds hUp₂
    have heq : p₁ =ᶠ[𝓝 (t : ℝ)] p₂ := by
      apply ODE_solution_unique_of_eventually
        (v := fun _ q ↦ secondOrderSystem F q) (s := fun _ ↦ U)
        (K := K)
      · exact Filter.Eventually.of_forall (fun _ ↦ hLip)
      · filter_upwards [hJnhds, hp₁mem] with q hqJ hqU
        exact ⟨hp₁deriv q hqJ, hqU⟩
      · filter_upwards [hJnhds, hp₂mem] with q hqJ hqU
        exact ⟨hp₂deriv q hqJ, hqU⟩
      · exact ht
    change {q : J | p₁ q = p₂ q} ∈ 𝓝 t
    exact continuousAt_subtype_val.eventually heq
  have hzeroJ : (0 : ℝ) ∈ J := by
    dsimp [J]
    exact ⟨neg_lt_zero.mpr hRpos, hRpos⟩
  let zeroJ : J := ⟨0, hzeroJ⟩
  have hzeroS : zeroJ ∈ S := by
    change p₁ 0 = p₂ 0
    simp [p₁, p₂, sol₁.coordinate_initial, sol₁.velocity_initial,
      sol₂.coordinate_initial, sol₂.velocity_initial]
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (⟨hSclosed, hSopen⟩ : IsClopen S) ⟨zeroJ, hzeroS⟩
  intro t ht
  have htJ : t ∈ J := by simpa [J, R] using ht
  have hmem : (⟨t, htJ⟩ : J) ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hmem

end LocalChartSecondOrderSolution

end BonnetMyersEntry
