/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Spherical

/-!
# Normal sequences and the Julia set

Normality is defined for sequences of maps from a topological space to a uniform space.
Every subsequence must have a further subsequence that converges locally uniformly on the
specified domain, using Mathlib's `TendstoLocallyUniformly` directly. Neither holomorphy nor
any special value at infinity is built into this general definition.

For the exponential, the codomain is the Riemann sphere and the domain remains the complex
plane. Classical complex analysis describes which locally uniform spherical limits of
holomorphic or meromorphic functions can occur. That characterization is unnecessary here:
`LeanPool.ExpChaotic.Spherical` directly rules out every possible sphere-valued limit.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

@[expose] public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- A sequence of maps is normal on `U` if each subsequence has a further subsequence
converging locally uniformly on the subtype `U` to some function `U → β`.

This definition makes sense for any topological domain and uniform codomain. It does not
require `U` to be open; openness is imposed when defining a local Fatou set. -/
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop

/-- The Fatou set consists of points having an open neighbourhood on which the
sphere-valued iterates form a normal sequence. The map `f` itself is defined only on `ℂ`. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    IsNormalSequenceOn (fun n z => ((f^[n]) z : RiemannSphere)) U}

/-- The Julia set, defined as the complement of the Fatou set. -/
def juliaSet (f : ℂ → ℂ) : Set ℂ := (fatouSet f)ᶜ

/-! ## Restriction -/

/-- Normality is inherited by subsets. A limit on `U` restricts along the continuous
inclusion `V → U`. -/
theorem IsNormalSequenceOn.mono {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {U V : Set α} (h : IsNormalSequenceOn F U) (hVU : V ⊆ U) :
    IsNormalSequenceOn F V := by
  intro φ hφ
  let i : V → U := fun z => ⟨z, hVU z.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  obtain ⟨ψ, hψ, g, hg⟩ := h φ hφ
  exact ⟨ψ, hψ, g ∘ i, hg.comp i hi⟩

/-- The local Fatou-set definition can be tested on open disks. -/
theorem mem_fatouSet_iff_exists_ball {f : ℂ → ℂ} {z : ℂ} :
    z ∈ fatouSet f ↔ ∃ r : ℝ, 0 < r ∧
      IsNormalSequenceOn (fun n w => ((f^[n]) w : RiemannSphere)) (ball z r) := by
  constructor
  · rintro ⟨U, hU, hz, hnormal⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨r, hr, hnormal.mono hball⟩
  · rintro ⟨r, hr, hnormal⟩
    exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hnormal⟩

/-! ## Non-normality and Misiurewicz's theorem -/

/-- The sphere-valued exponential iterates are not normal on a nonempty open set. -/
theorem not_isNormalSequenceOn_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ IsNormalSequenceOn sphericalExpIterate U := by
  intro hnormal
  obtain ⟨ψ, hψ, g, hg⟩ := hnormal id strictMono_id
  exact not_tendstoLocallyUniformly_expIterate_comp
    (q := fun w : ℂ => (w : RiemannSphere)) OnePoint.continuous_coe
    (fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)) hU hUne hψ g hg

/-- Misiurewicz's theorem in Fatou-set form: the sphere-valued iterates are normal
on no neighbourhood. -/
theorem misiurewicz_fatouSet_exp : fatouSet exponentialMap = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨U, hU, hz, hnormal⟩
  exact not_isNormalSequenceOn_sphericalExpIterate hU ⟨z, hz⟩ hnormal

/-- Misiurewicz's theorem: the Julia set of the complex exponential is the plane. -/
theorem misiurewicz_juliaSet_exp : juliaSet exponentialMap = Set.univ := by
  rw [juliaSet, misiurewicz_fatouSet_exp, Set.compl_empty]

end

end ExponentialJuliaSetMisiurewicz
