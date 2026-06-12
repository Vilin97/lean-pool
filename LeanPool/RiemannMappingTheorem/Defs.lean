/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import LeanPool.RiemannMappingTheorem.ToMathlib
import LeanPool.RiemannMappingTheorem.DerivInj

/-!
# LeanPool.RiemannMappingTheorem.Defs
-/

open Complex Metric Set

variable {u : ℂ} {U V W : Set ℂ}

/-- The collection of compact subsets of `U`. Used as the index for the
compact-open topology `𝓒 U`. -/
def compacts (U : Set ℂ) : Set (Set ℂ) := {K ⊆ U | IsCompact K}

@[simp] lemma union_compacts : ⋃₀ compacts U = U :=
  subset_antisymm (fun _ ⟨_, hK, hz⟩ => hK.1 hz)
    (fun z hz => ⟨{z}, ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩, mem_singleton z⟩)

/-- The open unit disk `{z : ℂ | ‖z‖ < 1}`. -/
def 𝔻 : Set ℂ := ball 0 1

lemma mem_𝔻_iff : u ∈ 𝔻 ↔ ‖u‖ < 1 :=
  mem_ball_zero_iff

lemma neg_in_𝔻 : u ∈ 𝔻 → -u ∈ 𝔻 := by
  simp [𝔻]

lemma sqrt_𝔻_eq_𝔻 : {z : ℂ | z ^ 2 ∈ 𝔻} = 𝔻 := by
  simp [𝔻, ball]

/-- A `good_domain` is a connected proper open nonempty subset of `ℂ` on
which every nowhere-zero holomorphic function admits a holomorphic
square root. The variant of the Riemann Mapping Theorem proved here
applies to such domains. -/
class good_domain (U : Set ℂ) : Prop where
  /-- `U` is open. -/
  is_open : IsOpen U
  /-- `U` is nonempty. -/
  is_nonempty : U.Nonempty
  /-- `U` is preconnected. -/
  is_preconnected : IsPreconnected U
  /-- `U` is a proper subset of `ℂ`. -/
  ne_univ : U ≠ univ
  /-- Every nowhere-zero holomorphic function on `U` has a holomorphic
  square root. -/
  hasSqrt : ∀ f : ℂ → ℂ, (∀ z ∈ U, f z ≠ 0) → (DifferentiableOn ℂ f U) →
    ∃ (g : ℂ → ℂ), (DifferentiableOn ℂ g U) ∧ (U.EqOn f (g ^ 2))

/-- An `embedding U V` is a holomorphic injection `ℂ → ℂ` whose
restriction to `U` lands in `V`. Used to package the various conformal
maps that build the Riemann-mapping isomorphism. -/
structure embedding (U V : Set ℂ) where
  /-- The underlying function `ℂ → ℂ`. -/
  toFun : ℂ → ℂ
  /-- The function is holomorphic on `U`. -/
  is_diff : DifferentiableOn ℂ toFun U
  /-- The function is injective on `U`. -/
  is_inj : InjOn toFun U
  /-- The function maps `U` into `V`. -/
  maps_to : MapsTo toFun U V

instance {U V : Set ℂ} : CoeFun (embedding U V) (fun _ => ℂ → ℂ) := ⟨embedding.toFun⟩

/-- The identity embedding `U → U`, lifted to an `embedding U V` whenever
`U = V`. -/
@[simp] def embedding.id (hUV : U = V) : embedding U V where
  toFun := fun x => x
  is_diff := differentiable_id.differentiableOn
  is_inj := fun _ _ _ _ z => z
  maps_to := fun _ hx => hUV ▸ hx

/-- Composition of embeddings: `(f ∘ g) : embedding U W`. -/
@[simp] def embedding.comp (f : embedding V W) (g : embedding U V) : embedding U W where
  toFun := f ∘ g
  is_diff := f.is_diff.comp g.is_diff g.maps_to
  is_inj := f.is_inj.comp g.is_inj g.maps_to
  maps_to := f.maps_to.comp g.maps_to

/-- Lift a nowhere-zero embedding `U → V` to an embedding `U → {z | z² ∈ V}`
by taking a holomorphic square root supplied by `good_domain.hasSqrt`. -/
noncomputable def embedding.sqrt [good_domain U] (f : embedding U V) (hf : ∀ z ∈ U, f z ≠ 0) :
    { g : embedding U {z | z ^ 2 ∈ V} // U.EqOn f (g.toFun ^ 2) } := by
  choose g g_diff g_sqrt using good_domain.hasSqrt f hf f.is_diff
  refine ⟨⟨g, g_diff, ?_, ?_⟩, g_sqrt⟩
  · exact fun z hz z' hz' h => f.is_inj hz hz' (by simp [g_sqrt hz, g_sqrt hz', h])
  · exact fun z hz => by simpa [g_sqrt hz] using f.maps_to hz

/-- Specialisation of `embedding.sqrt` when the codomain is the open unit
disk `𝔻`: the square root again lands in `𝔻`. -/
noncomputable def embedding.sqrt' [good_domain U] (f : embedding U 𝔻) (hf : ∀ z ∈ U, f z ≠ 0) :
    { g : embedding U 𝔻 // U.EqOn f (g.toFun ^ 2) } := by
  let ⟨g, hg⟩ := embedding.sqrt f hf
  exact ⟨(embedding.id sqrt_𝔻_eq_𝔻).comp g, hg⟩

lemma ne_center_of_not_mem_closed_ball {w : ℂ} {r : ℝ} (hr : 0 ≤ r) ⦃z : ℂ⦄
    (hz : z ∈ (closedBall w r)ᶜ) : z ≠ w := by
  contrapose! hz
  simp [hz, hr]

/-- The conformal inversion `z ↦ r / (z - w)` realised as an `embedding`
from the complement of the closed disk `closedBall w r` into the open
unit disk. -/
noncomputable def embedding.inv (w : ℂ) {r : ℝ} (hr : 0 < r) :
    embedding ((closedBall w r)ᶜ) 𝔻 where
  toFun := fun z => r / (z - w)
  is_diff := by
    refine (differentiableOn_const _).div
      (differentiableOn_id.sub (differentiableOn_const _)) ?_
    simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le
  is_inj := fun x hx y hy hxy => by
    rw [div_eq_div_iff, eq_comm] at hxy
    · simpa [hr.ne.symm] using hxy
    · simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le hx
    · simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le hy
  maps_to := fun x hx => by
    simp only [mem_compl_iff, mem_closedBall, not_le, dist_eq_norm] at hx
    simpa only [𝔻, mem_ball_zero_iff, norm_div, div_lt_one (hr.trans hx), norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr.le]

lemma embedding.deriv_ne_zero {f : embedding U V} {z : ℂ} (hU : IsOpen U) (hz : z ∈ U) :
    deriv f z ≠ 0 :=
  deriv_ne_zero_of_inj hU f.is_diff f.is_inj hz
