/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Meromorphic germs and Laurent coefficients as linear
functionals.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue
import Mathlib.Order.Filter.Germ.Basic

/-!
# Germ packaging of meromorphic functions (residue-calculus)

`RS.meromorphicGermsAt z₀` is the ℂ-submodule of germs at `𝓝[≠] z₀` that are meromorphic;
`RS.laurentCoeffL z₀ k` and `RS.resL z₀` package `laurentCoeffAt`/`resAt` as ℂ-linear functionals
on it — the currency for laurent-tails (CC8) and serre-duality-cech/tails.

Main exports: `RS.MeromorphicGerm`, `RS.meromorphicGermsAt`, `RS.laurentCoeffL`, `RS.resL`,
`RS.laurentCoeffL_mk`.
-/

open Filter Topology Metric Function

namespace RS

variable {z₀ : ℂ}

/-- Meromorphy is a property of the punctured germ. -/
def MeromorphicGerm (z₀ : ℂ) (γ : Filter.Germ (𝓝[≠] z₀) ℂ) : Prop :=
  γ.liftOn (MeromorphicAt · z₀) fun _ _ hfg => propext (MeromorphicAt.meromorphicAt_congr hfg)

@[simp] theorem meromorphicGerm_coe {f : ℂ → ℂ} :
    MeromorphicGerm z₀ (f : Filter.Germ (𝓝[≠] z₀) ℂ) ↔ MeromorphicAt f z₀ := Iff.rfl

/-- The ℂ-space of meromorphic germs at `z₀` (a submodule of the full germ module). -/
def meromorphicGermsAt (z₀ : ℂ) : Submodule ℂ (Filter.Germ (𝓝[≠] z₀) ℂ) where
  carrier := {γ | MeromorphicGerm z₀ γ}
  zero_mem' := analyticAt_const.meromorphicAt
  add_mem' {γ δ} hγ hδ := by
    induction γ using Filter.Germ.inductionOn with
    | _ f =>
      induction δ using Filter.Germ.inductionOn with
      | _ g =>
        have hf : MeromorphicAt f z₀ := hγ
        have hg : MeromorphicAt g z₀ := hδ
        change MeromorphicGerm z₀ ((f : Filter.Germ (𝓝[≠] z₀) ℂ) + (g : Filter.Germ (𝓝[≠] z₀) ℂ))
        rw [← Filter.Germ.coe_add]
        exact hf.add hg
  smul_mem' c γ hγ := by
    induction γ using Filter.Germ.inductionOn with
    | _ f =>
      have hf : MeromorphicAt f z₀ := hγ
      change MeromorphicGerm z₀ (c • (f : Filter.Germ (𝓝[≠] z₀) ℂ))
      rw [← Filter.Germ.coe_smul]
      exact (MeromorphicAt.const c z₀).mul hf

@[simp] theorem mem_meromorphicGermsAt {f : ℂ → ℂ} :
    (f : Filter.Germ (𝓝[≠] z₀) ℂ) ∈ meromorphicGermsAt z₀ ↔ MeromorphicAt f z₀ := Iff.rfl

/-- Laurent coefficients as ℂ-linear functionals on meromorphic germs. -/
noncomputable def laurentCoeffL (z₀ : ℂ) (k : ℤ) : meromorphicGermsAt z₀ →ₗ[ℂ] ℂ where
  toFun γ := (γ : Filter.Germ (𝓝[≠] z₀) ℂ).liftOn (laurentCoeffAt · z₀ k)
    fun _ _ hfg => laurentCoeffAt_congr hfg k
  map_add' := by
    rintro ⟨γ, hγ⟩ ⟨δ, hδ⟩
    induction γ using Filter.Germ.inductionOn with
    | _ f =>
      induction δ using Filter.Germ.inductionOn with
      | _ g =>
        have hf : MeromorphicAt f z₀ := hγ
        have hg : MeromorphicAt g z₀ := hδ
        change laurentCoeffAt (fun z => f z + g z) z₀ k
          = laurentCoeffAt f z₀ k + laurentCoeffAt g z₀ k
        exact laurentCoeffAt_fun_add hf hg k
  map_smul' := by
    rintro c ⟨γ, hγ⟩
    induction γ using Filter.Germ.inductionOn with
    | _ f =>
      have hf : MeromorphicAt f z₀ := hγ
      change laurentCoeffAt (fun z => c * f z) z₀ k = c * laurentCoeffAt f z₀ k
      exact laurentCoeffAt_const_mul c k

/-- The residue functional. -/
noncomputable def resL (z₀ : ℂ) : meromorphicGermsAt z₀ →ₗ[ℂ] ℂ := laurentCoeffL z₀ (-1)

@[simp] theorem laurentCoeffL_mk {f : ℂ → ℂ} (hf : MeromorphicAt f z₀) (k : ℤ) :
    laurentCoeffL z₀ k ⟨(f : Filter.Germ (𝓝[≠] z₀) ℂ), hf⟩ = laurentCoeffAt f z₀ k := rfl

end RS
