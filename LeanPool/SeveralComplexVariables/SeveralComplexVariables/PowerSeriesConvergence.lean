/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CartanThullen
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PowerSeriesConvergence.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Extension
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.HolomorphicConvexity

/-!
# Characterization of power-series convergence domains

An open complete logarithmically convex Reinhardt domain is holomorphically convex, by monomial
separation. Cartan–Thullen supplies a function with precisely that domain of existence. Its
Taylor series at zero has the prescribed convergence domain.

## Main results

`exists_powerSeriesConvergenceDomain_eq` realizes every nonempty open complete logarithmically
convex Reinhardt set as a scalar power-series convergence domain.
`isLogarithmicallyConvex_iff_exists_powerSeriesConvergenceDomain` is the corresponding
characterization among open complete Reinhardt sets.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
-/

public noncomputable section

open Set
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*} [Fintype ι]

/-- Changing coordinate labels transports the convergence domain of a coefficient family. -/
theorem powerSeriesConvergenceDomain_domCongr {κ : Type*} [Fintype κ]
    (e : ι ≃ κ) (c : MvPowerSeries κ ℂ) :
    powerSeriesConvergenceDomain (fun m => c (Finsupp.domCongr e m)) =
      (Homeomorph.piCongrLeft (Y := fun _ : κ => ℂ) e) ⁻¹' powerSeriesConvergenceDomain c := by
  let H := Homeomorph.piCongrLeft (Y := fun _ : κ => ℂ) e
  have he : powerSeriesAbsConvergenceSet (fun m => c (Finsupp.domCongr e m)) =
      H ⁻¹' powerSeriesAbsConvergenceSet c := by
    ext z
    change Summable (fun m : ι →₀ ℕ => ‖c (Finsupp.domCongr e m)‖ * ∏ i, ‖z i‖ ^ m i) ↔
      Summable (fun m : κ →₀ ℕ => ‖c m‖ * ∏ i, ‖H z i‖ ^ m i)
    rw [← (Finsupp.domCongr e).toEquiv.summable_iff]
    apply summable_congr
    intro m
    congr 1
    rw [← e.prod_comp]
    simp [H, Homeomorph.piCongrLeft, Equiv.piCongrLeft, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_apply]
  change interior (powerSeriesAbsConvergenceSet _) = H ⁻¹' interior (powerSeriesAbsConvergenceSet c)
  rw [he, H.preimage_interior]

/-- On finite ordered coordinates, the Taylor series of a nonextendable function realizes an open
complete logarithmically convex Reinhardt domain. -/
private theorem exists_powerSeriesConvergenceDomain_eq_fin {n : ℕ} {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hne : U.Nonempty) (hc : IsCompleteReinhardt U)
    (hl : IsLogarithmicallyConvex U) :
    ∃ c : MvPowerSeries (Fin n) ℂ, powerSeriesConvergenceDomain c = U := by
  obtain ⟨f, hf⟩ := (isHolomorphicallyConvex_of_completeReinhardt ho hc
    hl).exists_domainOfExistence ho
  obtain ⟨hUD, he⟩
    := IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum ho hc hf.1
  refine ⟨taylorCoefficientsAtZero f, Subset.antisymm ?_ hUD⟩
  exact hf.2 _ U (isOpen_powerSeriesConvergenceDomain _)
    ((isCompleteReinhardt_powerSeriesConvergenceDomain _).isConnected (hne.mono hUD))
    ho hne Subset.rfl hUD ⟨_, analyticOnNhd_powerSeriesSum _, he⟩

/-- **Hartogs' characterization, existence direction** ([Boas][Boas2013] §2.2, Theorem 1).
Every nonempty open complete logarithmically convex Reinhardt set is exactly the convergence
domain of a scalar power series. Monomial separation and Cartan–Thullen give a
nonextendable function whose Taylor series realizes the domain. -/
theorem exists_powerSeriesConvergenceDomain_eq {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hne : U.Nonempty) (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U) :
    ∃ c : MvPowerSeries ι ℂ, powerSeriesConvergenceDomain c = U := by
  let e := Fintype.equivFin ι
  let H : (Fin (Fintype.card ι) → ℂ) ≃ₜ (ι → ℂ) :=
    { toFun := fun z i => z (e i)
      invFun := fun z j => z (e.symm j)
      left_inv := fun z => by ext j; simp
      right_inv := fun z => by ext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply (e i)
      continuous_invFun := continuous_pi fun j => continuous_apply (e.symm j) }
  let V := H ⁻¹' U
  have hoV : IsOpen V := hU.preimage H.continuous
  have hnV : V.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨H.symm z, by simpa only [V, mem_preimage, H.apply_symm_apply] using hz⟩
  have hcV : IsCompleteReinhardt V := by
    intro z hz w hw
    change (fun i => w (e i)) ∈ U
    exact hc (show (fun i => z (e i)) ∈ U from hz) (fun i => hw (e i))
  have hlV : IsLogarithmicallyConvex V := by
    intro x hx y hy a b ha hb hab
    exact hl (x := fun i => x (e i)) hx (y := fun i => y (e i)) hy ha hb hab
  obtain ⟨c, hD⟩ := exists_powerSeriesConvergenceDomain_eq_fin hoV hnV hcV hlV
  refine ⟨fun m => c (Finsupp.domCongr e m), ?_⟩
  rw [powerSeriesConvergenceDomain_domCongr, hD]
  ext z
  change H ((Homeomorph.piCongrLeft (Y := fun _ : Fin (Fintype.card ι) => ℂ) e) z) ∈ U ↔ z ∈ U
  have he : H ((Homeomorph.piCongrLeft (Y := fun _ : Fin (Fintype.card ι) => ℂ) e) z) = z := by
    ext i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card ι) => ℂ) e z i
  rw [he]

/-- **Hartogs' characterization of power-series convergence domains.** For a nonempty
open complete Reinhardt set, logarithmic convexity is exactly the existence condition. -/
theorem isLogarithmicallyConvex_iff_exists_powerSeriesConvergenceDomain
    {U : Set (ι → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) (hc : IsCompleteReinhardt U) :
    IsLogarithmicallyConvex U ↔
      ∃ c : MvPowerSeries ι ℂ, powerSeriesConvergenceDomain c = U := by
  constructor
  · exact exists_powerSeriesConvergenceDomain_eq hU hne hc
  · rintro ⟨c, rfl⟩
    exact isLogarithmicallyConvex_powerSeriesConvergenceDomain c

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
