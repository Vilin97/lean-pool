/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.DoubleCoverClass
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Nontriviality of the monodromy classifying character of the double cover

This file proves that, for `n ≥ 1`, the **monodromy classifying homomorphism**

```text
classifyingHom n x : FundamentalGroup (RP n) x →* Multiplicative (ZMod 2)
```

of the double cover `proj n : S^n → RP n` (constructed in `DoubleCoverClass.lean`)
is **surjective** — equivalently, *nontrivial*: some loop of `RP n` has monodromy
that swaps the two sheets of the cover.

This is the honest *nontriviality* statement of *Route A* toward
`α ∈ H¹(RPⁿ; F₂)`. It does **not** require the (absent) computation `π₁(Sⁿ) = 0`
nor `SimplyConnectedSpace (Sphere n)`; it needs only that the sphere `S^n` is
**path-connected** for `n ≥ 1` (`isPathConnected_sphere`). The geometric content
is exactly: a point `e ∈ S^n` and its antipode `-e` lie in the same path
component, so the projection of any path `e ⤳ -e` is a *loop* of `RP n` whose
monodromy sends the sheet `e` to the other sheet `-e`.

## Main declarations

* `joined_antipode` — for `n ≥ 1`, every `e : S^n` is `Joined` to its antipode `-e`.
* `projMonodromy_mk_of_lift` — the monodromy of the class of a path `γ` sends a
 fibre point `e` to the endpoint of any continuous lift of `γ` starting at `e`.
* `exists_loop_projMonodromyPerm_ne_one` — for `n ≥ 1`, some loop class at `x` has
 a nontrivial (sheet-swapping) monodromy permutation.
* `exists_classifyingHom_ne_one` — for `n ≥ 1`, some class of `π₁(RP n, x)` has
 classifying value `≠ 1`.
* `classifyingHom_surjective` — for `n ≥ 1`, `classifyingHom n x` is surjective.
-/

@[expose] public section

noncomputable section

namespace SphereOddDegree

open CategoryTheory unitInterval

/--
For `n ≥ 1`, the ambient Euclidean space `ℝ^{n+1}` of `S^n` has rank `> 1`,
the hypothesis of `isPathConnected_sphere`.
-/
theorem one_lt_rank_euclidean (n : ℕ) (hn : 1 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_cast
  omega

/--
For `n ≥ 1`, every point `e : S^n` is joined by a path to its antipode `-e`
(the unit sphere of `ℝ^{n+1}` is path-connected when `n ≥ 1`).
-/
theorem joined_antipode (n : ℕ) (hn : 1 ≤ n) (e : Sphere n) : Joined e (-e) := by
  have h_path_connected : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isPathConnected_sphere (one_lt_rank_euclidean n hn) 0 (by norm_num)
  have he_neg : (-e : EuclideanSpace ℝ (Fin (n + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin
    (n + 1))) 1 := by
    change ‖(-e : EuclideanSpace ℝ (Fin (n + 1))) - 0‖ = 1
    simp
  have hj : JoinedIn (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (e : EuclideanSpace
    ℝ (Fin (n + 1))) (-e : EuclideanSpace ℝ (Fin (n + 1))) :=
    h_path_connected.joinedIn (e : EuclideanSpace ℝ (Fin (n + 1))) e.2 (-e : EuclideanSpace ℝ
      (Fin (n + 1))) he_neg
  exact hj.joined_subtype

/--
**Monodromy via an explicit lift.** If `Γ` is a continuous lift of the path
`γ` (i.e. `proj n ∘ Γ = γ` pointwise) starting at the fibre point `e`, then the
monodromy of the homotopy class `⟦γ⟧` sends `e` to the endpoint `Γ 1`.
-/
theorem projMonodromy_mk_of_lift (n : ℕ) {x y : RP n} (γ : Path x y)
    (e : proj n ⁻¹' {x}) (Γ : C(unitInterval, Sphere n))
    (hΓ : proj n ∘ Γ = γ) (hΓ0 : Γ 0 = (e : Sphere n)) :
    (projMonodromy n (⟦γ⟧ : Path.Homotopic.Quotient x y) e : Sphere n) = Γ 1 := by
  have hstart : γ 0 = proj n (e : Sphere n) := by
    have h0 := congrFun hΓ 0
    rw [Function.comp_apply, hΓ0] at h0
    exact h0.symm
  have h_eq : Γ = projLiftPath n γ (e : Sphere n) hstart :=
    eq_projLiftPath n γ (e : Sphere n) hstart hΓ hΓ0
  have h1 := congrArg (fun f : C(unitInterval, Sphere n) => f 1) h_eq.symm
  have hmono : (projMonodromy n (⟦γ⟧ : Path.Homotopic.Quotient x y) e : Sphere n) = projLiftPath
    n γ (e : Sphere n) hstart 1 := rfl
  exact hmono.trans h1

/--
**A sheet-swapping loop.** For `n ≥ 1` and any base point `x : RP n`, there
is a loop class at `x` whose monodromy permutation of the two-element fibre is
nontrivial (it swaps the two sheets of the double cover).
-/
theorem exists_loop_projMonodromyPerm_ne_one (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    ∃ γ : Path.Homotopic.Quotient x x, projMonodromyPerm n γ ≠ 1 := by
  obtain ⟨e, rfl⟩ := proj_surjective n x
  obtain ⟨p, -⟩ : ∃ p : Path e (-e), True := ⟨(joined_antipode n hn e).somePath, trivial⟩
  set γ_path : Path (proj n e) (proj n e) := (p.map (proj n).continuous).cast rfl
    (proj_eq_proj_neg e)
  refine ⟨⟦γ_path⟧, ?_⟩
  intro h
  have h_mono : (projMonodromy n ⟦γ_path⟧ ⟨e, rfl⟩ : Sphere n) = -e := by
    have h_lift := projMonodromy_mk_of_lift n γ_path ⟨e, rfl⟩ p.toContinuousMap (by
      ext t; rfl) p.source
    exact h_lift.trans p.target
  have h_val : (projMonodromy n ⟦γ_path⟧ ⟨e, rfl⟩ : Sphere n) = e := by
    have h_app := congrArg Subtype.val (congrFun (congrArg Equiv.toFun h) ⟨e, rfl⟩)
    exact h_app
  rw [h_mono] at h_val
  exact (ne_neg_self e).symm h_val

/--
**Nontriviality of the classifying character.** For `n ≥ 1` and any base
point `x : RP n`, some class of `π₁(RP n, x)` has classifying value `≠ 1`.
-/
theorem exists_classifyingHom_ne_one (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    ∃ a : FundamentalGroup (RP n) x, classifyingHom n x a ≠ 1 := by
  obtain ⟨γ, hγ⟩ := exists_loop_projMonodromyPerm_ne_one n hn x
  use FundamentalGroup.fromPath γ
  simp only [ne_eq]
  rw [classifyingHom_eq_one_iff]
  exact hγ

/--
**Surjectivity of the monodromy classifying character.** For `n ≥ 1`, the
classifying homomorphism `classifyingHom n x : π₁(RP n, x) → Multiplicative (ZMod 2)`
of the double cover `proj n : S^n → RP n` is surjective. This is the honest
nontriviality statement of *Route A* toward `α ∈ H¹(RPⁿ; F₂)`.
-/
theorem classifyingHom_surjective (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    Function.Surjective (classifyingHom n x) := by
  intro g
  by_cases hg : g = 1
  · exact ⟨1, hg.symm ▸ map_one _⟩
  · obtain ⟨a, ha⟩ := exists_classifyingHom_ne_one n hn x
    have h_two (u v : Multiplicative (ZMod 2)) (hu : u ≠ 1) (hv : v ≠ 1) : u = v := by
      have hu_add : Multiplicative.toAdd u ≠ 0 := by
        intro h; apply hu; exact Multiplicative.toAdd.injective (by simpa using h)
      have hv_add : Multiplicative.toAdd v ≠ 0 := by
        intro h; apply hv; exact Multiplicative.toAdd.injective (by simpa using h)
      have hu1 : Multiplicative.toAdd u = 1 := by
        generalize hu_var : Multiplicative.toAdd u = u_val
        rw [hu_var] at hu_add
        fin_cases u_val <;> [contradiction; rfl]
      have hv1 : Multiplicative.toAdd v = 1 := by
        generalize hv_var : Multiplicative.toAdd v = v_val
        rw [hv_var] at hv_add
        fin_cases v_val <;> [contradiction; rfl]
      apply Multiplicative.toAdd.injective
      rw [hu1, hv1]
    exact ⟨a, h_two (classifyingHom n x a) g ha hg ▸ rfl⟩

end SphereOddDegree
