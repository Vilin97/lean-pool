/-
Copyright (c) 2026 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic


/-!
# A van Kampen theorem for simple connectivity (special case) — infrastructure

This file develops the classical "two open sets" van Kampen theorem in the form needed to
compute fundamental groups of complements: if `X = U ∪ V` with `U`, `V` open and both
simply connected, and `U ∩ V` is path-connected, then `X` is simply connected.

We phrase the core content (`loop_nullhomotopic_of_cover`) elementarily in terms of loops
contained in `U` / `V` and `JoinedIn` connectivity, so it can be applied without first
passing to subtype topologies.

## Route (see `PLAN.md`)
The combinatorial backbone is Mathlib's Lebesgue subdivision
`exists_monotone_Icc_subset_open_cover_unitInterval`.  Working in the fundamental groupoid
`Path.Homotopic.Quotient`, the proof telescopes a subdivided loop into a product of loops each
contained in `U` or `V`.  The one geometric ingredient missing from Mathlib is the
`truncate`-splitting lemma `truncate_split` below (a path's restriction to `[s,u]` is homotopic
to the concatenation of its restrictions to `[s,t]` and `[t,u]`).
-/

open scoped Topology unitInterval

namespace Submission.VanKampen

/-
Pointwise formula for `truncateOfLE`: it clamps the parameter into `[t₀, t₁]`.
-/
theorem truncateOfLE_apply {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (w : ↑unitInterval) :
    γ.truncateOfLE h w = γ.extend (min (max (w : ℝ) t₀) t₁) := by
  -- By definition of `Path.truncate`, we have that `γ.truncate t₀ t₁` is the path that goes from `γ(t₀)` to `γ(t₁)`, and `toFun s := γ.extend (min (max (s:ℝ) t₀) t₁)`.
  simp [Path.truncateOfLE, Path.truncate, Path.cast]

/-
**`truncate`-splitting.** For a path `γ` and reals `s ≤ t ≤ u`, the restriction of `γ` to
`[s, u]` is homotopic (rel endpoints) to the concatenation of its restrictions to `[s, t]` and
`[t, u]`.  This is the geometric core of the subdivision argument; it is a reparametrization
homotopy and is currently missing from Mathlib.
-/
theorem truncate_split {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) (hu : u ≤ 1) :
    Path.Homotopic (γ.truncateOfLE (hst.trans htu))
      ((γ.truncateOfLE hst).trans (γ.truncateOfLE htu)) := by
  constructor;
  constructor;
  case val.toHomotopy => exact ⟨ ⟨ fun p => γ.extend ( ( 1 - p.1.val ) * min ( max p.2.val s ) u + p.1.val * ( if p.2.val ≤ 1 / 2 then min ( max ( 2 * p.2.val ) s ) t else min ( max ( 2 * p.2.val - 1 ) t ) u ) ), by
    refine' γ.continuous_extend.comp _;
    apply_rules [ Continuous.add, Continuous.mul, continuous_const, continuous_fst, continuous_snd ];
    · fun_prop;
    · fun_prop;
    · fun_prop;
    · apply_rules [ Continuous.if_le, Continuous.min, Continuous.max, continuous_const, continuous_fst, continuous_snd ];
      · fun_prop;
      · fun_prop;
      · exact continuous_subtype_val.comp continuous_snd;
      · grind ⟩, by
    simp +decide [ truncateOfLE_apply ], by
    intro x
    simp [truncateOfLE_apply, Path.trans_apply];
    split_ifs <;> rfl ⟩;
  simp +decide [Path.truncateOfLE];
  grind

/-- The `[t 0, t N]`-truncation of `γ` (with `t 0 = 0`, `t N = 1`), cast back to the loop
endpoints, has the same homotopy class as `γ` itself. -/
theorem trunc_mk_eq {X : Type*} [TopologicalSpace X] {x₀ : X} (γ : Path x₀ x₀)
    (t : ℕ → ℝ) (N : ℕ) (ht0 : t 0 = 0) (htN : t N = 1)
    (cm : x₀ = γ.extend (min (t 0) (t N))) (cN : x₀ = γ.extend (t N)) :
    (Path.Homotopic.Quotient.mk (γ.truncate (t 0) (t N))).cast cm cN
      = Path.Homotopic.Quotient.mk γ := by
  rw [← Path.Homotopic.Quotient.mk_cast]
  congr 1
  ext w
  rw [Path.cast_coe, Path.truncate, Path.coe_mk_mk, ht0, htN]
  have hw0 : (0:ℝ) ≤ (w:ℝ) := w.2.1
  have hw1 : (w:ℝ) ≤ 1 := w.2.2
  simp [max_eq_left hw0, min_eq_left hw1]

/-
**Telescoping induction (groupoid algebra).** Given a loop `γ` at `x₀`, a subdivision
`t : ℕ → ℝ` of `[0,1]` (with `t 0 = 0`, `t N = 1`, monotone, valued in `[0,1]`), and connecting
paths `β n : Path x₀ (γ.extend (t n))` with `β 0`, `β N` trivial, such that every "piece loop"
`(β n).trans ((γ.truncate over [t n, t (n+1)]).trans (β (n+1)).symm)` is null-homotopic, the loop
`γ` is null-homotopic.  This is pure fundamental-groupoid algebra (telescoping via
`truncate_split`), with no reference to the cover.
-/
theorem nullhomotopic_of_subdivision {X : Type*} [TopologicalSpace X] {x₀ : X}
    (γ : Path x₀ x₀) (N : ℕ) (t : ℕ → ℝ)
    (h0 : γ.extend (t 0) = x₀) (hN : γ.extend (t N) = x₀)
    (hmono : ∀ n, t n ≤ t (n + 1)) (hge0 : ∀ n, 0 ≤ t n) (hle1 : ∀ n, t n ≤ 1)
    (ht0 : t 0 = 0) (htN : t N = 1)
    (β : ∀ n, Path x₀ (γ.extend (t n)))
    (hβ0 : Path.Homotopic.Quotient.mk (β 0)
      = (Path.Homotopic.Quotient.refl x₀).cast rfl h0)
    (hβN : Path.Homotopic.Quotient.mk (β N)
      = (Path.Homotopic.Quotient.refl x₀).cast rfl hN)
    (hstep : ∀ n, n < N →
      Path.Homotopic ((β n).trans ((γ.truncateOfLE (hmono n)).trans (β (n + 1)).symm))
        (Path.refl x₀)) :
    Path.Homotopic γ (Path.refl x₀) := by
  revert hβ0 hβN hstep;
  intro hβ0 hβN hstep
  have h_ind : ∀ n ≤ N, Path.Homotopic.Quotient.mk (γ.truncateOfLE (by
  exact monotone_nat_of_le_succ hmono n.zero_le : t 0 ≤ t n)) = (Path.Homotopic.Quotient.mk (β n)).cast (by
  exact h0) (by
  rfl) := by
    intro n hn
    induction' n with n ih
    all_goals generalize_proofs at *;
    · simp +decide [ hβ0, Path.truncateOfLE ];
      grind;
    · have hmono' : Monotone t := monotone_nat_of_le_succ hmono
      have h_split : Path.Homotopic.Quotient.mk
            (γ.truncateOfLE (show t 0 ≤ t (n + 1) from hmono' (Nat.zero_le _)))
          = (Path.Homotopic.Quotient.mk
              (γ.truncateOfLE (show t 0 ≤ t n from hmono' (Nat.zero_le _)))).trans
            (Path.Homotopic.Quotient.mk
              (γ.truncateOfLE (show t n ≤ t (n + 1) from hmono n))) := by
        exact Quotient.sound
          (truncate_split γ (hge0 0) (hmono' (Nat.zero_le _)) (hmono n) (hle1 (n + 1)))
      generalize_proofs at *;
      have h_step : Path.Homotopic.Quotient.mk ((β n).trans ((γ.truncateOfLE (by
      exact hmono n : t n ≤ t (n + 1))).trans (β (n + 1)).symm)) = (Path.Homotopic.Quotient.refl x₀) := by
        exact Quotient.sound ( hstep n ( Nat.lt_of_succ_le hn ) )
      generalize_proofs at *;
      convert congr_arg ( fun x => x.trans ( Path.Homotopic.Quotient.mk ( β ( n + 1 ) ) ) ) h_step using 1;
      · rw [ h0 ];
      · grind +revert;
      · grind +suggestions
  generalize_proofs at *;
  simp_all +decide [ Path.truncateOfLE ];
  have key := h_ind N le_rfl
  have key2 := congrArg
    (fun q : Path.Homotopic.Quotient (γ.extend (t 0)) (γ.extend (t N)) =>
      q.cast h0.symm hN.symm) key
  simp only [Path.Homotopic.Quotient.cast_cast] at key2
  rw [trunc_mk_eq γ t N ht0 htN, hβN, Path.Homotopic.Quotient.cast_cast] at key2
  exact Quotient.exact key2

/-
**Subdivision with set assignment.** A loop `γ` has a subdivision `t : ℕ → ℝ` of `[0,1]`
(monotone, `t 0 = 0`, `t N = 1`, valued in `[0,1]`) together with sets `W n`, each equal to `U`
or `V`, such that `γ` maps `[t n, t (n+1)]` into `W n`.  (Lebesgue subdivision of the open cover
`{γ⁻¹ U, γ⁻¹ V}` of the unit interval.)
-/
theorem subdivision_with_W {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ)
    {x₀ : X} (γ : Path x₀ x₀) :
    ∃ (N : ℕ) (t : ℕ → ℝ) (W : ℕ → Set X),
      t 0 = 0 ∧ t N = 1 ∧ (∀ n, t n ≤ t (n + 1)) ∧ (∀ n, 0 ≤ t n) ∧ (∀ n, t n ≤ 1) ∧
      (∀ n, W n = U ∨ W n = V) ∧
      (∀ n (r : ℝ), r ∈ Set.Icc (t n) (t (n + 1)) → γ.extend r ∈ W n) := by
  classical
  obtain ⟨T, hT0, hTmono, ⟨N, hN⟩, hTcov⟩ :
      ∃ T : ℕ → ↑unitInterval, T 0 = 0 ∧ Monotone T ∧ (∃ n, ∀ m ≥ n, T m = 1) ∧
        ∀ n, ∃ i : Bool, Set.Icc (T n) (T (n + 1)) ⊆ (if i then γ ⁻¹' U else γ ⁻¹' V) := by
    apply exists_monotone_Icc_subset_open_cover_unitInterval
    · intro i; cases i
      · simpa using hVo.preimage γ.continuous
      · simpa using hUo.preimage γ.continuous
    · intro x _
      have : γ x ∈ U ∪ V := by rw [hcov]; trivial
      rcases this with h | h
      · exact Set.mem_iUnion.2 ⟨true, by simpa using h⟩
      · exact Set.mem_iUnion.2 ⟨false, by simpa using h⟩
  refine ⟨N, fun n => (T n : ℝ), fun n => if (hTcov n).choose then U else V,
    by simp [hT0], by simp [hN N le_rfl], fun n => by exact_mod_cast hTmono n.le_succ,
    fun n => (T n).2.1, fun n => (T n).2.2, fun n => by by_cases h : (hTcov n).choose <;> simp [h],
    ?_⟩
  intro n r hr
  have hr01 : (0 : ℝ) ≤ r ∧ r ≤ 1 :=
    ⟨le_trans (T n).2.1 hr.1, le_trans hr.2 (T (n + 1)).2.2⟩
  have hsub : (⟨r, hr01.1, hr01.2⟩ : ↑unitInterval) ∈ Set.Icc (T n) (T (n + 1)) :=
    ⟨hr.1, hr.2⟩
  have hmemc := (hTcov n).choose_spec hsub
  have hext : γ.extend r = γ ⟨r, hr01.1, hr01.2⟩ := γ.extend_extends' ⟨r, hr01.1, hr01.2⟩
  by_cases h : (hTcov n).choose
  · simp only [h, if_true] at hmemc ⊢; rw [hext]; exact hmemc
  · simp only [h] at hmemc ⊢; rw [hext]; exact hmemc

/-
All points of a concatenation lie in `S` if both pieces do.
-/
theorem trans_mem_of_mem {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) {S : Set X}
    (hp : ∀ s, p s ∈ S) (hq : ∀ s, q s ∈ S) : ∀ s, (p.trans q) s ∈ S := by
      grind

/-
All points of `p.symm` lie in `S` if those of `p` do.
-/
theorem symm_mem_of_mem {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) {S : Set X} (hp : ∀ s, p s ∈ S) : ∀ s, p.symm s ∈ S := by
      grind +qlia

/-
A loop that becomes null-homotopic after casting has trivial class.
-/
theorem quot_eq_refl_cast {X : Type*} [TopologicalSpace X] {x₀ y : X}
    (p : Path x₀ y) (h : y = x₀)
    (hp : Path.Homotopic (p.cast rfl h.symm) (Path.refl x₀)) :
    Path.Homotopic.Quotient.mk p = (Path.Homotopic.Quotient.refl x₀).cast rfl h := by
      convert Quotient.sound ?_;
      convert hp using 1

/-
The points of `p.cast rfl h` agree with those of `p`.
-/
theorem cast_apply_mem {X : Type*} [TopologicalSpace X] {x₀ y : X}
    (p : Path x₀ y) (h : y = x₀) {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ s, (p.cast rfl h.symm) s ∈ S := by
      simp +decide [ Path.cast ];
      exact fun a ha hb => hp ⟨ a, ha, hb ⟩

/-
Connecting path lying in the intersection of two cover sets, each of which is `U` or `V`.
-/
theorem exists_connecting {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (hUconn : ∀ y ∈ U, JoinedIn U x₀ y) (hVconn : ∀ y ∈ V, JoinedIn V x₀ y)
    (hIconn : ∀ y ∈ U ∩ V, JoinedIn (U ∩ V) x₀ y)
    {A B : Set X} (hA : A = U ∨ A = V) (hB : B = U ∨ B = V)
    {y : X} (hyA : y ∈ A) (hyB : y ∈ B) :
    ∃ p : Path x₀ y, (∀ s, p s ∈ A) ∧ (∀ s, p s ∈ B) := by
      rcases hA with ( rfl | rfl ) <;> rcases hB with ( rfl | rfl );
      · exact ⟨ Classical.choose ( hUconn y hyB ), fun s => Classical.choose_spec ( hUconn y hyB ) s, fun s => Classical.choose_spec ( hUconn y hyB ) s ⟩;
      · obtain ⟨ p, hp ⟩ := hIconn y ⟨ hyA, hyB ⟩;
        exact ⟨ p, fun s => hp s |>.1, fun s => hp s |>.2 ⟩;
      · obtain ⟨ p, hp ⟩ := hIconn y ⟨ hyB, hyA ⟩;
        exact ⟨ p, fun s => hp s |>.2, fun s => hp s |>.1 ⟩;
      · exact ⟨ hVconn y hyA |> JoinedIn.somePath, fun s => hVconn y hyA |> JoinedIn.somePath_mem |> fun h => h s, fun s => hVconn y hyA |> JoinedIn.somePath_mem |> fun h => h s ⟩

/-
**Connecting paths exist.** Given the subdivision data (a subdivision `t`, set assignment
`W` with the membership/`U`-or-`V` properties), there are connecting paths `β n` with `β 0`,
`β N` trivial such that each per-step loop is null-homotopic.  This packages all of the geometry
of the van Kampen argument; combined with `nullhomotopic_of_subdivision` it proves
`loop_nullhomotopic_of_cover`.
-/
theorem exists_beta {X : Type*} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUconn : ∀ y ∈ U, JoinedIn U x₀ y)
    (hVconn : ∀ y ∈ V, JoinedIn V x₀ y)
    (hIconn : ∀ y ∈ U ∩ V, JoinedIn (U ∩ V) x₀ y)
    (hUnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ U) → Path.Homotopic p (Path.refl x₀))
    (hVnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ V) → Path.Homotopic p (Path.refl x₀))
    (γ : Path x₀ x₀) (N : ℕ) (t : ℕ → ℝ) (W : ℕ → Set X)
    (h0 : γ.extend (t 0) = x₀) (hN : γ.extend (t N) = x₀)
    (hmono : ∀ n, t n ≤ t (n + 1)) (hge0 : ∀ n, 0 ≤ t n) (hle1 : ∀ n, t n ≤ 1)
    (hWUV : ∀ n, W n = U ∨ W n = V)
    (hmem : ∀ n (r : ℝ), r ∈ Set.Icc (t n) (t (n + 1)) → γ.extend r ∈ W n) :
    ∃ β : ∀ n, Path x₀ (γ.extend (t n)),
      Path.Homotopic.Quotient.mk (β 0)
          = (Path.Homotopic.Quotient.refl x₀).cast rfl h0 ∧
      Path.Homotopic.Quotient.mk (β N)
          = (Path.Homotopic.Quotient.refl x₀).cast rfl hN ∧
      (∀ n, n < N →
        Path.Homotopic ((β n).trans ((γ.truncateOfLE (hmono n)).trans (β (n + 1)).symm))
          (Path.refl x₀)) := by
  obtain ⟨β, hβA, hβB⟩ : ∃ β : ∀ n, Path x₀ (γ.extend (t n)), (∀ n s, β n s ∈ W (n - 1)) ∧ (∀ n s, β n s ∈ W n) := by
    have h_existsconnecting : ∀ n, ∃ p : Path x₀ (γ.extend (t n)), (∀ s, p s ∈ W (n - 1)) ∧ (∀ s, p s ∈ W n) := by
      intro n
      have h_mem : γ.extend (t n) ∈ W (n - 1) ∧ γ.extend (t n) ∈ W n := by
        grind +qlia;
      exact exists_connecting hUconn hVconn hIconn ( hWUV _ ) ( hWUV _ ) h_mem.1 h_mem.2;
    exact ⟨ fun n => Classical.choose ( h_existsconnecting n ), fun n s => Classical.choose_spec ( h_existsconnecting n ) |>.1 s, fun n s => Classical.choose_spec ( h_existsconnecting n ) |>.2 s ⟩
  generalize_proofs at *; (
  refine' ⟨ β, _, _, _ ⟩
  all_goals generalize_proofs at *;
  · apply quot_eq_refl_cast;
    cases hWUV 0 <;> simp_all +decide only [Set.mem_union];
    · exact hUnull _ fun s => by simpa [ ‹W 0 = U› ] using cast_apply_mem ( β 0 ) h0 ( by simpa [ ‹W 0 = U› ] using hβB 0 ) s;
    · exact hVnull _ fun s => by simpa [ ‹W 0 = V› ] using cast_apply_mem ( β 0 ) h0 ( by simpa [ ‹W 0 = V› ] using hβB 0 ) s;
  · apply quot_eq_refl_cast;
    cases hWUV ( N - 1 ) <;> simp_all +decide only;
    · exact hUnull _ fun s => by simpa [ ‹W ( N - 1 ) = U› ] using hβA N s;
    · exact hVnull _ fun s => by simpa [ ‹W ( N - 1 ) = V› ] using hβA N s;
  · intro n hn
    have hloop : ∀ s, ((β n).trans ((γ.truncateOfLE (hmono n)).trans (β (n + 1)).symm)) s ∈ W n := by
      intro s
      apply trans_mem_of_mem (β n) ((γ.truncateOfLE (hmono n)).trans (β (n + 1)).symm) (hβB n) (trans_mem_of_mem (γ.truncateOfLE (hmono n)) (β (n + 1)).symm (by
      intro s
      rw [truncateOfLE_apply];
      exact hmem n _ ⟨ by cases max_cases ( s : ℝ ) ( t n ) <;> cases min_cases ( max ( s : ℝ ) ( t n ) ) ( t ( n + 1 ) ) <;> linarith [ Set.mem_Icc.mp s.2, hge0 n, hle1 n, hmono n ], by cases max_cases ( s : ℝ ) ( t n ) <;> cases min_cases ( max ( s : ℝ ) ( t n ) ) ( t ( n + 1 ) ) <;> linarith [ Set.mem_Icc.mp s.2, hge0 n, hle1 n, hmono n ] ⟩) (by
      exact fun s => by simpa using symm_mem_of_mem ( β ( n + 1 ) ) ( hβA ( n + 1 ) ) s;)) s
    generalize_proofs at *; (
    grind))

/-- **van Kampen, simple-connectivity special case (loop form).**
If `X = U ∪ V` with `U`, `V` open, `x₀ ∈ U ∩ V`, every point of `U` (resp. `V`, resp. `U ∩ V`)
is joined to `x₀` inside `U` (resp. `V`, resp. `U ∩ V`), and every loop at `x₀` contained in `U`
(resp. `V`) is null-homotopic, then every loop at `x₀` in `X` is null-homotopic. -/
theorem loop_nullhomotopic_of_cover {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ)
    {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUconn : ∀ y ∈ U, JoinedIn U x₀ y)
    (hVconn : ∀ y ∈ V, JoinedIn V x₀ y)
    (hIconn : ∀ y ∈ U ∩ V, JoinedIn (U ∩ V) x₀ y)
    (hUnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ U) → Path.Homotopic p (Path.refl x₀))
    (hVnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ V) → Path.Homotopic p (Path.refl x₀))
    (γ : Path x₀ x₀) : Path.Homotopic γ (Path.refl x₀) := by
  obtain ⟨N, t, W, ht0, htN, hmono, hge0, hle1, hWUV, hmem⟩ :=
    subdivision_with_W hUo hVo hcov γ
  have h0 : γ.extend (t 0) = x₀ := by rw [ht0]; exact γ.extend_zero
  have hN : γ.extend (t N) = x₀ := by rw [htN]; exact γ.extend_one
  obtain ⟨β, hβ0, hβN, hstep⟩ :=
    exists_beta hxU hxV hUconn hVconn hIconn hUnull hVnull γ N t W h0 hN hmono hge0 hle1 hWUV hmem
  exact nullhomotopic_of_subdivision γ N t h0 hN hmono hge0 hle1 ht0 htN β hβ0 hβN hstep

end Submission.VanKampen