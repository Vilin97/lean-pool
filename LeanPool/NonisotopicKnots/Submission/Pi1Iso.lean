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

import LeanPool.NonisotopicKnots.Submission.VanKampen
import LeanPool.NonisotopicKnots.Submission.Invariant

/-!
# Van Kampen π₁-transfer of non-abelianness onto an open piece

If `X = U ∪ V` with `U`, `V` open, `x₀ ∈ U ∩ V`, all three sets path-connected to `x₀` inside
themselves, and `V` simply connected, then every loop in `X` at `x₀` is homotopic in `X` to a loop
lying in `U` (surjectivity of `incl_* : π₁(U,x₀) → π₁(X,x₀)`). Since `incl_*` is a group
homomorphism, this transfers non-abelianness: a non-abelian `π₁(X)` forces a non-abelian `π₁(U)`.

This is the form of van Kampen needed for *point removal* in a 3-manifold: take `V` a small ball
around the removed point (contractible, hence simply connected) and `U = X ∖ {q}`.

The proof reuses the subdivision/telescoping machinery of `Submission.VanKampen`.
-/

open scoped Topology unitInterval

namespace Submission.Pi1Iso

/-
**Telescoping accumulation into `U`.** Mirrors `Submission.VanKampen.nullhomotopic_of_subdivision`
but accumulates the kept `U`-loops. For each `n ≤ N` there is a loop `δ` in `U` whose class,
followed by the connecting path `β n`, equals the truncation of `γ` over `[t 0, t n]`.
-/
theorem accumulate_into_U {X : Type*} [TopologicalSpace X]
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U)
    (hVnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ V) → Path.Homotopic p (Path.refl x₀))
    (γ : Path x₀ x₀) (N : ℕ) (t : ℕ → ℝ) (W : ℕ → Set X)
    (h0 : γ.extend (t 0) = x₀)
    (hmono : ∀ n, t n ≤ t (n + 1)) (hge0 : ∀ n, 0 ≤ t n) (hle1 : ∀ n, t n ≤ 1)
    (hWUV : ∀ n, W n = U ∨ W n = V)
    (hmem : ∀ n (r : ℝ), r ∈ Set.Icc (t n) (t (n + 1)) → γ.extend r ∈ W n)
    (β : ∀ n, Path x₀ (γ.extend (t n)))
    (hβL : ∀ n s, β n s ∈ W (n - 1)) (hβR : ∀ n s, β n s ∈ W n)
    (hβ0 : Path.Homotopic.Quotient.mk (β 0)
      = (Path.Homotopic.Quotient.refl x₀).cast rfl h0) :
    ∀ n, n ≤ N → ∃ δ : Path x₀ x₀, (∀ s, δ s ∈ U) ∧
      Path.Homotopic.Quotient.mk (γ.truncateOfLE
          (show t 0 ≤ t n from (monotone_nat_of_le_succ hmono) (Nat.zero_le n)))
        = ((Path.Homotopic.Quotient.mk δ).trans (Path.Homotopic.Quotient.mk (β n))).cast h0 rfl := by
  intro n hn
  induction' n with n ih;
  · refine' ⟨ Path.refl x₀, _, _ ⟩ <;> simp_all +decide [ Path.truncateOfLE ];
    grind;
  · obtain ⟨ δ, hδ₁, hδ₂ ⟩ := ih ( Nat.le_of_succ_le hn );
    -- Let `P := γ.truncateOfLE (hmono n)`; `∀ s, P s ∈ W n` by `truncateOfLE_apply` + `hmem n`.
    set P : Path (γ.extend (t n)) (γ.extend (t (n + 1))) := γ.truncateOfLE (hmono n)
    have hP : ∀ s, P s ∈ W n := by
      intro s
      simp [P, hmem];
      convert hmem n ( min ( max ( s : ℝ ) ( t n ) ) ( t ( n + 1 ) ) ) ⟨ _, _ ⟩ using 1 <;> norm_num [ hmono, hge0, hle1 ]
    generalize_proofs at *;
    -- Let `L := (β n).trans (P.trans (β (n+1)).symm)`; `∀ s, L s ∈ W n` by `trans_mem_of_mem`/`symm_mem_of_mem`, `hβR n`, `hβL (n+1)`, `hP`.
    set L : Path x₀ x₀ := (β n).trans (P.trans (β (n + 1)).symm)
    have hL : ∀ s, L s ∈ W n := by
      grind
    generalize_proofs at *;
    -- By `truncate_split`, `⟦γ.truncateOfLE (t0≤t(n+1))⟧ = ⟦γ.truncateOfLE (t0≤tn)⟧.trans ⟦P⟧`.
    have h_split : Path.Homotopic.Quotient.mk (γ.truncateOfLE (show t 0 ≤ t (n + 1) by linarith [hmono n])) = (Path.Homotopic.Quotient.mk (γ.truncateOfLE (show t 0 ≤ t n by linarith [hmono n]))).trans (Path.Homotopic.Quotient.mk P) := by
                                                                                                                                                            apply Quotient.sound
                                                                                                                                                            generalize_proofs at *;
                                                                                                                                                            apply Submission.VanKampen.truncate_split;
                                                                                                                                                            · exact hge0 0;
                                                                                                                                                            · exact hle1 _
    generalize_proofs at *;
    cases' hWUV n with hWU hWV;
    · use δ.trans L;
      refine' ⟨ _, _ ⟩
      all_goals generalize_proofs at *;
      · grind;
      · grind +revert;
    · -- By `hVnull`, `⟦L⟧ = 1` ⇒ `⟦β n⟧.trans ⟦P⟧ = ⟦β (n+1)⟧`.
      have hL_null : Path.Homotopic.Quotient.mk L = (Path.Homotopic.Quotient.refl x₀) := by
        have hL_null : Path.Homotopic L (Path.refl x₀) := by
          exact hVnull L fun s => hWV ▸ hL s
        generalize_proofs at *;
        exact Quotient.sound hL_null
      generalize_proofs at *;
      grind

/-- `q` composed with a cast of the constant loop is just `q` cast. -/
theorem trans_refl_cast {X : Type*} [TopologicalSpace X] {a b : X}
    (q : Path.Homotopic.Quotient a a) (hb : b = a) :
    q.trans ((Path.Homotopic.Quotient.refl a).cast rfl hb) = q.cast rfl hb := by
  subst hb
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  induction q using Quotient.ind with | _ p =>
  exact Quotient.sound (Path.Homotopic.trans_refl p)

/-- **Surjectivity of `incl_* : π₁(U) → π₁(X)`.** Under the cover hypotheses with `V` simply
connected (and `U ∩ V` path-connected to `x₀`), every loop in `X` at `x₀` is homotopic in `X` to a
loop lying entirely in `U`. -/
theorem loop_homotopic_into_U {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ)
    {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUconn : ∀ y ∈ U, JoinedIn U x₀ y)
    (hVconn : ∀ y ∈ V, JoinedIn V x₀ y)
    (hIconn : ∀ y ∈ U ∩ V, JoinedIn (U ∩ V) x₀ y)
    (hVnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ V) → Path.Homotopic p (Path.refl x₀))
    (γ : Path x₀ x₀) :
    ∃ δ : Path x₀ x₀, (∀ t, δ t ∈ U) ∧ Path.Homotopic γ δ := by
  classical
  obtain ⟨N, t, W, ht0, htN, hmono, hge0, hle1, hWUV, hmem⟩ :=
    Submission.VanKampen.subdivision_with_W hUo hVo hcov γ
  have h0 : γ.extend (t 0) = x₀ := by rw [ht0]; exact γ.extend_zero
  have hN : γ.extend (t N) = x₀ := by rw [htN]; exact γ.extend_one
  have hxW : ∀ n, x₀ ∈ W n := fun n => (hWUV n).elim (fun h => h ▸ hxU) (fun h => h ▸ hxV)
  have hendR : ∀ n, γ.extend (t n) ∈ W n := fun n => hmem n (t n) ⟨le_refl _, hmono n⟩
  have hendL : ∀ n, γ.extend (t n) ∈ W (n - 1) := by
    intro n; rcases n with _ | m
    · simpa using hendR 0
    · exact hmem m (t (m+1)) ⟨hmono m, le_refl _⟩
  have hβex : ∀ n, ∃ p : Path x₀ (γ.extend (t n)),
      (∀ s, p s ∈ W (n - 1)) ∧ (∀ s, p s ∈ W n) ∧
      (∀ he : γ.extend (t n) = x₀,
        Path.Homotopic.Quotient.mk p = (Path.Homotopic.Quotient.refl x₀).cast rfl he) := by
    intro n
    by_cases h : γ.extend (t n) = x₀
    · refine ⟨(Path.refl x₀).cast rfl h, ?_, ?_, ?_⟩
      · intro s; simpa using hxW (n-1)
      · intro s; simpa using hxW n
      · intro he; rw [Path.Homotopic.Quotient.mk_cast]; rfl
    · obtain ⟨p, hp1, hp2⟩ :=
        Submission.VanKampen.exists_connecting hUconn hVconn hIconn (hWUV (n-1)) (hWUV n)
          (hendL n) (hendR n)
      exact ⟨p, hp1, hp2, fun he => absurd he h⟩
  choose β hβL hβR hβtriv using hβex
  obtain ⟨δ, hδU, hδeq⟩ :=
    accumulate_into_U hxU hVnull γ N t W h0 hmono hge0 hle1 hWUV hmem β hβL hβR (hβtriv 0 h0)
      N (le_refl N)
  refine ⟨δ, hδU, ?_⟩
  have hfulleq : γ.truncateOfLE
      (show t 0 ≤ t N from (monotone_nat_of_le_succ hmono) (Nat.zero_le N)) = γ.cast h0 hN := by
    ext w
    rw [Submission.VanKampen.truncateOfLE_apply, Path.cast_coe]
    have hw := w.2
    rw [ht0, htN, max_eq_left hw.1, min_eq_left hw.2, γ.extend_extends']
  rw [hfulleq, Path.Homotopic.Quotient.mk_cast, hβtriv N hN] at hδeq
  -- hδeq : (⟦γ⟧).cast h0 hN = (⟦δ⟧.trans ((refl x₀).cast rfl hN)).cast h0 rfl
  rw [trans_refl_cast _ hN, Path.Homotopic.Quotient.cast_cast] at hδeq
  have : Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk δ := by
    have := congrArg (fun z => Path.Homotopic.Quotient.cast z h0.symm hN.symm) hδeq
    simpa [Path.Homotopic.Quotient.cast_cast] using this
  exact Quotient.exact this

/-- The continuous inclusion `↥U ↪ X`. -/
def inclU {X : Type*} [TopologicalSpace X] (U : Set X) : C(↥U, X) :=
  ⟨fun y => (y : X), continuous_subtype_val⟩

/-
**Non-abelianness transfers to the open piece `U`.**
-/
theorem noncomm_of_cover {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ)
    {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUconn : ∀ y ∈ U, JoinedIn U x₀ y)
    (hVconn : ∀ y ∈ V, JoinedIn V x₀ y)
    (hIconn : ∀ y ∈ U ∩ V, JoinedIn (U ∩ V) x₀ y)
    (hVnull : ∀ (p : Path x₀ x₀), (∀ t, p t ∈ V) → Path.Homotopic p (Path.refl x₀))
    (hX : ∃ (x : X) (a b : FundamentalGroup X x), a * b ≠ b * a) :
    ∃ (x : ↥U) (a b : FundamentalGroup (↥U) x), a * b ≠ b * a := by
  contrapose! hX;
  have h_surjective : ∀ γ : Path x₀ x₀, ∃ δ : Path x₀ x₀, (∀ t, δ t ∈ U) ∧ Path.Homotopic γ δ := by
    apply loop_homotopic_into_U hUo hVo hcov hxU hxV hUconn hVconn hIconn hVnull;
  have h_surjective : ∀ γ : FundamentalGroup X x₀, ∃ δ : FundamentalGroup U ⟨x₀, hxU⟩, FundamentalGroup.map (inclU U) ⟨x₀, hxU⟩ δ = γ := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : Path x₀ x₀, FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ') = γ := by
      obtain ⟨ γ', hγ' ⟩ := γ;
      exact ⟨ ⟨ γ', hγ', by assumption ⟩, rfl ⟩;
    obtain ⟨ δ, hδ₁, hδ₂ ⟩ := h_surjective γ';
    have hδ₃ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) = FundamentalGroup.map (inclU U) ⟨x₀, hxU⟩ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.mk (⟨fun t => ⟨δ t, hδ₁ t⟩, by
      exact Continuous.subtype_mk ( δ.continuous ) _⟩) (by
    exact Subtype.ext ( δ.source' )) (by
    exact Subtype.ext ( δ.target' ))))) := by
      congr
    generalize_proofs at *;
    have hδ₄ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ') = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) := by
      exact congr_arg _ ( Quotient.sound hδ₂ );
    grind;
  have h_surjective : ∀ a b : FundamentalGroup X x₀, a * b = b * a := by
    intro a b; obtain ⟨ δ₁, rfl ⟩ := h_surjective a; obtain ⟨ δ₂, rfl ⟩ := h_surjective b; simp +decide [ hX ] ;
    convert congr_arg ( FundamentalGroup.map ( inclU U ) ⟨ x₀, hxU ⟩ ) ( hX ⟨ x₀, hxU ⟩ δ₁ δ₂ ) using 1;
    · simp +decide [ FundamentalGroup.map, Path.Homotopic.Quotient.map ];
      congr! 1;
    · simp +decide [ FundamentalGroup.map, Path.Homotopic.Quotient.map ];
      congr! 1;
  intro x a b;
  obtain ⟨p, hp⟩ : ∃ p : Path x₀ x, True := by
    by_cases hx : x ∈ U ∨ x ∈ V;
    · cases' hx with hx hx;
      · obtain ⟨ p, hp ⟩ := hUconn x hx;
        exact ⟨ p, trivial ⟩;
      · obtain ⟨ p, hp ⟩ := hVconn x hx;
        exact ⟨ p, trivial ⟩;
    · exact False.elim ( hx ( hcov.symm.subset ( Set.mem_univ x ) ) );
  have h_iso : Nonempty (FundamentalGroup X x ≃* FundamentalGroup X x₀) := by
    exact ⟨ FundamentalGroup.fundamentalGroupMulEquivOfPath p.symm ⟩;
  obtain ⟨ f ⟩ := h_iso;
  exact f.injective ( by simp +decide [ h_surjective ] )

end Submission.Pi1Iso