/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.H1Finite

/-!
# The χ ledger (`finiteness-and-chi`, gated file 3/3)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §8).

* `finiteDimensional_linSys`: `FiniteDimensional ℂ (LinSys D)` for ALL `D` (same six-term
  bookkeeping recipe as `H1Finite.lean`'s all-`D` step, applied to `windowMap` instead of
  `H1Incl`).
* `h1`/`chi`: the χ ledger's frozen definitions (`chi D := (l D : ℤ) − (h1 D : ℤ)`).
* `sixterm_ranks`: the shared rank bookkeeping fact behind every monotonicity/ledger lemma —
  four rank-nullity applications along cech's six-term fragment
  `0 → L(D) → L(D') → Window D D' → H¹(D) → H¹(D') → 0`, packaged as two witness naturals.
* `chi_of_le`/`chi_eq_chi_zero_add_degree`: the ledger identity `chi D' = chi D + deg(D'−D)`
  and its `D = 0`-anchored specialization.
* `chi_zero_add_degree_le_l`/`exists_ne_zero_mem_linSys`: the Riemann-inequality seed
  canonical-forms' Existence gate consumes (Forster 16.11 pattern), at the exact names/shapes
  `docs/design/canonical-forms.md` §D9 records.
* `l_mono`/`l_le_l_add_degree`/`h1_le_of_le`/`h1_le_h1_add_degree`: monotonicity corollaries.
-/

open scoped ContDiff Manifold
open Set Filter Topology TopologicalSpace RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable [T1Space X] [T2Space X] [CompactSpace X]

/-! ### All-`D` finiteness of `L(D)` (same recipe as `H1Finite.lean`'s all-`D` step) -/

/-- **All-`D` finiteness of the linear system**: `L(D)` is finite-dimensional for every `D`.
With `D' := D ⊔ 0`: `windowMap (0 ≤ D') : L(D') →ₗ Window 0 D'` has finite-dimensional kernel
(`= range` of the injective inclusion `L(0) ↪ L(D')`, cech's `exact_inclusion_windowMap`) and
finite-dimensional codomain (`Window 0 D'`), so `L(D')` is finite; `L(D) ≤ L(D')` finishes it. -/
instance finiteDimensional_linSys [ConnectedSpace X] (D : RS.Divisor X) :
    FiniteDimensional ℂ (RS.LinSys D) := by
  set D' := D ⊔ 0 with hD'_def
  have h0 : (0 : RS.Divisor X) ≤ D' := le_sup_right
  have h : D ≤ D' := le_sup_left
  have hz : FiniteDimensional ℂ (RS.LinSys (0 : RS.Divisor X)) := by
    rw [show RS.LinSys (0 : RS.Divisor X) = Submodule.span ℂ {1} from RS.linSys_zero_eq_span_one]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton 1)
  have hWfin : FiniteDimensional ℂ (Window (0 : RS.Divisor X) D') :=
    finiteDimensional_window (0 : RS.Divisor X) D' h0
  have hexact : LinearMap.ker (windowMap h0) =
      LinearMap.range (Submodule.inclusion (RS.linSys_mono h0)) :=
    (LinearMap.exact_iff).1 (exact_inclusion_windowMap h0)
  have hkerfin : FiniteDimensional ℂ (LinearMap.ker (windowMap h0)) := by
    rw [hexact]; exact LinearMap.finiteDimensional_range _
  have hD'fin : FiniteDimensional ℂ (RS.LinSys D') :=
    FiniteDimensional.of_linearMap_ker_range (windowMap h0)
  exact Submodule.finiteDimensional_of_le (RS.linSys_mono h)

/-! ### The χ ledger's frozen definitions -/

/-- `h¹(D)`: the dimension of the first Čech cohomology of `𝒪_D`. -/
noncomputable def h1 (D : RS.Divisor X) : ℕ := Module.finrank ℂ (H1 D)

/-- The Euler characteristic `χ(D) = l(D) - h¹(D)`. -/
noncomputable def chi (D : RS.Divisor X) : ℤ := (RS.l D : ℤ) - (h1 D : ℤ)

/-! ### The shared six-term rank bookkeeping -/

omit [T1Space X] in
/-- The four rank-nullity applications along the six-term fragment
`0 → L(D) → L(D') → Window D D' → H¹(D) → H¹(D') → 0`, packaged as two witness naturals `p, q`
(`p` = the drop in `l` from `D` to `D'`, `q` = the drop in `h1` from `D` to `D'`). -/
private theorem sixterm_rank1 [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    RS.l D' = RS.l D + Module.finrank ℂ (LinearMap.range (windowMap h)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (windowMap h)
  have hexact : LinearMap.ker (windowMap h) =
      LinearMap.range (Submodule.inclusion (RS.linSys_mono h)) :=
    (LinearMap.exact_iff).1 (exact_inclusion_windowMap h)
  rw [hexact] at hrn
  have hrange_eq : Module.finrank ℂ
      (LinearMap.range (Submodule.inclusion (RS.linSys_mono h))) = RS.l D := by
    rw [RS.l]
    exact (LinearEquiv.ofInjective _ (inclusion_injective h)).finrank_eq.symm
  rw [hrange_eq] at hrn
  change RS.l D' = RS.l D + Module.finrank ℂ (LinearMap.range (windowMap h))
  unfold RS.l at hrn ⊢
  omega

omit [T1Space X] in
private theorem sixterm_rank2 [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    Module.finrank ℂ (Window D D') = Module.finrank ℂ (LinearMap.range (windowMap h)) +
      Module.finrank ℂ (LinearMap.range (windowConnect h)) := by
  have hWfin : FiniteDimensional ℂ (Window D D') := finiteDimensional_window D D' h
  have hrn := LinearMap.finrank_range_add_finrank_ker (windowConnect h)
  have hexact : LinearMap.ker (windowConnect h) = LinearMap.range (windowMap h) :=
    (LinearMap.exact_iff).1 (exact_windowMap_windowConnect h)
  rw [hexact] at hrn
  omega

omit [T1Space X] in
private theorem sixterm_rank3 {D D' : RS.Divisor X} (h : D ≤ D') :
    h1 D = Module.finrank ℂ (LinearMap.range (windowConnect h)) + h1 D' := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (H1Incl D h)
  have hexact : LinearMap.ker (H1Incl D h) = LinearMap.range (windowConnect h) :=
    (LinearMap.exact_iff).1 (exact_windowConnect_H1Incl h)
  rw [hexact] at hrn
  have hsurj : LinearMap.range (H1Incl D h) = ⊤ :=
    LinearMap.range_eq_top.2 (H1Incl_surjective h)
  have hrange_eq : Module.finrank ℂ (LinearMap.range (H1Incl D h)) = h1 D' := by
    rw [hsurj]
    change Module.finrank ℂ (⊤ : Submodule ℂ (H1 D')) = Module.finrank ℂ (H1 D')
    exact finrank_top ℂ (H1 D')
  rw [hrange_eq] at hrn
  change h1 D = Module.finrank ℂ (LinearMap.range (windowConnect h)) + h1 D'
  unfold RS.Finiteness.h1 at hrn ⊢
  omega

omit [T1Space X] in
theorem sixterm_ranks [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    ∃ p q : ℕ, RS.l D' = RS.l D + p ∧ Module.finrank ℂ (Window D D') = p + q ∧
      h1 D = q + h1 D' :=
  ⟨Module.finrank ℂ (LinearMap.range (windowMap h)),
    Module.finrank ℂ (LinearMap.range (windowConnect h)),
    sixterm_rank1 h, sixterm_rank2 h, sixterm_rank3 h⟩

omit [T1Space X] in
theorem l_mono [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') : RS.l D ≤ RS.l D' := by
  obtain ⟨p, q, hp, -, -⟩ := sixterm_ranks h
  omega

omit [T1Space X] in
theorem l_le_l_add_degree [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    RS.l D' ≤ RS.l D + ((D' - D).degree).toNat := by
  obtain ⟨p, q, hp, hpq, -⟩ := sixterm_ranks h
  rw [finrank_window h] at hpq
  omega

omit [T1Space X] in
theorem h1_le_of_le [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') : h1 D' ≤ h1 D := by
  obtain ⟨p, q, -, -, hq⟩ := sixterm_ranks h
  omega

omit [T1Space X] in
theorem h1_le_h1_add_degree [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    h1 D ≤ h1 D' + ((D' - D).degree).toNat := by
  obtain ⟨p, q, -, hpq, hq⟩ := sixterm_ranks h
  rw [finrank_window h] at hpq
  omega

omit [T1Space X] in
/-- **The ledger step**: `χ(D') = χ(D) + deg(D' − D)` for `D ≤ D'`. -/
theorem chi_of_le [ConnectedSpace X] {D D' : RS.Divisor X} (h : D ≤ D') :
    chi D' = chi D + (D' - D).degree := by
  obtain ⟨p, q, hp, hpq, hq⟩ := sixterm_ranks h
  rw [finrank_window h] at hpq
  have hnn : (0 : ℤ) ≤ (D' - D).degree :=
    Function.locallyFinsuppWithin.degree_nonneg_of_nonneg (sub_nonneg.2 h)
  have hcast : (((D' - D).degree).toNat : ℤ) = (D' - D).degree := Int.toNat_of_nonneg hnn
  unfold chi
  omega

/-! ### `Divisor.single` bookkeeping (Compat: `degree_single` not upstreamed) -/

open scoped Classical in
omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] in
theorem degree_single (P : X) :
    (Function.locallyFinsuppWithin.single P (1 : ℤ) : RS.Divisor X).degree = 1 := by
  classical
  rw [Function.locallyFinsuppWithin.degree_eq_sum_of_subset
    (S := ({P} : Finset X)) (fun x hx => by
      simp only [Function.mem_support, ne_eq] at hx
      by_contra hxP
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hxP
      exact hx (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hxP]))]
  simp

open scoped Classical in
omit [T1Space X] in
theorem chi_single_add [ConnectedSpace X] (D : RS.Divisor X) (P : X) :
    chi (D + Function.locallyFinsuppWithin.single P (1 : ℤ)) = chi D + 1 := by
  have hle : D ≤ D + Function.locallyFinsuppWithin.single P (1 : ℤ) := by
    refine le_add_of_nonneg_right ?_
    exact Function.locallyFinsuppWithin.single_nonneg.mpr (by norm_num)
  have hdeg : ((D + Function.locallyFinsuppWithin.single P (1 : ℤ)) - D).degree = 1 := by
    rw [add_sub_cancel_left, degree_single]
  rw [chi_of_le hle, hdeg]

omit [T1Space X] in
/-- **§8's anchor**: `χ(D) = χ(0) + deg D` for every `D` (no induction — derive from
`chi_of_le` twice at `D' := D ⊔ 0`). -/
theorem chi_eq_chi_zero_add_degree [ConnectedSpace X] (D : RS.Divisor X) :
    chi D = chi (0 : RS.Divisor X) + D.degree := by
  set D' := D ⊔ 0 with hD'_def
  have e1 := chi_of_le (D := D) (D' := D') le_sup_left
  have e2 := chi_of_le (D := (0 : RS.Divisor X)) (D' := D') le_sup_right
  have hdeg1 : (D' - D).degree = D'.degree - D.degree := by
    rw [sub_eq_add_neg, Function.locallyFinsuppWithin.degree_add,
      Function.locallyFinsuppWithin.degree_neg]
    ring
  have hdeg2 : (D' - (0 : RS.Divisor X)).degree = D'.degree := by rw [sub_zero]
  rw [hdeg1] at e1
  rw [hdeg2] at e2
  omega

omit [T1Space X] in
/-- **The Riemann-inequality seed** (canonical-forms' workhorse): `χ(0) + deg D ≤ l(D)`. -/
theorem chi_zero_add_degree_le_l [ConnectedSpace X] (D : RS.Divisor X) :
    chi (0 : RS.Divisor X) + D.degree ≤ (RS.l D : ℤ) := by
  rw [← chi_eq_chi_zero_add_degree D]
  unfold chi
  have : (0 : ℤ) ≤ (h1 D : ℤ) := Int.natCast_nonneg _
  omega

omit [T1Space X] in
/-- **The existence half** (Forster 16.11 pattern): once `χ(0) + deg D > 0`, `L(D)` is
nontrivial. -/
theorem exists_ne_zero_mem_linSys [ConnectedSpace X] {D : RS.Divisor X}
    (h : 0 < chi (0 : RS.Divisor X) + D.degree) : ∃ f ∈ RS.LinSys D, f ≠ 0 := by
  have hle := chi_zero_add_degree_le_l D
  have hpos : (0 : ℤ) < (RS.l D : ℤ) := lt_of_lt_of_le h hle
  have hposNat : 0 < RS.l D := by exact_mod_cast hpos
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hposNat
  exact ⟨(x : RS.Mero X), x.2, fun hc => hx0 (Subtype.ext hc)⟩

end RS.Finiteness
