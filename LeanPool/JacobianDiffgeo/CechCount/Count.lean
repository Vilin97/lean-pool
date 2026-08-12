/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CechCount.Surjective
import LeanPool.JacobianDiffgeo.Finiteness
import LeanPool.JacobianDiffgeo.RiemannRoch
import LeanPool.JacobianDiffgeo.ProperDegree
import LeanPool.JacobianDiffgeo.CanonicalForms

/-!
# The Čech count: `dim H¹(𝒪_X) ≤ genus X` (cechcount unit, Forster 17.9/17.16)

The final theorem of the challenge. Write `g := genus X`, `h⁰¹ := dim_ℂ H¹(𝒪_X)` (Čech).

**Step 1 (the ledger).** For a point `P` and any `n > 2g - 2`, Riemann–Roch
(`RS.riemannRoch` + `linSys_eq_bot_of_degree_neg'` + `deg_canonical`) gives
`l(nP) = n + 1 - g`, and the Čech χ-ledger (`RS.Finiteness.chi_eq_chi_zero_add_degree`,
with `l(0) = 1`) turns this into the **constancy** `h¹(nP) = h⁰¹ - g` — independent of `n`.

**Step 2 (the growth contradiction, Forster 17.9's count in primal form).** Suppose
`h⁰¹ > g`, so `c := h⁰¹ - g ≥ 1` and `h¹(nP) = c > 0` for every large `n`. Fix
`ξ ≠ 0` in `H¹(n₀P)` (possible since `dim = c > 0`) and consider the linear map
`Φ : L(mP) →ₗ H¹((n₀+m)P)`, `f ↦ (f·) ξ` (the Čech multiplication `mulH1`). For
`m := g + h⁰¹ + 1` the domain has dimension `m + 1 - g = h⁰¹ + 2 > c`, the target
dimension `c`, so `Φ` is not injective: some `f ≠ 0` in `L(mP)` has `(f·) ξ = 0`. But
multiplication by a nonzero `f` is *surjective* `H¹(n₀P) → H¹((n₀+m)P)`
(`mulH1_surjective`, Forster 17.8) between spaces of the *same* finite dimension `c`,
hence injective — forcing `ξ = 0`. Contradiction; so `h⁰¹ ≤ g`.

Exports: `RS.cechCount` (= `RS.finrank_H1_zero_le_genus`).
-/

open scoped ContDiff Manifold
open Set TopologicalSpace


namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `l(nP) = n + 1 - g` for `n > 2g - 2` (Riemann–Roch with vanishing speciality index). -/
private theorem l_single_eq [DecidableEq X] (P : X) {n : ℤ}
    (hn : 2 * (genus X : ℤ) - 2 < n) :
    (RS.l (Function.locallyFinsuppWithin.single P n : RS.Divisor X) : ℤ)
      = n + 1 - (genus X : ℤ) := by
  obtain ⟨θ₀, hθ₀⟩ := RS.exists_ne_zero_mform (X := X)
  have hdeg : (Function.locallyFinsuppWithin.single P n : RS.Divisor X).degree = n :=
    Function.locallyFinsuppWithin.degree_single P n
  have hKdeg : (RS.canonicalDivisorOf θ₀ -
      (Function.locallyFinsuppWithin.single P n : RS.Divisor X)).degree
      = 2 * (genus X : ℤ) - 2 - n := by
    rw [sub_eq_add_neg, Function.locallyFinsuppWithin.degree_add,
      Function.locallyFinsuppWithin.degree_neg, RS.deg_canonical hθ₀, hdeg]
    ring
  have hKneg : (RS.canonicalDivisorOf θ₀ -
      (Function.locallyFinsuppWithin.single P n : RS.Divisor X)).degree < 0 := by
    rw [hKdeg]; omega
  have hlK : RS.l (RS.canonicalDivisorOf θ₀ -
      (Function.locallyFinsuppWithin.single P n : RS.Divisor X)) = 0 := by
    have hbot := RS.linSys_eq_bot_of_degree_neg' _ hKneg
    unfold RS.l
    rw [hbot]
    exact finrank_bot ℂ (ℳ X)
  have hRR := RS.riemannRoch hθ₀ (Function.locallyFinsuppWithin.single P n : RS.Divisor X)
  rw [hlK, hdeg] at hRR
  push_cast at hRR
  omega

/-- **Constancy of `h¹(nP)`** for `n > 2g - 2`: the Čech χ-ledger plus Riemann–Roch give
`h¹(nP) = h¹(0) - g`, independent of `n`. -/
private theorem h1_single_eq [DecidableEq X] (P : X) {n : ℤ}
    (hn : 2 * (genus X : ℤ) - 2 < n) :
    (RS.Finiteness.h1 (Function.locallyFinsuppWithin.single P n : RS.Divisor X) : ℤ)
      = (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) - (genus X : ℤ) := by
  have hchi := RS.Finiteness.chi_eq_chi_zero_add_degree
    (Function.locallyFinsuppWithin.single P n : RS.Divisor X)
  simp only [RS.Finiteness.chi] at hchi
  rw [Function.locallyFinsuppWithin.degree_single P n, RS.l_zero, l_single_eq P hn] at hchi
  push_cast at hchi
  omega

/-- **The Čech count** (the final theorem of the challenge; Forster §17.9's dimension count,
Hodge-free): the first Čech cohomology of the structure sheaf has dimension at most the genus. -/
theorem cechCount : Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) ≤ genus X := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : genus X < dim H¹(𝒪)`; abbreviate `g`, `h0` at the integer level.
  have hg : (genus X : ℤ) < (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) := by
    exact_mod_cast hcon
  have hg0 : (0 : ℤ) ≤ (genus X : ℤ) := Int.natCast_nonneg _
  have hh00 : (0 : ℤ) ≤ (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) := Int.natCast_nonneg _
  obtain ⟨P⟩ : Nonempty X := inferInstance
  -- The three divisors `n₀P`, `mP`, `(n₀+m)P` with `n₀ := 2g`, `m := g + h0 + 1`.
  set D₀ : RS.Divisor X :=
    Function.locallyFinsuppWithin.single P (2 * (genus X : ℤ)) with hD₀def
  set B : RS.Divisor X := Function.locallyFinsuppWithin.single P
    ((genus X : ℤ) + (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) + 1) with hBdef
  set E : RS.Divisor X := Function.locallyFinsuppWithin.single P
    (3 * (genus X : ℤ) + (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) + 1) with hEdef
  -- Their dimension data from the ledger.
  have hhD₀ : (RS.Finiteness.h1 D₀ : ℤ)
      = (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) - (genus X : ℤ) := by
    rw [hD₀def]; exact h1_single_eq P (by omega)
  have hhE : (RS.Finiteness.h1 E : ℤ)
      = (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) - (genus X : ℤ) := by
    rw [hEdef]; exact h1_single_eq P (by omega)
  have hlB : (RS.l B : ℤ) = (RS.Finiteness.h1 (0 : RS.Divisor X) : ℤ) + 2 := by
    rw [hBdef]
    rw [l_single_eq P (by omega)]
    ring
  -- A nonzero class `ξ ∈ H¹(D₀)` (dimension `h0 - g ≥ 1 > 0`).
  have hpos : 0 < Module.finrank ℂ (RS.Cech.H1 D₀) := by
    have hZ : (0 : ℤ) < (RS.Finiteness.h1 D₀ : ℤ) := by omega
    exact_mod_cast hZ
  have hnt : Nontrivial (RS.Cech.H1 D₀) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨ξ, hξ0⟩ := exists_ne (0 : RS.Cech.H1 D₀)
  -- Every element of `L(B)` multiplies `H¹(D₀)` into `H¹(E)`.
  have hbound : ∀ q : RS.LinSys B, RS.Cech.MulBound (q : ℳ X) D₀ E := fun q =>
    RS.Cech.mulBound_of_mem_linSys q.2 (fun x => by
      rw [hD₀def, hBdef, hEdef]
      simp only [Function.locallyFinsuppWithin.single_apply]
      by_cases hx : x = P
      · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx]; omega
      · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]; omega)
  -- The evaluation map `Φ : L(B) →ₗ H¹(E)`, `q ↦ (q·) ξ`.
  let Φ : RS.LinSys B →ₗ[ℂ] RS.Cech.H1 E :=
    { toFun := fun q => RS.Cech.mulH1 (q : ℳ X) (hbound q) ξ
      map_add' := fun q r =>
        RS.Cech.mulH1_add (hbound q) (hbound r) (hbound (q + r)) ξ
      map_smul' := fun a q =>
        RS.Cech.mulH1_smul a (hbound q) (hbound (a • q)) ξ }
  -- `Φ` cannot be injective: `dim L(B) = h0 + 2 > h0 - g = dim H¹(E)`.
  have hninj : ¬ Function.Injective Φ := by
    intro hinj
    have hle : Module.finrank ℂ (RS.LinSys B) ≤ Module.finrank ℂ (RS.Cech.H1 E) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have hleZ : (RS.l B : ℤ) ≤ (RS.Finiteness.h1 E : ℤ) := by exact_mod_cast hle
    omega
  obtain ⟨q, r, hqr, hne⟩ := Function.not_injective_iff.mp hninj
  -- The difference is a nonzero function killed by `ξ` under multiplication.
  have hf0 : ((q - r : RS.LinSys B) : ℳ X) ≠ 0 := by
    intro h0eq
    rw [AddSubgroupClass.coe_sub, sub_eq_zero] at h0eq
    exact hne (Subtype.ext h0eq)
  have hker : RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r)) ξ = 0 := by
    have hsub : Φ (q - r) = 0 := by rw [map_sub, hqr, sub_self]
    exact hsub
  -- But multiplication by a nonzero function is surjective between equal finite dimensions,
  -- hence injective — contradiction.
  have hsurj : Function.Surjective
      (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r))) :=
    RS.Cech.mulH1_surjective hf0 _
  have hrange : LinearMap.range
      (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r))) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r)))
  rw [hrange, finrank_top] at hrk
  have hfr : Module.finrank ℂ (RS.Cech.H1 E) = Module.finrank ℂ (RS.Cech.H1 D₀) := by
    have hZ : (RS.Finiteness.h1 E : ℤ) = (RS.Finiteness.h1 D₀ : ℤ) := by omega
    exact_mod_cast hZ
  have hker0 : Module.finrank ℂ
      (LinearMap.ker (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r)))) = 0 := by
    omega
  have hbot : LinearMap.ker
      (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r))) = ⊥ :=
    Submodule.finrank_eq_zero.mp hker0
  have hmem : ξ ∈ LinearMap.ker
      (RS.Cech.mulH1 ((q - r : RS.LinSys B) : ℳ X) (hbound (q - r))) := hker
  rw [hbot, Submodule.mem_bot] at hmem
  exact hξ0 hmem

/-- Alias for `cechCount` in the project's descriptive naming style. -/
theorem finrank_H1_zero_le_genus :
    Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) ≤ genus X :=
  cechCount

end RS
