/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

public import Mathlib.Tactic
public import LeanPool.SalemTheorem.PdtPisotLadder
public import LeanPool.SalemTheorem.PdtSalemCircle
public import LeanPool.SalemTheorem.PdtSalemArith
public import LeanPool.SalemTheorem.PdtSalemMinus
public import LeanPool.SalemTheorem.PdtSalemEndgame
public import LeanPool.SalemTheorem.PdtSalemQuadUnit

/-!
# SalemPisot — Salem's theorem for Pisot numbers, and the two
constructions with their family roots exposed

The bridge from a Pisot number to the Pisot-pattern data of its minimal
polynomial; Salem's theorem stated for Pisot numbers (every Pisot number
is a limit of Salem numbers from both sides); and the two constructions
of the proof modules re-run with the index `m` and the family
polynomial kept in the conclusion.

A Pisot number is a real algebraic integer `α > 1` all of whose other
complex conjugates lie strictly inside the unit circle; it is spelled
here as `1 < α`, `IsIntegral ℤ α`, and
`∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ α → ‖z‖ < 1`.

* `pattern_of_simple_root`: a monic integer polynomial with a simple
  complex root `α` (root multiplicity exactly one) whose other complex
  roots lie strictly inside the unit circle carries the Pisot-pattern
  data — the multiset `inside` of its other roots is interior and
  conjugation-closed, and the complex image factors as
  `(X − α)·∏ (X − z)`, the product over `inside`.  The conjugation
  closure comes from the integer coefficients (`Splits.roots_map`
  against the cast triangle), the factorization from
  `Splits.eq_prod_roots_of_monic` and `Multiset.cons_erase`.
* `pattern_of_pisot`: the minimal polynomial over `ℤ` of a Pisot number
  carries the pattern data.  Ingredients: the Gauss step
  `minpoly ℚ α = (minpoly ℤ α).map ℚ` (`ℤ` is integrally closed), the
  separability of the irreducible `minpoly ℚ α` in characteristic zero
  (so `α` is a simple root of its complex image), and the identification
  of the complex roots with `(minpoly ℚ α).aroots ℂ`.
* `salem_theorem`: **Salem's theorem** for Pisot numbers — for every
  `ε > 0` there is a Salem number in `(α − ε, α)` and one in
  `(α, α + ε)` — by transport through `salem_theorem_full`.
* `salem_construction_two_sided`: the assembly
  `PdtSalemEndgame.salem_two_sided` re-run keeping the index and the
  root equation — under the Pisot pattern and `P(1/α) ≠ 0`, with
  `e = ±1` the sign of `P(1/α)`, some `X^m·P + e·P.reverse` (`m ≥ 2`)
  has a Salem root in `(α − ε, α)` and some `X^m·P − e·P.reverse`
  (`m ≥ 2`) one in `(α, α + ε)`; the halves `exists_salem_below_root`
  and `exists_salem_above_root` are the ladder lemmas of
  `PdtSalemEndgame` with the root kept.
* `salem_quadratic_unit`: `PdtSalemQuadUnit.salem_two_sided_quad_unit`
  re-run keeping the index and the root equation, the family spelled
  as `(X² − rX + 1)(X^{2m} + 1) ± X^{m+1}` (`m ≥ 1`).
-/

@[expose] public section

namespace PDT
namespace SalemPisot

noncomputable section
open Polynomial

/-! ### The pattern data from a simple dominant root -/

/-- **The Pisot-pattern data from a simple root.**  For a monic integer
polynomial whose complex image has `α` as a root of multiplicity exactly
one and every other complex root strictly inside the unit circle, the
multiset `inside = roots.erase α` satisfies the three pattern
hypotheses: strict interiority, conjugation closure, and the
factorization `Pz = SalemCircle.P α inside`. -/
theorem pattern_of_simple_root (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (hsimple : Polynomial.rootMultiplicity ((alpha : ℂ)) (Pz.map (Int.castRingHom ℂ)) = 1)
    (hsmall : ∀ z : ℂ, (Pz.map (Int.castRingHom ℂ)).eval z = 0 → z ≠ ((alpha : ℂ)) → ‖z‖ < 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside := by
  classical
  set pC : Polynomial ℂ := Pz.map (Int.castRingHom ℂ) with hpC
  have hCmonic : pC.Monic := hmonic.map _
  have hCne : pC ≠ 0 := hCmonic.ne_zero
  have hsplits : pC.Splits := IsAlgClosed.splits pC
  have hroot : pC.eval ((alpha : ℂ)) = 0 := by
    have h1 : 0 < Polynomial.rootMultiplicity ((alpha : ℂ)) pC := by
      rw [hsimple]; exact one_pos
    exact (Polynomial.rootMultiplicity_pos hCne).mp h1
  have hmem : ((alpha : ℂ)) ∈ pC.roots := Polynomial.mem_roots'.mpr ⟨hCne, hroot⟩
  have hcount : pC.roots.count ((alpha : ℂ)) = 1 := by
    rw [Polynomial.count_roots]; exact hsimple
  have hnotin : ((alpha : ℂ)) ∉ pC.roots.erase ((alpha : ℂ)) := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, hcount]
  refine ⟨pC.roots.erase ((alpha : ℂ)), ?_, ?_, ?_⟩
  · -- strict interiority
    intro z hz
    have hzmem : z ∈ pC.roots := Multiset.mem_of_mem_erase hz
    have hzroot : pC.eval z = 0 := (Polynomial.mem_roots'.mp hzmem).2
    have hzne : z ≠ ((alpha : ℂ)) := fun h => hnotin (h ▸ hz)
    exact hsmall z hzroot hzne
  · -- conjugation closure
    have hmapconj : pC.map (starRingEnd ℂ) = pC := by
      rw [hpC, Polynomial.map_map,
        show (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from
          RingHom.ext_int _ _]
    have hroots_conj : pC.roots.map (starRingEnd ℂ) = pC.roots := by
      have h1 := hsplits.roots_map (starRingEnd ℂ)
      rw [hmapconj] at h1
      exact h1.symm
    rw [Multiset.map_erase _ (starRingEnd ℂ).injective, hroots_conj,
      Complex.conj_ofReal]
  · -- the factorization
    have hfac : pC = (pC.roots.map fun a => X - Polynomial.C a).prod :=
      hsplits.eq_prod_roots_of_monic hCmonic
    have hcons : ((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ)) = pC.roots :=
      Multiset.cons_erase hmem
    calc pC = (pC.roots.map fun a => X - Polynomial.C a).prod := hfac
      _ = ((((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ))).map
            fun a => X - Polynomial.C a).prod := by rw [hcons]
      _ = (X - Polynomial.C ((alpha : ℂ)))
          * ((pC.roots.erase ((alpha : ℂ))).map fun a => X - Polynomial.C a).prod := by
          rw [Multiset.map_cons, Multiset.prod_cons]
      _ = SalemCircle.P alpha (pC.roots.erase ((alpha : ℂ))) := rfl

/-! ### The pattern data of a Pisot number's minimal polynomial -/

/-- **The minimal polynomial of a Pisot number carries the pattern.**
For a real algebraic integer `α` every other complex root of whose
minimal polynomial over `ℚ` lies strictly inside the unit circle,
`minpoly ℤ α` (monic) has the Pisot-pattern data: its complex image is
`(X − α)·∏ (X − z)` over an interior, conjugation-closed multiset.  The
Gauss step identifies `minpoly ℚ α` with the rational image of
`minpoly ℤ α`; irreducibility gives separability in characteristic
zero, so `α` is a simple root of the complex image. -/
theorem pattern_of_pisot (alpha : ℝ) (hint : IsIntegral ℤ alpha)
    (hsmall : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      (minpoly ℤ alpha).map (Int.castRingHom ℂ) = SalemCircle.P alpha inside := by
  classical
  have hQint : IsIntegral ℚ alpha := hint.tower_top
  -- the Gauss step: `ℤ` is integrally closed
  have hmz : minpoly ℚ alpha = (minpoly ℤ alpha).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  -- the complex image of `minpoly ℤ α` is the complex image of `minpoly ℚ α`
  have hmapC : (minpoly ℤ alpha).map (Int.castRingHom ℂ)
      = (minpoly ℚ alpha).map (algebraMap ℚ ℂ) := by
    rw [hmz, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from
        RingHom.ext_int _ _]
  have hmonicC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Monic :=
    (minpoly.monic hQint).map _
  have hCne : (minpoly ℚ alpha).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  -- separability in characteristic zero: the complex roots are distinct
  have hsepC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Separable :=
    (minpoly.irreducible hQint).separable.map
  have hnodup : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  -- `α` is a root of the complex image
  have hroot : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).eval ((alpha : ℂ)) = 0 := by
    rw [← SalemArith.aeval_eq_eval_map, SalemArith.aeval_ofReal, minpoly.aeval,
      Complex.ofReal_zero]
  have hmem : ((alpha : ℂ)) ∈ ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots :=
    Polynomial.mem_roots'.mpr ⟨hCne, hroot⟩
  have hsimple : Polynomial.rootMultiplicity ((alpha : ℂ))
      ((minpoly ℤ alpha).map (Int.castRingHom ℂ)) = 1 := by
    rw [hmapC, ← Polynomial.count_roots]
    exact Multiset.count_eq_one_of_mem hnodup hmem
  -- every other complex root is an element of `aroots`, hence interior
  have hsmall' : ∀ z : ℂ, ((minpoly ℤ alpha).map (Int.castRingHom ℂ)).eval z = 0 →
      z ≠ ((alpha : ℂ)) → ‖z‖ < 1 := by
    intro z hz hzne
    rw [hmapC] at hz
    have hzmem : z ∈ (minpoly ℚ alpha).aroots ℂ := by
      rw [Polynomial.aroots_def]
      exact Polynomial.mem_roots'.mpr ⟨hCne, hz⟩
    exact hsmall z hzmem hzne
  exact pattern_of_simple_root (minpoly ℤ alpha) (minpoly.monic hint) alpha hsimple hsmall'

/-! ### Salem's theorem for Pisot numbers -/

/-- **Salem's theorem.**  Every Pisot number `α` — a real algebraic
integer `α > 1` whose other complex conjugates lie strictly inside the
unit circle — is a limit of Salem numbers from both sides: for every
`ε > 0` there is a Salem number in `(α − ε, α)` and one in
`(α, α + ε)`.  Transported through `salem_theorem_full` along the
pattern data of `minpoly ℤ α`. -/
theorem salem_theorem (alpha : ℝ) (halpha : 1 < alpha) (hint : IsIntegral ℤ alpha)
    (hsmall : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps) := by
  obtain ⟨inside, hin, hconj, hfacC⟩ := pattern_of_pisot alpha hint hsmall
  exact SalemQuadUnit.salem_theorem_full (minpoly ℤ alpha) (minpoly.monic hint)
    alpha halpha inside hin hconj hfacC eps heps

/-! ### The constructions with their family roots exposed

The two module assemblies (`PdtSalemEndgame.salem_two_sided` and
`PdtSalemQuadUnit.salem_two_sided_quad_unit`) conclude with a Salem
number in each window and discard the index `m` and the family
polynomial the number is a root of.  The statements below re-run the
same assemblies keeping both, so that each construction can be compared
as a construction. -/

/-- `PdtSalemEndgame.exists_salem_below` with the index `m ≥ 2` and the
root equation `(X^m·Pr + Qc)(τ) = 0` kept in the conclusion. -/
lemma exists_salem_below_root (alpha : ℝ) (halpha : 1 < alpha)
    (Pr G Qc : Polynomial ℝ)
    (hfacR : Pr = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQca : 0 < Qc.eval alpha)
    (cert : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * Pr + Qc).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) →
      SalemEndgame.IsSalem tau)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
      (X ^ m * Pr + Qc).eval tau = 0 ∧ alpha - eps < tau ∧ tau < alpha := by
  obtain ⟨c, hc1, hca, hwin⟩ := SalemEndgame.window_below Qc halpha hQca
  obtain ⟨M, lam, hprops, htend⟩ :=
    PisotLadder.pisot_ladder_family Pr G Qc alpha c halpha hc1 hca hfacR hG hwin
  have hstep : ∀ m, M ≤ m → lam m < lam (m + 1) := fun m hm => (hprops m hm).2.2.2
  have hinj : Set.InjOn lam (Set.Ici M) :=
    SalemEndgame.injOn_of_strict_mono_step lam M hstep
  have hbounds : ∀ m, M ≤ m → 1 < lam m ∧ lam m < alpha := fun m hm =>
    ⟨lt_trans hc1 (hprops m hm).1.1, (hprops m hm).1.2⟩
  obtain ⟨M', _hMM', hnd⟩ :=
    SalemEndgame.eventually_nondegenerate lam M alpha hinj hbounds
  have hev1 : ∀ᶠ m : ℕ in Filter.atTop, alpha - eps < lam m :=
    (tendsto_order.mp htend).1 (alpha - eps) (by linarith)
  obtain ⟨m, hm1, hm2⟩ :=
    (hev1.and (Filter.eventually_ge_atTop (max M (max M' 2)))).exists
  have hmM : M ≤ m := le_trans (le_max_left _ _) hm2
  have hmM' : M' ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hm2' : 2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  obtain ⟨⟨hgtc, hlta⟩, hroot, -, -⟩ := hprops m hmM
  obtain ⟨hτZ, hτtr⟩ := hnd m hmM'
  exact ⟨m, hm2', lam m, cert m hm2' (lam m) (lt_trans hc1 hgtc) hroot hτZ hτtr,
    hroot, hm1, hlta⟩

/-- `PdtSalemEndgame.exists_salem_above` with the index `m ≥ 2` and the
root equation `(X^m·Pr + Qc)(τ) = 0` kept in the conclusion. -/
lemma exists_salem_above_root (alpha : ℝ) (halpha : 1 < alpha)
    (Pr G Qc : Polynomial ℝ)
    (hfacR : Pr = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQca : Qc.eval alpha < 0)
    (cert : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * Pr + Qc).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) →
      SalemEndgame.IsSalem tau)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
      (X ^ m * Pr + Qc).eval tau = 0 ∧ alpha < tau ∧ tau < alpha + eps := by
  obtain ⟨M, mu, hprops, htend⟩ :=
    SalemEndgame.pisot_ladder_above Pr G Qc alpha halpha hfacR hG hQca
  have hstep : ∀ m, M ≤ m → mu (m + 1) < mu m := fun m hm => (hprops m hm).2.2.2
  have hinj : Set.InjOn mu (Set.Ici M) :=
    SalemEndgame.injOn_of_strict_anti_step mu M hstep
  have hbounds : ∀ m, M ≤ m → 1 < mu m ∧ mu m < alpha + 1 := fun m hm =>
    ⟨lt_trans halpha (hprops m hm).1.1, (hprops m hm).1.2⟩
  obtain ⟨M', _hMM', hnd⟩ :=
    SalemEndgame.eventually_nondegenerate mu M (alpha + 1) hinj hbounds
  have hev1 : ∀ᶠ m : ℕ in Filter.atTop, mu m < alpha + eps :=
    (tendsto_order.mp htend).2 (alpha + eps) (by linarith)
  obtain ⟨m, hm1, hm2⟩ :=
    (hev1.and (Filter.eventually_ge_atTop (max M (max M' 2)))).exists
  have hmM : M ≤ m := le_trans (le_max_left _ _) hm2
  have hmM' : M' ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hm2' : 2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  obtain ⟨⟨hgta, _⟩, hroot, -, -⟩ := hprops m hmM
  obtain ⟨hτZ, hτtr⟩ := hnd m hmM'
  exact ⟨m, hm2', mu m, cert m hm2' (mu m) (lt_trans halpha hgta) hroot hτZ hτtr,
    hroot, hgta, hm1⟩

/-- Evaluation of the mapped signed family `X^m·Pz + e·Pz.reverse`. -/
lemma eval_signed_family (Pz : Polynomial ℤ) (e : ℤ) (m : ℕ) (tau : ℝ) :
    ((X ^ m * Pz + C e * Pz.reverse).map (Int.castRingHom ℝ)).eval tau
      = tau ^ m * (Pz.map (Int.castRingHom ℝ)).eval tau
        + (e : ℝ) * (Pz.reverse.map (Int.castRingHom ℝ)).eval tau := by
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom]

/-- Evaluation of the mapped signed family `X^m·Pz − e·Pz.reverse`. -/
lemma eval_signed_family_sub (Pz : Polynomial ℤ) (e : ℤ) (m : ℕ) (tau : ℝ) :
    ((X ^ m * Pz - C e * Pz.reverse).map (Int.castRingHom ℝ)).eval tau
      = tau ^ m * (Pz.map (Int.castRingHom ℝ)).eval tau
        - (e : ℝ) * (Pz.reverse.map (Int.castRingHom ℝ)).eval tau := by
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom]

/-- **The main construction with its family root exposed.**  Under the
hypotheses of `PdtSalemEndgame.salem_two_sided` — the Pisot pattern and
`P(1/α) ≠ 0` — there is a sign `e = ±1`, the sign of `P(1/α)`, such that
for every `ε > 0` some member `X^m·Pz + e·Pz.reverse` (`m ≥ 2`) has a
Salem root in `(α − ε, α)` and some member `X^m·Pz − e·Pz.reverse`
(`m ≥ 2`) has a Salem root in `(α, α + ε)`.  The same assembly as
`salem_two_sided`, keeping the index and the root equation: the sign of
`Q(α) = α^p·P(1/α)` routes the plus family below and the minus family
above when `P(1/α) > 0`, and the reverse when `P(1/α) < 0`. -/
theorem salem_construction_two_sided
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (hnondeg : (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      0 < (e : ℝ) * (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
        ((X ^ m * Pz + C e * Pz.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha - eps < tau ∧ tau < alpha) ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
        ((X ^ m * Pz - C e * Pz.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha < tau ∧ tau < alpha + eps) := by
  classical
  have hapos : (0 : ℝ) < alpha := by linarith
  have ha0 : alpha ≠ 0 := ne_of_gt hapos
  -- monicity, degree, and the root `α` of the real image
  have hPrMonic : (Pz.map (Int.castRingHom ℝ)).Monic := hmonic.map _
  have hPrDeg : (Pz.map (Int.castRingHom ℝ)).natDegree = inside.card + 1 := by
    rw [hmonic.natDegree_map]
    exact SalemArith.Pz_natDegree Pz hmonic alpha inside hfacC
  have hPrAlpha : (Pz.map (Int.castRingHom ℝ)).eval alpha = 0 := by
    have h1 : ((((Pz.map (Int.castRingHom ℝ)).eval alpha : ℝ)) : ℂ)
        = (Pz.map (Int.castRingHom ℂ)).eval ((alpha : ℂ)) :=
      (SalemEndgame.eval_int_transfer Pz alpha).symm
    rw [hfacC, SalemCircle.eval_P, sub_self, zero_mul] at h1
    exact_mod_cast h1
  -- the sign scalar `Q(α) = α^p·P(1/α) ≠ 0`
  have hQrRev : Pz.reverse.map (Int.castRingHom ℝ)
      = (Pz.map (Int.castRingHom ℝ)).reflect (inside.card + 1) := by
    rw [← hPrDeg, Polynomial.reflect_map]
    congr 1
    rw [hmonic.natDegree_map]
    rfl
  have heId : (Pz.reverse.map (Int.castRingHom ℝ)).eval alpha
      = alpha ^ (inside.card + 1) * (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ := by
    rw [hQrRev]
    exact SalemEndgame.reflect_eval_eq (Pz.map (Int.castRingHom ℝ)) ha0 (inside.card + 1)
      (le_of_eq hPrDeg)
  have he_ne : (Pz.reverse.map (Int.castRingHom ℝ)).eval alpha ≠ 0 := by
    rw [heId]
    exact mul_ne_zero (pow_ne_zero _ ha0) hnondeg
  have hpowpos : (0 : ℝ) < alpha ^ (inside.card + 1) := pow_pos hapos _
  -- the quotient `G` and its positivity on `[1, ∞)`
  obtain ⟨G, hfacR⟩ : ∃ G : Polynomial ℝ,
      Pz.map (Int.castRingHom ℝ) = (X - Polynomial.C alpha) * G :=
    ⟨_, (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hPrAlpha).symm⟩
  have hGmonic : G.Monic :=
    (Polynomial.monic_X_sub_C alpha).of_mul_monic_left (hfacR ▸ hPrMonic)
  have hGmapC : G.map (algebraMap ℝ ℂ) = (inside.map fun r => X - Polynomial.C r).prod := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero ((alpha : ℂ)))
    calc (X - Polynomial.C ((alpha : ℂ))) * G.map (algebraMap ℝ ℂ)
        = ((X - Polynomial.C alpha) * G).map (algebraMap ℝ ℂ) := by
          rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
            Polynomial.map_C, Complex.coe_algebraMap]
      _ = (Pz.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) := by rw [← hfacR]
      _ = Pz.map (Int.castRingHom ℂ) := SalemEndgame.map_int_real_complex Pz
      _ = SalemCircle.P alpha inside := hfacC
      _ = (X - Polynomial.C ((alpha : ℂ)))
          * (inside.map fun r => X - Polynomial.C r).prod := rfl
  have hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x :=
    SalemEndgame.G_pos G hGmonic inside hin hGmapC
  -- the two packaged certificates
  have certP : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * (Pz.map (Int.castRingHom ℝ))
        + Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) →
      SalemEndgame.IsSalem tau :=
    fun m hm tau htau hroot hτZ hτtr =>
      SalemEndgame.isSalem_of_plus_root Pz hmonic alpha halpha inside hin hconj hfacC
        m hm tau htau hroot hτZ hτtr
  have certM : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * (Pz.map (Int.castRingHom ℝ))
        + -(Pz.reverse.map (Int.castRingHom ℝ))).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) →
      SalemEndgame.IsSalem tau := by
    intro m hm tau htau hroot hτZ hτtr
    have hroot' : (X ^ m * (Pz.map (Int.castRingHom ℝ))
        - Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0 := by
      rw [sub_eq_add_neg]
      exact hroot
    exact SalemEndgame.isSalem_of_minus_root Pz hmonic alpha halpha inside hin hconj hfacC
      m hm tau htau hroot' hτZ hτtr
  -- the sign fork: each case produces BOTH sides and records the sign
  rcases lt_or_lt_iff_ne.mpr he_ne with hneg | hpos
  · -- `Q(α) < 0`, so `P(1/α) < 0` and `e = −1`: BELOW via the minus
    -- family, ABOVE via the plus family
    have hPneg : (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ < 0 := by
      have h := hneg
      rw [heId] at h
      rcases mul_neg_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · exact absurd h1 (not_lt.mpr hpowpos.le)
    have hnegneg : 0 < (-(Pz.reverse.map (Int.castRingHom ℝ))).eval alpha := by
      rw [Polynomial.eval_neg]
      linarith
    obtain ⟨m₁, hm₁, τ₁, hS₁, hr₁, hlo₁, hhi₁⟩ :=
      exists_salem_below_root alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (-(Pz.reverse.map (Int.castRingHom ℝ))) hfacR hG hnegneg certM eps heps
    obtain ⟨m₂, hm₂, τ₂, hS₂, hr₂, hlo₂, hhi₂⟩ :=
      exists_salem_above_root alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (Pz.reverse.map (Int.castRingHom ℝ)) hfacR hG hneg certP eps heps
    refine ⟨-1, Or.inr rfl, by push_cast; linarith,
      ⟨m₁, hm₁, τ₁, hS₁, ?_, hlo₁, hhi₁⟩, ⟨m₂, hm₂, τ₂, hS₂, ?_, hlo₂, hhi₂⟩⟩
    · rw [eval_signed_family]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_neg] at hr₁
      push_cast
      linarith
    · rw [eval_signed_family_sub]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X] at hr₂
      push_cast
      linarith
  · -- `Q(α) > 0`, so `P(1/α) > 0` and `e = +1`: BELOW via the plus
    -- family, ABOVE via the minus family
    have hPpos : 0 < (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ := by
      have h := hpos
      rw [heId] at h
      rcases mul_pos_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · exact absurd h1 (not_lt.mpr hpowpos.le)
    have hnegneg : (-(Pz.reverse.map (Int.castRingHom ℝ))).eval alpha < 0 := by
      rw [Polynomial.eval_neg]
      linarith
    obtain ⟨m₁, hm₁, τ₁, hS₁, hr₁, hlo₁, hhi₁⟩ :=
      exists_salem_below_root alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (Pz.reverse.map (Int.castRingHom ℝ)) hfacR hG hpos certP eps heps
    obtain ⟨m₂, hm₂, τ₂, hS₂, hr₂, hlo₂, hhi₂⟩ :=
      exists_salem_above_root alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (-(Pz.reverse.map (Int.castRingHom ℝ))) hfacR hG hnegneg certM eps heps
    refine ⟨1, Or.inl rfl, by push_cast; linarith,
      ⟨m₁, hm₁, τ₁, hS₁, ?_, hlo₁, hhi₁⟩, ⟨m₂, hm₂, τ₂, hS₂, ?_, hlo₂, hhi₂⟩⟩
    · rw [eval_signed_family]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X] at hr₁
      push_cast
      linarith
    · rw [eval_signed_family_sub]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_neg] at hr₂
      push_cast
      linarith

/-- **The reciprocal-quadratic construction with its family root
exposed.**  `PdtSalemQuadUnit.salem_two_sided_quad_unit` re-run keeping
the index `m ≥ 1` and the root equation: below `α` a Salem root of
`(X² − rX + 1)(X^{2m} + 1) + X^{m+1}`, above `α` a Salem root of
`(X² − rX + 1)(X^{2m} + 1) − X^{m+1}` — the members `eps = +1` and
`eps = −1` of `PdtSalemQuadUnit.Bfam`, spelled out. -/
theorem salem_quadratic_unit (r : ℤ) (hr : 3 ≤ r)
    (alpha : ℝ) (halpha : 1 < alpha) (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) + X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha - eps < tau ∧ tau < alpha) ∧
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ, SalemEndgame.IsSalem tau ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) - X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha < tau ∧ tau < alpha + eps) := by
  have hB1 : ∀ m : ℕ, SalemQuadUnit.Bfam r 1 m
      = (X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) + X ^ (m + 1) := by
    intro m
    rw [SalemQuadUnit.Bfam, Polynomial.C_1, one_mul]
  have hBm : ∀ m : ℕ, SalemQuadUnit.Bfam r (-1) m
      = (X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) - X ^ (m + 1) := by
    intro m
    rw [SalemQuadUnit.Bfam, Polynomial.C_neg, Polynomial.C_1, neg_one_mul, ← sub_eq_add_neg]
  have halpha2 : 2 < alpha := SalemQuadUnit.alpha_gt_two hr halpha hmin
  have htr : alpha + alpha⁻¹ = (r : ℝ) := SalemQuadUnit.trace_eq halpha hmin
  have hainv1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  have hainv0 : 0 < alpha⁻¹ := inv_pos.mpr (by linarith)
  have hral : (r : ℝ) - 1 < alpha := SalemQuadUnit.r_sub_one_lt_alpha halpha hmin
  have haltr : alpha < (r : ℝ) := SalemQuadUnit.alpha_lt_r halpha hmin
  have h2pow : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  constructor
  · -- BELOW `alpha`: the `eps = +1` member
    obtain ⟨δ, hδ0, hδeps, hδa2, hδinv⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ eps ∧
        δ ≤ alpha - 2 ∧ δ ≤ (1 - alpha⁻¹) / 2 :=
      ⟨min eps (min (alpha - 2) ((1 - alpha⁻¹) / 2)),
        lt_min heps (lt_min (by linarith) (by linarith)),
        min_le_left _ _,
        le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have hev : ∀ᶠ k : ℕ in Filter.atTop, alpha / δ < 2 ^ k := h2pow.eventually_gt_atTop _
    obtain ⟨m, hm1, hm2⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    have hdm : alpha < δ * 2 ^ m := by
      rw [div_lt_iff₀ hδ0] at hm1
      linarith
    have hsignA : 0 < ((SalemQuadUnit.Bfam r 1 m).map (Int.castRingHom ℝ)).eval alpha := by
      rw [SalemQuadUnit.eval_at_alpha r 1 hmin m]
      push_cast
      have hp : (0 : ℝ) < alpha ^ (m + 1) := pow_pos (by linarith) _
      linarith
    have hsignB := SalemQuadUnit.eval_below_neg r halpha2 hmin m hδ0 hδa2 hdm
    obtain ⟨tau, htau1, htau2, htauroot⟩ := SalemQuadUnit.exists_root_between
      (fun y => ((SalemQuadUnit.Bfam r 1 m).map (Int.castRingHom ℝ)).eval y)
      (alpha - δ) alpha (by linarith)
      (Polynomial.continuous _).continuousOn
      (mul_neg_of_neg_of_pos hsignB hsignA)
    have htaugt2 : 2 < tau := by linarith
    have htauwin1 : (r : ℝ) - 1 < tau := by
      have hkey : alpha - (1 - alpha⁻¹) = (r : ℝ) - 1 := by linarith
      linarith
    have htauwin2 : tau < (r : ℝ) := by linarith
    refine ⟨m, hm2, tau, SalemQuadUnit.isSalem_of_quad_root r 1 hr (Or.inl rfl) hm2 tau
      (by linarith) htauroot (SalemQuadUnit.no_int_in_window htauwin1 htauwin2)
      (SalemQuadUnit.trace_not_int r 1 (Or.inl rfl) hm2 htaugt2 htauroot),
      ?_, by linarith, htau2⟩
    rw [← hB1]
    exact htauroot
  · -- ABOVE `alpha`: the `eps = −1` member
    obtain ⟨δ, hδ0, hδeps, hδinv⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ eps ∧ δ ≤ alpha⁻¹ :=
      ⟨min eps alpha⁻¹, lt_min heps hainv0, min_le_left _ _, min_le_right _ _⟩
    have hδ1 : δ ≤ 1 := by linarith
    have hcpos : 0 < δ * (alpha - alpha⁻¹) := mul_pos hδ0 (by linarith)
    have hev : ∀ᶠ k : ℕ in Filter.atTop, (alpha + 1) / (δ * (alpha - alpha⁻¹)) < 2 ^ k :=
      h2pow.eventually_gt_atTop _
    obtain ⟨m, hm1, hm2⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    have hdm : alpha + 1 < δ * (alpha - alpha⁻¹) * 2 ^ m := by
      rw [div_lt_iff₀ hcpos] at hm1
      linarith
    have hsignA : ((SalemQuadUnit.Bfam r (-1) m).map (Int.castRingHom ℝ)).eval alpha < 0 := by
      rw [SalemQuadUnit.eval_at_alpha r (-1) hmin m]
      push_cast
      have hp : (0 : ℝ) < alpha ^ (m + 1) := pow_pos (by linarith) _
      linarith
    have hsignB := SalemQuadUnit.eval_above_pos r halpha2 hmin m hδ0 hδ1 hdm
    obtain ⟨tau, htau1, htau2, htauroot⟩ := SalemQuadUnit.exists_root_between
      (fun y => ((SalemQuadUnit.Bfam r (-1) m).map (Int.castRingHom ℝ)).eval y)
      alpha (alpha + δ) (by linarith)
      (Polynomial.continuous _).continuousOn
      (mul_neg_of_neg_of_pos hsignA hsignB)
    have htaugt2 : 2 < tau := by linarith
    have htauwin1 : (r : ℝ) - 1 < tau := by linarith
    have htauwin2 : tau < (r : ℝ) := by linarith
    refine ⟨m, hm2, tau, SalemQuadUnit.isSalem_of_quad_root r (-1) hr (Or.inr rfl) hm2 tau
      (by linarith) htauroot (SalemQuadUnit.no_int_in_window htauwin1 htauwin2)
      (SalemQuadUnit.trace_not_int r (-1) (Or.inr rfl) hm2 htaugt2 htauroot),
      ?_, htau1, by linarith⟩
    rw [← hBm]
    exact htauroot

end

end SalemPisot
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
