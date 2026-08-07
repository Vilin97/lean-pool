/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CechCount.Mul

/-!
# Multiplication epimorphisms on Čech `H¹` (cechcount unit, Forster 17.8)

For a *nonzero* global meromorphic function `f` and any admissible bound `MulBound f D E`,
the multiplication map `mulH1 f hf : H¹(D) → H¹(E)` is **surjective** (Forster §17.8's lemma,
primal form). Proof: factor through the intermediate divisor `D₁ := E + divisor f`:

* `D ≤ D₁` (that is what the bound says, since `f ≠ 0` has finite order everywhere), so
  `H1Incl : H¹(D) → H¹(D₁)` is surjective (`H1Incl_surjective`, the six-term part (g));
* multiplication `H¹(D₁) → H¹(E)` by `f` at the *exact* bound is bijective, with inverse
  multiplication by `f⁻¹` (the composition laws `mulH1_mulH1`/`mulH1_one` and
  `f·f⁻¹ = 1` in the function field `ℳ X`);
* `mulH1 f hf` agrees with the composite (`mulH1_H1Incl`).
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech Module


namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Forster 17.8 (primal form)**: multiplication by a nonzero meromorphic function is
surjective on Čech `H¹`, for any admissible divisor bound. -/
theorem mulH1_surjective {f : ℳ X} (hf0 : f ≠ 0) {D E : RS.Divisor X} (hf : MulBound f D E) :
    Function.Surjective (mulH1 f hf : H1 D →ₗ[ℂ] H1 E) := by
  intro η
  have hfinv0 : (f⁻¹ : ℳ X) ≠ 0 := inv_ne_zero hf0
  -- the coe bookkeeping: `((divisor f x : ℤ) : WithTop ℤ) = f.ord x` for `f ≠ 0`
  have hcoe : ∀ x : X, ((RS.divisor f x : ℤ) : WithTop ℤ) = f.ord x := fun x =>
    WithTop.coe_untop₀_of_ne_top (RS.Mero.ord_ne_top hf0 x)
  have hcoeinv : ∀ x : X, ((RS.divisor (f⁻¹) x : ℤ) : WithTop ℤ) = (f⁻¹ : ℳ X).ord x := fun x =>
    WithTop.coe_untop₀_of_ne_top (RS.Mero.ord_ne_top hfinv0 x)
  -- the intermediate divisor
  set D₁ : RS.Divisor X := E + RS.divisor f with hD₁def
  have hD₁x : ∀ x, D₁ x = E x + RS.divisor f x := fun x =>
    RS.Divisor.add_apply E (RS.divisor f) x
  have h₁ : D ≤ D₁ := by
    rw [Function.locallyFinsuppWithin.le_def]
    intro x
    have hx := hf x
    rw [← hcoe x] at hx
    have hZ : D x - E x ≤ RS.divisor f x := by exact_mod_cast hx
    rw [hD₁x x]
    exact sub_le_iff_le_add'.mp hZ
  have hf₁ : MulBound f D₁ E := by
    intro x
    rw [hD₁x x]
    have heq : (E x + RS.divisor f x - E x : ℤ) = RS.divisor f x := by ring
    rw [heq, hcoe x]
  have hinv : MulBound (f⁻¹ : ℳ X) E D₁ := by
    intro x
    rw [hD₁x x]
    have heq : (E x - (E x + RS.divisor f x) : ℤ) = RS.divisor (f⁻¹) x := by
      rw [RS.divisor_inv f, RS.Divisor.neg_apply]
      ring
    rw [heq, hcoeinv x]
  -- the product bound (via `f · f⁻¹ = 1`)
  have hmul1 : f * f⁻¹ = 1 := RS.Mero.mul_inv_cancel hf0
  have hff : MulBound (f * f⁻¹) E E := by
    rw [hmul1]
    exact mulBound_one le_rfl
  -- lift `η` through the exact multiplication and the inclusion
  obtain ⟨ζ, hζ⟩ := H1Incl_surjective h₁ (mulH1 (f⁻¹ : ℳ X) hinv η)
  refine ⟨ζ, ?_⟩
  calc mulH1 f hf ζ
      = mulH1 f hf₁ (H1Incl D h₁ ζ) := (mulH1_H1Incl h₁ hf₁ hf ζ).symm
    _ = mulH1 f hf₁ (mulH1 (f⁻¹ : ℳ X) hinv η) := by rw [hζ]
    _ = mulH1 (f * f⁻¹) hff η := mulH1_mulH1 hf₁ hinv hff η
    _ = mulH1 (1 : ℳ X) (mulBound_one le_rfl) η := mulH1_congr hmul1 hff _ η
    _ = H1Incl E le_rfl η := mulH1_one _ le_rfl η
    _ = η := LinearMap.congr_fun (H1Incl_id E) η

end RS.Cech
