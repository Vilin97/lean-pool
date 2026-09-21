/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The nonarchimedean max norm on dual numbers (finite-jet vertices 𝓑 and 𝓓)

Source: [FJP] §1.4–§2. The comparison vertices of the finite-jet Milnor square are
`𝓑 = k⟨W,Q⟩/(Q²)` and `𝓓 = L⟨Q⟩/(Q²)`, i.e. *dual numbers* over `k⟨W⟩` resp. `L`, carrying
the quotient Gauss norm — which is the **max norm** `‖f₀ + Q f₁‖ = max(‖f₀‖, ‖f₁‖)`
([FJP] Lemma 2.2 and §5 (5.2): "Every element of 𝓑 is uniquely `f + Qg` with
`f, g ∈ k⟨W⟩`").

This file equips `DualNumber R` (mathlib's `TrivSqZeroExt R R`) with that norm for an
ultrametric normed base and provides the instance stack ([FJP] Prop 2.1's completeness and
noetherianity inputs for these vertices), the jet-power formula
`(f + Qg)ⁿ = fⁿ + n f^(n-1) Q g` ([FJP] (5.2)), and componentwise functoriality.
-/

open Filter Topology

namespace FiniteJet

namespace JetNorm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The max norm on dual numbers ([FJP] Lemma 2.2: the quotient norm of `k⟨W,Q⟩/(Q²)` is
`max(‖f₀‖, ‖f₁‖)`). -/
noncomputable def jetNorm (x : DualNumber R) : ℝ := max ‖x.fst‖ ‖x.snd‖

/-- The max norm is a ring norm (submultiplicativity uses the ultrametric inequality on the
cross term of `(a,b)(c,d) = (ac, ad + bc)`). -/
noncomputable def isRingNorm : RingNorm (DualNumber R) where
  toFun := jetNorm
  map_zero' := by simp [jetNorm]
  add_le' x y := by
    refine max_le ?_ ?_
    · refine (norm_add_le _ _).trans ?_
      exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · refine (norm_add_le _ _).trans ?_
      exact add_le_add (le_max_right _ _) (le_max_right _ _)
  neg' x := by simp [jetNorm]
  mul_le' x y := by
    have h0x : (0 : ℝ) ≤ max ‖x.fst‖ ‖x.snd‖ := le_max_of_le_left (norm_nonneg _)
    have h0y : (0 : ℝ) ≤ max ‖y.fst‖ ‖y.snd‖ := le_max_of_le_left (norm_nonneg _)
    refine max_le ?_ ?_
    · rw [TrivSqZeroExt.fst_mul]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) h0x)
    · rw [TrivSqZeroExt.snd_mul]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [smul_eq_mul]
        exact (norm_mul_le _ _).trans
          (mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) h0x)
      · rw [op_smul_eq_mul]
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) h0x
  eq_zero_of_map_eq_zero' x hx := by
    have h1 : ‖x.fst‖ = 0 :=
      le_antisymm (hx ▸ le_max_left _ _) (norm_nonneg _)
    have h2 : ‖x.snd‖ = 0 :=
      le_antisymm (hx ▸ le_max_right _ _) (norm_nonneg _)
    exact TrivSqZeroExt.ext (norm_eq_zero.mp h1) (norm_eq_zero.mp h2)

noncomputable instance : NormedCommRing (DualNumber R) where
  toNormedRing := RingNorm.toNormedRing isRingNorm
  mul_comm := mul_comm

theorem norm_def (x : DualNumber R) : ‖x‖ = max ‖x.fst‖ ‖x.snd‖ := rfl

@[simp] theorem norm_inl (a : R) : ‖(TrivSqZeroExt.inl a : DualNumber R)‖ = ‖a‖ := by
  rw [norm_def, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, norm_zero]
  exact max_eq_left (norm_nonneg a)

@[simp] theorem norm_eps_smul [NormOneClass R] (a : R) :
    ‖(TrivSqZeroExt.inr a : DualNumber R)‖ = ‖a‖ := by
  rw [norm_def, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, norm_zero]
  exact max_eq_right (norm_nonneg a)

instance : IsUltrametricDist (DualNumber R) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => ?_
  rw [norm_def, norm_def, norm_def]
  refine max_le ?_ ?_
  · rw [TrivSqZeroExt.fst_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    exact max_le_max (le_max_left _ _) (le_max_left _ _)
  · rw [TrivSqZeroExt.snd_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    exact max_le_max (le_max_right _ _) (le_max_right _ _)

instance [NormOneClass R] : NormOneClass (DualNumber R) := by
  refine ⟨?_⟩
  rw [norm_def, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, norm_zero, norm_one]
  exact max_eq_left zero_le_one

/-- Dual numbers over a complete base are complete (product of two copies). -/
instance [CompleteSpace R] : CompleteSpace (DualNumber R) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcomp : ∀ (proj : DualNumber R → R), (∀ x y : DualNumber R,
      ‖proj x - proj y‖ ≤ ‖x - y‖) → CauchySeq fun i => proj (u i) := by
    intro proj hproj
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    refine (hproj (u i) (u j)).trans_lt ?_
    have := hN i hi j hj
    rwa [dist_eq_norm] at this
  have hfst : CauchySeq fun i => (u i).fst := by
    refine hcomp TrivSqZeroExt.fst fun x y => ?_
    rw [show x.fst - y.fst = (x - y).fst from rfl, norm_def]
    exact le_max_left _ _
  have hsnd : CauchySeq fun i => (u i).snd := by
    refine hcomp TrivSqZeroExt.snd fun x y => ?_
    rw [show x.snd - y.snd = (x - y).snd from rfl, norm_def]
    exact le_max_right _ _
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hfst
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hsnd
  refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b,
    Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp ha) ε hε
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hb) ε hε
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_def]
  have hf : (u n - (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) : DualNumber R).fst =
      (u n).fst - a := by
    rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero]
  have hs : (u n - (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) : DualNumber R).snd =
      (u n).snd - b := by
    rw [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  rw [hf, hs]
  refine max_lt ?_ ?_
  · have := hN₁ n (le_of_max_le_left hn)
    rwa [dist_eq_norm] at this
  · have := hN₂ n (le_of_max_le_right hn)
    rwa [dist_eq_norm] at this

/-- The jet-power formula `(f + εg)ⁿ = fⁿ + n f^(n-1) ε g` ([FJP] (5.2), verbatim:
"`(f + Qg)ⁿ = fⁿ + n f^(n-1) Q g` is bounded independently of `n`"). -/
theorem pow_eq (a b : R) (n : ℕ) :
    ((TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber R)) ^ n =
      TrivSqZeroExt.inl (a ^ n) + TrivSqZeroExt.inr ((n : R) * a ^ (n - 1) * b) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, add_zero]
  · rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, add_zero, zero_add, zero_add]
    show (n : ℕ) • (a ^ (n - 1) • b) = (n : R) * a ^ (n - 1) * b
    rw [smul_eq_mul, nsmul_eq_mul, mul_assoc]

/-! ### Componentwise functoriality -/

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

/-- Componentwise application of a ring homomorphism to dual numbers. -/
def mapHom (φ : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := ⟨φ x.fst, φ x.snd⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show φ (1 : DualNumber R).fst = _
      rw [TrivSqZeroExt.fst_one, map_one, TrivSqZeroExt.fst_one]
    · show φ (1 : DualNumber R).snd = _
      rw [TrivSqZeroExt.snd_one, map_zero, TrivSqZeroExt.snd_one]
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show φ (x * y).fst = _
      rw [TrivSqZeroExt.fst_mul, map_mul]
      rfl
    · show φ (x * y).snd = _
      rw [TrivSqZeroExt.snd_mul]
      show φ (x.fst • y.snd + MulOpposite.op y.fst • x.snd) = _
      rw [smul_eq_mul, op_smul_eq_mul, map_add, map_mul, map_mul]
      rfl
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show φ (0 : DualNumber R).fst = _
      rw [TrivSqZeroExt.fst_zero, map_zero, TrivSqZeroExt.fst_zero]
    · show φ (0 : DualNumber R).snd = _
      rw [TrivSqZeroExt.snd_zero, map_zero, TrivSqZeroExt.snd_zero]
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show φ (x + y).fst = _
      rw [TrivSqZeroExt.fst_add, map_add]
      rfl
    · show φ (x + y).snd = _
      rw [TrivSqZeroExt.snd_add, map_add]
      rfl

@[simp] theorem mapHom_fst (φ : R →+* S) (x : DualNumber R) : (mapHom φ x).fst = φ x.fst := rfl

@[simp] theorem mapHom_snd (φ : R →+* S) (x : DualNumber R) : (mapHom φ x).snd = φ x.snd := rfl

/-- `mapHom` of a norm-preserving homomorphism preserves the jet norm. -/
theorem norm_mapHom (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ = ‖a‖) (x : DualNumber R) :
    ‖mapHom φ x‖ = ‖x‖ := by
  rw [norm_def, norm_def, mapHom_fst, mapHom_snd, hφ, hφ]

theorem mapHom_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (mapHom φ) := by
  intro x y hxy
  refine TrivSqZeroExt.ext (hφ ?_) (hφ ?_)
  · have := congrArg TrivSqZeroExt.fst hxy
    simpa using this
  · have := congrArg TrivSqZeroExt.snd hxy
    simpa using this

/-! ### Noetherianity: `DualNumber S` is a quotient of `S[X]`

[FJP] Prop 2.1 (verbatim): "Each of 𝓑, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`,
so each is strongly noetherian."  The engine at the coefficient level: dual numbers over a
noetherian ring are noetherian, via the surjection `S[X] → DualNumber S`, `X ↦ ε`. -/

/-- Evaluation of polynomials at `ε` is surjective onto the dual numbers. -/
theorem aeval_eps_surjective (S : Type*) [CommRing S] :
    Function.Surjective (Polynomial.aeval (R := S) (DualNumber.eps : DualNumber S)) := by
  intro x
  refine ⟨Polynomial.C x.fst + Polynomial.C x.snd * Polynomial.X, ?_⟩
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.algebraMap_eq_inl',
      TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inl,
      show (DualNumber.eps : DualNumber S).fst = 0 from rfl, mul_zero, add_zero]
    simp
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.algebraMap_eq_inl',
      TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl,
      show (DualNumber.eps : DualNumber S).snd = 1 from rfl,
      show (DualNumber.eps : DualNumber S).fst = 0 from rfl, smul_eq_mul, op_smul_eq_mul,
      mul_one, mul_zero, zero_add, add_zero]
    simp

/-- Dual numbers over a noetherian commutative ring are noetherian. -/
instance isNoetherianRing (S : Type*) [CommRing S] [IsNoetherianRing S] :
    IsNoetherianRing (DualNumber S) :=
  isNoetherianRing_of_surjective (Polynomial S) (DualNumber S)
    (Polynomial.aeval (DualNumber.eps : DualNumber S)).toRingHom
    (aeval_eps_surjective S)

end JetNorm

end FiniteJet
