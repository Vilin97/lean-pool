/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.KoszulFreeExactness
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFNoetherian
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic

/-!
# All-degree exactness of the graph Koszul complex over `P_E = E⟨T₁,…,T_m⟩`

This file proves the restricted-level positive-degree exactness statement of the
FJP → CDVF campaign (paper Lemma 5.1 clause 1; crosswalk decision D6, ticket K5): for
`g : E` and `f : Fin m → E` generating the unit ideal of `E`, the Koszul complex of the
graph sequence `r i = polyToP (C g * X i - C (f i))` over the restricted Gauss ring
`P E m = E⟨T₁,…,T_m⟩` is exact in every positive degree, provided the unit ball of the
Tate vertex `E` is noetherian.

## Main declarations

* `KoszulFree.koszulTermBaseChange` : the base-change identification
  `B ⊗[R] KoszulTerm R m n ≃ₗ[B] KoszulTerm B m n` for an arbitrary `R`-algebra `B`
  (Koszul terms are finite free; `TensorProduct.piScalarRight`).
* `KoszulFree.koszulTermBaseChange_lTensor_koszulDifferential` : under this
  identification the base-changed differential `(koszulDifferential r q).lTensor B` is
  the Koszul differential of the image sequence `fun i => algebraMap R B (r i)` — the
  equiv-level form of the naturality square `koszulTermAlgebraMap_comp_differential`.
* `KoszulFree.koszulDifferential_baseChange_exact` : positive-degree Koszul exactness
  transfers along any flat `R`-algebra `B` (`Module.Flat.lTensor_exact` conjugated
  through the base-change identification).
* `GraphKoszul.koszulGraph_restricted_exact` : **paper Lemma 5.1 clause 1** — for every
  `q`, the graph-sequence Koszul complex over `P E m` is exact at `K_{q+1}`.  Route:
  polynomial-level exactness (`koszulGraph_polynomial_exact`), then flat base change
  along `polyToP` (`flat_polyToP`, the [FJP] (4.4) identification
  `P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]`).  Only *positive-degree* exactness transfers ([FJP]:
  "exactness was established before completion"; `H₀` genuinely changes).

Exactness is always stated at `K_{q+1}` (never at `K_0`).  The datum interface — the
pair `(g, f)` with `Ideal.span ({g} ∪ Set.range f) = ⊤` in the coefficient ring `E` and
the `hr`-parametric sequence `r` — matches the degree-1 statement
`GraphKoszul.syzygy_graph_restricted`, which this theorem supersedes mathematically
(both remain; the degree-1 equational-criterion argument is not repeated here).
-/

open scoped TensorProduct

namespace FiniteJet

namespace KoszulFree

/-! ### Base change of Koszul terms and differentials

The Koszul terms are finite free, so for any `R`-algebra `B` the natural comparison
`B ⊗[R] KoszulTerm R m n → KoszulTerm B m n` is a `B`-linear equivalence
(`TensorProduct.piScalarRight`; `KoszulIndex m n` carries the inherited
`Fintype`/`DecidableEq` instances), and it intertwines the base-changed differential
`(koszulDifferential r q).lTensor B` with the Koszul differential of the image
sequence — the naturality square `koszulTermAlgebraMap_comp_differential`, upgraded to
the equiv level. -/

section BaseChange

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] {m : ℕ}

/-- The base-change identification of Koszul terms along an `R`-algebra `B`: the
degree-`n` term is finite free, so `B ⊗[R] KoszulTerm R m n ≃ₗ[B] KoszulTerm B m n`. -/
noncomputable def koszulTermBaseChange (m n : ℕ) :
    B ⊗[R] KoszulTerm R m n ≃ₗ[B] KoszulTerm B m n :=
  TensorProduct.piScalarRight R B B (KoszulIndex m n)

/-- On pure tensors, the base-change identification is the `B`-rescaled coordinatewise
algebra map. -/
theorem koszulTermBaseChange_tmul (m n : ℕ) (b : B) (x : KoszulTerm R m n) :
    koszulTermBaseChange R B m n (b ⊗ₜ x) = b • koszulTermAlgebraMap R B m n x := by
  show TensorProduct.piScalarRight R B B (KoszulIndex m n) (b ⊗ₜ x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  funext J
  rw [Pi.smul_apply, koszulTermAlgebraMap_apply, smul_eq_mul, Algebra.smul_def]
  exact mul_comm _ _

/-- Under the base-change identification, the base-changed Koszul differential
`(koszulDifferential r q).lTensor B` is the Koszul differential of the image sequence
`fun i => algebraMap R B (r i)` (equiv-level form of the naturality square
`koszulTermAlgebraMap_comp_differential`). -/
theorem koszulTermBaseChange_lTensor_koszulDifferential (r : Fin m → R) (q : ℕ)
    (x : B ⊗[R] KoszulTerm R m (q + 1)) :
    koszulTermBaseChange R B m q ((koszulDifferential r q).lTensor B x) =
      koszulDifferential (fun i => algebraMap R B (r i)) q
        (koszulTermBaseChange R B m (q + 1) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b v =>
    rw [LinearMap.lTensor_tmul, koszulTermBaseChange_tmul, koszulTermBaseChange_tmul,
      map_smul]
    refine congrArg (fun w => b • w) ?_
    exact LinearMap.congr_fun (koszulTermAlgebraMap_comp_differential R B r q) v
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R B}

/-- Positive-degree exactness of the Koszul complex transfers along a flat `R`-algebra
`B`: tensor the exact pair by the flat module `B` (`Module.Flat.lTensor_exact`) and
conjugate through the base-change identification of the three terms. -/
theorem koszulDifferential_baseChange_exact [Module.Flat R B] {r : Fin m → R} (q : ℕ)
    (hex : Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q)) :
    Function.Exact (koszulDifferential (fun i => algebraMap R B (r i)) (q + 1))
      (koszulDifferential (fun i => algebraMap R B (r i)) q) := by
  have hten := Module.Flat.lTensor_exact B hex
  intro y
  constructor
  · intro hy
    have hx : (koszulDifferential r q).lTensor B
        ((koszulTermBaseChange R B m (q + 1)).symm y) = 0 := by
      apply (koszulTermBaseChange R B m q).injective
      rw [map_zero, koszulTermBaseChange_lTensor_koszulDifferential,
        LinearEquiv.apply_symm_apply]
      exact hy
    obtain ⟨w, hw⟩ := (hten _).mp hx
    refine ⟨koszulTermBaseChange R B m (q + 1 + 1) w, ?_⟩
    rw [← koszulTermBaseChange_lTensor_koszulDifferential, hw,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    exact koszulDifferential_koszulDifferential _ q z

end BaseChange

end KoszulFree

namespace GraphKoszul

open KoszulFree

/-! ### All-degree exactness over `P_E` -/

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

/-- **Positive-degree exactness of the graph Koszul complex over `P_E = E⟨T₁,…,T_m⟩`**
(paper Lemma 5.1 clause 1): for `g : E` and `f : Fin m → E` with
`Ideal.span ({g} ∪ Set.range f) = ⊤` and `E` a Tate vertex with noetherian unit ball,
the Koszul complex of the graph sequence `r i = polyToP (C g * X i - C (f i))` is exact
at `K_{q+1}` for every `q : ℕ`.

Route ([FJP] Lemma 4.2 mechanism, all degrees): polynomial-level exactness
(`koszulGraph_polynomial_exact`) is tensored along the flat base change
`E[T₁,…,T_m] → P_E` (`flat_polyToP`, via the (4.4) identification
`P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]`) and conjugated through the finite-free base-change
identification of the Koszul terms.  Only positive-degree exactness transfers; the
degree-1 special case is `syzygy_graph_restricted` (kept as-is). -/
theorem koszulGraph_restricted_exact (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (q : ℕ) :
    Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q) := by
  letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
  haveI hflat : Module.Flat (MvPolynomial (Fin m) E) (P E m) :=
    flat_polyToP hE₀ t htu ht1 ht0 hscale
  obtain rfl : r = fun i => algebraMap (MvPolynomial (Fin m) E) (P E m)
      (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)) :=
    funext fun i => by rw [hr i, RingHom.algebraMap_toAlgebra]
  exact koszulDifferential_baseChange_exact q (koszulGraph_polynomial_exact g f hunit q)

/- The FJP pipeline composes at a CDVF base (`E := K`, `t := ϖ`): over a complete
discretely valued nonarchimedean field the scaling bundle is the uniformizer layer of
`CDVFBase.lean` and the noetherian input is the unit-ball hypothesis of
`CDVFNoetherian.lean`'s Uniformizer layer, so all-degree exactness of the graph Koszul
complex over `P K m = K⟨T₁,…,T_m⟩` is available for every datum `g, f` generating the
unit ideal of `K`.  The four FJP-vertex instantiations are wired downstream (tickets
K6/K9), not here. -/
example (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {m : ℕ} (ϖ : FiniteJetOver.Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (g : K) (f : Fin m → K) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P K m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (q : ℕ) :
    Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q) :=
  koszulGraph_restricted_exact hK₀ ϖ.val ϖ.isUnit_val ϖ.norm_val_lt_one ϖ.norm_val_pos
    ϖ.norm_val_mul g f hunit r hr q

end Restricted

end GraphKoszul

end FiniteJet
