/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.AdicCompletionPrincipal
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFBase
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic

/-!
# The restricted pods `K⟨T₁,…,T_m⟩` over a CDVF base are noetherian

Source: [FJP] §5.1 (the noetherian-vertex assertion), crosswalk D2 (ticket K2c). Over a
complete discretely valued nonarchimedean field `K` with uniformizer `ϖ`, the
noetherian-pod chain is assembled:

* `𝒪[K]` noetherian (`CDVFBase.lean`) gives `MvPolynomial (Fin m) ↥(unitBall K)`
  noetherian by the Hilbert basis theorem (`isNoetherianRing_mvPolynomial_unitBall`);
* the `(ϖ)`-adic completion of that polynomial ring is noetherian —
  `AdicCompletion.isNoetherianRing_span_singleton` (`AdicCompletionPrincipal.lean`) at the
  principal ideal `GraphKoszul.I0 = (C ϖ)` — and transport along the [FJP] (4.4)
  identification `GraphKoszul.ballAdicEquiv` gives
  `Uniformizer.isNoetherianRing_unitBall_P`;
* `P K m = K⟨T₁,…,T_m⟩` is the localization of its unit ball away from the central
  scaling constant `C ϖ`, so it is noetherian (`Uniformizer.isNoetherianRing_P`, via
  `IsLocalization.isNoetherianRing`);
* identifying `P K k` with the topological restricted subring along
  `UnitDiscExample.restrictedGaussEquiv` yields `IsStronglyNoetherian K`
  (`Uniformizer.isStronglyNoetherian`).

Layer-1 statements take an explicit uniformizer `ϖ` and the noetherianity of the unit
ball as a hypothesis (never a class); layer-2 versions assume
`[IsDiscreteValuationRing 𝒪[K]]` and choose `Uniformizer.ofDVR K`, with
`isStronglyNoetherian` registered as an instance, mirroring the Laurent-series
registration in `ExampleLaurentSeries.lean`.
-/

open Filter Topology
open scoped NormedField Valued

namespace FiniteJetOver

open FiniteJet

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Polynomials over the valuation ring of a complete discretely valued field form a
noetherian ring (Hilbert basis theorem over the noetherian `𝒪[K] = unitBall K`). -/
theorem isNoetherianRing_mvPolynomial_unitBall [IsDiscreteValuationRing 𝒪[K]] (m : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin m) ↥(unitBall K)) := by
  haveI := isNoetherianRing_unitBall K
  infer_instance

variable [CompleteSpace K]

namespace Uniformizer

variable {K}

/-- **The unit-ball pod is noetherian** ([FJP] §5.1, crosswalk D2): the unit ball of
`K⟨T₁,…,T_m⟩` is the `(ϖ)`-adic completion of `𝒪[K][T₁,…,T_m]` (the (4.4) identification
`GraphKoszul.ballAdicEquiv`), and the completion of a noetherian ring at a principal
ideal is noetherian (`AdicCompletion.isNoetherianRing_span_singleton`). -/
theorem isNoetherianRing_unitBall_P (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (m : ℕ) :
    IsNoetherianRing ↥(unitBall (GraphKoszul.P K m)) := by
  haveI := hK₀
  haveI hcomp : IsNoetherianRing (AdicCompletion
      (GraphKoszul.I0 ϖ.val ϖ.norm_val_lt_one)
      (MvPolynomial (Fin m) ↥(unitBall K))) :=
    AdicCompletion.isNoetherianRing_span_singleton _ _
  exact isNoetherianRing_of_ringEquiv _
    (GraphKoszul.ballAdicEquiv (E := K) (m := m) ϖ.val ϖ.isUnit_val ϖ.norm_val_lt_one
      ϖ.norm_val_pos ϖ.norm_val_mul).symm

/-- **The pod is noetherian** ([FJP] §5.1): `K⟨T₁,…,T_m⟩` is the localization of its
noetherian unit ball at the powers of the central scaling constant `C ϖ`. -/
theorem isNoetherianRing_P (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (m : ℕ) :
    IsNoetherianRing (GraphKoszul.P K m) := by
  haveI hball := ϖ.isNoetherianRing_unitBall_P hK₀ m
  letI : Algebra ↥(unitBall (GraphKoszul.P K m)) (GraphKoszul.P K m) :=
    (unitBall (GraphKoszul.P K m)).subtype.toAlgebra
  set s : ↥(unitBall (GraphKoszul.P K m)) :=
    ⟨GraphKoszul.polyToP (MvPolynomial.C ϖ.val),
      (mem_unitBall_iff _ _).mpr (by
        rw [GraphKoszul.norm_tP ϖ.val ϖ.norm_val_mul]
        exact ϖ.norm_val_lt_one.le)⟩ with hs
  haveI hloc : IsLocalization (Submonoid.powers s) (GraphKoszul.P K m) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨y, k, rfl⟩
      show IsUnit ((GraphKoszul.polyToP (MvPolynomial.C ϖ.val) : GraphKoszul.P K m) ^ k)
      exact (GraphKoszul.isUnit_tP ϖ.val ϖ.isUnit_val).pow k
    · intro F
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖ϖ.val‖ ^ n * ‖F‖ ≤ 1 := by
        rcases eq_or_ne ‖F‖ 0 with h0 | h0
        · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
        · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm h0)
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) ϖ.norm_val_lt_one
          exact ⟨n, by
            calc ‖ϖ.val‖ ^ n * ‖F‖ ≤ ‖F‖⁻¹ * ‖F‖ :=
                  mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
      have hmem : ‖GraphKoszul.polyToP (MvPolynomial.C ϖ.val) ^ n * F‖ ≤ 1 := by
        rw [norm_pow_mul_of_scale (E := GraphKoszul.P K m)
          (fun G => by
            rw [GraphKoszul.norm_tP ϖ.val ϖ.norm_val_mul]
            exact GraphKoszul.norm_tP_mul ϖ.val ϖ.norm_val_mul G) n,
          GraphKoszul.norm_tP ϖ.val ϖ.norm_val_mul]
        exact hn
      refine ⟨(⟨GraphKoszul.polyToP (MvPolynomial.C ϖ.val) ^ n * F, hmem⟩,
        ⟨s ^ n, n, rfl⟩), ?_⟩
      show F * (GraphKoszul.polyToP (MvPolynomial.C ϖ.val) : GraphKoszul.P K m) ^ n =
        GraphKoszul.polyToP (MvPolynomial.C ϖ.val) ^ n * F
      exact mul_comm F _
    · intro x y h
      refine ⟨1, ?_⟩
      have hinj : Function.Injective ((unitBall (GraphKoszul.P K m)).subtype) :=
        Subtype.val_injective
      rw [hinj h]
  exact IsLocalization.isNoetherianRing (Submonoid.powers s) (GraphKoszul.P K m) hball

/-- **`K` is strongly noetherian** ([FJP] §5.1, crosswalk D2 endpoint): every restricted
power series ring `K⟨T₁,…,T_k⟩` is noetherian — the topological restricted subring is
identified with the Gauss-restricted pod `P K k` along
`UnitDiscExample.restrictedGaussEquiv`. -/
theorem isStronglyNoetherian (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsStronglyNoetherian K := by
  constructor
  intro k
  haveI hP := ϖ.isNoetherianRing_P hK₀ k
  exact isNoetherianRing_of_ringEquiv (GraphKoszul.P K k)
    (UnitDiscExample.restrictedGaussEquiv K k)

end Uniformizer

/-! ### Layer 2: the `[IsDiscreteValuationRing 𝒪[K]]` versions

The uniformizer is chosen via `Uniformizer.ofDVR`, and the unit-ball noetherianity input
comes from `CDVFBase.isNoetherianRing_unitBall`; the statements are uniformizer-free. -/

/-- Layer-2 form of `Uniformizer.isNoetherianRing_unitBall_P`. -/
theorem isNoetherianRing_unitBall_P [IsDiscreteValuationRing 𝒪[K]] (m : ℕ) :
    IsNoetherianRing ↥(unitBall (GraphKoszul.P K m)) :=
  (Uniformizer.ofDVR K).isNoetherianRing_unitBall_P (isNoetherianRing_unitBall K) m

/-- Layer-2 form of `Uniformizer.isNoetherianRing_P`. -/
theorem isNoetherianRing_P [IsDiscreteValuationRing 𝒪[K]] (m : ℕ) :
    IsNoetherianRing (GraphKoszul.P K m) :=
  (Uniformizer.ofDVR K).isNoetherianRing_P (isNoetherianRing_unitBall K) m

/-- **A complete discretely valued nonarchimedean field is strongly noetherian**
([FJP] §5.1). Registered as an instance, mirroring the Laurent-series registration in
`ExampleLaurentSeries.lean`. -/
instance isStronglyNoetherian [IsDiscreteValuationRing 𝒪[K]] : IsStronglyNoetherian K :=
  (Uniformizer.ofDVR K).isStronglyNoetherian (isNoetherianRing_unitBall K)

end FiniteJetOver
