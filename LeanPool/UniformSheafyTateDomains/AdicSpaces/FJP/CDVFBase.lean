/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings

/-!
# Base-field API over a complete discretely valued nonarchimedean field

Source: [FJP] §1: "Fix a complete discretely valued nonarchimedean field `k`, with valuation
ring `k°`, uniformizer `ϖ`, and residue field `k̃`." This file is the two-layer base-field
API of the CDVF campaign (crosswalk decision D1, ticket K1), over the stack
`[NontriviallyNormedField K] [IsUltrametricDist K]` with the `Valued K ℝ≥0` instance
provided by the scoped instance `NormedField.toValued` (`open scoped NormedField`),
so that the valuation ring `k°` is `𝒪[K] = Valued.integer K`. The remaining member of the
D1 base stack, `[CompleteSpace K]`, is *not* assumed here: no statement of this file needs
completeness (the `unusedSectionVars` linter confirms it), so downstream files add it where
the sheafy/completion content actually uses it.

* **Layer 1** — `FiniteJetOver.Uniformizer K`: an *explicit* uniformizer, i.e. an element of
  `𝒪[K]` bundled with its irreducibility and **nothing else**. Every analytic or
  ring-theoretic consequence is *derived* from irreducibility, never assumed:
  nonvanishing (`elem_ne_zero`, `val_ne_zero`, `isUnit_val`), the norm window
  `0 < ‖ϖ.val‖ < 1` (`norm_val_pos`, `norm_val_lt_one`), exact norm scaling
  (`norm_val_mul`, `norm_val_pow_mul`), topological nilpotence (`tendsto_pow_val`,
  `isTopologicallyNilpotent_val`), the integral-lattice bound
  (`exists_pow_mul_mem_integer`), and the Huber/Tate structure of `K`
  (`Uniformizer.pod`, `Uniformizer.isHuberRing`, `Uniformizer.isTateRing`).
* **Layer 2** — `Uniformizer.ofDVR`: when `𝒪[K]` is a discrete valuation ring, a
  uniformizer is *chosen* via `IsDiscreteValuationRing.exists_irreducible`.

The scaling bundle `(t, htu, ht1, ht0, hscale)` consumed by the generic layer of
`FiniteJetGraphKoszul.lean` (and by `FiniteJet.unitBallPod` / `isHuberRing_of_scale` /
`isTateRing_of_scale` in `FiniteJetRings.lean`) is fed, at `t := ϖ.val`, by
`(ϖ.isUnit_val, ϖ.norm_val_lt_one, ϖ.norm_val_pos, ϖ.norm_val_mul)`.

Finally, the carrier bridge `unitBall_eq_integer : FiniteJet.unitBall K = 𝒪[K]` identifies
the generic unit-ball subring of `FiniteJetRings.lean` with the valuation ring (as an
equality of `Subring K`, with `unitBallEquivInteger` the induced ring equivalence), and
transports noetherianity from the DVR hypothesis: `isNoetherianRing_integer` and
`isNoetherianRing_unitBall`.
-/

open Filter Topology
open scoped NormedField Valued

namespace FiniteJetOver

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Layer 1** of the base-field API ([FJP] §1, crosswalk D1): an explicit uniformizer of
the complete discretely valued field `K` — an element of the valuation ring `𝒪[K]` together
with its irreducibility, and *nothing else*. All consequences (nonvanishing, `0 < ‖ϖ‖ < 1`,
topological nilpotence, Huber/Tate structure, noetherianity of `𝒪[K]`) are derived below or
in later files, never bundled here. -/
structure Uniformizer where
  /-- The uniformizer, as an element of the valuation ring `𝒪[K]`. -/
  elem : 𝒪[K]
  /-- The uniformizer is irreducible in `𝒪[K]`. -/
  irreducible : Irreducible elem

namespace Uniformizer

/-- **Layer 2** of the base-field API (crosswalk D1): when the valuation ring `𝒪[K]` is a
discrete valuation ring, a uniformizer can be chosen, via
`IsDiscreteValuationRing.exists_irreducible`. -/
noncomputable def ofDVR [IsDiscreteValuationRing 𝒪[K]] : Uniformizer K where
  elem := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose
  irreducible := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec

variable {K}

/-- The uniformizer as an element of the field `K` itself. -/
def val (ϖ : Uniformizer K) : K := (ϖ.elem : K)

theorem val_def (ϖ : Uniformizer K) : ϖ.val = (ϖ.elem : K) := rfl

/-- The subring norm of `ϖ.elem` agrees with the field norm of `ϖ.val`. -/
theorem norm_elem (ϖ : Uniformizer K) : ‖ϖ.elem‖ = ‖ϖ.val‖ := rfl

/-- A uniformizer is nonzero in `𝒪[K]`. -/
theorem elem_ne_zero (ϖ : Uniformizer K) : ϖ.elem ≠ 0 :=
  ϖ.irreducible.ne_zero

/-- A uniformizer is nonzero in `K`. -/
theorem val_ne_zero (ϖ : Uniformizer K) : ϖ.val ≠ 0 :=
  fun h => ϖ.elem_ne_zero (ZeroMemClass.coe_eq_zero.mp h)

/-- A uniformizer is a unit of the field `K` (though of course not of `𝒪[K]`). -/
theorem isUnit_val (ϖ : Uniformizer K) : IsUnit ϖ.val :=
  ϖ.val_ne_zero.isUnit

/-- A uniformizer has positive norm. -/
theorem norm_val_pos (ϖ : Uniformizer K) : 0 < ‖ϖ.val‖ :=
  ϖ.norm_elem ▸ Valued.integer.norm_irreducible_pos ϖ.irreducible

/-- A uniformizer has norm strictly less than one. -/
theorem norm_val_lt_one (ϖ : Uniformizer K) : ‖ϖ.val‖ < 1 :=
  ϖ.norm_elem ▸ Valued.integer.norm_irreducible_lt_one ϖ.irreducible

/-- Multiplication by a uniformizer scales norms exactly (the `hscale` input of the
`FiniteJet.GraphKoszul` scaling bundle, at `t := ϖ.val`). -/
theorem norm_val_mul (ϖ : Uniformizer K) (x : K) : ‖ϖ.val * x‖ = ‖ϖ.val‖ * ‖x‖ :=
  norm_mul _ _

/-- Multiplication by a power of a uniformizer scales norms exactly. -/
theorem norm_val_pow_mul (ϖ : Uniformizer K) (h : ℕ) (x : K) :
    ‖ϖ.val ^ h * x‖ = ‖ϖ.val‖ ^ h * ‖x‖ := by
  rw [norm_mul, norm_pow]

/-- Powers of a uniformizer tend to zero. -/
theorem tendsto_pow_val (ϖ : Uniformizer K) : Tendsto (ϖ.val ^ ·) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one ϖ.norm_val_lt_one

/-- A uniformizer is topologically nilpotent in `K`. -/
theorem isTopologicallyNilpotent_val (ϖ : Uniformizer K) : IsTopologicallyNilpotent ϖ.val :=
  ϖ.tendsto_pow_val

/-- The integral-lattice bound: every element of `K` is carried into the valuation ring by a
sufficiently large power of a uniformizer ([FJP] §1: `𝒪[K]`-lattices exhaust `K`). -/
theorem exists_pow_mul_mem_integer (ϖ : Uniformizer K) (x : K) :
    ∃ n : ℕ, ϖ.val ^ n * x ∈ 𝒪[K] := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  · have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hx0) ϖ.norm_val_lt_one
    refine ⟨n, Valued.integer.mem_iff.mpr ?_⟩
    rw [ϖ.norm_val_pow_mul]
    have h1 : ‖ϖ.val‖ ^ n * ‖x‖ < ‖x‖⁻¹ * ‖x‖ := mul_lt_mul_of_pos_right hn hx0
    rw [inv_mul_cancel₀ hx0.ne'] at h1
    exact h1.le

/-! ### The `GraphKoszul` scaling-bundle feeder

The generic layer of `FiniteJetGraphKoszul.lean` and the generic unit-ball section of
`FiniteJetRings.lean` consume an unbundled scaling pseudouniformizer
`(t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
(hscale : ∀ x, ‖t * x‖ = ‖t‖ * ‖x‖)`. At `E := K`, `t := ϖ.val` this bundle is exactly
`(ϖ.isUnit_val, ϖ.norm_val_lt_one, ϖ.norm_val_pos, ϖ.norm_val_mul)`; the three applied
endpoints below package it into the unit-ball pair of definition and the Huber/Tate
structure of `K`. -/

/-- The unit-ball pair of definition of `K` attached to a uniformizer
(`FiniteJet.unitBallPod` fed with the uniformizer scaling bundle). -/
noncomputable def pod (ϖ : Uniformizer K) : PairOfDefinition K :=
  FiniteJet.unitBallPod ϖ.val ϖ.isUnit_val ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul

/-- A complete discretely valued nonarchimedean field with a uniformizer is a Huber ring. -/
theorem isHuberRing (ϖ : Uniformizer K) : IsHuberRing K :=
  FiniteJet.isHuberRing_of_scale ϖ.val ϖ.isUnit_val ϖ.norm_val_lt_one ϖ.norm_val_pos
    ϖ.norm_val_mul

/-- A complete discretely valued nonarchimedean field with a uniformizer is a Tate ring. -/
theorem isTateRing (ϖ : Uniformizer K) : IsTateRing K :=
  FiniteJet.isTateRing_of_scale ϖ.val ϖ.isUnit_val ϖ.norm_val_lt_one ϖ.norm_val_pos
    ϖ.norm_val_mul

end Uniformizer

/-! ### The unit ball is the valuation ring

The generic unit-ball subring `FiniteJet.unitBall K` of `FiniteJetRings.lean` and the
valuation ring `𝒪[K]` are the *same* subring of `K`; noetherianity transports along the
identification. -/

/-- The generic unit-ball subring of `FiniteJetRings.lean` is the valuation ring `𝒪[K]`,
as an equality of subrings of `K`. -/
theorem unitBall_eq_integer : FiniteJet.unitBall K = 𝒪[K] :=
  Subring.ext fun x => (FiniteJet.mem_unitBall_iff K x).trans Valued.integer.mem_iff.symm

/-- The ring equivalence `FiniteJet.unitBall K ≃+* 𝒪[K]` induced by `unitBall_eq_integer`. -/
noncomputable def unitBallEquivInteger : FiniteJet.unitBall K ≃+* 𝒪[K] :=
  RingEquiv.subringCongr (unitBall_eq_integer K)

/-- The valuation ring of a complete discretely valued field is noetherian (via
`IsDiscreteValuationRing → IsPrincipalIdealRing → IsNoetherianRing`). -/
theorem isNoetherianRing_integer [IsDiscreteValuationRing 𝒪[K]] : IsNoetherianRing 𝒪[K] :=
  inferInstance

/-- The generic unit-ball subring of `K` is noetherian when `𝒪[K]` is a discrete valuation
ring — the noetherianity input of the K2 chain (crosswalk D2). -/
theorem isNoetherianRing_unitBall [IsDiscreteValuationRing 𝒪[K]] :
    IsNoetherianRing (FiniteJet.unitBall K) :=
  isNoetherianRing_of_ringEquiv 𝒪[K] (unitBallEquivInteger K).symm

end FiniteJetOver
