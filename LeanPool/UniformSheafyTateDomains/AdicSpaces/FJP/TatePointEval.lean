/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetFunctoriality
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateScalarExtension

/-!
# Evaluation of Tate algebras at points of the closed polydisc

([hrw-decomposition] Tate leaf 13a.) For a complete ultrametric normed field
`L` and a point `x` of the closed unit polydisc, the substitution
`F ↦ F(x)` is a ring homomorphism `P L m →+* L` (through the project's
`mvEvalHomBounded` engine and the norm-to-topological restrictedness bridge).
Its kernel is a maximal ideal with residue field `L` — the rationalized
maximal ideals of the scalar-extended Tate algebra.
-/

@[expose] public section

open scoped Classical

open Filter ValuationSpectrum

namespace FiniteJet.GraphKoszul

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {m : ℕ}

/-- The closed unit ball of an ultrametric normed field is bounded. -/
theorem isBounded_closedUnitBall :
    TopologicalRing.IsBounded {y : L | ‖y‖ ≤ 1} := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, v, hv, rfl⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right] at hv ⊢
  calc ‖s * v‖ = ‖s‖ * ‖v‖ := norm_mul s v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    _ = ‖v‖ := one_mul _
    _ < ε := hv

/-- Powers of a closed-ball element are bounded. -/
theorem isBounded_range_pow {x : L} (hx : ‖x‖ ≤ 1) :
    TopologicalRing.IsBounded (Set.range (x ^ · : ℕ → L)) := by
  refine isBounded_closedUnitBall.subset ?_
  rintro _ ⟨n, rfl⟩
  show ‖x ^ n‖ ≤ 1
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg x) hx

/-- Norm-decay restricted series are topologically restricted (the generic
form of the `bridgeToRestricted` pattern). -/
noncomputable def toTopRestricted :
    P L m →+* ↥(restrictedMvPowerSeriesSubring m L) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 :=
      p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 :=
      fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem toTopRestricted_coe (p : P L m) :
    (toTopRestricted (m := m) p).1 = p.1 := rfl

section PointEval

variable (x : Fin m → L) (hx : ∀ i, ‖x i‖ ≤ 1)

/-- **Evaluation at a point of the closed polydisc** — the substitution
`F ↦ F(x)`, convergent by restrictedness. -/
noncomputable def pointEval : P L m →+* L :=
  (mvEvalHomBounded (RingHom.id L) continuous_id x
    (fun i => isBounded_range_pow (hx i))).comp
    (toTopRestricted (m := m))

/-- Evaluation extends the constants. -/
theorem pointEval_polyToP_C (c : L) :
    pointEval (m := m) x hx (polyToP (MvPolynomial.C c)) = c := by
  have h1 : toTopRestricted (m := m) (polyToP (MvPolynomial.C c)) =
      algebraMap L ↥(restrictedMvPowerSeriesSubring m L) c := by
    refine Subtype.ext ?_
    show ((MvPolynomial.C c : MvPolynomial (Fin m) L) :
      MvPowerSeries (Fin m) L) = (MvPowerSeries.C c : MvPowerSeries (Fin m) L)
    exact MvPolynomial.coe_C c
  show mvEvalHomBounded (RingHom.id L) continuous_id x
    (fun i => isBounded_range_pow (hx i))
    (toTopRestricted (m := m) (polyToP (MvPolynomial.C c))) = c
  rw [h1]
  exact mvEvalHomBounded_algebraMap _ _ _ _ c

/-- Evaluation sends the variables to the point coordinates. -/
theorem pointEval_polyToP_X (j : Fin m) :
    pointEval (m := m) x hx (polyToP (MvPolynomial.X j)) = x j := by
  have h1 : toTopRestricted (m := m) (polyToP (MvPolynomial.X j)) =
      (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        ↥(restrictedMvPowerSeriesSubring m L)) := by
    refine Subtype.ext ?_
    show ((MvPolynomial.X j : MvPolynomial (Fin m) L) :
      MvPowerSeries (Fin m) L) = MvPowerSeries.X j
    exact MvPolynomial.coe_X j
  show mvEvalHomBounded (RingHom.id L) continuous_id x
    (fun i => isBounded_range_pow (hx i))
    (toTopRestricted (m := m) (polyToP (MvPolynomial.X j))) = x j
  rw [h1]
  exact mvEvalHomBounded_X _ _ _ _ j

theorem pointEval_surjective :
    Function.Surjective (pointEval (m := m) x hx) := fun c =>
  ⟨polyToP (MvPolynomial.C c), pointEval_polyToP_C x hx c⟩

/-- The maximal ideal of the point. -/
noncomputable abbrev pointIdeal : Ideal (P L m) :=
  RingHom.ker (pointEval (m := m) x hx)

/-- The residue field at a rational point is the base field. -/
noncomputable def pointResidueEquiv :
    (P L m ⧸ pointIdeal (m := m) x hx) ≃+* L :=
  RingHom.quotientKerEquivOfSurjective (pointEval_surjective x hx)

theorem pointIdeal_isMaximal : (pointIdeal (m := m) x hx).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (pointEval_surjective x hx)

end PointEval

end FiniteJet.GraphKoszul
