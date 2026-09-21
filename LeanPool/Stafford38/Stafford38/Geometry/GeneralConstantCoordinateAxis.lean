/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineComponentCoordinateSplit
import LeanPool.Stafford38.Stafford38.Geometry.ConstantCoordinateConormal
import Mathlib.RingTheory.Nullstellensatz

namespace Stafford38.Geometry.GeneralConstantCoordinateAxis

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ConstantCoordinateConormal

noncomputable section

universe u

theorem exists_constant_coordinate_equation_and_pure_axis
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (halg : IsAlgebraic k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ (c : k) (y : Fin m → k),
      MvPolynomial.X ⟨0, hm⟩ - MvPolynomial.C c ∈ P.asIdeal ∧
      (∀ f ∈ P.asIdeal, MvPolynomial.eval y f = 0) ∧
      Sum.elim y (fun j ↦ if j = ⟨0, hm⟩ then 1 else 0) ∈
        Stafford38.Geometry.AffineConormalClosure.equationConormalLocus
          P.asIdeal := by
  obtain ⟨c, hc⟩ | htrans :=
    coordinate_constant_or_transcendental P ⟨0, hm⟩
  · obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    obtain ⟨y, hMy⟩ :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hMmax
    have hy : ∀ f ∈ P.asIdeal, MvPolynomial.eval y f = 0 := by
      intro f hf
      have hfM : f ∈ M := hPM hf
      rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfM
      exact hfM
    refine ⟨c, y, hc, hy, ?_⟩
    exact constantCoordinate_phasePoint_mem_equationConormalLocus
      P.asIdeal y hy ⟨0, hm⟩ c hc
  · exact False.elim (htrans halg)


end

end Stafford38.Geometry.GeneralConstantCoordinateAxis
