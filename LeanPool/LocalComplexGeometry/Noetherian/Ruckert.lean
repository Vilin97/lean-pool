/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Algebra.NoetherianByRemainder
import LeanPool.LocalComplexGeometry.Germs.Ring
import LeanPool.LocalComplexGeometry.WPTBridge.PreparedAssociate
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Rückert's basis theorem

The induction is the classical analytic proof.  A nonzero element of an ideal
is made regular in the last variable, Weierstrass preparation replaces it by
an associated distinguished polynomial, and Weierstrass division maps the
ideal into a finite lower-dimensional remainder module.
-/


namespace LocalComplexGeometry

open WPTBridge

noncomputable section

/-- **Rückert's basis theorem.**  The local ring of holomorphic germs at the
origin of every finite-dimensional complex affine space is Noetherian. -/
theorem holomorphicGerm_isNoetherian_core :
    ∀ n : ℕ, IsNoetherianRing (HolomorphicGerm n)
  | 0 => holomorphicGerm_isNoetherian_zero
  | n + 1 => by
      let : IsNoetherianRing (HolomorphicGerm n) :=
        holomorphicGerm_isNoetherian_core n
      rw [isNoetherianRing_iff_ideal_fg]
      intro I
      by_cases hI : I = ⊥
      · subst I
        exact Submodule.fg_bot
      · obtain ⟨f, hfI, hf_ne⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot hI
        obtain ⟨L, d, H, a, u, hH, hcoord, hH0, horder, hprep⟩ :=
          exists_regularized_weierstrassPreparation hf_ne
        let e : HolomorphicGerm (n + 1) ≃+* HolomorphicGerm (n + 1) :=
          coordinatePullback L
        let J : Ideal (HolomorphicGerm (n + 1)) := I.map e.toRingHom
        let p : HolomorphicGerm (n + 1) :=
          preparedPolynomialGerm a hprep.1
        have hcoord_mem : coordinatePullback L f ∈ J := by
          exact Ideal.mem_map_of_mem e.toRingHom hfI
        have hassoc : Associated (coordinatePullback L f) p := by
          exact coordinatePullback_associated_preparedPolynomialGerm
            L H a u hcoord hprep
        have hpJ : p ∈ J :=
          (Ideal.mem_iff_of_associated hassoc).mp hcoord_mem
        have hJfg : J.FG :=
          Ideal.fg_of_remainder_kernel J p hpJ
            (preparedGermDivisionRemainderLinearMap
              a hprep.1 hprep.2.1)
            (preparedGermDivisionRemainderLinearMap_ker_le
              a hprep.1 hprep.2.1)
        have hback :
            (J.map e.symm.toRingHom).FG :=
          hJfg.map e.symm.toRingHom
        simpa [J, e, Ideal.map_map] using hback

/-- The Noetherian structure supplied by Rückert's theorem. -/
instance holomorphicGerm_instIsNoetherianRing (n : ℕ) :
    IsNoetherianRing (HolomorphicGerm n) :=
  holomorphicGerm_isNoetherian_core n

end

end LocalComplexGeometry
