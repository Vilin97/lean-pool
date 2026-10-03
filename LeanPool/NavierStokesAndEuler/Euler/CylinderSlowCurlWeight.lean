/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlTime
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime

/-! Related estimates used together by the same construction modules. -/

section

/-! Exact time-profile normalization of the actual slow curl and its time derivative. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSlowCurl

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerMeanCoefficients EulerPacketPiola
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderPotential
open scoped ContDiff BoundedContinuousFunction

section General

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlWeight3 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight4 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

variable (g : C(K, ℝ)) (G : C(K, Space →ᵇ Space →L[ℝ] Space))
  (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a p))

include hp in
theorem term_weight (i : Fin 3) :
    term P G (weight (E := LiftL2 P) g p) i = weight (E := LiftL2 P) g (term P G p i) :=
  (congrArg (fullMultiplierMap (K := K) (E := Space) (F := Space) P
      (curlCoefficientPath (K := K) i G)) (derivativePath_weight P g p hp i.succ)).trans
    (fullMultiplier_weight P g (derivativePath P p i.succ) (curlCoefficientPath (K := K) i G))

include hp in
theorem path_weight :
    path P G (weight (E := LiftL2 P) g p) = weight (E := LiftL2 P) g (path P G p) := by
  unfold path
  simp_rw [term_weight P g G p hp]
  exact (map_sum (weight (E := LiftL2 P) g) _ _).symm

include hp in
theorem path_normalize (hg : ∀ t, 0 < g t) :
    path P G (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p) =
      EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg (path P G p) :=
  path_weight P (reciprocal g hg) G p hp

include hp in
/-- The literal normalized curl has the same radius, with one spatial derivative. -/
theorem normalized_path_block_bound (hg : ∀ t, 0 < g t)
    (hG : ContDiff ℝ ∞ (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G) a‖ ≤
        C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block standardDirection q (fun a : LiftTangent =>
      pathTranslate (K := K) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize g hg p : C(K, CylinderL2 P _))) n 0 ≤
        D*majorant R d n)
    (n : ℕ) :
    block standardDirection q (fun a : LiftTangent =>
      pathTranslate (K := K) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize g hg (path P G p) : C(K, CylinderL2 P _))) n 0 ≤
      (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  rw [← path_normalize P g G p hp hg]
  exact path_block_bound P G hG (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p)
    (weighted_orbit P (reciprocal g hg) p hp) q Rc C R D hRc hC hD hR hbG d hbp n

end General

section Time

variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (G G₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent =>
    pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent =>
    pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a f))

include hp hf in
/-- This is C_t/g, so no derivative or extremum of the profile is needed. -/
theorem derivative_normalize :
    EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg (derivative P T G G₁ p f) =
      derivative P T G G₁ (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p)
        (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg f) := by
  unfold derivative EulerContinuousTimeWeight.normalize
  exact ((weight (E := LiftL2 P) (reciprocal g hg)).map_add _ _).trans
    (congrArg₂ (· + ·) (path_weight P (reciprocal g hg) G₁ p hp).symm
      (path_weight P (reciprocal g hg) G f hf).symm)

include hp hf in
theorem normalized_derivative_block_bound
    (hG : ContDiff ℝ ∞
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) G))
    (hG₁ : ContDiff ℝ ∞
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) G₁))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) G) a‖ ≤
        C * majorant Rc 0 n)
    (hbG₁ : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) G₁) a‖ ≤
        C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block standardDirection q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize (E := CylinderL2 P Vector3) g hg p)) n 0 ≤
        D*majorant R d n)
    (hbf : ∀ n, block standardDirection q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize (E := CylinderL2 P Vector3) g hg f)) n 0 ≤
        D*majorant R d n)
    (n : ℕ) :
    block standardDirection q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize (E := CylinderL2 P Vector3) g hg
          (derivative P T G G₁ p f))) n 0 ≤
      (18*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  simp only [derivative_normalize P T g hg G G₁ p f hp hf]
  exact derivative_block_bound P T G G₁ hG hG₁
    (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p)
    (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    q Rc C R D hRc hC hD hR hbG hbG₁ d hbp hbf n

end Time

end EulerCylinderSlowCurl

end
end

end

section

/-! Same-radius bounds and literal profile normalization for the constructed potential time
derivative. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPotential

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMeanCoefficients
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (B B₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B₁))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent =>
    pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent =>
    pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a f))

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight3 : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTimeWeight4 : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance

include hB hB₁ hp hf in
theorem potentialDerivative_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B) a‖ ≤
        C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B₁) a‖ ≤
        C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a p) n 0 ≤ D*majorant R d n)
    (hbf : ∀ n, block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a f) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (potentialDerivative P T B B₁ p f)) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  have he : (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (potentialDerivative P T B B₁ p f)) =
      (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (potentialPath P B₁ p)) +
        (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
          (potentialPath P B f)) := by
    funext a
    exact map_add (pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a) _ _
  rw [he]
  have hs := block_add_le directions q _ _
    (potentialPath_orbit P B₁ hB₁ p hp) (potentialPath_orbit P B hB f hf) n (0 : LiftTangent)
  have h₁ := potentialPath_block_bound P B₁ hB₁ p hp directions hd q
    Rc C R D hRc hC hD hR hbB₁ d hbp n
  have h₂ := potentialPath_block_bound P B hB f hf directions hd q
    Rc C R D hRc hC hD hR hbB d hbf n
  exact (hs.trans (add_le_add h₁ h₂)).trans_eq (by ring)

theorem potentialDerivative_normalize (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) :
    EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg (potentialDerivative P T B B₁ p f) =
      potentialDerivative P T B B₁ (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p)
        (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg f) := by
  unfold potentialDerivative EulerContinuousTimeWeight.normalize
  exact ((weight (E := LiftL2 P) (reciprocal g hg)).map_add _ _).trans
    (congrArg₂ (· + ·) (potentialPath_weight P (reciprocal g hg) p B₁).symm
      (potentialPath_weight P (reciprocal g hg) f B).symm)

include hB hB₁ hp hf in
/-- Estimate Q_t/g from A/g and A_t/g, without differentiating the profile g. -/
theorem normalized_potentialDerivative_block_bound
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B) a‖ ≤
        C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := Icc (0 : ℝ) T) (V := Space →L[ℝ] Space) B₁) a‖ ≤
        C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize g hg p : C(Icc (0 : ℝ) T, CylinderL2 P _))) n 0 ≤
          D*majorant R d n)
    (hbf : ∀ n, block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize g hg f : C(Icc (0 : ℝ) T, CylinderL2 P _))) n 0 ≤
          D*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := Vector3) P a
        (EulerContinuousTimeWeight.normalize g hg (potentialDerivative P T B B₁ p f) :
          C(Icc (0 : ℝ) T, CylinderL2 P _))) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  simp only [potentialDerivative_normalize]
  exact potentialDerivative_block_bound P T B B₁ hB hB₁
    (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg p)
    (EulerContinuousTimeWeight.normalize (E := LiftL2 P) g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    directions hd q Rc C R D hRc hC hD hR hbB hbB₁ d hbp hbf n

end EulerCylinderPotential

end
end

end
