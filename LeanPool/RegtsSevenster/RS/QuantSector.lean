/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.TheoremForward
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SuperKill

/-!
# Assembly of the quantitative theorem

The quantitative Regts–Sevenster statement, assembled against the
sector bound.  The sector bound (`SquareSectorBound`) is the model
half of the dichotomy: when the super permutation action kills the
square block idempotent, both sector dimensions of the standard
model lie below the side.  It is discharged as
`squareSectorBound_of_detPos` in
`RS/Classical/Interfaces/SectorDischarge.lean` (sector intertwining
together with the square Schur nonvanishing); this file holds the
tower half of the dichotomy and the assembly.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-- **The sector bound**: super-level death of the square block
idempotent forces both dimensions of the standard model below the
side.  Discharged as `squareSectorBound_of_detPos` in
`RS/Classical/Interfaces/SectorDischarge.lean`. -/
def SquareSectorBound : Prop :=
  ∀ {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f)) (k l s : ℕ), 1 ≤ s →
    ∀ (e : SuperVect.Hom (stdSuperPair k l) (P.ω.obj (SkeinObj.mk 1)))
    (e' : SuperVect.Hom (P.ω.obj (SkeinObj.mk 1)) (stdSuperPair k l)),
    SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuperPair k l) →
    SuperVect.Hom.comp e e' =
      SuperVect.Hom.id (P.ω.obj (SkeinObj.mk 1)) →
    (∀ s' : ℕ, s ≤ s' →
      superPermAction f P (squareDiagram s').card
        (charIdempotent (nDim (jtSimple (squareDiagram s')))
          (jtChar (squareDiagram s'))) = 0) →
    k < s ∧ 2 * l < s

/-- **THE QUANTITATIVE REGTS–SEVENSTER THEOREM, CONDITIONAL ON
DELIGNE AND THE SECTOR BOUND**: every graph parameter with
edge-connection rank at most `R ^ t` is the mixed partition
function of a functional with both dimensions at most `⌊2eR⌋`. -/
theorem regts_sevenster_quant_of_sector
    (HSB : SquareSectorBound)
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementQuant := by
  intro R f
  obtain ⟨P⟩ := skein_delignePackage f hDeligne
  obtain ⟨k, ℓ, e, e', he'e, hee', hform, hcopair⟩ :=
    skein_std_model f P
  have hs : 2 * Real.exp 1 * (R : ℝ) <
      ((⌊2 * Real.exp 1 * (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have hdead : ∀ s' : ℕ, ⌊2 * Real.exp 1 * (R : ℝ)⌋₊ + 1 ≤ s' →
      superPermAction f P (squareDiagram s').card
        (charIdempotent (nDim (jtSimple (squareDiagram s')))
          (jtChar (squareDiagram s'))) = 0 := fun s' hs' =>
    superPermAction_square_dead f P
      (lt_of_lt_of_le hs (by exact_mod_cast hs'))
  obtain ⟨hk, hl⟩ := HSB f P k ℓ
    (⌊2 * Real.exp 1 * (R : ℝ)⌋₊ + 1) (Nat.le_add_left 1 _)
    e e' he'e hee' hdead
  refine ⟨k, ℓ, hRS f P e', by omega, by omega, fun W => ?_⟩
  exact parameter_eq_mixedPartition f P e e' W
    hee' he'e hform hcopair

end RS
