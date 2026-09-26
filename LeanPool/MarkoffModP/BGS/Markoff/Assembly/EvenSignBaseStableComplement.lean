/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EvenSignComplementDivisibility

/-!
# From base sign-stability to complement divisibility

Because `Gamma` normalizes the even-sign subgroup, it is enough to connect the
four sign changes of one base point back to that base component. Every even
sign change then preserves the whole component and its finite complement.
-/

@[expose] public section

namespace BGS.Markoff

/-- If all even-sign changes of the base point lie in its `Gamma` component,
then every even sign preserves membership in that component. -/
theorem samePuncturedComponent_evenSign_smul_iff_of_base_stable
    {R : Type*} [CommRing R]
    (c x : PuncturedMarkoffSurface R)
    (hbase : ∀ s : EvenSign, SamePuncturedComponent c (s • c))
    (s : EvenSign) :
    SamePuncturedComponent c (s • x) ↔
      SamePuncturedComponent c x := by
  have hforward :
      ∀ (t : EvenSign) (y : PuncturedMarkoffSurface R),
        SamePuncturedComponent c y →
          SamePuncturedComponent c (t • y) := by
    intro t y hy
    obtain ⟨g, hgy⟩ := (samePuncturedComponent_iff_exists c y).1 hy
    obtain ⟨u, hcommute⟩ := exists_evenSign_smul_Gamma_smul t g
    have hbaseU := hbase u
    have hmove :
        SamePuncturedComponent (u • c) (g • (u • c)) :=
      (samePuncturedComponent_iff_exists (u • c) (g • (u • c))).2
        ⟨g, rfl⟩
    have htarget :
        SamePuncturedComponent c (g • (u • c)) :=
      samePuncturedComponent_trans hbaseU hmove
    have heq : t • y = g • (u • c) := by
      calc
        t • y = t • (g • c) := congrArg (t • ·) hgy.symm
        _ = g • (u • c) := hcommute c
    rw [heq]
    exact htarget
  constructor
  · intro hsx
    have hback := hforward s⁻¹ (s • x) hsx
    rw [inv_smul_smul] at hback
    exact hback
  · exact hforward s x

/-- Base sign-stability makes the finite component complement invariant under
every even sign. -/
theorem puncturedComponentComplementFinset_evenSign_mem_iff_of_base_stable
    (p : ℕ) [Fact p.Prime]
    (c x : PuncturedMarkoffSurface (ZMod p))
    (hbase : ∀ s : EvenSign, SamePuncturedComponent c (s • c))
    (s : EvenSign) :
    s • x ∈ puncturedComponentComplementFinset p c ↔
      x ∈ puncturedComponentComplementFinset p c := by
  rw [mem_puncturedComponentComplementFinset_iff,
    mem_puncturedComponentComplementFinset_iff]
  exact not_congr
    (samePuncturedComponent_evenSign_smul_iff_of_base_stable c x hbase s)

/-- The expected factor four in the complement size follows from the sole
geometric input that the four sign changes of the base point return to its
`Gamma` component. -/
theorem four_dvd_puncturedComponentComplementFinset_card_of_base_sign_stable
    (p : ℕ) [Fact p.Prime] (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hbase : ∀ s : EvenSign, SamePuncturedComponent c (s • c)) :
    4 ∣ (puncturedComponentComplementFinset p c).card := by
  apply
    four_dvd_puncturedComponentComplementFinset_card_of_evenSign_invariant
      p hpThree c
  intro s x
  exact
    puncturedComponentComplementFinset_evenSign_mem_iff_of_base_stable
      p c x hbase s

end BGS.Markoff
