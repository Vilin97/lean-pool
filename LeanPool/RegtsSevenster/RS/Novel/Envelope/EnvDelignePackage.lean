/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvSemisimple
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvGrowth
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatRigid
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatEmbMonoidal
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiRigid
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiEmbBraided
public import LeanPool.RegtsSevenster.RS.Novel.Skein.RigidInstance
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackageRestrict
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneTheorem

/-!
# The Deligne package for the skein category

The payoff of the envelope construction: the envelope
satisfies all hypotheses of the abstract Deligne statement, so it
receives a fibre functor; restricting along the braided linear
embedding of the skein category yields the Deligne package that
the extraction consumes — with Deligne's theorem itself as the
only transcendental input, applied to the concretely constructed
envelope.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The braided linear embedding of the skein category into its
envelope. -/
noncomputable def skeinToEnv : SkeinObj f ⥤ Env f :=
  toKaroubi (SkeinObj f) ⋙
    Mat_.embedding (Karoubi (SkeinObj f)) ⋙
    toKaroubi (Mat_ (Karoubi (SkeinObj f)))

/-- The embedding of the skein category into its envelope is
braided. -/
noncomputable instance skeinToEnvBraided :
    (skeinToEnv f).Braided := by
  unfold skeinToEnv
  infer_instance

/-- It is additive. -/
noncomputable instance skeinToEnvAdditive :
    (skeinToEnv f).Additive := by
  unfold skeinToEnv
  infer_instance

/-- And ℂ-linear — so restricting the envelope's fibre functor
along it gives a package on the skein category. -/
noncomputable instance skeinToEnvLinear :
    (skeinToEnv f).Linear ℂ := by
  unfold skeinToEnv
  infer_instance

/-- **The strand tensor-generates in Deligne's sense.**  The
envelope generates more strongly than the theorem asks — every
object is a retract of a finite biproduct of pure tensor powers of
the strand, where a subquotient of a biproduct of mixed powers
would do. -/
theorem env_deligneGenerated :
    TensorGeneratedBy (Env f) (envStrand f 1) :=
  tensorGeneratedBy_of_retract (Env f) (env_strandRetract f)

/-- **The Deligne package for the envelope**: Deligne's theorem
applies to the envelope.  Its growth hypothesis is stated by
composition length, which the envelope's bound on endomorphism
dimensions supplies through semisimplicity and finite-dimensional
Hom-spaces — properties of the envelope, not hypotheses of the
theorem; and its conclusion carries exactness and faithfulness,
which the package drops. -/
theorem env_delignePackage
    (hD : DeligneTheoremStatement.{1, 1}) :
    Nonempty (DelignePackage (Env f)) := by
  let := envAbelian f
  exact (hD (Env f) (env_endOne f)
    ⟨envStrand f 1, env_deligneGenerated f⟩
    (moderateLengthGrowth_of_endGrowth (Env f) (envAbelian f)
      (env_deligneSemisimple f) (env_finDimHom f)
      (env_deligneModerateGrowth f))).map
    DeligneFibreFunctor.toPackage

/-- **The Deligne package for the skein category**: restrict
the envelope's fibre functor along the embedding. -/
theorem skein_delignePackage
    (hD : DeligneTheoremStatement.{1, 1}) :
    Nonempty (DelignePackage (SkeinObj f)) := by
  obtain ⟨Q⟩ := env_delignePackage f hD
  exact ⟨Q.restrict (skeinToEnv f)⟩

end RS
