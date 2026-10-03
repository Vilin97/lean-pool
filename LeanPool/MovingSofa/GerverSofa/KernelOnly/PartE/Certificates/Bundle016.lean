/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch025`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells4a1452a6c6

/-- Subcell `0001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `0010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0010)))

/-- Subcell `000123013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012301)))

/-- Subcell `000123102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012310)))

/-- Subcell `000123102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012310)))

/-- Subcell `000123103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012310)))

/-- Subcell `000123103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012310)))

/-- Subcell `000123112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012311)))

/-- Subcell `000123112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012311)))

/-- Subcell `000123113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012311)))

/-- Subcell `000123113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000123113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012311)))

/-- Subcell `000132002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013200)))

/-- Subcell `000132002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013200)))

/-- Subcell `000132003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013200)))

/-- Subcell `000132003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013200)))

/-- Subcell `000132012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013201)))

/-- Subcell `000132012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013201)))

/-- Subcell `000132013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013201)))

/-- Subcell `000132013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013201)))

/-- Subcell `000132102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013210)))

/-- Subcell `000132102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013210)))

/-- Subcell `000132103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013210)))

/-- Subcell `000132103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013210)))

/-- Subcell `000132112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013211)))

/-- Subcell `000132112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013211)))

/-- Subcell `000132113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013211)))

/-- Subcell `000132113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000132113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000132113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013211)))

/-- Subcell `000133002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013300)))

/-- Subcell `000133002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013300)))

/-- Subcell `000133003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013300)))

/-- Subcell `000133003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013300)))

/-- Subcell `000133012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell00013301)))

/-- Subcell `000133012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell00013301)))

/-- Subcell `000133013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell00013301)))

/-- Subcell `000133013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell00013301)))

/-- Subcell `000133102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell00013310)))

/-- Subcell `000133102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell00013310)))

/-- Subcell `000133103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell00013310)))

/-- Subcell `000133103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell00013310)))

/-- Subcell `000133112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell00013311)))

/-- Subcell `000133112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00013311)))

/-- Subcell `000133113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00013311)))

/-- Subcell `000133113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `000133113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000133113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00013311)))

/-- Subcell `001022002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00102200)))

/-- Subcell `001022002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00102200)))

/-- Subcell `001022003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00102200)))

/-- Subcell `001022003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00102200)))

/-- Subcell `001022012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00102201)))

/-- Subcell `001022012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00102201)))

/-- Subcell `001022012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00102201)))

/-- Subcell `001022013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00102201)))

/-- Subcell `001022013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00102201)))

/-- Subcell `001022102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00102210)))

/-- Subcell `001022102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00102210)))

/-- Subcell `001022103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00102210)))

/-- Subcell `001022103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00102210)))

/-- Subcell `001022103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell001022103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00102210)))

end GerverSofa.PartE.CertificateCells4a1452a6c6

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchAeb87c7b95a29e08`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4a1452a6c6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4a1452a6c6

open CertificateCells4a1452a6c6
theorem e24KC2ThetaAboveLeaf0001230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013100 h)
        (by
          have h : (thetaAboveCell000123013101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013101 h)
        (by
          have h : (thetaAboveCell000123013102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013102 h)
        (by
          have h : (thetaAboveCell000123013103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013110 h)
        (by
          have h : (thetaAboveCell000123013111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013111 h)
        (by
          have h : (thetaAboveCell000123013112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013112 h)
        (by
          have h : (thetaAboveCell000123013113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013120 h)
        (by
          have h : (thetaAboveCell000123013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013121 h)
        (by
          have h : (thetaAboveCell000123013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013122 h)
        (by
          have h : (thetaAboveCell000123013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013130 h)
        (by
          have h : (thetaAboveCell000123013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013131 h)
        (by
          have h : (thetaAboveCell000123013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013132 h)
        (by
          have h : (thetaAboveCell000123013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013133 h))
theorem e24KC2ThetaAboveLeaf0001230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013200 h)
        (by
          have h : (thetaAboveCell000123013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013201 h)
        (by
          have h : (thetaAboveCell000123013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013202 h)
        (by
          have h : (thetaAboveCell000123013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013210 h)
        (by
          have h : (thetaAboveCell000123013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013211 h)
        (by
          have h : (thetaAboveCell000123013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013212 h)
        (by
          have h : (thetaAboveCell000123013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013300 h)
        (by
          have h : (thetaAboveCell000123013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013301 h)
        (by
          have h : (thetaAboveCell000123013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013302 h)
        (by
          have h : (thetaAboveCell000123013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013310 h)
        (by
          have h : (thetaAboveCell000123013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013311 h)
        (by
          have h : (thetaAboveCell000123013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013312 h)
        (by
          have h : (thetaAboveCell000123013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001231002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012310))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012310))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012310))) h)
theorem e24KC2ThetaAboveLeaf0001231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102000 h)
        (by
          have h : (thetaAboveCell000123102001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102001 h)
        (by
          have h : (thetaAboveCell000123102002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102002 h)
        (by
          have h : (thetaAboveCell000123102003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102010 h)
        (by
          have h : (thetaAboveCell000123102011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102011 h)
        (by
          have h : (thetaAboveCell000123102012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102012 h)
        (by
          have h : (thetaAboveCell000123102013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102020 h)
        (by
          have h : (thetaAboveCell000123102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102021 h)
        (by
          have h : (thetaAboveCell000123102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102022 h)
        (by
          have h : (thetaAboveCell000123102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102030 h)
        (by
          have h : (thetaAboveCell000123102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102031 h)
        (by
          have h : (thetaAboveCell000123102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102032 h)
        (by
          have h : (thetaAboveCell000123102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102033 h))
theorem e24KC2ThetaAboveLeaf0001231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102100 h)
        (by
          have h : (thetaAboveCell000123102101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102101 h)
        (by
          have h : (thetaAboveCell000123102102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102102 h)
        (by
          have h : (thetaAboveCell000123102103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102110 h)
        (by
          have h : (thetaAboveCell000123102111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102111 h)
        (by
          have h : (thetaAboveCell000123102112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102112 h)
        (by
          have h : (thetaAboveCell000123102113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102120 h)
        (by
          have h : (thetaAboveCell000123102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102121 h)
        (by
          have h : (thetaAboveCell000123102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102122 h)
        (by
          have h : (thetaAboveCell000123102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102130 h)
        (by
          have h : (thetaAboveCell000123102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102131 h)
        (by
          have h : (thetaAboveCell000123102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102132 h)
        (by
          have h : (thetaAboveCell000123102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102133 h))
theorem e24KC2ThetaAboveLeaf0001231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102200 h)
        (by
          have h : (thetaAboveCell000123102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102201 h)
        (by
          have h : (thetaAboveCell000123102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102202 h)
        (by
          have h : (thetaAboveCell000123102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102210 h)
        (by
          have h : (thetaAboveCell000123102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102211 h)
        (by
          have h : (thetaAboveCell000123102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102212 h)
        (by
          have h : (thetaAboveCell000123102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012310))) h)
theorem e24KC2ThetaAboveLeaf0001231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102300 h)
        (by
          have h : (thetaAboveCell000123102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102301 h)
        (by
          have h : (thetaAboveCell000123102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102302 h)
        (by
          have h : (thetaAboveCell000123102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102310 h)
        (by
          have h : (thetaAboveCell000123102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102311 h)
        (by
          have h : (thetaAboveCell000123102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102312 h)
        (by
          have h : (thetaAboveCell000123102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012310))) h)
theorem e24KC2ThetaAboveLeaf0001231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103000 h)
        (by
          have h : (thetaAboveCell000123103001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103001 h)
        (by
          have h : (thetaAboveCell000123103002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103002 h)
        (by
          have h : (thetaAboveCell000123103003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103010 h)
        (by
          have h : (thetaAboveCell000123103011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103011 h)
        (by
          have h : (thetaAboveCell000123103012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103012 h)
        (by
          have h : (thetaAboveCell000123103013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103020 h)
        (by
          have h : (thetaAboveCell000123103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103021 h)
        (by
          have h : (thetaAboveCell000123103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103022 h)
        (by
          have h : (thetaAboveCell000123103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103030 h)
        (by
          have h : (thetaAboveCell000123103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103031 h)
        (by
          have h : (thetaAboveCell000123103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103032 h)
        (by
          have h : (thetaAboveCell000123103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103033 h))
theorem e24KC2ThetaAboveLeaf0001231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103100 h)
        (by
          have h : (thetaAboveCell000123103101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103101 h)
        (by
          have h : (thetaAboveCell000123103102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103102 h)
        (by
          have h : (thetaAboveCell000123103103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103110 h)
        (by
          have h : (thetaAboveCell000123103111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103111 h)
        (by
          have h : (thetaAboveCell000123103112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103112 h)
        (by
          have h : (thetaAboveCell000123103113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103120 h)
        (by
          have h : (thetaAboveCell000123103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103121 h)
        (by
          have h : (thetaAboveCell000123103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103122 h)
        (by
          have h : (thetaAboveCell000123103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103130 h)
        (by
          have h : (thetaAboveCell000123103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103131 h)
        (by
          have h : (thetaAboveCell000123103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103132 h)
        (by
          have h : (thetaAboveCell000123103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103133 h))
theorem e24KC2ThetaAboveLeaf0001231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103200 h)
        (by
          have h : (thetaAboveCell000123103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103201 h)
        (by
          have h : (thetaAboveCell000123103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103202 h)
        (by
          have h : (thetaAboveCell000123103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103210 h)
        (by
          have h : (thetaAboveCell000123103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103211 h)
        (by
          have h : (thetaAboveCell000123103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103212 h)
        (by
          have h : (thetaAboveCell000123103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012310))) h)
theorem e24KC2ThetaAboveLeaf0001231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103300 h)
        (by
          have h : (thetaAboveCell000123103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103301 h)
        (by
          have h : (thetaAboveCell000123103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103302 h)
        (by
          have h : (thetaAboveCell000123103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012310)))
        (by
          have h : (thetaAboveCell000123103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103310 h)
        (by
          have h : (thetaAboveCell000123103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103311 h)
        (by
          have h : (thetaAboveCell000123103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103312 h)
        (by
          have h : (thetaAboveCell000123103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012310))) h)
theorem e24KC2ThetaAboveLeaf0001231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112000 h)
        (by
          have h : (thetaAboveCell000123112001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112001 h)
        (by
          have h : (thetaAboveCell000123112002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112002 h)
        (by
          have h : (thetaAboveCell000123112003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112010 h)
        (by
          have h : (thetaAboveCell000123112011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112011 h)
        (by
          have h : (thetaAboveCell000123112012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112012 h)
        (by
          have h : (thetaAboveCell000123112013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112020 h)
        (by
          have h : (thetaAboveCell000123112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112021 h)
        (by
          have h : (thetaAboveCell000123112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112022 h)
        (by
          have h : (thetaAboveCell000123112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112030 h)
        (by
          have h : (thetaAboveCell000123112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112031 h)
        (by
          have h : (thetaAboveCell000123112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112032 h)
        (by
          have h : (thetaAboveCell000123112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112033 h))
theorem e24KC2ThetaAboveLeaf0001231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112100 h)
        (by
          have h : (thetaAboveCell000123112101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112101 h)
        (by
          have h : (thetaAboveCell000123112102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112102 h)
        (by
          have h : (thetaAboveCell000123112103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112110 h)
        (by
          have h : (thetaAboveCell000123112111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112111 h)
        (by
          have h : (thetaAboveCell000123112112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112112 h)
        (by
          have h : (thetaAboveCell000123112113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112120 h)
        (by
          have h : (thetaAboveCell000123112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112121 h)
        (by
          have h : (thetaAboveCell000123112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112122 h)
        (by
          have h : (thetaAboveCell000123112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112130 h)
        (by
          have h : (thetaAboveCell000123112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112131 h)
        (by
          have h : (thetaAboveCell000123112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112132 h)
        (by
          have h : (thetaAboveCell000123112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112133 h))
theorem e24KC2ThetaAboveLeaf0001231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112200 h)
        (by
          have h : (thetaAboveCell000123112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112201 h)
        (by
          have h : (thetaAboveCell000123112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112202 h)
        (by
          have h : (thetaAboveCell000123112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112210 h)
        (by
          have h : (thetaAboveCell000123112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112211 h)
        (by
          have h : (thetaAboveCell000123112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112212 h)
        (by
          have h : (thetaAboveCell000123112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012311))) h)
theorem e24KC2ThetaAboveLeaf0001231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112300 h)
        (by
          have h : (thetaAboveCell000123112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112301 h)
        (by
          have h : (thetaAboveCell000123112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112302 h)
        (by
          have h : (thetaAboveCell000123112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112310 h)
        (by
          have h : (thetaAboveCell000123112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112311 h)
        (by
          have h : (thetaAboveCell000123112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112312 h)
        (by
          have h : (thetaAboveCell000123112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012311))) h)
theorem e24KC2ThetaAboveLeaf0001231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113000 h)
        (by
          have h : (thetaAboveCell000123113001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113001 h)
        (by
          have h : (thetaAboveCell000123113002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113002 h)
        (by
          have h : (thetaAboveCell000123113003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113010 h)
        (by
          have h : (thetaAboveCell000123113011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113011 h)
        (by
          have h : (thetaAboveCell000123113012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113012 h)
        (by
          have h : (thetaAboveCell000123113013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113020 h)
        (by
          have h : (thetaAboveCell000123113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113021 h)
        (by
          have h : (thetaAboveCell000123113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113022 h)
        (by
          have h : (thetaAboveCell000123113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113030 h)
        (by
          have h : (thetaAboveCell000123113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113031 h)
        (by
          have h : (thetaAboveCell000123113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113032 h)
        (by
          have h : (thetaAboveCell000123113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113033 h))
theorem e24KC2ThetaAboveLeaf0001231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113100 h)
        (by
          have h : (thetaAboveCell000123113101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113101 h)
        (by
          have h : (thetaAboveCell000123113102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113102 h)
        (by
          have h : (thetaAboveCell000123113103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113110 h)
        (by
          have h : (thetaAboveCell000123113111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113111 h)
        (by
          have h : (thetaAboveCell000123113112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113112 h)
        (by
          have h : (thetaAboveCell000123113113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113120 h)
        (by
          have h : (thetaAboveCell000123113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113121 h)
        (by
          have h : (thetaAboveCell000123113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113122 h)
        (by
          have h : (thetaAboveCell000123113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113130 h)
        (by
          have h : (thetaAboveCell000123113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113131 h)
        (by
          have h : (thetaAboveCell000123113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113132 h)
        (by
          have h : (thetaAboveCell000123113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113133 h))
theorem e24KC2ThetaAboveLeaf0001231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113200 h)
        (by
          have h : (thetaAboveCell000123113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113201 h)
        (by
          have h : (thetaAboveCell000123113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113202 h)
        (by
          have h : (thetaAboveCell000123113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113210 h)
        (by
          have h : (thetaAboveCell000123113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113211 h)
        (by
          have h : (thetaAboveCell000123113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113212 h)
        (by
          have h : (thetaAboveCell000123113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012311))) h)
theorem e24KC2ThetaAboveLeaf0001231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113300 h)
        (by
          have h : (thetaAboveCell000123113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113301 h)
        (by
          have h : (thetaAboveCell000123113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113302 h)
        (by
          have h : (thetaAboveCell000123113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012311)))
        (by
          have h : (thetaAboveCell000123113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113310 h)
        (by
          have h : (thetaAboveCell000123113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113311 h)
        (by
          have h : (thetaAboveCell000123113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113312 h)
        (by
          have h : (thetaAboveCell000123113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012311))) h)
theorem e24KC2ThetaAboveLeaf0001320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002000 h)
        (by
          have h : (thetaAboveCell000132002001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002001 h)
        (by
          have h : (thetaAboveCell000132002002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002002 h)
        (by
          have h : (thetaAboveCell000132002003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002010 h)
        (by
          have h : (thetaAboveCell000132002011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002011 h)
        (by
          have h : (thetaAboveCell000132002012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002012 h)
        (by
          have h : (thetaAboveCell000132002013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002020 h)
        (by
          have h : (thetaAboveCell000132002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002021 h)
        (by
          have h : (thetaAboveCell000132002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002022 h)
        (by
          have h : (thetaAboveCell000132002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002030 h)
        (by
          have h : (thetaAboveCell000132002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002031 h)
        (by
          have h : (thetaAboveCell000132002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002032 h)
        (by
          have h : (thetaAboveCell000132002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002033 h))
theorem e24KC2ThetaAboveLeaf0001320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002100 h)
        (by
          have h : (thetaAboveCell000132002101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002101 h)
        (by
          have h : (thetaAboveCell000132002102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002102 h)
        (by
          have h : (thetaAboveCell000132002103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002110 h)
        (by
          have h : (thetaAboveCell000132002111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002111 h)
        (by
          have h : (thetaAboveCell000132002112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002112 h)
        (by
          have h : (thetaAboveCell000132002113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002120 h)
        (by
          have h : (thetaAboveCell000132002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002121 h)
        (by
          have h : (thetaAboveCell000132002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002122 h)
        (by
          have h : (thetaAboveCell000132002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002130 h)
        (by
          have h : (thetaAboveCell000132002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002131 h)
        (by
          have h : (thetaAboveCell000132002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002132 h)
        (by
          have h : (thetaAboveCell000132002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002133 h))
theorem e24KC2ThetaAboveLeaf0001320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002200 h)
        (by
          have h : (thetaAboveCell000132002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002201 h)
        (by
          have h : (thetaAboveCell000132002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002202 h)
        (by
          have h : (thetaAboveCell000132002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002210 h)
        (by
          have h : (thetaAboveCell000132002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002211 h)
        (by
          have h : (thetaAboveCell000132002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002212 h)
        (by
          have h : (thetaAboveCell000132002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00013200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00013200))) h)
theorem e24KC2ThetaAboveLeaf0001320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002300 h)
        (by
          have h : (thetaAboveCell000132002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002301 h)
        (by
          have h : (thetaAboveCell000132002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002302 h)
        (by
          have h : (thetaAboveCell000132002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002310 h)
        (by
          have h : (thetaAboveCell000132002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002311 h)
        (by
          have h : (thetaAboveCell000132002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002312 h)
        (by
          have h : (thetaAboveCell000132002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013200))) h)
theorem e24KC2ThetaAboveLeaf0001320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013200))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013200))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003020 h)
        (by
          have h : (thetaAboveCell000132003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003021 h)
        (by
          have h : (thetaAboveCell000132003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003022 h)
        (by
          have h : (thetaAboveCell000132003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003030 h)
        (by
          have h : (thetaAboveCell000132003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003031 h)
        (by
          have h : (thetaAboveCell000132003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003032 h)
        (by
          have h : (thetaAboveCell000132003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003033 h))
theorem e24KC2ThetaAboveLeaf0001320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013200))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013200))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003120 h)
        (by
          have h : (thetaAboveCell000132003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003121 h)
        (by
          have h : (thetaAboveCell000132003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003122 h)
        (by
          have h : (thetaAboveCell000132003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003130 h)
        (by
          have h : (thetaAboveCell000132003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003131 h)
        (by
          have h : (thetaAboveCell000132003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003132 h)
        (by
          have h : (thetaAboveCell000132003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003133 h))
theorem e24KC2ThetaAboveLeaf0001320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003200 h)
        (by
          have h : (thetaAboveCell000132003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003201 h)
        (by
          have h : (thetaAboveCell000132003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003202 h)
        (by
          have h : (thetaAboveCell000132003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003210 h)
        (by
          have h : (thetaAboveCell000132003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003211 h)
        (by
          have h : (thetaAboveCell000132003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003212 h)
        (by
          have h : (thetaAboveCell000132003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013200))) h)
theorem e24KC2ThetaAboveLeaf0001320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003300 h)
        (by
          have h : (thetaAboveCell000132003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003301 h)
        (by
          have h : (thetaAboveCell000132003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003302 h)
        (by
          have h : (thetaAboveCell000132003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013200)))
        (by
          have h : (thetaAboveCell000132003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003310 h)
        (by
          have h : (thetaAboveCell000132003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003311 h)
        (by
          have h : (thetaAboveCell000132003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003312 h)
        (by
          have h : (thetaAboveCell000132003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013200))) h)
theorem e24KC2ThetaAboveLeaf0001320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013201))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013201))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012020 h)
        (by
          have h : (thetaAboveCell000132012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012021 h)
        (by
          have h : (thetaAboveCell000132012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012022 h)
        (by
          have h : (thetaAboveCell000132012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012030 h)
        (by
          have h : (thetaAboveCell000132012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012031 h)
        (by
          have h : (thetaAboveCell000132012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012032 h)
        (by
          have h : (thetaAboveCell000132012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012033 h))
theorem e24KC2ThetaAboveLeaf0001320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013201))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013201))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012120 h)
        (by
          have h : (thetaAboveCell000132012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012121 h)
        (by
          have h : (thetaAboveCell000132012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012122 h)
        (by
          have h : (thetaAboveCell000132012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012130 h)
        (by
          have h : (thetaAboveCell000132012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012131 h)
        (by
          have h : (thetaAboveCell000132012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012132 h)
        (by
          have h : (thetaAboveCell000132012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012133 h))
theorem e24KC2ThetaAboveLeaf0001320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012200 h)
        (by
          have h : (thetaAboveCell000132012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012201 h)
        (by
          have h : (thetaAboveCell000132012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012202 h)
        (by
          have h : (thetaAboveCell000132012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012210 h)
        (by
          have h : (thetaAboveCell000132012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012211 h)
        (by
          have h : (thetaAboveCell000132012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012212 h)
        (by
          have h : (thetaAboveCell000132012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00013201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00013201))) h)
theorem e24KC2ThetaAboveLeaf0001320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012300 h)
        (by
          have h : (thetaAboveCell000132012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012301 h)
        (by
          have h : (thetaAboveCell000132012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012302 h)
        (by
          have h : (thetaAboveCell000132012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012310 h)
        (by
          have h : (thetaAboveCell000132012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012311 h)
        (by
          have h : (thetaAboveCell000132012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012312 h)
        (by
          have h : (thetaAboveCell000132012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013201))) h)
theorem e24KC2ThetaAboveLeaf0001320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013201))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013201))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013020 h)
        (by
          have h : (thetaAboveCell000132013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013021 h)
        (by
          have h : (thetaAboveCell000132013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013022 h)
        (by
          have h : (thetaAboveCell000132013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013030 h)
        (by
          have h : (thetaAboveCell000132013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013031 h)
        (by
          have h : (thetaAboveCell000132013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013032 h)
        (by
          have h : (thetaAboveCell000132013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013033 h))
theorem e24KC2ThetaAboveLeaf0001320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013201))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013201))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013120 h)
        (by
          have h : (thetaAboveCell000132013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013121 h)
        (by
          have h : (thetaAboveCell000132013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013122 h)
        (by
          have h : (thetaAboveCell000132013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013130 h)
        (by
          have h : (thetaAboveCell000132013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013131 h)
        (by
          have h : (thetaAboveCell000132013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013132 h)
        (by
          have h : (thetaAboveCell000132013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013133 h))
theorem e24KC2ThetaAboveLeaf0001320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013200 h)
        (by
          have h : (thetaAboveCell000132013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013201 h)
        (by
          have h : (thetaAboveCell000132013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013202 h)
        (by
          have h : (thetaAboveCell000132013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013210 h)
        (by
          have h : (thetaAboveCell000132013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013211 h)
        (by
          have h : (thetaAboveCell000132013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013212 h)
        (by
          have h : (thetaAboveCell000132013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013201))) h)
theorem e24KC2ThetaAboveLeaf0001320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013300 h)
        (by
          have h : (thetaAboveCell000132013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013301 h)
        (by
          have h : (thetaAboveCell000132013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013302 h)
        (by
          have h : (thetaAboveCell000132013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013201)))
        (by
          have h : (thetaAboveCell000132013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013310 h)
        (by
          have h : (thetaAboveCell000132013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013311 h)
        (by
          have h : (thetaAboveCell000132013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013312 h)
        (by
          have h : (thetaAboveCell000132013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013201))) h)
theorem e24KC2ThetaAboveLeaf0001321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013210))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013210))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102020 h)
        (by
          have h : (thetaAboveCell000132102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102021 h)
        (by
          have h : (thetaAboveCell000132102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102022 h)
        (by
          have h : (thetaAboveCell000132102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102030 h)
        (by
          have h : (thetaAboveCell000132102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102031 h)
        (by
          have h : (thetaAboveCell000132102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102032 h)
        (by
          have h : (thetaAboveCell000132102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102033 h))
theorem e24KC2ThetaAboveLeaf0001321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013210))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013210))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102120 h)
        (by
          have h : (thetaAboveCell000132102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102121 h)
        (by
          have h : (thetaAboveCell000132102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102122 h)
        (by
          have h : (thetaAboveCell000132102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102130 h)
        (by
          have h : (thetaAboveCell000132102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102131 h)
        (by
          have h : (thetaAboveCell000132102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102132 h)
        (by
          have h : (thetaAboveCell000132102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102133 h))
theorem e24KC2ThetaAboveLeaf0001321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102200 h)
        (by
          have h : (thetaAboveCell000132102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102201 h)
        (by
          have h : (thetaAboveCell000132102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102202 h)
        (by
          have h : (thetaAboveCell000132102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102210 h)
        (by
          have h : (thetaAboveCell000132102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102211 h)
        (by
          have h : (thetaAboveCell000132102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102212 h)
        (by
          have h : (thetaAboveCell000132102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00013210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00013210))) h)
theorem e24KC2ThetaAboveLeaf0001321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102300 h)
        (by
          have h : (thetaAboveCell000132102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102301 h)
        (by
          have h : (thetaAboveCell000132102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102302 h)
        (by
          have h : (thetaAboveCell000132102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102310 h)
        (by
          have h : (thetaAboveCell000132102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102311 h)
        (by
          have h : (thetaAboveCell000132102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102312 h)
        (by
          have h : (thetaAboveCell000132102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013210))) h)
theorem e24KC2ThetaAboveLeaf0001321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013210))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013210))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103020 h)
        (by
          have h : (thetaAboveCell000132103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103021 h)
        (by
          have h : (thetaAboveCell000132103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103022 h)
        (by
          have h : (thetaAboveCell000132103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103030 h)
        (by
          have h : (thetaAboveCell000132103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103031 h)
        (by
          have h : (thetaAboveCell000132103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103032 h)
        (by
          have h : (thetaAboveCell000132103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103033 h))
theorem e24KC2ThetaAboveLeaf0001321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013210))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013210))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103120 h)
        (by
          have h : (thetaAboveCell000132103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103121 h)
        (by
          have h : (thetaAboveCell000132103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103122 h)
        (by
          have h : (thetaAboveCell000132103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103130 h)
        (by
          have h : (thetaAboveCell000132103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103131 h)
        (by
          have h : (thetaAboveCell000132103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103132 h)
        (by
          have h : (thetaAboveCell000132103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103133 h))
theorem e24KC2ThetaAboveLeaf0001321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103200 h)
        (by
          have h : (thetaAboveCell000132103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103201 h)
        (by
          have h : (thetaAboveCell000132103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103202 h)
        (by
          have h : (thetaAboveCell000132103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103210 h)
        (by
          have h : (thetaAboveCell000132103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103211 h)
        (by
          have h : (thetaAboveCell000132103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103212 h)
        (by
          have h : (thetaAboveCell000132103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013210))) h)
theorem e24KC2ThetaAboveLeaf0001321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103300 h)
        (by
          have h : (thetaAboveCell000132103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103301 h)
        (by
          have h : (thetaAboveCell000132103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103302 h)
        (by
          have h : (thetaAboveCell000132103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013210)))
        (by
          have h : (thetaAboveCell000132103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103310 h)
        (by
          have h : (thetaAboveCell000132103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103311 h)
        (by
          have h : (thetaAboveCell000132103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103312 h)
        (by
          have h : (thetaAboveCell000132103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013210))) h)
theorem e24KC2ThetaAboveLeaf0001321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013211))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013211))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112020 h)
        (by
          have h : (thetaAboveCell000132112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112021 h)
        (by
          have h : (thetaAboveCell000132112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112022 h)
        (by
          have h : (thetaAboveCell000132112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112030 h)
        (by
          have h : (thetaAboveCell000132112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112031 h)
        (by
          have h : (thetaAboveCell000132112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112032 h)
        (by
          have h : (thetaAboveCell000132112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112033 h))
theorem e24KC2ThetaAboveLeaf0001321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013211))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013211))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112120 h)
        (by
          have h : (thetaAboveCell000132112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112121 h)
        (by
          have h : (thetaAboveCell000132112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112122 h)
        (by
          have h : (thetaAboveCell000132112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112130 h)
        (by
          have h : (thetaAboveCell000132112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112131 h)
        (by
          have h : (thetaAboveCell000132112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112132 h)
        (by
          have h : (thetaAboveCell000132112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112133 h))
theorem e24KC2ThetaAboveLeaf0001321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112200 h)
        (by
          have h : (thetaAboveCell000132112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112201 h)
        (by
          have h : (thetaAboveCell000132112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112202 h)
        (by
          have h : (thetaAboveCell000132112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112210 h)
        (by
          have h : (thetaAboveCell000132112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112211 h)
        (by
          have h : (thetaAboveCell000132112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112212 h)
        (by
          have h : (thetaAboveCell000132112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00013211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00013211))) h)
theorem e24KC2ThetaAboveLeaf0001321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112300 h)
        (by
          have h : (thetaAboveCell000132112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112301 h)
        (by
          have h : (thetaAboveCell000132112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112302 h)
        (by
          have h : (thetaAboveCell000132112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112310 h)
        (by
          have h : (thetaAboveCell000132112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112311 h)
        (by
          have h : (thetaAboveCell000132112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112312 h)
        (by
          have h : (thetaAboveCell000132112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013211))) h)
theorem e24KC2ThetaAboveLeaf0001321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013211))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013211))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113020 h)
        (by
          have h : (thetaAboveCell000132113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113021 h)
        (by
          have h : (thetaAboveCell000132113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113022 h)
        (by
          have h : (thetaAboveCell000132113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113030 h)
        (by
          have h : (thetaAboveCell000132113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113031 h)
        (by
          have h : (thetaAboveCell000132113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113032 h)
        (by
          have h : (thetaAboveCell000132113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113033 h))
theorem e24KC2ThetaAboveLeaf0001321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013211))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013211))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113120 h)
        (by
          have h : (thetaAboveCell000132113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113121 h)
        (by
          have h : (thetaAboveCell000132113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113122 h)
        (by
          have h : (thetaAboveCell000132113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113130 h)
        (by
          have h : (thetaAboveCell000132113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113131 h)
        (by
          have h : (thetaAboveCell000132113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113132 h)
        (by
          have h : (thetaAboveCell000132113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113133 h))
theorem e24KC2ThetaAboveLeaf0001321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113200 h)
        (by
          have h : (thetaAboveCell000132113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113201 h)
        (by
          have h : (thetaAboveCell000132113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113202 h)
        (by
          have h : (thetaAboveCell000132113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113210 h)
        (by
          have h : (thetaAboveCell000132113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113211 h)
        (by
          have h : (thetaAboveCell000132113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113212 h)
        (by
          have h : (thetaAboveCell000132113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013211))) h)
theorem e24KC2ThetaAboveLeaf0001321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113300 h)
        (by
          have h : (thetaAboveCell000132113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113301 h)
        (by
          have h : (thetaAboveCell000132113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113302 h)
        (by
          have h : (thetaAboveCell000132113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013211)))
        (by
          have h : (thetaAboveCell000132113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113310 h)
        (by
          have h : (thetaAboveCell000132113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113311 h)
        (by
          have h : (thetaAboveCell000132113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113312 h)
        (by
          have h : (thetaAboveCell000132113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000132113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013211))) h)
theorem e24KC2ThetaAboveLeaf0001330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013300))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013300))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002020 h)
        (by
          have h : (thetaAboveCell000133002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002021 h)
        (by
          have h : (thetaAboveCell000133002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002022 h)
        (by
          have h : (thetaAboveCell000133002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002030 h)
        (by
          have h : (thetaAboveCell000133002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002031 h)
        (by
          have h : (thetaAboveCell000133002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002032 h)
        (by
          have h : (thetaAboveCell000133002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002033 h))
theorem e24KC2ThetaAboveLeaf0001330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013300))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013300))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002120 h)
        (by
          have h : (thetaAboveCell000133002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002121 h)
        (by
          have h : (thetaAboveCell000133002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002122 h)
        (by
          have h : (thetaAboveCell000133002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002130 h)
        (by
          have h : (thetaAboveCell000133002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002131 h)
        (by
          have h : (thetaAboveCell000133002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002132 h)
        (by
          have h : (thetaAboveCell000133002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002133 h))
theorem e24KC2ThetaAboveLeaf0001330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002200 h)
        (by
          have h : (thetaAboveCell000133002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002201 h)
        (by
          have h : (thetaAboveCell000133002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002202 h)
        (by
          have h : (thetaAboveCell000133002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002210 h)
        (by
          have h : (thetaAboveCell000133002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002211 h)
        (by
          have h : (thetaAboveCell000133002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002212 h)
        (by
          have h : (thetaAboveCell000133002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00013300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00013300))) h)
theorem e24KC2ThetaAboveLeaf0001330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002300 h)
        (by
          have h : (thetaAboveCell000133002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002301 h)
        (by
          have h : (thetaAboveCell000133002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002302 h)
        (by
          have h : (thetaAboveCell000133002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002310 h)
        (by
          have h : (thetaAboveCell000133002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002311 h)
        (by
          have h : (thetaAboveCell000133002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002312 h)
        (by
          have h : (thetaAboveCell000133002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013300))) h)
theorem e24KC2ThetaAboveLeaf0001330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013300))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013300))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003020 h)
        (by
          have h : (thetaAboveCell000133003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003021 h)
        (by
          have h : (thetaAboveCell000133003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003022 h)
        (by
          have h : (thetaAboveCell000133003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003030 h)
        (by
          have h : (thetaAboveCell000133003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003031 h)
        (by
          have h : (thetaAboveCell000133003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003032 h)
        (by
          have h : (thetaAboveCell000133003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003033 h))
theorem e24KC2ThetaAboveLeaf0001330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013300))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013300))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003120 h)
        (by
          have h : (thetaAboveCell000133003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003121 h)
        (by
          have h : (thetaAboveCell000133003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003122 h)
        (by
          have h : (thetaAboveCell000133003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003130 h)
        (by
          have h : (thetaAboveCell000133003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003131 h)
        (by
          have h : (thetaAboveCell000133003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003132 h)
        (by
          have h : (thetaAboveCell000133003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003133 h))
theorem e24KC2ThetaAboveLeaf0001330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003200 h)
        (by
          have h : (thetaAboveCell000133003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003201 h)
        (by
          have h : (thetaAboveCell000133003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003202 h)
        (by
          have h : (thetaAboveCell000133003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003210 h)
        (by
          have h : (thetaAboveCell000133003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003211 h)
        (by
          have h : (thetaAboveCell000133003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003212 h)
        (by
          have h : (thetaAboveCell000133003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013300))) h)
theorem e24KC2ThetaAboveLeaf0001330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003300 h)
        (by
          have h : (thetaAboveCell000133003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003301 h)
        (by
          have h : (thetaAboveCell000133003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003302 h)
        (by
          have h : (thetaAboveCell000133003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013300)))
        (by
          have h : (thetaAboveCell000133003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003310 h)
        (by
          have h : (thetaAboveCell000133003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003311 h)
        (by
          have h : (thetaAboveCell000133003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003312 h)
        (by
          have h : (thetaAboveCell000133003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013300))) h)
theorem e24KC2ThetaAboveLeaf0001330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013301))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013301))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013301))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012020 h)
        (by
          have h : (thetaAboveCell000133012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012021 h)
        (by
          have h : (thetaAboveCell000133012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012022 h)
        (by
          have h : (thetaAboveCell000133012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012030 h)
        (by
          have h : (thetaAboveCell000133012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012031 h)
        (by
          have h : (thetaAboveCell000133012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012032 h)
        (by
          have h : (thetaAboveCell000133012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012033 h))
theorem e24KC2ThetaAboveLeaf0001330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013301))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013301))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013301))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012120 h)
        (by
          have h : (thetaAboveCell000133012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012121 h)
        (by
          have h : (thetaAboveCell000133012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012122 h)
        (by
          have h : (thetaAboveCell000133012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012130 h)
        (by
          have h : (thetaAboveCell000133012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012131 h)
        (by
          have h : (thetaAboveCell000133012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012132 h)
        (by
          have h : (thetaAboveCell000133012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012133 h))
theorem e24KC2ThetaAboveLeaf0001330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012200 h)
        (by
          have h : (thetaAboveCell000133012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012201 h)
        (by
          have h : (thetaAboveCell000133012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012202 h)
        (by
          have h : (thetaAboveCell000133012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012210 h)
        (by
          have h : (thetaAboveCell000133012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012211 h)
        (by
          have h : (thetaAboveCell000133012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012212 h)
        (by
          have h : (thetaAboveCell000133012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012220 h)
        (by
          have h : (thetaAboveCell000133012221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012221 h)
        (by
          have h : (thetaAboveCell000133012222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012222 h)
        (by
          have h : (thetaAboveCell000133012223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012230 h)
        (by
          have h : (thetaAboveCell000133012231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012231 h)
        (by
          have h : (thetaAboveCell000133012232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012232 h)
        (by
          have h : (thetaAboveCell000133012233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012233 h))
theorem e24KC2ThetaAboveLeaf0001330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012300 h)
        (by
          have h : (thetaAboveCell000133012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012301 h)
        (by
          have h : (thetaAboveCell000133012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012302 h)
        (by
          have h : (thetaAboveCell000133012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012310 h)
        (by
          have h : (thetaAboveCell000133012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012311 h)
        (by
          have h : (thetaAboveCell000133012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012312 h)
        (by
          have h : (thetaAboveCell000133012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012320 h)
        (by
          have h : (thetaAboveCell000133012321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012321 h)
        (by
          have h : (thetaAboveCell000133012322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012322 h)
        (by
          have h : (thetaAboveCell000133012323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133012330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012330 h)
        (by
          have h : (thetaAboveCell000133012331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012331 h)
        (by
          have h : (thetaAboveCell000133012332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012332 h)
        (by
          have h : (thetaAboveCell000133012333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133012333 h))
theorem e24KC2ThetaAboveLeaf0001330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013301))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013301))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013301))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013020 h)
        (by
          have h : (thetaAboveCell000133013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013021 h)
        (by
          have h : (thetaAboveCell000133013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013022 h)
        (by
          have h : (thetaAboveCell000133013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013030 h)
        (by
          have h : (thetaAboveCell000133013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013031 h)
        (by
          have h : (thetaAboveCell000133013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013032 h)
        (by
          have h : (thetaAboveCell000133013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013033 h))
theorem e24KC2ThetaAboveLeaf0001330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013301))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013301))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013301))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013120 h)
        (by
          have h : (thetaAboveCell000133013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013121 h)
        (by
          have h : (thetaAboveCell000133013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013122 h)
        (by
          have h : (thetaAboveCell000133013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013130 h)
        (by
          have h : (thetaAboveCell000133013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013131 h)
        (by
          have h : (thetaAboveCell000133013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013132 h)
        (by
          have h : (thetaAboveCell000133013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013133 h))
theorem e24KC2ThetaAboveLeaf0001330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013200 h)
        (by
          have h : (thetaAboveCell000133013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013201 h)
        (by
          have h : (thetaAboveCell000133013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013202 h)
        (by
          have h : (thetaAboveCell000133013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013210 h)
        (by
          have h : (thetaAboveCell000133013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013211 h)
        (by
          have h : (thetaAboveCell000133013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013212 h)
        (by
          have h : (thetaAboveCell000133013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013220 h)
        (by
          have h : (thetaAboveCell000133013221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013221 h)
        (by
          have h : (thetaAboveCell000133013222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013222 h)
        (by
          have h : (thetaAboveCell000133013223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013230 h)
        (by
          have h : (thetaAboveCell000133013231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013231 h)
        (by
          have h : (thetaAboveCell000133013232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013232 h)
        (by
          have h : (thetaAboveCell000133013233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013233 h))
theorem e24KC2ThetaAboveLeaf0001330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013300 h)
        (by
          have h : (thetaAboveCell000133013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013301 h)
        (by
          have h : (thetaAboveCell000133013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013302 h)
        (by
          have h : (thetaAboveCell000133013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013310 h)
        (by
          have h : (thetaAboveCell000133013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013311 h)
        (by
          have h : (thetaAboveCell000133013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013312 h)
        (by
          have h : (thetaAboveCell000133013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013320 h)
        (by
          have h : (thetaAboveCell000133013321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013321 h)
        (by
          have h : (thetaAboveCell000133013322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013322 h)
        (by
          have h : (thetaAboveCell000133013323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH
        thetaAboveCell00013301)))
        (by
          have h : (thetaAboveCell000133013330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013330 h)
        (by
          have h : (thetaAboveCell000133013331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013331 h)
        (by
          have h : (thetaAboveCell000133013332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013332 h)
        (by
          have h : (thetaAboveCell000133013333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133013333 h))
theorem e24KC2ThetaAboveLeaf0001331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013310))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013310))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013310))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102020 h)
        (by
          have h : (thetaAboveCell000133102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102021 h)
        (by
          have h : (thetaAboveCell000133102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102022 h)
        (by
          have h : (thetaAboveCell000133102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102030 h)
        (by
          have h : (thetaAboveCell000133102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102031 h)
        (by
          have h : (thetaAboveCell000133102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102032 h)
        (by
          have h : (thetaAboveCell000133102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102033 h))
theorem e24KC2ThetaAboveLeaf0001331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013310))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013310))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013310))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102120 h)
        (by
          have h : (thetaAboveCell000133102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102121 h)
        (by
          have h : (thetaAboveCell000133102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102122 h)
        (by
          have h : (thetaAboveCell000133102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102130 h)
        (by
          have h : (thetaAboveCell000133102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102131 h)
        (by
          have h : (thetaAboveCell000133102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102132 h)
        (by
          have h : (thetaAboveCell000133102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102133 h))
theorem e24KC2ThetaAboveLeaf0001331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102200 h)
        (by
          have h : (thetaAboveCell000133102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102201 h)
        (by
          have h : (thetaAboveCell000133102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102202 h)
        (by
          have h : (thetaAboveCell000133102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102210 h)
        (by
          have h : (thetaAboveCell000133102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102211 h)
        (by
          have h : (thetaAboveCell000133102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102212 h)
        (by
          have h : (thetaAboveCell000133102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102220 h)
        (by
          have h : (thetaAboveCell000133102221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102221 h)
        (by
          have h : (thetaAboveCell000133102222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102222 h)
        (by
          have h : (thetaAboveCell000133102223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102230 h)
        (by
          have h : (thetaAboveCell000133102231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102231 h)
        (by
          have h : (thetaAboveCell000133102232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102232 h)
        (by
          have h : (thetaAboveCell000133102233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102233 h))
theorem e24KC2ThetaAboveLeaf0001331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102300 h)
        (by
          have h : (thetaAboveCell000133102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102301 h)
        (by
          have h : (thetaAboveCell000133102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102302 h)
        (by
          have h : (thetaAboveCell000133102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102310 h)
        (by
          have h : (thetaAboveCell000133102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102311 h)
        (by
          have h : (thetaAboveCell000133102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102312 h)
        (by
          have h : (thetaAboveCell000133102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102320 h)
        (by
          have h : (thetaAboveCell000133102321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102321 h)
        (by
          have h : (thetaAboveCell000133102322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102322 h)
        (by
          have h : (thetaAboveCell000133102323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133102330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102330 h)
        (by
          have h : (thetaAboveCell000133102331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102331 h)
        (by
          have h : (thetaAboveCell000133102332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102332 h)
        (by
          have h : (thetaAboveCell000133102333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133102333 h))
theorem e24KC2ThetaAboveLeaf0001331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013310))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013310))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013310))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103020 h)
        (by
          have h : (thetaAboveCell000133103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103021 h)
        (by
          have h : (thetaAboveCell000133103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103022 h)
        (by
          have h : (thetaAboveCell000133103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103030 h)
        (by
          have h : (thetaAboveCell000133103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103031 h)
        (by
          have h : (thetaAboveCell000133103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103032 h)
        (by
          have h : (thetaAboveCell000133103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103033 h))
theorem e24KC2ThetaAboveLeaf0001331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013310))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013310))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013310))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103120 h)
        (by
          have h : (thetaAboveCell000133103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103121 h)
        (by
          have h : (thetaAboveCell000133103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103122 h)
        (by
          have h : (thetaAboveCell000133103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103130 h)
        (by
          have h : (thetaAboveCell000133103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103131 h)
        (by
          have h : (thetaAboveCell000133103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103132 h)
        (by
          have h : (thetaAboveCell000133103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103133 h))
theorem e24KC2ThetaAboveLeaf0001331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103200 h)
        (by
          have h : (thetaAboveCell000133103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103201 h)
        (by
          have h : (thetaAboveCell000133103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103202 h)
        (by
          have h : (thetaAboveCell000133103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103210 h)
        (by
          have h : (thetaAboveCell000133103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103211 h)
        (by
          have h : (thetaAboveCell000133103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103212 h)
        (by
          have h : (thetaAboveCell000133103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103220 h)
        (by
          have h : (thetaAboveCell000133103221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103221 h)
        (by
          have h : (thetaAboveCell000133103222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103222 h)
        (by
          have h : (thetaAboveCell000133103223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103230 h)
        (by
          have h : (thetaAboveCell000133103231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103231 h)
        (by
          have h : (thetaAboveCell000133103232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103232 h)
        (by
          have h : (thetaAboveCell000133103233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103233 h))
theorem e24KC2ThetaAboveLeaf0001331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103300 h)
        (by
          have h : (thetaAboveCell000133103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103301 h)
        (by
          have h : (thetaAboveCell000133103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103302 h)
        (by
          have h : (thetaAboveCell000133103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103310 h)
        (by
          have h : (thetaAboveCell000133103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103311 h)
        (by
          have h : (thetaAboveCell000133103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103312 h)
        (by
          have h : (thetaAboveCell000133103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103320 h)
        (by
          have h : (thetaAboveCell000133103321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103321 h)
        (by
          have h : (thetaAboveCell000133103322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103322 h)
        (by
          have h : (thetaAboveCell000133103323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH
        thetaAboveCell00013310)))
        (by
          have h : (thetaAboveCell000133103330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103330 h)
        (by
          have h : (thetaAboveCell000133103331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103331 h)
        (by
          have h : (thetaAboveCell000133103332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103332 h)
        (by
          have h : (thetaAboveCell000133103333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133103333 h))
theorem e24KC2ThetaAboveLeaf0001331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00013311))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00013311))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00013311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112020 h)
        (by
          have h : (thetaAboveCell000133112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112021 h)
        (by
          have h : (thetaAboveCell000133112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112022 h)
        (by
          have h : (thetaAboveCell000133112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112030 h)
        (by
          have h : (thetaAboveCell000133112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112031 h)
        (by
          have h : (thetaAboveCell000133112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112032 h)
        (by
          have h : (thetaAboveCell000133112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112033 h))
theorem e24KC2ThetaAboveLeaf0001331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00013311))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00013311))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00013311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112120 h)
        (by
          have h : (thetaAboveCell000133112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112121 h)
        (by
          have h : (thetaAboveCell000133112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112122 h)
        (by
          have h : (thetaAboveCell000133112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112130 h)
        (by
          have h : (thetaAboveCell000133112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112131 h)
        (by
          have h : (thetaAboveCell000133112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112132 h)
        (by
          have h : (thetaAboveCell000133112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112133 h))
theorem e24KC2ThetaAboveLeaf0001331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00013311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112200 h)
        (by
          have h : (thetaAboveCell000133112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112201 h)
        (by
          have h : (thetaAboveCell000133112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112202 h)
        (by
          have h : (thetaAboveCell000133112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112210 h)
        (by
          have h : (thetaAboveCell000133112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112211 h)
        (by
          have h : (thetaAboveCell000133112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112212 h)
        (by
          have h : (thetaAboveCell000133112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112220 h)
        (by
          have h : (thetaAboveCell000133112221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112221 h)
        (by
          have h : (thetaAboveCell000133112222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112222 h)
        (by
          have h : (thetaAboveCell000133112223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112230 h)
        (by
          have h : (thetaAboveCell000133112231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112231 h)
        (by
          have h : (thetaAboveCell000133112232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112232 h)
        (by
          have h : (thetaAboveCell000133112233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112233 h))
theorem e24KC2ThetaAboveLeaf0001331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00013311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112300 h)
        (by
          have h : (thetaAboveCell000133112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112301 h)
        (by
          have h : (thetaAboveCell000133112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112302 h)
        (by
          have h : (thetaAboveCell000133112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112310 h)
        (by
          have h : (thetaAboveCell000133112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112311 h)
        (by
          have h : (thetaAboveCell000133112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112312 h)
        (by
          have h : (thetaAboveCell000133112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00013311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00013311))) h)
theorem e24KC2ThetaAboveLeaf0001331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00013311))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00013311))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00013311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113020 h)
        (by
          have h : (thetaAboveCell000133113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113021 h)
        (by
          have h : (thetaAboveCell000133113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113022 h)
        (by
          have h : (thetaAboveCell000133113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113030 h)
        (by
          have h : (thetaAboveCell000133113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113031 h)
        (by
          have h : (thetaAboveCell000133113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113032 h)
        (by
          have h : (thetaAboveCell000133113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113033 h))
theorem e24KC2ThetaAboveLeaf0001331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00013311))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00013311))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00013311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113120 h)
        (by
          have h : (thetaAboveCell000133113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113121 h)
        (by
          have h : (thetaAboveCell000133113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113122 h)
        (by
          have h : (thetaAboveCell000133113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113130 h)
        (by
          have h : (thetaAboveCell000133113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113131 h)
        (by
          have h : (thetaAboveCell000133113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113132 h)
        (by
          have h : (thetaAboveCell000133113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113133 h))
theorem e24KC2ThetaAboveLeaf0001331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00013311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113200 h)
        (by
          have h : (thetaAboveCell000133113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113201 h)
        (by
          have h : (thetaAboveCell000133113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113202 h)
        (by
          have h : (thetaAboveCell000133113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113210 h)
        (by
          have h : (thetaAboveCell000133113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113211 h)
        (by
          have h : (thetaAboveCell000133113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113212 h)
        (by
          have h : (thetaAboveCell000133113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00013311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00013311))) h)
theorem e24KC2ThetaAboveLeaf0001331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00013311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00013311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113300 h)
        (by
          have h : (thetaAboveCell000133113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113301 h)
        (by
          have h : (thetaAboveCell000133113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113302 h)
        (by
          have h : (thetaAboveCell000133113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00013311)))
        (by
          have h : (thetaAboveCell000133113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113310 h)
        (by
          have h : (thetaAboveCell000133113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113311 h)
        (by
          have h : (thetaAboveCell000133113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113312 h)
        (by
          have h : (thetaAboveCell000133113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000133113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00013311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00013311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00013311))) h)
theorem e24KC2ThetaAboveLeaf0001331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00013313))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00013313))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00013313))) h)
theorem e24KC2ThetaAboveLeaf0001331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00013313))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00013313))) h)
theorem e24KC2ThetaAboveLeaf0001331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00013313))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00013313))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00013313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00013313))) h)
theorem e24KC2ThetaAboveLeaf0010220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102200))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102200))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002020 h)
        (by
          have h : (thetaAboveCell001022002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002021 h)
        (by
          have h : (thetaAboveCell001022002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002022 h)
        (by
          have h : (thetaAboveCell001022002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002030 h)
        (by
          have h : (thetaAboveCell001022002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002031 h)
        (by
          have h : (thetaAboveCell001022002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002032 h)
        (by
          have h : (thetaAboveCell001022002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002033 h))
theorem e24KC2ThetaAboveLeaf0010220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102200))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102200))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002120 h)
        (by
          have h : (thetaAboveCell001022002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002121 h)
        (by
          have h : (thetaAboveCell001022002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002122 h)
        (by
          have h : (thetaAboveCell001022002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002130 h)
        (by
          have h : (thetaAboveCell001022002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002131 h)
        (by
          have h : (thetaAboveCell001022002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002132 h)
        (by
          have h : (thetaAboveCell001022002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002133 h))
theorem e24KC2ThetaAboveLeaf0010220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002200 h)
        (by
          have h : (thetaAboveCell001022002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002201 h)
        (by
          have h : (thetaAboveCell001022002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002202 h)
        (by
          have h : (thetaAboveCell001022002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002210 h)
        (by
          have h : (thetaAboveCell001022002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002211 h)
        (by
          have h : (thetaAboveCell001022002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002212 h)
        (by
          have h : (thetaAboveCell001022002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102200))) h)
theorem e24KC2ThetaAboveLeaf0010220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002300 h)
        (by
          have h : (thetaAboveCell001022002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002301 h)
        (by
          have h : (thetaAboveCell001022002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002302 h)
        (by
          have h : (thetaAboveCell001022002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002310 h)
        (by
          have h : (thetaAboveCell001022002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002311 h)
        (by
          have h : (thetaAboveCell001022002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002312 h)
        (by
          have h : (thetaAboveCell001022002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102200))) h)
theorem e24KC2ThetaAboveLeaf0010220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102200))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102200))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003020 h)
        (by
          have h : (thetaAboveCell001022003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003021 h)
        (by
          have h : (thetaAboveCell001022003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003022 h)
        (by
          have h : (thetaAboveCell001022003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003030 h)
        (by
          have h : (thetaAboveCell001022003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003031 h)
        (by
          have h : (thetaAboveCell001022003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003032 h)
        (by
          have h : (thetaAboveCell001022003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003033 h))
theorem e24KC2ThetaAboveLeaf0010220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102200))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102200))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003120 h)
        (by
          have h : (thetaAboveCell001022003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003121 h)
        (by
          have h : (thetaAboveCell001022003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003122 h)
        (by
          have h : (thetaAboveCell001022003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003130 h)
        (by
          have h : (thetaAboveCell001022003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003131 h)
        (by
          have h : (thetaAboveCell001022003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003132 h)
        (by
          have h : (thetaAboveCell001022003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003133 h))
theorem e24KC2ThetaAboveLeaf0010220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003200 h)
        (by
          have h : (thetaAboveCell001022003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003201 h)
        (by
          have h : (thetaAboveCell001022003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003202 h)
        (by
          have h : (thetaAboveCell001022003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003210 h)
        (by
          have h : (thetaAboveCell001022003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003211 h)
        (by
          have h : (thetaAboveCell001022003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003212 h)
        (by
          have h : (thetaAboveCell001022003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102200))) h)
theorem e24KC2ThetaAboveLeaf0010220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003300 h)
        (by
          have h : (thetaAboveCell001022003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003301 h)
        (by
          have h : (thetaAboveCell001022003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003302 h)
        (by
          have h : (thetaAboveCell001022003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00102200)))
        (by
          have h : (thetaAboveCell001022003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003310 h)
        (by
          have h : (thetaAboveCell001022003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003311 h)
        (by
          have h : (thetaAboveCell001022003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003312 h)
        (by
          have h : (thetaAboveCell001022003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102200))) h)
theorem e24KC2ThetaAboveLeaf0010220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102201))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012020 h)
        (by
          have h : (thetaAboveCell001022012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012021 h)
        (by
          have h : (thetaAboveCell001022012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012022 h)
        (by
          have h : (thetaAboveCell001022012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012030 h)
        (by
          have h : (thetaAboveCell001022012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012031 h)
        (by
          have h : (thetaAboveCell001022012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012032 h)
        (by
          have h : (thetaAboveCell001022012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012033 h))
theorem e24KC2ThetaAboveLeaf0010220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102201))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012120 h)
        (by
          have h : (thetaAboveCell001022012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012121 h)
        (by
          have h : (thetaAboveCell001022012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012122 h)
        (by
          have h : (thetaAboveCell001022012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012130 h)
        (by
          have h : (thetaAboveCell001022012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012131 h)
        (by
          have h : (thetaAboveCell001022012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012132 h)
        (by
          have h : (thetaAboveCell001022012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012133 h))
theorem e24KC2ThetaAboveLeaf0010220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012200 h)
        (by
          have h : (thetaAboveCell001022012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012201 h)
        (by
          have h : (thetaAboveCell001022012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012202 h)
        (by
          have h : (thetaAboveCell001022012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022012203 h))
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102201))) h)
theorem e24KC2ThetaAboveLeaf0010220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102201))) h)
theorem e24KC2ThetaAboveLeaf0010220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102201))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013020 h)
        (by
          have h : (thetaAboveCell001022013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013021 h)
        (by
          have h : (thetaAboveCell001022013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013022 h)
        (by
          have h : (thetaAboveCell001022013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013030 h)
        (by
          have h : (thetaAboveCell001022013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013031 h)
        (by
          have h : (thetaAboveCell001022013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013032 h)
        (by
          have h : (thetaAboveCell001022013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013033 h))
theorem e24KC2ThetaAboveLeaf0010220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102201))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013120 h)
        (by
          have h : (thetaAboveCell001022013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013121 h)
        (by
          have h : (thetaAboveCell001022013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013122 h)
        (by
          have h : (thetaAboveCell001022013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00102201)))
        (by
          have h : (thetaAboveCell001022013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013130 h)
        (by
          have h : (thetaAboveCell001022013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013131 h)
        (by
          have h : (thetaAboveCell001022013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013132 h)
        (by
          have h : (thetaAboveCell001022013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022013133 h))
theorem e24KC2ThetaAboveLeaf0010220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102201))) h)
theorem e24KC2ThetaAboveLeaf0010220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102201))) h)
theorem e24KC2ThetaAboveLeaf0010220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102202))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102202))) h)
theorem e24KC2ThetaAboveLeaf0010220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102202))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102202))) h)
theorem e24KC2ThetaAboveLeaf0010220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102202))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102202))) h)
theorem e24KC2ThetaAboveLeaf0010220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102202))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102202))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102202))) h)
theorem e24KC2ThetaAboveLeaf0010220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102203))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102203))) h)
theorem e24KC2ThetaAboveLeaf0010220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102203))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102203))) h)
theorem e24KC2ThetaAboveLeaf0010220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102203))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102203))) h)
theorem e24KC2ThetaAboveLeaf0010220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102203))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102203))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102203))) h)
theorem e24KC2ThetaAboveLeaf0010221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102210))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102020 h)
        (by
          have h : (thetaAboveCell001022102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102021 h)
        (by
          have h : (thetaAboveCell001022102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102022 h)
        (by
          have h : (thetaAboveCell001022102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102030 h)
        (by
          have h : (thetaAboveCell001022102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102031 h)
        (by
          have h : (thetaAboveCell001022102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102032 h)
        (by
          have h : (thetaAboveCell001022102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102033 h))
theorem e24KC2ThetaAboveLeaf0010221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102210))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102120 h)
        (by
          have h : (thetaAboveCell001022102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102121 h)
        (by
          have h : (thetaAboveCell001022102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102122 h)
        (by
          have h : (thetaAboveCell001022102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102130 h)
        (by
          have h : (thetaAboveCell001022102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102131 h)
        (by
          have h : (thetaAboveCell001022102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102132 h)
        (by
          have h : (thetaAboveCell001022102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022102133 h))
theorem e24KC2ThetaAboveLeaf0010221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102210))) h)
theorem e24KC2ThetaAboveLeaf0010221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102210))) h)
theorem e24KC2ThetaAboveLeaf0010221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102210))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103020 h)
        (by
          have h : (thetaAboveCell001022103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103021 h)
        (by
          have h : (thetaAboveCell001022103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103022 h)
        (by
          have h : (thetaAboveCell001022103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103030 h)
        (by
          have h : (thetaAboveCell001022103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103031 h)
        (by
          have h : (thetaAboveCell001022103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103032 h)
        (by
          have h : (thetaAboveCell001022103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103033 h))
theorem e24KC2ThetaAboveLeaf0010221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102210))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103120 h)
        (by
          have h : (thetaAboveCell001022103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103121 h)
        (by
          have h : (thetaAboveCell001022103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103122 h)
        (by
          have h : (thetaAboveCell001022103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00102210)))
        (by
          have h : (thetaAboveCell001022103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103130 h)
        (by
          have h : (thetaAboveCell001022103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103131 h)
        (by
          have h : (thetaAboveCell001022103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103132 h)
        (by
          have h : (thetaAboveCell001022103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell001022103133 h))
theorem e24KC2ThetaAboveLeaf0010221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102210))) h)
theorem e24KC2ThetaAboveLeaf0010221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102210))) h)
theorem e24KC2ThetaAboveLeaf0010221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102211))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00102211))) h)

end PartE
end GerverSofa

end

end

end

end

end

end
